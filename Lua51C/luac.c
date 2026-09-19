/*
** $Id: luac.c,v 1.44a 2003/04/07 20:34:20 lhf Exp $
** Lua compiler (saves bytecodes to files; also list bytecodes)
** See Copyright Notice in lua.h
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

#include "lua.h"
#include "lauxlib.h"

#include "lfunc.h"
#include "lmem.h"
#include "lobject.h"
#include "lopcodes.h"
#include "lstring.h"
#include "lundump.h"

#ifndef LUA_DEBUG
#define luaB_opentests(L)
#endif

#ifndef PROGNAME
#define PROGNAME	"luac"		/* program name */
#endif

#define	OUTPUT		"luac.out"	/* default output file */

static int listing = 0;			/* list bytecodes? */
static int dumping = 1;			/* dump bytecodes? */
static int stripping = 0;			/* strip debug information? */
static char Output[] = { OUTPUT };	/* default output file name */
static const char* output = Output;	/* output file name */
static const char* progname = PROGNAME;	/* actual program name */
static void fatal(const char* message);

/* Black Box handler metadata support.
 * Editable Lua may contain:
 *   -- export: h_12345678
 *   -- function: definite_drive_race_stategraph_...
 *
 * The exact export is copied from the original bytecode by luadec.  luac
 * appends that alias only in memory before parsing, so the editable source
 * stays readable and does not need `h_XXXXXXXX = function_name`.  The older
 * `-- handler:` path/hash metadata remains accepted as a compatibility
 * fallback. */
static unsigned int vlt_hash32(const char* text)
{
	const unsigned char* arr = (const unsigned char*)text;
	unsigned int a = 0x9E3779B9u, b = 0x9E3779B9u, c = 0xABCDEF00u;
	size_t len = strlen(text), left = len, p = 0;
	#define MIX() do { \
		a = ((c >> 13) ^ (a - b - c)); \
		b = ((a << 8) ^ (b - c - a)); \
		c = ((b >> 13) ^ (c - a - b)); \
		a = ((c >> 12) ^ (a - b - c)); \
		b = ((a << 16) ^ (b - c - a)); \
		c = ((b >> 5) ^ (c - a - b)); \
		a = ((c >> 3) ^ (a - b - c)); \
		b = ((a << 10) ^ (b - c - a)); \
		c = ((b >> 15) ^ (c - a - b)); \
	} while (0)
	while (left >= 12) {
		a += (unsigned int)arr[p] | ((unsigned int)arr[p+1] << 8) | ((unsigned int)arr[p+2] << 16) | ((unsigned int)arr[p+3] << 24);
		b += (unsigned int)arr[p+4] | ((unsigned int)arr[p+5] << 8) | ((unsigned int)arr[p+6] << 16) | ((unsigned int)arr[p+7] << 24);
		c += (unsigned int)arr[p+8] | ((unsigned int)arr[p+9] << 8) | ((unsigned int)arr[p+10] << 16) | ((unsigned int)arr[p+11] << 24);
		MIX(); p += 12; left -= 12;
	}
	c += (unsigned int)len;
	if (left >= 11) c += (unsigned int)arr[p+10] << 24;
	if (left >= 10) c += (unsigned int)arr[p+9] << 16;
	if (left >= 9)  c += (unsigned int)arr[p+8] << 8;
	if (left >= 8)  b += (unsigned int)arr[p+7] << 24;
	if (left >= 7)  b += (unsigned int)arr[p+6] << 16;
	if (left >= 6)  b += (unsigned int)arr[p+5] << 8;
	if (left >= 5)  b += (unsigned int)arr[p+4];
	if (left >= 4)  a += (unsigned int)arr[p+3] << 24;
	if (left >= 3)  a += (unsigned int)arr[p+2] << 16;
	if (left >= 2)  a += (unsigned int)arr[p+1] << 8;
	if (left >= 1)  a += (unsigned int)arr[p];
	MIX();
	#undef MIX
	return c;
}

static char* read_text_file(const char* filename, size_t* outSize)
{
	FILE* f = fopen(filename, "rb");
	long size;
	char* data;
	if (!f) return NULL;
	fseek(f, 0, SEEK_END); size = ftell(f); fseek(f, 0, SEEK_SET);
	if (size < 0) { fclose(f); return NULL; }
	data = (char*)malloc((size_t)size + 1);
	if (!data) { fclose(f); return NULL; }
	if (size && fread(data, 1, (size_t)size, f) != (size_t)size) { free(data); fclose(f); return NULL; }
	data[size] = 0;
	fclose(f);
	if (outSize) *outSize = (size_t)size;
	return data;
}

static int read_metadata_value(const char* text, const char* key, char* out, size_t outSize)
{
	const char* p = text;
	size_t keyLen = strlen(key);
	while (*p) {
		const char* line = p;
		const char* end = strchr(line, '\n');
		size_t len = end ? (size_t)(end - line) : strlen(line);
		while (len && (*line == ' ' || *line == '\t' || *line == '\r')) { line++; len--; }
		if (len > keyLen && strncmp(line, key, keyLen) == 0) {
			const char* value = line + keyLen;
			size_t n;
			while ((size_t)(value - line) < len && (*value == ' ' || *value == '\t')) value++;
			n = len - (size_t)(value - line);
			while (n && (value[n-1] == '\r' || value[n-1] == ' ' || value[n-1] == '\t')) n--;
			if (n >= outSize) n = outSize - 1;
			memcpy(out, value, n); out[n] = 0;
			return n > 0;
		}
		if (!end) break;
		p = end + 1;
	}
	return 0;
}

static int read_first_function_name(const char* text, char* out, size_t outSize)
{
	const char* p = text;
	while ((p = strstr(p, "function")) != NULL) {
		const char* q;
		size_t n = 0;
		if (p != text && (isalnum((unsigned char)p[-1]) || p[-1] == '_')) { p += 8; continue; }
		q = p + 8;
		while (*q == ' ' || *q == '\t' || *q == '\r' || *q == '\n') q++;
		if (!(isalpha((unsigned char)*q) || *q == '_')) { p += 8; continue; }
		while (isalnum((unsigned char)q[n]) || q[n] == '_') n++;
		if (q[n] != '(' || n == 0 || n >= outSize) { p += 8; continue; }
		memcpy(out, q, n); out[n] = 0;
		return 1;
	}
	return 0;
}

/* Reconstruct the gameplay handler collection from Carbon's readable
 * decompiler function name when there is no original blob or metadata.
 *
 * Example:
 *   race_bin_santafe_de_sf_1_2_stategraph_drive_to_target_driving_handler_notifytimer
 * becomes:
 *   race_bin_santafe/de_sf_1_2/stategraph_drive_to_target_driving_handler_notifytimer
 *
 * This rule is intentionally limited to race_bin_* stategraph handlers.  It is
 * unambiguous there because the gameplay root is race_bin_<region>, the owner
 * lies between that root and `_stategraph_`, and the remainder is the handler
 * collection name.  Other handler families still require --export/--handler or
 * an original sibling blob rather than guessing a runtime global.
 */
static int derive_race_bin_handler_from_function(const char* functionName,
	char* out, size_t outSize)
{
	const char* rootPrefix = "race_bin_";
	const char* regionEnd;
	const char* stategraph;
	const char* owner;
	size_t rootLen, ownerLen, suffixLen, needed;

	if (!functionName || !out || outSize == 0) return 0;
	if (strncmp(functionName, rootPrefix, strlen(rootPrefix)) != 0) return 0;
	if (strstr(functionName, "_handler_") == NULL) return 0;

	regionEnd = strchr(functionName + strlen(rootPrefix), '_');
	if (!regionEnd) return 0;
	stategraph = strstr(regionEnd + 1, "_stategraph_");
	if (!stategraph) return 0;

	owner = regionEnd + 1;
	rootLen = (size_t)(regionEnd - functionName);
	ownerLen = (size_t)(stategraph - owner);
	if (rootLen == 0 || ownerLen == 0) return 0;

	/* Skip the separator underscore before "stategraph_". */
	suffixLen = strlen(stategraph + 1);
	needed = rootLen + 1 + ownerLen + 1 + suffixLen;
	if (needed + 1 > outSize) return 0;

	memcpy(out, functionName, rootLen);
	out[rootLen] = '/';
	memcpy(out + rootLen + 1, owner, ownerLen);
	out[rootLen + 1 + ownerLen] = '/';
	memcpy(out + rootLen + 1 + ownerLen + 1, stategraph + 1, suffixLen);
	out[needed] = 0;
	return 1;
}

static int read_export_from_sibling_blob(const char* luaFilename, char* out, size_t outSize)
{
	char blobFilename[4096];
	FILE* f;
	unsigned char* data;
	long size;
	size_t i;
	if (!luaFilename || outSize < 11) return 0;
	if (strlen(luaFilename) < 5 || _stricmp(luaFilename + strlen(luaFilename) - 4, ".lua") != 0) return 0;
	if (strlen(luaFilename) - 4 >= sizeof(blobFilename)) return 0;
	memcpy(blobFilename, luaFilename, strlen(luaFilename) - 4);
	blobFilename[strlen(luaFilename) - 4] = 0;
	f = fopen(blobFilename, "rb");
	if (!f) return 0;
	fseek(f, 0, SEEK_END); size = ftell(f); fseek(f, 0, SEEK_SET);
	if (size <= 0) { fclose(f); return 0; }
	data = (unsigned char*)malloc((size_t)size);
	if (!data) { fclose(f); return 0; }
	if (fread(data, 1, (size_t)size, f) != (size_t)size) { free(data); fclose(f); return 0; }
	fclose(f);
	for (i = 0; i + 10 < (size_t)size; i++) {
		int j;
		if (data[i] != 'h' || data[i + 1] != '_') continue;
		for (j = 0; j < 8 && isxdigit((unsigned char)data[i + 2 + j]); j++) {}
		if (j == 8 && (data[i + 10] == 0 || !isalnum((unsigned char)data[i + 10]))) {
			memcpy(out, data + i, 10); out[10] = 0;
			free(data);
			return 1;
		}
	}
	free(data);
	return 0;
}

static int loadfile_with_handler_metadata(lua_State* L, const char* filename)
{
	size_t sourceSize = 0;
	char handler[1024] = {0}, functionName[1024] = {0}, exportName[64] = {0};
	char* source;
	char* combined;
	char alias[1152];
	char declaration[1152];
	char replacement[128];
	size_t combinedSize;
	int result;
	if (!filename) return luaL_loadfile(L, filename);
	source = read_text_file(filename, &sourceSize);
	if (!source) return luaL_loadfile(L, filename);
	if (!read_metadata_value(source, "-- function:", functionName, sizeof(functionName)) &&
		!read_first_function_name(source, functionName, sizeof(functionName))) {
		free(source);
		return luaL_loadfile(L, filename);
	}

	if (read_metadata_value(source, "-- export:", exportName, sizeof(exportName))) {
		int i, valid = (strlen(exportName) == 10 && exportName[0] == 'h' && exportName[1] == '_');
		for (i = 2; valid && i < 10; i++) if (!isxdigit((unsigned char)exportName[i])) valid = 0;
		if (!valid) { free(source); fatal("invalid -- export: metadata"); }
	}
	else if (read_metadata_value(source, "-- handler:", handler, sizeof(handler))) {
		sprintf(exportName, "h_%08X", vlt_hash32(handler));
	}
	else if (read_export_from_sibling_blob(filename, exportName, sizeof(exportName))) {
		/* Normal decompile -> edit -> compile path.  luadec intentionally keeps
		 * the source clean, so recover the exact export from the original blob
		 * sitting next to <blob>.lua. */
	}
	else if (derive_race_bin_handler_from_function(functionName, handler, sizeof(handler))) {
		/* New Carbon gameplay handler with no source metadata and no original
		 * sibling blob.  Derive the collection path from the canonical readable
		 * race_bin_* function name and emit the runtime h_XXXXXXXX global. */
		sprintf(exportName, "h_%08X", vlt_hash32(handler));
	}
	else {
		/* Never silently compile a handler-looking function as a friendly global:
		 * Carbon's message dispatcher resolves h_XXXXXXXX, and accepting the long
		 * name here creates bytecode that parses successfully but is wrong at
		 * runtime. */
		if (strstr(functionName, "_handler_") != NULL) {
			free(source);
			fatal("cannot resolve Carbon handler export; use --export/--handler metadata or a race_bin_* canonical function name");
		}
		free(source);
		return luaL_loadfile(L, filename);
	}

	/* Compile the readable declaration directly as the original h_XXXXXXXX
	 * assignment.  This keeps the file pleasant to edit while restoring the
	 * original top-level bytecode shape (CLOSURE + SETGLOBAL) instead of adding
	 * an extra friendly global and a second alias assignment. */
	sprintf(declaration, "function %s(", functionName);
	sprintf(replacement, "%s = function(", exportName);
	{
		char* decl = strstr(source, declaration);
		if (decl) {
			size_t before = (size_t)(decl - source);
			size_t declLen = strlen(declaration);
			size_t replLen = strlen(replacement);
			combinedSize = sourceSize - declLen + replLen;
			combined = (char*)malloc(combinedSize + 1);
			if (!combined) { free(source); fatal("out of memory while restoring handler export"); }
			memcpy(combined, source, before);
			memcpy(combined + before, replacement, replLen);
			memcpy(combined + before + replLen, decl + declLen, sourceSize - before - declLen);
			combined[combinedSize] = 0;
		}
		else {
			/* Compatibility path for older hand-edited sources that do not use the
			 * friendly `function name(...)` declaration. */
			sprintf(alias, "\n%s = %s\n", exportName, functionName);
			combinedSize = sourceSize + strlen(alias);
			combined = (char*)malloc(combinedSize + 1);
			if (!combined) { free(source); fatal("out of memory while adding handler export"); }
			memcpy(combined, source, sourceSize);
			memcpy(combined + sourceSize, alias, strlen(alias) + 1);
		}
	}
	result = luaL_loadbuffer(L, combined, combinedSize, filename);
	free(combined);
	free(source);
	return result;
}

static void fatal(const char* message)
{
	fprintf(stderr, "%s: %s\n", progname, message);
	exit(EXIT_FAILURE);
}

static void cannot(const char* name, const char* what, const char* mode)
{
	fprintf(stderr, "%s: cannot %s %sput file ", progname, what, mode);
	perror(name);
	exit(EXIT_FAILURE);
}

static void usage(const char* message, const char* arg)
{
	if (message != NULL)
	{
		fprintf(stderr, "%s: ", progname); fprintf(stderr, message, arg); fprintf(stderr, "\n");
	}
	fprintf(stderr,
		"usage: %s [options] [filenames].  Available options are:\n"
		"  -        process stdin\n"
		"  -l       list\n"
		"  -o name  output to file `name' (default is \"" OUTPUT "\")\n"
		"  -p       parse only\n"
		"  -s       strip debug information in dump\n"
		"  -v       show "PROGNAME" version\n"
		"  --       stop handling options\n",
		progname);
	exit(EXIT_FAILURE);
}

#define	IS(s)	(strcmp(argv[i],s)==0)

static int doargs(int argc, char* argv[])
{
	int i;
	if (argv[0] != NULL && *argv[0] != 0) progname = argv[0];
	for (i = 1; i < argc; i++)
	{
		if (*argv[i] != '-')			/* end of options; keep it */
			break;
		else if (IS("--"))			/* end of options; skip it */
		{
			++i;
			break;
		}
		else if (IS("-"))			/* end of options; use stdin */
			return i;
		else if (IS("-l"))			/* list */
			listing = 1;
		else if (IS("-o"))			/* output file */
		{
			output = argv[++i];
			if (output == NULL || *output == 0) usage("`-o' needs argument", NULL);
		}
		else if (IS("-p"))			/* parse only */
			dumping = 0;
		else if (IS("-s"))			/* strip debug information */
			stripping = 1;
		else if (IS("-v"))			/* show version */
		{
			printf("%s  %s\n", LUA_VERSION, LUA_COPYRIGHT);
			if (argc == 2) exit(EXIT_SUCCESS);
		}
		else					/* unknown option */
			usage("unrecognized option `%s'", argv[i]);
	}
	if (i == argc && (listing || !dumping))
	{
		dumping = 0;
		argv[--i] = Output;
	}
	return i;
}

static Proto* toproto(lua_State* L, int i)
{
	const Closure* c = (const Closure*)lua_topointer(L, i);
	return c->l.p;
}

static Proto* combine(lua_State* L, int n)
{
	if (n == 1)
		return toproto(L, -1);
	else
	{
		int i, pc = 0;
		Proto* f = luaF_newproto(L);
		f->source = luaS_newliteral(L, "=(" PROGNAME ")");
		f->maxstacksize = 1;
		f->p = luaM_newvector(L, n, Proto*);
		f->sizep = n;
		f->sizecode = 2 * n + 1;
		f->code = luaM_newvector(L, f->sizecode, Instruction);
		for (i = 0; i < n; i++)
		{
			f->p[i] = toproto(L, i - n);
			f->code[pc++] = CREATE_ABx(OP_CLOSURE, 0, i);
			f->code[pc++] = CREATE_ABC(OP_CALL, 0, 1, 1);
		}
		f->code[pc++] = CREATE_ABC(OP_RETURN, 0, 1, 0);
		return f;
	}
}

static void strip(lua_State* L, Proto* f)
{
	int i, n = f->sizep;
	luaM_freearray(L, f->lineinfo, f->sizelineinfo, int);
	luaM_freearray(L, f->locvars, f->sizelocvars, struct LocVar);
	luaM_freearray(L, f->upvalues, f->sizeupvalues, TString*);
	f->lineinfo = NULL; f->sizelineinfo = 0;
	f->locvars = NULL;  f->sizelocvars = 0;
	f->upvalues = NULL; f->sizeupvalues = 0;
	f->source = luaS_newliteral(L, "=(none)");
	for (i = 0; i < n; i++) strip(L, f->p[i]);
}

static int writer(lua_State* L, const void* p, size_t size, void* u)
{
	UNUSED(L);
	return fwrite(p, size, 1, (FILE*)u) == 1;
}

int main(int argc, char* argv[])
{
	lua_State* L;
	Proto* f;
	int i = doargs(argc, argv);
	argc -= i; argv += i;
	if (argc <= 0) usage("no input files given", NULL);
	L = lua_open();
	luaB_opentests(L);
	for (i = 0; i < argc; i++)
	{
		const char* filename = IS("-") ? NULL : argv[i];
			if (loadfile_with_handler_metadata(L, filename) != 0) fatal(lua_tostring(L, -1));
	}
	f = combine(L, argc);
	if (listing) luaU_print(f);
	if (dumping)
	{
		FILE* D = fopen(output, "wb");
		if (D == NULL) cannot(output, "open", "out");
		if (stripping) strip(L, f);
		lua_lock(L);
		luaU_dump(L, f, writer, D);
		lua_unlock(L);
		if (ferror(D)) cannot(output, "write", "out");
		fclose(D);
	}
	lua_close(L);
	return 0;
}
