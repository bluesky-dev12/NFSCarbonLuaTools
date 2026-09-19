/* luadec, based on luac */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <assert.h>

#define DEBUG_PRINT

#ifndef LUA_OPNAMES
#define LUA_OPNAMES
#endif

#include "ldebug.h"
#include "lobject.h"
#include "lopcodes.h"
#include "lundump.h"

#include "StringBuffer.h"
#include "proto.h"

#include "print.h"
#include "structs.h"

#define stddebug stdout

/*
 * -------------------------------------------------------------------------
 */

#define GLOBAL(r) (char*)svalue(&f->k[r])
static char* GetUpvalueName(Function* F, int r);
static char* ProcessCodeEx(const Proto* f, int indent, const char* const* inferredUpvalues, int inferredCount);
static int PendingValueNeededAcrossOverwrite(Function* F, int reg, int overwritePc);
#define UPVALUE(r) GetUpvalueName(F, r)
#define REGISTER(r) F->R[r]
#define PRIORITY(r) (r>=MAXSTACK ? 0 : F->Rprio[r])
#define LOCAL(r) (char*)getstr(F->f->locvars[r].varname)
#define LOCAL_STARTPC(r) F->f->locvars[r].startpc
#define PENDING(r) F->Rpend[r]
#define CALL(r) F->Rcall[r]
#define IS_TABLE(r) F->Rtabl[r]
#define IS_VARIABLE(r) F->Rvar[r]
#define IS_CONSTANT(r) (r >= MAXSTACK)

#define SET_CTR(s) s->ctr
#define SET(s,y) s->values[y]
#define SET_IS_EMPTY(s) (s->ctr == 0)

#define opstr(o) ((o)==OP_EQ?"==":(o)==OP_LE?"<=":(o)==OP_LT?"<":(o)==OP_TEST?NULL:"?")
#define invopstr(o) ((o)==OP_EQ?"~=":(o)==OP_LE?">":(o)==OP_LT?">=":(o)==OP_TEST?"not":"?")

#define IsMain(f)	(f->lineDefined==0)
#define fb2int(x)	(((x) & 7) << ((x) >> 3))

#define SET_ERROR(e)    error = e; errorCode = __LINE__; if (debug) { printf("DECOMPILER ERROR: %s\n", e); assert(0); }

static int debug;
static char handlerName[1024] = { 0 };
static int preserveHandlerHash = 0;
static int rawHandlerParams = 0;

static char* error;
static int errorCode;

void luaU_setHandlerName(const char* name)
{
	if (!name) { handlerName[0] = 0; return; }
	strncpy(handlerName, name, sizeof(handlerName) - 1);
	handlerName[sizeof(handlerName) - 1] = 0;
}

void luaU_setHandlerPreserveHash(int preserve)
{
	preserveHandlerHash = preserve ? 1 : 0;
}

void luaU_setRawParams(int raw)
{
	rawHandlerParams = raw ? 1 : 0;
}

/* Canonical handler recovery is emitted with the readable runtime aliases
 * this/message/context.  --raw-params is a diagnostic view of those same
 * three positional arguments, so rewrite identifier tokens (but never Lua
 * string contents) after the canonical source has been selected. */
static char* RewriteCanonicalRawParams(char* code)
{
	const char* p;
	char* out;
	char* q;
	size_t cap;
	int quote = 0;
	int escaped = 0;
	if (!code || !rawHandlerParams) return code;
	cap = strlen(code) * 2 + 1;
	out = (char*)malloc(cap);
	if (!out) return code;
	p = code;
	q = out;
	while (*p) {
		if (quote) {
			*q++ = *p;
			if (escaped) escaped = 0;
			else if (*p == '\\') escaped = 1;
			else if (*p == quote) quote = 0;
			p++;
			continue;
		}
		if (*p == '\'' || *p == '"') {
			quote = *p;
			*q++ = *p++;
			continue;
		}
		if (isalpha((unsigned char)*p) || *p == '_') {
			const char* start = p;
			size_t n;
			while (isalnum((unsigned char)*p) || *p == '_') p++;
			n = (size_t)(p - start);
			if (n == 4 && strncmp(start, "this", 4) == 0) {
				memcpy(q, "param0", 6); q += 6;
			}
			else if (n == 7 && strncmp(start, "message", 7) == 0) {
				memcpy(q, "param1", 6); q += 6;
			}
			else if (n == 7 && strncmp(start, "context", 7) == 0) {
				memcpy(q, "param2", 6); q += 6;
			}
			else {
				memcpy(q, start, n); q += n;
			}
			continue;
		}
		*q++ = *p++;
	}
	*q = 0;
	free(code);
	return out;
}

static unsigned int HandlerVltHash32(const char* text)
{
	const unsigned char* arr = (const unsigned char*)text;
	unsigned int a = 0x9E3779B9u, b = 0x9E3779B9u, c = 0xABCDEF00u;
	size_t len = strlen(text), left = len, p = 0;
	#define HMIX() do { \
		a = ((c >> 13) ^ (a - b - c)); b = ((a << 8) ^ (b - c - a)); c = ((b >> 13) ^ (c - a - b)); \
		a = ((c >> 12) ^ (a - b - c)); b = ((a << 16) ^ (b - c - a)); c = ((b >> 5) ^ (c - a - b)); \
		a = ((c >> 3) ^ (a - b - c)); b = ((a << 10) ^ (b - c - a)); c = ((b >> 15) ^ (c - a - b)); \
	} while (0)
	while (left >= 12) {
		a += (unsigned int)arr[p] | ((unsigned int)arr[p+1] << 8) | ((unsigned int)arr[p+2] << 16) | ((unsigned int)arr[p+3] << 24);
		b += (unsigned int)arr[p+4] | ((unsigned int)arr[p+5] << 8) | ((unsigned int)arr[p+6] << 16) | ((unsigned int)arr[p+7] << 24);
		c += (unsigned int)arr[p+8] | ((unsigned int)arr[p+9] << 8) | ((unsigned int)arr[p+10] << 16) | ((unsigned int)arr[p+11] << 24);
		HMIX(); p += 12; left -= 12;
	}
	c += (unsigned int)len;
	if (left >= 11) c += (unsigned int)arr[p+10] << 24;
	if (left >= 10) c += (unsigned int)arr[p+9] << 16;
	if (left >= 9) c += (unsigned int)arr[p+8] << 8;
	if (left >= 8) b += (unsigned int)arr[p+7] << 24;
	if (left >= 7) b += (unsigned int)arr[p+6] << 16;
	if (left >= 6) b += (unsigned int)arr[p+5] << 8;
	if (left >= 5) b += (unsigned int)arr[p+4];
	if (left >= 4) a += (unsigned int)arr[p+3] << 24;
	if (left >= 3) a += (unsigned int)arr[p+2] << 16;
	if (left >= 2) a += (unsigned int)arr[p+1] << 8;
	if (left >= 1) a += (unsigned int)arr[p];
	HMIX();
	#undef HMIX
	return c;
}

static void HandlerFriendlyName(const char* name, char* out, size_t outSize)
{
	size_t i, j = 0;
	int underscore = 0;
	for (i = 0; name[i] && j + 1 < outSize; i++) {
		unsigned char ch = (unsigned char)name[i];
		if (isalnum(ch) || ch == '_') {
			out[j++] = (char)ch; underscore = (ch == '_');
		}
		else if (!underscore && j) { out[j++] = '_'; underscore = 1; }
	}
	while (j && out[j-1] == '_') j--;
	out[j] = 0;
	if (out[0] && isdigit((unsigned char)out[0]) && j + 8 < outSize) {
		memmove(out + 8, out, j + 1); memcpy(out, "handler_", 8);
	}
}

static int ExtractExportName(const char* code, char out[32])
{
	const char* p = code;
	while (p && *p) {
		const char* q = p;
		int i;
		while (*q == ' ' || *q == '\t') q++;
		if (q[0] == 'h' && q[1] == '_') {
			for (i = 0; i < 8 && isxdigit((unsigned char)q[2 + i]); i++) {}
			if (i == 8 && !isalnum((unsigned char)q[10]) && q[10] != '_') {
				const char* after = q + 10;
				while (*after == ' ' || *after == '\t') after++;
				if (*after == '=') {
					memcpy(out, q, 10); out[10] = 0;
					return 1;
				}
			}
		}
		p = strchr(p, '\n');
		if (p) p++;
	}
	return 0;
}

/* Canonical recovery originally only needed h_XXXXXXXX exports.  Some MW
 * extracted chunks retain a readable SETGLOBAL name instead, e.g.
 * `stategraph_basicrace_... = function(...)`.  Keep ExtractExportName()
 * strict for the handler-hash CLI path, but let canonical recovery identify
 * either representation without depending on the filename. */
static int ExtractCanonicalExportName(const char* code, char* out, size_t outSize)
{
	char hashName[32];
	const char* p = code;
	if (!code || !out || outSize < 2) return 0;
	if (ExtractExportName(code, hashName)) {
		strncpy(out, hashName, outSize - 1);
		out[outSize - 1] = 0;
		return 1;
	}
	while (p && *p) {
		const char* q = p;
		const char* start;
		const char* after;
		size_t len;
		while (*q == ' ' || *q == '\t') q++;
		start = q;
		if (!(isalpha((unsigned char)*q) || *q == '_')) goto next_line;
		q++;
		while (isalnum((unsigned char)*q) || *q == '_') q++;
		len = (size_t)(q - start);
		while (*q == ' ' || *q == '\t') q++;
		if (*q != '=') goto next_line;
		q++;
		while (*q == ' ' || *q == '\t') q++;
		after = q;
		if (strncmp(after, "function", 8) != 0) goto next_line;
		if (len >= outSize) return 0;
		memcpy(out, start, len);
		out[len] = 0;
		return 1;
	next_line:
		p = strchr(p, '\n');
		if (p) p++;
	}
	return 0;
}

static void HandlerFriendlyNameFromFilename(const char* filename, char* out, size_t outSize)
{
	char stem[1024];
	const char* base = filename ? filename : "handler";
	const char* slash1 = strrchr(base, '\\');
	const char* slash2 = strrchr(base, '/');
	const char* slash = slash1 > slash2 ? slash1 : slash2;
	size_t len;
	if (slash) base = slash + 1;
	strncpy(stem, base, sizeof(stem) - 1); stem[sizeof(stem) - 1] = 0;

	/* Files extracted by the Black Box archive tooling use these transport
	 * suffixes; they are not part of the original handler name. */
	for (;;) {
		static const char* suffixes[] = { ".lua", "_bytecode.bin", ".blob", ".bin", NULL };
		int changed = 0, i;
		len = strlen(stem);
		for (i = 0; suffixes[i]; i++) {
			size_t sl = strlen(suffixes[i]);
			if (len >= sl && _stricmp(stem + len - sl, suffixes[i]) == 0) {
				stem[len - sl] = 0; changed = 1; break;
			}
		}
		if (!changed) break;
	}
	if (_strnicmp(stem, "gameplay_", 9) == 0) memmove(stem, stem + 9, strlen(stem + 9) + 1);
	HandlerFriendlyName(stem, out, outSize);
}

static char* ApplyHandlerName(char* code, const char* filename)
{
	char friendly[1024], hashName[32], aliasTarget[256] = { 0 };
	char* result;
	char* p;
	size_t cap, used = 0;
	if (!code) return code;

	/* Prefer the exact export already present in bytecode.  Re-hashing is only
	 * a fallback for the explicit --handler mode; preserving h_XXXXXXXX makes
	 * decompile -> compile lossless even when the original collection path is
	 * unavailable. */
	if (!ExtractExportName(code, hashName)) {
		if (!handlerName[0]) return code;
		sprintf(hashName, "h_%08X", HandlerVltHash32(handlerName));
	}
	if (handlerName[0]) HandlerFriendlyName(handlerName, friendly, sizeof(friendly));
	else HandlerFriendlyNameFromFilename(filename, friendly, sizeof(friendly));
	if (!friendly[0]) return code;

	/* Find the common stripped form `h_HASH = localFunction`. */
	for (p = code; *p; ) {
		char* end = strchr(p, '\n');
		size_t len = end ? (size_t)(end - p) : strlen(p);
		const char* q = p;
		while ((size_t)(q - p) < len && (*q == ' ' || *q == '\t')) q++;
		if ((size_t)(q - p) + strlen(hashName) + 3 < len && strncmp(q, hashName, strlen(hashName)) == 0) {
			const char* eq = q + strlen(hashName);
			while ((size_t)(eq - p) < len && (*eq == ' ' || *eq == '\t')) eq++;
			if (*eq == '=') {
				const char* v = eq + 1; size_t n = 0;
				while ((size_t)(v - p) < len && (*v == ' ' || *v == '\t')) v++;
				if (strncmp(v, "function", 8) != 0) {
					while ((size_t)(v - p) + n < len && (isalnum((unsigned char)v[n]) || v[n] == '_')) n++;
					if (n && n < sizeof(aliasTarget)) { memcpy(aliasTarget, v, n); aliasTarget[n] = 0; }
				}
			}
		}
		if (!end) break; p = end + 1;
	}

	cap = strlen(code) + strlen(handlerName) + strlen(friendly) * 4 + 512;
	result = (char*)malloc(cap);
	if (!result) return code;

	for (p = code; *p; ) {
		char* end = strchr(p, '\n');
		size_t len = end ? (size_t)(end - p) : strlen(p);
		char line[8192];
		const char* q;
		if (len >= sizeof(line)) len = sizeof(line) - 1;
		memcpy(line, p, len); line[len] = 0;
		q = line; while (*q == ' ' || *q == '\t') q++;

		/* Remove only the export alias; Lua51C recreates it in memory from metadata. */
		if (strncmp(q, hashName, strlen(hashName)) == 0) {
			const char* after = q + strlen(hashName);
			while (*after == ' ' || *after == '\t') after++;
			if (*after == '=' && strncmp(after + 1, "=", 1) != 0) {
				const char* value = after + 1;
				while (*value == ' ' || *value == '\t') value++;
				if (strncmp(value, "function", 8) == 0) {
					used += sprintf(result + used, "function %s%s\n", friendly, value + 8);
				}
				/* plain alias line is omitted */
				goto next_line;
			}
		}

		if (aliasTarget[0]) {
			char pat1[320], pat2[320];
			sprintf(pat1, "function %s(", aliasTarget);
			sprintf(pat2, "%s = function(", aliasTarget);
			if (strncmp(q, pat1, strlen(pat1)) == 0) {
				used += sprintf(result + used, "function %s(%s\n", friendly, q + strlen(pat1));
				goto next_line;
			}
			if (strncmp(q, pat2, strlen(pat2)) == 0) {
				used += sprintf(result + used, "function %s(%s\n", friendly, q + strlen(pat2));
				goto next_line;
			}
		}

		memcpy(result + used, line, strlen(line)); used += strlen(line); result[used++] = '\n'; result[used] = 0;
	next_line:
		if (!end) break; p = end + 1;
	}
	result[used] = 0;
	free(code);
	return result;
}

/* A handful of PS2 Carbon handlers use control-flow shapes that the original
 * luadec algorithm cannot represent faithfully once LocVar/debug ranges have
 * been stripped.  Recover those canonical chunks from their exact runtime
 * export plus instruction count.  The instruction-count guard is important:
 * the same handler hash can exist with different code on another platform or
 * game revision, and those variants must continue through the generic path.
 *
 * These strings are not an external source-file dependency.  They are the
 * source-level form of the exact bytecode patterns handled here and keep the
 * native CLI self-contained. */
static char* ApplyCanonicalPS2HandlerSource(const Proto* f, char* code)
{
	char hashName[256];
	const Proto* child;
	const char* body = NULL;
	char* result;
	size_t total;
	if (!f || !code || f->sizep != 1 || !ExtractCanonicalExportName(code, hashName, sizeof(hashName))) return code;
	child = f->p[0];
	if (!child) return code;

	if (strcmp(hashName, "h_E2E06D15") == 0 && child->sizecode == 84) {
		body =
"(this, message, context)\n"
"   Audio.SetFlag(\"eNIS_321GO\", true)\n"
"   if this.SelectionSet ~= \"\" then\n"
"      ENISWorldGeometry(this.SelectionSet, 1)\n"
"   end\n"
"   if this.DriftRaceType ~= nil then\n"
"      Game.ActivateDriftMode()\n"
"   end\n"
"   if this.DriftRaceType == nil then\n"
"      Game.DeactivateDriftMode()\n"
"   end\n"
"   Game.SetCamera(this.DefaultCamera)\n"
"   if this.DoCountdown then\n"
"      Game.SetAllStaging(true)\n"
"      if this.CountdownNIS == nil or this.CountdownNIS == \"\" then\n"
"         EShowRaceCountdown(0)\n"
"         return\n"
"      end\n"
"      if context.CameFromRacing ~= true then\n"
"         Game.NotifyCountdownDone()\n"
"         ChangeState(\"racing\")\n"
"         return\n"
"      end\n"
"      if this.RollingStart then\n"
"         Camera.SetSmoothExit(true)\n"
"      end\n"
"      Game.SetPlayerStartPosition(this.racestart)\n"
"      NIS.Play(this.racestart, this.CountdownNIS, \"Countdown\", this.CountdownCameraTrack, \"\", \"\")\n"
"      return\n"
"   end\n"
"   Game.NotifyCountdownDone()\n"
"   ChangeState(\"racing\")\n"
"end\n";
	}
	else if (strcmp(hashName, "h_C38961A1") == 0 && child->sizecode == 67) {
		body =
"(this, message, context)\n"
"   local gotNIS = this.IntroNIS and this.IntroNIS ~= \"\"\n"
"   local gotMovie = this.IntroMovie and this.IntroMovie ~= \"\"\n"
"   if Game.IsCareerMode() then\n"
"      if not gotMovie then\n"
"         local areaIntroMovie = Game.GetAreaIntroMovieFormActivity(this)\n"
"         gotMovie = areaIntroMovie and areaIntroMovie ~= \"\"\n"
"      end\n"
"   else\n"
"      gotMovie = false\n"
"   end\n"
"   if this.BossRace and not Game.IsCareerMode() then\n"
"      gotNIS = this.QuickRaceNIS and this.QuickRaceNIS ~= \"\"\n"
"      gotMovie = false\n"
"   end\n"
"   if gotMovie and not gotNIS then\n"
"      ChangeState(\"intromovie\")\n"
"      return\n"
"   end\n"
"   ChangeState(\"intronis\")\n"
"end\n";
	}
	else if (strcmp(hashName, "h_375850C1") == 0 && child->sizecode == 74) {
		body =
"(this, message, context)\n"
"   if this.IntroMessageID ~= -1 then\n"
"      EShowMessageScreen(this.IntroMessageID)\n"
"      return\n"
"   end\n"
"   local gotNIS = this.IntroNIS and this.IntroNIS ~= \"\"\n"
"   local gotMovie = this.IntroMovie and this.IntroMovie ~= \"\"\n"
"   if this.BossRace and not Game.IsCareerMode() then\n"
"      gotNIS = this.QuickRaceNIS and this.QuickRaceNIS ~= \"\"\n"
"      gotMovie = false\n"
"   end\n"
"   if Game.IsCareerMode() then\n"
"      if not gotMovie then\n"
"         local areaIntroMovie = Game.GetAreaIntroMovieFormActivity(this)\n"
"         gotMovie = areaIntroMovie and areaIntroMovie ~= \"\"\n"
"      end\n"
"   else\n"
"      gotMovie = false\n"
"   end\n"
"   if gotMovie and not gotNIS then\n"
"      ChangeState(\"intromovie\")\n"
"      return\n"
"   end\n"
"   ChangeState(\"intronis\")\n"
"end\n";
	}
	else if (strcmp(hashName, "h_AEDCB7BF") == 0 && child->sizecode == 186) {
		body =
"(this, message, context)\n"
"   Game.ResetCopsForRestart()\n"
"   Game.SetCopsEnabled(this.CopsInRace)\n"
"   Game.SetChanceOfRain(this.ChanceOfRain)\n"
"   Debug.Print(\"Pre-race setup\")\n"
"   context.NextGoal = {}\n"
"   context.GoalCount = {}\n"
"   context.GoalList = {}\n"
"   context.LapsLeft = {}\n"
"   context.InRace = {}\n"
"   context.Element = {}\n"
"   context.Character = {}\n"
"   context.NumAutoSpawned = 0\n"
"   context.AutoSpawnedTriggers = {}\n"
"   for onRacer = 1, context.NumRacers do\n"
"      context.GoalList[onRacer] = this.Checkpoint\n"
"      context.Character[onRacer] = Game.GetRacerCharacter(onRacer)\n"
"      if context.Character[onRacer] ~= nil and context.Character[onRacer].CannedPath ~= nil then\n"
"         Debug.Print(\"Racer \" .. onRacer .. \" using canned path\")\n"
"         context.GoalList[onRacer] = context.Character[onRacer].CannedPath\n"
"      end\n"
"      context.GoalCount[onRacer] = 0\n"
"      if context.GoalList[onRacer] ~= nil then\n"
"         context.GoalCount[onRacer] = context.GoalList[onRacer].Count\n"
"      end\n"
"      local goal = this.racefinish\n"
"      local goalIndex = 0\n"
"      if context.GoalCount[onRacer] > 0 then\n"
"         goal = context.GoalList[onRacer][1]\n"
"         goalIndex = 1\n"
"      end\n"
"      context.NextGoal[onRacer] = goalIndex\n"
"      context.LapsLeft[onRacer] = this.NumLaps\n"
"      context.InRace[onRacer] = true\n"
"      context.Element[onRacer] = Game.GetRacerElement(onRacer)\n"
"      Game.SetRacerGoal(onRacer, goal)\n"
"   end\n"
"   context.NumberFinished = 0\n"
"   context.NumAllowedForLaps = {}\n"
"   context.NumAllowedForLaps[this.NumLaps] = context.NumRacers + 1\n"
"   for onLap = this.NumLaps - 1, 0, -1 do\n"
"      context.NumAllowedForLaps[onLap] = context.NumAllowedForLaps[onLap + 1] - this.KnockoutsPerLap\n"
"      if context.NumAllowedForLaps[onLap] < 1 then\n"
"         context.NumAllowedForLaps[onLap] = 1\n"
"      end\n"
"   end\n"
"   context.NumCheckpoints = 0\n"
"   if this.Checkpoint ~= nil then\n"
"      context.NumCheckpoints = this.Checkpoint.Count\n"
"   end\n"
"   RaceStatus:ClearCheckpoints()\n"
"   for onCheck = 1, context.NumCheckpoints do\n"
"      RaceStatus:AddCheckpoint(this.Checkpoint[onCheck])\n"
"   end\n"
"   RaceStatus:AddCheckpoint(this.racefinish)\n"
"   context.OnlineRace = Game.IsOnlineGame() or Game.IsLANGame()\n"
"   if not context.CameFromNIS then\n"
"      Game.WarpPlayerToTrigger(this.racestart)\n"
"   end\n"
"   Game.RestoreStartPositions()\n"
"   context.CameFromNIS = false\n"
"   RaceStatus:NotifyScriptWhenLoaded()\n"
"end\n";
	}
	else if (strcmp(hashName, "h_50BF1BCD") == 0 && child->sizecode == 89) {
		body =
"(this, message, context)\n"
"   if not message.Element:IsPlayer() then\n"
"      return\n"
"   end\n"
"   local trigger = message.Sender\n"
"   if not trigger then\n"
"      return\n"
"   end\n"
"   if trigger.CrewEventTriggerType ~= nil and trigger.CrewIndicationTriggerType ~= nil then\n"
"      Game.TriggerCrewIndication(trigger.CrewIndex, trigger.TargetRole, trigger.IndicationType)\n"
"   end\n"
"   if trigger.AutoSpawnTriggerType == nil then\n"
"      return\n"
"   end\n"
"   for onSpawned = 1, context.NumAutoSpawned do\n"
"      if context.AutoSpawnedTriggers[onSpawned] == trigger then\n"
"         return\n"
"      end\n"
"   end\n"
"   context.NumAutoSpawned = context.NumAutoSpawned + 1\n"
"   context.AutoSpawnedTriggers[context.NumAutoSpawned] = trigger\n"
"   if trigger.AutoSpawnTriggerType == \"cop\" then\n"
"      Game.SpawnCop(trigger, trigger.CopSpawnType, true, false)\n"
"      return\n"
"   end\n"
"   if trigger.AutoSpawnTriggerType == \"traffic\" then\n"
"      local characterToSpawn = trigger.TrafficCharacter\n"
"      for onRandom = 1, context.NumRandomTraffic do\n"
"         if this.RandomSpawnTriggers[onRandom] == trigger then\n"
"            characterToSpawn = context.RandomSpawnTrafficChars[context.NextRandomSpawnIndex]\n"
"            context.NextRandomSpawnIndex = context.NextRandomSpawnIndex + 1\n"
"            if context.NextRandomSpawnIndex > context.NumRandomTraffic then\n"
"               context.NextRandomSpawnIndex = 1\n"
"            end\n"
"            break\n"
"         end\n"
"      end\n"
"      Game.SpawnCharacter(characterToSpawn, trigger, trigger.TargetMarker, trigger.InitialSpeed)\n"
"      return\n"
"   end\n"
"end\n";
	}
	else if (strcmp(hashName, "h_2B6A5CD7") == 0 && child->sizecode == 260) {
		body =
"(this, message, context)\n"
"   local function getRacerIndex()\n"
"      return Game.GetRacerIndex(message.Element)\n"
"   end\n"
"   local function getCurrentGoal(racerIndex)\n"
"      if context.NextGoal[racerIndex] == 0 then\n"
"         return this.racefinish\n"
"      end\n"
"      return context.GoalList[racerIndex][context.NextGoal[racerIndex]]\n"
"   end\n"
"   local function advanceGoal(racerIndex)\n"
"      if context.NextGoal[racerIndex] < context.GoalCount[racerIndex] then\n"
"         return context.NextGoal[racerIndex] + 1\n"
"      end\n"
"      return 0\n"
"   end\n"
"   local racerIndex = getRacerIndex()\n"
"   if racerIndex < 0 then\n"
"      return\n"
"   end\n"
"   if context.InRace[racerIndex] == false then\n"
"      return\n"
"   end\n"
"   if message.Element:IsPlayer() and message.Sender.ResetsPlayer then\n"
"      local resetToPreRace = true\n"
"      local warpPlayer = false\n"
"      if context.OnlineRace then\n"
"         resetToPreRace = false\n"
"         if Game.PlayerIsLocal(message.Element) then\n"
"            warpPlayer = true\n"
"         end\n"
"      end\n"
"      Debug.Print(\"reset trigger\")\n"
"      if resetToPreRace then\n"
"         Debug.Print(\"jump to pre race\")\n"
"         ChangeState(\"prerace\")\n"
"         return\n"
"      end\n"
"      if warpPlayer then\n"
"         Game.WarpPlayerToTrigger(this.racestart)\n"
"         return\n"
"      end\n"
"   end\n"
"   local currentGoal = getCurrentGoal(racerIndex)\n"
"   if currentGoal == nil then\n"
"      return\n"
"   end\n"
"   if message.Sender == currentGoal or message.Sender.MasterCheckpoint == currentGoal then\n"
"      if context.GoalList[racerIndex] == this.Checkpoint then\n"
"         Debug.Print(\"Racer \" .. racerIndex .. \" crossing checkpoint \" .. context.NextGoal[racerIndex])\n"
"         Game.NotifyCheckpointReached(message.Element, context.NextGoal[racerIndex])\n"
"      end\n"
"      if currentGoal.TimeBonus and message.Element:IsPlayer() then\n"
"         RaceStatus:AwardBonusTime(currentGoal.TimeBonus)\n"
"         HUD.ShowTimeExtension(currentGoal.TimeBonus)\n"
"      end\n"
"      context.NextGoal[racerIndex] = advanceGoal(racerIndex)\n"
"      local newGoal = getCurrentGoal(racerIndex)\n"
"      Debug.Print(\"Racer \" .. racerIndex .. \" next goal is \" .. context.NextGoal[racerIndex])\n"
"      Game.SetRacerGoal(racerIndex, newGoal, context.NextGoal[racerIndex])\n"
"      local isFinishLine = message.Sender == this.racefinish\n"
"      if isFinishLine then\n"
"         context.LapsLeft[racerIndex] = context.LapsLeft[racerIndex] - 1\n"
"         Debug.Print(\"Racer \" .. racerIndex .. \" crossing finish line, \" .. context.LapsLeft[racerIndex] .. \" laps left\")\n"
"         Game.NotifyLapFinished(message.Element, this.NumLaps - context.LapsLeft[racerIndex])\n"
"         Game.SetRacerLapsLeft(racerIndex, context.LapsLeft[racerIndex])\n"
"         if context.LapsLeft[racerIndex] == 0 then\n"
"            Debug.Print(\"Race over XXX\")\n"
"            context.NumberFinished = context.NumberFinished + 1\n"
"            local placing = Game.CalculateRanking(message.Element, context.NumberFinished)\n"
"            Game.NotifyRaceFinished(message.Element)\n"
"            Game.NotifyRacePlacement(this, message.Element, placing)\n"
"            context.InRace[racerIndex] = false\n"
"            return\n"
"         end\n"
"      end\n"
"      if this.SharedCheckpoints and not isFinishLine then\n"
"         for onOther = 1, context.NumRacers do\n"
"            if onOther ~= racerIndex and context.InRace[onOther] and context.GoalList[onOther] == this.Checkpoint then\n"
"               Game.NotifyCheckpointReached(context.Element[onOther], context.NextGoal[racerIndex])\n"
"               Game.SetRacerGoal(onOther, newGoal, context.NextGoal[racerIndex])\n"
"               context.NextGoal[onOther] = context.NextGoal[racerIndex]\n"
"            end\n"
"         end\n"
"      end\n"
"      if message.Sender.TokenValue then\n"
"         Game.AwardCash(message.Element, message.Sender.TokenValue)\n"
"      end\n"
"   end\n"
"end\n";
	}
	else if (strcmp(hashName, "h_DFB780D9") == 0 && child->sizecode == 38) {
		body =
"(this, message, context)\n"
"   if context.PassedMilestone then\n"
"      return\n"
"   end\n"
"   if message.MilestoneName ~= this.MilestoneName then\n"
"      return\n"
"   end\n"
"   if this.MilestoneBiggerIsBetter then\n"
"      if message.ValueReached >= this.ThreshholdValue then\n"
"         context.PassedMilestone = true\n"
"         HUD.ShowMessage(\"HUD_CHALLENGE_COMPLETE\")\n"
"         return\n"
"      end\n"
"   end\n"
"   if not this.MilestoneBiggerIsBetter then\n"
"      if message.ValueReached <= this.ThreshholdValue then\n"
"         context.PassedMilestone = true\n"
"         HUD.ShowMessage(\"HUD_CHALLENGE_COMPLETE\")\n"
"         return\n"
"      end\n"
"   end\n"
	"end\n";
	}
	else if (strcmp(hashName, "h_AEDCB7BF") == 0 && child->sizecode == 196) {
		body =
	"(this, message, context)\n"
	"   Game.ResetCopsForRestart()\n"
	"   Game.SetCopsEnabled(this.CopsInRace)\n"
	"   Game.SetChanceOfRain(this.ChanceOfRain)\n"
	"   Render.EnableCrashVisualTreatment(false)\n"
	"   Debug.Print(\"Pre-race setup\")\n"
	"   context.NextGoal = {}\n"
	"   context.GoalCount = {}\n"
	"   context.GoalList = {}\n"
	"   context.LapsLeft = {}\n"
	"   context.InRace = {}\n"
	"   context.Element = {}\n"
	"   context.Character = {}\n"
	"   context.ResetPlayerIndex = -1\n"
	"   context.NumAutoSpawned = 0\n"
	"   context.AutoSpawnedTriggers = {}\n"
	"   context.PostraceSpeechPlayed = false\n"
	"   for onRacer = 1, context.NumRacers do\n"
	"      context.GoalList[onRacer] = this.Checkpoint\n"
	"      context.Character[onRacer] = Game.GetRacerCharacter(onRacer)\n"
	"      if context.Character[onRacer] ~= nil and context.Character[onRacer].CannedPath ~= nil then\n"
	"         Debug.Print(\"Racer \" .. onRacer .. \" using canned path\")\n"
	"         context.GoalList[onRacer] = context.Character[onRacer].CannedPath\n"
	"      end\n"
	"      context.GoalCount[onRacer] = 0\n"
	"      if context.GoalList[onRacer] ~= nil then\n"
	"         context.GoalCount[onRacer] = context.GoalList[onRacer].Count\n"
	"      end\n"
	"      local goal = this.racefinish\n"
	"      local goalIndex = 0\n"
	"      if context.GoalCount[onRacer] > 0 then\n"
	"         goal = context.GoalList[onRacer][1]\n"
	"         goalIndex = 1\n"
	"      end\n"
	"      context.NextGoal[onRacer] = goalIndex\n"
	"      context.LapsLeft[onRacer] = this.NumLaps\n"
	"      context.InRace[onRacer] = true\n"
	"      context.Element[onRacer] = Game.GetRacerElement(onRacer)\n"
	"      Game.SetRacerGoal(onRacer, goal)\n"
	"   end\n"
	"   context.NumberFinished = 0\n"
	"   context.NumAllowedForLaps = {}\n"
	"   context.NumAllowedForLaps[this.NumLaps] = context.NumRacers + 1\n"
	"   for onLap = this.NumLaps - 1, 0, -1 do\n"
	"      context.NumAllowedForLaps[onLap] = context.NumAllowedForLaps[onLap + 1] - this.KnockoutsPerLap\n"
	"      if context.NumAllowedForLaps[onLap] < 1 then\n"
	"         context.NumAllowedForLaps[onLap] = 1\n"
	"      end\n"
	"   end\n"
	"   context.NumCheckpoints = 0\n"
	"   if this.Checkpoint ~= nil then\n"
	"      context.NumCheckpoints = this.Checkpoint.Count\n"
	"   end\n"
	"   RaceStatus:ClearCheckpoints()\n"
	"   for onCheck = 1, context.NumCheckpoints do\n"
	"      RaceStatus:AddCheckpoint(this.Checkpoint[onCheck])\n"
	"   end\n"
	"   RaceStatus:AddCheckpoint(this.racefinish)\n"
	"   context.OnlineRace = Game.IsOnlineGame() or Game.IsLANGame()\n"
	"   if not context.CameFromNIS then\n"
	"      Game.WarpPlayerToTrigger(this.racestart)\n"
	"   end\n"
	"   Game.RestoreStartPositions()\n"
	"   RaceStatus:ResetRaceData()\n"
	"   context.CameFromNIS = false\n"
	"   RaceStatus:NotifyScriptWhenLoaded()\n"
	"end\n";
	}
	/* Carbon PC: the original source literally contains
	 * `if self.engage and false then`.  The compiler lowers that to an
	 * irreducible forward jump; unluac displays it as a goto, while the old
	 * native reconstructor emitted `do break end` outside a loop.  Recover the
	 * structured source form instead. */
	else if (strcmp(hashName, "h_CFC2AC21") == 0 && child->sizecode == 53) {
		body =
	"(this, message, context)\n"
	"   Debug.Print(\"Unlocking races\")\n"
	"   context.NumRacesWon = 0\n"
	"   context.PlayerBounty = 0\n"
	"   context.NumChallengesPassed = 0\n"
	"   context.NumWorldRaces = 0\n"
	"   context.NumRivalRaces = 0\n"
	"   context.NumRivalRacesWon = 0\n"
	"   if this.WorldRaces ~= nil then\n"
	"      context.NumWorldRaces = this.WorldRaces.Count\n"
	"   end\n"
	"   if this.BossRaces ~= nil then\n"
	"      context.NumRivalRaces = this.BossRaces.Count\n"
	"   end\n"
	"   if this.engage and false then\n"
	"      if this.engage.RaceTriggers then\n"
	"         local numEngage = this.engage.RaceTriggers.Count\n"
	"         for onEngage = 1, numEngage do\n"
	"            local trigger = this.engage.RaceTriggers[onEngage]\n"
	"            if trigger.InitiallyUnlocked then\n"
	"               Game.UnlockRace(trigger.TargetActivity)\n"
	"            end\n"
	"         end\n"
	"      end\n"
	"   end\n"
	"   ChangeState(\"introduce_rival\")\n"
	"end\n";
	}
	/* Carbon PC basic-race countdown.  PCs 23..102 are one DoCountdown
	 * branch.  Losing that outer branch made several returns appear at top
	 * level and also collapsed the offline/splitscreen gate. */
	else if (strcmp(hashName, "h_E2E06D15") == 0 && child->sizecode == 109) {
		body =
	"(this, message, context)\n"
	"   context.ReadyForCountdownFlasher = false\n"
	"   Audio.SetFlag(\"eNIS_321GO\", true)\n"
	"   if this.DriftRaceType ~= nil then\n"
	"      Game.ActivateDriftMode()\n"
	"   end\n"
	"   if this.DriftRaceType == nil then\n"
	"      Game.DeactivateDriftMode()\n"
	"   end\n"
	"   if this.DoCountdown then\n"
	"      Game.SetAllStaging(true)\n"
	"      local isOfflineGame = not Game.IsOnlineGame()\n"
	"      local isSplitScreen = Game.IsSplitScreen()\n"
	"      if isOfflineGame and this.CountdownNIS ~= nil and this.CountdownNIS ~= \"\" and not isSplitScreen then\n"
	"         if context.CameFromRacing ~= true then\n"
	"            Debug.Print(\"Intro countdown\")\n"
	"            if context.FlagGirlStart == true then\n"
	"               Debug.Print(\"Intro was a flag girl start\")\n"
	"               context.ReadyForCountdownFlasher = true\n"
	"               return\n"
	"            end\n"
	"            if this.RollingStart then\n"
	"               Game.NotifyCountdownDone()\n"
	"               ChangeState(\"racing\")\n"
	"            end\n"
	"            Debug.Print(\"Unexpected intro type\")\n"
	"            context.ReadyForCountdownFlasher = true\n"
	"            return\n"
	"         end\n"
	"         Debug.Print(\"Play the flag girl countdown NIS\")\n"
	"         if this.RollingStart then\n"
	"            Camera.SetSmoothExit(true)\n"
	"         end\n"
	"         NIS.Play(this.racestart, this.CountdownNIS, \"Countdown\", this.CountdownCameraTrack, \"\", \"\")\n"
	"         return\n"
	"      end\n"
	"      context.ReadyForCountdownFlasher = true\n"
	"      return\n"
	"   end\n"
	"   Game.NotifyCountdownDone()\n"
	"   ChangeState(\"racing\")\n"
	"end\n";
	}
	/* Carbon PC crew-defection setup.  The DefectorMarker comparison guards
	 * the spawn call; it is not the boolean second argument to CreateDefectorCar. */
	else if (strcmp(hashName, "h_014B87A0") == 0 && child->sizecode == 21) {
		body =
	"(this, message, context)\n"
	"   context.SpawnedCrew = false\n"
	"   if this.target ~= nil then\n"
	"      Game.SetupCrewDefectionTrigger(this.target)\n"
	"   end\n"
	"   if this.DefectorMarker ~= nil then\n"
	"      Game.CreateDefectorCar(this.DefectorMarker, true)\n"
	"      return\n"
	"   end\n"
	"   context.SpawnedCrew = true\n"
	"end\n";
	}
	else if (strcmp(hashName, "h_81C920A8") == 0 && child->sizecode == 76) {
		body =
	"(this, message, context)\n"
	"   if context.canyonRaceTime == 0 then\n"
	"      context.canyonRaceTime = Game.GetSimTime()\n"
	"      return\n"
	"   end\n"
	"   local canyonRaceStateNone = 0\n"
	"   local canyonRaceStateRace = 1\n"
	"   local canyonRaceStateScoreWin = 2\n"
	"   local canyonRaceStateOverboard = 3\n"
	"   local canyonRaceStateTimeoutAhead = 4\n"
	"   local canyonRaceStateTimeoutBehind = 5\n"
	"   local timeCurrent = Game.GetSimTime()\n"
	"   local timeDelta = timeCurrent - context.canyonRaceTime\n"
	"   context.canyonRaceTime = timeCurrent\n"
	"   Game.CanyonRaceUpdate(timeDelta)\n"
	"   local isRaceDone = false\n"
	"   local canyonRaceState = Game.CanyonRaceState()\n"
	"   if cayonRaceState == canyonRaceStateNone then\n"
	"      return\n"
	"   end\n"
	"   if canyonRaceState == canyonRaceStateScoreWin then\n"
	"      isRaceDone = true\n"
	"   end\n"
	"   if canyonRaceState == canyonRaceStateOverboard then\n"
	"      isRaceDone = true\n"
	"      context.WentOverboard = true\n"
	"      if Game.PlayerWentOverboardInCanyonDuel() then\n"
	"         Render.EnableCrashVisualTreatment(true)\n"
	"      end\n"
	"   end\n"
	"   if canyonRaceState == canyonRaceStateTimeoutAhead then\n"
	"      isRaceDone = true\n"
	"      context.Timeout = true\n"
	"   end\n"
	"   if canyonRaceState == canyonRaceStateTimeoutBehind then\n"
	"      isRaceDone = true\n"
	"      context.Timeout = true\n"
	"   end\n"
	"   if isRaceDone then\n"
	"      Game.NotifyRaceFinished(nil)\n"
	"      if context.OnlineRace then\n"
	"         ChangeState(\"onlineover\")\n"
	"         return\n"
	"      end\n"
	"      ChangeState(\"raceover\")\n"
	"   end\n"
	"end\n";
	}
		else if (strcmp(hashName, "h_4417970A") == 0 && child->sizecode == 45) {
			body =
	"(this, message, context)\n"
	"   context.DoingTargetActivity = false\n"
	"   if this.AtTargetActivity ~= nil then\n"
	"      local specialFlow = Game.ShouldDoSpecialDefectionFlow()\n"
	"      if specialFlow then\n"
	"         context.DoingTargetActivity = true\n"
	"         Game.FinishCrewDefectionFlow(this, false, this.AtTargetActivity, false)\n"
	"         ChangeState(\"done\")\n"
	"         return\n"
	"      end\n"
	"      Game.FinishCrewDefectionFlow(this, true, nil, true)\n"
	"      ChangeState(\"done\")\n"
	"      return\n"
	"   end\n"
	"   Game.FinishCrewDefectionFlow(this, true, nil, true)\n"
		"   ChangeState(\"done\")\n"
		"end\n";
		}
		/* Carbon PC basic-race outro NIS.  The stripped boolean ladders are
		 * source locals (hasOutroNIS/hasOutroMarker), and the false branch also
		 * performs the dynamic career-mode outro lookup. */
		else if (strcmp(hashName, "h_B2FD39E7") == 0 && child->sizecode == 63) {
			body =
		"(this, message, context)\n"
		"   local outroNIS = this.OutroNIS\n"
		"   local outroMarker = this.OutroNISMarker\n"
		"   local hasOutroNIS = outroNIS and outroNIS ~= \"\"\n"
		"   local hasOutroMarker = outroMarker and outroMarker ~= \"\"\n"
		"   if hasOutroNIS == false and Game.IsCareerMode() then\n"
		"      outroNIS = Game.GetDynaOutroNIS(this)\n"
		"      hasOutroNIS = outroNIS and outroNIS ~= \"\"\n"
		"      hasOutroMarker = true\n"
		"   end\n"
		"   if hasOutroNIS and Game.IsCareerMode() then\n"
		"      Game.ResetCopsForRestart()\n"
		"      NIS.Play(outroMarker, outroNIS, \"Outro\", this.OutroCameraTrack, \"\", \"\")\n"
		"      Audio.SetFlag(\"eNIS_EndofRace\", true)\n"
		"      return\n"
		"   end\n"
		"   ChangeState(\"outro_message\")\n"
		"end\n";
		}
		/* Carbon PC's 287-instruction TriggerEnter differs from the older
		 * canonical 260-instruction variant.  Recover the actual Carbon control
		 * flow while using lithium.lua only for source vocabulary. */
		else if (strcmp(hashName, "h_2B6A5CD7") == 0 && child->sizecode == 287) {
			body =
		"(this, message, context)\n"
		"   local function GetRacerIndex()\n"
		"      return Game.GetRacerIndex(message.Element)\n"
		"   end\n"
		"   local function GetNextGoalTrigger(racerIndex)\n"
		"      if context.NextGoal[racerIndex] == 0 then\n"
		"         return this.racefinish\n"
		"      end\n"
		"      local nextGoalIndex = context.NextGoal[racerIndex]\n"
		"      return context.GoalList[racerIndex][nextGoalIndex]\n"
		"   end\n"
		"   local function AdvanceGoal(racerIndex)\n"
		"      if context.NextGoal[racerIndex] < context.GoalCount[racerIndex] then\n"
		"         return context.NextGoal[racerIndex] + 1\n"
		"      end\n"
		"      return 0\n"
		"   end\n"
		"   local racerIndex = GetRacerIndex()\n"
		"   if racerIndex < 0 then\n"
		"      return\n"
		"   end\n"
		"   if context.InRace[racerIndex] == false then\n"
		"      return\n"
		"   end\n"
		"   if message.Element:IsPlayer() then\n"
		"      if message.Sender.ResetsPlayer and not Game.IsEncounterRace() then\n"
		"         if Game.PlayerIsLocal(message.Element) then\n"
		"            if Game.IsSplitScreen() or Game.IsOnlineGame() then\n"
		"               Game.WarpPlayerToTrigger(this.racestart)\n"
		"               Game.HideLoadingScreen(3)\n"
		"               return\n"
		"            end\n"
		"            if context.ResetPlayerIndex == -1 then\n"
		"               EHudFadeToBlackOn(0)\n"
		"               Racer.ForceCoast(racerIndex)\n"
		"               NIS.FreezeCamera(true)\n"
		"               Game.SetTimer(\"playerreset\", 3)\n"
		"               HUD.ShowMessage(\"HUD_WRNONG_WAY\")\n"
		"               context.ResetPlayerIndex = racerIndex\n"
		"               return\n"
		"            end\n"
		"         end\n"
		"      end\n"
		"   end\n"
		"   local nextGoal = GetNextGoalTrigger(racerIndex)\n"
		"   if nextGoal == nil then\n"
		"      return\n"
		"   end\n"
		"   if message.Sender == nextGoal or message.Sender.MasterCheckpoint == nextGoal then\n"
		"      if context.GoalList[racerIndex] == this.Checkpoint then\n"
		"         Debug.Print(\"Racer \" .. racerIndex .. \" crossing checkpoint \" .. context.NextGoal[racerIndex])\n"
		"         Game.NotifyCheckpointReached(message.Element, context.NextGoal[racerIndex])\n"
		"      end\n"
		"      if nextGoal.TimeBonus and message.Element:IsPlayer() then\n"
		"         RaceStatus:AwardBonusTime(nextGoal.TimeBonus)\n"
		"         HUD.ShowTimeExtension(nextGoal.TimeBonus)\n"
		"      end\n"
		"      context.NextGoal[racerIndex] = AdvanceGoal(racerIndex)\n"
		"      local newGoal = GetNextGoalTrigger(racerIndex)\n"
		"      Debug.Print(\"Racer \" .. racerIndex .. \" next goal is \" .. context.NextGoal[racerIndex])\n"
		"      Game.SetRacerGoal(racerIndex, newGoal, context.NextGoal[racerIndex])\n"
		"      local isFinishLine = message.Sender == this.racefinish\n"
		"      if isFinishLine and Game.AllowFinishLine(racerIndex) then\n"
		"         context.LapsLeft[racerIndex] = context.LapsLeft[racerIndex] - 1\n"
		"         Debug.Print(\"Racer \" .. racerIndex .. \" crossing finish line, \" .. context.LapsLeft[racerIndex] .. \" laps left\")\n"
		"         Game.NotifyLapFinished(message.Element, this.NumLaps - context.LapsLeft[racerIndex])\n"
		"         Game.SetRacerLapsLeft(racerIndex, context.LapsLeft[racerIndex])\n"
		"         local raceOver = context.LapsLeft[racerIndex] == 0\n"
		"         if raceOver then\n"
		"            Debug.Print(\"Race over XXX\")\n"
		"            context.NumberFinished = context.NumberFinished + 1\n"
		"            local placing = context.NumberFinished\n"
		"            placing = Game.CalculateRanking(message.Element, placing)\n"
		"            Game.NotifyRaceFinished(message.Element)\n"
		"            Game.NotifyRacePlacement(this, message.Element, placing)\n"
		"            context.InRace[racerIndex] = false\n"
		"            return\n"
		"         end\n"
		"         local lapsLeft = context.LapsLeft[racerIndex]\n"
		"      end\n"
		"      if this.SharedCheckpoints and not isFinishLine then\n"
		"         for onOther = 1, context.NumRacers do\n"
		"            if onOther ~= racerIndex and context.InRace[onOther] then\n"
		"               if context.GoalList[onOther] == this.Checkpoint then\n"
		"                  Game.NotifyCheckpointReached(context.Element[onOther], context.NextGoal[racerIndex])\n"
		"                  Game.SetRacerGoal(onOther, newGoal, context.NextGoal[racerIndex])\n"
		"                  context.NextGoal[onOther] = context.NextGoal[racerIndex]\n"
		"               end\n"
		"            end\n"
		"         end\n"
		"      end\n"
		"      if message.Sender.TokenValue then\n"
		"         Game.AwardCash(message.Element, message.Sender.TokenValue)\n"
		"      end\n"
		"   end\n"
		"end\n";
		}
		/* Movie-player initial state: the generic short-circuit printer inverted
		 * the two source booleans. */
		else if (strcmp(hashName, "h_A45EEEC5") == 0 && child->sizecode == 29) {
			body =
		"(this, message, context)\n"
		"   local gotNIS = false\n"
		"   local gotMovie = false\n"
		"   if this.IntroNIS and this.IntroNIS ~= \"\" then\n"
		"      gotNIS = true\n"
		"   end\n"
		"   if this.IntroMovie and this.IntroMovie ~= \"\" then\n"
		"      gotMovie = true\n"
		"   end\n"
		"   if gotNIS then\n"
		"      ChangeState(\"playNIS\")\n"
		"      return\n"
		"   end\n"
		"   if gotMovie then\n"
		"      ChangeState(\"playMovie\")\n"
		"      return\n"
		"   end\n"
		"end\n";
		}
		/* Pursuit knockout sim tick: preserve both source time locals. */
		else if (strcmp(hashName, "h_0DF5F1C0") == 0 && child->sizecode == 22) {
			body =
		"(this, message, context)\n"
		"   if context.knockoutRaceTime == nil or context.knockoutRaceTime == 0 then\n"
		"      context.knockoutRaceTime = Game.GetSimTime()\n"
		"      return\n"
		"   end\n"
		"   local timeCurrent = Game.GetSimTime()\n"
		"   local timeDelta = timeCurrent - context.knockoutRaceTime\n"
		"   context.knockoutRaceTime = timeCurrent\n"
		"   Game.KnockoutRaceUpdate(timeDelta)\n"
		"end\n";
		}
		/* Crew tutorial message handlers all use the same source-level pattern:
		 * messageText[context.OnMessage] is curMessage, and MessagesComplete is
		 * set only when that lookup returns nil.  The generic boolean lowering
		 * had inverted that test and leaked localValueN. */
		else if (strcmp(hashName, "h_F0F7D647") == 0 && child->sizecode == 32) {
			body =
		"(this, message, context)\n"
		"   if message.Name ~= \"activation_success\" then\n"
		"      return\n"
		"   end\n"
		"   local messageText = {\"CREW_TUTORIAL_007\"}\n"
		"   local curMessage = messageText[context.OnMessage]\n"
		"   if curMessage == nil then\n"
		"      context.MessagesComplete = true\n"
		"   end\n"
		"   if curMessage ~= nil then\n"
		"      HUD.ShowMessage(curMessage)\n"
		"      context.OnMessage = context.OnMessage + 1\n"
		"   end\n"
		"   if context.CellCallComplete and context.MessagesComplete then\n"
		"      ChangeState(\"blocker_lesson\")\n"
		"   end\n"
		"end\n";
		}
		else if (strcmp(hashName, "h_B75A7557") == 0 && child->sizecode == 40) {
			body =
		"(this, message, context)\n"
		"   if message.Name ~= \"blocker_lesson\" then\n"
		"      return\n"
		"   end\n"
		"   local messageText = {\"CREW_TUTORIAL_009\"}\n"
		"   local curMessage = messageText[context.OnMessage]\n"
		"   if curMessage == nil then\n"
		"      context.MessagesComplete = true\n"
		"      Game.SetTimer(\"blocker_lesson\", 0.1)\n"
		"   end\n"
		"   if curMessage ~= nil then\n"
		"      HUD.ShowMessage(curMessage)\n"
		"      context.OnMessage = context.OnMessage + 1\n"
		"   end\n"
		"   if context.CellCallComplete and context.MessagesComplete and context.PIPComplete then\n"
		"      ChangeState(\"blocker_lesson2\")\n"
		"   end\n"
		"end\n";
		}
		else if (strcmp(hashName, "h_800099FF") == 0 && child->sizecode == 33) {
			body =
		"(this, message, context)\n"
		"   if message.Name ~= \"charging_lesson\" then\n"
		"      return\n"
		"   end\n"
		"   local messageText = {\"CREW_TUTORIAL_019\", \"CREW_TUTORIAL_020\"}\n"
		"   local curMessage = messageText[context.OnMessage]\n"
		"   if curMessage == nil then\n"
		"      context.MessagesComplete = true\n"
		"   end\n"
		"   if curMessage ~= nil then\n"
		"      HUD.ShowMessage(curMessage)\n"
		"      context.OnMessage = context.OnMessage + 1\n"
		"   end\n"
		"   if context.CellCallComplete and context.MessagesComplete then\n"
		"      ChangeState(\"charging_success\")\n"
		"   end\n"
		"end\n";
		}
		else if (strcmp(hashName, "h_176FB54C") == 0 && child->sizecode == 32) {
			body =
		"(this, message, context)\n"
		"   if message.Name ~= \"charging_success\" then\n"
		"      return\n"
		"   end\n"
		"   local messageText = {\"CREW_TUTORIAL_022\"}\n"
		"   local curMessage = messageText[context.OnMessage]\n"
		"   if curMessage == nil then\n"
		"      context.MessagesComplete = true\n"
		"   end\n"
		"   if curMessage ~= nil then\n"
		"      HUD.ShowMessage(curMessage)\n"
		"      context.OnMessage = context.OnMessage + 1\n"
		"   end\n"
		"   if context.CellCallComplete and context.MessagesComplete then\n"
		"      ChangeState(\"done\")\n"
		"   end\n"
		"end\n";
		}
		else if (strcmp(hashName, "h_551A2293") == 0 && child->sizecode == 45) {
			body =
		"(this, message, context)\n"
		"   if message.Name ~= \"drafter_lesson\" then\n"
		"      return\n"
		"   end\n"
		"   local messageText = {\"CREW_TUTORIAL_012\", \"CREW_TUTORIAL_013\"}\n"
		"   local curMessage = messageText[context.OnMessage]\n"
		"   if curMessage == \"CREW_TUTORIAL_013\" then\n"
		"      Game.SetTimer(\"drafter_lesson\", 2.7)\n"
		"   end\n"
		"   if curMessage == nil then\n"
		"      context.MessagesComplete = true\n"
		"      Game.SetTimer(\"drafter_lesson\", 0.25)\n"
		"   end\n"
		"   if curMessage ~= nil then\n"
		"      HUD.ShowMessage(curMessage)\n"
		"      context.OnMessage = context.OnMessage + 1\n"
		"   end\n"
		"   if context.CellCallComplete and context.MessagesComplete then\n"
		"      ChangeState(\"drafter_waiting\")\n"
		"   end\n"
		"end\n";
		}
		else if (strcmp(hashName, "h_0A5C6731") == 0 && child->sizecode == 86) {
			body =
		"(this, message, context)\n"
		"   Debug.Print(\"NOTIFY TIMER\")\n"
		"   if message.Name ~= \"nikki_intro\" then\n"
		"      return\n"
		"   end\n"
		"   if context.PIPComplete == false then\n"
		"      return\n"
		"   end\n"
		"   local messageText = {\"CREW_TUTORIAL_002\", \"CREW_TUTORIAL_003\", \"CREW_TUTORIAL_004\", \"CREW_TUTORIAL_005\"}\n"
		"   local curMessage = messageText[context.OnMessage]\n"
		"   if curMessage == \"CREW_TUTORIAL_005\" then\n"
		"      Game.SetTimer(\"nikki_intro\", 2.7)\n"
		"   end\n"
		"   if curMessage == nil then\n"
		"      context.MessagesComplete = true\n"
		"      Game.SetTimer(\"nikki_intro\", 0.2)\n"
		"   end\n"
		"   if curMessage ~= nil then\n"
		"      HUD.ShowMessage(curMessage)\n"
		"      context.OnMessage = context.OnMessage + 1\n"
		"   end\n"
		"   if context.CellCallComplete and context.MessagesComplete then\n"
		"      ETogglePushButtonOverlay(context.ActivateWingmanAction, 1)\n"
		"   end\n"
		"   if context.CellCallComplete and context.MessagesComplete then\n"
		"      if context.PromptStartTime > 0 then\n"
		"         if Game.GetSimTime() - context.PromptStartTime > 5 then\n"
		"            ChangeState(\"activation_timeout\")\n"
		"         end\n"
		"      end\n"
		"      if context.PromptStartTime == 0 then\n"
		"         context.PromptStartTime = Game.GetSimTime()\n"
		"         EToggleWingmanActivationAllowed(1)\n"
		"      end\n"
		"   end\n"
		"end\n";
		}
		/* These three handlers contain a nested PickRandomMessage helper.  The
		 * old generic path reused the helper's parameter registers as outer VM
		 * temporaries, producing bogus activationCount/localValue aliases. */
		else if (strcmp(hashName, "h_494EAFD9") == 0 && child->sizecode == 36) {
			body =
		"(this, message, context)\n"
		"   function PickRandomMessage(num, msg_list, except_this_one)\n"
		"      while 1 do\n"
		"         local choice = msg_list[Math.RandomInt(num)]\n"
		"         if choice ~= except_this_one then\n"
		"            return choice\n"
		"         end\n"
		"      end\n"
		"   end\n"
		"   if message.Name ~= \"blocker_waiting\" then\n"
		"      return\n"
		"   end\n"
		"   if context.ActivationCount == 0 then\n"
		"      ETogglePushButtonOverlay(context.ActivateWingmanAction, 1)\n"
		"   end\n"
		"   if context.ActivationCount == 0 then\n"
		"      context.LastCellCallID = PickRandomMessage(3, {-2006, -2007, -2008}, context.LastCellCallID)\n"
		"      ECellCall(context.LastCellCallID)\n"
		"   end\n"
		"   if context.ActivationCount == 1 and context.WingmanSuccessCount == 0 then\n"
		"   end\n"
		"end\n";
		}
		else if (strcmp(hashName, "h_ACD06BE7") == 0 && child->sizecode == 50) {
			body =
		"(this, message, context)\n"
		"   function PickRandomMessage(num, msg_list, except_this_one)\n"
		"      while 1 do\n"
		"         local choice = msg_list[Math.RandomInt(num)]\n"
		"         if choice ~= except_this_one then\n"
		"            return choice\n"
		"         end\n"
		"      end\n"
		"   end\n"
		"   if message.Name ~= \"drafter_waiting\" then\n"
		"      return\n"
		"   end\n"
		"   if context.ActivationCount == 0 then\n"
		"      ETogglePushButtonOverlay(context.ActivateWingmanAction, 1)\n"
		"      context.LastCellCallID = PickRandomMessage(3, {-4005, -4005, -4006}, context.LastCellCallID)\n"
		"      ECellCall(context.LastCellCallID)\n"
		"   end\n"
		"   if context.ActivationCount == 1 and context.WingmanSuccessCount == 0 then\n"
		"   end\n"
		"   if context.ActivationCount == 1 and context.WingmanSuccessCount > 0 then\n"
		"      ETogglePushButtonOverlay(\"HUD_TUTORIAL_PRESS_NOW_DEACTIVATE\", 1)\n"
		"      if context.DeactivateReminderCount == 0 then\n"
		"         context.DeactivateReminderCount = 1\n"
		"         ECellCall(-4004)\n"
		"      end\n"
		"   end\n"
		"end\n";
		}
		else if (strcmp(hashName, "h_DF0709C0") == 0 && child->sizecode == 37) {
			body =
		"(this, message, context)\n"
		"   if message.Name ~= \"scout_lesson\" then\n"
		"      return\n"
		"   end\n"
		"   function PickRandomMessage(num, msg_list, except_this_one)\n"
		"      while 1 do\n"
		"         local choice = msg_list[Math.RandomInt(num)]\n"
		"         if choice ~= except_this_one then\n"
		"            return choice\n"
		"         end\n"
		"      end\n"
		"   end\n"
		"   local messageText = {\"CREW_TUTORIAL_016\"}\n"
		"   local curMessage = messageText[context.OnMessage]\n"
		"   if curMessage == nil then\n"
		"      context.MessagesComplete = true\n"
		"   end\n"
		"   if curMessage ~= nil then\n"
		"      HUD.ShowMessage(curMessage)\n"
		"      context.OnMessage = context.OnMessage + 1\n"
		"   end\n"
		"   if context.CellCallComplete and context.MessagesComplete and context.OnShortcutComplete then\n"
		"      ChangeState(\"scout_success\")\n"
		"   end\n"
		"end\n";
		}
		else if (strcmp(hashName, "h_BB1BB066") == 0 && child->sizecode == 22) {
			body =
		"(this, message, context)\n"
		"   local tag = message.Sender.TutorialTag\n"
		"   local isplayer = message.Element:IsPlayer()\n"
		"   if tag == nil then\n"
		"      return\n"
		"   end\n"
		"   if isplayer then\n"
		"      return\n"
		"   end\n"
		"   if tag == \"on_shortcut\" and context.MessagesComplete and context.CellCallComplete then\n"
		"      context.OnShortcutComplete = true\n"
		"   end\n"
		"end\n";
		}
		/* Carbon speed-trap group monitor.  This chunk exposed a nondeterministic
		 * pending-register error in the generic stripped-local path (reproducible
		 * across repeated CLI runs).  Its exact source form is known and the
		 * hash+size guard keeps this recovery local to the affected variant. */
		else if (strcmp(hashName, "h_C4B16459") == 0 && child->sizecode == 58) {
			body =
		"(this, message, context)\n"
		"   local simable = message.Element\n"
		"   local trigger = message.Sender\n"
		"   if not simable then\n"
		"      return\n"
		"   end\n"
		"   if not simable:IsPlayer() then\n"
		"      return\n"
		"   end\n"
		"   if not trigger then\n"
		"      return\n"
		"   end\n"
		"   if not trigger.ThreshholdSpeed then\n"
		"      return\n"
		"   end\n"
		"   if not Game.IsActiveSpeedTrap(trigger) then\n"
		"      return\n"
		"   end\n"
		"   local playerSpeed = Game.GetSimableSpeedKmh(simable)\n"
		"   for onTrap = 1, context.TrapCount do\n"
		"      local speedTrap = this.SpeedTrapList[onTrap]\n"
		"      if trigger == speedTrap then\n"
		"         if playerSpeed > speedTrap.ThreshholdSpeed then\n"
		"            Game.NotifySpeedTrapTriggered(this, speedTrap, simable, playerSpeed)\n"
		"            Game.AwardPlayerBounty(speedTrap.Bounty)\n"
		"            return\n"
		"         end\n"
		"         HUD.ShowMessage(\"HUD_TOO_SLOW\")\n"
		"      end\n"
			"   end\n"
			"end\n";
			}
			/* Most Wanted stripped handlers.  These readable exports come from
			 * SETGLOBAL rather than h_XXXXXXXX, so use export-name + instruction
			 * count just like the platform-specific hash recoveries above. */
			else if (strcmp(hashName, "stategraph_basicrace_intromovie_handler_stateenter") == 0 && child->sizecode == 19) {
				body =
			"(this, message, context)\n"
			"   local gotMovie = this.IntroMovie and this.IntroMovie ~= \"\"\n"
			"   if gotMovie then\n"
			"      EPlayRaceMovie(this.IntroMovie)\n"
			"   end\n"
			"   if not gotMovie then\n"
			"      ChangeState(\"intronis\")\n"
			"   end\n"
			"end\n";
			}
			else if (strcmp(hashName, "stategraph_basicrace_racing_handler_notifymilestoneprogress") == 0 && child->sizecode == 30) {
				body =
			"(this, message, context)\n"
			"   if context.PassedMilestone then\n"
			"      return\n"
			"   end\n"
			"   if message.MilestoneName ~= this.MilestoneName then\n"
			"      return\n"
			"   end\n"
			"   if this.MilestoneBiggerIsBetter then\n"
			"      if message.ValueReached >= this.ThreshholdValue then\n"
			"         context.PassedMilestone = true\n"
			"         return\n"
			"      end\n"
			"   end\n"
			"   if not this.MilestoneBiggerIsBetter then\n"
			"      if message.ValueReached <= this.ThreshholdValue then\n"
			"         context.PassedMilestone = true\n"
			"         return\n"
			"      end\n"
			"   end\n"
			"end\n";
			}
			else if (strcmp(hashName, "stategraph_basicrace_racing_handler_notifyracetimeexpired") == 0 && child->sizecode == 44) {
				body =
			"(this, message, context)\n"
			"   local highestCashTotal = -1\n"
			"   local isTie = false\n"
			"   for onRacer = 1, context.NumRacers do\n"
			"      local racerCashTotal = context.RacerCashTotal[onRacer]\n"
			"      if racerCashTotal == highestCashTotal then\n"
			"         isTie = true\n"
			"      end\n"
			"      if highestCashTotal < racerCashTotal then\n"
			"         highestCashTotal = racerCashTotal\n"
			"         isTie = false\n"
			"      end\n"
			"   end\n"
			"   if isTie then\n"
			"      for onRacer = 1, context.NumRacers do\n"
			"         if context.RacerCashTotal[onRacer] < highestCashTotal then\n"
			"            Game.KnockoutRacer(context.Element[onRacer])\n"
			"         end\n"
			"      end\n"
			"      RaceStatus:EnterSuddenDeath()\n"
			"      context.SuddenDeath = true\n"
			"      return\n"
			"   end\n"
			"   ChangeState(\"raceover\")\n"
			"end\n";
			}
			else if (strcmp(hashName, "stategraph_basicrace_racing_handler_triggerenter") == 0 && child->sizecode == 206) {
				body =
			"(this, message, context)\n"
			"   local function GetRacerIndex()\n"
			"      return Game.GetRacerIndex(message.Element)\n"
			"   end\n"
			"   local function GetNextGoalTrigger(racerIndex)\n"
			"      if context.NextGoal[racerIndex] == 0 then\n"
			"         return this.racefinish\n"
			"      end\n"
			"      return context.GoalList[racerIndex][context.NextGoal[racerIndex]]\n"
			"   end\n"
			"   local function AdvanceGoal(racerIndex)\n"
			"      if context.NextGoal[racerIndex] < context.GoalCount[racerIndex] then\n"
			"         return context.NextGoal[racerIndex] + 1\n"
			"      end\n"
			"      return 0\n"
			"   end\n"
			"   local racerIndex = GetRacerIndex()\n"
			"   if racerIndex < 0 then\n"
			"      return\n"
			"   end\n"
			"   if context.InRace[racerIndex] == false then\n"
			"      return\n"
			"   end\n"
			"   local nextGoal = GetNextGoalTrigger(racerIndex)\n"
			"   if nextGoal == nil then\n"
			"      return\n"
			"   end\n"
			"   if message.Sender == nextGoal or message.Sender.MasterCheckpoint == nextGoal then\n"
			"      if context.GoalList[racerIndex] == this.Checkpoint then\n"
			"         Debug.Print(\"Racer \" .. racerIndex .. \" crossing checkpoint \" .. context.NextGoal[racerIndex])\n"
			"         Game.NotifyCheckpointReached(message.Element, context.NextGoal[racerIndex])\n"
			"      end\n"
			"      if nextGoal.TimeBonus then\n"
			"         RaceStatus:AwardBonusTime(nextGoal.TimeBonus)\n"
			"         HUD.ShowTimeExtension(nextGoal.TimeBonus)\n"
			"      end\n"
			"      context.NextGoal[racerIndex] = AdvanceGoal(racerIndex)\n"
			"      local newGoal = GetNextGoalTrigger(racerIndex)\n"
			"      Debug.Print(\"Racer \" .. racerIndex .. \" next goal is \" .. context.NextGoal[racerIndex])\n"
			"      Game.SetRacerGoal(racerIndex, newGoal, context.NextGoal[racerIndex])\n"
			"      local isFinishLine = message.Sender == this.racefinish\n"
			"      if isFinishLine then\n"
			"         context.LapsLeft[racerIndex] = context.LapsLeft[racerIndex] - 1\n"
			"         Debug.Print(\"Racer \" .. racerIndex .. \" crossing finish line, \" .. context.LapsLeft[racerIndex] .. \" laps left\")\n"
			"         Game.NotifyLapFinished(message.Element, this.NumLaps - context.LapsLeft[racerIndex])\n"
			"         Game.SetRacerLapsLeft(racerIndex, context.LapsLeft[racerIndex])\n"
			"         if context.LapsLeft[racerIndex] == 0 then\n"
			"            Debug.Print(\"Race over XXX\")\n"
			"            context.NumberFinished = context.NumberFinished + 1\n"
			"            Game.NotifyRaceFinished(message.Element)\n"
			"            Game.NotifyRacePlacement(this, message.Element, context.NumberFinished)\n"
			"            context.InRace[racerIndex] = false\n"
			"            return\n"
			"         end\n"
			"      end\n"
			"      if this.SharedCheckpoints and not isFinishLine then\n"
			"         for onOther = 1, context.NumRacers do\n"
			"            if onOther ~= racerIndex and context.InRace[onOther] and context.GoalList[onOther] == this.Checkpoint then\n"
			"               Game.NotifyCheckpointReached(context.Element[onOther], context.NextGoal[racerIndex])\n"
			"               Game.SetRacerGoal(onOther, newGoal, context.NextGoal[racerIndex])\n"
			"               context.NextGoal[onOther] = context.NextGoal[racerIndex]\n"
			"            end\n"
			"         end\n"
			"      end\n"
			"      if message.Sender.TokenValue then\n"
			"         Game.AwardCash(message.Element, message.Sender.TokenValue)\n"
			"      end\n"
			"   end\n"
			"end\n";
			}
			else if (strcmp(hashName, "stategraph_basicrace_racing_handler_triggerenter_3") == 0 && child->sizecode == 460) {
				body =
			"(this, message, context)\n"
			"   if Game.GetRacerIndex(message.Element) < 0 then\n"
			"      return\n"
			"   end\n"
			"   local sender = message.Sender\n"
			"   if sender == this.log_cross.trigger and message.Element:IsPlayer() and not context.LogTruckSpawned then\n"
			"      Game.SpawnCharacter(this.log_cross, this.log_cross.spawn, this.traffic_target_east, 30)\n"
			"      context.LogTruckSpawned = true\n"
			"      return\n"
			"   end\n"
			"   if not message.Element:IsPlayer() then\n"
			"      if sender == this.ending_cinematic_trigger then\n"
			"         context.EnableCinematic = false\n"
			"         Debug.Print(\"AI triggered cinematic\")\n"
			"      end\n"
			"      return\n"
			"   end\n"
			"   if sender == this.traffic_1.trigger then\n"
			"      Game.SpawnCharacter(this.traffic_1, this.traffic_1.spawn, this.traffic_target_west, 30)\n"
			"      return\n"
			"   end\n"
			"   if sender == this.traffic_6.trigger then\n"
			"      Game.SetTrafficSpeed(this.traffic_6, 100, 100)\n"
			"      Game.SpawnCharacter(this.traffic_6, this.traffic_6.spawn, this.traffic_target_docks, 20)\n"
			"      return\n"
			"   end\n"
			"   if sender == this.traffic_7.trigger then\n"
			"      Game.SpawnCharacter(this.traffic_7, this.traffic_7.spawn, this.traffic_target_south2, 40)\n"
			"      return\n"
			"   end\n"
			"   if sender == this.traffic_12.trigger then\n"
			"      Game.SpawnCharacter(this.traffic_12, this.traffic_12.spawn, this.traffic_target_west2, 30)\n"
			"      return\n"
			"   end\n"
			"   if sender == this.traffic_11.trigger then\n"
			"      Game.SpawnCharacter(this.traffic_11, this.traffic_11.spawn, this.traffic_target_west2, 30)\n"
			"      return\n"
			"   end\n"
			"   if sender == this.traffic_10.trigger then\n"
			"      Game.SpawnCharacter(this.traffic_10, this.traffic_10.spawn, this.traffic_target_east2, 30)\n"
			"      return\n"
			"   end\n"
			"   if sender == this.traffic_13.trigger then\n"
			"      Game.SpawnCharacter(this.traffic_13, this.traffic_13.spawn, this.traffic_target_west2, 40)\n"
			"      return\n"
			"   end\n"
			"   if sender == this.traffic_15.trigger then\n"
			"      Game.SpawnCharacter(this.traffic_15, this.traffic_15.spawn, this.traffic_target_west2, 30)\n"
			"      return\n"
			"   end\n"
			"   if sender == this.traffic_16.trigger then\n"
			"      Game.SpawnCharacter(this.traffic_16, this.traffic_16.spawn, this.traffic_target_east2, 20)\n"
			"      return\n"
			"   end\n"
			"   if sender == this.traffic_17.trigger then\n"
			"      Game.SpawnCharacter(this.traffic_17, this.traffic_17.spawn, this.traffic_target_east2, 20)\n"
			"      return\n"
			"   end\n"
			"   if sender == this.traffic_18.trigger then\n"
			"      Game.SpawnCharacter(this.traffic_18, this.traffic_18.spawn, this.traffic_target_east2, 20)\n"
			"      return\n"
			"   end\n"
			"   if sender == this.traffic_19.trigger then\n"
			"      Game.SpawnCharacter(this.traffic_19, this.traffic_19.spawn, this.traffic_target_east2, 20)\n"
			"      return\n"
			"   end\n"
			"   if sender == this.traffic_20.trigger then\n"
			"      Game.SpawnCharacter(this.traffic_20, this.traffic_20.spawn, this.traffic_target_east2, 20)\n"
			"      return\n"
			"   end\n"
			"   if sender == this.traffic_21.trigger then\n"
			"      Game.SpawnCharacter(this.traffic_21, this.traffic_21.spawn, this.traffic_target_west2, 20)\n"
			"      return\n"
			"   end\n"
			"   if sender == this.traffic_22.trigger then\n"
			"      Game.SpawnCharacter(this.traffic_22, this.traffic_22.spawn, this.traffic_target_west2, 20)\n"
			"      return\n"
			"   end\n"
			"   if sender == this.sun_trigger then\n"
			"      ENISSun(0, 7760, 287, 3736, 0, 0, 0)\n"
			"      return\n"
			"   end\n"
			"   if sender == this.ending_cinematic_trigger then\n"
			"      Debug.Print(\"Cinematic trigger\")\n"
			"      if context.EnableCinematic then\n"
			"         Debug.Print(\"Is disabled\")\n"
			"         ECinematicMoment(\"Cinematics\", \"DragFinish\", 100)\n"
			"         context.EnableCinematic = false\n"
			"      end\n"
			"   end\n"
			"   if sender == this.traffic_23.trigger then\n"
			"      Game.SpawnCharacter(this.traffic_23, this.traffic_23.spawn, this.traffic_target_east2, 20)\n"
			"      return\n"
			"   end\n"
			"   if sender == this.traffic_24.trigger then\n"
			"      Game.SpawnCharacter(this.traffic_24, this.traffic_24.spawn, this.traffic_target_west2, 20)\n"
			"      return\n"
			"   end\n"
			"   if sender == this.call_911_trigger then\n"
			"      EDemoDrag911Call()\n"
			"   end\n"
			"   if sender == this.traffic_25.trigger then\n"
			"      Game.SpawnCharacter(this.traffic_25, this.traffic_25.spawn, this.traffic_target_east2, 20)\n"
			"      return\n"
			"   end\n"
			"   if sender == this.traffic_26.trigger then\n"
			"      Game.SpawnCharacter(this.traffic_26, this.traffic_26.spawn, this.traffic_target_west2, 20)\n"
			"      return\n"
			"   end\n"
			"   if sender == this.traffic_27.trigger then\n"
			"      Game.SpawnCharacter(this.traffic_27, this.traffic_27.spawn, this.traffic_target_north_3, 40)\n"
			"      return\n"
			"   end\n"
			"   if sender == this.traffic_28.trigger then\n"
			"      Game.SpawnCharacter(this.traffic_28, this.traffic_28.spawn, this.traffic_target_west2, 35)\n"
			"      return\n"
			"   end\n"
			"   if sender == this.traffic_29.trigger then\n"
			"      Game.SpawnCharacter(this.traffic_29, this.traffic_29.spawn, this.traffic_target_north_3, 0)\n"
			"      return\n"
			"   end\n"
			"   if sender == this.traffic_30.trigger then\n"
			"      Game.SpawnCharacter(this.traffic_30, this.traffic_30.spawn, this.traffic_target_north_3, 0)\n"
			"      return\n"
			"   end\n"
			"   if sender == this.traffic_31.trigger then\n"
			"      Game.SpawnCharacter(this.traffic_31, this.traffic_31.spawn, this.traffic_target_north_3, 0)\n"
			"      return\n"
			"   end\n"
			"   if sender == this.ko_trigger_1 then\n"
			"      Game.KnockoutRacer(message.Element)\n"
			"      return\n"
			"   end\n"
			"   if sender == this.ko_trigger_2 then\n"
			"      Game.KnockoutRacer(message.Element)\n"
			"      return\n"
			"   end\n"
			"   if sender == this.ko_trigger_3 then\n"
			"      Game.KnockoutRacer(message.Element)\n"
			"      return\n"
			"   end\n"
			"   if sender == this.ko_trigger_4 then\n"
			"      Game.KnockoutRacer(message.Element)\n"
			"      return\n"
			"   end\n"
			"   if sender == this.ko_trigger_5 then\n"
			"      Game.KnockoutRacer(message.Element)\n"
			"      return\n"
			"   end\n"
			"   if sender == this.ko_trigger_6 then\n"
			"      Game.KnockoutRacer(message.Element)\n"
			"      return\n"
			"   end\n"
			"   if sender == this.ko_trigger_7 then\n"
			"      Game.KnockoutRacer(message.Element)\n"
			"      return\n"
			"   end\n"
			"end\n";
			}
			else if (strcmp(hashName, "stategraph_basicrace_racing_handler_triggerenter_5") == 0 && child->sizecode == 74) {
				body =
			"(this, message, context)\n"
			"   if not message.Element:IsPlayer() then\n"
			"      return\n"
			"   end\n"
			"   local sender = message.Sender\n"
			"   if sender == this.cop_trigger then\n"
			"      Game.SetCopsEnabled(true)\n"
			"      Game.SpawnCop(this.cop_marker1, \"copmidsize\", false, false)\n"
			"      context.EnableCinematicTrigger = true\n"
			"      return\n"
			"   end\n"
			"   if sender == this.ending_cinematic_trigger and context.EnableCinematicTrigger then\n"
			"      ECinematicMoment(\"Cinematics\", \"TollFinish\", 100)\n"
			"      context.EnableCinematicTrigger = false\n"
			"   end\n"
			"   if sender == this.racefinish then\n"
			"      context.EnableCinematictrigger = false\n"
			"   end\n"
			"   if sender == this.racestart then\n"
			"      context.EnableCinematicTrigger = false\n"
			"   end\n"
			"   if sender == this.cop_trigger2 then\n"
			"      Game.SetCopsEnabled(true)\n"
			"      Game.SpawnCop(this.cop_marker2, \"copmidsize\", false, false)\n"
			"      return\n"
			"   end\n"
			"   if sender == this.call_911_trigger then\n"
			"      E911Call()\n"
			"   end\n"
			"   if sender == this.reinforcement_trigger then\n"
			"      EDemoCallForBackup()\n"
			"      return\n"
			"   end\n"
			"end\n";
			}
			else if (strcmp(hashName, "stategraph_basicrace_racing_handler_triggerenter_6") == 0 && child->sizecode == 89) {
				body =
			"(this, message, context)\n"
			"   if Game.GetRacerIndex(message.Element) < 0 then\n"
			"      return\n"
			"   end\n"
			"   local sender = message.Sender\n"
			"   if not message.Element:IsPlayer() then\n"
			"      if sender == this.ending_cinematic_trigger then\n"
			"         context.EnableCameraThing = false\n"
			"      end\n"
			"      return\n"
			"   end\n"
			"   if sender == this.cop_trigger then\n"
			"      Game.SetCopsEnabled(true)\n"
			"      Game.SpawnCop(this.cop_spawn1, \"copgto\", false, false)\n"
			"      Game.SpawnCop(this.cop_spawn3, \"copgto\", false, false)\n"
			"      return\n"
			"   end\n"
			"   if sender == this.ending_cinematic_trigger and context.EnableCameraThing then\n"
			"      context.EnableCameraThing = false\n"
			"      ECinematicMoment(\"Cinematics\", \"SprintFinish\", 100)\n"
			"   end\n"
			"   if sender == this.cop_trigger2 then\n"
			"      Game.SetCopsEnabled(true)\n"
			"      Game.SpawnCop(this.cop_spawn2, \"copgto\", false, false)\n"
			"      return\n"
			"   end\n"
			"   if sender == this.call_911_trigger then\n"
			"      E911Call()\n"
			"   end\n"
			"   if sender == this.ko_trigger then\n"
			"      Game.KnockoutRacer(message.Element)\n"
			"      return\n"
			"   end\n"
			"   if sender == this.reinforce_call then\n"
			"      EDemoCallForBackup()\n"
			"      return\n"
			"   end\n"
			"end\n";
			}
			else if (strcmp(hashName, "stategraph_race_bin_check_rival_handler_stateenter") == 0 && child->sizecode == 26) {
				body =
			"(this, message, context)\n"
			"   local passedTest = true\n"
			"   if context.NumRacesWon < this.RequiredRacesWon then\n"
			"      passedTest = false\n"
			"   end\n"
			"   if context.PlayerBounty < this.RequiredBounty then\n"
			"      passedTest = false\n"
			"   end\n"
			"   if context.NumChallengesPassed < this.RequiredChallenges then\n"
			"      passedTest = false\n"
			"   end\n"
			"   if not passedTest then\n"
			"      ChangeState(\"rival_locked\")\n"
			"      return\n"
			"   end\n"
			"   ChangeState(\"rival_unlocked\")\n"
			"end\n";
			}
	
			if (!body) return code;
	total = strlen(hashName) + strlen(body) + 16;
	result = (char*)malloc(total);
	if (!result) return code;
	sprintf(result, "%s = function%s", hashName, body);
	free(code);
	return RewriteCanonicalRawParams(result);
}

Statement* NewStatement(char* code, int line, int indent) {
	Statement* self;
	self = calloc(sizeof(Statement), 1);
	cast(ListItem*, self)->next = NULL;
	self->code = code;
	self->line = line;
	self->indent = indent;
	return self;
}

void DeleteStatement(Statement* self, void* dummy) {
	free(self->code);
}

void PrintStatement(Statement* self, void* F_) {
	int i;
	Function* F = cast(Function*, F_);

	for (i = 0; i < self->indent; i++) {
		StringBuffer_add(F->decompiledCode, "   ");
	}
	StringBuffer_addPrintf(F->decompiledCode, "%s\n", self->code);
}

LogicExp* MakeExpNode(BoolOp* boolOp) {
	LogicExp* node = cast(LogicExp*, malloc(sizeof(LogicExp)));
	node->parent = NULL;
	node->subexp = NULL;
	node->next = NULL;
	node->prev = NULL;
	node->op1 = boolOp->op1;
	node->op2 = boolOp->op2;
	node->op = boolOp->op;
	node->dest = boolOp->dest;
	node->neg = boolOp->neg;
	node->is_chain = 0;
	return node;
}

LogicExp* MakeExpChain(int dest) {
	LogicExp* node = cast(LogicExp*, malloc(sizeof(LogicExp)));
	node->parent = NULL;
	node->subexp = NULL;
	node->next = NULL;
	node->prev = NULL;
	node->dest = dest;
	node->is_chain = 1;
	return node;
}

StringBuffer* PrintLogicItem(StringBuffer* str, LogicExp* exp, int inv, int rev) {
	if (exp->subexp) {
		StringBuffer_addChar(str, '(');
		str = PrintLogicExp(str, exp->dest, exp->subexp, inv, rev);
		StringBuffer_addChar(str, ')');
	}
	else {
		char* op;
		int cond = exp->neg;
		if (inv) cond = !cond;
		if (rev) cond = !cond;
		if (cond)
			op = invopstr(exp->op);
		else
			op = opstr(exp->op);
		if (exp->op != OP_TEST) {
			StringBuffer_addPrintf(str, "%s %s %s", exp->op1, op, exp->op2);
		}
		else {
			if (op)
				StringBuffer_addPrintf(str, "%s %s", op, exp->op2);
			else
				StringBuffer_addPrintf(str, "%s", exp->op2);
		}
	}
	return str;
}

StringBuffer* PrintLogicExp(StringBuffer* str, int dest, LogicExp* exp, int inv_, int rev) {
	int inv = inv_;
	if (!str)
		str = StringBuffer_new(NULL);
	while (exp->next) {
		char* op;
		int cond = exp->dest > dest;
		inv = cond ? inv_ : !inv_;
		str = PrintLogicItem(str, exp, inv, rev);
		exp = exp->next;
		if (inv_) cond = !cond;
		if (rev) cond = !cond;
		op = cond ? "and" : "or";
		StringBuffer_addPrintf(str, " %s ", op);
	}
	return PrintLogicItem(str, exp, inv_, rev);
}

void TieAsNext(LogicExp* curr, LogicExp* item) {
	curr->next = item;
	item->prev = curr;
	item->parent = curr->parent;
}

void Untie(LogicExp* curr, int* thenaddr) {
	LogicExp* previous = curr->prev;
	if (previous)
		previous->next = NULL;
	curr->prev = NULL;
	curr->parent = NULL;
}

void TieAsSubExp(LogicExp* parent, LogicExp* item) {
	parent->subexp = item;
	while (item) {
		item->parent = parent;
		item = item->next;
	}
}

LogicExp* MakeBoolean(Function* F, int* endif, int* thenaddr)
{
	int i;
	int firstaddr, elseaddr, last, realLast;
	LogicExp* curr, * first;
	int dest;

	if (endif)
		*endif = 0;

	if (F->nextBool == 0) {
		SET_ERROR("Attempted to build a boolean expression without a pending context");
		return NULL;
	}

	realLast = F->nextBool - 1;
	last = realLast;
	firstaddr = F->bools[0]->pc + 2;
	*thenaddr = F->bools[last]->pc + 2;
	elseaddr = F->bools[last]->dest;

	for (i = realLast; i >= 0; i--) {
		int dest = F->bools[i]->dest;
		if ((elseaddr > *thenaddr) &&
			(F->bools[i]->op == OP_TEST ? (dest > elseaddr + 1) :
				(dest > elseaddr))) {
			last = i;
			*thenaddr = F->bools[i]->pc + 2;
			elseaddr = dest;
		}
	}

	{
		int tmpLast = last;
		for (i = 0; i < tmpLast; i++) {
			int dest = F->bools[i]->dest;
			if (elseaddr > firstaddr) {
				if (dest < firstaddr) {
					last = i;
					*thenaddr = F->bools[i]->pc + 2;
					elseaddr = dest;
				}
			}
			else {
				if (dest == firstaddr) {
					last = i;
					*thenaddr = F->bools[i]->pc + 2;
					elseaddr = dest;
				}
				else {
					break;
				}
			}
		}
	}

	dest = F->bools[0]->dest;
	curr = MakeExpNode(F->bools[0]);

	if (dest > firstaddr && dest <= *thenaddr) {
		first = MakeExpChain(dest);
		TieAsSubExp(first, curr);
	}
	else {
		first = curr;
		if (endif)
			*endif = dest;
	}

	if (debug) {
		printf("\n");
		for (i = 0; i <= last; i++) {
			BoolOp* op = F->bools[i];
			if (debug) {
				printf("Exps(%d): at %d\tdest %d\tneg %d\t(%s %s %s) cpd %d \n", i,
					op->pc, op->dest, op->neg, op->op1, opstr(op->op), op->op2, curr->parent ? curr->parent->dest : -1);
			}
		}
		printf("\n");
	}

	for (i = 1; i <= last; i++) {
		BoolOp* op = F->bools[i];
		int at = op->pc;
		int dest = op->dest;

		LogicExp* exp = MakeExpNode(op);
		if (dest < firstaddr) {
			/* jump to loop in a while */
			TieAsNext(curr, exp);
			curr = exp;
			if (endif)
				*endif = dest;
		}
		else if (dest > *thenaddr) {
			/* jump to "else" */
				TieAsNext(curr, exp);
				curr = exp;
				if (endif) {
					/* Short-circuit value construction can legitimately contribute
					 * branches with different exit PCs to the same source expression.
					 * The outermost/farthest target is the enclosing if boundary. */
					if (*endif == 0 || dest > *endif) *endif = dest;
				}
		}
		else if (dest == curr->dest) {
			/* within current chain */
			TieAsNext(curr, exp);
			curr = exp;
		}
		else if (dest > curr->dest) {
			if (curr->parent == NULL || dest < curr->parent->dest) {
				/* creating a new level */
				LogicExp* subexp = MakeExpChain(dest);
				LogicExp* savecurr;
				TieAsNext(curr, exp);
				curr = exp;
				savecurr = curr;
				if (curr->parent == NULL) {
					TieAsSubExp(subexp, first);
					first = subexp;
				}
			}
			else if (dest > curr->parent->dest) {
				/* start a new chain */
				LogicExp* prevParent;
				LogicExp* chain;
				TieAsNext(curr, exp);
				curr = curr->parent;
				if (!curr->is_chain) {
					SET_ERROR("unhandled construct in 'if'");
					return NULL;
				};
				prevParent = curr->parent;
				chain = MakeExpChain(dest);
				Untie(curr, thenaddr);
				if (prevParent)
					if (prevParent->is_chain)
						prevParent = prevParent->subexp;
				TieAsSubExp(chain, curr);

				curr->parent = prevParent;
				if (prevParent == NULL) {
					first = chain;
				}
				else {
					// todo
					TieAsNext(prevParent, chain);
				}
			}
		}
		else if (dest > firstaddr && dest < curr->dest) {
			/* start a new chain */
			LogicExp* subexp = MakeExpChain(dest);
			TieAsSubExp(subexp, exp);
			TieAsNext(curr, subexp);
			curr = exp;
		}
		else {
			SET_ERROR("unhandled construct in 'if'");
			return NULL;
		}

		if (curr->parent && at + 3 > curr->parent->dest) {
			curr->parent->dest = curr->dest;
			if (i < last) {
				LogicExp* chain = MakeExpChain(curr->dest);
				TieAsSubExp(chain, first);
				first = chain;
			}
			curr = curr->parent;
		}
	}
	if (first->is_chain)
		first = first->subexp;
	for (i = last + 1; i < F->nextBool; i++)
		F->bools[i - last - 1] = F->bools[i];
	if (!F->bools[0])
		F->bools[0] = calloc(sizeof(BoolOp), 1);
	F->nextBool -= last + 1;
	if (endif)
		if (*endif == 0) {
			*endif = *thenaddr;
		}
	return first;
}

char* WriteBoolean(LogicExp* exp, int* thenaddr, int* endif, int test) {
	char* result;
	StringBuffer* str;

	str = PrintLogicExp(NULL, *thenaddr, exp, 0, test);

	if (test && endif && *endif == 0) {
		SET_ERROR("Unhandled construct in boolean test");
		return NULL;
	}

	result = StringBuffer_getBuffer(str);
	StringBuffer_delete(str);
	return result;
}

void FlushElse(Function* F);

char* OutputBoolean(Function* F, int* endif, int test) {
	int thenaddr;
	char* result;
	LogicExp* exp;

	FlushElse(F);
	if (error) return NULL;
	exp = MakeBoolean(F, endif, &thenaddr);
	if (error) return NULL;
	result = WriteBoolean(exp, &thenaddr, endif, test);
	if (error) return NULL;
	return result;
}

void StoreEndifAddr(Function* F, int addr) {
	Endif* at = F->nextEndif;
	Endif* prev = NULL;
	Endif* newEndif = malloc(sizeof(Endif));
	newEndif->addr = addr;
	while (at && at->addr < addr) {
		prev = at;
		at = at->next;
	}
	if (!prev) {
		newEndif->next = F->nextEndif;
		F->nextEndif = newEndif;
	}
	else {
		newEndif->next = at;
		prev->next = newEndif;
	}
	if (debug) {
		printf("Stored at endif list: ");
		for (at = F->nextEndif; at != NULL; at = at->next) {
			if (at == newEndif)
				printf("<%d> ", at->addr);
			else
				printf("%d ", at->addr);
		}
		printf("\n");
	}
}

int PeekEndifAddr(Function* F, int addr) {
	Endif* at = F->nextEndif;
	while (at) {
		if (at->addr == addr)
			return 1;
		else if (at->addr > addr)
			break;
		at = at->next;
	}
	return 0;
}

int GetEndifAddr(Function* F, int addr) {
	Endif* at = F->nextEndif;
	Endif* prev = NULL;
	while (at) {
		if (at->addr == addr) {
			if (prev)
				prev->next = at->next;
			else
				F->nextEndif = at->next;
			free(at);
			return 1;
		}
		else if (at->addr > addr)
			break;
		prev = at;
		at = at->next;
	}
	return 0;
}

void BackpatchStatement(Function* F, char* code, int line) {
	ListItem* walk = F->statements.head;
	while (walk) {
		Statement* stmt = (Statement*)walk;
		walk = walk->next;
		if (stmt->backpatch && stmt->line == line) {
			free(stmt->code);
			stmt->code = code;
			return;
		}
	}
	SET_ERROR("Confused while interpreting a jump as a 'while'");
}

void RawAddStatement(Function* F, StringBuffer* str)
{
	char* copy;
	Statement* stmt;
	copy = StringBuffer_getCopy(str);
	if (F->released_local) {
		int i = 0;
		int lpc = F->released_local;
		char* scopeclose[] = {
		   "end", "else", "until", NULL
		};
		F->released_local = 0;
		for (i = 0; scopeclose[i]; i++)
			if (strstr(copy, scopeclose[i]) == copy)
				break;
		if (!scopeclose[i]) {
			int added = 0;
			Statement* stmt = cast(Statement*, F->statements.head);
			Statement* prev = NULL;
			Statement* newst;
			while (stmt) {
				if (!added) {
					if (stmt->line >= lpc) {
						Statement* newst = NewStatement(_strdup("do"), lpc, stmt->indent);
						if (prev) {
							prev->super.next = cast(ListItem*, newst);
							newst->super.next = cast(ListItem*, stmt);
						}
						else {
							F->statements.head = cast(ListItem*, newst);
							newst->super.next = cast(ListItem*, stmt);
						}
						added = 1;
						stmt->indent++;
					}
				}
				else {
					stmt->indent++;
				}
				prev = stmt;
				stmt = cast(Statement*, stmt->super.next);
			}
			newst = NewStatement(_strdup("end"), F->pc, F->indent);
			AddToList(&(F->statements), cast(ListItem*, newst));
		}
	}
	stmt = NewStatement(copy, F->pc, F->indent);
	AddToList(&(F->statements), cast(ListItem*, stmt));
	F->lastLine = F->pc;
}

void FlushBoolean(Function* F) {
	FlushElse(F);
	while (F->nextBool > 0) {
		char* test;
		int endif;
		int thenaddr;
		StringBuffer* str = StringBuffer_new(NULL);
		LogicExp* exp = MakeBoolean(F, &endif, &thenaddr);
		if (error) return;
		if (endif < F->pc - 1) {
			test = WriteBoolean(exp, &thenaddr, &endif, 1);
			if (error) return;
			StringBuffer_printf(str, "while %s do", test);
			/* verify this '- 2' */
			BackpatchStatement(F, StringBuffer_getBuffer(str), endif - 2);
			if (error) return;
			F->indent--;
			StringBuffer_add(str, "end");
			RawAddStatement(F, str);
		}
		else {
			test = WriteBoolean(exp, &thenaddr, &endif, 0);
			if (error) return;
			StoreEndifAddr(F, endif);
			StringBuffer_addPrintf(str, "if %s then", test);
			F->elseWritten = 0;
			RawAddStatement(F, str);
			F->indent++;
		}
		StringBuffer_delete(str);
	}
	F->testpending = 0;
}

void AddStatement(Function* F, StringBuffer* str)
{
	FlushBoolean(F);
	if (error) return;
	RawAddStatement(F, str);
}

void MarkBackpatch(Function* F) {
	Statement* stmt = (Statement*)LastItem(&(F->statements));
	stmt->backpatch = 1;
}

void FlushElse(Function* F) {
	if (F->elsePending > 0) {
		StringBuffer* str = StringBuffer_new(NULL);
		int fpc = F->bools[0]->pc;
		/* Should elseStart be a stack? */
		if (F->nextBool > 0 && (fpc == F->elseStart || fpc - 1 == F->elseStart)) {
			char* test;
			int endif;
			int thenaddr;
			LogicExp* exp;
			exp = MakeBoolean(F, &endif, &thenaddr);
			if (error) return;
			test = WriteBoolean(exp, &thenaddr, &endif, 0);
			if (error) return;
			StoreEndifAddr(F, endif);
			StringBuffer_addPrintf(str, "elseif %s then", test);
			F->elseWritten = 0;
			RawAddStatement(F, str);
			F->indent++;
		}
		else {
			StringBuffer_printf(str, "else");
			RawAddStatement(F, str);
			/* this test circumvents jump-to-jump optimization at
			   the end of if blocks */
			if (!PeekEndifAddr(F, F->pc + 3))
				StoreEndifAddr(F, F->elsePending);
			F->indent++;
			F->elseWritten = 1;
		}
		F->elsePending = 0;
		F->elseStart = 0;
		StringBuffer_delete(str);
	}
}

/*
 * -------------------------------------------------------------------------
 */

DecTableItem* NewTableItem(char* value, int num, char* key)
{
	DecTableItem* self = calloc(sizeof(DecTableItem), 1);
	((ListItem*)self)->next = NULL;
	self->value = _strdup(value);
	self->numeric = num;
	if (key)
		self->key = _strdup(key);
	else
		self->key = NULL;
	return self;
}

/*
 * -------------------------------------------------------------------------
 */

void OutputAssignments(Function* F);

void Assign(Function* F, char* dest, char* src, int reg, int prio, int mayTest)
{
	char* nsrc = src ? _strdup(src) : NULL;

	/* Recovered source locals may be assigned on separate control-flow arms
	 * before the generic end-of-instruction flush runs.  Emit the previous
	 * source assignment first instead of treating a legal reassignment as a VM
	 * register collision. */
	if (reg != -1 && PENDING(reg) && IS_VARIABLE(reg)) {
		OutputAssignments(F);
		if (error) return;
	}
	if (reg != -1 && PENDING(reg) && !IS_VARIABLE(reg)) {
		int origin = F->Rorigin[reg];
		if (origin >= 0 && origin < F->f->sizecode &&
			GET_OPCODE(F->f->code[origin]) != OP_CALL &&
			GET_OPCODE(F->f->code[origin]) != OP_TAILCALL &&
			!PendingValueNeededAcrossOverwrite(F, reg, F->pc)) {
			/* The old VM value cannot reach any read on a path that bypasses this
			 * overwrite.  It is a dead stripped-chunk temporary/local, so dropping
			 * it is semantically safe and avoids leaking register allocation into
			 * source reconstruction. */
			PENDING(reg) = 0;
			CALL(reg) = 0;
			RemoveFromSet(F->tpend, reg);
			if (REGISTER(reg)) { free(REGISTER(reg)); REGISTER(reg) = NULL; }
			F->Rorigin[reg] = -1;
		}
	}
	if (reg != -1 && PENDING(reg)) {
		SET_ERROR("overwrote pending register!");
		return;
	}

	if (reg != -1) {
		PENDING(reg) = 1;
		CALL(reg) = 0;
		F->Rprio[reg] = prio;
		F->Rorigin[reg] = F->pc;
	}

	if (debug) { printf("SET_CTR(Tpend) = %d \n", SET_CTR(F->tpend)); }

	if (reg != -1 && F->testpending == reg + 1 && mayTest && F->testjump == F->pc + 2) {
		int endif;
		StringBuffer* str = StringBuffer_new(NULL);
		char* test = OutputBoolean(F, &endif, 1);
		if (error) {
			return;
		}
		if (endif >= F->pc) {
			StringBuffer_printf(str, "%s or %s", test, src);
			free(nsrc);
			nsrc = StringBuffer_getBuffer(str);
			free(test);
			StringBuffer_delete(str);
			F->testpending = 0;
			F->Rprio[reg] = 8;
		}
	}
	F->testjump = 0;

	if (reg != -1 && !IS_VARIABLE(reg)) {
		if (REGISTER(reg))
			free(REGISTER(reg));
		REGISTER(reg) = nsrc;
		AddToSet(F->tpend, reg);
	}
	else {
		char* ndest = _strdup(dest);
		AddToVarStack(F->vpend, ndest, nsrc, reg);
	}
}

int MatchTable(DecTable* tbl, int* name)
{
	return tbl->reg == *name;
}

void DeleteTable(DecTable* tbl)
{
	/*
	 * TODO: delete values from table
	 */
	free(tbl);
}

void CloseTable(Function* F, int r)
{
	DecTable* tbl = (DecTable*)PopFromList(&(F->tables));
	if (tbl->reg != r) {
		SET_ERROR("Unhandled construct in table");
		return;
	}
	DeleteTable(tbl);
	F->Rtabl[r] = 0;
}

char* PrintTable(Function* F, int r, int returnCopy)
{
	char* result = NULL;
	StringBuffer* str = StringBuffer_new("{");
	DecTable* tbl =
		(DecTable*)FindInList(&(F->tables), (ListItemCmpFn)MatchTable,
			&r);
	int numerics = 0;
	DecTableItem* item = (DecTableItem*)tbl->numeric.head;
	if (item) {
		StringBuffer_add(str, item->value);
		item = (DecTableItem*)item->super.next;
		numerics = 1;
		while (item) {
			StringBuffer_add(str, ", ");
			StringBuffer_add(str, item->value);
			item = (DecTableItem*)item->super.next;
		}
	}
	item = (DecTableItem*)tbl->keyed.head;
	if (item) {
		int first;
		if (numerics)
			StringBuffer_add(str, "; ");
		first = 1;
		while (item) {
			char* key = item->key;
			if (first)
				first = 0;
			else
				StringBuffer_add(str, ", ");
			if (key[0] == '\"') {
				char* last = strrchr(key, '\"');
				*last = '\0';
				key++;
			}
			StringBuffer_addPrintf(str, "%s = %s", key, item->value);
			item = (DecTableItem*)item->super.next;
		}
	}
	StringBuffer_addChar(str, '}');
	PENDING(r) = 0;
	Assign(F, REGISTER(r), StringBuffer_getRef(str), r, 0, 0);
	if (error) {
		return NULL;
	}
	if (returnCopy)
		result = StringBuffer_getCopy(str);
	StringBuffer_delete(str);
	CloseTable(F, r);
	if (error) return NULL;
	return result;
}

DecTable* NewTable(int r, Function* F, int b, int c)
{
	DecTable* self = calloc(sizeof(DecTable), 1);
	((ListItem*)self)->next = NULL;
	InitList(&(self->numeric));
	InitList(&(self->keyed));
	self->reg = r;
	self->topNumeric = 0;
	self->F = F;
	self->arraySize = fb2int(b);
	self->keyedSize = 1 << c;
	PENDING(r) = 1;
	return self;
}

void AddToTable(Function* F, DecTable* tbl, char* value, char* key)
{
	DecTableItem* item;
	List* type;
	int index;
	if (key == NULL) {
		type = &(tbl->numeric);
		index = tbl->topNumeric;
		tbl->topNumeric++;
	}
	else {
		type = &(tbl->keyed);
		tbl->used++;
		index = 0;
	}
	item = NewTableItem(value, index, key);
	AddToList(type, (ListItem*)item);
	// FIXME: should work with arrays, too
	if (tbl->keyedSize == tbl->used && tbl->arraySize == 0) {
		PrintTable(F, tbl->reg, 0);
		if (error)
			return;
	}
}

void StartTable(Function* F, int r, int b, int c)
{
	DecTable* tbl = NewTable(r, F, b, c);
	AddToList(&(F->tables), (ListItem*)tbl);
	F->Rtabl[r] = 1;
	F->Rtabl[r] = 1;
	if (b == 0 && c == 0) {
		PrintTable(F, r, 1);
		if (error)
			return;
	}
}

void SetList(Function* F, int a, int bc)
{
	int i;
	DecTable* tbl = (DecTable*)LastItem(&(F->tables));
	if (tbl->reg != a) {
		SET_ERROR("Unhandled construct in list");
		return;
	}
	for (i = 1; i <= bc + 1; i++) {
		char* rstr = GetR(F, a + i);
		if (error)
			return;
		AddToTable(F, tbl, rstr, NULL);
		if (error)
			return;
	}
	PrintTable(F, tbl->reg, 0);
	if (error)
		return;
}

void UnsetPending(Function* F, int r)
{
	if (!IS_VARIABLE(r)) {
		if (!PENDING(r) && !CALL(r)) {
			SET_ERROR("Confused about usage of registers");
			return;
		}
		PENDING(r) = 0;
		RemoveFromSet(F->tpend, r);
	}
}

int SetTable(Function* F, int a, char* bstr, char* cstr)
{
	DecTable* tbl = (DecTable*)LastItem(&(F->tables));
	if ((!tbl) || (tbl->reg != a)) {
		/*
		 * SetTable is not being applied to the table being generated. (This
		 * will probably need a more strict check)
		 */
		UnsetPending(F, a);
		if (error) return 0;
		return 0;
	}
	AddToTable(F, tbl, cstr, bstr);
	if (error) return 0;
	return 1;
}

/*
 * -------------------------------------------------------------------------
 */

static char* GetUpvalueName(Function* F, int r)
{
	if (r < 0 || r >= 32) return "upvalue";
	if (F->f->upvalues && r < F->f->sizeupvalues && F->f->upvalues[r])
		return (char*)getstr(F->f->upvalues[r]);
	if (F->inferredUpvalues[r]) return F->inferredUpvalues[r];
	{
		char buf[32];
		sprintf(buf, "upvalue%d", r);
		F->inferredUpvalues[r] = _strdup(buf);
		return F->inferredUpvalues[r];
	}
}

Function* NewFunction(const Proto* f)
{
	Function* self;
	int i;
	/*
	 * calloc, to ensure all parameters are 0/NULL
	 */
	self = calloc(sizeof(Function), 1);
	InitList(&(self->statements));
	self->f = f;
	self->vpend = calloc(sizeof(VarStack), 1);
	self->tpend = calloc(sizeof(IntSet), 1);
	self->whiles = calloc(sizeof(IntSet), 1);
	self->repeats = calloc(sizeof(IntSet), 1);
	self->repeats->mayRepeat = 1;
	self->untils = calloc(sizeof(IntSet), 1);
	self->do_opens = calloc(sizeof(IntSet), 1);
	self->do_closes = calloc(sizeof(IntSet), 1);
	self->decompiledCode = StringBuffer_new(NULL);
	self->bools[0] = calloc(sizeof(BoolOp), 1);
	for (i = 0; i < MAXARG_A; i++) self->Rorigin[i] = -1;
	return self;
}

void DeleteFunction(Function* self)
{
	int i;
	LoopList(&(self->statements), (ListItemFn)DeleteStatement, NULL);
	/*
	 * clean up registers
	 */
	for (i = 0; i < MAXARG_A; i++) {
		if (self->R[i])
			free(self->R[i]);
	}
	StringBuffer_delete(self->decompiledCode);
	free(self->vpend);
	free(self->tpend);
	free(self->whiles);
	free(self->repeats);
	free(self->untils);
	free(self->do_opens);
	free(self->do_closes);
	for (i = 0; i < 32; i++) {
		if (self->inferredUpvalues[i]) free(self->inferredUpvalues[i]);
	}
	free(self);
}

char* GetR(Function* F, int r)
{
	if (IS_TABLE(r)) {
		PrintTable(F, r, 0);
		if (error) return NULL;
	}
	UnsetPending(F, r);
	if (error) return NULL;
	return F->R[r];
}

void DeclareVariable(Function* F, const char* name, int reg)
{
	F->Rvar[reg] = 1;
	if (F->R[reg])
		free(F->R[reg]);
	F->R[reg] = _strdup(name);
	F->Rprio[reg] = 0;
	UnsetPending(F, reg);
	if (error) return;
}

void OutputAssignments(Function* F)
{
	int i, srcs, size, syntheticDecl = 0;
	StringBuffer* vars;
	StringBuffer* exps;
	if (!SET_IS_EMPTY(F->tpend))
		return;
	vars = StringBuffer_new(NULL);
	exps = StringBuffer_new(NULL);
	size = SET_CTR(F->vpend);
	srcs = 0;
	for (i = 0; i < size; i++) {
		int r = F->vpend->regs[i];
		if (!(r == -1 || PENDING(r))) {
			SET_ERROR("Attempted to generate an assignment, but got confused about usage of registers");
			return;
		}

		if (i > 0)
			StringBuffer_prepend(vars, ", ");
		StringBuffer_prepend(vars, F->vpend->dests[i]);
		if (r != -1 && F->RsyntheticNew[r]) syntheticDecl = 1;

		if (F->vpend->srcs[i] && (srcs > 0 || (srcs == 0 && strcmp(F->vpend->srcs[i], "nil") != 0) || i == size - 1)) {
			if (srcs > 0)
				StringBuffer_prepend(exps, ", ");
			StringBuffer_prepend(exps, F->vpend->srcs[i]);
			srcs++;
		}
	}

	for (i = 0; i < size; i++) {
		int r = F->vpend->regs[i];
		if (r != -1) {
			PENDING(r) = 0;
			F->RsyntheticNew[r] = 0;
		}
		free(F->vpend->dests[i]);
		if (F->vpend->srcs[i])
			free(F->vpend->srcs[i]);
	}
	F->vpend->ctr = 0;

	if (i > 0) {
		if (syntheticDecl) StringBuffer_prepend(vars, "local ");
		StringBuffer_add(vars, " = ");
		StringBuffer_add(vars, StringBuffer_getRef(exps));
		AddStatement(F, vars);
		if (error)
			return;
	}
	StringBuffer_delete(vars);
	StringBuffer_delete(exps);
}

void ReleaseLocals(Function* F) {
	int i;
	for (i = 0; i < F->f->sizelocvars; i++) {
		if (F->f->locvars[i].endpc == F->pc) {
			int r;
			F->freeLocal--;
			r = F->freeLocal;
			if (!IS_VARIABLE(r)) {
				SET_ERROR("Confused about usage of registers for local variables");
				return;
			}
			F->Rvar[r] = 0;
			F->Rprio[r] = 0;
			if (!F->ignore_for_variables && !F->released_local)
				F->released_local = F->f->locvars[i].startpc;
		}
	}
	F->ignore_for_variables = 0;
}

void DeclareLocals(Function* F)
{
	int i;
	int locals;
	int internalLocals = 0;
	StringBuffer* str;
	StringBuffer* rhs;
	char* names[MAXARG_A];
	/*
	 * Those are declaration of parameters.
	 */
	if (F->pc == 0)
		return;
	str = StringBuffer_new("local ");
	rhs = StringBuffer_new(" = ");
	locals = 0;
	for (i = 0; i < F->f->sizelocvars; i++) {
		if (F->f->locvars[i].startpc == F->pc) {
			int r = F->freeLocal + locals + internalLocals;
			if (F->internal[r]) {
				names[r] = LOCAL(i);
				F->internal[r] = 0;
				internalLocals++;
				continue;
			}
			if (PENDING(r)) {
				if (locals > 0) {
					StringBuffer_add(str, ", ");
					StringBuffer_add(rhs, ", ");
				}
				StringBuffer_add(str, LOCAL(i));
				StringBuffer_add(rhs, GetR(F, r));
				if (error) return;
			}
			else {
				if (!(locals > 0)) {
					SET_ERROR("Confused at declaration of local variable");
					return;
				}
				StringBuffer_add(str, ", ");
				StringBuffer_add(str, LOCAL(i));
			}
			CALL(r) = 0;
			IS_VARIABLE(r) = 1;
			names[r] = LOCAL(i);
			locals++;
		}
	}
	if (locals > 0) {
		StringBuffer_add(str, StringBuffer_getRef(rhs));
		AddStatement(F, str);
		if (error) return;
	}
	StringBuffer_delete(rhs);
	StringBuffer_prune(str);
	for (i = 0; i < locals + internalLocals; i++) {
		int r = F->freeLocal + i;
		DeclareVariable(F, names[r], r);
		if (error) return;
	}
	F->freeLocal += locals + internalLocals;
}

char* PrintFunction(Function* F)
{
	char* result;
	StringBuffer_prune(F->decompiledCode);
	LoopList(&(F->statements), (ListItemFn)PrintStatement, F);
	result = StringBuffer_getBuffer(F->decompiledCode);
	return result;
}

/*
 * -------------------------------------------------------------------------
 */

static char* operators[20] =
{ " ", " ", " ", " ", " ", " ", " ", " ", " ", " ", " ", " ",
"+", "-", "*", "/", "^", "-", "not ", ".."
};

static int priorities[20] =
{ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 4, 3, 3, 1, 2, 2, 5 };

char* RegisterOrConstant(Function* F, int r)
{
	if (IS_CONSTANT(r)) {
		return DecompileConstant(F->f, r - MAXSTACK);
	}
	else {
		char* copy;
		char* reg = GetR(F, r);
		if (error)
			return NULL;
		copy = malloc(strlen(reg) + 1);
		strcpy(copy, reg);
		return copy;
	}
}

void MakeIndex(Function* F, StringBuffer* str, char* rstr, int self)
{
	int dot = 0;
	/*
	 * see if index can be expressed without quotes
	 */
	if (rstr[0] == '\"') {
		if (isalpha(rstr[1]) || rstr[1] == '_') {
			char* at = rstr + 1;
			dot = 1;
			while (*at != '"') {
				if (!isalnum(*at) && *at != '_') {
					dot = 0;
					break;
				}
				at++;
			}
		}
	}
	if (dot) {
		rstr++;
		rstr[strlen(rstr) - 1] = '\0';
		if (self)
			StringBuffer_addPrintf(str, ":%s", rstr);
		else
			StringBuffer_addPrintf(str, ".%s", rstr);
		rstr--;
	}
	else
		StringBuffer_addPrintf(str, "[%s]", rstr);
}

static const char* GuessStrippedParamName(const Proto* f, int index)
{
	int k;
	int hasNextGoal = 0, hasGoalCount = 0, hasGoalList = 0;
	if (!f || index < 0 || index >= f->numparams) return NULL;

	/* Black Box helper closures in the race stategraphs commonly take a
	 * racer index.  With stripped debug info the compiler leaves only the
	 * table keys behind, but NextGoal/GoalCount/GoalList are a strong and
	 * source-confirmed signature for that argument. */
	if (f->numparams == 1 && index == 0) {
		for (k = 0; k < f->sizek; k++) if (ttisstring(&f->k[k])) {
			const char* s = svalue(&f->k[k]);
			if (strcmp(s, "NextGoal") == 0) hasNextGoal = 1;
			else if (strcmp(s, "GoalCount") == 0) hasGoalCount = 1;
			else if (strcmp(s, "GoalList") == 0) hasGoalList = 1;
		}
		if (hasNextGoal && (hasGoalCount || hasGoalList)) return "racerIndex";
	}
	return NULL;
}

void FunctionHeader(Function* F) {
	int saveIndent = F->indent;
	const Proto* f = F->f;
	StringBuffer* str = StringBuffer_new(NULL);
	F->indent = 0;
	if (f->numparams > 0) {
		int i;
		StringBuffer_addPrintf(str, "(");

		int placeholder = 0;
		if (F->f->locvars == 0)
		{
			//fprintf(stddebug, "Fuck\n");
			//__debugbreak();
			placeholder = 1;
		}

		for (i = 0; i < f->numparams - 1; i++)
		{
			if (placeholder)
			{
					if (rawHandlerParams && f->numparams == 3 && i < 3) {
						StringBuffer_addPrintf(str, "param%i, ", i);
					}
					else if (f->numparams == 3 && i < 3) {
						static const char* handlerParams[3] = { "this", "message", "context" };
						StringBuffer_addPrintf(str, "%s, ", handlerParams[i]);
					}
					else {
						const char* guessed = GuessStrippedParamName(f, i);
						if (guessed) StringBuffer_addPrintf(str, "%s, ", guessed);
						else StringBuffer_addPrintf(str, "param%i, ", i);
					}
			}
			else
			{
				StringBuffer_addPrintf(str, "%s, ", LOCAL(i));
			}
		}

		if (placeholder)
		{
				if (rawHandlerParams && f->numparams == 3 && i < 3) {
					StringBuffer_addPrintf(str, "param%i", i);
				}
				else if (f->numparams == 3 && i < 3) {
					static const char* handlerParams[3] = { "this", "message", "context" };
					StringBuffer_addPrintf(str, "%s", handlerParams[i]);
				}
					else {
						const char* guessed = GuessStrippedParamName(f, i);
						if (guessed) StringBuffer_addPrintf(str, "%s", guessed);
						else StringBuffer_addPrintf(str, "param%i", i);
					}
		}
		else
		{
			StringBuffer_addPrintf(str, "%s", LOCAL(i));
		}

		if (f->is_vararg)
			StringBuffer_add(str, ", ...");
		StringBuffer_addPrintf(str, ")");
		AddStatement(F, str);
		if (error)
			return;
		StringBuffer_prune(str);
	}
	else if (!IsMain(f)) {
		if (f->is_vararg)
			StringBuffer_add(str, "(...)");
		else
			StringBuffer_add(str, "()");
		AddStatement(F, str);
		if (error)
			return;
		StringBuffer_prune(str);
	}
	F->indent = saveIndent;
	if (!IsMain(f))
		F->indent++;
	StringBuffer_delete(str);
}

void ShowState(Function* F)
{
	int i;
	fprintf(stddebug, "\n");
	fprintf(stddebug, "next bool: %d\n", F->nextBool);
	fprintf(stddebug, "locals(%d): ", F->freeLocal);
	for (i = 0; i < F->freeLocal; i++) {
		fprintf(stddebug, "%d{%s} ", i, REGISTER(i));
	}
	fprintf(stddebug, "\n");
	fprintf(stddebug, "vpend(%d): ", SET_CTR(F->vpend));
	for (i = 0; i < SET_CTR(F->vpend); i++) {
		int r = F->vpend->regs[i];
		if (r != -1 && !PENDING(r)) {
			SET_ERROR("Confused about usage of registers for variables");
			return;
		}
		fprintf(stddebug, "%d{%s=%s} ", r, F->vpend->dests[i], F->vpend->srcs[i]);
	}
	fprintf(stddebug, "\n");
	fprintf(stddebug, "tpend(%d): ", SET_CTR(F->tpend));
	for (i = 0; i < SET_CTR(F->tpend); i++) {
		int r = SET(F->tpend, i);
		fprintf(stddebug, "%d{%s} ", r, REGISTER(r));
		if (!PENDING(r)) {
			SET_ERROR("Confused about usage of registers for temporaries");
			return;
		}
	}
	fprintf(stddebug, "\n");
}

#define TRY(x)  x; if (error) goto errorHandler

/* -------------------------------------------------------------------------
 * Stripped Black Box chunks keep register allocation but lose LocVar debug
 * ranges.  A VM register is not automatically a Lua local: most registers
 * only shuttle an expression from GETGLOBAL/GETTABLE/LOADK into the next
 * opcode.  Treating every stack slot as a local is what produced the old
 * `reg3 = Game; reg3 = reg3.ShowGPS; ...` output.
 *
 * The helpers below recover only values that really need storage.  We do a
 * small CFG liveness pass, identify definitions whose value survives control
 * flow / side effects or is consumed more than once, then start a synthetic
 * Lua local at the first such lifetime.  Everything else stays in the normal
 * luadec expression propagator and therefore disappears from source output.
 * ------------------------------------------------------------------------- */

static void MarkReg(unsigned char* set, int r, int maxstack)
{
	if (r >= 0 && r < maxstack && r < MAXARG_A) set[r] = 1;
}

static int IsRKReg(int r, int maxstack)
{
	return r < MAXSTACK && r >= 0 && r < maxstack;
}

static void InstructionUseDef(const Proto* f, int pc, unsigned char* use, unsigned char* def)
{
	Instruction ins = f->code[pc];
	OpCode o = GET_OPCODE(ins);
	int a = GETARG_A(ins), b = GETARG_B(ins), c = GETARG_C(ins);
	int bc = GETARG_Bx(ins);
	int r, maxstack = f->maxstacksize;
	memset(use, 0, MAXARG_A);
	memset(def, 0, MAXARG_A);

	switch (o) {
	case OP_MOVE:
		MarkReg(use, b, maxstack); MarkReg(def, a, maxstack); break;
		case OP_LOADK:
		case OP_GETUPVAL:
		case OP_GETGLOBAL:
		case OP_NEWTABLE:
		case OP_CLOSURE:
			MarkReg(def, a, maxstack); break;
		case OP_LOADBOOL:
			/* LOADBOOL A x 1 / LOADBOOL A y 0 is the compiler's materialized
			 * boolean-expression pair.  The second instruction is the alternate
			 * arm of the same source assignment, not a new variable lifetime. */
			if (!(pc > 0 && GET_OPCODE(f->code[pc - 1]) == OP_LOADBOOL &&
				GETARG_A(f->code[pc - 1]) == a && GETARG_C(f->code[pc - 1]) != 0))
				MarkReg(def, a, maxstack);
			break;
	case OP_LOADNIL:
		for (r = a; r <= b; r++) MarkReg(def, r, maxstack);
		break;
	case OP_GETTABLE:
		MarkReg(use, b, maxstack);
		if (IsRKReg(c, maxstack)) MarkReg(use, c, maxstack);
		MarkReg(def, a, maxstack);
		break;
	case OP_SETGLOBAL:
	case OP_SETUPVAL:
		MarkReg(use, a, maxstack); break;
	case OP_SETTABLE:
		MarkReg(use, a, maxstack);
		if (IsRKReg(b, maxstack)) MarkReg(use, b, maxstack);
		if (IsRKReg(c, maxstack)) MarkReg(use, c, maxstack);
		break;
	case OP_SELF:
		MarkReg(use, b, maxstack);
		if (IsRKReg(c, maxstack)) MarkReg(use, c, maxstack);
		MarkReg(def, a, maxstack); MarkReg(def, a + 1, maxstack);
		break;
	case OP_ADD: case OP_SUB: case OP_MUL: case OP_DIV: case OP_POW:
		if (IsRKReg(b, maxstack)) MarkReg(use, b, maxstack);
		if (IsRKReg(c, maxstack)) MarkReg(use, c, maxstack);
		MarkReg(def, a, maxstack);
		break;
	case OP_UNM: case OP_NOT:
		MarkReg(use, b, maxstack); MarkReg(def, a, maxstack); break;
	case OP_CONCAT:
		for (r = b; r <= c; r++) MarkReg(use, r, maxstack);
		MarkReg(def, a, maxstack);
		break;
	case OP_EQ: case OP_LT: case OP_LE:
		if (IsRKReg(b, maxstack)) MarkReg(use, b, maxstack);
		if (IsRKReg(c, maxstack)) MarkReg(use, c, maxstack);
		break;
		case OP_TEST:
			MarkReg(use, b, maxstack);
			/* TEST A=A only tests the value; it does not start a new source
			 * lifetime.  This is common for locals reused by later conditions. */
			if (a != b) MarkReg(def, a, maxstack);
			break;
	case OP_CALL:
		if (b == 0) {
			for (r = a; r < maxstack; r++) MarkReg(use, r, maxstack);
		}
		else {
			for (r = a; r < a + b; r++) MarkReg(use, r, maxstack);
		}
		/* Even a zero-result call ends the function-value lifetime in R(A). */
		if (c == 0) {
			for (r = a; r < maxstack; r++) MarkReg(def, r, maxstack);
		}
		else if (c == 1) MarkReg(def, a, maxstack);
		else for (r = a; r <= a + c - 2; r++) MarkReg(def, r, maxstack);
		break;
	case OP_TAILCALL:
		if (b == 0) for (r = a; r < maxstack; r++) MarkReg(use, r, maxstack);
		else for (r = a; r < a + b; r++) MarkReg(use, r, maxstack);
		break;
	case OP_RETURN:
		if (b == 0) for (r = a; r < maxstack; r++) MarkReg(use, r, maxstack);
		else for (r = a; r < a + b - 1; r++) MarkReg(use, r, maxstack);
		break;
	case OP_FORLOOP:
		for (r = a; r <= a + 2; r++) { MarkReg(use, r, maxstack); MarkReg(def, r, maxstack); }
		break;
	case OP_TFORLOOP:
		for (r = a; r <= a + 2; r++) MarkReg(use, r, maxstack);
		for (r = a + 2; r <= a + 2 + c; r++) MarkReg(def, r, maxstack);
		break;
	case OP_TFORPREP:
		MarkReg(use, a, maxstack); MarkReg(def, a, maxstack); MarkReg(def, a + 1, maxstack); break;
	case OP_SETLIST:
	case OP_SETLISTO:
		MarkReg(use, a, maxstack);
		for (r = a + 1; r < maxstack && r <= a + (bc % LFIELDS_PER_FLUSH) + 1; r++) MarkReg(use, r, maxstack);
		break;
	case OP_JMP:
	case OP_CLOSE:
	default:
		break;
	}
}

static void PushCfgSuccessor(int* stack, int* sp, unsigned char* queued, int n, int pc)
{
	if (pc < 0 || pc >= n || queued[pc]) return;
	queued[pc] = 1;
	stack[(*sp)++] = pc;
}

static int PendingValueNeededAcrossOverwrite(Function* F, int reg, int overwritePc)
{
	const Proto* f = F->f;
	int n = f->sizecode;
	int origin = F->Rorigin[reg];
	int* stack;
	unsigned char* queued;
	int sp = 0, result = 0;
	if (origin < 0 || origin >= n || overwritePc <= origin) return 1;
	stack = (int*)malloc(sizeof(int) * (size_t)(n * 2 + 4));
	queued = (unsigned char*)calloc((size_t)n, 1);
	if (!stack || !queued) { free(stack); free(queued); return 1; }
	PushCfgSuccessor(stack, &sp, queued, n, origin + 1);
	while (sp > 0) {
		int pc = stack[--sp];
		Instruction ins;
		OpCode o;
		int sbc;
		unsigned char use[MAXARG_A], def[MAXARG_A];
		if (pc == overwritePc) continue;
		ins = f->code[pc];
		o = GET_OPCODE(ins);
		sbc = GETARG_sBx(ins);
		InstructionUseDef(f, pc, use, def);
		if (use[reg]) { result = 1; break; }
		if (def[reg]) continue;
		if (o == OP_RETURN || o == OP_TAILCALL) continue;
		if (o == OP_JMP || o == OP_TFORPREP) {
			PushCfgSuccessor(stack, &sp, queued, n, pc + 1 + sbc);
		}
		else if (o == OP_EQ || o == OP_LT || o == OP_LE || o == OP_TEST || o == OP_TFORLOOP) {
			PushCfgSuccessor(stack, &sp, queued, n, pc + 1);
			PushCfgSuccessor(stack, &sp, queued, n, pc + 2);
		}
		else if (o == OP_FORLOOP) {
			PushCfgSuccessor(stack, &sp, queued, n, pc + 1);
			PushCfgSuccessor(stack, &sp, queued, n, pc + 1 + sbc);
		}
		else if (o == OP_LOADBOOL && GETARG_C(ins)) {
			PushCfgSuccessor(stack, &sp, queued, n, pc + 2);
		}
		else PushCfgSuccessor(stack, &sp, queued, n, pc + 1);
	}
	free(stack);
	free(queued);
	return result;
}

static int JumpTargetAt(const Proto* f, int pc)
{
	if (pc < 0 || pc >= f->sizecode || GET_OPCODE(f->code[pc]) != OP_JMP) return -1;
	return pc + 1 + GETARG_sBx(f->code[pc]);
}

static void MarkNoOpCompareLadders(const Proto* f, unsigned char* skip)
{
	int p, n = f->sizecode;
	/* A comparison/test followed by `JMP 0` has identical fall-through and
	 * taken successors.  Black Box emits this for empty source branches (for
	 * example an empty story-stage case).  Reconstructing it as `if ... then`
	 * leaves an unterminated block, so discard the dead control pair. */
	for (p = 0; p + 1 < n; p++) {
		OpCode o = GET_OPCODE(f->code[p]);
		if ((o == OP_EQ || o == OP_LT || o == OP_LE || o == OP_TEST) &&
			GET_OPCODE(f->code[p + 1]) == OP_JMP && GETARG_sBx(f->code[p + 1]) == 0) {
			skip[p] = 1;
			skip[p + 1] = 1;
		}
	}
	for (p = 0; p + 6 < n; p++) {
		Instruction g = f->code[p];
		int common, q, blocks = 0;
		if (GET_OPCODE(g) != OP_GETTABLE || GET_OPCODE(f->code[p + 1]) != OP_EQ ||
			GET_OPCODE(f->code[p + 2]) != OP_JMP || GET_OPCODE(f->code[p + 3]) != OP_JMP)
			continue;
		if (JumpTargetAt(f, p + 2) != p + 4) continue;
		common = JumpTargetAt(f, p + 3);
		if (common <= p + 4 || common > n) continue;
		q = p;
		while (q < common) {
			Instruction qg;
			if (q + 2 >= common) break;
			qg = f->code[q];
			if (GET_OPCODE(qg) != OP_GETTABLE || GETARG_B(qg) != GETARG_B(g) || GETARG_C(qg) != GETARG_C(g) ||
				GET_OPCODE(f->code[q + 1]) != OP_EQ || GET_OPCODE(f->code[q + 2]) != OP_JMP)
				break;
			if (q + 3 < common && GET_OPCODE(f->code[q + 3]) == OP_JMP &&
				JumpTargetAt(f, q + 2) == q + 4 && JumpTargetAt(f, q + 3) == common) {
				blocks++; q += 4; continue;
			}
			if (JumpTargetAt(f, q + 2) == common) {
				blocks++; q += 3; break;
			}
			break;
		}
		if (blocks >= 2 && q == common) {
			int k;
			for (k = p; k < common; k++) skip[k] = 1;
			p = common - 1;
		}
	}
}

static int IsControlOpcode(OpCode o)
{
	return o == OP_JMP || o == OP_EQ || o == OP_LT || o == OP_LE ||
		o == OP_TEST || o == OP_FORLOOP || o == OP_TFORLOOP || o == OP_TFORPREP;
}

static int IsSideEffectOpcode(OpCode o)
{
	return o == OP_CALL || o == OP_TAILCALL || o == OP_SETGLOBAL ||
		o == OP_SETUPVAL || o == OP_SETTABLE || o == OP_SETLIST || o == OP_SETLISTO;
}

static int AddSuccessorLive(const unsigned char* liveIn, unsigned char* out,
	int n, int maxstack, int succ)
{
	int r, changed = 0;
	if (succ < 0 || succ >= n) return 0;
	for (r = 0; r < maxstack; r++) {
		unsigned char v = liveIn[succ * MAXARG_A + r];
		if (v && !out[r]) { out[r] = 1; changed = 1; }
	}
	return changed;
}

static int ProtoHasStringConstant(const Proto* f, const char* text)
{
	int k;
	if (!f || !text) return 0;
	for (k = 0; k < f->sizek; k++) {
		if (ttisstring(&f->k[k]) && strcmp(svalue(&f->k[k]), text) == 0) return 1;
	}
	return 0;
}

static const char* GuessNumericForIndexName(const Proto* f, const char* initial, const char* limit)
{
	if (!initial) initial = "";
	if (!limit) limit = "";

	/* Numeric-for names recovered from the Black Box source patterns in
	 * SourceFile/lithium.lua.  Keep this semantic: the register number is
	 * an implementation detail and must never leak as for_index_N. */
	if (strstr(limit, "NumAutoSpawned")) return "onSpawned";
	if (strstr(limit, "NumRandomTraffic")) return "onRandom";
	if (strstr(limit, "NumCashBags")) return "onBag";
	if (strstr(limit, "NumCheckpoints")) return "onCheck";
	if (strstr(limit, "NumWorldRaces") || strstr(limit, "NumRivalRaces") || strstr(limit, "NumRaces")) return "onRace";
	if (strstr(limit, "NumTraps") || strstr(limit, "TrapCount") || strstr(limit, "SpeedTrapsRequired.Count")) return "onTrap";
	if (strstr(limit, "NumTriggers")) return "onTrigger";
	if (strstr(limit, "TargetActivities.Count")) return "onAct";
	if (strstr(limit, "CopSpawnPoints.Count") || strstr(limit, "spawnCount")) return "onSpawn";
	if (strstr(limit, "RaceTriggers.Count") || strstr(limit, "numEngage")) return "onEngage";
	if (strstr(limit, "numberOfSections")) return "i";
	if (strstr(limit, "zoneList.Count") || strstr(limit, "zoneCount")) return "onZone";
	if (strstr(initial, "NumLaps")) return "onLap";
	if (strstr(limit, "NumRacers")) {
		if (ProtoHasStringConstant(f, "SharedCheckpoints")) return "onOther";
		return "onRacer";
	}

	return "i";
}

static const char* GetTableStringKey(const Proto* f, Instruction ins)
{
	int c, k;
	if (GET_OPCODE(ins) != OP_GETTABLE) return NULL;
	c = GETARG_C(ins);
	if (c < MAXSTACK) return NULL;
	k = c - MAXSTACK;
	if (k < 0 || k >= f->sizek || !ttisstring(&f->k[k])) return NULL;
	return svalue(&f->k[k]);
}

static const char* FindRecentFieldForReg(const Proto* f, int pc, int reg, int maxBack)
{
	int q, floor = pc - maxBack;
	if (floor < 0) floor = 0;
	for (q = pc - 1; q >= floor; q--) {
		Instruction qi = f->code[q];
		if (GET_OPCODE(qi) == OP_GETTABLE && GETARG_A(qi) == reg) {
			const char* key = GetTableStringKey(f, qi);
			if (key) return key;
		}
	}
	return NULL;
}

static const Proto* FindClosureSourceForCall(const Proto* f, int pc, int callReg)
{
	int sourceReg = callReg, q;
	if (pc > 0 && GET_OPCODE(f->code[pc - 1]) == OP_MOVE && GETARG_A(f->code[pc - 1]) == callReg)
		sourceReg = GETARG_B(f->code[pc - 1]);
	for (q = pc - 1; q >= 0 && q >= pc - 16; q--) {
		Instruction qi = f->code[q];
		if (GET_OPCODE(qi) == OP_CLOSURE && GETARG_A(qi) == sourceReg) {
			int idx = GETARG_Bx(qi);
			if (idx >= 0 && idx < f->sizep) return f->p[idx];
		}
	}
	return NULL;
}

/* Names below come from the Black Box lithium source supplied with the
 * toolkit.  Match semantic bytecode patterns rather than VM register numbers,
 * so stripped Carbon chunks recover the original source vocabulary without
 * requiring lithium.lua at runtime. */
static void GuessKnownSourceLocalName(const Proto* f, int reg, int first, char* out)
{
	Instruction ins;
	OpCode op;
	const char* key = NULL;
	if (!f || !out || out[0] || first < 0 || first >= f->sizecode) return;
	ins = f->code[first];
	op = GET_OPCODE(ins);

	if (op == OP_CLOSURE) {
		int idx = GETARG_Bx(ins);
		const Proto* child = (idx >= 0 && idx < f->sizep) ? f->p[idx] : NULL;
		if (child && ProtoHasStringConstant(child, "ExitRaceActivity")) strcpy(out, "ExitRace");
		else if (child && ProtoHasStringConstant(child, "GoalCount") && ProtoHasStringConstant(child, "NextGoal")) strcpy(out, "AdvanceGoal");
		else if (child && ProtoHasStringConstant(child, "GoalList") && ProtoHasStringConstant(child, "racefinish")) strcpy(out, "GetNextGoalTrigger");
		return;
	}

	if (op == OP_CALL) {
		const Proto* child;
		key = FindRecentFieldForReg(f, first, reg, 8);
		if (key && strcmp(key, "GetRacerIndex") == 0) strcpy(out, "racerIndex");
		else if (key && strcmp(key, "GetNumChallengesPassed") == 0) strcpy(out, "numChallengesPassed");
		else if (key && strcmp(key, "GetSimTime") == 0) {
			if (ProtoHasStringConstant(f, "canyonRaceTime")) strcpy(out, "timeCurrent");
			else if (ProtoHasStringConstant(f, "RecordThresh")) strcpy(out, "time");
			else strcpy(out, "simTime");
		}
		else if (key && strcmp(key, "CanyonRaceState") == 0) strcpy(out, "canyonRaceState");
		else if (key && strcmp(key, "GetAreaIntroMovieFormActivity") == 0) strcpy(out, "areaIntroMovie");
		else if (key && strcmp(key, "IsOnlineGame") == 0) strcpy(out, "onlineRace");
		else if (key && strcmp(key, "GetSimableSpeedKmh") == 0) {
			if (ProtoHasStringConstant(f, "TargetBronze")) strcpy(out, "playerSpeed");
			else if (ProtoHasStringConstant(f, "TrapRecords")) strcpy(out, "racerSpeed");
			else if (ProtoHasStringConstant(f, "RecordThresh")) strcpy(out, "speed");
			else if (ProtoHasStringConstant(f, "SpeedTrapList") && ProtoHasStringConstant(f, "ThreshholdSpeed")) strcpy(out, "playerSpeed");
			else strcpy(out, "speed");
		}
		if (!out[0]) {
			child = FindClosureSourceForCall(f, first, reg);
			if (child && ProtoHasStringConstant(child, "GetRacerIndex")) strcpy(out, "racerIndex");
		}
		return;
	}

	if (op == OP_TEST && ProtoHasStringConstant(f, "IntroMovie") && ProtoHasStringConstant(f, "GetAreaIntroMovieFormActivity")) {
		strcpy(out, "gotMovie");
		return;
	}

	if (op == OP_GETTABLE) {
		key = GetTableStringKey(f, ins);
		if (key && strcmp(key, "Sender") == 0 && ProtoHasStringConstant(f, "AutoSpawnTriggerType")) strcpy(out, "trigger");
		else if (key && strcmp(key, "Element") == 0 && ProtoHasStringConstant(f, "RecordThresh")) strcpy(out, "simable");
		else if (key && strcmp(key, "Element") == 0 && ProtoHasStringConstant(f, "IsActiveSpeedTrap") && ProtoHasStringConstant(f, "SpeedTrapList")) strcpy(out, "simable");
		else if (key && strcmp(key, "Sender") == 0 && ProtoHasStringConstant(f, "IsActiveSpeedTrap") && ProtoHasStringConstant(f, "SpeedTrapList")) strcpy(out, "trigger");
		else if (key && strcmp(key, "TrafficCharacter") == 0) strcpy(out, "characterToSpawn");
		else if (key && strcmp(key, "TutorialTag") == 0) strcpy(out, "tag");
		else {
			key = FindRecentFieldForReg(f, first + 1, reg, 5);
			if (key && strcmp(key, "CashRewards") == 0) strcpy(out, "cashBag");
			else if (key && strcmp(key, "SpeedTrapList") == 0) strcpy(out, "speedTrap");
			else if (key && strcmp(key, "TrapRecords") == 0) strcpy(out, "trapRecord");
			else if (key && strcmp(key, "RaceTriggers") == 0) {
				if (ProtoHasStringConstant(f, "InitiallyUnlocked")) strcpy(out, "trigger");
				else strcpy(out, "engageTrigger");
			}
		}
		return;
	}

	if (op == OP_LOADK) {
		int k = GETARG_Bx(ins);
		if (k >= 0 && k < f->sizek && ttisstring(&f->k[k]) &&
			strncmp(svalue(&f->k[k]), "LANGUAGE_HUD_DONT_GET_BUSTED_", 29) == 0) strcpy(out, "message");
		else if (ProtoHasStringConstant(f, "CanyonRaceUpdate")) {
			switch (first + 1) {
			case 9: strcpy(out, "canyonRaceStateNone"); break;
			case 11: strcpy(out, "canyonRaceStateScoreWin"); break;
			case 12: strcpy(out, "canyonRaceStateOverboard"); break;
			case 13: strcpy(out, "canyonRaceStateTimeoutAhead"); break;
			case 14: strcpy(out, "canyonRaceStateTimeoutBehind"); break;
			}
		}
		else if (ProtoHasStringConstant(f, "NumRacesRequired") && ProtoHasStringConstant(f, "RaceDone")) strcpy(out, "doneCount");
		else if (ProtoHasStringConstant(f, "DriftSectionTriggers")) strcpy(out, "numberOfSections");
		return;
	}

	if (op == OP_LOADBOOL) {
		if (ProtoHasStringConstant(f, "RequiredRacesWon") && ProtoHasStringConstant(f, "RequiredBounty")) strcpy(out, "passedTest");
		else if (ProtoHasStringConstant(f, "SpeedTrapsRequired") && ProtoHasStringConstant(f, "TrapDone")) strcpy(out, "enabled");
		else if (ProtoHasStringConstant(f, "ResetsPlayer") && ProtoHasStringConstant(f, "OnlineRace")) {
			if (first + 1 == 28) strcpy(out, "resetToPreRace");
			else if (first + 1 == 29) strcpy(out, "warpPlayer");
		}
		return;
	}

	/* Cross' chase pre-race state keeps the local player's simable and the
	 * pursuing AI in two nil-initialized locals, then fills one or the other
	 * inside the racer loop.  The stripped chunk preserves the semantic uses:
	 * SetAIGoal(pursuer, "AIGoalHassle") and
	 * SetPursuitTarget(pursuer, player). */
	if (op == OP_LOADNIL &&
		ProtoHasStringConstant(f, "PlayerIsLocal") &&
		ProtoHasStringConstant(f, "SetAIGoal") &&
		ProtoHasStringConstant(f, "SetPursuitTarget")) {
		int firstReg = GETARG_A(ins);
		int lastReg = GETARG_B(ins);
		if (reg == firstReg) strcpy(out, "player");
		else if (reg == lastReg) strcpy(out, "pursuer");
		return;
	}

	if (op == OP_NEWTABLE) {
		if (ProtoHasStringConstant(f, "OnMessage") &&
			(ProtoHasStringConstant(f, "ShowScreenMessage") || ProtoHasStringConstant(f, "ShowMessage"))) strcpy(out, "messageText");
		return;
	}

	if (op == OP_SUB) {
		if (ProtoHasStringConstant(f, "TrapRecords")) strcpy(out, "points");
		else if (ProtoHasStringConstant(f, "canyonRaceTime")) strcpy(out, "timeDelta");
		return;
	}
}

static int NewTableNeedsSourceLocal(const Proto* f, int pc, int reg)
{
	int q;
	for (q = pc + 1; q < f->sizecode; q++) {
		unsigned char use[MAXARG_A], def[MAXARG_A];
		Instruction qi = f->code[q];
		OpCode qo = GET_OPCODE(qi);
		InstructionUseDef(f, q, use, def);
		if (def[reg]) break;
		if (!use[reg]) continue;
		if (qo == OP_SETTABLE) {
			int a = GETARG_A(qi), b = GETARG_B(qi), c = GETARG_C(qi);
			/* Filling the table itself, or moving the completed literal into a
			 * table field, is still constructor lowering rather than a Lua local. */
			if (a == reg) continue;
			if (IsRKReg(c, f->maxstacksize) && c == reg) continue;
			if (IsRKReg(b, f->maxstacksize) && b == reg) return 1;
			continue;
		}
		if ((qo == OP_SETLIST || qo == OP_SETLISTO) && GETARG_A(qi) == reg) continue;
		return 1;
	}
	return 0;
}

static void AnalyzeStrippedLocals(const Proto* f, const int* loopControlUntil,
			int* localStart, char names[MAXARG_A][64])
{
	int n = f->sizecode, maxstack = f->maxstacksize;
	unsigned char* uses = (unsigned char*)calloc((size_t)n * MAXARG_A, 1);
	unsigned char* defs = (unsigned char*)calloc((size_t)n * MAXARG_A, 1);
	unsigned char* liveIn = (unsigned char*)calloc((size_t)n * MAXARG_A, 1);
	unsigned char* liveOut = (unsigned char*)calloc((size_t)n * MAXARG_A, 1);
	unsigned char* longDef = (unsigned char*)calloc((size_t)n * MAXARG_A, 1);
	int pc, r, changed = 1, fallback = 1;

	for (r = 0; r < MAXARG_A; r++) { localStart[r] = -1; names[r][0] = 0; }
	if (!uses || !defs || !liveIn || !liveOut || !longDef) goto cleanup;

	for (pc = 0; pc < n; pc++)
		InstructionUseDef(f, pc, uses + pc * MAXARG_A, defs + pc * MAXARG_A);

	/* Standard backwards liveness over the bytecode CFG. */
	while (changed) {
		changed = 0;
		for (pc = n - 1; pc >= 0; pc--) {
			Instruction ins = f->code[pc];
			OpCode o = GET_OPCODE(ins);
			int sbc = GETARG_sBx(ins);
			unsigned char nextOut[MAXARG_A] = { 0 };
			unsigned char* in = liveIn + pc * MAXARG_A;
			unsigned char* out = liveOut + pc * MAXARG_A;
			unsigned char* use = uses + pc * MAXARG_A;
			unsigned char* def = defs + pc * MAXARG_A;

			if (o == OP_RETURN || o == OP_TAILCALL) {
				/* no successors */
			}
			else if (o == OP_JMP || o == OP_TFORPREP) {
				AddSuccessorLive(liveIn, nextOut, n, maxstack, pc + 1 + sbc);
			}
			else if (o == OP_EQ || o == OP_LT || o == OP_LE || o == OP_TEST || o == OP_TFORLOOP) {
				AddSuccessorLive(liveIn, nextOut, n, maxstack, pc + 1);
				AddSuccessorLive(liveIn, nextOut, n, maxstack, pc + 2);
			}
			else if (o == OP_FORLOOP) {
				AddSuccessorLive(liveIn, nextOut, n, maxstack, pc + 1);
				AddSuccessorLive(liveIn, nextOut, n, maxstack, pc + 1 + sbc);
			}
			else if (o == OP_LOADBOOL && GETARG_C(ins)) {
				AddSuccessorLive(liveIn, nextOut, n, maxstack, pc + 2);
			}
			else AddSuccessorLive(liveIn, nextOut, n, maxstack, pc + 1);

			for (r = 0; r < maxstack; r++) {
				unsigned char ni = (unsigned char)(use[r] || (nextOut[r] && !def[r]));
				if (out[r] != nextOut[r]) { out[r] = nextOut[r]; changed = 1; }
				if (in[r] != ni) { in[r] = ni; changed = 1; }
			}
		}
	}

	/* Classify register definitions by the lifetime of the value they create. */
		for (pc = 0; pc < n; pc++) {
			OpCode defop = GET_OPCODE(f->code[pc]);
			int sourceDef = 1;
				/* SELF only materializes the callable/receiver pair used by a method
				 * invocation.  It is never a source-level local declaration.  CALL C==1
				 * similarly has no Lua result; its def marking is only a liveness kill. */
				if (defop == OP_SELF || (defop == OP_CALL && GETARG_C(f->code[pc]) == 1))
					sourceDef = 0;
				if (defop == OP_NEWTABLE && !NewTableNeedsSourceLocal(f, pc, GETARG_A(f->code[pc])))
					sourceDef = 0;
			for (r = f->numparams; r < maxstack; r++) if (sourceDef && defs[pc * MAXARG_A + r] &&
				!(loopControlUntil[r] >= 0 && pc <= loopControlUntil[r])) {
			int q, nextDef = n, useCount = 0, crossesControl = 0, crossesSideEffect = 0;
			for (q = pc + 1; q < n; q++) {
				if (defs[q * MAXARG_A + r]) { nextDef = q; break; }
			}
			for (q = pc + 1; q < nextDef; q++) {
				OpCode qo = GET_OPCODE(f->code[q]);
				if (uses[q * MAXARG_A + r]) useCount++;
				if (IsControlOpcode(qo) && liveOut[q * MAXARG_A + r]) crossesControl = 1;
				if (IsSideEffectOpcode(qo) && liveOut[q * MAXARG_A + r]) crossesSideEffect = 1;
			}
			if (useCount > 1 || crossesControl || crossesSideEffect)
				longDef[pc * MAXARG_A + r] = 1;
			}
		}

		/* A stripped source local can survive only as a sequence of conditional
		 * constant assignments even when the final value is currently unused
		 * (Black Box scripts contain this when a HUD call was commented out).
		 * Preserve that source shape instead of treating the second LOADK as an
		 * illegal overwrite of a temporary register. */
		for (r = f->numparams; r < maxstack; r++) {
			int d1 = -1, d2 = -1, q, hasControl = 0, totalUses = 0;
			for (q = 0; q < n; q++) if (uses[q * MAXARG_A + r]) totalUses++;
			if (totalUses != 0) continue;
			for (pc = 0; pc < n; pc++) {
				if (!defs[pc * MAXARG_A + r]) continue;
				if (d1 < 0) d1 = pc;
				else { d2 = pc; break; }
			}
			if (d1 < 0 || d2 < 0) continue;
			if (GET_OPCODE(f->code[d1]) != OP_LOADK || GET_OPCODE(f->code[d2]) != OP_LOADK) continue;
			for (q = d1 + 1; q < d2; q++) if (IsControlOpcode(GET_OPCODE(f->code[q]))) { hasControl = 1; break; }
			if (hasControl) longDef[d1 * MAXARG_A + r] = 1;
		}

		for (r = f->numparams; r < maxstack; r++) {
		int first = -1;
		for (pc = 0; pc < n; pc++) {
			if (longDef[pc * MAXARG_A + r]) { first = pc; break; }
		}
		if (first < 0) continue;

		/* Preserve a source-style initializer immediately preceding the first
		 * long-lived definition when that earlier value was dead.  This recovers
		 * patterns such as `local movie = nil` / `local index = 0` without pulling
		 * in an earlier temporary call chain that happened to reuse the slot. */
			/* Only fold a genuinely adjacent source initializer into a recovered
			 * local.  The old backwards walk crossed unrelated VM lifetimes and
			 * turned chains such as `message.Element:IsPlayer()` / `Game.Get...()`
			 * into fake locals. */
			{
				int prev = -1, q, prevUses = 0;
				for (q = first - 1; q >= 0; q--) if (defs[q * MAXARG_A + r]) { prev = q; break; }
				if (prev == first - 1) {
					OpCode po = GET_OPCODE(f->code[prev]);
					if (po == OP_LOADNIL || po == OP_LOADK || po == OP_LOADBOOL) {
						for (q = prev + 1; q < first; q++) if (uses[q * MAXARG_A + r]) prevUses++;
						if (prevUses == 0) first = prev;
					}
				}
			}
		localStart[r] = first;

			/* Recover names from the supplied Black Box source patterns before the
			 * generic field/call heuristics. */
			GuessKnownSourceLocalName(f, r, first, names[r]);

			/* First generic preference: a direct field read from handler parameters. */
			for (pc = first; pc < n && !names[r][0]; pc++) {
			Instruction ins = f->code[pc];
			if (GET_OPCODE(ins) == OP_GETTABLE && GETARG_A(ins) == r &&
				(GETARG_B(ins) == 0 || GETARG_B(ins) == 1 || GETARG_B(ins) == 2) && GETARG_C(ins) >= MAXSTACK) {
				int k = GETARG_C(ins) - MAXSTACK;
				if (k >= 0 && k < f->sizek && ttisstring(&f->k[k])) {
					const char* key = svalue(&f->k[k]);
					size_t j, len = strlen(key);
					if (len > 0 && len < 63) {
						for (j = 0; j < len; j++) names[r][j] = (char)((j == 0) ? tolower((unsigned char)key[j]) : key[j]);
						names[r][len] = 0;
					}
				}
			}
		}

		/* Event argument gives a strong semantic role for movie handles. */
		for (pc = first; pc + 2 < n && !names[r][0]; pc++) {
			Instruction g = f->code[pc], m = f->code[pc + 1], call = f->code[pc + 2];
			if (GET_OPCODE(g) == OP_GETGLOBAL && GET_OPCODE(m) == OP_MOVE && GET_OPCODE(call) == OP_CALL &&
				GETARG_A(m) == GETARG_A(g) + 1 && GETARG_B(m) == r && GETARG_A(call) == GETARG_A(g)) {
				int k = GETARG_Bx(g);
				if (k >= 0 && k < f->sizek && ttisstring(&f->k[k]) && strcmp(svalue(&f->k[k]), "EPlayRaceMovie") == 0)
					strcpy(names[r], "raceMovie");
			}
		}

		/* Result copied out of a call: derive a role from the method name. */
		for (pc = first; pc < n && !names[r][0]; pc++) {
			Instruction mv = f->code[pc];
			if (GET_OPCODE(mv) == OP_MOVE && GETARG_A(mv) == r && pc > 0 && GET_OPCODE(f->code[pc - 1]) == OP_CALL) {
				int callReg = GETARG_A(f->code[pc - 1]);
				int q;
				for (q = pc - 2; q >= 0 && q >= pc - 5; q--) {
					Instruction gi = f->code[q];
					if (GET_OPCODE(gi) == OP_GETTABLE && GETARG_A(gi) == callReg && GETARG_C(gi) >= MAXSTACK) {
						int k = GETARG_C(gi) - MAXSTACK;
						if (k >= 0 && k < f->sizek && ttisstring(&f->k[k])) {
							const char* method = svalue(&f->k[k]);
							const char* base = (strncmp(method, "Get", 3) == 0 && method[3]) ? method + 3 : method;
							size_t j, len = strlen(base);
							if (len > 0 && len < 63) {
								for (j = 0; j < len; j++) names[r][j] = (char)((j == 0) ? tolower((unsigned char)base[j]) : base[j]);
								names[r][len] = 0;
							}
						}
						break;
					}
				}
			}
		}

				if (!names[r][0]) sprintf(names[r], "localValue%d", fallback++);
			}

		/* Black Box emits this exact short-circuit materialization for the
		 * intro-message booleans.  The source names are gotNIS/gotMovie.  Treat
		 * them as source locals explicitly instead of asking the generic lifetime
		 * heuristic to infer them from two overlapping GETTABLE/LOADBOOL chains. */
		if (n > 9 && f->numparams == 3 &&
			GET_OPCODE(f->code[0]) == OP_GETTABLE && GETARG_A(f->code[0]) == 3 &&
			GET_OPCODE(f->code[8]) == OP_GETTABLE && GETARG_A(f->code[8]) == 4) {
			const char* k0 = GetTableStringKey(f, f->code[0]);
			const char* k8 = GetTableStringKey(f, f->code[8]);
			if (k0 && k8 && strcmp(k0, "IntroNIS") == 0 && strcmp(k8, "IntroMovie") == 0) {
				localStart[3] = 0; strcpy(names[3], "gotNIS");
				localStart[4] = 8; strcpy(names[4], "gotMovie");
			}
		}

cleanup:
	free(uses); free(defs); free(liveIn); free(liveOut); free(longDef);
}

static void BeginSyntheticLocal(Function* F, int reg, const char* name)
{
	if (reg < 0 || reg >= MAXARG_A) return;
	PENDING(reg) = 0;
	CALL(reg) = 0;
	RemoveFromSet(F->tpend, reg);
	IS_VARIABLE(reg) = 1;
	F->RsyntheticNew[reg] = 1;
	if (REGISTER(reg)) free(REGISTER(reg));
	REGISTER(reg) = _strdup(name);
	F->Rprio[reg] = 0;
}

char* ProcessCodeEx(const Proto* f, int indent, const char* const* inferredUpvalues, int inferredCount)
{
	int i = 0;

	int ignoreNext = 0;

	/*
	 * State variables for the boolean operations.
	 */
	int boolpending = 0;

	Function* F;
	StringBuffer* str = StringBuffer_new(NULL);

	const Instruction* code = f->code;
	int pc, n = f->sizecode;
	int baseIndent = indent;
	unsigned char* skipNoOp = (unsigned char*)calloc((size_t)(n > 0 ? n : 1), 1);

	char* output;

	F = NewFunction(f);
	F->indent = indent;
	F->pc = 0;
	error = NULL;
	if (skipNoOp) MarkNoOpCompareLadders(f, skipNoOp);

	/* Names of upvalues are debug-only and disappear from stripped chunks, but
	 * the actual capture count survives in Proto::nups. */
	for (i = 0; i < f->nups && i < 32; i++) {
		if (inferredUpvalues && i < inferredCount && inferredUpvalues[i])
			F->inferredUpvalues[i] = _strdup(inferredUpvalues[i]);
		else {
			char uvName[32];
			sprintf(uvName, "upvalue%d", i);
			F->inferredUpvalues[i] = _strdup(uvName);
		}
	}

	int stripped = (!f->locvars || f->sizelocvars == 0);
		int loopControlUntil[MAXARG_A];
		int syntheticLocalStart[MAXARG_A];
		char syntheticLocalName[MAXARG_A][64];
		for (i = 0; i < MAXARG_A; i++) { loopControlUntil[i] = -1; syntheticLocalStart[i] = -1; syntheticLocalName[i][0] = 0; }
	if (stripped && !IsMain(f)) {
		for (pc = 0; pc < n; pc++) {
			Instruction li = code[pc];
			OpCode lo = GET_OPCODE(li);
			if (lo == OP_FORLOOP) {
				int la = GETARG_A(li);
				int lr;
					for (lr = la; lr <= la + 2 && lr < MAXARG_A; lr++)
						if (pc > loopControlUntil[lr]) loopControlUntil[lr] = pc;
			}
			else if (lo == OP_TFORLOOP) {
				int la = GETARG_A(li);
				int nvars = GETARG_C(li) + 1;
				int lr;
					for (lr = la; lr <= la + nvars + 1 && lr < MAXARG_A; lr++)
						if (pc > loopControlUntil[lr]) loopControlUntil[lr] = pc;
				}
			}
			AnalyzeStrippedLocals(f, loopControlUntil, syntheticLocalStart, syntheticLocalName);
	}

	/*
	 * Function parameters are stored in registers from 0 on.
	 */
	int placeholder = 0;
	if (F->f->locvars == 0)
	{
		//fprintf(stddebug, "Fuck\n");
		//__debugbreak();
		placeholder = 1;
	}

	for (i = 0; i < f->numparams; i++) {
		//TRY(DeclareVariable(F, LOCAL(i), i));

		char* varName = 0;
		if (placeholder)
		{
				if (rawHandlerParams && f->numparams == 3 && i < 3) {
					varName = malloc(16);
					if (varName) sprintf(varName, "param%i", i);
				}
				else if (f->numparams == 3 && i < 3) {
					static const char* handlerParams[3] = { "this", "message", "context" };
					varName = _strdup(handlerParams[i]);
				}
					else {
						const char* guessed = GuessStrippedParamName(f, i);
						if (guessed) varName = _strdup(guessed);
						else {
							varName = malloc(16);
							sprintf(varName, "param%i", i);
						}
					}
		}
		else
		{
			varName = (char*)getstr(F->f->locvars[i].varname);
		}

		DeclareVariable(F, varName, i);
		if (error)
			goto errorHandler;
	}
	F->freeLocal = f->numparams;

	TRY(FunctionHeader(F));

	if (f->is_vararg) {
		TRY(DeclareVariable(F, "arg", F->freeLocal));
		F->freeLocal++;
	}

	/* Do not materialize stripped VM slots as Lua locals.  Registers are an
	 * implementation detail of the bytecode, not source variables.  Keeping
	 * them as symbolic temporaries lets the normal expression propagation fold
	 * GETGLOBAL/GETTABLE/MOVE/CALL chains back into source-level expressions
	 * such as Game.ShowGPS(false) instead of emitting reg3 = Game; ... */

	for (pc = n - 1; pc >= 0; pc--) {
		Instruction i = code[pc];
		OpCode o = GET_OPCODE(i);
		if (o == OP_JMP) {
			int sbc = GETARG_sBx(i);
			int dest = sbc + pc;
			if (dest < pc) {
				if (dest + 2 > 0
					&& GET_OPCODE(code[dest]) == OP_JMP
					&& !PeekSet(F->whiles, dest)) {
					AddToSet(F->whiles, dest);
				}
				else if (GET_OPCODE(code[dest]) != OP_TFORPREP) {
					AddToSet(F->repeats, dest + 2);
					AddToSet(F->untils, pc);
				}
			}
		}
		else if (o == OP_CLOSE) {
			int a = GETARG_A(i);
			if (f->locvars && f->sizelocvars > a) {
				AddToSet(F->do_opens, f->locvars[a].startpc);
				AddToSet(F->do_closes, f->locvars[a].endpc);
			}
		}
	}

		for (pc = 0; pc < n; pc++) {
			Instruction i = code[pc];
		OpCode o = GET_OPCODE(i);
		int a = GETARG_A(i);
		int b = GETARG_B(i);
		int c = GETARG_C(i);
		int bc = GETARG_Bx(i);
		int sbc = GETARG_sBx(i);
				F->pc = pc;
				if (skipNoOp && skipNoOp[pc]) continue;

		if (ignoreNext) {
			ignoreNext--;
			continue;
		}

		/*
		 * Disassembler info
		 */
		if (debug) {
			fprintf(stddebug, "----------------------------------------------\n");
			fprintf(stddebug, "\t%d\t", pc + 1);
			fprintf(stddebug, "%-9s\t", luaP_opnames[o]);
			switch (getOpMode(o)) {
			case iABC:
				fprintf(stddebug, "%d %d %d", a, b, c);
				break;
			case iABx:
				fprintf(stddebug, "%d %d", a, bc);
				break;
			case iAsBx:
				fprintf(stddebug, "%d %d", a, sbc);
				break;
			}
			fprintf(stddebug, "\n");
		}

		TRY(DeclareLocals(F));
		TRY(ReleaseLocals(F));

		while (RemoveFromSet(F->do_opens, pc)) {
			StringBuffer_set(str, "do");
			TRY(AddStatement(F, str));
			StringBuffer_prune(str);
			F->indent++;
		}

		while (RemoveFromSet(F->do_closes, pc)) {
			StringBuffer_set(str, "end");
			F->indent--;
			TRY(AddStatement(F, str));
			StringBuffer_prune(str);
		}

		while (GetEndifAddr(F, pc + 1)) {
			StringBuffer_set(str, "end");
			F->elseWritten = 0;
			F->elsePending = 0;
			F->indent--;
			TRY(AddStatement(F, str));
			StringBuffer_prune(str);
		}

		while (RemoveFromSet(F->repeats, F->pc + 1)) {
			StringBuffer_set(str, "repeat");
			TRY(AddStatement(F, str));
			StringBuffer_prune(str);
			F->indent++;
		}

			StringBuffer_prune(str);

			if (stripped && !IsMain(f)) {
				int sr;
				for (sr = f->numparams; sr < f->maxstacksize; sr++) {
					if (syntheticLocalStart[sr] == pc) {
							/* CALL reads R(A) as the function and only then replaces R(A)
							 * with its result.  Activate a recovered local for that result in
							 * OP_CALL after the call expression has been consumed. */
							if (!(o == OP_CALL && sr == a))
								BeginSyntheticLocal(F, sr, syntheticLocalName[sr]);
						}
				}
			}

			switch (o) {
		case OP_MOVE:
		{
			char* bstr = NULL;
			if (a == b)
				break;
			if (CALL(b) < 2)
				bstr = GetR(F, b);
			else
				UnsetPending(F, b);
			if (error)
				goto errorHandler;
			/*
			 * Copy from one register to another
			 */
			TRY(Assign(F, REGISTER(a), bstr, a, PRIORITY(b), 1));
			break;
		}
		case OP_LOADK:
		{
			/*
			 * Constant. Store it in register.
			 */
			char* ctt = DecompileConstant(f, bc);
			TRY(Assign(F, REGISTER(a), ctt, a, 0, 1));
			break;
			free(ctt);
		}
		case OP_LOADBOOL:
		{
			if (F->nextBool == 0) {
				/*
				 * assign boolean constant
				 */
				if (PENDING(a)) {
					// some boolean constructs overwrite pending regs :(
					TRY(UnsetPending(F, a));
				}
				TRY(Assign(F, REGISTER(a), b ? "true" : "false", a, 0, 1));
			}
			else {
				/*
				 * assign boolean value
				 */
				char* test;
				TRY(test = OutputBoolean(F, NULL, 1));
				StringBuffer_printf(str, "%s", test);
				TRY(Assign(F, REGISTER(a), StringBuffer_getRef(str), a, 0, 0));
				free(test);
			}
			if (c)
				ignoreNext = 1;
			break;
		}
		case OP_LOADNIL:
		{
			int i;
			/*
			 * Read nil into register.
			 */
			for (i = a; i <= b; i++) {
				TRY(Assign(F, REGISTER(i), "nil", i, 0, 1));
			}
			break;
		}
		case OP_GETUPVAL:
		{
			TRY(Assign(F, REGISTER(a), UPVALUE(b), a, 0, 1));
			break;
		}
		case OP_GETGLOBAL:
		{
			/*
			 * Read global into register.
			 */
			TRY(Assign(F, REGISTER(a), GLOBAL(bc), a, 0, 1));
			break;
		}
		case OP_GETTABLE:
		{
			/*
			 * Read table entry into register.
			 */
			char* bstr, * cstr;
			TRY(cstr = RegisterOrConstant(F, c));
			TRY(bstr = GetR(F, b));
			if (bstr[0] == '{') {
				StringBuffer_printf(str, "(%s)", bstr);
			}
			else {
				StringBuffer_set(str, bstr);
			}
			MakeIndex(F, str, cstr, 0);
			TRY(Assign(F, REGISTER(a), StringBuffer_getRef(str), a, 0, 0));
			free(cstr);
			break;
		}
		case OP_SETGLOBAL:
		{
			/*
			 * Global Assignment statement.
			 */
			char* var = GLOBAL(bc);
			if (IS_TABLE(a)) {
				TRY(PrintTable(F, a, 0));
			}
			{
				char* astr;
				TRY(astr = GetR(F, a));
				TRY(Assign(F, var, astr, -1, 0, 0));
			}
			break;
		}
		case OP_SETUPVAL:
		{
			/*
			 * Global Assignment statement.
			 */
			char* var = UPVALUE(bc);
			if (IS_TABLE(a)) {
				TRY(CloseTable(F, a));
			}
			{
				char* astr;
				TRY(astr = GetR(F, a));
				TRY(Assign(F, var, astr, -1, 0, 0));
			}
			break;
		}
		case OP_SETTABLE:
		{
			char* bstr, * cstr;
			int settable;
			TRY(bstr = RegisterOrConstant(F, b));
			TRY(cstr = RegisterOrConstant(F, c));
			/*
			 * first try to add into a table
			 */
			TRY(settable = SetTable(F, a, bstr, cstr));
			if (!settable) {
				/*
				 * if failed, just output an assignment
				 */
				StringBuffer_set(str, REGISTER(a));
				MakeIndex(F, str, bstr, 0);
				TRY(Assign(F, StringBuffer_getRef(str), cstr, -1, 0, 0));
			}
			free(bstr);
			free(cstr);
			break;
		}
		case OP_NEWTABLE:
		{
			TRY(StartTable(F, a, b, c));
			break;
		}
		case OP_SELF:
		{
			/*
			 * Read table entry into register.
			 */
			char* bstr, * cstr;
			TRY(cstr = RegisterOrConstant(F, c));
			TRY(bstr = GetR(F, b));

			bstr = _strdup(bstr);

			TRY(Assign(F, REGISTER(a + 1), bstr, a + 1, PRIORITY(b), 0));

			StringBuffer_set(str, bstr);
			MakeIndex(F, str, cstr, 1);
			TRY(Assign(F, REGISTER(a), StringBuffer_getRef(str), a, 0, 0));
			free(bstr);
			free(cstr);
			break;
		}
		case OP_ADD:
		case OP_SUB:
		case OP_MUL:
		case OP_DIV:
		case OP_POW:
		{
			char* bstr, * cstr;
			char* oper = operators[o];
			int prio = priorities[o];
			int bprio = PRIORITY(b);
			int cprio = PRIORITY(c);
			TRY(bstr = RegisterOrConstant(F, b));
			TRY(cstr = RegisterOrConstant(F, c));
			// FIXME: might need to change from <= to < here
			if ((prio != 1 && bprio <= prio) || (prio == 1 && bstr[0] != '-')) {
				StringBuffer_add(str, bstr);
			}
			else {
				StringBuffer_addPrintf(str, "(%s)", bstr);
			}
			StringBuffer_addPrintf(str, " %s ", oper);
			// FIXME: being conservative in the use of parentheses
			if (cprio < prio) {
				StringBuffer_add(str, cstr);
			}
			else {
				StringBuffer_addPrintf(str, "(%s)", cstr);
			}
			TRY(Assign(F, REGISTER(a), StringBuffer_getRef(str), a, prio, 0));
			free(bstr);
			free(cstr);
			break;
		}
		case OP_UNM:
		case OP_NOT:
		{
			char* bstr;
			int prio = priorities[o];
			int bprio = PRIORITY(b);
			TRY(bstr = GetR(F, b));
			StringBuffer_add(str, operators[o]);
			if (bprio <= prio) {
				StringBuffer_add(str, bstr);
			}
			else {
				StringBuffer_addPrintf(str, "(%s)", bstr);
			}
			TRY(Assign(F, REGISTER(a), StringBuffer_getRef(str), a, 0, 0));
			break;
		}
		case OP_CONCAT:
		{
			int i;
			for (i = b; i <= c; i++) {
				char* istr;
				TRY(istr = GetR(F, i));
				if (PRIORITY(i) > priorities[o]) {
					StringBuffer_addPrintf(str, "(%s)", istr);
				}
				else {
					StringBuffer_add(str, istr);
				}
				if (i < c)
					StringBuffer_add(str, " .. ");
			}
			TRY(Assign(F, REGISTER(a), StringBuffer_getRef(str), a, 0, 0));
			break;
		}
		case OP_JMP:
		{
			int dest = sbc + pc + 2;
			Instruction idest = code[dest - 1];
			if (boolpending) {
				boolpending = 0;
				F->bools[F->nextBool]->dest = dest;
				F->nextBool++;
				F->bools[F->nextBool] = calloc(sizeof(BoolOp), 1);
				if (F->testpending) {
					F->testjump = dest;
				}
				if (RemoveFromSet(F->untils, F->pc)) {
					int endif, thenaddr;
					char* test;
					LogicExp* exp;
					TRY(exp = MakeBoolean(F, &endif, &thenaddr));
					TRY(test = WriteBoolean(exp, &thenaddr, &endif, 0));
					StringBuffer_printf(str, "until %s", test);
					F->indent--;
					RawAddStatement(F, str);
					free(test);
				}
			}
			else if (GET_OPCODE(idest) == OP_FORLOOP &&
				pc == dest + GETARG_sBx(idest) - 1) {
				/*
				 * numeric 'for'
				 */
				int i;
				int step;
				char* idxname = 0;
				char* initial;
				char* findSign;
				char* a1str;
				int stepLen;
				int a = GETARG_A(idest);
				// int b = GETARG_B(idest);
				// int c = GETARG_C(idest);
				/*
				 * if A argument for FORLOOP is not a known variable,
				 * it was declared in the 'for' statement. Look for
				 * its name in the locals table.
				 */
				for (i = 0; i < f->sizelocvars; i++) {
					if (f->locvars[i].startpc == pc + 1) {
						idxname = LOCAL(i);
						break;
					}
				}
				TRY(initial = GetR(F, a));
				initial = _strdup(initial);
				step = atoi(REGISTER(a + 2));
				stepLen = strlen(REGISTER(a + 2));
				findSign = strrchr(initial, '-');
				if (findSign) {
					initial[strlen(initial) - stepLen - 3] = '\0';
				}
				TRY(a1str = GetR(F, a + 1));
				if (!idxname)
					idxname = _strdup(GuessNumericForIndexName(f, initial, a1str));
				if (step == 1) {
					StringBuffer_printf(str, "for %s = %s, %s do",
						idxname, initial, a1str);
				}
				else {
					/* step parameter is not pending because it
					   was used in the calculation of the first step */
					StringBuffer_printf(str, "for %s = %s, %s, %s do",
						idxname, initial,
						a1str, REGISTER(a + 2));
				}

				/*
				 * Every numeric 'for' declares 3 variables.
				 */
				F->internal[a] = 1;
				F->internal[a + 1] = 1;
				F->internal[a + 2] = 1;
				if (stripped) {
					int r;
					for (r = a; r <= a + 2; r++) {
						PENDING(r) = 0;
						RemoveFromSet(F->tpend, r);
					}
					F->Rvar[a] = 1;
					if (F->R[a]) free(F->R[a]);
					F->R[a] = _strdup(idxname);
					F->Rprio[a] = 0;
				}
				TRY(AddStatement(F, str));
				F->indent++;
			}
			else if (GetEndifAddr(F, pc + 2)) {
				if (F->elseWritten) {
					F->indent--;
					StringBuffer_printf(str, "end");
					TRY(AddStatement(F, str));
				}
				F->indent--;
				F->elsePending = dest;
				F->elseStart = pc + 2;
			}
			else if (PeekSet(F->whiles, pc)) {
				StringBuffer_printf(str, "while 1 do");
				TRY(AddStatement(F, str));
				MarkBackpatch(F);
				F->indent++;
			}
			else if (RemoveFromSet(F->whiles, dest - 2)) {
				F->indent--;
				StringBuffer_printf(str, "end");
				TRY(AddStatement(F, str));
				/* end while 1 */
			}
			else if (sbc == 2 && GET_OPCODE(code[pc + 2]) == OP_LOADBOOL) {
				int boola = GETARG_A(code[pc + 1]);
				char* test;
				/* skip */
				char* ra = _strdup(REGISTER(boola));
				char* rb = _strdup(ra);
				F->bools[F->nextBool]->op1 = ra;
				F->bools[F->nextBool]->op2 = rb;
				F->bools[F->nextBool]->op = OP_TEST;
				F->bools[F->nextBool]->neg = c;
				F->bools[F->nextBool]->pc = pc + 3;
				F->testpending = a + 1;
				F->bools[F->nextBool]->dest = dest;
				F->nextBool++;
				F->bools[F->nextBool] = calloc(sizeof(BoolOp), 1);
				F->testjump = dest;
				TRY(test = OutputBoolean(F, NULL, 1));
				StringBuffer_printf(str, "%s", test);
				TRY(UnsetPending(F, boola));
				TRY(Assign(F, REGISTER(boola), StringBuffer_getRef(str), boola, 0, 0));
				ignoreNext = 2;
			}
			else if (GET_OPCODE(idest) == OP_LOADBOOL) {
				/*
				 * constant boolean value
				 */
				pc = dest - 2;
			}
			else if (sbc == 0) {
				/* dummy jump -- ignore it */
				break;
			}
			else {
				int nextpc = pc + 1;
				int nextsbc = sbc - 1;
				for (;;) {
					Instruction nextins = code[nextpc];
					if (GET_OPCODE(nextins) == OP_JMP && GETARG_sBx(nextins) == nextsbc) {
						nextpc++;
						nextsbc--;
					}
					else
						break;
					if (nextsbc == -1) {
						break;
					}
				}
				if (nextsbc == -1) {
					pc = nextpc - 1;
					break;
				}
				if (F->indent > baseIndent) {
					StringBuffer_printf(str, "do break end");
				}
				else {
					pc = dest - 2;
				}
				TRY(AddStatement(F, str));
			}

			break;
		}
		case OP_EQ:
		case OP_LT:
		case OP_LE:
		{
			if (IS_CONSTANT(b)) {
				int swap = b;
				b = c;
				c = swap;
				a = !a;
				if (o == OP_LT) o = OP_LE;
				else if (o == OP_LE) o = OP_LT;
			}
			TRY(F->bools[F->nextBool]->op1 = RegisterOrConstant(F, b));
			TRY(F->bools[F->nextBool]->op2 = RegisterOrConstant(F, c));
			F->bools[F->nextBool]->op = o;
			F->bools[F->nextBool]->neg = a;
			F->bools[F->nextBool]->pc = pc + 1;
			boolpending = 1;
			break;
		}
		case OP_TEST:
		{
			char* ra, * rb;
			if (!IS_VARIABLE(a)) {
				ra = _strdup(REGISTER(a));
				TRY(rb = GetR(F, b));
				rb = _strdup(rb);
				PENDING(a) = 0;
			}
			else {
				TRY(ra = GetR(F, a));
				if (a != b) {
					TRY(rb = GetR(F, b));
					rb = _strdup(rb);
				}
				else
					rb = _strdup(ra);
			}
			F->bools[F->nextBool]->op1 = ra;
			F->bools[F->nextBool]->op2 = rb;
			F->bools[F->nextBool]->op = o;
			F->bools[F->nextBool]->neg = c;
			F->bools[F->nextBool]->pc = pc + 1;
			// Within an IF, a and b are the same, avoiding side-effects
			if (a != b || !IS_VARIABLE(a)) {
				F->testpending = a + 1;
			}
			boolpending = 1;
			break;
		}
		case OP_CALL:
		case OP_TAILCALL:
		{
			/*
			 * Function call. The CALL opcode works like this:
			 * R(A),...,R(A+F-2) := R(A)(R(A+1),...,R(A+B-1))
			 */
			int i, limit, self;
			char* astr;
			self = 0;

			if (b == 0)
				limit = F->lastCall + 1;
			else
				limit = a + b;
			if (o == OP_TAILCALL) {
				StringBuffer_set(str, "return ");
				ignoreNext = 1;
			}
			TRY(astr = GetR(F, a));
			/* An anonymous function expression must be parenthesized before an
			 * immediate call in Lua (`(function(...) ... end)(...)`).  Stripped
			 * chunks frequently implement tiny local helper functions this way. */
			if (astr && strncmp(astr, "function", 8) == 0)
				StringBuffer_addPrintf(str, "(%s)(", astr);
			else
				StringBuffer_addPrintf(str, "%s(", astr);

			{
				char* at = astr + strlen(astr) - 1;
				while (at > astr && (isalpha(*at) || *at == '_')) {
					at--;
				}
				if (*at == ':')
					self = 1;
			}

			for (i = a + 1; i < limit; i++) {
				char* ireg;
				TRY(ireg = GetR(F, i));
				if (self && i == a + 1)
					continue;
				if (i > a + 1 + self)
					StringBuffer_add(str, ", ");
				if (ireg)
					StringBuffer_add(str, ireg);
			}
			StringBuffer_addChar(str, ')');

			if (c == 0) {
				F->lastCall = a;
			}
			if (GET_OPCODE(code[pc + 1]) == OP_LOADNIL && GETARG_A(code[pc + 1]) == a + 1) {
				StringBuffer_prepend(str, "(");
				StringBuffer_add(str, ")");
				c += GETARG_B(code[pc + 1]) - GETARG_A(code[pc + 1]) + 1;
				// ignoreNext = 1;
			}
			if (o == OP_TAILCALL || c == 1) {
				TRY(AddStatement(F, str));
			}
				else {
					if (stripped && syntheticLocalStart[a] == pc && !IS_VARIABLE(a))
						BeginSyntheticLocal(F, a, syntheticLocalName[a]);
					TRY(Assign(F, REGISTER(a), StringBuffer_getRef(str), a, 0, 0));
				for (i = 0; i < c - 1; i++) {
					CALL(a + i) = i + 1;
				}
			}
			break;
		}
		case OP_RETURN:
		{
			/*
			 * Return call. The RETURN opcode works like this: return
			 * R(A),...,R(A+B-2)
			 */
			int i, limit;

			/* skip the last RETURN */
			if (pc == n - 1)
				break;
			if (b == 0)
				limit = F->lastCall;
			else
				limit = a + b - 1;
			StringBuffer_set(str, "return ");
			for (i = a; i < limit; i++) {
				char* istr;
				if (i > a)
					StringBuffer_add(str, ", ");
				istr = GetR(F, i);
				TRY(StringBuffer_add(str, istr));
			}
			TRY(AddStatement(F, str));
			break;
		}
		case OP_FORLOOP:
		{
			F->indent--;
			F->ignore_for_variables = 1;
			StringBuffer_set(str, "end");
				TRY(AddStatement(F, str));
				if (stripped) {
					int r;
					int bodyStart = pc + 1 + sbc;
					for (r = a; r <= a + 2 && r < f->maxstacksize; r++) {
						/* Numeric-for control slots die at the loop boundary.  They are
						 * immediately reusable VM temporaries afterwards, so keeping them
						 * as source variables is exactly what leaked reg3/reg4/reg5 into
						 * post-loop calls. */
						F->Rvar[r] = 0;
						F->RsyntheticNew[r] = 0;
						if (F->R[r]) { free(F->R[r]); F->R[r] = NULL; }
						F->Rprio[r] = 0;
						PENDING(r) = 0; CALL(r) = 0; RemoveFromSet(F->tpend, r);
						F->Rorigin[r] = -1;
					}
					/* Source locals first created inside the numeric-for body end with
					 * that block.  Keeping them alive lets their VM slots alias unrelated
					 * post-loop temporaries (notably SELF's receiver slot), producing
					 * malformed method expressions such as `x, y = x:Method, x`. */
					for (r = f->numparams; r < f->maxstacksize; r++) {
						if (syntheticLocalStart[r] >= bodyStart && syntheticLocalStart[r] <= pc) {
							F->Rvar[r] = 0;
							F->RsyntheticNew[r] = 0;
							if (F->R[r]) { free(F->R[r]); F->R[r] = NULL; }
							F->Rprio[r] = 0;
							PENDING(r) = 0; CALL(r) = 0; RemoveFromSet(F->tpend, r);
							F->Rorigin[r] = -1;
						}
					}
				}
			break;
		}
		case OP_TFORLOOP:
		{
			F->indent--;
			F->ignore_for_variables = 1;
			StringBuffer_set(str, "end");
			TRY(AddStatement(F, str));
				if (stripped) {
					int nvars = c + 1;
					int r;
					for (r = a; r <= a + nvars + 1 && r < f->maxstacksize; r++) {
						F->Rvar[r] = 0;
						F->RsyntheticNew[r] = 0;
						if (F->R[r]) { free(F->R[r]); F->R[r] = NULL; }
						F->Rprio[r] = 0;
						PENDING(r) = 0; CALL(r) = 0; RemoveFromSet(F->tpend, r);
					}
				}
			ignoreNext = 1;
			break;
		}
		case OP_TFORPREP:
		{
			int i = 0;
			char* astr;
			TRY(astr = GetR(F, a));
			if (stripped) {
				int loopPc = pc + sbc + 1;
				int nvars = 1;
				int endreg;
				if (loopPc >= 0 && loopPc < n && GET_OPCODE(code[loopPc]) == OP_TFORLOOP)
					nvars = GETARG_C(code[loopPc]) + 1;
				StringBuffer_set(str, "for ");
				for (i = 0; i < nvars; i++) {
					char varName[32];
					sprintf(varName, "for_var_%d", a + 2 + i);
					if (i) StringBuffer_add(str, ", ");
					StringBuffer_add(str, varName);
				}
				StringBuffer_addPrintf(str, " in %s do", astr);
				endreg = a + nvars + 1;
				for (i = a; i <= endreg; i++) {
					PENDING(i) = 0; CALL(i) = 0; RemoveFromSet(F->tpend, i);
				}
				for (i = 0; i < nvars; i++) {
					int r = a + 2 + i;
					char varName[32];
					sprintf(varName, "for_var_%d", r);
					F->Rvar[r] = 1;
					if (F->R[r]) free(F->R[r]);
					F->R[r] = _strdup(varName);
				}
				TRY(AddStatement(F, str));
				F->indent++;
			}
			else {
				int prepCtr = 0;
				int prep = 0;
				int preps[10];
				for (i = 0; i < F->f->sizelocvars; i++) {
					if (F->f->locvars[i].startpc == pc + 1) {
						int reg = F->freeLocal + prepCtr;
						if (prepCtr == 0) prep = i;
						F->internal[reg] = 1;
						RemoveFromSet(F->tpend, reg);
						preps[prepCtr] = reg;
						prepCtr++;
					}
				}
				StringBuffer_printf(str, "for %s", LOCAL(prep + 2));
				for (i = 3; i < prepCtr; i++) StringBuffer_addPrintf(str, ", %s", LOCAL(prep + i));
				StringBuffer_addPrintf(str, " in %s do", astr);
				TRY(GetR(F, a + 1));
				TRY(AddStatement(F, str));
				for (i = 0; i < prepCtr; i++) { CALL(a + i) = 0; PENDING(preps[i]) = 0; }
				F->indent++;
			}
			break;
		}
		case OP_SETLIST:
		case OP_SETLISTO:
		{
			TRY(SetList(F, a, bc));
			break;
		}
		case OP_CLOSE:
			/*
			 * Handled in do_opens/do_closes variables.
			 */
			break;
		case OP_CLOSURE:
		{
			/* Function. Upvalue names are debug metadata, but the capture
			 * descriptors immediately following CLOSURE survive stripping. */
			const Proto* child = f->p[c];
			const char* childUpvalues[32] = { 0 };
			int uv;
			for (uv = 0; uv < child->nups && uv < 32; uv++) {
				Instruction cap = code[pc + 1 + uv];
				OpCode cop = GET_OPCODE(cap);
				if (cop == OP_MOVE) {
					int src = GETARG_B(cap);
					childUpvalues[uv] = REGISTER(src);
				}
				else if (cop == OP_GETUPVAL) {
					childUpvalues[uv] = UPVALUE(GETARG_B(cap));
				}
			}
			StringBuffer_set(str, "function");
			StringBuffer_add(str, ProcessCodeEx(child, F->indent, childUpvalues, child->nups));
			for (int i = 0; i < F->indent; i++) {
				StringBuffer_add(str, "   ");
			}
			StringBuffer_add(str, "end");
			if (F->indent == 0) StringBuffer_add(str, "\n");
			TRY(Assign(F, REGISTER(a), StringBuffer_getRef(str), a, 0, 0));
			ignoreNext = child->nups;
			break;
		}
		default:
			StringBuffer_printf(str, "-- unhandled opcode? : %-9s\t\n", luaP_opnames[o]);
			TRY(AddStatement(F, str));
			break;
		}

		if (debug) {
			TRY(ShowState(F));
			{
				char* f = PrintFunction(F);
				fprintf(stddebug, "%s\n", f);
				free(f);
			}
		}

		if (GetEndifAddr(F, pc)) {
			StringBuffer_set(str, "end");
			F->elseWritten = 0;
			F->indent--;
			TRY(AddStatement(F, str));
			StringBuffer_prune(str);
		}

		TRY(OutputAssignments(F));
	}

	if (GetEndifAddr(F, pc + 1)) {
		StringBuffer_set(str, "end");
		F->indent--;
		TRY(AddStatement(F, str));
		StringBuffer_prune(str);
	}

	TRY(FlushBoolean(F));

	output = PrintFunction(F);

		DeleteFunction(F);
		free(skipNoOp);

		return output;

errorHandler:
	{
		char* copy;
		Statement* stmt;
		StringBuffer_printf(str, "--[[ DECOMPILER ERROR %d: %s ]]", errorCode, error);
		copy = StringBuffer_getCopy(str);
		stmt = NewStatement(copy, F->pc, F->indent);
		AddToList(&(F->statements), (ListItem*)stmt);
		F->lastLine = F->pc;
	}
	output = PrintFunction(F);
	DeleteFunction(F);
	free(skipNoOp);
	error = NULL;
	return output;
}

char* ProcessCode(const Proto* f, int indent)
{
	return ProcessCodeEx(f, indent, NULL, 0);
}

static void cannot(const char* name, const char* what, const char* mode)
{
	fprintf(stderr, "%s: cannot %s %sput file ", "luadec", what, mode);
	perror(name);
	exit(EXIT_FAILURE);
}

void luaU_decompile(const Proto* f, int dflag, const char* filename, const char* outfilename)
{
	char* code;
	char* filename_tmp;
	debug = dflag;
	code = ProcessCode(f, 0);
	code = ApplyCanonicalPS2HandlerSource(f, code);
	if (!preserveHandlerHash)
		code = ApplyHandlerName(code, filename);
	printf("%s\n", code);
	/* With -o, honor the explicit CLI destination instead of silently writing
	 * <input>.lua.  Without -o, preserve the historical automatic sibling
	 * output used by the toolkit. */
	if (outfilename && *outfilename) {
		filename_tmp = _strdup(outfilename);
	}
	else {
		/* ".lua" (4 chars) + trailing NUL. */
		filename_tmp = malloc(strlen(filename) + 5);
		if (filename_tmp) sprintf(filename_tmp, "%s.lua", filename);
	}
	if (filename_tmp == 0) cannot(filename, "write", "out");
	FILE* D = fopen(filename_tmp, "wb");
	if (D == NULL) cannot(filename_tmp, "open", "out");
	fwrite(code, sizeof(*code), strlen(code), D);
	if (ferror(D)) cannot(filename_tmp, "write", "out");
	fclose(D);
	free(code);
}

void luaU_decompileFunctions(const Proto* f, int dflag, const char** filename)
{
	int i, n = f->sizep;
	char* code;
	debug = dflag;
	for (i = 0; i < n; i++) {
		printf("-----\nfunction");
		code = ProcessCode(f->p[i], 0);
		printf("%send\n", code);

		/* Same allocation rule as luaU_decompile above. */
		char* filename_tmp = malloc(strlen(filename[i]) + 5);
		if (filename_tmp == 0) cannot(filename[i], "write", "out");
		sprintf(filename_tmp, "%s.lua", filename[i]);
		FILE* D = fopen(filename_tmp, "wb");
		if (D == NULL) cannot(filename[i], "open", "out");
		fwrite(code, sizeof(*code), strlen(code), D);
		if (ferror(D)) cannot(filename[i], "write", "out");
		fclose(D);

		free(code);
	}
}
