# NFS Lua Tools
 Lua compiler and decompiler for Need for Speed BlackBox\
 Based on Hisham Muhammad decompiler with some fixes for NFS Bytecode.\
 Use Win32 version, because NFS is 32bit app.
 
Original Repo:
https://github.com/VAX325/NFS-MW-Lua-Toolkit
 
# Some info
 NFS (Black box at least) uses modifed Lua 5.0.1. Modifed because the struct lua_Number in NFS weight 4 bytes (it's float), but in normal Lua 5.0.1 it's double (8 bytes).
 
# Updates

- Added variables(Thanks to Felipe379), de-hashed function and parameters(Thanks to rx).
- Supports MW, CARBON PC/ MW, CARBON, UC PS2.
