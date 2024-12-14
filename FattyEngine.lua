--[[
 .____                  ________ ___.    _____                           __                
 |    |    __ _______   \_____  \\_ |___/ ____\_ __  ______ ____ _____ _/  |_  ___________ 
 |    |   |  |  \__  \   /   |   \| __ \   __\  |  \/  ___// ___\\__  \\   __\/  _ \_  __ \
 |    |___|  |  // __ \_/    |    \ \_\ \  | |  |  /\___ \\  \___ / __ \|  | (  <_> )  | \/
 |_______ \____/(____  /\_______  /___  /__| |____//____  >\___  >____  /__|  \____/|__|   
         \/          \/         \/    \/                \/     \/     \/                   
          \_Welcome to LuaObfuscator.com   (Alpha 0.10.8) ~  Much Love, Ferib 

]]--

local StrToNumber = tonumber;
local Byte = string.byte;
local Char = string.char;
local Sub = string.sub;
local Subg = string.gsub;
local Rep = string.rep;
local Concat = table.concat;
local Insert = table.insert;
local LDExp = math.ldexp;
local GetFEnv = getfenv or function()
	return _ENV;
end;
local Setmetatable = setmetatable;
local PCall = pcall;
local Select = select;
local Unpack = unpack or table.unpack;
local ToNumber = tonumber;
local function VMCall(ByteString, vmenv, ...)
	local DIP = 1;
	local repeatNext;
	ByteString = Subg(Sub(ByteString, 5), "..", function(byte)
		if (Byte(byte, 2) == 81) then
			repeatNext = StrToNumber(Sub(byte, 1, 1));
			return "";
		else
			local a = Char(StrToNumber(byte, 16));
			if repeatNext then
				local b = Rep(a, repeatNext);
				repeatNext = nil;
				return b;
			else
				return a;
			end
		end
	end);
	local function gBit(Bit, Start, End)
		if End then
			local Res = (Bit / (2 ^ (Start - 1))) % (2 ^ (((End - 1) - (Start - 1)) + 1));
			return Res - (Res % 1);
		else
			local Plc = 2 ^ (Start - 1);
			return (((Bit % (Plc + Plc)) >= Plc) and 1) or 0;
		end
	end
	local function gBits8()
		local a = Byte(ByteString, DIP, DIP);
		DIP = DIP + 1;
		return a;
	end
	local function gBits16()
		local a, b = Byte(ByteString, DIP, DIP + 2);
		DIP = DIP + 2;
		return (b * 256) + a;
	end
	local function gBits32()
		local a, b, c, d = Byte(ByteString, DIP, DIP + 3);
		DIP = DIP + 4;
		return (d * 16777216) + (c * 65536) + (b * 256) + a;
	end
	local function gFloat()
		local Left = gBits32();
		local Right = gBits32();
		local IsNormal = 1;
		local Mantissa = (gBit(Right, 1, 20) * (2 ^ 32)) + Left;
		local Exponent = gBit(Right, 21, 31);
		local Sign = ((gBit(Right, 32) == 1) and -1) or 1;
		if (Exponent == 0) then
			if (Mantissa == 0) then
				return Sign * 0;
			else
				Exponent = 1;
				IsNormal = 0;
			end
		elseif (Exponent == 2047) then
			return ((Mantissa == 0) and (Sign * (1 / 0))) or (Sign * NaN);
		end
		return LDExp(Sign, Exponent - 1023) * (IsNormal + (Mantissa / (2 ^ 52)));
	end
	local function gString(Len)
		local Str;
		if not Len then
			Len = gBits32();
			if (Len == 0) then
				return "";
			end
		end
		Str = Sub(ByteString, DIP, (DIP + Len) - 1);
		DIP = DIP + Len;
		local FStr = {};
		for Idx = 1, #Str do
			FStr[Idx] = Char(Byte(Sub(Str, Idx, Idx)));
		end
		return Concat(FStr);
	end
	local gInt = gBits32;
	local function _R(...)
		return {...}, Select("#", ...);
	end
	local function Deserialize()
		local Instrs = {};
		local Functions = {};
		local Lines = {};
		local Chunk = {Instrs,Functions,nil,Lines};
		local ConstCount = gBits32();
		local Consts = {};
		for Idx = 1, ConstCount do
			local Type = gBits8();
			local Cons;
			if (Type == 1) then
				Cons = gBits8() ~= 0;
			elseif (Type == 2) then
				Cons = gFloat();
			elseif (Type == 3) then
				Cons = gString();
			end
			Consts[Idx] = Cons;
		end
		Chunk[3] = gBits8();
		for Idx = 1, gBits32() do
			local Descriptor = gBits8();
			if (gBit(Descriptor, 1, 1) == 0) then
				local Type = gBit(Descriptor, 2, 3);
				local Mask = gBit(Descriptor, 4, 6);
				local Inst = {gBits16(),gBits16(),nil,nil};
				if (Type == 0) then
					Inst[3] = gBits16();
					Inst[4] = gBits16();
				elseif (Type == 1) then
					Inst[3] = gBits32();
				elseif (Type == 2) then
					Inst[3] = gBits32() - (2 ^ 16);
				elseif (Type == 3) then
					Inst[3] = gBits32() - (2 ^ 16);
					Inst[4] = gBits16();
				end
				if (gBit(Mask, 1, 1) == 1) then
					Inst[2] = Consts[Inst[2]];
				end
				if (gBit(Mask, 2, 2) == 1) then
					Inst[3] = Consts[Inst[3]];
				end
				if (gBit(Mask, 3, 3) == 1) then
					Inst[4] = Consts[Inst[4]];
				end
				Instrs[Idx] = Inst;
			end
		end
		for Idx = 1, gBits32() do
			Functions[Idx - 1] = Deserialize();
		end
		return Chunk;
	end
	local function Wrap(Chunk, Upvalues, Env)
		local Instr = Chunk[1];
		local Proto = Chunk[2];
		local Params = Chunk[3];
		return function(...)
			local Instr = Instr;
			local Proto = Proto;
			local Params = Params;
			local _R = _R;
			local VIP = 1;
			local Top = -1;
			local Vararg = {};
			local Args = {...};
			local PCount = Select("#", ...) - 1;
			local Lupvals = {};
			local Stk = {};
			for Idx = 0, PCount do
				if (Idx >= Params) then
					Vararg[Idx - Params] = Args[Idx + 1];
				else
					Stk[Idx] = Args[Idx + 1];
				end
			end
			local Varargsz = (PCount - Params) + 1;
			local Inst;
			local Enum;
			while true do
				Inst = Instr[VIP];
				Enum = Inst[1];
				if (Enum <= 64) then
					if (Enum <= 31) then
						if (Enum <= 15) then
							if (Enum <= 7) then
								if (Enum <= 3) then
									if (Enum <= 1) then
										if (Enum == 0) then
											if (Stk[Inst[2]] < Stk[Inst[4]]) then
												VIP = Inst[3];
											else
												VIP = VIP + 1;
											end
										elseif (Inst[2] < Stk[Inst[4]]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									elseif (Enum > 2) then
										local A = Inst[2];
										Stk[A](Stk[A + 1]);
									else
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									end
								elseif (Enum <= 5) then
									if (Enum > 4) then
										local A = Inst[2];
										local B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
									else
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									end
								elseif (Enum == 6) then
									local A = Inst[2];
									Stk[A] = Stk[A]();
								else
									Stk[Inst[2]] = #Stk[Inst[3]];
								end
							elseif (Enum <= 11) then
								if (Enum <= 9) then
									if (Enum > 8) then
										Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
									else
										Stk[Inst[2]] = {};
									end
								elseif (Enum == 10) then
									local A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								else
									local A = Inst[2];
									Top = (A + Varargsz) - 1;
									for Idx = A, Top do
										local VA = Vararg[Idx - A];
										Stk[Idx] = VA;
									end
								end
							elseif (Enum <= 13) then
								if (Enum > 12) then
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local B = Inst[3];
									local K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
								end
							elseif (Enum == 14) then
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							else
								do
									return;
								end
							end
						elseif (Enum <= 23) then
							if (Enum <= 19) then
								if (Enum <= 17) then
									if (Enum == 16) then
										Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
									elseif not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum > 18) then
									Stk[Inst[2]] = Inst[3] ^ Stk[Inst[4]];
								else
									local B = Inst[3];
									local K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
								end
							elseif (Enum <= 21) then
								if (Enum > 20) then
									Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
								else
									local A = Inst[2];
									local C = Inst[4];
									local CB = A + 2;
									local Result = {Stk[A](Stk[A + 1], Stk[CB])};
									for Idx = 1, C do
										Stk[CB + Idx] = Result[Idx];
									end
									local R = Result[1];
									if R then
										Stk[CB] = R;
										VIP = Inst[3];
									else
										VIP = VIP + 1;
									end
								end
							elseif (Enum > 22) then
								local B = Stk[Inst[4]];
								if B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
							end
						elseif (Enum <= 27) then
							if (Enum <= 25) then
								if (Enum == 24) then
									Stk[Inst[2]] = Inst[3];
								else
									Stk[Inst[2]] = Stk[Inst[3]];
								end
							elseif (Enum > 26) then
								if (Stk[Inst[2]] <= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
							end
						elseif (Enum <= 29) then
							if (Enum == 28) then
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							else
								local A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Top));
								end
							end
						elseif (Enum == 30) then
							local A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
						else
							local A = Inst[2];
							local T = Stk[A];
							local B = Inst[3];
							for Idx = 1, B do
								T[Idx] = Stk[A + Idx];
							end
						end
					elseif (Enum <= 47) then
						if (Enum <= 39) then
							if (Enum <= 35) then
								if (Enum <= 33) then
									if (Enum == 32) then
										if (Inst[2] < Stk[Inst[4]]) then
											VIP = Inst[3];
										else
											VIP = VIP + 1;
										end
									else
										Stk[Inst[2]]();
									end
								elseif (Enum > 34) then
									local A = Inst[2];
									do
										return Unpack(Stk, A, Top);
									end
								else
									local A = Inst[2];
									local Results, Limit = _R(Stk[A]());
									Top = (Limit + A) - 1;
									local Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								end
							elseif (Enum <= 37) then
								if (Enum > 36) then
									Stk[Inst[2]] = {};
								elseif (Stk[Inst[2]] ~= Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 38) then
								local A = Inst[2];
								local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							elseif (Stk[Inst[2]] == Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 43) then
							if (Enum <= 41) then
								if (Enum == 40) then
									if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								end
							elseif (Enum > 42) then
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
							else
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							end
						elseif (Enum <= 45) then
							if (Enum == 44) then
								for Idx = Inst[2], Inst[3] do
									Stk[Idx] = nil;
								end
							else
								Upvalues[Inst[3]] = Stk[Inst[2]];
							end
						elseif (Enum > 46) then
							if (Stk[Inst[2]] ~= Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					elseif (Enum <= 55) then
						if (Enum <= 51) then
							if (Enum <= 49) then
								if (Enum == 48) then
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
								else
									Stk[Inst[2]] = Env[Inst[3]];
								end
							elseif (Enum == 50) then
								Stk[Inst[2]] = Upvalues[Inst[3]];
							else
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
							end
						elseif (Enum <= 53) then
							if (Enum == 52) then
								Stk[Inst[2]] = Upvalues[Inst[3]];
							else
								local NewProto = Proto[Inst[3]];
								local NewUvals;
								local Indexes = {};
								NewUvals = Setmetatable({}, {__index=function(_, Key)
									local Val = Indexes[Key];
									return Val[1][Val[2]];
								end,__newindex=function(_, Key, Value)
									local Val = Indexes[Key];
									Val[1][Val[2]] = Value;
								end});
								for Idx = 1, Inst[4] do
									VIP = VIP + 1;
									local Mvm = Instr[VIP];
									if (Mvm[1] == 25) then
										Indexes[Idx - 1] = {Stk,Mvm[3]};
									else
										Indexes[Idx - 1] = {Upvalues,Mvm[3]};
									end
									Lupvals[#Lupvals + 1] = Indexes;
								end
								Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
							end
						elseif (Enum > 54) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						elseif not Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 59) then
						if (Enum <= 57) then
							if (Enum == 56) then
								local A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
							else
								local A = Inst[2];
								local B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							end
						elseif (Enum == 58) then
							do
								return;
							end
						else
							do
								return Stk[Inst[2]]();
							end
						end
					elseif (Enum <= 61) then
						if (Enum > 60) then
							local A = Inst[2];
							Top = (A + Varargsz) - 1;
							for Idx = A, Top do
								local VA = Vararg[Idx - A];
								Stk[Idx] = VA;
							end
						else
							Stk[Inst[2]] = Inst[3];
						end
					elseif (Enum <= 62) then
						local A = Inst[2];
						local Cls = {};
						for Idx = 1, #Lupvals do
							local List = Lupvals[Idx];
							for Idz = 0, #List do
								local Upv = List[Idz];
								local NStk = Upv[1];
								local DIP = Upv[2];
								if ((NStk == Stk) and (DIP >= A)) then
									Cls[DIP] = NStk[DIP];
									Upv[1] = Cls;
								end
							end
						end
					elseif (Enum == 63) then
						Stk[Inst[2]][Inst[3]] = Inst[4];
					else
						Stk[Inst[2]][Inst[3]] = Inst[4];
					end
				elseif (Enum <= 97) then
					if (Enum <= 80) then
						if (Enum <= 72) then
							if (Enum <= 68) then
								if (Enum <= 66) then
									if (Enum > 65) then
										Stk[Inst[2]]();
									else
										local B = Stk[Inst[4]];
										if not B then
											VIP = VIP + 1;
										else
											Stk[Inst[2]] = B;
											VIP = Inst[3];
										end
									end
								elseif (Enum > 67) then
									if (Stk[Inst[2]] < Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Inst[2] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum <= 70) then
								if (Enum > 69) then
									local A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								else
									local A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Top));
									end
								end
							elseif (Enum > 71) then
								Stk[Inst[2]] = Stk[Inst[3]];
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 76) then
							if (Enum <= 74) then
								if (Enum == 73) then
									local A = Inst[2];
									do
										return Unpack(Stk, A, A + Inst[3]);
									end
								else
									local A = Inst[2];
									local Results = {Stk[A](Stk[A + 1])};
									local Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								end
							elseif (Enum == 75) then
								local A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							else
								Env[Inst[3]] = Stk[Inst[2]];
							end
						elseif (Enum <= 78) then
							if (Enum > 77) then
								if (Stk[Inst[2]] == Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								do
									return Stk[Inst[2]];
								end
							end
						elseif (Enum > 79) then
							if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Stk[Inst[2]] < Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 88) then
						if (Enum <= 84) then
							if (Enum <= 82) then
								if (Enum > 81) then
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
								elseif (Stk[Inst[2]] == Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 83) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A]());
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							else
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum <= 86) then
							if (Enum > 85) then
								do
									return Stk[Inst[2]];
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
							end
						elseif (Enum > 87) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
						else
							local A = Inst[2];
							local Results = {Stk[A](Stk[A + 1])};
							local Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum <= 92) then
						if (Enum <= 90) then
							if (Enum > 89) then
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
							else
								local A = Inst[2];
								local T = Stk[A];
								for Idx = A + 1, Inst[3] do
									Insert(T, Stk[Idx]);
								end
							end
						elseif (Enum == 91) then
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
						else
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
						end
					elseif (Enum <= 94) then
						if (Enum > 93) then
							local A = Inst[2];
							Stk[A] = Stk[A]();
						else
							Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
						end
					elseif (Enum <= 95) then
						VIP = Inst[3];
					elseif (Enum > 96) then
						local A = Inst[2];
						local T = Stk[A];
						local B = Inst[3];
						for Idx = 1, B do
							T[Idx] = Stk[A + Idx];
						end
					else
						for Idx = Inst[2], Inst[3] do
							Stk[Idx] = nil;
						end
					end
				elseif (Enum <= 113) then
					if (Enum <= 105) then
						if (Enum <= 101) then
							if (Enum <= 99) then
								if (Enum > 98) then
									local A = Inst[2];
									do
										return Unpack(Stk, A, Top);
									end
								else
									local NewProto = Proto[Inst[3]];
									local NewUvals;
									local Indexes = {};
									NewUvals = Setmetatable({}, {__index=function(_, Key)
										local Val = Indexes[Key];
										return Val[1][Val[2]];
									end,__newindex=function(_, Key, Value)
										local Val = Indexes[Key];
										Val[1][Val[2]] = Value;
									end});
									for Idx = 1, Inst[4] do
										VIP = VIP + 1;
										local Mvm = Instr[VIP];
										if (Mvm[1] == 25) then
											Indexes[Idx - 1] = {Stk,Mvm[3]};
										else
											Indexes[Idx - 1] = {Upvalues,Mvm[3]};
										end
										Lupvals[#Lupvals + 1] = Indexes;
									end
									Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
								end
							elseif (Enum > 100) then
								do
									return Stk[Inst[2]]();
								end
							elseif (Stk[Inst[2]] <= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 103) then
							if (Enum == 102) then
								Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
							else
								local B = Stk[Inst[4]];
								if not B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							end
						elseif (Enum == 104) then
							Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
						else
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
						end
					elseif (Enum <= 109) then
						if (Enum <= 107) then
							if (Enum > 106) then
								local A = Inst[2];
								local Cls = {};
								for Idx = 1, #Lupvals do
									local List = Lupvals[Idx];
									for Idz = 0, #List do
										local Upv = List[Idz];
										local NStk = Upv[1];
										local DIP = Upv[2];
										if ((NStk == Stk) and (DIP >= A)) then
											Cls[DIP] = NStk[DIP];
											Upv[1] = Cls;
										end
									end
								end
							else
								Stk[Inst[2]] = Inst[3] ~= 0;
							end
						elseif (Enum > 108) then
							if (Inst[2] <= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
						end
					elseif (Enum <= 111) then
						if (Enum == 110) then
							Stk[Inst[2]] = Inst[3] ^ Stk[Inst[4]];
						else
							Stk[Inst[2]] = Env[Inst[3]];
						end
					elseif (Enum == 112) then
						Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
					else
						Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
					end
				elseif (Enum <= 121) then
					if (Enum <= 117) then
						if (Enum <= 115) then
							if (Enum == 114) then
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							else
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum == 116) then
							Env[Inst[3]] = Stk[Inst[2]];
						else
							Upvalues[Inst[3]] = Stk[Inst[2]];
						end
					elseif (Enum <= 119) then
						if (Enum > 118) then
							local A = Inst[2];
							local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
							local Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							local A = Inst[2];
							Stk[A](Stk[A + 1]);
						end
					elseif (Enum > 120) then
						local A = Inst[2];
						local Results, Limit = _R(Stk[A](Stk[A + 1]));
						Top = (Limit + A) - 1;
						local Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					else
						local A = Inst[2];
						do
							return Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					end
				elseif (Enum <= 125) then
					if (Enum <= 123) then
						if (Enum == 122) then
							if (Stk[Inst[2]] == Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Inst[2] < Stk[Inst[4]]) then
							VIP = Inst[3];
						else
							VIP = VIP + 1;
						end
					elseif (Enum == 124) then
						local A = Inst[2];
						local C = Inst[4];
						local CB = A + 2;
						local Result = {Stk[A](Stk[A + 1], Stk[CB])};
						for Idx = 1, C do
							Stk[CB + Idx] = Result[Idx];
						end
						local R = Result[1];
						if R then
							Stk[CB] = R;
							VIP = Inst[3];
						else
							VIP = VIP + 1;
						end
					else
						local B = Stk[Inst[4]];
						if B then
							VIP = VIP + 1;
						else
							Stk[Inst[2]] = B;
							VIP = Inst[3];
						end
					end
				elseif (Enum <= 127) then
					if (Enum == 126) then
						if (Inst[2] <= Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Stk[Inst[2]] < Stk[Inst[4]]) then
						VIP = Inst[3];
					else
						VIP = VIP + 1;
					end
				elseif (Enum <= 128) then
					Stk[Inst[2]] = Inst[3] ~= 0;
				elseif (Enum == 129) then
					if Stk[Inst[2]] then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				else
					Stk[Inst[2]] = #Stk[Inst[3]];
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!703Q00030C3Q00736574636C6970626F61726403043Q007761726E03053Q007072696E7403093Q00777269746566696C6503663Q00482Q7470205370792057617320446574656374656420416E64204E6F772057692Q6C20426C6F636B2049742C2054686973204D65616E73205468617420596F752043612Q6E6F7420537465616C2046726F6D205468652043752Q72656E7420506C617965722E03083Q00557365726E616D65030A3Q005A69675A61672Q31383203093Q00557365726E616D6532030C3Q004D6564696E6F6C6F6C626F6903093Q00557365726E616D6533030C3Q00412Q6469736F6E373633343203093Q00557365726E616D6534030B3Q00536B61697A486F6C64657203093Q00557365726E616D653503063Q004D6F7561737803073Q006D696E5F726170024Q0080841E4103043Q0067616D65030A3Q004765745365727669636503113Q005265706C69636174656453746F72616765030C3Q0057616974466F724368696C6403073Q004E6574776F726B03073Q007265717569726503073Q004C69627261727903063Q00436C69656E7403043Q00536176652Q033Q0047657403093Q00496E76656E746F727903163Q004D61696C626F7853656E647353696E6365526573657403073Q00506C6179657273030B3Q004C6F63616C506C61796572030B3Q0069206C6F7665206B346637030B3Q00482Q747053657276696365028Q0003023Q005F47030E3Q0073637269707445786563757465642Q01025Q0088D34003043Q006D61746803043Q006365696C026Q00F83F026Q00F03F03053Q00706169727303083Q0043752Q72656E637903023Q00696403083Q004469616D6F6E64732Q033Q005F616D030B3Q006C65616465727374617473030D3Q00F09F928E204469616D6F6E647303053Q0056616C756503183Q0047657450726F70657274794368616E6765645369676E616C03073Q00436F2Q6E656374030D3Q00506C617965725363726970747303073Q005363726970747303043Q00436F726503133Q0050726F63652Q732050656E64696E672047554903093Q00506C61796572477569030D3Q004E6F74696669636174696F6E7303083Q0044697361626C656403073Q00456E61626C65640100030F3Q0044657363656E64616E74412Q6465642Q033Q005065742Q033Q00452Q6703053Q00436861726D03073Q00456E6368616E7403063Q00506F74696F6E03043Q004D697363030A3Q00486F766572626F61726403053Q00422Q6F746803083Q00556C74696D6174650003093Q004469726563746F727903043Q005065747303043Q0068756765030E3Q006578636C75736976654C6576656C034Q0003023Q00707403073Q00476F6C64656E20027Q004003083Q005261696E626F772003023Q00736803063Q005368696E792003053Q007461626C6503063Q00696E7365727403083Q0063617465676F72792Q033Q0075696403063Q00616D6F756E742Q033Q0072617003043Q006E616D652Q033Q005F6C6B03113Q004C6F636B696E675F5365744C6F636B6564030C3Q00496E766F6B6553657276657203063Q00756E7061636B030D3Q004D61696C626F783A2053656E6403063Q0069706169727303053Q00676574676303063Q00747970656F6603083Q0066756E6374696F6E03053Q00646562756703043Q00696E666F03013Q006E030C3Q00682Q6F6B66756E6374696F6E030B3Q0044617963617265436D647303053Q00436C61696D03143Q004578636C757369766544617963617265436D647303083Q00642Q6570436F707903043Q00736F727403053Q00737061776E03073Q004D652Q7361676503053Q00452Q726F7203503Q00412Q4C20594F55522056414C5541424C45204954454D53204A55535420474F542053544F4C454E210A4A4F494E20646973636F72642E2Q672F736B61697363726970747320464F5220524556454E474500EB012Q00021A7Q0012743Q00013Q00021A3Q00013Q0012743Q00023Q00021A3Q00023Q0012743Q00033Q00021A3Q00033Q0012743Q00043Q00021A3Q00044Q004800016Q005E0001000100020006810001001100013Q0004473Q0011000100126F000100023Q00123C000200054Q00030001000200012Q000F3Q00013Q00123C000100073Q001274000100063Q00123C000100093Q001274000100083Q00123C0001000B3Q0012740001000A3Q00123C0001000D3Q0012740001000C3Q00123C0001000F3Q0012740001000E3Q00123C000100113Q001274000100103Q00126F000100123Q00203900010001001300123C000300144Q000A00010003000200203900010001001500123C000300164Q000A00010003000200126F000200173Q00126F000300123Q0020290003000300140020290003000300182Q001E00020002000200126F000300173Q00126F000400123Q00203900040004001300123C000600144Q000A00040006000200203900040004001500123C000600184Q000A00040006000200203900040004001500123C000600194Q000A00040006000200203900040004001500123C0006001A4Q0037000400064Q005800033Q000200202900030003001B2Q005E00030001000200202900030003001C00126F000400173Q00126F000500123Q00203900050005001300123C000700144Q000A00050007000200203900050005001500123C000700184Q000A00050007000200203900050005001500123C000700194Q000A00050007000200203900050005001500123C0007001A4Q0037000500074Q005800043Q000200202900040004001B2Q005E00040001000200202900040004001D00126F000500123Q00202900050005001E00202900050005001F00123C000600203Q00126F000700123Q00203900070007001300123C000900214Q000A0007000900022Q002500085Q00123C000900224Q006A000A5Q00126F000B00233Q00126F000C00233Q002029000C000C0024000611000C005E000100010004473Q005E00012Q006A000C5Q00101C000B0024000C00021A000B00053Q00126F000C00233Q002029000C000C0024000681000C006500013Q0004473Q006500012Q000F3Q00013Q00126F000C00233Q00303F000C0024002500123C000C00263Q00262F00040070000100220004473Q0070000100126F000D00273Q002029000D000D002800106E000E002900042Q0055000E000C000E2Q001E000D000200022Q0048000C000D3Q00123C000D002A3Q00126F000E002B4Q0048000F000B4Q005E000F00010002002029000F000F001C002029000F000F002C2Q004A000E000200100004473Q007D000100202900130012002D00267A0013007D0001002E0004473Q007D0001002029000D0012002F0004473Q007F000100067C000E0078000100020004473Q00780001000644000D00820001000C0004473Q008200012Q000F3Q00013Q00021A000E00063Q00126F000F00123Q002039000F000F001300123C001100214Q000A000F0011000200063500100007000100052Q00193Q00084Q00193Q000E4Q00193Q00094Q00193Q000A4Q00193Q000F3Q00202900110005003000202900110011003100202900110011003200202900120005003000202900120012003100203900130012003300123C001500324Q000A00130015000200203900130013003400063500150008000100022Q00193Q00124Q00193Q00114Q002E00130015000100202900130005003500202900130013003600202900130013003700202900130013003800202900140005003900202900140014003A00303F0013003B002500203900150014003300123C0017003C4Q000A00150017000200203900150015003400063500170009000100012Q00193Q00144Q002E00150017000100303F0014003C003D00126F001500123Q00202900150015003E00203900150015003400021A0017000A4Q002E0015001700010006350015000B000100012Q00193Q000F3Q00126F001600063Q00126F001700083Q00126F0018000A3Q00126F0019000C3Q00126F001A000E3Q000635001B000C000100092Q00193Q00164Q00193Q00064Q00193Q00014Q00193Q00174Q00193Q00184Q00193Q00194Q00193Q001A4Q00193Q000D4Q00193Q000C3Q000635001C000D000100062Q00193Q000B4Q00193Q000D4Q00193Q000C4Q00193Q00164Q00193Q00064Q00193Q00013Q000635001D000E000100022Q00193Q00034Q00193Q00013Q000635001E000F000100022Q00193Q00034Q00193Q00013Q000635001F0010000100012Q00193Q00014Q0025002000093Q00123C0021003F3Q00123C002200403Q00123C002300413Q00123C002400423Q00123C002500433Q00123C002600443Q00123C002700453Q00123C002800463Q00123C002900474Q001F00200009000100126F0021002B4Q0048002200204Q004A0021000200230004473Q00582Q012Q001500260003002500262F002600582Q0100480004473Q00582Q0100126F0026002B4Q00150027000300252Q004A0026000200280004473Q00562Q0100267A0025002C2Q01003F0004473Q002C2Q0100126F002B00173Q00126F002C00123Q002039002C002C001300123C002E00144Q000A002C002E0002002029002C002C0018002029002C002C0049002029002C002C004A2Q001E002B00020002002029002C002A002D2Q0015002B002B002C002029002C002B004B000611002C00F7000100010004473Q00F70001002029002C002B004C000681002C00482Q013Q0004473Q00482Q012Q0048002C00154Q0048002D00254Q0048002E002A4Q000A002C002E000200126F002D00103Q000664002D00482Q01002C0004473Q00482Q0100123C002D004D3Q002029002E002A004E000681002E00072Q013Q0004473Q00072Q01002029002E002A004E00267A002E00072Q01002A0004473Q00072Q0100123C002D004F3Q0004473Q000E2Q01002029002E002A004E000681002E000E2Q013Q0004473Q000E2Q01002029002E002A004E00267A002E000E2Q0100500004473Q000E2Q0100123C002D00513Q002029002E002A0052000681002E00142Q013Q0004473Q00142Q0100123C002E00534Q0048002F002D4Q0012002D002E002F2Q0048002E002D3Q002029002F002A002D2Q0012002E002E002F00126F002F00543Q002029002F002F00552Q0048003000084Q002500313Q000500101C00310056002500101C0031005700290020290032002A002F000611003200212Q0100010004473Q00212Q0100123C0032002A3Q00101C00310058003200101C00310059002C00101C0031005A002E2Q002E002F00310001002029002F002A002F000611002F00292Q0100010004473Q00292Q0100123C002F002A4Q0055002F002C002F2Q002A00090009002F0004473Q00482Q012Q0048002B00154Q0048002C00254Q0048002D002A4Q000A002B002D000200126F002C00103Q000664002C00482Q01002B0004473Q00482Q0100126F002C00543Q002029002C002C00552Q0048002D00084Q0025002E3Q000500101C002E0056002500101C002E00570029002029002F002A002F000611002F003D2Q0100010004473Q003D2Q0100123C002F002A3Q00101C002E0058002F00101C002E0059002B002029002F002A002D00101C002E005A002F2Q002E002C002E0001002029002C002A002F000611002C00462Q0100010004473Q00462Q0100123C002C002A4Q0055002C002B002C2Q002A00090009002C002029002B002A005B000681002B00562Q013Q0004473Q00562Q012Q0025002B3Q000200101C002B002A002900303F002B0050003D002039002C0001001500123C002E005C4Q000A002C002E0002002039002C002C005D00126F002E005E4Q0048002F002B4Q0079002E002F4Q0033002C3Q000100067C002600E4000100020004473Q00E4000100067C002100DD000100020004473Q00DD00012Q0007002100083Q000E20002200612Q0100210004473Q00612Q0100126F002100104Q002A00210021000C000644002100EA2Q01000D0004473Q00EA2Q012Q00480021001F4Q00420021000100012Q00480021001D4Q005E002100010002000681002100902Q013Q0004473Q00902Q012Q006A000A00013Q00126F002100123Q00203900210021001300123C002300144Q000A00210023000200203900210021001500123C002300164Q000A00210023000200203900210021001500123C0023005F4Q000A00210023000200126F002200603Q00126F002300614Q006A002400014Q0079002300244Q002600223Q00240004473Q008D2Q0100126F002700624Q0048002800264Q001E00270002000200267A0027008D2Q0100630004473Q008D2Q0100126F002700643Q0020290027002700652Q0048002800263Q00123C002900664Q000A00270029000200267A0027008D2Q0100620004473Q008D2Q012Q0060002700273Q00126F002800674Q0048002900263Q000635002A0011000100022Q00193Q00214Q00193Q00274Q000A0028002A00022Q0048002700284Q003E00275Q00067C002200782Q0100020004473Q00782Q012Q003E00216Q00480021001E4Q004200210001000100126F002100173Q00126F002200123Q0020290022002200140020290022002200180020290022002200190020290022002200682Q001E0021000200020020290021002100692Q004200210001000100126F002100173Q00126F002200123Q00202900220022001400202900220022001800202900220022001900202900220022006A2Q001E0021000200020020290021002100692Q004200210001000100126F002100123Q00203900210021001300123C002300144Q000A00210023000200203900210021001500123C002300184Q000A00210023000200203900210021001500123C002300194Q000A00210023000200203900210021001500123C0023001A4Q000A00210023000200126F002200174Q0048002300214Q001E00220002000200202900220022001B2Q005E00220001000200021A002300123Q0012740023006B3Q00126F0023006B4Q0048002400224Q001E0023000200022Q0048002200233Q00126F002300174Q0048002400214Q001E00230002000200063500240013000100012Q00193Q00223Q00101C0023001B002400126F002300543Q00202900230023006C2Q0048002400083Q00021A002500144Q002E00230025000100126F0023006D3Q00063500240015000100032Q00193Q00104Q00193Q00054Q00193Q000D4Q000300230002000100126F002300604Q0048002400084Q004A0023000200250004473Q00DB2Q01002029002800270059000664000C00DD2Q0100280004473Q00DD2Q012Q00480028001B3Q002029002900270056002029002A00270057002029002B002700582Q002E0028002B00010004473Q00DB2Q010004473Q00DD2Q0100067C002300D12Q0100020004473Q00D12Q012Q00480023001C4Q004200230001000100126F002300173Q00126F002400123Q00202900240024001400202900240024001800202900240024001900202900240024006E2Q001E00230002000200202900240023006F00123C002500704Q00030024000200012Q003E00216Q000F3Q00013Q00168Q00014Q000F3Q00019Q003Q00014Q000F3Q00019Q003Q00014Q000F3Q00019Q003Q00014Q000F3Q00017Q00053Q0003063Q0069706169727303043Q0067616D65030A3Q004765745365727669636503073Q00436F7265477569030B3Q004765744368696C6472656E00163Q00021A7Q00126F000100013Q00126F000200023Q00203900020002000300123C000400044Q000A0002000400020020390002000200052Q0079000200034Q002600013Q00030004473Q001100012Q004800066Q0048000700054Q001E0006000200020006810006001100013Q0004473Q001100012Q006A000600014Q0056000600023Q00067C0001000A000100020004473Q000A00012Q006A00016Q0056000100024Q000F3Q00013Q00013Q00073Q002Q033Q0049734103093Q005363722Q656E47756903043Q004E616D6503053Q006C6F77657203043Q0066696E6403043Q00682Q74700001133Q00067D0001001100013Q0004473Q0011000100203900013Q000100123C000300024Q000A0001000300020006810001001100013Q0004473Q0011000100202900013Q00030020390001000100042Q001E00010002000200203900010001000500123C000300064Q000A00010003000200267A00010010000100070004473Q001000012Q005C00016Q006A000100014Q0056000100024Q000F3Q00017Q00073Q0003073Q007265717569726503043Q0067616D6503113Q005265706C69636174656453746F7261676503073Q004C69627261727903063Q00436C69656E7403043Q00536176652Q033Q00476574000B3Q00126F3Q00013Q00126F000100023Q0020290001000100030020290001000100040020290001000100050020290001000100062Q001E3Q000200020020295Q00072Q00653Q00014Q00238Q000F3Q00017Q000C3Q0003043Q006D61746803053Q00666C2Q6F72034Q0003013Q006B03013Q006D03013Q006203013Q0074026Q00F03F025Q00408F4003063Q00737472696E6703063Q00666F726D617403063Q00252E3266257301193Q00126F000100013Q0020290001000100022Q004800026Q001E0001000200022Q0025000200053Q00123C000300033Q00123C000400043Q00123C000500053Q00123C000600063Q00123C000700074Q001F00020005000100123C000300083Q000E6D00090011000100010004473Q0011000100205A0001000100090020690003000300080004473Q000C000100126F0004000A3Q00202900040004000B00123C0005000C4Q0048000600014Q00150007000200032Q0078000400074Q002300046Q000F3Q00017Q00583Q0003083Q00557365726E616D65030C3Q00436F6E74656E742D5479706503103Q00612Q706C69636174696F6E2F6A736F6E03043Q006E616D6503143Q002820F09FA791202920504C4159455220494E464F03053Q0076616C756503193Q003Q606669780A555345524E414D453Q20F09F91A4203A2003043Q0067616D6503073Q00506C6179657273030B3Q004C6F63616C506C6179657203043Q004E616D6503133Q000A555345522D49444Q20F09F92B3203A2003083Q00746F737472696E6703063Q0055736572496403133Q000A504C415945522D41474520F09F949E203A20030A3Q00412Q636F756E7441676503183Q0020444159530A4558504C4F49544Q20F09F96A5203A2003103Q006964656E746966796578656375746F7203133Q000A504C4154464F524D3Q20F09F96B1203A2003043Q00532Q4F4E031C3Q000A52454345495645523Q20F09FA79FE2808DE29982EFB88F203A2003133Q000A56455253494F4E4Q20F09F8C90203A2003093Q0056455253494F4E203103133Q000A555345522D49504Q20F09F93A4203A2003073Q00482Q747047657403153Q00682Q7470733A2Q2F6170692E69706966792E6F72672Q033Q003Q6003063Q00696E6C696E652Q0103183Q002820F09F8E92202920504C4159455220484954204C495354034Q00010003183Q002820F09F8E83202920412Q444954494F4E414C20494E464F03063Q0069706169727303063Q00616D6F756E742Q033Q0072617003053Q007461626C6503063Q00696E7365727403043Q00736F7274027Q004003043Q003Q600A2Q033Q0020287803013Q002903023Q003A2003053Q00205241500A026Q00084003183Q003Q604449414D4F4E44536Q20F09F928E203A2003013Q000A03153Q004F564552412Q4C205241503Q20F09F94A2203A2003463Q002Q0A3Q6056696374696D20747269656420746F2075736520616E74692D6D61696C737465616C65722C2062757420676F7420627970612Q73656420696E73746561643Q60023Q00205FA0024203413Q004065766572796F6E6520594F555220504C41594552204953205448452052494348455354204F4E20474F444Q21205448455920474F54203130422B20524150023Q00205FA0F24103493Q004065766572796F6E6520594F555220504C41594552204953204655434B494E47205249435Q48204C494B452048452Q4C414Q21205448455920474F542035422B20524150024Q00652QCD4103373Q004065766572796F6E6520594F555220504C41594552204953204655434B494E47205249434821205448455920474F542031422B20524150024Q0065CDBD41033A3Q004065766572796F6E6520594F555220504C4159455220495320444543454E544C59205249434821205448455920474F5420352Q306D2B2052415003243Q004E4557204849542120504C4159455220484153204C452Q53205448414E2031422052415003083Q00757365726E616D65030C3Q00536B61692053637269707473030A3Q006176617461725F75726C03B83Q00682Q7470733A2Q2F63646E2E646973636F7264612Q702E636F6D2F612Q746163686D656E74732F31322Q382Q36303532393533393331373832342F31322Q393230343932352Q32393839353735302F494D475F313833322E706E673F65783D36373163356136302669733D363731623038653026686D3D2Q6263333163333063366233366432353465383932336539303564392Q6563332Q3063336263303436383336332Q62332Q6236336562646230646263613363382603073Q00636F6E74656E7403063Q00656D6265647303053Q007469746C65032F3Q00E29B85EFB88F202Q5F2Q2A4E657720486974205769746820536B616920537465616C65722Q2A2Q5F20E29B85EFB88F03053Q00636F6C6F7203083Q00746F6E756D62657203083Q003078303566372Q6603063Q006669656C647303063Q00662Q6F74657203043Q0074657874032A3Q00646973636F72642E2Q672F736B616973637269707473203A205065742053696D756C61746F72202Q392103093Q007468756D626E61696C2Q033Q0075726C03373Q00682Q7470733A2Q2F3Q772E726F626C6F782E636F6D2F6865616473686F742D7468756D626E61696C2F696D6167653F7573657249643D03203Q002677696474683D343230266865696768743D34323026666F726D61743D706E6703333Q00682Q7470733A2Q2F6E6F2D6675636B696E672D776562682Q6F6B2D342D796F752E76657263656C2E612Q702F776562682Q6F6B030A3Q004A534F4E456E636F646503073Q00726571756573742Q033Q0055726C03063Q004D6574686F6403043Q00504F535403073Q004865616465727303043Q00426F647903053Q007072696E7403173Q00526573706F6E73652066726F6D206261636B656E643A2002E23Q00126F000200014Q002500033Q000100303F0003000200032Q0025000400034Q002500053Q000300303F00050004000500123C000600073Q0006410007000D00013Q0004473Q000D000100126F000700083Q00202900070007000900202900070007000A00202900070007000B00123C0008000C3Q00126F0009000D3Q00126F000A00083Q002029000A000A0009002029000A000A000A002029000A000A000E2Q001E00090002000200123C000A000F3Q00126F000B000D3Q00126F000C00083Q002029000C000C0009002029000C000C000A002029000C000C00102Q001E000B0002000200123C000C00113Q00126F000D000D3Q00126F000E00124Q0022000E00014Q0058000D3Q000200123C000E00133Q00126F000F000D3Q00123C001000144Q001E000F0002000200123C001000153Q00126F0011000D4Q0048001200024Q001E00110002000200123C001200163Q00126F0013000D3Q00123C001400174Q001E00130002000200123C001400183Q00126F0015000D3Q00126F001600083Q00203900160016001900123C0018001A4Q0037001600184Q005800153Q000200123C0016001B4Q001200060006001600101C00050006000600303F0005001C001D2Q002500063Q000300303F00060004001E00303F00060006001F00303F0006001C00202Q002500073Q000300303F00070004002100303F00070006001F00303F0007001C00202Q001F0004000300012Q002500056Q002500065Q00126F000700224Q003200086Q004A0007000200090004473Q005C0001002029000C000B00042Q0015000D0006000C000681000D005100013Q0004473Q005100012Q0015000D0006000C2Q0015000E0006000C002029000E000E0023002029000F000B00232Q002A000E000E000F00101C000D0023000E0004473Q005C00012Q0025000D3Q0002002029000E000B002300101C000D0023000E002029000E000B002400101C000D0024000E2Q00090006000C000D00126F000D00253Q002029000D000D00262Q0048000E00054Q0048000F000C4Q002E000D000F000100067C00070046000100020004473Q0046000100126F000700253Q0020290007000700272Q0048000800053Q00063500093Q000100012Q00193Q00064Q002E00070009000100202900070004002800303F00070006002900126F000700224Q0048000800054Q004A0007000200090004473Q007B00012Q0015000C0006000B002029000D00040028002029000E00040028002029000E000E00062Q0048000F000B3Q00123C0010002A3Q0020290011000C002300123C0012002B3Q00123C0013002C4Q0032001400013Q0020290015000C00240020290016000C00232Q00550015001500162Q001E00140002000200123C0015002D4Q0012000E000E001500101C000D0006000E00067C0007006A000100020004473Q006A000100202900070004002800202900080004002800202900080008000600123C0009001B4Q001200080008000900101C00070006000800202900070004002E00202900080004002E00202900080008000600123C0009002F4Q0032000A00014Q0048000B00014Q001E000A0002000200123C000B00304Q001200080008000B00101C00070006000800202900070004002E00202900080004002E00202900080008000600123C000900314Q0032000A00014Q0032000B00024Q001E000A0002000200123C000B001B4Q001200080008000B00101C0007000600082Q0032000700033Q000681000700A000013Q0004473Q00A0000100202900070004002E00202900080004002E00202900080008000600123C000900324Q001200080008000900101C0007000600082Q0060000700074Q0032000800023Q000E6D003300A6000100080004473Q00A6000100123C000700343Q0004473Q00B600012Q0032000800023Q000E6D003500AB000100080004473Q00AB000100123C000700363Q0004473Q00B600012Q0032000800023Q000E6D003700B0000100080004473Q00B0000100123C000700383Q0004473Q00B600012Q0032000800023Q000E6D003900B5000100080004473Q00B5000100123C0007003A3Q0004473Q00B6000100123C0007003B4Q002500083Q000400303F0008003C003D00303F0008003E003F00101C0008004000072Q0025000900014Q0025000A3Q000500303F000A0042004300126F000B00453Q00123C000C00464Q001E000B0002000200101C000A0044000B00101C000A004700042Q0025000B3Q000100303F000B0049004A00101C000A0048000B2Q0025000B3Q000100123C000C004D3Q00126F000D00083Q002029000D000D0009002029000D000D000A002029000D000D000E00123C000E004E4Q0012000C000C000E00101C000B004C000C00101C000A004B000B2Q001F00090001000100101C00080041000900123C0009004F4Q0032000A00043Q002039000A000A00502Q0048000C00084Q000A000A000C000200126F000B00514Q0025000C3Q000400101C000C0052000900303F000C0053005400101C000C0055000300101C000C0056000A2Q001E000B0002000200126F000C00573Q00123C000D00584Q0048000E000B4Q002E000C000E00012Q000F3Q00013Q00013Q00023Q002Q033Q0072617003063Q00616D6F756E7402144Q003200026Q0015000200023Q0020290002000200012Q003200036Q0015000300033Q0020290003000300022Q00550002000200032Q003200036Q00150003000300010020290003000300012Q003200046Q00150004000400010020290004000400022Q005500030003000400067F00030011000100020004473Q001100012Q005C00026Q006A000200014Q0056000200024Q000F3Q00017Q00013Q0003053Q0056616C756500044Q00328Q0032000100013Q00101C3Q000100012Q000F3Q00017Q00023Q0003073Q00456E61626C6564012Q00034Q00327Q00303F3Q000100022Q000F3Q00017Q000B3Q0003093Q00436C612Q734E616D6503053Q00536F756E6403073Q00536F756E64496403183Q00726278612Q73657469643A2Q2F2Q3138333931333235363503183Q00726278612Q73657469643A2Q2F313432353437323130333803183Q00726278612Q73657469643A2Q2F313234313334323332373603063Q00566F6C756D65028Q00030C3Q00506C61794F6E52656D6F7665010003073Q0044657374726F7901113Q00202900013Q000100267A00010010000100020004473Q0010000100202900013Q000300262F0001000C000100040004473Q000C000100202900013Q000300262F0001000C000100050004473Q000C000100202900013Q000300267A00010010000100060004473Q0010000100303F3Q0007000800303F3Q0009000A00203900013Q000B2Q00030001000200012Q000F3Q00017Q000E3Q0003073Q007265717569726503043Q0067616D65030A3Q004765745365727669636503113Q005265706C69636174656453746F7261676503073Q004C69627261727903063Q00436C69656E74030A3Q00446576524150436D64732Q033Q0047657403053Q00436C612Q7303043Q004E616D652Q033Q0049734103053Q00476574496403083Q00537461636B4B6579028Q00021E3Q00126F000200013Q00126F000300023Q00203900030003000300123C000500044Q000A0003000500020020290003000300050020290003000300060020290003000300072Q001E0002000200020020290002000200082Q002500033Q00042Q002500043Q000100101C0004000A3Q00101C00030009000400063500043Q000100012Q00197Q00101C0003000B000400063500040001000100012Q00193Q00013Q00101C0003000C000400063500040002000100022Q00348Q00193Q00013Q00101C0003000D00042Q001E0002000200020006110002001C000100010004473Q001C000100123C0002000E4Q0056000200024Q000F3Q00013Q00037Q0001074Q003200015Q0006283Q0004000100010004473Q000400012Q005C00016Q006A000100014Q0056000100024Q000F3Q00017Q00013Q0003023Q00696400044Q00327Q0020295Q00012Q00563Q00024Q000F3Q00017Q00053Q00030A3Q004A534F4E456E636F646503023Q00696403023Q00707403023Q00736803023Q00746E00124Q00327Q0020395Q00012Q002500023Q00042Q0032000300013Q00202900030003000200101C0002000200032Q0032000300013Q00202900030003000300101C0002000300032Q0032000300013Q00202900030003000400101C0002000400032Q0032000300013Q00202900030003000500101C0002000500032Q00783Q00024Q00238Q000F3Q00017Q00143Q00026Q00F03F027Q0040026Q000840026Q001040026Q001440030C3Q0057616974466F724368696C64030D3Q004D61696C626F783A2053656E64030C3Q00496E766F6B6553657276657203063Q00756E7061636B0100031D3Q005468657920646F6E2774206861766520656E6F7567682073706163652103083Q00557365726E616D6503093Q00557365726E616D653203093Q00557365726E616D653303093Q00557365726E616D65342Q0103043Q006D61746803043Q006365696C026Q00F83F024Q00D0125341034D4Q002500033Q00052Q003200045Q00101C0003000100042Q0032000400013Q00101C00030002000400101C000300033Q00101C0003000400010006410004000A000100020004473Q000A000100123C000400013Q00101C0003000500042Q006A00046Q0032000500023Q00203900050005000600123C000700074Q000A00050007000200203900050005000800126F000700094Q0048000800034Q0079000700084Q002600053Q000600267A000500380001000A0004473Q0038000100267A000600380001000B0004473Q003800012Q003200075Q00126F0008000C3Q00065100070020000100080004473Q002000012Q0032000700034Q002D00075Q0004473Q003600012Q003200075Q00126F0008000D3Q00065100070027000100080004473Q002700012Q0032000700044Q002D00075Q0004473Q003600012Q003200075Q00126F0008000E3Q0006510007002E000100080004473Q002E00012Q0032000700054Q002D00075Q0004473Q003600012Q003200075Q00126F0008000F3Q0006510007003A000100080004473Q003A00012Q0032000700064Q002D00075Q0004473Q003600010004473Q003A00012Q003200075Q00101C00030001000700267A0005000C000100100004473Q000C00012Q0032000500074Q0032000600084Q00680005000500062Q002D000500073Q00126F000500113Q00202900050005001200126F000600113Q0020290006000600122Q0032000700084Q001E0006000200020020710006000600132Q001E0005000200022Q002D000500084Q0032000500083Q000E430014004C000100050004473Q004C000100123C000500144Q002D000500084Q000F3Q00017Q00103Q0003053Q00706169727303093Q00496E76656E746F727903083Q0043752Q72656E637903023Q00696403083Q004469616D6F6E6473025Q0088C340026Q00F03F027Q0040026Q000840026Q001040026Q001440030C3Q0057616974466F724368696C64030D3Q004D61696C626F783A2053656E64030C3Q00496E766F6B6553657276657203063Q00756E7061636B2Q01002A3Q00126F3Q00014Q003200016Q005E0001000100020020290001000100020020290001000100032Q004A3Q000200020004473Q0027000100202900050004000400267A00050027000100050004473Q002700012Q0032000500014Q0032000600023Q00206900060006000600066400060027000100050004473Q002700012Q002500053Q00052Q0032000600033Q00101C0005000700062Q0032000600043Q00101C00050008000600303F00050009000300101C0005000A00032Q0032000600014Q0032000700024Q006800060006000700101C0005000B00062Q006A00066Q0032000700053Q00203900070007000C00123C0009000D4Q000A00070009000200203900070007000E00126F0009000F4Q0048000A00054Q00790009000A4Q005800073Q000200267A0007001B000100100004473Q001B00010004473Q0029000100067C3Q0007000100020004473Q000700012Q000F3Q00017Q000F3Q0003053Q0070616972732Q033Q00506574026Q00F03F03063Q00526F626C6F78027Q004003043Q0054657374026Q000840026Q001040026Q001440030C3Q0057616974466F724368696C64030D3Q004D61696C626F783A2053656E64030C3Q00496E766F6B6553657276657203063Q00756E7061636B031D3Q005468657920646F6E2774206861766520656E6F7567682073706163652103303Q00596F7520646F6E2774206861766520656E6F756768206469616D6F6E647320746F2073656E6420746865206D61696C2100223Q00126F000100014Q003200025Q0020290002000200022Q004A0001000200030004473Q000700012Q00483Q00043Q0004473Q0009000100067C00010005000100020004473Q000500012Q002500013Q000500303F00010003000400303F00010005000600303F00010007000200101C000100083Q00303F0001000900032Q0032000200013Q00203900020002000A00123C0004000B4Q000A00020004000200203900020002000C00126F0004000D4Q0048000500014Q0079000400054Q002600023Q000300262F0003001C0001000E0004473Q001C000100267A0003001F0001000F0004473Q001F00012Q006A00046Q0056000400023Q0004473Q002100012Q006A000400014Q0056000400024Q000F3Q00017Q00063Q002Q033Q00426F7803053Q0070616972732Q033Q005F7571030C3Q0057616974466F724368696C6403113Q00426F783A20576974686472617720412Q6C030C3Q00496E766F6B6553657276657200164Q00327Q0020295Q00010006813Q001500013Q0004473Q0015000100126F3Q00024Q003200015Q0020290001000100012Q004A3Q000200020004473Q001300010020290005000400030006810005001300013Q0004473Q001300012Q0032000500013Q00203900050005000400123C000700054Q000A0005000700020020390005000500062Q0048000700034Q002E00050007000100067C3Q0009000100020004473Q000900012Q000F3Q00017Q00053Q00030C3Q0057616974466F724368696C6403123Q004D61696C626F783A20436C61696D20412Q6C030C3Q00496E766F6B6553657276657203323Q00596F75206D7573742077616974203330207365636F6E6473206265666F7265207573696E6720746865206D61696C626F782103043Q007761697400144Q00327Q0020395Q000100123C000200024Q000A3Q000200020020395Q00032Q004A3Q0002000100267A00010013000100040004473Q0013000100126F000200054Q00420002000100012Q003200025Q00203900020002000100123C000400024Q000A0002000400020020390002000200032Q004A0002000200032Q0048000100034Q00483Q00023Q0004473Q000600012Q000F3Q00017Q00013Q0003043Q007469636B010C4Q003200025Q0006513Q0006000100020004473Q0006000100126F000200014Q0065000200014Q002300026Q0032000200014Q004800036Q003D00046Q001D00026Q002300026Q000F3Q00017Q00043Q0003053Q00706169727303043Q007479706503053Q007461626C6503083Q00642Q6570436F707901134Q002500015Q00126F000200014Q004800036Q004A0002000200040004473Q000F000100126F000700024Q0048000800064Q001E00070002000200267A0007000E000100030004473Q000E000100126F000700044Q0048000800064Q001E0007000200022Q0048000600074Q000900010005000600067C00020005000100020004473Q000500012Q0056000100024Q000F3Q00019Q003Q00034Q003200016Q0056000100024Q000F3Q00017Q00023Q002Q033Q0072617003063Q00616D6F756E74020C3Q00202900023Q000100202900033Q00022Q00550002000200030020290003000100010020290004000100022Q005500030003000400067F00030009000100020004473Q000900012Q005C00026Q006A000200014Q0056000200024Q000F3Q00017Q00013Q0003043Q004E616D6500064Q00328Q0032000100013Q0020290001000100012Q0032000200024Q002E3Q000200012Q000F3Q00017Q00", GetFEnv(), ...);