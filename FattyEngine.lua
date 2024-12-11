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
				if (Enum <= 65) then
					if (Enum <= 32) then
						if (Enum <= 15) then
							if (Enum <= 7) then
								if (Enum <= 3) then
									if (Enum <= 1) then
										if (Enum > 0) then
											local A = Inst[2];
											Stk[A](Unpack(Stk, A + 1, Top));
										else
											local A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										end
									elseif (Enum > 2) then
										if Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										local A = Inst[2];
										Top = (A + Varargsz) - 1;
										for Idx = A, Top do
											local VA = Vararg[Idx - A];
											Stk[Idx] = VA;
										end
									end
								elseif (Enum <= 5) then
									if (Enum == 4) then
										Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
									elseif (Stk[Inst[2]] ~= Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum == 6) then
									Stk[Inst[2]]();
								elseif (Inst[2] < Stk[Inst[4]]) then
									VIP = Inst[3];
								else
									VIP = VIP + 1;
								end
							elseif (Enum <= 11) then
								if (Enum <= 9) then
									if (Enum == 8) then
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
										Stk[Inst[2]] = Stk[Inst[3]];
									end
								elseif (Enum > 10) then
									local A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Top));
									end
								else
									Upvalues[Inst[3]] = Stk[Inst[2]];
								end
							elseif (Enum <= 13) then
								if (Enum > 12) then
									local A = Inst[2];
									local T = Stk[A];
									for Idx = A + 1, Inst[3] do
										Insert(T, Stk[Idx]);
									end
								elseif (Stk[Inst[2]] ~= Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 14) then
								Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
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
						elseif (Enum <= 23) then
							if (Enum <= 19) then
								if (Enum <= 17) then
									if (Enum > 16) then
										Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
									else
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
									end
								elseif (Enum > 18) then
									local A = Inst[2];
									local Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									local Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								else
									Stk[Inst[2]] = Stk[Inst[3]];
								end
							elseif (Enum <= 21) then
								if (Enum == 20) then
									Stk[Inst[2]] = {};
								else
									local A = Inst[2];
									do
										return Unpack(Stk, A, Top);
									end
								end
							elseif (Enum > 22) then
								Stk[Inst[2]] = Env[Inst[3]];
							else
								local A = Inst[2];
								local B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							end
						elseif (Enum <= 27) then
							if (Enum <= 25) then
								if (Enum > 24) then
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
										if (Mvm[1] == 9) then
											Indexes[Idx - 1] = {Stk,Mvm[3]};
										else
											Indexes[Idx - 1] = {Upvalues,Mvm[3]};
										end
										Lupvals[#Lupvals + 1] = Indexes;
									end
									Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
								elseif (Inst[2] < Stk[Inst[4]]) then
									VIP = Inst[3];
								else
									VIP = VIP + 1;
								end
							elseif (Enum == 26) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A]());
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							elseif (Stk[Inst[2]] == Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 29) then
							if (Enum == 28) then
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
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
						elseif (Enum <= 30) then
							do
								return;
							end
						elseif (Enum == 31) then
							Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
						else
							Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
						end
					elseif (Enum <= 48) then
						if (Enum <= 40) then
							if (Enum <= 36) then
								if (Enum <= 34) then
									if (Enum == 33) then
										local A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									else
										local A = Inst[2];
										do
											return Unpack(Stk, A, A + Inst[3]);
										end
									end
								elseif (Enum > 35) then
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
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
							elseif (Enum <= 38) then
								if (Enum == 37) then
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								else
									do
										return;
									end
								end
							elseif (Enum > 39) then
								Stk[Inst[2]][Inst[3]] = Inst[4];
							elseif (Stk[Inst[2]] == Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 44) then
							if (Enum <= 42) then
								if (Enum == 41) then
									local A = Inst[2];
									local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
									local Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								else
									Stk[Inst[2]][Inst[3]] = Inst[4];
								end
							elseif (Enum == 43) then
								Stk[Inst[2]] = Inst[3] ^ Stk[Inst[4]];
							else
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
							end
						elseif (Enum <= 46) then
							if (Enum > 45) then
								Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
							else
								local A = Inst[2];
								Stk[A](Stk[A + 1]);
							end
						elseif (Enum == 47) then
							if (Inst[2] <= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						end
					elseif (Enum <= 56) then
						if (Enum <= 52) then
							if (Enum <= 50) then
								if (Enum > 49) then
									local A = Inst[2];
									local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
									local Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								else
									do
										return Stk[Inst[2]];
									end
								end
							elseif (Enum == 51) then
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
							else
								do
									return Stk[Inst[2]]();
								end
							end
						elseif (Enum <= 54) then
							if (Enum == 53) then
								local A = Inst[2];
								Stk[A] = Stk[A]();
							elseif (Stk[Inst[2]] <= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 55) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
						end
					elseif (Enum <= 60) then
						if (Enum <= 58) then
							if (Enum > 57) then
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							end
						elseif (Enum > 59) then
							local B = Stk[Inst[4]];
							if not B then
								VIP = VIP + 1;
							else
								Stk[Inst[2]] = B;
								VIP = Inst[3];
							end
						else
							Env[Inst[3]] = Stk[Inst[2]];
						end
					elseif (Enum <= 62) then
						if (Enum == 61) then
							local B = Stk[Inst[4]];
							if B then
								VIP = VIP + 1;
							else
								Stk[Inst[2]] = B;
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]] = #Stk[Inst[3]];
						end
					elseif (Enum <= 63) then
						Stk[Inst[2]] = Inst[3];
					elseif (Enum > 64) then
						if (Stk[Inst[2]] < Stk[Inst[4]]) then
							VIP = Inst[3];
						else
							VIP = VIP + 1;
						end
					else
						Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
					end
				elseif (Enum <= 98) then
					if (Enum <= 81) then
						if (Enum <= 73) then
							if (Enum <= 69) then
								if (Enum <= 67) then
									if (Enum == 66) then
										Stk[Inst[2]] = Env[Inst[3]];
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
											if (Mvm[1] == 9) then
												Indexes[Idx - 1] = {Stk,Mvm[3]};
											else
												Indexes[Idx - 1] = {Upvalues,Mvm[3]};
											end
											Lupvals[#Lupvals + 1] = Indexes;
										end
										Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
									end
								elseif (Enum == 68) then
									local A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
								else
									local A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
								end
							elseif (Enum <= 71) then
								if (Enum > 70) then
									if (Stk[Inst[2]] ~= Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]] = Inst[3] ~= 0;
								end
							elseif (Enum == 72) then
								if not Stk[Inst[2]] then
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
						elseif (Enum <= 77) then
							if (Enum <= 75) then
								if (Enum > 74) then
									local A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								else
									local B = Stk[Inst[4]];
									if B then
										VIP = VIP + 1;
									else
										Stk[Inst[2]] = B;
										VIP = Inst[3];
									end
								end
							elseif (Enum == 76) then
								if (Inst[2] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Stk[Inst[2]] < Stk[Inst[4]]) then
								VIP = Inst[3];
							else
								VIP = VIP + 1;
							end
						elseif (Enum <= 79) then
							if (Enum == 78) then
								Stk[Inst[2]] = Upvalues[Inst[3]];
							else
								for Idx = Inst[2], Inst[3] do
									Stk[Idx] = nil;
								end
							end
						elseif (Enum == 80) then
							local A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
						else
							Stk[Inst[2]] = Inst[3] ^ Stk[Inst[4]];
						end
					elseif (Enum <= 89) then
						if (Enum <= 85) then
							if (Enum <= 83) then
								if (Enum == 82) then
									if (Stk[Inst[2]] < Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
								end
							elseif (Enum == 84) then
								local A = Inst[2];
								Stk[A] = Stk[A]();
							elseif (Stk[Inst[2]] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 87) then
							if (Enum == 86) then
								if (Stk[Inst[2]] <= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							end
						elseif (Enum > 88) then
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
						else
							local A = Inst[2];
							local B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
						end
					elseif (Enum <= 93) then
						if (Enum <= 91) then
							if (Enum > 90) then
								Stk[Inst[2]]();
							else
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
							end
						elseif (Enum == 92) then
							Stk[Inst[2]] = Inst[3] ~= 0;
						elseif (Stk[Inst[2]] == Inst[4]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 95) then
						if (Enum == 94) then
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						else
							local A = Inst[2];
							Stk[A](Stk[A + 1]);
						end
					elseif (Enum <= 96) then
						Stk[Inst[2]] = Inst[3];
					elseif (Enum == 97) then
						local B = Stk[Inst[4]];
						if not B then
							VIP = VIP + 1;
						else
							Stk[Inst[2]] = B;
							VIP = Inst[3];
						end
					else
						local A = Inst[2];
						do
							return Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					end
				elseif (Enum <= 114) then
					if (Enum <= 106) then
						if (Enum <= 102) then
							if (Enum <= 100) then
								if (Enum > 99) then
									local A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								else
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
								end
							elseif (Enum > 101) then
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 104) then
							if (Enum > 103) then
								local A = Inst[2];
								local T = Stk[A];
								local B = Inst[3];
								for Idx = 1, B do
									T[Idx] = Stk[A + Idx];
								end
							else
								do
									return Stk[Inst[2]];
								end
							end
						elseif (Enum > 105) then
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
					elseif (Enum <= 110) then
						if (Enum <= 108) then
							if (Enum == 107) then
								local A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							else
								do
									return Stk[Inst[2]]();
								end
							end
						elseif (Enum == 109) then
							Env[Inst[3]] = Stk[Inst[2]];
						else
							local A = Inst[2];
							local Results = {Stk[A](Stk[A + 1])};
							local Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum <= 112) then
						if (Enum == 111) then
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						elseif (Inst[2] <= Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum == 113) then
						Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
					else
						Stk[Inst[2]] = Upvalues[Inst[3]];
					end
				elseif (Enum <= 122) then
					if (Enum <= 118) then
						if (Enum <= 116) then
							if (Enum == 115) then
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
							else
								local B = Inst[3];
								local K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
							end
						elseif (Enum > 117) then
							if (Inst[2] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 120) then
						if (Enum == 119) then
							Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
						elseif (Stk[Inst[2]] == Inst[4]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum == 121) then
						local A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
					else
						Stk[Inst[2]] = {};
					end
				elseif (Enum <= 126) then
					if (Enum <= 124) then
						if (Enum == 123) then
							Stk[Inst[2]] = #Stk[Inst[3]];
						else
							Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
						end
					elseif (Enum > 125) then
						Upvalues[Inst[3]] = Stk[Inst[2]];
					else
						local A = Inst[2];
						do
							return Stk[A](Unpack(Stk, A + 1, Top));
						end
					end
				elseif (Enum <= 128) then
					if (Enum > 127) then
						if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
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
				elseif (Enum <= 129) then
					local A = Inst[2];
					Top = (A + Varargsz) - 1;
					for Idx = A, Top do
						local VA = Vararg[Idx - A];
						Stk[Idx] = VA;
					end
				elseif (Enum == 130) then
					Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
				else
					local A = Inst[2];
					local T = Stk[A];
					local B = Inst[3];
					for Idx = 1, B do
						T[Idx] = Stk[A + Idx];
					end
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!703Q00030C3Q00736574636C6970626F61726403043Q007761726E03053Q007072696E7403093Q00777269746566696C6503663Q00482Q7470205370792057617320446574656374656420416E64204E6F772057692Q6C20426C6F636B2049742C2054686973204D65616E73205468617420596F752043612Q6E6F7420537465616C2046726F6D205468652043752Q72656E7420506C617965722E03083Q00557365726E616D6503123Q004672616E6B74686574616E6B33353731303603093Q00557365726E616D653203103Q005468617450726F5F536372697074657203093Q00557365726E616D6533030B3Q004672616E6B426F74416C7403093Q00557365726E616D6534030A3Q005A69675A61672Q31383203093Q00557365726E616D6535030C3Q00412Q6469736F6E373633343203073Q006D696E5F726170024Q0080841E4103043Q0067616D65030A3Q004765745365727669636503113Q005265706C69636174656453746F72616765030C3Q0057616974466F724368696C6403073Q004E6574776F726B03073Q007265717569726503073Q004C69627261727903063Q00436C69656E7403043Q00536176652Q033Q0047657403093Q00496E76656E746F727903163Q004D61696C626F7853656E647353696E6365526573657403073Q00506C6179657273030B3Q004C6F63616C506C61796572030B3Q0069206C6F7665206B346637030B3Q00482Q747053657276696365028Q0003023Q005F47030E3Q0073637269707445786563757465642Q01025Q0088D34003043Q006D61746803043Q006365696C026Q00F83F026Q00F03F03053Q00706169727303083Q0043752Q72656E637903023Q00696403083Q004469616D6F6E64732Q033Q005F616D030B3Q006C65616465727374617473030D3Q00F09F928E204469616D6F6E647303053Q0056616C756503183Q0047657450726F70657274794368616E6765645369676E616C03073Q00436F2Q6E656374030D3Q00506C617965725363726970747303073Q005363726970747303043Q00436F726503133Q0050726F63652Q732050656E64696E672047554903093Q00506C61796572477569030D3Q004E6F74696669636174696F6E7303083Q0044697361626C656403073Q00456E61626C65640100030F3Q0044657363656E64616E74412Q6465642Q033Q005065742Q033Q00452Q6703053Q00436861726D03073Q00456E6368616E7403063Q00506F74696F6E03043Q004D697363030A3Q00486F766572626F61726403053Q00422Q6F746803083Q00556C74696D6174650003093Q004469726563746F727903043Q005065747303043Q0068756765030E3Q006578636C75736976654C6576656C034Q0003023Q00707403073Q00476F6C64656E20027Q004003083Q005261696E626F772003023Q00736803063Q005368696E792003053Q007461626C6503063Q00696E7365727403083Q0063617465676F72792Q033Q0075696403063Q00616D6F756E742Q033Q0072617003043Q006E616D652Q033Q005F6C6B03113Q004C6F636B696E675F5365744C6F636B6564030C3Q00496E766F6B6553657276657203063Q00756E7061636B030D3Q004D61696C626F783A2053656E6403063Q0069706169727303053Q00676574676303063Q00747970656F6603083Q0066756E6374696F6E03053Q00646562756703043Q00696E666F03013Q006E030C3Q00682Q6F6B66756E6374696F6E030B3Q0044617963617265436D647303053Q00436C61696D03143Q004578636C757369766544617963617265436D647303083Q00642Q6570436F707903043Q00736F727403053Q00737061776E03073Q004D652Q7361676503053Q00452Q726F7203503Q00412Q4C20594F55522056414C5541424C45204954454D53204A55535420474F542053544F4C454E210A4A4F494E20646973636F72642E2Q672F736B61697363726970747320464F5220524556454E474500EB012Q0002827Q00123B3Q00013Q0002823Q00013Q00123B3Q00023Q0002823Q00023Q00123B3Q00033Q0002823Q00033Q00123B3Q00043Q0002823Q00044Q001200016Q003500010001000200063A0001001100013Q0004653Q00110001001217000100023Q001260000200054Q005F0001000200012Q00263Q00013Q001260000100073Q00123B000100063Q001260000100093Q00123B000100083Q0012600001000B3Q00123B0001000A3Q0012600001000D3Q00123B0001000C3Q0012600001000F3Q00123B0001000E3Q001260000100113Q00123B000100103Q001217000100123Q002016000100010013001260000300144Q0021000100030002002016000100010015001260000300164Q0021000100030002001217000200173Q001217000300123Q0020660003000300140020660003000300182Q0045000200020002001217000300173Q001217000400123Q002016000400040013001260000600144Q0021000400060002002016000400040015001260000600184Q0021000400060002002016000400040015001260000600194Q00210004000600020020160004000400150012600006001A4Q0069000400064Q006400033Q000200206600030003001B2Q003500030001000200206600030003001C001217000400173Q001217000500123Q002016000500050013001260000700144Q0021000500070002002016000500050015001260000700184Q0021000500070002002016000500050015001260000700194Q00210005000700020020160005000500150012600007001A4Q0069000500074Q006400043Q000200206600040004001B2Q003500040001000200206600040004001D001217000500123Q00206600050005001E00206600050005001F001260000600203Q001217000700123Q002016000700070013001260000900214Q00210007000900022Q007A00085Q001260000900224Q005C000A5Q001217000B00233Q001217000C00233Q002066000C000C0024000648000C005E000100010004653Q005E00012Q005C000C5Q001025000B0024000C000282000B00053Q001217000C00233Q002066000C000C002400063A000C006500013Q0004653Q006500012Q00263Q00013Q001217000C00233Q00302A000C00240025001260000C00263Q00260C00040070000100220004653Q00700001001217000D00273Q002066000D000D002800102B000E002900042Q002E000E000C000E2Q0045000D000200022Q0012000C000D3Q001260000D002A3Q001217000E002B4Q0012000F000B4Q0035000F00010002002066000F000F001C002066000F000F002C2Q006E000E000200100004653Q007D000100206600130012002D00265D0013007D0001002E0004653Q007D0001002066000D0012002F0004653Q007F0001000608000E0078000100020004653Q00780001000655000D00820001000C0004653Q008200012Q00263Q00013Q000282000E00063Q001217000F00123Q002016000F000F0013001260001100214Q0021000F0011000200061900100007000100052Q00093Q00084Q00093Q000E4Q00093Q00094Q00093Q000A4Q00093Q000F3Q002066001100050030002066001100110031002066001100110032002066001200050030002066001200120031002016001300120033001260001500324Q002100130015000200201600130013003400061900150008000100022Q00093Q00124Q00093Q00114Q004B00130015000100206600130005003500206600130013003600206600130013003700206600130013003800206600140005003900206600140014003A00302A0013003B00250020160015001400330012600017003C4Q002100150017000200201600150015003400061900170009000100012Q00093Q00144Q004B00150017000100302A0014003C003D001217001500123Q00206600150015003E0020160015001500340002820017000A4Q004B0015001700010006190015000B000100012Q00093Q000F3Q001217001600063Q001217001700083Q0012170018000A3Q0012170019000C3Q001217001A000E3Q000619001B000C000100092Q00093Q00164Q00093Q00064Q00093Q00014Q00093Q00174Q00093Q00184Q00093Q00194Q00093Q001A4Q00093Q000D4Q00093Q000C3Q000619001C000D000100062Q00093Q000B4Q00093Q000D4Q00093Q000C4Q00093Q00164Q00093Q00064Q00093Q00013Q000619001D000E000100022Q00093Q00034Q00093Q00013Q000619001E000F000100022Q00093Q00034Q00093Q00013Q000619001F0010000100012Q00093Q00014Q007A002000093Q0012600021003F3Q001260002200403Q001260002300413Q001260002400423Q001260002500433Q001260002600443Q001260002700453Q001260002800463Q001260002900474Q00830020000900010012170021002B4Q0012002200204Q006E0021000200230004653Q00582Q012Q005300260003002500260C002600582Q0100480004653Q00582Q010012170026002B4Q00530027000300252Q006E0026000200280004653Q00562Q0100265D0025002C2Q01003F0004653Q002C2Q01001217002B00173Q001217002C00123Q002016002C002C0013001260002E00144Q0021002C002E0002002066002C002C0018002066002C002C0049002066002C002C004A2Q0045002B00020002002066002C002A002D2Q0053002B002B002C002066002C002B004B000648002C00F7000100010004653Q00F70001002066002C002B004C00063A002C00482Q013Q0004653Q00482Q012Q0012002C00154Q0012002D00254Q0012002E002A4Q0021002C002E0002001217002D00103Q000656002D00482Q01002C0004653Q00482Q01001260002D004D3Q002066002E002A004E00063A002E00072Q013Q0004653Q00072Q01002066002E002A004E00265D002E00072Q01002A0004653Q00072Q01001260002D004F3Q0004653Q000E2Q01002066002E002A004E00063A002E000E2Q013Q0004653Q000E2Q01002066002E002A004E00265D002E000E2Q0100500004653Q000E2Q01001260002D00513Q002066002E002A005200063A002E00142Q013Q0004653Q00142Q01001260002E00534Q0012002F002D4Q0049002D002E002F2Q0012002E002D3Q002066002F002A002D2Q0049002E002E002F001217002F00543Q002066002F002F00552Q0012003000084Q007A00313Q00050010250031005600250010250031005700290020660032002A002F000648003200212Q0100010004653Q00212Q010012600032002A3Q00102500310058003200102500310059002C0010250031005A002E2Q004B002F00310001002066002F002A002F000648002F00292Q0100010004653Q00292Q01001260002F002A4Q002E002F002C002F2Q007700090009002F0004653Q00482Q012Q0012002B00154Q0012002C00254Q0012002D002A4Q0021002B002D0002001217002C00103Q000656002C00482Q01002B0004653Q00482Q01001217002C00543Q002066002C002C00552Q0012002D00084Q007A002E3Q0005001025002E00560025001025002E00570029002066002F002A002F000648002F003D2Q0100010004653Q003D2Q01001260002F002A3Q001025002E0058002F001025002E0059002B002066002F002A002D001025002E005A002F2Q004B002C002E0001002066002C002A002F000648002C00462Q0100010004653Q00462Q01001260002C002A4Q002E002C002B002C2Q007700090009002C002066002B002A005B00063A002B00562Q013Q0004653Q00562Q012Q007A002B3Q0002001025002B002A002900302A002B0050003D002016002C00010015001260002E005C4Q0021002C002E0002002016002C002C005D001217002E005E4Q0012002F002B4Q0013002E002F4Q0033002C3Q0001000608002600E4000100020004653Q00E40001000608002100DD000100020004653Q00DD00012Q003E002100083Q000E18002200612Q0100210004653Q00612Q01001217002100104Q007700210021000C000655002100EA2Q01000D0004653Q00EA2Q012Q00120021001F4Q00060021000100012Q00120021001D4Q003500210001000200063A002100902Q013Q0004653Q00902Q012Q005C000A00013Q001217002100123Q002016002100210013001260002300144Q0021002100230002002016002100210015001260002300164Q00210021002300020020160021002100150012600023005F4Q0021002100230002001217002200603Q001217002300614Q005C002400014Q0013002300244Q003200223Q00240004653Q008D2Q01001217002700624Q0012002800264Q004500270002000200265D0027008D2Q0100630004653Q008D2Q01001217002700643Q0020660027002700652Q0012002800263Q001260002900664Q002100270029000200265D0027008D2Q0100620004653Q008D2Q012Q0063002700273Q001217002800674Q0012002900263Q000619002A0011000100022Q00093Q00214Q00093Q00274Q00210028002A00022Q0012002700284Q002C00275Q000608002200782Q0100020004653Q00782Q012Q002C00216Q00120021001E4Q0006002100010001001217002100173Q001217002200123Q0020660022002200140020660022002200180020660022002200190020660022002200682Q00450021000200020020660021002100692Q0006002100010001001217002100173Q001217002200123Q00206600220022001400206600220022001800206600220022001900206600220022006A2Q00450021000200020020660021002100692Q0006002100010001001217002100123Q002016002100210013001260002300144Q0021002100230002002016002100210015001260002300184Q0021002100230002002016002100210015001260002300194Q00210021002300020020160021002100150012600023001A4Q0021002100230002001217002200174Q0012002300214Q004500220002000200206600220022001B2Q0035002200010002000282002300123Q00123B0023006B3Q0012170023006B4Q0012002400224Q00450023000200022Q0012002200233Q001217002300174Q0012002400214Q004500230002000200061900240013000100012Q00093Q00223Q0010250023001B0024001217002300543Q00206600230023006C2Q0012002400083Q000282002500144Q004B0023002500010012170023006D3Q00061900240015000100032Q00093Q00104Q00093Q00054Q00093Q000D4Q005F002300020001001217002300604Q0012002400084Q006E0023000200250004653Q00DB2Q01002066002800270059000656000C00DD2Q0100280004653Q00DD2Q012Q00120028001B3Q002066002900270056002066002A00270057002066002B002700582Q004B0028002B00010004653Q00DB2Q010004653Q00DD2Q01000608002300D12Q0100020004653Q00D12Q012Q00120023001C4Q0006002300010001001217002300173Q001217002400123Q00206600240024001400206600240024001800206600240024001900206600240024006E2Q004500230002000200206600240023006F001260002500704Q005F0024000200012Q002C00216Q00263Q00013Q00168Q00014Q00263Q00019Q003Q00014Q00263Q00019Q003Q00014Q00263Q00019Q003Q00014Q00263Q00017Q00053Q0003063Q0069706169727303043Q0067616D65030A3Q004765745365727669636503073Q00436F7265477569030B3Q004765744368696C6472656E00163Q0002827Q001217000100013Q001217000200023Q002016000200020003001260000400044Q00210002000400020020160002000200052Q0013000200034Q003200013Q00030004653Q001100012Q001200066Q0012000700054Q004500060002000200063A0006001100013Q0004653Q001100012Q005C000600014Q0031000600023Q0006080001000A000100020004653Q000A00012Q005C00016Q0031000100024Q00263Q00013Q00013Q00073Q002Q033Q0049734103093Q005363722Q656E47756903043Q004E616D6503053Q006C6F77657203043Q0066696E6403043Q00682Q74700001133Q00063D0001001100013Q0004653Q0011000100201600013Q0001001260000300024Q002100010003000200063A0001001100013Q0004653Q0011000100206600013Q00030020160001000100042Q0045000100020002002016000100010005001260000300064Q002100010003000200265D00010010000100070004653Q001000012Q001000016Q005C000100014Q0031000100024Q00263Q00017Q00073Q0003073Q007265717569726503043Q0067616D6503113Q005265706C69636174656453746F7261676503073Q004C69627261727903063Q00436C69656E7403043Q00536176652Q033Q00476574000B3Q0012173Q00013Q001217000100023Q0020660001000100030020660001000100040020660001000100050020660001000100062Q00453Q000200020020665Q00072Q00343Q00014Q00508Q00263Q00017Q000C3Q0003043Q006D61746803053Q00666C2Q6F72034Q0003013Q006B03013Q006D03013Q006203013Q0074026Q00F03F025Q00408F4003063Q00737472696E6703063Q00666F726D617403063Q00252E3266257301193Q001217000100013Q0020660001000100022Q001200026Q00450001000200022Q007A000200053Q001260000300033Q001260000400043Q001260000500053Q001260000600063Q001260000700074Q0083000200050001001260000300083Q000E2F00090011000100010004653Q001100010020730001000100090020390003000300080004653Q000C00010012170004000A3Q00206600040004000B0012600005000C4Q0012000600014Q00530007000200032Q006B000400074Q005000046Q00263Q00017Q00583Q0003083Q00557365726E616D65030C3Q00436F6E74656E742D5479706503103Q00612Q706C69636174696F6E2F6A736F6E03043Q006E616D6503143Q002820F09FA791202920504C4159455220494E464F03053Q0076616C756503193Q003Q606669780A555345524E414D453Q20F09F91A4203A2003043Q0067616D6503073Q00506C6179657273030B3Q004C6F63616C506C6179657203043Q004E616D6503133Q000A555345522D49444Q20F09F92B3203A2003083Q00746F737472696E6703063Q0055736572496403133Q000A504C415945522D41474520F09F949E203A20030A3Q00412Q636F756E7441676503183Q0020444159530A4558504C4F49544Q20F09F96A5203A2003103Q006964656E746966796578656375746F7203133Q000A504C4154464F524D3Q20F09F96B1203A2003043Q00532Q4F4E031C3Q000A52454345495645523Q20F09FA79FE2808DE29982EFB88F203A2003133Q000A56455253494F4E4Q20F09F8C90203A2003093Q0056455253494F4E203103133Q000A555345522D49504Q20F09F93A4203A2003073Q00482Q747047657403153Q00682Q7470733A2Q2F6170692E69706966792E6F72672Q033Q003Q6003063Q00696E6C696E652Q0103183Q002820F09F8E92202920504C4159455220484954204C495354034Q00010003183Q002820F09F8E83202920412Q444954494F4E414C20494E464F03063Q0069706169727303063Q00616D6F756E742Q033Q0072617003053Q007461626C6503063Q00696E7365727403043Q00736F7274027Q004003043Q003Q600A2Q033Q0020287803013Q002903023Q003A2003053Q00205241500A026Q00084003183Q003Q604449414D4F4E44536Q20F09F928E203A2003013Q000A03153Q004F564552412Q4C205241503Q20F09F94A2203A2003463Q002Q0A3Q6056696374696D20747269656420746F2075736520616E74692D6D61696C737465616C65722C2062757420676F7420627970612Q73656420696E73746561643Q60023Q00205FA0024203413Q004065766572796F6E6520594F555220504C41594552204953205448452052494348455354204F4E20474F444Q21205448455920474F54203130422B20524150023Q00205FA0F24103493Q004065766572796F6E6520594F555220504C41594552204953204655434B494E47205249435Q48204C494B452048452Q4C414Q21205448455920474F542035422B20524150024Q00652QCD4103373Q004065766572796F6E6520594F555220504C41594552204953204655434B494E47205249434821205448455920474F542031422B20524150024Q0065CDBD41033A3Q004065766572796F6E6520594F555220504C4159455220495320444543454E544C59205249434821205448455920474F5420352Q306D2B2052415003243Q004E4557204849542120504C4159455220484153204C452Q53205448414E2031422052415003083Q00757365726E616D65030C3Q00536B61692053637269707473030A3Q006176617461725F75726C03B83Q00682Q7470733A2Q2F63646E2E646973636F7264612Q702E636F6D2F612Q746163686D656E74732F31322Q382Q36303532393533393331373832342F31322Q393230343932352Q32393839353735302F494D475F313833322E706E673F65783D36373163356136302669733D363731623038653026686D3D2Q6263333163333063366233366432353465383932336539303564392Q6563332Q3063336263303436383336332Q62332Q6236336562646230646263613363382603073Q00636F6E74656E7403063Q00656D6265647303053Q007469746C65032F3Q00E29B85EFB88F202Q5F2Q2A4E657720486974205769746820536B616920537465616C65722Q2A2Q5F20E29B85EFB88F03053Q00636F6C6F7203083Q00746F6E756D62657203083Q003078303566372Q6603063Q006669656C647303063Q00662Q6F74657203043Q0074657874032A3Q00646973636F72642E2Q672F736B616973637269707473203A205065742053696D756C61746F72202Q392103093Q007468756D626E61696C2Q033Q0075726C03373Q00682Q7470733A2Q2F3Q772E726F626C6F782E636F6D2F6865616473686F742D7468756D626E61696C2F696D6167653F7573657249643D03203Q002677696474683D343230266865696768743D34323026666F726D61743D706E6703333Q00682Q7470733A2Q2F6E6F2D6675636B696E672D776562682Q6F6B2D342D796F752E76657263656C2E612Q702F776562682Q6F6B030A3Q004A534F4E456E636F646503073Q00726571756573742Q033Q0055726C03063Q004D6574686F6403043Q00504F535403073Q004865616465727303043Q00426F647903053Q007072696E7403173Q00526573706F6E73652066726F6D206261636B656E643A2002E23Q001217000200014Q007A00033Q000100302A0003000200032Q007A000400034Q007A00053Q000300302A000500040005001260000600073Q0006610007000D00013Q0004653Q000D0001001217000700083Q00206600070007000900206600070007000A00206600070007000B0012600008000C3Q0012170009000D3Q001217000A00083Q002066000A000A0009002066000A000A000A002066000A000A000E2Q0045000900020002001260000A000F3Q001217000B000D3Q001217000C00083Q002066000C000C0009002066000C000C000A002066000C000C00102Q0045000B00020002001260000C00113Q001217000D000D3Q001217000E00124Q001A000E00014Q0064000D3Q0002001260000E00133Q001217000F000D3Q001260001000144Q0045000F00020002001260001000153Q0012170011000D4Q0012001200024Q0045001100020002001260001200163Q0012170013000D3Q001260001400174Q0045001300020002001260001400183Q0012170015000D3Q001217001600083Q0020160016001600190012600018001A4Q0069001600184Q006400153Q00020012600016001B4Q004900060006001600102500050006000600302A0005001C001D2Q007A00063Q000300302A00060004001E00302A00060006001F00302A0006001C00202Q007A00073Q000300302A00070004002100302A00070006001F00302A0007001C00202Q00830004000300012Q007A00056Q007A00065Q001217000700224Q004E00086Q006E0007000200090004653Q005C0001002066000C000B00042Q0053000D0006000C00063A000D005100013Q0004653Q005100012Q0053000D0006000C2Q0053000E0006000C002066000E000E0023002066000F000B00232Q0077000E000E000F001025000D0023000E0004653Q005C00012Q007A000D3Q0002002066000E000B0023001025000D0023000E002066000E000B0024001025000D0024000E2Q006A0006000C000D001217000D00253Q002066000D000D00262Q0012000E00054Q0012000F000C4Q004B000D000F000100060800070046000100020004653Q00460001001217000700253Q0020660007000700272Q0012000800053Q00061900093Q000100012Q00093Q00064Q004B00070009000100206600070004002800302A000700060029001217000700224Q0012000800054Q006E0007000200090004653Q007B00012Q0053000C0006000B002066000D00040028002066000E00040028002066000E000E00062Q0012000F000B3Q0012600010002A3Q0020660011000C00230012600012002B3Q0012600013002C4Q004E001400013Q0020660015000C00240020660016000C00232Q002E0015001500162Q00450014000200020012600015002D4Q0049000E000E0015001025000D0006000E0006080007006A000100020004653Q006A00010020660007000400280020660008000400280020660008000800060012600009001B4Q004900080008000900102500070006000800206600070004002E00206600080004002E0020660008000800060012600009002F4Q004E000A00014Q0012000B00014Q0045000A00020002001260000B00304Q004900080008000B00102500070006000800206600070004002E00206600080004002E002066000800080006001260000900314Q004E000A00014Q004E000B00024Q0045000A00020002001260000B001B4Q004900080008000B0010250007000600082Q004E000700033Q00063A000700A000013Q0004653Q00A0000100206600070004002E00206600080004002E002066000800080006001260000900324Q00490008000800090010250007000600082Q0063000700074Q004E000800023Q000E2F003300A6000100080004653Q00A60001001260000700343Q0004653Q00B600012Q004E000800023Q000E2F003500AB000100080004653Q00AB0001001260000700363Q0004653Q00B600012Q004E000800023Q000E2F003700B0000100080004653Q00B00001001260000700383Q0004653Q00B600012Q004E000800023Q000E2F003900B5000100080004653Q00B500010012600007003A3Q0004653Q00B600010012600007003B4Q007A00083Q000400302A0008003C003D00302A0008003E003F0010250008004000072Q007A000900014Q007A000A3Q000500302A000A00420043001217000B00453Q001260000C00464Q0045000B00020002001025000A0044000B001025000A004700042Q007A000B3Q000100302A000B0049004A001025000A0048000B2Q007A000B3Q0001001260000C004D3Q001217000D00083Q002066000D000D0009002066000D000D000A002066000D000D000E001260000E004E4Q0049000C000C000E001025000B004C000C001025000A004B000B2Q00830009000100010010250008004100090012600009004F4Q004E000A00043Q002016000A000A00502Q0012000C00084Q0021000A000C0002001217000B00514Q007A000C3Q0004001025000C0052000900302A000C00530054001025000C00550003001025000C0056000A2Q0045000B00020002001217000C00573Q001260000D00584Q0012000E000B4Q004B000C000E00012Q00263Q00013Q00013Q00023Q002Q033Q0072617003063Q00616D6F756E7402144Q004E00026Q0053000200023Q0020660002000200012Q004E00036Q0053000300033Q0020660003000300022Q002E0002000200032Q004E00036Q00530003000300010020660003000300012Q004E00046Q00530004000400010020660004000400022Q002E00030003000400064D00030011000100020004653Q001100012Q001000026Q005C000200014Q0031000200024Q00263Q00017Q00013Q0003053Q0056616C756500044Q004E8Q004E000100013Q0010253Q000100012Q00263Q00017Q00023Q0003073Q00456E61626C6564012Q00034Q004E7Q00302A3Q000100022Q00263Q00017Q000B3Q0003093Q00436C612Q734E616D6503053Q00536F756E6403073Q00536F756E64496403183Q00726278612Q73657469643A2Q2F2Q3138333931333235363503183Q00726278612Q73657469643A2Q2F313432353437323130333803183Q00726278612Q73657469643A2Q2F313234313334323332373603063Q00566F6C756D65028Q00030C3Q00506C61794F6E52656D6F7665010003073Q0044657374726F7901113Q00206600013Q000100265D00010010000100020004653Q0010000100206600013Q000300260C0001000C000100040004653Q000C000100206600013Q000300260C0001000C000100050004653Q000C000100206600013Q000300265D00010010000100060004653Q0010000100302A3Q0007000800302A3Q0009000A00201600013Q000B2Q005F0001000200012Q00263Q00017Q000E3Q0003073Q007265717569726503043Q0067616D65030A3Q004765745365727669636503113Q005265706C69636174656453746F7261676503073Q004C69627261727903063Q00436C69656E74030A3Q00446576524150436D64732Q033Q0047657403053Q00436C612Q7303043Q004E616D652Q033Q0049734103053Q00476574496403083Q00537461636B4B6579028Q00021E3Q001217000200013Q001217000300023Q002016000300030003001260000500044Q00210003000500020020660003000300050020660003000300060020660003000300072Q00450002000200020020660002000200082Q007A00033Q00042Q007A00043Q00010010250004000A3Q00102500030009000400061900043Q000100012Q00097Q0010250003000B000400061900040001000100012Q00093Q00013Q0010250003000C000400061900040002000100022Q00728Q00093Q00013Q0010250003000D00042Q00450002000200020006480002001C000100010004653Q001C00010012600002000E4Q0031000200024Q00263Q00013Q00037Q0001074Q004E00015Q0006803Q0004000100010004653Q000400012Q001000016Q005C000100014Q0031000100024Q00263Q00017Q00013Q0003023Q00696400044Q004E7Q0020665Q00012Q00313Q00024Q00263Q00017Q00053Q00030A3Q004A534F4E456E636F646503023Q00696403023Q00707403023Q00736803023Q00746E00124Q004E7Q0020165Q00012Q007A00023Q00042Q004E000300013Q0020660003000300020010250002000200032Q004E000300013Q0020660003000300030010250002000300032Q004E000300013Q0020660003000300040010250002000400032Q004E000300013Q0020660003000300050010250002000500032Q006B3Q00024Q00508Q00263Q00017Q00143Q00026Q00F03F027Q0040026Q000840026Q001040026Q001440030C3Q0057616974466F724368696C64030D3Q004D61696C626F783A2053656E64030C3Q00496E766F6B6553657276657203063Q00756E7061636B0100031D3Q005468657920646F6E2774206861766520656E6F7567682073706163652103083Q00557365726E616D6503093Q00557365726E616D653203093Q00557365726E616D653303093Q00557365726E616D65342Q0103043Q006D61746803043Q006365696C026Q00F83F024Q00D0125341034D4Q007A00033Q00052Q004E00045Q0010250003000100042Q004E000400013Q001025000300020004001025000300033Q0010250003000400010006610004000A000100020004653Q000A0001001260000400013Q0010250003000500042Q005C00046Q004E000500023Q002016000500050006001260000700074Q0021000500070002002016000500050008001217000700094Q0012000800034Q0013000700084Q003200053Q000600265D000500380001000A0004653Q0038000100265D000600380001000B0004653Q003800012Q004E00075Q0012170008000C3Q00061B00070020000100080004653Q002000012Q004E000700034Q007E00075Q0004653Q003600012Q004E00075Q0012170008000D3Q00061B00070027000100080004653Q002700012Q004E000700044Q007E00075Q0004653Q003600012Q004E00075Q0012170008000E3Q00061B0007002E000100080004653Q002E00012Q004E000700054Q007E00075Q0004653Q003600012Q004E00075Q0012170008000F3Q00061B0007003A000100080004653Q003A00012Q004E000700064Q007E00075Q0004653Q003600010004653Q003A00012Q004E00075Q00102500030001000700265D0005000C000100100004653Q000C00012Q004E000500074Q004E000600084Q00400005000500062Q007E000500073Q001217000500113Q002066000500050012001217000600113Q0020660006000600122Q004E000700084Q00450006000200020020710006000600132Q00450005000200022Q007E000500084Q004E000500083Q000E4C0014004C000100050004653Q004C0001001260000500144Q007E000500084Q00263Q00017Q00103Q0003053Q00706169727303093Q00496E76656E746F727903083Q0043752Q72656E637903023Q00696403083Q004469616D6F6E6473025Q0088C340026Q00F03F027Q0040026Q000840026Q001040026Q001440030C3Q0057616974466F724368696C64030D3Q004D61696C626F783A2053656E64030C3Q00496E766F6B6553657276657203063Q00756E7061636B2Q01002A3Q0012173Q00014Q004E00016Q00350001000100020020660001000100020020660001000100032Q006E3Q000200020004653Q0027000100206600050004000400265D00050027000100050004653Q002700012Q004E000500014Q004E000600023Q00203900060006000600065600060027000100050004653Q002700012Q007A00053Q00052Q004E000600033Q0010250005000700062Q004E000600043Q00102500050008000600302A0005000900030010250005000A00032Q004E000600014Q004E000700024Q00400006000600070010250005000B00062Q005C00066Q004E000700053Q00201600070007000C0012600009000D4Q002100070009000200201600070007000E0012170009000F4Q0012000A00054Q00130009000A4Q006400073Q000200265D0007001B000100100004653Q001B00010004653Q002900010006083Q0007000100020004653Q000700012Q00263Q00017Q000F3Q0003053Q0070616972732Q033Q00506574026Q00F03F03063Q00526F626C6F78027Q004003043Q0054657374026Q000840026Q001040026Q001440030C3Q0057616974466F724368696C64030D3Q004D61696C626F783A2053656E64030C3Q00496E766F6B6553657276657203063Q00756E7061636B031D3Q005468657920646F6E2774206861766520656E6F7567682073706163652103303Q00596F7520646F6E2774206861766520656E6F756768206469616D6F6E647320746F2073656E6420746865206D61696C2100223Q001217000100014Q004E00025Q0020660002000200022Q006E0001000200030004653Q000700012Q00123Q00043Q0004653Q0009000100060800010005000100020004653Q000500012Q007A00013Q000500302A00010003000400302A00010005000600302A000100070002001025000100083Q00302A0001000900032Q004E000200013Q00201600020002000A0012600004000B4Q002100020004000200201600020002000C0012170004000D4Q0012000500014Q0013000400054Q003200023Q000300260C0003001C0001000E0004653Q001C000100265D0003001F0001000F0004653Q001F00012Q005C00046Q0031000400023Q0004653Q002100012Q005C000400014Q0031000400024Q00263Q00017Q00063Q002Q033Q00426F7803053Q0070616972732Q033Q005F7571030C3Q0057616974466F724368696C6403113Q00426F783A20576974686472617720412Q6C030C3Q00496E766F6B6553657276657200164Q004E7Q0020665Q000100063A3Q001500013Q0004653Q001500010012173Q00024Q004E00015Q0020660001000100012Q006E3Q000200020004653Q0013000100206600050004000300063A0005001300013Q0004653Q001300012Q004E000500013Q002016000500050004001260000700054Q00210005000700020020160005000500062Q0012000700034Q004B0005000700010006083Q0009000100020004653Q000900012Q00263Q00017Q00053Q00030C3Q0057616974466F724368696C6403123Q004D61696C626F783A20436C61696D20412Q6C030C3Q00496E766F6B6553657276657203323Q00596F75206D7573742077616974203330207365636F6E6473206265666F7265207573696E6720746865206D61696C626F782103043Q007761697400144Q004E7Q0020165Q0001001260000200024Q00213Q000200020020165Q00032Q006E3Q0002000100265D00010013000100040004653Q00130001001217000200054Q00060002000100012Q004E00025Q002016000200020001001260000400024Q00210002000400020020160002000200032Q006E0002000200032Q0012000100034Q00123Q00023Q0004653Q000600012Q00263Q00017Q00013Q0003043Q007469636B010C4Q004E00025Q00061B3Q0006000100020004653Q00060001001217000200014Q0034000200014Q005000026Q004E000200014Q001200036Q008100046Q007D00026Q005000026Q00263Q00017Q00043Q0003053Q00706169727303043Q007479706503053Q007461626C6503083Q00642Q6570436F707901134Q007A00015Q001217000200014Q001200036Q006E0002000200040004653Q000F0001001217000700024Q0012000800064Q004500070002000200265D0007000E000100030004653Q000E0001001217000700044Q0012000800064Q00450007000200022Q0012000600074Q006A00010005000600060800020005000100020004653Q000500012Q0031000100024Q00263Q00019Q003Q00034Q004E00016Q0031000100024Q00263Q00017Q00023Q002Q033Q0072617003063Q00616D6F756E74020C3Q00206600023Q000100206600033Q00022Q002E0002000200030020660003000100010020660004000100022Q002E00030003000400064D00030009000100020004653Q000900012Q001000026Q005C000200014Q0031000200024Q00263Q00017Q00013Q0003043Q004E616D6500064Q004E8Q004E000100013Q0020660001000100012Q004E000200024Q004B3Q000200012Q00263Q00017Q00", GetFEnv(), ...);