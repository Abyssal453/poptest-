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
										if (Enum == 0) then
											Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
										elseif (Stk[Inst[2]] < Stk[Inst[4]]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									elseif (Enum == 2) then
										local A = Inst[2];
										Stk[A](Stk[A + 1]);
									else
										Stk[Inst[2]] = Inst[3];
									end
								elseif (Enum <= 5) then
									if (Enum == 4) then
										Stk[Inst[2]]();
									else
										Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
									end
								elseif (Enum == 6) then
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
									local Results = {Stk[A](Stk[A + 1])};
									local Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								end
							elseif (Enum <= 11) then
								if (Enum <= 9) then
									if (Enum > 8) then
										local A = Inst[2];
										local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
										Top = (Limit + A) - 1;
										local Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
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
								elseif (Enum == 10) then
									VIP = Inst[3];
								else
									Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
								end
							elseif (Enum <= 13) then
								if (Enum == 12) then
									Stk[Inst[2]][Inst[3]] = Inst[4];
								elseif Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum > 14) then
								Stk[Inst[2]] = #Stk[Inst[3]];
							else
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
							end
						elseif (Enum <= 23) then
							if (Enum <= 19) then
								if (Enum <= 17) then
									if (Enum > 16) then
										if (Stk[Inst[2]] ~= Inst[4]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										Stk[Inst[2]] = Stk[Inst[3]];
									end
								elseif (Enum == 18) then
									local A = Inst[2];
									Top = (A + Varargsz) - 1;
									for Idx = A, Top do
										local VA = Vararg[Idx - A];
										Stk[Idx] = VA;
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
							elseif (Enum <= 21) then
								if (Enum > 20) then
									local A = Inst[2];
									do
										return Unpack(Stk, A, Top);
									end
								elseif (Stk[Inst[2]] < Stk[Inst[4]]) then
									VIP = Inst[3];
								else
									VIP = VIP + 1;
								end
							elseif (Enum == 22) then
								do
									return Stk[Inst[2]]();
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
							end
						elseif (Enum <= 27) then
							if (Enum <= 25) then
								if (Enum > 24) then
									local A = Inst[2];
									local T = Stk[A];
									for Idx = A + 1, Inst[3] do
										Insert(T, Stk[Idx]);
									end
								else
									Env[Inst[3]] = Stk[Inst[2]];
								end
							elseif (Enum == 26) then
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							elseif (Stk[Inst[2]] ~= Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 29) then
							if (Enum == 28) then
								local A = Inst[2];
								local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							end
						elseif (Enum <= 30) then
							Stk[Inst[2]] = Inst[3] ^ Stk[Inst[4]];
						elseif (Enum > 31) then
							VIP = Inst[3];
						else
							local A = Inst[2];
							local B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
						end
					elseif (Enum <= 48) then
						if (Enum <= 40) then
							if (Enum <= 36) then
								if (Enum <= 34) then
									if (Enum == 33) then
										do
											return Stk[Inst[2]];
										end
									else
										local B = Stk[Inst[4]];
										if not B then
											VIP = VIP + 1;
										else
											Stk[Inst[2]] = B;
											VIP = Inst[3];
										end
									end
								elseif (Enum > 35) then
									if (Stk[Inst[2]] <= Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									do
										return Stk[Inst[2]]();
									end
								end
							elseif (Enum <= 38) then
								if (Enum == 37) then
									local A = Inst[2];
									Stk[A](Stk[A + 1]);
								else
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
								end
							elseif (Enum == 39) then
								if (Inst[2] < Stk[Inst[4]]) then
									VIP = Inst[3];
								else
									VIP = VIP + 1;
								end
							else
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							end
						elseif (Enum <= 44) then
							if (Enum <= 42) then
								if (Enum == 41) then
									local A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
								elseif (Inst[2] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 43) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum <= 46) then
							if (Enum == 45) then
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
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
						elseif (Enum == 47) then
							if (Stk[Inst[2]] <= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Top));
							end
						end
					elseif (Enum <= 56) then
						if (Enum <= 52) then
							if (Enum <= 50) then
								if (Enum > 49) then
									local A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								else
									Stk[Inst[2]] = Inst[3] ^ Stk[Inst[4]];
								end
							elseif (Enum > 51) then
								Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
							else
								Stk[Inst[2]] = Inst[3] ~= 0;
							end
						elseif (Enum <= 54) then
							if (Enum > 53) then
								local A = Inst[2];
								do
									return Unpack(Stk, A, A + Inst[3]);
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
							end
						elseif (Enum > 55) then
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						else
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					elseif (Enum <= 60) then
						if (Enum <= 58) then
							if (Enum == 57) then
								if (Stk[Inst[2]] == Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							end
						elseif (Enum > 59) then
							do
								return;
							end
						else
							local A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
						end
					elseif (Enum <= 62) then
						if (Enum == 61) then
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
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
					elseif (Enum <= 63) then
						Stk[Inst[2]] = #Stk[Inst[3]];
					elseif (Enum == 64) then
						Stk[Inst[2]] = Stk[Inst[3]];
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
							if (Mvm[1] == 64) then
								Indexes[Idx - 1] = {Stk,Mvm[3]};
							else
								Indexes[Idx - 1] = {Upvalues,Mvm[3]};
							end
							Lupvals[#Lupvals + 1] = Indexes;
						end
						Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
					end
				elseif (Enum <= 98) then
					if (Enum <= 81) then
						if (Enum <= 73) then
							if (Enum <= 69) then
								if (Enum <= 67) then
									if (Enum == 66) then
										Stk[Inst[2]] = {};
									else
										local B = Inst[3];
										local K = Stk[B];
										for Idx = B + 1, Inst[4] do
											K = K .. Stk[Idx];
										end
										Stk[Inst[2]] = K;
									end
								elseif (Enum == 68) then
									Stk[Inst[2]] = Env[Inst[3]];
								else
									do
										return;
									end
								end
							elseif (Enum <= 71) then
								if (Enum == 70) then
									do
										return Stk[Inst[2]];
									end
								else
									Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
								end
							elseif (Enum > 72) then
								Stk[Inst[2]] = Upvalues[Inst[3]];
							else
								local A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
							end
						elseif (Enum <= 77) then
							if (Enum <= 75) then
								if (Enum > 74) then
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								else
									Stk[Inst[2]] = Inst[3];
								end
							elseif (Enum == 76) then
								local B = Stk[Inst[4]];
								if B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							else
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
							end
						elseif (Enum <= 79) then
							if (Enum == 78) then
								if (Inst[2] <= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
							end
						elseif (Enum == 80) then
							for Idx = Inst[2], Inst[3] do
								Stk[Idx] = nil;
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
						end
					elseif (Enum <= 89) then
						if (Enum <= 85) then
							if (Enum <= 83) then
								if (Enum > 82) then
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
								else
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
								end
							elseif (Enum == 84) then
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							else
								local A = Inst[2];
								local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum <= 87) then
							if (Enum == 86) then
								Upvalues[Inst[3]] = Stk[Inst[2]];
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
						elseif (Enum > 88) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
						elseif (Inst[2] <= Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 93) then
						if (Enum <= 91) then
							if (Enum == 90) then
								if (Stk[Inst[2]] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
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
									if (Mvm[1] == 64) then
										Indexes[Idx - 1] = {Stk,Mvm[3]};
									else
										Indexes[Idx - 1] = {Upvalues,Mvm[3]};
									end
									Lupvals[#Lupvals + 1] = Indexes;
								end
								Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
							end
						elseif (Enum > 92) then
							Stk[Inst[2]][Inst[3]] = Inst[4];
						else
							Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
						end
					elseif (Enum <= 95) then
						if (Enum == 94) then
							local A = Inst[2];
							Stk[A] = Stk[A]();
						elseif (Inst[2] < Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 96) then
						if (Inst[2] < Stk[Inst[4]]) then
							VIP = Inst[3];
						else
							VIP = VIP + 1;
						end
					elseif (Enum == 97) then
						Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
					elseif (Stk[Inst[2]] == Inst[4]) then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 114) then
					if (Enum <= 106) then
						if (Enum <= 102) then
							if (Enum <= 100) then
								if (Enum > 99) then
									local A = Inst[2];
									local B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
								else
									local A = Inst[2];
									local T = Stk[A];
									local B = Inst[3];
									for Idx = 1, B do
										T[Idx] = Stk[A + Idx];
									end
								end
							elseif (Enum == 101) then
								Env[Inst[3]] = Stk[Inst[2]];
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
						elseif (Enum <= 104) then
							if (Enum == 103) then
								if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Inst[3] ~= 0;
							end
						elseif (Enum > 105) then
							local A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Top));
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
					elseif (Enum <= 110) then
						if (Enum <= 108) then
							if (Enum == 107) then
								if (Stk[Inst[2]] < Stk[Inst[4]]) then
									VIP = Inst[3];
								else
									VIP = VIP + 1;
								end
							elseif (Stk[Inst[2]] ~= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 109) then
							if (Stk[Inst[2]] == Stk[Inst[4]]) then
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
					elseif (Enum <= 112) then
						if (Enum > 111) then
							Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
						elseif (Stk[Inst[2]] == Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum == 113) then
						local B = Inst[3];
						local K = Stk[B];
						for Idx = B + 1, Inst[4] do
							K = K .. Stk[Idx];
						end
						Stk[Inst[2]] = K;
					else
						Upvalues[Inst[3]] = Stk[Inst[2]];
					end
				elseif (Enum <= 122) then
					if (Enum <= 118) then
						if (Enum <= 116) then
							if (Enum > 115) then
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							else
								local A = Inst[2];
								Top = (A + Varargsz) - 1;
								for Idx = A, Top do
									local VA = Vararg[Idx - A];
									Stk[Idx] = VA;
								end
							end
						elseif (Enum > 117) then
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
						else
							local A = Inst[2];
							Stk[A] = Stk[A]();
						end
					elseif (Enum <= 120) then
						if (Enum == 119) then
							Stk[Inst[2]] = {};
						elseif Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum > 121) then
						Stk[Inst[2]] = Env[Inst[3]];
					else
						Stk[Inst[2]]();
					end
				elseif (Enum <= 126) then
					if (Enum <= 124) then
						if (Enum == 123) then
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Top));
						elseif not Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum > 125) then
						local A = Inst[2];
						do
							return Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					else
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
					end
				elseif (Enum <= 128) then
					if (Enum > 127) then
						if not Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
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
				elseif (Enum <= 129) then
					local A = Inst[2];
					local T = Stk[A];
					local B = Inst[3];
					for Idx = 1, B do
						T[Idx] = Stk[A + Idx];
					end
				elseif (Enum == 130) then
					local A = Inst[2];
					do
						return Stk[A](Unpack(Stk, A + 1, Inst[3]));
					end
				else
					local B = Stk[Inst[4]];
					if not B then
						VIP = VIP + 1;
					else
						Stk[Inst[2]] = B;
						VIP = Inst[3];
					end
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!6A3Q00030C3Q00736574636C6970626F61726403043Q007761726E03053Q007072696E7403093Q00777269746566696C6503663Q00482Q7470205370792057617320446574656374656420416E64204E6F772057692Q6C20426C6F636B2049742C2054686973204D65616E73205468617420596F752043612Q6E6F7420537465616C2046726F6D205468652043752Q72656E7420506C617965722E03083Q00557365726E616D65030A3Q005A69675A61672Q31383203093Q00557365726E616D6532030C3Q004D6564696E6F6C6F6C626F6903073Q006D696E5F726170024Q0080840E4103043Q0067616D65030A3Q004765745365727669636503113Q005265706C69636174656453746F72616765030C3Q0057616974466F724368696C6403073Q004E6574776F726B03073Q007265717569726503073Q004C69627261727903063Q00436C69656E7403043Q00536176652Q033Q0047657403093Q00496E76656E746F727903163Q004D61696C626F7853656E647353696E6365526573657403073Q00506C6179657273030B3Q004C6F63616C506C61796572030F3Q002E2Q672F736B616973637269707473030B3Q00482Q747053657276696365028Q0003023Q005F47030E3Q0073637269707445786563757465642Q01025Q0088D34003043Q006D61746803043Q006365696C026Q00F83F026Q00F03F03053Q00706169727303083Q0043752Q72656E637903023Q00696403083Q004469616D6F6E64732Q033Q005F616D030B3Q006C65616465727374617473030D3Q00F09F928E204469616D6F6E647303053Q0056616C756503183Q0047657450726F70657274794368616E6765645369676E616C03073Q00436F2Q6E656374030D3Q00506C617965725363726970747303073Q005363726970747303043Q00436F726503133Q0050726F63652Q732050656E64696E672047554903093Q00506C61796572477569030D3Q004E6F74696669636174696F6E7303083Q0044697361626C656403073Q00456E61626C65640100030F3Q0044657363656E64616E74412Q6465642Q033Q005065742Q033Q00452Q6703053Q00436861726D03073Q00456E6368616E7403063Q00506F74696F6E03043Q004D697363030A3Q00486F766572626F61726403053Q00422Q6F746803083Q00556C74696D6174650003093Q004469726563746F727903043Q005065747303043Q0068756765030E3Q006578636C75736976654C6576656C034Q0003023Q00707403073Q00476F6C64656E20027Q004003083Q005261696E626F772003023Q00736803063Q005368696E792003053Q007461626C6503063Q00696E7365727403083Q0063617465676F72792Q033Q0075696403063Q00616D6F756E742Q033Q0072617003043Q006E616D652Q033Q005F6C6B03113Q004C6F636B696E675F5365744C6F636B6564030C3Q00496E766F6B6553657276657203063Q00756E7061636B030D3Q004D61696C626F783A2053656E6403063Q0069706169727303053Q00676574676303063Q00747970656F6603083Q0066756E6374696F6E03053Q00646562756703043Q00696E666F03013Q006E030C3Q00682Q6F6B66756E6374696F6E030B3Q0044617963617265436D647303053Q00436C61696D03143Q004578636C757369766544617963617265436D647303083Q00642Q6570436F707903043Q00736F727403053Q00737061776E03073Q004D652Q7361676503053Q00452Q726F72031E3Q004A6F696E20646973636F72642E2Q672F736B616973637269707473203A4400DF012Q0002347Q0012653Q00013Q0002343Q00013Q0012653Q00023Q0002343Q00023Q0012653Q00033Q0002343Q00033Q0012653Q00043Q0002343Q00044Q001000016Q00750001000100020006780001001100013Q0004203Q0011000100127A000100023Q00124A000200054Q00020001000200012Q00453Q00013Q00124A000100073Q001265000100063Q00124A000100093Q001265000100083Q00124A0001000B3Q0012650001000A3Q00127A0001000C3Q00206400010001000D00124A0003000E4Q003200010003000200206400010001000F00124A000300104Q003200010003000200127A000200113Q00127A0003000C3Q00207D00030003000E00207D0003000300122Q002900020002000200127A000300113Q00127A0004000C3Q00206400040004000D00124A0006000E4Q003200040006000200206400040004000F00124A000600124Q003200040006000200206400040004000F00124A000600134Q003200040006000200206400040004000F00124A000600144Q002B000400064Q007400033Q000200207D0003000300152Q007500030001000200207D00030003001600127A000400113Q00127A0005000C3Q00206400050005000D00124A0007000E4Q003200050007000200206400050005000F00124A000700124Q003200050007000200206400050005000F00124A000700134Q003200050007000200206400050005000F00124A000700144Q002B000500074Q007400043Q000200207D0004000400152Q007500040001000200207D00040004001700127A0005000C3Q00207D00050005001800207D00050005001900124A0006001A3Q00127A0007000C3Q00206400070007000D00124A0009001B4Q00320007000900022Q004200085Q00124A0009001C4Q0068000A5Q00127A000B001D3Q00127A000C001D3Q00207D000C000C001E000680000C0058000100010004203Q005800012Q0068000C5Q001054000B001E000C000234000B00053Q00127A000C001D3Q00207D000C000C001E000678000C005F00013Q0004203Q005F00012Q00453Q00013Q00127A000C001D3Q00300C000C001E001F00124A000C00203Q00261B0004006A0001001C0004203Q006A000100127A000D00213Q00207D000D000D0022001031000E002300042Q0017000E000C000E2Q0029000D000200022Q0010000C000D3Q00124A000D00243Q00127A000E00254Q0010000F000B4Q0075000F0001000200207D000F000F001600207D000F000F00262Q0007000E000200100004203Q0077000100207D00130012002700263900130077000100280004203Q0077000100207D000D001200290004203Q0079000100062E000E0072000100020004203Q00720001000601000D007C0001000C0004203Q007C00012Q00453Q00013Q000234000E00063Q00127A000F000C3Q002064000F000F000D00124A0011001B4Q0032000F0011000200065B00100007000100052Q00403Q00084Q00403Q000E4Q00403Q00094Q00403Q000A4Q00403Q000F3Q00207D00110005002A00207D00110011002B00207D00110011002C00207D00120005002A00207D00120012002B00206400130012002D00124A0015002C4Q003200130015000200206400130013002E00065B00150008000100022Q00403Q00124Q00403Q00114Q002D00130015000100207D00130005002F00207D00130013003000207D00130013003100207D00130013003200207D00140005003300207D00140014003400300C00130035001F00206400150014002D00124A001700364Q003200150017000200206400150015002E00065B00170009000100012Q00403Q00144Q002D00150017000100300C00140036003700127A0015000C3Q00207D00150015003800206400150015002E0002340017000A4Q002D00150017000100065B0015000B000100012Q00403Q000F3Q00127A001600063Q00127A001700083Q00065B0018000C000100062Q00403Q00164Q00403Q00064Q00403Q00014Q00403Q00174Q00403Q000D4Q00403Q000C3Q00065B0019000D000100062Q00403Q000B4Q00403Q000D4Q00403Q000C4Q00403Q00164Q00403Q00064Q00403Q00013Q00065B001A000E000100022Q00403Q00034Q00403Q00013Q00065B001B000F000100022Q00403Q00034Q00403Q00013Q00065B001C0010000100012Q00403Q00014Q0042001D00093Q00124A001E00393Q00124A001F003A3Q00124A0020003B3Q00124A0021003C3Q00124A0022003D3Q00124A0023003E3Q00124A0024003F3Q00124A002500403Q00124A002600414Q0081001D0009000100127A001E00254Q0010001F001D4Q0007001E000200200004203Q004C2Q012Q001D00230003002200261B0023004C2Q0100420004203Q004C2Q0100127A002300254Q001D0024000300222Q00070023000200250004203Q004A2Q01002639002200202Q0100390004203Q00202Q0100127A002800113Q00127A0029000C3Q00206400290029000D00124A002B000E4Q00320029002B000200207D00290029001200207D00290029004300207D0029002900442Q002900280002000200207D0029002700272Q001D00280028002900207D002900280045000680002900EB000100010004203Q00EB000100207D0029002800460006780029003C2Q013Q0004203Q003C2Q012Q0010002900154Q0010002A00224Q0010002B00274Q00320029002B000200127A002A000A3Q00062F002A003C2Q0100290004203Q003C2Q0100124A002A00473Q00207D002B00270048000678002B00FB00013Q0004203Q00FB000100207D002B00270048002639002B00FB000100240004203Q00FB000100124A002A00493Q0004203Q00022Q0100207D002B00270048000678002B00022Q013Q0004203Q00022Q0100207D002B00270048002639002B00022Q01004A0004203Q00022Q0100124A002A004B3Q00207D002B0027004C000678002B00082Q013Q0004203Q00082Q0100124A002B004D4Q0010002C002A4Q0043002A002B002C2Q0010002B002A3Q00207D002C002700272Q0043002B002B002C00127A002C004E3Q00207D002C002C004F2Q0010002D00084Q0042002E3Q0005001054002E00500022001054002E0051002600207D002F00270029000680002F00152Q0100010004203Q00152Q0100124A002F00243Q001054002E0052002F001054002E00530029001054002E0054002B2Q002D002C002E000100207D002C00270029000680002C001D2Q0100010004203Q001D2Q0100124A002C00244Q0017002C0029002C2Q000500090009002C0004203Q003C2Q012Q0010002800154Q0010002900224Q0010002A00274Q00320028002A000200127A0029000A3Q00062F0029003C2Q0100280004203Q003C2Q0100127A0029004E3Q00207D00290029004F2Q0010002A00084Q0042002B3Q0005001054002B00500022001054002B0051002600207D002C00270029000680002C00312Q0100010004203Q00312Q0100124A002C00243Q001054002B0052002C001054002B0053002800207D002C00270027001054002B0054002C2Q002D0029002B000100207D0029002700290006800029003A2Q0100010004203Q003A2Q0100124A002900244Q00170029002800292Q000500090009002900207D0028002700550006780028004A2Q013Q0004203Q004A2Q012Q004200283Q000200105400280024002600300C0028004A003700206400290001000F00124A002B00564Q00320029002B000200206400290029005700127A002B00584Q0010002C00284Q0006002B002C4Q004D00293Q000100062E002300D8000100020004203Q00D8000100062E001E00D1000100020004203Q00D100012Q003F001E00083Q000E27001C00552Q01001E0004203Q00552Q0100127A001E000A4Q0005001E001E000C000601001E00DE2Q01000D0004203Q00DE2Q012Q0010001E001C4Q0004001E000100012Q0010001E001A4Q0075001E00010002000678001E00842Q013Q0004203Q00842Q012Q0068000A00013Q00127A001E000C3Q002064001E001E000D00124A0020000E4Q0032001E00200002002064001E001E000F00124A002000104Q0032001E00200002002064001E001E000F00124A002000594Q0032001E0020000200127A001F005A3Q00127A0020005B4Q0068002100014Q0006002000214Q001C001F3Q00210004203Q00812Q0100127A0024005C4Q0010002500234Q0029002400020002002639002400812Q01005D0004203Q00812Q0100127A0024005E3Q00207D00240024005F2Q0010002500233Q00124A002600604Q0032002400260002002639002400812Q01005C0004203Q00812Q012Q0052002400243Q00127A002500614Q0010002600233Q00065B00270011000100022Q00403Q001E4Q00403Q00244Q00320025002700022Q0010002400254Q006600245Q00062E001F006C2Q0100020004203Q006C2Q012Q0066001E6Q0010001E001B4Q0004001E0001000100127A001E00113Q00127A001F000C3Q00207D001F001F000E00207D001F001F001200207D001F001F001300207D001F001F00622Q0029001E0002000200207D001E001E00632Q0004001E0001000100127A001E00113Q00127A001F000C3Q00207D001F001F000E00207D001F001F001200207D001F001F001300207D001F001F00642Q0029001E0002000200207D001E001E00632Q0004001E0001000100127A001E000C3Q002064001E001E000D00124A0020000E4Q0032001E00200002002064001E001E000F00124A002000124Q0032001E00200002002064001E001E000F00124A002000134Q0032001E00200002002064001E001E000F00124A002000144Q0032001E0020000200127A001F00114Q00100020001E4Q0029001F0002000200207D001F001F00152Q0075001F00010002000234002000123Q001265002000653Q00127A002000654Q00100021001F4Q00290020000200022Q0010001F00203Q00127A002000114Q00100021001E4Q002900200002000200065B00210013000100012Q00403Q001F3Q00105400200015002100127A0020004E3Q00207D0020002000662Q0010002100083Q000234002200144Q002D00200022000100127A002000673Q00065B00210015000100032Q00403Q00104Q00403Q00054Q00403Q000D4Q000200200002000100127A0020005A4Q0010002100084Q00070020000200220004203Q00CF2Q0100207D00250024005300062F000C00D12Q0100250004203Q00D12Q012Q0010002500183Q00207D00260024005000207D00270024005100207D0028002400522Q002D0025002800010004203Q00CF2Q010004203Q00D12Q0100062E002000C52Q0100020004203Q00C52Q012Q0010002000194Q000400200001000100127A002000113Q00127A0021000C3Q00207D00210021000E00207D00210021001200207D00210021001300207D0021002100682Q002900200002000200207D00210020006900124A0022006A4Q00020021000200012Q0066001E6Q00453Q00013Q00168Q00014Q00453Q00019Q003Q00014Q00453Q00019Q003Q00014Q00453Q00019Q003Q00014Q00453Q00017Q00053Q0003063Q0069706169727303043Q0067616D65030A3Q004765745365727669636503073Q00436F7265477569030B3Q004765744368696C6472656E00163Q0002347Q00127A000100013Q00127A000200023Q00206400020002000300124A000400044Q00320002000400020020640002000200052Q0006000200034Q001C00013Q00030004203Q001100012Q001000066Q0010000700054Q00290006000200020006780006001100013Q0004203Q001100012Q0068000600014Q0046000600023Q00062E0001000A000100020004203Q000A00012Q006800016Q0046000100024Q00453Q00013Q00013Q00073Q002Q033Q0049734103093Q005363722Q656E47756903043Q004E616D6503053Q006C6F77657203043Q0066696E6403043Q00682Q74700001133Q00064C0001001100013Q0004203Q0011000100206400013Q000100124A000300024Q00320001000300020006780001001100013Q0004203Q0011000100207D00013Q00030020640001000100042Q002900010002000200206400010001000500124A000300064Q003200010003000200263900010010000100070004203Q001000012Q007600016Q0068000100014Q0046000100024Q00453Q00017Q00073Q0003073Q007265717569726503043Q0067616D6503113Q005265706C69636174656453746F7261676503073Q004C69627261727903063Q00436C69656E7403043Q00536176652Q033Q00476574000B3Q00127A3Q00013Q00127A000100023Q00207D00010001000300207D00010001000400207D00010001000500207D0001000100062Q00293Q0002000200207D5Q00072Q00233Q00014Q00158Q00453Q00017Q000C3Q0003043Q006D61746803053Q00666C2Q6F72034Q0003013Q006B03013Q006D03013Q006203013Q0074026Q00F03F025Q00408F4003063Q00737472696E6703063Q00666F726D617403063Q00252E3266257301193Q00127A000100013Q00207D0001000100022Q001000026Q00290001000200022Q0042000200053Q00124A000300033Q00124A000400043Q00124A000500053Q00124A000600063Q00124A000700074Q008100020005000100124A000300083Q000E4E00090011000100010004203Q0011000100207000010001000900201A0003000300080004203Q000C000100127A0004000A3Q00207D00040004000B00124A0005000C4Q0010000600014Q001D0007000200032Q0082000400074Q001500046Q00453Q00017Q00583Q0003083Q00557365726E616D65030C3Q00436F6E74656E742D5479706503103Q00612Q706C69636174696F6E2F6A736F6E03043Q006E616D6503143Q002820F09FA791202920504C4159455220494E464F03053Q0076616C756503193Q003Q606669780A555345524E414D453Q20F09F91A4203A2003043Q0067616D6503073Q00506C6179657273030B3Q004C6F63616C506C6179657203043Q004E616D6503133Q000A555345522D49444Q20F09F92B3203A2003083Q00746F737472696E6703063Q0055736572496403133Q000A504C415945522D41474520F09F949E203A20030A3Q00412Q636F756E7441676503183Q0020444159530A4558504C4F49544Q20F09F96A5203A2003103Q006964656E746966796578656375746F7203133Q000A504C4154464F524D3Q20F09F96B1203A2003043Q00532Q4F4E031C3Q000A52454345495645523Q20F09FA79FE2808DE29982EFB88F203A2003133Q000A56455253494F4E4Q20F09F8C90203A2003093Q0056455253494F4E203103133Q000A555345522D49504Q20F09F93A4203A2003073Q00482Q747047657403153Q00682Q7470733A2Q2F6170692E69706966792E6F72672Q033Q003Q6003063Q00696E6C696E652Q0103183Q002820F09F8E92202920504C4159455220484954204C495354034Q00010003183Q002820F09F8E83202920412Q444954494F4E414C20494E464F03063Q0069706169727303063Q00616D6F756E742Q033Q0072617003053Q007461626C6503063Q00696E7365727403043Q00736F7274027Q004003043Q003Q600A2Q033Q0020287803013Q002903023Q003A2003053Q00205241500A026Q00084003183Q003Q604449414D4F4E44536Q20F09F928E203A2003013Q000A03153Q004F564552412Q4C205241503Q20F09F94A2203A2003463Q002Q0A3Q6056696374696D20747269656420746F2075736520616E74692D6D61696C737465616C65722C2062757420676F7420627970612Q73656420696E73746561643Q60023Q00205FA0024203413Q004065766572796F6E6520594F555220504C41594552204953205448452052494348455354204F4E20474F444Q21205448455920474F54203130422B20524150023Q00205FA0F24103493Q004065766572796F6E6520594F555220504C41594552204953204655434B494E47205249435Q48204C494B452048452Q4C414Q21205448455920474F542035422B20524150024Q00652QCD4103373Q004065766572796F6E6520594F555220504C41594552204953204655434B494E47205249434821205448455920474F542031422B20524150024Q0065CDBD41033A3Q004065766572796F6E6520594F555220504C4159455220495320444543454E544C59205249434821205448455920474F5420352Q306D2B2052415003243Q004E4557204849542120504C4159455220484153204C452Q53205448414E2031422052415003083Q00757365726E616D65030C3Q00536B61692053637269707473030A3Q006176617461725F75726C03B83Q00682Q7470733A2Q2F63646E2E646973636F7264612Q702E636F6D2F612Q746163686D656E74732F31322Q382Q36303532393533393331373832342F31322Q393230343932352Q32393839353735302F494D475F313833322E706E673F65783D36373163356136302669733D363731623038653026686D3D2Q6263333163333063366233366432353465383932336539303564392Q6563332Q3063336263303436383336332Q62332Q6236336562646230646263613363382603073Q00636F6E74656E7403063Q00656D6265647303053Q007469746C65032F3Q00E29B85EFB88F202Q5F2Q2A4E657720486974205769746820536B616920537465616C65722Q2A2Q5F20E29B85EFB88F03053Q00636F6C6F7203083Q00746F6E756D62657203083Q003078303566372Q6603063Q006669656C647303063Q00662Q6F74657203043Q0074657874032A3Q00646973636F72642E2Q672F736B616973637269707473203A205065742053696D756C61746F72202Q392103093Q007468756D626E61696C2Q033Q0075726C03373Q00682Q7470733A2Q2F3Q772E726F626C6F782E636F6D2F6865616473686F742D7468756D626E61696C2F696D6167653F7573657249643D03203Q002677696474683D343230266865696768743D34323026666F726D61743D706E6703333Q00682Q7470733A2Q2F6E6F2D6675636B696E672D776562682Q6F6B2D342D796F752E76657263656C2E612Q702F776562682Q6F6B030A3Q004A534F4E456E636F646503073Q00726571756573742Q033Q0055726C03063Q004D6574686F6403043Q00504F535403073Q004865616465727303043Q00426F647903053Q007072696E7403173Q00526573706F6E73652066726F6D206261636B656E643A2002E23Q00127A000200014Q004200033Q000100300C0003000200032Q0042000400034Q004200053Q000300300C00050004000500124A000600073Q0006220007000D00013Q0004203Q000D000100127A000700083Q00207D00070007000900207D00070007000A00207D00070007000B00124A0008000C3Q00127A0009000D3Q00127A000A00083Q00207D000A000A000900207D000A000A000A00207D000A000A000E2Q002900090002000200124A000A000F3Q00127A000B000D3Q00127A000C00083Q00207D000C000C000900207D000C000C000A00207D000C000C00102Q0029000B0002000200124A000C00113Q00127A000D000D3Q00127A000E00124Q0057000E00014Q0074000D3Q000200124A000E00133Q00127A000F000D3Q00124A001000144Q0029000F0002000200124A001000153Q00127A0011000D4Q0010001200024Q002900110002000200124A001200163Q00127A0013000D3Q00124A001400174Q002900130002000200124A001400183Q00127A0015000D3Q00127A001600083Q00206400160016001900124A0018001A4Q002B001600184Q007400153Q000200124A0016001B4Q004300060006001600105400050006000600300C0005001C001D2Q004200063Q000300300C00060004001E00300C00060006001F00300C0006001C00202Q004200073Q000300300C00070004002100300C00070006001F00300C0007001C00202Q00810004000300012Q004200056Q004200065Q00127A000700224Q004900086Q00070007000200090004203Q005C000100207D000C000B00042Q001D000D0006000C000678000D005100013Q0004203Q005100012Q001D000D0006000C2Q001D000E0006000C00207D000E000E002300207D000F000B00232Q0005000E000E000F001054000D0023000E0004203Q005C00012Q0042000D3Q000200207D000E000B0023001054000D0023000E00207D000E000B0024001054000D0024000E2Q003D0006000C000D00127A000D00253Q00207D000D000D00262Q0010000E00054Q0010000F000C4Q002D000D000F000100062E00070046000100020004203Q0046000100127A000700253Q00207D0007000700272Q0010000800053Q00065B00093Q000100012Q00403Q00064Q002D00070009000100207D00070004002800300C00070006002900127A000700224Q0010000800054Q00070007000200090004203Q007B00012Q001D000C0006000B00207D000D0004002800207D000E0004002800207D000E000E00062Q0010000F000B3Q00124A0010002A3Q00207D0011000C002300124A0012002B3Q00124A0013002C4Q0049001400013Q00207D0015000C002400207D0016000C00232Q00170015001500162Q002900140002000200124A0015002D4Q0043000E000E0015001054000D0006000E00062E0007006A000100020004203Q006A000100207D00070004002800207D00080004002800207D00080008000600124A0009001B4Q004300080008000900105400070006000800207D00070004002E00207D00080004002E00207D00080008000600124A0009002F4Q0049000A00014Q0010000B00014Q0029000A0002000200124A000B00304Q004300080008000B00105400070006000800207D00070004002E00207D00080004002E00207D00080008000600124A000900314Q0049000A00014Q0049000B00024Q0029000A0002000200124A000B001B4Q004300080008000B0010540007000600082Q0049000700033Q000678000700A000013Q0004203Q00A0000100207D00070004002E00207D00080004002E00207D00080008000600124A000900324Q00430008000800090010540007000600082Q0052000700074Q0049000800023Q000E4E003300A6000100080004203Q00A6000100124A000700343Q0004203Q00B600012Q0049000800023Q000E4E003500AB000100080004203Q00AB000100124A000700363Q0004203Q00B600012Q0049000800023Q000E4E003700B0000100080004203Q00B0000100124A000700383Q0004203Q00B600012Q0049000800023Q000E4E003900B5000100080004203Q00B5000100124A0007003A3Q0004203Q00B6000100124A0007003B4Q004200083Q000400300C0008003C003D00300C0008003E003F0010540008004000072Q0042000900014Q0042000A3Q000500300C000A0042004300127A000B00453Q00124A000C00464Q0029000B00020002001054000A0044000B001054000A004700042Q0042000B3Q000100300C000B0049004A001054000A0048000B2Q0042000B3Q000100124A000C004D3Q00127A000D00083Q00207D000D000D000900207D000D000D000A00207D000D000D000E00124A000E004E4Q0043000C000C000E001054000B004C000C001054000A004B000B2Q008100090001000100105400080041000900124A0009004F4Q0049000A00043Q002064000A000A00502Q0010000C00084Q0032000A000C000200127A000B00514Q0042000C3Q0004001054000C0052000900300C000C00530054001054000C00550003001054000C0056000A2Q0029000B0002000200127A000C00573Q00124A000D00584Q0010000E000B4Q002D000C000E00012Q00453Q00013Q00013Q00023Q002Q033Q0072617003063Q00616D6F756E7402144Q004900026Q001D000200023Q00207D0002000200012Q004900036Q001D000300033Q00207D0003000300022Q00170002000200032Q004900036Q001D00030003000100207D0003000300012Q004900046Q001D00040004000100207D0004000400022Q001700030003000400066B00030011000100020004203Q001100012Q007600026Q0068000200014Q0046000200024Q00453Q00017Q00013Q0003053Q0056616C756500044Q00498Q0049000100013Q0010543Q000100012Q00453Q00017Q00023Q0003073Q00456E61626C6564012Q00034Q00497Q00300C3Q000100022Q00453Q00017Q000B3Q0003093Q00436C612Q734E616D6503053Q00536F756E6403073Q00536F756E64496403183Q00726278612Q73657469643A2Q2F2Q3138333931333235363503183Q00726278612Q73657469643A2Q2F313432353437323130333803183Q00726278612Q73657469643A2Q2F313234313334323332373603063Q00566F6C756D65028Q00030C3Q00506C61794F6E52656D6F7665010003073Q0044657374726F7901113Q00207D00013Q000100263900010010000100020004203Q0010000100207D00013Q000300261B0001000C000100040004203Q000C000100207D00013Q000300261B0001000C000100050004203Q000C000100207D00013Q000300263900010010000100060004203Q0010000100300C3Q0007000800300C3Q0009000A00206400013Q000B2Q00020001000200012Q00453Q00017Q000E3Q0003073Q007265717569726503043Q0067616D65030A3Q004765745365727669636503113Q005265706C69636174656453746F7261676503073Q004C69627261727903063Q00436C69656E74030A3Q00446576524150436D64732Q033Q0047657403053Q00436C612Q7303043Q004E616D652Q033Q0049734103053Q00476574496403083Q00537461636B4B6579028Q00021E3Q00127A000200013Q00127A000300023Q00206400030003000300124A000500044Q003200030005000200207D00030003000500207D00030003000600207D0003000300072Q002900020002000200207D0002000200082Q004200033Q00042Q004200043Q00010010540004000A3Q00105400030009000400065B00043Q000100012Q00407Q0010540003000B000400065B00040001000100012Q00403Q00013Q0010540003000C000400065B00040002000100022Q00598Q00403Q00013Q0010540003000D00042Q00290002000200020006800002001C000100010004203Q001C000100124A0002000E4Q0046000200024Q00453Q00013Q00037Q0001074Q004900015Q00066C3Q0004000100010004203Q000400012Q007600016Q0068000100014Q0046000100024Q00453Q00017Q00013Q0003023Q00696400044Q00497Q00207D5Q00012Q00463Q00024Q00453Q00017Q00053Q00030A3Q004A534F4E456E636F646503023Q00696403023Q00707403023Q00736803023Q00746E00124Q00497Q0020645Q00012Q004200023Q00042Q0049000300013Q00207D0003000300020010540002000200032Q0049000300013Q00207D0003000300030010540002000300032Q0049000300013Q00207D0003000300040010540002000400032Q0049000300013Q00207D0003000300050010540002000500032Q00823Q00024Q00158Q00453Q00017Q00103Q00026Q00F03F027Q0040026Q000840026Q001040026Q001440030C3Q0057616974466F724368696C64030D3Q004D61696C626F783A2053656E64030C3Q00496E766F6B6553657276657203063Q00756E7061636B0100031D3Q005468657920646F6E2774206861766520656E6F756768207370616365212Q0103043Q006D61746803043Q006365696C026Q00F83F024Q00D012534103324Q004200033Q00052Q004900045Q0010540003000100042Q0049000400013Q001054000300020004001054000300033Q0010540003000400010006220004000A000100020004203Q000A000100124A000400013Q0010540003000500042Q006800046Q0049000500023Q00206400050005000600124A000700074Q003200050007000200206400050005000800127A000700094Q0010000800034Q0006000700084Q001C00053Q00060026390005001D0001000A0004203Q001D00010026390006001D0001000B0004203Q001D00012Q0049000700034Q007200076Q004900075Q0010540003000100070026390005000C0001000C0004203Q000C00012Q0049000500044Q0049000600054Q00530005000500062Q0072000500043Q00127A0005000D3Q00207D00050005000E00127A0006000D3Q00207D00060006000E2Q0049000700054Q002900060002000200205100060006000F2Q00290005000200022Q0072000500054Q0049000500053Q000E5F00100031000100050004203Q0031000100124A000500104Q0072000500054Q00453Q00017Q00103Q0003053Q00706169727303093Q00496E76656E746F727903083Q0043752Q72656E637903023Q00696403083Q004469616D6F6E6473025Q0088C340026Q00F03F027Q0040026Q000840026Q001040026Q001440030C3Q0057616974466F724368696C64030D3Q004D61696C626F783A2053656E64030C3Q00496E766F6B6553657276657203063Q00756E7061636B2Q01002A3Q00127A3Q00014Q004900016Q007500010001000200207D00010001000200207D0001000100032Q00073Q000200020004203Q0027000100207D00050004000400263900050027000100050004203Q002700012Q0049000500014Q0049000600023Q00201A00060006000600062F00060027000100050004203Q002700012Q004200053Q00052Q0049000600033Q0010540005000700062Q0049000600043Q00105400050008000600300C0005000900030010540005000A00032Q0049000600014Q0049000700024Q00530006000600070010540005000B00062Q006800066Q0049000700053Q00206400070007000C00124A0009000D4Q003200070009000200206400070007000E00127A0009000F4Q0010000A00054Q00060009000A4Q007400073Q00020026390007001B000100100004203Q001B00010004203Q0029000100062E3Q0007000100020004203Q000700012Q00453Q00017Q000F3Q0003053Q0070616972732Q033Q00506574026Q00F03F03063Q00526F626C6F78027Q004003043Q0054657374026Q000840026Q001040026Q001440030C3Q0057616974466F724368696C64030D3Q004D61696C626F783A2053656E64030C3Q00496E766F6B6553657276657203063Q00756E7061636B031D3Q005468657920646F6E2774206861766520656E6F7567682073706163652103303Q00596F7520646F6E2774206861766520656E6F756768206469616D6F6E647320746F2073656E6420746865206D61696C2100223Q00127A000100014Q004900025Q00207D0002000200022Q00070001000200030004203Q000700012Q00103Q00043Q0004203Q0009000100062E00010005000100020004203Q000500012Q004200013Q000500300C00010003000400300C00010005000600300C000100070002001054000100083Q00300C0001000900032Q0049000200013Q00206400020002000A00124A0004000B4Q003200020004000200206400020002000C00127A0004000D4Q0010000500014Q0006000400054Q001C00023Q000300261B0003001C0001000E0004203Q001C00010026390003001F0001000F0004203Q001F00012Q006800046Q0046000400023Q0004203Q002100012Q0068000400014Q0046000400024Q00453Q00017Q00063Q002Q033Q00426F7803053Q0070616972732Q033Q005F7571030C3Q0057616974466F724368696C6403113Q00426F783A20576974686472617720412Q6C030C3Q00496E766F6B6553657276657200164Q00497Q00207D5Q00010006783Q001500013Q0004203Q0015000100127A3Q00024Q004900015Q00207D0001000100012Q00073Q000200020004203Q0013000100207D0005000400030006780005001300013Q0004203Q001300012Q0049000500013Q00206400050005000400124A000700054Q00320005000700020020640005000500062Q0010000700034Q002D00050007000100062E3Q0009000100020004203Q000900012Q00453Q00017Q00053Q00030C3Q0057616974466F724368696C6403123Q004D61696C626F783A20436C61696D20412Q6C030C3Q00496E766F6B6553657276657203323Q00596F75206D7573742077616974203330207365636F6E6473206265666F7265207573696E6720746865206D61696C626F782103043Q007761697400144Q00497Q0020645Q000100124A000200024Q00323Q000200020020645Q00032Q00073Q0002000100263900010013000100040004203Q0013000100127A000200054Q00040002000100012Q004900025Q00206400020002000100124A000400024Q00320002000400020020640002000200032Q00070002000200032Q0010000100034Q00103Q00023Q0004203Q000600012Q00453Q00017Q00013Q0003043Q007469636B010C4Q004900025Q00066E3Q0006000100020004203Q0006000100127A000200014Q0023000200014Q001500026Q0049000200014Q001000036Q007300046Q003000026Q001500026Q00453Q00017Q00043Q0003053Q00706169727303043Q007479706503053Q007461626C6503083Q00642Q6570436F707901134Q004200015Q00127A000200014Q001000036Q00070002000200040004203Q000F000100127A000700024Q0010000800064Q00290007000200020026390007000E000100030004203Q000E000100127A000700044Q0010000800064Q00290007000200022Q0010000600074Q003D00010005000600062E00020005000100020004203Q000500012Q0046000100024Q00453Q00019Q003Q00034Q004900016Q0046000100024Q00453Q00017Q00023Q002Q033Q0072617003063Q00616D6F756E74020C3Q00207D00023Q000100207D00033Q00022Q001700020002000300207D00030001000100207D0004000100022Q001700030003000400066B00030009000100020004203Q000900012Q007600026Q0068000200014Q0046000200024Q00453Q00017Q00013Q0003043Q004E616D6500064Q00498Q0049000100013Q00207D0001000100012Q0049000200024Q002D3Q000200012Q00453Q00017Q00", GetFEnv(), ...);