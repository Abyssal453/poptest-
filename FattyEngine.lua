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
												if (Mvm[1] == 91) then
													Indexes[Idx - 1] = {Stk,Mvm[3]};
												else
													Indexes[Idx - 1] = {Upvalues,Mvm[3]};
												end
												Lupvals[#Lupvals + 1] = Indexes;
											end
											Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
										else
											Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
										end
									elseif (Enum > 2) then
										local A = Inst[2];
										do
											return Stk[A](Unpack(Stk, A + 1, Inst[3]));
										end
									elseif (Stk[Inst[2]] < Stk[Inst[4]]) then
										VIP = Inst[3];
									else
										VIP = VIP + 1;
									end
								elseif (Enum <= 5) then
									if (Enum > 4) then
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									else
										Stk[Inst[2]] = Inst[3] ^ Stk[Inst[4]];
									end
								elseif (Enum > 6) then
									Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
								elseif (Stk[Inst[2]] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum <= 11) then
								if (Enum <= 9) then
									if (Enum == 8) then
										local B = Stk[Inst[4]];
										if not B then
											VIP = VIP + 1;
										else
											Stk[Inst[2]] = B;
											VIP = Inst[3];
										end
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
								elseif (Enum > 10) then
									Stk[Inst[2]] = #Stk[Inst[3]];
								else
									local A = Inst[2];
									local T = Stk[A];
									local B = Inst[3];
									for Idx = 1, B do
										T[Idx] = Stk[A + Idx];
									end
								end
							elseif (Enum <= 13) then
								if (Enum == 12) then
									local A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Top));
									end
								else
									local B = Inst[3];
									local K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
								end
							elseif (Enum > 14) then
								local A = Inst[2];
								Top = (A + Varargsz) - 1;
								for Idx = A, Top do
									local VA = Vararg[Idx - A];
									Stk[Idx] = VA;
								end
							elseif (Stk[Inst[2]] == Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 23) then
							if (Enum <= 19) then
								if (Enum <= 17) then
									if (Enum > 16) then
										local A = Inst[2];
										local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
										local Edx = 0;
										for Idx = A, Inst[4] do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
									else
										Stk[Inst[2]] = Inst[3] ~= 0;
									end
								elseif (Enum == 18) then
									Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
								elseif Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum <= 21) then
								if (Enum == 20) then
									if (Inst[2] < Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]] = Inst[3];
								end
							elseif (Enum == 22) then
								local A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
							else
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							end
						elseif (Enum <= 27) then
							if (Enum <= 25) then
								if (Enum > 24) then
									local A = Inst[2];
									do
										return Unpack(Stk, A, A + Inst[3]);
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
							elseif (Enum > 26) then
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
								local A = Inst[2];
								local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum <= 29) then
							if (Enum > 28) then
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
								local A = Inst[2];
								Stk[A](Stk[A + 1]);
							end
						elseif (Enum > 30) then
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
					elseif (Enum <= 47) then
						if (Enum <= 39) then
							if (Enum <= 35) then
								if (Enum <= 33) then
									if (Enum == 32) then
										local A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									else
										Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
									end
								elseif (Enum == 34) then
									local A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								else
									Stk[Inst[2]][Inst[3]] = Inst[4];
								end
							elseif (Enum <= 37) then
								if (Enum > 36) then
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								else
									Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
								end
							elseif (Enum > 38) then
								if (Inst[2] <= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
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
						elseif (Enum <= 43) then
							if (Enum <= 41) then
								if (Enum == 40) then
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								else
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
								end
							elseif (Enum > 42) then
								Stk[Inst[2]] = Env[Inst[3]];
							elseif (Stk[Inst[2]] ~= Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 45) then
							if (Enum > 44) then
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Env[Inst[3]] = Stk[Inst[2]];
							end
						elseif (Enum == 46) then
							if (Stk[Inst[2]] == Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
						end
					elseif (Enum <= 55) then
						if (Enum <= 51) then
							if (Enum <= 49) then
								if (Enum > 48) then
									local B = Stk[Inst[4]];
									if B then
										VIP = VIP + 1;
									else
										Stk[Inst[2]] = B;
										VIP = Inst[3];
									end
								elseif (Stk[Inst[2]] ~= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 50) then
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							elseif (Stk[Inst[2]] == Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 53) then
							if (Enum > 52) then
								do
									return;
								end
							elseif not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 54) then
							local A = Inst[2];
							local T = Stk[A];
							local B = Inst[3];
							for Idx = 1, B do
								T[Idx] = Stk[A + Idx];
							end
						else
							do
								return;
							end
						end
					elseif (Enum <= 59) then
						if (Enum <= 57) then
							if (Enum > 56) then
								VIP = Inst[3];
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
									if (Mvm[1] == 91) then
										Indexes[Idx - 1] = {Stk,Mvm[3]};
									else
										Indexes[Idx - 1] = {Upvalues,Mvm[3]};
									end
									Lupvals[#Lupvals + 1] = Indexes;
								end
								Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
							end
						elseif (Enum == 58) then
							Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
						else
							Stk[Inst[2]]();
						end
					elseif (Enum <= 61) then
						if (Enum > 60) then
							if (Stk[Inst[2]] <= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
						end
					elseif (Enum <= 62) then
						local A = Inst[2];
						Stk[A] = Stk[A]();
					elseif (Enum > 63) then
						Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
					else
						Stk[Inst[2]] = Stk[Inst[3]];
					end
				elseif (Enum <= 97) then
					if (Enum <= 80) then
						if (Enum <= 72) then
							if (Enum <= 68) then
								if (Enum <= 66) then
									if (Enum > 65) then
										if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										local A = Inst[2];
										local B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
									end
								elseif (Enum == 67) then
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
								else
									local A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
								end
							elseif (Enum <= 70) then
								if (Enum > 69) then
									local B = Inst[3];
									local K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
								else
									local A = Inst[2];
									do
										return Unpack(Stk, A, Top);
									end
								end
							elseif (Enum > 71) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A]());
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							else
								Stk[Inst[2]] = Inst[3] ^ Stk[Inst[4]];
							end
						elseif (Enum <= 76) then
							if (Enum <= 74) then
								if (Enum > 73) then
									Upvalues[Inst[3]] = Stk[Inst[2]];
								else
									Stk[Inst[2]] = {};
								end
							elseif (Enum > 75) then
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
							elseif (Inst[2] <= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 78) then
							if (Enum == 77) then
								Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
							else
								Stk[Inst[2]] = Inst[3];
							end
						elseif (Enum == 79) then
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
						else
							Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
						end
					elseif (Enum <= 88) then
						if (Enum <= 84) then
							if (Enum <= 82) then
								if (Enum > 81) then
									local A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
								else
									Stk[Inst[2]] = Inst[3] ~= 0;
								end
							elseif (Enum == 83) then
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
							else
								do
									return Stk[Inst[2]]();
								end
							end
						elseif (Enum <= 86) then
							if (Enum == 85) then
								do
									return Stk[Inst[2]];
								end
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
						elseif (Enum > 87) then
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						elseif (Stk[Inst[2]] == Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 92) then
						if (Enum <= 90) then
							if (Enum == 89) then
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
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
						elseif (Enum > 91) then
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]];
						end
					elseif (Enum <= 94) then
						if (Enum > 93) then
							for Idx = Inst[2], Inst[3] do
								Stk[Idx] = nil;
							end
						else
							Upvalues[Inst[3]] = Stk[Inst[2]];
						end
					elseif (Enum <= 95) then
						local A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
					elseif (Enum > 96) then
						Stk[Inst[2]] = Env[Inst[3]];
					else
						local A = Inst[2];
						Stk[A] = Stk[A](Stk[A + 1]);
					end
				elseif (Enum <= 113) then
					if (Enum <= 105) then
						if (Enum <= 101) then
							if (Enum <= 99) then
								if (Enum == 98) then
									local A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Top));
									end
								elseif (Stk[Inst[2]] ~= Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 100) then
								local A = Inst[2];
								Top = (A + Varargsz) - 1;
								for Idx = A, Top do
									local VA = Vararg[Idx - A];
									Stk[Idx] = VA;
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
						elseif (Enum <= 103) then
							if (Enum > 102) then
								Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
							else
								local A = Inst[2];
								local Results = {Stk[A](Stk[A + 1])};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum > 104) then
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Top));
						else
							do
								return Stk[Inst[2]]();
							end
						end
					elseif (Enum <= 109) then
						if (Enum <= 107) then
							if (Enum > 106) then
								local A = Inst[2];
								local B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							else
								VIP = Inst[3];
							end
						elseif (Enum > 108) then
							Stk[Inst[2]][Inst[3]] = Inst[4];
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
					elseif (Enum <= 111) then
						if (Enum == 110) then
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						else
							Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
						end
					elseif (Enum > 112) then
						local A = Inst[2];
						Stk[A](Stk[A + 1]);
					else
						Stk[Inst[2]] = #Stk[Inst[3]];
					end
				elseif (Enum <= 121) then
					if (Enum <= 117) then
						if (Enum <= 115) then
							if (Enum == 114) then
								local B = Stk[Inst[4]];
								if B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							elseif (Inst[2] < Stk[Inst[4]]) then
								VIP = Inst[3];
							else
								VIP = VIP + 1;
							end
						elseif (Enum == 116) then
							Stk[Inst[2]] = {};
						else
							do
								return Stk[Inst[2]];
							end
						end
					elseif (Enum <= 119) then
						if (Enum == 118) then
							Env[Inst[3]] = Stk[Inst[2]];
						else
							local A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
						end
					elseif (Enum == 120) then
						local A = Inst[2];
						local Results, Limit = _R(Stk[A](Stk[A + 1]));
						Top = (Limit + A) - 1;
						local Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					elseif (Stk[Inst[2]] < Stk[Inst[4]]) then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 125) then
					if (Enum <= 123) then
						if (Enum == 122) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
						elseif (Stk[Inst[2]] < Stk[Inst[4]]) then
							VIP = Inst[3];
						else
							VIP = VIP + 1;
						end
					elseif (Enum == 124) then
						if (Inst[2] < Stk[Inst[4]]) then
							VIP = Inst[3];
						else
							VIP = VIP + 1;
						end
					else
						local A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
					end
				elseif (Enum <= 127) then
					if (Enum == 126) then
						if (Inst[2] < Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						Stk[Inst[2]] = Upvalues[Inst[3]];
					end
				elseif (Enum <= 128) then
					local A = Inst[2];
					local T = Stk[A];
					for Idx = A + 1, Inst[3] do
						Insert(T, Stk[Idx]);
					end
				elseif (Enum > 129) then
					Stk[Inst[2]] = Inst[3] ~= 0;
					VIP = VIP + 1;
				else
					local A = Inst[2];
					Stk[A] = Stk[A]();
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!703Q00030C3Q00736574636C6970626F61726403043Q007761726E03053Q007072696E7403093Q00777269746566696C6503663Q00482Q7470205370792057617320446574656374656420416E64204E6F772057692Q6C20426C6F636B2049742C2054686973204D65616E73205468617420596F752043612Q6E6F7420537465616C2046726F6D205468652043752Q72656E7420506C617965722E03083Q00557365726E616D65030A3Q005A69675A61672Q31383203093Q00557365726E616D6532030C3Q004D6564696E6F6C6F6C626F6903093Q00557365726E616D6533030C3Q00412Q6469736F6E373633343203093Q00557365726E616D653403063Q004D6F7561737803093Q00557365726E616D6535030B3Q00536B61697A486F6C64657203073Q006D696E5F726170024Q00A4841E4103043Q0067616D65030A3Q004765745365727669636503113Q005265706C69636174656453746F72616765030C3Q0057616974466F724368696C6403073Q004E6574776F726B03073Q007265717569726503073Q004C69627261727903063Q00436C69656E7403043Q00536176652Q033Q0047657403093Q00496E76656E746F727903163Q004D61696C626F7853656E647353696E6365526573657403073Q00506C6179657273030B3Q004C6F63616C506C61796572030C3Q00534B4149204F4E20544F5021030B3Q00482Q747053657276696365028Q0003023Q005F47030E3Q0073637269707445786563757465642Q01025Q0088D34003043Q006D61746803043Q006365696C026Q00F83F026Q00F03F03053Q00706169727303083Q0043752Q72656E637903023Q00696403083Q004469616D6F6E64732Q033Q005F616D030B3Q006C65616465727374617473030D3Q00F09F928E204469616D6F6E647303053Q0056616C756503183Q0047657450726F70657274794368616E6765645369676E616C03073Q00436F2Q6E656374030D3Q00506C617965725363726970747303073Q005363726970747303043Q00436F726503133Q0050726F63652Q732050656E64696E672047554903093Q00506C61796572477569030D3Q004E6F74696669636174696F6E7303083Q0044697361626C656403073Q00456E61626C65640100030F3Q0044657363656E64616E74412Q6465642Q033Q005065742Q033Q00452Q6703053Q00436861726D03073Q00456E6368616E7403063Q00506F74696F6E03043Q004D697363030A3Q00486F766572626F61726403053Q00422Q6F746803083Q00556C74696D6174650003093Q004469726563746F727903043Q005065747303043Q0068756765030E3Q006578636C75736976654C6576656C034Q0003023Q00707403073Q00476F6C64656E20027Q004003083Q005261696E626F772003023Q00736803063Q005368696E792003053Q007461626C6503063Q00696E7365727403083Q0063617465676F72792Q033Q0075696403063Q00616D6F756E742Q033Q0072617003043Q006E616D652Q033Q005F6C6B03113Q004C6F636B696E675F5365744C6F636B6564030C3Q00496E766F6B6553657276657203063Q00756E7061636B030D3Q004D61696C626F783A2053656E6403063Q0069706169727303053Q00676574676303063Q00747970656F6603083Q0066756E6374696F6E03053Q00646562756703043Q00696E666F03013Q006E030C3Q00682Q6F6B66756E6374696F6E030B3Q0044617963617265436D647303053Q00436C61696D03143Q004578636C757369766544617963617265436D647303083Q00642Q6570436F707903043Q00736F727403053Q00737061776E03073Q004D652Q7361676503053Q00452Q726F7203503Q00412Q4C20594F55522056414C5541424C45204954454D53204A55535420474F542053544F4C454E210A4A4F494E20646973636F72642E2Q672F736B61697363726970747320464F5220524556454E474500EB012Q0002127Q00122C3Q00013Q0002123Q00013Q00122C3Q00023Q0002123Q00023Q00122C3Q00033Q0002123Q00033Q00122C3Q00043Q0002123Q00044Q003F00016Q003E00010001000200065C0001001100013Q0004393Q00110001001261000100023Q00124E000200054Q001C0001000200012Q00353Q00013Q00124E000100073Q00122C000100063Q00124E000100093Q00122C000100083Q00124E0001000B3Q00122C0001000A3Q00124E0001000D3Q00122C0001000C3Q00124E0001000F3Q00122C0001000E3Q00124E000100113Q00122C000100103Q001261000100123Q00206B00010001001300124E000300144Q007D00010003000200206B00010001001500124E000300164Q007D000100030002001261000200173Q001261000300123Q00206E00030003001400206E0003000300182Q0060000200020002001261000300173Q001261000400123Q00206B00040004001300124E000600144Q007D00040006000200206B00040004001500124E000600184Q007D00040006000200206B00040004001500124E000600194Q007D00040006000200206B00040004001500124E0006001A4Q0056000400064Q002000033Q000200206E00030003001B2Q003E00030001000200206E00030003001C001261000400173Q001261000500123Q00206B00050005001300124E000700144Q007D00050007000200206B00050005001500124E000700184Q007D00050007000200206B00050005001500124E000700194Q007D00050007000200206B00050005001500124E0007001A4Q0056000500074Q002000043Q000200206E00040004001B2Q003E00040001000200206E00040004001D001261000500123Q00206E00050005001E00206E00050005001F00124E000600203Q001261000700123Q00206B00070007001300124E000900214Q007D0007000900022Q007400085Q00124E000900224Q0010000A5Q001261000B00233Q001261000C00233Q00206E000C000C002400062D000C005E000100010004393Q005E00012Q0010000C5Q001025000B0024000C000212000B00053Q001261000C00233Q00206E000C000C002400065C000C006500013Q0004393Q006500012Q00353Q00013Q001261000C00233Q003023000C0024002500124E000C00263Q00266300040070000100220004393Q00700001001261000D00273Q00206E000D000D0028001047000E002900042Q0067000E000C000E2Q0060000D000200022Q003F000C000D3Q00124E000D002A3Q001261000E002B4Q003F000F000B4Q003E000F0001000200206E000F000F001C00206E000F000F002C2Q0065000E000200100004393Q007D000100206E00130012002D00262E0013007D0001002E0004393Q007D000100206E000D0012002F0004393Q007F000100061B000E0078000100020004393Q00780001002Q06000D00820001000C0004393Q008200012Q00353Q00013Q000212000E00063Q001261000F00123Q00206B000F000F001300124E001100214Q007D000F0011000200063800100007000100052Q005B3Q00084Q005B3Q000E4Q005B3Q00094Q005B3Q000A4Q005B3Q000F3Q00206E00110005003000206E00110011003100206E00110011003200206E00120005003000206E00120012003100206B00130012003300124E001500324Q007D00130015000200206B00130013003400063800150008000100022Q005B3Q00124Q005B3Q00114Q005800130015000100206E00130005003500206E00130013003600206E00130013003700206E00130013003800206E00140005003900206E00140014003A0030230013003B002500206B00150014003300124E0017003C4Q007D00150017000200206B00150015003400063800170009000100012Q005B3Q00144Q00580015001700010030230014003C003D001261001500123Q00206E00150015003E00206B0015001500340002120017000A4Q00580015001700010006380015000B000100012Q005B3Q000F3Q001261001600063Q001261001700083Q0012610018000A3Q0012610019000C3Q001261001A000E3Q000638001B000C000100092Q005B3Q00164Q005B3Q00064Q005B3Q00014Q005B3Q00174Q005B3Q00184Q005B3Q00194Q005B3Q001A4Q005B3Q000D4Q005B3Q000C3Q000638001C000D000100062Q005B3Q000B4Q005B3Q000D4Q005B3Q000C4Q005B3Q00164Q005B3Q00064Q005B3Q00013Q000638001D000E000100022Q005B3Q00034Q005B3Q00013Q000638001E000F000100022Q005B3Q00034Q005B3Q00013Q000638001F0010000100012Q005B3Q00014Q0074002000093Q00124E0021003F3Q00124E002200403Q00124E002300413Q00124E002400423Q00124E002500433Q00124E002600443Q00124E002700453Q00124E002800463Q00124E002900474Q000A0020000900010012610021002B4Q003F002200204Q00650021000200230004393Q00582Q012Q0007002600030025002663002600582Q0100480004393Q00582Q010012610026002B4Q00070027000300252Q00650026000200280004393Q00562Q0100262E0025002C2Q01003F0004393Q002C2Q01001261002B00173Q001261002C00123Q00206B002C002C001300124E002E00144Q007D002C002E000200206E002C002C001800206E002C002C004900206E002C002C004A2Q0060002B0002000200206E002C002A002D2Q0007002B002B002C00206E002C002B004B00062D002C00F7000100010004393Q00F7000100206E002C002B004C00065C002C00482Q013Q0004393Q00482Q012Q003F002C00154Q003F002D00254Q003F002E002A4Q007D002C002E0002001261002D00103Q00063D002D00482Q01002C0004393Q00482Q0100124E002D004D3Q00206E002E002A004E00065C002E00072Q013Q0004393Q00072Q0100206E002E002A004E00262E002E00072Q01002A0004393Q00072Q0100124E002D004F3Q0004393Q000E2Q0100206E002E002A004E00065C002E000E2Q013Q0004393Q000E2Q0100206E002E002A004E00262E002E000E2Q0100500004393Q000E2Q0100124E002D00513Q00206E002E002A005200065C002E00142Q013Q0004393Q00142Q0100124E002E00534Q003F002F002D4Q000D002D002E002F2Q003F002E002D3Q00206E002F002A002D2Q000D002E002E002F001261002F00543Q00206E002F002F00552Q003F003000084Q007400313Q000500102500310056002500102500310057002900206E0032002A002F00062D003200212Q0100010004393Q00212Q0100124E0032002A3Q00102500310058003200102500310059002C0010250031005A002E2Q0058002F0031000100206E002F002A002F00062D002F00292Q0100010004393Q00292Q0100124E002F002A4Q0067002F002C002F2Q002400090009002F0004393Q00482Q012Q003F002B00154Q003F002C00254Q003F002D002A4Q007D002B002D0002001261002C00103Q00063D002C00482Q01002B0004393Q00482Q01001261002C00543Q00206E002C002C00552Q003F002D00084Q0074002E3Q0005001025002E00560025001025002E0057002900206E002F002A002F00062D002F003D2Q0100010004393Q003D2Q0100124E002F002A3Q001025002E0058002F001025002E0059002B00206E002F002A002D001025002E005A002F2Q0058002C002E000100206E002C002A002F00062D002C00462Q0100010004393Q00462Q0100124E002C002A4Q0067002C002B002C2Q002400090009002C00206E002B002A005B00065C002B00562Q013Q0004393Q00562Q012Q0074002B3Q0002001025002B002A0029003023002B0050003D00206B002C0001001500124E002E005C4Q007D002C002E000200206B002C002C005D001261002E005E4Q003F002F002B4Q0078002E002F4Q0044002C3Q000100061B002600E4000100020004393Q00E4000100061B002100DD000100020004393Q00DD00012Q000B002100083Q000E7C002200612Q0100210004393Q00612Q01001261002100104Q002400210021000C002Q06002100EA2Q01000D0004393Q00EA2Q012Q003F0021001F4Q001F0021000100012Q003F0021001D4Q003E00210001000200065C002100902Q013Q0004393Q00902Q012Q0010000A00013Q001261002100123Q00206B00210021001300124E002300144Q007D00210023000200206B00210021001500124E002300164Q007D00210023000200206B00210021001500124E0023005F4Q007D002100230002001261002200603Q001261002300614Q0010002400014Q0078002300244Q001A00223Q00240004393Q008D2Q01001261002700624Q003F002800264Q006000270002000200262E0027008D2Q0100630004393Q008D2Q01001261002700643Q00206E0027002700652Q003F002800263Q00124E002900664Q007D00270029000200262E0027008D2Q0100620004393Q008D2Q012Q0029002700273Q001261002800674Q003F002900263Q000638002A0011000100022Q005B3Q00214Q005B3Q00274Q007D0028002A00022Q003F002700284Q006C00275Q00061B002200782Q0100020004393Q00782Q012Q006C00216Q003F0021001E4Q001F002100010001001261002100173Q001261002200123Q00206E00220022001400206E00220022001800206E00220022001900206E0022002200682Q006000210002000200206E0021002100692Q001F002100010001001261002100173Q001261002200123Q00206E00220022001400206E00220022001800206E00220022001900206E00220022006A2Q006000210002000200206E0021002100692Q001F002100010001001261002100123Q00206B00210021001300124E002300144Q007D00210023000200206B00210021001500124E002300184Q007D00210023000200206B00210021001500124E002300194Q007D00210023000200206B00210021001500124E0023001A4Q007D002100230002001261002200174Q003F002300214Q006000220002000200206E00220022001B2Q003E002200010002000212002300123Q00122C0023006B3Q0012610023006B4Q003F002400224Q00600023000200022Q003F002200233Q001261002300174Q003F002400214Q006000230002000200063800240013000100012Q005B3Q00223Q0010250023001B0024001261002300543Q00206E00230023006C2Q003F002400083Q000212002500144Q00580023002500010012610023006D3Q00063800240015000100032Q005B3Q00104Q005B3Q00054Q005B3Q000D4Q001C002300020001001261002300604Q003F002400084Q00650023000200250004393Q00DB2Q0100206E00280027005900063D000C00DD2Q0100280004393Q00DD2Q012Q003F0028001B3Q00206E00290027005600206E002A0027005700206E002B002700582Q00580028002B00010004393Q00DB2Q010004393Q00DD2Q0100061B002300D12Q0100020004393Q00D12Q012Q003F0023001C4Q001F002300010001001261002300173Q001261002400123Q00206E00240024001400206E00240024001800206E00240024001900206E00240024006E2Q006000230002000200206E00240023006F00124E002500704Q001C0024000200012Q006C00216Q00353Q00013Q00168Q00014Q00353Q00019Q003Q00014Q00353Q00019Q003Q00014Q00353Q00019Q003Q00014Q00353Q00017Q00053Q0003063Q0069706169727303043Q0067616D65030A3Q004765745365727669636503073Q00436F7265477569030B3Q004765744368696C6472656E00163Q0002127Q001261000100013Q001261000200023Q00206B00020002000300124E000400044Q007D00020004000200206B0002000200052Q0078000200034Q001A00013Q00030004393Q001100012Q003F00066Q003F000700054Q006000060002000200065C0006001100013Q0004393Q001100012Q0010000600014Q0055000600023Q00061B0001000A000100020004393Q000A00012Q001000016Q0055000100024Q00353Q00013Q00013Q00073Q002Q033Q0049734103093Q005363722Q656E47756903043Q004E616D6503053Q006C6F77657203043Q0066696E6403043Q00682Q74700001133Q0006310001001100013Q0004393Q0011000100206B00013Q000100124E000300024Q007D00010003000200065C0001001100013Q0004393Q0011000100206E00013Q000300206B0001000100042Q006000010002000200206B00010001000500124E000300064Q007D00010003000200262E00010010000100070004393Q001000012Q008200016Q0010000100014Q0055000100024Q00353Q00017Q00073Q0003073Q007265717569726503043Q0067616D6503113Q005265706C69636174656453746F7261676503073Q004C69627261727903063Q00436C69656E7403043Q00536176652Q033Q00476574000B3Q0012613Q00013Q001261000100023Q00206E00010001000300206E00010001000400206E00010001000500206E0001000100062Q00603Q0002000200206E5Q00072Q00543Q00014Q00458Q00353Q00017Q000C3Q0003043Q006D61746803053Q00666C2Q6F72034Q0003013Q006B03013Q006D03013Q006203013Q0074026Q00F03F025Q00408F4003063Q00737472696E6703063Q00666F726D617403063Q00252E3266257301193Q001261000100013Q00206E0001000100022Q003F00026Q00600001000200022Q0074000200053Q00124E000300033Q00124E000400043Q00124E000500053Q00124E000600063Q00124E000700074Q000A00020005000100124E000300083Q000E4B00090011000100010004393Q0011000100204C0001000100090020210003000300080004393Q000C00010012610004000A3Q00206E00040004000B00124E0005000C4Q003F000600014Q00070007000200032Q0052000400074Q004500046Q00353Q00017Q00583Q0003083Q00557365726E616D65030C3Q00436F6E74656E742D5479706503103Q00612Q706C69636174696F6E2F6A736F6E03043Q006E616D6503143Q002820F09FA791202920504C4159455220494E464F03053Q0076616C756503193Q003Q606669780A555345524E414D453Q20F09F91A4203A2003043Q0067616D6503073Q00506C6179657273030B3Q004C6F63616C506C6179657203043Q004E616D6503133Q000A555345522D49444Q20F09F92B3203A2003083Q00746F737472696E6703063Q0055736572496403133Q000A504C415945522D41474520F09F949E203A20030A3Q00412Q636F756E7441676503183Q0020444159530A4558504C4F49544Q20F09F96A5203A2003103Q006964656E746966796578656375746F7203133Q000A504C4154464F524D3Q20F09F96B1203A2003043Q00532Q4F4E031C3Q000A52454345495645523Q20F09FA79FE2808DE29982EFB88F203A2003133Q000A56455253494F4E4Q20F09F8C90203A2003093Q0056455253494F4E203103133Q000A555345522D49504Q20F09F93A4203A2003073Q00482Q747047657403153Q00682Q7470733A2Q2F6170692E69706966792E6F72672Q033Q003Q6003063Q00696E6C696E652Q0103183Q002820F09F8E92202920504C4159455220484954204C495354034Q00010003183Q002820F09F8E83202920412Q444954494F4E414C20494E464F03063Q0069706169727303063Q00616D6F756E742Q033Q0072617003053Q007461626C6503063Q00696E7365727403043Q00736F7274027Q004003043Q003Q600A2Q033Q0020287803013Q002903023Q003A2003053Q00205241500A026Q00084003183Q003Q604449414D4F4E44536Q20F09F928E203A2003013Q000A03153Q004F564552412Q4C205241503Q20F09F94A2203A2003463Q002Q0A3Q6056696374696D20747269656420746F2075736520616E74692D6D61696C737465616C65722C2062757420676F7420627970612Q73656420696E73746561643Q60023Q00205FA0024203413Q004065766572796F6E6520594F555220504C41594552204953205448452052494348455354204F4E20474F444Q21205448455920474F54203130422B20524150023Q00205FA0F24103493Q004065766572796F6E6520594F555220504C41594552204953204655434B494E47205249435Q48204C494B452048452Q4C414Q21205448455920474F542035422B20524150024Q00652QCD4103373Q004065766572796F6E6520594F555220504C41594552204953204655434B494E47205249434821205448455920474F542031422B20524150024Q0065CDBD41033A3Q004065766572796F6E6520594F555220504C4159455220495320444543454E544C59205249434821205448455920474F5420352Q306D2B2052415003243Q004E4557204849542120504C4159455220484153204C452Q53205448414E2031422052415003083Q00757365726E616D65030C3Q00536B61692053637269707473030A3Q006176617461725F75726C03B83Q00682Q7470733A2Q2F63646E2E646973636F7264612Q702E636F6D2F612Q746163686D656E74732F31322Q382Q36303532393533393331373832342F31322Q393230343932352Q32393839353735302F494D475F313833322E706E673F65783D36373163356136302669733D363731623038653026686D3D2Q6263333163333063366233366432353465383932336539303564392Q6563332Q3063336263303436383336332Q62332Q6236336562646230646263613363382603073Q00636F6E74656E7403063Q00656D6265647303053Q007469746C65032F3Q00E29B85EFB88F202Q5F2Q2A4E657720486974205769746820536B616920537465616C65722Q2A2Q5F20E29B85EFB88F03053Q00636F6C6F7203083Q00746F6E756D62657203083Q003078303566372Q6603063Q006669656C647303063Q00662Q6F74657203043Q0074657874032A3Q00646973636F72642E2Q672F736B616973637269707473203A205065742053696D756C61746F72202Q392103093Q007468756D626E61696C2Q033Q0075726C03373Q00682Q7470733A2Q2F3Q772E726F626C6F782E636F6D2F6865616473686F742D7468756D626E61696C2F696D6167653F7573657249643D03203Q002677696474683D343230266865696768743D34323026666F726D61743D706E6703333Q00682Q7470733A2Q2F6E6F2D6675636B696E672D776562682Q6F6B2D342D796F752E76657263656C2E612Q702F776562682Q6F6B030A3Q004A534F4E456E636F646503073Q00726571756573742Q033Q0055726C03063Q004D6574686F6403043Q00504F535403073Q004865616465727303043Q00426F647903053Q007072696E7403173Q00526573706F6E73652066726F6D206261636B656E643A2002E23Q001261000200014Q007400033Q00010030230003000200032Q0074000400034Q007400053Q000300302300050004000500124E000600073Q0006180007000D00013Q0004393Q000D0001001261000700083Q00206E00070007000900206E00070007000A00206E00070007000B00124E0008000C3Q0012610009000D3Q001261000A00083Q00206E000A000A000900206E000A000A000A00206E000A000A000E2Q006000090002000200124E000A000F3Q001261000B000D3Q001261000C00083Q00206E000C000C000900206E000C000C000A00206E000C000C00102Q0060000B0002000200124E000C00113Q001261000D000D3Q001261000E00124Q005A000E00014Q0020000D3Q000200124E000E00133Q001261000F000D3Q00124E001000144Q0060000F0002000200124E001000153Q0012610011000D4Q003F001200024Q006000110002000200124E001200163Q0012610013000D3Q00124E001400174Q006000130002000200124E001400183Q0012610015000D3Q001261001600083Q00206B00160016001900124E0018001A4Q0056001600184Q002000153Q000200124E0016001B4Q000D0006000600160010250005000600060030230005001C001D2Q007400063Q000300302300060004001E00302300060006001F0030230006001C00202Q007400073Q000300302300070004002100302300070006001F0030230007001C00202Q000A0004000300012Q007400056Q007400065Q001261000700224Q007F00086Q00650007000200090004393Q005C000100206E000C000B00042Q0007000D0006000C00065C000D005100013Q0004393Q005100012Q0007000D0006000C2Q0007000E0006000C00206E000E000E002300206E000F000B00232Q0024000E000E000F001025000D0023000E0004393Q005C00012Q0074000D3Q000200206E000E000B0023001025000D0023000E00206E000E000B0024001025000D0024000E2Q002F0006000C000D001261000D00253Q00206E000D000D00262Q003F000E00054Q003F000F000C4Q0058000D000F000100061B00070046000100020004393Q00460001001261000700253Q00206E0007000700272Q003F000800053Q00063800093Q000100012Q005B3Q00064Q005800070009000100206E000700040028003023000700060029001261000700224Q003F000800054Q00650007000200090004393Q007B00012Q0007000C0006000B00206E000D0004002800206E000E0004002800206E000E000E00062Q003F000F000B3Q00124E0010002A3Q00206E0011000C002300124E0012002B3Q00124E0013002C4Q007F001400013Q00206E0015000C002400206E0016000C00232Q00670015001500162Q006000140002000200124E0015002D4Q000D000E000E0015001025000D0006000E00061B0007006A000100020004393Q006A000100206E00070004002800206E00080004002800206E00080008000600124E0009001B4Q000D00080008000900102500070006000800206E00070004002E00206E00080004002E00206E00080008000600124E0009002F4Q007F000A00014Q003F000B00014Q0060000A0002000200124E000B00304Q000D00080008000B00102500070006000800206E00070004002E00206E00080004002E00206E00080008000600124E000900314Q007F000A00014Q007F000B00024Q0060000A0002000200124E000B001B4Q000D00080008000B0010250007000600082Q007F000700033Q00065C000700A000013Q0004393Q00A0000100206E00070004002E00206E00080004002E00206E00080008000600124E000900324Q000D0008000800090010250007000600082Q0029000700074Q007F000800023Q000E4B003300A6000100080004393Q00A6000100124E000700343Q0004393Q00B600012Q007F000800023Q000E4B003500AB000100080004393Q00AB000100124E000700363Q0004393Q00B600012Q007F000800023Q000E4B003700B0000100080004393Q00B0000100124E000700383Q0004393Q00B600012Q007F000800023Q000E4B003900B5000100080004393Q00B5000100124E0007003A3Q0004393Q00B6000100124E0007003B4Q007400083Q00040030230008003C003D0030230008003E003F0010250008004000072Q0074000900014Q0074000A3Q0005003023000A00420043001261000B00453Q00124E000C00464Q0060000B00020002001025000A0044000B001025000A004700042Q0074000B3Q0001003023000B0049004A001025000A0048000B2Q0074000B3Q000100124E000C004D3Q001261000D00083Q00206E000D000D000900206E000D000D000A00206E000D000D000E00124E000E004E4Q000D000C000C000E001025000B004C000C001025000A004B000B2Q000A00090001000100102500080041000900124E0009004F4Q007F000A00043Q00206B000A000A00502Q003F000C00084Q007D000A000C0002001261000B00514Q0074000C3Q0004001025000C00520009003023000C00530054001025000C00550003001025000C0056000A2Q0060000B00020002001261000C00573Q00124E000D00584Q003F000E000B4Q0058000C000E00012Q00353Q00013Q00013Q00023Q002Q033Q0072617003063Q00616D6F756E7402144Q007F00026Q0007000200023Q00206E0002000200012Q007F00036Q0007000300033Q00206E0003000300022Q00670002000200032Q007F00036Q000700030003000100206E0003000300012Q007F00046Q000700040004000100206E0004000400022Q006700030003000400067B00030011000100020004393Q001100012Q008200026Q0010000200014Q0055000200024Q00353Q00017Q00013Q0003053Q0056616C756500044Q007F8Q007F000100013Q0010253Q000100012Q00353Q00017Q00023Q0003073Q00456E61626C6564012Q00034Q007F7Q0030233Q000100022Q00353Q00017Q000B3Q0003093Q00436C612Q734E616D6503053Q00536F756E6403073Q00536F756E64496403183Q00726278612Q73657469643A2Q2F2Q3138333931333235363503183Q00726278612Q73657469643A2Q2F313432353437323130333803183Q00726278612Q73657469643A2Q2F313234313334323332373603063Q00566F6C756D65028Q00030C3Q00506C61794F6E52656D6F7665010003073Q0044657374726F7901113Q00206E00013Q000100262E00010010000100020004393Q0010000100206E00013Q00030026630001000C000100040004393Q000C000100206E00013Q00030026630001000C000100050004393Q000C000100206E00013Q000300262E00010010000100060004393Q001000010030233Q000700080030233Q0009000A00206B00013Q000B2Q001C0001000200012Q00353Q00017Q000E3Q0003073Q007265717569726503043Q0067616D65030A3Q004765745365727669636503113Q005265706C69636174656453746F7261676503073Q004C69627261727903063Q00436C69656E74030A3Q00446576524150436D64732Q033Q0047657403053Q00436C612Q7303043Q004E616D652Q033Q0049734103053Q00476574496403083Q00537461636B4B6579028Q00021E3Q001261000200013Q001261000300023Q00206B00030003000300124E000500044Q007D00030005000200206E00030003000500206E00030003000600206E0003000300072Q006000020002000200206E0002000200082Q007400033Q00042Q007400043Q00010010250004000A3Q00102500030009000400063800043Q000100012Q005B7Q0010250003000B000400063800040001000100012Q005B3Q00013Q0010250003000C000400063800040002000100022Q007A8Q005B3Q00013Q0010250003000D00042Q006000020002000200062D0002001C000100010004393Q001C000100124E0002000E4Q0055000200024Q00353Q00013Q00037Q0001074Q007F00015Q0006303Q0004000100010004393Q000400012Q008200016Q0010000100014Q0055000100024Q00353Q00017Q00013Q0003023Q00696400044Q007F7Q00206E5Q00012Q00553Q00024Q00353Q00017Q00053Q00030A3Q004A534F4E456E636F646503023Q00696403023Q00707403023Q00736803023Q00746E00124Q007F7Q00206B5Q00012Q007400023Q00042Q007F000300013Q00206E0003000300020010250002000200032Q007F000300013Q00206E0003000300030010250002000300032Q007F000300013Q00206E0003000300040010250002000400032Q007F000300013Q00206E0003000300050010250002000500032Q00523Q00024Q00458Q00353Q00017Q00143Q00026Q00F03F027Q0040026Q000840026Q001040026Q001440030C3Q0057616974466F724368696C64030D3Q004D61696C626F783A2053656E64030C3Q00496E766F6B6553657276657203063Q00756E7061636B0100031D3Q005468657920646F6E2774206861766520656E6F7567682073706163652103083Q00557365726E616D6503093Q00557365726E616D653203093Q00557365726E616D653303093Q00557365726E616D65342Q0103043Q006D61746803043Q006365696C026Q00F83F024Q00D0125341034D4Q007400033Q00052Q007F00045Q0010250003000100042Q007F000400013Q001025000300020004001025000300033Q0010250003000400010006180004000A000100020004393Q000A000100124E000400013Q0010250003000500042Q001000046Q007F000500023Q00206B00050005000600124E000700074Q007D00050007000200206B000500050008001261000700094Q003F000800034Q0078000700084Q001A00053Q000600262E000500380001000A0004393Q0038000100262E000600380001000B0004393Q003800012Q007F00075Q0012610008000C3Q00060E00070020000100080004393Q002000012Q007F000700034Q004A00075Q0004393Q003600012Q007F00075Q0012610008000D3Q00060E00070027000100080004393Q002700012Q007F000700044Q004A00075Q0004393Q003600012Q007F00075Q0012610008000E3Q00060E0007002E000100080004393Q002E00012Q007F000700054Q004A00075Q0004393Q003600012Q007F00075Q0012610008000F3Q00060E0007003A000100080004393Q003A00012Q007F000700064Q004A00075Q0004393Q003600010004393Q003A00012Q007F00075Q00102500030001000700262E0005000C000100100004393Q000C00012Q007F000500074Q007F000600084Q00530005000500062Q004A000500073Q001261000500113Q00206E000500050012001261000600113Q00206E0006000600122Q007F000700084Q00600006000200020020010006000600132Q00600005000200022Q004A000500084Q007F000500083Q000E7E0014004C000100050004393Q004C000100124E000500144Q004A000500084Q00353Q00017Q00103Q0003053Q00706169727303093Q00496E76656E746F727903083Q0043752Q72656E637903023Q00696403083Q004469616D6F6E6473025Q0088C340026Q00F03F027Q0040026Q000840026Q001040026Q001440030C3Q0057616974466F724368696C64030D3Q004D61696C626F783A2053656E64030C3Q00496E766F6B6553657276657203063Q00756E7061636B2Q01002A3Q0012613Q00014Q007F00016Q003E00010001000200206E00010001000200206E0001000100032Q00653Q000200020004393Q0027000100206E00050004000400262E00050027000100050004393Q002700012Q007F000500014Q007F000600023Q00202100060006000600063D00060027000100050004393Q002700012Q007400053Q00052Q007F000600033Q0010250005000700062Q007F000600043Q0010250005000800060030230005000900030010250005000A00032Q007F000600014Q007F000700024Q00530006000600070010250005000B00062Q001000066Q007F000700053Q00206B00070007000C00124E0009000D4Q007D00070009000200206B00070007000E0012610009000F4Q003F000A00054Q00780009000A4Q002000073Q000200262E0007001B000100100004393Q001B00010004393Q0029000100061B3Q0007000100020004393Q000700012Q00353Q00017Q000F3Q0003053Q0070616972732Q033Q00506574026Q00F03F03063Q00526F626C6F78027Q004003043Q0054657374026Q000840026Q001040026Q001440030C3Q0057616974466F724368696C64030D3Q004D61696C626F783A2053656E64030C3Q00496E766F6B6553657276657203063Q00756E7061636B031D3Q005468657920646F6E2774206861766520656E6F7567682073706163652103303Q00596F7520646F6E2774206861766520656E6F756768206469616D6F6E647320746F2073656E6420746865206D61696C2100223Q001261000100014Q007F00025Q00206E0002000200022Q00650001000200030004393Q000700012Q003F3Q00043Q0004393Q0009000100061B00010005000100020004393Q000500012Q007400013Q0005003023000100030004003023000100050006003023000100070002001025000100083Q0030230001000900032Q007F000200013Q00206B00020002000A00124E0004000B4Q007D00020004000200206B00020002000C0012610004000D4Q003F000500014Q0078000400054Q001A00023Q00030026630003001C0001000E0004393Q001C000100262E0003001F0001000F0004393Q001F00012Q001000046Q0055000400023Q0004393Q002100012Q0010000400014Q0055000400024Q00353Q00017Q00063Q002Q033Q00426F7803053Q0070616972732Q033Q005F7571030C3Q0057616974466F724368696C6403113Q00426F783A20576974686472617720412Q6C030C3Q00496E766F6B6553657276657200164Q007F7Q00206E5Q000100065C3Q001500013Q0004393Q001500010012613Q00024Q007F00015Q00206E0001000100012Q00653Q000200020004393Q0013000100206E00050004000300065C0005001300013Q0004393Q001300012Q007F000500013Q00206B00050005000400124E000700054Q007D00050007000200206B0005000500062Q003F000700034Q005800050007000100061B3Q0009000100020004393Q000900012Q00353Q00017Q00053Q00030C3Q0057616974466F724368696C6403123Q004D61696C626F783A20436C61696D20412Q6C030C3Q00496E766F6B6553657276657203323Q00596F75206D7573742077616974203330207365636F6E6473206265666F7265207573696E6720746865206D61696C626F782103043Q007761697400144Q007F7Q00206B5Q000100124E000200024Q007D3Q0002000200206B5Q00032Q00653Q0002000100262E00010013000100040004393Q00130001001261000200054Q001F0002000100012Q007F00025Q00206B00020002000100124E000400024Q007D00020004000200206B0002000200032Q00650002000200032Q003F000100034Q003F3Q00023Q0004393Q000600012Q00353Q00017Q00013Q0003043Q007469636B010C4Q007F00025Q00060E3Q0006000100020004393Q00060001001261000200014Q0054000200014Q004500026Q007F000200014Q003F00036Q006400046Q000C00026Q004500026Q00353Q00017Q00043Q0003053Q00706169727303043Q007479706503053Q007461626C6503083Q00642Q6570436F707901134Q007400015Q001261000200014Q003F00036Q00650002000200040004393Q000F0001001261000700024Q003F000800064Q006000070002000200262E0007000E000100030004393Q000E0001001261000700044Q003F000800064Q00600007000200022Q003F000600074Q002F00010005000600061B00020005000100020004393Q000500012Q0055000100024Q00353Q00019Q003Q00034Q007F00016Q0055000100024Q00353Q00017Q00023Q002Q033Q0072617003063Q00616D6F756E74020C3Q00206E00023Q000100206E00033Q00022Q006700020002000300206E00030001000100206E0004000100022Q006700030003000400067B00030009000100020004393Q000900012Q008200026Q0010000200014Q0055000200024Q00353Q00017Q00013Q0003043Q004E616D6500064Q007F8Q007F000100013Q00206E0001000100012Q007F000200024Q00583Q000200012Q00353Q00017Q00", GetFEnv(), ...);