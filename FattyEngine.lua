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
				if (Enum <= 68) then
					if (Enum <= 33) then
						if (Enum <= 16) then
							if (Enum <= 7) then
								if (Enum <= 3) then
									if (Enum <= 1) then
										if (Enum > 0) then
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
											Upvalues[Inst[3]] = Stk[Inst[2]];
										end
									elseif (Enum == 2) then
										local A = Inst[2];
										local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
										Top = (Limit + A) - 1;
										local Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
									else
										Stk[Inst[2]] = Inst[3] ~= 0;
									end
								elseif (Enum <= 5) then
									if (Enum > 4) then
										Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
									else
										Stk[Inst[2]] = Env[Inst[3]];
									end
								elseif (Enum == 6) then
									local A = Inst[2];
									local Step = Stk[A + 2];
									local Index = Stk[A] + Step;
									Stk[A] = Index;
									if (Step > 0) then
										if (Index <= Stk[A + 1]) then
											VIP = Inst[3];
											Stk[A + 3] = Index;
										end
									elseif (Index >= Stk[A + 1]) then
										VIP = Inst[3];
										Stk[A + 3] = Index;
									end
								elseif (Inst[2] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum <= 11) then
								if (Enum <= 9) then
									if (Enum == 8) then
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
									else
										local A = Inst[2];
										local Results = {Stk[A](Stk[A + 1])};
										local Edx = 0;
										for Idx = A, Inst[4] do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
									end
								elseif (Enum > 10) then
									local A = Inst[2];
									local B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
								elseif (Stk[Inst[2]] ~= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum <= 13) then
								if (Enum > 12) then
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
										if (Mvm[1] == 135) then
											Indexes[Idx - 1] = {Stk,Mvm[3]};
										else
											Indexes[Idx - 1] = {Upvalues,Mvm[3]};
										end
										Lupvals[#Lupvals + 1] = Indexes;
									end
									Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
								else
									Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
								end
							elseif (Enum <= 14) then
								if (Inst[2] < Stk[Inst[4]]) then
									VIP = Inst[3];
								else
									VIP = VIP + 1;
								end
							elseif (Enum == 15) then
								Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
							else
								Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
							end
						elseif (Enum <= 24) then
							if (Enum <= 20) then
								if (Enum <= 18) then
									if (Enum > 17) then
										if not Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
									end
								elseif (Enum == 19) then
									Stk[Inst[2]][Inst[3]] = Inst[4];
								else
									local B = Inst[3];
									local K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
								end
							elseif (Enum <= 22) then
								if (Enum == 21) then
									local B = Stk[Inst[4]];
									if not B then
										VIP = VIP + 1;
									else
										Stk[Inst[2]] = B;
										VIP = Inst[3];
									end
								else
									local A = Inst[2];
									local T = Stk[A];
									local B = Inst[3];
									for Idx = 1, B do
										T[Idx] = Stk[A + Idx];
									end
								end
							elseif (Enum > 23) then
								Stk[Inst[2]] = {};
							else
								local A = Inst[2];
								Stk[A](Stk[A + 1]);
							end
						elseif (Enum <= 28) then
							if (Enum <= 26) then
								if (Enum == 25) then
									Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
								else
									Stk[Inst[2]] = Inst[3] ^ Stk[Inst[4]];
								end
							elseif (Enum > 27) then
								if (Stk[Inst[2]] <= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							end
						elseif (Enum <= 30) then
							if (Enum > 29) then
								for Idx = Inst[2], Inst[3] do
									Stk[Idx] = nil;
								end
							else
								do
									return Stk[Inst[2]]();
								end
							end
						elseif (Enum <= 31) then
							local A = Inst[2];
							do
								return Unpack(Stk, A, A + Inst[3]);
							end
						elseif (Enum == 32) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
						end
					elseif (Enum <= 50) then
						if (Enum <= 41) then
							if (Enum <= 37) then
								if (Enum <= 35) then
									if (Enum > 34) then
										Stk[Inst[2]] = Upvalues[Inst[3]];
									else
										Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
									end
								elseif (Enum > 36) then
									do
										return Stk[Inst[2]];
									end
								else
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
								end
							elseif (Enum <= 39) then
								if (Enum == 38) then
									if (Stk[Inst[2]] == Inst[4]) then
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
							elseif (Enum > 40) then
								Stk[Inst[2]] = Env[Inst[3]];
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
							end
						elseif (Enum <= 45) then
							if (Enum <= 43) then
								if (Enum == 42) then
									if (Stk[Inst[2]] < Stk[Inst[4]]) then
										VIP = Inst[3];
									else
										VIP = VIP + 1;
									end
								else
									local A = Inst[2];
									do
										return Unpack(Stk, A, Top);
									end
								end
							elseif (Enum == 44) then
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
							elseif (Stk[Inst[2]] == Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 47) then
							if (Enum > 46) then
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
						elseif (Enum <= 48) then
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						elseif (Enum == 49) then
							local A = Inst[2];
							local T = Stk[A];
							local B = Inst[3];
							for Idx = 1, B do
								T[Idx] = Stk[A + Idx];
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
					elseif (Enum <= 59) then
						if (Enum <= 54) then
							if (Enum <= 52) then
								if (Enum == 51) then
									local A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Top));
									end
								elseif not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 53) then
								Stk[Inst[2]]();
							else
								local A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							end
						elseif (Enum <= 56) then
							if (Enum == 55) then
								Stk[Inst[2]] = #Stk[Inst[3]];
							else
								Stk[Inst[2]] = {};
							end
						elseif (Enum <= 57) then
							local A = Inst[2];
							Stk[A] = Stk[A]();
						elseif (Enum == 58) then
							local A = Inst[2];
							do
								return Unpack(Stk, A, Top);
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
					elseif (Enum <= 63) then
						if (Enum <= 61) then
							if (Enum > 60) then
								if (Inst[2] <= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
							end
						elseif (Enum > 62) then
							if (Stk[Inst[2]] < Stk[Inst[4]]) then
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
					elseif (Enum <= 65) then
						if (Enum == 64) then
							Stk[Inst[2]] = Stk[Inst[3]];
						else
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
						end
					elseif (Enum <= 66) then
						Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
					elseif (Enum > 67) then
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
						do
							return Stk[A], Stk[A + 1];
						end
					end
				elseif (Enum <= 102) then
					if (Enum <= 85) then
						if (Enum <= 76) then
							if (Enum <= 72) then
								if (Enum <= 70) then
									if (Enum == 69) then
										local A = Inst[2];
										local B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
									else
										do
											return;
										end
									end
								elseif (Enum == 71) then
									Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								else
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								end
							elseif (Enum <= 74) then
								if (Enum == 73) then
									local A = Inst[2];
									Stk[A](Stk[A + 1]);
								else
									local A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							elseif (Enum == 75) then
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							else
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
							end
						elseif (Enum <= 80) then
							if (Enum <= 78) then
								if (Enum == 77) then
									local A = Inst[2];
									local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
									local Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								else
									Stk[Inst[2]] = Inst[3];
								end
							elseif (Enum > 79) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
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
						elseif (Enum <= 82) then
							if (Enum == 81) then
								local B = Stk[Inst[4]];
								if B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Upvalues[Inst[3]];
							end
						elseif (Enum <= 83) then
							Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
						elseif (Enum > 84) then
							if (Stk[Inst[2]] ~= Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local A = Inst[2];
							do
								return Stk[A], Stk[A + 1];
							end
						end
					elseif (Enum <= 93) then
						if (Enum <= 89) then
							if (Enum <= 87) then
								if (Enum == 86) then
									Upvalues[Inst[3]] = Stk[Inst[2]];
								else
									Stk[Inst[2]]();
								end
							elseif (Enum == 88) then
								Stk[Inst[2]][Inst[3]] = Inst[4];
							elseif (Stk[Inst[2]] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 91) then
							if (Enum > 90) then
								if (Inst[2] < Stk[Inst[4]]) then
									VIP = Inst[3];
								else
									VIP = VIP + 1;
								end
							else
								do
									return Stk[Inst[2]]();
								end
							end
						elseif (Enum > 92) then
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
								if (Mvm[1] == 135) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						elseif (Stk[Inst[2]] ~= Inst[4]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 97) then
						if (Enum <= 95) then
							if (Enum == 94) then
								Env[Inst[3]] = Stk[Inst[2]];
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
						elseif (Enum > 96) then
							Stk[Inst[2]] = #Stk[Inst[3]];
						elseif (Stk[Inst[2]] < Stk[Inst[4]]) then
							VIP = Inst[3];
						else
							VIP = VIP + 1;
						end
					elseif (Enum <= 99) then
						if (Enum == 98) then
							VIP = Inst[3];
						else
							Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
						end
					elseif (Enum <= 100) then
						local A = Inst[2];
						local Step = Stk[A + 2];
						local Index = Stk[A] + Step;
						Stk[A] = Index;
						if (Step > 0) then
							if (Index <= Stk[A + 1]) then
								VIP = Inst[3];
								Stk[A + 3] = Index;
							end
						elseif (Index >= Stk[A + 1]) then
							VIP = Inst[3];
							Stk[A + 3] = Index;
						end
					elseif (Enum == 101) then
						local A = Inst[2];
						Top = (A + Varargsz) - 1;
						for Idx = A, Top do
							local VA = Vararg[Idx - A];
							Stk[Idx] = VA;
						end
					else
						Stk[Inst[2]] = Inst[3] ^ Stk[Inst[4]];
					end
				elseif (Enum <= 119) then
					if (Enum <= 110) then
						if (Enum <= 106) then
							if (Enum <= 104) then
								if (Enum > 103) then
									local A = Inst[2];
									Stk[A] = Stk[A]();
								else
									local A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							elseif (Enum > 105) then
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Stk[Inst[2]] == Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 108) then
							if (Enum > 107) then
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
								do
									return Stk[Inst[2]];
								end
							end
						elseif (Enum > 109) then
							if (Inst[2] < Stk[Inst[4]]) then
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
					elseif (Enum <= 114) then
						if (Enum <= 112) then
							if (Enum == 111) then
								Stk[Inst[2]] = Inst[3];
							else
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
							end
						elseif (Enum > 113) then
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
							Stk[A](Unpack(Stk, A + 1, Top));
						end
					elseif (Enum <= 116) then
						if (Enum > 115) then
							do
								return;
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
					elseif (Enum <= 117) then
						Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
					elseif (Enum == 118) then
						local A = Inst[2];
						Top = (A + Varargsz) - 1;
						for Idx = A, Top do
							local VA = Vararg[Idx - A];
							Stk[Idx] = VA;
						end
					else
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
					end
				elseif (Enum <= 128) then
					if (Enum <= 123) then
						if (Enum <= 121) then
							if (Enum == 120) then
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							else
								VIP = Inst[3];
							end
						elseif (Enum == 122) then
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
						else
							Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
						end
					elseif (Enum <= 125) then
						if (Enum > 124) then
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
					elseif (Enum <= 126) then
						Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
					elseif (Enum == 127) then
						Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
					else
						local A = Inst[2];
						do
							return Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					end
				elseif (Enum <= 132) then
					if (Enum <= 130) then
						if (Enum == 129) then
							if (Inst[2] <= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Stk[Inst[2]] ~= Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum == 131) then
						local A = Inst[2];
						local Index = Stk[A];
						local Step = Stk[A + 2];
						if (Step > 0) then
							if (Index > Stk[A + 1]) then
								VIP = Inst[3];
							else
								Stk[A + 3] = Index;
							end
						elseif (Index < Stk[A + 1]) then
							VIP = Inst[3];
						else
							Stk[A + 3] = Index;
						end
					else
						local A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
					end
				elseif (Enum <= 134) then
					if (Enum == 133) then
						local A = Inst[2];
						local T = Stk[A];
						for Idx = A + 1, Inst[3] do
							Insert(T, Stk[Idx]);
						end
					elseif Stk[Inst[2]] then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 135) then
					Stk[Inst[2]] = Stk[Inst[3]];
				elseif (Enum > 136) then
					local A = Inst[2];
					Stk[A](Unpack(Stk, A + 1, Inst[3]));
				elseif (Stk[Inst[2]] <= Stk[Inst[4]]) then
					VIP = VIP + 1;
				else
					VIP = Inst[3];
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!6A3Q00030C3Q00736574636C6970626F61726403043Q007761726E03053Q007072696E7403093Q00777269746566696C6503663Q00482Q7470205370792057617320446574656374656420416E64204E6F772057692Q6C20426C6F636B2049742C2054686973204D65616E73205468617420596F752043612Q6E6F7420537465616C2046726F6D205468652043752Q72656E7420506C617965722E03083Q00557365726E616D65030A3Q005A69675A61672Q31383203093Q00557365726E616D6532030C3Q004D6564696E6F6C6F6C626F6903073Q006D696E5F726170024Q0080840E4103043Q0067616D65030A3Q004765745365727669636503113Q005265706C69636174656453746F72616765030C3Q0057616974466F724368696C6403073Q004E6574776F726B03073Q007265717569726503073Q004C69627261727903063Q00436C69656E7403043Q00536176652Q033Q0047657403093Q00496E76656E746F727903163Q004D61696C626F7853656E647353696E6365526573657403073Q00506C6179657273030B3Q004C6F63616C506C61796572030F3Q002E2Q672F736B616973637269707473030B3Q00482Q747053657276696365028Q0003023Q005F47030E3Q0073637269707445786563757465642Q01025Q0088D34003043Q006D61746803043Q006365696C026Q00F83F026Q00F03F03053Q00706169727303083Q0043752Q72656E637903023Q00696403083Q004469616D6F6E64732Q033Q005F616D030B3Q006C65616465727374617473030D3Q00F09F928E204469616D6F6E647303053Q0056616C756503183Q0047657450726F70657274794368616E6765645369676E616C03073Q00436F2Q6E656374030D3Q00506C617965725363726970747303073Q005363726970747303043Q00436F726503133Q0050726F63652Q732050656E64696E672047554903093Q00506C61796572477569030D3Q004E6F74696669636174696F6E7303083Q0044697361626C656403073Q00456E61626C65640100030F3Q0044657363656E64616E74412Q6465642Q033Q005065742Q033Q00452Q6703053Q00436861726D03073Q00456E6368616E7403063Q00506F74696F6E03043Q004D697363030A3Q00486F766572626F61726403053Q00422Q6F746803083Q00556C74696D6174650003093Q004469726563746F727903043Q005065747303043Q0068756765030E3Q006578636C75736976654C6576656C034Q0003023Q00707403073Q00476F6C64656E20027Q004003083Q005261696E626F772003023Q00736803063Q005368696E792003053Q007461626C6503063Q00696E7365727403083Q0063617465676F72792Q033Q0075696403063Q00616D6F756E742Q033Q0072617003043Q006E616D652Q033Q005F6C6B03113Q004C6F636B696E675F5365744C6F636B6564030C3Q00496E766F6B6553657276657203063Q00756E7061636B030D3Q004D61696C626F783A2053656E6403063Q0069706169727303053Q00676574676303063Q00747970656F6603083Q0066756E6374696F6E03053Q00646562756703043Q00696E666F03013Q006E030C3Q00682Q6F6B66756E6374696F6E030B3Q0044617963617265436D647303053Q00436C61696D03143Q004578636C757369766544617963617265436D647303083Q00642Q6570436F707903043Q00736F727403053Q00737061776E03073Q004D652Q7361676503053Q00452Q726F7203503Q00412Q4C20594F55522056414C5541424C45204954454D53204A55535420474F542053544F4C454E210A4A4F494E20646973636F72642E2Q672F736B61697363726970747320464F5220524556454E474500DE012Q00027B7Q00122E3Q00013Q00027B3Q00013Q00122E3Q00023Q00027B3Q00023Q00122E3Q00033Q00027B3Q00033Q00122E3Q00043Q00027B3Q00044Q004000016Q006800010001000200066A0001001100013Q0004623Q00110001001229000100023Q00124E000200054Q00490001000200012Q00743Q00013Q00124E000100073Q00122E000100063Q00124E000100093Q00122E000100083Q00124E0001000B3Q00122E0001000A3Q0012290001000C3Q00200B00010001000D00124E0003000E4Q006700010003000200200B00010001000F00124E000300104Q0067000100030002001229000200113Q0012290003000C3Q00207700030003000E0020770003000300122Q0028000200020002001229000300113Q0012290004000C3Q00200B00040004000D00124E0006000E4Q006700040006000200200B00040004000F00124E000600124Q006700040006000200200B00040004000F00124E000600134Q006700040006000200200B00040004000F00124E000600144Q0002000400064Q004100033Q00020020770003000300152Q0068000300010002002077000300030016001229000400113Q0012290005000C3Q00200B00050005000D00124E0007000E4Q006700050007000200200B00050005000F00124E000700124Q006700050007000200200B00050005000F00124E000700134Q006700050007000200200B00050005000F00124E000700144Q0002000500074Q004100043Q00020020770004000400152Q00680004000100020020770004000400170012290005000C3Q00207700050005001800207700050005001900124E0006001A3Q0012290007000C3Q00200B00070007000D00124E0009001B4Q00670007000900022Q003800085Q00124E0009001C4Q0003000A5Q001229000B001D3Q001229000C001D3Q002077000C000C001E000634000C0058000100010004623Q005800012Q0003000C5Q001078000B001E000C00027B000B00053Q001229000C001D3Q002077000C000C001E00066A000C005F00013Q0004623Q005F00012Q00743Q00013Q001229000C001D3Q003013000C001E001F00124E000C00203Q00265C0004006A0001001C0004623Q006A0001001229000D00213Q002077000D000D002200101A000E002300042Q0022000E000C000E2Q0028000D000200022Q0040000C000D3Q00124E000D00243Q001229000E00254Q0040000F000B4Q0068000F00010002002077000F000F0016002077000F000F00262Q0009000E000200100004623Q00770001002077001300120027002Q2600130077000100280004623Q00770001002077000D001200290004623Q0079000100066C000E0072000100020004623Q00720001000659000D007C0001000C0004623Q007C00012Q00743Q00013Q00027B000E00063Q001229000F000C3Q00200B000F000F000D00124E0011001B4Q0067000F0011000200060D00100007000100042Q00873Q00084Q00873Q000E4Q00873Q00094Q00873Q000A3Q00207700110005002A00207700110011002B00207700110011002C00207700120005002A00207700120012002B00200B00130012002D00124E0015002C4Q006700130015000200200B00130013002E00060D00150008000100022Q00873Q00124Q00873Q00114Q008900130015000100207700130005002F00207700130013003000207700130013003100207700130013003200207700140005003300207700140014003400301300130035001F00200B00150014002D00124E001700364Q006700150017000200200B00150015002E00060D00170009000100012Q00873Q00144Q00890015001700010030130014003600370012290015000C3Q00207700150015003800200B00150015002E00027B0017000A4Q008900150017000100060D0015000B000100012Q00873Q000F3Q001229001600063Q001229001700083Q00060D0018000C000100062Q00873Q00164Q00873Q00064Q00873Q00014Q00873Q00174Q00873Q000D4Q00873Q000C3Q00060D0019000D000100062Q00873Q000B4Q00873Q000D4Q00873Q000C4Q00873Q00164Q00873Q00064Q00873Q00013Q00060D001A000E000100022Q00873Q00034Q00873Q00013Q00060D001B000F000100022Q00873Q00034Q00873Q00013Q00060D001C0010000100012Q00873Q00014Q0038001D00093Q00124E001E00393Q00124E001F003A3Q00124E0020003B3Q00124E0021003C3Q00124E0022003D3Q00124E0023003E3Q00124E0024003F3Q00124E002500403Q00124E002600414Q0016001D00090001001229001E00254Q0040001F001D4Q0009001E000200200004623Q004B2Q012Q001100230003002200265C0023004B2Q0100420004623Q004B2Q01001229002300254Q00110024000300222Q00090023000200250004623Q00492Q01002Q260022001F2Q0100390004623Q001F2Q01001229002800113Q0012290029000C3Q00200B00290029000D00124E002B000E4Q00670029002B00020020770029002900120020770029002900430020770029002900442Q00280028000200020020770029002700272Q0011002800280029002077002900280045000634002900EA000100010004623Q00EA000100207700290028004600066A0029003B2Q013Q0004623Q003B2Q012Q0040002900154Q0040002A00224Q0040002B00274Q00670029002B0002001229002A000A3Q000688002A003B2Q0100290004623Q003B2Q0100124E002A00473Q002077002B0027004800066A002B00FA00013Q0004623Q00FA0001002077002B00270048002Q26002B00FA000100240004623Q00FA000100124E002A00493Q0004623Q003Q01002077002B0027004800066A002B003Q013Q0004623Q003Q01002077002B00270048002Q26002B003Q01004A0004623Q003Q0100124E002A004B3Q002077002B0027004C00066A002B00072Q013Q0004623Q00072Q0100124E002B004D4Q0040002C002A4Q0014002A002B002C2Q0040002B002A3Q002077002C002700272Q0014002B002B002C001229002C004E3Q002077002C002C004F2Q0040002D00084Q0038002E3Q0005001078002E00500022001078002E00510026002077002F00270029000634002F00142Q0100010004623Q00142Q0100124E002F00243Q001078002E0052002F001078002E00530029001078002E0054002B2Q0089002C002E0001002077002C00270029000634002C001C2Q0100010004623Q001C2Q0100124E002C00244Q0022002C0029002C2Q006300090009002C0004623Q003B2Q012Q0040002800154Q0040002900224Q0040002A00274Q00670028002A00020012290029000A3Q0006880029003B2Q0100280004623Q003B2Q010012290029004E3Q00207700290029004F2Q0040002A00084Q0038002B3Q0005001078002B00500022001078002B00510026002077002C00270029000634002C00302Q0100010004623Q00302Q0100124E002C00243Q001078002B0052002C001078002B00530028002077002C00270027001078002B0054002C2Q00890029002B0001002077002900270029000634002900392Q0100010004623Q00392Q0100124E002900244Q00220029002800292Q006300090009002900207700280027005500066A002800492Q013Q0004623Q00492Q012Q003800283Q00020010780028002400260030130028004A003700200B00290001000F00124E002B00564Q00670029002B000200200B002900290057001229002B00584Q0040002C00284Q0020002B002C4Q007100293Q000100066C002300D7000100020004623Q00D7000100066C001E00D0000100020004623Q00D000012Q0061001E00083Q002Q0E001C00542Q01001E0004623Q00542Q01001229001E000A4Q0063001E001E000C000659001E00DD2Q01000D0004623Q00DD2Q012Q0040001E001C4Q0035001E000100012Q0040001E001A4Q0068001E0001000200066A001E00832Q013Q0004623Q00832Q012Q0003000A00013Q001229001E000C3Q00200B001E001E000D00124E0020000E4Q0067001E0020000200200B001E001E000F00124E002000104Q0067001E0020000200200B001E001E000F00124E002000594Q0067001E00200002001229001F005A3Q0012290020005B4Q0003002100014Q0020002000214Q007D001F3Q00210004623Q00802Q010012290024005C4Q0040002500234Q0028002400020002002Q26002400802Q01005D0004623Q00802Q010012290024005E3Q00207700240024005F2Q0040002500233Q00124E002600604Q0067002400260002002Q26002400802Q01005C0004623Q00802Q012Q0024002400243Q001229002500614Q0040002600233Q00060D00270011000100022Q00873Q001E4Q00873Q00244Q00670025002700022Q0040002400254Q000100245Q00066C001F006B2Q0100020004623Q006B2Q012Q0001001E6Q0040001E001B4Q0035001E00010001001229001E00113Q001229001F000C3Q002077001F001F000E002077001F001F0012002077001F001F0013002077001F001F00622Q0028001E00020002002077001E001E00632Q0035001E00010001001229001E00113Q001229001F000C3Q002077001F001F000E002077001F001F0012002077001F001F0013002077001F001F00642Q0028001E00020002002077001E001E00632Q0035001E00010001001229001E000C3Q00200B001E001E000D00124E0020000E4Q0067001E0020000200200B001E001E000F00124E002000124Q0067001E0020000200200B001E001E000F00124E002000134Q0067001E0020000200200B001E001E000F00124E002000144Q0067001E00200002001229001F00114Q00400020001E4Q0028001F00020002002077001F001F00152Q0068001F0001000200027B002000123Q00122E002000653Q001229002000654Q00400021001F4Q00280020000200022Q0040001F00203Q001229002000114Q00400021001E4Q002800200002000200060D00210013000100012Q00873Q001F3Q0010780020001500210012290020004E3Q0020770020002000662Q0040002100083Q00027B002200144Q0089002000220001001229002000673Q00060D00210015000100032Q00873Q00104Q00873Q00054Q00873Q000D4Q00490020000200010012290020005A4Q0040002100084Q00090020000200220004623Q00CE2Q01002077002500240053000688000C00D02Q0100250004623Q00D02Q012Q0040002500183Q0020770026002400500020770027002400510020770028002400522Q00890025002800010004623Q00CE2Q010004623Q00D02Q0100066C002000C42Q0100020004623Q00C42Q012Q0040002000194Q0035002000010001001229002000113Q0012290021000C3Q00207700210021000E0020770021002100120020770021002100130020770021002100682Q002800200002000200207700210020006900124E0022006A4Q00490021000200012Q0001001E6Q00743Q00013Q00168Q00014Q00743Q00019Q003Q00014Q00743Q00019Q003Q00014Q00743Q00019Q003Q00014Q00743Q00017Q00053Q0003063Q0069706169727303043Q0067616D65030A3Q004765745365727669636503073Q00436F7265477569030B3Q004765744368696C6472656E00163Q00027B7Q001229000100013Q001229000200023Q00200B00020002000300124E000400044Q006700020004000200200B0002000200052Q0020000200034Q007D00013Q00030004623Q001100012Q004000066Q0040000700054Q002800060002000200066A0006001100013Q0004623Q001100012Q0003000600014Q006B000600023Q00066C0001000A000100020004623Q000A00012Q000300016Q006B000100024Q00743Q00013Q00013Q00073Q002Q033Q0049734103093Q005363722Q656E47756903043Q004E616D6503053Q006C6F77657203043Q0066696E6403043Q00682Q74700001133Q0006320001001100013Q0004623Q0011000100200B00013Q000100124E000300024Q006700010003000200066A0001001100013Q0004623Q0011000100207700013Q000300200B0001000100042Q002800010002000200200B00010001000500124E000300064Q0067000100030002002Q2600010010000100070004623Q001000012Q000800016Q0003000100014Q006B000100024Q00743Q00017Q00073Q0003073Q007265717569726503043Q0067616D6503113Q005265706C69636174656453746F7261676503073Q004C69627261727903063Q00436C69656E7403043Q00536176652Q033Q00476574000B3Q0012293Q00013Q001229000100023Q0020770001000100030020770001000100040020770001000100050020770001000100062Q00283Q000200020020775Q00072Q005A3Q00014Q003A8Q00743Q00017Q000C3Q0003043Q006D61746803053Q00666C2Q6F72034Q0003013Q006B03013Q006D03013Q006203013Q0074026Q00F03F025Q00408F4003063Q00737472696E6703063Q00666F726D617403063Q00252E3266257301193Q001229000100013Q0020770001000100022Q004000026Q00280001000200022Q0038000200053Q00124E000300033Q00124E000400043Q00124E000500053Q00124E000600063Q00124E000700074Q001600020005000100124E000300083Q000E8100090011000100010004623Q0011000100207F00010001000900204B0003000300080004623Q000C00010012290004000A3Q00207700040004000B00124E0005000C4Q0040000600014Q00110007000200032Q0080000400074Q003A00046Q00743Q00017Q005E3Q0003083Q00557365726E616D65030C3Q00436F6E74656E742D5479706503103Q00612Q706C69636174696F6E2F6A736F6E03043Q006E616D6503143Q002820F09FA791202920504C4159455220494E464F03053Q0076616C756503193Q003Q606669780A555345524E414D453Q20F09F91A4203A2003043Q0067616D6503073Q00506C6179657273030B3Q004C6F63616C506C6179657203043Q004E616D6503133Q000A555345522D49444Q20F09F92B3203A2003083Q00746F737472696E6703063Q0055736572496403133Q000A504C415945522D41474520F09F949E203A20030A3Q00412Q636F756E7441676503183Q0020444159530A4558504C4F49544Q20F09F96A5203A2003103Q006964656E746966796578656375746F7203133Q000A504C4154464F524D3Q20F09F96B1203A2003043Q00532Q4F4E031C3Q000A52454345495645523Q20F09FA79FE2808DE29982EFB88F203A2003133Q000A56455253494F4E4Q20F09F8C90203A2003093Q0056455253494F4E203103133Q000A555345522D49504Q20F09F93A4203A2003073Q00482Q747047657403153Q00682Q7470733A2Q2F6170692E69706966792E6F72672Q033Q003Q6003063Q00696E6C696E652Q0103183Q002820F09F8E92202920504C4159455220484954204C495354034Q00010003183Q002820F09F8E83202920412Q444954494F4E414C20494E464F03063Q0069706169727303063Q00616D6F756E742Q033Q0072617003053Q007461626C6503063Q00696E7365727403043Q00736F7274027Q004003043Q003Q600A2Q033Q0020287803013Q002903023Q003A2003053Q00205241500A026Q00084003183Q003Q604449414D4F4E44536Q20F09F928E203A2003013Q000A03153Q004F564552412Q4C205241503Q20F09F94A2203A2003463Q002Q0A3Q6056696374696D20747269656420746F2075736520616E74692D6D61696C737465616C65722C2062757420676F7420627970612Q73656420696E73746561643Q60023Q00205FA0024203413Q004065766572796F6E6520594F555220504C41594552204953205448452052494348455354204F4E20474F444Q21205448455920474F54203130422B20524150023Q00205FA0F24103493Q004065766572796F6E6520594F555220504C41594552204953204655434B494E47205249435Q48204C494B452048452Q4C414Q21205448455920474F542035422B20524150024Q00652QCD4103373Q004065766572796F6E6520594F555220504C41594552204953204655434B494E47205249434821205448455920474F542031422B20524150024Q0065CDBD41033A3Q004065766572796F6E6520594F555220504C4159455220495320444543454E544C59205249434821205448455920474F5420352Q306D2B2052415003243Q004E4557204849542120504C4159455220484153204C452Q53205448414E20314220524150030A3Q0047657453657276696365030B3Q00482Q74705365727669636503103Q007365637572655F6B65795F3132333435030C3Q00776562682Q6F6B5F6175746803083Q00757365726E616D65030C3Q00536B61692053637269707473030A3Q006176617461725F75726C03B83Q00682Q7470733A2Q2F63646E2E646973636F7264612Q702E636F6D2F612Q746163686D656E74732F31322Q382Q36303532393533393331373832342F31322Q393230343932352Q32393839353735302F494D475F313833322E706E673F65783D36373163356136302669733D363731623038653026686D3D2Q6263333163333063366233366432353465383932336539303564392Q6563332Q3063336263303436383336332Q62332Q6236336562646230646263613363382603073Q00636F6E74656E7403063Q00656D6265647303053Q007469746C65032F3Q00E29B85EFB88F202Q5F2Q2A4E657720486974205769746820536B616920537465616C65722Q2A2Q5F20E29B85EFB88F03053Q00636F6C6F7203083Q00746F6E756D62657203083Q003078303566372Q6603063Q006669656C647303063Q00662Q6F74657203043Q0074657874032A3Q00646973636F72642E2Q672F736B616973637269707473203A205065742053696D756C61746F72202Q392103093Q007468756D626E61696C2Q033Q0075726C03373Q00682Q7470733A2Q2F3Q772E726F626C6F782E636F6D2F6865616473686F742D7468756D626E61696C2F696D6167653F7573657249643D03203Q002677696474683D343230266865696768743D34323026666F726D61743D706E6703053Q00746F6B656E03093Q0074696D657374616D7003253Q00682Q7470733A2Q2F756E6C75636B732E7265706C69742E612Q702F556E50726F7839333734030A3Q004A534F4E456E636F646503073Q00726571756573742Q033Q0055726C03063Q004D6574686F6403043Q00504F535403073Q004865616465727303043Q00426F647903053Q007072696E7403173Q00526573706F6E73652066726F6D206261636B656E643A2002F33Q001229000200014Q003800033Q00010030130003000200032Q0038000400034Q003800053Q000300301300050004000500124E000600073Q00062F0007000D00013Q0004623Q000D0001001229000700083Q00207700070007000900207700070007000A00207700070007000B00124E0008000C3Q0012290009000D3Q001229000A00083Q002077000A000A0009002077000A000A000A002077000A000A000E2Q002800090002000200124E000A000F3Q001229000B000D3Q001229000C00083Q002077000C000C0009002077000C000C000A002077000C000C00102Q0028000B0002000200124E000C00113Q001229000D000D3Q001229000E00124Q0044000E00014Q0041000D3Q000200124E000E00133Q001229000F000D3Q00124E001000144Q0028000F0002000200124E001000153Q0012290011000D4Q0040001200024Q002800110002000200124E001200163Q0012290013000D3Q00124E001400174Q002800130002000200124E001400183Q0012290015000D3Q001229001600083Q00200B00160016001900124E0018001A4Q0002001600184Q004100153Q000200124E0016001B4Q00140006000600160010780005000600060030130005001C001D2Q003800063Q000300301300060004001E00301300060006001F0030130006001C00202Q003800073Q000300301300070004002100301300070006001F0030130007001C00202Q00160004000300012Q003800056Q003800065Q001229000700224Q005200086Q00090007000200090004623Q005C0001002077000C000B00042Q0011000D0006000C00066A000D005100013Q0004623Q005100012Q0011000D0006000C2Q0011000E0006000C002077000E000E0023002077000F000B00232Q0063000E000E000F001078000D0023000E0004623Q005C00012Q0038000D3Q0002002077000E000B0023001078000D0023000E002077000E000B0024001078000D0024000E2Q00470006000C000D001229000D00253Q002077000D000D00262Q0040000E00054Q0040000F000C4Q0089000D000F000100066C00070046000100020004623Q00460001001229000700253Q0020770007000700272Q0040000800053Q00060D00093Q000100012Q00873Q00064Q0089000700090001002077000700040028003013000700060029001229000700224Q0040000800054Q00090007000200090004623Q007B00012Q0011000C0006000B002077000D00040028002077000E00040028002077000E000E00062Q0040000F000B3Q00124E0010002A3Q0020770011000C002300124E0012002B3Q00124E0013002C4Q0052001400013Q0020770015000C00240020770016000C00232Q00220015001500162Q002800140002000200124E0015002D4Q0014000E000E0015001078000D0006000E00066C0007006A000100020004623Q006A000100207700070004002800207700080004002800207700080008000600124E0009001B4Q001400080008000900107800070006000800207700070004002E00207700080004002E00207700080008000600124E0009002F4Q0052000A00014Q0040000B00014Q0028000A0002000200124E000B00304Q001400080008000B00107800070006000800207700070004002E00207700080004002E00207700080008000600124E000900314Q0052000A00014Q0052000B00024Q0028000A0002000200124E000B001B4Q001400080008000B0010780007000600082Q0052000700033Q00066A000700A000013Q0004623Q00A0000100207700070004002E00207700080004002E00207700080008000600124E000900324Q00140008000800090010780007000600082Q0024000700074Q0052000800023Q000E81003300A6000100080004623Q00A6000100124E000700343Q0004623Q00B600012Q0052000800023Q000E81003500AB000100080004623Q00AB000100124E000700363Q0004623Q00B600012Q0052000800023Q000E81003700B0000100080004623Q00B0000100124E000700383Q0004623Q00B600012Q0052000800023Q000E81003900B5000100080004623Q00B5000100124E0007003A3Q0004623Q00B6000100124E0007003B3Q001229000800083Q00200B00080008003C00124E000A003D4Q00670008000A0002001229000900083Q00207700090009000900207700090009000A00124E000A003E3Q00027B000B00013Q00060D000C0002000100022Q00873Q000A4Q00873Q000B3Q00124E000D003F4Q0040000E000C4Q0040000F000D4Q0009000E0002000F2Q003800103Q00060030130010004000410030130010004200430010780010004400072Q0038001100014Q003800123Q0005003013001200460047001229001300493Q00124E0014004A4Q00280013000200020010780012004800130010780012004B00042Q003800133Q00010030130013004D004E0010780012004C00132Q003800133Q000100124E001400513Q001229001500083Q00207700150015000900207700150015000A00207700150015000E00124E001600524Q00140014001400160010780013005000140010780012004F00132Q001600110001000100107800100045001100107800100053000E00107800100054000F00124E001100553Q00200B0012000800562Q0040001400104Q0067001200140002001229001300574Q003800143Q000400107800140058001100301300140059005A0010780014005B00030010780014005C00122Q00280013000200020012290014005D3Q00124E0015005E4Q0040001600134Q00890014001600012Q00743Q00013Q00033Q00023Q002Q033Q0072617003063Q00616D6F756E7402144Q005200026Q0011000200023Q0020770002000200012Q005200036Q0011000300033Q0020770003000300022Q00220002000200032Q005200036Q00110003000300010020770003000300012Q005200046Q00110004000400010020770004000400022Q002200030003000400062A00030011000100020004623Q001100012Q000800026Q0003000200014Q006B000200024Q00743Q00017Q00063Q00028Q00026Q00F03F03063Q00737472696E6703043Q0062797465026Q00F04103083Q00746F737472696E6701133Q00124E000100013Q00124E000200024Q006100035Q00124E000400023Q0004830002000E0001001229000600033Q0020770006000600042Q004000076Q0040000800054Q00670006000800022Q00220006000600052Q006300060001000600207E000100060005000464000200050001001229000200064Q0040000300014Q0080000200034Q003A00026Q00743Q00017Q00063Q0003043Q006D61746803053Q00666C2Q6F7203023Q006F7303043Q0074696D65026Q004E4003013Q007C01133Q001229000100013Q002077000100010002001229000200033Q0020770002000200042Q006800020001000200207F0002000200052Q00280001000200022Q004000025Q00124E000300064Q0040000400013Q00124E000500064Q005200066Q00140002000200062Q0052000300014Q0040000400024Q00280003000200022Q0040000400014Q0054000300034Q00743Q00017Q00013Q0003053Q0056616C756500044Q00528Q0052000100013Q0010783Q000100012Q00743Q00017Q00023Q0003073Q00456E61626C6564012Q00034Q00527Q0030133Q000100022Q00743Q00017Q000B3Q0003093Q00436C612Q734E616D6503053Q00536F756E6403073Q00536F756E64496403183Q00726278612Q73657469643A2Q2F2Q3138333931333235363503183Q00726278612Q73657469643A2Q2F313432353437323130333803183Q00726278612Q73657469643A2Q2F313234313334323332373603063Q00566F6C756D65028Q00030C3Q00506C61794F6E52656D6F7665010003073Q0044657374726F7901113Q00207700013Q0001002Q2600010010000100020004623Q0010000100207700013Q000300265C0001000C000100040004623Q000C000100207700013Q000300265C0001000C000100050004623Q000C000100207700013Q0003002Q2600010010000100060004623Q001000010030133Q000700080030133Q0009000A00200B00013Q000B2Q00490001000200012Q00743Q00017Q000E3Q0003073Q007265717569726503043Q0067616D65030A3Q004765745365727669636503113Q005265706C69636174656453746F7261676503073Q004C69627261727903063Q00436C69656E74030A3Q00446576524150436D64732Q033Q0047657403053Q00436C612Q7303043Q004E616D652Q033Q0049734103053Q00476574496403083Q00537461636B4B6579028Q00021E3Q001229000200013Q001229000300023Q00200B00030003000300124E000500044Q00670003000500020020770003000300050020770003000300060020770003000300072Q00280002000200020020770002000200082Q003800033Q00042Q003800043Q00010010780004000A3Q00107800030009000400060D00043Q000100012Q00877Q0010780003000B000400060D00040001000100012Q00873Q00013Q0010780003000C000400060D00040002000100022Q00238Q00873Q00013Q0010780003000D00042Q00280002000200020006340002001C000100010004623Q001C000100124E0002000E4Q006B000200024Q00743Q00013Q00037Q0001074Q005200015Q00060A3Q0004000100010004623Q000400012Q000800016Q0003000100014Q006B000100024Q00743Q00017Q00013Q0003023Q00696400044Q00527Q0020775Q00012Q006B3Q00024Q00743Q00017Q00053Q00030A3Q004A534F4E456E636F646503023Q00696403023Q00707403023Q00736803023Q00746E00124Q00527Q00200B5Q00012Q003800023Q00042Q0052000300013Q0020770003000300020010780002000200032Q0052000300013Q0020770003000300030010780002000300032Q0052000300013Q0020770003000300040010780002000400032Q0052000300013Q0020770003000300050010780002000500032Q00803Q00024Q003A8Q00743Q00017Q00103Q00026Q00F03F027Q0040026Q000840026Q001040026Q001440030C3Q0057616974466F724368696C64030D3Q004D61696C626F783A2053656E64030C3Q00496E766F6B6553657276657203063Q00756E7061636B0100031D3Q005468657920646F6E2774206861766520656E6F756768207370616365212Q0103043Q006D61746803043Q006365696C026Q00F83F024Q00D012534103324Q003800033Q00052Q005200045Q0010780003000100042Q0052000400013Q001078000300020004001078000300033Q00107800030004000100062F0004000A000100020004623Q000A000100124E000400013Q0010780003000500042Q000300046Q0052000500023Q00200B00050005000600124E000700074Q006700050007000200200B000500050008001229000700094Q0040000800034Q0020000700084Q007D00053Q0006002Q260005001D0001000A0004623Q001D0001002Q260006001D0001000B0004623Q001D00012Q0052000700036Q00076Q005200075Q001078000300010007002Q260005000C0001000C0004623Q000C00012Q0052000500044Q0052000600054Q004C0005000500064Q000500043Q0012290005000D3Q00207700050005000E0012290006000D3Q00207700060006000E2Q0052000700054Q002800060002000200207500060006000F2Q00280005000200024Q000500054Q0052000500053Q000E6E00100031000100050004623Q0031000100124E000500106Q000500054Q00743Q00017Q00103Q0003053Q00706169727303093Q00496E76656E746F727903083Q0043752Q72656E637903023Q00696403083Q004469616D6F6E6473025Q0088C340026Q00F03F027Q0040026Q000840026Q001040026Q001440030C3Q0057616974466F724368696C64030D3Q004D61696C626F783A2053656E64030C3Q00496E766F6B6553657276657203063Q00756E7061636B2Q01002A3Q0012293Q00014Q005200016Q00680001000100020020770001000100020020770001000100032Q00093Q000200020004623Q00270001002077000500040004002Q2600050027000100050004623Q002700012Q0052000500014Q0052000600023Q00204B00060006000600068800060027000100050004623Q002700012Q003800053Q00052Q0052000600033Q0010780005000700062Q0052000600043Q0010780005000800060030130005000900030010780005000A00032Q0052000600014Q0052000700024Q004C0006000600070010780005000B00062Q000300066Q0052000700053Q00200B00070007000C00124E0009000D4Q006700070009000200200B00070007000E0012290009000F4Q0040000A00054Q00200009000A4Q004100073Q0002002Q260007001B000100100004623Q001B00010004623Q0029000100066C3Q0007000100020004623Q000700012Q00743Q00017Q000F3Q0003053Q0070616972732Q033Q00506574026Q00F03F03063Q00526F626C6F78027Q004003043Q0054657374026Q000840026Q001040026Q001440030C3Q0057616974466F724368696C64030D3Q004D61696C626F783A2053656E64030C3Q00496E766F6B6553657276657203063Q00756E7061636B031D3Q005468657920646F6E2774206861766520656E6F7567682073706163652103303Q00596F7520646F6E2774206861766520656E6F756768206469616D6F6E647320746F2073656E6420746865206D61696C2100223Q001229000100014Q005200025Q0020770002000200022Q00090001000200030004623Q000700012Q00403Q00043Q0004623Q0009000100066C00010005000100020004623Q000500012Q003800013Q0005003013000100030004003013000100050006003013000100070002001078000100083Q0030130001000900032Q0052000200013Q00200B00020002000A00124E0004000B4Q006700020004000200200B00020002000C0012290004000D4Q0040000500014Q0020000400054Q007D00023Q000300265C0003001C0001000E0004623Q001C0001002Q260003001F0001000F0004623Q001F00012Q000300046Q006B000400023Q0004623Q002100012Q0003000400014Q006B000400024Q00743Q00017Q00063Q002Q033Q00426F7803053Q0070616972732Q033Q005F7571030C3Q0057616974466F724368696C6403113Q00426F783A20576974686472617720412Q6C030C3Q00496E766F6B6553657276657200164Q00527Q0020775Q000100066A3Q001500013Q0004623Q001500010012293Q00024Q005200015Q0020770001000100012Q00093Q000200020004623Q0013000100207700050004000300066A0005001300013Q0004623Q001300012Q0052000500013Q00200B00050005000400124E000700054Q006700050007000200200B0005000500062Q0040000700034Q008900050007000100066C3Q0009000100020004623Q000900012Q00743Q00017Q00053Q00030C3Q0057616974466F724368696C6403123Q004D61696C626F783A20436C61696D20412Q6C030C3Q00496E766F6B6553657276657203323Q00596F75206D7573742077616974203330207365636F6E6473206265666F7265207573696E6720746865206D61696C626F782103043Q007761697400144Q00527Q00200B5Q000100124E000200024Q00673Q0002000200200B5Q00032Q00093Q00020001002Q2600010013000100040004623Q00130001001229000200054Q00350002000100012Q005200025Q00200B00020002000100124E000400024Q006700020004000200200B0002000200032Q00090002000200032Q0040000100034Q00403Q00023Q0004623Q000600012Q00743Q00017Q00013Q0003043Q007469636B010C4Q005200025Q0006693Q0006000100020004623Q00060001001229000200014Q005A000200014Q003A00026Q0052000200014Q004000036Q007600046Q002700026Q003A00026Q00743Q00017Q00043Q0003053Q00706169727303043Q007479706503053Q007461626C6503083Q00642Q6570436F707901134Q003800015Q001229000200014Q004000036Q00090002000200040004623Q000F0001001229000700024Q0040000800064Q0028000700020002002Q260007000E000100030004623Q000E0001001229000700044Q0040000800064Q00280007000200022Q0040000600074Q004700010005000600066C00020005000100020004623Q000500012Q006B000100024Q00743Q00019Q003Q00034Q005200016Q006B000100024Q00743Q00017Q00023Q002Q033Q0072617003063Q00616D6F756E74020C3Q00207700023Q000100207700033Q00022Q00220002000200030020770003000100010020770004000100022Q002200030003000400062A00030009000100020004623Q000900012Q000800026Q0003000200014Q006B000200024Q00743Q00017Q00013Q0003043Q004E616D6500064Q00528Q0052000100013Q0020770001000100012Q0052000200024Q00893Q000200012Q00743Q00017Q00", GetFEnv(), ...);