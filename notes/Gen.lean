module
meta import VerifiedGarbage.Impl.Aes.X86_64.Sbox
meta import VerifiedGarbage.Impl.Aes.X86_64.Alloc
public import VerifiedGarbage.Impl.Aes.X86_64.Sbox
open VG.X86_64 VG.Impl.Aes.X86_64 VG.Impl.Aes.Circuit
meta def rn (r : Reg) : String := "." ++ ((reprStr r).splitOn ".").getLast!
meta def sl (m : MemOp) : Nat := (m.disp / 8).toNat
meta def sh : Instr → String
 | .mov d (.reg s) => s!"movR {rn d} {rn s}" | .mov d (.mem m) => s!"movS {rn d} {sl m}"
 | .alu .xor d (.reg s) => s!"xorR {rn d} {rn s}" | .alu .xor d (.mem m) => s!"xorS {rn d} {sl m}"
 | .alu .and d (.reg s) => s!"andR {rn d} {rn s}" | .alu .and d (.mem m) => s!"andS {rn d} {sl m}"
 | .store m r => s!"st {sl m} {rn r}" | .movImm64 d _ => s!"ones {rn d}" | _ => "??"
#eval IO.println (", ".intercalate ((compile sb sbox sboxIns sboxOuts [t0, t1] onesSlot spillSlots).map sh))
