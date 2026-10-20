module
public import VerifiedGarbage.TCB.AArch64.Isa

import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Framework.PowLit

/-! # The register instructions of `AltOps`, one step each

`exec` of each register instruction the field operations of
`Impl/X25519/AArch64/AltOps` use, on 64-bit registers, so that their
symbolic execution unfolds no other instruction (and leaves the `ldp` and
`stp` to `Alt/Mem`). -/

@[expose] public section

namespace VG.Proof.X25519.AArch64.Alt

open VG VG.AArch64

theorem read_x64 (s : State) (n : Reg) : s.read .x n = s.gpr n := by
  simp only [State.read, BitVec.setWidth_eq]

theorem exec_adds_x (s : State) (d n m : Reg) :
    exec (.adds .x d n m) s = some (s.addWithCarry .x d (s.gpr n) (s.gpr m) false) := by
  simp only [exec, read_x64]

theorem exec_adcs_x (s : State) (d n m : Reg) :
    exec (.adcs .x d n m) s = some (s.addWithCarry .x d (s.gpr n) (s.gpr m) s.c) := by
  simp only [exec, read_x64]

theorem exec_adc_x (s : State) (d n m : Reg) :
    exec (.adc .x d n m) s =
      some (s.write .x d (s.gpr n + s.gpr m + BitVec.ofNat 64 s.c.toNat)) := by
  simp only [exec, read_x64]

theorem exec_subs_x (s : State) (d n m : Reg) :
    exec (.subs .x d n m) s = some (s.addWithCarry .x d (s.gpr n) (~~~s.gpr m) true) := by
  simp only [exec, read_x64]

theorem exec_sbcs_x (s : State) (d n m : Reg) :
    exec (.sbcs .x d n m) s = some (s.addWithCarry .x d (s.gpr n) (~~~s.gpr m) s.c) := by
  simp only [exec, read_x64]

theorem exec_sbc_x (s : State) (d n m : Reg) :
    exec (.sbc .x d n m) s =
      some (s.write .x d (s.gpr n + ~~~s.gpr m + BitVec.ofNat 64 s.c.toNat)) := by
  simp only [exec, read_x64]

theorem exec_mul_x (s : State) (d n m : Reg) :
    exec (.mul .x d n m) s = some (s.write .x d (s.gpr n * s.gpr m)) := by
  simp only [exec, read_x64]

theorem exec_umulh_x (s : State) (d n m : Reg) :
    exec (.umulh d n m) s =
      some (s.write .x d (BitVec.ofNat 64 ((s.gpr n).toNat * (s.gpr m).toNat / 2 ^ 64))) := rfl

theorem exec_cselc_x (s : State) (d n m : Reg) (c : CondCode) :
    exec (.cselc .x d n m c) s = some (s.write .x d (if c.holds s then s.gpr n else s.gpr m)) := rfl

theorem exec_lsr1_x (s : State) (d n : Reg) :
    exec (.lsr .x d n 1) s = some (s.write .x d (s.gpr n >>> 1)) := by
  rw [exec_lsr_x (by decide), read_x64]

end VG.Proof.X25519.AArch64.Alt
