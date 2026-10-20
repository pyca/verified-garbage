module
public import VerifiedGarbage.Proof.Framework.X86_64.Frame

import VerifiedGarbage.Proof.MillerRabin.X86_64.Stack
import VerifiedGarbage.Proof.Framework.Mem

/-! # Leave the two fixed frames -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64

def exited (s : State) : State := popped .r11 13 (popped .rbp 1 s)

theorem exited_mem (s : State) : (exited s).mem = s.mem := by simp only [exited, popped_mem]

theorem exited_mxcsr (s : State) : (exited s).mxcsr = s.mxcsr := by simp only [exited, popped_mxcsr]

theorem exited_rsp (s : State) : (exited s).gpr .rsp = s.gpr .rsp + 112#64 := by
  simp only [exited, popped_rsp]
  bv_omega

theorem exited_gpr (s : State) {r : Reg} (hsp : r ≠ .rsp) (hbp : r ≠ .rbp) (h11 : r ≠ .r11) :
    (exited s).gpr r = s.gpr r :=
  (popped_gpr _ _ _ hsp h11).trans (popped_gpr _ _ _ hsp hbp)

theorem exited_rbp (s : State) : (exited s).gpr .rbp = s.mem.readW (s.gpr .rsp) 64 := by
  unfold exited
  rw [popped_gpr _ _ _ (by decide : Reg.rbp ≠ Reg.rsp) (by decide : Reg.rbp ≠ Reg.r11), popped_rbp]

end VG.Proof.MillerRabin.X86_64
