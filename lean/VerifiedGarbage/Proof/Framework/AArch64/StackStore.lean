module

public import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch

/-! Execution of an aligned stack-relative word store. -/
@[expose] public section
namespace VG.Proof.Bignum.AArch64
open VG VG.AArch64

theorem exec_storeSp {s : State} {t : Reg} {off : Nat}
    (ho : off % 8 = 0 ∧ off < 32768)
    (h : InRegions s.wr (s.sp + BitVec.ofNat 64 off) 8) :
    exec (.strSp t off) s =
      some { s with mem := s.mem.writeW (s.sp + BitVec.ofNat 64 off) (s.gpr t) } := by
  simp only [exec, ho, and_self, ite_true, State.store, h, Mem.writeW]
  rfl

end VG.Proof.Bignum.AArch64
