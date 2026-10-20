module

public import VerifiedGarbage.Proof.Bignum.Arm.LayoutPreserved
public import VerifiedGarbage.Spec.Rsa.Contract

/-! Reuse exact byte preservation for packed context word lists. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Proof.Bignum.Arm VG.Proof.Mont

theorem wordsAt_eq {base : Addr} {size d count : Nat} {m m' : Mem}
    (h : WorkspaceEq base size m m') (bound : d+8*count≤size) :
    Spec.Rsa.wordsAt m' (off base d) count = Spec.Rsa.wordsAt m (off base d) count := by
  unfold Spec.Rsa.wordsAt
  apply List.map_congr_left
  intro i hi
  have hi' : i<count := List.mem_range.mp hi
  have read := h.word (d:=d+8*i) (bits:=64) (by omega)
  simpa only [off,BitVec.ofNat_add,←BitVec.add_assoc] using read

end VG.Proof.Ffdh.Arm.CombBuilder
