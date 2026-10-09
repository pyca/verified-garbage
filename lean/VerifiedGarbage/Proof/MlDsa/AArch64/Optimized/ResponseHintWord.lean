import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintMath

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64

def hintWord (g t high : BitVec 32) : BitVec 32 :=
  ((((g-t) ||| (t-(-g))).sshiftRight 31) |||
    ((if t= -g then -1 else 0) &&& ~~~(if high=0 then -1 else 0))) >>> 31

theorem signedMask (x : BitVec 32) :
    x.sshiftRight 31=if x.toInt<0 then -1 else 0 := by
  rw [ResidentMask.signMask32]
  have hx := BitVec.toInt_eq_toNat_cond x
  split <;> split <;> first | rfl | omega

theorem hintWord_value {g : Nat} (hg : 1≤g) (hg' : g≤524288)
    (t high : BitVec 32) (hl : -8380417<t.toInt) (hh : t.toInt<8380417) :
    hintWord (BitVec.ofNat 32 g) t high=
      if hintPredicate g t.toInt high.toInt then 1 else 0 := by
  have gi : (BitVec.ofNat 32 g).toInt=(g:Int) := by
    change (BitVec.ofInt 32 (g:Int)).toInt=(g:Int)
    apply BitVec.toInt_ofInt_eq_self (by decide) <;> omega
  have gn : (-(BitVec.ofNat 32 g)).toInt= -(g:Int) := by
    change (-BitVec.ofInt 32 (g:Int)).toInt= -(g:Int)
    rw [←BitVec.ofInt_neg]
    apply BitVec.toInt_ofInt_eq_self (by decide) <;> omega
  have l := subWord_int (BitVec.ofNat 32 g) t (by rw [gi]; omega) (by rw [gi]; omega)
  have r := subWord_int t (-(BitVec.ofNat 32 g)) (by rw [gn]; omega) (by rw [gn]; omega)
  have te : t= -(BitVec.ofNat 32 g) ↔ t.toInt= -(g:Int) := by
    constructor
    · intro h; rw [h,gn]
    · intro h; exact BitVec.eq_of_toInt_eq (h.trans gn.symm)
  have he : high=0 ↔ high.toInt=0 := by
    constructor
    · intro h; rw [h]; rfl
    · intro h; exact BitVec.eq_of_toInt_eq h
  unfold hintWord
  rw [BitVec.sshiftRight_or_distrib,signedMask,signedMask,l,r,gi,gn]
  simp only [te,he]
  unfold hintPredicate
  split <;> split <;> split <;> split <;>
    try simp only [ite_true,ite_false]
  all_goals split <;> first | rfl | omega

end VG.Proof.MlDsa.AArch64.Optimized.Response
