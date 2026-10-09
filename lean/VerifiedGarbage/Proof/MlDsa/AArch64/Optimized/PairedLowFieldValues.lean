import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowFlagValue
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowSemantics

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlDsa.AArch64.Optimized.Response

/-- Each high output is the specification's decomposition of the difference. -/
theorem lowHighOutput_field {g : Nat} (hg : IsG g) {m : Mem} {out : Addr} {raw : BitVec 128}
    {e : Nat} (he : e<4) (ha : (vword (m.read out 16) e).toNat<q)
    (hb : -8380417<(vword raw e).toInt ∧ (vword raw e).toInt<2*8380417) :
    (vword (lowHighOutput g m out raw) e).toNat=(highBits g (lowInputField m out raw e)).toNat := by
  rw [lowHighOutput,laneVector_word _ he]
  exact lowInputValues_high hg ha hb.1 hb.2

/-- Each low output has the exact signed low-bits representative, on all paths. -/
theorem lowLowOutput_field {g : Nat} (hg : IsG g) {m : Mem} {out : Addr} {raw : BitVec 128}
    {c : LowConstants} {e : Nat} (he : e<4) (hs : vword c.scale e=BitVec.ofNat 32 (2*g))
    (ha : (vword (m.read out 16) e).toNat<q)
    (hb : -8380417<(vword raw e).toInt ∧ (vword raw e).toInt<2*8380417) :
    (vword (lowLowOutput g m out raw c) e).toInt=lowBits g (lowInputField m out raw e) := by
  rw [lowLowOutput,laneVector_word _ he,hs]
  exact lowInputValues_low hg ha hb.1 hb.2

/-- The r0 machine mask is zero exactly when the strict low-bits norm passes. -/
theorem lowMask_zero {g B : Nat} (hg : IsG g) {m : Mem} {out : Addr} {raw : BitVec 128}
    {c : LowConstants} {e : Nat}
    (hs : vword c.scale e=BitVec.ofNat 32 (2*g))
    (hl : vword c.lower e=BitVec.ofNat 32 (B-1))
    (hw : vword c.width e=BitVec.ofNat 32 (2*B-1))
    (ha : (vword (m.read out 16) e).toNat<q)
    (hb : -8380417<(vword raw e).toInt ∧ (vword raw e).toInt<2*8380417)
    (hB : 1≤B) (hB' : B≤524288) :
    lowMask g m out raw c e=0 ↔ normZq (ofInt (lowBits g (lowInputField m out raw e)))<B := by
  rw [lowMask,hs,hl,hw,lowInputValues_norm hg ha hb.1 hb.2 hB hB']
  split
  · rename_i h
    exact ⟨fun _ => h,fun _ => rfl⟩
  · rename_i h
    exact ⟨fun hz => False.elim ((by decide : (-1 : BitVec 32)≠0) hz),fun hx => False.elim (h hx)⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired
