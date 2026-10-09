import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVec
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Response

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG.Proof.MlKem.AArch64 (VChg wp_vop)

/-- An accepted centered response needs only the conditional addition of q. -/
theorem acceptedCanonical_bounds (x : BitVec 32)
    (hl : -8380417<x.toInt) (hh : x.toInt<8380417) : (signCorrected x).toNat<8380417 := by
  have he := signCorrected_int x hl (by omega)
  have hn := BitVec.toInt_eq_toNat_cond (signCorrected x)
  split at he <;> omega

theorem acceptedCanonical_mod (x : BitVec 32)
    (hl : -8380417<x.toInt) (hh : x.toInt<8380417) :
    ((signCorrected x).toNat : Int)=x.toInt%8380417 := by
  have he := signCorrected_int x hl (by omega)
  have hn := BitVec.toInt_eq_toNat_cond (signCorrected x)
  have hb := acceptedCanonical_bounds x hl hh
  split at he <;> omega

/-- Exact three-instruction accepted-output conversion, without an
additional subtraction or reduction pass. -/
theorem cadd_ok {d : VReg} (h7 : d≠.v7)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (hq : ∀e<4,vword (s.v .v16) e=8380417#32)
    (k : ∀t,VChg [.v7,d] s t →
      (∀e<4,vword (t.v d) e=signCorrected (vword (s.v d) e)) → WP isa (.block rest) t Q) :
    WP isa (.block (VG.Impl.MlDsa.AArch64.Optimized.Response.cadd d++rest)) s Q := by
  refine wp_vop (d := .v7) rfl fun a ha => wp_vop (d := .v7) rfl fun b hb =>
    wp_vop (d := d) rfl fun t ht => ?_
  refine k t (((ha.chg.trans hb.chg).trans ht.chg).mono ?_) ?_
  · intro r hr
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
    grind only
  · intro e he
    rw [ht.v,VG.AArch64.vword_map2 _ _ _ he,hb.get d h7,ha.get d h7,hb.v,word_and,
      ha.v,VG.AArch64.vword_map2 _ _ _ he,ha.get .v16 (by decide),hq e he]
    rfl

end VG.Proof.MlDsa.AArch64.Optimized.Response
