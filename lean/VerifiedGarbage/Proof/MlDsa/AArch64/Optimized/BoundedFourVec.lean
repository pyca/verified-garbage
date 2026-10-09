import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourWord
import VerifiedGarbage.Proof.MlKem.AArch64.Vec
import VerifiedGarbage.Proof.Framework.AArch64.Simd

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour

/-- Canonicalize all four eta-minus-nibble values in registers. -/
theorem valueTail_ok (η : Nat) {s : State} {rest : List Instr} {Q : State → Prop}
    (hq : ∀e<4,vword (s.v .v21) e=8380417#32)
    (hη : ∀e<4,vword (s.v .v20) e=BitVec.ofNat 32 (Spec.MlDsa.q+η))
    (k : ∀t,VChg [.v1,.v2] s t →
      (∀e<4,vword (t.v .v1) e=
        let v:=BitVec.ofNat 32 (Spec.MlDsa.q+η)-vword (s.v .v1) e
        if v.toNat≤(v-8380417#32).toNat then v else v-8380417#32) →
      WP isa (.block rest) t Q) :
    WP isa (.block (valueTail++rest)) s Q := by
  refine wp_vop (d := .v1) rfl fun a ha => wp_vop (d := .v2) rfl fun b hb =>
    wp_vop (d := .v1) rfl fun t ht => ?_
  refine k t (((ha.chg.trans hb.chg).trans ht.chg).mono ?_) ?_
  · intro r hr
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
    grind only
  · intro e he
    rw [ht.v,VG.AArch64.vword_map2 _ _ _ he,hb.v,VG.AArch64.vword_map2 _ _ _ he,
      hb.get .v1 (by decide),ha.v,VG.AArch64.vword_map2 _ _ _ he,
      ha.get .v21 (by decide),hq e he,hη e he]

/-- Exact per-lane arithmetic for the selected eta=2 and eta=4 kernels. -/
theorem vectorVal_ok (η : Nat) {s : State} {rest : List Instr} {Q : State → Prop}
    (h13 : ∀e<4,vword (s.v .v18) e=13#32)
    (h5 : ∀e<4,vword (s.v .v19) e=5#32)
    (hq : ∀e<4,vword (s.v .v21) e=8380417#32)
    (hη : ∀e<4,vword (s.v .v20) e=BitVec.ofNat 32 (Spec.MlDsa.q+η))
    (k : ∀t,VChg [.v1,.v2] s t →
      (∀e<4,vword (t.v .v1) e=valueWord η (vword (s.v .v1) e)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (vectorVal η++rest)) s Q := by
  by_cases he : η=2
  · subst η
    simp only [vectorVal,BEq.rfl,ite_true,List.cons_append,List.nil_append]
    refine wp_vop (d := .v2) rfl fun a ha => wp_vop (d := .v2) rfl fun b hb =>
      wp_vop (d := .v2) rfl fun c hc => wp_vop (d := .v1) rfl fun d hd => ?_
    have hkeep : VChg [.v1,.v2] s d :=
      (((ha.chg.trans hb.chg).trans hc.chg).trans hd.chg).mono (by
        intro r hr
        simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
        grind only)
    have hr (e : Nat) (he : e<4) :
        vword (d.v .v1) e=vword (s.v .v1) e-((vword (s.v .v1) e*13#32)>>>6)*5#32 := by
      rw [hd.v,VG.AArch64.vword_map2 _ _ _ he,hc.get .v1 (by decide),
        hb.get .v1 (by decide),ha.get .v1 (by decide),hc.v,VG.AArch64.vword_map2 _ _ _ he,
        hb.get .v19 (by decide),ha.get .v19 (by decide),h5 e he,
        hb.v,VG.AArch64.vword_map2 _ _ _ he,ha.v,VG.AArch64.vword_map2 _ _ _ he,h13 e he]
      rfl
    refine valueTail_ok 2 (fun e he => by rw [hkeep.v .v21 (by decide)]; exact hq e he)
      (fun e he => by rw [hkeep.v .v20 (by decide)]; exact hη e he) fun t ht hv => ?_
    refine k t ((hkeep.trans ht).mono (by
      intro r hr; simpa only [List.mem_append,or_self] using hr)) ?_
    intro e he
    rw [hv e he,hr e he]
    rfl
  · simp only [vectorVal,beq_iff_eq,he,ite_false,List.nil_append]
    refine valueTail_ok η hq hη fun t ht hv => k t ht ?_
    intro e hb
    rw [hv e hb]
    simp only [valueWord,he,ite_false]

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
