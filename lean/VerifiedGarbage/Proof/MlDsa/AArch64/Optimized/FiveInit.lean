import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.FiveLoop

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlKem.AArch64 (mov)
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

def fiveSetup : List Instr := [mov .x2 .x0,mov .x3 .x1,.addImm .x .x4 .x1 32,
  .addImm .x .x5 .x1 96,.addImm .x .x7 .x1 224,.addImm .x .x8 .x1 352,.movz .x .x10 8 0]

theorem fiveSetup_ok (s : State) : WP isa (.block fiveSetup) s fun t =>
    Keep fiveGprs s t ∧ t.mem=s.mem ∧ t.v=s.v ∧ t.gpr .x2=s.gpr .x0 ∧
      t.gpr .x10=8 ∧ FivePointers t (s.gpr .x1) 0 := by
  have run : WP isa (.block fiveSetup) s fun t =>
      ((t.gpr .x2=s.gpr .x0 ∧ t.gpr .x3=s.gpr .x1 ∧ t.gpr .x4=s.gpr .x1+32#64 ∧
        t.gpr .x5=s.gpr .x1+96#64 ∧ t.gpr .x7=s.gpr .x1+224#64 ∧ t.gpr .x8=s.gpr .x1+352#64 ∧
        t.gpr .x10=8 ∧ t.mem=s.mem) ∧ Keep fiveGprs s t) ∧ t.v=s.v := by
    apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
    refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
    unfold fiveSetup
    arun [mov]
  refine WP.mono run fun t ⟨⟨⟨h2,h3,h4,h5,h7,h8,h10,hm⟩,hk⟩,hv⟩ =>
    ⟨hk,hm,hv,h2,h10,?_,?_⟩
  · intro gap
    by_cases h4g : gap=4
    · subst gap
      change t.gpr .x3=s.gpr .x1+0#64
      simpa only [BitVec.add_zero] using h3
    · by_cases h2g : gap=2
      · subst gap
        change t.gpr .x4=s.gpr .x1+32#64
        exact h4
      · simpa only [innerBase,innerOffset,h4g,h2g,ite_false,Nat.mul_zero,Nat.zero_add] using h5
  · intro len
    by_cases h2l : len=2
    · subst len
      change t.gpr .x7=s.gpr .x1+224#64
      exact h7
    · simpa only [tailBase,tailOffset,h2l,ite_false,Nat.mul_zero,Nat.zero_add] using h8

theorem renFive_eq : renFive = .seq (.block fiveSetup)
    (.loop (.block (fiveSliceCode ++ fiveAdvance)) (.nonzero .x .x10)) := by
  rw [renFive,renFiveBody_eq]
  simp only [fiveAdvance,fiveSetup,List.append_assoc,List.cons_append,List.nil_append]

theorem renFive_ok {s : State} {r : Region} {zi zt : Nat → Nat → Nat → Nat → Int}
    (hT : RootTable s.mem (s.gpr .x1) zi zt)
    (hq : ∀ e < 4, vword (s.v .v16) e = 8380417#32)
    (htr : expandedRegion (s.gpr .x1) ∈ s.rd++s.wr) (hr : r ∈ s.wr)
    (hsep : (expandedRegion (s.gpr .x1)).Disjoint r)
    (hcontains : ∀ u < 8, ∀ i : Fin 8, r.Contains
      ((s.gpr .x0+BitVec.ofNat 64 (128*u))+BitVec.ofNat 64 (16*i.val)) 16) :
    WP isa renFive s fun t => Keep fiveGprs s t ∧ Frame [r] s.mem t.mem ∧
      t.gpr .x2=s.gpr .x0+1024 ∧ (∀ e < 4, vword (t.v .v16) e = 8380417#32) ∧
      t.mem=fivePassMem s.mem (s.gpr .x0) zi zt 8 := by
  rw [renFive_eq]
  refine WP.seq (WP.mono (fiveSetup_ok s) fun s₁ ⟨hk₁,hm₁,hv₁,hp₁,hc₁,hptr₁⟩ => ?_)
  refine WP.mono (fiveLoop_ok (zi := zi) (zt := zt) (by simpa only [hm₁] using hT) hptr₁
    (by simpa only [hv₁] using hq) hc₁
    (by simpa only [hk₁.rd,hk₁.wr] using htr) (by simpa only [hk₁.wr] using hr) hsep
    (by simpa only [hp₁] using hcontains)) fun t ⟨hk₂,hf₂,_,hp₂,hq₂,hm₂⟩ => ?_
  refine ⟨(hk₁.trans hk₂).mono,?_,?_,hq₂,?_⟩
  · simpa only [hm₁] using hf₂
  · simpa only [hp₁] using hp₂
  · simpa only [hm₁,hp₁] using hm₂

end VG.Proof.MlDsa.AArch64.Optimized
