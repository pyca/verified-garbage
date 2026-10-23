module

public import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
public import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.MlKem.Arith
meta import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.SigEval
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.SigEval

/-!
# ML-KEM on PPC64LE: `vg_mlkem_sample_ntt`, constant time and `Verified`
-/

@[expose] public section

namespace VG.Proof.MlKem.PPC64LE.Sample

open VG VG.PPC64LE VG.Impl.MlKem.PPC64LE
open VG.Spec.MlKem

theorem pre_of {s : State} (h : (Spec.MlKem.sampleNTTContract PPC64LE.abi 48).pre s) : Pre s := by
  sig_pre [Spec.MlKem.sampleNTTContract, Spec.MlKem.sampleNTTSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem polyAt_toPoly {m : Mem} {p : Addr} {L : List Zq} (hl : L.length = n)
    (h : ∀ k < L.length, coeffAt m p k = BitVec.ofNat 32 (L.getD k 0).val) :
    PolyIs m p (VG.Proof.MlKem.toPoly L) := by
  refine polyIs_of_coeffAt fun i hi => ?_
  rw [h i (by rw [hl]; exact hi), getElem!_eq _ hi]
  simp only [VG.Proof.MlKem.toPoly, Vector.getElem_ofFn]

theorem post_of {s₀ s : State} (h : Done s₀ s) : (Spec.MlKem.sampleNTTContract PPC64LE.abi 48).post s₀ s := by
  sig_post [Spec.MlKem.sampleNTTContract, Spec.MlKem.sampleNTTSig, PPC64LE.abi, PPC64LE.argRegs]
  rw [h.r3]
  by_cases hl : (Ls s₀ 280).length = 256
  · rw [ite_eq_left hl]
    have hpi := polyAt_toPoly (by rw [n_eq]; exact hl) h.coeff
    refine ⟨fun _ => hpi.1, VG.Proof.MlKem.outcome_of_min (.inl ⟨rfl, ?_⟩)⟩
    rw [hpi.2]
    exact VG.Proof.MlKem.sampleNTT_of_full (Nat.le_refl _) (by rw [n_eq]; exact hl)
  · rw [ite_eq_right hl]
    refine ⟨fun e => absurd e (by decide), VG.Proof.MlKem.outcome_of_min (.inr ⟨rfl, ?_⟩)⟩
    exact VG.Proof.MlKem.sampleNTT_none (by rw [n_eq]; exact hl)

/-! ## Constant time -/

/-- Two runs, from states that agree on the public data. -/
structure Two (s₁ s₂ : State) : Prop where
  hp₁ : Pre s₁
  hp₂ : Pre s₂
  sp : s₁.sp = s₂.sp
  seed : s₁.gpr .r3 = s₂.gpr .r3
  a : s₁.gpr .r4 = s₂.gpr .r4
  scr : s₁.gpr .r5 = s₂.gpr .r5
  B : B s₁ = B s₂

theorem taint_block {P : State → State → Prop} {is : List Instr} (rs : List Reg)
    (hsp : ∀ a b, P a b → a.sp = b.sp) (hP : ∀ a b, P a b → ∀ r ∈ rs, a.gpr r = b.gpr r)
    {hc : VG.Taint.Hint VG.PPC64LE.taint.T}
    (h : (VG.PPC64LE.taint.check (Taint.ofRegs rs) (.block is) hc).isSome = true) :
    RelCT isa P (.block is) fun _ _ => True :=
  RelCT.taint (A := VG.PPC64LE.taint) (Taint.ofRegs rs)
    (fun a b hab => ⟨hsp a b hab, fun r hr => hP a b hab r (Taint.mem_ofRegs.mp hr)⟩) h

theorem relct_wp {c : Prog isa} {P : State → State → Prop} {F₁ F₂ : State → Prop}
    (hct : RelCT isa P c fun _ _ => True) (hw : ∀ a b, P a b → WP isa c a F₁ ∧ WP isa c b F₂) :
    RelCT isa P c fun a b => F₁ a ∧ F₂ b :=
  (hct.wp hw).mono (fun _ _ h => h) fun _ _ h => ⟨h.2.1, h.2.2⟩

section
variable {s₁ s₂ : State} (h : Two s₁ s₂)
include h

theorem Ls_eq (t : Nat) : Ls s₁ t = Ls s₂ t := by simp only [Ls, h.B]
theorem D1_eq (t : Nat) : D1 s₁ t = D1 s₂ t := by simp only [D1, h.B]
theorem D2_eq (t : Nat) : D2 s₁ t = D2 s₂ t := by simp only [D2, h.B]

/-- A call of verified code from the same registers in both runs, with the
same regions. -/
theorem call_ct {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {F : State → State → Prop} (hF : ∀ s₀ t, F s₀ t → SEnv s₀ t)
    (rd wr : State → List Region) (hrd : ∀ s₀, ∀ r ∈ rd s₀, r = ⟨SEED s₀, 34⟩)
    (hwr : ∀ s₀, ∀ r ∈ wr s₀, ∃ o n, o + n ≤ 1680 ∧ r = ⟨S s₀ + BitVec.ofNat 64 o, n⟩)
    (hpre : ∀ s₀ t, Pre s₀ → F s₀ t → k.pre (t.callEntry.withRegions (rd s₀) (wr s₀)))
    (hrd₂ : rd s₂ = rd s₁) (hwr₂ : wr s₂ = wr s₁)
    (hpub : ∀ a b, F s₁ a → F s₂ b →
      k.pub (a.callEntry.withRegions (rd s₁) (wr s₁)) (b.callEntry.withRegions (rd s₁) (wr s₁))) :
    RelCT isa (fun a b => F s₁ a ∧ F s₂ b) (.call n c) fun _ _ => True :=
  RelCT.call hv hct (rd s₁) (wr s₁) fun a b ⟨fa, fb⟩ => by
    have c₁ := call_covers h.hp₁ (hF _ _ fa) (hrd s₁) (hwr s₁)
    have c₂ := call_covers h.hp₂ (hF _ _ fb) (hrd s₂) (hwr s₂)
    have p₂ := hpre _ _ h.hp₂ fb
    rw [hrd₂, hwr₂] at c₂ p₂
    exact ⟨hpre _ _ h.hp₁ fa, p₂, hpub a b fa fb, c₁.1, c₁.2, c₂.1, c₂.2⟩

/-! ## The loop -/

omit h in
/-- A candidate accepted or not, in both runs alike. -/
theorem accept_ct {d : Reg} (hd : d = .r10 ∨ d = .r11) {P : State → State → Prop}
    (hsp : ∀ a b, P a b → a.sp = b.sp) (hz : ∀ a b, P a b → a.gpr .r12 = b.gpr .r12)
    (h4 : ∀ a b, P a b → a.gpr .r4 = b.gpr .r4) :
    RelCT isa P (accept d) fun _ _ => True := by
  refine RelCT.ite (fun a b hab => by rw [eval_zero, eval_zero, hz a b hab]) ?_ ?_
  · exact taint_block [] (fun a b hab => hsp a b hab.1) (fun _ _ _ _ hr => absurd hr List.not_mem_nil)
      (by taint_decide)
  · have h4' : ∀ a b, (P a b ∧ isa.eval (.zero .d .r12) a = some false) → ∀ r ∈ [Reg.r4], a.gpr r = b.gpr r :=
      fun a b hab r hr => by rw [List.mem_singleton] at hr; subst hr; exact h4 a b hab.1
    rcases hd with rfl | rfl
    · exact taint_block [.r4] (fun a b hab => hsp a b hab.1) h4' (by taint_decide)
    · exact taint_block [.r4] (fun a b hab => hsp a b hab.1) h4' (by taint_decide)

theorem body_ct {t : Nat} (ht : t < 280) :
    RelCT isa (fun a b => Inv s₁ t a ∧ Inv s₂ t b) rejBody fun a b =>
      (Inv s₁ (t + 1) a ∧ (a.gpr .r6 != 0) = decide (t + 1 ≠ 280)) ∧
      (Inv s₂ (t + 1) b ∧ (b.gpr .r6 != 0) = decide (t + 1 ≠ 280)) := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  have sp : ∀ {a b : State} {L₁ L₂ : List Zq}, LS s₁ L₁ a → LS s₂ L₂ b → a.sp = b.sp :=
    fun l₁ l₂ => by rw [l₁.env.sp, l₂.env.sp, h.sp]
  refine relct_wp ?_ fun a b hab => ⟨body_ok hp₁ ht hab.1, body_ok hp₂ ht hab.2⟩
  refine RelCT.seq (R := fun a b => P1 s₁ t a ∧ P1 s₂ t b) (relct_wp ?_ fun a b hab =>
    ⟨piece1 hp₁ ht hab.1, piece1 hp₂ ht hab.2⟩) ?_
  · exact taint_block [.r3] (fun a b hab => sp hab.1.ls hab.2.ls) (fun a b hab r hr => by
      rw [List.mem_singleton] at hr; subst hr; rw [hab.1.r3, hab.2.r3, S, S, h.scr]) (by taint_decide)
  refine RelCT.seq (R := fun a b => P2 s₁ t a ∧ P2 s₂ t b) (relct_wp ?_ fun a b hab =>
    ⟨piece2 hp₁ hab.1, piece2 hp₂ hab.2⟩) ?_
  · refine accept_ct (.inl rfl) (fun a b hab => sp hab.1.ls hab.2.ls)
      (fun a b hab => by rw [hab.1.r12, hab.2.r12, D1_eq h, Ls_eq h]) fun a b hab => ?_
    rw [hab.1.ls.r4, hab.2.ls.r4, A, A, h.a, Ls_eq h]
  refine RelCT.seq (R := fun a b => P3 s₁ t a ∧ P3 s₂ t b) (relct_wp ?_ fun a b hab =>
    ⟨piece3 hp₁ hab.1, piece3 hp₂ hab.2⟩) ?_
  · exact taint_block [] (fun a b hab => sp hab.1.ls hab.2.ls) (fun _ _ _ _ hr => absurd hr List.not_mem_nil)
      (by taint_decide)
  refine RelCT.seq (R := fun a b => P4 s₁ t a ∧ P4 s₂ t b) (relct_wp ?_ fun a b hab =>
    ⟨piece4 hp₁ hab.1, piece4 hp₂ hab.2⟩) ?_
  · refine accept_ct (.inr rfl) (fun a b hab => sp hab.1.p2.ls hab.2.p2.ls)
      (fun a b hab => by rw [hab.1.r12, hab.2.r12, D1_eq h, D2_eq h, Ls_eq h]) fun a b hab => ?_
    rw [hab.1.p2.ls.r4, hab.2.p2.ls.r4, A, A, h.a, Ls_eq h, D1_eq h]
  · exact taint_block [] (fun a b hab => sp hab.1.ls hab.2.ls) (fun _ _ _ _ hr => absurd hr List.not_mem_nil)
      (by taint_decide)

theorem loop_ct :
    RelCT isa (fun a b => Inv s₁ 0 a ∧ Inv s₂ 0 b) (.loop rejBody (.nonzero .d .r6)) fun a b =>
      Inv s₁ 280 a ∧ Inv s₂ 280 b := by
  refine RelCT.mono (RelCT.loop (M := isa) (body := rejBody) (c := .nonzero .d .r6)
    (Q := fun a b => Inv s₁ 280 a ∧ Inv s₂ 280 b)
    (fun n a b => ∃ t, t < 280 ∧ n = 280 - t ∧ Inv s₁ t a ∧ Inv s₂ t b) (fun n => ?_) 280)
    (fun a b hab => ⟨0, by decide, rfl, hab⟩) (fun _ _ h => h)
  refine RelCT.mono (P := fun a b => ∃ t, t < 280 ∧ n = 280 - t ∧ Inv s₁ t a ∧ Inv s₂ t b)
    (RelCT.exists_ fun t => ?_) (fun _ _ hab => hab) (fun _ _ h => h)
  by_cases ht : t < 280
  · by_cases hn : n = 280 - t
    · refine RelCT.mono (P := fun a b => Inv s₁ t a ∧ Inv s₂ t b) (body_ct h ht) (fun _ _ hab => hab.2.2)
        fun a b ⟨⟨i₁, z₁⟩, ⟨i₂, z₂⟩⟩ => ⟨?_, fun e => ?_, fun e => ?_⟩
      · rw [eval_nonzero, eval_nonzero, z₁, z₂]
      · have : t + 1 = 280 := by
          have e' : (a.gpr .r6 != 0) = false := by rw [eval_nonzero] at e; exact Option.some.inj e
          rw [z₁] at e'; simpa using e'
        rw [this] at i₁ i₂; exact ⟨i₁, i₂⟩
      · have : t + 1 ≠ 280 := by
          have e' : (a.gpr .r6 != 0) = true := by rw [eval_nonzero] at e; exact Option.some.inj e
          rw [z₁] at e'; simpa using e'
        exact ⟨280 - (t + 1), by omega, t + 1, by omega, rfl, i₁, i₂⟩
    · exact RelCT.of_false fun _ _ hab => hn hab.2.1
  · exact RelCT.of_false fun _ _ hab => ht hab.1

end

end VG.Proof.MlKem.PPC64LE.Sample
