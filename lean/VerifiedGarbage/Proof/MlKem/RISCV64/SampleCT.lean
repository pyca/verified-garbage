module

public import VerifiedGarbage.Proof.MlKem.RISCV64.Sample
public import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.MlKem.Arith
meta import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.CallsCT
meta import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.CallsCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.SigEval
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Sample
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.SigEval

/-!
# ML-KEM on RISC-V: `vg_mlkem_sample_ntt`, constant time and `Verified`

As on PPC64LE (`Proof/MlKem/PPC64LE/SampleCT.lean`), with the calls of the
sponge related by `absorbCall_ct`, `padCall_ct` and `squeezeCall_ct`
(`Proof/Sha3/RISCV64/Stream/CallsCT.lean`).
-/

@[expose] public section

namespace VG.Proof.MlKem.RISCV64.Sample

open VG VG.RISCV64 VG.Impl.MlKem.RISCV64
open VG.Spec.MlKem
open VG.Spec.Sha3 (stateAt)
open VG.Proof.Sha3.RISCV64.Stream (absorbCall_ct padCall_ct squeezeCall_ct)

theorem pre_of {s : State} (h : (Spec.MlKem.sampleNTTContract RISCV64.abi 1168).pre s) : Pre s := by
  sig_pre [Spec.MlKem.sampleNTTContract, Spec.MlKem.sampleNTTSig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

theorem polyAt_toPoly {m : Mem} {p : Addr} {L : List Zq} (hl : L.length = n)
    (h : ∀ k < L.length, coeffAt m p k = BitVec.ofNat 32 (L.getD k 0).val) :
    PolyIs m p (VG.Proof.MlKem.toPoly L) := by
  refine polyIs_of_coeffAt fun i hi => ?_
  rw [h i (by rw [hl]; exact hi), getElem!_eq _ hi]
  simp only [VG.Proof.MlKem.toPoly, Vector.getElem_ofFn]

theorem post_of {s₀ s : State} (h : Done s₀ s) : (Spec.MlKem.sampleNTTContract RISCV64.abi 1168).post s₀ s := by
  sig_post [Spec.MlKem.sampleNTTContract, Spec.MlKem.sampleNTTSig, RISCV64.abi, RISCV64.argRegs]
  rw [h.a0]
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
  seed : s₁.gpr .a0 = s₂.gpr .a0
  a : s₁.gpr .a1 = s₂.gpr .a1
  scr : s₁.gpr .a2 = s₂.gpr .a2
  B : B s₁ = B s₂

theorem taint_block {P : State → State → Prop} {is : List Instr} (rs : List Reg)
    (hsp : ∀ a b, P a b → a.sp = b.sp) (hP : ∀ a b, P a b → ∀ r ∈ rs, a.gpr r = b.gpr r)
    {hc : VG.Taint.Hint VG.RISCV64.taint.T}
    (h : (VG.RISCV64.taint.check (Taint.ofRegs rs) (.block is) hc).isSome = true) :
    RelCT isa P (.block is) fun _ _ => True :=
  RelCT.taint (A := VG.RISCV64.taint) (Taint.ofRegs rs)
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

/-! ## The loop -/

omit h in
/-- A candidate accepted or not, in both runs alike. -/
theorem accept_ct {d : Reg} (hd : d = .a7 ∨ d = .t1) {P : State → State → Prop}
    (hsp : ∀ a b, P a b → a.sp = b.sp) (hz : ∀ a b, P a b → a.gpr .t2 = b.gpr .t2)
    (h4 : ∀ a b, P a b → a.gpr .a1 = b.gpr .a1) :
    RelCT isa P (accept d) fun _ _ => True := by
  refine RelCT.ite (fun a b hab => by rw [Steps.eval_zero, Steps.eval_zero, hz a b hab]) ?_ ?_
  · exact taint_block [] (fun a b hab => hsp a b hab.1) (fun _ _ _ _ hr => absurd hr List.not_mem_nil)
      (by taint_decide)
  · have h4' : ∀ a b, (P a b ∧ isa.eval (.zero .t2) a = some false) → ∀ r ∈ [Reg.a1], a.gpr r = b.gpr r :=
      fun a b hab r hr => by rw [List.mem_singleton] at hr; subst hr; exact h4 a b hab.1
    rcases hd with rfl | rfl
    · exact taint_block [.a1] (fun a b hab => hsp a b hab.1) h4' (by taint_decide)
    · exact taint_block [.a1] (fun a b hab => hsp a b hab.1) h4' (by taint_decide)

theorem body_ct {t : Nat} (ht : t < 280) :
    RelCT isa (fun a b => Inv s₁ t a ∧ Inv s₂ t b) rejBody fun a b =>
      (Inv s₁ (t + 1) a ∧ (a.gpr .a3 != 0) = decide (t + 1 ≠ 280)) ∧
      (Inv s₂ (t + 1) b ∧ (b.gpr .a3 != 0) = decide (t + 1 ≠ 280)) := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  have sp : ∀ {a b : State} {L₁ L₂ : List Zq}, LS s₁ L₁ a → LS s₂ L₂ b → a.sp = b.sp :=
    fun l₁ l₂ => by rw [l₁.env.sp, l₂.env.sp, h.sp]
  refine relct_wp ?_ fun a b hab => ⟨body_ok hp₁ ht hab.1, body_ok hp₂ ht hab.2⟩
  refine RelCT.seq (R := fun a b => P1 s₁ t a ∧ P1 s₂ t b) (relct_wp ?_ fun a b hab =>
    ⟨piece1 hp₁ ht hab.1, piece1 hp₂ ht hab.2⟩) ?_
  · exact taint_block [.a0] (fun a b hab => sp hab.1.ls hab.2.ls) (fun a b hab r hr => by
      rw [List.mem_singleton] at hr; subst hr; rw [hab.1.a0, hab.2.a0, S, S, h.scr]) (by taint_decide)
  refine RelCT.seq (R := fun a b => P2 s₁ t a ∧ P2 s₂ t b) (relct_wp ?_ fun a b hab =>
    ⟨piece2 hp₁ hab.1, piece2 hp₂ hab.2⟩) ?_
  · refine accept_ct (.inl rfl) (fun a b hab => sp hab.1.ls hab.2.ls)
      (fun a b hab => by rw [hab.1.t2, hab.2.t2, D1_eq h, Ls_eq h]) fun a b hab => ?_
    rw [hab.1.ls.a1, hab.2.ls.a1, A, A, h.a, Ls_eq h]
  refine RelCT.seq (R := fun a b => P3 s₁ t a ∧ P3 s₂ t b) (relct_wp ?_ fun a b hab =>
    ⟨piece3 hp₁ hab.1, piece3 hp₂ hab.2⟩) ?_
  · exact taint_block [] (fun a b hab => sp hab.1.ls hab.2.ls) (fun _ _ _ _ hr => absurd hr List.not_mem_nil)
      (by taint_decide)
  refine RelCT.seq (R := fun a b => P4 s₁ t a ∧ P4 s₂ t b) (relct_wp ?_ fun a b hab =>
    ⟨piece4 hp₁ hab.1, piece4 hp₂ hab.2⟩) ?_
  · refine accept_ct (.inr rfl) (fun a b hab => sp hab.1.p2.ls hab.2.p2.ls)
      (fun a b hab => by rw [hab.1.t2, hab.2.t2, D1_eq h, D2_eq h, Ls_eq h]) fun a b hab => ?_
    rw [hab.1.p2.ls.a1, hab.2.p2.ls.a1, A, A, h.a, Ls_eq h, D1_eq h]
  · exact taint_block [] (fun a b hab => sp hab.1.ls hab.2.ls) (fun _ _ _ _ hr => absurd hr List.not_mem_nil)
      (by taint_decide)

theorem loop_ct :
    RelCT isa (fun a b => Inv s₁ 0 a ∧ Inv s₂ 0 b) (.loop rejBody (.nonzero .a3)) fun a b =>
      Inv s₁ 280 a ∧ Inv s₂ 280 b := by
  refine RelCT.mono (RelCT.loop (M := isa) (body := rejBody) (c := .nonzero .a3)
    (Q := fun a b => Inv s₁ 280 a ∧ Inv s₂ 280 b)
    (fun n a b => ∃ t, t < 280 ∧ n = 280 - t ∧ Inv s₁ t a ∧ Inv s₂ t b) (fun n => ?_) 280)
    (fun a b hab => ⟨0, by decide, rfl, hab⟩) (fun _ _ h => h)
  refine RelCT.mono (P := fun a b => ∃ t, t < 280 ∧ n = 280 - t ∧ Inv s₁ t a ∧ Inv s₂ t b)
    (RelCT.exists_ fun t => ?_) (fun _ _ hab => hab) (fun _ _ h => h)
  by_cases ht : t < 280
  · by_cases hn : n = 280 - t
    · refine RelCT.mono (P := fun a b => Inv s₁ t a ∧ Inv s₂ t b) (body_ct h ht) (fun _ _ hab => hab.2.2)
        fun a b ⟨⟨i₁, z₁⟩, ⟨i₂, z₂⟩⟩ => ⟨?_, fun e => ?_, fun e => ?_⟩
      · rw [Steps.eval_nonzero, Steps.eval_nonzero, z₁, z₂]
      · have : t + 1 = 280 := by
          have e' : (a.gpr .a3 != 0) = false := by rw [Steps.eval_nonzero] at e; exact Option.some.inj e
          rw [z₁] at e'; simpa using e'
        rw [this] at i₁ i₂; exact ⟨i₁, i₂⟩
      · have : t + 1 ≠ 280 := by
          have e' : (a.gpr .a3 != 0) = true := by rw [Steps.eval_nonzero] at e; exact Option.some.inj e
          rw [z₁] at e'; simpa using e'
        exact ⟨280 - (t + 1), by omega, t + 1, by omega, rfl, i₁, i₂⟩
    · exact RelCT.of_false fun _ _ hab => hn hab.2.1
  · exact RelCT.of_false fun _ _ hab => ht hab.1

end

/-! ## The sponge -/

/-- `absorb`'s arguments. -/
abbrev FA (s₀ t : State) : Prop := SEnv s₀ t ∧ Proof.Sha3.RISCV64.Stream.AbsorbArgs t (S s₀) (SEED s₀) 168 0 34

/-- `pad`'s arguments. -/
abbrev FP (s₀ t : State) : Prop :=
  SEnv s₀ t ∧ Proof.Sha3.RISCV64.Stream.PadArgs t (S s₀) 168 34 ∧ t.gpr .a3 = BitVec.ofNat 64 0x1f

/-- `squeeze`'s arguments. -/
abbrev FS (s₀ t : State) : Prop :=
  SEnv s₀ t ∧ Proof.Sha3.RISCV64.Stream.SqueezeArgs t (S s₀) (S s₀ + BitVec.ofNat 64 840) 168 0 840

section
variable {s₁ s₂ : State} (h : Two s₁ s₂)
include h

theorem env_sp {a b : State} (ha : SEnv s₁ a) (hb : SEnv s₂ b) : a.sp = b.sp := by
  rw [ha.sp, hb.sp, h.sp]

theorem eS : S s₂ = S s₁ := h.scr.symm
theorem eSEED : SEED s₂ = SEED s₁ := h.seed.symm

theorem absorbPhase_ct :
    RelCT isa (fun a b => (SEnv s₁ a ∧ stateAt a.mem (S s₁) = Spec.Sha3.zero) ∧
      (SEnv s₂ b ∧ stateAt b.mem (S s₂) = Spec.Sha3.zero))
      (.seq (.block absorbSeedArgs) (.call Spec.Sha3.absorbApi.name Impl.Sha3.RISCV64.Stream.absorb))
      fun _ _ => True := by
  have hw : ∀ s₀ s, Pre s₀ → SEnv s₀ s → WP isa (.block absorbSeedArgs) s (FA s₀) := fun s₀ s hp hs =>
    WP.mono (absorbArgs_ok hp hs) fun _ ⟨ht, _, ha⟩ => ⟨ht, ha⟩
  refine RelCT.seq (R := fun a b => FA s₁ a ∧ FA s₂ b) (relct_wp ?_ fun a b hab =>
    ⟨hw _ _ h.hp₁ hab.1.1, hw _ _ h.hp₂ hab.2.1⟩) ?_
  · exact taint_block [] (fun a b hab => env_sp h hab.1.1 hab.2.1) (fun _ _ _ _ hr => absurd hr List.not_mem_nil)
      (by taint_decide)
  refine absorbCall_ct (st := S s₁) (pa := SEED s₁) (rate := 168) (pos := 0) (pl := 34) fun a b ⟨⟨ea, aa⟩, ⟨eb, ab⟩⟩ => ?_
  have ca := call_covers h.hp₁ ea (rd := [⟨SEED s₁, 34⟩]) (wr := [⟨S s₁, 200⟩])
    (fun r hr => by rw [List.mem_singleton] at hr; exact hr)
    (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact lowS)
  have cb := call_covers h.hp₂ eb (rd := [⟨SEED s₂, 34⟩]) (wr := [⟨S s₂, 200⟩])
    (fun r hr => by rw [List.mem_singleton] at hr; exact hr)
    (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact lowS)
  rw [eS h, eSEED h] at ab cb
  exact ⟨env_sp h ea eb, aa, ab, ca.1, ca.2, cb.1, cb.2⟩

theorem padPhase_ct :
    RelCT isa (fun a b => (SEnv s₁ a ∧ Spec.Sha3.Repr a.mem (S s₁) 168 (B s₁) ∧ (a.gpr .a0).toNat = 34) ∧
      (SEnv s₂ b ∧ Spec.Sha3.Repr b.mem (S s₂) 168 (B s₂) ∧ (b.gpr .a0).toNat = 34))
      (.seq (.block padArgs) (.call Spec.Sha3.padApi.name Impl.Sha3.RISCV64.Stream.pad)) fun _ _ => True := by
  have hw : ∀ s₀ s, Pre s₀ → SEnv s₀ s → (s.gpr .a0).toNat = 34 → WP isa (.block padArgs) s (FP s₀) :=
    fun s₀ s hp hs h3 => WP.mono (padArgs_ok hp hs h3) fun _ ⟨ht, _, ha, a3⟩ => ⟨ht, ha, a3⟩
  refine RelCT.seq (R := fun a b => FP s₁ a ∧ FP s₂ b) (relct_wp ?_ fun a b hab =>
    ⟨hw _ _ h.hp₁ hab.1.1 hab.1.2.2, hw _ _ h.hp₂ hab.2.1 hab.2.2.2⟩) ?_
  · exact taint_block [] (fun a b hab => env_sp h hab.1.1 hab.2.1) (fun _ _ _ _ hr => absurd hr List.not_mem_nil)
      (by taint_decide)
  refine padCall_ct (st := S s₁) (rate := 168) (pos := 34) fun a b ⟨⟨ea, aa, _⟩, ⟨eb, ab, _⟩⟩ => ?_
  have ca := call_covers h.hp₁ ea (rd := []) (wr := [⟨S s₁, 200⟩])
    (fun r hr => absurd hr List.not_mem_nil)
    (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact lowS)
  have cb := call_covers h.hp₂ eb (rd := []) (wr := [⟨S s₂, 200⟩])
    (fun r hr => absurd hr List.not_mem_nil)
    (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact lowS)
  rw [eS h] at ab cb
  exact ⟨env_sp h ea eb, aa, ab, ca.1, ca.2, cb.1, cb.2⟩

theorem squeezePhase_ct :
    RelCT isa (fun a b =>
      (SEnv s₁ a ∧ stateAt a.mem (S s₁) = VG.Proof.MlKem.padded 168 Spec.Sha3.shakeSuffix (B s₁)) ∧
      (SEnv s₂ b ∧ stateAt b.mem (S s₂) = VG.Proof.MlKem.padded 168 Spec.Sha3.shakeSuffix (B s₂)))
      (.seq (.block squeezeArgs) (.call Spec.Sha3.squeezeApi.name Impl.Sha3.RISCV64.Stream.squeeze))
      fun _ _ => True := by
  have hw : ∀ s₀ s, Pre s₀ → SEnv s₀ s → WP isa (.block squeezeArgs) s (FS s₀) := fun s₀ s hp hs =>
    WP.mono (squeezeArgs_ok hp hs) fun _ ⟨ht, _, ha⟩ => ⟨ht, ha⟩
  refine RelCT.seq (R := fun a b => FS s₁ a ∧ FS s₂ b) (relct_wp ?_ fun a b hab =>
    ⟨hw _ _ h.hp₁ hab.1.1, hw _ _ h.hp₂ hab.2.1⟩) ?_
  · exact taint_block [] (fun a b hab => env_sp h hab.1.1 hab.2.1) (fun _ _ _ _ hr => absurd hr List.not_mem_nil)
      (by taint_decide)
  have wq : ∀ {s₀ : State} {r : Region}, r ∈ [(⟨S s₀, 200⟩ : Region), ⟨S s₀ + BitVec.ofNat 64 840, 840⟩] →
      ∃ o n, o + n ≤ 1680 ∧ r = ⟨S s₀ + BitVec.ofNat 64 o, n⟩ := fun hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact lowS
    · exact ⟨840, 840, by decide, rfl⟩
  refine squeezeCall_ct (st := S s₁) (pa := S s₁ + BitVec.ofNat 64 840) (rate := 168) (pos := 0) (pl := 840)
    fun a b ⟨⟨ea, aa⟩, ⟨eb, ab⟩⟩ => ?_
  have ca := call_covers h.hp₁ ea (rd := []) (wr := [⟨S s₁, 200⟩, ⟨S s₁ + BitVec.ofNat 64 840, 840⟩])
    (fun r hr => absurd hr List.not_mem_nil) (fun r hr => wq hr)
  have cb := call_covers h.hp₂ eb (rd := []) (wr := [⟨S s₂, 200⟩, ⟨S s₂ + BitVec.ofNat 64 840, 840⟩])
    (fun r hr => absurd hr List.not_mem_nil) (fun r hr => wq hr)
  rw [eS h] at ab cb
  exact ⟨env_sp h ea eb, aa, ab, ca.1, ca.2, cb.1, cb.2⟩

/-! ## The whole function -/

/-- What holds after each phase, in one run. -/
abbrev E1 (s₀ s : State) : Prop := SEnv s₀ s ∧ stateAt s.mem (S s₀) = Spec.Sha3.zero
abbrev E2 (s₀ s : State) : Prop := SEnv s₀ s ∧ Spec.Sha3.Repr s.mem (S s₀) 168 (B s₀) ∧ (s.gpr .a0).toNat = 34
abbrev E3 (s₀ s : State) : Prop :=
  SEnv s₀ s ∧ stateAt s.mem (S s₀) = VG.Proof.MlKem.padded 168 Spec.Sha3.shakeSuffix (B s₀)
abbrev E4 (s₀ s : State) : Prop :=
  SEnv s₀ s ∧ Spec.Sha3.bytesAt s.mem (S s₀ + BitVec.ofNat 64 840) 840 = xof (B s₀) 840

theorem all_ct : RelCT isa (fun a b => a = s₁ ∧ b = s₂) sampleNTT fun _ _ => True := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  refine RelCT.seq (R := fun a b => E1 s₁ a ∧ E1 s₂ b) (relct_wp ?_ fun a b hab =>
    ⟨by rw [hab.1]; exact setup_ok hp₁, by rw [hab.2]; exact setup_ok hp₂⟩) ?_
  · exact taint_block [.a2] (fun a b hab => by rw [hab.1, hab.2]; exact h.sp) (fun a b hab r hr => by
      rw [List.mem_singleton] at hr; subst hr; rw [hab.1, hab.2]; exact h.scr) (by taint_decide)
  refine RelCT.seq (R := fun a b => E2 s₁ a ∧ E2 s₂ b) (relct_wp (absorbPhase_ct h) fun a b hab =>
    ⟨absorb_phase hp₁ hab.1.1 hab.1.2, absorb_phase hp₂ hab.2.1 hab.2.2⟩) ?_
  refine RelCT.seq (R := fun a b => E3 s₁ a ∧ E3 s₂ b) (relct_wp (padPhase_ct h) fun a b hab =>
    ⟨pad_phase hp₁ hab.1.1 hab.1.2.1 hab.1.2.2, pad_phase hp₂ hab.2.1 hab.2.2.1 hab.2.2.2⟩) ?_
  refine RelCT.seq (R := fun a b => E4 s₁ a ∧ E4 s₂ b) (relct_wp (squeezePhase_ct h) fun a b hab =>
    ⟨squeeze_phase hp₁ hab.1.1 hab.1.2, squeeze_phase hp₂ hab.2.1 hab.2.2⟩) ?_
  refine RelCT.seq (R := fun a b => Inv s₁ 0 a ∧ Inv s₂ 0 b) (relct_wp ?_ fun a b hab =>
    ⟨init_ok hp₁ hab.1.1 hab.1.2, init_ok hp₂ hab.2.1 hab.2.2⟩) ?_
  · exact taint_block [] (fun a b hab => env_sp h hab.1.1 hab.2.1) (fun _ _ _ _ hr => absurd hr List.not_mem_nil)
      (by taint_decide)
  refine RelCT.seq (R := fun a b => Inv s₁ 280 a ∧ Inv s₂ 280 b) (loop_ct h) ?_
  exact taint_block [.s9] (fun a b hab => env_sp h hab.1.ls.env hab.2.ls.env) (fun a b hab r hr => by
    rw [List.mem_singleton] at hr; subst hr; rw [hab.1.ls.env.g9, hab.2.ls.env.g9, S, S, h.scr])
    (by taint_decide)

end

/-! ## Verified -/

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 34⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

theorem verified :
    Verified RISCV64.target Impl.MlKem.RISCV64.sampleNTT (Spec.MlKem.sampleNTTContract RISCV64.abi 1168) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, hd⟩ := correct (pre_of hs)
    exact ⟨t, s', he, ⟨hd.pres, hd.sp, hd.ra⟩, post_of hd⟩
  · have hp₁ := pre_of h₁
    have hp₂ := pre_of h₂
    sig_pub [Spec.MlKem.sampleNTTContract, Spec.MlKem.sampleNTTSig, RISCV64.abi, RISCV64.argRegs] at hpub
    obtain ⟨hsp, hb, h3, h4, h5⟩ := hpub
    have two : Two s₁ s₂ := ⟨hp₁, hp₂, hsp, h3, h4, h5,
      (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hb⟩
    exact (all_ct two s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Spec.MlKem.sampleNTTContract, Spec.MlKem.sampleNTTSig, RISCV64.abi, RISCV64.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | decide +kernel

end VG.Proof.MlKem.RISCV64.Sample
