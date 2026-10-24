module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Sample
public import VerifiedGarbage.Proof.Dsa.SameTrace
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Sample
meta import VerifiedGarbage.Proof.Dsa.SameTrace
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# DSA sampling on PPC64LE: constant time

Two runs of the sampler with the same public data `E` (q's significant
octets, the tape's place and length, the frame), from the same count of
octets consumed and draws left, and with the same trace of
`Random.sample` from there, leak the same trace (`sample_st`). The taint
analysis checks each piece from the registers both runs agree on
(`st_taint`): the tape's length, the octets consumed and the width decide
the short test and the draw's addresses; the candidate's acceptance, which
the taint analysis sees secret, is the head of the sampling trace
(`acc_iff`), and so are the loop's decisions (`step_ok`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Rnd

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random
open VG.Proof.Mont
open VG.Spec.Dsa.Random (sample candidate drawBytes)
open VG.Proof.Dsa.Random (sampleStatus)

/-- Two states agree on the registers `rs`. -/
def EqRegs (s₁ s₂ : State) : List Reg → Prop
  | [] => True
  | [r] => s₁.gpr r = s₂.gpr r
  | r :: rs => s₁.gpr r = s₂.gpr r ∧ EqRegs s₁ s₂ rs

theorem EqRegs.mem {s₁ s₂ : State} : ∀ {rs : List Reg}, EqRegs s₁ s₂ rs → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r
  | [], _, _, hr => absurd hr List.not_mem_nil
  | [_], h, _, hr => by rw [List.mem_singleton.mp hr]; exact h
  | _ :: _ :: _, h, _, hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact h.1
    · exact EqRegs.mem h.2 _ hr

theorem EqRegs.single {s₁ s₂ : State} {r : Reg} (h : s₁.gpr r = s₂.gpr r) : EqRegs s₁ s₂ [r] := h

/-- Code the taint analysis checks from the registers `rs`, which two
states with the same stack pointer agree on, leaks the same trace. -/
theorem st_taint {c : Prog isa} (rs : List Reg) {s₁ s₂ : State} (hsp : s₁.sp = s₂.sp)
    (hr : EqRegs s₁ s₂ rs) {hc : VG.Taint.Hint T}
    (h : (taint.check (ofRegs rs) c hc).isSome = true) : SameTrace isa c s₁ s₂ :=
  SameTrace.of_relCT (RelCT.taint (A := taint) (P := fun a b => a = s₁ ∧ b = s₂) (ofRegs rs)
    (fun _ _ ⟨e₁, e₂⟩ => by
      subst e₁ e₂
      exact ⟨hsp, fun r hm => hr.mem r (RegSet.mem_ofList.mp hm)⟩) h) ⟨rfl, rfl⟩

/-- `RelCT` from the traces of the runs from each related pair, and what
each run satisfies. -/
theorem relCT_of {P Q : State → State → Prop} {c : Prog isa}
    (h : ∀ s₁ s₂, P s₁ s₂ → SameTrace isa c s₁ s₂ ∧ ∃ F₁ F₂ : State → Prop, WP isa c s₁ F₁ ∧ WP isa c s₂ F₂ ∧
      ∀ t₁ t₂, F₁ t₁ → F₂ t₂ → Q t₁ t₂) : RelCT isa P c Q := by
  intro s₁ s₂ tr₁ tr₂ t₁ t₂ hp e₁ e₂
  obtain ⟨hs, F₁, F₂, ⟨_, u₁, f₁, g₁⟩, ⟨_, u₂, f₂, g₂⟩, hq⟩ := h _ _ hp
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  exact ⟨hs _ _ _ _ e₁ e₂, hq _ _ g₁ g₂⟩

/-- A loop whose iterations, from related states, leak the same trace and
agree on the condition. -/
theorem st_loop {body : Prog isa} {c : Cond} (I : Nat → State → State → Prop)
    (hstep : ∀ n s₁ s₂, I n s₁ s₂ → SameTrace isa body s₁ s₂ ∧ ∃ F₁ F₂ : State → Prop,
      WP isa body s₁ F₁ ∧ WP isa body s₂ F₂ ∧ ∀ t₁ t₂, F₁ t₁ → F₂ t₂ →
        isa.eval c t₁ = isa.eval c t₂ ∧ (isa.eval c t₁ = some true → ∃ m < n, I m t₁ t₂))
    {n : Nat} {s₁ s₂ : State} (h : I n s₁ s₂) : SameTrace isa (.loop body c) s₁ s₂ :=
  SameTrace.of_relCT (RelCT.loop (Q := fun _ _ => True) I (fun n => relCT_of fun s₁ s₂ hi => by
    obtain ⟨hs, F₁, F₂, w₁, w₂, hq⟩ := hstep n s₁ s₂ hi
    exact ⟨hs, F₁, F₂, w₁, w₂, fun t₁ t₂ f₁ f₂ => ⟨(hq t₁ t₂ f₁ f₂).1, fun _ => trivial, (hq t₁ t₂ f₁ f₂).2⟩⟩) n) h

/-- A run of `.seq c d` is one of `c`, which keeps the stack pointer. -/
theorem WP.of_seq {c d : Prog isa} {s : State} {Q : State → Prop} (h : WP isa (.seq c d) s Q) :
    WP isa c s fun t => t.sp = s.sp := by
  obtain ⟨_, _, e, _⟩ := h
  cases e with
  | seq a _ => exact ⟨_, _, a, VG.PPC64LE.Exec.sp a⟩

/-- A draw at `u` of a tape with `W` octets left is accepted exactly when the
sampling trace from there starts with an acceptance. -/
theorem acc_iff {E : SE} {qb R : List Byte} {u d : Nat} (hQ : E.Q qb) (hR : R.length = E.rl)
    (hs : u + E.W ≤ E.rl) (hd : 1 ≤ d) :
    acc qb R u E.W ↔ (sample (Spec.Dsa.decodeBE qb) d (R.drop u)).trace.head? = some 1 := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have hs' : drawBytes (Spec.Dsa.decodeBE qb) ≤ (R.drop u).length := by
    rw [List.length_drop, hR, hQ.draw]; omega
  by_cases ha : acc qb R u E.W
  · have hS := Dsa.Random.sample_accept _ d' _ hQ.gt hs' (by rw [hQ.draw]; exact ha)
    rw [hS]
    exact iff_of_true ha rfl
  · have hS := Dsa.Random.sample_reject _ d' _ hQ.gt hs' (by rw [hQ.draw]; exact ha)
    rw [hS]
    exact iff_of_false ha (by simp)

/-- Two draws with the same public data, from the same octets consumed `u`
and draws left `d`, and the same sampling trace from there, leak the same
trace. -/
theorem draw_st {E : SE} {qb R₁ R₂ : List Byte} {s₁ s₂ : State} {u d : Nat} (hE : E.Ok) (hQ : E.Q qb)
    (h₁ : SEnv E R₁ s₁) (h₂ : SEnv E R₂ s₂) (a25 : s₁.gpr .r25 = BitVec.ofNat 64 u)
    (b25 : s₂.gpr .r25 = BitVec.ofNat 64 u) (hu : u ≤ E.rl) (a17 : s₁.gpr .r17 = BitVec.ofNat 64 d)
    (b17 : s₂.gpr .r17 = BitVec.ofNat 64 d) (hd : 1 ≤ d)
    (ht : (sample (Spec.Dsa.decodeBE qb) d (R₁.drop u)).trace = (sample (Spec.Dsa.decodeBE qb) d (R₂.drop u)).trace) :
    SameTrace isa draw s₁ s₂ := by
  have hsp : s₁.sp = s₂.sp := h₁.sp.trans h₂.sp.symm
  unfold draw
  refine SameTrace.seq (st_taint [.r24, .r25, .r28] hsp ⟨h₁.r24.trans h₂.r24.symm, a25.trans b25.symm,
      h₁.r28.trans h₂.r28.symm⟩ (by taint_decide)) (shortTest_ok hE h₁ a25 hu) (shortTest_ok hE h₂ b25 hu)
    fun t₁ t₂ ⟨⟨c3, m1⟩, k1⟩ ⟨⟨d3, m2⟩, k2⟩ => ?_
  have g1 : SEnv E R₁ t₁ := h₁.step hE k1 (o := 0) (n := 0) (by omega) (by rw [m1]; exact Outside.refl _ _ _ _)
  have g2 : SEnv E R₂ t₂ := h₂.step hE k2 (o := 0) (n := 0) (by omega) (by rw [m2]; exact Outside.refl _ _ _ _)
  have tsp : t₁.sp = t₂.sp := g1.sp.trans g2.sp.symm
  refine SameTrace.ite (by rw [VG.PPC64LE.eval_nonzero, VG.PPC64LE.eval_nonzero, c3, d3])
    (fun _ => by exact st_taint [] tsp trivial (by taint_decide)) (fun hs => ?_)
  have hs' : ¬ E.rl - u < E.W := fun hc => by
    rw [VG.PPC64LE.eval_nonzero, c3, ite_eq_left hc] at hs
    exact absurd hs (by decide)
  have t25 : t₁.gpr .r25 = BitVec.ofNat 64 u := (k1.gpr .r25 (by decide)).trans a25
  have u25 : t₂.gpr .r25 = BitVec.ofNat 64 u := (k2.gpr .r25 (by decide)).trans b25
  refine SameTrace.seq (st_taint [.r21, .r23, .r25, .r27, .r28] tsp ⟨g1.r21.trans g2.r21.symm,
      g1.r23.trans g2.r23.symm, t25.trans u25.symm, g1.r27.trans g2.r27.symm, g1.r28.trans g2.r28.symm⟩
      (by taint_decide)) (copyRange_ok hE hQ g1 t25 (by omega)) (copyRange_ok hE hQ g2 u25 (by omega))
    fun x₁ x₂ ⟨⟨e1, _, _, x6, _⟩, kx1⟩ ⟨⟨e2, _, _, y6, _⟩, kx2⟩ => ?_
  have hacc : acc qb R₁ u E.W ↔ acc qb R₂ u E.W := by
    rw [acc_iff hQ h₁.R_length (by omega) hd, acc_iff hQ h₂.R_length (by omega) hd, ht]
  have xsp : x₁.sp = x₂.sp := e1.sp.trans e2.sp.symm
  have e17 : EqRegs x₁ x₂ [.r17] := ((kx1.gpr .r17 (by decide)).trans ((k1.gpr .r17 (by decide)).trans a17)).trans
    ((kx2.gpr .r17 (by decide)).trans ((k2.gpr .r17 (by decide)).trans b17)).symm
  unfold drawFinish
  refine SameTrace.ite (by rw [VG.PPC64LE.eval_nonzero, VG.PPC64LE.eval_nonzero, x6, y6]; simp only [hacc])
    (fun _ => by exact st_taint [] xsp trivial (by taint_decide)) (fun _ => by exact st_taint [.r17] xsp e17 (by taint_decide))

/-- A draw and the loop's test, against `Random.sample`: it goes on, with a
draw fewer, after a rejection that leaves draws, or it ends. -/
theorem step_ok {E : SE} {qb R : List Byte} {s : State} {u d : Nat} (hE : E.Ok) (hQ : E.Q qb)
    (h : SEnv E R s) (h25 : s.gpr .r25 = BitVec.ofNat 64 u) (hu : u ≤ E.rl)
    (h17 : s.gpr .r17 = BitVec.ofNat 64 d) (hd : 1 ≤ d) (hd' : d ≤ 128) (h31 : s.gpr .r31 = BitVec.ofNat 64 4) :
    WP isa (.seq draw (.block [.subi .r3 .r31 4])) s fun t =>
      SEnv E R t ∧
        ((isa.eval (.zero .d .r3) t = some true ∧ t.gpr .r17 = BitVec.ofNat 64 (d - 1) ∧
            t.gpr .r25 = BitVec.ofNat 64 (u + E.W) ∧ t.gpr .r31 = BitVec.ofNat 64 4 ∧ 2 ≤ d ∧
            u + E.W ≤ E.rl ∧
            sample (Spec.Dsa.decodeBE qb) d (R.drop u) =
              rejectOf E.W (sample (Spec.Dsa.decodeBE qb) (d - 1) (R.drop (u + E.W)))) ∨
          (isa.eval (.zero .d .r3) t = some false ∧
            ((sample (Spec.Dsa.decodeBE qb) d (R.drop u)).trace.head? = some 0 → d = 1))) := by
  refine WP.seq (WP.mono (draw_ok hE hQ h h25 hu h17 hd hd' h31) fun t₁ ⟨h1, _, _, hc⟩ => ?_)
  refine WP.mono (WP.keep [.r3] (Q := fun t₂ => t₂.mem = t₁.mem ∧
    t₂.gpr .r3 = t₁.gpr .r31 - BitVec.ofNat 64 4) (by prun) (by decide)) fun t₂ ⟨⟨m2, a3⟩, k2⟩ => ?_
  have h2 : SEnv E R t₂ := h1.step hE k2 (o := 0) (n := 0) (by omega) (by rw [m2]; exact Outside.refl _ _ _ _)
  refine ⟨h2, ?_⟩
  rcases hc with ⟨b31, h2d, b17, b25, hu', hrej⟩ | ⟨b31, -, -, hh⟩
  · refine .inl ⟨?_, (k2.gpr .r17 (by decide)).trans b17, (k2.gpr .r25 (by decide)).trans b25,
      (k2.gpr .r31 (by decide)).trans b31, h2d, hu', hrej⟩
    rw [VG.PPC64LE.eval_zero, a3, b31]; rfl
  · refine .inr ⟨?_, hh⟩
    rw [VG.PPC64LE.eval_zero, a3, b31, status_sub4 _ (by have := sampleStatus_le (sample (Spec.Dsa.decodeBE qb) d (R.drop u)); omega)]

/-- The sampling loop's two runs, with `d` draws left. -/
def DI (E : SE) (qb R₁ R₂ : List Byte) (d : Nat) (s₁ s₂ : State) : Prop :=
  ∃ u, 1 ≤ d ∧ d ≤ 128 ∧ SEnv E R₁ s₁ ∧ SEnv E R₂ s₂ ∧ s₁.gpr .r25 = BitVec.ofNat 64 u ∧
    s₂.gpr .r25 = BitVec.ofNat 64 u ∧ u ≤ E.rl ∧ s₁.gpr .r17 = BitVec.ofNat 64 d ∧
    s₂.gpr .r17 = BitVec.ofNat 64 d ∧ s₁.gpr .r31 = BitVec.ofNat 64 4 ∧ s₂.gpr .r31 = BitVec.ofNat 64 4 ∧
    (sample (Spec.Dsa.decodeBE qb) d (R₁.drop u)).trace = (sample (Spec.Dsa.decodeBE qb) d (R₂.drop u)).trace

theorem sampleLoop_st {E : SE} {qb R₁ R₂ : List Byte} (hE : E.Ok) (hQ : E.Q qb) {d : Nat} {s₁ s₂ : State}
    (h : DI E qb R₁ R₂ d s₁ s₂) :
    SameTrace isa (.loop (.seq draw (.block [.subi .r3 .r31 4])) (.zero .d .r3)) s₁ s₂ := by
  refine st_loop (DI E qb R₁ R₂) (fun n s₁ s₂ ⟨u, hd, hd', h₁, h₂, a25, b25, hu, a17, b17, a31, b31, ht⟩ => ?_) h
  refine ⟨SameTrace.seq (draw_st hE hQ h₁ h₂ a25 b25 hu a17 b17 hd ht)
    (draw_ok hE hQ h₁ a25 hu a17 hd hd' a31) (draw_ok hE hQ h₂ b25 hu b17 hd hd' b31)
    fun t₁ t₂ ⟨e₁, _⟩ ⟨e₂, _⟩ => by exact st_taint [] (e₁.sp.trans e₂.sp.symm) trivial (by taint_decide), _, _,
    step_ok hE hQ h₁ a25 hu a17 hd hd' a31, step_ok hE hQ h₂ b25 hu b17 hd hd' b31,
    fun t₁ t₂ ⟨e₁, c₁⟩ ⟨e₂, c₂⟩ => ?_⟩
  rcases c₁ with ⟨v₁, x17, x25, x31, hn, hu', hr₁⟩ | ⟨v₁, hh₁⟩ <;>
    rcases c₂ with ⟨v₂, y17, y25, y31, hn₂, -, hr₂⟩ | ⟨v₂, hh₂⟩
  · refine ⟨v₁.trans v₂.symm, fun _ => ⟨n - 1, by omega, u + E.W, by omega, by omega, e₁, e₂, x25, y25, hu',
      x17, y17, x31, y31, ?_⟩⟩
    rw [hr₁, hr₂] at ht
    exact (List.cons.inj ht).2
  · rw [hr₁] at ht
    have := hh₂ (by rw [← ht]; rfl)
    omega
  · rw [hr₂] at ht
    have := hh₁ (by rw [ht]; rfl)
    have := hd'
    omega
  · exact ⟨v₁.trans v₂.symm, fun hc => by rw [v₁] at hc; cases hc⟩

/-- `sample` from the same public data, octets consumed and sampling trace. -/
theorem sample_st {E : SE} {qb R₁ R₂ : List Byte} {s₁ s₂ : State} {u : Nat} (hE : E.Ok) (hQ : E.Q qb)
    (h₁ : SEnv E R₁ s₁) (h₂ : SEnv E R₂ s₂) (a25 : s₁.gpr .r25 = BitVec.ofNat 64 u)
    (b25 : s₂.gpr .r25 = BitVec.ofNat 64 u) (hu : u ≤ E.rl)
    (ht : (sample (Spec.Dsa.decodeBE qb) 128 (R₁.drop u)).trace = (sample (Spec.Dsa.decodeBE qb) 128 (R₂.drop u)).trace) :
    SameTrace isa Impl.Dsa.PPC64LE.Random.sample s₁ s₂ := by
  have W : ∀ {s : State}, WP isa (.block [.li .r17 128, .li .r31 4]) s fun t =>
      (t.mem = s.mem ∧ t.gpr .r17 = BitVec.ofNat 64 128 ∧ t.gpr .r31 = BitVec.ofNat 64 4) ∧
        Keep [.r17, .r31] s t := fun {s} => WP.keep [.r17, .r31] (by prun) (by decide)
  unfold Impl.Dsa.PPC64LE.Random.sample
  refine SameTrace.seq (st_taint [] (h₁.sp.trans h₂.sp.symm) trivial (by taint_decide)) W W
    fun t₁ t₂ ⟨⟨m1, a17, a31⟩, k1⟩ ⟨⟨m2, b17, b31⟩, k2⟩ => sampleLoop_st hE hQ ⟨u, by decide, by decide,
      h₁.step hE k1 (o := 0) (n := 0) (by omega) (by rw [m1]; exact Outside.refl _ _ _ _),
      h₂.step hE k2 (o := 0) (n := 0) (by omega) (by rw [m2]; exact Outside.refl _ _ _ _),
      (k1.gpr _ (by decide)).trans a25, (k2.gpr _ (by decide)).trans b25, hu, a17, b17, a31, b31, ht⟩

end VG.Proof.Dsa.PPC64LE.Rnd
