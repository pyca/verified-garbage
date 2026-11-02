module

public import VerifiedGarbage.Proof.Dsa.RISCV64.RndSample
public import VerifiedGarbage.Proof.Dsa.SameTrace
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
meta import VerifiedGarbage.Proof.Dsa.RISCV64.RndSample
meta import VerifiedGarbage.Proof.Dsa.SameTrace
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
import VerifiedGarbage.Proof.Dsa.RISCV64.RndDraw
import VerifiedGarbage.Proof.Dsa.RISCV64.Ctx
import VerifiedGarbage.Proof.Dsa.RandomResult
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Dsa.RISCV64.RndDraw
meta import VerifiedGarbage.Proof.Dsa.RISCV64.Ctx
meta import VerifiedGarbage.Proof.Dsa.RandomResult
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps

/-!
# DSA sampling on RISC-V: constant time

As on PPC64LE (`Proof/Dsa/PPC64LE/Random/CT.lean`). Two runs of the sampler
with the same public data `E` (q's significant octets, the tape's place
and length, the frame), from the same count of octets consumed and draws
left, and with the same trace of `Random.sample` from there, leak the same
trace (`sample_st`). The taint analysis checks each piece from the
registers both runs agree on (`st_taint`): the tape's length, the octets
consumed and the width decide the short test and the draw's addresses
(the sampler loads only octets of the tape, the nonce and q, which it uses
as values); the candidate's acceptance, which the taint analysis sees
secret, is the head of the sampling trace (`acc_iff`), and so are the
loop's decisions (`step_ok`). Also the pieces the key generation's and the
randomized signing's constant time share: `st_alloc` for the frame.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.Rnd

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Bignum.RISCV64 VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64.Random
open VG.Proof.Mont
open VG.Spec.Dsa.Random (sample candidate drawBytes)
open VG.Proof.Dsa.Random (sampleStatus)

/-- Two states agree on the registers `rs`. -/
def EqRegs (s₁ s₂ : State) : List Reg → Prop
  | [] => True
  | [r] => s₁.gpr r = s₂.gpr r
  | r :: rs => s₁.gpr r = s₂.gpr r ∧ EqRegs s₁ s₂ rs

theorem EqRegs.mem {s₁ s₂ : State} : ∀ {rs : List Reg}, EqRegs s₁ s₂ rs → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r
  | [], _, _, h => absurd h List.not_mem_nil
  | [_], h, _, hm => by rw [List.mem_singleton.mp hm]; exact h
  | _ :: _ :: _, ⟨h₁, h₂⟩, _, hm => by
    rcases List.mem_cons.mp hm with rfl | hm
    · exact h₁
    · exact EqRegs.mem h₂ _ hm

theorem EqRegs.single {s₁ s₂ : State} {r : Reg} (h : s₁.gpr r = s₂.gpr r) : EqRegs s₁ s₂ [r] := h

theorem EqRegs.sub {s₁ s₂ : State} {rs : List Reg} (h : EqRegs s₁ s₂ rs) {rs' : List Reg}
    (hs : ∀ r ∈ rs', r ∈ rs := by decide) : EqRegs s₁ s₂ rs' := by
  induction rs' with
  | nil => trivial
  | cons r rs' ih =>
    cases rs' with
    | nil => exact h.mem r (hs r (List.mem_singleton_self r))
    | cons r' rs'' =>
      exact ⟨h.mem r (hs r (List.mem_cons_self ..)), ih fun x hx => hs x (List.mem_cons_of_mem _ hx)⟩

/-- Code the taint analysis checks from the registers `rs`, which two
states with the same stack pointer agree on, leaks the same trace. -/
theorem st_taint {c : Prog isa} (rs : List Reg) {s₁ s₂ : State} (hsp : s₁.sp = s₂.sp)
    (hr : EqRegs s₁ s₂ rs) {hc : VG.Taint.Hint taint.T}
    (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true) : SameTrace isa c s₁ s₂ :=
  SameTrace.of_relCT (RelCT.taint (A := taint) (P := fun a b => a = s₁ ∧ b = s₂) (Taint.ofRegs rs)
    (fun _ _ ⟨e₁, e₂⟩ => by
      subst e₁ e₂
      exact ⟨hsp, fun r hm => hr.mem r (Taint.mem_ofRegs.mp hm)⟩) h) ⟨rfl, rfl⟩

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

/-- Allocating and freeing a frame leaks nothing. -/
theorem relCT_alloc {bytes : Nat} {body : Prog isa} {P R : State → State → Prop}
    (hb : RelCT isa (fun a b => ∃ s t, P s t ∧ a = allocd bytes s ∧ b = allocd bytes t) body R) :
    RelCT isa P (.frame (.alloc bytes) body (.free bytes)) fun _ _ => True := by
  intro s t ts tt s' t' hp es et
  have alloc_eq : ∀ {a b : State}, isa.push (.alloc bytes) a = some b → b = allocd bytes a := by
    intro a b h
    simp only [isa, push] at h
    split at h <;> cases h
    rfl
  cases es with
  | frame ps bs qs =>
    cases et with
    | frame pt bt qt =>
      have ea := alloc_eq ps
      have eb := alloc_eq pt
      subst ea eb
      obtain ⟨rfl, _⟩ := hb _ _ _ _ _ _ ⟨s, t, hp, rfl, rfl⟩ bs bt
      exact ⟨rfl, trivial⟩

theorem st_alloc {n : Nat} {body : Prog isa} {s₁ s₂ : State}
    (h : SameTrace isa body (allocd n s₁) (allocd n s₂)) :
    SameTrace isa (.frame (.alloc n) body (.free n)) s₁ s₂ :=
  SameTrace.of_relCT (relCT_alloc (P := fun a b => a = s₁ ∧ b = s₂) (R := fun _ _ => True)
    (h.to_relCT.mono (fun a b ⟨_, _, ⟨e₁, e₂⟩, ea, eb⟩ => by subst e₁ e₂; exact ⟨ea, eb⟩) fun _ _ h => h))
    ⟨rfl, rfl⟩

theorem beq_of_iff {x : BitVec 64} {P : Prop} [Decidable P] (h : x = 0 ↔ P) : (x == 0) = decide P := by
  by_cases hp : P
  · simp [h.mpr hp, hp]
  · rw [decide_eq_false hp]
    exact beq_eq_false_iff_ne.mpr fun e => hp (h.mp e)

/-- A run of `.seq c d` is one of `c`, which keeps the stack pointer. -/
theorem WP.of_seq {c d : Prog isa} {s : State} {Q : State → Prop} (h : WP isa (.seq c d) s Q) :
    WP isa c s fun t => t.sp = s.sp := by
  obtain ⟨_, _, e, _⟩ := h
  cases e with
  | seq a _ => exact ⟨_, _, a, Exec.sp a⟩

/-! ## The sampler -/

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
    (h₁ : SEnv E R₁ s₁) (h₂ : SEnv E R₂ s₂) (a5 : s₁.gpr .s5 = BitVec.ofNat 64 u)
    (b5 : s₂.gpr .s5 = BitVec.ofNat 64 u) (hu : u ≤ E.rl) (a11 : s₁.gpr .s11 = BitVec.ofNat 64 d)
    (b11 : s₂.gpr .s11 = BitVec.ofNat 64 d) (hd : 1 ≤ d)
    (ht : (sample (Spec.Dsa.decodeBE qb) d (R₁.drop u)).trace = (sample (Spec.Dsa.decodeBE qb) d (R₂.drop u)).trace) :
    SameTrace isa draw s₁ s₂ := by
  have hsp : s₁.sp = s₂.sp := h₁.sp.trans h₂.sp.symm
  unfold draw
  refine SameTrace.seq (st_taint [.s4, .s5, .s8] hsp ⟨h₁.s4.trans h₂.s4.symm, a5.trans b5.symm,
      h₁.s8.trans h₂.s8.symm⟩ (by taint_decide)) (wp_sp (shortTest_ok hE h₁ a5 hu))
    (wp_sp (shortTest_ok hE h₂ b5 hu)) fun t₁ t₂ ⟨⟨⟨c3, m1⟩, k1⟩, sp1⟩ ⟨⟨⟨d3, m2⟩, k2⟩, sp2⟩ => ?_
  have g1 : SEnv E R₁ t₁ := h₁.stepM hE k1 sp1 m1
  have g2 : SEnv E R₂ t₂ := h₂.stepM hE k2 sp2 m2
  have tsp : t₁.sp = t₂.sp := g1.sp.trans g2.sp.symm
  refine SameTrace.ite (by rw [Steps.eval_nonzero, Steps.eval_nonzero, c3, d3])
    (fun _ => by exact st_taint [] tsp trivial (by taint_decide)) (fun hs => ?_)
  have hs' : ¬ E.rl - u < E.W := fun hc => by
    rw [Steps.eval_nonzero, c3, ite_eq_left hc] at hs
    exact absurd hs (by decide)
  have t5 : t₁.gpr .s5 = BitVec.ofNat 64 u := (k1.gpr (by decide)).trans a5
  have u5 : t₂.gpr .s5 = BitVec.ofNat 64 u := (k2.gpr (by decide)).trans b5
  refine SameTrace.seq (st_taint [.s2, .s3, .s5, .s7, .s8, .s9] tsp ⟨g1.s2.trans g2.s2.symm,
      g1.s3.trans g2.s3.symm, t5.trans u5.symm, g1.s7.trans g2.s7.symm, g1.s8.trans g2.s8.symm,
      g1.s9.trans g2.s9.symm⟩ (by taint_decide)) (copyRange_ok hE hQ g1 t5 (by omega))
    (copyRange_ok hE hQ g2 u5 (by omega))
    fun x₁ x₂ ⟨⟨e1, _, _, x6, _⟩, kx1⟩ ⟨⟨e2, _, _, y6, _⟩, kx2⟩ => ?_
  have hacc : acc qb R₁ u E.W ↔ acc qb R₂ u E.W := by
    rw [acc_iff hQ h₁.R_length (by omega) hd, acc_iff hQ h₂.R_length (by omega) hd, ht]
  have xsp : x₁.sp = x₂.sp := e1.sp.trans e2.sp.symm
  have e11 : EqRegs x₁ x₂ [.s11] := ((kx1.gpr (by decide)).trans ((k1.gpr (by decide)).trans a11)).trans
    ((kx2.gpr (by decide)).trans ((k2.gpr (by decide)).trans b11)).symm
  unfold drawFinish
  refine SameTrace.ite (by rw [Steps.eval_nonzero, Steps.eval_nonzero, x6, y6]; simp only [hacc])
    (fun _ => by exact st_taint [] xsp trivial (by taint_decide))
    (fun _ => by exact st_taint [.s11] xsp e11 (by taint_decide))

/-- A draw and the loop's test, against `Random.sample`: it goes on, with a
draw fewer, after a rejection that leaves draws, or it ends. -/
theorem step_ok {E : SE} {qb R : List Byte} {s : State} {u d : Nat} (hE : E.Ok) (hQ : E.Q qb)
    (h : SEnv E R s) (h5 : s.gpr .s5 = BitVec.ofNat 64 u) (hu : u ≤ E.rl)
    (h11 : s.gpr .s11 = BitVec.ofNat 64 d) (hd : 1 ≤ d) (hd' : d ≤ 128) (h10 : s.gpr .s10 = BitVec.ofNat 64 4) :
    WP isa (.seq draw (.block [.addi .a0 .s10 (-4)])) s fun t =>
      SEnv E R t ∧
        ((isa.eval (.zero .a0) t = some true ∧ t.gpr .s11 = BitVec.ofNat 64 (d - 1) ∧
            t.gpr .s5 = BitVec.ofNat 64 (u + E.W) ∧ t.gpr .s10 = BitVec.ofNat 64 4 ∧ 2 ≤ d ∧
            u + E.W ≤ E.rl ∧
            sample (Spec.Dsa.decodeBE qb) d (R.drop u) =
              rejectOf E.W (sample (Spec.Dsa.decodeBE qb) (d - 1) (R.drop (u + E.W)))) ∨
          (isa.eval (.zero .a0) t = some false ∧
            ((sample (Spec.Dsa.decodeBE qb) d (R.drop u)).trace.head? = some 0 → d = 1))) := by
  refine WP.seq (WP.mono (draw_ok hE hQ h h5 hu h11 hd hd' h10) fun t₁ ⟨h1, _, _, hc⟩ => ?_)
  refine WP.mono (wp_sp (WP.keep [.a0] (Q := fun t₂ => t₂.mem = t₁.mem ∧
    t₂.gpr .a0 = t₁.gpr .s10 - BitVec.ofNat 64 4) (by brun) (by decide) (by rfl)))
    fun t₂ ⟨⟨⟨m2, a3⟩, k2⟩, sp2⟩ => ?_
  have h2 : SEnv E R t₂ := h1.stepM hE k2 sp2 m2
  refine ⟨h2, ?_⟩
  rcases hc with ⟨b10, h2d, b11, b5, hu', hrej⟩ | ⟨b10, -, -, hh⟩
  · refine .inl ⟨?_, (k2.gpr (by decide)).trans b11, (k2.gpr (by decide)).trans b5,
      (k2.gpr (by decide)).trans b10, h2d, hu', hrej⟩
    rw [Steps.eval_zero, a3, b10]; rfl
  · refine .inr ⟨?_, hh⟩
    rw [Steps.eval_zero, a3, b10,
      status_sub4 _ (by have := sampleStatus_le (sample (Spec.Dsa.decodeBE qb) d (R.drop u)); omega)]

/-- The sampling loop's two runs, with `d` draws left. -/
def DI (E : SE) (qb R₁ R₂ : List Byte) (d : Nat) (s₁ s₂ : State) : Prop :=
  ∃ u, 1 ≤ d ∧ d ≤ 128 ∧ SEnv E R₁ s₁ ∧ SEnv E R₂ s₂ ∧ s₁.gpr .s5 = BitVec.ofNat 64 u ∧
    s₂.gpr .s5 = BitVec.ofNat 64 u ∧ u ≤ E.rl ∧ s₁.gpr .s11 = BitVec.ofNat 64 d ∧
    s₂.gpr .s11 = BitVec.ofNat 64 d ∧ s₁.gpr .s10 = BitVec.ofNat 64 4 ∧ s₂.gpr .s10 = BitVec.ofNat 64 4 ∧
    (sample (Spec.Dsa.decodeBE qb) d (R₁.drop u)).trace = (sample (Spec.Dsa.decodeBE qb) d (R₂.drop u)).trace

theorem sampleLoop_st {E : SE} {qb R₁ R₂ : List Byte} (hE : E.Ok) (hQ : E.Q qb) {d : Nat} {s₁ s₂ : State}
    (h : DI E qb R₁ R₂ d s₁ s₂) :
    SameTrace isa (.loop (.seq draw (.block [.addi .a0 .s10 (-4)])) (.zero .a0)) s₁ s₂ := by
  refine st_loop (DI E qb R₁ R₂) (fun n s₁ s₂ ⟨u, hd, hd', h₁, h₂, a5, b5, hu, a11, b11, a10, b10, ht⟩ => ?_) h
  refine ⟨SameTrace.seq (draw_st hE hQ h₁ h₂ a5 b5 hu a11 b11 hd ht)
    (draw_ok hE hQ h₁ a5 hu a11 hd hd' a10) (draw_ok hE hQ h₂ b5 hu b11 hd hd' b10)
    fun t₁ t₂ ⟨e₁, _⟩ ⟨e₂, _⟩ => by exact st_taint [] (e₁.sp.trans e₂.sp.symm) trivial (by taint_decide), _, _,
    step_ok hE hQ h₁ a5 hu a11 hd hd' a10, step_ok hE hQ h₂ b5 hu b11 hd hd' b10,
    fun t₁ t₂ ⟨e₁, c₁⟩ ⟨e₂, c₂⟩ => ?_⟩
  rcases c₁ with ⟨v₁, x11, x5, x10, hn, hu', hr₁⟩ | ⟨v₁, hh₁⟩ <;>
    rcases c₂ with ⟨v₂, y11, y5, y10, hn₂, -, hr₂⟩ | ⟨v₂, hh₂⟩
  · refine ⟨v₁.trans v₂.symm, fun _ => ⟨n - 1, by omega, u + E.W, by omega, by omega, e₁, e₂, x5, y5, hu',
      x11, y11, x10, y10, ?_⟩⟩
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
    (h₁ : SEnv E R₁ s₁) (h₂ : SEnv E R₂ s₂) (a5 : s₁.gpr .s5 = BitVec.ofNat 64 u)
    (b5 : s₂.gpr .s5 = BitVec.ofNat 64 u) (hu : u ≤ E.rl)
    (ht : (sample (Spec.Dsa.decodeBE qb) 128 (R₁.drop u)).trace = (sample (Spec.Dsa.decodeBE qb) 128 (R₂.drop u)).trace) :
    SameTrace isa Impl.Dsa.RISCV64.Random.sample s₁ s₂ := by
  have W : ∀ {s : State}, WP isa (.block [.li .s11 128, .li .s10 4]) s fun t =>
      ((t.mem = s.mem ∧ t.gpr .s11 = BitVec.ofNat 64 128 ∧ t.gpr .s10 = BitVec.ofNat 64 4) ∧
        Keep [.s11, .s10] s t) ∧ t.sp = s.sp := fun {s} =>
    wp_sp (WP.keep [.s11, .s10]
      (by brun [exec_li_lit (show 128 < 2048 by decide), exec_li_lit (show 4 < 2048 by decide)])
      (by decide) (by rfl))
  unfold Impl.Dsa.RISCV64.Random.sample
  refine SameTrace.seq (st_taint [] (h₁.sp.trans h₂.sp.symm) trivial (by taint_decide)) W W
    fun t₁ t₂ ⟨⟨⟨m1, a11, a10⟩, k1⟩, sp1⟩ ⟨⟨⟨m2, b11, b10⟩, k2⟩, sp2⟩ => sampleLoop_st hE hQ ⟨u, by decide,
      by decide, h₁.stepM hE k1 sp1 m1, h₂.stepM hE k2 sp2 m2,
      (k1.gpr (by decide)).trans a5, (k2.gpr (by decide)).trans b5, hu, a11, b11, a10, b10, ht⟩

end VG.Proof.Dsa.RISCV64.Rnd
