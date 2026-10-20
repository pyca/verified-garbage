module

import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.StepU
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Out
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.LaneU
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Core

/-!
# RSA with AVX512_IFMA on x86-64: the multiplication with the look-ahead

`ammCoreU l` ends as `ammCore l` does (`ammCoreU_ok`), for the layouts of
`UOk`: its zeroing (`zerosU_ok`), the lanes' starts (`lanesStartU_ok`) and
its `S` steps (`stepsU_chain`) leave the lanes' limbs of `Amm52N.steps` in
the roles of step `S`, which it stores and carries as `ammCore` does.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Impl.Rsa.X86_64.CrtIfma
open VG.Proof.Bignum (word)
open VG.Proof.Bignum.X86_64.AmmSym (ops Ctx Keeps wrList)

/-! ## The zeroing -/

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-- The zeroing of `ammCoreU`: the roles and the zero register. -/
def zerosU (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : List Instr :=
  (List.range (l.nl * l.R)).map (fun r => .eop (.bin .vpxorq (vreg r) (vreg r) (vreg r))) ++
    [.eop (.bin .vpxorq (uzReg l) (uzReg l) (uzReg l))]

def checkZerosU (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : Bool :=
  match ESym.init.run (fun _ => 0) (zerosU l) with
  | some σ => (List.range 32).all fun r =>
      decide (σ.reg r = if r < l.nl * l.R ∨ r = uzN l then .zero else .reg r)
  | none => false

theorem checkZerosU_2048 : checkZerosU lay2048 = true := by decide +kernel
theorem checkZerosU_p2048 : checkZerosU VG.Impl.Rsa.X86_64.PubIfma.pay2048 = true := by decide +kernel

theorem UOk.checkZeros (hu : UOk l) : checkZerosU l = true := by
  rcases hu with rfl | rfl
  · exact checkZerosU_2048
  · exact checkZerosU_p2048

theorem zerosU_ok (hu : UOk l) {s : State} :
    WP isa (.block (zerosU l)) s fun s' =>
      (∀ r < 32, ∀ t < 4, qv s' (vreg r) t = if r < l.nl * l.R ∨ r = uzN l then 0 else qv s (vreg r) t) ∧
        Keeps s s' := by
  have h := hu.checkZeros
  unfold checkZerosU at h
  split at h
  · rename_i σ hσ
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
    refine WP.mono (run_ok (fun b d n hn hd => absurd hd (by omega)) (SRel.init s) hσ) fun s' hs =>
      ⟨fun r hr t ht => ?_, ⟨fun r hr => hs.gpr hr, hs.mem, hs.rd, hs.wr, hs.mxcsr, hs.flags⟩⟩
    rw [hs.reg _ t ht, vi_vreg r hr, h r hr]
    split <;> rfl
  · cases h

/-! ## The invariant -/

section
variable {s₀ s : State} {a m : Nat → Nat → Nat} {k : Nat → Nat} {bl : Nat → Nat → Nat}

/-- Lane `p`'s registers before its step `n`: its roles hold the limbs after
`n` steps, role 0 with `lo(a₀ b_n)` added, and the registers of `n`'s
parity `b_n` and `u_n`, while `n < S`. -/
structure LaneU (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (s : State) (a m : Nat → Nat → Nat) (k : Nat → Nat)
    (bl : Nat → Nat → Nat) (p n : Nat) : Prop where
  lanes : ∀ kk < l.R, ∀ t < 4, qv s (vreg (regOf l p kk n)) t =
    BitVec.ofNat 64 (lm l a m k bl p n (kk + l.R * t) +
      if kk = 0 ∧ n < l.S then lo (a p (kk + l.R * t)) (bl p n) else 0)
  bv : n < l.S → ∀ t < 4, qv s (vreg (ubN l p (n % 2))) t = BitVec.ofNat 64 (bl p n)
  uv : n < l.S → ∀ t < 4, qv s (vreg (uuN l p (n % 2))) t =
    BitVec.ofNat 64 (stepU (ops a m k p) (lm l a m k bl p n) (bl p n))

/-- What the steps keep: the zero register, the bases, memory and its regions. -/
structure GlobU (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (s₀ s : State) : Prop where
  z : ∀ t < 4, qv s (vreg (uzN l)) t = 0
  r8 : s.gpr .r8 = s₀.gpr .r8
  r9 : s.gpr .r9 = s₀.gpr .r9
  r10 : s.gpr .r10 = s₀.gpr .r10
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem GlobU.keep (g : GlobU l s₀ s) {s' : State} (hk : Keeps s s')
    (hz : ∀ t < 4, qv s' (vreg (uzN l)) t = 0) : GlobU l s₀ s' :=
  ⟨hz, (hk.gpr _ (by decide)).trans g.r8, (hk.gpr _ (by decide)).trans g.r9, (hk.gpr _ (by decide)).trans g.r10,
    hk.mem.trans g.mem, hk.rd.trans g.rd, hk.wr.trans g.wr⟩

theorem GlobU.ctx (e : Env l s₀ a m k bl) (g : GlobU l s₀ s) : Ctx (limU l) s := by
  intro b d n hn hdn
  rw [g.rd, g.wr]
  by_cases b8 : b = .r8
  · subst b8; rw [g.r8]; exact e.rd8 d n hn hdn
  by_cases b9 : b = .r9
  · subst b9; rw [g.r9]; refine e.rd9 d n hn ?_
    simp only [limU, lim, reduceCtorEq, ↓reduceIte, Lay.NB] at hdn ⊢
    omega
  by_cases b10 : b = .r10
  · subst b10; rw [g.r10]; exact e.rd10 d n hn hdn
  · simp only [limU, b8, b9, b10, ite_false] at hdn
    omega

theorem LaneU.stepIn (hu : UOk l) (e : Env l s₀ a m k bl) (g : GlobU l s₀ s) {p n : Nat} (hp : p < l.nl)
    (hn : n < l.S) (h : LaneU l s a m k bl p n) :
    StepInU l s p n (lm l a m k bl p n) (a p) (m p) (k p) (bl p n)
      (if n + 1 < l.S then bl p (n + 1) else 0) := by
  obtain ⟨hl, -, h20, -, -⟩ := hu.regs
  have hS := hl.steps.2.2.2.1
  refine ⟨g.z, fun kk hk t ht => ?_, h.bv hn, h.uv hn, fun j hj => lm_lt h20 (by omega) hj,
    fun kk hk t ht => ?_, fun kk hk t ht => ?_, fun t ht => ?_, fun hn' => ?_, e.alt p hp, e.mlt p hp,
    e.klt p hp, e.blt p hp n (by omega), ?_⟩
  · rw [h.lanes kk hk t ht]; simp only [hn, and_true]
  · rw [g.mem, g.r8]; exact e.ina p hp kk hk t ht
  · rw [g.mem, g.r10]; exact e.inm p hp kk hk t ht
  · rw [g.mem, g.r10]; exact e.ink p hp t ht
  · rw [g.mem, g.r9, ite_eq_left (by omega)]; exact e.inb p hp (n + 1) (by omega)
  · split
    · exact e.blt p hp (n + 1) (by omega)
    · decide

/-- The registers of lane `p`: its roles and its eight of the look-ahead. -/
def Frame (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (s s' : State) (p : Nat) : Prop :=
  ∀ r < 32, (r < l.R * p ∨ l.R * p + l.R ≤ r) → (r < l.nl * l.R + 8 * p ∨ l.nl * l.R + 8 * p + 8 ≤ r) →
    ∀ t < 4, qv s' (vreg r) t = qv s (vreg r) t

/-- The registers of lanes `p` and `q`, two of them, are apart. -/
theorem lanes_apart {p q : Nat} (hp : p < l.nl) (hq : q < l.nl) (hpq : p ≠ q) :
    (l.R * q + l.R ≤ l.R * p ∨ l.R * p + l.R ≤ l.R * q) ∧ l.R * q + l.R ≤ l.nl * l.R ∧
      l.R * p + l.R ≤ l.nl * l.R ∧ 8 * q + 8 ≤ 8 * l.nl ∧ 8 * p + 8 ≤ 8 * l.nl := by
  have hq' := (regsS hq).2.1
  have hp' := (regsS hp).2.1
  refine ⟨?_, hq', hp', by omega, by omega⟩
  rcases Nat.lt_or_gt_of_ne hpq with h | h
  · have := Nat.mul_le_mul_left l.R (show p + 1 ≤ q by omega)
    rw [Nat.mul_add, Nat.mul_one] at this; omega
  · have := Nat.mul_le_mul_left l.R (show q + 1 ≤ p by omega)
    rw [Nat.mul_add, Nat.mul_one] at this; omega

/-- Lane `q`'s registers, kept by lane `p`'s step. -/
theorem LaneU.frame (hu : UOk l) {p q n : Nat} (hp : p < l.nl) (hq : q < l.nl) (hpq : p ≠ q) {s' : State}
    (hf : Frame l s s' p) (h : LaneU l s a m k bl q n) : LaneU l s' a m k bl q n := by
  obtain ⟨-, hR, -, -, hb⟩ := hu.regs
  have hm := Nat.mod_lt n (show 0 < 2 by decide)
  have ha := lanes_apart hp hq hpq
  have eu : ubN l q (n % 2) = l.nl * l.R + 8 * q + n % 2 := rfl
  have ev : uuN l q (n % 2) = l.nl * l.R + 8 * q + 2 + n % 2 := rfl
  refine ⟨fun kk hk t ht => ?_, fun hn t ht => ?_, fun hn t ht => ?_⟩
  · have hr := regOf_bounds (l := l) (by omega) (p := q) (kk := kk) (j := n)
    rw [hf _ (by omega) (by omega) (by omega) t ht]; exact h.lanes kk hk t ht
  · rw [hf _ (by omega) (by omega) (by omega) t ht]; exact h.bv hn t ht
  · rw [hf _ (by omega) (by omega) (by omega) t ht]; exact h.uv hn t ht

/-- Lane `p`'s step `n`. -/
theorem laneStepU_ok (hu : UOk l) (e : Env l s₀ a m k bl) (g : GlobU l s₀ s) {p n : Nat} (hp : p < l.nl)
    (hn : n < l.S) (h : LaneU l s a m k bl p n) :
    WP isa (.block (ammStepU l p n)) s fun s' => GlobU l s₀ s' ∧ LaneU l s' a m k bl p (n + 1) ∧
      Frame l s s' p ∧ Keeps s s' := by
  obtain ⟨-, hR, -, -, hb⟩ := hu.regs
  have := (regsS hp).2.1
  have := (regsS hp).2.2.2.2.2
  refine WP.mono (ammStepU_ok hu hp hn (h.stepIn hu e g hp hn) (g.ctx e)) fun s' ⟨hl, hb', hu', hf, hk⟩ =>
    ⟨g.keep hk fun t ht => by
      rw [hf _ (by simp only [uzN]; omega) (by simp only [uzN]; omega) (by simp only [uzN]; omega) t ht]
      exact g.z t ht, ⟨fun kk hk' t ht => ?_, fun hn' t ht => ?_, fun hn' t ht => ?_⟩, hf, hk⟩
  · rw [hl kk hk' t ht]
    by_cases hn' : n + 1 < l.S
    · simp only [hn', ite_true, show ¬ l.S ≤ n + 1 by omega, not_false_eq_true, and_true]; rfl
    · simp only [hn', ite_false, show l.S ≤ n + 1 by omega, not_true, and_false]; rfl
  · rw [hb' (by omega) t ht, ite_eq_left hn']
  · rw [hu' (by omega) t ht, ite_eq_left hn']; rfl

/-- All lanes before step `n`. -/
def AllU (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (s₀ s : State) (a m : Nat → Nat → Nat) (k : Nat → Nat)
    (bl : Nat → Nat → Nat) (n : Nat) : Prop :=
  GlobU l s₀ s ∧ ∀ p < l.nl, LaneU l s a m k bl p n

/-- Step `n` of the first `q` lanes. -/
theorem lanesStepU_ok (hu : UOk l) (e : Env l s₀ a m k bl) {n : Nat} (hn : n < l.S) :
    ∀ q ≤ l.nl, ∀ s, AllU l s₀ s a m k bl n →
      WP isa (.block ((List.range q).flatMap fun p => ammStepU l p n)) s fun s' =>
        GlobU l s₀ s' ∧ (∀ p < q, LaneU l s' a m k bl p (n + 1)) ∧
        (∀ p, q ≤ p → p < l.nl → LaneU l s' a m k bl p n) ∧
        (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.mxcsr = s.mxcsr := by
  intro q
  induction q with
  | zero => intro _ s h; exact WP.block_nil ⟨h.1, fun _ h => absurd h (by omega), fun p _ hp => h.2 p hp,
      fun _ _ => rfl, rfl⟩
  | succ q ih =>
    intro hq s h
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (ih (by omega) s h) fun s₁ ⟨g₁, d₁, t₁, r₁, x₁⟩ => ?_
    refine WP.mono (laneStepU_ok hu e g₁ (p := q) (by omega) hn (t₁ q (Nat.le_refl _) (by omega)))
      fun s₂ ⟨g₂, l₂, f₂, k₂⟩ => ⟨g₂, fun p hp => ?_, fun p hp hp' => ?_,
        fun r hr => (k₂.gpr r hr).trans (r₁ r hr), k₂.mxcsr.trans x₁⟩
    · by_cases hpq : p = q
      · subst hpq; exact l₂
      · exact (d₁ p (by omega)).frame hu (p := q) (by omega) (by omega) (Ne.symm hpq) f₂
    · exact (t₁ p (by omega) hp').frame hu (p := q) (by omega) hp' (by omega) f₂

/-- Step `n` of all lanes. -/
theorem pairStepU_ok (hu : UOk l) (e : Env l s₀ a m k bl) {n : Nat} (hn : n < l.S) (h : AllU l s₀ s a m k bl n) :
    WP isa (.block ((List.range l.nl).flatMap fun p => ammStepU l p n)) s fun s' =>
      AllU l s₀ s' a m k bl (n + 1) ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.mxcsr = s.mxcsr :=
  WP.mono (lanesStepU_ok hu e hn l.nl (Nat.le_refl _) s h) fun _ ⟨g, d, _, r, x⟩ => ⟨⟨g, d⟩, r, x⟩

/-- The first `n` steps of all lanes. -/
theorem stepsU_chain (hu : UOk l) (e : Env l s₀ a m k bl) :
    ∀ n ≤ l.S, ∀ s, AllU l s₀ s a m k bl 0 →
      WP isa (.block ((List.range n).flatMap fun i => (List.range l.nl).flatMap fun p => ammStepU l p i)) s
        fun s' => AllU l s₀ s' a m k bl n ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.mxcsr = s.mxcsr := by
  intro n
  induction n with
  | zero => intro _ s h; exact WP.block_nil ⟨h, fun _ _ => rfl, rfl⟩
  | succ n ih =>
    intro hn s h
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (ih (by omega) s h) fun s₁ ⟨h₁, g₁, x₁⟩ => ?_
    exact WP.mono (pairStepU_ok hu e (by omega) h₁) fun s₂ ⟨h₂, g₂, x₂⟩ =>
      ⟨h₂, fun r hr => (g₂ r hr).trans (g₁ r hr), x₂.trans x₁⟩

/-- Lane `p`'s start. -/
theorem laneStartU_ok (hu : UOk l) (e : Env l s₀ a m k bl) (g : GlobU l s₀ s) {p : Nat} (hp : p < l.nl)
    (h0 : ∀ t < 4, qv s (vreg (regOf l p 0 0)) t = 0) :
    WP isa (.block (ammStartU l p)) s fun s' => GlobU l s₀ s' ∧
      (∀ t < 4, qv s' (vreg (regOf l p 0 0)) t = BitVec.ofNat 64 (0 + lo (a p (0 + l.R * t)) (bl p 0))) ∧
      (∀ t < 4, qv s' (vreg (ubN l p 0)) t = BitVec.ofNat 64 (bl p 0)) ∧
      (∀ t < 4, qv s' (vreg (uuN l p 0)) t = BitVec.ofNat 64 (stepU (ops a m k p) (fun _ => 0) (bl p 0))) ∧
      (∀ r < 32, r ≠ l.R * p → (r < l.nl * l.R + 8 * p ∨ l.nl * l.R + 8 * p + 8 ≤ r) →
        ∀ t < 4, qv s' (vreg r) t = qv s (vreg r) t) ∧
      Keeps s s' := by
  obtain ⟨hl, hR, -, -, hbud⟩ := hu.regs
  have := regsS hp
  have hb := e.inb p hp 0 (by simp only [Lay.L]; omega)
  rw [show l.D * p + l.off 0 = l.D * p by simp only [Lay.off, Nat.zero_mod, Nat.zero_div,
    Nat.mul_zero, Nat.add_zero]] at hb
  refine WP.mono (ammStartU_ok (m := m p) hu hp (g.ctx e) h0
    (fun t ht => by rw [g.mem, g.r8]; exact e.ina p hp 0 (by omega) t ht)
    (by rw [g.mem, g.r10]; exact e.ink p hp 0 (by decide)) (by rw [g.mem, g.r9]; exact hb))
    fun s' ⟨h₀, hb', hu', hf, hk⟩ => ⟨g.keep hk fun t ht => by
      rw [hf _ (by simp only [uzN]; omega) (by simp only [uzN]; omega) (by simp only [uzN]; omega)
        (by simp only [uzN]; omega) (by simp only [uzN]; omega) t ht]; exact g.z t ht, h₀, hb', hu',
      fun r hr h1 h2 t ht => hf r hr (by omega) (by omega) (by omega) (by omega) t ht, hk⟩

/-- The first `q` lanes' starts, from roles zero. -/
theorem lanesStartU_ok (hu : UOk l) (e : Env l s₀ a m k bl) :
    ∀ q ≤ l.nl, ∀ s, GlobU l s₀ s → (∀ r < l.nl * l.R, ∀ t < 4, qv s (vreg r) t = 0) →
      WP isa (.block ((List.range q).flatMap (ammStartU l))) s fun s' =>
        GlobU l s₀ s' ∧ (∀ p < q, LaneU l s' a m k bl p 0) ∧
        (∀ r, l.R * q ≤ r → r < l.nl * l.R → ∀ t < 4, qv s' (vreg r) t = 0) ∧
        (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨-, hR, -, -, hbud⟩ := hu.regs
  intro q
  induction q with
  | zero => intro _ s g hz; exact WP.block_nil ⟨g, fun _ h => absurd h (by omega), fun r _ hr => hz r hr,
      fun _ _ => rfl, rfl⟩
  | succ q ih =>
    intro hq s g hz
    have hqs := regsS (show q < l.nl by omega)
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (ih (by omega) s g hz) fun s₁ ⟨g₁, d₁, z₁, r₁, x₁⟩ => ?_
    refine WP.mono (laneStartU_ok hu e g₁ (p := q) (by omega) fun t ht => by
        rw [hqs.1]; exact z₁ _ (Nat.le_refl _) (by omega) t ht)
      fun s₂ ⟨g₂, a₂, b₂, u₂, f₂, k₂⟩ => ⟨g₂, fun p hp => ?_, fun r hr hr' t ht => ?_,
        fun r hr => (k₂.gpr r hr).trans (r₁ r hr), k₂.mxcsr.trans x₁⟩
    · by_cases hpq : p = q
      · subst hpq
        refine ⟨fun kk hk t ht => ?_, fun _ t ht => b₂ t ht, fun _ t ht => u₂ t ht⟩
        by_cases k0 : kk = 0
        · subst k0; rw [ite_eq_left ⟨rfl, by have := hu.regs.1.steps.2.2.1; omega⟩]; exact a₂ t ht
        · have hr := regOf_bounds (l := l) (by omega) (p := p) (kk := kk) (j := 0)
          have e0 : regOf l p kk 0 = l.R * p + kk := by
            simp only [regOf, Nat.add_zero, Nat.mod_eq_of_lt hk]
          rw [ite_eq_right (by omega), f₂ _ (by omega) (by omega) (by omega) t ht,
            z₁ _ (by omega) (by omega) t ht]; rfl
      · have ha := lanes_apart (show p < l.nl by omega) (show q < l.nl by omega) hpq
        have h1 := d₁ p (by omega)
        refine ⟨fun kk hk t ht => ?_, fun hn t ht => ?_, fun hn t ht => ?_⟩
        · have hr := regOf_bounds (l := l) (by omega) (p := p) (kk := kk) (j := 0)
          rw [f₂ _ (by omega) (by omega) (by omega) t ht]; exact h1.lanes kk hk t ht
        · have eu : ubN l p (0 % 2) = l.nl * l.R + 8 * p := rfl
          rw [f₂ _ (by omega) (by omega) (by omega) t ht]; exact h1.bv hn t ht
        · have ev : uuN l p (0 % 2) = l.nl * l.R + 8 * p + 2 := rfl
          rw [f₂ _ (by omega) (by omega) (by omega) t ht]; exact h1.uv hn t ht
    · rw [Nat.mul_add, Nat.mul_one] at hr
      rw [f₂ _ (by omega) (by omega) (by omega) t ht]; exact z₁ r (by omega) hr' t ht

end

/-! ## The whole multiplication -/

theorem ammCoreU_code : ammCoreU l = .block (Instr.mov .r10 (.reg .rbx) :: (zerosU l ++
    ((List.range l.nl).flatMap (ammStartU l) ++
    ((List.range l.S).flatMap (fun i => (List.range l.nl).flatMap fun p => ammStepU l p i) ++
    (storeCode .r11 (accStores l) ++ (Instr.movImm64 .r12 mask52 :: carryOut l)))))) := by
  simp only [ammCoreU, zerosU, ← accStores_code, List.append_assoc, List.cons_append, List.nil_append]

/-- `ammCoreU l` ends as `ammCore l` does (`ammCore_ok`). -/
theorem ammCoreU_ok (hu : UOk l) {s : State} {B : Addr} {a m : Nat → Nat → Nat} {k : Nat → Nat}
    {bl : Nat → Nat → Nat} (e : Env l (s.setReg .r10 (s.gpr .rbx)) a m k bl) (hB : s.gpr .r11 = B)
    (hs : Scr s B (l.D * (l.nl - 1) + l.NB)) :
    WP isa (ammCoreU l) s fun s' =>
      (∀ p < l.nl, ∀ q < l.L, word s'.mem B (l.D * p + l.off q) =
        BitVec.ofNat 64 (carried (lm l a m k bl p l.S) q)) ∧
      (∀ p < l.nl, s'.gpr (cReg p) = BitVec.ofNat 64 (carryIn (lm l a m k bl p l.S) l.L)) ∧
      OutN l B 0 l.NB s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r9 → r ≠ .r10 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.gpr .r12 = mask52 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨hl, hR, h20, hn1, hbud⟩ := hu.regs
  have hst := hl.steps
  have hD := hl.D_bounds
  have hDn : l.D * (l.nl - 1) ≤ l.D := D_le hl (show l.nl - 1 < l.nl by omega)
  rw [ammCoreU_code, WP.block_cons_iff]
  refine ⟨s.setReg .r10 (s.gpr .rbx), rfl, ?_⟩
  rw [WP.block_append_iff]
  refine WP.mono (zerosU_ok hu) fun s₁ ⟨hz, k₁⟩ => ?_
  have g₁ : GlobU l (s.setReg .r10 (s.gpr .rbx)) s₁ :=
    ⟨fun t ht => by rw [hz (uzN l) (by simp only [uzN]; omega) t ht, ite_eq_left (Or.inr rfl)],
      k₁.gpr _ (by decide), k₁.gpr _ (by decide), k₁.gpr _ (by decide), k₁.mem, k₁.rd, k₁.wr⟩
  rw [WP.block_append_iff]
  refine WP.mono (lanesStartU_ok hu e l.nl (Nat.le_refl _) s₁ g₁ fun r hr t ht => by
      rw [hz r (by omega) t ht, ite_eq_left (Or.inl hr)])
    fun s₂ ⟨g₂', d₂, _, g₂, x₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (stepsU_chain hu e l.S (Nat.le_refl _) s₂ ⟨g₂', d₂⟩) fun s₃ ⟨h₃, g₃, x₃⟩ => ?_
  have hB₃ : s₃.gpr .r11 = B := by
    rw [g₃ _ (by decide), g₂ _ (by decide), k₁.gpr _ (by decide)]
    exact (RegUpd.gpr_setReg_of_ne _ _ (by decide)).trans hB
  have wr₃ : s₃.wr = s.wr := by rw [h₃.1.wr]; rfl
  have m₃ : s₃.mem = s.mem := h₃.1.mem
  rw [WP.block_append_iff]
  refine WP.mono (stores_gen (accStores l) s₃ hB₃ fun x hx =>
    wr₃ ▸ (let ⟨_, h, c⟩ := hs.region (accStores_lt x hx) (by decide); ⟨_, h, c⟩)) fun s₄ h₄ => ?_
  subst h₄
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, ?_⟩
  refine WP.mono (carryOut_ok hl (B := B) (L := fun p => lm l a m k bl p l.S)
    (fun p _ q hq => lm_lt h20 hst.2.2.2.1 hq)
    (fun d hd => by rw [RegUpd.wr_setReg, wr₃]; exact hs.st hd)
    (by rw [RegUpd.gpr_setReg_of_ne _ _ (by decide)]; exact hB₃)
    (RegUpd.gpr_setReg_self _ _ _) fun p hp q hq => ?_) fun s' ⟨h, g, rd, wr, x⟩ => ?_
  · have h1 := Nat.mod_lt q (show 0 < l.R by omega)
    have h2 : q / l.R < 4 := Nat.div_lt_of_lt_mul (by simp only [Lay.L] at hq; rw [Nat.mul_comm]; exact hq)
    have := read_stores hl s₃.mem B s₃ hp (k := q % l.R) (t := q / l.R) h1 h2
    have er : regOf l p (q % l.R) (l.S % l.R) = regOf l p (q % l.R) l.S := by
      simp only [regOf, Nat.add_mod_mod]
    rw [er, (h₃.2 p hp).lanes _ h1 _ h2, ite_eq_right (by omega), Nat.add_zero, Nat.mod_add_div] at this
    rw [RegUpd.mem_setReg, show l.D * p + l.off q =
      l.D * p + 32 * (q % l.R) + 8 * (q / l.R) by unfold Lay.off; omega]
    exact this
  refine ⟨fun p hp q hq => by rw [h.words p hp q hq]; simp only [hq, true_or, ite_true],
    fun p hp => by rw [h.c p hp]; simp only [Nat.not_lt_zero, ↓reduceIte], ?_,
    fun r r1 r2 r3 r4 r5 r6 r7 => ?_,
    by rw [g _ (by decide) (by decide) (by decide) (by decide)]; exact RegUpd.gpr_setReg_self _ _ _,
    by rw [rd, RegUpd.rd_setReg, h₃.1.rd]; rfl, by rw [wr, RegUpd.wr_setReg, wr₃],
    by rw [x, RegUpd.mxcsr_setReg, x₃, x₂, k₁.mxcsr]; rfl⟩
  · have o := wrList_outN (l := l) B (o := 0) (n := l.NB) (by omega)
      ((accStores l).map fun x => (x.1, s₃.vy x.2)) s₃.mem fun x hx => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        exact accStores_win y hy
    have hf : OutN l B 0 l.NB
        (wrList s₃.mem B ((accStores l).map fun x => (x.1, s₃.vy x.2))) s'.mem := h.frame
    have o' : OutN l B 0 l.NB s.mem
        (wrList s₃.mem B ((accStores l).map fun x => (x.1, s₃.vy x.2))) :=
      fun x hx => (o x hx).trans (congrFun m₃ x)
    exact o'.trans hf
  · rw [g r r1 r2 r3 r4, RegUpd.gpr_setReg_of_ne _ _ r7, g₃ r r1, g₂ r r1, k₁.gpr r r1,
      RegUpd.gpr_setReg_of_ne _ _ r6]

theorem ammCoreU_core (hu : UOk l) : CoreOk l (ammCoreU l) := fun e hB hs => ammCoreU_ok hu e hB hs

/-- The multiplication of each layout. -/
theorem ammMul_core (hl : AmmOk l) : CoreOk l (ammMul l) := by
  unfold ammMul
  split
  · rename_i h; exact ammCoreU_core (UOk.of_amm hl h)
  · exact ammCore_core hl

end VG.Proof.Bignum.X86_64.Ifma
