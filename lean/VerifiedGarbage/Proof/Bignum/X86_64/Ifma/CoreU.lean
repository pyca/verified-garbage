module

public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.StepU
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Out
import VerifiedGarbage.Proof.Framework.Omega

/-!
# RSA with AVX512_IFMA on x86-64: the multiplication with the look-ahead, 2048 bits

`ammCoreU lay2048` ends as `ammCore lay2048` does (`ammCoreU_ok`): its
zeroing (`zerosU_ok`), the lanes' starts (`startsU_ok`) and its 20 steps
(`stepsU_chain`) leave the lanes' limbs of `Amm52N.steps` in the roles of
step 20, which it stores and carries as `ammCore` does.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Impl.Rsa.X86_64.CrtIfma
open VG.Proof.Bignum (word)
open VG.Proof.Bignum.X86_64.AmmSym (ops Ctx Keeps wrList)

/-! ## The zeroing -/

/-- The zeroing of `ammCoreU`: the roles and the zero register. -/
def zerosU : List Instr :=
  (List.range (lay2048.nl * lay2048.R)).map (fun r => .eop (.bin .vpxorq (vreg r) (vreg r) (vreg r))) ++
    [.eop (.bin .vpxorq (uzReg lay2048) (uzReg lay2048) (uzReg lay2048))]

def checkZerosU : Bool :=
  match ESym.init.run (fun _ => 0) zerosU with
  | some σ => (List.range 32).all fun r => decide (σ.reg r = if r < 10 ∨ r = 26 then .zero else .reg r)
  | none => false

theorem checkZerosU_ok : checkZerosU = true := by decide +kernel

theorem zerosU_ok {s : State} :
    WP isa (.block zerosU) s fun s' =>
      (∀ r < 32, ∀ t < 4, qv s' (vreg r) t = if r < 10 ∨ r = 26 then 0 else qv s (vreg r) t) ∧ Keeps s s' := by
  have h := checkZerosU_ok
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
structure LaneU (s : State) (a m : Nat → Nat → Nat) (k : Nat → Nat) (bl : Nat → Nat → Nat) (p n : Nat) : Prop where
  lanes : ∀ kk < lay2048.R, ∀ t < 4, qv s (vreg (regOf lay2048 p kk n)) t =
    BitVec.ofNat 64 (lm lay2048 a m k bl p n (kk + lay2048.R * t) +
      if kk = 0 ∧ n < lay2048.S then lo (a p (kk + lay2048.R * t)) (bl p n) else 0)
  bv : n < lay2048.S → ∀ t < 4, qv s (vreg (ubN lay2048 p (n % 2))) t = BitVec.ofNat 64 (bl p n)
  uv : n < lay2048.S → ∀ t < 4, qv s (vreg (uuN lay2048 p (n % 2))) t =
    BitVec.ofNat 64 (stepU (ops a m k p) (lm lay2048 a m k bl p n) (bl p n))

/-- What the steps keep: the zero register, the bases, memory and its regions. -/
structure GlobU (s₀ s : State) : Prop where
  z : ∀ t < 4, qv s (vreg (uzN lay2048)) t = 0
  r8 : s.gpr .r8 = s₀.gpr .r8
  r9 : s.gpr .r9 = s₀.gpr .r9
  r10 : s.gpr .r10 = s₀.gpr .r10
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem GlobU.keep (g : GlobU s₀ s) {s' : State} (hk : Keeps s s') (hz : ∀ t < 4, qv s' (vreg (uzN lay2048)) t = 0) :
    GlobU s₀ s' :=
  ⟨hz, (hk.gpr _ (by decide)).trans g.r8, (hk.gpr _ (by decide)).trans g.r9, (hk.gpr _ (by decide)).trans g.r10,
    hk.mem.trans g.mem, hk.rd.trans g.rd, hk.wr.trans g.wr⟩

theorem GlobU.ctx (e : Env lay2048 s₀ a m k bl) (g : GlobU s₀ s) : Ctx (limU lay2048) s := by
  intro b d n hn hdn
  rw [g.rd, g.wr]
  by_cases b8 : b = .r8
  · subst b8; rw [g.r8]; exact e.rd8 d n hn hdn
  by_cases b9 : b = .r9
  · subst b9; rw [g.r9]; exact e.rd9 d n hn hdn
  by_cases b10 : b = .r10
  · subst b10; rw [g.r10]; exact e.rd10 d n hn hdn
  · simp only [limU, b8, b9, b10, ite_false] at hdn
    omega

theorem LaneU.stepIn (e : Env lay2048 s₀ a m k bl) (g : GlobU s₀ s) {p n : Nat} (hp : p < 2)
    (hn : n < lay2048.S) (h : LaneU s a m k bl p n) :
    StepInU lay2048 s p n (lm lay2048 a m k bl p n) (a p) (m p) (k p) (bl p n)
      (if n + 1 < lay2048.S then bl p (n + 1) else 0) := by
  have hS := S2048
  have hL : lay2048.L = 20 := rfl
  have hp' : p < lay2048.nl := hp
  refine ⟨g.z, fun kk hk t ht => ?_, h.bv hn, h.uv hn, fun j hj => lm_lt (by decide) (by omega) hj,
    fun kk hk t ht => ?_, fun kk hk t ht => ?_, fun t ht => ?_, fun hn' => ?_, e.alt p hp', e.mlt p hp',
    e.klt p hp', e.blt p hp' n (by omega), ?_⟩
  · rw [h.lanes kk hk t ht]; simp only [hn, and_true]
  · rw [g.mem, g.r8]; exact e.ina p hp' kk hk t ht
  · rw [g.mem, g.r10]; exact e.inm p hp' kk hk t ht
  · rw [g.mem, g.r10]; exact e.ink p hp' t ht
  · rw [g.mem, g.r9, ite_eq_left (by omega)]; exact e.inb p hp' (n + 1) (by omega)
  · split
    · exact e.blt p hp' (n + 1) (by omega)
    · decide

/-- Lane `q`'s registers, kept by lane `p`'s step. -/
theorem LaneU.frame {p q n : Nat} (hp : p < 2) (hq : q < 2) (hpq : p ≠ q) {s' : State}
    (hf : ∀ r < 32, (r < 5 * p ∨ 5 * p + 5 ≤ r) → (r < 10 + 8 * p ∨ 18 + 8 * p ≤ r) →
      ∀ t < 4, qv s' (vreg r) t = qv s (vreg r) t) (h : LaneU s a m k bl q n) : LaneU s' a m k bl q n := by
  have hm := Nat.mod_lt n (show 0 < 2 by decide)
  have eu : ubN lay2048 q (n % 2) = 10 + 8 * q + n % 2 := rfl
  have ev : uuN lay2048 q (n % 2) = 10 + 8 * q + 2 + n % 2 := rfl
  refine ⟨fun kk hk t ht => ?_, fun hn t ht => ?_, fun hn t ht => ?_⟩
  · have hr := regOf2048 (p := q) (kk := kk) (j := n)
    rw [hf _ (by omega) (by omega) (by omega) t ht]; exact h.lanes kk hk t ht
  · rw [hf _ (by omega) (by omega) (by omega) t ht]; exact h.bv hn t ht
  · rw [hf _ (by omega) (by omega) (by omega) t ht]; exact h.uv hn t ht

/-- Lane `p`'s step `n`. -/
theorem laneStepU_ok (e : Env lay2048 s₀ a m k bl) (g : GlobU s₀ s) {p n : Nat} (hp : p < 2)
    (hn : n < lay2048.S) (h : LaneU s a m k bl p n) :
    WP isa (.block (ammStepU lay2048 p n)) s fun s' => GlobU s₀ s' ∧ LaneU s' a m k bl p (n + 1) ∧
      (∀ r < 32, (r < 5 * p ∨ 5 * p + 5 ≤ r) → (r < 10 + 8 * p ∨ 18 + 8 * p ≤ r) →
        ∀ t < 4, qv s' (vreg r) t = qv s (vreg r) t) ∧ Keeps s s' := by
  have hS := S2048
  have hz : uzN lay2048 = 26 := rfl
  refine WP.mono (ammStepU_ok hp (by omega) (h.stepIn e g hp hn) (g.ctx e)) fun s' ⟨hl, hb, hu, hf, hk⟩ =>
    ⟨g.keep hk fun t ht => by
      rw [hf _ (by decide) (by omega) (by omega) t ht]; exact g.z t ht, ⟨fun kk hk' t ht => ?_, fun hn' t ht => ?_,
      fun hn' t ht => ?_⟩, hf, hk⟩
  · rw [hl kk hk' t ht]
    by_cases hn' : n + 1 < lay2048.S
    · simp only [hn', ite_true, show ¬ lay2048.S ≤ n + 1 by omega, not_false_eq_true, and_true]; rfl
    · simp only [hn', ite_false, show lay2048.S ≤ n + 1 by omega, not_true, and_false]; rfl
  · rw [hb (by omega) t ht, ite_eq_left hn']
  · rw [hu (by omega) t ht, ite_eq_left hn']; rfl

/-- All lanes before step `n`. -/
def AllU (s₀ s : State) (a m : Nat → Nat → Nat) (k : Nat → Nat) (bl : Nat → Nat → Nat) (n : Nat) : Prop :=
  GlobU s₀ s ∧ ∀ p < 2, LaneU s a m k bl p n

/-- Step `n` of both lanes. -/
theorem pairStepU_ok (e : Env lay2048 s₀ a m k bl) {n : Nat} (hn : n < lay2048.S) (h : AllU s₀ s a m k bl n) :
    WP isa (.block ((List.range lay2048.nl).flatMap fun p => ammStepU lay2048 p n)) s fun s' =>
      AllU s₀ s' a m k bl (n + 1) ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.mxcsr = s.mxcsr := by
  rw [show List.range lay2048.nl = [0, 1] from rfl, List.flatMap_cons, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, WP.block_append_iff]
  refine WP.mono (laneStepU_ok e h.1 (p := 0) (by decide) hn (h.2 0 (by decide))) fun s₁ ⟨g₁, l₁, f₁, k₁⟩ => ?_
  have l₁' := (h.2 1 (by decide)).frame (p := 0) (by decide) (by decide) (by decide) f₁
  refine WP.mono (laneStepU_ok e g₁ (p := 1) (by decide) hn l₁') fun s₂ ⟨g₂, l₂, f₂, k₂⟩ => ?_
  refine ⟨⟨g₂, fun p hp => ?_⟩, fun r hr => (k₂.gpr r hr).trans (k₁.gpr r hr), k₂.mxcsr.trans k₁.mxcsr⟩
  rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl
  · exact l₁.frame (p := 1) (by decide) (by decide) (by decide) f₂
  · exact l₂

/-- The first `n` steps of both lanes. -/
theorem stepsU_chain (e : Env lay2048 s₀ a m k bl) :
    ∀ n ≤ lay2048.S, ∀ s, AllU s₀ s a m k bl 0 →
      WP isa (.block ((List.range n).flatMap fun i => (List.range lay2048.nl).flatMap fun p => ammStepU lay2048 p i)) s
        fun s' => AllU s₀ s' a m k bl n ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.mxcsr = s.mxcsr := by
  intro n
  induction n with
  | zero => intro _ s h; exact WP.block_nil ⟨h, fun _ _ => rfl, rfl⟩
  | succ n ih =>
    intro hn s h
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (ih (by omega) s h) fun s₁ ⟨h₁, g₁, x₁⟩ => ?_
    exact WP.mono (pairStepU_ok e (by omega) h₁) fun s₂ ⟨h₂, g₂, x₂⟩ =>
      ⟨h₂, fun r hr => (g₂ r hr).trans (g₁ r hr), x₂.trans x₁⟩

theorem regOf_eq2048 {p kk j : Nat} : regOf lay2048 p kk j = 5 * p + (kk + j) % 5 := by
  simp only [regOf, R2048]

/-- Lane `p`'s start. -/
theorem laneStartU_ok (e : Env lay2048 s₀ a m k bl) (g : GlobU s₀ s) {p : Nat} (hp : p < 2)
    (h0 : ∀ t < 4, qv s (vreg (regOf lay2048 p 0 0)) t = 0) :
    WP isa (.block (ammStartU lay2048 p)) s fun s' => GlobU s₀ s' ∧
      (∀ t < 4, qv s' (vreg (regOf lay2048 p 0 0)) t = BitVec.ofNat 64 (0 + lo (a p (0 + lay2048.R * t)) (bl p 0))) ∧
      (∀ t < 4, qv s' (vreg (ubN lay2048 p 0)) t = BitVec.ofNat 64 (bl p 0)) ∧
      (∀ t < 4, qv s' (vreg (uuN lay2048 p 0)) t = BitVec.ofNat 64 (stepU (ops a m k p) (fun _ => 0) (bl p 0))) ∧
      (∀ r < 32, r ≠ 5 * p → (r < 10 + 8 * p ∨ 18 + 8 * p ≤ r) → ∀ t < 4, qv s' (vreg r) t = qv s (vreg r) t) ∧
      Keeps s s' := by
  have hp' : p < lay2048.nl := hp
  have := regsS2048 p
  have hz : uzN lay2048 = 26 := rfl
  have hb := e.inb p hp' 0 (by decide)
  rw [show lay2048.D * p + lay2048.off 0 = lay2048.D * p by simp only [Lay.off, Nat.zero_mod, Nat.zero_div,
    Nat.mul_zero, Nat.add_zero]] at hb
  refine WP.mono (ammStartU_ok (m := m p) hp (g.ctx e) h0 (fun t ht => by rw [g.mem, g.r8]; exact e.ina p hp' 0 (by decide) t ht)
    (by rw [g.mem, g.r10]; exact e.ink p hp' 0 (by decide)) (by rw [g.mem, g.r9]; exact hb))
    fun s' ⟨h₀, hb', hu, hf, hk⟩ => ⟨g.keep hk fun t ht => by
      rw [hf _ (by omega) (by omega) (by omega) (by omega) (by omega) t ht]; exact g.z t ht, h₀, hb', hu,
      fun r hr h1 h2 t ht => hf r hr (by omega) (by omega) (by omega) (by omega) t ht, hk⟩

/-- The lanes' starts, from roles zero. -/
theorem startsU_ok (e : Env lay2048 s₀ a m k bl) (g : GlobU s₀ s) (hz : ∀ r < 10, ∀ t < 4, qv s (vreg r) t = 0) :
    WP isa (.block ((List.range lay2048.nl).flatMap (ammStartU lay2048))) s fun s' =>
      AllU s₀ s' a m k bl 0 ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.mxcsr = s.mxcsr := by
  have r0 := regsS2048 0
  have r1 := regsS2048 1
  rw [show List.range lay2048.nl = [0, 1] from rfl, List.flatMap_cons, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, WP.block_append_iff]
  refine WP.mono (laneStartU_ok e g (p := 0) (by decide) fun t ht => hz _ (by omega) t ht)
    fun s₁ ⟨g₁, a₁, b₁, u₁, f₁, k₁⟩ => ?_
  refine WP.mono (laneStartU_ok e g₁ (p := 1) (by decide) fun t ht => by
      rw [f₁ _ (by omega) (by omega) (by omega) t ht]; exact hz _ (by omega) t ht)
    fun s₂ ⟨g₂, a₂, b₂, u₂, f₂, k₂⟩ => ?_
  have lane0 : ∀ p < 2, (∀ t < 4, qv s₂ (vreg (regOf lay2048 p 0 0)) t =
        BitVec.ofNat 64 (0 + lo (a p (0 + lay2048.R * t)) (bl p 0))) →
      (∀ t < 4, qv s₂ (vreg (ubN lay2048 p 0)) t = BitVec.ofNat 64 (bl p 0)) →
      (∀ t < 4, qv s₂ (vreg (uuN lay2048 p 0)) t = BitVec.ofNat 64 (stepU (ops a m k p) (fun _ => 0) (bl p 0))) →
      (∀ kk < 5, kk ≠ 0 → ∀ t < 4, qv s₂ (vreg (regOf lay2048 p kk 0)) t = 0) → LaneU s₂ a m k bl p 0 :=
    fun p _ ha hb hu hr => ⟨fun kk hk t ht => by
      by_cases k0 : kk = 0
      · subst k0; rw [ite_eq_left ⟨rfl, by decide⟩]; exact ha t ht
      · rw [ite_eq_right (by omega), hr kk (by rw [R2048] at hk; exact hk) k0 t ht]; rfl,
      fun _ t ht => hb t ht, fun _ t ht => hu t ht⟩
  refine ⟨⟨g₂, fun p hp => ?_⟩, fun r hr => (k₂.gpr r hr).trans (k₁.gpr r hr), k₂.mxcsr.trans k₁.mxcsr⟩
  rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl
  · refine lane0 0 (by decide) (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_) fun kk hk k0 t ht => ?_
    · rw [f₂ _ (by omega) (by omega) (by omega) t ht]; exact a₁ t ht
    · rw [f₂ _ (by omega) (by omega) (by omega) t ht]; exact b₁ t ht
    · rw [f₂ _ (by omega) (by omega) (by omega) t ht]; exact u₁ t ht
    · have e0 := regOf_eq2048 (p := 0) (kk := kk) (j := 0)
      rw [f₂ _ (by omega) (by omega) (by omega) t ht, f₁ _ (by omega) (by omega) (by omega) t ht]
      exact hz _ (by omega) t ht
  · refine lane0 1 (by decide) a₂ b₂ u₂ fun kk hk k0 t ht => ?_
    have e0 := regOf_eq2048 (p := 1) (kk := kk) (j := 0)
    rw [f₂ _ (by omega) (by omega) (by omega) t ht, f₁ _ (by omega) (by omega) (by omega) t ht]
    exact hz _ (by omega) t ht

end

/-! ## The whole multiplication -/

theorem ammCoreU_code : ammCoreU lay2048 = .block (Instr.mov .r10 (.reg .rbx) :: (zerosU ++
    ((List.range lay2048.nl).flatMap (ammStartU lay2048) ++
    ((List.range lay2048.S).flatMap (fun i => (List.range lay2048.nl).flatMap fun p => ammStepU lay2048 p i) ++
    (storeCode .r11 (accStores lay2048) ++ (Instr.movImm64 .r12 mask52 :: carryOut lay2048)))))) := by
  simp only [ammCoreU, zerosU, ← accStores_code, List.append_assoc, List.cons_append, List.nil_append]

/-- `ammCoreU lay2048` ends as `ammCore lay2048` does (`ammCore_ok`). -/
theorem ammCoreU_ok {s : State} {B : Addr} {a m : Nat → Nat → Nat} {k : Nat → Nat}
    {bl : Nat → Nat → Nat} (e : Env lay2048 (s.setReg .r10 (s.gpr .rbx)) a m k bl) (hB : s.gpr .r11 = B)
    (hs : Scr s B (lay2048.D * (lay2048.nl - 1) + lay2048.NB)) :
    WP isa (ammCoreU lay2048) s fun s' =>
      (∀ p < lay2048.nl, ∀ q < lay2048.L, word s'.mem B (lay2048.D * p + lay2048.off q) =
        BitVec.ofNat 64 (carried (lm lay2048 a m k bl p lay2048.S) q)) ∧
      (∀ p < lay2048.nl, s'.gpr (cReg p) = BitVec.ofNat 64 (carryIn (lm lay2048 a m k bl p lay2048.S) lay2048.L)) ∧
      OutN lay2048 B 0 lay2048.NB s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r9 → r ≠ .r10 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.gpr .r12 = mask52 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  have hl : AmmOk lay2048 := .inl (.inl rfl)
  have hst := hl.steps
  have hS := S2048
  have hD := hl.D_bounds
  have hDn : lay2048.D * (lay2048.nl - 1) ≤ lay2048.D := D_le hl (show lay2048.nl - 1 < lay2048.nl by decide)
  rw [ammCoreU_code, WP.block_cons_iff]
  refine ⟨s.setReg .r10 (s.gpr .rbx), rfl, ?_⟩
  rw [WP.block_append_iff]
  refine WP.mono zerosU_ok fun s₁ ⟨hz, k₁⟩ => ?_
  have g₁ : GlobU (s.setReg .r10 (s.gpr .rbx)) s₁ :=
    ⟨fun t ht => by rw [hz (uzN lay2048) (by decide) t ht, ite_eq_left (by decide)],
      k₁.gpr _ (by decide), k₁.gpr _ (by decide), k₁.gpr _ (by decide), k₁.mem, k₁.rd, k₁.wr⟩
  rw [WP.block_append_iff]
  refine WP.mono (startsU_ok e g₁ fun r hr t ht => by rw [hz r (by omega) t ht, ite_eq_left (Or.inl hr)])
    fun s₂ ⟨h₂, g₂, x₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (stepsU_chain e lay2048.S (Nat.le_refl _) s₂ h₂) fun s₃ ⟨h₃, g₃, x₃⟩ => ?_
  have hB₃ : s₃.gpr .r11 = B := by
    rw [g₃ _ (by decide), g₂ _ (by decide), k₁.gpr _ (by decide)]
    exact (RegUpd.gpr_setReg_of_ne _ _ (by decide)).trans hB
  have wr₃ : s₃.wr = s.wr := by rw [h₃.1.wr]; rfl
  have m₃ : s₃.mem = s.mem := h₃.1.mem
  rw [WP.block_append_iff]
  refine WP.mono (stores_gen (accStores lay2048) s₃ hB₃ fun x hx =>
    wr₃ ▸ (let ⟨_, h, c⟩ := hs.region (accStores_lt x hx) (by decide); ⟨_, h, c⟩)) fun s₄ h₄ => ?_
  subst h₄
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, ?_⟩
  refine WP.mono (carryOut_ok hl (B := B) (L := fun p => lm lay2048 a m k bl p lay2048.S)
    (fun p _ q hq => lm_lt (by decide) hst.2.2.2.1 hq)
    (fun d hd => by rw [RegUpd.wr_setReg, wr₃]; exact hs.st hd)
    (by rw [RegUpd.gpr_setReg_of_ne _ _ (by decide)]; exact hB₃)
    (RegUpd.gpr_setReg_self _ _ _) fun p hp q hq => ?_) fun s' ⟨h, g, rd, wr, x⟩ => ?_
  · have h1 := Nat.mod_lt q (show 0 < lay2048.R by decide)
    have h2 : q / lay2048.R < 4 := Nat.div_lt_of_lt_mul (by simp only [Lay.L] at hq; rw [Nat.mul_comm]; exact hq)
    have := read_stores hl s₃.mem B s₃ hp (k := q % lay2048.R) (t := q / lay2048.R) h1 h2
    have er : regOf lay2048 p (q % lay2048.R) (lay2048.S % lay2048.R) =
        regOf lay2048 p (q % lay2048.R) lay2048.S := by
      rw [regOf_eq2048, regOf_eq2048, R2048, hS]; omega
    rw [er, (h₃.2 p hp).lanes _ h1 _ h2, ite_eq_right (by omega), Nat.add_zero, Nat.mod_add_div] at this
    rw [RegUpd.mem_setReg, show lay2048.D * p + lay2048.off q =
      lay2048.D * p + 32 * (q % lay2048.R) + 8 * (q / lay2048.R) by unfold Lay.off; omega]
    exact this
  refine ⟨fun p hp q hq => by rw [h.words p hp q hq]; simp only [hq, true_or, ite_true],
    fun p hp => by rw [h.c p hp]; simp only [Nat.not_lt_zero, ↓reduceIte], ?_,
    fun r r1 r2 r3 r4 r5 r6 r7 => ?_,
    by rw [g _ (by decide) (by decide) (by decide) (by decide)]; exact RegUpd.gpr_setReg_self _ _ _,
    by rw [rd, RegUpd.rd_setReg, h₃.1.rd]; rfl, by rw [wr, RegUpd.wr_setReg, wr₃],
    by rw [x, RegUpd.mxcsr_setReg, x₃, x₂, k₁.mxcsr]; rfl⟩
  · have o := wrList_outN (l := lay2048) B (o := 0) (n := lay2048.NB) (by omega)
      ((accStores lay2048).map fun x => (x.1, s₃.vy x.2)) s₃.mem fun x hx => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        exact accStores_win y hy
    have hf : OutN lay2048 B 0 lay2048.NB
        (wrList s₃.mem B ((accStores lay2048).map fun x => (x.1, s₃.vy x.2))) s'.mem := h.frame
    have o' : OutN lay2048 B 0 lay2048.NB s.mem
        (wrList s₃.mem B ((accStores lay2048).map fun x => (x.1, s₃.vy x.2))) :=
      fun x hx => (o x hx).trans (congrFun m₃ x)
    exact o'.trans hf
  · rw [g r r1 r2 r3 r4, RegUpd.gpr_setReg_of_ne _ _ r7, g₃ r r1, g₂ r r1, k₁.gpr r r1,
      RegUpd.gpr_setReg_of_ne _ _ r6]

theorem ammCoreU_core : CoreOk lay2048 (ammCoreU lay2048) := fun e hB hs => ammCoreU_ok e hB hs

/-- The multiplication of each layout. -/
theorem ammMul_core {l : Lay} (hl : LayOk l) : CoreOk l (ammMul l) := by
  unfold ammMul
  split
  · rename_i h; subst h; exact ammCoreU_core
  · exact ammCore_core hl.amm

end VG.Proof.Bignum.X86_64.Ifma
