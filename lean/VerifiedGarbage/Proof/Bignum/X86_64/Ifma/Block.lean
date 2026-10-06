import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Lane
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Lemmas

/-!
# RSA with AVX512_IFMA on x86-64, any size: a step on the machine

From a state with `StepIn`, the code of step
`i` leaves in role `k`'s lanes at step `i + 1` the limbs of
`Amm52N.step (4 R)`, the zero register still zero, and changes nothing but
the vector registers and `rax` (`ammStep_ok`); a block of `R` steps moves
`r9` to the next block's limbs and counts down `rcx` (`ammBlock_ok`).
-/

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Impl.Rsa.X86_64.CrtIfma
open VG.Proof.Bignum.X86_64.AmmSym (ops Ctx Keeps ofNat_add64)

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

theorem LayOk.bounds (hl : LayOk l) : 2 ≤ l.R ∧ l.R ≤ 10 := by
  rcases hl with rfl | rfl | rfl <;> decide

theorem regOf_lt {p k i : Nat} (hp : p < 2) (hR : 2 ≤ l.R) : regOf l p k i < 2 * l.R := by
  have := Nat.mod_lt (k + i) (show 0 < l.R by omega)
  have := Nat.mul_le_mul_left l.R (show p ≤ 1 by omega)
  unfold regOf; omega

theorem regOf_div {p k i : Nat} (hR : 2 ≤ l.R) : regOf l p k i / l.R = p := by
  unfold regOf
  rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega),
    Nat.div_eq_of_lt (Nat.mod_lt _ (by omega)), Nat.zero_add]

theorem regOf_mod {p k i : Nat} : regOf l p k i % l.R = (k + i) % l.R := by
  unfold regOf
  rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_mod]

theorem mod_role {R kk y : Nat} (hk : kk < R) (hy : y < R) : ((kk + y) % R + R - y) % R = kk := by
  by_cases h : kk + y < R
  · rw [Nat.mod_eq_of_lt h, show kk + y + R - y = kk + R by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hk]
  · have e : (kk + y) % R = kk + y - R := by
      rw [Nat.mod_eq_sub_mod (a := kk + y) (b := R) (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [e, show kk + y - R + R - y = kk by omega, Nat.mod_eq_of_lt hk]

theorem expReg_regOf {p kk i : Nat} (hp : p < 2) (hR : 2 ≤ l.R) (hk : kk < l.R) :
    expReg l i (regOf l p kk (i + 1)) = hT l p kk i := by
  have hr := regOf_lt (k := kk) (i := i + 1) hp hR
  simp only [expReg, hr, ite_true, regOf_div hR]
  congr 1
  unfold roleOf
  rw [regOf_mod, Nat.add_mod, Nat.mod_eq_of_lt hk]
  exact mod_role hk (Nat.mod_lt _ (by omega))

theorem expReg_zN (i : Nat) : expReg l i (zN l) = .reg (zN l) := by
  simp only [expReg, zN, tN, show ¬ 2 * l.R + 4 < 2 * l.R by omega, show 2 * l.R + 4 ≠ 2 * l.R by omega,
    show 2 * l.R + 4 ≠ 2 * l.R + 1 by omega, show 2 * l.R + 4 ≠ 2 * l.R + 2 by omega,
    show 2 * l.R + 4 ≠ 2 * l.R + 3 by omega, show 2 * l.R + 4 ≠ 2 * l.R + 5 by omega, ite_false]

theorem ammStep_ok (hl : LayOk l) {s : State} {i : Nat} (hi : i < l.R) {L a m : Nat → Nat → Nat}
    {k b : Nat → Nat} (h : StepIn l s i L a m k b) (hc : Ctx (lim l) s) :
    WP isa (.block (ammStep l i)) s fun s' =>
      (∀ p < 2, ∀ kk < l.R, ∀ t < 4, qv s' (vreg (regOf l p kk (i + 1))) t =
        BitVec.ofNat 64 (Amm52N.step l.L (ops a m k p) (L p) (b p) (kk + l.R * t))) ∧
      (∀ t < 4, qv s' (vreg (zN l)) t = 0) ∧ Keeps s s' := by
  obtain ⟨hR, hR10⟩ := hl.bounds
  obtain ⟨σ, e, hσ⟩ := run_ammStep hl hi
  refine WP.mono (run_ok hc (SRel.init s) e) fun s' hs => ⟨fun p hp kk hk t ht => ?_, fun t ht => ?_, ?_⟩
  · have hr := regOf_lt (k := kk) (i := i + 1) hp hR
    rw [hs.reg _ t ht, vi_vreg _ (by omega), hσ _ (by omega), expReg_regOf hp hR hk]
    exact hT_eval h hR hp hk ht
  · rw [hs.reg _ t ht, vi_vreg _ (by simp only [zN]; omega), hσ _ (by simp only [zN]; omega), expReg_zN]
    exact h.z t ht
  · exact ⟨fun r hr => hs.gpr hr, hs.mem, hs.rd, hs.wr, hs.mxcsr, hs.flags⟩

/-! ## The steps of a block -/

/-- What the multiplication reads, from the state `s₀` where it starts: the
operand `a` at `r8`, the modulus and `k₀` at `r10`, the second operand `bl`
at `r9` (each prime's at `D` further), all readable. -/
structure Env (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (s₀ : State) (a m : Nat → Nat → Nat) (k : Nat → Nat) (bl : Nat → Nat → Nat) : Prop where
  ina : ∀ p < 2, ∀ kk < l.R, ∀ t < 4,
    s₀.mem.readW (s₀.gpr .r8 + BitVec.ofNat 64 (l.D * p + 32 * kk + 8 * t)) 64 = BitVec.ofNat 64 (a p (kk + l.R * t))
  inm : ∀ p < 2, ∀ kk < l.R, ∀ t < 4,
    s₀.mem.readW (s₀.gpr .r10 + BitVec.ofNat 64 (l.D * p + oM + 32 * kk + 8 * t)) 64 =
      BitVec.ofNat 64 (m p (kk + l.R * t))
  ink : ∀ p < 2, ∀ t < 4,
    s₀.mem.readW (s₀.gpr .r10 + BitVec.ofNat 64 (l.D * p + l.oK0 + 8 * t)) 64 = BitVec.ofNat 64 (k p)
  inb : ∀ p < 2, ∀ j < l.L,
    s₀.mem.readW (s₀.gpr .r9 + BitVec.ofNat 64 (l.D * p + l.off j)) 64 = BitVec.ofNat 64 (bl p j)
  alt : ∀ p < 2, ∀ j < l.L, a p j < 2 ^ 52
  mlt : ∀ p < 2, ∀ j < l.L, m p j < 2 ^ 52
  klt : ∀ p < 2, k p < 2 ^ 52
  blt : ∀ p < 2, ∀ j < l.L, bl p j < 2 ^ 52
  rd8 : ∀ d n, 0 < n → d + n ≤ lim l .r8 → InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .r8 + BitVec.ofNat 64 d) n
  rd9 : ∀ d n, 0 < n → d + n ≤ lim l .r9 + 24 → InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .r9 + BitVec.ofNat 64 d) n
  rd10 : ∀ d n, 0 < n → d + n ≤ lim l .r10 → InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .r10 + BitVec.ofNat 64 d) n

/-- The limbs of prime `p` after `n` steps. -/
def lm (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (a m : Nat → Nat → Nat) (k : Nat → Nat) (bl : Nat → Nat → Nat) (p n : Nat) : Nat → Nat :=
  Amm52N.steps l.L (ops a m k p) (bl p) n fun _ => 0

theorem lm_lt (hR : l.R ≤ 10) {a m : Nat → Nat → Nat} {k : Nat → Nat} {bl : Nat → Nat → Nat} {p n j : Nat}
    (hn : n ≤ l.L) (hj : j < l.L) : lm l a m k bl p n j < 2 ^ 62 := by
  have := Amm52N.steps_lt (o := ops a m k p) (b := bl p) (L := fun _ => 0) (by simp only [Lay.L]; omega)
    (fun _ _ => by decide) n hn j hj
  have : (n + 1) * 2 ^ 56 ≤ 41 * 2 ^ 56 := Nat.mul_le_mul_right _ (by simp only [Lay.L] at hn; omega)
  unfold lm
  omega

/-- The machine within block `blk`, before step `i`: the lanes after
`R blk + i` steps, `r9` at the block's limbs, the zero register zero. -/
structure InBlk (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (s₀ s : State) (a m : Nat → Nat → Nat) (k : Nat → Nat) (bl : Nat → Nat → Nat)
    (blk i : Nat) : Prop where
  lanes : ∀ p < 2, ∀ kk < l.R, ∀ t < 4,
    qv s (vreg (regOf l p kk i)) t = BitVec.ofNat 64 (lm l a m k bl p (l.R * blk + i) (kk + l.R * t))
  z : ∀ t < 4, qv s (vreg (zN l)) t = 0
  r8 : s.gpr .r8 = s₀.gpr .r8
  r9 : s.gpr .r9 = s₀.gpr .r9 + BitVec.ofNat 64 (8 * blk)
  r10 : s.gpr .r10 = s₀.gpr .r10
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem lim_other {b : Reg} (h8 : b ≠ .r8) (h9 : b ≠ .r9) (h10 : b ≠ .r10) : lim l b = 0 := by
  simp only [lim, h8, h9, h10, ite_false]

theorem off_blk (hR : 2 ≤ l.R) {blk i : Nat} (hi : i < l.R) : l.off (l.R * blk + i) = 32 * i + 8 * blk := by
  unfold Lay.off
  rw [Nat.add_comm (l.R * blk), Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ (by omega),
    Nat.mod_eq_of_lt hi, Nat.div_eq_of_lt hi, Nat.zero_add]

theorem InBlk.stepIn (hl : LayOk l) {s₀ s : State} {a m : Nat → Nat → Nat} {k : Nat → Nat}
    {bl : Nat → Nat → Nat} {blk i : Nat} (hb : blk < 4) (hi : i < l.R) (e : Env l s₀ a m k bl)
    (h : InBlk l s₀ s a m k bl blk i) :
    StepIn l s i (fun p => lm l a m k bl p (l.R * blk + i)) a m k (fun p => bl p (l.R * blk + i)) ∧
      Ctx (lim l) s := by
  obtain ⟨hR, hR10⟩ := hl.bounds
  have hbi : l.R * blk + i < l.L := by
    have := Nat.mul_le_mul_left l.R (Nat.le_of_lt_succ hb)
    simp only [Lay.L]; omega
  refine ⟨⟨h.z, h.lanes, fun p _ j hj => lm_lt hR10 (by omega) hj, fun p hp kk hk t ht => ?_,
    fun p hp kk hk t ht => ?_, fun p hp t ht => ?_, fun p hp => ?_, e.alt, e.mlt, e.klt,
    fun p hp => e.blt p hp _ hbi⟩, ?_⟩
  · rw [h.mem, h.r8]; exact e.ina p hp kk hk t ht
  · rw [h.mem, h.r10]; exact e.inm p hp kk hk t ht
  · rw [h.mem, h.r10]; exact e.ink p hp t ht
  · rw [h.mem, h.r9, ofNat_add64, ← e.inb p hp (l.R * blk + i) hbi, off_blk hR hi]
    exact congrArg (fun d => s₀.mem.readW (s₀.gpr .r9 + BitVec.ofNat 64 d) 64) (by omega)
  · intro b d n hn hdn
    rw [h.rd, h.wr]
    by_cases b8 : b = .r8
    · subst b8; rw [h.r8]; exact e.rd8 d n hn hdn
    by_cases b9 : b = .r9
    · subst b9; rw [h.r9, ofNat_add64]; exact e.rd9 _ n hn (by omega)
    by_cases b10 : b = .r10
    · subst b10; rw [h.r10]; exact e.rd10 d n hn hdn
    · rw [lim_other b8 b9 b10] at hdn
      omega

theorem steps_chain (hl : LayOk l) {s₀ : State} {a m : Nat → Nat → Nat} {k : Nat → Nat}
    {bl : Nat → Nat → Nat} {blk : Nat} (hb : blk < 4) (e : Env l s₀ a m k bl) :
    ∀ i ≤ l.R, ∀ s, InBlk l s₀ s a m k bl blk 0 →
      WP isa (.block ((List.range i).flatMap (ammStep l))) s fun s' =>
        InBlk l s₀ s' a m k bl blk i ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.mxcsr = s.mxcsr := by
  intro i
  induction i with
  | zero => intro _ s h; exact WP.block_nil ⟨h, fun _ _ => rfl, rfl⟩
  | succ i ih =>
    intro hi s h
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (ih (by omega) s h) fun s₁ ⟨h₁, g₁, x₁⟩ => ?_
    obtain ⟨hst, hc⟩ := h₁.stepIn hl hb (by omega) e
    refine WP.mono (ammStep_ok hl (by omega) hst hc) fun s₂ ⟨l₂, z₂, k₂⟩ => ?_
    refine ⟨⟨fun p hp kk hk t ht => ?_, z₂, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun r hr => (k₂.gpr r hr).trans (g₁ r hr),
      k₂.mxcsr.trans x₁⟩
    · rw [l₂ p hp kk hk t ht]; rfl
    · rw [k₂.gpr _ (by decide)]; exact h₁.r8
    · rw [k₂.gpr _ (by decide)]; exact h₁.r9
    · rw [k₂.gpr _ (by decide)]; exact h₁.r10
    · rw [k₂.mem]; exact h₁.mem
    · rw [k₂.rd]; exact h₁.rd
    · rw [k₂.wr]; exact h₁.wr

theorem regOf_R (p kk : Nat) : regOf l p kk l.R = regOf l p kk 0 := by
  unfold regOf; rw [Nat.add_mod_right, Nat.add_zero]

/-- A block: `R` steps, `r9` to the next block's limbs, the count down. -/
theorem ammBlock_ok (hl : LayOk l) {s₀ s : State} {a m : Nat → Nat → Nat} {k : Nat → Nat}
    {bl : Nat → Nat → Nat} {blk : Nat} (hb : blk < 4) (e : Env l s₀ a m k bl)
    (h : InBlk l s₀ s a m k bl blk 0) (hcx : s.gpr .rcx = BitVec.ofNat 64 (4 - blk)) :
    WP isa (.block (ammBlock l)) s fun s' =>
      InBlk l s₀ s' a m k bl (blk + 1) 0 ∧ s'.gpr .rcx = BitVec.ofNat 64 (4 - (blk + 1)) ∧
      s'.zf = some (decide (blk + 1 = 4)) ∧ (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r9 → s'.gpr r = s.gpr r) ∧
      s'.mxcsr = s.mxcsr := by
  rw [show ammBlock l = (List.range l.R).flatMap (ammStep l) ++
    ([.alu .add .r9 (.imm 8), .alu .sub .rcx (.imm 1)] : List Instr) from rfl, WP.block_append_iff]
  refine WP.mono (steps_chain hl hb e l.R (Nat.le_refl _) s h) fun s₁ ⟨h₁, g₁, x₁⟩ => ?_
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  have r9₁ := h₁.r9
  have cx₁ : s₁.gpr .rcx = BitVec.ofNat 64 (4 - blk) := by rw [g₁ _ (by decide)]; exact hcx
  have e8 : BitVec.signExtend 64 (8 : BitVec 32) = BitVec.ofNat 64 8 := rfl
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := rfl
  have hc : BitVec.ofNat 64 (4 - blk) - 1 = BitVec.ofNat 64 (4 - (blk + 1)) := by
    rw [show 4 - blk = (4 - (blk + 1)) + 1 by omega, BitVec.ofNat_add]; exact BitVec.add_sub_cancel _ _
  simp only [e8, e1]
  generalize hS₂ : (arithFlags s₁ (s₁.gpr .r9 + BitVec.ofNat 64 8) _ _).setReg .r9 (s₁.gpr .r9 + BitVec.ofNat 64 8) = S₂
  have g₂ : ∀ r, r ≠ .r9 → S₂.gpr r = s₁.gpr r := fun r hr => by
    rw [← hS₂, RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]
  have r9₂ : S₂.gpr .r9 = s₁.gpr .r9 + BitVec.ofNat 64 8 := by rw [← hS₂, RegUpd.gpr_setReg_self]
  have q₂ : ∀ r t, qv S₂ r t = qv s₁ r t := fun r t => by rw [← hS₂]; rfl
  have v₂ : S₂.mem = s₁.mem ∧ S₂.rd = s₁.rd ∧ S₂.wr = s₁.wr ∧ S₂.mxcsr = s₁.mxcsr := by
    rw [← hS₂]; exact ⟨rfl, rfl, rfl, rfl⟩
  generalize hS₃ : (arithFlags S₂ (S₂.gpr .rcx - 1) _ _).setReg .rcx (S₂.gpr .rcx - 1) = S₃
  have g₃ : ∀ r, r ≠ .rcx → S₃.gpr r = S₂.gpr r := fun r hr => by
    rw [← hS₃, RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]
  have cx₃ : S₃.gpr .rcx = S₂.gpr .rcx - 1 := by rw [← hS₃, RegUpd.gpr_setReg_self]
  have z₃ : S₃.zf = some (S₂.gpr .rcx - 1 == 0) := by rw [← hS₃]; rfl
  have q₃ : ∀ r t, qv S₃ r t = qv S₂ r t := fun r t => by rw [← hS₃]; rfl
  have v₃ : S₃.mem = S₂.mem ∧ S₃.rd = S₂.rd ∧ S₃.wr = S₂.wr ∧ S₃.mxcsr = S₂.mxcsr := by
    rw [← hS₃]; exact ⟨rfl, rfl, rfl, rfl⟩
  have cx₂ : S₂.gpr .rcx = BitVec.ofNat 64 (4 - blk) := by rw [g₂ _ (by decide), cx₁]
  refine ⟨⟨fun p hp kk hk t ht => ?_, fun t ht => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_,
    fun r h1 h2 h3 => ?_, ?_⟩
  · rw [q₃, q₂, ← regOf_R p kk, show l.R * (blk + 1) + 0 = l.R * blk + l.R by rw [Nat.mul_add, Nat.mul_one, Nat.add_zero]]
    exact h₁.lanes p hp kk hk t ht
  · rw [q₃, q₂]; exact h₁.z t ht
  · rw [g₃ _ (by decide), g₂ _ (by decide)]; exact h₁.r8
  · rw [g₃ _ (by decide), r9₂, r9₁, BitVec.add_assoc, show 8 * (blk + 1) = 8 * blk + 8 by omega, BitVec.ofNat_add]
  · rw [g₃ _ (by decide), g₂ _ (by decide)]; exact h₁.r10
  · rw [v₃.1, v₂.1]; exact h₁.mem
  · rw [v₃.2.1, v₂.2.1]; exact h₁.rd
  · rw [v₃.2.2.1, v₂.2.2.1]; exact h₁.wr
  · rw [cx₃, cx₂, hc]
  · rw [z₃, cx₂, hc]
    rcases (by omega : blk = 0 ∨ blk = 1 ∨ blk = 2 ∨ blk = 3) with rfl | rfl | rfl | rfl <;> rfl
  · rw [g₃ _ h2, g₂ _ h3]; exact g₁ r h1
  · rw [v₃.2.2.2, v₂.2.2.2]; exact x₁

end VG.Proof.Bignum.X86_64.Ifma
