import VerifiedGarbage.Proof.Bignum.X86_64.AmmLane
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-!
# RSA with AVX512_IFMA on x86-64: a step on the machine

`ammStep_ok`: from a state with `StepIn`, the code of step `i` leaves in
role `k`'s lanes at step `i + 1` the limbs of `Amm52.step`, register 14
still zero, and changes nothing but the vector registers and `rax`.
-/

namespace VG.Proof.Bignum.X86_64.AmmSym

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Impl.Rsa.X86_64.CrtIfma (D oM oK0 ammStep)
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi qw)

theorem xi_xr : ∀ r < 16, xi (xr r) = r := by decide

theorem regOf_lt {p k i : Nat} (hp : p < 2) : regOf p k i < 10 := by unfold regOf; omega

theorem expReg_regOf {p kk i : Nat} (hp : p < 2) (hk : kk < 5) :
    expReg i (regOf p kk (i + 1)) = hT p kk i := by
  have hr := regOf_lt (k := kk) (i := i + 1) hp
  simp only [expReg, hr, ite_true]
  congr 1
  · unfold regOf; omega
  · unfold roleOf regOf; omega

/-- What a step keeps: everything but the vector registers and `rax`. -/
structure Keeps (s s' : State) : Prop where
  gpr : ∀ r, r ≠ .rax → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mxcsr : s'.mxcsr = s.mxcsr
  flags : s'.cf = s.cf ∧ s'.zf = s.zf ∧ s'.sf = s.sf ∧ s'.of = s.of

theorem Keeps.trans {s₁ s₂ s₃ : State} (h₁ : Keeps s₁ s₂) (h₂ : Keeps s₂ s₃) : Keeps s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr, h₂.mxcsr.trans h₁.mxcsr,
    ⟨h₂.flags.1.trans h₁.flags.1, h₂.flags.2.1.trans h₁.flags.2.1, h₂.flags.2.2.1.trans h₁.flags.2.2.1,
      h₂.flags.2.2.2.trans h₁.flags.2.2.2⟩⟩

theorem ammStep_ok {s : State} {i : Nat} (hi : i < 5) {L a m : Nat → Nat → Nat} {k b : Nat → Nat}
    (h : StepIn s i L a m k b) (hc : Ctx lim s) :
    WP isa (.block (ammStep i)) s fun s' =>
      (∀ p < 2, ∀ kk < 5, ∀ t < 4, qw s' (xr (regOf p kk (i + 1))) t =
        BitVec.ofNat 64 (step (ops a m k p) (L p) (b p) (kk + 5 * t))) ∧
      (∀ t < 4, qw s' .xmm14 t = 0) ∧ Keeps s s' := by
  obtain ⟨σ, e, hσ⟩ := run_ammStep hi
  refine WP.mono (run_ok hc e) fun s' hs => ⟨fun p hp kk hk t ht => ?_, fun t ht => ?_, ?_⟩
  · have hr := regOf_lt (k := kk) (i := i + 1) hp
    rw [hs.reg _ t ht, xi_xr _ (by omega), hσ _ (by omega), expReg_regOf hp hk]
    exact hT_eval h hp hk ht
  · rw [hs.reg _ t ht, show xi .xmm14 = 14 from rfl, hσ 14 (by decide)]
    simp only [expReg, show ¬ (14 : Nat) < 10 by decide, ite_false, show (14 : Nat) ≠ 10 by decide,
      show (14 : Nat) ≠ 11 by decide, show (14 : Nat) ≠ 12 by decide, show (14 : Nat) ≠ 13 by decide,
      show (14 : Nat) ≠ 15 by decide, A.eval]
    exact h.z t ht
  · exact ⟨fun r hr => hs.gpr hr, hs.mem, hs.rd, hs.wr, hs.mxcsr, hs.flags⟩

/-! ## The steps of a block -/

/-- What the multiplication reads, from the state `s₀` where it starts: the
operand `a` at `r8`, the modulus and `k₀` at `r10`, the second operand `bl`
at `r9` (each prime's at `D` further), all readable. -/
structure Env (s₀ : State) (a m : Nat → Nat → Nat) (k : Nat → Nat) (bl : Nat → Nat → Nat) : Prop where
  ina : ∀ p < 2, ∀ kk < 5, ∀ t < 4,
    s₀.mem.readW (s₀.gpr .r8 + BitVec.ofNat 64 (D * p + 32 * kk + 8 * t)) 64 = BitVec.ofNat 64 (a p (kk + 5 * t))
  inm : ∀ p < 2, ∀ kk < 5, ∀ t < 4,
    s₀.mem.readW (s₀.gpr .r10 + BitVec.ofNat 64 (D * p + oM + 32 * kk + 8 * t)) 64 =
      BitVec.ofNat 64 (m p (kk + 5 * t))
  ink : ∀ p < 2, ∀ t < 4, s₀.mem.readW (s₀.gpr .r10 + BitVec.ofNat 64 (D * p + oK0 + 8 * t)) 64 = BitVec.ofNat 64 (k p)
  inb : ∀ p < 2, ∀ l < 20,
    s₀.mem.readW (s₀.gpr .r9 + BitVec.ofNat 64 (D * p + VG.Impl.Rsa.X86_64.CrtIfma.off l)) 64 = BitVec.ofNat 64 (bl p l)
  alt : ∀ p < 2, ∀ j < 20, a p j < 2 ^ 52
  mlt : ∀ p < 2, ∀ j < 20, m p j < 2 ^ 52
  klt : ∀ p < 2, k p < 2 ^ 52
  blt : ∀ p < 2, ∀ l < 20, bl p l < 2 ^ 52
  rd8 : ∀ d n, 0 < n → d + n ≤ lim .r8 → InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .r8 + BitVec.ofNat 64 d) n
  rd9 : ∀ d n, 0 < n → d + n ≤ lim .r9 + 24 → InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .r9 + BitVec.ofNat 64 d) n
  rd10 : ∀ d n, 0 < n → d + n ≤ lim .r10 → InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .r10 + BitVec.ofNat 64 d) n

/-- The limbs of prime `p` after `n` steps. -/
def lm (a m : Nat → Nat → Nat) (k : Nat → Nat) (bl : Nat → Nat → Nat) (p n : Nat) : Nat → Nat :=
  steps (ops a m k p) (bl p) n fun _ => 0

theorem lm_lt {a m : Nat → Nat → Nat} {k : Nat → Nat} {bl : Nat → Nat → Nat} {p n j : Nat} (hn : n ≤ 20)
    (hj : j < 20) : lm a m k bl p n j < 2 ^ 61 := by
  have := steps_lt (o := ops a m k p) (b := bl p) (L := fun _ => 0) (fun _ _ => by decide) n hn j hj
  unfold lm
  omega

/-- The machine within block `blk`, before step `i`: the lanes after
`5 blk + i` steps, `r9` at the block's limbs, register 14 zero. -/
structure InBlk (s₀ s : State) (a m : Nat → Nat → Nat) (k : Nat → Nat) (bl : Nat → Nat → Nat)
    (blk i : Nat) : Prop where
  lanes : ∀ p < 2, ∀ kk < 5, ∀ t < 4,
    qw s (xr (regOf p kk i)) t = BitVec.ofNat 64 (lm a m k bl p (5 * blk + i) (kk + 5 * t))
  z : ∀ t < 4, qw s .xmm14 t = 0
  r8 : s.gpr .r8 = s₀.gpr .r8
  r9 : s.gpr .r9 = s₀.gpr .r9 + BitVec.ofNat 64 (8 * blk)
  r10 : s.gpr .r10 = s₀.gpr .r10
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem lim9 : lim .r9 = D + 136 := rfl
theorem lim_other {b : Reg} (h8 : b ≠ .r8) (h9 : b ≠ .r9) (h10 : b ≠ .r10) : lim b = 0 := by
  simp only [lim, h8, h9, h10, ite_false]

theorem ofNat_add64 (x : BitVec 64) (c d : Nat) :
    x + BitVec.ofNat 64 c + BitVec.ofNat 64 d = x + BitVec.ofNat 64 (c + d) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem InBlk.stepIn {s₀ s : State} {a m : Nat → Nat → Nat} {k : Nat → Nat} {bl : Nat → Nat → Nat}
    {blk i : Nat} (hb : blk < 4) (hi : i < 5) (e : Env s₀ a m k bl) (h : InBlk s₀ s a m k bl blk i) :
    StepIn s i (fun p => lm a m k bl p (5 * blk + i)) a m k (fun p => bl p (5 * blk + i)) ∧ Ctx lim s := by
  refine ⟨⟨h.z, h.lanes, fun p _ j hj => lm_lt (by omega) hj, fun p hp kk hk t ht => ?_,
    fun p hp kk hk t ht => ?_, fun p hp t ht => ?_, fun p hp => ?_, e.alt, e.mlt, e.klt,
    fun p hp => e.blt p hp _ (by omega)⟩, ?_⟩
  · rw [h.mem, h.r8]; exact e.ina p hp kk hk t ht
  · rw [h.mem, h.r10]; exact e.inm p hp kk hk t ht
  · rw [h.mem, h.r10]; exact e.ink p hp t ht
  · rw [h.mem, h.r9, ofNat_add64, ← e.inb p hp (5 * blk + i) (by omega)]
    congr 3
    unfold VG.Impl.Rsa.X86_64.CrtIfma.off; omega
  · intro b d n hn hdn
    rw [h.rd, h.wr]
    by_cases b8 : b = .r8
    · subst b8; rw [h.r8]; exact e.rd8 d n hn hdn
    by_cases b9 : b = .r9
    · subst b9; rw [h.r9, ofNat_add64]; exact e.rd9 _ n hn (by rw [lim9] at hdn ⊢; omega)
    by_cases b10 : b = .r10
    · subst b10; rw [h.r10]; exact e.rd10 d n hn hdn
    · rw [lim_other b8 b9 b10] at hdn
      omega

theorem steps_chain {s₀ : State} {a m : Nat → Nat → Nat} {k : Nat → Nat} {bl : Nat → Nat → Nat}
    {blk : Nat} (hb : blk < 4) (e : Env s₀ a m k bl) :
    ∀ i ≤ 5, ∀ s, InBlk s₀ s a m k bl blk 0 →
      WP isa (.block ((List.range i).flatMap ammStep)) s fun s' =>
        InBlk s₀ s' a m k bl blk i ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.mxcsr = s.mxcsr := by
  intro i
  induction i with
  | zero => intro _ s h; exact WP.block_nil ⟨h, fun _ _ => rfl, rfl⟩
  | succ i ih =>
    intro hi s h
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (ih (by omega) s h) fun s₁ ⟨h₁, g₁, x₁⟩ => ?_
    obtain ⟨hst, hc⟩ := h₁.stepIn hb (by omega) e
    refine WP.mono (ammStep_ok (by omega) hst hc) fun s₂ ⟨l₂, z₂, k₂⟩ => ?_
    refine ⟨⟨fun p hp kk hk t ht => ?_, z₂, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun r hr => (k₂.gpr r hr).trans (g₁ r hr),
      k₂.mxcsr.trans x₁⟩
    · rw [l₂ p hp kk hk t ht]; rfl
    · rw [k₂.gpr _ (by decide)]; exact h₁.r8
    · rw [k₂.gpr _ (by decide)]; exact h₁.r9
    · rw [k₂.gpr _ (by decide)]; exact h₁.r10
    · rw [k₂.mem]; exact h₁.mem
    · rw [k₂.rd]; exact h₁.rd
    · rw [k₂.wr]; exact h₁.wr

theorem regOf_five (p kk : Nat) : regOf p kk 5 = regOf p kk 0 := by unfold regOf; omega

/-- A block: five steps, `r9` to the next block's limbs, the count down. -/
theorem ammBlock_ok {s₀ s : State} {a m : Nat → Nat → Nat} {k : Nat → Nat} {bl : Nat → Nat → Nat}
    {blk : Nat} (hb : blk < 4) (e : Env s₀ a m k bl) (h : InBlk s₀ s a m k bl blk 0)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 (4 - blk)) :
    WP isa (.block VG.Impl.Rsa.X86_64.CrtIfma.ammBlock) s fun s' =>
      InBlk s₀ s' a m k bl (blk + 1) 0 ∧ s'.gpr .rcx = BitVec.ofNat 64 (4 - (blk + 1)) ∧
      s'.zf = some (decide (blk + 1 = 4)) ∧ (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r9 → s'.gpr r = s.gpr r) ∧
      s'.mxcsr = s.mxcsr := by
  rw [show VG.Impl.Rsa.X86_64.CrtIfma.ammBlock = (List.range 5).flatMap ammStep ++
    ([.alu .add .r9 (.imm 8), .alu .sub .rcx (.imm 1)] : List Instr) from rfl, WP.block_append_iff]
  refine WP.mono (steps_chain hb e 5 (Nat.le_refl _) s h) fun s₁ ⟨h₁, g₁, x₁⟩ => ?_
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
  have q₂ : ∀ r t, qw S₂ r t = qw s₁ r t := fun r t => by rw [← hS₂]; rfl
  have v₂ : S₂.mem = s₁.mem ∧ S₂.rd = s₁.rd ∧ S₂.wr = s₁.wr ∧ S₂.mxcsr = s₁.mxcsr := by
    rw [← hS₂]; exact ⟨rfl, rfl, rfl, rfl⟩
  generalize hS₃ : (arithFlags S₂ (S₂.gpr .rcx - 1) _ _).setReg .rcx (S₂.gpr .rcx - 1) = S₃
  have g₃ : ∀ r, r ≠ .rcx → S₃.gpr r = S₂.gpr r := fun r hr => by
    rw [← hS₃, RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]
  have cx₃ : S₃.gpr .rcx = S₂.gpr .rcx - 1 := by rw [← hS₃, RegUpd.gpr_setReg_self]
  have z₃ : S₃.zf = some (S₂.gpr .rcx - 1 == 0) := by rw [← hS₃]; rfl
  have q₃ : ∀ r t, qw S₃ r t = qw S₂ r t := fun r t => by rw [← hS₃]; rfl
  have v₃ : S₃.mem = S₂.mem ∧ S₃.rd = S₂.rd ∧ S₃.wr = S₂.wr ∧ S₃.mxcsr = S₂.mxcsr := by
    rw [← hS₃]; exact ⟨rfl, rfl, rfl, rfl⟩
  have cx₂ : S₂.gpr .rcx = BitVec.ofNat 64 (4 - blk) := by rw [g₂ _ (by decide), cx₁]
  refine ⟨⟨fun p hp kk hk t ht => ?_, fun t ht => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_,
    fun r h1 h2 h3 => ?_, ?_⟩
  · rw [q₃, q₂, ← regOf_five p kk, show 5 * (blk + 1) + 0 = 5 * blk + 5 by omega]
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

end VG.Proof.Bignum.X86_64.AmmSym
