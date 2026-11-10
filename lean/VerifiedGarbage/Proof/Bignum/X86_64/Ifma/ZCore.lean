module

public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.ZStep
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Spec
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-!
# RSA with AVX512_IFMA on x86-64: the multiplication modulo `-1 (mod 2¹⁰⁴)`

`ammCoreZ` (`Impl/Rsa/X86_64/CrtIfma.lean`) from the operands it reads
(`EnvZ`: the first operand's rows at `r8`, the second operand's limbs at
`r9`, and the rows of the modulus plus one at `rbx + oMs`, whose limbs 0
and 1 are zero, from limb 2 on): its start leaves the two sets of limbs zero in the roles
of step 0 (`zStart_ok`), each block of `R` steps and the steps after the
last block leave `AmmD52.steps`' limbs (`zSteps_ok`, `zLoop_ok`), and the
end stores `AmmD52.tot` of them, which `carryOut` carries (`ammCoreZ_ok`).
-/
-- separate module: the multiplication down to its instructions; `Area` is about the regions' numbers and is rebuilt when their facts change.

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64
open VG.Proof.Bignum.Amm52 (lo hi lo_lt hi_lt carried lval lval_congr lval_lt carried_lt carried_val)
open VG.Proof.Bignum.AmmD52 (Ops St Ok lowS stepQ pend)
open VG.Proof.Bignum (off word)
open VG.Impl.Rsa.X86_64.CrtIfma
open VG.Proof.Bignum.X86_64.AmmSym (Ctx ofNat_add64 off_add ofNat_toNat64)
open VG.Proof.X25519.X86_64.Ifma (mad52)
open VG.Proof.Poly1305.X86_64.Avx2 (sel4)

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-- What the multiplication reads, from the state `s₀` where it starts
(with `r10` the area): the first operand `a` at `r8`, the second operand
`bl` at `r9`, and at `r10 + oMs` the modulus plus one `ms` over `2¹⁰⁴`,
that is, its limbs from limb 2 on, the last two zero; lane 1's `D` further,
all readable. -/
structure EnvZ (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (s₀ : State) (a ms bl : Nat → Nat → Nat) : Prop where
  ina : ∀ p < 2, ∀ kk < l.R, ∀ t < 4,
    s₀.mem.readW (s₀.gpr .r8 + BitVec.ofNat 64 (l.D * p + 32 * kk + 8 * t)) 64 =
      BitVec.ofNat 64 (a p (l.R * t + kk))
  inm : ∀ p < 2, ∀ kk < l.R, ∀ t < 4,
    s₀.mem.readW (s₀.gpr .r10 + BitVec.ofNat 64 (l.D * p + l.oMs + 32 * kk + 8 * t)) 64 =
      BitVec.ofNat 64 (ms p (l.R * t + kk + 2))
  mtop : ∀ p < 2, ms p l.L = 0 ∧ ms p (l.L + 1) = 0
  inb : ∀ p < 2, ∀ j < l.L,
    s₀.mem.readW (s₀.gpr .r9 + BitVec.ofNat 64 (l.D * p + l.off j)) 64 = BitVec.ofNat 64 (bl p j)
  ok : ∀ p < 2, Ok l.L ⟨a p, ms p⟩
  blt : ∀ p < 2, ∀ j < l.L, bl p j < 2 ^ 52
  rd8 : ∀ d n, 0 < n → d + n ≤ l.D + l.NB → InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .r8 + BitVec.ofNat 64 d) n
  rd9 : ∀ d n, 0 < n → d + n ≤ l.D + l.NB → InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .r9 + BitVec.ofNat 64 d) n
  rd10 : ∀ d n, 0 < n → d + n ≤ l.D + l.oMs + l.NB →
    InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .r10 + BitVec.ofNat 64 d) n

/-- Lane `p`'s operands. -/
def zo (a ms : Nat → Nat → Nat) (p : Nat) : Ops := ⟨a p, ms p⟩

/-- Lane `p`'s limbs after `n` steps. -/
def zst (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (a ms bl : Nat → Nat → Nat) (p n : Nat) : St :=
  AmmD52.steps l.L l.R (zo a ms p) (bl p) n ⟨fun _ => 0, fun _ => 0, 0⟩

/-- The limbs the multiplication stores, lane `p`'s. -/
def zlm (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (a ms bl : Nat → Nat → Nat) (p : Nat) : Nat → Nat :=
  AmmD52.tot l.R (zo a ms p) (zst l a ms bl p l.S)

/-- The machine within block `blk`, before step `i`: the lanes after
`R blk + i` steps, with the low halves of row 0's products with the limb
`b`; `r9` at the block's limbs. -/
structure InZ (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (s₀ s : State) (a ms bl : Nat → Nat → Nat) (blk i : Nat)
    (b : Nat → Nat) : Prop where
  acc : ∃ w, ZAcc l s i (zo a ms) (fun p => zst l a ms bl p (l.R * blk + i)) b w ((l.R * blk + i + 1) * 2 ^ 56)
  con : ZCon l s (zo a ms)
  r8 : s.gpr .r8 = s₀.gpr .r8
  r9 : s.gpr .r9 = s₀.gpr .r9 + BitVec.ofNat 64 (8 * blk)
  r10 : s.gpr .r10 = s₀.gpr .r10
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The limb of the second operand of step `R blk + i`, in its register. -/
def BqZ (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (s : State) (bl : Nat → Nat → Nat) (blk i : Nat) : Prop :=
  ∀ k < 8, qz s (zBq l (i % 2)) k = BitVec.ofNat 64 (bl (k / 4) (l.R * blk + i))

theorem ZOk.S (hz : ZOk l) : l.S = 22 := by rw [hz]; rfl
theorem ZOk.NB (hz : ZOk l) : l.NB = 192 := by rw [hz]; rfl

/-- The limb after step `i` of a block, from the block's `r9`. -/
theorem off_next (hR : l.R = 6) {blk i : Nat} (_ : i < 6) :
    l.off (l.R * blk + i + 1) = l.off (i + 1) + 8 * blk := by
  unfold Lay.off; rw [hR]; omega

/-- The loads' bounds in a block. -/
theorem InZ.ctx (hz : ZOk l) {s₀ s : State} {a ms bl : Nat → Nat → Nat} {blk i : Nat} {b : Nat → Nat}
    (e : EnvZ l s₀ a ms bl) (h : InZ l s₀ s a ms bl blk i b) (hb : blk ≤ 3) : Ctx (limZ l) s := by
  have hR := hz.R; have hN := hz.NB
  intro r d n hn hdn
  rw [h.rd, h.wr]
  by_cases b8 : r = .r8
  · subst b8; rw [h.r8]; exact e.rd8 d n hn hdn
  by_cases b9 : r = .r9
  · subst b9; rw [h.r9, ofNat_add64]
    exact e.rd9 _ n hn (by simp only [limZ] at hdn; omega)
  by_cases b10 : r = .r10
  · subst b10; rw [h.r10]; exact e.rd10 d n hn hdn
  · have : limZ l r = 0 := by cases r <;> first | rfl | contradiction
    omega

/-! ## The steps of a block -/

theorem ZAcc.congr {s s' : State} {i : Nat} {o : Nat → Ops} {st : Nat → St} {b w : Nat → Nat} {Bd : Nat}
    (h : ZAcc l s i o st b w Bd) (hq : ∀ r k, qz s' r k = qz s r k) : ZAcc l s' i o st b w Bd :=
  ⟨fun kk hkk k hk => (hq _ _).trans (h.bs kk hkk k hk), fun kk hkk k hk => (hq _ _).trans (h.us kk hkk k hk),
    fun k hk => (hq _ _).trans (h.up k hk), h.wq, h.bd⟩

theorem ZCon.congr {s s' : State} {o : Nat → Ops} (h : ZCon l s o) (hq : ∀ r k, qz s' r k = qz s r k) :
    ZCon l s' o :=
  ⟨fun kk hkk k hk => (hq _ _).trans (h.a kk hkk k hk), fun kk h1 hkk k hk => (hq _ _).trans (h.m kk h1 hkk k hk),
    fun k hk => (hq _ _).trans (h.m0 k hk), fun k hk => (hq _ _).trans (h.m1 k hk),
    fun k hk => (hq _ _).trans (h.k k hk)⟩

/-- After `R` steps the roles are those of step 0. -/
theorem ZAcc.wrap (hR : l.R = 6) {s : State} {o : Nat → Ops} {st : Nat → St} {b w : Nat → Nat} {Bd : Nat}
    (h : ZAcc l s l.R o st b w Bd) : ZAcc l s 0 o st b w Bd := by
  have eB : ∀ kk, zB l kk l.R = zB l kk 0 := fun kk => by unfold zB; rw [Nat.add_mod_right, Nat.add_zero]
  have eU : ∀ kk, zU l kk l.R = zU l kk 0 := fun kk => by unfold zU; rw [Nat.add_mod_right, Nat.add_zero]
  have eq : zUq l ((l.R + 1) % 2) = zUq l ((0 + 1) % 2) := by rw [hR]
  exact ⟨fun kk hkk k hk => eB kk ▸ h.bs kk hkk k hk, fun kk hkk k hk => eU kk ▸ h.us kk hkk k hk,
    fun k hk => eq ▸ h.up k hk, h.wq, h.bd⟩

/-- Steps 0 to `n - 1` of block `blk`, each with a limb of the second
operand after it. -/
theorem zSteps_ok (hz : ZOk l) {s₀ : State} {a ms bl : Nat → Nat → Nat} {blk : Nat} (e : EnvZ l s₀ a ms bl)
    (hb : blk ≤ 3) :
    ∀ n ≤ l.R, l.R * blk + n < l.L → ∀ s, InZ l s₀ s a ms bl blk 0 (fun p => bl p (l.R * blk + 0)) →
      BqZ l s bl blk 0 →
      WP isa (.block ((List.range n).flatMap fun i => zStep l i false)) s fun s' =>
        InZ l s₀ s' a ms bl blk n (fun p => bl p (l.R * blk + n)) ∧ BqZ l s' bl blk n ∧ s'.gpr = s.gpr ∧
          s'.mxcsr = s.mxcsr := by
  have hR := hz.R; have hL := hz.L
  intro n
  induction n with
  | zero => intro _ _ s h hq; exact WP.block_nil ⟨h, hq, rfl, rfl⟩
  | succ n ih =>
    intro hn hlt s h hq
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (ih (by omega) (by omega) s h hq) fun s₁ ⟨h₁, q₁, g₁, x₁⟩ => ?_
    obtain ⟨w, acc⟩ := h₁.acc
    have hin : ZIn l s₁ n (zo a ms) (fun p => zst l a ms bl p (l.R * blk + n)) (fun p => bl p (l.R * blk + n)) w
        ((l.R * blk + n + 1) * 2 ^ 56) := ⟨acc, h₁.con, q₁, e.ok, by omega⟩
    have hrd : ∀ p < 2, s₁.mem.readW (s₁.gpr .r9 + BitVec.ofNat 64 (l.D * p + l.off (n + 1))) 64 =
        BitVec.ofNat 64 (bl p (l.R * blk + (n + 1))) := fun p hp => by
      rw [h₁.mem, h₁.r9, ofNat_add64, ← e.inb p hp (l.R * blk + (n + 1)) hlt,
        show l.R * blk + (n + 1) = l.R * blk + n + 1 from rfl, off_next hR (by omega)]
      exact congrArg (fun d => s₀.mem.readW (s₀.gpr .r9 + BitVec.ofNat 64 d) 64) (by omega)
    refine WP.mono (zStep_ok hz (by omega) hin false (bn := fun p => bl p (l.R * blk + (n + 1)))
      (fun _ => by have := hrd 0 (by decide); rwa [Nat.mul_zero, Nat.zero_add] at this)
      (fun _ => by have := hrd 1 (by decide); rwa [Nat.mul_one] at this)
      (fun h0 => absurd h0 (by decide)) (h₁.ctx hz e hb)) fun s₂ ⟨acc₂, con₂, q₂, k₂⟩ => ?_
    have eB : (l.R * blk + n + 1) * 2 ^ 56 + 2 ^ 56 = (l.R * blk + (n + 1) + 1) * 2 ^ 56 := by omega
    exact ⟨⟨⟨_, eB ▸ acc₂⟩, con₂, by rw [k₂.gpr]; exact h₁.r8, by rw [k₂.gpr]; exact h₁.r9,
      by rw [k₂.gpr]; exact h₁.r10, k₂.mem.trans h₁.mem, k₂.rd.trans h₁.rd, k₂.wr.trans h₁.wr⟩, q₂ rfl,
      k₂.gpr.trans g₁, k₂.mxcsr.trans x₁⟩

theorem ZOk.blocks (hz : ZOk l) : l.S / l.R = 3 := by rw [hz]; rfl

/-- A block: `R` steps, `r9` to the next block's limbs, the count down. -/
theorem zBlock_ok (hz : ZOk l) {s₀ s : State} {a ms bl : Nat → Nat → Nat} {blk : Nat} (hb : blk < l.S / l.R)
    (e : EnvZ l s₀ a ms bl) (h : InZ l s₀ s a ms bl blk 0 (fun p => bl p (l.R * blk + 0)))
    (hq : BqZ l s bl blk 0) (hcx : s.gpr .rcx = BitVec.ofNat 64 (l.S / l.R - blk)) :
    WP isa (.block (zBlock l)) s fun s' =>
      InZ l s₀ s' a ms bl (blk + 1) 0 (fun p => bl p (l.R * (blk + 1) + 0)) ∧ BqZ l s' bl (blk + 1) 0 ∧
      s'.gpr .rcx = BitVec.ofNat 64 (l.S / l.R - (blk + 1)) ∧
      s'.zf = some (decide (blk + 1 = l.S / l.R)) ∧ (∀ r, r ≠ .rcx → r ≠ .r9 → s'.gpr r = s.gpr r) ∧
      s'.mxcsr = s.mxcsr := by
  have hR := hz.R; have hL := hz.L; have h3 := hz.blocks
  rw [show zBlock l = ((List.range l.R).flatMap fun i => zStep l i false) ++
    ([.alu .add .r9 (.imm 8), .alu .sub .rcx (.imm 1)] : List Instr) from rfl, WP.block_append_iff]
  have hlt : l.R * blk + l.R < l.L := by
    have : l.R * blk ≤ l.R * 2 := Nat.mul_le_mul_left _ (by omega)
    omega
  refine WP.mono (zSteps_ok hz e (by omega) l.R (Nat.le_refl _) hlt s h hq) fun s₁ ⟨h₁, q₁, g₁, x₁⟩ => ?_
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  have r9₁ := h₁.r9
  have cx₁ : s₁.gpr .rcx = BitVec.ofNat 64 (l.S / l.R - blk) := by rw [g₁]; exact hcx
  have e8 : BitVec.signExtend 64 (8 : BitVec 32) = BitVec.ofNat 64 8 := rfl
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := rfl
  have hc : BitVec.ofNat 64 (l.S / l.R - blk) - 1 = BitVec.ofNat 64 (l.S / l.R - (blk + 1)) := by
    rw [show l.S / l.R - blk = (l.S / l.R - (blk + 1)) + 1 by omega, BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _
  simp only [e8, e1]
  generalize hS₂ : (arithFlags s₁ (s₁.gpr .r9 + BitVec.ofNat 64 8) _ _).setReg .r9 (s₁.gpr .r9 + BitVec.ofNat 64 8) = S₂
  have g₂ : ∀ r, r ≠ .r9 → S₂.gpr r = s₁.gpr r := fun r hr => by
    rw [← hS₂, RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]
  have r9₂ : S₂.gpr .r9 = s₁.gpr .r9 + BitVec.ofNat 64 8 := by rw [← hS₂, RegUpd.gpr_setReg_self]
  have q₂ : ∀ r k, qz S₂ r k = qz s₁ r k := fun r k => by rw [← hS₂]; rfl
  have v₂ : S₂.mem = s₁.mem ∧ S₂.rd = s₁.rd ∧ S₂.wr = s₁.wr ∧ S₂.mxcsr = s₁.mxcsr := by
    rw [← hS₂]; exact ⟨rfl, rfl, rfl, rfl⟩
  generalize hS₃ : (arithFlags S₂ (S₂.gpr .rcx - 1) _ _).setReg .rcx (S₂.gpr .rcx - 1) = S₃
  have g₃ : ∀ r, r ≠ .rcx → S₃.gpr r = S₂.gpr r := fun r hr => by
    rw [← hS₃, RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]
  have cx₃ : S₃.gpr .rcx = S₂.gpr .rcx - 1 := by rw [← hS₃, RegUpd.gpr_setReg_self]
  have z₃ : S₃.zf = some (S₂.gpr .rcx - 1 == 0) := by rw [← hS₃]; rfl
  have q₃ : ∀ r k, qz S₃ r k = qz S₂ r k := fun r k => by rw [← hS₃]; rfl
  have v₃ : S₃.mem = S₂.mem ∧ S₃.rd = S₂.rd ∧ S₃.wr = S₂.wr ∧ S₃.mxcsr = S₂.mxcsr := by
    rw [← hS₃]; exact ⟨rfl, rfl, rfl, rfl⟩
  have cx₂ : S₂.gpr .rcx = BitVec.ofNat 64 (l.S / l.R - blk) := by rw [g₂ _ (by decide), cx₁]
  have q₃₁ : ∀ r k, qz S₃ r k = qz s₁ r k := fun r k => (q₃ r k).trans (q₂ r k)
  have eI : l.R * (blk + 1) + 0 = l.R * blk + l.R := by rw [Nat.mul_add, Nat.mul_one, Nat.add_zero]
  obtain ⟨w, acc₁⟩ := h₁.acc
  refine ⟨⟨⟨w, ?_⟩, h₁.con.congr q₃₁, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun k hk => ?_, ?_, ?_, fun r h1 h2 => ?_, ?_⟩
  · rw [eI]; exact (acc₁.congr q₃₁).wrap hR
  · rw [g₃ _ (by decide), g₂ _ (by decide)]; exact h₁.r8
  · rw [g₃ _ (by decide), r9₂, r9₁, BitVec.add_assoc, show 8 * (blk + 1) = 8 * blk + 8 by omega, BitVec.ofNat_add]
  · rw [g₃ _ (by decide), g₂ _ (by decide)]; exact h₁.r10
  · rw [v₃.1, v₂.1]; exact h₁.mem
  · rw [v₃.2.1, v₂.2.1]; exact h₁.rd
  · rw [v₃.2.2.1, v₂.2.2.1]; exact h₁.wr
  · rw [eI, q₃₁, show zBq l (0 % 2) = zBq l (l.R % 2) by rw [hR]]; exact q₁ k hk
  · rw [cx₃, cx₂, hc]
  · rw [z₃, cx₂, hc, h3]
    rcases (by omega : blk = 0 ∨ blk = 1 ∨ blk = 2) with rfl | rfl | rfl <;> rfl
  · rw [g₃ _ h1, g₂ _ h2, g₁]
  · rw [v₃.2.2.2, v₂.2.2.2]; exact x₁

/-- The loop of `S / R` blocks, from block `S / R - n`. -/
theorem zLoop_ok (hz : ZOk l) {s₀ : State} {a ms bl : Nat → Nat → Nat} (e : EnvZ l s₀ a ms bl) :
    ∀ n s, 1 ≤ n → n ≤ l.S / l.R → InZ l s₀ s a ms bl (l.S / l.R - n) 0 (fun p => bl p (l.R * (l.S / l.R - n) + 0)) →
      BqZ l s bl (l.S / l.R - n) 0 → s.gpr .rcx = BitVec.ofNat 64 n →
      WP isa (.loop (.block (zBlock l)) .ne) s fun s' =>
        InZ l s₀ s' a ms bl (l.S / l.R) 0 (fun p => bl p (l.R * (l.S / l.R) + 0)) ∧ BqZ l s' bl (l.S / l.R) 0 ∧
        (∀ r, r ≠ .rcx → r ≠ .r9 → s'.gpr r = s.gpr r) ∧ s'.mxcsr = s.mxcsr := by
  intro n s h1 h4 hi hq hc
  refine WP.loop (M := isa) (body := .block (zBlock l)) (c := .ne)
    (Q := fun s' => InZ l s₀ s' a ms bl (l.S / l.R) 0 (fun p => bl p (l.R * (l.S / l.R) + 0)) ∧
      BqZ l s' bl (l.S / l.R) 0 ∧ (∀ r, r ≠ .rcx → r ≠ .r9 → s'.gpr r = s.gpr r) ∧ s'.mxcsr = s.mxcsr)
    (fun n (t : State) => 1 ≤ n ∧ n ≤ l.S / l.R ∧
      InZ l s₀ t a ms bl (l.S / l.R - n) 0 (fun p => bl p (l.R * (l.S / l.R - n) + 0)) ∧
      BqZ l t bl (l.S / l.R - n) 0 ∧ t.gpr .rcx = BitVec.ofNat 64 n ∧
      (∀ r, r ≠ .rcx → r ≠ .r9 → t.gpr r = s.gpr r) ∧ t.mxcsr = s.mxcsr) ?_ n s
    ⟨h1, h4, hi, hq, hc, fun _ _ _ => rfl, rfl⟩
  intro n t ⟨h1, h4, hi, hq, hc, hg, hx⟩
  refine WP.mono (zBlock_ok hz (blk := l.S / l.R - n) (by omega) e hi hq (by rw [hc]; congr 1; omega))
    fun t' ⟨hi', hq', hc', hzf, hg', hx'⟩ => ?_
  simp only [eval, hzf, Option.map_some]
  rcases Nat.eq_or_lt_of_le h1 with rfl | hn
  · refine .inl ⟨by simp only [show l.S / l.R - 1 + 1 = l.S / l.R by omega, decide_true, Bool.not_true], ?_, ?_,
      fun r r1 r2 => (hg' r r1 r2).trans (hg r r1 r2), hx'.trans hx⟩
    · rw [show l.S / l.R - 1 + 1 = l.S / l.R by omega] at hi'
      exact hi'
    · rw [show l.S / l.R - 1 + 1 = l.S / l.R by omega] at hq'
      exact hq'
  · refine .inr ⟨by simp only [decide_eq_false (show ¬ (l.S / l.R - n + 1 = l.S / l.R) by omega),
        Bool.not_false], n - 1,
      by omega, by omega, by omega, by rw [show l.S / l.R - (n - 1) = l.S / l.R - n + 1 by omega]; exact hi',
      by rw [show l.S / l.R - (n - 1) = l.S / l.R - n + 1 by omega]; exact hq',
      by rw [hc']; congr 1; omega, fun r r1 r2 => (hg' r r1 r2).trans (hg r r1 r2), hx'.trans hx⟩

/-! ## The start -/

section StartTerms

variable (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay)

/-- The start's vector instructions: all but the first three. -/
def zStartV : List Instr := (zStart l).drop 3

/-- A row of each lane: the 32 bytes at `b + d` and at `b + D + d`. -/
def zLd (b : Reg) (d : Nat) : ZT := .ins (.ldy b d) (.ldy b (l.D + d))

/-- The second operand's first limb, of each lane. -/
def zB0 : ZT := .ins (.bcy .r9 0) (.bcy .r9 (l.D + 0))

/-- The registers after the start. -/
def expStart (r : Nat) : ZT :=
  if r = 0 then .mad false .zero (zB0 l) (zLd l .r8 (32 * 0))
  else if r < 2 * l.R then .zero
  else if r = znBq l 0 then zB0 l
  else if r = znUq l 1 then .zero
  else if r = znK l then .ins (.perm (.lane0 .rax) 0x40) (.perm (.lane0 .rax) 0x40)
  else if r = znT l then .bcy .r9 (l.D + 0)
  else if r = znM l 1 then .perm (zLd l .r10 (l.oMs + 32 * (l.R - 1))) 0x93
  else if znA l 0 ≤ r ∧ r < znA l l.R then zLd l .r8 (32 * (r - znA l 0))
  else if znM l 2 ≤ r ∧ r < znM l (l.R + 2) then zLd l .r10 (l.oMs + 32 * (r - znM l 2))
  else .reg r

/-- The last `u`'s products of rows 0 and 1, added to the second set's role 0. -/
def uFin : ZT :=
  .mad false (.mad true (.reg (znU l 0 (l.S % l.R))) (.reg (znUq l ((l.S - 1) % 2)))
      (.perm (.reg (znM l l.R)) 0x93))
    (.reg (znUq l ((l.S - 1) % 2))) (.reg (znM l 1))

/-- The registers after the end's additions. -/
def expFin (r : Nat) : ZT :=
  if r < l.R then .add (.reg r) (if l.R + r = znU l 0 (l.S % l.R) then uFin l else .reg (l.R + r))
  else if r = znU l 0 (l.S % l.R) then uFin l
  else if r = znT l then .perm (.reg (znM l l.R)) 0x93
  else .reg r

end StartTerms

theorem zStart_run2048 :
    ((ZSym.init.run (limZ lay2048z) (zStartV lay2048z)).map fun σ => (List.range 32).map σ.reg) =
      some ((List.range 32).map (expStart lay2048z)) := by
  kernel_rfl

theorem zFin_run2048 :
    ((ZSym.init.run (limZ lay2048z) (zFin lay2048z)).map fun σ => (List.range 32).map σ.reg) =
      some ((List.range 32).map (expFin lay2048z)) := by
  kernel_rfl

theorem run_zStart (hz : ZOk l) :
    ∃ σ, ZSym.init.run (limZ l) (zStartV l) = some σ ∧ ∀ r < 32, σ.reg r = expStart l r := by
  obtain rfl := hz
  obtain ⟨σ, e, h3⟩ := Option.map_eq_some_iff.1 zStart_run2048
  exact ⟨σ, e, fun r hr => List.map_inj_left.1 h3 r (List.mem_range.2 hr)⟩

theorem run_zFin (hz : ZOk l) :
    ∃ σ, ZSym.init.run (limZ l) (zFin l) = some σ ∧ ∀ r < 32, σ.reg r = expFin l r := by
  obtain rfl := hz
  obtain ⟨σ, e, h3⟩ := Option.map_eq_some_iff.1 zFin_run2048
  exact ⟨σ, e, fun r hr => List.map_inj_left.1 h3 r (List.mem_range.2 hr)⟩

/-- A row's register: quadword `k` is the limb read `8 (k % 4)` bytes into lane `k / 4`'s row. -/
theorem zLd_eval {s : State} {b : Reg} {d : Nat} {f : Nat → Nat → Nat}
    (hf : ∀ p < 2, ∀ t < 4,
      s.mem.readW (s.gpr b + BitVec.ofNat 64 (l.D * p + d + 8 * t)) 64 = BitVec.ofNat 64 (f p t))
    {k : Nat} (hk : k < 8) : (zLd l b d).eval s k = BitVec.ofNat 64 (f (k / 4) (k % 4)) := by
  simp only [zLd, ZT.eval]
  by_cases h4 : k < 4
  · have := hf 0 (by decide) k h4
    rw [Nat.mul_zero, Nat.zero_add] at this
    rw [ite_eq_left h4, ite_eq_left h4, this, show k / 4 = 0 by omega, show k % 4 = k by omega]
  · have := hf 1 (by decide) (k - 4) (by omega)
    rw [Nat.mul_one] at this
    rw [ite_eq_right h4, ite_eq_left (by omega), this, show k / 4 = 1 by omega, show k % 4 = k - 4 by omega]

/-- The first limb's register. -/
theorem zB0_eval {s : State} {g : Nat → Nat}
    (hg : ∀ p < 2, s.mem.readW (s.gpr .r9 + BitVec.ofNat 64 (l.D * p + 0)) 64 = BitVec.ofNat 64 (g p))
    {k : Nat} (hk : k < 8) : (zB0 l).eval s k = BitVec.ofNat 64 (g (k / 4)) := by
  simp only [zB0, ZT.eval]
  by_cases h4 : k < 4
  · have := hg 0 (by decide)
    rw [Nat.mul_zero, Nat.zero_add] at this
    rw [ite_eq_left h4, ite_eq_left h4, this, show k / 4 = 0 by omega]
  · have := hg 1 (by decide)
    rw [Nat.mul_one] at this
    rw [ite_eq_right h4, ite_eq_left (by omega), this, show k / 4 = 1 by omega]

theorem sel4_93 {t : Nat} (ht : t < 4) : sel4 0x93 t = (t + 3) % 4 := by
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl | rfl <;> rfl

theorem sel4_40 {t : Nat} (ht : t < 4) : sel4 0x40 t = if t < 3 then 0 else 1 := by
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl | rfl <;> rfl

/-- A row moved up a quadword within each lane, the last quadword first. -/
theorem zLd_perm {s : State} {b : Reg} {d : Nat} {f : Nat → Nat → Nat}
    (hf : ∀ p < 2, ∀ t < 4,
      s.mem.readW (s.gpr b + BitVec.ofNat 64 (l.D * p + d + 8 * t)) 64 = BitVec.ofNat 64 (f p t))
    {k : Nat} (hk : k < 8) :
    (ZT.perm (zLd l b d) 0x93).eval s k = BitVec.ofNat 64 (f (k / 4) ((k % 4 + 3) % 4)) := by
  simp only [ZT.eval]
  have h4 : (k % 4 + 3) % 4 < 4 := Nat.mod_lt _ (by decide)
  rw [sel4_93 (Nat.mod_lt _ (by decide)), zLd_eval hf (by omega),
    show (4 * (k / 4) + (k % 4 + 3) % 4) / 4 = k / 4 by omega,
    show (4 * (k / 4) + (k % 4 + 3) % 4) % 4 = (k % 4 + 3) % 4 by omega]

/-- The mask's register. -/
theorem zK_eval {s : State} {k : Nat} (hk : k < 8) :
    (ZT.ins (.perm (.lane0 .rax) 0x40) (.perm (.lane0 .rax) 0x40)).eval s k =
      if k % 4 < 3 then s.gpr .rax else 0 := by
  have key : ∀ j < 4, (ZT.perm (.lane0 .rax) 0x40).eval s j = if j < 3 then s.gpr .rax else 0 := fun j hj => by
    simp only [ZT.eval]
    rw [show j / 4 = 0 by omega, Nat.mul_zero, Nat.zero_add, show j % 4 = j by omega, sel4_40 hj]
    by_cases h3 : j < 3
    · rw [ite_eq_left h3, ite_eq_left h3, ite_eq_left rfl]
    · rw [ite_eq_right h3, ite_eq_right h3, ite_eq_right (by decide)]
  rw [ZT.eval]
  by_cases h4 : k < 4
  · rw [ite_eq_left h4, key k h4, show k % 4 = k by omega]
  · rw [ite_eq_right h4, key (k - 4) (by omega), show k % 4 = k - 4 by omega]

section StartRegs

variable (hR : l.R = 6)
include hR

omit hR in
theorem expStart_B0 : expStart l 0 = .mad false .zero (zB0 l) (zLd l .r8 (32 * 0)) := by
  rw [expStart, ite_eq_left rfl]

theorem expStart_zero {r : Nat} (h0 : 0 < r) (h1 : r < 2 * l.R) : expStart l r = .zero := by
  rw [expStart, ite_eq_right (by omega), ite_eq_left h1]

theorem expStart_Bq : expStart l (znBq l 0) = zB0 l := by
  simp (disch := omega) only [expStart, znBq, hR, ↓ite_eq_right, ↓ite_eq_left]

theorem expStart_Uq : expStart l (znUq l 1) = .zero := by
  simp (disch := omega) only [expStart, znBq, znUq, hR, ↓ite_eq_right, ↓ite_eq_left]

theorem expStart_K :
    expStart l (znK l) = .ins (.perm (.lane0 .rax) 0x40) (.perm (.lane0 .rax) 0x40) := by
  simp (disch := omega) only [expStart, znBq, znUq, znK, hR, ↓ite_eq_right, ↓ite_eq_left]

theorem expStart_M1 : expStart l (znM l 1) = .perm (zLd l .r10 (l.oMs + 32 * (l.R - 1))) 0x93 := by
  simp (disch := omega) only [expStart, znBq, znUq, znK, znT, znM, hR, ↓ite_eq_right, ↓ite_eq_left]

theorem expStart_A {kk : Nat} (hkk : kk < 6) : expStart l (znA l kk) = zLd l .r8 (32 * kk) := by
  simp (disch := omega) only [expStart, znBq, znUq, znK, znT, znM, znA, hR, ↓ite_eq_right, ↓ite_eq_left]
  congr 2; omega

theorem expStart_M {kk : Nat} (h1 : 2 ≤ kk) (hkk : kk < 8) :
    expStart l (znM l kk) = zLd l .r10 (l.oMs + 32 * (kk - 2)) := by
  simp (disch := omega) only [expStart, znBq, znUq, znK, znT, znM, znA, hR, ↓ite_eq_right, ↓ite_eq_left]
  congr 3; omega

end StartRegs

theorem off_zero (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : l.off 0 = 0 := by
  unfold Lay.off; rw [Nat.zero_mod, Nat.zero_div]

/-- The start: the two sets zero but the first products of the second
operand's first limb, the operands' rows and the mask in their registers,
and the count of blocks. -/
theorem zStart_ok (hz : ZOk l) {s : State} {a ms bl : Nat → Nat → Nat}
    (e : EnvZ l (s.setReg .r10 (s.gpr .rbx)) a ms bl) :
    WP isa (.block (zStart l)) s fun s' =>
      InZ l (s.setReg .r10 (s.gpr .rbx)) s' a ms bl 0 0 (fun p => bl p (l.R * 0 + 0)) ∧ BqZ l s' bl 0 0 ∧
      s'.gpr .rcx = BitVec.ofNat 64 (l.S / l.R) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.mxcsr = s.mxcsr := by
  have hR := hz.R; have hL := hz.L; have hN := hz.NB
  rw [show zStart l = ([.mov .r10 (.reg .rbx), .mov32 .rcx (.imm (BitVec.ofNat 32 (l.S / l.R))),
    .movImm64 .rax mask52] : List Instr) ++ zStartV l from rfl]
  rw [List.cons_append, WP.block_cons_iff]
  refine ⟨s.setReg .r10 (s.gpr .rbx), rfl, ?_⟩
  rw [List.cons_append, WP.block_cons_iff]
  refine ⟨_, rfl, ?_⟩
  rw [List.cons_append, WP.block_cons_iff]
  refine ⟨_, rfl, ?_⟩
  rw [List.nil_append]
  generalize hs₀ : s.setReg .r10 (s.gpr .rbx) = s₀ at e ⊢
  generalize hs₁ : (s₀.setReg32 .rcx (BitVec.ofNat 32 (l.S / l.R))).setReg .rax mask52 = s₁
  have g₁ : ∀ r, r ≠ .rax → r ≠ .rcx → s₁.gpr r = s₀.gpr r := fun r h1 h2 => by
    rw [← hs₁, RegUpd.gpr_setReg_of_ne _ _ h1, State.setReg32, RegUpd.gpr_setReg_of_ne _ _ h2]
  have ax₁ : s₁.gpr .rax = mask52 := by rw [← hs₁, RegUpd.gpr_setReg_self]
  have cx₁ : s₁.gpr .rcx = BitVec.ofNat 64 (l.S / l.R) := by
    rw [← hs₁, RegUpd.gpr_setReg_of_ne _ _ (by decide), State.setReg32, RegUpd.gpr_setReg_self, hz.blocks]; rfl
  have m₁ : s₁.mem = s₀.mem := by rw [← hs₁]; rfl
  have rd₁ : s₁.rd = s₀.rd := by rw [← hs₁]; rfl
  have wr₁ : s₁.wr = s₀.wr := by rw [← hs₁]; rfl
  have x₁ : s₁.mxcsr = s.mxcsr := by rw [← hs₁, ← hs₀]; rfl
  have r8₁ := g₁ .r8 (by decide) (by decide)
  have r9₁ := g₁ .r9 (by decide) (by decide)
  have r10₁ := g₁ .r10 (by decide) (by decide)
  have hc : Ctx (limZ l) s₁ := by
    intro r d n hn hdn
    rw [rd₁, wr₁]
    by_cases b8 : r = .r8
    · subst b8; rw [r8₁]; exact e.rd8 d n hn hdn
    by_cases b9 : r = .r9
    · subst b9; rw [r9₁]; exact e.rd9 d n hn (by simp only [limZ] at hdn; omega)
    by_cases b10 : r = .r10
    · subst b10; rw [r10₁]; exact e.rd10 d n hn hdn
    · have : limZ l r = 0 := by cases r <;> first | rfl | contradiction
      omega
  -- what the start reads
  have rdA : ∀ kk < 6, ∀ p < 2, ∀ t < 4,
      s₁.mem.readW (s₁.gpr .r8 + BitVec.ofNat 64 (l.D * p + 32 * kk + 8 * t)) 64 =
        BitVec.ofNat 64 (a p (l.R * t + kk)) := fun kk hkk p hp t ht => by
    rw [m₁, r8₁]; exact e.ina p hp kk (by omega) t ht
  have rdM : ∀ kk < 6, ∀ p < 2, ∀ t < 4,
      s₁.mem.readW (s₁.gpr .r10 + BitVec.ofNat 64 (l.D * p + (l.oMs + 32 * kk) + 8 * t)) 64 =
        BitVec.ofNat 64 (ms p (l.R * t + kk + 2)) := fun kk hkk p hp t ht => by
    rw [m₁, r10₁, ← e.inm p hp kk (by omega) t ht]
    exact congrArg (fun d => s₀.mem.readW (s₀.gpr .r10 + BitVec.ofNat 64 d) 64) (by omega)
  have rdB : ∀ p < 2, s₁.mem.readW (s₁.gpr .r9 + BitVec.ofNat 64 (l.D * p + 0)) 64 =
      BitVec.ofNat 64 (bl p 0) := fun p hp => by
    have := e.inb p hp 0 (by omega)
    rw [off_zero] at this
    rw [m₁, r9₁]; exact this
  obtain ⟨σ, er, hσ⟩ := run_zStart hz
  have ev : ∀ (s' : State), ZRel σ s₁ s' → ∀ n < 32, ∀ k < 8, qz s' (vreg n) k = (expStart l n).eval s₁ k :=
    fun s' hs n hn k hk => by rw [hs.reg _ k hk, vi_vreg _ hn, hσ _ hn]
  have hB0 : ∀ k < 8, (zB0 l).eval s₁ k = BitVec.ofNat 64 (bl (k / 4) 0) := fun k hk => zB0_eval rdB hk
  refine WP.mono (zrun_ok hc (ZRel.init s₁) er) fun s' hs => ⟨⟨⟨fun _ => 0, fun kk hkk k hk => ?_,
    fun kk hkk k hk => ?_, fun k hk => ?_, fun p _ => rfl, fun p _ j => ⟨by show (0 : Nat) < _; omega, by show (0 : Nat) < _; omega⟩⟩,
    ⟨fun kk hkk k hk => ?_, fun kk h1 hkk k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩,
    by rw [hs.gpr]; exact r8₁, by rw [hs.gpr, r9₁, Nat.mul_zero]; exact (BitVec.add_zero _).symm,
    by rw [hs.gpr]; exact r10₁, hs.mem.trans m₁, hs.rd.trans rd₁, hs.wr.trans wr₁⟩, fun k hk => ?_,
    by rw [hs.gpr]; exact cx₁, fun r h1 h2 h3 => ?_, hs.mxcsr.trans x₁⟩
  · rw [show zB l kk 0 = vreg (kk % l.R) from rfl, Nat.mod_eq_of_lt hkk, ev s' hs _ (by omega) k hk]
    show _ = BitVec.ofNat 64 (0 + _)
    by_cases h0 : kk = 0
    · subst h0
      rw [expStart_B0, ite_eq_left rfl]
      simp only [ZT.eval]
      rw [hB0 k hk, zLd_eval (rdA 0 (by decide)) hk, show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl, mad_lo',
        Nat.add_zero, Nat.add_zero]
      rfl
    · rw [expStart_zero hR (by omega) (by omega), ite_eq_right h0]; rfl
  · rw [show zU l kk 0 = vreg (l.R + kk % l.R) from rfl, Nat.mod_eq_of_lt hkk, ev s' hs _ (by omega) k hk,
      expStart_zero hR (by omega) (by omega)]; rfl
  · rw [show zUq l ((0 + 1) % 2) = vreg (znUq l 1) from rfl, ev s' hs _ (by simp only [znUq]; omega) k hk,
      expStart_Uq hR]; rfl
  · rw [show zA l kk = vreg (znA l kk) from rfl, ev s' hs _ (by simp only [znA]; omega) k hk,
      expStart_A hR (by omega)]
    exact zLd_eval (rdA kk (by omega)) hk
  · rw [show zM l kk = vreg (znM l kk) from rfl, ev s' hs _ (by simp only [znM]; omega) k hk]
    have hp : k / 4 < 2 := by omega
    rcases Nat.eq_or_lt_of_le h1 with rfl | h2
    · -- row 1: the last row a quadword up, its last quadword, zero, first
      rw [expStart_M1 hR, show l.R - 1 = 5 by omega, zLd_perm (rdM 5 (by decide)) hk]
      congr 1
      show ms (k / 4) (l.R * ((k % 4 + 3) % 4) + 5 + 2) = ms (k / 4) (l.R * (k % 4) + 1)
      rcases Nat.eq_zero_or_pos (k % 4) with h0 | h0
      · rw [show l.R * ((k % 4 + 3) % 4) + 5 + 2 = l.L + 1 by rw [h0, hR, hL],
          show l.R * (k % 4) + 1 = 1 by rw [h0]; rfl, (e.mtop _ hp).2]
        exact ((e.ok _ hp).ms1).symm
      · exact congrArg _ (by rw [hR]; omega)
    · rw [expStart_M hR (by omega) (by omega), zLd_eval (rdM (kk - 2) (by omega)) hk]
      exact congrArg (fun j => BitVec.ofNat 64 (ms (k / 4) j)) (by omega)
  · rw [show zM l l.R = vreg (znM l l.R) from rfl, ev s' hs _ (by simp only [znM]; omega) k hk,
      expStart_M hR (by omega) (by omega), show l.R - 2 = 4 by omega, zLd_eval (rdM 4 (by decide)) hk]
    have hp : k / 4 < 2 := by omega
    congr 1
    show ms (k / 4) (l.R * (k % 4) + 4 + 2) = ms (k / 4) (l.R * ((k % 4 + 1) % 4))
    rcases (by omega : k % 4 = 3 ∨ k % 4 < 3) with h3 | h3
    · rw [show l.R * (k % 4) + 4 + 2 = l.L by rw [h3, hR, hL],
        show l.R * ((k % 4 + 1) % 4) = 0 by rw [h3]; rfl, (e.mtop _ hp).1]
      exact ((e.ok _ hp).ms0).symm
    · exact congrArg _ (by rw [hR]; omega)
  · rw [show zM l (l.R + 1) = vreg (znM l (l.R + 1)) from rfl, ev s' hs _ (by simp only [znM]; omega) k hk,
      expStart_M hR (by omega) (by omega), show l.R + 1 - 2 = 5 by omega, zLd_eval (rdM 5 (by decide)) hk]
    have hp : k / 4 < 2 := by omega
    congr 1
    show ms (k / 4) (l.R * (k % 4) + 5 + 2) = ms (k / 4) (l.R * ((k % 4 + 1) % 4) + 1)
    rcases (by omega : k % 4 = 3 ∨ k % 4 < 3) with h3 | h3
    · rw [show l.R * (k % 4) + 5 + 2 = l.L + 1 by rw [h3, hR, hL],
        show l.R * ((k % 4 + 1) % 4) + 1 = 1 by rw [h3]; rfl, (e.mtop _ hp).2]
      exact ((e.ok _ hp).ms1).symm
    · exact congrArg _ (by rw [hR]; omega)
  · rw [show zK l = vreg (znK l) from rfl, ev s' hs _ (by simp only [znK]; omega) k hk, expStart_K hR,
      zK_eval hk, ax₁]
  · rw [show zBq l (0 % 2) = vreg (znBq l 0) from rfl, ev s' hs _ (by simp only [znBq]; omega) k hk,
      expStart_Bq hR]
    exact hB0 k hk
  · rw [hs.gpr, g₁ r h1 h2, ← hs₀, RegUpd.gpr_setReg_of_ne _ _ h3]

/-! ## The steps after the last block -/

theorem zTail_eq (hz : ZOk l) :
    ((List.range (l.S % l.R)).flatMap fun i => zStep l i (i + 1 = l.S % l.R)) =
      ((List.range 3).flatMap fun i => zStep l i false) ++ zStep l 3 true := by
  obtain rfl := hz
  kernel_rfl

/-- The steps after the last block: the limbs after all `S` steps, in the
roles of step `S % R`. -/
theorem zTail_ok (hz : ZOk l) {s₀ s : State} {a ms bl : Nat → Nat → Nat} (e : EnvZ l s₀ a ms bl)
    (h : InZ l s₀ s a ms bl 3 0 (fun p => bl p (l.R * 3 + 0))) (hq : BqZ l s bl 3 0) :
    WP isa (.block ((List.range (l.S % l.R)).flatMap fun i => zStep l i (i + 1 = l.S % l.R))) s fun s' =>
      InZ l s₀ s' a ms bl 3 4 (fun _ => 0) ∧ s'.gpr = s.gpr ∧ s'.mxcsr = s.mxcsr := by
  have hR := hz.R; have hL := hz.L
  rw [zTail_eq hz, WP.block_append_iff]
  refine WP.mono (zSteps_ok hz e (Nat.le_refl 3) 3 (by omega) (by omega) s h hq) fun s₁ ⟨h₁, q₁, g₁, x₁⟩ => ?_
  obtain ⟨w, acc⟩ := h₁.acc
  have hin : ZIn l s₁ 3 (zo a ms) (fun p => zst l a ms bl p (l.R * 3 + 3)) (fun p => bl p (l.R * 3 + 3)) w
      ((l.R * 3 + 3 + 1) * 2 ^ 56) := ⟨acc, h₁.con, q₁, e.ok, by omega⟩
  refine WP.mono (zStep_ok hz (by omega) hin true (bn := fun _ => 0) (fun h0 => absurd h0 (by decide))
    (fun h0 => absurd h0 (by decide)) (fun _ _ => rfl) (h₁.ctx hz e (Nat.le_refl 3)))
    fun s₂ ⟨acc₂, con₂, _, k₂⟩ => ?_
  have eB : (l.R * 3 + 3 + 1) * 2 ^ 56 + 2 ^ 56 = (l.R * 3 + 4 + 1) * 2 ^ 56 := by omega
  exact ⟨⟨⟨_, eB ▸ acc₂⟩, con₂, by rw [k₂.gpr]; exact h₁.r8, by rw [k₂.gpr]; exact h₁.r9,
    by rw [k₂.gpr]; exact h₁.r10, k₂.mem.trans h₁.mem, k₂.rd.trans h₁.rd, k₂.wr.trans h₁.wr⟩,
    k₂.gpr.trans g₁, k₂.mxcsr.trans x₁⟩

/-! ## The end -/

theorem lo_zr (x : Nat) : lo x 0 = 0 := by unfold lo; rw [Nat.zero_mod, Nat.mul_zero, Nat.zero_mod]

theorem ZOk.tail (hz : ZOk l) : l.S % l.R = 4 ∧ (l.S - 1) % 2 = 1 ∧ l.S = l.R * 3 + 4 := by
  rw [hz]; exact ⟨rfl, rfl, rfl⟩

/-- The end's additions: the limbs the two sets stand for, in the first
set's registers. -/
theorem zFin_ok (hz : ZOk l) {s₀ s : State} {a ms bl : Nat → Nat → Nat} (e : EnvZ l s₀ a ms bl)
    (h : InZ l s₀ s a ms bl 3 4 (fun _ => 0)) :
    WP isa (.block (zFin l)) s fun s' =>
      (∀ kk < l.R, ∀ k < 8, qz s' (zB l kk (l.S % l.R)) k =
        BitVec.ofNat 64 (zlm l a ms bl (k / 4) (l.R * (k % 4) + kk))) ∧ ZKeep s s' := by
  have hR := hz.R; have hL := hz.L
  obtain ⟨hS4, hS2, hS⟩ := hz.tail
  obtain ⟨σ, er, hσ⟩ := run_zFin hz
  obtain ⟨w, acc⟩ := h.acc
  have hT : ∀ k < 8, qz s (vreg (znM l l.R)) (4 * (k / 4) + sel4 0x93 (k % 4)) =
      BitVec.ofNat 64 ((zo a ms (k / 4)).ms (l.R * (k % 4))) := fun k hk => by
    have h4 : (k % 4 + 3) % 4 < 4 := Nat.mod_lt _ (by decide)
    rw [sel4_93 (Nat.mod_lt _ (by decide)),
      show qz s (vreg (znM l l.R)) _ = _ from h.con.m0 (4 * (k / 4) + (k % 4 + 3) % 4) (by omega),
      show (4 * (k / 4) + (k % 4 + 3) % 4) / 4 = k / 4 by omega,
      show ((4 * (k / 4) + (k % 4 + 3) % 4) % 4 + 1) % 4 = k % 4 by omega]
  refine WP.mono (zrun_ok (h.ctx hz e (Nat.le_refl 3)) (ZRel.init s) er) fun s' hs => ⟨fun kk hkk k hk => ?_, hs.keep⟩
  have hp : k / 4 < 2 := by omega
  have hm6 : (kk + 4) % l.R < 6 := by rw [hR]; exact Nat.mod_lt _ (by decide)
  have hb : qz s (vreg ((kk + 4) % l.R)) k = _ := acc.bs kk hkk k hk
  have hu : qz s (vreg (l.R + (kk + 4) % l.R)) k = _ := acc.us kk hkk k hk
  rw [hS4, show zB l kk 4 = vreg ((kk + 4) % l.R) from rfl, hs.reg _ k hk, vi_vreg _ (by omega),
    hσ _ (by omega), expFin, ite_eq_left (by omega)]
  simp only [zlm, AmmD52.tot, pend]
  by_cases h0 : kk = 0
  · subst h0
    have hUp : qz s (vreg (znUq l 1)) k = _ := acc.up k hk
    have hM1 : qz s (vreg (znM l 1)) k = _ := h.con.m 1 (by decide) (by omega) k hk
    rw [ite_eq_left (by simp only [znU, hS4]), uFin, hS4, hS2]
    simp only [ZT.eval]
    have hwq : w (k / 4) % 2 ^ 52 = (zst l a ms bl (k / 4) l.S).qp := by rw [hS]; exact acc.wq _ hp
    rw [hb, show znU l 0 4 = l.R + (0 + 4) % l.R from rfl, hu, hUp, hT k hk, hM1,
      ite_eq_left rfl, lo_zr, mad_hi', mad_lo', ← BitVec.ofNat_add, ite_eq_left (by rw [hR]; omega), ← hS,
      ← hwq, hi_modr, lo_modr]
    congr 1
    simp only [zo, Nat.add_zero]
    omega
  · rw [ite_eq_right (by simp only [znU, hR]; omega)]
    simp only [ZT.eval]
    rw [hb, hu, ite_eq_right h0, ← BitVec.ofNat_add, ite_eq_right (by rw [hR]; omega), ← hS]
    congr 1

/-! ## The stores -/

/-- 32-byte stores of each register's halves, the low one at `r11` plus an
offset and the high one `D` further. -/
def zStoreCode (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (xs : List (Nat × VReg)) : List Instr :=
  xs.flatMap fun x => [.evStore (at_ .r11 x.1) x.2, .e5ExtractStore (at_ .r11 (l.D + x.1)) x.2 1]

/-- What they write. -/
def zStoreList (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (s : State) (xs : List (Nat × VReg)) :
    List (Nat × BitVec 256) :=
  xs.flatMap fun x => [(x.1, s.vy x.2), (l.D + x.1, s.vz x.2 3 ++ s.vz x.2 2)]

theorem zStores_gen {B : Addr} :
    ∀ (xs : List (Nat × VReg)) (s : State), s.gpr .r11 = B →
      (∀ x ∈ xs, InRegions s.wr (off B x.1) 32 ∧ InRegions s.wr (off B (l.D + x.1)) 32) →
      WP isa (.block (zStoreCode l xs)) s fun s' =>
        s' = { s with mem := AmmSym.wrList s.mem B (zStoreList l s xs) }
  | [], s, _, _ => WP.block_nil rfl
  | (d, r) :: rest, s, hB, hw => by
    obtain ⟨w1, w2⟩ := hw (d, r) (List.mem_cons_self ..)
    rw [zStoreCode, List.flatMap_cons, List.cons_append, List.cons_append, List.nil_append, WP.block_cons_iff]
    refine ⟨{ s with mem := s.mem.writeW (off B d) (s.vy r) }, ?_, ?_⟩
    · simp only [exec, eaG hB, State.store256, w1, ite_true]
    rw [WP.block_cons_iff]
    refine ⟨{ s with mem := (s.mem.writeW (off B d) (s.vy r)).writeW (off B (l.D + d)) (s.vz r 3 ++ s.vz r 2) }, ?_, ?_⟩
    · have hB' : ({ s with mem := s.mem.writeW (off B d) (s.vy r) } : State).gpr .r11 = B := hB
      simp only [exec, eaG hB', State.store256]
      rw [ite_eq_left (show InRegions s.wr (off B (l.D + d)) 32 from w2)]
      rfl
    · refine WP.mono (zStores_gen rest _ hB fun x hx => hw x (List.mem_cons_of_mem _ hx)) fun s' h => ?_
      rw [h]
      rfl

/-- The high half's quadwords. -/
theorem qz_hi (s : State) (r : VReg) {t : Nat} (ht : t < 4) :
    (s.vz r 3 ++ s.vz r 2).extractLsb' (64 * t) 64 = qz s r (4 + t) := by
  show qword256 _ t = _
  rw [qword256_cat2 _ _ ht, qz, show (4 + t) % 2 = t % 2 by omega]
  by_cases h2 : t < 2
  · rw [ite_eq_left h2, show (4 + t) / 2 = 2 by omega]
  · rw [ite_eq_right h2, show (4 + t) / 2 = 3 by omega]

/-! ## The whole multiplication -/

theorem ZOk.amm (hz : ZOk l) : AmmOk l := .inl (.inr (.inr (.inr hz)))

theorem ZOk.nl (hz : ZOk l) : l.nl = 2 := by rw [hz]; rfl

/-- The registers the end stores. -/
def zSt (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : List (Nat × VReg) :=
  (List.range l.R).map fun k => (32 * k, zB l k (l.S % l.R))

theorem zStores_code : zStores l = zStoreCode l (zSt l) := by
  simp only [zStores, zStoreCode, zSt, List.flatMap_map]

theorem mem_zStoreList {s : State} {x : Nat × BitVec 256} (hx : x ∈ zStoreList l s (zSt l)) :
    ∃ k < l.R, x = (32 * k, s.vy (zB l k (l.S % l.R))) ∨
      x = (l.D + 32 * k, s.vz (zB l k (l.S % l.R)) 3 ++ s.vz (zB l k (l.S % l.R)) 2) := by
  simp only [zStoreList, zSt, List.flatMap_map, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  obtain ⟨k, hk, h⟩ := hx
  exact ⟨k, hk, h⟩

/-- The limbs stay below `2⁶³`. -/
theorem zlm_lt (hz : ZOk l) (a ms bl : Nat → Nat → Nat) (p q : Nat) : zlm l a ms bl p q < 2 ^ 63 := by
  have hS := hz.S
  obtain ⟨h1, h2⟩ := AmmD52.steps_lt (N := l.L) (R := l.R) (o := zo a ms p) (b := bl p)
    (s := ⟨fun _ => 0, fun _ => 0, 0⟩) (fun _ => by show (0 : Nat) < _; decide)
    (fun _ => by show (0 : Nat) < _; decide) l.S (by omega)
  unfold zlm AmmD52.tot pend zst
  generalize AmmD52.steps l.L l.R (zo a ms p) (bl p) l.S ⟨fun _ => 0, fun _ => 0, 0⟩ = st at h1 h2 ⊢
  have := h1 q; have := h2 q
  have := hi_lt ((zo a ms p).ms q) st.qp
  have := lo_lt ((zo a ms p).ms (q + 1)) st.qp
  split <;> omega

/-- `ammCoreZ` from the operands `a` (at `r8`), `bl` (at `r9`) and the
modulus plus one `ms` (at `rbx + oMs`), into limbs at `r11 = B`: each lane's
limbs of `AmmD52.tot` after `S` steps, carried. -/
theorem ammCoreZ_ok (hz : ZOk l) {s : State} {B : Addr} {a ms bl : Nat → Nat → Nat}
    (e : EnvZ l (s.setReg .r10 (s.gpr .rbx)) a ms bl) (hB : s.gpr .r11 = B)
    (hs : Scr s B (l.D * (l.nl - 1) + l.NB)) :
    WP isa (ammCoreZ l) s fun s' =>
      (∀ p < l.nl, ∀ q < l.L, word s'.mem B (l.D * p + l.off q) =
        BitVec.ofNat 64 (carried (zlm l a ms bl p) q)) ∧
      OutN l B 0 l.NB s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r9 → r ≠ .r10 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.gpr .r12 = mask52 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  have hR := hz.R; have hL := hz.L; have hN := hz.NB; have h3 := hz.blocks; have hnl := hz.nl
  have hl := hz.amm
  have hD := hl.D_bounds
  obtain ⟨hS4, _, _⟩ := hz.tail
  refine WP.seq (WP.mono (zStart_ok hz e) fun s₁ ⟨i₁, q₁, cx₁, g₁, x₁⟩ => ?_)
  refine WP.seq (WP.mono (zLoop_ok hz e (l.S / l.R) s₁ (by omega) (Nat.le_refl _)
    (by rw [Nat.sub_self]; exact i₁) (by rw [Nat.sub_self]; exact q₁) cx₁) fun s₂ ⟨i₂, q₂, g₂, x₂⟩ => ?_)
  rw [h3] at i₂ q₂
  rw [zStores_code, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (zTail_ok hz e i₂ q₂) fun s₃ ⟨i₃, g₃, x₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (zFin_ok hz e i₃) fun s₄ ⟨v₄, k₄⟩ => ?_
  have m₄ : s₄.mem = s.mem := k₄.mem.trans i₃.mem
  have wr₄ : s₄.wr = s.wr := k₄.wr.trans i₃.wr
  have rd₄ : s₄.rd = s.rd := k₄.rd.trans i₃.rd
  have g₄ : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r9 → r ≠ .r10 → s₄.gpr r = s.gpr r := fun r r1 r2 r3 r4 => by
    rw [k₄.gpr, g₃, g₂ r r2 r3, g₁ r r1 r2 r4]
  have hB₄ : s₄.gpr .r11 = B := (g₄ _ (by decide) (by decide) (by decide) (by decide)).trans hB
  have hreg : ∀ d, d + 32 ≤ l.D + l.NB → InRegions s₄.wr (off B d) 32 := fun d hd => by
    rw [wr₄]
    obtain ⟨_, h, c⟩ := hs.region (d := d) (n := 32) (by rw [hnl]; omega) (by decide)
    exact ⟨_, h, c⟩
  rw [WP.block_append_iff]
  refine WP.mono (zStores_gen (zSt l) s₄ hB₄ fun x hx => by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    have := List.mem_range.1 hk
    exact ⟨hreg _ (by omega), hreg _ (by omega)⟩) fun s₅ h₅ => ?_
  subst h₅
  rw [List.singleton_append, WP.block_cons_iff]
  refine ⟨_, rfl, ?_⟩
  -- the words stored
  have hwords : ∀ p < l.nl, ∀ q < l.L, word (AmmSym.wrList s₄.mem B (zStoreList l s₄ (zSt l))) B (l.D * p + l.off q) =
      BitVec.ofNat 64 (zlm l a ms bl p q) := fun p hp q hq => by
    obtain ⟨kk, t, hk, ht, rfl⟩ : ∃ kk t, kk < l.R ∧ t < 4 ∧ q = l.R * t + kk :=
      ⟨q % l.R, q / l.R, Nat.mod_lt _ (by omega), Nat.div_lt_of_lt_mul (by omega), (Nat.div_add_mod q l.R).symm⟩
    have hsep : ∀ x ∈ zStoreList l s₄ (zSt l), ∀ e', (e' = 32 * kk ∨ e' = l.D + 32 * kk) →
        x.1 + 32 ≤ 2 ^ 63 ∧ (x.1 = e' ∨ e' + 32 ≤ x.1 ∨ x.1 + 32 ≤ e') := fun x hx e' he' => by
      obtain ⟨k', hk', rfl | rfl⟩ := mem_zStoreList hx <;> rcases he' with rfl | rfl <;> omega
    rw [off_blk (by omega) hk]
    rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl
    · rw [show l.D * 0 + (32 * kk + 8 * t) = 32 * kk + 8 * t by omega]
      rw [AmmSym.word_wrList_unique B ht (by omega) _ s₄.mem
        (v := s₄.vy (zB l kk (l.S % l.R))) ?_ (fun x hx => hsep x hx _ (.inl rfl)) (fun x hx he => ?_)]
      · show qv s₄ _ _ = _
        rw [← qz_lo s₄ _ ht, v₄ _ hk _ (by omega), show t / 4 = 0 by omega, show t % 4 = t by omega]
      · simp only [zStoreList, zSt, List.flatMap_map, List.mem_flatMap, List.mem_range, List.mem_cons,
          List.not_mem_nil, or_false]
        exact ⟨kk, hk, .inl rfl⟩
      · obtain ⟨k', hk', rfl | rfl⟩ := mem_zStoreList hx
        · have : k' = kk := by simp only at he; omega
          rw [this]
        · simp only at he; omega
    · rw [show l.D * 1 + (32 * kk + 8 * t) = l.D + 32 * kk + 8 * t by omega]
      rw [AmmSym.word_wrList_unique B ht (by omega) _ s₄.mem
        (v := s₄.vz (zB l kk (l.S % l.R)) 3 ++ s₄.vz (zB l kk (l.S % l.R)) 2) ?_
        (fun x hx => hsep x hx _ (.inr rfl)) (fun x hx he => ?_)]
      · rw [qz_hi s₄ _ ht, v₄ _ hk _ (by omega), show (4 + t) / 4 = 1 by omega, show (4 + t) % 4 = t by omega]
      · simp only [zStoreList, zSt, List.flatMap_map, List.mem_flatMap, List.mem_range, List.mem_cons,
          List.not_mem_nil, or_false]
        exact ⟨kk, hk, .inr rfl⟩
      · obtain ⟨k', hk', rfl | rfl⟩ := mem_zStoreList hx
        · simp only at he; omega
        · have : k' = kk := by simp only at he; omega
          rw [this]
  refine WP.mono (carryOut_ok hl (B := B) (L := fun p => zlm l a ms bl p) (fun p _ q _ => zlm_lt hz a ms bl p q)
    (fun d hd => by rw [RegUpd.wr_setReg]; show InRegions s₄.wr _ _; rw [wr₄]; exact hs.st hd)
    (by rw [RegUpd.gpr_setReg_of_ne _ _ (by decide)]; exact hB₄)
    (RegUpd.gpr_setReg_self _ _ _) fun p hp q hq => by rw [RegUpd.mem_setReg]; exact hwords p hp q hq)
    fun s' ⟨h, g, rd, wr, x⟩ => ?_
  refine ⟨fun p hp q hq => by rw [h.words p hp q hq]; simp only [hq, true_or, ite_true], ?_,
    fun r r1 r2 r3 r4 r5 r6 r7 => ?_,
    by rw [g _ (by decide) (by decide) (by decide) (by decide)]; exact RegUpd.gpr_setReg_self _ _ _,
    by rw [rd, RegUpd.rd_setReg]; exact rd₄, by rw [wr, RegUpd.wr_setReg]; exact wr₄,
    by rw [x, RegUpd.mxcsr_setReg]; show s₄.mxcsr = _; rw [k₄.mxcsr, x₃, x₂, x₁]⟩
  · have o := wrList_outN (l := l) B (o := 0) (n := l.NB) (by rw [hnl]; omega)
      (zStoreList l s₄ (zSt l)) s₄.mem fun x hx => by
        obtain ⟨k', hk', rfl | rfl⟩ := mem_zStoreList hx
        · exact ⟨0, by omega, by omega, by omega⟩
        · exact ⟨1, by omega, by omega, by omega⟩
    have hf : OutN l B 0 l.NB (AmmSym.wrList s₄.mem B (zStoreList l s₄ (zSt l))) s'.mem := h.frame
    have o' : OutN l B 0 l.NB s.mem (AmmSym.wrList s₄.mem B (zStoreList l s₄ (zSt l))) :=
      fun x hx => (o x hx).trans (congrFun m₄ x)
    exact o'.trans hf
  · rw [g r r1 r2 r3 r4, RegUpd.gpr_setReg_of_ne _ _ r7]
    exact g₄ r r1 r2 r5 r6

/-! ## The multiplication's values -/

theorem hi_zr (x : Nat) : hi x 0 = 0 := by unfold hi; rw [Nat.zero_mod, Nat.mul_zero, Nat.zero_div]

/-- The limbs before the first step are zero. -/
theorem tot_init (R : Nat) (o : Ops) (j : Nat) : AmmD52.tot R o ⟨fun _ => 0, fun _ => 0, 0⟩ j = 0 := by
  simp only [AmmD52.tot, pend, lo_zr, hi_zr, Nat.add_zero, ite_self]

theorem ZOk.offs (hz : ZOk l) : l.oMs + l.NB ≤ l.D ∧ l.D + l.NB ≤ 2 ^ 20 ∧ l.NB ≤ l.D := by
  rw [hz]; decide

/-- A number's limbs two limbs up. -/
theorem lval_up2 {f g : Nat → Nat} (g0 : g 0 = 0) (g1 : g 1 = 0) (hg : ∀ j, g (j + 2) = f j) :
    ∀ n, lval g (n + 2) = 2 ^ 104 * lval f n
  | 0 => by
    rw [show (0 : Nat) + 2 = 0 + 1 + 1 from rfl, VG.Proof.Bignum.Amm52.lval_succ, VG.Proof.Bignum.Amm52.lval_succ]
    simp only [Nat.zero_add, VG.Proof.Bignum.Amm52.lval_zero, g0, g1, Nat.zero_mul, Nat.mul_zero]
  | n + 1 => by
    rw [show n + 1 + 2 = (n + 2) + 1 from rfl, VG.Proof.Bignum.Amm52.lval_succ, lval_up2 g0 g1 hg n,
      VG.Proof.Bignum.Amm52.lval_succ, hg, show 52 * (n + 2) = 52 * n + 52 * 2 by omega, Nat.pow_add,
      Nat.mul_add (2 ^ 104)]
    congr 1
    rw [← Nat.mul_assoc, Nat.mul_comm]

/-- Two zero limbs at the top. -/
theorem lval_top2 {f : Nat → Nat} {n : Nat} (t1 : f n = 0) (t2 : f (n + 1) = 0) : lval f (n + 2) = lval f n := by
  rw [show n + 2 = n + 1 + 1 from rfl, VG.Proof.Bignum.Amm52.lval_succ, VG.Proof.Bignum.Amm52.lval_succ, t1, t2]
  simp only [Nat.zero_mul, Nat.add_zero]

/-- `ammCoreZ` with `r8`, `r9`, `r11` at offsets `a`, `b`, `o` of `B = rbx`:
for a modulus `X` with `X + 1` the number at `oMs` times `2¹⁰⁴` (its last two
limbs zero), a second operand below `2^(52 S)` and a product that fits, the
result times `2^(52 S)` is the product plus a multiple `X Q` of the modulus,
with `Q < 2^(52 S)`. -/
theorem ammCoreZSpec_ok (hz : ZOk l) {s : State} {B : Addr} {o a b : Nat}
    (hB : s.gpr .rbx = B) (r8₃ : s.gpr .r8 = off B a) (r9₃ : s.gpr .r9 = off B b) (r11₃ : s.gpr .r11 = off B o)
    (hs : Scr s B (l.nl * l.D)) (ho : o + l.NB ≤ l.D) (ha : a + l.NB ≤ l.D) (hb : b + l.NB ≤ l.D)
    (hlt : ∀ p < l.nl, ∀ j < l.L, limb l s.mem B (l.D * p + a) j < 2 ^ 52 ∧
      limb l s.mem B (l.D * p + b) j < 2 ^ 52 ∧ limb l s.mem B (l.D * p + l.oMs) j < 2 ^ 52)
    (hmt : ∀ p < l.nl, limb l s.mem B (l.D * p + l.oMs) (l.L - 2) = 0 ∧
      limb l s.mem B (l.D * p + l.oMs) (l.L - 1) = 0) :
    WP isa (ammCoreZ l) s fun s' => (∀ p < l.nl,
      (∀ j < l.L, limb l s'.mem B (l.D * p + o) j < 2 ^ 52) ∧
      (∀ X, 2 ^ 104 * val52 l s.mem B (l.D * p + l.oMs) = X + 1 → val52 l s.mem B (l.D * p + b) < 2 ^ (52 * l.S) →
        val52 l s.mem B (l.D * p + a) * val52 l s.mem B (l.D * p + b) + X * 2 ^ (52 * l.S) <
          2 ^ (52 * l.S) * 2 ^ (52 * l.L) →
        ∃ Q, Q < 2 ^ (52 * l.S) ∧ val52 l s'.mem B (l.D * p + o) * 2 ^ (52 * l.S) =
          val52 l s.mem B (l.D * p + a) * val52 l s.mem B (l.D * p + b) + X * Q)) ∧
      Out2 l B o l.NB s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r9 → r ≠ .r10 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  have hR := hz.R; have hL := hz.L; have hN := hz.NB; have hnl := hz.nl; have hS := hz.S
  obtain ⟨hD1, hD2, hD3⟩ := hz.offs
  let A : Nat → Nat → Nat := fun p => limb l s.mem B (l.D * p + a)
  let Bl : Nat → Nat → Nat := fun p => limb l s.mem B (l.D * p + b)
  let Mh : Nat → Nat → Nat := fun p => limb l s.mem B (l.D * p + l.oMs)
  let M : Nat → Nat → Nat := fun p j => if j < 2 then 0 else Mh p (j - 2)
  have hDp : ∀ p < 2, l.D * p ≤ l.D := fun p hp => by
    rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl <;> omega
  have rdS : ∀ d n, 0 < n → d + n ≤ l.nl * l.D → InRegions (s.rd ++ s.wr) (off B d) n := fun d n hn hd =>
    let ⟨_, h, c⟩ := hs.region hd hn; ⟨_, List.mem_append_right _ h, c⟩
  have e : EnvZ l (s.setReg .r10 (s.gpr .rbx)) A M Bl := by
    refine ⟨fun p hp kk hk t ht => ?_, fun p hp kk hk t ht => ?_,
      fun p hp => ⟨by show (if l.L < 2 then 0 else Mh p (l.L - 2)) = 0
                      rw [ite_eq_right (by omega)]; exact (hmt p (by omega)).1,
        by show (if l.L + 1 < 2 then 0 else Mh p (l.L + 1 - 2)) = 0
           rw [ite_eq_right (by omega), show l.L + 1 - 2 = l.L - 1 by omega]; exact (hmt p (by omega)).2⟩,
      fun p hp q hq => ?_,
      fun p hp => ⟨fun j hj => (hlt p (by omega) j hj).1, fun j hj => ?_, rfl, rfl⟩,
      fun p hp q hq => (hlt p (by omega) q hq).2.1,
      fun d n hn hd => ?_, fun d n hn hd => ?_, fun d n hn hd => ?_⟩
    · have := hDp p hp
      rw [RegUpd.mem_setReg, RegUpd.gpr_setReg_of_ne _ _ (by decide), r8₃, off_add]
      show _ = BitVec.ofNat 64 (limb l s.mem B (l.D * p + a) (l.R * t + kk))
      rw [ofNat_toNat64, off_blk (by omega) hk]
      exact congrArg (fun d => s.mem.readW (off B d) 64) (by omega)
    · have := hDp p hp
      rw [RegUpd.mem_setReg, RegUpd.gpr_setReg_self, hB]
      show s.mem.readW (off B _) 64 =
        BitVec.ofNat 64 (if l.R * t + kk + 2 < 2 then 0 else limb l s.mem B (l.D * p + l.oMs) (l.R * t + kk + 2 - 2))
      rw [ite_eq_right (by omega), Nat.add_sub_cancel, ofNat_toNat64, off_blk (by omega) hk]
      exact congrArg (fun d => s.mem.readW (off B d) 64) (by omega)
    · rw [RegUpd.mem_setReg, RegUpd.gpr_setReg_of_ne _ _ (by decide), r9₃, off_add]
      show _ = BitVec.ofNat 64 (limb l s.mem B (l.D * p + b) q)
      rw [ofNat_toNat64]
      exact congrArg (fun d => s.mem.readW (off B d) 64) (by omega)
    · show (if j < 2 then 0 else Mh p (j - 2)) < 2 ^ 52
      split
      · decide
      · exact (hlt p (by omega) (j - 2) (by omega)).2.2
    · rw [RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_setReg_of_ne _ _ (by decide), r8₃, off_add]
      exact rdS _ n hn (by rw [hnl]; omega)
    · rw [RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_setReg_of_ne _ _ (by decide), r9₃, off_add]
      exact rdS _ n hn (by rw [hnl]; omega)
    · rw [RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_setReg_self, hB]
      exact rdS _ n hn (by rw [hnl]; omega)
  have hs₃ : Scr s (off B o) (l.D * (l.nl - 1) + l.NB) := hs.sub (by rw [hnl]; omega) (by omega)
  refine WP.mono (ammCoreZ_ok hz e r11₃ hs₃) fun s' ⟨hw, hf, hg, _, hrd, hwr, hx⟩ => ?_
  refine ⟨fun p hp => ?_, (hf.rebaseN (by rw [hnl]; omega)).out2, hg, hrd, hwr, hx⟩
  have hp2 : p < 2 := by omega
  have hq : ∀ j < l.L, limb l s'.mem B (l.D * p + o) j = carried (zlm l A M Bl p) j := fun j hj => by
    have := hw p hp j hj
    simp only [word, VG.Proof.Bignum.off_off] at this
    show (s'.mem.readW (off B _) 64).toNat = _
    rw [show l.D * p + o + l.off j = o + (l.D * p + l.off j) by omega, this, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := carried_lt (zlm l A M Bl p) j; omega)]
  have hv : val52 l s'.mem B (l.D * p + o) = lval (carried (zlm l A M Bl p)) l.L := by
    unfold val52; exact lval_congr hq
  refine ⟨fun j hj => (hq j hj) ▸ carried_lt _ j, fun X hX hBv hfit => ?_⟩
  -- the modulus plus one is the number at `oMs`, two limbs up
  have hMv : lval (M p) l.L = X + 1 := by
    have h1 := lval_up2 (f := Mh p) (g := M p) rfl rfl (fun j => by
      show (if j + 2 < 2 then 0 else Mh p (j + 2 - 2)) = Mh p j
      rw [ite_eq_right (by omega), Nat.add_sub_cancel]) (l.L - 2)
    have h2 := lval_top2 (f := Mh p) (n := l.L - 2) (hmt p hp).1
      (by rw [show l.L - 2 + 1 = l.L - 1 by omega]; exact (hmt p hp).2)
    rw [show l.L - 2 + 2 = l.L by omega] at h1 h2
    exact h1.trans (by rw [← h2]; exact hX)
  have he := AmmD52.steps_val (R := l.R) (N := l.L) (by omega) (by omega) (by rw [hL, hR]) (e.ok p hp2)
    (b := Bl p) (fun i hi => (hlt p hp i hi).2.1) ⟨fun _ => 0, fun _ => 0, 0⟩ hMv l.S (by omega)
  have z : lval (AmmD52.tot l.R ⟨A p, M p⟩ ⟨fun _ => 0, fun _ => 0, 0⟩) l.L = 0 := by
    rw [lval_congr (L' := fun j => (fun _ : Nat => 0) j * 0) fun j _ => tot_init l.R _ j,
      VG.Proof.Bignum.Amm52.lval_mul, Nat.mul_zero]
  have hQ : lval (AmmD52.stepsQ l.L l.R ⟨A p, M p⟩ (Bl p) ⟨fun _ => 0, fun _ => 0, 0⟩) l.S < 2 ^ (52 * l.S) :=
    lval_lt fun j _ => AmmD52.stepsQ_lt _ _ _ _ _ _
  rw [z, Nat.zero_add] at he
  have hbS : lval (Bl p) l.L = lval (Bl p) l.S := lval_trunc _ (by omega) hBv
  change lval (zlm l A M Bl p) l.L * _ = lval (A p) l.L * lval (Bl p) l.S + X * _ at he
  change lval (A p) l.L * lval (Bl p) l.L + X * _ < _ at hfit
  rw [hbS] at hfit
  generalize lval (AmmD52.stepsQ l.L l.R ⟨A p, M p⟩ (Bl p) ⟨fun _ => 0, fun _ => 0, 0⟩) l.S = Q at he hQ
  have hz' : lval (zlm l A M Bl p) l.L < 2 ^ (52 * l.L) := by
    have h1 : X * Q ≤ X * 2 ^ (52 * l.S) := Nat.mul_le_mul_left _ (Nat.le_of_lt hQ)
    refine Nat.lt_of_mul_lt_mul_left (a := 2 ^ (52 * l.S)) ?_
    rw [Nat.mul_comm]
    generalize 2 ^ (52 * l.S) * 2 ^ (52 * l.L) = T at hfit ⊢
    omega
  have hcv := carried_val (zlm l A M Bl p) l.L
  rw [Amm52N.carryIn_zero hz', Nat.zero_mul, Nat.add_zero] at hcv
  refine ⟨Q, hQ, ?_⟩
  rw [hv, hcv]
  show lval (zlm l A M Bl p) l.L * _ = lval (A p) l.L * lval (Bl p) l.L + X * Q
  rw [hbS]; exact he

end VG.Proof.Bignum.X86_64.Ifma
