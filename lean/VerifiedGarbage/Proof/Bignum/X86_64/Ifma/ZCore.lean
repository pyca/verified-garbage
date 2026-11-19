module

public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.ZStep
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.StepU
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Block

/-! ### `Bignum.X86_64.Ifma.CoreU`, which this module and modules that import it used -/

section

/-! ### `Bignum.X86_64.Ifma.Core`, which this module and modules that import it used -/

section

/-!
# RSA with AVX512_IFMA on x86-64, any size: the multiplication's loop

The zeroing of the accumulators and the zero
register (`zeros_ok`), and the loop of `S / R` blocks from `InBlk` for block
`S / R - n` to `InBlk` for block `S / R`: the lanes after `R (S / R)` steps (`loop_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64
open VG.Impl.Rsa.X86_64.CrtIfma
open VG.Proof.Bignum.X86_64.AmmSym (Keeps)

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-- The zeroing of the accumulators and the zero register. -/
def zeros (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : List Instr :=
  (List.range (l.nl * l.R + 2 * l.nl + 1)).map fun r => .eop (.bin .vpxorq (vreg r) (vreg r) (vreg r))

def checkZeros (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : Bool :=
  match ESym.init.run (fun _ => 0) (zeros l) with
  | some σ => (List.range (l.nl * l.R + 2 * l.nl + 1)).all fun r => decide (σ.reg r = .zero)
  | none => false

theorem checkZeros_ok (hl : AmmOk l) : checkZeros l = true := by
  rcases hl with (rfl | rfl | rfl | rfl) | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem zeros_ok (hl : AmmOk l) {s : State} :
    WP isa (.block (zeros l)) s fun s' => (∀ r < l.nl * l.R + 2 * l.nl + 1, ∀ t < 4, qv s' (vreg r) t = 0) ∧ Keeps s s' := by
  obtain ⟨_, hrg⟩ := hl.regs
  have h := checkZeros_ok hl
  unfold checkZeros at h
  split at h
  · rename_i σ hσ
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
    refine WP.mono (run_ok (fun b d n hn hd => absurd hd (by omega_using [hn])) (SRel.init s) hσ) fun s' hs =>
      ⟨fun r hr t ht => ?_, ⟨fun r hr => hs.gpr hr, hs.mem, hs.rd, hs.wr, hs.mxcsr, hs.flags⟩⟩
    rw [hs.reg _ t ht, vi_vreg r (by omega_using [hr, hrg]), h r hr]; rfl
  · cases h

/-- The loop of `S / R` blocks, from block `S / R - n`. -/
theorem loop_ok (hl : AmmOk l) {s₀ : State} {a m : Nat → Nat → Nat} {k : Nat → Nat} {bl : Nat → Nat → Nat}
    (e : Env l s₀ a m k bl) :
    ∀ n s, 1 ≤ n → n ≤ l.S / l.R → InBlk l s₀ s a m k bl (l.S / l.R - n) 0 → s.gpr .rcx = BitVec.ofNat 64 n →
      WP isa (.loop (.block (ammBlock l)) .ne) s fun s' =>
        InBlk l s₀ s' a m k bl (l.S / l.R) 0 ∧ (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r9 → s'.gpr r = s.gpr r) ∧
        s'.mxcsr = s.mxcsr := by
  intro n s h1 h4 hi hc
  refine WP.loop (M := isa) (body := .block (ammBlock l)) (c := .ne)
    (Q := fun s' => InBlk l s₀ s' a m k bl (l.S / l.R) 0 ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r9 → s'.gpr r = s.gpr r) ∧ s'.mxcsr = s.mxcsr)
    (fun n (t : State) => 1 ≤ n ∧ n ≤ l.S / l.R ∧ InBlk l s₀ t a m k bl (l.S / l.R - n) 0 ∧
      t.gpr .rcx = BitVec.ofNat 64 n ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r9 → t.gpr r = s.gpr r) ∧ t.mxcsr = s.mxcsr) ?_ n s
    ⟨h1, h4, hi, hc, fun _ _ _ _ => rfl, rfl⟩
  intro n t ⟨h1, h4, hi, hc, hg, hx⟩
  refine WP.mono (ammBlock_ok hl (blk := l.S / l.R - n) (by omega_using [h1, h4]) e hi (by rw [hc]; congr 1; omega_using [h4]))
    fun t' ⟨hi', hc', hz, hg', hx'⟩ => ?_
  simp only [eval, hz, Option.map_some]
  rcases Nat.eq_or_lt_of_le h1 with rfl | hn
  · refine .inl ⟨by simp only [show l.S / l.R - 1 + 1 = l.S / l.R by omega_using [h4], decide_true, Bool.not_true], ?_,
      fun r r1 r2 r3 => (hg' r r1 r2 r3).trans (hg r r1 r2 r3), hx'.trans hx⟩
    rw [show l.S / l.R - 1 + 1 = l.S / l.R by omega_using [h4]] at hi'
    exact hi'
  · refine .inr ⟨by simp only [decide_eq_false (show ¬ (l.S / l.R - n + 1 = l.S / l.R) by omega_using [h4, hn]),
        Bool.not_false], n - 1,
      by omega_using [h1], by omega_using [hn], by omega_using [h4], by rw [show l.S / l.R - (n - 1) = l.S / l.R - n + 1 by omega_using [h1, h4]]; exact hi',
      by rw [hc']; congr 1; omega_using [h4], fun r r1 r2 r3 => (hg' r r1 r2 r3).trans (hg r r1 r2 r3), hx'.trans hx⟩

end VG.Proof.Bignum.X86_64.Ifma

end

end

/-! ### `Bignum.X86_64.Ifma.Out`, which this module and modules that import it used -/

section

/-!
# RSA with AVX512_IFMA on x86-64, any size: the multiplication's result

After the loop and the steps of the last, partial block, `ammCore` stores the `R`
accumulators of each prime at `r11` (and `r11 + D`), then carries the `4 R`
limbs of each in order (`carryOut`), the two chains interleaved
(`ammCore_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside ofs_off writeW_outside word_writeW_self)
open VG.Impl.Rsa.X86_64.CrtIfma
open VG.Proof.Bignum.X86_64.AmmSym (wrList writeW256_outside word_wrList_unique Upd ex_add_mem ex_mov ex_and
  ex_shr ex_store add_ofNat' shr_ofNat wrList_outside Keeps)

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

theorem AmmOk.D_bounds (hl : AmmOk l) : l.NB ≤ l.D ∧ l.D + l.NB ≤ 2 ^ 20 := by
  rcases hl with (rfl | rfl | rfl | rfl) | rfl | rfl | rfl | rfl | rfl <;> decide

theorem LayOk.D_bounds (hl : LayOk l) : l.NB ≤ l.D ∧ l.D + l.NB ≤ 2 ^ 20 := hl.amm.D_bounds

/-- At most two lanes, whose carries are `rdx` and `rsi`. -/
theorem AmmOk.nl_le (hl : AmmOk l) : 1 ≤ l.nl ∧ l.nl ≤ 2 := by
  rcases hl with (rfl | rfl | rfl | rfl) | rfl | rfl | rfl | rfl | rfl <;> decide

theorem off_ltN (hl : AmmOk l) {j : Nat} (hj : j < l.L) : l.off j + 8 ≤ l.NB := by
  obtain ⟨hR, _⟩ := hl.bounds
  have h1 := Nat.mod_lt j (show 0 < l.R by omega_arith)
  have h2 : j / l.R < 4 := Nat.div_lt_of_lt_mul (by simp only [Lay.L] at hj; rw [Nat.mul_comm]; exact hj)
  unfold Lay.off Lay.NB; omega_arith

theorem off_lt (hl : LayOk l) {j : Nat} (hj : j < l.L) : l.off j + 8 ≤ l.NB := off_ltN hl.amm hj

theorem off_sepN (hl : AmmOk l) {j q : Nat} (hj : j < l.L) (hq : q < l.L) (h : q ≠ j) :
    l.off q + 8 ≤ l.off j ∨ l.off j + 8 ≤ l.off q := by
  obtain ⟨hR, _⟩ := hl.bounds
  have h1 := Nat.mod_lt j (show 0 < l.R by omega_arith)
  have h2 : j / l.R < 4 := Nat.div_lt_of_lt_mul (by simp only [Lay.L] at hj; rw [Nat.mul_comm]; exact hj)
  have h3 := Nat.mod_lt q (show 0 < l.R by omega_arith)
  have h4 : q / l.R < 4 := Nat.div_lt_of_lt_mul (by simp only [Lay.L] at hq; rw [Nat.mul_comm]; exact hq)
  unfold Lay.off
  by_cases e : q % l.R = j % l.R
  · have e' : q / l.R ≠ j / l.R := fun e' => h (by rw [← Nat.div_add_mod q l.R, ← Nat.div_add_mod j l.R, e, e'])
    omega_arith
  · omega_arith

theorem off_sep (hl : LayOk l) {j q : Nat} (hj : j < l.L) (hq : q < l.L) (h : q ≠ j) :
    l.off q + 8 ≤ l.off j ∨ l.off j + 8 ≤ l.off q := off_sepN hl.amm hj hq h

theorem carryIn_lt63 {L : Nat → Nat} {n : Nat} (h : ∀ j < n, L j < 2 ^ 63) : carryIn L n < 2 ^ 12 := by
  induction n with
  | zero => simp only [carryIn]; decide
  | succ n ih =>
    have := ih fun j hj => h j (by omega_arith)
    have := h n (by omega_arith)
    simp only [carryIn]
    exact Nat.div_lt_of_lt_mul (by omega_arith)

theorem and_mask {y : Nat} (hy : y < 2 ^ 64) : BitVec.ofNat 64 y &&& mask52 = BitVec.ofNat 64 (y % 2 ^ 52) :=
  AmmSym.and_mask hy

theorem eaG {s : State} {B : Addr} {b : Reg} (h : s.gpr b = B) (d : Nat) : s.ea (at_ b d) = off B d := by
  simp only [State.ea, at_, h, off]
  exact congrArg _ (BitVec.ofInt_natCast ..)

/-! ## The stores -/

/-- 32-byte stores of registers at `b` plus offsets. -/
def storeCode (b : Reg) (xs : List (Nat × VReg)) : List Instr :=
  xs.map fun x => .evStore (at_ b x.1) x.2

theorem stores_gen {B : Addr} {b : Reg} :
    ∀ (xs : List (Nat × VReg)) (s : State), s.gpr b = B →
      (∀ x ∈ xs, InRegions s.wr (off B x.1) 32) →
      WP isa (.block (storeCode b xs)) s fun s' => s' = { s with mem := wrList s.mem B (xs.map fun x => (x.1, s.vy x.2)) }
  | [], s, _, _ => WP.block_nil rfl
  | (e, r) :: rest, s, hB, hw => by
    rw [storeCode, List.map_cons, WP.block_cons_iff]
    refine ⟨{ s with mem := s.mem.writeW (off B e) (s.vy r) }, ?_, ?_⟩
    · simp only [exec, eaG hB, State.store256, hw (e, r) (List.mem_cons_self ..), ite_true]
    · refine WP.mono (stores_gen rest _ hB fun x hx => hw x (List.mem_cons_of_mem _ hx)) fun s' h => ?_
      rw [h]
      rfl

/-- The accumulators' stores of `ammCore`. -/
def accStores (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : List (Nat × VReg) :=
  (List.range l.nl).flatMap fun p => (List.range l.R).map fun k => (l.D * p + 32 * k, acc l p k (l.S % l.R))

theorem accStores_code :
    ((List.range l.nl).flatMap fun p => (List.range l.R).map fun k =>
      (Instr.evStore (at_ .r11 (l.D * p + 32 * k)) (acc l p k (l.S % l.R)))) = storeCode .r11 (accStores l) := by
  simp only [storeCode, accStores, List.map_flatMap, List.map_map, Function.comp_def]

theorem mem_accStores {x : Nat × VReg} (hx : x ∈ accStores l) :
    ∃ p < l.nl, ∃ k < l.R, x = (l.D * p + 32 * k, acc l p k (l.S % l.R)) := by
  simp only [accStores, List.mem_flatMap, List.mem_range, List.mem_map] at hx
  obtain ⟨p, hp, k, hk, rfl⟩ := hx
  exact ⟨p, hp, k, hk, rfl⟩

theorem accStores_win :
    ∀ x ∈ accStores l, ∃ p < l.nl, l.D * p + 0 ≤ x.1 ∧ x.1 + 32 ≤ l.D * p + 0 + l.NB := by
  intro x hx
  obtain ⟨p, hp, k, hk, rfl⟩ := mem_accStores hx
  exact ⟨p, hp, by omega_arith, by simp only [Lay.NB]; omega_arith⟩

/-- Lane `p` within the lanes' regions. -/
theorem D_lane {p : Nat} (hp : p < l.nl) : l.D * p ≤ l.D * (l.nl - 1) := Nat.mul_le_mul_left _ (by omega_arith)

theorem accStores_lt : ∀ x ∈ accStores l, x.1 + 32 ≤ l.D * (l.nl - 1) + l.NB := by
  intro x hx
  obtain ⟨p, hp, k, hk, rfl⟩ := mem_accStores hx
  have := D_lane (l := l) hp
  simp only [Lay.NB]; omega_arith

/-- Each lane's region starts within `D` of the first. -/
theorem D_le (hl : AmmOk l) {p : Nat} (hp : p < l.nl) : l.D * p ≤ l.D :=
  Nat.le_trans (Nat.mul_le_mul_left _ (show p ≤ 1 by have := hl.nl_le; omega_arith)) (Nat.le_of_eq (Nat.mul_one _))

/-- A lane's region starts at 0 or at `D`. -/
theorem D_mulN (hl : AmmOk l) {p : Nat} (hp : p < l.nl) : l.D * p = 0 ∨ l.D * p = l.D := by
  have := hl.nl_le; rcases (by omega_arith : p = 0 ∨ p = 1) with rfl | rfl <;> simp

/-- A lane is 0 or 1. -/
theorem lane01 (hl : AmmOk l) {p : Nat} (hp : p < l.nl) : p = 0 ∨ p = 1 := by
  have := hl.nl_le; omega_arith

/-- The lanes' regions, `D` bytes each. -/
theorem nlD (hl : AmmOk l) : l.nl * l.D = l.D * (l.nl - 1) + l.D := by
  have := hl.nl_le; rw [Nat.mul_comm, ← Nat.mul_succ]; congr 1; omega_arith

/-- A lane's region ends within the lanes'. -/
theorem lane_end (hl : AmmOk l) {p : Nat} (hp : p < l.nl) : l.D * p + l.D ≤ l.nl * l.D := by
  rw [nlD hl]; have := D_lane (l := l) hp; omega_arith

theorem nlD_le (hl : AmmOk l) : l.D ≤ l.nl * l.D ∧ l.nl * l.D ≤ 2 * l.D := by
  have := hl.nl_le
  exact ⟨Nat.le_mul_of_pos_left _ (by omega_arith), Nat.mul_le_mul_right _ this.2⟩

/-- Two lanes' regions, `D ≥ NB` apart. -/
theorem lane_sep (hl : AmmOk l) {p p' : Nat} (hp : p < l.nl) (hp' : p' < l.nl) (h : p ≠ p') :
    l.D * p + l.NB ≤ l.D * p' ∨ l.D * p' + l.NB ≤ l.D * p := by
  have hD := hl.D_bounds
  have hn := hl.nl_le
  rcases (by omega_arith : (p = 0 ∧ p' = 1) ∨ (p = 1 ∧ p' = 0)) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp <;> omega_arith

/-- The word of limb `k + R t` of lane `p` after the stores. -/
theorem read_stores (hl : AmmOk l) (m : Mem) (B : Addr) (s : State) {p k t : Nat} (hp : p < l.nl) (hk : k < l.R)
    (ht : t < 4) :
    word (wrList m B ((accStores l).map fun x => (x.1, s.vy x.2))) B (l.D * p + 32 * k + 8 * t) =
      qv s (vreg (regOf l p k (l.S % l.R))) t := by
  have hD := hl.D_bounds
  simp only [Lay.NB] at hD
  have hD1 : ∀ {q}, q < l.nl → l.D * q ≤ l.D := fun hq => D_le hl hq
  have hp' := hD1 hp
  refine word_wrList_unique B ht (by omega_arith) _ m ?_ (fun x hx => ?_) (fun x hx he => ?_)
  · simp only [List.mem_map]
    exact ⟨_, List.mem_flatMap.2 ⟨p, List.mem_range.2 hp, List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩⟩, rfl⟩
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    obtain ⟨p', hp'', k', hk', rfl⟩ := mem_accStores hy
    have := hD1 hp''
    simp only
    by_cases e : p' = p
    · subst e; omega_arith
    · have := lane_sep hl hp hp'' (Ne.symm e)
      simp only [Lay.NB] at this
      omega_arith
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    obtain ⟨p', hp'', k', hk', rfl⟩ := mem_accStores hy
    have : p' = p ∧ k' = k := by
      by_cases e : p' = p
      · subst e; simp only at he; omega_arith
      · have := lane_sep hl hp hp'' (Ne.symm e)
        simp only [Lay.NB] at this
        simp only at he; omega_arith
    obtain ⟨rfl, rfl⟩ := this
    rfl

/-! ## Frames of both regions -/

/-- `m'` agrees with `m` but on the bytes at offsets `[D p + o, D p + o + n)` of `B`, for each lane `p`. -/
def Out2 (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (B : Addr) (o n : Nat) (m m' : Mem) : Prop :=
  ∀ x, (∀ p < l.nl, ofs B x < l.D * p + o ∨ l.D * p + o + n ≤ ofs B x) → m' x = m x

theorem Out2.refl (B : Addr) (o n : Nat) (m : Mem) : Out2 l B o n m m := fun _ _ => rfl

theorem Out2.trans {B : Addr} {o n : Nat} {m₁ m₂ m₃ : Mem} (h₁ : Out2 l B o n m₁ m₂) (h₂ : Out2 l B o n m₂ m₃) :
    Out2 l B o n m₁ m₃ := fun x hx => (h₂ x hx).trans (h₁ x hx)

theorem Out2.of_outside {B : Addr} {o n p : Nat} {m m' : Mem} (hp : p < l.nl)
    (h : Outside B (l.D * p + o) n m m') : Out2 l B o n m m' := fun x hx => h x (hx p hp)

/-- Writes of 32 bytes within the windows. -/
theorem wrList_out2 (hl : AmmOk l) (B : Addr) {o n : Nat} (hn : l.D + o + n ≤ 2 ^ 63) :
    ∀ (xs : List (Nat × BitVec 256)) (m : Mem), (∀ x ∈ xs, ∃ p < l.nl, l.D * p + o ≤ x.1 ∧ x.1 + 32 ≤ l.D * p + o + n) →
      Out2 l B o n m (wrList m B xs)
  | [], m, _ => Out2.refl B o n m
  | (e, v) :: rest, m, h => by
    obtain ⟨p, hp, h1, h2⟩ := h (e, v) (List.mem_cons_self ..)
    have hDp : l.D * p ≤ l.D := by
      have := hl.nl_le; rcases (by omega_arith : p = 0 ∨ p = 1) with rfl | rfl <;> simp
    exact (Out2.of_outside hp ((writeW256_outside m B v (by omega_arith)).mono h1 (by omega_arith))).trans
      (wrList_out2 hl B hn rest _ fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- `m'` agrees with `m` but on the bytes at offsets `[D p + o, D p + o + n)` of `B`, for each lane. -/
def OutN (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (B : Addr) (o n : Nat) (m m' : Mem) : Prop :=
  ∀ x, (∀ p < l.nl, ofs B x < l.D * p + o ∨ l.D * p + o + n ≤ ofs B x) → m' x = m x

theorem OutN.refl (B : Addr) (o n : Nat) (m : Mem) : OutN l B o n m m := fun _ _ => rfl

theorem OutN.trans {B : Addr} {o n : Nat} {m₁ m₂ m₃ : Mem} (h₁ : OutN l B o n m₁ m₂) (h₂ : OutN l B o n m₂ m₃) :
    OutN l B o n m₁ m₃ := fun x hx => (h₂ x hx).trans (h₁ x hx)

theorem OutN.of_outside {B : Addr} {o n p : Nat} {m m' : Mem} (hp : p < l.nl)
    (h : Outside B (l.D * p + o) n m m') : OutN l B o n m m' := fun x hx => h x (hx p hp)

/-- `Out2`, which is the same. -/
theorem OutN.out2 {B : Addr} {o n : Nat} {m m' : Mem} (h : OutN l B o n m m') : Out2 l B o n m m' := h

/-- Writes of 32 bytes within the lanes' windows. -/
theorem wrList_outN (B : Addr) {o n : Nat} (hn : l.D * (l.nl - 1) + o + n ≤ 2 ^ 63) :
    ∀ (xs : List (Nat × BitVec 256)) (m : Mem),
      (∀ x ∈ xs, ∃ p < l.nl, l.D * p + o ≤ x.1 ∧ x.1 + 32 ≤ l.D * p + o + n) →
      OutN l B o n m (wrList m B xs)
  | [], m, _ => OutN.refl B o n m
  | (e, v) :: rest, m, h => by
    obtain ⟨p, hp, h1, h2⟩ := h (e, v) (List.mem_cons_self ..)
    have hDp := D_lane (l := l) hp
    exact (OutN.of_outside hp ((writeW256_outside m B v (by omega_arith)).mono h1 (by omega_arith))).trans
      (wrList_outN B hn rest _ fun x hx => h x (List.mem_cons_of_mem _ hx))

/-! ## The carries -/

/-- After limb `j` of the lanes below `p` (and every limb below `j`), from
the stored limbs `L p`. -/
structure CarryN (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (B : Addr) (L : Nat → Nat → Nat) (m₀ : Mem) (s : State)
    (j p : Nat) : Prop where
  r11 : s.gpr .r11 = B
  r12 : s.gpr .r12 = mask52
  c : ∀ p' < l.nl, s.gpr (cReg p') = BitVec.ofNat 64 (carryIn (L p') (if p' < p then j + 1 else j))
  words : ∀ p' < l.nl, ∀ q < l.L, word s.mem B (l.D * p' + l.off q) =
    BitVec.ofNat 64 (if q < j ∨ (q = j ∧ p' < p) then carried (L p') q else L p' q)
  frame : OutN l B 0 l.NB m₀ s.mem

/-- The lanes' carries and temporaries are four distinct registers. -/
theorem cReg_cases (p : Nat) : (cReg p = .rdx ∧ cTmp p = .rax) ∨ (cReg p = .rsi ∧ cTmp p = .rcx) := by
  unfold cReg cTmp; split <;> simp

theorem cReg_inj (hl : AmmOk l) {p p' : Nat} (hp : p < l.nl) (hp' : p' < l.nl) (h : p' ≠ p) :
    cReg p' ≠ cReg p := by
  have := hl.nl_le
  rcases (by omega_arith : (p = 0 ∧ p' = 1) ∨ (p = 1 ∧ p' = 0)) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem cTmp_ne (p p' : Nat) : cReg p' ≠ cTmp p := by
  rcases cReg_cases p with ⟨_, h⟩ | ⟨_, h⟩ <;> rcases cReg_cases p' with ⟨h', _⟩ | ⟨h', _⟩ <;> rw [h, h'] <;> decide

/-- Limb `j` of lane `p`'s chain. -/
theorem laneStep_ok (hl : AmmOk l) {B : Addr} {L : Nat → Nat → Nat} {m₀ : Mem} {s : State} {j p : Nat}
    (hj : j < l.L) (hp : p < l.nl) (hL : ∀ p < l.nl, ∀ q < l.L, L p q < 2 ^ 63)
    (hw : ∀ d, d + 8 ≤ l.D * (l.nl - 1) + l.NB → InRegions s.wr (off B d) 8)
    (h : CarryN l B L m₀ s j p) :
    WP isa (.block (carryStep l j p)) s fun s' => CarryN l B L m₀ s' j (p + 1) ∧
      (∀ r, r ≠ cTmp p → r ≠ cReg p → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  have hD := hl.D_bounds
  have hDp := D_lane (l := l) hp
  have hDl := D_le hl hp
  have hDn : l.D * (l.nl - 1) ≤ l.D := D_le hl (show l.nl - 1 < l.nl by have := hl.nl_le; omega_arith)
  have ho := off_ltN hl hj
  have c0 := carryIn_lt63 (L := L p) (n := j) fun q hq => hL p hp q (by omega_arith)
  have l0 := hL p hp j hj
  have w0 : s.mem.readW (off B (l.D * p + l.off j)) 64 = BitVec.ofNat 64 (L p j) := by
    have := h.words p hp j hj
    rw [ite_eq_right_iff.2 (fun h => absurd h (by omega_arith))] at this; exact this
  have hc0 : s.gpr (cReg p) = BitVec.ofNat 64 (carryIn (L p) j) := by
    have := h.c p hp; rw [ite_eq_right_iff.2 (fun h => absurd h (by omega_arith))] at this; exact this
  have rin : ∀ d, d + 8 ≤ l.D * (l.nl - 1) + l.NB → InRegions (s.rd ++ s.wr) (off B d) 8 := fun d hd => by
    obtain ⟨r, hr, hc⟩ := hw d hd; exact ⟨r, List.mem_append_right _ hr, hc⟩
  obtain ⟨n1, n2, n3, n4, n5⟩ : cReg p ≠ cTmp p ∧ Reg.r11 ≠ cReg p ∧ Reg.r12 ≠ cReg p ∧ Reg.r11 ≠ cTmp p ∧
      Reg.r12 ≠ cTmp p := by
    rcases cReg_cases p with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> decide
  rw [carryStep, WP.block_cons_iff]
  obtain ⟨s1, e1, u1⟩ := ex_add_mem (s := s) (r := cReg p) (m := at_ .r11 (l.D * p + l.off j))
    (by rw [eaG h.r11]; exact rin _ (by omega_arith))
  refine ⟨s1, e1, ?_⟩
  rw [eaG h.r11, hc0, w0, add_ofNat' (by omega_arith)] at u1
  rw [WP.block_cons_iff]
  obtain ⟨s2, e2, u2⟩ := ex_mov (s := s1) (d := cTmp p) (r := cReg p)
  refine ⟨s2, e2, ?_⟩
  rw [WP.block_cons_iff]
  obtain ⟨s3, e3, u3⟩ := ex_and (s := s2) (d := cTmp p) (r := .r12)
  refine ⟨s3, e3, ?_⟩
  rw [u2.self, u2.other _ n5, u1.self, u1.other _ n3, h.r12, and_mask (by omega_arith)] at u3
  rw [WP.block_cons_iff]
  have r11₃ : s3.gpr .r11 = B := by rw [u3.other _ n4, u2.other _ n4, u1.other _ n2, h.r11]
  obtain ⟨s4, e4, m4, g4, rd4, wr4, x4⟩ := ex_store (s := s3) (r := cTmp p) (m := at_ .r11 (l.D * p + l.off j))
    (by rw [eaG r11₃, u3.wr, u2.wr, u1.wr]; exact hw _ (by omega_arith))
  refine ⟨s4, e4, ?_⟩
  rw [eaG r11₃, u3.self] at m4
  rw [WP.block_cons_iff]
  obtain ⟨s5, e5, u5⟩ := ex_shr (s := s4) (d := cReg p)
  refine ⟨s5, e5, ?_⟩
  rw [congrFun g4, u3.other _ n1, u2.other _ n1, u1.self, shr_ofNat (by omega_arith)] at u5
  have mem₅ : s5.mem = s.mem.writeW (off B (l.D * p + l.off j))
      (BitVec.ofNat 64 ((carryIn (L p) j + L p j) % 2 ^ 52)) := by
    rw [u5.mem, m4, u3.mem, u2.mem, u1.mem]
  have g5 : ∀ r, r ≠ cTmp p → r ≠ cReg p → s5.gpr r = s.gpr r := fun r a b => by
    rw [u5.other _ b, congrFun g4, u3.other _ a, u2.other _ a, u1.other _ b]
  refine WP.block_nil ⟨⟨by rw [g5 _ n4 n2, h.r11], by rw [g5 _ n5 n3, h.r12], fun p' hp' => ?_, fun p' hp' q hq => ?_, ?_⟩,
    g5, by rw [u5.rd, rd4, u3.rd, u2.rd, u1.rd], by rw [u5.wr, wr4, u3.wr, u2.wr, u1.wr],
    by rw [u5.mxcsr, x4, u3.mxcsr, u2.mxcsr, u1.mxcsr]⟩
  · by_cases e : p' = p
    · subst e
      rw [u5.self]
      simp only [Nat.lt_succ_self, ↓reduceIte, carryIn]; rw [Nat.add_comm]
    · rw [g5 _ (cTmp_ne p p') (cReg_inj hl hp hp' e), h.c p' hp']
      rcases Nat.lt_or_ge p' p with e' | e'
      · simp only [e', show p' < p + 1 by omega_arith, ↓reduceIte]
      · simp only [show ¬ p' < p by omega_arith, show ¬ p' < p + 1 by omega_arith, ↓reduceIte]
  · have hoq := off_ltN hl hq
    have hDp' := D_lane (l := l) hp'
    have hDl' := D_le hl hp'
    rw [mem₅]
    by_cases e : p' = p ∧ q = j
    · obtain ⟨rfl, rfl⟩ := e
      rw [word_writeW_self]
      simp only [Nat.lt_irrefl, Nat.lt_succ_self, and_self, or_true, ↓reduceIte, carried]; rw [Nat.add_comm]
    · have hsep : l.D * p' + l.off q + 8 ≤ l.D * p + l.off j ∨ l.D * p + l.off j + 8 ≤ l.D * p' + l.off q := by
        by_cases e' : p' = p
        · subst e'
          have := off_sepN hl hj hq (fun h => e ⟨rfl, h⟩)
          omega_arith
        · have := lane_sep hl hp hp' (Ne.symm e')
          omega_arith
      rw [(writeW_outside _ B _ (by omega_arith)).word (by omega_arith) (by omega_arith), h.words p' hp' q hq]
      by_cases c : q < j ∨ (q = j ∧ p' < p)
      · simp only [c, show q < j ∨ (q = j ∧ p' < p + 1) by omega_arith, ↓reduceIte]
      · simp only [c, show ¬ (q < j ∨ (q = j ∧ p' < p + 1)) by omega_arith, ↓reduceIte]
  · rw [mem₅]
    exact h.frame.trans (OutN.of_outside hp ((writeW_outside _ B _ (by omega_arith)).mono (by omega_arith) (by omega_arith)))

/-- Limb `j` of the lanes from `p`. -/
theorem lanes_ok (hl : AmmOk l) {B : Addr} {L : Nat → Nat → Nat} {m₀ : Mem} {j : Nat} (hj : j < l.L)
    (hL : ∀ p < l.nl, ∀ q < l.L, L p q < 2 ^ 63) :
    ∀ n p (s : State), p + n = l.nl → (∀ d, d + 8 ≤ l.D * (l.nl - 1) + l.NB → InRegions s.wr (off B d) 8) →
      CarryN l B L m₀ s j p →
      WP isa (.block ((List.range' p n).flatMap (carryStep l j))) s fun s' => CarryN l B L m₀ s' j l.nl ∧
        (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → s'.gpr r = s.gpr r) ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr
  | 0, p, s, hn, _, h => WP.block_nil ⟨by rw [← hn]; exact h, fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  | n + 1, p, s, hn, hw, h => by
    rw [List.range'_succ, List.flatMap_cons]
    refine WP.block_append (WP.mono (laneStep_ok hl hj (by omega_arith) hL hw h) fun s₁ ⟨h₁, g₁, rd₁, wr₁, x₁⟩ =>
      WP.mono (lanes_ok hl hj hL n (p + 1) s₁ (by omega_arith) (fun d hd => wr₁ ▸ hw d hd) h₁)
        fun s₂ ⟨h₂, g₂, rd₂, wr₂, x₂⟩ => ⟨h₂, fun r a b c d => (g₂ r a b c d).trans (g₁ r ?_ ?_),
          rd₂.trans rd₁, wr₂.trans wr₁, x₂.trans x₁⟩)
    · rcases cReg_cases p with ⟨_, e⟩ | ⟨_, e⟩ <;> rw [e] <;> with_reducible assumption
    · rcases cReg_cases p with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> with_reducible assumption

/-- Limb `j` of every lane. -/
theorem lanesAll_ok (hl : AmmOk l) {B : Addr} {L : Nat → Nat → Nat} {m₀ : Mem} {j : Nat} (hj : j < l.L)
    (hL : ∀ p < l.nl, ∀ q < l.L, L p q < 2 ^ 63) {s : State}
    (hw : ∀ d, d + 8 ≤ l.D * (l.nl - 1) + l.NB → InRegions s.wr (off B d) 8) (h : CarryN l B L m₀ s j 0) :
    WP isa (.block ((List.range l.nl).flatMap (carryStep l j))) s fun s' => CarryN l B L m₀ s' j l.nl ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  rw [List.range_eq_range']
  exact lanes_ok hl hj hL l.nl 0 s (Nat.zero_add _) hw h

/-- All lanes of limb `j` done: limb `j + 1` of none. -/
theorem CarryN.next {B : Addr} {L : Nat → Nat → Nat} {m₀ : Mem} {s : State} {j : Nat}
    (h : CarryN l B L m₀ s j l.nl) : CarryN l B L m₀ s (j + 1) 0 :=
  ⟨h.r11, h.r12, fun p' hp' => by rw [h.c p' hp']; simp only [hp', Nat.not_lt_zero, ↓reduceIte],
    fun p' hp' q hq => by
      rw [h.words p' hp' q hq]
      by_cases c : q < j + 1
      · simp only [show q < j ∨ (q = j ∧ p' < l.nl) by omega_arith, show q < j + 1 ∨ (q = j + 1 ∧ p' < 0) by omega_arith,
          ↓reduceIte]
      · simp only [show ¬ (q < j ∨ (q = j ∧ p' < l.nl)) by omega_arith,
          show ¬ (q < j + 1 ∨ (q = j + 1 ∧ p' < 0)) by omega_arith, ↓reduceIte], h.frame⟩

/-- The limbs from `j` on. -/
theorem limbs_ok (hl : AmmOk l) {B : Addr} {L : Nat → Nat → Nat} {m₀ : Mem}
    (hL : ∀ p < l.nl, ∀ q < l.L, L p q < 2 ^ 63) :
    ∀ n j (s : State), j + n = l.L → (∀ d, d + 8 ≤ l.D * (l.nl - 1) + l.NB → InRegions s.wr (off B d) 8) →
      CarryN l B L m₀ s j 0 →
      WP isa (.block ((List.range' j n).flatMap fun j => (List.range l.nl).flatMap (carryStep l j))) s fun s' =>
        CarryN l B L m₀ s' l.L 0 ∧
        (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → s'.gpr r = s.gpr r) ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr
  | 0, j, s, hn, _, h => WP.block_nil ⟨by rw [← hn]; exact h, fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  | n + 1, j, s, hn, hw, h => by
    rw [List.range'_succ, List.flatMap_cons]
    refine WP.block_append (WP.mono (lanesAll_ok hl (by omega_arith) hL hw h)
      fun s₁ ⟨h₁, g₁, rd₁, wr₁, x₁⟩ =>
      WP.mono (limbs_ok hl hL n (j + 1) s₁ (by omega_arith) (fun d hd => wr₁ ▸ hw d hd) h₁.next)
        fun s₂ ⟨h₂, g₂, rd₂, wr₂, x₂⟩ => ⟨h₂, fun r a b c d => (g₂ r a b c d).trans (g₁ r a b c d),
          rd₂.trans rd₁, wr₂.trans wr₁, x₂.trans x₁⟩)

/-- The lanes' carries set to zero. -/
theorem zeroC_ok (hl : AmmOk l) (s : State) :
    WP isa (.block ((List.range l.nl).map fun p => Instr.mov32 (cReg p) (.imm 0))) s fun s' =>
      (∀ p < l.nl, s'.gpr (cReg p) = 0) ∧ (∀ r, r ≠ .rdx → r ≠ .rsi → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  have := hl.nl_le
  have c0 : cReg 0 = .rdx := rfl
  have c1 : cReg 1 = .rsi := rfl
  rcases (by omega_arith : l.nl = 1 ∨ l.nl = 2) with hn | hn <;> rw [hn]
  · rw [List.range_one, List.map_singleton, WP.block_cons_iff, c0]
    refine ⟨_, rfl, WP.block_nil ⟨fun p hp => ?_, fun r a _ => ?_, rfl, rfl, rfl, rfl⟩⟩
    · obtain rfl : p = 0 := by omega_arith
      dsimp only; rw [c0, State.setReg32, RegUpd.gpr_setReg_self]; rfl
    · dsimp only; rw [State.setReg32, RegUpd.gpr_setReg_of_ne _ _ a]
  · rw [show List.range 2 = [0, 1] from rfl, List.map_cons, List.map_singleton, WP.block_cons_iff, c0, c1]
    refine ⟨_, rfl, ?_⟩
    rw [WP.block_cons_iff]
    refine ⟨_, rfl, WP.block_nil ⟨fun p hp => ?_, fun r a b => ?_, rfl, rfl, rfl, rfl⟩⟩
    · rcases (by omega_arith : p = 0 ∨ p = 1) with rfl | rfl
      · dsimp only
        rw [c0, State.setReg32, RegUpd.gpr_setReg_of_ne _ _ (by decide), State.setReg32, RegUpd.gpr_setReg_self]; rfl
      · dsimp only; rw [c1, State.setReg32, RegUpd.gpr_setReg_self]; rfl
    · dsimp only
      rw [State.setReg32, RegUpd.gpr_setReg_of_ne _ _ b, State.setReg32, RegUpd.gpr_setReg_of_ne _ _ a]

/-- The carry pass, from the limbs `L p` stored. -/
theorem carryOut_ok (hl : AmmOk l) {B : Addr} {L : Nat → Nat → Nat} {s : State}
    (hL : ∀ p < l.nl, ∀ q < l.L, L p q < 2 ^ 63)
    (hw : ∀ d, d + 8 ≤ l.D * (l.nl - 1) + l.NB → InRegions s.wr (off B d) 8)
    (hr11 : s.gpr .r11 = B) (hr12 : s.gpr .r12 = mask52)
    (hwords : ∀ p < l.nl, ∀ q < l.L, word s.mem B (l.D * p + l.off q) = BitVec.ofNat 64 (L p q)) :
    WP isa (.block (carryOut l)) s fun s' => CarryN l B L s.mem s' l.L 0 ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  rw [carryOut, WP.block_append_iff, List.range_eq_range' (n := l.L)]
  refine WP.mono (zeroC_ok hl s) fun s₁ ⟨c₁, g₁, m₁, rd₁, wr₁, x₁⟩ => ?_
  refine WP.mono (limbs_ok hl hL (m₀ := s.mem) l.L 0 s₁ (Nat.zero_add _) (fun d hd => wr₁ ▸ hw d hd)
    ⟨by rw [g₁ _ (by decide) (by decide), hr11], by rw [g₁ _ (by decide) (by decide), hr12],
      fun p hp => by rw [c₁ p hp]; simp only [Nat.not_lt_zero, ↓reduceIte, carryIn]; rfl,
      fun p hp q hq => by
        rw [m₁, hwords p hp q hq]; simp only [Nat.not_lt_zero, and_false, or_self, ↓reduceIte],
      by rw [m₁]; exact OutN.refl _ _ _ _⟩) fun s' ⟨h, g, rd, wr, x⟩ =>
    ⟨h, fun r a b c d => (g r a b c d).trans (g₁ r c d), rd.trans rd₁, wr.trans wr₁, x.trans x₁⟩

/-! ## The whole multiplication -/

/-- `ammCore` from the operands `a` (at `r8`), `b` (at `r9`) and the modulus `m`
with `k` (at `rbx`), into limbs at `r11 = B`: each lane's limbs carried, and
its carry out. -/
theorem ammCore_ok (hl : AmmOk l) {s : State} {B : Addr} {a m : Nat → Nat → Nat} {k : Nat → Nat}
    {bl : Nat → Nat → Nat} (e : Env l (s.setReg .r10 (s.gpr .rbx)) a m k bl) (hB : s.gpr .r11 = B)
    (hs : Scr s B (l.D * (l.nl - 1) + l.NB)) :
    WP isa (ammCore l) s fun s' =>
      (∀ p < l.nl, ∀ q < l.L, word s'.mem B (l.D * p + l.off q) =
        BitVec.ofNat 64 (carried (lm l a m k bl p l.S) q)) ∧
      (∀ p < l.nl, s'.gpr (cReg p) = BitVec.ofNat 64 (carryIn (lm l a m k bl p l.S) l.L)) ∧
      OutN l B 0 l.NB s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r9 → r ≠ .r10 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.gpr .r12 = mask52 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨hR, hR10⟩ := hl.bounds
  obtain ⟨_, hrg⟩ := hl.regs
  have hD := hl.D_bounds
  have hDn : l.D * (l.nl - 1) ≤ l.D := D_le hl (show l.nl - 1 < l.nl by have := hl.nl_le; omega_arith)
  refine WP.seq ?_
  rw [List.cons_append, WP.block_cons_iff]
  refine ⟨s.setReg .r10 (s.gpr .rbx), rfl, ?_⟩
  rw [List.cons_append, WP.block_cons_iff]
  refine ⟨_, rfl, ?_⟩
  refine WP.mono (zeros_ok hl (s := (s.setReg .r10 (s.gpr .rbx)).setReg32 .rcx (BitVec.ofNat 32 (l.S / l.R))))
    fun s₁ ⟨hz, k₁⟩ => ?_
  have g₁ : ∀ r, r ≠ .rax → r ≠ .rcx → s₁.gpr r = (s.setReg .r10 (s.gpr .rbx)).gpr r := fun r a c => by
    rw [k₁.gpr r a]; exact RegUpd.gpr_setReg_of_ne _ _ c
  have i₁ : InBlk l (s.setReg .r10 (s.gpr .rbx)) s₁ a m k bl 0 0 :=
    ⟨fun p hp kk hk t ht => by
      rw [hz _ (by have := regOf_lt (k := kk) (i := 0) hp hR; omega_arith) t ht]; rfl,
     fun t ht => hz _ (by simp only [zN]; omega_arith) t ht, g₁ _ (by decide) (by decide),
     by rw [g₁ _ (by decide) (by decide), Nat.mul_zero, BitVec.add_zero], g₁ _ (by decide) (by decide),
     k₁.mem, k₁.rd, k₁.wr⟩
  have hst := hl.steps
  refine WP.seq (WP.mono (loop_ok hl e (l.S / l.R) s₁ hst.1 (Nat.le_refl _) (by rw [Nat.sub_self]; exact i₁)
      (by rw [k₁.gpr _ (by decide)]; rcases hl with (rfl | rfl | rfl | rfl) | rfl | rfl | rfl | rfl | rfl <;> rfl))
    fun s₂ₐ ⟨i₂ₐ, g₂ₐ, x₂ₐ⟩ => ?_)
  rw [accStores_code, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (steps_chain hl e (l.S % l.R) (by omega_arith) (by omega_arith) s₂ₐ i₂ₐ) fun s₂ ⟨i₂, g₂', x₂'⟩ => ?_
  have g₂ : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r9 → s₂.gpr r = s₁.gpr r := fun r a c n =>
    (g₂' r a).trans (g₂ₐ r a c n)
  have x₂ : s₂.mxcsr = s₁.mxcsr := x₂'.trans x₂ₐ
  have hB₂ : s₂.gpr .r11 = B := by
    rw [g₂ _ (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide)]
    exact (RegUpd.gpr_setReg_of_ne _ _ (by decide)).trans hB
  have wr₂ : s₂.wr = s.wr := by rw [i₂.wr]; rfl
  rw [WP.block_append_iff]
  refine WP.mono (stores_gen (accStores l) s₂ hB₂ fun x hx =>
    wr₂ ▸ (let ⟨_, h, c⟩ := hs.region (accStores_lt x hx) (by decide); ⟨_, h, c⟩)) fun s₃ h₃ => ?_
  subst h₃
  rw [List.singleton_append, WP.block_cons_iff]
  refine ⟨_, rfl, ?_⟩
  have m₂ : s₂.mem = s.mem := i₂.mem
  refine WP.mono (carryOut_ok hl (B := B) (L := fun p => lm l a m k bl p l.S)
    (fun p _ q hq => lm_lt hR10 hst.2.2.2.1 hq)
    (fun d hd => by rw [RegUpd.wr_setReg, wr₂]; exact hs.st hd)
    (by rw [RegUpd.gpr_setReg_of_ne _ _ (by decide)]; exact hB₂)
    (RegUpd.gpr_setReg_self _ _ _) fun p hp q hq => ?_) fun s' ⟨h, g, rd, wr, x⟩ => ?_
  · have h1 := Nat.mod_lt q (show 0 < l.R by omega_arith)
    have h2 : q / l.R < 4 := Nat.div_lt_of_lt_mul (by simp only [Lay.L] at hq; rw [Nat.mul_comm]; exact hq)
    have := read_stores hl s₂.mem B s₂ hp (k := q % l.R) (t := q / l.R) h1 h2
    rw [i₂.lanes p hp _ h1 _ h2, Nat.mod_add_div, hst.2.2.2.2.1] at this
    rw [RegUpd.mem_setReg, show l.D * p + l.off q = l.D * p + 32 * (q % l.R) + 8 * (q / l.R) by
      unfold Lay.off; omega_arith]
    exact this
  refine ⟨fun p hp q hq => by rw [h.words p hp q hq]; simp only [hq, true_or, ite_true],
    fun p hp => by rw [h.c p hp]; simp only [Nat.not_lt_zero, ↓reduceIte], ?_,
    fun r r1 r2 r3 r4 r5 r6 r7 => ?_, by rw [g _ (by decide) (by decide) (by decide) (by decide)]; exact RegUpd.gpr_setReg_self _ _ _,
    by rw [rd, RegUpd.rd_setReg, i₂.rd]; rfl, by rw [wr, RegUpd.wr_setReg, wr₂],
    by rw [x, RegUpd.mxcsr_setReg, x₂, k₁.mxcsr]; rfl⟩
  · have o := wrList_outN (l := l) B (o := 0) (n := l.NB) (by omega_arith)
      ((accStores l).map fun x => (x.1, s₂.vy x.2)) s₂.mem fun x hx => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        exact accStores_win y hy
    have hf : OutN l B 0 l.NB (wrList s₂.mem B ((accStores l).map fun x => (x.1, s₂.vy x.2))) s'.mem := h.frame
    have o' : OutN l B 0 l.NB s.mem (wrList s₂.mem B ((accStores l).map fun x => (x.1, s₂.vy x.2))) :=
      fun x hx => (o x hx).trans (congrFun m₂ x)
    exact o'.trans hf
  · rw [g r r1 r2 r3 r4, RegUpd.gpr_setReg_of_ne _ _ r7, g₂ r r1 r2 r5, g₁ r r1 r2, RegUpd.gpr_setReg_of_ne _ _ r6]

/-- What `ammCore_ok` proves of `ammCore l`, of a code `c`. -/
def CoreOk (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (c : Prog isa) : Prop :=
  ∀ {s : State} {B : Addr} {a m : Nat → Nat → Nat} {k : Nat → Nat} {bl : Nat → Nat → Nat},
    Env l (s.setReg .r10 (s.gpr .rbx)) a m k bl → s.gpr .r11 = B → Scr s B (l.D * (l.nl - 1) + l.NB) →
    WP isa c s fun s' =>
      (∀ p < l.nl, ∀ q < l.L, word s'.mem B (l.D * p + l.off q) =
        BitVec.ofNat 64 (carried (lm l a m k bl p l.S) q)) ∧
      (∀ p < l.nl, s'.gpr (cReg p) = BitVec.ofNat 64 (carryIn (lm l a m k bl p l.S) l.L)) ∧
      OutN l B 0 l.NB s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r9 → r ≠ .r10 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.gpr .r12 = mask52 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr

theorem ammCore_core (hl : AmmOk l) : CoreOk l (ammCore l) := fun e hB hs => ammCore_ok hl e hB hs

end VG.Proof.Bignum.X86_64.Ifma

end

end

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
theorem checkZerosU_p1024 : checkZerosU VG.Impl.Rsa.X86_64.PubIfma.pay1024 = true := by decide +kernel
theorem checkZerosU_p1536 : checkZerosU VG.Impl.Rsa.X86_64.PubIfma.pay1536 = true := by decide +kernel

theorem UOk.checkZeros (hu : UOk l) : checkZerosU l = true := by
  rcases hu with rfl | rfl | rfl | rfl
  · exact checkZerosU_2048
  · exact checkZerosU_p2048
  · exact checkZerosU_p1024
  · exact checkZerosU_p1536

theorem zerosU_ok (hu : UOk l) {s : State} :
    WP isa (.block (zerosU l)) s fun s' =>
      (∀ r < 32, ∀ t < 4, qv s' (vreg r) t = if r < l.nl * l.R ∨ r = uzN l then 0 else qv s (vreg r) t) ∧
        Keeps s s' := by
  have h := hu.checkZeros
  unfold checkZerosU at h
  split at h
  · rename_i σ hσ
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
    refine WP.mono (run_ok (fun b d n hn hd => absurd hd (by omega_arith)) (SRel.init s) hσ) fun s' hs =>
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
    omega_arith
  by_cases b10 : b = .r10
  · subst b10; rw [g.r10]; exact e.rd10 d n hn hdn
  · simp only [limU, b8, b9, b10, ite_false] at hdn
    omega_arith

theorem LaneU.stepIn (hu : UOk l) (e : Env l s₀ a m k bl) (g : GlobU l s₀ s) {p n : Nat} (hp : p < l.nl)
    (hn : n < l.S) (h : LaneU l s a m k bl p n) :
    StepInU l s p n (lm l a m k bl p n) (a p) (m p) (k p) (bl p n)
      (if n + 1 < l.S then bl p (n + 1) else 0) := by
  obtain ⟨hl, -, h20, -, -⟩ := hu.regs
  have hS := hl.steps.2.2.2.1
  refine ⟨g.z, fun kk hk t ht => ?_, h.bv hn, h.uv hn, fun j hj => lm_lt h20 (by omega_arith) hj,
    fun kk hk t ht => ?_, fun kk hk t ht => ?_, fun t ht => ?_, fun hn' => ?_, e.alt p hp, e.mlt p hp,
    e.klt p hp, e.blt p hp n (by omega_arith), ?_⟩
  · rw [h.lanes kk hk t ht]; simp only [hn, and_true]
  · rw [g.mem, g.r8]; exact e.ina p hp kk hk t ht
  · rw [g.mem, g.r10]; exact e.inm p hp kk hk t ht
  · rw [g.mem, g.r10]; exact e.ink p hp t ht
  · rw [g.mem, g.r9, ite_eq_left (by omega_arith)]; exact e.inb p hp (n + 1) (by omega_arith)
  · split
    · exact e.blt p hp (n + 1) (by omega_arith)
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
  refine ⟨?_, hq', hp', by omega_arith, by omega_arith⟩
  rcases Nat.lt_or_gt_of_ne hpq with h | h
  · have := Nat.mul_le_mul_left l.R (show p + 1 ≤ q by omega_arith)
    rw [Nat.mul_add, Nat.mul_one] at this; omega_arith
  · have := Nat.mul_le_mul_left l.R (show q + 1 ≤ p by omega_arith)
    rw [Nat.mul_add, Nat.mul_one] at this; omega_arith

/-- Lane `q`'s registers, kept by lane `p`'s step. -/
theorem LaneU.frame (hu : UOk l) {p q n : Nat} (hp : p < l.nl) (hq : q < l.nl) (hpq : p ≠ q) {s' : State}
    (hf : Frame l s s' p) (h : LaneU l s a m k bl q n) : LaneU l s' a m k bl q n := by
  obtain ⟨-, hR, -, -, hb⟩ := hu.regs
  have hm := Nat.mod_lt n (show 0 < 2 by decide)
  have ha := lanes_apart hp hq hpq
  have eu : ubN l q (n % 2) = l.nl * l.R + 8 * q + n % 2 := rfl
  have ev : uuN l q (n % 2) = l.nl * l.R + 8 * q + 2 + n % 2 := rfl
  refine ⟨fun kk hk t ht => ?_, fun hn t ht => ?_, fun hn t ht => ?_⟩
  · have hr := regOf_bounds (l := l) (by omega_arith) (p := q) (kk := kk) (j := n)
    rw [hf _ (by omega_arith) (by omega_arith) (by omega_arith) t ht]; exact h.lanes kk hk t ht
  · rw [hf _ (by omega_arith) (by omega_arith) (by omega_arith) t ht]; exact h.bv hn t ht
  · rw [hf _ (by omega_arith) (by omega_arith) (by omega_arith) t ht]; exact h.uv hn t ht

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
      rw [hf _ (by simp only [uzN]; omega_arith) (by simp only [uzN]; omega_arith) (by simp only [uzN]; omega_arith) t ht]
      exact g.z t ht, ⟨fun kk hk' t ht => ?_, fun hn' t ht => ?_, fun hn' t ht => ?_⟩, hf, hk⟩
  · rw [hl kk hk' t ht]
    by_cases hn' : n + 1 < l.S
    · simp only [hn', ite_true, show ¬ l.S ≤ n + 1 by omega_arith, not_false_eq_true, and_true]; rfl
    · simp only [hn', ite_false, show l.S ≤ n + 1 by omega_arith, not_true, and_false]; rfl
  · rw [hb' (by omega_arith) t ht, ite_eq_left hn']
  · rw [hu' (by omega_arith) t ht, ite_eq_left hn']; rfl

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
  | zero => intro _ s h; exact WP.block_nil ⟨h.1, fun _ h => absurd h (by omega_arith), fun p _ hp => h.2 p hp,
      fun _ _ => rfl, rfl⟩
  | succ q ih =>
    intro hq s h
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (ih (by omega_arith) s h) fun s₁ ⟨g₁, d₁, t₁, r₁, x₁⟩ => ?_
    refine WP.mono (laneStepU_ok hu e g₁ (p := q) (by omega_arith) hn (t₁ q (Nat.le_refl _) (by omega_arith)))
      fun s₂ ⟨g₂, l₂, f₂, k₂⟩ => ⟨g₂, fun p hp => ?_, fun p hp hp' => ?_,
        fun r hr => (k₂.gpr r hr).trans (r₁ r hr), k₂.mxcsr.trans x₁⟩
    · by_cases hpq : p = q
      · subst hpq; exact l₂
      · exact (d₁ p (by omega_arith)).frame hu (p := q) (by omega_arith) (by omega_arith) (Ne.symm hpq) f₂
    · exact (t₁ p (by omega_arith) hp').frame hu (p := q) (by omega_arith) hp' (by omega_arith) f₂

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
    refine WP.mono (ih (by omega_arith) s h) fun s₁ ⟨h₁, g₁, x₁⟩ => ?_
    exact WP.mono (pairStepU_ok hu e (by omega_arith) h₁) fun s₂ ⟨h₂, g₂, x₂⟩ =>
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
  have hb := e.inb p hp 0 (by simp only [Lay.L]; omega_arith)
  rw [show l.D * p + l.off 0 = l.D * p by simp only [Lay.off, Nat.zero_mod, Nat.zero_div,
    Nat.mul_zero, Nat.add_zero]] at hb
  refine WP.mono (ammStartU_ok (m := m p) hu hp (g.ctx e) h0
    (fun t ht => by rw [g.mem, g.r8]; exact e.ina p hp 0 (by omega_arith) t ht)
    (by rw [g.mem, g.r10]; exact e.ink p hp 0 (by decide)) (by rw [g.mem, g.r9]; exact hb))
    fun s' ⟨h₀, hb', hu', hf, hk⟩ => ⟨g.keep hk fun t ht => by
      rw [hf _ (by simp only [uzN]; omega_arith) (by simp only [uzN]; omega_arith) (by simp only [uzN]; omega_arith)
        (by simp only [uzN]; omega_arith) (by simp only [uzN]; omega_arith) t ht]; exact g.z t ht, h₀, hb', hu',
      fun r hr h1 h2 t ht => hf r hr (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) t ht, hk⟩

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
  | zero => intro _ s g hz; exact WP.block_nil ⟨g, fun _ h => absurd h (by omega_arith), fun r _ hr => hz r hr,
      fun _ _ => rfl, rfl⟩
  | succ q ih =>
    intro hq s g hz
    have hqs := regsS (show q < l.nl by omega_arith)
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (ih (by omega_arith) s g hz) fun s₁ ⟨g₁, d₁, z₁, r₁, x₁⟩ => ?_
    refine WP.mono (laneStartU_ok hu e g₁ (p := q) (by omega_arith) fun t ht => by
        rw [hqs.1]; exact z₁ _ (Nat.le_refl _) (by omega_arith) t ht)
      fun s₂ ⟨g₂, a₂, b₂, u₂, f₂, k₂⟩ => ⟨g₂, fun p hp => ?_, fun r hr hr' t ht => ?_,
        fun r hr => (k₂.gpr r hr).trans (r₁ r hr), k₂.mxcsr.trans x₁⟩
    · by_cases hpq : p = q
      · subst hpq
        refine ⟨fun kk hk t ht => ?_, fun _ t ht => b₂ t ht, fun _ t ht => u₂ t ht⟩
        by_cases k0 : kk = 0
        · subst k0; rw [ite_eq_left ⟨rfl, by have := hu.regs.1.steps.2.2.1; omega_arith⟩]; exact a₂ t ht
        · have hr := regOf_bounds (l := l) (by omega_arith) (p := p) (kk := kk) (j := 0)
          have e0 : regOf l p kk 0 = l.R * p + kk := by
            simp only [regOf, Nat.add_zero, Nat.mod_eq_of_lt hk]
          rw [ite_eq_right (by omega_arith), f₂ _ (by omega_arith) (by omega_arith) (by omega_arith) t ht,
            z₁ _ (by omega_arith) (by omega_arith) t ht]; rfl
      · have ha := lanes_apart (show p < l.nl by omega_arith) (show q < l.nl by omega_arith) hpq
        have h1 := d₁ p (by omega_arith)
        refine ⟨fun kk hk t ht => ?_, fun hn t ht => ?_, fun hn t ht => ?_⟩
        · have hr := regOf_bounds (l := l) (by omega_arith) (p := p) (kk := kk) (j := 0)
          rw [f₂ _ (by omega_arith) (by omega_arith) (by omega_arith) t ht]; exact h1.lanes kk hk t ht
        · have eu : ubN l p (0 % 2) = l.nl * l.R + 8 * p := rfl
          rw [f₂ _ (by omega_arith) (by omega_arith) (by omega_arith) t ht]; exact h1.bv hn t ht
        · have ev : uuN l p (0 % 2) = l.nl * l.R + 8 * p + 2 := rfl
          rw [f₂ _ (by omega_arith) (by omega_arith) (by omega_arith) t ht]; exact h1.uv hn t ht
    · rw [Nat.mul_add, Nat.mul_one] at hr
      rw [f₂ _ (by omega_arith) (by omega_arith) (by omega_arith) t ht]; exact z₁ r (by omega_arith) hr' t ht

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
  have hDn : l.D * (l.nl - 1) ≤ l.D := D_le hl (show l.nl - 1 < l.nl by omega_arith)
  rw [ammCoreU_code, WP.block_cons_iff]
  refine ⟨s.setReg .r10 (s.gpr .rbx), rfl, ?_⟩
  rw [WP.block_append_iff]
  refine WP.mono (zerosU_ok hu) fun s₁ ⟨hz, k₁⟩ => ?_
  have g₁ : GlobU l (s.setReg .r10 (s.gpr .rbx)) s₁ :=
    ⟨fun t ht => by rw [hz (uzN l) (by simp only [uzN]; omega_arith) t ht, ite_eq_left (Or.inr rfl)],
      k₁.gpr _ (by decide), k₁.gpr _ (by decide), k₁.gpr _ (by decide), k₁.mem, k₁.rd, k₁.wr⟩
  rw [WP.block_append_iff]
  refine WP.mono (lanesStartU_ok hu e l.nl (Nat.le_refl _) s₁ g₁ fun r hr t ht => by
      rw [hz r (by omega_arith) t ht, ite_eq_left (Or.inl hr)])
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
  · have h1 := Nat.mod_lt q (show 0 < l.R by omega_arith)
    have h2 : q / l.R < 4 := Nat.div_lt_of_lt_mul (by simp only [Lay.L] at hq; rw [Nat.mul_comm]; exact hq)
    have := read_stores hl s₃.mem B s₃ hp (k := q % l.R) (t := q / l.R) h1 h2
    have er : regOf l p (q % l.R) (l.S % l.R) = regOf l p (q % l.R) l.S := by
      simp only [regOf, Nat.add_mod_mod]
    rw [er, (h₃.2 p hp).lanes _ h1 _ h2, ite_eq_right (by omega_arith), Nat.add_zero, Nat.mod_add_div] at this
    rw [RegUpd.mem_setReg, show l.D * p + l.off q =
      l.D * p + 32 * (q % l.R) + 8 * (q / l.R) by unfold Lay.off; omega_arith]
    exact this
  refine ⟨fun p hp q hq => by rw [h.words p hp q hq]; simp only [hq, true_or, ite_true],
    fun p hp => by rw [h.c p hp]; simp only [Nat.not_lt_zero, ↓reduceIte], ?_,
    fun r r1 r2 r3 r4 r5 r6 r7 => ?_,
    by rw [g _ (by decide) (by decide) (by decide) (by decide)]; exact RegUpd.gpr_setReg_self _ _ _,
    by rw [rd, RegUpd.rd_setReg, h₃.1.rd]; rfl, by rw [wr, RegUpd.wr_setReg, wr₃],
    by rw [x, RegUpd.mxcsr_setReg, x₃, x₂, k₁.mxcsr]; rfl⟩
  · have o := wrList_outN (l := l) B (o := 0) (n := l.NB) (by omega_arith)
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

/-- The multiplication of each layout but `ammCoreZ`'s. -/
theorem ammMul_core (hl : AmmOk l) (hz : l.z = false) : CoreOk l (ammMul l) := by
  unfold ammMul
  rw [hz, ite_eq_right (by decide)]
  split
  · rename_i h; exact ammCoreU_core (UOk.of_amm hl h)
  · exact ammCore_core hl

end VG.Proof.Bignum.X86_64.Ifma

end

end

/-! ### `Bignum.X86_64.Ifma.Spec`, which this module and modules that import it used -/

section

/-!
# RSA with AVX512_IFMA on x86-64, any size: the multiplication

`amm_ok`: for each prime `p`, with its region at
`B + D p` (`B` in `rbx`), the numbers of `4 R` limbs of 52 bits at offsets
`a` and `b` multiplied and divided by `2^(52 S)` modulo the modulus at
`oM`, into offset `o`: below twice the modulus when both operands are, and
congruent to their product over `2^(52 S)`.

The numbers are in the stride layout: limb `j` at `Lay.off j`, read by
`limb`; `val52` is their value.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside off_off)
open VG.Impl.Rsa.X86_64.CrtIfma
open VG.Proof.Bignum.X86_64.AmmSym (ops se_ofNat off_add ofNat_toNat64 setOff ofs_rebase')

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-- Limb `j` of the number at `B + d`. -/
abbrev limb (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (m : Mem) (B : Addr) (d j : Nat) : Nat := (word m B (d + l.off j)).toNat

/-- The number at `B + d`. -/
def val52 (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (m : Mem) (B : Addr) (d : Nat) : Nat := lval (limb l m B d) l.L

/-- Limbs of a value below `2^(52 S)` from limb `S` on are zero. -/
theorem lval_trunc {b : Nat → Nat} {S : Nat} : ∀ n, S ≤ n → lval b n < 2 ^ (52 * S) → lval b n = lval b S
  | 0, h, _ => by rw [Nat.le_zero.1 h]
  | n + 1, h, hl => by
    rcases Nat.eq_or_lt_of_le h with rfl | h'
    · rfl
    rw [lval_succ] at hl ⊢
    have hp : 2 ^ (52 * S) ≤ 2 ^ (52 * n) := Nat.pow_le_pow_right (by decide) (by omega_arith)
    have hz : b n = 0 := by
      rcases Nat.eq_zero_or_pos (b n) with h0 | h0
      · exact h0
      · have : 2 ^ (52 * n) ≤ b n * 2 ^ (52 * n) := Nat.le_mul_of_pos_left _ h0
        omega_arith
    rw [hz, Nat.zero_mul, Nat.add_zero] at hl ⊢
    exact lval_trunc n (by omega_arith) hl

theorem LayOk.D_ge (hl : LayOk l) : l.NB + 32 ≤ l.D := by
  rcases hl with rfl | rfl | rfl | rfl <;> decide

theorem AmmOk.D_ge (hl : AmmOk l) : l.NB + 32 ≤ l.D := by
  rcases hl with (rfl | rfl | rfl | rfl) | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The CRT's layouts have the two primes' lanes. -/
theorem LayOk.nl (hl : LayOk l) : l.nl = 2 := by
  rcases hl with rfl | rfl | rfl | rfl <;> rfl

/-- The CRT's layouts' two regions. -/
theorem LayOk.nlD (hl : LayOk l) : l.nl * l.D = 2 * l.D := by rw [hl.nl]

/-- A frame at `B + o` as one at `B`, for the lanes. -/
theorem OutN.rebaseN {B : Addr} {o n : Nat} {m m' : Mem} (h : OutN l (off B o) 0 n m m')
    (hn : o + l.D * (l.nl - 1) + n < 2 ^ 64) : OutN l B o n m m' := fun x hx => h x fun p hp => by
  have hDp := D_lane (l := l) hp
  rcases ofs_rebase' B x (o := o) (by omega_arith) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases hx p hp with h3 | h3 <;> omega_arith
  · omega_arith

/-- The product of numbers below `2 M` fits, with a multiple of `M`, when `4 M ≤ R`. -/
theorem fit_of_lt {A B M R T : Nat} (hA : A < 2 * M) (hB : B < 2 * M) (hM : 4 * M ≤ R) (hRT : R ≤ T) :
    A * B + M * R < R * T := by
  have h1 : A * B ≤ R * M := by
    have := Nat.mul_le_mul (Nat.le_of_lt hA) (Nat.le_of_lt hB)
    have e : 2 * M * (2 * M) = 4 * M * M := by grind
    exact Nat.le_trans (e ▸ this) (Nat.mul_le_mul_right _ hM)
  have h2 : R * (2 * M) < R * T := Nat.mul_lt_mul_of_pos_left (by omega_using [hA, hM, hRT]) (by omega_using [hA, hM])
  rw [show R * (2 * M) = R * M + M * R by rw [Nat.mul_comm M R, ← Nat.mul_add]; congr 1; omega_using []] at h2
  omega_using [h1, h2]

/-- A multiplication `c` (`ammCore`, or `ammCoreU`) with `r8`, `r9`, `r11` at offsets `a`, `b`, `o` of
`B = rbx`: for a second operand below `2^(52 S)` and a product that fits, the result times `2^(52 S)` is
the product plus a multiple `M U` of the modulus, with `U < 2^(52 S)`. -/
theorem ammCoreSpecN_eq (hl : AmmOk l) {c : Prog isa} (hc : CoreOk l c) {s : State} {B : Addr} {Z o a b : Nat} {k : Nat → Nat}
    (hB : s.gpr .rbx = B) (r8₃ : s.gpr .r8 = off B a) (r9₃ : s.gpr .r9 = off B b) (r11₃ : s.gpr .r11 = off B o)
    (hs : Scr s B Z) (hZ : l.D * (l.nl - 1) + l.NB + 32 ≤ Z) (hZb : Z ≤ 2 ^ 63)
    (ho : o + l.D * (l.nl - 1) + l.NB ≤ Z) (ha : a + l.D * (l.nl - 1) + l.NB ≤ Z)
    (hb : b + l.D * (l.nl - 1) + l.NB ≤ Z)
    (hlt : ∀ p < l.nl, ∀ j < l.L, limb l s.mem B (l.D * p + a) j < 2 ^ 52 ∧ limb l s.mem B (l.D * p + b) j < 2 ^ 52 ∧
      limb l s.mem B (l.D * p + oM) j < 2 ^ 52)
    (hk : ∀ p < l.nl, ∀ t < 4, word s.mem B (l.D * p + l.oK0 + 8 * t) = BitVec.ofNat 64 (k p))
    (hklt : ∀ p < l.nl, k p < 2 ^ 52) (hk0 : ∀ p < l.nl, (limb l s.mem B (l.D * p + oM) 0 * k p + 1) % 2 ^ 52 = 0) :
    WP isa c s fun s' => (∀ p < l.nl,
      (∀ j < l.L, limb l s'.mem B (l.D * p + o) j < 2 ^ 52) ∧
      (val52 l s.mem B (l.D * p + b) < 2 ^ (52 * l.S) →
        val52 l s.mem B (l.D * p + a) * val52 l s.mem B (l.D * p + b) +
          val52 l s.mem B (l.D * p + oM) * 2 ^ (52 * l.S) < 2 ^ (52 * l.S) * 2 ^ (52 * l.L) →
        ∃ U, U < 2 ^ (52 * l.S) ∧ val52 l s'.mem B (l.D * p + o) * 2 ^ (52 * l.S) =
          val52 l s.mem B (l.D * p + a) * val52 l s.mem B (l.D * p + b) + val52 l s.mem B (l.D * p + oM) * U)) ∧
      OutN l B o l.NB s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r9 → r ≠ .r10 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.gpr .r12 = mask52 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨hR, hR10⟩ := hl.bounds
  have hD := hl.D_bounds
  have hD' := hl.D_ge
  have hDn : l.D * (l.nl - 1) ≤ l.D := D_le hl (show l.nl - 1 < l.nl by have := hl.nl_le; omega_arith)
  have hnD : l.nl * l.D = l.D * (l.nl - 1) + l.D := by
    have := hl.nl_le; rw [Nat.mul_comm, ← Nat.mul_succ]; congr 1; omega_arith
  -- the operands, as functions of the limb index
  let A : Nat → Nat → Nat := fun p => limb l s.mem B (l.D * p + a)
  let Bl : Nat → Nat → Nat := fun p => limb l s.mem B (l.D * p + b)
  let M : Nat → Nat → Nat := fun p => limb l s.mem B (l.D * p + oM)
  have rdS : ∀ d n, 0 < n → d + n ≤ Z → InRegions (s.rd ++ s.wr) (off B d) n := fun d n hn hd =>
    let ⟨_, h, c⟩ := hs.region hd hn; ⟨_, List.mem_append_right _ h, c⟩
  have hoff : ∀ kk < l.R, ∀ t < 4, l.off (kk + l.R * t) = 32 * kk + 8 * t := fun kk hk t _ => by
    rw [Nat.add_comm, off_blk hR hk]
  have e : Env l (s.setReg .r10 (s.gpr .rbx)) A M k Bl := by
    refine ⟨fun p hp kk hk t ht => ?_, fun p hp kk hk t ht => ?_, fun p hp t ht => ?_, fun p hp q hq => ?_,
      fun p hp j hj => (hlt p hp j hj).1, fun p hp j hj => (hlt p hp j hj).2.2, hklt,
      fun p hp q hq => (hlt p hp q hq).2.1, fun d n hn hd => ?_, fun d n hn hd => ?_, fun d n hn hd => ?_⟩
    · rw [RegUpd.mem_setReg, RegUpd.gpr_setReg_of_ne _ _ (by decide), r8₃, off_add]
      show _ = BitVec.ofNat 64 (limb l s.mem B (l.D * p + a) (kk + l.R * t))
      rw [ofNat_toNat64, hoff kk hk t ht]
      exact congrArg (fun d => s.mem.readW (off B d) 64) (by omega_arith)
    · rw [RegUpd.mem_setReg, RegUpd.gpr_setReg_self, hB]
      show _ = BitVec.ofNat 64 (limb l s.mem B (l.D * p + oM) (kk + l.R * t))
      rw [ofNat_toNat64, hoff kk hk t ht]
      exact congrArg (fun d => s.mem.readW (off B d) 64) (by simp only [oM]; omega_arith)
    · rw [RegUpd.mem_setReg, RegUpd.gpr_setReg_self, hB]
      exact hk p hp t ht
    · rw [RegUpd.mem_setReg, RegUpd.gpr_setReg_of_ne _ _ (by decide), r9₃, off_add]
      show _ = BitVec.ofNat 64 (limb l s.mem B (l.D * p + b) q)
      rw [ofNat_toNat64]
      exact congrArg (fun d => s.mem.readW (off B d) 64) (by omega_arith)
    · rw [RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_setReg_of_ne _ _ (by decide), r8₃, off_add]
      exact rdS _ n hn (by rw [show lim l .r8 = l.D * (l.nl - 1) + l.NB from rfl] at hd; omega_arith)
    · rw [RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_setReg_of_ne _ _ (by decide), r9₃, off_add]
      exact rdS _ n hn (by
        rw [show lim l .r9 = l.D * (l.nl - 1) + 32 * (l.R - 1) + 8 from rfl] at hd; simp only [Lay.NB] at hb; omega_arith)
    · rw [RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_setReg_self, hB]
      exact rdS _ n hn (by rw [show lim l .r10 = l.D * (l.nl - 1) + l.NB + 32 from rfl] at hd; omega_arith)
  have hNB : 0 < l.NB := by simp only [Lay.NB]; omega_arith
  have hs₃ : Scr s (off B o) (l.D * (l.nl - 1) + l.NB) := hs.sub (by omega_arith) (by omega_arith)
  refine WP.mono (hc e r11₃ hs₃) fun s' ⟨hw, _, hf, hg, h12, hrd, hwr, hx⟩ => ?_
  refine ⟨fun p hp => ?_, hf.rebaseN (by omega_arith), hg, h12, hrd, hwr, hx⟩
  have hq : ∀ j < l.L, limb l s'.mem B (l.D * p + o) j = carried (lm l A M k Bl p l.S) j := fun j hj => by
    have := hw p hp j hj
    simp only [word, off_off] at this
    show (s'.mem.readW (off B _) 64).toNat = _
    rw [show l.D * p + o + l.off j = o + (l.D * p + l.off j) by omega_arith, this, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := carried_lt (lm l A M k Bl p l.S) j; omega_arith)]
  have hv : val52 l s'.mem B (l.D * p + o) = lval (carried (lm l A M k Bl p l.S)) l.L := by
    unfold val52; exact lval_congr hq
  refine ⟨fun j hj => (hq j hj) ▸ carried_lt _ j, fun hBv hfit => ?_⟩
  have ok : Amm52N.Ok l.L (ops A M k p) :=
    ⟨fun j hj => (hlt p hp j hj).1, fun j hj => (hlt p hp j hj).2.2, hk0 p hp⟩
  have hst := hl.steps
  have he := Amm52N.steps_val (by simp only [Lay.L]; omega_arith) ok (b := Bl p) (fun i hi => (hlt p hp i hi).2.1)
    (fun _ => 0) l.S hst.2.2.2.1
  have z : lval (fun _ => 0) l.L = 0 := by
    rw [show (fun _ : Nat => 0) = fun j => (fun _ : Nat => 0) j * 0 by funext; rfl, lval_mul, Nat.mul_zero]
  rw [z, Nat.zero_add] at he
  have hU : lval (Amm52N.stepsU l.L (ops A M k p) (Bl p) fun _ => 0) l.S < 2 ^ (52 * l.S) :=
    lval_lt fun j _ => lo_lt _ _
  have hcv := carried_val (lm l A M k Bl p l.S) l.L
  rw [hv]
  unfold val52 at hBv hfit ⊢
  change lval (lm l A M k Bl p l.S) l.L * _ = lval (A p) l.L * lval (Bl p) l.S + lval (M p) l.L * _ at he
  change lval (Bl p) l.L < _ at hBv
  change lval (A p) l.L * lval (Bl p) l.L + lval (M p) l.L * _ < _ at hfit
  have hbS : lval (Bl p) l.L = lval (Bl p) l.S := lval_trunc _ hst.2.2.2.1 hBv
  rw [hbS] at hfit
  generalize lval (Amm52N.stepsU l.L (ops A M k p) (Bl p) fun _ => 0) l.S = U at he hU
  have hz : lval (lm l A M k Bl p l.S) l.L < 2 ^ (52 * l.L) := by
    have h1 : lval (M p) l.L * U ≤ lval (M p) l.L * 2 ^ (52 * l.S) := Nat.mul_le_mul_left _ (Nat.le_of_lt hU)
    refine Nat.lt_of_mul_lt_mul_left (a := 2 ^ (52 * l.S)) ?_
    rw [Nat.mul_comm]
    generalize 2 ^ (52 * l.S) * 2 ^ (52 * l.L) = T at hfit ⊢
    omega_arith
  rw [Amm52N.carryIn_zero hz, Nat.zero_mul, Nat.add_zero] at hcv
  refine ⟨U, hU, ?_⟩
  rw [hcv]
  show lval (lm l A M k Bl p l.S) l.L * _ = lval (A p) l.L * lval (Bl p) l.L + lval (M p) l.L * U
  rw [hbS]; exact he

/-- `ammCoreSpecN_eq` for operands below twice the modulus: so is the result, and it is congruent to
their product over `2^(52 S)`. -/
theorem ammCoreSpecN_ok (hl : AmmOk l) {c : Prog isa} (hc : CoreOk l c) {s : State} {B : Addr} {Z o a b : Nat} {k : Nat → Nat}
    (hB : s.gpr .rbx = B) (r8₃ : s.gpr .r8 = off B a) (r9₃ : s.gpr .r9 = off B b) (r11₃ : s.gpr .r11 = off B o)
    (hs : Scr s B Z) (hZ : l.D * (l.nl - 1) + l.NB + 32 ≤ Z) (hZb : Z ≤ 2 ^ 63)
    (ho : o + l.D * (l.nl - 1) + l.NB ≤ Z) (ha : a + l.D * (l.nl - 1) + l.NB ≤ Z)
    (hb : b + l.D * (l.nl - 1) + l.NB ≤ Z)
    (hlt : ∀ p < l.nl, ∀ j < l.L, limb l s.mem B (l.D * p + a) j < 2 ^ 52 ∧ limb l s.mem B (l.D * p + b) j < 2 ^ 52 ∧
      limb l s.mem B (l.D * p + oM) j < 2 ^ 52)
    (hk : ∀ p < l.nl, ∀ t < 4, word s.mem B (l.D * p + l.oK0 + 8 * t) = BitVec.ofNat 64 (k p))
    (hklt : ∀ p < l.nl, k p < 2 ^ 52) (hk0 : ∀ p < l.nl, (limb l s.mem B (l.D * p + oM) 0 * k p + 1) % 2 ^ 52 = 0) :
    WP isa c s fun s' => (∀ p < l.nl,
      (∀ j < l.L, limb l s'.mem B (l.D * p + o) j < 2 ^ 52) ∧
      (val52 l s.mem B (l.D * p + a) < 2 * val52 l s.mem B (l.D * p + oM) →
        val52 l s.mem B (l.D * p + b) < 2 * val52 l s.mem B (l.D * p + oM) →
        4 * val52 l s.mem B (l.D * p + oM) ≤ 2 ^ (52 * l.S) →
        val52 l s'.mem B (l.D * p + o) < 2 * val52 l s.mem B (l.D * p + oM) ∧
        val52 l s'.mem B (l.D * p + o) * 2 ^ (52 * l.S) % val52 l s.mem B (l.D * p + oM) =
          val52 l s.mem B (l.D * p + a) * val52 l s.mem B (l.D * p + b) % val52 l s.mem B (l.D * p + oM))) ∧
      OutN l B o l.NB s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r9 → r ≠ .r10 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.gpr .r12 = mask52 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  refine WP.mono (ammCoreSpecN_eq hl hc hB r8₃ r9₃ r11₃ hs hZ hZb ho ha hb hlt hk hklt hk0) fun s' ⟨hv, rest⟩ =>
    ⟨fun p hp => ⟨(hv p hp).1, fun hA hB' hM => ?_⟩, rest⟩
  have hSL : 2 ^ (52 * l.S) ≤ 2 ^ (52 * l.L) :=
    Nat.pow_le_pow_right (by decide) (by have := hl.steps; omega_arith)
  obtain ⟨U, hU, he⟩ := (hv p hp).2 (by omega_arith) (fit_of_lt hA hB' hM hSL)
  exact ⟨amm_lt he hU hA hB' hM, by rw [he, Nat.add_mul_mod_self_left]⟩

/-- The layout's multiplication with `r8`, `r9`, `r11` at offsets `a`, `b`, `o` of `B = rbx`. -/
theorem ammCoreSpec_ok (hl : AmmOk l) (hz : l.z = false) {s : State} {B : Addr} {o a b : Nat} {k : Nat → Nat}
    (hB : s.gpr .rbx = B) (r8₃ : s.gpr .r8 = off B a) (r9₃ : s.gpr .r9 = off B b) (r11₃ : s.gpr .r11 = off B o)
    (hs : Scr s B (l.nl * l.D))
    (ho : o + l.NB ≤ l.D) (ha : a + l.NB ≤ l.D) (hb : b + l.NB ≤ l.D)
    (hlt : ∀ p < l.nl, ∀ j < l.L, limb l s.mem B (l.D * p + a) j < 2 ^ 52 ∧ limb l s.mem B (l.D * p + b) j < 2 ^ 52 ∧
      limb l s.mem B (l.D * p + oM) j < 2 ^ 52)
    (hk : ∀ p < l.nl, ∀ t < 4, word s.mem B (l.D * p + l.oK0 + 8 * t) = BitVec.ofNat 64 (k p))
    (hklt : ∀ p < l.nl, k p < 2 ^ 52) (hk0 : ∀ p < l.nl, (limb l s.mem B (l.D * p + oM) 0 * k p + 1) % 2 ^ 52 = 0)
    (hA : ∀ p < l.nl, val52 l s.mem B (l.D * p + a) < 2 * val52 l s.mem B (l.D * p + oM))
    (hBv : ∀ p < l.nl, val52 l s.mem B (l.D * p + b) < 2 * val52 l s.mem B (l.D * p + oM))
    (hM : ∀ p < l.nl, 4 * val52 l s.mem B (l.D * p + oM) ≤ 2 ^ (52 * l.S)) :
    WP isa (ammMul l) s fun s' => (∀ p < l.nl,
      (∀ j < l.L, limb l s'.mem B (l.D * p + o) j < 2 ^ 52) ∧
      val52 l s'.mem B (l.D * p + o) < 2 * val52 l s.mem B (l.D * p + oM) ∧
      val52 l s'.mem B (l.D * p + o) * 2 ^ (52 * l.S) % val52 l s.mem B (l.D * p + oM) =
        val52 l s.mem B (l.D * p + a) * val52 l s.mem B (l.D * p + b) % val52 l s.mem B (l.D * p + oM)) ∧
      Out2 l B o l.NB s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r9 → r ≠ .r10 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  have hnD := nlD hl
  have hD := hl.D_bounds
  have hD' := hl.D_ge
  have hnl := hl.nl_le
  have hDn : l.D * (l.nl - 1) ≤ l.D := D_le hl (show l.nl - 1 < l.nl by omega_arith)
  refine WP.mono (ammCoreSpecN_ok hl (ammMul_core hl hz) hB r8₃ r9₃ r11₃ hs (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) hlt hk hklt hk0) fun s' ⟨hv, hf, hg, _, hrd, hwr, hx⟩ =>
    ⟨fun p hp => let h := hv p hp; ⟨h.1, (h.2 (hA p hp) (hBv p hp) (hM p hp)).1,
      (h.2 (hA p hp) (hBv p hp) (hM p hp)).2⟩, hf.out2, hg, hrd, hwr, hx⟩

/-- `[o] := [a] [b] / 2^(208 R)` for each lane. -/
theorem amm_ok (hl : AmmOk l) (hz : l.z = false) {s : State} {B : Addr} {o a b : Nat} {k : Nat → Nat}
    (hB : s.gpr .rbx = B) (hs : Scr s B (l.nl * l.D))
    (ho : o + l.NB ≤ l.D) (ha : a + l.NB ≤ l.D) (hb : b + l.NB ≤ l.D)
    (hlt : ∀ p < l.nl, ∀ j < l.L, limb l s.mem B (l.D * p + a) j < 2 ^ 52 ∧ limb l s.mem B (l.D * p + b) j < 2 ^ 52 ∧
      limb l s.mem B (l.D * p + oM) j < 2 ^ 52)
    (hk : ∀ p < l.nl, ∀ t < 4, word s.mem B (l.D * p + l.oK0 + 8 * t) = BitVec.ofNat 64 (k p))
    (hklt : ∀ p < l.nl, k p < 2 ^ 52) (hk0 : ∀ p < l.nl, (limb l s.mem B (l.D * p + oM) 0 * k p + 1) % 2 ^ 52 = 0)
    (hA : ∀ p < l.nl, val52 l s.mem B (l.D * p + a) < 2 * val52 l s.mem B (l.D * p + oM))
    (hBv : ∀ p < l.nl, val52 l s.mem B (l.D * p + b) < 2 * val52 l s.mem B (l.D * p + oM))
    (hM : ∀ p < l.nl, 4 * val52 l s.mem B (l.D * p + oM) ≤ 2 ^ (52 * l.S)) :
    WP isa (amm l o a b) s fun s' => (∀ p < l.nl,
      (∀ j < l.L, limb l s'.mem B (l.D * p + o) j < 2 ^ 52) ∧
      val52 l s'.mem B (l.D * p + o) < 2 * val52 l s.mem B (l.D * p + oM) ∧
      val52 l s'.mem B (l.D * p + o) * 2 ^ (52 * l.S) % val52 l s.mem B (l.D * p + oM) =
        val52 l s.mem B (l.D * p + a) * val52 l s.mem B (l.D * p + b) % val52 l s.mem B (l.D * p + oM)) ∧
      Out2 l B o l.NB s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  have hD : l.D + l.NB ≤ 2 ^ 20 := hl.D_bounds.2
  refine WP.seq ?_
  refine setOff (by omega_arith) fun s₁ u₁ => setOff (by omega_arith) fun s₂ u₂ =>
    setOff (by omega_arith) fun s₃ u₃ => WP.block_nil ?_
  rw [u₁.other _ (by decide), hB] at u₂
  rw [u₂.other _ (by decide), u₁.other _ (by decide), hB] at u₃
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have rd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have wr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have r8₃ : s₃.gpr .r8 = off B a := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.self, hB]
  have r9₃ : s₃.gpr .r9 = off B b := by rw [u₃.other _ (by decide), u₂.self]
  have rbx₃ : s₃.gpr .rbx = B := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hB]
  have g₃ : ∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r11 → s₃.gpr r = s.gpr r := fun r h8 h9 h11 => by
    rw [u₃.other _ h11, u₂.other _ h9, u₁.other _ h8]
  rw [← m₃] at hlt hk hk0 hA hBv hM ⊢
  refine WP.mono (ammCoreSpec_ok hl hz rbx₃ r8₃ r9₃ u₃.self (hs.congr wr₃) ho ha hb hlt hk hklt hk0 hA hBv hM)
    fun s' ⟨hv, hf, hg, hrd, hwr, hx⟩ => ⟨hv, hf, fun r h1 h2 h3 h4 h5 h6 h7 h8 h9 => ?_,
      hrd.trans rd₃, hwr.trans wr₃, by rw [hx, u₃.mxcsr, u₂.mxcsr, u₁.mxcsr]⟩
  rw [hg r h1 h2 h3 h4 h6 h7 h9, g₃ r h5 h6 h8]

end VG.Proof.Bignum.X86_64.Ifma

end

end

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
  unfold Lay.off; rw [hR]; omega_using []

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
    exact e.rd9 _ n hn (by simp only [limZ] at hdn; omega_using [hb, hR, hN, hdn])
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
    refine WP.mono (ih (by omega_using [hn]) (by omega_using [hlt]) s h hq) fun s₁ ⟨h₁, q₁, g₁, x₁⟩ => ?_
    obtain ⟨w, acc⟩ := h₁.acc
    have hin : ZIn l s₁ n (zo a ms) (fun p => zst l a ms bl p (l.R * blk + n)) (fun p => bl p (l.R * blk + n)) w
        ((l.R * blk + n + 1) * 2 ^ 56) := ⟨acc, h₁.con, q₁, e.ok, by omega_using [hL, hlt]⟩
    have hrd : ∀ p < 2, s₁.mem.readW (s₁.gpr .r9 + BitVec.ofNat 64 (l.D * p + l.off (n + 1))) 64 =
        BitVec.ofNat 64 (bl p (l.R * blk + (n + 1))) := fun p hp => by
      rw [h₁.mem, h₁.r9, ofNat_add64, ← e.inb p hp (l.R * blk + (n + 1)) hlt,
        show l.R * blk + (n + 1) = l.R * blk + n + 1 from rfl, off_next hR (by omega_using [hR, hn])]
      exact congrArg (fun d => s₀.mem.readW (s₀.gpr .r9 + BitVec.ofNat 64 d) 64) (by omega_using [])
    refine WP.mono (zStep_ok hz (by omega_using [hn]) hin false (bn := fun p => bl p (l.R * blk + (n + 1)))
      (fun _ => by have := hrd 0 (by decide); rwa [Nat.mul_zero, Nat.zero_add] at this)
      (fun _ => by have := hrd 1 (by decide); rwa [Nat.mul_one] at this)
      (fun h0 => absurd h0 (by decide)) (h₁.ctx hz e hb)) fun s₂ ⟨acc₂, con₂, q₂, k₂⟩ => ?_
    have eB : (l.R * blk + n + 1) * 2 ^ 56 + 2 ^ 56 = (l.R * blk + (n + 1) + 1) * 2 ^ 56 := by omega_using []
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
    have : l.R * blk ≤ l.R * 2 := Nat.mul_le_mul_left _ (by omega_using [hb, h3])
    omega_using [hR, hL, this]
  refine WP.mono (zSteps_ok hz e (by omega_using [hb, h3]) l.R (Nat.le_refl _) hlt s h hq) fun s₁ ⟨h₁, q₁, g₁, x₁⟩ => ?_
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  have r9₁ := h₁.r9
  have cx₁ : s₁.gpr .rcx = BitVec.ofNat 64 (l.S / l.R - blk) := by rw [g₁]; exact hcx
  have e8 : BitVec.signExtend 64 (8 : BitVec 32) = BitVec.ofNat 64 8 := rfl
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := rfl
  have hc : BitVec.ofNat 64 (l.S / l.R - blk) - 1 = BitVec.ofNat 64 (l.S / l.R - (blk + 1)) := by
    rw [show l.S / l.R - blk = (l.S / l.R - (blk + 1)) + 1 by omega_using [hb], BitVec.ofNat_add]
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
  · rw [g₃ _ (by decide), r9₂, r9₁, BitVec.add_assoc, show 8 * (blk + 1) = 8 * blk + 8 by omega_using [], BitVec.ofNat_add]
  · rw [g₃ _ (by decide), g₂ _ (by decide)]; exact h₁.r10
  · rw [v₃.1, v₂.1]; exact h₁.mem
  · rw [v₃.2.1, v₂.2.1]; exact h₁.rd
  · rw [v₃.2.2.1, v₂.2.2.1]; exact h₁.wr
  · rw [eI, q₃₁, show zBq l (0 % 2) = zBq l (l.R % 2) by rw [hR]]; exact q₁ k hk
  · rw [cx₃, cx₂, hc]
  · rw [z₃, cx₂, hc, h3]
    rcases (by omega_using [hb, h3] : blk = 0 ∨ blk = 1 ∨ blk = 2) with rfl | rfl | rfl <;> rfl
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
  refine WP.mono (zBlock_ok hz (blk := l.S / l.R - n) (by omega_using [h1, h4]) e hi hq (by rw [hc]; congr 1; omega_using [h4]))
    fun t' ⟨hi', hq', hc', hzf, hg', hx'⟩ => ?_
  simp only [eval, hzf, Option.map_some]
  rcases Nat.eq_or_lt_of_le h1 with rfl | hn
  · refine .inl ⟨by simp only [show l.S / l.R - 1 + 1 = l.S / l.R by omega_using [h4], decide_true, Bool.not_true], ?_, ?_,
      fun r r1 r2 => (hg' r r1 r2).trans (hg r r1 r2), hx'.trans hx⟩
    · rw [show l.S / l.R - 1 + 1 = l.S / l.R by omega_using [h4]] at hi'
      exact hi'
    · rw [show l.S / l.R - 1 + 1 = l.S / l.R by omega_using [h4]] at hq'
      exact hq'
  · refine .inr ⟨by simp only [decide_eq_false (show ¬ (l.S / l.R - n + 1 = l.S / l.R) by omega_using [h4, hn]),
        Bool.not_false], n - 1,
      by omega_using [h1], by omega_using [hn], by omega_using [h4], by rw [show l.S / l.R - (n - 1) = l.S / l.R - n + 1 by omega_using [h1, h4]]; exact hi',
      by rw [show l.S / l.R - (n - 1) = l.S / l.R - n + 1 by omega_using [h1, h4]]; exact hq',
      by rw [hc']; congr 1; omega_using [h4], fun r r1 r2 => (hg' r r1 r2).trans (hg r r1 r2), hx'.trans hx⟩

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
    rw [ite_eq_left h4, ite_eq_left h4, this, show k / 4 = 0 by omega_using [h4], show k % 4 = k by omega_using [h4]]
  · have := hf 1 (by decide) (k - 4) (by omega_using [hk])
    rw [Nat.mul_one] at this
    rw [ite_eq_right h4, ite_eq_left (by omega_using [hk]), this, show k / 4 = 1 by omega_using [hk, h4], show k % 4 = k - 4 by omega_using [hk, h4]]

/-- The first limb's register. -/
theorem zB0_eval {s : State} {g : Nat → Nat}
    (hg : ∀ p < 2, s.mem.readW (s.gpr .r9 + BitVec.ofNat 64 (l.D * p + 0)) 64 = BitVec.ofNat 64 (g p))
    {k : Nat} (hk : k < 8) : (zB0 l).eval s k = BitVec.ofNat 64 (g (k / 4)) := by
  simp only [zB0, ZT.eval]
  by_cases h4 : k < 4
  · have := hg 0 (by decide)
    rw [Nat.mul_zero, Nat.zero_add] at this
    rw [ite_eq_left h4, ite_eq_left h4, this, show k / 4 = 0 by omega_using [h4]]
  · have := hg 1 (by decide)
    rw [Nat.mul_one] at this
    rw [ite_eq_right h4, ite_eq_left (by omega_using [hk]), this, show k / 4 = 1 by omega_using [hk, h4]]

theorem sel4_93 {t : Nat} (ht : t < 4) : sel4 0x93 t = (t + 3) % 4 := by
  rcases (by omega_using [ht] : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl | rfl <;> rfl

theorem sel4_40 {t : Nat} (ht : t < 4) : sel4 0x40 t = if t < 3 then 0 else 1 := by
  rcases (by omega_using [ht] : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl | rfl <;> rfl

/-- A row moved up a quadword within each lane, the last quadword first. -/
theorem zLd_perm {s : State} {b : Reg} {d : Nat} {f : Nat → Nat → Nat}
    (hf : ∀ p < 2, ∀ t < 4,
      s.mem.readW (s.gpr b + BitVec.ofNat 64 (l.D * p + d + 8 * t)) 64 = BitVec.ofNat 64 (f p t))
    {k : Nat} (hk : k < 8) :
    (ZT.perm (zLd l b d) 0x93).eval s k = BitVec.ofNat 64 (f (k / 4) ((k % 4 + 3) % 4)) := by
  simp only [ZT.eval]
  have h4 : (k % 4 + 3) % 4 < 4 := Nat.mod_lt _ (by decide)
  rw [sel4_93 (Nat.mod_lt _ (by decide)), zLd_eval hf (by omega_using [hk]),
    show (4 * (k / 4) + (k % 4 + 3) % 4) / 4 = k / 4 by omega_using [],
    show (4 * (k / 4) + (k % 4 + 3) % 4) % 4 = (k % 4 + 3) % 4 by omega_using []]

/-- The mask's register. -/
theorem zK_eval {s : State} {k : Nat} (hk : k < 8) :
    (ZT.ins (.perm (.lane0 .rax) 0x40) (.perm (.lane0 .rax) 0x40)).eval s k =
      if k % 4 < 3 then s.gpr .rax else 0 := by
  have key : ∀ j < 4, (ZT.perm (.lane0 .rax) 0x40).eval s j = if j < 3 then s.gpr .rax else 0 := fun j hj => by
    simp only [ZT.eval]
    rw [show j / 4 = 0 by omega_using [hj], Nat.mul_zero, Nat.zero_add, show j % 4 = j by omega_using [hj], sel4_40 hj]
    by_cases h3 : j < 3
    · rw [ite_eq_left h3, ite_eq_left h3, ite_eq_left rfl]
    · rw [ite_eq_right h3, ite_eq_right h3, ite_eq_right (by decide)]
  rw [ZT.eval]
  by_cases h4 : k < 4
  · rw [ite_eq_left h4, key k h4, show k % 4 = k by omega_using [h4]]
  · rw [ite_eq_right h4, key (k - 4) (by omega_using [hk]), show k % 4 = k - 4 by omega_using [hk, h4]]

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
  congr 2; omega_using []

theorem expStart_M {kk : Nat} (h1 : 2 ≤ kk) (hkk : kk < 8) :
    expStart l (znM l kk) = zLd l .r10 (l.oMs + 32 * (kk - 2)) := by
  simp (disch := omega) only [expStart, znBq, znUq, znK, znT, znM, znA, hR, ↓ite_eq_right, ↓ite_eq_left]
  congr 3; omega_using []

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
    · subst b9; rw [r9₁]; exact e.rd9 d n hn (by simp only [limZ] at hdn; omega_using [hR, hN, hdn])
    by_cases b10 : r = .r10
    · subst b10; rw [r10₁]; exact e.rd10 d n hn hdn
    · have : limZ l r = 0 := by cases r <;> first | rfl | contradiction
      omega
  -- what the start reads
  have rdA : ∀ kk < 6, ∀ p < 2, ∀ t < 4,
      s₁.mem.readW (s₁.gpr .r8 + BitVec.ofNat 64 (l.D * p + 32 * kk + 8 * t)) 64 =
        BitVec.ofNat 64 (a p (l.R * t + kk)) := fun kk hkk p hp t ht => by
    rw [m₁, r8₁]; exact e.ina p hp kk (by omega_using [hR, hkk]) t ht
  have rdM : ∀ kk < 6, ∀ p < 2, ∀ t < 4,
      s₁.mem.readW (s₁.gpr .r10 + BitVec.ofNat 64 (l.D * p + (l.oMs + 32 * kk) + 8 * t)) 64 =
        BitVec.ofNat 64 (ms p (l.R * t + kk + 2)) := fun kk hkk p hp t ht => by
    rw [m₁, r10₁, ← e.inm p hp kk (by omega_using [hR, hkk]) t ht]
    exact congrArg (fun d => s₀.mem.readW (s₀.gpr .r10 + BitVec.ofNat 64 d) 64) (by omega_using [])
  have rdB : ∀ p < 2, s₁.mem.readW (s₁.gpr .r9 + BitVec.ofNat 64 (l.D * p + 0)) 64 =
      BitVec.ofNat 64 (bl p 0) := fun p hp => by
    have := e.inb p hp 0 (by omega_using [hL])
    rw [off_zero] at this
    rw [m₁, r9₁]; exact this
  obtain ⟨σ, er, hσ⟩ := run_zStart hz
  have ev : ∀ (s' : State), ZRel σ s₁ s' → ∀ n < 32, ∀ k < 8, qz s' (vreg n) k = (expStart l n).eval s₁ k :=
    fun s' hs n hn k hk => by rw [hs.reg _ k hk, vi_vreg _ hn, hσ _ hn]
  have hB0 : ∀ k < 8, (zB0 l).eval s₁ k = BitVec.ofNat 64 (bl (k / 4) 0) := fun k hk => zB0_eval rdB hk
  refine WP.mono (zrun_ok hc (ZRel.init s₁) er) fun s' hs => ⟨⟨⟨fun _ => 0, fun kk hkk k hk => ?_,
    fun kk hkk k hk => ?_, fun k hk => ?_, fun p _ => rfl, fun p _ j => ⟨by show (0 : Nat) < _; omega_using [], by show (0 : Nat) < _; omega_using []⟩⟩,
    ⟨fun kk hkk k hk => ?_, fun kk h1 hkk k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩,
    by rw [hs.gpr]; exact r8₁, by rw [hs.gpr, r9₁, Nat.mul_zero]; exact (BitVec.add_zero _).symm,
    by rw [hs.gpr]; exact r10₁, hs.mem.trans m₁, hs.rd.trans rd₁, hs.wr.trans wr₁⟩, fun k hk => ?_,
    by rw [hs.gpr]; exact cx₁, fun r h1 h2 h3 => ?_, hs.mxcsr.trans x₁⟩
  · rw [show zB l kk 0 = vreg (kk % l.R) from rfl, Nat.mod_eq_of_lt hkk, ev s' hs _ (by omega_using [hR, hkk]) k hk]
    show _ = BitVec.ofNat 64 (0 + _)
    by_cases h0 : kk = 0
    · subst h0
      rw [expStart_B0, ite_eq_left rfl]
      simp only [ZT.eval]
      rw [hB0 k hk, zLd_eval (rdA 0 (by decide)) hk, show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl, mad_lo',
        Nat.add_zero, Nat.add_zero]
      rfl
    · rw [expStart_zero hR (by omega_using [h0]) (by omega_using [hkk]), ite_eq_right h0]; rfl
  · rw [show zU l kk 0 = vreg (l.R + kk % l.R) from rfl, Nat.mod_eq_of_lt hkk, ev s' hs _ (by omega_using [hR, hkk]) k hk,
      expStart_zero hR (by omega_using [hR]) (by omega_using [hkk])]; rfl
  · rw [show zUq l ((0 + 1) % 2) = vreg (znUq l 1) from rfl, ev s' hs _ (by simp only [znUq]; omega_using [hR]) k hk,
      expStart_Uq hR]; rfl
  · rw [show zA l kk = vreg (znA l kk) from rfl, ev s' hs _ (by simp only [znA]; omega_using [hR, hkk]) k hk,
      expStart_A hR (by omega_using [hR, hkk])]
    exact zLd_eval (rdA kk (by omega_using [hR, hkk])) hk
  · rw [show zM l kk = vreg (znM l kk) from rfl, ev s' hs _ (by simp only [znM]; omega_using [hR, hkk]) k hk]
    have hp : k / 4 < 2 := by omega_using [hk]
    rcases Nat.eq_or_lt_of_le h1 with rfl | h2
    · -- row 1: the last row a quadword up, its last quadword, zero, first
      rw [expStart_M1 hR, show l.R - 1 = 5 by omega_using [hR], zLd_perm (rdM 5 (by decide)) hk]
      congr 1
      show ms (k / 4) (l.R * ((k % 4 + 3) % 4) + 5 + 2) = ms (k / 4) (l.R * (k % 4) + 1)
      rcases Nat.eq_zero_or_pos (k % 4) with h0 | h0
      · rw [show l.R * ((k % 4 + 3) % 4) + 5 + 2 = l.L + 1 by rw [h0, hR, hL],
          show l.R * (k % 4) + 1 = 1 by rw [h0]; rfl, (e.mtop _ hp).2]
        exact ((e.ok _ hp).ms1).symm
      · exact congrArg _ (by rw [hR]; omega_using [h0])
    · rw [expStart_M hR (by omega_using [h2]) (by omega_using [hR, hkk]), zLd_eval (rdM (kk - 2) (by omega_using [hR, hkk])) hk]
      exact congrArg (fun j => BitVec.ofNat 64 (ms (k / 4) j)) (by omega_using [h2])
  · rw [show zM l l.R = vreg (znM l l.R) from rfl, ev s' hs _ (by simp only [znM]; omega_using [hR]) k hk,
      expStart_M hR (by omega_using [hR]) (by omega_using [hR]), show l.R - 2 = 4 by omega_using [hR], zLd_eval (rdM 4 (by decide)) hk]
    have hp : k / 4 < 2 := by omega_using [hk]
    congr 1
    show ms (k / 4) (l.R * (k % 4) + 4 + 2) = ms (k / 4) (l.R * ((k % 4 + 1) % 4))
    rcases (by omega_using [] : k % 4 = 3 ∨ k % 4 < 3) with h3 | h3
    · rw [show l.R * (k % 4) + 4 + 2 = l.L by rw [h3, hR, hL],
        show l.R * ((k % 4 + 1) % 4) = 0 by rw [h3]; rfl, (e.mtop _ hp).1]
      exact ((e.ok _ hp).ms0).symm
    · exact congrArg _ (by rw [hR]; omega_using [h3])
  · rw [show zM l (l.R + 1) = vreg (znM l (l.R + 1)) from rfl, ev s' hs _ (by simp only [znM]; omega_using [hR]) k hk,
      expStart_M hR (by omega_using [hR]) (by omega_using [hR]), show l.R + 1 - 2 = 5 by omega_using [hR], zLd_eval (rdM 5 (by decide)) hk]
    have hp : k / 4 < 2 := by omega_using [hk]
    congr 1
    show ms (k / 4) (l.R * (k % 4) + 5 + 2) = ms (k / 4) (l.R * ((k % 4 + 1) % 4) + 1)
    rcases (by omega_using [] : k % 4 = 3 ∨ k % 4 < 3) with h3 | h3
    · rw [show l.R * (k % 4) + 5 + 2 = l.L + 1 by rw [h3, hR, hL],
        show l.R * ((k % 4 + 1) % 4) + 1 = 1 by rw [h3]; rfl, (e.mtop _ hp).2]
      exact ((e.ok _ hp).ms1).symm
    · exact congrArg _ (by rw [hR]; omega_using [h3])
  · rw [show zK l = vreg (znK l) from rfl, ev s' hs _ (by simp only [znK]; omega_using [hR]) k hk, expStart_K hR,
      zK_eval hk, ax₁]
  · rw [show zBq l (0 % 2) = vreg (znBq l 0) from rfl, ev s' hs _ (by simp only [znBq]; omega_using [hR]) k hk,
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
  refine WP.mono (zSteps_ok hz e (Nat.le_refl 3) 3 (by omega_using [hR]) (by omega_using [hR, hL]) s h hq) fun s₁ ⟨h₁, q₁, g₁, x₁⟩ => ?_
  obtain ⟨w, acc⟩ := h₁.acc
  have hin : ZIn l s₁ 3 (zo a ms) (fun p => zst l a ms bl p (l.R * 3 + 3)) (fun p => bl p (l.R * 3 + 3)) w
      ((l.R * 3 + 3 + 1) * 2 ^ 56) := ⟨acc, h₁.con, q₁, e.ok, by omega_using [hR]⟩
  refine WP.mono (zStep_ok hz (by omega_using [hR]) hin true (bn := fun _ => 0) (fun h0 => absurd h0 (by decide))
    (fun h0 => absurd h0 (by decide)) (fun _ _ => rfl) (h₁.ctx hz e (Nat.le_refl 3)))
    fun s₂ ⟨acc₂, con₂, _, k₂⟩ => ?_
  have eB : (l.R * 3 + 3 + 1) * 2 ^ 56 + 2 ^ 56 = (l.R * 3 + 4 + 1) * 2 ^ 56 := by omega_using []
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
      show qz s (vreg (znM l l.R)) _ = _ from h.con.m0 (4 * (k / 4) + (k % 4 + 3) % 4) (by omega_using [hk]),
      show (4 * (k / 4) + (k % 4 + 3) % 4) / 4 = k / 4 by omega_using [],
      show ((4 * (k / 4) + (k % 4 + 3) % 4) % 4 + 1) % 4 = k % 4 by omega_using []]
  refine WP.mono (zrun_ok (h.ctx hz e (Nat.le_refl 3)) (ZRel.init s) er) fun s' hs => ⟨fun kk hkk k hk => ?_, hs.keep⟩
  have hp : k / 4 < 2 := by omega_using [hk]
  have hm6 : (kk + 4) % l.R < 6 := by rw [hR]; exact Nat.mod_lt _ (by decide)
  have hb : qz s (vreg ((kk + 4) % l.R)) k = _ := acc.bs kk hkk k hk
  have hu : qz s (vreg (l.R + (kk + 4) % l.R)) k = _ := acc.us kk hkk k hk
  rw [hS4, show zB l kk 4 = vreg ((kk + 4) % l.R) from rfl, hs.reg _ k hk, vi_vreg _ (by omega_using [hm6]),
    hσ _ (by omega_using [hm6]), expFin, ite_eq_left (by omega_using [hR, hm6])]
  simp only [zlm, AmmD52.tot, pend]
  by_cases h0 : kk = 0
  · subst h0
    have hUp : qz s (vreg (znUq l 1)) k = _ := acc.up k hk
    have hM1 : qz s (vreg (znM l 1)) k = _ := h.con.m 1 (by decide) (by omega_using [hR]) k hk
    rw [ite_eq_left (by simp only [znU, hS4]), uFin, hS4, hS2]
    simp only [ZT.eval]
    have hwq : w (k / 4) % 2 ^ 52 = (zst l a ms bl (k / 4) l.S).qp := by rw [hS]; exact acc.wq _ hp
    rw [hb, show znU l 0 4 = l.R + (0 + 4) % l.R from rfl, hu, hUp, hT k hk, hM1,
      ite_eq_left rfl, lo_zr, mad_hi', mad_lo', ← BitVec.ofNat_add, ite_eq_left (by rw [hR]; omega_using []), ← hS,
      ← hwq, hi_modr, lo_modr]
    congr 1
    simp only [zo, Nat.add_zero]
    omega_using []
  · rw [ite_eq_right (by simp only [znU, hR]; omega_using [hR, hS, hkk, h0])]
    simp only [ZT.eval]
    rw [hb, hu, ite_eq_right h0, ← BitVec.ofNat_add, ite_eq_right (by rw [hR]; omega_using [hR, hkk, h0]), ← hS]
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
  rw [qword256_cat2 _ _ ht, qz, show (4 + t) % 2 = t % 2 by omega_using []]
  by_cases h2 : t < 2
  · rw [ite_eq_left h2, show (4 + t) / 2 = 2 by omega_using [h2]]
  · rw [ite_eq_right h2, show (4 + t) / 2 = 3 by omega_using [ht, h2]]

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
    (fun _ => by show (0 : Nat) < _; decide) l.S (by omega_using [hS])
  unfold zlm AmmD52.tot pend zst
  generalize AmmD52.steps l.L l.R (zo a ms p) (bl p) l.S ⟨fun _ => 0, fun _ => 0, 0⟩ = st at h1 h2 ⊢
  have := h1 q; have := h2 q
  have := hi_lt ((zo a ms p).ms q) st.qp
  have := lo_lt ((zo a ms p).ms (q + 1)) st.qp
  split <;> omega_arith

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
  refine WP.seq (WP.mono (zLoop_ok hz e (l.S / l.R) s₁ (by omega_using [h3]) (Nat.le_refl _)
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
    obtain ⟨_, h, c⟩ := hs.region (d := d) (n := 32) (by rw [hnl]; omega_using [hd]) (by decide)
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
      ⟨q % l.R, q / l.R, Nat.mod_lt _ (by omega_using [hR]), Nat.div_lt_of_lt_mul (by omega_using [hR, hL, hq]), (Nat.div_add_mod q l.R).symm⟩
    have hsep : ∀ x ∈ zStoreList l s₄ (zSt l), ∀ e', (e' = 32 * kk ∨ e' = l.D + 32 * kk) →
        x.1 + 32 ≤ 2 ^ 63 ∧ (x.1 = e' ∨ e' + 32 ≤ x.1 ∨ x.1 + 32 ≤ e') := fun x hx e' he' => by
      obtain ⟨k', hk', rfl | rfl⟩ := mem_zStoreList hx <;> rcases he' with rfl | rfl <;> omega
    rw [off_blk (by omega_using [hR]) hk]
    rcases (by omega_using [hnl, hp] : p = 0 ∨ p = 1) with rfl | rfl
    · rw [show l.D * 0 + (32 * kk + 8 * t) = 32 * kk + 8 * t by omega_using []]
      rw [AmmSym.word_wrList_unique B ht (by omega_using [hR, hk]) _ s₄.mem
        (v := s₄.vy (zB l kk (l.S % l.R))) ?_ (fun x hx => hsep x hx _ (.inl rfl)) (fun x hx he => ?_)]
      · show qv s₄ _ _ = _
        rw [← qz_lo s₄ _ ht, v₄ _ hk _ (by omega_using [ht]), show t / 4 = 0 by omega_using [ht], show t % 4 = t by omega_using [ht]]
      · simp only [zStoreList, zSt, List.flatMap_map, List.mem_flatMap, List.mem_range, List.mem_cons,
          List.not_mem_nil, or_false]
        exact ⟨kk, hk, .inl rfl⟩
      · obtain ⟨k', hk', rfl | rfl⟩ := mem_zStoreList hx
        · have : k' = kk := by simp only at he; omega_using [he]
          rw [this]
        · simp only at he; omega
    · rw [show l.D * 1 + (32 * kk + 8 * t) = l.D + 32 * kk + 8 * t by omega_using []]
      rw [AmmSym.word_wrList_unique B ht (by omega_using [hR, hD, hk]) _ s₄.mem
        (v := s₄.vz (zB l kk (l.S % l.R)) 3 ++ s₄.vz (zB l kk (l.S % l.R)) 2) ?_
        (fun x hx => hsep x hx _ (.inr rfl)) (fun x hx he => ?_)]
      · rw [qz_hi s₄ _ ht, v₄ _ hk _ (by omega_using [ht]), show (4 + t) / 4 = 1 by omega_using [ht], show (4 + t) % 4 = t by omega_using [ht]]
      · simp only [zStoreList, zSt, List.flatMap_map, List.mem_flatMap, List.mem_range, List.mem_cons,
          List.not_mem_nil, or_false]
        exact ⟨kk, hk, .inr rfl⟩
      · obtain ⟨k', hk', rfl | rfl⟩ := mem_zStoreList hx
        · simp only at he; omega
        · have : k' = kk := by simp only at he; omega_using [he]
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
  · have o := wrList_outN (l := l) B (o := 0) (n := l.NB) (by rw [hnl]; omega_using [hD])
      (zStoreList l s₄ (zSt l)) s₄.mem fun x hx => by
        obtain ⟨k', hk', rfl | rfl⟩ := mem_zStoreList hx
        · exact ⟨0, by omega_using [hnl], by omega_using [], by omega⟩
        · exact ⟨1, by omega_using [hnl], by omega_using [], by omega⟩
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
      VG.Proof.Bignum.Amm52.lval_succ, hg, show 52 * (n + 2) = 52 * n + 52 * 2 by omega_using [], Nat.pow_add,
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
    rcases (by omega_using [hp] : p = 0 ∨ p = 1) with rfl | rfl <;> omega_using []
  have rdS : ∀ d n, 0 < n → d + n ≤ l.nl * l.D → InRegions (s.rd ++ s.wr) (off B d) n := fun d n hn hd =>
    let ⟨_, h, c⟩ := hs.region hd hn; ⟨_, List.mem_append_right _ h, c⟩
  have e : EnvZ l (s.setReg .r10 (s.gpr .rbx)) A M Bl := by
    refine ⟨fun p hp kk hk t ht => ?_, fun p hp kk hk t ht => ?_,
      fun p hp => ⟨by show (if l.L < 2 then 0 else Mh p (l.L - 2)) = 0
                      rw [ite_eq_right (by omega_using [hL])]; exact (hmt p (by omega_using [hnl, hp])).1,
        by show (if l.L + 1 < 2 then 0 else Mh p (l.L + 1 - 2)) = 0
           rw [ite_eq_right (by omega_using [hL]), show l.L + 1 - 2 = l.L - 1 by omega_using []]; exact (hmt p (by omega_using [hnl, hp])).2⟩,
      fun p hp q hq => ?_,
      fun p hp => ⟨fun j hj => (hlt p (by omega_using [hnl, hp]) j hj).1, fun j hj => ?_, rfl, rfl⟩,
      fun p hp q hq => (hlt p (by omega_using [hnl, hp]) q hq).2.1,
      fun d n hn hd => ?_, fun d n hn hd => ?_, fun d n hn hd => ?_⟩
    · have := hDp p hp
      rw [RegUpd.mem_setReg, RegUpd.gpr_setReg_of_ne _ _ (by decide), r8₃, off_add]
      show _ = BitVec.ofNat 64 (limb l s.mem B (l.D * p + a) (l.R * t + kk))
      rw [ofNat_toNat64, off_blk (by omega_using [hR]) hk]
      exact congrArg (fun d => s.mem.readW (off B d) 64) (by omega_using [])
    · have := hDp p hp
      rw [RegUpd.mem_setReg, RegUpd.gpr_setReg_self, hB]
      show s.mem.readW (off B _) 64 =
        BitVec.ofNat 64 (if l.R * t + kk + 2 < 2 then 0 else limb l s.mem B (l.D * p + l.oMs) (l.R * t + kk + 2 - 2))
      rw [ite_eq_right (by omega_using []), Nat.add_sub_cancel, ofNat_toNat64, off_blk (by omega_using [hR]) hk]
      exact congrArg (fun d => s.mem.readW (off B d) 64) (by omega_using [])
    · rw [RegUpd.mem_setReg, RegUpd.gpr_setReg_of_ne _ _ (by decide), r9₃, off_add]
      show _ = BitVec.ofNat 64 (limb l s.mem B (l.D * p + b) q)
      rw [ofNat_toNat64]
      exact congrArg (fun d => s.mem.readW (off B d) 64) (by omega_using [])
    · show (if j < 2 then 0 else Mh p (j - 2)) < 2 ^ 52
      split
      · decide
      · exact (hlt p (by omega_using [hnl, hp]) (j - 2) (by omega_using [hj])).2.2
    · rw [RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_setReg_of_ne _ _ (by decide), r8₃, off_add]
      exact rdS _ n hn (by rw [hnl]; omega_using [ha, hd])
    · rw [RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_setReg_of_ne _ _ (by decide), r9₃, off_add]
      exact rdS _ n hn (by rw [hnl]; omega_using [hb, hd])
    · rw [RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_setReg_self, hB]
      exact rdS _ n hn (by rw [hnl]; omega_using [hD1, hd])
  have hs₃ : Scr s (off B o) (l.D * (l.nl - 1) + l.NB) := hs.sub (by rw [hnl]; omega_using [ho]) (by omega_using [hN])
  refine WP.mono (ammCoreZ_ok hz e r11₃ hs₃) fun s' ⟨hw, hf, hg, _, hrd, hwr, hx⟩ => ?_
  refine ⟨fun p hp => ?_, (hf.rebaseN (by rw [hnl]; omega_using [ho, hD2])).out2, hg, hrd, hwr, hx⟩
  have hp2 : p < 2 := by omega_using [hnl, hp]
  have hq : ∀ j < l.L, limb l s'.mem B (l.D * p + o) j = carried (zlm l A M Bl p) j := fun j hj => by
    have := hw p hp j hj
    simp only [word, VG.Proof.Bignum.off_off] at this
    show (s'.mem.readW (off B _) 64).toNat = _
    rw [show l.D * p + o + l.off j = o + (l.D * p + l.off j) by omega_using [], this, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := carried_lt (zlm l A M Bl p) j; omega_using [this])]
  have hv : val52 l s'.mem B (l.D * p + o) = lval (carried (zlm l A M Bl p)) l.L := by
    unfold val52; exact lval_congr hq
  refine ⟨fun j hj => (hq j hj) ▸ carried_lt _ j, fun X hX hBv hfit => ?_⟩
  -- the modulus plus one is the number at `oMs`, two limbs up
  have hMv : lval (M p) l.L = X + 1 := by
    have h1 := lval_up2 (f := Mh p) (g := M p) rfl rfl (fun j => by
      show (if j + 2 < 2 then 0 else Mh p (j + 2 - 2)) = Mh p j
      rw [ite_eq_right (by omega_using []), Nat.add_sub_cancel]) (l.L - 2)
    have h2 := lval_top2 (f := Mh p) (n := l.L - 2) (hmt p hp).1
      (by rw [show l.L - 2 + 1 = l.L - 1 by omega_using [hL]]; exact (hmt p hp).2)
    rw [show l.L - 2 + 2 = l.L by omega_using [hL]] at h1 h2
    exact h1.trans (by rw [← h2]; exact hX)
  have he := AmmD52.steps_val (R := l.R) (N := l.L) (by omega_using [hR]) (by omega_using [hL]) (by rw [hL, hR]) (e.ok p hp2)
    (b := Bl p) (fun i hi => (hlt p hp i hi).2.1) ⟨fun _ => 0, fun _ => 0, 0⟩ hMv l.S (by omega_using [hL, hS])
  have z : lval (AmmD52.tot l.R ⟨A p, M p⟩ ⟨fun _ => 0, fun _ => 0, 0⟩) l.L = 0 := by
    rw [lval_congr (L' := fun j => (fun _ : Nat => 0) j * 0) fun j _ => tot_init l.R _ j,
      VG.Proof.Bignum.Amm52.lval_mul, Nat.mul_zero]
  have hQ : lval (AmmD52.stepsQ l.L l.R ⟨A p, M p⟩ (Bl p) ⟨fun _ => 0, fun _ => 0, 0⟩) l.S < 2 ^ (52 * l.S) :=
    lval_lt fun j _ => AmmD52.stepsQ_lt _ _ _ _ _ _
  rw [z, Nat.zero_add] at he
  have hbS : lval (Bl p) l.L = lval (Bl p) l.S := lval_trunc _ (by omega_using [hL, hS]) hBv
  change lval (zlm l A M Bl p) l.L * _ = lval (A p) l.L * lval (Bl p) l.S + X * _ at he
  change lval (A p) l.L * lval (Bl p) l.L + X * _ < _ at hfit
  rw [hbS] at hfit
  generalize lval (AmmD52.stepsQ l.L l.R ⟨A p, M p⟩ (Bl p) ⟨fun _ => 0, fun _ => 0, 0⟩) l.S = Q at he hQ
  have hz' : lval (zlm l A M Bl p) l.L < 2 ^ (52 * l.L) := by
    have h1 : X * Q ≤ X * 2 ^ (52 * l.S) := Nat.mul_le_mul_left _ (Nat.le_of_lt hQ)
    refine Nat.lt_of_mul_lt_mul_left (a := 2 ^ (52 * l.S)) ?_
    rw [Nat.mul_comm]
    generalize 2 ^ (52 * l.S) * 2 ^ (52 * l.L) = T at hfit ⊢
    omega_using [he, h1, hfit]
  have hcv := carried_val (zlm l A M Bl p) l.L
  rw [Amm52N.carryIn_zero hz', Nat.zero_mul, Nat.add_zero] at hcv
  refine ⟨Q, hQ, ?_⟩
  rw [hv, hcv]
  show lval (zlm l A M Bl p) l.L * _ = lval (A p) l.L * lval (Bl p) l.L + X * Q
  rw [hbS]; exact he

end VG.Proof.Bignum.X86_64.Ifma
