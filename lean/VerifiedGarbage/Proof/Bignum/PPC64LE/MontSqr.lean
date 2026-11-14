module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRows
import VerifiedGarbage.Proof.Framework.PPC64LE.Carry
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFios
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.AddrArith

-- separate module: it builds in parallel with `MontCore`'s other imports, and a change to `MontCore` does not re-check it.

/-!
# Montgomery multiplication on PPC64LE: the kernel's squaring

The kernel's squaring (`sqr8`) computes `S = a²` into `2 w` words (the
triangle `Σ_{i<j} aᵢ aⱼ 2^(64 (i + j))`, by blocks of eight words, then the
doubling with the squares of the words), then reduces it, `T = (S + U m) /
2^(64 w)`, by blocks of eight words of `S`.

Every row is one word times eight (`row8`): two carry chains of eight words
(`chain_ok`, by induction over the words), the low words of the products into
the window and their high words one word down, with the word above the
window in `r4` and CA. `row_arith8` puts them together: `2⁶⁴ V' + o = V + x
P` for the window's value `V` (`Vw`), the word `o` that drops out, and the
eight words `P` the row multiplies.
-/

@[expose] public section

-- The window's top words weigh `2^448` and `2^512`.
set_option exponentiation.threshold 1024

namespace VG.Proof.Bignum.PPC64LE.Sqr

open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Proof.Mont VG.Impl.Bignum.PPC64LE
open VG.Proof.Bignum.PPC64LE (Scr Keep off_add gpr_write)
open VG.Proof.Bignum.PPC64LE.Mont4 (W1 W1.write W1.writeCarry wp_ld wp_st wp_write wp_addi wp_mul wp_mulhu wp_adde wp_addc
  wp_addze psum psum_congr rv pv wp_prod rv_lt rv_congr lo_hi hiw flatMap_range_succ psum_shift row0_zero)

/-! ## A chain of eight words -/

/-- Word `j` of a chain (`chain8`). -/
def cstep (hi : Bool) (x : Reg) (p dst src : Nat → Reg) (j : Nat) : List Instr :=
  if p j = .r0 then [if j = 0 then Instr.addc (dst j) (src j) .r0 else Instr.addze (dst j) (src j)]
  else [(if hi then Instr.mulhu else Instr.mul) .r30 (p j) x, (if j = 0 then Instr.addc else Instr.adde) (dst j) (src j) .r30]

theorem chain8_eq (hi : Bool) (x : Reg) (p dst src : Nat → Reg) :
    chain8 hi x p dst src = (List.range 8).flatMap (cstep hi x p dst src) := rfl

/-- What a chain's registers must be: the destinations distinct, none read
after it is written, none `r0`, `x` or the temporary `r30`. -/
def CRegs (x : Reg) (p dst src : Nat → Reg) : Prop :=
  x ≠ .r30 ∧ (∀ j < 8, p j ≠ .r30 ∧ src j ≠ .r30 ∧ dst j ≠ .r30 ∧ dst j ≠ x ∧ dst j ≠ .r0) ∧
    (∀ j < 8, ∀ k < 8, dst j ≠ p k) ∧ ∀ j < 8, ∀ k < 8, j < k → dst j ≠ src k ∧ dst j ≠ dst k

instance (x : Reg) (p dst src : Nat → Reg) : Decidable (CRegs x p dst src) := by
  unfold CRegs; exact inferInstance

/-- A product's low or high word into `d`. -/
theorem wp_prodD {is : List Instr} {s : State} {Q : State → Prop} (hi : Bool) (d a b : Reg)
    (k : ∀ t, W1 s t d → (t.gpr d).toNat = pv hi (s.gpr a) (s.gpr b) → t.ca = s.ca → WP isa (.block is) t Q) :
    WP isa (.block ((if hi then Instr.mulhu else Instr.mul) d a b :: is)) s Q := by
  cases hi
  · exact wp_mul fun t w e c => k t w (by rw [e]; rfl) c
  · exact wp_mulhu fun t w e c => k t w (by rw [e]; rfl) c

theorem pv_zero (hi : Bool) (x : BitVec 64) : pv hi 0 x = 0 := by
  cases hi <;> simp [pv, hiw]

theorem chain_notin {dst : Nat → Reg} {n : Nat} {r : Reg} (h30 : r ≠ .r30) (hd : ∀ j < n, dst j ≠ r) : r ∉ Reg.r30 :: (List.range n).map dst := by
  intro h
  rcases List.mem_cons.mp h with h | h
  · exact h30 h
  · obtain ⟨j, hj, e⟩ := List.mem_map.mp h
    exact hd j (List.mem_range.mp hj) e

/-- The first `n` words of a chain (`cstep`): `dst := src + (lo or hi) (p x)` as
a `64 n`-bit sum, the carry out in CA (and in, for `n = 0`). -/
theorem chain_ok {hi : Bool} {x : Reg} {p dst src : Nat → Reg} (hr : CRegs x p dst src) :
    ∀ (n : Nat) {s : State}, n ≤ 8 → s.gpr .r0 = 0 →
    WP isa (.block ((List.range n).flatMap (cstep hi x p dst src))) s fun t =>
      (rv t dst n + 2 ^ (64 * n) * t.ca.toNat = rv s src n + psum (fun j => pv hi (s.gpr (p j)) (s.gpr x)) n +
          (if n = 0 then s.ca.toNat else 0) ∧
        (0 < n → (t.gpr (dst 0)).toNat = ((s.gpr (src 0)).toNat + pv hi (s.gpr (p 0)) (s.gpr x)) % 2 ^ 64) ∧
        t.mem = s.mem) ∧ Keep (.r30 :: (List.range n).map dst) s t
  | 0, s, _, _ => WP.block_nil ⟨⟨by simp [rv, psum], fun h => absurd h (by decide), rfl⟩, Keep.refl _ _⟩
  | n + 1, s, hn, h0 => by
    obtain ⟨hx, hA, hP, hS⟩ := hr
    have an := hA n (by omega_using [hn])
    rw [flatMap_range_succ, WP.block_append_iff]
    refine WP.mono (chain_ok ⟨hx, hA, hP, hS⟩ n (by omega_using [hn]) h0) fun t ⟨⟨e, l, m⟩, k⟩ => ?_
    -- What word `n` reads: as on entry.
    have g : ∀ r, r ≠ .r30 → (∀ j < n, dst j ≠ r) → t.gpr r = s.gpr r := fun r h1 h2 =>
      k.gpr r (chain_notin h1 h2)
    have gs : t.gpr (src n) = s.gpr (src n) := g _ an.2.1 fun j hj => (hS j (by omega_using [hn, hj]) n (by omega_using [hn]) hj).1
    have gx : t.gpr x = s.gpr x := g _ hx fun j hj => (hA j (by omega_using [hn, hj])).2.2.2.1
    have gp : t.gpr (p n) = s.gpr (p n) := g _ an.1 fun j hj => hP j (by omega_using [hn, hj]) n (by omega_using [hn])
    have g0 : t.gpr .r0 = 0 := by
      rw [g _ (by decide) fun j hj => (hA j (by omega_using [hn, hj])).2.2.2.2]; exact h0
    -- Word `n`.
    have post : ∀ (u : State), (∀ r, r ≠ dst n → r ≠ .r30 → u.gpr r = t.gpr r) →
        Keep [.r30, dst n] t u → u.mem = t.mem →
        (u.gpr (dst n)).toNat + 2 ^ 64 * u.ca.toNat = (s.gpr (src n)).toNat + pv hi (s.gpr (p n)) (s.gpr x) +
          (if n = 0 then 0 else t.ca.toNat) →
        (rv u dst (n + 1) + 2 ^ (64 * (n + 1)) * u.ca.toNat = rv s src (n + 1) +
            psum (fun j => pv hi (s.gpr (p j)) (s.gpr x)) (n + 1) + (if n + 1 = 0 then s.ca.toNat else 0) ∧
          (0 < n + 1 → (u.gpr (dst 0)).toNat = ((s.gpr (src 0)).toNat + pv hi (s.gpr (p 0)) (s.gpr x)) % 2 ^ 64) ∧
          u.mem = s.mem) ∧ Keep (.r30 :: (List.range (n + 1)).map dst) s u := fun u gu ku mu eu => by
      have prev : rv u dst n = rv t dst n := rv_congr n fun j hj =>
        gu _ (hS j (by omega_using [hn, hj]) n (by omega_using [hn]) hj).2 (hA j (by omega_using [hn, hj])).2.2.1
      refine ⟨⟨?_, fun _ => ?_, by rw [mu, m]⟩, (k.trans ku).mono fun r hr => ?_⟩
      · show rv u dst n + 2 ^ (64 * n) * (u.gpr (dst n)).toNat + _ = rv s src n + 2 ^ (64 * n) * (s.gpr (src n)).toNat +
          (psum _ n + 2 ^ (64 * n) * pv hi (s.gpr (p n)) (s.gpr x)) + _
        rw [prev, pow64_succ]
        rcases Nat.eq_zero_or_pos n with rfl | hn0
        · simp only [rv, psum, ↓reduceIte, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero,
            Nat.mul_one, Nat.reduceEqDiff] at e eu ⊢
          omega_using [eu]
        · simp only [show ¬n = 0 by omega_using [hn0], show ¬n + 1 = 0 by omega_using [], ↓reduceIte, Nat.add_zero] at e eu ⊢
          have := congrArg (2 ^ (64 * n) * ·) eu
          simp only [Nat.mul_add] at this
          grind
      · rcases Nat.eq_zero_or_pos n with rfl | hn0
        · simp only [↓reduceIte, Nat.add_zero] at eu
          have := (u.gpr (dst 0)).isLt
          omega_using [eu]
        · rw [gu _ (hS 0 (by omega_using []) n (by omega_using [hn]) hn0).2 (hA 0 (by omega_using [])).2.2.1]
          exact l hn0
      · rcases List.mem_append.mp hr with h | h
        · exact List.mem_cons.mpr (by
            rcases List.mem_cons.mp h with h | h
            · exact .inl h
            · exact .inr (by rw [List.range_succ, List.map_append]; exact List.mem_append_left _ h))
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (by rw [List.range_succ, List.map_append]; simp)
    unfold cstep
    by_cases hp : p n = .r0
    · simp only [hp, ↓reduceIte]
      have pz : pv hi (s.gpr (p n)) (s.gpr x) = 0 := by rw [← gp, hp, g0, pv_zero]
      by_cases hn0 : n = 0
      · subst hn0
        simp only [↓reduceIte]
        refine wp_addc fun u w eu => WP.block_nil (post u (fun r h1 _ => w.gpr r h1) (w.keep.mono (by simp)) w.mem ?_)
        rw [gs, g0] at eu; rw [pz]; simpa using eu
      · simp only [hn0, ↓reduceIte]
        refine wp_addze fun u w eu => WP.block_nil (post u (fun r h1 _ => w.gpr r h1) (w.keep.mono (by simp)) w.mem ?_)
        rw [gs] at eu; rw [pz]; simp only [hn0, ↓reduceIte]; omega_using [eu]
    · simp only [hp, ↓reduceIte]
      refine wp_prodD hi .r30 (p n) x fun t₁ w₁ e₁ c₁ => ?_
      have g₁ : ∀ r, r ≠ .r30 → t₁.gpr r = t.gpr r := fun r h => w₁.gpr r h
      by_cases hn0 : n = 0
      · subst hn0
        simp only [↓reduceIte]
        refine wp_addc fun u w eu => WP.block_nil (post u (fun r h1 h2 => (w.gpr r h1).trans (g₁ r h2))
          ((w₁.keep.trans w.keep).mono (by simp)) (w.mem.trans w₁.mem) ?_)
        rw [g₁ _ an.2.1, gs, e₁, gp, gx] at eu; simpa using eu
      · simp only [hn0, ↓reduceIte]
        refine wp_adde fun u w eu => WP.block_nil (post u (fun r h1 h2 => (w.gpr r h1).trans (g₁ r h2))
          ((w₁.keep.trans w.keep).mono (by simp)) (w.mem.trans w₁.mem) ?_)
        rw [g₁ _ an.2.1, gs, e₁, gp, gx, c₁] at eu; simp only [hn0, ↓reduceIte]; exact eu

/-! ## A row -/

/-- What a row's chains add up to, from the window `RA` and the word above it
`CY1` (with CA clear): the low chain (`RL`, its carry `c2` into `CY2`), the
window moved down (`R7`, its words `1` to `7`) and the high chain (`RH`,
carry `c4`): `2⁶⁴ V' + o = V + P x`, `Q = 2^448`. -/
theorem rowCore_arith {Q RA RL c2 L CY1 CY2 c3 A0 R7 RH c4 H Px : Nat}
    (elo : RL + 2 ^ 64 * Q * c2 = RA + L) (e₃ : CY2 + 2 ^ 64 * c3 = CY1 + c2) (hCY1 : CY1 ≤ 3) (hc2 : c2 ≤ 1)
    (hCY2 : CY2 < 2 ^ 64) (hRL : RL = A0 + 2 ^ 64 * R7) (ehi : RH + 2 ^ 64 * Q * c4 = R7 + Q * CY2 + H)
    (lh : L + 2 ^ 64 * H = Px) :
    2 ^ 64 * (RH + 2 ^ 64 * Q * c4) + A0 = RA + 2 ^ 64 * Q * CY1 + Px := by
  have c3z : c3 = 0 := by omega
  subst c3z
  grind

/-- The low words and the high words of the products of `x` with `n` words. -/
theorem lohi_n (s : State) (p : Nat → Reg) (x : BitVec 64) : ∀ n,
    psum (fun j => pv false (s.gpr (p j)) x) n + 2 ^ 64 * psum (fun j => pv true (s.gpr (p j)) x) n =
      rv s p n * x.toNat
  | 0 => by simp [psum, rv]
  | n + 1 => by
    have ih := lohi_n s p x n
    have hl := congrArg (2 ^ (64 * n) * ·) (lo_hi (s.gpr (p n)) x)
    simp only [psum, rv, pv, Bool.false_eq_true, ↓reduceIte, hiw] at ih hl ⊢
    grind

/-- The window's value: its eight words, and the word above it, `st` and CA. -/
def Vw (s : State) (st : Reg) : Nat := rv s sacc 8 + 2 ^ 64 * 2 ^ (64 * 7) * ((s.gpr st).toNat + s.ca.toNat)

theorem psum8 (f : Nat → Nat) : psum f 8 = psum f 7 + 2 ^ (64 * 7) * f 7 := by rw [psum]

theorem pow512 : (2 : Nat) ^ (64 * 8) = 2 ^ 64 * 2 ^ (64 * 7) := (pow64_succ 7 : _)

theorem rv8_shift (s : State) : rv s sacc 8 = (s.gpr (sacc 0)).toNat + 2 ^ 64 * rv s (fun c => sacc (c + 1)) 7 :=
  psum_shift _ 7

theorem rv8_sshift (s : State) :
    rv s sshift 8 = rv s (fun c => sacc (c + 1)) 7 + 2 ^ (64 * 7) * (s.gpr .r4).toNat := by
  rw [rv, psum8]
  exact congrArg (· + _) (psum_congr fun j hj => by simp only [sshift, hj, ↓reduceIte])

/-- The registers of a row's chains. -/
def RowRegs (x : Reg) (p : Nat → Reg) : Prop :=
  CRegs x p sacc sacc ∧ CRegs x p sacc sshift ∧ x ≠ .r4 ∧ (∀ j < 8, p j ≠ .r4)

instance (x : Reg) (p : Nat → Reg) : Decidable (RowRegs x p) := by unfold RowRegs; exact inferInstance

/-- The store of the window's low word at `k(P)` (`some (P, k)`), or none. -/
def outStore (o : Option (Reg × Nat)) : List Instr := o.elim [] fun (P, k) => [.store .d (sacc 0) P k]

/-- A row's chains, from CA clear (`rowCore`), with the store of the word that
drops out (`outStore`) or not: `2⁶⁴ V' + w = W + 2⁵¹² r4 + P x` for the
window `W` and the eight words `P`, and `w` the window's low word plus that
of `p₀ x`. -/
theorem rowCore_ok {x : Reg} {p : Nat → Reg} {u : State} (o : Option (Reg × Nat))
    (hr : RowRegs x p) (h0 : u.gpr .r0 = 0) (hca : u.ca = false) (h4 : (u.gpr .r4).toNat ≤ 3)
    (hout : ∀ P k, o = some (P, k) → P ≠ .r0 ∧ P ≠ .r30 ∧ P ≠ .r4 ∧ (∀ j < 8, sacc j ≠ P) ∧ k < 2 ^ 15 ∧
      k % 4 = 0 ∧ InRegions u.wr (u.gpr P + BitVec.ofNat 64 k) 8) :
    WP isa (.block (chain8 false x p sacc sacc ++ (.addze .r4 .r4 :: (outStore o ++ chain8 true x p sacc sshift)))) u
      fun t =>
      (∃ w : BitVec 64, w.toNat = ((u.gpr (sacc 0)).toNat + pv false (u.gpr (p 0)) (u.gpr x)) % 2 ^ 64 ∧
        t.mem = (o.elim u.mem fun (P, k) => u.mem.writeW (u.gpr P + BitVec.ofNat 64 k) w) ∧
        2 ^ 64 * Vw t .r0 + w.toNat = rv u sacc 8 + 2 ^ 64 * 2 ^ (64 * 7) * (u.gpr .r4).toNat +
          rv u p 8 * (u.gpr x).toNat) ∧
      Keep (.r30 :: .r4 :: (List.range 8).map sacc) u t := by
  obtain ⟨hlo, hhi, hx4, hp4⟩ := hr
  rw [chain8_eq, chain8_eq, WP.block_append_iff]
  refine WP.mono (chain_ok hlo 8 (Nat.le_refl _) h0) fun t₁ ⟨⟨e₁, l₁, m₁⟩, k₁⟩ => ?_
  have g₁ : ∀ r, r ≠ .r30 → (∀ j < 8, sacc j ≠ r) → t₁.gpr r = u.gpr r := fun r h1 h2 =>
    k₁.gpr r (chain_notin h1 h2)
  refine wp_addze fun t₂ w₂ e₂ => ?_
  have g4 : t₁.gpr .r4 = u.gpr .r4 := g₁ _ (by decide) (by decide)
  rw [g4] at e₂
  -- After the store, or none: the high chain.
  have hi : ∀ (v : State), Keep [] t₂ v → v.ca = t₂.ca →
      v.mem = (o.elim t₂.mem fun (P, k) => t₂.mem.writeW (u.gpr P + BitVec.ofNat 64 k) (t₂.gpr (sacc 0))) →
      WP isa (.block ((List.range 8).flatMap (cstep true x p sacc sshift))) v fun t =>
        (∃ w : BitVec 64, w.toNat = ((u.gpr (sacc 0)).toNat + pv false (u.gpr (p 0)) (u.gpr x)) % 2 ^ 64 ∧
          t.mem = (o.elim u.mem fun (P, k) => u.mem.writeW (u.gpr P + BitVec.ofNat 64 k) w) ∧
          2 ^ 64 * Vw t .r0 + w.toNat = rv u sacc 8 + 2 ^ 64 * 2 ^ (64 * 7) * (u.gpr .r4).toNat +
            rv u p 8 * (u.gpr x).toNat) ∧
        Keep (.r30 :: .r4 :: (List.range 8).map sacc) u t := by
    intro v kv cv mv
    have gv : ∀ r, r ≠ .r4 → r ≠ .r30 → (∀ j < 8, sacc j ≠ r) → v.gpr r = u.gpr r := fun r a b c => by
      rw [kv.gpr _ (by simp), w₂.gpr _ a, g₁ _ b c]
    refine WP.mono (chain_ok hhi 8 (Nat.le_refl _) (by rw [gv _ (by decide) (by decide) (by decide), h0]))
      fun t ⟨⟨e₃, _, m₃⟩, k₃⟩ => ⟨⟨t₂.gpr (sacc 0), ?_, ?_, ?_⟩, ?_⟩
    · rw [w₂.gpr _ (by decide)]
      exact l₁ (by decide)
    · rw [m₃, mv, w₂.mem, m₁]
    · have pv8 : ∀ hi, psum (fun j => pv hi (v.gpr (p j)) (v.gpr x)) 8 =
          psum (fun j => pv hi (u.gpr (p j)) (u.gpr x)) 8 := fun hi => psum_congr fun j hj => by
        rw [gv _ (hp4 j hj) (hlo.2.1 j hj).1 fun k hk => hlo.2.2.1 k hk j hj,
          gv _ hx4 hlo.1 fun k hk => (hlo.2.1 k hk).2.2.2.1]
      rw [pv8] at e₃
      have hrs : rv v sshift 8 = rv t₁ (fun c => sacc (c + 1)) 7 + 2 ^ (64 * 7) * (t₂.gpr .r4).toNat := by
        rw [rv8_sshift, kv.gpr .r4 (by simp)]
        exact congrArg (· + _) (rv_congr 7 fun j hj => by rw [kv.gpr _ (by simp), w₂.gpr _ (by revert j; decide)])
      rw [hrs] at e₃
      have h0t : t.gpr .r0 = 0 := by
        rw [k₃.gpr _ (by decide), gv _ (by decide) (by decide) (by decide), h0]
      have a0 : t₂.gpr (sacc 0) = t₁.gpr (sacc 0) := w₂.gpr _ (by decide)
      rw [hca, pow512] at e₁
      rw [pow512] at e₃
      unfold Vw
      rw [h0t, show (0 : BitVec 64).toNat = 0 from rfl, Nat.zero_add, a0]
      exact rowCore_arith e₁ e₂ h4 (Bool.toNat_le _) (t₂.gpr .r4).isLt (rv8_shift t₁) e₃ (lohi_n u p (u.gpr x) 8)
    · exact ((k₁.trans w₂.keep).trans (kv.trans k₃)).mono fun r hr => by
        simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil, or_false] at hr ⊢
        grind
  rcases o with _ | ⟨P, k⟩
  · exact hi t₂ (Keep.refl _ _) rfl rfl
  · obtain ⟨hP0, hP30, hP4, hPa, hk, hk4, hin⟩ := hout P k rfl
    have gP : t₂.gpr P = u.gpr P := by rw [w₂.gpr _ hP4, g₁ _ hP30 hPa]
    show WP isa (.block (.store .d (sacc 0) P k :: _)) t₂ _
    refine wp_st hP0 ⟨hk, hk4⟩ (by rw [gP]) (by rw [w₂.wr, k₁.wr]; exact hin) fun v kv mv cv =>
      hi v kv cv (by rw [mv]; rfl)

/-- A row's first step, `r4 := start + CA`: CA clear, and the window's value
kept. -/
theorem row_start {s : State} {st : Reg} {is : List Instr} {Q : State → Prop} (hst : (s.gpr st).toNat ≤ 2)
    (k : ∀ u, W1 s u .r4 → u.ca = false → (u.gpr .r4).toNat ≤ 3 →
      rv u sacc 8 + 2 ^ 64 * 2 ^ (64 * 7) * (u.gpr .r4).toNat = Vw s st → WP isa (.block is) u Q) :
    WP isa (.block (.addze .r4 st :: is)) s Q :=
  wp_addze fun u w e => by
    have hc := Bool.toNat_le s.ca
    have hu := (u.gpr .r4).isLt
    have hca : u.ca.toNat = 0 := by omega_using [hst, e, hc]
    refine k u w (by cases h : u.ca <;> simp_all) (by omega_using [hst, e, hc]) ?_
    have : rv u sacc 8 = rv s sacc 8 := rv_congr 8 fun j hj => w.gpr _ (by revert j; decide)
    unfold Vw
    rw [this, show (u.gpr .r4).toNat = (s.gpr st).toNat + s.ca.toNat by omega_using [hst, e, hc]]

theorem triRow0_regs : ∀ r < 8, RowRegs (smr r) (fun c => if c < r then smr c else .r0) := by decide

theorem row_regs : RowRegs .r3 smr := by decide

/-- The start register of row `r`: `r4` for the first row of a group, after a
boundary, `r0` (CA alone) for the others. -/
def rstart (r : Nat) : Reg := if r = 0 then .r4 else .r0

theorem rstart_ok (r : Nat) : rstart r ≠ .r4 → rstart r = .r0 := by
  unfold rstart; split <;> simp

/-- Row `r` within a block (`triRow0 r`), `r12` at `dT`: the window's low word
stored at `dT + 8 r`, and `2⁶⁴ V' + w = V + P x` for the block's words `P`
below `r` and `x` its word `r`. -/
theorem triRow0_ok {s : State} {B : Addr} {Z dT r : Nat} (hs : Scr s B Z) (h0 : s.gpr .r0 = 0) (hr : r < 8)
    (h12 : s.gpr .r12 = off B dT) (hT : dT + 8 * r + 8 ≤ Z) (hst : (s.gpr (rstart r)).toNat ≤ 2) :
    WP isa (.block (triRow0 r)) s fun t =>
      (∃ w : BitVec 64, t.mem = s.mem.writeW (off B (dT + 8 * r)) w ∧
        2 ^ 64 * Vw t .r0 + w.toNat = Vw s (rstart r) +
          rv s (fun c => if c < r then smr c else .r0) 8 * (s.gpr (smr r)).toNat) ∧
      Keep (.r30 :: .r4 :: (List.range 8).map sacc) s t := by
  unfold triRow0 row8
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine row_start hst fun u w ca h4 hv => ?_
  have hu : ∀ r', r' ≠ .r4 → u.gpr r' = s.gpr r' := fun r' h => w.gpr r' h
  show WP isa (.block (chain8 false _ _ sacc sacc ++ (.addze .r4 .r4 :: (outStore (some (.r12, 8 * r)) ++
    chain8 true _ _ sacc sshift)))) u _
  refine WP.mono (rowCore_ok (some (.r12, 8 * r)) (triRow0_regs r hr) (by rw [hu _ (by decide), h0]) ca h4
    fun P k e => ?_) fun t ⟨⟨wv, _, mt, et⟩, kt⟩ => ⟨⟨wv, ?_, ?_⟩, ?_⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    refine ⟨by decide, by decide, by decide, by decide, by omega_using [hr], by omega_using [], ?_⟩
    rw [hu _ (by decide), h12, off_add, w.wr]
    exact hs.st (by omega_using [hT])
  · rw [mt]; simp only [Option.elim]; rw [hu _ (by decide), h12, off_add, w.mem]
  · have hm : ∀ r < 8, ∀ j < 8, (if j < r then smr j else .r0) ≠ .r4 := by decide
    have hs4 : ∀ r < 8, smr r ≠ .r4 := by decide
    rw [et, show rstart r = (if r = 0 then .r4 else .r0) from rfl, ← hv,
      rv_congr 8 fun j hj => hu _ (hm r hr j hj), hu _ (hs4 r hr)]
  · exact (w.keep.trans kt).mono (by simp)

/-- A row whose word is loaded from `kx(PX)` into `r3` (`triRow`, `redRow`), the
window's low word stored at `ko(PO)`. -/
theorem rowLd_ok {s : State} {B : Addr} {Z dX dO kx ko : Nat} {PX PO : Reg} {st : Reg} (hs : Scr s B Z)
    (h0 : s.gpr .r0 = 0) (hX : s.gpr PX = off B dX) (hO : s.gpr PO = off B dO) (hdx : dX + kx + 8 ≤ Z)
    (hdo : dO + ko + 8 ≤ Z) (hkx : kx < 2 ^ 15 ∧ kx % 4 = 0) (hko : ko < 2 ^ 15 ∧ ko % 4 = 0)
    (hPX : PX ≠ .r0 ∧ PX ≠ .r4) (hPO : PO ≠ .r0 ∧ PO ≠ .r30 ∧ PO ≠ .r4 ∧ PO ≠ .r3 ∧ ∀ j < 8, sacc j ≠ PO)
    (hst : (s.gpr st).toNat ≤ 2) :
    WP isa (.block (.addze .r4 st :: .load .d .r3 PX kx :: (chain8 false .r3 smr sacc sacc ++
        (.addze .r4 .r4 :: .store .d (sacc 0) PO ko :: chain8 true .r3 smr sacc sshift)))) s fun t =>
      (∃ w : BitVec 64, t.mem = s.mem.writeW (off B (dO + ko)) w ∧
        2 ^ 64 * Vw t .r0 + w.toNat = Vw s st + rv s smr 8 * (word s.mem B (dX + kx)).toNat) ∧
      Keep (.r3 :: .r30 :: .r4 :: (List.range 8).map sacc) s t := by
  refine row_start hst fun u w ca h4 hv => ?_
  have hu : ∀ r', r' ≠ .r4 → u.gpr r' = s.gpr r' := fun r' h => w.gpr r' h
  refine wp_ld hPX.1 hkx (by rw [hu _ hPX.2, hX, off_add]) ((hs.congr w.wr).ld (by omega_using [hdx])) fun u₁ w₁ e₁ c₁ => ?_
  have hu₁ : ∀ r', r' ≠ .r4 → r' ≠ .r3 → u₁.gpr r' = s.gpr r' := fun r' a b => (w₁.gpr r' b).trans (hu r' a)
  show WP isa (.block (chain8 false _ _ sacc sacc ++ (.addze .r4 .r4 :: (outStore (some (PO, ko)) ++
    chain8 true _ _ sacc sshift)))) u₁ _
  refine WP.mono (rowCore_ok (some (PO, ko)) row_regs (by rw [hu₁ _ (by decide) (by decide), h0])
    (by rw [c₁, ca]) (by rw [w₁.gpr _ (by decide)]; exact h4) fun P k e => ?_) fun t ⟨⟨wv, _, mt, et⟩, kt⟩ =>
      ⟨⟨wv, ?_, ?_⟩, ?_⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    refine ⟨hPO.1, hPO.2.1, hPO.2.2.1, hPO.2.2.2.2, hko.1, hko.2, ?_⟩
    rw [hu₁ _ hPO.2.2.1 hPO.2.2.2.1, hO, off_add, w₁.wr, w.wr]
    exact hs.st (by omega_using [hdo])
  · rw [mt]; simp only [Option.elim]; rw [hu₁ _ hPO.2.2.1 hPO.2.2.2.1, hO, off_add, w₁.mem, w.mem]
  · have hm : ∀ j < 8, smr j ≠ .r4 ∧ smr j ≠ .r3 := by decide
    rw [et, ← hv, rv_congr 8 fun j hj => w₁.gpr _ (by revert j; decide), rv_congr 8 fun j hj => hu₁ _ (hm j hj).1 (hm j hj).2,
      e₁, w.mem, w₁.gpr .r4 (by decide)]
  · exact ((w.keep.trans w₁.keep).trans kt).mono (by simp)

/-- Row `r` of a group of the triangle (`triRow r`), `r7` at the group's words of
`a` (`dA`), `r12` at the window (`dT`). -/
theorem triRow_ok {s : State} {B : Addr} {Z dA dT r : Nat} (hs : Scr s B Z) (h0 : s.gpr .r0 = 0) (hr : r < 8)
    (h7 : s.gpr .r7 = off B dA) (h12 : s.gpr .r12 = off B dT) (hA : dA + 8 * r + 8 ≤ Z) (hT : dT + 8 * r + 8 ≤ Z)
    (hst : (s.gpr (rstart r)).toNat ≤ 2) :
    WP isa (.block (triRow r)) s fun t =>
      (∃ w : BitVec 64, t.mem = s.mem.writeW (off B (dT + 8 * r)) w ∧
        2 ^ 64 * Vw t .r0 + w.toNat = Vw s (rstart r) + rv s smr 8 * (word s.mem B (dA + 8 * r)).toNat) ∧
      Keep (.r3 :: .r30 :: .r4 :: (List.range 8).map sacc) s t := by
  unfold triRow row8
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  exact rowLd_ok hs h0 h7 h12 hA hT ⟨by omega_using [hr], by omega_using []⟩ ⟨by omega_using [hr], by omega_using []⟩ (by decide) (by decide) hst

/-- Row `r` of a later chunk of the reduction (`redRow r`), `r10` at the block's
`uᵢ` (`dU`), `r12` at the window (`dT`). -/
theorem redRow_ok {s : State} {B : Addr} {Z dU dT r : Nat} (hs : Scr s B Z) (h0 : s.gpr .r0 = 0) (hr : r < 8)
    (h10 : s.gpr .r10 = off B dU) (h12 : s.gpr .r12 = off B dT) (hU : dU + 8 * r + 8 ≤ Z) (hT : dT + 8 * r + 8 ≤ Z)
    (hst : (s.gpr (rstart r)).toNat ≤ 2) :
    WP isa (.block (redRow r)) s fun t =>
      (∃ w : BitVec 64, t.mem = s.mem.writeW (off B (dT + 8 * r)) w ∧
        2 ^ 64 * Vw t .r0 + w.toNat = Vw s (rstart r) + rv s smr 8 * (word s.mem B (dU + 8 * r)).toNat) ∧
      Keep (.r3 :: .r30 :: .r4 :: (List.range 8).map sacc) s t := by
  unfold redRow row8
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  exact rowLd_ok hs h0 h10 h12 hU hT ⟨by omega_using [hr], by omega_using []⟩ ⟨by omega_using [hr], by omega_using []⟩ (by decide) (by decide) hst

/-- Row `r` of a block's first chunk of the reduction (`redRow0 r`): `uᵢ = W₀ m'`
(`m'` in `r31`) stored at `dU + 8 r` (`r10`), which zeroes the word that
drops out. -/
theorem redRow0_ok {s : State} {B : Addr} {Z dU r : Nat} (hs : Scr s B Z) (h0 : s.gpr .r0 = 0) (hr : r < 8)
    (h10 : s.gpr .r10 = off B dU) (hU : dU + 8 * r + 8 ≤ Z) (hst : (s.gpr (rstart r)).toNat ≤ 2)
    (hm : ((s.gpr (smr 0)).toNat * (s.gpr .r31).toNat + 1) % 2 ^ 64 = 0) :
    WP isa (.block (redRow0 r)) s fun t =>
      (t.mem = s.mem.writeW (off B (dU + 8 * r)) (t.gpr .r3) ∧ t.gpr .r3 = s.gpr (sacc 0) * s.gpr .r31 ∧
        2 ^ 64 * Vw t .r0 = Vw s (rstart r) + rv s smr 8 * (t.gpr .r3).toNat) ∧
      Keep (.r3 :: .r30 :: .r4 :: (List.range 8).map sacc) s t := by
  unfold redRow0 row8
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine row_start hst fun u w ca h4 hv => ?_
  have hu : ∀ r', r' ≠ .r4 → u.gpr r' = s.gpr r' := fun r' h => w.gpr r' h
  refine wp_mul fun u₁ w₁ e₁ c₁ => ?_
  rw [hu _ (by decide), hu _ (by decide)] at e₁
  refine wp_st (by decide) ⟨by omega_using [hr], by omega_using []⟩ (by rw [w₁.gpr _ (by decide), hu _ (by decide), h10, off_add])
    ((hs.congr (w₁.wr.trans w.wr)).st (by omega_using [hU])) fun u₂ k₂ m₂ c₂ => ?_
  have hu₂ : ∀ r', r' ≠ .r4 → r' ≠ .r3 → u₂.gpr r' = s.gpr r' := fun r' a b => by
    rw [k₂.gpr _ (by simp), w₁.gpr r' b, hu r' a]
  show WP isa (.block (chain8 false .r3 smr sacc sacc ++ (.addze .r4 .r4 :: (outStore none ++
    chain8 true .r3 smr sacc sshift)))) u₂ _
  refine WP.mono (rowCore_ok none row_regs (by rw [hu₂ _ (by decide) (by decide), h0]) (by rw [c₂, c₁, ca])
    (by rw [k₂.gpr _ (by simp), w₁.gpr _ (by decide)]; exact h4) fun P k e => by cases e)
    fun t ⟨⟨wv, hw, mt, et⟩, kt⟩ => ?_
  have t3 : t.gpr .r3 = u₁.gpr .r3 := by rw [kt.gpr _ (by decide), k₂.gpr _ (by simp)]
  have u3 : u₂.gpr .r3 = u₁.gpr .r3 := k₂.gpr _ (by simp)
  have z : wv.toNat = 0 := by
    rw [hw, u3, e₁, hu₂ _ (by decide) (by decide), hu₂ _ (by decide) (by decide)]
    exact row0_zero _ _ _ hm
  have hm' : ∀ j < 8, smr j ≠ .r4 ∧ smr j ≠ .r3 := by decide
  refine ⟨⟨by rw [mt]; simp only [Option.elim]; rw [m₂, w₁.mem, w.mem, t3], by rw [t3, e₁], ?_⟩,
    ((w.keep.trans w₁.keep).trans (k₂.trans kt)).mono (by simp)⟩
  rw [z, Nat.add_zero] at et
  have a2 : rv u₂ sacc 8 = rv u sacc 8 :=
    rv_congr 8 fun j hj => by rw [k₂.gpr _ (by simp), w₁.gpr _ (by revert j; decide)]
  have r42 : u₂.gpr .r4 = u.gpr .r4 := by rw [k₂.gpr _ (by simp), w₁.gpr _ (by decide)]
  rw [et, a2, r42, show rstart r = (if r = 0 then .r4 else .r0) from rfl, ← hv,
    rv_congr 8 fun j hj => hu₂ _ (hm' j hj).1 (hm' j hj).2, u3, t3]

/-! ## Loads, stores and boundaries -/

/-- `n` words from `ptr` (at `d`) into `f 0`, …, `f (n - 1)`. -/
theorem loadN_ok {f : Nat → Reg} {ptr : Reg} {B : Addr} {Z d : Nat} (hp0 : ptr ≠ .r0)
    (hf : ∀ j < 8, f j ≠ ptr ∧ ∀ k < 8, j < k → f j ≠ f k) :
    ∀ (n : Nat) {s : State}, Scr s B Z → s.gpr ptr = off B d → n ≤ 8 → d + 8 * n ≤ Z →
    WP isa (.block ((List.range n).map fun c => .load .d (f c) ptr (8 * c))) s fun t =>
      (rv t f n = wordsVal s.mem B d n ∧ t.mem = s.mem ∧ t.ca = s.ca ∧
        ∀ j < n, t.gpr (f j) = word s.mem B (d + 8 * j)) ∧ Keep ((List.range n).map f) s t
  | 0, s, _, _, _, _ => WP.block_nil ⟨⟨rfl, rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩, Keep.refl _ _⟩
  | n + 1, s, hs, hp, hn, hd => by
    rw [Mont4.map_succ, WP.block_append_iff]
    refine WP.mono (loadN_ok hp0 hf n hs hp (by omega_using [hn]) (by omega_using [hd])) fun t₁ ⟨⟨e₁, m₁, c₁, g₁⟩, k₁⟩ => ?_
    have hp' : t₁.gpr ptr = off B d := by
      rw [k₁.gpr _ fun h => by
        obtain ⟨j, hj, e⟩ := List.mem_map.mp h
        exact (hf j (by have := List.mem_range.mp hj; omega_using [hn, this])).1 e, hp]
    refine wp_ld hp0 ⟨by omega_using [hn], by omega_using []⟩ (by rw [hp', off_add]) ((hs.congr k₁.wr).ld (by omega_using [hd]))
      fun t w e c => WP.block_nil ⟨⟨?_, by rw [w.mem, m₁], by rw [c, c₁], fun j hj => ?_⟩,
        (k₁.trans w.keep).mono fun r hr => ?_⟩
    · have pt : rv t f n = rv t₁ f n := rv_congr n fun j hj => w.gpr _ ((hf j (by omega_using [hn, hj])).2 n (by omega_using [hn]) hj)
      show rv t f n + 2 ^ (64 * n) * (t.gpr (f n)).toNat = _
      rw [pt, e₁, wordsVal_succ_top, e, m₁]
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [w.gpr _ ((hf j (by omega_arith)).2 n (by omega_using [hn]) hj), g₁ j hj]
      · rw [e, m₁]
    · rw [List.range_succ, List.map_append]
      simp only [List.mem_append, List.mem_singleton, List.map_cons, List.map_nil] at hr ⊢
      exact hr

/-- `f 0`, …, `f (n - 1)` stored at `ptr` (at `d`). -/
theorem storeN_ok {f : Nat → Reg} {ptr : Reg} {B : Addr} {Z d : Nat} (hp0 : ptr ≠ .r0) :
    ∀ (n : Nat) {s : State}, Scr s B Z → s.gpr ptr = off B d → n ≤ 8 → d + 8 * n ≤ Z →
    WP isa (.block ((List.range n).map fun c => .store .d (f c) ptr (8 * c))) s fun t =>
      (wordsVal t.mem B d n = rv s f n ∧ Outside B d (8 * n) s.mem t.mem ∧ t.ca = s.ca) ∧ Keep [] s t
  | 0, s, _, _, _, _ => WP.block_nil ⟨⟨rfl, Outside.refl _ _ _ _, rfl⟩, Keep.refl _ _⟩
  | n + 1, s, hs, hp, hn, hd => by
    have hnw := hs.nowrap
    rw [Mont4.map_succ, WP.block_append_iff]
    refine WP.mono (storeN_ok hp0 n hs hp (by omega_using [hn]) (by omega_using [hd])) fun t₁ ⟨⟨e₁, o₁, c₁⟩, k₁⟩ => ?_
    refine wp_st hp0 ⟨by omega_using [hn], by omega_using []⟩ (by rw [k₁.gpr _ (by simp), hp, off_add]) ((hs.congr k₁.wr).st (by omega_using [hd]))
      fun t w wm c => WP.block_nil ⟨⟨?_, ?_, by rw [c, c₁]⟩, k₁.trans' w⟩
    · rw [wm, wordsVal_succ_top, (writeW_outside _ B _ (by omega_using [hd, hnw])).wordsVal (by omega_using []) (by omega_using [hd, hnw]),
        word_writeW_self, e₁, k₁.gpr _ (by simp)]
      rfl
    · rw [wm]
      exact (o₁.mono (Nat.le_refl _) (by omega_using [])).trans ((writeW_outside _ B _ (by omega_using [hd, hnw])).mono (by omega_using []) (by omega_using []))

theorem load8_ok {f : Nat → Reg} {ptr : Reg} {s : State} {B : Addr} {Z d : Nat} (hs : Scr s B Z)
    (hp : s.gpr ptr = off B d) (hd : d + 64 ≤ Z) (hp0 : ptr ≠ .r0)
    (hf : ∀ j < 8, f j ≠ ptr ∧ ∀ k < 8, j < k → f j ≠ f k) :
    WP isa (.block (load8 f ptr)) s fun t =>
      (rv t f 8 = wordsVal s.mem B d 8 ∧ t.mem = s.mem ∧ t.ca = s.ca ∧
        ∀ j < 8, t.gpr (f j) = word s.mem B (d + 8 * j)) ∧ Keep ((List.range 8).map f) s t :=
  loadN_ok hp0 hf 8 hs hp (Nat.le_refl _) (by omega_using [hd])

theorem store8_ok {f : Nat → Reg} {ptr : Reg} {s : State} {B : Addr} {Z d : Nat} (hs : Scr s B Z)
    (hp : s.gpr ptr = off B d) (hd : d + 64 ≤ Z) (hp0 : ptr ≠ .r0) :
    WP isa (.block (store8 f ptr)) s fun t =>
      (wordsVal t.mem B d 8 = rv s f 8 ∧ Outside B d 64 s.mem t.mem ∧ t.ca = s.ca) ∧ Keep [] s t :=
  storeN_ok hp0 8 hs hp (Nat.le_refl _) (by omega_using [hd])

theorem sacc_ne : ∀ j < 8, sacc j ≠ .r30 ∧ sacc j ≠ .r4 ∧ sacc j ≠ .r0 ∧ sacc j ≠ .r3 := by decide

theorem sacc_inj : ∀ j < 8, ∀ k < 8, sacc j = sacc k → j = k := by decide

theorem ldadd_arith {n R Rs W c cS d' c' sn wn : Nat}
    (e : R + 2 ^ (64 * n) * c = Rs + W + (if n = 0 then cS else 0))
    (eu : d' + 2 ^ 64 * c' = sn + wn + (if n = 0 then 0 else c)) (hn0 : n = 0 → R = 0 ∧ Rs = 0 ∧ W = 0) :
    R + 2 ^ (64 * n) * d' + 2 ^ (64 * (n + 1)) * c' = Rs + 2 ^ (64 * n) * sn + (W + 2 ^ (64 * n) * wn) +
      (if n + 1 = 0 then cS else 0) := by
  rw [pow64_succ]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain ⟨rfl, rfl, rfl⟩ := hn0 rfl
    simp only [↓reduceIte, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.mul_one,
      Nat.reduceEqDiff] at e eu ⊢
    omega_using [eu]
  · simp only [show ¬n = 0 by omega_using [hn], show ¬n + 1 = 0 by omega_using [], ↓reduceIte, Nat.add_zero] at e eu ⊢
    have := congrArg (2 ^ (64 * n) * ·) eu
    simp only [Nat.mul_add] at this
    grind

theorem keep_succ {s t u : State} {f : Nat → Reg} {n : Nat} {a : Reg}
    (k : Keep (a :: (List.range n).map f) s t) (k' : Keep [a, f n] t u) :
    Keep (a :: (List.range (n + 1)).map f) s u :=
  (k.trans k').mono fun r hr => by
    rw [List.range_succ, List.map_append]
    simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil,
      or_false, List.map_cons, List.map_nil] at hr ⊢
    grind

/-- The first `n` words of a boundary's chain: the words at `ptr` added to the
window. -/
theorem ldadd_ok {ptr : Reg} {B : Addr} {Z d : Nat} (hp0 : ptr ≠ .r0) (hp : ptr ≠ .r30 ∧ ∀ j < 8, sacc j ≠ ptr) :
    ∀ (n : Nat) {s : State}, Scr s B Z → s.gpr ptr = off B d → n ≤ 8 → d + 8 * n ≤ Z →
    WP isa (.block ((List.range n).flatMap fun c =>
        [.load .d .r30 ptr (8 * c), (if c = 0 then Instr.addc else Instr.adde) (sacc c) (sacc c) .r30])) s fun t =>
      (rv t sacc n + 2 ^ (64 * n) * t.ca.toNat = rv s sacc n + wordsVal s.mem B d n +
          (if n = 0 then s.ca.toNat else 0) ∧ t.mem = s.mem) ∧ Keep (.r30 :: (List.range n).map sacc) s t
  | 0, s, _, _, _, _ => WP.block_nil ⟨⟨by simp [rv, psum, wordsVal], rfl⟩, Keep.refl _ _⟩
  | n + 1, s, hs, h, hn, hd => by
    rw [flatMap_range_succ, WP.block_append_iff]
    refine WP.mono (ldadd_ok hp0 hp n hs h (by omega_using [hn]) (by omega_using [hd])) fun t ⟨⟨e, m⟩, k⟩ => ?_
    have hpt : t.gpr ptr = off B d := by rw [k.gpr _ (chain_notin hp.1 fun j hj => hp.2 j (by omega_using [hn, hj])), h]
    refine wp_ld hp0 ⟨by omega_using [hn], by omega_using []⟩ (by rw [hpt, off_add]) ((hs.congr k.wr).ld (by omega_using [hd])) fun t₁ w₁ e₁ c₁ => ?_
    have an := sacc_ne n (by omega_using [hn])
    have sn : t₁.gpr (sacc n) = s.gpr (sacc n) := by
      rw [w₁.gpr _ an.1, k.gpr _ (chain_notin an.1 fun j hj e => absurd (sacc_inj j (by omega_using [hn, hj]) n (by omega_using [hn]) e) (by omega_using [hj]))]
    rw [m] at e₁
    have post : ∀ u, W1 t₁ u (sacc n) → rv u sacc n = rv t sacc n ∧ u.mem = s.mem ∧
        Keep (.r30 :: (List.range (n + 1)).map sacc) s u := fun u w =>
      ⟨rv_congr n fun j hj => by
        rw [w.gpr _ fun e => absurd (sacc_inj j (by omega_using [hn, hj]) n (by omega_using [hn]) e) (by omega_using [hj]), w₁.gpr _ (sacc_ne j (by omega_using [hn, hj])).1],
        by rw [w.mem, w₁.mem, m], keep_succ k ((w₁.keep.trans w.keep).mono (by simp))⟩
    have fin : ∀ u, W1 t₁ u (sacc n) →
        (u.gpr (sacc n)).toNat + 2 ^ 64 * u.ca.toNat = (s.gpr (sacc n)).toNat + (word s.mem B (d + 8 * n)).toNat +
          (if n = 0 then 0 else t.ca.toNat) →
        rv u sacc (n + 1) + 2 ^ (64 * (n + 1)) * u.ca.toNat = rv s sacc (n + 1) + wordsVal s.mem B d (n + 1) +
          (if n + 1 = 0 then s.ca.toNat else 0) := fun u w eu => by
      show rv u sacc n + 2 ^ (64 * n) * (u.gpr (sacc n)).toNat + _ = rv s sacc n + 2 ^ (64 * n) * (s.gpr (sacc n)).toNat + _ + _
      rw [(post u w).1, wordsVal_succ_top]
      exact ldadd_arith e eu fun h0 => by subst h0; exact ⟨rfl, rfl, rfl⟩
    by_cases hn0 : n = 0
    · subst hn0
      simp only [↓reduceIte]
      refine wp_addc fun u w eu => WP.block_nil ⟨⟨fin u w ?_, (post u w).2.1⟩, (post u w).2.2⟩
      rw [sn, e₁] at eu; simpa using eu
    · simp only [hn0, ↓reduceIte]
      refine wp_adde fun u w eu => WP.block_nil ⟨⟨fin u w ?_, (post u w).2.1⟩, (post u w).2.2⟩
      rw [sn, e₁, c₁] at eu; simp only [hn0, ↓reduceIte]; exact eu

/-- A boundary (`boundary8`): the eight words at `ptr` (at `d`) into the
window, the word above it in `r4`, CA clear. -/
theorem boundary8_ok {ptr : Reg} {s : State} {B : Addr} {Z d : Nat} (hs : Scr s B Z) (h0 : s.gpr .r0 = 0)
    (hp : s.gpr ptr = off B d) (hd : d + 64 ≤ Z) (hp0 : ptr ≠ .r0) (hp4 : ptr ≠ .r4)
    (hpa : ptr ≠ .r30 ∧ ∀ j < 8, sacc j ≠ ptr) :
    WP isa (.block (boundary8 ptr)) s fun t =>
      (Vw t .r4 = Vw s .r0 + wordsVal s.mem B d 8 ∧ (t.gpr .r4).toNat ≤ 2 ∧ t.ca = false ∧ t.mem = s.mem) ∧
        Keep (.r4 :: .r30 :: (List.range 8).map sacc) s t := by
  unfold boundary8
  simp only [List.cons_append, List.nil_append]
  refine wp_addze fun u w eu => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ldadd_ok (d := d) hp0 hpa 8 (hs.congr w.wr) (by rw [w.gpr _ hp4, hp]) (Nat.le_refl _) (by omega_using [hd]))
    fun v ⟨⟨ev, mv⟩, kv⟩ => wp_addze fun t w' et => WP.block_nil ⟨⟨?_, ?_, ?_, by rw [w'.mem, mv, w.mem]⟩, ?_⟩
  · have hc := Bool.toNat_le s.ca
    have h0u : (s.gpr .r0).toNat = 0 := by rw [h0]; rfl
    rw [h0u] at eu
    have r4v : v.gpr .r4 = u.gpr .r4 := kv.gpr _ (by decide)
    rw [r4v] at et
    have ra : rv t sacc 8 = rv v sacc 8 := rv_congr 8 fun j hj => w'.gpr _ (sacc_ne j hj).2.1
    have ru : rv u sacc 8 = rv s sacc 8 := rv_congr 8 fun j hj => w.gpr _ (sacc_ne j hj).2.1
    simp only [ru, w.mem, pow512] at ev
    unfold Vw
    rw [ra, h0, show (0 : BitVec 64).toNat = 0 from rfl, Nat.zero_add]
    have := (t.gpr .r4).isLt; have := Bool.toNat_le t.ca; have := Bool.toNat_le v.ca; have := Bool.toNat_le u.ca
    have := (u.gpr .r4).isLt
    have hct : t.ca.toNat = 0 := by omega_arith
    rw [hct]
    grind
  · have hc := Bool.toNat_le s.ca
    have h0u : (s.gpr .r0).toNat = 0 := by rw [h0]; rfl
    rw [h0u] at eu
    rw [kv.gpr _ (by decide)] at et
    have := Bool.toNat_le v.ca; have := Bool.toNat_le u.ca; have := (u.gpr .r4).isLt
    omega_arith
  · have hc := Bool.toNat_le s.ca
    have h0u : (s.gpr .r0).toNat = 0 := by rw [h0]; rfl
    rw [h0u] at eu
    rw [kv.gpr _ (by decide)] at et
    have := Bool.toNat_le v.ca; have := Bool.toNat_le u.ca; have := (u.gpr .r4).isLt; have := (t.gpr .r4).isLt
    cases h : t.ca
    · rfl
    · rw [h] at et; simp at et; omega
  · exact ((w.keep.trans kv).trans w'.keep).mono fun r hr => by
      simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil, or_false] at hr ⊢
      grind

/-! ## Eight rows -/

theorem rstart_succ (n : Nat) : rstart (n + 1) = .r0 := rfl

/-- `n` rows of a group, row `r` storing the word that drops out at `dT + 8 r`
and adding `C r` to the window: `2^(64 n) V' + [out] = V + Σ 2^(64 r) C r`. -/
theorem rowsN_ok {rows : Nat → List Instr} {C : Nat → BitVec 64 → Nat} {I : State → Prop} {L : List Reg} {B : Addr}
    {dT : Nat} (hnw : dT + 64 ≤ 2 ^ 64)
    (hrow : ∀ r < 8, ∀ s, I s → (s.gpr (rstart r)).toNat ≤ 2 →
      WP isa (.block (rows r)) s fun t => (∃ w : BitVec 64, t.mem = s.mem.writeW (off B (dT + 8 * r)) w ∧
        2 ^ 64 * Vw t .r0 + w.toNat = Vw s (rstart r) + C r w) ∧ Keep L s t)
    (hI : ∀ r < 8, ∀ s t (w : BitVec 64), I s → Keep L s t → t.mem = s.mem.writeW (off B (dT + 8 * r)) w → I t)
    (h0 : ∀ s, I s → s.gpr .r0 = 0) :
    ∀ n ≤ 8, ∀ s, I s → (s.gpr .r4).toNat ≤ 2 →
      WP isa (.block ((List.range n).flatMap rows)) s fun t =>
        (2 ^ (64 * n) * Vw t (rstart n) + wordsVal t.mem B dT n =
            Vw s .r4 + psum (fun r => C r (word t.mem B (dT + 8 * r))) n ∧
          Outside B dT (8 * n) s.mem t.mem ∧ I t) ∧ Keep L s t
  | 0, _, s, hs, _ => WP.block_nil ⟨⟨by simp [rstart, wordsVal, psum], Outside.refl _ _ _ _, hs⟩, Keep.refl _ _⟩
  | n + 1, hn, s, hs, h4 => by
    rw [flatMap_range_succ, WP.block_append_iff]
    have step : ∀ t, (2 ^ (64 * n) * Vw t (rstart n) + wordsVal t.mem B dT n =
            Vw s .r4 + psum (fun r => C r (word t.mem B (dT + 8 * r))) n ∧
        Outside B dT (8 * n) s.mem t.mem ∧ I t) ∧ Keep L s t → (t.gpr (rstart n)).toNat ≤ 2 →
        WP isa (.block (rows n)) t fun t =>
          (2 ^ (64 * (n + 1)) * Vw t (rstart (n + 1)) + wordsVal t.mem B dT (n + 1) =
              Vw s .r4 + psum (fun r => C r (word t.mem B (dT + 8 * r))) (n + 1) ∧
            Outside B dT (8 * (n + 1)) s.mem t.mem ∧ I t) ∧ Keep L s t := fun t ⟨⟨e, o, it⟩, k⟩ hst =>
      WP.mono (hrow n (by omega_using [hn]) t it hst) fun u ⟨⟨w, mu, eu⟩, ku⟩ => ⟨⟨?_, ?_, hI n (by omega_using [hn]) t u w it ku mu⟩,
        (k.trans ku).mono fun r hr => by simp only [List.mem_append, or_self] at hr; exact hr⟩
    · by_cases hn0 : n = 0
      · subst hn0
        exact WP.block_nil (step s ⟨⟨by simp [rstart, wordsVal, psum], Outside.refl _ _ _ _, hs⟩, Keep.refl _ _⟩ h4)
      · exact WP.mono (rowsN_ok hnw hrow hI h0 n (by omega_using [hn]) s hs h4) fun t h =>
          step t h (by rw [show rstart n = .r0 by simp [rstart, hn0], h0 t h.1.2.2]; decide)
    · have pc : psum (fun r => C r (word u.mem B (dT + 8 * r))) n = psum (fun r => C r (word t.mem B (dT + 8 * r))) n :=
        psum_congr fun j hj => by rw [mu, (writeW_outside t.mem B w (by omega_using [hnw, hn])).word (by omega_using [hj]) (by omega_using [hnw, hn, hj])]
      rw [psum, pc, show word u.mem B (dT + 8 * n) = w by rw [mu, word_writeW_self]]
      rw [rstart_succ, mu, fios_wordsVal_write_top _ _ _ _ _ (by omega_using [hnw, hn]), pow64_succ]
      have := congrArg (2 ^ (64 * n) * ·) eu
      simp only [Nat.mul_add] at this
      grind
    · rw [mu]
      exact (o.mono (Nat.le_refl _) (by omega_using [])).trans ((writeW_outside _ B _ (by omega_using [hnw, hn])).mono (by omega_using []) (by omega_using []))

/-! ## The squaring's arithmetic -/

/-- `Σ_{i<n} 2^(128 i) aᵢ²` of the `n` words at `d`. -/
def sqs (m : Mem) (B : Addr) (d : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sqs m B d n + 2 ^ (64 * n) * 2 ^ (64 * n) * ((word m B (d + 8 * n)).toNat * (word m B (d + 8 * n)).toNat)

theorem sqs_append (m : Mem) (B : Addr) (d j : Nat) : ∀ k,
    sqs m B d (j + k) = sqs m B d j + 2 ^ (64 * j) * 2 ^ (64 * j) * sqs m B (d + 8 * j) k
  | 0 => by simp [sqs]
  | k + 1 => by
    rw [← Nat.add_assoc, sqs, sqs_append m B d j k, sqs, show d + 8 * j + 8 * k = d + 8 * (j + k) by omega_using [],
      show 64 * (j + k) = 64 * j + 64 * k by omega_using [], Nat.pow_add]
    grind

/-- Within a block: the products of each word with the words below it, doubled,
and the squares, are the block's square. -/
theorem tri_lower (m : Mem) (B : Addr) (d : Nat) : ∀ n,
    2 * psum (fun r => wordsVal m B d r * (word m B (d + 8 * r)).toNat) n + sqs m B d n =
      wordsVal m B d n * wordsVal m B d n
  | 0 => by simp [psum, sqs, wordsVal]
  | n + 1 => by
    have ih := tri_lower m B d n
    rw [psum, sqs, wordsVal_succ_top]
    grind

/-- The blocks' step: with `x` the block's value (at its weight), `D` its
products within it, `R'` the words above it (at their weight), `P` the
blocks below. -/
theorem tri_step {T Q P R R' x D Sq : Nat} (ih : 2 * T + Q = P * P + 2 * P * R) (hR : R = x + R')
    (hD : 2 * D + Sq = x * x) :
    2 * (T + (D + x * R')) + (Q + Sq) = (P + x) * (P + x) + 2 * (P + x) * R' := by
  subst hR
  grind

/-- The products within block `k` of `a` (each word times the words of the
block below it). -/
def triD (m : Mem) (B : Addr) (da k : Nat) : Nat :=
  psum (fun r => wordsVal m B (da + 64 * k) r * (word m B (da + 64 * k + 8 * r)).toNat) 8

/-- What block `k` of the triangle adds to `S`: its products within it, and
the block times the words above it. -/
def triInc (m : Mem) (B : Addr) (da w k : Nat) : Nat :=
  2 ^ (64 * (16 * k)) * triD m B da k +
    2 ^ (64 * (16 * k + 8)) * (wordsVal m B (da + 64 * k) 8 * wordsVal m B (da + 64 * (k + 1)) (w - 8 * (k + 1)))

/-- The triangle after `k` blocks. -/
def triS (m : Mem) (B : Addr) (da w : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => triS m B da w k + triInc m B da w k

theorem triS_inv (m : Mem) (B : Addr) (da w : Nat) : ∀ k, 8 * k ≤ w →
    2 * triS m B da w k + sqs m B da (8 * k) = wordsVal m B da (8 * k) * wordsVal m B da (8 * k) +
      2 * wordsVal m B da (8 * k) * (2 ^ (64 * (8 * k)) * wordsVal m B (da + 64 * k) (w - 8 * k))
  | 0, _ => by simp [triS, sqs, wordsVal]
  | k + 1, hk => by
    have ih := triS_inv m B da w k (by omega_using [hk])
    have e8 : 8 * (k + 1) = 8 * k + 8 := by omega_using []
    have hP : wordsVal m B da (8 * (k + 1)) = wordsVal m B da (8 * k) +
        2 ^ (64 * (8 * k)) * wordsVal m B (da + 64 * k) 8 := by
      rw [e8, fios_wordsVal_append, show da + 8 * (8 * k) = da + 64 * k by omega_using []]
    have hR : 2 ^ (64 * (8 * k)) * wordsVal m B (da + 64 * k) (w - 8 * k) =
        2 ^ (64 * (8 * k)) * wordsVal m B (da + 64 * k) 8 +
          2 ^ (64 * (8 * (k + 1))) * wordsVal m B (da + 64 * (k + 1)) (w - 8 * (k + 1)) := by
      rw [show w - 8 * k = 8 + (w - 8 * (k + 1)) by omega_using [hk], fios_wordsVal_append,
        show da + 64 * k + 8 * 8 = da + 64 * (k + 1) by omega_using [], e8, show 64 * (8 * k + 8) = 64 * (8 * k) + 64 * 8 by omega_using [],
        Nat.pow_add]
      grind
    have hQ : sqs m B da (8 * (k + 1)) = sqs m B da (8 * k) +
        2 ^ (64 * (8 * k)) * 2 ^ (64 * (8 * k)) * sqs m B (da + 64 * k) 8 := by
      rw [e8, sqs_append, show da + 8 * (8 * k) = da + 64 * k by omega_using []]
    have hD := tri_lower m B (da + 64 * k) 8
    have hI : triInc m B da w k = 2 ^ (64 * (16 * k)) * triD m B da k +
        2 ^ (64 * (8 * k)) * wordsVal m B (da + 64 * k) 8 *
          (2 ^ (64 * (8 * (k + 1))) * wordsVal m B (da + 64 * (k + 1)) (w - 8 * (k + 1))) := by
      unfold triInc
      rw [show 64 * (16 * k + 8) = 64 * (8 * k) + 64 * (8 * (k + 1)) by omega_using [], Nat.pow_add]
      grind
    have h16 : 2 ^ (64 * (16 * k)) = 2 ^ (64 * (8 * k)) * 2 ^ (64 * (8 * k)) := by
      rw [← Nat.pow_add]; congr 1; omega_using []
    rw [triS, hI, hP, hQ]
    refine tri_step ih hR ?_
    rw [h16]
    unfold triD
    grind

/-- The triangle doubled, and the squares, are `a²`. -/
theorem triS_total (m : Mem) (B : Addr) (da K : Nat) :
    2 * triS m B da (8 * K) K + sqs m B da (8 * K) = wordsVal m B da (8 * K) * wordsVal m B da (8 * K) := by
  have := triS_inv m B da (8 * K) K (Nat.le_refl _)
  rw [Nat.sub_self] at this
  simpa [wordsVal] using this

/-! ## Counters in the halves of a register -/

/-- Blocks `h` in the high half, groups `l` in the low half. -/
abbrev cnt (h l : Nat) : BitVec 64 := BitVec.ofNat 64 (2 ^ 32 * h + l)

theorem cnt_hi {h l : Nat} (hh : h < 2 ^ 32) (hl : l < 2 ^ 32) : cnt h l >>> 32 = BitVec.ofNat 64 h := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (by omega_using [hh, hl]), Nat.mod_eq_of_lt (by omega_using [hh])]
  omega_using [hl]

theorem cnt_or {h l : Nat} (hh : h < 2 ^ 32) (hl : l < 2 ^ 32) : cnt h 0 ||| BitVec.ofNat 64 l = cnt h l := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_ofNat, Nat.add_zero]
  rw [Nat.mod_eq_of_lt (by omega_using [hh]), Nat.mod_eq_of_lt (by omega_using [hl]), Nat.mod_eq_of_lt (by omega_using [hh, hl]), Nat.mul_comm,
    ← Nat.shiftLeft_eq, Nat.shiftLeft_add_eq_or_of_lt hl]

theorem cnt_dec {h l : Nat} (hl1 : 1 ≤ l) :
    cnt h l - BitVec.ofNat 64 1 = cnt h (l - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega_using [hl1]

theorem cnt_decHi {h : Nat} (hh : h < 2 ^ 32) (h1 : 1 ≤ h) :
    cnt h 0 - BitVec.ofNat 64 1 <<< 32 = cnt (h - 1) 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq]
  omega

theorem eval_zero_w {s : State} {r : Reg} {h l : Nat} (hl : l < 2 ^ 32) (e : s.gpr r = cnt h l) :
    isa.eval (.zero .w r) s = some (decide (l = 0)) := by
  change some (s.read .w r == 0) = _
  rw [Option.some.injEq]
  have : s.read .w r = BitVec.ofNat 32 l := by
    apply BitVec.eq_of_toNat_eq
    simp only [State.read, Size.bits, e, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_using []
  rw [this]
  by_cases h0 : l = 0
  · subst h0; rfl
  · rw [decide_eq_false h0]
    refine beq_false_of_ne fun e0 => h0 ?_
    have := congrArg BitVec.toNat e0
    rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl] at this

theorem eval_nonzero_w {s : State} {r : Reg} {h l : Nat} (hl : l < 2 ^ 32) (e : s.gpr r = cnt h l) :
    isa.eval (.nonzero .w r) s = some (decide (l ≠ 0)) := by
  have z := eval_zero_w hl e
  change some (s.read .w r == 0) = _ at z
  change some (s.read .w r != 0) = _
  rw [Option.some.injEq] at z ⊢
  rw [bne, z]
  by_cases h0 : l = 0 <;> simp [h0]

/-- A do-while loop on the low half of a register, which its body decrements, from `N > 0`. -/
theorem wp_countdown_w {body : Prog isa} {cr : Reg} {h N : Nat} (hN : N < 2 ^ 32) (hN0 : 0 < N)
    (Inv : Nat → State → Prop)
    (hbody : ∀ i < N, ∀ s, Inv i s → s.gpr cr = cnt h (N - i) →
      WP isa body s fun s' => Inv (i + 1) s' ∧ s'.gpr cr = cnt h (N - i - 1))
    {s : State} (h0 : Inv 0 s) (hc : s.gpr cr = cnt h N) :
    WP isa (.loop body (.nonzero .w cr)) s fun t => Inv N t ∧ t.gpr cr = cnt h 0 := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = N - k ∧ k < N ∧ Inv k s ∧ s.gpr cr = cnt h (N - k)) ?_ N s
    ⟨0, by omega_using [], hN0, h0, by rw [hc, Nat.sub_zero]⟩
  rintro m s ⟨k, rfl, hk, hi, hc⟩
  refine WP.mono (hbody k hk s hi hc) fun s' ⟨hi', hc'⟩ => ?_
  have hz := eval_nonzero_w (show N - k - 1 < 2 ^ 32 by omega_using [hN]) hc'
  by_cases hl : k + 1 = N
  · refine .inl ⟨by rw [hz]; simp [show N - k - 1 = 0 by omega_using [hl]], ?_, ?_⟩
    · rwa [hl] at hi'
    · rw [hc', show N - k - 1 = 0 by omega_using [hl]]
  · exact .inr ⟨by rw [hz]; simp [show N - k - 1 ≠ 0 by omega_using [hk, hl]], N - (k + 1), by omega_using [hk], k + 1, rfl, by omega_using [hk, hl], hi',
      by rw [hc', show N - k - 1 = N - (k + 1) by omega_using []]⟩

/-! ## The triangle's groups -/

theorem psum_mulw (c : Nat) (m : Mem) (B : Addr) (d : Nat) : ∀ n,
    psum (fun r => c * (word m B (d + 8 * r)).toNat) n = c * wordsVal m B d n
  | 0 => by simp [psum, wordsVal]
  | n + 1 => by rw [psum, psum_mulw c m B d n, wordsVal_succ_top]; grind

/-- The invariant of the rows of a group whose words are at `dA`. -/
def GrpI (g : State) (B : Addr) (Z dA dT Bk : Nat) (u : State) : Prop :=
  Scr u B Z ∧ u.gpr .r0 = 0 ∧ u.gpr .r7 = off B dA ∧ u.gpr .r12 = off B dT ∧ rv u smr 8 = Bk ∧
    ∀ r < 8, word u.mem B (dA + 8 * r) = word g.mem B (dA + 8 * r)

/-- The registers a row writes. -/
abbrev rowRegs : List Reg := .r3 :: .r30 :: .r4 :: (List.range 8).map sacc

theorem GrpI.step {g u t : State} {B : Addr} {Z dA dT Bk r : Nat} {w : BitVec 64} (h : GrpI g B Z dA dT Bk u)
    (hr : r < 8) (k : Keep rowRegs u t) (m : t.mem = u.mem.writeW (off B (dT + 8 * r)) w)
    (hsep : dA + 64 ≤ dT ∨ dT + 64 ≤ dA) (hZ : dT + 64 ≤ Z) (hA : dA + 64 ≤ Z) : GrpI g B Z dA dT Bk t := by
  obtain ⟨hu, u0, u7, u12, ub, uw⟩ := h
  have hnw := hu.nowrap
  refine ⟨hu.congr k.wr, by rw [k.gpr _ (by decide), u0], by rw [k.gpr _ (by decide), u7],
    by rw [k.gpr _ (by decide), u12], by rw [← ub]; exact rv_congr 8 fun j hj => k.gpr _ (by revert j; decide),
    fun r' hr' => ?_⟩
  rw [m, (writeW_outside u.mem B w (by omega_using [hr, hZ, hnw])).word (by omega_using [hr, hsep, hr']) (by omega_using [hA, hnw, hr']), uw r' hr']

/-- A group's eight rows (`triRow`): `2⁵¹² V' + [out] = V + Bₖ A` for the
group's words `A` of `a` (at `dA`). -/
theorem triRows_ok {s : State} {B : Addr} {Z dA dT : Nat} (hs : Scr s B Z) (h0 : s.gpr .r0 = 0)
    (h7 : s.gpr .r7 = off B dA) (h12 : s.gpr .r12 = off B dT) (hA : dA + 64 ≤ Z) (hT : dT + 64 ≤ Z)
    (hsep : dA + 64 ≤ dT ∨ dT + 64 ≤ dA) (h4 : (s.gpr .r4).toNat ≤ 2) :
    WP isa (.block ((List.range 8).flatMap triRow)) s fun t =>
      (2 ^ (64 * 8) * Vw t .r0 + wordsVal t.mem B dT 8 = Vw s .r4 + rv s smr 8 * wordsVal s.mem B dA 8 ∧
        Outside B dT 64 s.mem t.mem ∧ GrpI s B Z dA dT (rv s smr 8) t) ∧ Keep rowRegs s t := by
  have hnw := hs.nowrap
  refine WP.mono (rowsN_ok (C := fun r _ => rv s smr 8 * (word s.mem B (dA + 8 * r)).toNat)
    (I := GrpI s B Z dA dT (rv s smr 8)) (L := rowRegs) (B := B) (dT := dT) (by omega_using [hT, hnw])
    (fun r hr u ⟨hu, u0, u7, u12, ub, uw⟩ hst => ?_) (fun r hr u t w h k m => h.step hr k m hsep hT hA)
    (fun u h => h.2.1) 8 (Nat.le_refl _) s ⟨hs, h0, h7, h12, rfl, fun _ _ => rfl⟩ h4)
    fun t ⟨⟨e, o, it⟩, k⟩ => ⟨⟨by rw [← psum_mulw, ← e]; rfl, o, it⟩, k⟩
  refine WP.mono (triRow_ok hu u0 hr u7 u12 (by omega_using [hA, hr]) (by omega_using [hT, hr]) hst) fun t ⟨⟨w, mt, et⟩, kt⟩ => ⟨⟨w, mt, ?_⟩, kt⟩
  rw [et, ub, uw r hr]

/-- The value of `S` (`N` words at `dS`) while the window, after a boundary,
is at its word `p`: the words below it, the window, and the words above it. -/
def tot (t : State) (B : Addr) (dS N p : Nat) : Nat :=
  wordsVal t.mem B dS p + 2 ^ (64 * p) * (Vw t .r4 + 2 ^ (64 * 8) * wordsVal t.mem B (dS + 8 * p + 64) (N - p - 8))

theorem Vw_congr {s t : State} (h : ∀ j < 8, t.gpr (sacc j) = s.gpr (sacc j)) (h0 : t.gpr .r0 = s.gpr .r0)
    (hc : t.ca = s.ca) : Vw t .r0 = Vw s .r0 := by
  unfold Vw; rw [rv_congr 8 h, h0, hc]

theorem tot_arith {L Q R V0 W A X V4 C : Nat} (e : R * V0 + W = V4 + C) :
    L + Q * W + Q * R * (V0 + A + R * X) = L + Q * (V4 + R * (A + R * X)) + Q * C := by
  have := congrArg (Q * ·) e
  simp only [Nat.mul_add] at this ⊢
  grind

/-- A group of the triangle (the body of `triGroups`): `S` takes in the
products of the block (`smr`) with eight words of `a` (at `da + 8 j`), the
window moves on eight words, one group less in `r9`. -/
theorem triGroup_ok {s : State} {B : Addr} {Z dA dS N p h l : Nat} (hs : Scr s B Z) (h0 : s.gpr .r0 = 0)
    (h7 : s.gpr .r7 = off B (dA)) (h12 : s.gpr .r12 = off B (dS + 8 * p)) (h9 : s.gpr .r9 = cnt h l)
    (hl : 1 ≤ l) (h4 : (s.gpr .r4).toNat ≤ 2) (hA : dA + 64 ≤ Z) (hS : dS + 8 * N ≤ Z)
    (hsep : dA + 64 ≤ dS ∨ dS + 8 * N ≤ dA) (hp : p + 16 ≤ N) :
    WP isa (.block ((List.range 8).flatMap triRow ++ ([.addi .r12 .r12 64, .addi .r7 .r7 64] : List Instr) ++
        boundary8 .r12 ++ ([.subi .r9 .r9 1] : List Instr))) s fun t =>
      (tot t B dS N (p + 8) = tot s B dS N p + 2 ^ (64 * p) * (rv s smr 8 * wordsVal s.mem B (dA) 8) ∧
        Outside B (dS + 8 * p) 64 s.mem t.mem ∧ t.gpr .r7 = off B (dA + 64) ∧
        t.gpr .r12 = off B (dS + 8 * p + 64) ∧ t.gpr .r9 = cnt h (l - 1) ∧ (t.gpr .r4).toNat ≤ 2 ∧ t.ca = false) ∧
      Keep (.r12 :: .r7 :: .r9 :: rowRegs) s t := by
  have hnw := hs.nowrap
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [WP.block_append_iff]
  refine WP.mono (triRows_ok hs h0 h7 h12 hA (by omega_using [hS, hp]) (by omega_using [hsep, hp]) h4) fun t₁ ⟨⟨e₁, o₁, ⟨hs₁, z₁, r7₁, r12₁, _, _⟩⟩, k₁⟩ => ?_
  refine wp_addi (by decide) (by decide) fun u₁ w₁ f₁ c₁ => ?_
  refine wp_addi (by decide) (by decide) fun u₂ w₂ f₂ c₂ => ?_
  rw [WP.block_append_iff]
  have hu₂ : Scr u₂ B Z := hs₁.congr (w₂.wr.trans w₁.wr)
  have p12 : u₂.gpr .r12 = off B (dS + 8 * p + 64) := by rw [w₂.gpr _ (by decide), f₁, r12₁, off_add]
  have z₂ : u₂.gpr .r0 = 0 := by rw [w₂.gpr _ (by decide), w₁.gpr _ (by decide), z₁]
  refine WP.mono (boundary8_ok hu₂ z₂ p12 (by omega_using [hS, hp]) (by decide) (by decide) (by decide))
    fun t₂ ⟨⟨e₂, l₂, c₂', m₂⟩, k₂⟩ => ?_
  refine wp_write (exec_subi (by decide) (by decide)) fun t w₃ f₃ c₃ => WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · have mt : t.mem = t₁.mem := by rw [w₃.mem, m₂, w₂.mem, w₁.mem]
    have v₂ : Vw u₂ .r0 = Vw t₁ .r0 :=
      Vw_congr (fun j hj => by rw [w₂.gpr _ (by revert j; decide), w₁.gpr _ (by revert j; decide)])
        (by rw [w₂.gpr _ (by decide), w₁.gpr _ (by decide)]) (by rw [c₂, c₁])
    have vt : Vw t .r4 = Vw t₂ .r4 := by
      unfold Vw; rw [rv_congr 8 fun j hj => w₃.gpr _ (by revert j; decide), w₃.gpr _ (by decide), c₃]
    rw [w₂.mem, w₁.mem, v₂] at e₂
    have hw : ∀ d k, (d + 8 * k ≤ dS + 8 * p ∨ dS + 8 * p + 64 ≤ d) → d + 8 * k ≤ Z →
        wordsVal t₁.mem B d k = wordsVal s.mem B d k := fun d k h1 h2 => o₁.wordsVal h1 (by omega_using [hnw, h2])
    have A1 : wordsVal t₁.mem B dS (p + 8) = wordsVal s.mem B dS p + 2 ^ (64 * p) * wordsVal t₁.mem B (dS + 8 * p) 8 := by
      rw [fios_wordsVal_append, hw dS p (Or.inl (by omega_using [])) (by omega_using [hS, hp])]
    have A2 : wordsVal t₁.mem B (dS + 8 * (p + 8) + 64) (N - (p + 8) - 8) =
        wordsVal s.mem B (dS + 8 * p + 128) (N - p - 16) := by
      rw [show dS + 8 * (p + 8) + 64 = dS + 8 * p + 128 by omega_using [], show N - (p + 8) - 8 = N - p - 16 by omega_using []]
      exact hw _ _ (Or.inr (by omega_using [])) (by omega_using [hS, hp])
    have A3 : wordsVal t₁.mem B (dS + 8 * p + 64) 8 = wordsVal s.mem B (dS + 8 * p + 64) 8 :=
      hw _ _ (Or.inr (by omega_using [])) (by omega_using [hS, hp])
    have A4 : wordsVal s.mem B (dS + 8 * p + 64) (N - p - 8) = wordsVal s.mem B (dS + 8 * p + 64) 8 +
        2 ^ (64 * 8) * wordsVal s.mem B (dS + 8 * p + 128) (N - p - 16) := by
      rw [show N - p - 8 = 8 + (N - p - 16) by omega_using [hp], fios_wordsVal_append,
        show dS + 8 * p + 64 + 8 * 8 = dS + 8 * p + 128 by omega_using []]
    have P : 2 ^ (64 * (p + 8)) = 2 ^ (64 * p) * 2 ^ (64 * 8) := by rw [← Nat.pow_add, Nat.mul_add]
    unfold tot
    rw [mt, vt, e₂, A1, A2, A3, A4, P]
    exact tot_arith e₁
  · rw [w₃.mem, m₂, w₂.mem, w₁.mem]; exact o₁
  · rw [w₃.gpr _ (by decide), k₂.gpr _ (by decide), f₂, w₁.gpr _ (by decide), r7₁, off_add]
  · rw [w₃.gpr _ (by decide), k₂.gpr _ (by decide)]; exact p12
  · rw [f₃, k₂.gpr _ (by decide), w₂.gpr _ (by decide), w₁.gpr _ (by decide), k₁.gpr _ (by decide), h9, cnt_dec hl]
  · rw [w₃.gpr _ (by decide)]; exact l₂
  · rw [c₃]; exact c₂'
  · exact (((k₁.trans w₁.keep).trans w₂.keep).trans (k₂.trans w₃.keep)).mono fun r hr => by
      simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil, or_false] at hr ⊢
      grind

/-- The registers a group writes. -/
abbrev grpRegs : List Reg := .r12 :: .r7 :: .r9 :: rowRegs

/-- The groups after a block's own rows (`triGroups`), `G` of them in `r9`'s
low half: `S` takes in the block times the `8 G` words of `a` at `dA`. -/
theorem triGroups_ok {s : State} {B : Addr} {Z dA dS N p h G : Nat} (hs : Scr s B Z) (h0 : s.gpr .r0 = 0)
    (h7 : s.gpr .r7 = off B dA) (h12 : s.gpr .r12 = off B (dS + 8 * p)) (h9 : s.gpr .r9 = cnt h G)
    (hG : G < 2 ^ 32) (h4 : (s.gpr .r4).toNat ≤ 2) (hca : s.ca = false) (hA : dA + 64 * G ≤ Z)
    (hS : dS + 8 * N ≤ Z) (hsep : dA + 64 * G ≤ dS ∨ dS + 8 * N ≤ dA) (hp : p + 8 * G + 8 ≤ N) :
    WP isa triGroups s fun t =>
      (tot t B dS N (p + 8 * G) = tot s B dS N p + 2 ^ (64 * p) * (rv s smr 8 * wordsVal s.mem B dA (8 * G)) ∧
        Outside B (dS + 8 * p) (64 * G) s.mem t.mem ∧ t.gpr .r7 = off B (dA + 64 * G) ∧
        t.gpr .r12 = off B (dS + 8 * p + 64 * G) ∧ t.gpr .r9 = cnt h 0 ∧ (t.gpr .r4).toNat ≤ 2 ∧ t.ca = false) ∧
      Keep grpRegs s t := by
  have hnw := hs.nowrap
  unfold triGroups
  refine WP.ite _ (eval_zero_w hG h9) (fun hz => ?_) (fun hz => ?_)
  · have : G = 0 := of_decide_eq_true hz
    subst this
    exact WP.block_nil ⟨⟨by simp [wordsVal], Outside.refl _ _ _ _, h7, h12, h9, h4, hca⟩, Keep.refl _ _⟩
  have hG0 : G ≠ 0 := of_decide_eq_false hz
  refine WP.mono (wp_countdown_w (h := h) hG (by omega_using [hG0]) (fun i t =>
    (tot t B dS N (p + 8 * i) = tot s B dS N p + 2 ^ (64 * p) * (rv s smr 8 * wordsVal s.mem B dA (8 * i)) ∧
      Outside B (dS + 8 * p) (64 * i) s.mem t.mem ∧ t.gpr .r7 = off B (dA + 64 * i) ∧
      t.gpr .r12 = off B (dS + 8 * p + 64 * i) ∧ (t.gpr .r4).toNat ≤ 2 ∧ t.ca = false) ∧ Keep grpRegs s t)
    (fun i hi t ⟨⟨e, o, t7, t12, t4, tc⟩, k⟩ t9 => ?_)
    ⟨⟨by simp [wordsVal], Outside.refl _ _ _ _, h7, h12, h4, hca⟩, Keep.refl _ _⟩ h9)
    fun t ⟨⟨⟨e, o, t7, t12, t4, tc⟩, k⟩, t9⟩ => ⟨⟨e, o, t7, t12, t9, t4, tc⟩, k⟩
  have ht : Scr t B Z := hs.congr k.wr
  have wa : wordsVal t.mem B (dA + 64 * i) 8 = wordsVal s.mem B (dA + 64 * i) 8 :=
    o.wordsVal (by omega_using [hsep, hp, hi]) (by omega_using [hA, hnw, hi])
  refine WP.mono (triGroup_ok (p := p + 8 * i) ht (by rw [k.gpr _ (by decide), h0]) t7
    (by rw [t12, show dS + 8 * p + 64 * i = dS + 8 * (p + 8 * i) by omega_using []]) t9 (by omega_using [hi]) t4 (by omega_using [hA, hi]) hS
    (by omega_using [hsep, hi]) (by omega_using [hp, hi])) fun u ⟨⟨eu, ou, u7, u12, u9, u4, uc⟩, ku⟩ => ⟨⟨⟨?_, ?_, ?_, ?_, u4, uc⟩, (k.trans ku).mono
      fun r hr => by simp only [List.mem_append, or_self] at hr; exact hr⟩, u9⟩
  · have r8 : rv t smr 8 = rv s smr 8 := rv_congr 8 fun j hj => k.gpr _ (by revert j; decide)
    rw [show p + 8 * (i + 1) = p + 8 * i + 8 by omega_using [], eu, e, r8, wa, show 8 * (i + 1) = 8 * i + 8 by omega_using [],
      fios_wordsVal_append, show dA + 8 * (8 * i) = dA + 64 * i by omega_using [],
      show 64 * (p + 8 * i) = 64 * p + 64 * (8 * i) by omega_using [], Nat.pow_add]
    grind
  · exact (o.mono (Nat.le_refl _) (by omega_using [])).trans (ou.mono (by omega_using []) (by omega_using []))
  · rw [u7, show dA + 64 * i + 64 = dA + 64 * (i + 1) by omega_using []]
  · rw [u12, show dS + 8 * (p + 8 * i) + 64 = dS + 8 * p + 64 * (i + 1) by omega_using []]

/-! ## A block of the triangle -/

theorem psum_trunc (f : Nat → Nat) (r : Nat) : ∀ n, r ≤ n → psum (fun c => if c < r then f c else 0) n = psum f r
  | 0, h => by rw [Nat.le_zero.mp h]; rfl
  | n + 1, h => by
    rcases Nat.lt_or_ge n r with hn | hn
    · have : r = n + 1 := by omega_using [h, hn]
      subst this
      exact psum_congr fun j hj => by simp [hj]
    · rw [psum, psum_trunc f r n hn]; simp [show ¬n < r by omega_using [hn]]

theorem wordsVal_psum (m : Mem) (B : Addr) (d n : Nat) :
    wordsVal m B d n = psum (fun j => (word m B (d + 8 * j)).toNat) n := by
  have := psum_mulw 1 m B d n
  simp only [Nat.one_mul] at this
  exact this.symm

/-- The rows of a block's own words (`triRow0`), the block's words in `smr`
(those of `mA` at `dB`): `2⁵¹² V' + [out] = V + D` for the block's products
within it, `D`. -/
theorem triRows0_ok {s : State} {B : Addr} {Z dT dB : Nat} {mA : Mem} (hs : Scr s B Z) (h0 : s.gpr .r0 = 0)
    (h12 : s.gpr .r12 = off B dT) (hT : dT + 64 ≤ Z) (hb : ∀ c < 8, s.gpr (smr c) = word mA B (dB + 8 * c))
    (h4 : (s.gpr .r4).toNat ≤ 2) :
    WP isa (.block ((List.range 8).flatMap triRow0)) s fun t =>
      (2 ^ (64 * 8) * Vw t .r0 + wordsVal t.mem B dT 8 =
          Vw s .r4 + psum (fun r => wordsVal mA B dB r * (word mA B (dB + 8 * r)).toNat) 8 ∧
        Outside B dT 64 s.mem t.mem ∧ t.gpr .r12 = s.gpr .r12 ∧ (∀ c < 8, t.gpr (smr c) = s.gpr (smr c)) ∧
        t.gpr .r0 = 0) ∧ Keep rowRegs s t := by
  have hnw := hs.nowrap
  refine WP.mono (rowsN_ok (C := fun r _ => wordsVal mA B dB r * (word mA B (dB + 8 * r)).toNat)
    (I := fun u => Scr u B Z ∧ u.gpr .r0 = 0 ∧ u.gpr .r12 = off B dT ∧ ∀ c < 8, u.gpr (smr c) = s.gpr (smr c))
    (L := rowRegs) (B := B) (dT := dT) (by omega_using [hT, hnw]) (fun r hr u ⟨hu, u0, u12, ub⟩ hst => ?_)
    (fun r hr u t w ⟨hu, u0, u12, ub⟩ k m => ⟨hu.congr k.wr, by rw [k.gpr _ (by decide), u0],
      by rw [k.gpr _ (by decide), u12], fun c hc => by rw [k.gpr _ (by revert c; decide), ub c hc]⟩)
    (fun u h => h.2.1) 8 (Nat.le_refl _) s ⟨hs, h0, h12, fun _ _ => rfl⟩ h4)
    fun t ⟨⟨e, o, ⟨_, t0, t12, tb⟩⟩, k⟩ => ⟨⟨e, o, by rw [t12, h12], tb, t0⟩, k⟩
  refine WP.mono (triRow0_ok hu u0 hr u12 (by omega_using [hT, hr]) hst) fun t ⟨⟨w, mt, et⟩, kt⟩ => ⟨⟨w, mt, ?_⟩, kt.mono fun _ hr => List.mem_cons_of_mem _ hr⟩
  rw [et]
  congr 1
  have hp : rv u (fun c => if c < r then smr c else .r0) 8 = wordsVal mA B dB r := by
    unfold rv
    rw [psum_congr (g := fun c => if c < r then (u.gpr (smr c)).toNat else 0) fun j hj => by
      by_cases h : j < r <;> simp [h, u0], psum_trunc _ r 8 (by omega_using [hr]), wordsVal_psum]
    exact psum_congr fun j hj => by rw [ub j (by omega_using [hr, hj]), hb j (by omega_using [hr, hj])]
  rw [hp, ub r hr, hb r hr]

theorem notin8 {f : Nat → Reg} {r : Reg} (h : ∀ j < 8, f j ≠ r) : r ∉ (List.range 8).map f := by
  simp only [List.mem_map, List.mem_range, not_exists, not_and]; exact fun j hj e => h j hj e

/-- The registers the start of a block of the triangle writes. -/
abbrev headRegs : List Reg :=
  .r12 :: .r30 :: .r4 :: .r7 :: .r9 :: .r3 :: ((List.range 8).map smr ++ (List.range 8).map sacc)

/-- The registers a block of the triangle writes. -/
abbrev triRegs : List Reg := .r6 :: .r10 :: headRegs

/-- `tot` after eight rows (`2⁵¹² V₀ + [out] = W + C`, from a window `W` at
word `p` of `m₀`) and a boundary: `S`'s value with the window `W`, and `C`. -/
theorem tot_eq {t : State} {m₀ m₁ : Mem} {B : Addr} {Z dS N p V0 W C : Nat} (hnw : B.toNat + Z ≤ 2 ^ 64)
    (hS : dS + 8 * N ≤ Z) (hp : p + 16 ≤ N) (mt : t.mem = m₁) (o : Outside B (dS + 8 * p) 64 m₀ m₁)
    (ev : Vw t .r4 = V0 + wordsVal m₁ B (dS + 8 * p + 64) 8)
    (er : 2 ^ (64 * 8) * V0 + wordsVal m₁ B (dS + 8 * p) 8 = W + C) :
    tot t B dS N (p + 8) = wordsVal m₀ B dS p + 2 ^ (64 * p) * (W + 2 ^ (64 * 8) *
      wordsVal m₀ B (dS + 8 * p + 64) (N - p - 8)) + 2 ^ (64 * p) * C := by
  have hw : ∀ d k, (d + 8 * k ≤ dS + 8 * p ∨ dS + 8 * p + 64 ≤ d) → d + 8 * k ≤ Z →
      wordsVal m₁ B d k = wordsVal m₀ B d k := fun d k h1 h2 => o.wordsVal h1 (by omega_using [hnw, h2])
  have A1 : wordsVal m₁ B dS (p + 8) = wordsVal m₀ B dS p + 2 ^ (64 * p) * wordsVal m₁ B (dS + 8 * p) 8 := by
    rw [fios_wordsVal_append, hw dS p (Or.inl (by omega_using [])) (by omega_using [hS, hp])]
  have A2 : wordsVal m₁ B (dS + 8 * (p + 8) + 64) (N - (p + 8) - 8) =
      wordsVal m₀ B (dS + 8 * p + 128) (N - p - 16) := by
    rw [show dS + 8 * (p + 8) + 64 = dS + 8 * p + 128 by omega_using [], show N - (p + 8) - 8 = N - p - 16 by omega_using []]
    exact hw _ _ (Or.inr (by omega_using [])) (by omega_using [hS, hp])
  have A3 : wordsVal m₁ B (dS + 8 * p + 64) 8 = wordsVal m₀ B (dS + 8 * p + 64) 8 :=
    hw _ _ (Or.inr (by omega_using [])) (by omega_using [hS, hp])
  have A4 : wordsVal m₀ B (dS + 8 * p + 64) (N - p - 8) = wordsVal m₀ B (dS + 8 * p + 64) 8 +
      2 ^ (64 * 8) * wordsVal m₀ B (dS + 8 * p + 128) (N - p - 16) := by
    rw [show N - p - 8 = 8 + (N - p - 16) by omega_using [hp], fios_wordsVal_append,
      show dS + 8 * p + 64 + 8 * 8 = dS + 8 * p + 128 by omega_using []]
  have P : 2 ^ (64 * (p + 8)) = 2 ^ (64 * p) * 2 ^ (64 * 8) := by rw [← Nat.pow_add, Nat.mul_add]
  unfold tot
  rw [mt, ev, A1, A2, A3, A4, P]
  exact tot_arith er

/-- The loads at the start of a block of the triangle: its words of `a` (at
`dB`) into `smr`, `S`'s words `p` to `p + 7` into the window, `r4` and CA
clear. -/
theorem triLoad_ok {s : State} {B : Addr} {Z dB dS p : Nat} (hs : Scr s B Z) (h0 : s.gpr .r0 = 0)
    (h6 : s.gpr .r6 = off B dB) (h10 : s.gpr .r10 = off B (dS + 8 * p)) (hB : dB + 64 ≤ Z)
    (hS : dS + 8 * p + 64 ≤ Z) :
    WP isa (.block (load8 smr .r6 ++ ([.addi .r12 .r10 0] : List Instr) ++ load8 sacc .r12 ++
      ([.li .r4 0, .addc .r30 .r0 .r0] : List Instr))) s fun t =>
      (Vw t .r4 = wordsVal s.mem B (dS + 8 * p) 8 ∧ t.gpr .r4 = 0 ∧ t.gpr .r12 = off B (dS + 8 * p) ∧
        (∀ c < 8, t.gpr (smr c) = word s.mem B (dB + 8 * c)) ∧ t.mem = s.mem) ∧
      Keep (.r30 :: .r4 :: .r12 :: ((List.range 8).map smr ++ (List.range 8).map sacc)) s t := by
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [WP.block_append_iff]
  refine WP.mono (load8_ok hs h6 hB (by decide) (by decide)) fun u₁ ⟨⟨_, m₁, _, g₁⟩, k₁⟩ => ?_
  refine wp_addi (by decide) (by decide) fun u₂ w₂ f₂ _ => ?_
  have hu₂ : Scr u₂ B Z := (hs.congr k₁.wr).congr w₂.wr
  have p12 : u₂.gpr .r12 = off B (dS + 8 * p) := by
    rw [f₂, k₁.gpr _ (by decide), h10]; exact BitVec.add_zero _
  rw [WP.block_append_iff]
  refine WP.mono (load8_ok hu₂ p12 hS (by decide) (by decide)) fun u₃ ⟨⟨e₃, m₃, _, _⟩, k₃⟩ => ?_
  refine wp_write (exec_li (by decide)) fun u₄ w₄ f₄ _ => ?_
  refine wp_addc fun t w₅ f₅ => WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · have z4 : u₄.gpr .r0 = 0 := by rw [w₄.gpr _ (by decide), k₃.gpr _ (by decide), w₂.gpr _ (by decide),
      k₁.gpr _ (by decide), h0]
    rw [z4] at f₅
    have := (t.gpr .r30).isLt
    have ca : t.ca = false := by
      cases h : t.ca
      · rfl
      · rw [h] at f₅; simp at f₅
    have ra : rv t sacc 8 = rv u₃ sacc 8 :=
      rv_congr 8 fun j hj => by rw [w₅.gpr _ (sacc_ne j hj).1, w₄.gpr _ (sacc_ne j hj).2.1]
    unfold Vw
    rw [ra, e₃, w₂.mem, m₁, w₅.gpr _ (by decide), f₄, ca]
    simp
  · rw [w₅.gpr _ (by decide), f₄]; rfl
  · rw [w₅.gpr _ (by decide), w₄.gpr _ (by decide), k₃.gpr _ (by decide), p12]
  · intro c hc
    have hs1 : ∀ c < 8, smr c ≠ .r30 ∧ smr c ≠ .r4 ∧ smr c ≠ .r12 ∧ ∀ j < 8, sacc j ≠ smr c := by decide
    obtain ⟨a1, a2, a3, a4⟩ := hs1 c hc
    rw [w₅.gpr _ a1, w₄.gpr _ a2, k₃.gpr _ (notin8 a4), w₂.gpr _ a3, g₁ c hc]
  · rw [w₅.mem, w₄.mem, m₃, w₂.mem, m₁]
  · exact ((((k₁.trans w₂.keep).trans k₃).trans w₄.keep).trans w₅.keep).mono fun r hr => by
      simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil, or_false] at hr ⊢
      grind

/-- The groups' count of a block (`h - 1`, from the blocks to go, `h`) and
`r7` at the words of `a` above the block. -/
theorem triCnt_ok {s : State} {B : Addr} {dB h : Nat} (h6 : s.gpr .r6 = off B dB) (h9 : s.gpr .r9 = cnt h 0)
    (hh : 1 ≤ h) (hh' : h < 2 ^ 32) :
    WP isa (.block [.lsr .d .r30 .r9 32, .subi .r30 .r30 1, .logic .or .r9 .r9 .r30, .addi .r7 .r6 64]) s fun t =>
      (t.gpr .r7 = off B (dB + 64) ∧ t.gpr .r9 = cnt h (h - 1) ∧ t.mem = s.mem ∧ t.ca = s.ca) ∧
        Keep [.r30, .r9, .r7] s t := by
  refine wp_write (exec_lsr_d (by decide)) fun v₁ x₁ f₈ c₈ => ?_
  refine wp_write (exec_subi (by decide) (by decide)) fun v₂ x₂ f₉ c₉ => ?_
  refine wp_write exec_logic fun v₃ x₃ f₁₀ c₁₀ => ?_
  refine wp_addi (by decide) (by decide) fun t x₄ f₁₁ c₁₁ => WP.block_nil ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [f₁₁, x₃.gpr _ (by decide), x₂.gpr _ (by decide), x₁.gpr _ (by decide), h6, off_add]
  · rw [x₄.gpr _ (by decide), f₁₀, x₂.gpr _ (by decide), x₁.gpr _ (by decide), f₉, f₈, h9,
      cnt_hi hh' (by decide), show BitVec.ofNat 64 1 = 1#64 from rfl, ofNat_sub_one hh (by omega_using [hh']),
      cnt_or hh' (by omega_using [hh'])]
  · rw [x₄.mem, x₃.mem, x₂.mem, x₁.mem]
  · rw [c₁₁, c₁₀, c₉, c₈]
  · exact (((x₁.keep.trans x₂.keep).trans x₃.keep).trans x₄.keep).mono fun r hr => by
      simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with ((rfl | rfl) | rfl) | rfl <;> decide

/-- The start of a block of the triangle, its words of `a` at `dB` and the
window at `S`'s word `p`: the block's products within it into `S`, the window
on at its word `p + 8`, and `h - 1` groups to go in `r9`'s low half. -/
theorem triHead_ok {s : State} {B : Addr} {Z dB dS N p h : Nat} (hs : Scr s B Z) (h0 : s.gpr .r0 = 0)
    (h6 : s.gpr .r6 = off B dB) (h10 : s.gpr .r10 = off B (dS + 8 * p)) (h9 : s.gpr .r9 = cnt h 0)
    (hh : 1 ≤ h) (hh' : h < 2 ^ 32) (hB : dB + 64 ≤ Z) (hS : dS + 8 * N ≤ Z) (hp : p + 16 ≤ N) :
    WP isa (.block (load8 smr .r6 ++ ([.addi .r12 .r10 0] : List Instr) ++ load8 sacc .r12 ++
      ([.li .r4 0, .addc .r30 .r0 .r0] : List Instr) ++ (List.range 8).flatMap triRow0 ++
      ([.addi .r12 .r12 64] : List Instr) ++ boundary8 .r12 ++
      ([.lsr .d .r30 .r9 32, .subi .r30 .r30 1, .logic .or .r9 .r9 .r30, .addi .r7 .r6 64] : List Instr))) s fun t =>
      (tot t B dS N (p + 8) = wordsVal s.mem B dS N +
          2 ^ (64 * p) * psum (fun r => wordsVal s.mem B dB r * (word s.mem B (dB + 8 * r)).toNat) 8 ∧
        Outside B (dS + 8 * p) 64 s.mem t.mem ∧ t.gpr .r12 = off B (dS + 8 * p + 64) ∧
        t.gpr .r7 = off B (dB + 64) ∧ t.gpr .r9 = cnt h (h - 1) ∧ (t.gpr .r4).toNat ≤ 2 ∧ t.ca = false ∧
        rv t smr 8 = wordsVal s.mem B dB 8 ∧ t.gpr .r0 = 0) ∧ Keep headRegs s t := by
  have hnw := hs.nowrap
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (triLoad_ok hs h0 h6 h10 hB (by omega_using [hS, hp])) fun u₅ ⟨⟨v₅, r4₅, p12₅, hb, mu5⟩, K₅⟩ => ?_
  have hu₅ : Scr u₅ B Z := hs.congr K₅.wr
  have z5 : u₅.gpr .r0 = 0 := by rw [K₅.gpr _ (by decide), h0]
  refine WP.mono (triRows0_ok hu₅ z5 p12₅ (by omega_using [hS, hp]) hb (by rw [r4₅]; decide))
    fun t₁ ⟨⟨e₆, o₆, t12, tb, t0⟩, k₆⟩ => ?_
  refine wp_addi (by decide) (by decide) fun u₆ w₆ f₆ c₆ => WP.block_nil ?_
  have hu₆ : Scr u₆ B Z := (hu₅.congr k₆.wr).congr w₆.wr
  have p12₆ : u₆.gpr .r12 = off B (dS + 8 * p + 64) := by rw [f₆, t12, p12₅, off_add]
  refine WP.mono (boundary8_ok hu₆ (by rw [w₆.gpr _ (by decide), t0]) p12₆ (by omega_using [hS, hp]) (by decide) (by decide)
    (by decide)) fun t₂ ⟨⟨e₇, l₇, c₇, m₇⟩, k₇⟩ => ?_
  have K₇ : Keep (.r30 :: .r4 :: .r12 :: .r3 :: ((List.range 8).map smr ++ (List.range 8).map sacc)) s t₂ :=
    (((K₅.trans k₆).trans w₆.keep).trans k₇).mono fun r hr => by
      simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil, or_false] at hr ⊢
      grind
  refine WP.mono (triCnt_ok (by rw [K₇.gpr _ (by decide), h6]) (by rw [K₇.gpr _ (by decide), h9]) hh hh')
    fun t ⟨⟨t7, t9, mt, ct⟩, Kt⟩ => ⟨⟨?_, ?_, ?_, t7, t9, ?_, by rw [ct]; exact c₇, ?_, ?_⟩, ?_⟩
  · have v₆ : Vw u₆ .r0 = Vw t₁ .r0 :=
      Vw_congr (fun j hj => w₆.gpr _ (by revert j; decide)) (w₆.gpr _ (by decide)) c₆
    have vt : Vw t .r4 = Vw t₂ .r4 := by
      unfold Vw
      rw [rv_congr 8 fun j hj => Kt.gpr _ (by revert j; decide), Kt.gpr .r4 (by decide), ct]
    rw [w₆.mem, v₆] at e₇
    rw [v₅] at e₆
    rw [tot_eq hnw hS hp (by rw [mt, m₇, w₆.mem]) (mu5 ▸ o₆) (vt.trans e₇) e₆]
    have : wordsVal s.mem B dS N = wordsVal s.mem B dS (p + (8 + (N - p - 8))) := by congr 1; omega_using [hp]
    rw [this, fios_wordsVal_append, fios_wordsVal_append, show dS + 8 * p + 8 * 8 = dS + 8 * p + 64 by omega_using []]
  · rw [mt, m₇, w₆.mem, ← mu5]; exact o₆
  · rw [Kt.gpr _ (by decide), k₇.gpr _ (by decide)]; exact p12₆
  · rw [Kt.gpr _ (by decide)]; exact l₇
  · have r8 : rv t smr 8 = rv u₅ smr 8 := rv_congr 8 fun j hj => by
      rw [Kt.gpr _ (by revert j; decide), k₇.gpr _ (by revert j; decide), w₆.gpr _ (by revert j; decide), tb j hj]
    rw [r8, wordsVal_psum]
    exact psum_congr fun j hj => by rw [hb j hj]
  · rw [Kt.gpr _ (by decide), k₇.gpr _ (by decide), w₆.gpr _ (by decide), t0]
  · exact (K₇.trans Kt).mono fun r hr => by
      simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil, or_false] at hr ⊢
      grind

/-- The end of a block of the triangle: the window and the word above it
stored at `S`'s word `q`, the pointers on a block, one block less in `r9`'s
high half, and that count in `r30`. -/
theorem triTail_ok {s : State} {B : Addr} {Z dq dB dP h : Nat} (hs : Scr s B Z) (h12 : s.gpr .r12 = off B dq)
    (hq : dq + 72 ≤ Z) (h6 : s.gpr .r6 = off B dB) (h10 : s.gpr .r10 = off B dP) (h9 : s.gpr .r9 = cnt h 0)
    (hh : 1 ≤ h) (hh' : h < 2 ^ 32) :
    WP isa (.block (store8 sacc .r12 ++ ([.store .d .r4 .r12 64, .addi .r6 .r6 64, .addi .r10 .r10 128,
      .li .r30 1, .lsl .r30 .r30 32, .sub .r9 .r9 .r30, .lsr .d .r30 .r9 32] : List Instr))) s fun t =>
      (wordsVal t.mem B dq 9 = rv s sacc 8 + 2 ^ (64 * 8) * (s.gpr .r4).toNat ∧ Outside B dq 72 s.mem t.mem ∧
        t.gpr .r6 = off B (dB + 64) ∧ t.gpr .r10 = off B (dP + 128) ∧ t.gpr .r9 = cnt (h - 1) 0 ∧
        t.gpr .r30 = BitVec.ofNat 64 (h - 1)) ∧ Keep [.r6, .r10, .r30, .r9] s t := by
  have hnw := hs.nowrap
  rw [WP.block_append_iff]
  refine WP.mono (store8_ok hs h12 (by omega_using [hq]) (by decide)) fun u ⟨⟨eu, ou, _⟩, ku⟩ => ?_
  refine wp_st (by decide) ⟨by decide, by decide⟩ (by rw [ku.gpr _ (by simp), h12, off_add])
    ((hs.congr ku.wr).st (by omega_using [hq])) fun u₁ k₁ m₁ _ => ?_
  refine wp_addi (by decide) (by decide) fun u₂ w₂ f₂ _ => ?_
  refine wp_addi (by decide) (by decide) fun u₃ w₃ f₃ _ => ?_
  refine wp_write (exec_li (by decide)) fun u₄ w₄ f₄ _ => ?_
  refine wp_write (exec_lsl (by decide)) fun u₅ w₅ f₅ _ => ?_
  refine wp_write exec_sub fun u₆ w₆ f₆ _ => ?_
  refine wp_write (exec_lsr_d (by decide)) fun t w₇ f₇ _ => WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  all_goals have mt : t.mem = u₁.mem := by rw [w₇.mem, w₆.mem, w₅.mem, w₄.mem, w₃.mem, w₂.mem]
  · rw [mt, m₁, wordsVal_succ_top, (writeW_outside u.mem B _ (by omega_using [hq, hnw])).wordsVal (Or.inl (by omega_using [])) (by omega_using [hq, hnw]),
      eu, show dq + 8 * 8 = dq + 64 by omega_using [], word_writeW_self, ku.gpr _ (by simp)]
  · rw [mt, m₁]
    exact (ou.mono (Nat.le_refl _) (by omega_using [])).trans ((writeW_outside _ B _ (by omega_using [hq, hnw])).mono (by omega_using []) (by omega_using []))
  · rw [w₇.gpr _ (by decide), w₆.gpr _ (by decide), w₅.gpr _ (by decide), w₄.gpr _ (by decide),
      w₃.gpr _ (by decide), f₂, k₁.gpr _ (by simp), ku.gpr _ (by simp), h6, off_add]
  · rw [w₇.gpr _ (by decide), w₆.gpr _ (by decide), w₅.gpr _ (by decide), w₄.gpr _ (by decide), f₃,
      w₂.gpr _ (by decide), k₁.gpr _ (by simp), ku.gpr _ (by simp), h10, off_add]
  · rw [w₇.gpr _ (by decide), f₆, f₅, w₅.gpr _ (by decide), f₄, w₄.gpr _ (by decide), w₃.gpr _ (by decide),
      w₂.gpr _ (by decide), k₁.gpr _ (by simp), ku.gpr _ (by simp), h9, cnt_decHi hh' hh]
  · rw [f₇, f₆, f₅, w₅.gpr _ (by decide), f₄, w₄.gpr _ (by decide),
      w₃.gpr _ (by decide), w₂.gpr _ (by decide), k₁.gpr _ (by simp), ku.gpr _ (by simp), h9, cnt_decHi hh' hh,
      cnt_hi (by omega_using [hh']) (by decide)]
  · exact ((((((ku.trans k₁).trans w₂.keep).trans w₃.keep).trans w₄.keep).trans (w₅.keep.trans w₆.keep)).trans
      w₇.keep).mono fun r hr => by
        simp only [List.mem_append, List.mem_singleton, List.not_mem_nil, false_or, or_false] at hr
        rcases hr with ((((rfl | rfl) | rfl) | rfl | rfl) | rfl) <;> decide

/-- `S`'s value once a block's window and the word above it are stored at its
word `q`, where `S` was 0: `tot` at `q`. -/
theorem tot_close {t₂ t : State} {B : Addr} {Z dS N q : Nat} (hnw : B.toNat + Z ≤ 2 ^ 64) (hS : dS + 8 * N ≤ Z)
    (hq : q + 9 ≤ N) (hz : word t₂.mem B (dS + 8 * q + 64) = 0) (hc : t₂.ca = false)
    (et : wordsVal t.mem B (dS + 8 * q) 9 = rv t₂ sacc 8 + 2 ^ (64 * 8) * (t₂.gpr .r4).toNat)
    (o : Outside B (dS + 8 * q) 72 t₂.mem t.mem) :
    wordsVal t.mem B dS N = tot t₂ B dS N q := by
  have h1 := fios_wordsVal_append t.mem B dS q (N - q)
  rw [Nat.add_sub_cancel' (by omega_using [hq] : q ≤ N), show N - q = 9 + (N - q - 9) by omega_using [hq], fios_wordsVal_append] at h1
  rw [h1, o.wordsVal (Or.inl (by omega_using [])) (by omega_using [hnw, hS, hq]),
    o.wordsVal (d := dS + 8 * q + 8 * 9) (Or.inr (by omega_using [])) (by omega_using [hnw, hS, hq]), et]
  unfold tot Vw
  rw [show N - q - 8 = 1 + (N - q - 9) by omega_using [hq], fios_wordsVal_append,
    show wordsVal t₂.mem B (dS + 8 * q + 64) 1 = (word t₂.mem B (dS + 8 * q + 64)).toNat by simp [wordsVal], hz, hc,
    show dS + 8 * q + 64 + 8 * 1 = dS + 8 * q + 8 * 9 by omega_using [], pow512,
    show 64 * 9 = 64 + 64 * 8 by rfl, Nat.pow_add, show (64 * 1 : Nat) = 64 by rfl]
  simp only [Bool.toNat_false, Nat.add_zero, show (0 : BitVec 64).toNat = 0 from rfl, Nat.zero_add]
  grind

/-- One block of the triangle (`triBlock`), block `k` of `K` (`w = 8 K`): `S`
(its `16 K + 1` words at `dS`) takes in what block `k` adds (`triInc`). -/
theorem triBlock_ok {s : State} {B : Addr} {Z da dS K k : Nat} (hs : Scr s B Z) (h0 : s.gpr .r0 = 0)
    (h6 : s.gpr .r6 = off B (da + 64 * k)) (h10 : s.gpr .r10 = off B (dS + 8 * (16 * k)))
    (h9 : s.gpr .r9 = cnt (K - k) 0) (hk : k < K) (hK : K < 2 ^ 32) (ha : da + 64 * K ≤ Z)
    (hS : dS + 8 * (16 * K + 1) ≤ Z) (hsep : da + 64 * K ≤ dS ∨ dS + 8 * (16 * K + 1) ≤ da)
    (hz : ∀ i, 8 * K + 8 * k + 1 ≤ i → i < 16 * K + 1 → word s.mem B (dS + 8 * i) = 0) :
    WP isa triBlock s fun t =>
      (wordsVal t.mem B dS (16 * K + 1) = wordsVal s.mem B dS (16 * K + 1) + triInc s.mem B da (8 * K) k ∧
        (∀ i, 8 * K + 8 * (k + 1) + 1 ≤ i → i < 16 * K + 1 → word t.mem B (dS + 8 * i) = 0) ∧
        Outside B dS (8 * (16 * K + 1)) s.mem t.mem ∧ t.gpr .r6 = off B (da + 64 * (k + 1)) ∧
        t.gpr .r10 = off B (dS + 8 * (16 * (k + 1))) ∧ t.gpr .r9 = cnt (K - k - 1) 0 ∧
        t.gpr .r30 = BitVec.ofNat 64 (K - k - 1) ∧ t.gpr .r0 = 0) ∧ Keep triRegs s t := by
  have hnw := hs.nowrap
  unfold triBlock
  refine WP.seq (WP.mono (triHead_ok (dB := da + 64 * k) (N := 16 * K + 1) hs h0 h6 h10 h9 (by omega_using [hk]) (by omega_using [hK])
    (by omega_using [hk, ha]) hS (by omega_using [hk])) fun t₁ ⟨⟨e₁, o₁, r12₁, r7₁, r9₁, r4₁, c₁, b₁, z₁⟩, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.wr
  refine WP.seq (WP.mono (triGroups_ok (p := 16 * k + 8) (N := 16 * K + 1) (G := K - k - 1) hs₁ z₁ r7₁
    (by rw [r12₁, show dS + 8 * (16 * k) + 64 = dS + 8 * (16 * k + 8) by omega_using []]) r9₁ (by omega_using [hK]) r4₁ c₁
    (by omega_using [hk, ha]) hS (by omega_using [hk, hsep]) (by omega_using [hk])) fun t₂ ⟨⟨e₂, o₂, _, r12₂, r9₂, r4₂, c₂⟩, k₂⟩ => ?_)
  have hs₂ := hs₁.congr k₂.wr
  have q : 16 * k + 8 + 8 * (K - k - 1) = 8 * K + 8 * k := by omega_using [hk]
  have g₂ : ∀ r, r ∉ headRegs → t₂.gpr r = s.gpr r := fun r hr => by
    rw [k₂.gpr r fun h => hr (by simp only [grpRegs, rowRegs, List.mem_cons] at h ⊢; grind), k₁.gpr r hr]
  refine WP.mono (triTail_ok (dq := dS + 8 * (8 * K + 8 * k)) (dB := da + 64 * k) (dP := dS + 8 * (16 * k)) hs₂
    (by rw [r12₂, show dS + 8 * (16 * k + 8) + 64 * (K - k - 1) = dS + 8 * (8 * K + 8 * k) by omega_using [hk]]) (by omega_using [hk, hS])
    (by rw [g₂ _ (by decide), h6]) (by rw [g₂ _ (by decide), h10]) r9₂ (by omega_using [hk]) (by omega_using [hK]))
    fun t ⟨⟨e₃, o₃, r6₃, r10₃, r9₃, r30₃⟩, k₃⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  -- The memory: what changed is `S`'s words `16 k` to `8 K + 8 k + 8`.
  all_goals have O₂ : Outside B dS (8 * (8 * K + 8 * k)) s.mem t₂.mem :=
    (o₁.mono (by omega_using []) (by omega_using [hk])).trans (o₂.mono (by omega_using []) (by omega_using [hk]))
  all_goals have O₃ : Outside B dS (8 * (8 * K + 8 * k + 9)) s.mem t.mem :=
    (O₂.mono (Nat.le_refl _) (by omega_using [])).trans (o₃.mono (by omega_using []) (by omega_using []))
  · have hz₂ : word t₂.mem B (dS + 8 * (8 * K + 8 * k) + 64) = 0 := by
      rw [O₂.word (Or.inr (by omega_using [])) (by omega_using [hk, hS, hnw]), show dS + 8 * (8 * K + 8 * k) + 64 = dS + 8 * (8 * K + 8 * k + 8) by omega_using []]
      exact hz _ (by omega_using []) (by omega_using [hk])
    rw [tot_close hnw hS (by omega_using [hk]) hz₂ c₂ e₃ o₃, ← q, e₂, e₁]
    have wa : wordsVal t₁.mem B (da + 64 * k + 64) (8 * (K - k - 1)) =
        wordsVal s.mem B (da + 64 * (k + 1)) (8 * K - 8 * (k + 1)) := by
      rw [o₁.wordsVal (by omega_using [hk, hsep]) (by omega_using [hk, ha, hnw]), show da + 64 * k + 64 = da + 64 * (k + 1) by omega_using [],
        show 8 * (K - k - 1) = 8 * K - 8 * (k + 1) by omega_using []]
    rw [b₁, wa]
    unfold triInc triD
    rw [show 16 * k + 8 = 16 * k + 8 from rfl]
    grind
  · intro i hi hi'
    rw [O₃.word (Or.inr (by omega_using [hi])) (by omega_using [hS, hnw, hi'])]
    exact hz i (by omega_using [hi]) hi'
  · exact O₃.mono (Nat.le_refl _) (by omega_using [hk])
  · rw [r6₃, show da + 64 * k + 64 = da + 64 * (k + 1) by omega_using []]
  · rw [r10₃, show dS + 8 * (16 * k) + 128 = dS + 8 * (16 * (k + 1)) by omega_using []]
  · rw [r9₃, show K - k - 1 = K - k - 1 from rfl]
  · exact r30₃
  · rw [k₃.gpr _ (by decide), g₂ _ (by decide), h0]
  · exact ((k₁.trans k₂).trans k₃).mono fun r hr => by
      simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil, or_false] at hr ⊢
      grind

/-! ## The triangle -/

theorem off_off (B : Addr) (a b : Nat) : off (off B a) b = off B (a + b) := by
  simp only [off, BitVec.add_assoc, BitVec.ofNat_add]

theorem off_sub (B : Addr) {a k : Nat} (h : k ≤ a) : off B a - BitVec.ofNat 64 k = off B (a - k) :=
  VG.Offset.add_ofNat_sub _ h

theorem wordsVal_zero_word {m : Mem} {B : Addr} {d n : Nat} (h : wordsVal m B d n = 0) {i : Nat} (hi : i < n) :
    word m B (d + 8 * i) = 0 := by
  have e := fios_wordsVal_append m B d i (n - i)
  rw [Nat.add_sub_cancel' (by omega_using [hi] : i ≤ n), show n - i = 1 + (n - i - 1) by omega_using [hi], fios_wordsVal_append, h] at e
  obtain ⟨-, e2⟩ := Nat.add_eq_zero_iff.mp e.symm
  rcases Nat.mul_eq_zero.mp e2 with h2 | h2
  · exact absurd h2 (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _))
  · obtain ⟨h1, -⟩ := Nat.add_eq_zero_iff.mp h2
    simp only [wordsVal, Nat.mul_zero, Nat.add_zero] at h1
    exact BitVec.eq_of_toNat_eq h1

/-- What a block adds depends only on `a`'s words. -/
theorem triInc_out {m m' : Mem} {B : Addr} {dS L da w k : Nat} (o : Outside B dS L m m')
    (hsep : da + 8 * w ≤ dS ∨ dS + L ≤ da) (hk : 8 * (k + 1) ≤ w) (hZ : da + 8 * w ≤ 2 ^ 64) :
    triInc m' B da w k = triInc m B da w k := by
  have ow : ∀ d n, da ≤ d → d + 8 * n ≤ da + 8 * w → wordsVal m' B d n = wordsVal m B d n :=
    fun d n h1 h2 => o.wordsVal (by omega_using [hsep, h1, h2]) (by omega_using [hZ, h2])
  unfold triInc triD
  rw [ow _ 8 (by omega_using []) (by omega_using [hk]), ow _ _ (by omega_using []) (by omega_using [hk]),
    psum_congr fun r hr => by rw [ow _ r (by omega_using []) (by omega_using [hk, hr]), o.word (by omega_using [hsep, hk, hr]) (by omega_using [hk, hZ, hr])]]

/-- The registers of the triangle. -/
abbrev sqrTriRegs : List Reg := triRegs

/-- The triangle (`sqrTri`): `S` (`16 K + 1` words at `dS`, zero) := `Σ_{i<j}
aᵢ aⱼ 2^(64 (i + j))`, by blocks (`triS`), for `w = 8 K`. -/
theorem sqrTri_ok {s : State} {B : Addr} {Z da dS K : Nat} (hs : Scr s B Z) (h0 : s.gpr .r0 = 0)
    (h6 : s.gpr .r6 = off B da) (h8 : s.gpr .r8 = off B dS) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * (8 * K)))
    (hK1 : 1 ≤ K) (hK : K < 2 ^ 28) (ha : da + 64 * K ≤ Z) (hS : dS + 8 * (16 * K + 1) ≤ Z)
    (hsep : da + 64 * K ≤ dS ∨ dS + 8 * (16 * K + 1) ≤ da) (hz : wordsVal s.mem B dS (16 * K + 1) = 0) :
    WP isa sqrTri s fun t =>
      (wordsVal t.mem B dS (16 * K + 1) = triS s.mem B da (8 * K) K ∧
        Outside B dS (8 * (16 * K + 1)) s.mem t.mem ∧ t.gpr .r6 = off B da ∧ t.gpr .r10 = off B dS ∧
        t.gpr .r0 = 0) ∧ Keep triRegs s t := by
  have hnw := hs.nowrap
  unfold sqrTri
  refine WP.seq ?_
  -- The block count and the pointers.
  refine wp_addi (by decide) (by decide) fun u₁ w₁ f₁ _ => ?_
  refine wp_write (exec_lsr_d (by decide)) fun u₂ w₂ f₂ _ => ?_
  refine wp_write (exec_lsl (by decide)) fun u₃ w₃ f₃ _ => WP.block_nil ?_
  have k₃ : Keep [.r10, .r30, .r9] s u₃ := ((w₁.keep.trans w₂.keep).trans w₃.keep).mono fun r hr => by
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with (rfl | rfl) | rfl <;> decide
  have r30₂ : u₂.gpr .r30 = BitVec.ofNat 64 K := by
    rw [f₂, w₁.gpr _ (by decide), h11]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (by omega_using [hK]), Nat.mod_eq_of_lt (by omega_using [hK])]; omega_using []
  have r30₃ : u₃.gpr .r30 = BitVec.ofNat 64 K := by rw [w₃.gpr _ (by decide), r30₂]
  have r9₃ : u₃.gpr .r9 = cnt K 0 := by
    rw [f₃, r30₂]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega_using []
  have r10₃ : u₃.gpr .r10 = off B dS := by
    rw [w₃.gpr _ (by decide), w₂.gpr _ (by decide), f₁, h8]; exact BitVec.add_zero _
  have m₃ : u₃.mem = s.mem := by rw [w₃.mem, w₂.mem, w₁.mem]
  let I : Nat → State → Prop := fun k t => Scr t B Z ∧ t.gpr .r0 = 0 ∧ t.gpr .r6 = off B (da + 64 * k) ∧
    t.gpr .r10 = off B (dS + 8 * (16 * k)) ∧ t.gpr .r9 = cnt (K - k) 0 ∧
    wordsVal t.mem B dS (16 * K + 1) = triS s.mem B da (8 * K) k ∧
    (∀ i, 8 * K + 8 * k + 1 ≤ i → i < 16 * K + 1 → word t.mem B (dS + 8 * i) = 0) ∧
    Outside B dS (8 * (16 * K + 1)) s.mem t.mem ∧ Keep triRegs s t
  have I0 : I 0 u₃ := ⟨hs.congr k₃.wr, by rw [k₃.gpr _ (by decide), h0], by simp only [k₃.gpr .r6 (by decide), h6, Nat.mul_zero, Nat.add_zero],
    by simp only [r10₃, Nat.mul_zero, Nat.add_zero], by simp only [r9₃, Nat.sub_zero], by rw [m₃, hz]; rfl,
    fun i _ hi => by rw [m₃]; exact wordsVal_zero_word hz hi, by rw [m₃]; exact Outside.refl _ _ _ _,
    k₃.mono fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide⟩
  refine WP.seq (WP.mono (count_loop (cr := .r30) (n := K) hK1 I (fun k hk t ⟨ht, t0, t6, t10, t9, te, tz, to, tk⟩ =>
    WP.mono (triBlock_ok ht t0 t6 t10 t9 hk (by omega_using [hK]) ha hS hsep tz)
      fun t' ⟨⟨e, z, o, r6, r10, r9, r30, r0⟩, k'⟩ => ⟨⟨ht.congr k'.wr, r0, r6, r10,
        by rw [r9, show K - k - 1 = K - (k + 1) by omega_using []],
        by rw [e, te, triS, triInc_out to (by omega_using [hsep]) (by omega_using [hk]) (by omega_using [ha, hnw])],
        fun i hi hi' => z i (by omega_using [hi]) hi', to.trans o, (tk.trans k').mono fun r hr => by
          simp only [List.mem_append, or_self] at hr; exact hr⟩,
        by rw [r30, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hK])]; omega_using [hk]⟩) I0)
    fun t ⟨ht, t0, t6, t10, _, te, _, to, tk⟩ => ?_)
  have r11 : t.gpr .r11 = s.gpr .r11 := by rw [tk.gpr _ (by decide)]
  refine wp_write (exec_lsl (by decide)) fun v₁ x₁ f₁ _ => ?_
  refine wp_write exec_sub fun v₂ x₂ f₂ _ => ?_
  refine wp_write exec_sub fun v₃ x₃ f₃ _ => ?_
  refine wp_write exec_sub fun v₄ x₄ f₄ _ => WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  all_goals have r30 : v₁.gpr .r30 = BitVec.ofNat 64 (8 * (8 * K)) := by rw [f₁, r11, h11, Mont4.shl2_8]
  · rw [x₄.mem, x₃.mem, x₂.mem, x₁.mem, te]
  · rw [x₄.mem, x₃.mem, x₂.mem, x₁.mem]; exact to
  · rw [x₄.gpr _ (by decide), x₃.gpr _ (by decide), f₂, r30, x₁.gpr _ (by decide), t6, off_sub _ (by omega_using []),
      show da + 64 * K - 8 * (8 * K) = da by omega_using []]
  · rw [f₄, f₃, x₃.gpr .r30 (by decide), x₂.gpr .r30 (by decide), x₂.gpr .r10 (by decide), r30, x₁.gpr .r10 (by decide),
      t10, off_sub _ (by omega_using []),
      off_sub _ (by omega_using []), show dS + 8 * (16 * K) - 8 * (8 * K) - 8 * (8 * K) = dS by omega_using []]
  · rw [x₄.gpr _ (by decide), x₃.gpr _ (by decide), x₂.gpr _ (by decide), x₁.gpr _ (by decide), t0]
  · exact (tk.trans ((((x₁.keep.trans x₂.keep).trans x₃.keep).trans x₄.keep))).mono fun r hr => by
      simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with h | ((h | h) | h) | h
      · exact h
      all_goals (subst h; decide)

/-! ## The doubling -/

theorem shl1_or (x c : BitVec 64) (hc : c.toNat ≤ 1) : (x <<< 1 ||| c).toNat = 2 * x.toNat % 2 ^ 64 + c.toNat := by
  have h1 : (x <<< 1).toNat = (x.toNat % 2 ^ 63) <<< 1 := by
    simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega_using []
  rw [BitVec.toNat_or, h1, ← Nat.shiftLeft_add_eq_or_of_lt (by omega_using [hc] : c.toNat < 2 ^ 1), Nat.shiftLeft_eq]
  omega_using []

theorem shr63 (x : BitVec 64) : (x >>> 63).toNat = x.toNat / 2 ^ 63 := by
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem dbl_arith {x0 x1 a b c y0 y1 z0 z1 c1 c2 lo hi : Nat}
    (ey0 : y0 = 2 * x0 % 2 ^ 64 + b) (ey1 : y1 = 2 * x1 % 2 ^ 64 + x0 / 2 ^ 63)
    (e1 : z0 + 2 ^ 64 * c1 = y0 + lo + c) (e2 : z1 + 2 ^ 64 * c2 = y1 + hi + c1) (elh : lo + 2 ^ 64 * hi = a) :
    z0 + 2 ^ 64 * z1 + 2 ^ 128 * (x1 / 2 ^ 63 + c2) = 2 * (x0 + 2 ^ 64 * x1) + a + b + c := by
  omega_using [ey0, ey1, e1, e2, elh]

/-- A step of the doubling (`dblBody`, and the count): `S`'s words `2 i` and
`2 i + 1` (at `dT`) doubled, the bit shifted in from `r3` and the bit shifted
out into it, and `aᵢ²` (`aᵢ` at `dA`) added with CA. -/
theorem dblStep_ok {s : State} {B : Addr} {Z dT dA : Nat} (hs : Scr s B Z) (h12 : s.gpr .r12 = off B dT)
    (h7 : s.gpr .r7 = off B dA) (h3 : (s.gpr .r3).toNat ≤ 1) (hT : dT + 16 ≤ Z) (hA : dA + 8 ≤ Z) :
    WP isa (.block (dblBody ++ ([.subi .r9 .r9 1] : List Instr))) s fun t =>
      (wordsVal t.mem B dT 2 + 2 ^ 128 * ((t.gpr .r3).toNat + t.ca.toNat) =
          2 * wordsVal s.mem B dT 2 + (word s.mem B dA).toNat * (word s.mem B dA).toNat + (s.gpr .r3).toNat +
            s.ca.toNat ∧
        (t.gpr .r3).toNat ≤ 1 ∧ Outside B dT 16 s.mem t.mem ∧ t.gpr .r12 = off B (dT + 16) ∧
        t.gpr .r7 = off B (dA + 8) ∧ t.gpr .r9 = s.gpr .r9 - BitVec.ofNat 64 1) ∧
      Keep (.r3 :: .r12 :: .r7 :: .r9 :: (List.range 8).map sacc) s t := by
  have hnw := hs.nowrap
  show WP isa (.block [.load .d .r22 .r12 0, .load .d .r23 .r12 8, .load .d .r24 .r7 0, .mul .r25 .r24 .r24,
    .mulhu .r26 .r24 .r24, .lsl .r27 .r22 1, .logic .or .r27 .r27 .r3, .lsr .d .r28 .r22 63, .lsl .r29 .r23 1,
    .logic .or .r29 .r29 .r28, .lsr .d .r3 .r23 63, .adde .r27 .r27 .r25, .adde .r29 .r29 .r26,
    .store .d .r27 .r12 0, .store .d .r29 .r12 8, .addi .r12 .r12 16, .addi .r7 .r7 8, .subi .r9 .r9 1]) s _
  refine wp_ld (by decide) ⟨by decide, by decide⟩ (by rw [h12, off_add, Nat.add_zero]) (hs.ld (by omega_using [hT]))
    fun u₀ w₀ e₀ c₀ => ?_
  refine wp_ld (by decide) ⟨by decide, by decide⟩ (by rw [w₀.gpr _ (by decide), h12, off_add])
    ((hs.congr w₀.wr).ld (by omega_using [hT])) fun u₁ w₁ e₁ c₁ => ?_
  refine wp_ld (by decide) ⟨by decide, by decide⟩ (by rw [w₁.gpr _ (by decide), w₀.gpr _ (by decide), h7, off_add,
    Nat.add_zero]) (((hs.congr w₀.wr).congr w₁.wr).ld (by omega_using [hA])) fun u₂ w₂ e₂ c₂ => ?_
  refine wp_mul fun u₃ w₃ e₃ c₃ => ?_
  refine wp_mulhu fun u₄ w₄ e₄ c₄ => ?_
  refine wp_write (exec_lsl (by decide)) fun u₅ w₅ e₅ c₅ => ?_
  refine wp_write exec_logic fun u₆ w₆ e₆ c₆ => ?_
  refine wp_write (exec_lsr_d (by decide)) fun u₇ w₇ e₇ c₇ => ?_
  refine wp_write (exec_lsl (by decide)) fun u₈ w₈ e₈ c₈ => ?_
  refine wp_write exec_logic fun u₉ w₉ e₉ c₉ => ?_
  refine wp_write (exec_lsr_d (by decide)) fun u₁₀ w₁₀ e₁₀ c₁₀ => ?_
  refine wp_adde fun u₁₁ w₁₁ e₁₁ => ?_
  refine wp_adde fun u₁₂ w₁₂ e₁₂ => ?_
  have K : Keep [.r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r3] s u₁₂ :=
    (((((((((((w₀.keep.trans w₁.keep).trans w₂.keep).trans w₃.keep).trans w₄.keep).trans w₅.keep).trans
      w₆.keep).trans w₇.keep).trans w₈.keep).trans w₉.keep).trans w₁₀.keep).trans w₁₁.keep |>.trans
      w₁₂.keep).mono (by decide)
  have m₁₂ : u₁₂.mem = s.mem := by
    rw [w₁₂.mem, w₁₁.mem, w₁₀.mem, w₉.mem, w₈.mem, w₇.mem, w₆.mem, w₅.mem, w₄.mem, w₃.mem, w₂.mem, w₁.mem, w₀.mem]
  have p12 : u₁₂.gpr .r12 = off B dT := by rw [K.gpr _ (by decide), h12]
  have hs₁₂ : Scr u₁₂ B Z := hs.congr K.wr
  refine wp_st (a := off B dT) (by decide) ⟨by decide, by decide⟩ (by rw [p12, off_add, Nat.add_zero])
    (hs₁₂.st (d := dT) (n := 8) (by omega_using [hT])) fun v₁ k₁ mv₁ cv₁ => ?_
  refine wp_st (by decide) ⟨by decide, by decide⟩ (by rw [k₁.gpr _ (by simp), p12, off_add])
    ((hs₁₂.congr k₁.wr).st (by omega_using [hT])) fun v₂ k₂ mv₂ cv₂ => ?_
  refine wp_addi (by decide) (by decide) fun v₃ x₃ f₃ d₃ => ?_
  refine wp_addi (by decide) (by decide) fun v₄ x₄ f₄ d₄ => ?_
  refine wp_write (exec_subi (by decide) (by decide)) fun t x₅ f₅ d₅ => ?_
  have mt : t.mem = (s.mem.writeW (off B dT) (u₁₂.gpr .r27)).writeW (off B (dT + 8)) (u₁₂.gpr .r29) := by
    rw [x₅.mem, x₄.mem, x₃.mem, mv₂, mv₁, m₁₂, k₁.gpr .r29 (by simp)]
  have g3 : t.gpr .r3 = u₁₀.gpr .r3 := by
    rw [x₅.gpr _ (by decide), x₄.gpr _ (by decide), x₃.gpr _ (by decide), k₂.gpr _ (by simp), k₁.gpr _ (by simp),
      w₁₂.gpr _ (by decide), w₁₁.gpr _ (by decide)]
  have r3v : (u₁₀.gpr .r3).toNat = (word s.mem B (dT + 8)).toNat / 2 ^ 63 := by
    rw [e₁₀, shr63, w₉.gpr _ (by decide), w₈.gpr _ (by decide), w₇.gpr _ (by decide), w₆.gpr _ (by decide),
      w₅.gpr _ (by decide), w₄.gpr _ (by decide), w₃.gpr _ (by decide), w₂.gpr _ (by decide), e₁, w₀.mem]
  refine WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · have x0 : u₆.gpr .r22 = word s.mem B dT := by
      rw [w₆.gpr _ (by decide), w₅.gpr _ (by decide), w₄.gpr _ (by decide), w₃.gpr _ (by decide),
        w₂.gpr _ (by decide), w₁.gpr _ (by decide), e₀]
    have x1 : u₇.gpr .r23 = word s.mem B (dT + 8) := by
      rw [w₇.gpr _ (by decide), w₆.gpr _ (by decide), w₅.gpr _ (by decide), w₄.gpr _ (by decide),
        w₃.gpr _ (by decide), w₂.gpr _ (by decide), e₁, w₀.mem]
    have aa : u₂.gpr .r24 = word s.mem B dA := by rw [e₂, w₁.mem, w₀.mem]
    have y0 : (u₁₀.gpr .r27).toNat = 2 * (word s.mem B dT).toNat % 2 ^ 64 + (s.gpr .r3).toNat := by
      have b3 : u₅.gpr .r3 = s.gpr .r3 := by
        rw [w₅.gpr _ (by decide), w₄.gpr _ (by decide), w₃.gpr _ (by decide), w₂.gpr _ (by decide),
          w₁.gpr _ (by decide), w₀.gpr _ (by decide)]
      rw [w₁₀.gpr _ (by decide), w₉.gpr _ (by decide), w₈.gpr _ (by decide), w₇.gpr _ (by decide), e₆]
      simp only
      rw [e₅, shl1_or (u₄.gpr .r22) (u₅.gpr .r3) (by rw [b3]; exact h3), b3, w₄.gpr _ (by decide),
        w₃.gpr _ (by decide), w₂.gpr _ (by decide), w₁.gpr _ (by decide), e₀]
    have y1 : (u₁₁.gpr .r29).toNat = 2 * (word s.mem B (dT + 8)).toNat % 2 ^ 64 + (word s.mem B dT).toNat / 2 ^ 63 := by
      rw [w₁₁.gpr _ (by decide), w₁₀.gpr _ (by decide), e₉]
      simp only
      rw [e₈, shl1_or (u₇.gpr .r23) (u₈.gpr .r28)
        (by rw [w₈.gpr _ (by decide), e₇, shr63]; have := (u₆.gpr .r22).isLt; omega_using []), x1,
        w₈.gpr _ (by decide), e₇, shr63, x0]
    have lo : (u₁₀.gpr .r25).toNat = (word s.mem B dA).toNat * (word s.mem B dA).toNat % 2 ^ 64 := by
      rw [w₁₀.gpr _ (by decide), w₉.gpr _ (by decide), w₈.gpr _ (by decide), w₇.gpr _ (by decide),
        w₆.gpr _ (by decide), w₅.gpr _ (by decide), w₄.gpr _ (by decide), e₃, BitVec.toNat_mul, aa]
    have hi : (u₁₁.gpr .r26).toNat = (word s.mem B dA).toNat * (word s.mem B dA).toNat / 2 ^ 64 := by
      rw [w₁₁.gpr _ (by decide), w₁₀.gpr _ (by decide), w₉.gpr _ (by decide), w₈.gpr _ (by decide),
        w₇.gpr _ (by decide), w₆.gpr _ (by decide), w₅.gpr _ (by decide), e₄, w₃.gpr _ (by decide), aa]
    have ca : u₁₀.ca = s.ca := by rw [c₁₀, c₉, c₈, c₇, c₆, c₅, c₄, c₃, c₂, c₁, c₀]
    have z0 : u₁₂.gpr .r27 = u₁₁.gpr .r27 := w₁₂.gpr _ (by decide)
    rw [ca, y0, lo] at e₁₁
    rw [y1, hi] at e₁₂
    rw [z0] at mt
    have wv2 : wordsVal t.mem B dT 2 = (u₁₁.gpr .r27).toNat + 2 ^ 64 * (u₁₂.gpr .r29).toNat := by
      rw [mt]
      simp only [wordsVal, Nat.mul_zero, Nat.add_zero]
      rw [word_writeW_self, (writeW_outside _ B _ (by omega_using [hT, hnw])).word (d := dT) (by omega_using []) (by omega_using [hT, hnw]), word_writeW_self]
    have hw2 : wordsVal s.mem B dT 2 = (word s.mem B dT).toNat + 2 ^ 64 * (word s.mem B (dT + 8)).toNat := by
      simp [wordsVal]
    rw [wv2, hw2, g3, r3v, d₅, d₄, d₃, cv₂, cv₁]
    have := dbl_arith (x0 := (word s.mem B dT).toNat) (x1 := (word s.mem B (dT + 8)).toNat)
      (a := (word s.mem B dA).toNat * (word s.mem B dA).toNat) (b := (s.gpr .r3).toNat) (c := s.ca.toNat) rfl rfl
      e₁₁ e₁₂ (by have := Nat.mod_add_div ((word s.mem B dA).toNat * (word s.mem B dA).toNat) (2 ^ 64); omega_using [])
    omega_using [e₁₁, e₁₂]
  · rw [g3, r3v]; have := (word s.mem B (dT + 8)).isLt; omega_using []
  · rw [mt]
    exact ((writeW_outside _ B _ (by omega_using [hT, hnw])).mono (by omega_using []) (by omega_using [])).trans
      ((writeW_outside _ B _ (by omega_using [hT, hnw])).mono (by omega_using []) (by omega_using []))
  · rw [x₅.gpr _ (by decide), x₄.gpr _ (by decide), f₃, k₂.gpr _ (by simp), k₁.gpr _ (by simp), p12, off_add]
  · rw [x₅.gpr _ (by decide), f₄, x₃.gpr _ (by decide), k₂.gpr _ (by simp), k₁.gpr _ (by simp), K.gpr _ (by decide),
      h7, off_add]
  · rw [f₅, x₄.gpr _ (by decide), x₃.gpr _ (by decide), k₂.gpr _ (by simp), k₁.gpr _ (by simp), K.gpr _ (by decide)]
  · exact (((((K.trans k₁).trans k₂).trans x₃.keep).trans x₄.keep).trans x₅.keep).mono (by decide)

theorem mul_lt_self_zero {Q x : Nat} (h : Q * x < Q) : x = 0 := by
  rcases Nat.eq_zero_or_pos x with h0 | h0
  · exact h0
  · have := Nat.le_mul_of_pos_right Q h0; omega_using [h, this]

theorem pow128 (i : Nat) : 2 ^ (64 * (2 * (i + 1))) = 2 ^ (64 * (2 * i)) * 2 ^ 128 := by
  rw [← Nat.pow_add, show 64 * (2 * i) + 128 = 64 * (2 * (i + 1)) by omega_using []]

theorem dblInv_arith {Wt Wm Q r c Sq Tt Tm a r' c' : Nat} (ih : Wt + Q * (r + c) = 2 * Wm + Sq)
    (e : Tt + 2 ^ 128 * (r' + c') = 2 * Tm + a + r + c) :
    Wt + Q * Tt + Q * 2 ^ 128 * (r' + c') = 2 * (Wm + Q * Tm) + (Sq + Q * a) := by
  have := congrArg (Q * ·) e
  simp only [Nat.mul_add] at this ih ⊢
  grind

/-- The doubling (`sqrDbl`), of the `2 w` words of `S` at `dS` (memory `m₀`, its
`2 w + 1` words the triangle `T`), with `a` at `da`: `S := 2 T + Σ aᵢ² 2^(128 i)`,
which is `a²`. -/
theorem sqrDbl_ok {s : State} {B : Addr} {Z da dS w : Nat} (hs : Scr s B Z) (h0 : s.gpr .r0 = 0)
    (h6 : s.gpr .r6 = off B da) (h10 : s.gpr .r10 = off B dS) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (ha : da + 8 * w ≤ Z) (hS : dS + 8 * (2 * w + 1) ≤ Z)
    (hsep : da + 8 * w ≤ dS ∨ dS + 8 * (2 * w + 1) ≤ da)
    (hT : 2 * wordsVal s.mem B dS (2 * w + 1) + sqs s.mem B da w = wordsVal s.mem B da w * wordsVal s.mem B da w) :
    WP isa sqrDbl s fun t =>
      (wordsVal t.mem B dS (2 * w + 1) = wordsVal s.mem B da w * wordsVal s.mem B da w ∧
        Outside B dS (8 * (2 * w)) s.mem t.mem) ∧ Keep (.r12 :: .r7 :: .r9 :: .r3 :: .r30 :: (List.range 8).map sacc) s t := by
  have hnw := hs.nowrap
  unfold sqrDbl countLoop
  refine WP.seq ?_
  refine wp_addi (by decide) (by decide) fun u₁ w₁ f₁ _ => ?_
  refine wp_addi (by decide) (by decide) fun u₂ w₂ f₂ _ => ?_
  refine wp_write (exec_lsr_d (by decide)) fun u₃ w₃ f₃ _ => ?_
  refine wp_write (exec_li (by decide)) fun u₄ w₄ f₄ _ => ?_
  refine wp_addc fun u₅ w₅ f₅ => WP.block_nil ?_
  have k₅ : Keep [.r12, .r7, .r9, .r3, .r30] s u₅ :=
    ((((w₁.keep.trans w₂.keep).trans w₃.keep).trans w₄.keep).trans w₅.keep).mono (by decide)
  have m₅ : u₅.mem = s.mem := by rw [w₅.mem, w₄.mem, w₃.mem, w₂.mem, w₁.mem]
  have z4 : u₄.gpr .r0 = 0 := by
    rw [w₄.gpr _ (by decide), w₃.gpr _ (by decide), w₂.gpr _ (by decide), w₁.gpr _ (by decide), h0]
  rw [z4] at f₅
  have ca₅ : u₅.ca = false := by
    have := (u₅.gpr .r30).isLt
    cases h : u₅.ca
    · rfl
    · rw [h] at f₅; simp at f₅
  have r9₅ : u₅.gpr .r9 = BitVec.ofNat 64 w := by
    rw [w₅.gpr _ (by decide), w₄.gpr _ (by decide), f₃, w₂.gpr _ (by decide), w₁.gpr _ (by decide), h11]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega_using [hw']
  have r3₅ : u₅.gpr .r3 = 0 := by rw [w₅.gpr _ (by decide), f₄]; rfl
  have L : Keep (.r12 :: .r7 :: .r9 :: .r3 :: .r30 :: (List.range 8).map sacc) s u₅ := k₅.mono (by decide)
  refine WP.mono (wp_countdown (cnt := .r9) (N := w) (by omega_using [hw']) hw (fun i t =>
    (Scr t B Z ∧ t.gpr .r12 = off B (dS + 16 * i) ∧ t.gpr .r7 = off B (da + 8 * i) ∧ (t.gpr .r3).toNat ≤ 1 ∧
      wordsVal t.mem B dS (2 * i) + 2 ^ (64 * (2 * i)) * ((t.gpr .r3).toNat + t.ca.toNat) =
        2 * wordsVal s.mem B dS (2 * i) + sqs s.mem B da i ∧ Outside B dS (16 * i) s.mem t.mem) ∧
    Keep (.r12 :: .r7 :: .r9 :: .r3 :: .r30 :: (List.range 8).map sacc) s t)
    (fun i hi t ⟨⟨ht, t12, t7, t3, te, to⟩, tk⟩ _ => WP.mono (dblStep_ok ht t12 t7 t3 (by omega_using [hS, hi]) (by omega_using [ha, hi]))
      fun t' ⟨⟨e, r3', o, r12', r7', r9'⟩, k'⟩ => ⟨⟨⟨ht.congr k'.wr,
        by rw [r12', show dS + 16 * i + 16 = dS + 16 * (i + 1) by omega_using []],
        by rw [r7', show da + 8 * i + 8 = da + 8 * (i + 1) by omega_using []], r3', ?_,
        (to.mono (Nat.le_refl _) (by omega_using [])).trans (o.mono (by omega_using []) (by omega_using []))⟩,
        (tk.trans k').mono (by decide)⟩, r9'⟩)
    ⟨⟨hs.congr k₅.wr, by rw [w₅.gpr .r12 (by decide), w₄.gpr .r12 (by decide), w₃.gpr .r12 (by decide),
      w₂.gpr .r12 (by decide), f₁, h10]; simp,
      by rw [w₅.gpr .r7 (by decide), w₄.gpr .r7 (by decide), w₃.gpr .r7 (by decide), f₂, w₁.gpr .r6 (by decide), h6]; simp,
      by rw [r3₅]; decide, by simp [wordsVal, sqs, r3₅, ca₅], by rw [m₅]; exact Outside.refl _ _ _ _⟩, L⟩ r9₅)
    fun t ⟨⟨_, _, _, _, te, to⟩, tk⟩ => ⟨⟨?_, to.mono (Nat.le_refl _) (by omega_using [])⟩, tk⟩
  · have hw1 : wordsVal t'.mem B dS (2 * (i + 1)) = wordsVal t.mem B dS (2 * i) +
        2 ^ (64 * (2 * i)) * wordsVal t'.mem B (dS + 16 * i) 2 := by
      rw [show 2 * (i + 1) = 2 * i + 2 by omega_using [], fios_wordsVal_append, show dS + 8 * (2 * i) = dS + 16 * i by omega_using [],
        o.wordsVal (Or.inl (by omega_using [])) (by omega_using [hS, hnw, hi])]
    have hw2 : wordsVal s.mem B dS (2 * (i + 1)) = wordsVal s.mem B dS (2 * i) +
        2 ^ (64 * (2 * i)) * wordsVal s.mem B (dS + 16 * i) 2 := by
      rw [show 2 * (i + 1) = 2 * i + 2 by omega_using [], fios_wordsVal_append, show dS + 8 * (2 * i) = dS + 16 * i by omega_using []]
    have hm : wordsVal t.mem B (dS + 16 * i) 2 = wordsVal s.mem B (dS + 16 * i) 2 :=
      to.wordsVal (Or.inr (by omega_using [])) (by omega_using [hS, hnw, hi])
    have ha' : word t.mem B (da + 8 * i) = word s.mem B (da + 8 * i) := to.word (by omega_using [hsep, hi]) (by omega_using [ha, hnw, hi])
    have hq : sqs s.mem B da (i + 1) = sqs s.mem B da i +
        2 ^ (64 * (2 * i)) * ((word s.mem B (da + 8 * i)).toNat * (word s.mem B (da + 8 * i)).toNat) := by
      rw [sqs, show 64 * (2 * i) = 64 * i + 64 * i by omega_using [], Nat.pow_add]
    rw [hm, ha'] at e
    rw [hw1, hw2, hq, pow128]
    exact dblInv_arith te e
  · have hA := wordsVal_lt s.mem B da w
    have hQ : 2 ^ (64 * (2 * w)) = 2 ^ (64 * w) * 2 ^ (64 * w) := by
      rw [← Nat.pow_add, show 64 * w + 64 * w = 64 * (2 * w) by omega_using []]
    have AA : wordsVal s.mem B da w * wordsVal s.mem B da w < 2 ^ (64 * (2 * w)) := by
      rw [hQ]; exact Nat.mul_lt_mul'' hA hA
    have hs2 := wordsVal_succ_top s.mem B dS (2 * w)
    have ht2 := wordsVal_succ_top t.mem B dS (2 * w)
    rw [to.word (Or.inr (by omega_using [])) (by omega_using [hS, hnw])] at ht2
    have z : (word s.mem B (dS + 8 * (2 * w))).toNat = 0 :=
      mul_lt_self_zero (Q := 2 ^ (64 * (2 * w))) (by omega_using [hT, AA, hs2])
    have z' : (t.gpr .r3).toNat + t.ca.toNat = 0 := mul_lt_self_zero (Q := 2 ^ (64 * (2 * w))) (by omega_using [hT, te, AA, hs2])
    rw [z, Nat.mul_zero, Nat.add_zero] at hs2
    rw [z', Nat.mul_zero, Nat.add_zero] at te
    rw [ht2, z, Nat.mul_zero, Nat.add_zero]
    omega_using [hT, te, hs2]

/-! ## The reduction -/

/-- The value of `S` (`N` words at `dS`, memory `m`) while a window of value
`V` sits at its word `p`, after a chunk's rows: the words below it, the window,
and the words from `p` on, which the next boundary adds to the window. -/
def totR (m : Mem) (B : Addr) (dS N p V : Nat) : Nat :=
  wordsVal m B dS p + 2 ^ (64 * p) * (V + wordsVal m B (dS + 8 * p) (N - p))

theorem totR_arith {L Q R V A X V2 W2 C : Nat} (er : R * V2 + W2 = V + A + C) :
    L + Q * W2 + Q * R * (V2 + X) = L + Q * (V + (A + R * X)) + Q * C := by
  have := congrArg (Q * ·) er
  simp only [Nat.mul_add] at this ⊢
  grind

/-- A chunk (a boundary, then rows, `2⁵¹² V₂ + [out] = V + [S's words] + C`)
adds `2^(64 p) C` to `totR`. -/
theorem totR_step {m₀ m₂ : Mem} {B : Addr} {Z dS N p V V2 C : Nat} (hnw : B.toNat + Z ≤ 2 ^ 64)
    (hS : dS + 8 * N ≤ Z) (hp : p + 8 ≤ N) (o : Outside B (dS + 8 * p) 64 m₀ m₂)
    (er : 2 ^ (64 * 8) * V2 + wordsVal m₂ B (dS + 8 * p) 8 = V + wordsVal m₀ B (dS + 8 * p) 8 + C) :
    totR m₂ B dS N (p + 8) V2 = totR m₀ B dS N p V + 2 ^ (64 * p) * C := by
  have hw : ∀ d k, (d + 8 * k ≤ dS + 8 * p ∨ dS + 8 * p + 64 ≤ d) → d + 8 * k ≤ Z →
      wordsVal m₂ B d k = wordsVal m₀ B d k := fun d k h1 h2 => o.wordsVal h1 (by omega_using [hnw, h2])
  have A1 : wordsVal m₂ B dS (p + 8) = wordsVal m₀ B dS p + 2 ^ (64 * p) * wordsVal m₂ B (dS + 8 * p) 8 := by
    rw [fios_wordsVal_append, hw dS p (Or.inl (by omega_using [])) (by omega_using [hS, hp])]
  have A2 : wordsVal m₂ B (dS + 8 * (p + 8)) (N - (p + 8)) = wordsVal m₀ B (dS + 8 * p + 64) (N - p - 8) := by
    rw [show dS + 8 * (p + 8) = dS + 8 * p + 64 by omega_using [], show N - (p + 8) = N - p - 8 by omega_using []]
    exact hw _ _ (Or.inr (by omega_using [])) (by omega_using [hS, hp])
  have A4 : wordsVal m₀ B (dS + 8 * p) (N - p) = wordsVal m₀ B (dS + 8 * p) 8 +
      2 ^ (64 * 8) * wordsVal m₀ B (dS + 8 * p + 64) (N - p - 8) := by
    have := fios_wordsVal_append m₀ B (dS + 8 * p) 8 (N - p - 8)
    rwa [show 8 + (N - p - 8) = N - p by omega_using [hp], show dS + 8 * p + 8 * 8 = dS + 8 * p + 64 by omega_using []] at this
  have P : 2 ^ (64 * (p + 8)) = 2 ^ (64 * p) * 2 ^ (64 * 8) := by rw [← Nat.pow_add, Nat.mul_add]
  unfold totR
  rw [A1, A2, A4, P]
  exact totR_arith er

/-- With no window, `totR` is `S`'s value. -/
theorem totR_zero (m : Mem) (B : Addr) {dS N p : Nat} (hp : p ≤ N) : totR m B dS N p 0 = wordsVal m B dS N := by
  unfold totR
  have := fios_wordsVal_append m B dS p (N - p)
  rw [Nat.add_sub_cancel' hp] at this
  rw [this, Nat.zero_add]

/-- A block's first chunk of the reduction (`redRow0`): `uᵢ` stored at `dU`,
`2⁵¹² V' = V + (M₀ + 1) U - U`, for `M₀` the eight words of `m` in `smr` and `U`
the eight `uᵢ`. -/
theorem redRows0_ok {s : State} {B : Addr} {Z dU : Nat} (hs : Scr s B Z) (h0 : s.gpr .r0 = 0)
    (h10 : s.gpr .r10 = off B dU) (hU : dU + 64 ≤ Z) (h4 : (s.gpr .r4).toNat ≤ 2)
    (hm : ((s.gpr (smr 0)).toNat * (s.gpr .r31).toNat + 1) % 2 ^ 64 = 0) :
    WP isa (.block ((List.range 8).flatMap redRow0)) s fun t =>
      (2 ^ (64 * 8) * Vw t .r0 + wordsVal t.mem B dU 8 = Vw s .r4 + (rv s smr 8 + 1) * wordsVal t.mem B dU 8 ∧
        Outside B dU 64 s.mem t.mem ∧ (∀ c < 8, t.gpr (smr c) = s.gpr (smr c)) ∧ t.gpr .r0 = 0 ∧
        t.gpr .r31 = s.gpr .r31 ∧ t.gpr .r10 = s.gpr .r10) ∧ Keep rowRegs s t := by
  have hnw := hs.nowrap
  refine WP.mono (rowsN_ok (C := fun _ w => (rv s smr 8 + 1) * w.toNat)
    (I := fun u => Scr u B Z ∧ u.gpr .r0 = 0 ∧ u.gpr .r10 = off B dU ∧ (∀ c < 8, u.gpr (smr c) = s.gpr (smr c)) ∧
      u.gpr .r31 = s.gpr .r31)
    (L := rowRegs) (B := B) (dT := dU) (by omega_using [hU, hnw]) (fun r hr u ⟨hu, u0, u10, ub, u31⟩ hst => ?_)
    (fun r hr u t w ⟨hu, u0, u10, ub, u31⟩ k m => ⟨hu.congr k.wr, by rw [k.gpr _ (by decide), u0],
      by rw [k.gpr _ (by decide), u10], fun c hc => by rw [k.gpr _ (by revert c; decide), ub c hc],
      by rw [k.gpr _ (by decide), u31]⟩)
    (fun u h => h.2.1) 8 (Nat.le_refl _) s ⟨hs, h0, h10, fun _ _ => rfl, rfl⟩ h4)
    fun t ⟨⟨e, o, ⟨_, t0, t10, tb, t31⟩⟩, k⟩ => ⟨⟨?_, o, tb, t0, t31, by rw [t10, h10]⟩, k⟩
  · have hm' : ((u.gpr (smr 0)).toNat * (u.gpr .r31).toNat + 1) % 2 ^ 64 = 0 := by rw [ub 0 (by decide), u31]; exact hm
    refine WP.mono (redRow0_ok hu u0 hr u10 (by omega_using [hU, hr]) hst hm') fun t ⟨⟨mt, _, et⟩, kt⟩ =>
      ⟨⟨t.gpr .r3, mt, ?_⟩, kt⟩
    have : rv u smr 8 = rv s smr 8 := rv_congr 8 ub
    rw [et, this, Nat.add_mul, Nat.one_mul, Nat.add_assoc]
  · rw [← psum_mulw, ← e]; rfl

theorem shl4 (w : Nat) : BitVec.ofNat 64 (2 * w) <<< 4 = BitVec.ofNat 64 (32 * w) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_using []

/-- The loads at the start of a block of the reduction: `S`'s words at `dU`
into the window, `m`'s first eight words into `smr`, `r4` and CA clear, and
`m'` (at `m`'s base `+ 32 w + 40`) into `r31`. -/
theorem redLoad_ok {s : State} {B : Addr} {Z dU dM w : Nat} (hs : Scr s B Z) (h0 : s.gpr .r0 = 0)
    (h10 : s.gpr .r10 = off B dU) (h7 : s.gpr .r7 = off B dM) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (hU : dU + 64 ≤ Z) (hM : dM + 64 ≤ Z) (hM' : dM + 32 * w + 48 ≤ Z) :
    WP isa (.block (load8 sacc .r10 ++ load8 smr .r7 ++ ([.li .r4 0, .addc .r30 .r0 .r0, .lsl .r31 .r11 4,
      .add .r31 .r31 .r7, .load .d .r31 .r31 40] : List Instr))) s fun t =>
      (Vw t .r4 = wordsVal s.mem B dU 8 ∧ t.gpr .r4 = 0 ∧ (∀ c < 8, t.gpr (smr c) = word s.mem B (dM + 8 * c)) ∧
        t.gpr .r31 = word s.mem B (dM + 32 * w + 40) ∧ t.mem = s.mem ∧ t.gpr .r0 = 0) ∧
      Keep (.r30 :: .r4 :: .r31 :: ((List.range 8).map smr ++ (List.range 8).map sacc)) s t := by
  have hnw := hs.nowrap
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (load8_ok hs h10 hU (by decide) (by decide)) fun u₁ ⟨⟨e₁, m₁, _, _⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (load8_ok (hs.congr k₁.wr) (by rw [k₁.gpr _ (by decide), h7]) hM (by decide) (by decide))
    fun u₂ ⟨⟨_, m₂, _, g₂⟩, k₂⟩ => ?_
  have K₂ : Keep ((List.range 8).map sacc ++ (List.range 8).map smr) s u₂ := k₁.trans k₂
  refine wp_write (exec_li (by decide)) fun u₃ w₃ f₃ _ => ?_
  refine wp_addc fun u₄ w₄ f₄ => ?_
  refine wp_write (exec_lsl (by decide)) fun u₅ w₅ f₅ c₅ => ?_
  refine wp_write exec_add fun u₆ w₆ f₆ c₆ => ?_
  have r7₅ : u₅.gpr .r7 = off B dM := by
    rw [w₅.gpr .r7 (by decide), w₄.gpr .r7 (by decide), w₃.gpr .r7 (by decide), K₂.gpr .r7 (by decide), h7]
  have r11₄ : u₄.gpr .r11 = BitVec.ofNat 64 (2 * w) := by
    rw [w₄.gpr .r11 (by decide), w₃.gpr .r11 (by decide), K₂.gpr .r11 (by decide), h11]
  have p31 : u₆.gpr .r31 = off B (dM + 32 * w) := by
    rw [f₆, f₅, r11₄, r7₅, shl4 w, BitVec.add_comm, off_add]
  have m₆ : u₆.mem = s.mem := by rw [w₆.mem, w₅.mem, w₄.mem, w₃.mem, m₂, m₁]
  have hs₆ : Scr u₆ B Z := hs.congr ((K₂.trans ((w₃.keep.trans w₄.keep).trans (w₅.keep.trans w₆.keep))).wr)
  refine wp_ld (by decide) ⟨by decide, by decide⟩ (by rw [p31, off_add]) (hs₆.ld (by omega_using [hM'])) fun t w₇ f₇ c₇ =>
    WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · have z3 : u₃.gpr .r0 = 0 := by rw [w₃.gpr _ (by decide), K₂.gpr _ (by decide), h0]
    rw [z3] at f₄
    have := (u₄.gpr .r30).isLt
    have ca : u₄.ca = false := by
      cases h : u₄.ca
      · rfl
      · rw [h] at f₄; simp at f₄
    have ra : rv t sacc 8 = rv u₁ sacc 8 := rv_congr 8 fun j hj => by
      rw [w₇.gpr _ (by revert j; decide), w₆.gpr _ (by revert j; decide), w₅.gpr _ (by revert j; decide),
        w₄.gpr _ (by revert j; decide), w₃.gpr _ (by revert j; decide), k₂.gpr _ (by revert j; decide)]
    unfold Vw
    rw [ra, e₁, w₇.gpr .r4 (by decide), w₆.gpr .r4 (by decide), w₅.gpr .r4 (by decide), w₄.gpr .r4 (by decide), f₃,
      c₇, c₆, c₅, ca]
    simp
  · rw [w₇.gpr .r4 (by decide), w₆.gpr .r4 (by decide), w₅.gpr .r4 (by decide), w₄.gpr .r4 (by decide), f₃]; rfl
  · intro c hc
    have hs1 : ∀ c < 8, smr c ≠ .r31 ∧ smr c ≠ .r30 ∧ smr c ≠ .r4 := by decide
    obtain ⟨a1, a2, a3⟩ := hs1 c hc
    rw [w₇.gpr _ a1, w₆.gpr _ a1, w₅.gpr _ a1, w₄.gpr _ a2, w₃.gpr _ a3, g₂ c hc, m₁]
  · rw [f₇, m₆]
  · rw [w₇.mem, m₆]
  · rw [w₇.gpr _ (by decide), w₆.gpr _ (by decide), w₅.gpr _ (by decide), w₄.gpr _ (by decide),
      w₃.gpr _ (by decide), K₂.gpr _ (by decide), h0]
  · exact ((K₂.trans ((w₃.keep.trans w₄.keep).trans (w₅.keep.trans w₆.keep))).trans w₇.keep).mono (by decide)

/-- The later chunks' count of a block of the reduction (`K - 1`), and the
pointers at the second chunk. -/
theorem redCnt_ok {s : State} {B : Addr} {dM dU h K : Nat} (h7 : s.gpr .r7 = off B dM) (h10 : s.gpr .r10 = off B dU)
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * (8 * K))) (h9 : s.gpr .r9 = cnt h 0) (hK : 1 ≤ K) (hK' : K < 2 ^ 28)
    (hh : h < 2 ^ 32) :
    WP isa (.block [.addi .r7 .r7 64, .addi .r12 .r10 64, .lsr .d .r30 .r11 4, .subi .r30 .r30 1,
      .logic .or .r9 .r9 .r30]) s fun t =>
      (t.gpr .r7 = off B (dM + 64) ∧ t.gpr .r12 = off B (dU + 64) ∧ t.gpr .r9 = cnt h (K - 1) ∧ t.mem = s.mem ∧
        t.ca = s.ca) ∧ Keep [.r7, .r12, .r30, .r9] s t := by
  refine wp_addi (by decide) (by decide) fun u₁ w₁ f₁ c₁ => ?_
  refine wp_addi (by decide) (by decide) fun u₂ w₂ f₂ c₂ => ?_
  refine wp_write (exec_lsr_d (by decide)) fun u₃ w₃ f₃ c₃ => ?_
  refine wp_write (exec_subi (by decide) (by decide)) fun u₄ w₄ f₄ c₄ => ?_
  refine wp_write exec_logic fun t w₅ f₅ c₅ => WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [w₅.gpr _ (by decide), w₄.gpr _ (by decide), w₃.gpr _ (by decide), w₂.gpr _ (by decide), f₁, h7, off_add]
  · rw [w₅.gpr _ (by decide), w₄.gpr _ (by decide), w₃.gpr _ (by decide), f₂, w₁.gpr _ (by decide), h10, off_add]
  · have r30 : u₄.gpr .r30 = BitVec.ofNat 64 (K - 1) := by
      rw [f₄, f₃, w₂.gpr _ (by decide), w₁.gpr _ (by decide), h11]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.shiftRight_eq_div_pow]
      omega_using [hK, hK']
    rw [f₅]
    simp only
    rw [r30, w₄.gpr _ (by decide), w₃.gpr _ (by decide), w₂.gpr _ (by decide), w₁.gpr _ (by decide), h9,
      cnt_or hh (by omega_using [hK'])]
  · rw [w₅.mem, w₄.mem, w₃.mem, w₂.mem, w₁.mem]
  · rw [c₅, c₄, c₃, c₂, c₁]
  · exact ((((w₁.keep.trans w₂.keep).trans w₃.keep).trans w₄.keep).trans w₅.keep).mono (by decide)

/-- The registers the start of a block of the reduction writes. -/
abbrev redHeadRegs : List Reg :=
  .r7 :: .r12 :: .r30 :: .r9 :: .r3 :: .r4 :: .r31 :: ((List.range 8).map smr ++ (List.range 8).map sacc)

/-- The start of a block of the reduction, its window at `S`'s word `p` (`r10`),
`m` at `dM` (`w = 8 K` words, `m'` at `dM + 32 w + 40`): the block's first
chunk, `uᵢ` stored at `S`'s words `p` to `p + 7`. -/
theorem redHead_ok {s : State} {B : Addr} {Z dS N p dM h K : Nat} (hs : Scr s B Z) (h0 : s.gpr .r0 = 0)
    (h10 : s.gpr .r10 = off B (dS + 8 * p)) (h7 : s.gpr .r7 = off B dM)
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * (8 * K))) (h9 : s.gpr .r9 = cnt h 0) (hK : 1 ≤ K) (hK' : K < 2 ^ 28)
    (hh : h < 2 ^ 32) (hS : dS + 8 * N ≤ Z) (hp : p + 8 ≤ N) (hM : dM + 64 ≤ Z) (hM' : dM + 32 * (8 * K) + 48 ≤ Z)
    (hm : ((word s.mem B dM).toNat * (word s.mem B (dM + 32 * (8 * K) + 40)).toNat + 1) % 2 ^ 64 = 0) :
    WP isa (.block (load8 sacc .r10 ++ load8 smr .r7 ++ ([.li .r4 0, .addc .r30 .r0 .r0, .lsl .r31 .r11 4,
      .add .r31 .r31 .r7, .load .d .r31 .r31 40] : List Instr) ++ (List.range 8).flatMap redRow0 ++
      ([.addi .r7 .r7 64, .addi .r12 .r10 64, .lsr .d .r30 .r11 4, .subi .r30 .r30 1, .logic .or .r9 .r9 .r30] :
        List Instr))) s fun t =>
      (totR t.mem B dS N (p + 8) (Vw t .r0) = wordsVal s.mem B dS N +
          2 ^ (64 * p) * ((wordsVal s.mem B dM 8 + 1) * wordsVal t.mem B (dS + 8 * p) 8) ∧
        Outside B (dS + 8 * p) 64 s.mem t.mem ∧ t.gpr .r7 = off B (dM + 64) ∧
        t.gpr .r12 = off B (dS + 8 * p + 64) ∧ t.gpr .r9 = cnt h (K - 1) ∧ t.gpr .r0 = 0 ∧
        t.gpr .r31 = word s.mem B (dM + 32 * (8 * K) + 40)) ∧ Keep redHeadRegs s t := by
  have hnw := hs.nowrap
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (redLoad_ok hs h0 h10 h7 h11 (by omega_using [hS, hp]) hM hM') fun u ⟨⟨vu, r4u, mu, r31u, mmu, z0u⟩, ku⟩ => ?_
  have hu : Scr u B Z := hs.congr ku.wr
  refine WP.mono (redRows0_ok (dU := dS + 8 * p) hu z0u (by rw [ku.gpr _ (by decide), h10]) (by omega_using [hS, hp]) (by rw [r4u]; decide)
    (by rw [mu 0 (by decide), r31u, Nat.add_zero, Nat.mul_zero]; exact hm))
    fun t₁ ⟨⟨e₁, o₁, b₁, z₁, r31₁, r10₁⟩, k₁⟩ => ?_
  have K₁ : Keep (.r30 :: .r4 :: .r31 :: .r3 :: ((List.range 8).map smr ++ (List.range 8).map sacc)) s t₁ :=
    (ku.trans k₁).mono (by decide)
  refine WP.mono (redCnt_ok (by rw [K₁.gpr _ (by decide), h7]) (by rw [K₁.gpr _ (by decide), h10])
    (by rw [K₁.gpr _ (by decide), h11]) (by rw [K₁.gpr _ (by decide), h9]) hK hK' hh)
    fun t ⟨⟨r7, r12, r9, mt, ct⟩, kt⟩ => ⟨⟨?_, by rw [mt, ← mmu]; exact o₁, r7, r12, r9,
      by rw [kt.gpr _ (by decide), z₁], by rw [kt.gpr _ (by decide), r31₁, r31u]⟩, (K₁.trans kt).mono (by decide)⟩
  have rm : rv u smr 8 = wordsVal s.mem B dM 8 := by
    rw [wordsVal_psum]; exact psum_congr fun j hj => by rw [mu j hj]
  have vt : Vw t .r0 = Vw t₁ .r0 :=
    Vw_congr (fun j hj => kt.gpr _ (by revert j; decide)) (kt.gpr _ (by decide)) ct
  rw [vu, rm] at e₁
  rw [mt, vt, totR_step (C := (wordsVal s.mem B dM 8 + 1) * wordsVal t₁.mem B (dS + 8 * p) 8) hnw hS hp
    (mmu ▸ o₁) (by rw [Nat.zero_add]; exact e₁), totR_zero _ _ (by omega_using [hp])]

/-- The invariant of the rows of a later chunk of the reduction, the `uᵢ` at `dU`. -/
def RedI (g : State) (B : Addr) (Z dU dT Bk : Nat) (u : State) : Prop :=
  Scr u B Z ∧ u.gpr .r0 = 0 ∧ u.gpr .r10 = off B dU ∧ u.gpr .r12 = off B dT ∧ rv u smr 8 = Bk ∧
    ∀ r < 8, word u.mem B (dU + 8 * r) = word g.mem B (dU + 8 * r)

/-- A later chunk's eight rows (`redRow`): `2⁵¹² V' + [out] = V + Mc U` for the
chunk's words `Mc` of `m` (in `smr`) and the block's `uᵢ`, `U` (at `dU`). -/
theorem redRows_ok {s : State} {B : Addr} {Z dU dT : Nat} (hs : Scr s B Z) (h0 : s.gpr .r0 = 0)
    (h10 : s.gpr .r10 = off B dU) (h12 : s.gpr .r12 = off B dT) (hU : dU + 64 ≤ Z) (hT : dT + 64 ≤ Z)
    (hsep : dU + 64 ≤ dT ∨ dT + 64 ≤ dU) (h4 : (s.gpr .r4).toNat ≤ 2) :
    WP isa (.block ((List.range 8).flatMap redRow)) s fun t =>
      (2 ^ (64 * 8) * Vw t .r0 + wordsVal t.mem B dT 8 = Vw s .r4 + rv s smr 8 * wordsVal s.mem B dU 8 ∧
        Outside B dT 64 s.mem t.mem ∧ RedI s B Z dU dT (rv s smr 8) t) ∧ Keep rowRegs s t := by
  have hnw := hs.nowrap
  refine WP.mono (rowsN_ok (C := fun r _ => rv s smr 8 * (word s.mem B (dU + 8 * r)).toNat)
    (I := RedI s B Z dU dT (rv s smr 8)) (L := rowRegs) (B := B) (dT := dT) (by omega_using [hT, hnw])
    (fun r hr u ⟨hu, u0, u10, u12, ub, uw⟩ hst => ?_) (fun r hr u t w ⟨hu, u0, u10, u12, ub, uw⟩ k m => ?_)
    (fun u h => h.2.1) 8 (Nat.le_refl _) s ⟨hs, h0, h10, h12, rfl, fun _ _ => rfl⟩ h4)
    fun t ⟨⟨e, o, it⟩, k⟩ => ⟨⟨by rw [← psum_mulw, ← e]; rfl, o, it⟩, k⟩
  · refine WP.mono (redRow_ok hu u0 hr u10 u12 (by omega_using [hU, hr]) (by omega_using [hT, hr]) hst) fun t ⟨⟨w, mt, et⟩, kt⟩ =>
      ⟨⟨w, mt, ?_⟩, kt.mono fun _ hr => hr⟩
    rw [et, ub, uw r hr]
  · refine ⟨hu.congr k.wr, by rw [k.gpr _ (by decide), u0], by rw [k.gpr _ (by decide), u10],
      by rw [k.gpr _ (by decide), u12], by rw [← ub]; exact rv_congr 8 fun j hj => k.gpr _ (by revert j; decide),
      fun r' hr' => ?_⟩
    rw [m, (writeW_outside u.mem B w (by omega_using [hT, hnw, hr])).word (by omega_using [hsep, hr, hr']) (by omega_using [hU, hnw, hr']), uw r' hr']

/-- A later chunk of the reduction (the body of `redChunks`), the window at
`S`'s word `p` (`r12`), the chunk's words of `m` at `dC` (`r7`), the block's
`uᵢ` at `dU` (`r10`): `totR` takes in `2^(64 p) Mc U`. -/
theorem redChunk_ok {s : State} {B : Addr} {Z dS N p dC dU h l : Nat} (hs : Scr s B Z) (h0 : s.gpr .r0 = 0)
    (h12 : s.gpr .r12 = off B (dS + 8 * p)) (h7 : s.gpr .r7 = off B dC) (h10 : s.gpr .r10 = off B dU)
    (h9 : s.gpr .r9 = cnt h l) (hl : 1 ≤ l) (hS : dS + 8 * N ≤ Z) (hp : p + 8 ≤ N) (hC : dC + 64 ≤ Z)
    (hU : dU + 64 ≤ dS + 8 * p) :
    WP isa (.block (boundary8 .r12 ++ load8 smr .r7 ++ (List.range 8).flatMap redRow ++
      ([.addi .r12 .r12 64, .addi .r7 .r7 64, .subi .r9 .r9 1] : List Instr))) s fun t =>
      (totR t.mem B dS N (p + 8) (Vw t .r0) = totR s.mem B dS N p (Vw s .r0) +
          2 ^ (64 * p) * (wordsVal s.mem B dC 8 * wordsVal s.mem B dU 8) ∧
        Outside B (dS + 8 * p) 64 s.mem t.mem ∧ t.gpr .r12 = off B (dS + 8 * p + 64) ∧
        t.gpr .r7 = off B (dC + 64) ∧ t.gpr .r9 = cnt h (l - 1) ∧ t.gpr .r10 = s.gpr .r10 ∧ t.gpr .r0 = 0) ∧
      Keep (.r12 :: .r7 :: .r9 :: .r3 :: .r30 :: .r4 :: ((List.range 8).map smr ++ (List.range 8).map sacc)) s t := by
  have hnw := hs.nowrap
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (boundary8_ok hs h0 h12 (by omega_using [hS, hp]) (by decide) (by decide) (by decide))
    fun t₁ ⟨⟨e₁, l₁, c₁, m₁⟩, k₁⟩ => ?_
  have hs₁ := hs.congr k₁.wr
  refine WP.mono (load8_ok hs₁ (by rw [k₁.gpr _ (by decide), h7]) hC (by decide) (by decide))
    fun t₂ ⟨⟨_, m₂, c₂, g₂⟩, k₂⟩ => ?_
  have K₂ : Keep (.r4 :: .r30 :: ((List.range 8).map sacc ++ (List.range 8).map smr)) s t₂ :=
    (k₁.trans k₂).mono (by decide)
  have hs₂ := hs.congr K₂.wr
  refine WP.mono (redRows_ok (dU := dU) (dT := dS + 8 * p) hs₂ (by rw [K₂.gpr _ (by decide), h0]) (by rw [K₂.gpr _ (by decide), h10])
    (by rw [k₂.gpr _ (by decide), k₁.gpr _ (by decide), h12]) (by omega_using [hS, hp, hU]) (by omega_using [hS, hp]) (by omega_using [hU])
    (by rw [k₂.gpr _ (by decide)]; exact l₁)) fun t₃ ⟨⟨e₃, o₃, ⟨_, z₃, r10₃, r12₃, _, _⟩⟩, k₃⟩ => ?_
  refine wp_addi (by decide) (by decide) fun u₁ w₁ f₁ c₁' => ?_
  refine wp_addi (by decide) (by decide) fun u₂ w₂ f₂ c₂' => ?_
  refine wp_write (exec_subi (by decide) (by decide)) fun t w₃ f₃ c₃ => WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · have v₂ : Vw t₂ .r4 = Vw t₁ .r4 := by
      unfold Vw
      rw [rv_congr 8 fun j hj => k₂.gpr _ (by revert j; decide), k₂.gpr .r4 (by decide), c₂]
    have vt : Vw t .r0 = Vw t₃ .r0 :=
      Vw_congr (fun j hj => by rw [w₃.gpr _ (by revert j; decide), w₂.gpr _ (by revert j; decide),
        w₁.gpr _ (by revert j; decide)]) (by rw [w₃.gpr _ (by decide), w₂.gpr _ (by decide), w₁.gpr _ (by decide)])
        (by rw [c₃, c₂', c₁'])
    have rb : rv t₂ smr 8 = wordsVal s.mem B dC 8 := by
      rw [wordsVal_psum]; exact psum_congr fun j hj => by rw [g₂ j hj, m₁]
    rw [v₂, e₁, rb, m₂, m₁] at e₃
    rw [w₃.mem, w₂.mem, w₁.mem, vt]
    exact totR_step hnw hS hp (by rw [m₂, m₁] at o₃; exact o₃) (by rw [e₃])
  · rw [w₃.mem, w₂.mem, w₁.mem]; rw [m₂, m₁] at o₃; exact o₃
  · rw [w₃.gpr _ (by decide), w₂.gpr _ (by decide), f₁, r12₃, off_add]
  · rw [w₃.gpr _ (by decide), f₂, w₁.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide),
      k₁.gpr _ (by decide), h7, off_add]
  · rw [f₃, w₂.gpr _ (by decide), w₁.gpr _ (by decide), k₃.gpr _ (by decide), K₂.gpr _ (by decide), h9, cnt_dec hl]
  · rw [w₃.gpr _ (by decide), w₂.gpr _ (by decide), w₁.gpr _ (by decide), r10₃, h10]
  · rw [w₃.gpr _ (by decide), w₂.gpr _ (by decide), w₁.gpr _ (by decide), z₃]
  · exact ((((K₂.trans k₃).trans w₁.keep).trans w₂.keep).trans w₃.keep).mono (by decide)

/-- The registers of the reduction's later chunks. -/
abbrev chunkRegsR : List Reg :=
  .r12 :: .r7 :: .r9 :: .r3 :: .r30 :: .r4 :: ((List.range 8).map smr ++ (List.range 8).map sacc)

/-- A block's later chunks (`redChunks`), `G` of them in `r9`'s low half: `totR`
takes in `2^(64 p) M' U` for the `8 G` words `M'` of `m` at `dC`. -/
theorem redChunks_ok {s : State} {B : Addr} {Z dS N p dC dU h G : Nat} (hs : Scr s B Z) (h0 : s.gpr .r0 = 0)
    (h12 : s.gpr .r12 = off B (dS + 8 * p)) (h7 : s.gpr .r7 = off B dC) (h10 : s.gpr .r10 = off B dU)
    (h9 : s.gpr .r9 = cnt h G) (hG : G < 2 ^ 32) (hS : dS + 8 * N ≤ Z) (hp : p + 8 * G ≤ N) (hC : dC + 64 * G ≤ Z)
    (hsep : dC + 64 * G ≤ dS ∨ dS + 8 * N ≤ dC) (hU : dU + 64 ≤ dS + 8 * p) :
    WP isa redChunks s fun t =>
      (totR t.mem B dS N (p + 8 * G) (Vw t .r0) = totR s.mem B dS N p (Vw s .r0) +
          2 ^ (64 * p) * (wordsVal s.mem B dC (8 * G) * wordsVal s.mem B dU 8) ∧
        Outside B (dS + 8 * p) (64 * G) s.mem t.mem ∧ t.gpr .r12 = off B (dS + 8 * p + 64 * G) ∧
        t.gpr .r7 = off B (dC + 64 * G) ∧ t.gpr .r9 = cnt h 0 ∧ t.gpr .r10 = s.gpr .r10 ∧ t.gpr .r0 = 0) ∧
      Keep chunkRegsR s t := by
  have hnw := hs.nowrap
  unfold redChunks
  refine WP.ite _ (eval_zero_w hG h9) (fun hz => ?_) (fun hz => ?_)
  · have : G = 0 := of_decide_eq_true hz
    subst this
    exact WP.block_nil ⟨⟨by simp [wordsVal], Outside.refl _ _ _ _, h12, h7, h9, rfl, h0⟩, Keep.refl _ _⟩
  have hG0 : G ≠ 0 := of_decide_eq_false hz
  refine WP.mono (wp_countdown_w (h := h) hG (by omega_using [hG0]) (fun i t =>
    (totR t.mem B dS N (p + 8 * i) (Vw t .r0) = totR s.mem B dS N p (Vw s .r0) +
        2 ^ (64 * p) * (wordsVal s.mem B dC (8 * i) * wordsVal s.mem B dU 8) ∧
      Outside B (dS + 8 * p) (64 * i) s.mem t.mem ∧ t.gpr .r12 = off B (dS + 8 * p + 64 * i) ∧
      t.gpr .r7 = off B (dC + 64 * i)) ∧ Keep chunkRegsR s t)
    (fun i hi t ⟨⟨e, o, t12, t7⟩, k⟩ t9 => ?_)
    ⟨⟨by simp [wordsVal], Outside.refl _ _ _ _, h12, h7⟩, Keep.refl _ _⟩ h9)
    fun t ⟨⟨⟨e, o, t12, t7⟩, k⟩, t9⟩ => ⟨⟨e, o, t12, t7, t9, k.gpr _ (by decide), by rw [k.gpr _ (by decide), h0]⟩, k⟩
  have ht : Scr t B Z := hs.congr k.wr
  have wc : wordsVal t.mem B (dC + 64 * i) 8 = wordsVal s.mem B (dC + 64 * i) 8 := o.wordsVal (by omega_using [hp, hsep, hi]) (by omega_using [hC, hnw, hi])
  have wu : wordsVal t.mem B dU 8 = wordsVal s.mem B dU 8 := o.wordsVal (by omega_using [hU]) (by omega_using [hS, hp, hU, hnw])
  refine WP.mono (redChunk_ok (p := p + 8 * i) (dU := dU) ht (by rw [k.gpr _ (by decide), h0])
    (by rw [t12, show dS + 8 * p + 64 * i = dS + 8 * (p + 8 * i) by omega_using []]) t7 (by rw [k.gpr _ (by decide), h10]) t9
    (by omega_using [hi]) hS (by omega_using [hp, hi]) (by omega_using [hC, hi]) (by omega_using [hU])) fun u ⟨⟨eu, ou, u12, u7, u9, _, _⟩, ku⟩ =>
      ⟨⟨⟨?_, ?_, ?_, ?_⟩, (k.trans ku).mono (by decide)⟩, u9⟩
  · rw [show p + 8 * (i + 1) = p + 8 * i + 8 by omega_using [], eu, e, wc, wu, show 8 * (i + 1) = 8 * i + 8 by omega_using [],
      fios_wordsVal_append, show dC + 8 * (8 * i) = dC + 64 * i by omega_using [],
      show 64 * (p + 8 * i) = 64 * p + 64 * (8 * i) by omega_using [], Nat.pow_add]
    grind
  · exact (o.mono (Nat.le_refl _) (by omega_using [])).trans (ou.mono (by omega_using []) (by omega_using []))
  · rw [u12, show dS + 8 * (p + 8 * i) + 64 = dS + 8 * p + 64 * (i + 1) by omega_using []]
  · rw [u7, show dC + 64 * i + 64 = dC + 64 * (i + 1) by omega_using []]

/-- The window's words `1` to `n` take in CA. -/
theorem addzeN_ok : ∀ (n : Nat) {s : State}, n ≤ 7 →
    WP isa (.block ((List.range n).map fun c => Instr.addze (sacc (c + 1)) (sacc (c + 1)))) s fun t =>
      (rv t (fun c => sacc (c + 1)) n + 2 ^ (64 * n) * t.ca.toNat = rv s (fun c => sacc (c + 1)) n + s.ca.toNat ∧
        t.mem = s.mem) ∧ Keep ((List.range n).map fun c => sacc (c + 1)) s t
  | 0, s, _ => WP.block_nil ⟨⟨by simp [rv, psum], rfl⟩, Keep.refl _ _⟩
  | n + 1, s, hn => by
    rw [Mont4.map_succ, WP.block_append_iff]
    refine WP.mono (addzeN_ok n (by omega_using [hn])) fun t ⟨⟨e, m⟩, k⟩ => ?_
    refine wp_addze fun u w eu => WP.block_nil ⟨⟨?_, by rw [w.mem, m]⟩, (k.trans w.keep).mono fun r hr => ?_⟩
    · have hd : ∀ j < 7, ∀ i < 7, j < i → sacc (j + 1) ≠ sacc (i + 1) := by decide
      have r1 : rv u (fun c => sacc (c + 1)) n = rv t (fun c => sacc (c + 1)) n :=
        rv_congr n fun j hj => w.gpr _ (hd j (by omega_using [hn, hj]) n (by omega_using [hn]) hj)
      have sn : t.gpr (sacc (n + 1)) = s.gpr (sacc (n + 1)) := k.gpr _ fun h => by
        obtain ⟨j, hj, e⟩ := List.mem_map.mp h
        exact hd j (by have := List.mem_range.mp hj; omega_using [hn, this]) n (by omega_using [hn]) (List.mem_range.mp hj) e
      show rv u (fun c => sacc (c + 1)) n + 2 ^ (64 * n) * (u.gpr (sacc (n + 1))).toNat + _ =
        rv s (fun c => sacc (c + 1)) n + 2 ^ (64 * n) * (s.gpr (sacc (n + 1))).toNat + _
      rw [r1, ← sn, pow64_succ]
      have := congrArg (2 ^ (64 * n) * ·) eu
      simp only [Nat.mul_add] at this
      grind
    · rw [List.range_succ, List.map_append]
      simp only [List.mem_append, List.mem_singleton, List.map_cons, List.map_nil] at hr ⊢
      exact hr

/-- The top (`r8`, at most 3) of the block below added to the window, CA clear,
the carry into `r4` (at most 2): `W' + 2⁵¹² r4' = W + 2⁵¹² r4 + r8`. -/
theorem addTop_ok {s : State} (h4 : (s.gpr .r4).toNat ≤ 2) {Y : List Instr} {Q : State → Prop}
    (k : ∀ t, (rv t sacc 8 + 2 ^ (64 * 8) * (t.gpr .r4).toNat = rv s sacc 8 + 2 ^ (64 * 8) * (s.gpr .r4).toNat +
        (s.gpr .r8).toNat ∧ (t.gpr .r4).toNat ≤ 3 ∧ t.mem = s.mem) ∧ Keep (.r4 :: (List.range 8).map sacc) s t →
      WP isa (.block Y) t Q) :
    WP isa (.block (.addc (sacc 0) (sacc 0) .r8 :: ((List.range 7).map (fun c => Instr.addze (sacc (c + 1)) (sacc (c + 1))) ++
      (.addze .r4 .r4 :: Y)))) s Q := by
  refine wp_addc fun u w eu => ?_
  rw [WP.block_append_iff]
  refine WP.mono (addzeN_ok 7 (Nat.le_refl _)) fun v ⟨⟨ev, mv⟩, kv⟩ => wp_addze fun t w' et => k t
    ⟨⟨?_, ?_, by rw [w'.mem, mv, w.mem]⟩, ((w.keep.trans kv).trans w'.keep).mono (by decide)⟩
  all_goals have r4v : v.gpr .r4 = s.gpr .r4 := by rw [kv.gpr _ (by decide), w.gpr _ (by decide)]
  all_goals rw [r4v] at et
  all_goals have := Bool.toNat_le v.ca
  · have ru : rv u (fun c => sacc (c + 1)) 7 = rv s (fun c => sacc (c + 1)) 7 :=
      rv_congr 7 fun j hj => w.gpr _ (by revert j; decide)
    have rt : rv t sacc 8 = rv v sacc 8 := rv_congr 8 fun j hj => w'.gpr _ (by revert j; decide)
    have s0 : v.gpr (sacc 0) = u.gpr (sacc 0) := kv.gpr _ (by decide)
    rw [ru] at ev
    rw [rt, rv8_shift v, rv8_shift s, s0, pow512]
    have hct : t.ca.toNat = 0 := by have := (t.gpr .r4).isLt; have := Bool.toNat_le t.ca; omega_arith
    have := congrArg (2 ^ 64 * ·) ev
    simp only [Nat.mul_add] at this
    rw [hct, Nat.mul_zero, Nat.add_zero] at et
    rw [et]
    grind
  · have := (t.gpr .r4).isLt; have := Bool.toNat_le t.ca; omega_arith

/-- The end of a block of the reduction, the window at `S`'s word `p` (`r12`):
`S`'s words there and the top of the block below (`r8`) added, the window
stored, its carry the new top; `m`'s pointer back at its base, `S`'s a block
on, one block less in `r9`'s high half, and that count in `r30`. -/
theorem redTail_ok {s : State} {B : Addr} {Z dS N p dM dU h w : Nat} (hs : Scr s B Z) (h0 : s.gpr .r0 = 0)
    (h12 : s.gpr .r12 = off B (dS + 8 * p)) (h7 : s.gpr .r7 = off B (dM + 8 * w)) (h10 : s.gpr .r10 = off B dU)
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (h9 : s.gpr .r9 = cnt h 0) (hh : 1 ≤ h) (hh' : h < 2 ^ 32)
    (hS : dS + 8 * N ≤ Z) (hp : p + 8 ≤ N) :
    WP isa (.block (boundary8 .r12 ++ ([.addc (sacc 0) (sacc 0) .r8] : List Instr) ++
      (List.range 7).map (fun c => .addze (sacc (c + 1)) (sacc (c + 1))) ++ ([.addze .r4 .r4] : List Instr) ++
      store8 sacc .r12 ++ ([.addi .r8 .r4 0, .lsl .r30 .r11 2, .sub .r7 .r7 .r30, .addi .r10 .r10 64, .li .r30 1,
        .lsl .r30 .r30 32, .sub .r9 .r9 .r30, .lsr .d .r30 .r9 32] : List Instr))) s fun t =>
      (wordsVal t.mem B dS N + 2 ^ (64 * (p + 8)) * (t.gpr .r8).toNat =
          totR s.mem B dS N p (Vw s .r0) + 2 ^ (64 * p) * (s.gpr .r8).toNat ∧ (t.gpr .r8).toNat ≤ 3 ∧
        Outside B (dS + 8 * p) 64 s.mem t.mem ∧ t.gpr .r7 = off B dM ∧ t.gpr .r10 = off B (dU + 64) ∧
        t.gpr .r9 = cnt (h - 1) 0 ∧ t.gpr .r30 = BitVec.ofNat 64 (h - 1)) ∧
      Keep (.r8 :: .r7 :: .r10 :: .r9 :: .r30 :: .r4 :: (List.range 8).map sacc) s t := by
  have hnw := hs.nowrap
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [WP.block_append_iff]
  refine WP.mono (boundary8_ok hs h0 h12 (by omega_using [hS, hp]) (by decide) (by decide) (by decide))
    fun t₁ ⟨⟨e₁, l₁, c₁, m₁⟩, k₁⟩ => ?_
  refine addTop_ok l₁ fun t₂ ⟨⟨e₂, l₂, m₂⟩, k₂⟩ => ?_
  have K₂ : Keep (.r4 :: .r30 :: (List.range 8).map sacc) s t₂ := (k₁.trans k₂).mono (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (store8_ok (d := dS + 8 * p) (hs.congr K₂.wr) (by rw [K₂.gpr _ (by decide), h12]) (by omega_using [hS, hp]) (by decide))
    fun t₃ ⟨⟨e₃, o₃, _⟩, k₃⟩ => ?_
  refine wp_addi (by decide) (by decide) fun v₁ x₁ f₁ _ => ?_
  refine wp_write (exec_lsl (by decide)) fun v₂ x₂ f₂ _ => ?_
  refine wp_write exec_sub fun v₃ x₃ f₃ _ => ?_
  refine wp_addi (by decide) (by decide) fun v₄ x₄ f₄ _ => ?_
  refine wp_write (exec_li (by decide)) fun v₅ x₅ f₅ _ => ?_
  refine wp_write (exec_lsl (by decide)) fun v₆ x₆ f₆ _ => ?_
  refine wp_write exec_sub fun v₇ x₇ f₇ _ => ?_
  refine wp_write (exec_lsr_d (by decide)) fun t x₈ f₈ _ => ?_
  have Kt : Keep [.r8, .r30, .r7, .r10, .r9] t₃ t :=
    (((((((x₁.keep.trans x₂.keep).trans x₃.keep).trans x₄.keep).trans x₅.keep).trans x₆.keep).trans
      x₇.keep).trans x₈.keep).mono (by decide)
  have mt : t.mem = t₃.mem := by
    rw [x₈.mem, x₇.mem, x₆.mem, x₅.mem, x₄.mem, x₃.mem, x₂.mem, x₁.mem]
  have r8t : t.gpr .r8 = t₂.gpr .r4 := by
    rw [x₈.gpr _ (by decide), x₇.gpr _ (by decide), x₆.gpr _ (by decide), x₅.gpr _ (by decide),
      x₄.gpr _ (by decide), x₃.gpr _ (by decide), x₂.gpr _ (by decide), f₁, k₃.gpr _ (by simp)]
    exact BitVec.add_zero _
  have r9₇ : v₇.gpr .r9 = cnt (h - 1) 0 := by
    rw [f₇, f₆, f₅, x₆.gpr .r9 (by decide), x₅.gpr .r9 (by decide), x₄.gpr .r9 (by decide), x₃.gpr .r9 (by decide),
      x₂.gpr .r9 (by decide), x₁.gpr .r9 (by decide), k₃.gpr _ (by simp), K₂.gpr _ (by decide), h9, cnt_decHi hh' hh]
  refine WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · have ms : t₂.mem = s.mem := by rw [m₂, m₁]
    rw [ms] at o₃
    have hw : ∀ d k, (d + 8 * k ≤ dS + 8 * p ∨ dS + 8 * p + 64 ≤ d) → d + 8 * k ≤ Z →
        wordsVal t.mem B d k = wordsVal s.mem B d k := fun d k h1 h2 => by rw [mt]; exact o₃.wordsVal h1 (by omega_using [hnw, h2])
    have A1 : wordsVal t.mem B dS N = wordsVal s.mem B dS p + 2 ^ (64 * p) * (rv t₂ sacc 8 +
        2 ^ (64 * 8) * wordsVal s.mem B (dS + 8 * p + 64) (N - p - 8)) := by
      have := fios_wordsVal_append t.mem B dS p (8 + (N - p - 8))
      rw [show p + (8 + (N - p - 8)) = N by omega_using [hp], fios_wordsVal_append] at this
      rw [this, hw dS p (Or.inl (by omega_using [])) (by omega_using [hS, hp]), show dS + 8 * p + 8 * 8 = dS + 8 * p + 64 by omega_using [],
        hw (dS + 8 * p + 64) (N - p - 8) (Or.inr (by omega_using [])) (by omega_using [hS, hp]), mt, e₃]
    have A2 : wordsVal s.mem B (dS + 8 * p) (N - p) = wordsVal s.mem B (dS + 8 * p) 8 +
        2 ^ (64 * 8) * wordsVal s.mem B (dS + 8 * p + 64) (N - p - 8) := by
      have := fios_wordsVal_append s.mem B (dS + 8 * p) 8 (N - p - 8)
      rwa [show 8 + (N - p - 8) = N - p by omega_using [hp], show dS + 8 * p + 8 * 8 = dS + 8 * p + 64 by omega_using []] at this
    have v₁ : Vw t₁ .r4 = rv t₁ sacc 8 + 2 ^ (64 * 8) * (t₁.gpr .r4).toNat := by
      unfold Vw; rw [c₁, pow512]; simp
    rw [k₁.gpr .r8 (by decide)] at e₂
    unfold totR
    rw [A1, A2, r8t, show 64 * (p + 8) = 64 * p + 64 * 8 by omega_using [], Nat.pow_add]
    have := e₂.trans (by rw [← v₁, e₁] : rv t₁ sacc 8 + 2 ^ (64 * 8) * (t₁.gpr .r4).toNat + (s.gpr .r8).toNat =
      Vw s .r0 + wordsVal s.mem B (dS + 8 * p) 8 + (s.gpr .r8).toNat)
    have h2 := congrArg (2 ^ (64 * p) * ·) this
    simp only [Nat.mul_add] at h2 ⊢
    grind
  · rw [r8t]; exact l₂
  · rw [mt, ← m₁, ← m₂]; exact o₃
  · rw [x₈.gpr _ (by decide), x₇.gpr _ (by decide), x₆.gpr _ (by decide), x₅.gpr _ (by decide),
      x₄.gpr _ (by decide), f₃, f₂, x₂.gpr .r7 (by decide), x₁.gpr .r7 (by decide), x₁.gpr .r11 (by decide),
      k₃.gpr _ (by simp), k₃.gpr _ (by simp), K₂.gpr _ (by decide), K₂.gpr _ (by decide), h7, h11, Mont4.shl2_8,
      off_sub _ (by omega_using []), Nat.add_sub_cancel]
  · rw [x₈.gpr _ (by decide), x₇.gpr _ (by decide), x₆.gpr _ (by decide), x₅.gpr _ (by decide), f₄,
      x₃.gpr _ (by decide), x₂.gpr _ (by decide), x₁.gpr _ (by decide), k₃.gpr _ (by simp), K₂.gpr _ (by decide),
      h10, off_add]
  · rw [x₈.gpr _ (by decide)]; exact r9₇
  · rw [f₈, r9₇, cnt_hi (by omega_using [hh']) (by decide)]
  · exact (((K₂.trans k₃).trans Kt).mono (by decide))

theorem redBlock_arith {A2 M M0 M' Ls N0 Nt T1 T2 P R W U r8 r8' : Nat} (eH : T1 = N0 + P * ((M0 + 1) * U))
    (eC : T2 = T1 + P * R * (M' * U)) (eT : Nt + P * W * R * r8' = T2 + P * W * r8)
    (inv : N0 + P * W * r8 = A2 + (M + 1) * Ls) (hM : M = M0 + R * M') :
    Nt + P * W * R * r8' = A2 + (M + 1) * (Ls + P * U) := by
  subst hM
  rw [eT, eC, eH]
  grind

/-- The registers a block of the reduction writes. -/
abbrev redRegs : List Reg :=
  .r8 :: .r10 :: .r7 :: .r12 :: .r30 :: .r9 :: .r3 :: .r4 :: .r31 :: ((List.range 8).map smr ++ (List.range 8).map sacc)

/-- One block of the reduction (`redBlock`), block `q` of `K` (`w = 8 K`, `S`'s
`2 w` words at `dS`, `m` at `dM`): with `U` the `uᵢ` so far (`S`'s low `8 q`
words) and the top `r8` (at `S`'s word `8 q + w`), `S + 2^(64 (8 q + w)) r8 =
A + (m + 1) U` stays true with a block more of `uᵢ`. -/
theorem redBlock_ok {s : State} {B : Addr} {Z dS dM K q A2 : Nat} (hs : Scr s B Z) (h0 : s.gpr .r0 = 0)
    (h10 : s.gpr .r10 = off B (dS + 8 * (8 * q))) (h7 : s.gpr .r7 = off B dM)
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * (8 * K))) (h9 : s.gpr .r9 = cnt (K - q) 0)
    (hq : q < K) (hK' : K < 2 ^ 28) (hS : dS + 8 * (16 * K) ≤ Z) (hM : dM + 32 * (8 * K) + 48 ≤ Z)
    (hsep : dM + 64 * K ≤ dS) (hmS : dS + 8 * (16 * K) ≤ dM + 32 * (8 * K) + 40)
    (hm : ((word s.mem B dM).toNat * (word s.mem B (dM + 32 * (8 * K) + 40)).toNat + 1) % 2 ^ 64 = 0)
    (inv : wordsVal s.mem B dS (16 * K) + 2 ^ (64 * (8 * q + 8 * K)) * (s.gpr .r8).toNat =
      A2 + (wordsVal s.mem B dM (8 * K) + 1) * wordsVal s.mem B dS (8 * q)) :
    WP isa redBlock s fun t =>
      (wordsVal t.mem B dS (16 * K) + 2 ^ (64 * (8 * (q + 1) + 8 * K)) * (t.gpr .r8).toNat =
          A2 + (wordsVal s.mem B dM (8 * K) + 1) * wordsVal t.mem B dS (8 * (q + 1)) ∧ (t.gpr .r8).toNat ≤ 3 ∧
        Outside B (dS + 8 * (8 * q)) (8 * (16 * K - 8 * q)) s.mem t.mem ∧
        t.gpr .r10 = off B (dS + 8 * (8 * (q + 1))) ∧ t.gpr .r7 = off B dM ∧ t.gpr .r9 = cnt (K - q - 1) 0 ∧
        t.gpr .r30 = BitVec.ofNat 64 (K - q - 1) ∧ t.gpr .r0 = 0) ∧ Keep redRegs s t := by
  have hnw := hs.nowrap
  unfold redBlock
  refine WP.seq (WP.mono (redHead_ok (N := 16 * K) (p := 8 * q) hs h0 h10 h7 h11 h9 (by omega) hK' (by omega) hS
    (by omega) (by omega) hM hm) fun t₁ ⟨⟨e₁, o₁, r7₁, r12₁, r9₁, z₁, _⟩, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.wr
  refine WP.seq (WP.mono (redChunks_ok (p := 8 * q + 8) (N := 16 * K) (G := K - 1) (dU := dS + 8 * (8 * q)) hs₁ z₁
    (by rw [r12₁, show dS + 8 * (8 * q) + 64 = dS + 8 * (8 * q + 8) by omega]) r7₁ (by rw [k₁.gpr _ (by decide), h10])
    r9₁ (by omega) hS (by omega) (by omega) (by omega) (by omega))
    fun t₂ ⟨⟨e₂, o₂, r12₂, r7₂, r9₂, r10₂, z₂⟩, k₂⟩ => ?_)
  have hs₂ := hs₁.congr k₂.wr
  have g₂ : ∀ r, r ∉ redHeadRegs → r ∉ chunkRegsR → t₂.gpr r = s.gpr r := fun r h1 h2 => by
    rw [k₂.gpr r h2, k₁.gpr r h1]
  refine WP.mono (redTail_ok (p := 8 * q + 8 + 8 * (K - 1)) (N := 16 * K) (dM := dM) (dU := dS + 8 * (8 * q))
    (w := 8 * K) hs₂ z₂ (by rw [r12₂, show dS + 8 * (8 * q + 8) + 64 * (K - 1) = dS + 8 * (8 * q + 8 + 8 * (K - 1)) by omega])
    (by rw [r7₂, show dM + 64 + 64 * (K - 1) = dM + 8 * (8 * K) by omega]) (by rw [r10₂, k₁.gpr _ (by decide), h10])
    (by rw [g₂ _ (by decide) (by decide), h11]) r9₂ (by omega) (by omega) hS (by omega))
    fun t ⟨⟨e₃, l₃, o₃, r7₃, r10₃, r9₃, r30₃⟩, k₃⟩ => ⟨⟨?_, l₃, ?_, ?_, r7₃, ?_, ?_, ?_⟩, ?_⟩
  -- The memory: what changed is `S`'s words from `8 q`.
  all_goals have O : Outside B (dS + 8 * (8 * q)) (8 * (16 * K - 8 * q)) s.mem t.mem :=
    ((o₁.mono (Nat.le_refl _) (by omega)).trans (o₂.mono (by omega) (by omega))).trans (o₃.mono (by omega) (by omega))
  · have wM : ∀ d k, d + 8 * k ≤ dS → wordsVal t₁.mem B d k = wordsVal s.mem B d k :=
      fun d k h => o₁.wordsVal (Or.inl (by omega)) (by omega)
    have hU : wordsVal t.mem B (dS + 8 * (8 * q)) 8 = wordsVal t₁.mem B (dS + 8 * (8 * q)) 8 := by
      rw [o₃.wordsVal (Or.inl (by omega)) (by omega), o₂.wordsVal (Or.inl (by omega)) (by omega)]
    have pt : 8 * q + 8 + 8 * (K - 1) = 8 * q + 8 * K := by omega
    rw [pt] at e₂ e₃
    have hP1 : 2 ^ (64 * (8 * q + 8)) = 2 ^ (64 * (8 * q)) * 2 ^ (64 * 8) := by rw [← Nat.pow_add, Nat.mul_add]
    have hP2 : 2 ^ (64 * (8 * q + 8 * K)) = 2 ^ (64 * (8 * q)) * 2 ^ (64 * (8 * K)) := by
      rw [← Nat.pow_add, Nat.mul_add]
    have hP3 : 2 ^ (64 * (8 * q + 8 * K + 8)) = 2 ^ (64 * (8 * q)) * 2 ^ (64 * (8 * K)) * 2 ^ (64 * 8) := by
      rw [← Nat.pow_add, ← Nat.pow_add, Nat.mul_add, Nat.mul_add]
    have hM' : wordsVal s.mem B dM (8 * K) = wordsVal s.mem B dM 8 +
        2 ^ (64 * 8) * wordsVal s.mem B (dM + 64) (8 * (K - 1)) := by
      have := fios_wordsVal_append s.mem B dM 8 (8 * (K - 1))
      rwa [show 8 + 8 * (K - 1) = 8 * K by omega, show dM + 8 * 8 = dM + 64 by omega] at this
    have hL : wordsVal t.mem B dS (8 * (q + 1)) = wordsVal s.mem B dS (8 * q) +
        2 ^ (64 * (8 * q)) * wordsVal t₁.mem B (dS + 8 * (8 * q)) 8 := by
      rw [show 8 * (q + 1) = 8 * q + 8 by omega, fios_wordsVal_append, O.wordsVal (Or.inl (by omega)) (by omega), hU]
    rw [hP1, wM _ _ (by omega)] at e₂
    rw [hP3, hP2, g₂ _ (by decide) (by decide)] at e₃
    rw [hP2] at inv
    rw [show 8 * (q + 1) + 8 * K = 8 * q + 8 * K + 8 by omega, hP3, hL]
    exact redBlock_arith e₁ e₂ e₃ inv hM'
  · exact O
  · rw [r10₃, show dS + 8 * (8 * q) + 64 = dS + 8 * (8 * (q + 1)) by omega]
  · rw [r9₃, show K - q - 1 = K - q - 1 from rfl]
  · rw [r30₃]
  · rw [k₃.gpr _ (by decide), z₂]
  · exact ((k₁.trans k₂).trans k₃).mono (by decide)

/-- The reduction (`sqrRed`), `S` (`2 w = 16 K` words at `dS`) holding `A` and
`m` at `dS - 16 (w + 2)`: the `uᵢ` into `S`'s low `w` words, `U`, and `S`'s top
`w` words with the top carry (`r8`) `(A + U m) / 2^(64 w)`. -/
theorem sqrRed_ok {s : State} {B : Addr} {Z dS dM K : Nat} (hs : Scr s B Z) (h0 : s.gpr .r0 = 0)
    (h10 : s.gpr .r10 = off B dS) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * (8 * K))) (hK : 1 ≤ K) (hK' : K < 2 ^ 28)
    (hlay : dS = dM + 16 * (8 * K + 2)) (hS : dS + 8 * (16 * K) + 16 ≤ Z)
    (hm : ((word s.mem B dM).toNat * (word s.mem B (dM + 32 * (8 * K) + 40)).toNat + 1) % 2 ^ 64 = 0) :
    WP isa sqrRed s fun t =>
      (wordsVal t.mem B dS (16 * K) + 2 ^ (64 * (16 * K)) * (t.gpr .r8).toNat =
          wordsVal s.mem B dS (16 * K) + (wordsVal s.mem B dM (8 * K) + 1) * wordsVal t.mem B dS (8 * K) ∧
        Outside B dS (8 * (16 * K)) s.mem t.mem ∧ t.gpr .r10 = off B (dS + 8 * (8 * K)) ∧ t.gpr .r0 = 0) ∧
      Keep redRegs s t := by
  have hnw := hs.nowrap
  unfold sqrRed
  refine WP.seq ?_
  refine wp_write (exec_lsl (by decide)) fun u₁ w₁ f₁ _ => ?_
  refine wp_write exec_sub fun u₂ w₂ f₂ _ => ?_
  refine wp_write (exec_subi (by decide) (by decide)) fun u₃ w₃ f₃ _ => ?_
  refine wp_write (exec_li (by decide)) fun u₄ w₄ f₄ _ => ?_
  refine wp_write (exec_lsr_d (by decide)) fun u₅ w₅ f₅ _ => ?_
  refine wp_write (exec_lsl (by decide)) fun u₆ w₆ f₆ _ => WP.block_nil ?_
  have k₆ : Keep [.r30, .r7, .r8, .r9] s u₆ :=
    (((((w₁.keep.trans w₂.keep).trans w₃.keep).trans w₄.keep).trans w₅.keep).trans w₆.keep).mono (by decide)
  have m₆ : u₆.mem = s.mem := by rw [w₆.mem, w₅.mem, w₄.mem, w₃.mem, w₂.mem, w₁.mem]
  have r7₆ : u₆.gpr .r7 = off B dM := by
    rw [w₆.gpr _ (by decide), w₅.gpr _ (by decide), w₄.gpr _ (by decide), f₃, f₂, f₁, w₁.gpr .r10 (by decide),
      h10, h11]
    have : BitVec.ofNat 64 (2 * (8 * K)) <<< 3 = BitVec.ofNat 64 (128 * K) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      omega_using []
    rw [this, off_sub _ (by omega_using [hlay]), off_sub _ (by omega_using [hlay]), show dS - 128 * K - 32 = dM by omega_using [hlay]]
  have r30₅ : u₅.gpr .r30 = BitVec.ofNat 64 K := by
    rw [f₅, w₄.gpr _ (by decide), w₃.gpr _ (by decide), w₂.gpr _ (by decide), w₁.gpr _ (by decide), h11]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega_using [hK']
  have r9₆ : u₆.gpr .r9 = cnt K 0 := by
    rw [f₆, r30₅]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega_using []
  have r8₆ : u₆.gpr .r8 = 0 := by rw [w₆.gpr _ (by decide), w₅.gpr _ (by decide), f₄]; rfl
  let I : Nat → State → Prop := fun q t => Scr t B Z ∧ t.gpr .r0 = 0 ∧ t.gpr .r10 = off B (dS + 8 * (8 * q)) ∧
    t.gpr .r7 = off B dM ∧ t.gpr .r9 = cnt (K - q) 0 ∧ t.gpr .r11 = s.gpr .r11 ∧
    wordsVal t.mem B dS (16 * K) + 2 ^ (64 * (8 * q + 8 * K)) * (t.gpr .r8).toNat =
      wordsVal s.mem B dS (16 * K) + (wordsVal s.mem B dM (8 * K) + 1) * wordsVal t.mem B dS (8 * q) ∧
    Outside B dS (8 * (16 * K)) s.mem t.mem ∧ Keep redRegs s t
  have I0 : I 0 u₆ := ⟨hs.congr k₆.wr, by rw [k₆.gpr _ (by decide), h0], by simp only [k₆.gpr .r10 (by decide), h10,
      Nat.mul_zero, Nat.add_zero], r7₆, by simp only [r9₆, Nat.sub_zero], k₆.gpr _ (by decide),
    by simp [r8₆, m₆, wordsVal], by rw [m₆]; exact Outside.refl _ _ _ _, k₆.mono (by decide)⟩
  refine WP.mono (count_loop (cr := .r30) (n := K) hK I (fun q hq t ⟨ht, t0, t10, t7, t9, t11, te, to, tk⟩ =>
    WP.mono (redBlock_ok (A2 := wordsVal s.mem B dS (16 * K)) ht t0 t10 t7 (by rw [t11, h11]) t9 hq hK'
      (by omega_using [hS]) (by omega_using [hlay, hS]) (by omega_using [hlay]) (by omega_using [hlay])
      (by rw [to.word (Or.inl (by omega_using [hlay])) (by omega), to.word (Or.inr (by omega_using [hlay])) (by omega_using [hlay, hS, hnw])]; exact hm)
      (by rw [to.wordsVal (d := dM) (Or.inl (by omega_using [hlay])) (by omega_using [hlay, hS, hnw])]; exact te))
      fun t' ⟨⟨e, _, o, r10, r7, r9, r30, r0⟩, k'⟩ => ⟨⟨ht.congr k'.wr, r0, r10, r7,
        by rw [r9, show K - q - 1 = K - (q + 1) by omega_using []], by rw [k'.gpr _ (by decide), t11],
        by rw [e, to.wordsVal (d := dM) (Or.inl (by omega_using [hlay])) (by omega_using [hlay, hS, hnw])],
        to.trans (o.mono (by omega_using []) (by omega_using [hq])), (tk.trans k').mono (by decide)⟩,
        by rw [r30, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hK'])]; omega_using [hq]⟩) I0)
    fun t ⟨_, t0, t10, _, _, _, te, to, tk⟩ => ⟨⟨?_, to, t10, t0⟩, tk⟩
  rw [show 8 * K + 8 * K = 16 * K by omega_using []] at te
  exact te

/-! ## The squaring's start and end -/

/-- `n ≤ 16` words of zeros (`r0`) at `ptr` (at `d`). -/
theorem zeroN_ok {ptr : Reg} {B : Addr} {Z d : Nat} (hp0 : ptr ≠ .r0) :
    ∀ (n : Nat) {s : State}, Scr s B Z → s.gpr ptr = off B d → s.gpr .r0 = 0 → n ≤ 16 → d + 8 * n ≤ Z →
    WP isa (.block ((List.range n).map fun c => .store .d .r0 ptr (8 * c))) s fun t =>
      (wordsVal t.mem B d n = 0 ∧ Outside B d (8 * n) s.mem t.mem ∧ t.ca = s.ca) ∧ Keep [] s t
  | 0, s, _, _, _, _, _ => WP.block_nil ⟨⟨rfl, Outside.refl _ _ _ _, rfl⟩, Keep.refl _ _⟩
  | n + 1, s, hs, hp, h0, hn, hd => by
    have hnw := hs.nowrap
    rw [Mont4.map_succ, WP.block_append_iff]
    refine WP.mono (zeroN_ok hp0 n hs hp h0 (by omega_using [hn]) (by omega_using [hd])) fun t₁ ⟨⟨e₁, o₁, c₁⟩, k₁⟩ => ?_
    refine wp_st hp0 ⟨by omega_using [hn], by omega_using []⟩ (by rw [k₁.gpr _ (by simp), hp, off_add]) ((hs.congr k₁.wr).st (by omega_using [hd]))
      fun t w wm c => WP.block_nil ⟨⟨?_, ?_, by rw [c, c₁]⟩, k₁.trans' w⟩
    · rw [wm, fios_wordsVal_write_top _ _ _ _ _ (by omega_using [hd, hnw]), e₁, k₁.gpr _ (by simp), h0]; rfl
    · rw [wm]
      exact (o₁.mono (Nat.le_refl _) (by omega_using [])).trans ((writeW_outside _ B _ (by omega_using [hd, hnw])).mono (by omega_using []) (by omega_using []))

/-- The squaring's start (`sqrInit`): `m' = -m⁻¹ mod 2⁶⁴` (from `y`, `r12`)
into `S`'s word `2 w + 1`, and `S`'s first `2 w + 1` words (`w = 8 K`) := 0. -/
theorem sqrInit_ok {s : State} {B : Addr} {Z dS dM K : Nat} (hs : Scr s B Z) (h10 : s.gpr .r10 = off B dM)
    (h8 : s.gpr .r8 = off B dS) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * (8 * K))) (hK : 1 ≤ K) (hK' : K < 2 ^ 28)
    (hM : dM + 8 ≤ Z) (hS : dS + 8 * (16 * K + 2) ≤ Z) :
    WP isa sqrInit s fun t =>
      (wordsVal t.mem B dS (16 * K + 1) = 0 ∧
        word t.mem B (dS + 8 * (16 * K + 1)) = (word s.mem B dM * s.gpr .r12 + BitVec.ofNat 64 2) * s.gpr .r12 ∧
        Outside B dS (8 * (16 * K + 2)) s.mem t.mem ∧ t.gpr .r0 = 0) ∧
      Keep [.r0, .r3, .r30, .r31] s t := by
  have hnw := hs.nowrap
  unfold sqrInit countLoop
  refine WP.seq ?_
  refine wp_write (exec_li (by decide)) fun u₀ w₀ f₀ _ => ?_
  refine wp_ld (by decide) ⟨by decide, by decide⟩ (by rw [w₀.gpr _ (by decide), h10, off_add, Nat.add_zero])
    ((hs.congr w₀.wr).ld (by omega_using [hM])) fun u₁ w₁ f₁ _ => ?_
  refine wp_mul fun u₂ w₂ f₂ _ => ?_
  refine wp_addi (by decide) (by decide) fun u₃ w₃ f₃ _ => ?_
  refine wp_mul fun u₄ w₄ f₄ _ => ?_
  refine wp_write (exec_lsl (by decide)) fun u₅ w₅ f₅ _ => ?_
  refine wp_write exec_add fun u₆ w₆ f₆ _ => ?_
  have K₆ : Keep [.r0, .r3, .r30, .r31] s u₆ :=
    ((((((w₀.keep.trans w₁.keep).trans w₂.keep).trans w₃.keep).trans w₄.keep).trans w₅.keep).trans w₆.keep).mono
      (by decide)
  have hs₆ : Scr u₆ B Z := hs.congr K₆.wr
  have m₆ : u₆.mem = s.mem := by rw [w₆.mem, w₅.mem, w₄.mem, w₃.mem, w₂.mem, w₁.mem, w₀.mem]
  have g₄ : ∀ r, r ≠ .r0 → r ≠ .r3 → u₄.gpr r = s.gpr r := fun r a b => by
    rw [w₄.gpr _ b, w₃.gpr _ b, w₂.gpr _ b, w₁.gpr _ b, w₀.gpr _ a]
  have shl3 : BitVec.ofNat 64 (2 * (8 * K)) <<< 3 = BitVec.ofNat 64 (8 * (16 * K)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega_using []
  have p31 : u₆.gpr .r31 = off B (dS + 8 * (16 * K)) := by
    rw [f₆, f₅, w₅.gpr .r8 (by decide), g₄ _ (by decide) (by decide), g₄ _ (by decide) (by decide), h8, h11, shl3,
      off_add]
  have mv : u₆.gpr .r3 = (word s.mem B dM * s.gpr .r12 + BitVec.ofNat 64 2) * s.gpr .r12 := by
    rw [w₆.gpr _ (by decide), w₅.gpr _ (by decide), f₄, f₃, f₂, f₁, w₃.gpr .r12 (by decide), w₂.gpr .r12 (by decide),
      w₁.gpr .r12 (by decide), w₀.gpr .r12 (by decide), w₀.mem]
  have z₆ : u₆.gpr .r0 = 0 := by
    rw [w₆.gpr _ (by decide), w₅.gpr _ (by decide), w₄.gpr _ (by decide), w₃.gpr _ (by decide), w₂.gpr _ (by decide),
      w₁.gpr _ (by decide), f₀]; rfl
  refine wp_st (by decide) ⟨by decide, by decide⟩ (by rw [p31, off_add]) (hs₆.st (by omega_using [hS])) fun v₁ k₁ m₁ c₁ => ?_
  refine wp_st (a := off B (dS + 8 * (16 * K))) (by decide) ⟨by decide, by decide⟩
    (by rw [k₁.gpr _ (by simp), p31]; exact BitVec.add_zero _) ((hs₆.congr k₁.wr).st (by omega_using [hS])) fun v₂ k₂ m₂ c₂ => ?_
  refine wp_addi (by decide) (by decide) fun v₃ x₃ f₃ _ => ?_
  refine wp_write (exec_lsr_d (by decide)) fun v₄ x₄ f₄' _ => WP.block_nil ?_
  have K₄ : Keep [.r0, .r3, .r30, .r31] s v₄ := (((K₆.trans k₁).trans k₂).trans (x₃.keep.trans x₄.keep)).mono (by decide)
  have m₄ : v₄.mem = (s.mem.writeW (off B (dS + 8 * (16 * K) + 8)) (u₆.gpr .r3)).writeW (off B (dS + 8 * (16 * K)))
      (0 : BitVec 64) := by
    rw [x₄.mem, x₃.mem, m₂, k₁.gpr _ (by simp), z₆, m₁, m₆]
  have r3₄ : v₄.gpr .r3 = BitVec.ofNat 64 K := by
    rw [f₄', x₃.gpr _ (by decide), k₂.gpr _ (by simp), k₁.gpr _ (by simp), w₆.gpr _ (by decide), w₅.gpr _ (by decide),
      g₄ _ (by decide) (by decide), h11]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega_using [hK']
  have r31₄ : v₄.gpr .r31 = off B dS := by
    rw [x₄.gpr _ (by decide), f₃, k₂.gpr _ (by simp), k₁.gpr _ (by simp), w₆.gpr _ (by decide), w₅.gpr _ (by decide),
      g₄ _ (by decide) (by decide), h8]; exact BitVec.add_zero _
  have z₄ : v₄.gpr .r0 = 0 := by rw [x₄.gpr _ (by decide), x₃.gpr _ (by decide), k₂.gpr _ (by simp), k₁.gpr _ (by simp), z₆]
  have hw1 : word v₄.mem B (dS + 8 * (16 * K + 1)) = (word s.mem B dM * s.gpr .r12 + BitVec.ofNat 64 2) * s.gpr .r12 := by
    rw [m₄, (writeW_outside _ B _ (by omega_using [hS, hnw])).word (by omega_using []) (by omega_using [hS, hnw]), show dS + 8 * (16 * K + 1) = dS + 8 * (16 * K) + 8 by omega_using [],
      word_writeW_self, mv]
  have hw0 : word v₄.mem B (dS + 8 * (16 * K)) = 0 := by rw [m₄, word_writeW_self]
  have o₄ : Outside B dS (8 * (16 * K + 2)) s.mem v₄.mem := by
    rw [m₄]
    exact ((writeW_outside _ B _ (by omega_using [hS, hnw])).mono (by omega_using []) (by omega_using [])).trans
      ((writeW_outside _ B _ (by omega_using [hS, hnw])).mono (by omega_using []) (by omega_using []))
  refine WP.mono (wp_countdown (cnt := .r3) (N := K) (by omega_using [hK']) hK (fun i t =>
    (Scr t B Z ∧ t.gpr .r31 = off B (dS + 128 * i) ∧ t.gpr .r0 = 0 ∧ wordsVal t.mem B dS (16 * i) = 0 ∧
      word t.mem B (dS + 8 * (16 * K)) = 0 ∧
      word t.mem B (dS + 8 * (16 * K + 1)) = (word s.mem B dM * s.gpr .r12 + BitVec.ofNat 64 2) * s.gpr .r12 ∧
      Outside B dS (8 * (16 * K + 2)) s.mem t.mem) ∧ Keep [.r0, .r3, .r30, .r31] s t)
    (fun i hi t ⟨⟨ht, t31, t0, te, tz, tm, to⟩, tk⟩ _ => ?_)
    ⟨⟨hs.congr K₄.wr, by rw [r31₄]; simp, z₄, by simp [wordsVal], hw0, hw1, o₄⟩, K₄⟩ r3₄)
    fun t ⟨⟨_, _, t0, te, tz, tm, to⟩, tk⟩ => ⟨⟨?_, tm, to, t0⟩, tk⟩
  · have htw := ht.nowrap
    rw [WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (zeroN_ok (d := dS + 128 * i) (by decide) 16 ht t31 t0 (Nat.le_refl _) (by omega_using [hS, hi]))
      fun t₁ ⟨⟨e₁, o₁, _⟩, k₁⟩ => ?_
    refine wp_addi (by decide) (by decide) fun t₂ x₂ f₂ _ => WP.block_nil ?_
    refine wp_write (exec_subi (by decide) (by decide)) fun t' x₃ f₃ _ => WP.block_nil ⟨⟨⟨ht.congr ((k₁.trans x₂.keep).trans x₃.keep).wr,
      by rw [x₃.gpr _ (by decide), f₂, k₁.gpr _ (by simp), t31, off_add, show dS + 128 * i + 128 = dS + 128 * (i + 1) by omega_using []],
      by rw [x₃.gpr _ (by decide), x₂.gpr _ (by decide), k₁.gpr _ (by simp), t0], ?_, ?_, ?_, ?_⟩,
      (tk.trans ((k₁.trans x₂.keep).trans x₃.keep)).mono (by decide)⟩,
      by rw [f₃, x₂.gpr _ (by decide), k₁.gpr _ (by simp)]⟩
    all_goals have mt : t'.mem = t₁.mem := by rw [x₃.mem, x₂.mem]
    · rw [mt, show 16 * (i + 1) = 16 * i + 16 by omega_using [], fios_wordsVal_append, o₁.wordsVal (Or.inl (by omega_using [])) (by omega_using [hS, hnw, hi]), te,
        show dS + 8 * (16 * i) = dS + 128 * i by omega_using [], e₁, Nat.mul_zero]
    · rw [mt, o₁.word (Or.inr (by omega_using [hi])) (by omega_using [hS, hnw]), tz]
    · rw [mt, o₁.word (Or.inr (by omega_using [hi])) (by omega_using [hS, hnw]), tm]
    · rw [mt]; exact to.trans (o₁.mono (by omega_using []) (by omega_using [hi]))
  · rw [wordsVal_succ_top, te, tz]; rfl

/-- The end of `sqrCopy`: `T`'s top word (`r8`), then the bases and `m'`. -/
theorem copyTail_ok {s : State} {B : Addr} {Z dS dM K : Nat} (hs : Scr s B Z)
    (h31 : s.gpr .r31 = off B (dS + 64 * K)) (h12 : s.gpr .r12 = off B dS)
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * (8 * K))) (hK : 1 ≤ K) (hK' : K < 2 ^ 28)
    (hlay : dS = dM + 16 * (8 * K + 2)) (hS : dS + 8 * (16 * K + 2) ≤ Z) :
    WP isa (.block [.store .d .r8 .r31 0, .addi .r8 .r12 0, .lsl .r30 .r11 2, .add .r9 .r8 .r30, .addi .r9 .r9 16,
        .lsl .r30 .r11 3, .sub .r10 .r8 .r30, .subi .r10 .r10 32, .lsl .r30 .r11 2, .add .r30 .r9 .r30,
        .subi .r30 .r30 8, .load .d .r22 .r30 0, .addi .r7 .r6 0]) s fun t =>
      (word t.mem B (dS + 8 * (8 * K)) = s.gpr .r8 ∧ Outside B (dS + 8 * (8 * K)) 8 s.mem t.mem ∧
        t.gpr .r8 = off B dS ∧ t.gpr .r9 = off B (dS + 8 * (8 * K + 2)) ∧ t.gpr .r10 = off B dM ∧
        t.gpr .r22 = word t.mem B (dS + 8 * (16 * K + 1)) ∧ t.gpr .r7 = s.gpr .r6) ∧
      Keep [.r8, .r30, .r9, .r10, .r22, .r7] s t := by
  have hnw := hs.nowrap
  have sh2 := Mont4.shl2_8 (8 * K)
  have sh3 : BitVec.ofNat 64 (2 * (8 * K)) <<< 3 = BitVec.ofNat 64 (16 * (8 * K)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  refine wp_st (a := off B (dS + 8 * (8 * K))) (by decide) ⟨by decide, by decide⟩
    (by rw [h31, show dS + 64 * K = dS + 8 * (8 * K) by omega]; exact BitVec.add_zero _) (hs.st (by omega))
    fun u₀ k₀ m₀ _ => ?_
  refine wp_addi (by decide) (by decide) fun u₁ w₁ f₁ _ => ?_
  refine wp_write (exec_lsl (by decide)) fun u₂ w₂ f₂ _ => ?_
  refine wp_write exec_add fun u₃ w₃ f₃ _ => ?_
  refine wp_addi (by decide) (by decide) fun u₄ w₄ f₄ _ => ?_
  refine wp_write (exec_lsl (by decide)) fun u₅ w₅ f₅ _ => ?_
  refine wp_write exec_sub fun u₆ w₆ f₆ _ => ?_
  refine wp_write (exec_subi (by decide) (by decide)) fun u₇ w₇ f₇ _ => ?_
  refine wp_write (exec_lsl (by decide)) fun u₈ w₈ f₈ _ => ?_
  refine wp_write exec_add fun u₉ w₉ f₉ _ => ?_
  refine wp_write (exec_subi (by decide) (by decide)) fun u₁₀ w₁₀ f₁₀ _ => ?_
  have K₁₀ : Keep [.r8, .r30, .r9, .r10] s u₁₀ :=
    ((((((((((k₀.trans w₁.keep).trans w₂.keep).trans w₃.keep).trans w₄.keep).trans w₅.keep).trans w₆.keep).trans
      w₇.keep).trans w₈.keep).trans w₉.keep).trans w₁₀.keep).mono (by decide)
  have m₁₀ : u₁₀.mem = s.mem.writeW (off B (dS + 8 * (8 * K))) (s.gpr .r8) := by
    rw [w₁₀.mem, w₉.mem, w₈.mem, w₇.mem, w₆.mem, w₅.mem, w₄.mem, w₃.mem, w₂.mem, w₁.mem, m₀]
  have r11 : ∀ {u : State}, Keep [.r8, .r30, .r9, .r10] s u → u.gpr .r11 = BitVec.ofNat 64 (2 * (8 * K)) :=
    fun k => by rw [k.gpr _ (by decide), h11]
  have r8₁ : u₁.gpr .r8 = off B dS := by rw [f₁, k₀.gpr _ (by simp), h12]; exact BitVec.add_zero _
  have r9₄ : u₄.gpr .r9 = off B (dS + 8 * (8 * K) + 16) := by
    rw [f₄, f₃, f₂, w₂.gpr .r8 (by decide), r8₁, w₁.gpr .r11 (by decide), k₀.gpr _ (by simp), h11, sh2, off_add,
      off_off, Nat.add_assoc]
  have r10₇ : u₇.gpr .r10 = off B dM := by
    rw [f₇, f₆, f₅, w₅.gpr .r8 (by decide), w₄.gpr .r8 (by decide), w₃.gpr .r8 (by decide), w₂.gpr .r8 (by decide), r8₁,
      w₄.gpr .r11 (by decide), w₃.gpr .r11 (by decide), w₂.gpr .r11 (by decide), w₁.gpr .r11 (by decide),
      k₀.gpr _ (by simp), h11, sh3, off_sub _ (by omega), off_sub _ (by omega), show dS - 16 * (8 * K) - 32 = dM by omega]
  have r30₁₀ : u₁₀.gpr .r30 = off B (dS + 8 * (16 * K + 1)) := by
    rw [f₁₀, f₉, f₈, w₈.gpr .r9 (by decide), w₇.gpr .r9 (by decide), w₆.gpr .r9 (by decide), w₅.gpr .r9 (by decide), r9₄,
      w₇.gpr .r11 (by decide), w₆.gpr .r11 (by decide), w₅.gpr .r11 (by decide), w₄.gpr .r11 (by decide),
      w₃.gpr .r11 (by decide), w₂.gpr .r11 (by decide), w₁.gpr .r11 (by decide), k₀.gpr _ (by simp), h11, sh2, off_add,
      off_sub _ (by omega), show dS + 8 * (8 * K) + 16 + 8 * (8 * K) - 8 = dS + 8 * (16 * K + 1) by omega]
  refine wp_ld (by decide) ⟨by decide, by decide⟩ (by rw [r30₁₀]; exact BitVec.add_zero _) ((hs.congr K₁₀.wr).ld (by omega))
    fun u₁₁ w₁₁ f₁₁ _ => ?_
  refine wp_addi (by decide) (by decide) fun t w₁₂ f₁₂ _ => WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  all_goals have mt : t.mem = u₁₀.mem := by rw [w₁₂.mem, w₁₁.mem]
  · rw [mt, m₁₀, word_writeW_self]
  · rw [mt, m₁₀]; exact writeW_outside _ B _ (by omega)
  · rw [w₁₂.gpr .r8 (by decide), w₁₁.gpr .r8 (by decide), w₁₀.gpr .r8 (by decide), w₉.gpr .r8 (by decide),
      w₈.gpr .r8 (by decide), w₇.gpr .r8 (by decide), w₆.gpr .r8 (by decide), w₅.gpr .r8 (by decide),
      w₄.gpr .r8 (by decide), w₃.gpr .r8 (by decide), w₂.gpr .r8 (by decide), r8₁]
  · rw [w₁₂.gpr .r9 (by decide), w₁₁.gpr .r9 (by decide), w₁₀.gpr .r9 (by decide), w₉.gpr .r9 (by decide),
      w₈.gpr .r9 (by decide), w₇.gpr .r9 (by decide), w₆.gpr .r9 (by decide), w₅.gpr .r9 (by decide), r9₄,
      show dS + 8 * (8 * K) + 16 = dS + 8 * (8 * K + 2) by omega]
  · rw [w₁₂.gpr .r10 (by decide), w₁₁.gpr .r10 (by decide), w₁₀.gpr .r10 (by decide), w₉.gpr .r10 (by decide),
      w₈.gpr .r10 (by decide), r10₇]
  · rw [w₁₂.gpr .r22 (by decide), f₁₁, mt]
  · rw [f₁₂, w₁₁.gpr .r6 (by decide), K₁₀.gpr .r6 (by decide)]; exact BitVec.add_zero _
  · exact ((K₁₀.trans w₁₁.keep).trans w₁₂.keep).mono (by decide)

/-- The squaring's end (`sqrCopy`), `S`'s top half at `dS + 8 w` (`r10`, `w = 8 K`):
`T` (`w + 1` words at `dS`) := `S`'s top `w` words and the top carry (`r8`),
then the bases (`r8`, `r9`, `r10`), `b`'s pointer (`r7 := r6`) and `m'` (`r22`,
from `S`'s word `2 w + 1`) where the rounds leave them. -/
theorem sqrCopy_ok {s : State} {B : Addr} {Z dS dM K : Nat} (hs : Scr s B Z)
    (h10 : s.gpr .r10 = off B (dS + 8 * (8 * K))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * (8 * K))) (hK : 1 ≤ K)
    (hK' : K < 2 ^ 28) (hlay : dS = dM + 16 * (8 * K + 2)) (hS : dS + 8 * (16 * K + 2) ≤ Z) :
    WP isa sqrCopy s fun t =>
      (wordsVal t.mem B dS (8 * K + 1) = wordsVal s.mem B (dS + 8 * (8 * K)) (8 * K) +
          2 ^ (64 * (8 * K)) * (s.gpr .r8).toNat ∧ Outside B dS (8 * (8 * K + 1)) s.mem t.mem ∧
        t.gpr .r8 = off B dS ∧ t.gpr .r9 = off B (dS + 8 * (8 * K + 2)) ∧ t.gpr .r10 = off B dM ∧
        t.gpr .r22 = word s.mem B (dS + 8 * (16 * K + 1)) ∧ t.gpr .r7 = s.gpr .r6) ∧
      Keep (.r30 :: .r12 :: .r9 :: .r31 :: .r10 :: .r8 :: .r22 :: .r7 :: (List.range 8).map sacc) s t := by
  have hnw := hs.nowrap
  have sh2 := Mont4.shl2_8 (8 * K)
  have sh3 : BitVec.ofNat 64 (2 * (8 * K)) <<< 3 = BitVec.ofNat 64 (16 * (8 * K)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega_using []
  unfold sqrCopy countLoop
  refine WP.seq ?_
  refine wp_write (exec_lsl (by decide)) fun u₁ w₁ f₁ _ => ?_
  refine wp_write exec_sub fun u₂ w₂ f₂ _ => ?_
  refine wp_write (exec_lsr_d (by decide)) fun u₃ w₃ f₃ _ => ?_
  refine wp_addi (by decide) (by decide) fun u₄ w₄ f₄ _ => WP.block_nil ?_
  have k₄ : Keep [.r30, .r12, .r9, .r31] s u₄ := (((w₁.keep.trans w₂.keep).trans w₃.keep).trans w₄.keep).mono (by decide)
  have r12₄ : u₄.gpr .r12 = off B dS := by
    rw [w₄.gpr _ (by decide), w₃.gpr _ (by decide), f₂, f₁, w₁.gpr .r10 (by decide), h10, h11, sh2, off_sub _ (by omega_using []),
      Nat.add_sub_cancel]
  have r31₄ : u₄.gpr .r31 = off B dS := by
    rw [f₄, w₃.gpr _ (by decide), f₂, f₁, w₁.gpr .r10 (by decide), h10, h11, sh2, off_sub _ (by omega_using []),
      Nat.add_sub_cancel]; exact BitVec.add_zero _
  have r9₄ : u₄.gpr .r9 = BitVec.ofNat 64 K := by
    rw [w₄.gpr _ (by decide), f₃, w₂.gpr .r11 (by decide), w₁.gpr .r11 (by decide), h11]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega_using [hK']
  have m₄ : u₄.mem = s.mem := by rw [w₄.mem, w₃.mem, w₂.mem, w₁.mem]
  have L₄ : Keep (.r30 :: .r12 :: .r9 :: .r31 :: .r10 :: .r8 :: .r22 :: .r7 :: (List.range 8).map sacc) s u₄ :=
    k₄.mono (by decide)
  refine WP.seq (WP.mono (wp_countdown (cnt := .r9) (N := K) (by omega_using [hK']) hK (fun i t =>
    (Scr t B Z ∧ t.gpr .r10 = off B (dS + 8 * (8 * K) + 64 * i) ∧ t.gpr .r31 = off B (dS + 64 * i) ∧
      wordsVal t.mem B dS (8 * i) = wordsVal s.mem B (dS + 8 * (8 * K)) (8 * i) ∧
      Outside B dS (64 * i) s.mem t.mem ∧ t.gpr .r12 = off B dS ∧ t.gpr .r8 = s.gpr .r8) ∧
    Keep (.r30 :: .r12 :: .r9 :: .r31 :: .r10 :: .r8 :: .r22 :: .r7 :: (List.range 8).map sacc) s t)
    (fun i hi t ⟨⟨ht, t10, t31, te, to, t12, t8⟩, tk⟩ _ => ?_)
    ⟨⟨hs.congr k₄.wr, by rw [k₄.gpr _ (by decide), h10]; simp, by rw [r31₄]; simp, by simp [wordsVal],
      by rw [m₄]; exact Outside.refl _ _ _ _, r12₄, k₄.gpr _ (by decide)⟩, L₄⟩ r9₄)
    fun t ⟨⟨ht, t10, t31, te, to, t12, t8⟩, tk⟩ => ?_)
  · rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (load8_ok (d := dS + 8 * (8 * K) + 64 * i) ht t10 (by omega_using [hS, hi]) (by decide) (by decide))
      fun t₁ ⟨⟨e₁, m₁, _, _⟩, k₁⟩ => ?_
    refine WP.mono (store8_ok (d := dS + 64 * i) (hs.congr (tk.trans k₁).wr) (by rw [k₁.gpr _ (by decide), t31]) (by omega_using [hS, hi])
      (by decide)) fun t₂ ⟨⟨e₂, o₂, _⟩, k₂⟩ => ?_
    refine wp_addi (by decide) (by decide) fun t₃ x₃ f₃ _ => ?_
    refine wp_addi (by decide) (by decide) fun t₄ x₄ f₄ _ => WP.block_nil ?_
    refine wp_write (exec_subi (by decide) (by decide)) fun t' x₅ f₅ _ => WP.block_nil
      ⟨⟨⟨ht.congr ((((k₁.trans k₂).trans x₃.keep).trans x₄.keep).trans x₅.keep).wr, ?_, ?_, ?_, ?_, ?_, ?_⟩,
        (tk.trans ((((k₁.trans k₂).trans x₃.keep).trans x₄.keep).trans x₅.keep)).mono (by decide)⟩, ?_⟩
    all_goals have mt : t'.mem = t₂.mem := by rw [x₅.mem, x₄.mem, x₃.mem]
    · rw [x₅.gpr _ (by decide), x₄.gpr _ (by decide), f₃, k₂.gpr _ (by simp), k₁.gpr _ (by decide), t10, off_add,
        show dS + 8 * (8 * K) + 64 * i + 64 = dS + 8 * (8 * K) + 64 * (i + 1) by omega_using []]
    · rw [x₅.gpr _ (by decide), f₄, x₃.gpr _ (by decide), k₂.gpr _ (by simp), k₁.gpr _ (by decide), t31, off_add,
        show dS + 64 * i + 64 = dS + 64 * (i + 1) by omega_using []]
    · have src : wordsVal t.mem B (dS + 8 * (8 * K) + 64 * i) 8 = wordsVal s.mem B (dS + 8 * (8 * K) + 64 * i) 8 :=
        to.wordsVal (Or.inr (by omega_using [])) (by omega_using [hS, hnw, hi])
      rw [mt, show 8 * (i + 1) = 8 * i + 8 by omega_using [], fios_wordsVal_append, fios_wordsVal_append (d := dS + 8 * (8 * K)),
        o₂.wordsVal (Or.inl (by omega_using [])) (by omega_using [hS, hnw, hi]), m₁, te, show dS + 8 * (8 * i) = dS + 64 * i by omega_using [], e₂, e₁, src,
        show dS + 8 * (8 * K) + 8 * (8 * i) = dS + 8 * (8 * K) + 64 * i by omega_using []]
    · rw [mt]; rw [m₁] at o₂; exact (to.mono (Nat.le_refl _) (by omega_using [])).trans (o₂.mono (by omega_using []) (by omega_using []))
    · rw [x₅.gpr _ (by decide), x₄.gpr _ (by decide), x₃.gpr _ (by decide), k₂.gpr _ (by simp), k₁.gpr _ (by decide), t12]
    · rw [x₅.gpr _ (by decide), x₄.gpr _ (by decide), x₃.gpr _ (by decide), k₂.gpr _ (by simp), k₁.gpr _ (by decide), t8]
    · rw [f₅, x₄.gpr _ (by decide), x₃.gpr _ (by decide), k₂.gpr _ (by simp), k₁.gpr _ (by decide)]
  refine WP.mono (copyTail_ok ht t31 t12 (by rw [tk.gpr _ (by decide), h11]) hK hK' hlay hS) fun u ⟨⟨eu, ou, u8, u9, u10, u22, u7⟩, ku⟩ =>
    ⟨⟨?_, ?_, u8, u9, u10, ?_, by rw [u7, tk.gpr _ (by decide)]⟩, (tk.trans ku).mono (by decide)⟩
  · rw [wordsVal_succ_top, ou.wordsVal (Or.inl (by omega_using [])) (by omega_using [hS, hnw]), te, eu, t8]
  · exact (to.mono (Nat.le_refl _) (by omega_using [])).trans (ou.mono (by omega_using []) (by omega_using []))
  · rw [u22, ou.word (Or.inr (by omega_using [])) (by omega_using [hS, hnw]), to.word (Or.inr (by omega_using [])) (by omega_using [hS, hnw])]

/-! ## The squaring -/

theorem sqs_out {m m' : Mem} {B : Addr} {dS L da : Nat} (o : Outside B dS L m m') : ∀ n,
    (da + 8 * n ≤ dS ∨ dS + L ≤ da) → da + 8 * n ≤ 2 ^ 64 → sqs m' B da n = sqs m B da n
  | 0, _, _ => rfl
  | n + 1, h1, h2 => by
    rw [sqs, sqs, sqs_out o n (by omega_using [h1]) (by omega_using [h2]), o.word (by omega_using [h1]) (by omega_using [h2])]

theorem sqr_final {W T A M U : Nat} (e : W * T = A * A + M * U) (hA : A < M) (hM : M < W) (hU : U < W) :
    T < 2 * M ∧ W * T % M = A * A % M := by
  refine ⟨?_, by rw [e, Nat.add_mul_mod_self_left]⟩
  have h1 : A * A < M * W :=
    Nat.lt_of_lt_of_le (Nat.mul_self_lt_mul_self hA) (Nat.mul_le_mul_left M (Nat.le_of_lt hM))
  have h2 : M * U < M * W := Nat.mul_lt_mul_of_pos_left hU (by omega_using [hA])
  by_contra h
  have := Nat.mul_le_mul_left W (Nat.le_of_not_lt h)
  rw [show W * (2 * M) = 2 * (M * W) by rw [Nat.mul_comm W, Nat.mul_assoc]] at this
  omega_using [e, h1, h2, this]

/-- The squaring's first half (`sqrInit`, `sqrTri`, `sqrDbl`): `m'` stored at
`S`'s word `2 w + 1` and `S := a²` in its `2 w + 1` words (`w = 8 K`). -/
theorem sqrSq_ok {s : State} {B : Addr} {Z da dS dM K : Nat} (hs : Scr s B Z) (h6 : s.gpr .r6 = off B da)
    (h8 : s.gpr .r8 = off B dS) (h10 : s.gpr .r10 = off B dM) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * (8 * K)))
    (hK : 1 ≤ K) (hK' : K < 2 ^ 28) (ha : da + 64 * K ≤ Z) (hS : dS + 8 * (16 * K + 2) ≤ Z) (hM : dM + 8 ≤ Z)
    (hsep : da + 64 * K ≤ dS ∨ dS + 8 * (16 * K + 2) ≤ da) :
    WP isa (.seq sqrInit (.seq sqrTri sqrDbl)) s fun t =>
      (wordsVal t.mem B dS (16 * K + 1) = wordsVal s.mem B da (8 * K) * wordsVal s.mem B da (8 * K) ∧
        word t.mem B (dS + 8 * (16 * K + 1)) = (word s.mem B dM * s.gpr .r12 + BitVec.ofNat 64 2) * s.gpr .r12 ∧
        Outside B dS (8 * (16 * K + 2)) s.mem t.mem ∧ t.gpr .r0 = 0 ∧ t.gpr .r10 = off B dS ∧
        t.gpr .r6 = off B da) ∧
      Keep (.r0 :: .r3 :: .r31 :: triRegs ++ ([.r12, .r7, .r9, .r3, .r30] : List Reg)) s t := by
  have hnw := hs.nowrap
  refine WP.seq (WP.mono (sqrInit_ok hs h10 h8 h11 hK hK' hM hS) fun t₁ ⟨⟨z₁, m₁, o₁, r0₁⟩, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.wr
  refine WP.seq (WP.mono (sqrTri_ok hs₁ r0₁ (by rw [k₁.gpr _ (by decide), h6]) (by rw [k₁.gpr _ (by decide), h8])
    (by rw [k₁.gpr _ (by decide), h11]) hK hK' ha (by omega_using [hS]) (by omega_using [hsep]) z₁)
    fun t₂ ⟨⟨e₂, o₂, r6₂, r10₂, r0₂⟩, k₂⟩ => ?_)
  have hs₂ := hs₁.congr k₂.wr
  have wa : ∀ {m m' : Mem} {L : Nat}, Outside B dS L m m' → dS + L ≤ dS + 8 * (16 * K + 2) →
      wordsVal m' B da (8 * K) = wordsVal m B da (8 * K) := fun o hL => o.wordsVal (by omega_using [hsep, hL]) (by omega_using [ha, hnw])
  have tot := triS_total t₁.mem B da K
  rw [← e₂, sqs_out o₂ (8 * K) (by omega_using [hsep]) (by omega_using [ha, hnw]) |>.symm, ← wa o₂ (by omega_using [])] at tot
  refine WP.mono (sqrDbl_ok (w := 8 * K) hs₂ r0₂ r6₂ r10₂ (by rw [k₂.gpr _ (by decide), k₁.gpr _ (by decide), h11]) (by omega_using [hK])
    (by omega_using [hK']) (by omega_using [ha]) (by omega_using [hS]) (by omega_using [hsep]) (by rw [show 2 * (8 * K) + 1 = 16 * K + 1 by omega_using []]; exact tot))
    fun t ⟨⟨e₃, o₃⟩, k₃⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, by rw [k₃.gpr _ (by decide), r6₂]⟩, ?_⟩
  · rw [show 16 * K + 1 = 2 * (8 * K) + 1 by omega_using [], e₃, wa o₂ (by omega_using []), wa o₁ (by omega_using [])]
  · rw [o₃.word (Or.inr (by omega_using [])) (by omega_using [hS, hnw]), o₂.word (Or.inr (by omega_using [])) (by omega_using [hS, hnw]), m₁]
  · exact (o₁.trans (o₂.mono (Nat.le_refl _) (by omega_using []))).trans (o₃.mono (Nat.le_refl _) (by omega_using []))
  · rw [k₃.gpr _ (by decide), r0₂]
  · rw [k₃.gpr _ (by decide), r10₂]
  · exact ((k₁.trans k₂).trans k₃).mono (by decide)

/-- The registers the squaring writes. -/
abbrev sqrRegs : List Reg := .r0 :: .r3 :: .r31 :: .r22 :: triRegs ++ redRegs

/-- The squaring (`sqr8`), `a` at `da`, `T` and `S` at `dS` (`2 w + 2` words
there, `w = 8 K`), `m` at `dM = dS - 16 (w + 2)`: `T < 2 m` and `2^(64 w) T ≡
a² (mod m)` in `T`'s `w + 1` words, as the rounds leave them, and `m'`
(`y (2 + m₀ y)`, from `y` in `r12`) in `r22`. -/
theorem sqr8_ok {s : State} {B : Addr} {Z da dS dM K : Nat} (hs : Scr s B Z) (h6 : s.gpr .r6 = off B da)
    (h8 : s.gpr .r8 = off B dS) (h10 : s.gpr .r10 = off B dM) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * (8 * K)))
    (hK : 1 ≤ K) (hK' : K < 2 ^ 28) (hlay : dS = dM + 16 * (8 * K + 2)) (ha : da + 64 * K ≤ Z)
    (hS : dS + 8 * (16 * K + 2) ≤ Z) (hsep : da + 64 * K ≤ dS ∨ dS + 8 * (16 * K + 2) ≤ da)
    (hm : ((word s.mem B dM).toNat * ((word s.mem B dM * s.gpr .r12 + BitVec.ofNat 64 2) * s.gpr .r12).toNat + 1) %
      2 ^ 64 = 0)
    (hB : wordsVal s.mem B da (8 * K) < wordsVal s.mem B dM (8 * K)) :
    WP isa sqr8 s fun t =>
      (wordsVal t.mem B dS (8 * K + 1) < 2 * wordsVal s.mem B dM (8 * K) ∧
        2 ^ (64 * (8 * K)) * wordsVal t.mem B dS (8 * K + 1) % wordsVal s.mem B dM (8 * K) =
          wordsVal s.mem B da (8 * K) * wordsVal s.mem B da (8 * K) % wordsVal s.mem B dM (8 * K) ∧
        Outside B dS (8 * (16 * K + 2)) s.mem t.mem ∧
        t.gpr .r22 = (word s.mem B dM * s.gpr .r12 + BitVec.ofNat 64 2) * s.gpr .r12 ∧
        t.gpr .r8 = s.gpr .r8 ∧ t.gpr .r9 = off B (dS + 8 * (8 * K + 2)) ∧ t.gpr .r10 = s.gpr .r10 ∧
        t.gpr .r7 = s.gpr .r6) ∧ Keep sqrRegs s t := by
  have hnw := hs.nowrap
  have H := sqrSq_ok hs h6 h8 h10 h11 hK hK' ha hS (by omega_using [hlay, hS]) hsep
  unfold sqr8
  rw [WP.seq_iff] at H ⊢
  refine WP.mono H fun t₁ h₁ => ?_
  rw [WP.seq_iff] at h₁ ⊢
  refine WP.mono h₁ fun t₂ h₂ => ?_
  rw [WP.seq_iff]
  refine WP.mono h₂ fun t₃ ⟨⟨e₃, m₃, o₃, z₃, r10₃, r6₃⟩, k₃⟩ => ?_
  have hs₃ := hs.congr k₃.wr
  have wM : ∀ {m m' : Mem} {o L : Nat}, Outside B o L m m' → dS ≤ o → wordsVal m' B dM (8 * K) = wordsVal m B dM (8 * K) :=
    fun ot ho => ot.wordsVal (Or.inl (by omega_using [hlay, ho])) (by omega_using [hlay, hS, hnw])
  have wA : ∀ {m m' : Mem} {o L : Nat}, Outside B o L m m' → dS ≤ o → o + L ≤ dS + 8 * (16 * K + 2) →
      wordsVal m' B da (8 * K) = wordsVal m B da (8 * K) := fun ot h1 h2 => ot.wordsVal (by omega_using [hsep, h1, h2]) (by omega_using [ha, hnw])
  refine WP.seq (WP.mono (sqrRed_ok hs₃ z₃ r10₃ (by rw [k₃.gpr _ (by decide), h11]) hK hK' hlay (by omega_using [hS])
    (by rw [o₃.word (Or.inl (by omega_using [hlay])) (by omega), show dM + 32 * (8 * K) + 40 = dS + 8 * (16 * K + 1) by omega_using [hlay], m₃]
        exact hm)) fun t₄ ⟨⟨e₄, o₄, r10₄, _⟩, k₄⟩ => ?_)
  have hs₄ := hs₃.congr k₄.wr
  refine WP.mono (sqrCopy_ok (dM := dM) hs₄ r10₄ (by rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide), h11]) hK hK' hlay hS)
    fun t ⟨⟨e₅, o₅, r8₅, r9₅, r10₅, r22₅, r7₅⟩, k₅⟩ => ?_
  have M₄ : wordsVal t₄.mem B dM (8 * K) = wordsVal s.mem B dM (8 * K) := by
    rw [wM o₄ (Nat.le_refl _), wM o₃ (Nat.le_refl _)]
  have A₃ : wordsVal t₃.mem B da (8 * K) = wordsVal s.mem B da (8 * K) := wA o₃ (Nat.le_refl _) (Nat.le_refl _)
  have fin : 2 ^ (64 * (8 * K)) * wordsVal t.mem B dS (8 * K + 1) =
      wordsVal s.mem B da (8 * K) * wordsVal s.mem B da (8 * K) +
        wordsVal s.mem B dM (8 * K) * wordsVal t₄.mem B dS (8 * K) := by
    have hA := wordsVal_lt s.mem B da (8 * K)
    have hWW : 2 ^ (64 * (16 * K)) = 2 ^ (64 * (8 * K)) * 2 ^ (64 * (8 * K)) := by
      rw [← Nat.pow_add, show 64 * (8 * K) + 64 * (8 * K) = 64 * (16 * K) by omega_using []]
    have AA : wordsVal s.mem B da (8 * K) * wordsVal s.mem B da (8 * K) < 2 ^ (64 * (16 * K)) := by
      rw [hWW]; exact Nat.mul_lt_mul'' hA hA
    have s3 := wordsVal_succ_top t₃.mem B dS (16 * K)
    rw [e₃] at s3
    have z : (word t₃.mem B (dS + 8 * (16 * K))).toNat = 0 := mul_lt_self_zero (Q := 2 ^ (64 * (16 * K))) (by omega_using [AA, s3])
    rw [z, Nat.mul_zero, Nat.add_zero] at s3
    have sp := fios_wordsVal_append t₄.mem B dS (8 * K) (8 * K)
    rw [show 8 * K + 8 * K = 16 * K by omega_using []] at sp
    rw [← s3, sp, wM o₃ (Nat.le_refl _), hWW] at e₄
    rw [e₅]
    have := Nat.mul_lt_mul'' hA hA
    grind
  refine ⟨⟨?_, ?_, ?_, ?_, by rw [r8₅, h8], r9₅, by rw [r10₅, h10],
      by rw [r7₅, k₄.gpr _ (by decide), r6₃, h6]⟩, ((k₃.trans k₄).trans k₅).mono (by decide)⟩
  · exact (sqr_final fin hB (wordsVal_lt _ _ _ _) (wordsVal_lt _ _ _ _)).1
  · exact (sqr_final fin hB (wordsVal_lt _ _ _ _) (wordsVal_lt _ _ _ _)).2
  · exact (o₃.trans (o₄.mono (Nat.le_refl _) (by omega_using []))).trans (o₅.mono (Nat.le_refl _) (by omega_using []))
  · rw [r22₅, o₄.word (Or.inr (by omega_using [])) (by omega_using [hS, hnw]), m₃]

/-! ## The squaring's condition -/

theorem or_zero {x y : BitVec 64} (h : x ||| y = 0) : x = 0 ∧ y = 0 := BitVec.or_eq_zero_iff.mp h

/-- The squaring's condition (`sqrFlag`): `r3 = 0` only if `a` and `b` are the
same array (`r6 = r7`), `w` is a multiple of 8 and `a` is not the temporary
(`r6 ≠ r9`). -/
theorem sqrFlag_ok {s : State} {w : Nat} (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) :
    WP isa (.block sqrFlag) s fun t =>
      (t.gpr .r3 = 0 → s.gpr .r6 = s.gpr .r7 ∧ w % 8 = 0 ∧ s.gpr .r6 ≠ s.gpr .r9) ∧ t.mem = s.mem ∧
        t.gpr .r0 = 0 ∧ Keep [.r0, .r3, .r4, .r30] s t := by
  unfold sqrFlag
  refine wp_write (exec_li (by decide)) fun u₀ w₀ f₀ _ => ?_
  refine wp_write exec_sub fun u₁ w₁ f₁ _ => ?_
  refine wp_write (exec_lsl (by decide)) fun u₂ w₂ f₂ _ => ?_
  refine wp_write (exec_lsr_d (by decide)) fun u₃ w₃ f₃ _ => ?_
  refine wp_write exec_logic fun u₄ w₄ f₄ _ => ?_
  refine wp_write exec_sub fun u₅ w₅ f₅ _ => ?_
  refine wp_write exec_sub fun u₆ w₆ f₆ _ => ?_
  refine wp_write exec_logic fun u₇ w₇ f₇ _ => ?_
  refine wp_write (exec_lsr_d (by decide)) fun u₈ w₈ f₈ _ => ?_
  refine wp_write (exec_li (by decide)) fun u₉ w₉ f₉ _ => ?_
  refine wp_write exec_sub fun u₁₀ w₁₀ f₁₀ _ => ?_
  refine wp_write exec_logic fun t w₁₁ f₁₁ _ => WP.block_nil ⟨fun h3 => ?_, ?_, ?_, ?_⟩
  · rw [f₁₁] at h3
    simp only at h3
    obtain ⟨a3, a4⟩ := or_zero h3
    rw [w₁₀.gpr _ (by decide), w₉.gpr _ (by decide), w₈.gpr _ (by decide), w₇.gpr _ (by decide),
      w₆.gpr _ (by decide), w₅.gpr _ (by decide), f₄] at a3
    simp only at a3
    obtain ⟨b1, b2⟩ := or_zero a3
    rw [w₃.gpr _ (by decide), w₂.gpr _ (by decide), f₁, w₀.gpr _ (by decide), w₀.gpr _ (by decide)] at b1
    rw [f₃, f₂, w₁.gpr _ (by decide), w₀.gpr _ (by decide), h11] at b2
    refine ⟨?_, ?_, fun e => ?_⟩
    · have := congrArg BitVec.toNat b1
      rw [BitVec.toNat_sub, show (0 : BitVec 64).toNat = 0 from rfl] at this
      have := (s.gpr .r6).isLt; have := (s.gpr .r7).isLt
      apply BitVec.eq_of_toNat_eq
      omega_arith
    · have := congrArg BitVec.toNat b2
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
        Nat.shiftRight_eq_div_pow] at this
      rw [show (0 : BitVec 64).toNat = 0 from rfl, show (2 : Nat) ^ 64 = 16 * 2 ^ 60 from rfl, Nat.mul_mod_mul_right,
        Nat.mul_div_cancel _ (Nat.two_pow_pos 60)] at this
      omega_using [this]
    · -- `a` is the temporary: `x = 0`, so `r4 = 1 - 0`.
      have x0 : u₅.gpr .r4 = 0 := by
        rw [f₅, w₄.gpr .r6 (by decide), w₃.gpr .r6 (by decide), w₂.gpr .r6 (by decide), w₁.gpr .r6 (by decide),
          w₀.gpr .r6 (by decide), w₄.gpr .r9 (by decide), w₃.gpr .r9 (by decide), w₂.gpr .r9 (by decide),
          w₁.gpr .r9 (by decide), w₀.gpr .r9 (by decide), e, BitVec.sub_self]; rfl
      have z7 : u₇.gpr .r4 = 0 := by
        rw [f₇]
        simp only
        rw [w₆.gpr .r4 (by decide), x0, f₆, w₅.gpr .r0 (by decide), x0, w₄.gpr .r0 (by decide), w₃.gpr .r0 (by decide),
          w₂.gpr .r0 (by decide), w₁.gpr .r0 (by decide), f₀]
        rfl
      rw [f₁₀, w₉.gpr .r4 (by decide), f₈, z7, f₉] at a4
      exact absurd a4 (by decide)
  · rw [w₁₁.mem, w₁₀.mem, w₉.mem, w₈.mem, w₇.mem, w₆.mem, w₅.mem, w₄.mem, w₃.mem, w₂.mem, w₁.mem, w₀.mem]
  · rw [w₁₁.gpr _ (by decide), w₁₀.gpr _ (by decide), w₉.gpr _ (by decide), w₈.gpr _ (by decide), w₇.gpr _ (by decide),
      w₆.gpr _ (by decide), w₅.gpr _ (by decide), w₄.gpr _ (by decide), w₃.gpr _ (by decide), w₂.gpr _ (by decide),
      w₁.gpr _ (by decide), f₀]; rfl
  · exact ((((((((((w₀.keep.trans w₁.keep).trans w₂.keep).trans w₃.keep).trans w₄.keep).trans w₅.keep).trans
      w₆.keep).trans w₇.keep).trans w₈.keep).trans w₉.keep).trans w₁₀.keep |>.trans w₁₁.keep).mono (by decide)

end VG.Proof.Bignum.PPC64LE.Sqr
