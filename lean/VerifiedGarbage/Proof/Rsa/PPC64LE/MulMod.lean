module

public import VerifiedGarbage.Impl.Rsa.PPC64LE.MulMod
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyOps
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyBits
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyHalf
import VerifiedGarbage.Proof.Rsa.PPC64LE.InvParts
import VerifiedGarbage.Proof.Rsa.MulModArithmetic
import VerifiedGarbage.Proof.Framework.Block

/-! # `mulMod` on PPC64LE: `[a] = ([a] + ([y] mod 2^k) [x]) mod [m]`

As on ARMv7 (`Proof/Rsa/Arm/MulMod.lean`). `addMod_ok`: `[o] = ([a] + [b])
mod [m]` for `[a], [b] < [m]`, `2 [m] ≤ 2^(32 w)` and `[z] = 0`.
`mulMod_ok`: `k = r4` steps of `mulModStep`, each adding the selected `[x]`
to `[a]` and doubling `[x]` modulo `[m]`, and halving `[y]`. From `[a], [x] <
[m]` with `2 [m] ≤ 2^(32 w)` and `[z] = 0`, `[a]` ends as
`([a] + ([y] mod 2^k) [x]) mod [m]`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Keys

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Rsa.PPC64LE.Keys (seqs addMod mulHead mulTail mulModStep mulMod sB sC)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

theorem addMod_ok {s : State} {B : Addr} {Z w N o a b m z t : Nat} (h : Ws s B Z w N)
    (hN : N ≤ 256) (ho : o < N) (ha : a < N) (hb : b < N) (hm : m < N) (hz : z < N) (ht : t + 2 < N)
    (htz : t ≠ z) (htb : t ≠ b) (hat : a ≠ t) (hat1 : a ≠ t + 1) (hmt : m ≠ t) (hmt1 : m ≠ t + 1)
    (hmt2 : m ≠ t + 2) (hot1 : o ≠ t + 1) (hot2 : o ≠ t + 2) :
    WP isa (seqs (addMod o a b m z t)) s fun u => Ws u B Z w N ∧
      KeyWorkspace.Keep B w [t, t + 1, t + 2, o] [sC] s.mem u.mem ∧ Keep opRegs s u ∧
      (num s.mem B w z = 0 → num s.mem B w a < num s.mem B w m → num s.mem B w b < num s.mem B w m →
        2 * num s.mem B w m ≤ 2 ^ (32 * w) →
        num u.mem B w o = (num s.mem B w a + num s.mem B w b) % num s.mem B w m) := by
  unfold addMod
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h (o := t) (a := z) (b := b) (by omega) hz hb hN htz htb)
    fun t1 ⟨h1, k1, v1, b1, r1⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h1 (o := t + 1) (a := a) (b := t) (by omega) ha (by omega) hN (Ne.symm hat1)
    (by omega)) fun t2 ⟨h2, k2, v2, b2, r2⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h2 (o := t + 2) (a := t + 1) (b := m) ht (by omega) hm hN (by omega)
    (Ne.symm hmt2)) fun t3 ⟨h3, k3, v3, b3, r3⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _), ← List.append_nil (VG.Impl.Rsa.PPC64LE.Keys.stBorrow sC)]
  refine stBorrow_ok h3 (by decide) b3 fun t4 h4 k4 s4 r4 => WP.block_nil ?_
  rw [show seqs [VG.Impl.Rsa.PPC64LE.Keys.sel o (t + 2) (t + 1) sC] =
    VG.Impl.Rsa.PPC64LE.Keys.sel o (t + 2) (t + 1) sC from rfl]
  refine WP.mono (sel_ok h4 (o := o) (a := t + 2) (b := t + 1) (sl := sC) ho ht (by omega) hN hot2 hot1
    (by decide) (by rw [s4]; exact b3)) fun u ⟨hu, k5, v5, r5⟩ => ?_
  refine ⟨hu, ((k1.mono.trans k2.mono).trans k3.mono).trans (k4.mono.trans k5.mono),
    (r1.trans (r2.trans (r3.trans (r4.trans r5)))).mono, fun hZ hA hB hM => ?_⟩
  have fa := h.fit64 ha
  have fm := h.fit64 hm
  have ft1 := h.fit64 (j := t + 1) (by omega)
  have ft2 := h.fit64 (j := t + 2) (by omega)
  -- The values the later steps read.
  have a1 : num t1.mem B w a = num s.mem B w a := k1.num (by simp; omega) (by simp) fa
  have m2 : num t2.mem B w m = num s.mem B w m := by
    rw [k2.num (by simp; omega) (by simp) fm, k1.num (by simp; omega) (by simp) fm]
  have T3 : num t3.mem B w (t + 1) = num t2.mem B w (t + 1) := k3.num (by simp) (by simp) ft1
  have T4 : num t4.mem B w (t + 1) = num t2.mem B w (t + 1) := by
    rw [k4.num (by simp) (by simp; decide) ft1, T3]
  have U4 : num t4.mem B w (t + 2) = num t3.mem B w (t + 2) := k4.num (by simp) (by simp; decide) ft2
  rw [v5, s4, T4, U4]
  rw [hZ] at v1
  rw [a1] at v2
  rw [m2] at v3
  have e := VG.Proof.Rsa.addMod_impl hA hB hM (by rw [Nat.add_comm] at v1; omega) (val32_lt _ _ _ _) b1
    (by omega) (val32_lt _ _ _ _) b2 (by omega) (val32_lt _ _ _ _) b3
  exact e

/-- `mulHead`: `[t]` is `[x]` if `[y]` is odd, `[z]` if not. -/
theorem mulHead_ok {s : State} {B : Addr} {Z w N z y x t : Nat} (h : Ws s B Z w N)
    (hN : N ≤ 256) (ht : t < N) (hz : z < N) (hy : y < N) (hx : x < N) (htz : t ≠ z) (htx : t ≠ x) :
    WP isa (mulHead z y x t) s fun u => Ws u B Z w N ∧ KeyWorkspace.Keep B w [t] [sB] s.mem u.mem ∧
      Keep opRegs s u ∧
      num u.mem B w t = (if num s.mem B w y % 2 = 0 then num s.mem B w z else num s.mem B w x) := by
  rw [mulHead, WP.seq_iff, ← List.append_nil (VG.Impl.Rsa.PPC64LE.Keys.bitOf sB y)]
  refine bitOf_ok h hy hN (by decide) fun t1 h1 k1 e1 r1 => WP.block_nil ?_
  refine WP.mono (sel_ok h1 (o := t) (a := z) (b := x) (sl := sB) ht hz hx hN htz htx (by decide)
    (by rw [e1]; omega)) fun u ⟨hu, k2, e2, r2⟩ => ⟨hu, k1.mono.trans k2.mono, (r1.trans r2).mono, ?_⟩
  rw [e2, e1, k1.num (by simp) (by simp; decide) (h.fit64 hz), k1.num (by simp) (by simp; decide) (h.fit64 hx)]

/-- `mulTail`: `[y]` halved, `r4` decremented. -/
theorem mulTail_ok {s : State} {B : Addr} {Z w N y : Nat} (h : Ws s B Z w N) (hN : N ≤ 256) (hy : y < N) :
    WP isa (mulTail y) s fun u => Ws u B Z w N ∧ KeyWorkspace.Keep B w [y] [] s.mem u.mem ∧
      Keep (.r4 :: opRegs) s u ∧ u.gpr .r4 = s.gpr .r4 - BitVec.ofNat 64 1 ∧
      num u.mem B w y = num s.mem B w y / 2 := by
  rw [mulTail, wp_seqs_cons (List.cons_ne_nil _ _)]
  have b0 : WP isa (.block [.li .r9 0]) s fun u => (u.gpr .r9 = 0 ∧ u.mem = s.mem) ∧ Keep [.r9] s u := by
    refine WP.keep _ ?_ (by decide)
    prun []
    rfl
  refine WP.mono b0 fun t5 ⟨⟨u9, m5⟩, k5⟩ => ?_
  have h5 := h.of_keep k5
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (half_ok h5 (j := y) hy hN (by rw [u9]; decide)) fun t6 ⟨h6, k6, e6, r6⟩ => ?_
  rw [show seqs [.block [.subi .r4 .r4 1]] = .block [.subi .r4 .r4 1] from rfl]
  have b7 : WP isa (.block [.subi .r4 .r4 1]) t6 fun u =>
      (u.gpr .r4 = t6.gpr .r4 - BitVec.ofNat 64 1 ∧ u.mem = t6.mem) ∧ Keep [.r4] t6 u := by
    refine WP.keep _ ?_ (by decide)
    prun []
  refine WP.mono b7 fun u ⟨⟨u4, m7⟩, k7⟩ => ?_
  have r4eq : t6.gpr .r4 = s.gpr .r4 := by rw [r6.gpr _ (by decide), k5.gpr _ (by decide)]
  rw [u9, m5] at e6
  rw [m5] at k6
  refine ⟨h6.of_keep k7, by rw [m7]; exact k6, ((k5.trans r6).trans k7).mono, by rw [u4, r4eq], ?_⟩
  rw [m7, e6, show (0 : BitVec 64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]

/-- The arrays of `mulMod z y x a m t`: each below `N`, `t` above the
others, which are distinct. -/
abbrev MulIdx (N z y x a m t : Nat) : Prop :=
  t + 3 < N ∧ z < t ∧ y < t ∧ x < t ∧ a < t ∧ m < t ∧ z ≠ y ∧ z ≠ x ∧ z ≠ a ∧ z ≠ m ∧ y ≠ x ∧ y ≠ a ∧
    y ≠ m ∧ x ≠ a ∧ x ≠ m ∧ a ≠ m

/-- The arrays `mulMod` writes. -/
abbrev mulArrs (y x a t : Nat) : List Nat := [y, x, a, t, t + 1, t + 2, t + 3]

/-- One step. -/
theorem mulModStep_ok {s : State} {B : Addr} {Z w N z y x a m t : Nat} (h : Ws s B Z w N)
    (hN : N ≤ 256) (hi : MulIdx N z y x a m t) :
    WP isa (mulModStep z y x a m t) s fun u => Ws u B Z w N ∧
      KeyWorkspace.Keep B w (mulArrs y x a t) [sB, sC] s.mem u.mem ∧ Keep (.r4 :: opRegs) s u ∧
      u.gpr .r4 = s.gpr .r4 - BitVec.ofNat 64 1 ∧
      num u.mem B w y = num s.mem B w y / 2 ∧
      (num s.mem B w z = 0 → num s.mem B w a < num s.mem B w m → num s.mem B w x < num s.mem B w m →
        2 * num s.mem B w m ≤ 2 ^ (32 * w) →
        num u.mem B w a = (num s.mem B w a + num s.mem B w y % 2 * num s.mem B w x) % num s.mem B w m ∧
        num u.mem B w x = (num s.mem B w x + num s.mem B w x) % num s.mem B w m) := by
  obtain ⟨ht, hz, hy, hx, ha, hm, hzy, hzx, hza, hzm, hyx, hya, hym, hxa, hxm, ham⟩ := hi
  have zN : z < N := by omega
  have yN : y < N := by omega
  have xN : x < N := by omega
  have aN : a < N := by omega
  have mN : m < N := by omega
  have tN : t < N := by omega
  have t1N : t + 1 + 2 < N := by omega
  -- The arrays each step does not write, while the context is small.
  have nm : ∀ {l : List Nat} {j : Nat}, (∀ k ∈ l, k ≠ j) → ∀ k ∈ l, k ≠ j := fun h => h
  have n2 : ∀ j, j ≠ t → ∀ k ∈ [t], k ≠ j := fun j hj k hk => by
    rw [List.mem_singleton] at hk; subst hk; exact Ne.symm hj
  have n4 : ∀ j o, j ≠ t + 1 → j ≠ t + 1 + 1 → j ≠ t + 1 + 2 → j ≠ o →
      ∀ k ∈ [t + 1, t + 1 + 1, t + 1 + 2, o], k ≠ j := fun j o h1 h2 h3 h4 k hk => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> exact Ne.symm (by with_reducible assumption)
  have n1 : ∀ j, j ≠ y → ∀ k ∈ [y], k ≠ j := fun j hj k hk => by
    rw [List.mem_singleton] at hk; subst hk; exact Ne.symm hj
  clear nm
  have fz := h.fit64 zN
  have fy := h.fit64 yN
  have fx := h.fit64 xN
  have fa := h.fit64 aN
  have fm := h.fit64 mN
  rw [mulModStep, wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (mulHead_ok h hN tN zN yN xN (by omega) (by omega)) fun t2 ⟨h2, k2, r2, e2⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (addMod_ok h2 (o := a) (a := a) (b := t) (m := m) (z := z) (t := t + 1) hN aN aN tN mN zN t1N
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
    fun t3 ⟨h3, k3, r3, e3⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (addMod_ok h3 (o := x) (a := x) (b := x) (m := m) (z := z) (t := t + 1) hN xN xN xN mN zN t1N
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
    fun t4 ⟨h4, k4, r4, e4⟩ => ?_
  rw [show seqs [mulTail y] = mulTail y from rfl]
  refine WP.mono (mulTail_ok h4 hN yN) fun u ⟨hu, k6, r6, c6, e6⟩ => ?_
  have r4eq : t4.gpr .r4 = s.gpr .r4 := by
    rw [r4.gpr _ (by decide), r3.gpr _ (by decide), r2.gpr _ (by decide)]
  refine ⟨hu, ((k2.mono.trans k3.mono).trans k4.mono).trans k6.mono,
    (((r2.trans r3).trans r4).trans r6).mono, by rw [c6, r4eq], ?_, fun hZ hA hX hM => ?_⟩
  · rw [e6, k4.num (n4 y x (by omega) (by omega) (by omega) hyx) (by simp; decide) fy,
      k3.num (n4 y a (by omega) (by omega) (by omega) hya) (by simp; decide) fy,
      k2.num (n2 y (by omega)) (by simp; decide) fy]
  · -- The values each step reads.
    have z2 : num t2.mem B w z = 0 := by rw [k2.num (n2 z (by omega)) (by simp; decide) fz, hZ]
    have mm2 : num t2.mem B w m = num s.mem B w m := k2.num (n2 m (by omega)) (by simp; decide) fm
    have a2 : num t2.mem B w a = num s.mem B w a := k2.num (n2 a (by omega)) (by simp; decide) fa
    have x2 : num t2.mem B w x = num s.mem B w x := k2.num (n2 x (by omega)) (by simp; decide) fx
    have d2 : num t2.mem B w t = num s.mem B w y % 2 * num s.mem B w x := by
      rw [e2, hZ]
      rcases Nat.mod_two_eq_zero_or_one (num s.mem B w y) with e | e <;> simp [e]
    have dlt : num t2.mem B w t < num s.mem B w m := by
      rw [d2]; rcases Nat.mod_two_eq_zero_or_one (num s.mem B w y) with e | e <;> simp [e] <;> omega
    have A3 := e3 z2 (by rw [a2, mm2]; exact hA) (by rw [mm2]; exact dlt) (by rw [mm2]; exact hM)
    rw [a2, mm2, d2] at A3
    have z3 : num t3.mem B w z = 0 := by rw [k3.num (n4 z a (by omega) (by omega) (by omega) hza) (by simp; decide) fz, z2]
    have mm3 : num t3.mem B w m = num s.mem B w m := by
      rw [k3.num (n4 m a (by omega) (by omega) (by omega) (Ne.symm ham)) (by simp; decide) fm, mm2]
    have x3 : num t3.mem B w x = num s.mem B w x := by
      rw [k3.num (n4 x a (by omega) (by omega) (by omega) hxa) (by simp; decide) fx, x2]
    have X4 := e4 z3 (by rw [x3, mm3]; exact hX) (by rw [x3, mm3]; exact hX) (by rw [mm3]; exact hM)
    rw [x3, mm3] at X4
    refine ⟨?_, ?_⟩
    · rw [k6.num (n1 a (Ne.symm hya)) (by simp) fa,
        k4.num (n4 a x (by omega) (by omega) (by omega) (Ne.symm hxa)) (by simp; decide) fa, A3]
    · rw [k6.num (n1 x (Ne.symm hyx)) (by simp) fx, X4]

/-- The state after `i` of the `k` steps. -/
structure MulI (s0 : State) (B : Addr) (Z w N z y x a m t : Nat) (i : Nat) (u : State) : Prop where
  ws : Ws u B Z w N
  keep : KeyWorkspace.Keep B w (mulArrs y x a t) [sB, sC] s0.mem u.mem
  regs : Keep (.r4 :: opRegs) s0 u
  yv : num u.mem B w y = num s0.mem B w y / 2 ^ i
  value : num s0.mem B w z = 0 → num s0.mem B w a < num s0.mem B w m → num s0.mem B w x < num s0.mem B w m →
    2 * num s0.mem B w m ≤ 2 ^ (32 * w) →
    num u.mem B w a = (num s0.mem B w a + num s0.mem B w y % 2 ^ i * num s0.mem B w x) % num s0.mem B w m ∧
    num u.mem B w x = 2 ^ i * num s0.mem B w x % num s0.mem B w m

theorem mulModBody_ok {s0 u : State} {B : Addr} {Z w N z y x a m t i : Nat} (hN : N ≤ 256)
    (hi : MulIdx N z y x a m t) (inv : MulI s0 B Z w N z y x a m t i u) :
    WP isa (mulModStep z y x a m t) u fun u' =>
      MulI s0 B Z w N z y x a m t (i + 1) u' ∧ u'.gpr .r4 = u.gpr .r4 - BitVec.ofNat 64 1 := by
  have h := inv.ws
  have hi' := hi
  obtain ⟨ht, hz, hy, hx, ha, hm, hzy, hzx, hza, hzm, hyx, hya, hym, hxa, hxm, ham⟩ := hi'
  have fz := h.fit64 (j := z) (by omega)
  have fm := h.fit64 (j := m) (by omega)
  have zk : num u.mem B w z = num s0.mem B w z := inv.keep.num (by simp; omega) (by simp; decide) fz
  have mk : num u.mem B w m = num s0.mem B w m := inv.keep.num (by simp; omega) (by simp; decide) fm
  refine WP.mono (mulModStep_ok h hN hi) fun u' ⟨h', k', r', c', y', v'⟩ => ?_
  refine ⟨⟨h', inv.keep.trans k', (inv.regs.trans r').mono, ?_, fun hZ hA hX hM => ?_⟩, c'⟩
  · rw [y', inv.yv, Nat.div_div_eq_div_mul, Nat.pow_succ]
  · obtain ⟨va, vx⟩ := inv.value hZ hA hX hM
    have M0 : 0 < num s0.mem B w m := by omega
    have aLt : num u.mem B w a < num u.mem B w m := by rw [va, mk]; exact Nat.mod_lt _ M0
    have xLt : num u.mem B w x < num u.mem B w m := by rw [vx, mk]; exact Nat.mod_lt _ M0
    obtain ⟨va', vx'⟩ := v' (by rw [zk, hZ]) aLt xLt (by rw [mk]; exact hM)
    rw [va', vx', va, vx, inv.yv, mk]
    exact ⟨VG.Proof.Rsa.mulMod_arith, VG.Proof.Rsa.double_arith⟩

/-- `mulMod z y x a m t` with `r4 = k > 0`. -/
theorem mulMod_ok {s : State} {B : Addr} {Z w N z y x a m t k : Nat} (h : Ws s B Z w N)
    (hN : N ≤ 256) (hi : MulIdx N z y x a m t) (hk : 0 < k) (hk' : k < 2 ^ 64)
    (c : s.gpr .r4 = BitVec.ofNat 64 k) :
    WP isa (mulMod z y x a m t) s fun u => Ws u B Z w N ∧
      KeyWorkspace.Keep B w (mulArrs y x a t) [sB, sC] s.mem u.mem ∧ Keep (.r4 :: opRegs) s u ∧
      (num s.mem B w z = 0 → num s.mem B w a < num s.mem B w m → num s.mem B w x < num s.mem B w m →
        2 * num s.mem B w m ≤ 2 ^ (32 * w) →
        num u.mem B w a = (num s.mem B w a + num s.mem B w y % 2 ^ k * num s.mem B w x) % num s.mem B w m) := by
  have start : MulI s B Z w N z y x a m t 0 s :=
    ⟨h, KeyWorkspace.Keep.refl _ _ _ _ _, Keep.refl _ _, by rw [Nat.pow_zero, Nat.div_one],
      fun _ hA hX _ => ⟨by rw [Nat.pow_zero, Nat.mod_one, Nat.zero_mul, Nat.add_zero, Nat.mod_eq_of_lt hA],
        by rw [Nat.pow_zero, Nat.one_mul, Nat.mod_eq_of_lt hX]⟩⟩
  refine WP.mono (wp_countdown (body := mulModStep z y x a m t) (cnt := .r4) (N := k) hk' hk
    (MulI s B Z w N z y x a m t) (fun i _ u inv _ => mulModBody_ok hN hi inv) start c)
    fun u inv => ⟨inv.ws, inv.keep, inv.regs, fun hZ hA hX hM => (inv.value hZ hA hX hM).1⟩

end VG.Proof.Rsa.PPC64LE.Keys
