module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.KcFrame
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyWs
public import VerifiedGarbage.Proof.Rsa.KeyArrays
public import VerifiedGarbage.Spec.Rsa
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyHalf
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyOps
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvMid
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvLoads
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvBytes
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Rsa.PPC64LE.Seqs
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvStores
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KcMath
public import VerifiedGarbage.Impl.Rsa.PPC64LE.CheckKey
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PubE
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMid
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyBits
import VerifiedGarbage.Proof.Rsa.PPC64LE.DivN
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvArithA
import VerifiedGarbage.Proof.Rsa.InverseArithmetic
public import VerifiedGarbage.Proof.Rsa.KeyCheckMath
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyDiv
import VerifiedGarbage.Proof.Rsa.PPC64LE.IbOps
public import VerifiedGarbage.Proof.Rsa.MontCheckMath
public import VerifiedGarbage.Proof.Rsa.PPC64LE.MontKey
public import VerifiedGarbage.Impl.Rsa.PPC64LE.KeyCheck
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KcContract
public import VerifiedGarbage.Impl.Rsa.PPC64LE.MulMod
import VerifiedGarbage.Proof.Rsa.MulModArithmetic

/-! ### `Rsa.PPC64LE.MulMod`, which only this module used -/

section

/-! # `mulMod` on PPC64LE: `[a] = ([a] + ([y] mod 2^k) [x]) mod [m]`

As on ARMv7 (`Proof/Rsa/Arm/KcOps.lean`). `addMod_ok`: `[o] = ([a] + [b])
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
  refine WP.mono (sub3_ok h (o := t) (a := z) (b := b) (by omega_arith) hz hb hN htz htb)
    fun t1 ⟨h1, k1, v1, b1, r1⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h1 (o := t + 1) (a := a) (b := t) (by omega_arith) ha (by omega_arith) hN (Ne.symm hat1)
    (by omega_arith)) fun t2 ⟨h2, k2, v2, b2, r2⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h2 (o := t + 2) (a := t + 1) (b := m) ht (by omega_arith) hm hN (by omega_arith)
    (Ne.symm hmt2)) fun t3 ⟨h3, k3, v3, b3, r3⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _), ← List.append_nil (VG.Impl.Rsa.PPC64LE.Keys.stBorrow sC)]
  refine stBorrow_ok h3 (by decide) b3 fun t4 h4 k4 s4 r4 => WP.block_nil ?_
  rw [show seqs [VG.Impl.Rsa.PPC64LE.Keys.sel o (t + 2) (t + 1) sC] =
    VG.Impl.Rsa.PPC64LE.Keys.sel o (t + 2) (t + 1) sC from rfl]
  refine WP.mono (sel_ok h4 (o := o) (a := t + 2) (b := t + 1) (sl := sC) ho ht (by omega_arith) hN hot2 hot1
    (by decide) (by rw [s4]; exact b3)) fun u ⟨hu, k5, v5, r5⟩ => ?_
  refine ⟨hu, ((k1.mono.trans k2.mono).trans k3.mono).trans (k4.mono.trans k5.mono),
    (r1.trans (r2.trans (r3.trans (r4.trans r5)))).mono, fun hZ hA hB hM => ?_⟩
  obtain fa := h.fit64 ha
  obtain fm := h.fit64 hm
  obtain ft1 := h.fit64 (j := t + 1) (by omega_arith)
  obtain ft2 := h.fit64 (j := t + 2) (by omega_arith)
  -- The values the later steps read.
  obtain a1 : num t1.mem B w a = num s.mem B w a := k1.num (by simp; omega_arith) (by simp) fa
  obtain m2 : num t2.mem B w m = num s.mem B w m := by
    rw [k2.num (by simp; omega_arith) (by simp) fm, k1.num (by simp; omega_arith) (by simp) fm]
  obtain T3 : num t3.mem B w (t + 1) = num t2.mem B w (t + 1) := k3.num (by simp) (by simp) ft1
  obtain T4 : num t4.mem B w (t + 1) = num t2.mem B w (t + 1) := by
    rw [k4.num (by simp) (by simp; decide) ft1, T3]
  obtain U4 : num t4.mem B w (t + 2) = num t3.mem B w (t + 2) := k4.num (by simp) (by simp; decide) ft2
  rw [v5, s4, T4, U4]
  rw [hZ] at v1
  rw [a1] at v2
  rw [m2] at v3
  obtain e := VG.Proof.Rsa.addMod_impl hA hB hM (by rw [Nat.add_comm] at v1; omega_arith) (val32_lt _ _ _ _) b1
    (by omega_arith) (val32_lt _ _ _ _) b2 (by omega_arith) (val32_lt _ _ _ _) b3
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
    (by rw [e1]; omega_arith)) fun u ⟨hu, k2, e2, r2⟩ => ⟨hu, k1.mono.trans k2.mono, (r1.trans r2).mono, ?_⟩
  rw [e2, e1, k1.num (by simp) (by simp; decide) (h.fit64 hz), k1.num (by simp) (by simp; decide) (h.fit64 hx)]

/-- `mulTail`: `[y]` halved, `r4` decremented. -/
theorem mulTail_ok {s : State} {B : Addr} {Z w N y : Nat} (h : Ws s B Z w N) (hN : N ≤ 256) (hy : y < N) :
    WP isa (mulTail y) s fun u => Ws u B Z w N ∧ KeyWorkspace.Keep B w [y] [] s.mem u.mem ∧
      Keep (.r4 :: opRegs) s u ∧ u.gpr .r4 = s.gpr .r4 - BitVec.ofNat 64 1 ∧
      num u.mem B w y = num s.mem B w y / 2 := by
  rw [mulTail, wp_seqs_cons (List.cons_ne_nil _ _)]
  obtain b0 : WP isa (.block [.li .r9 0]) s fun u => (u.gpr .r9 = 0 ∧ u.mem = s.mem) ∧ Keep [.r9] s u := by
    refine WP.keep _ ?_ (by decide)
    prun []
    rfl
  refine WP.mono b0 fun t5 ⟨⟨u9, m5⟩, k5⟩ => ?_
  obtain h5 := h.of_keep k5
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (half_ok h5 (j := y) hy hN (by rw [u9]; decide)) fun t6 ⟨h6, k6, e6, r6⟩ => ?_
  rw [show seqs [.block [.subi .r4 .r4 1]] = .block [.subi .r4 .r4 1] from rfl]
  obtain b7 : WP isa (.block [.subi .r4 .r4 1]) t6 fun u =>
      (u.gpr .r4 = t6.gpr .r4 - BitVec.ofNat 64 1 ∧ u.mem = t6.mem) ∧ Keep [.r4] t6 u := by
    refine WP.keep _ ?_ (by decide)
    prun []
  refine WP.mono b7 fun u ⟨⟨u4, m7⟩, k7⟩ => ?_
  obtain r4eq : t6.gpr .r4 = s.gpr .r4 := by rw [r6.gpr _ (by decide), k5.gpr _ (by decide)]
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
  obtain zN : z < N := by omega_arith
  obtain yN : y < N := by omega_arith
  obtain xN : x < N := by omega_arith
  obtain aN : a < N := by omega_arith
  obtain mN : m < N := by omega_arith
  obtain tN : t < N := by omega_arith
  obtain t1N : t + 1 + 2 < N := by omega_arith
  -- The arrays each step does not write, while the context is small.
  obtain nm : ∀ {l : List Nat} {j : Nat}, (∀ k ∈ l, k ≠ j) → ∀ k ∈ l, k ≠ j := fun h => h
  obtain n2 : ∀ j, j ≠ t → ∀ k ∈ [t], k ≠ j := fun j hj k hk => by
    rw [List.mem_singleton] at hk; subst hk; exact Ne.symm hj
  obtain n4 : ∀ j o, j ≠ t + 1 → j ≠ t + 1 + 1 → j ≠ t + 1 + 2 → j ≠ o →
      ∀ k ∈ [t + 1, t + 1 + 1, t + 1 + 2, o], k ≠ j := fun j o h1 h2 h3 h4 k hk => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> exact Ne.symm (by with_reducible assumption)
  obtain n1 : ∀ j, j ≠ y → ∀ k ∈ [y], k ≠ j := fun j hj k hk => by
    rw [List.mem_singleton] at hk; subst hk; exact Ne.symm hj
  clear nm
  obtain fz := h.fit64 zN
  obtain fy := h.fit64 yN
  obtain fx := h.fit64 xN
  obtain fa := h.fit64 aN
  obtain fm := h.fit64 mN
  rw [mulModStep, wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (mulHead_ok h hN tN zN yN xN (by omega_arith) (by omega_arith)) fun t2 ⟨h2, k2, r2, e2⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (addMod_ok h2 (o := a) (a := a) (b := t) (m := m) (z := z) (t := t + 1) hN aN aN tN mN zN t1N
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith))
    fun t3 ⟨h3, k3, r3, e3⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (addMod_ok h3 (o := x) (a := x) (b := x) (m := m) (z := z) (t := t + 1) hN xN xN xN mN zN t1N
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith))
    fun t4 ⟨h4, k4, r4, e4⟩ => ?_
  rw [show seqs [mulTail y] = mulTail y from rfl]
  refine WP.mono (mulTail_ok h4 hN yN) fun u ⟨hu, k6, r6, c6, e6⟩ => ?_
  obtain r4eq : t4.gpr .r4 = s.gpr .r4 := by
    rw [r4.gpr _ (by decide), r3.gpr _ (by decide), r2.gpr _ (by decide)]
  refine ⟨hu, ((k2.mono.trans k3.mono).trans k4.mono).trans k6.mono,
    (((r2.trans r3).trans r4).trans r6).mono, by rw [c6, r4eq], ?_, fun hZ hA hX hM => ?_⟩
  · rw [e6, k4.num (n4 y x (by omega_arith) (by omega_arith) (by omega_arith) hyx) (by simp; decide) fy,
      k3.num (n4 y a (by omega_arith) (by omega_arith) (by omega_arith) hya) (by simp; decide) fy,
      k2.num (n2 y (by omega_arith)) (by simp; decide) fy]
  · -- The values each step reads.
    obtain z2 : num t2.mem B w z = 0 := by rw [k2.num (n2 z (by omega_arith)) (by simp; decide) fz, hZ]
    obtain mm2 : num t2.mem B w m = num s.mem B w m := k2.num (n2 m (by omega_arith)) (by simp; decide) fm
    obtain a2 : num t2.mem B w a = num s.mem B w a := k2.num (n2 a (by omega_arith)) (by simp; decide) fa
    obtain x2 : num t2.mem B w x = num s.mem B w x := k2.num (n2 x (by omega_arith)) (by simp; decide) fx
    obtain d2 : num t2.mem B w t = num s.mem B w y % 2 * num s.mem B w x := by
      rw [e2, hZ]
      rcases Nat.mod_two_eq_zero_or_one (num s.mem B w y) with e | e <;> simp [e]
    obtain dlt : num t2.mem B w t < num s.mem B w m := by
      rw [d2]; rcases Nat.mod_two_eq_zero_or_one (num s.mem B w y) with e | e <;> simp [e] <;> omega_arith
    obtain A3 := e3 z2 (by rw [a2, mm2]; exact hA) (by rw [mm2]; exact dlt) (by rw [mm2]; exact hM)
    rw [a2, mm2, d2] at A3
    obtain z3 : num t3.mem B w z = 0 := by rw [k3.num (n4 z a (by omega_arith) (by omega_arith) (by omega_arith) hza) (by simp; decide) fz, z2]
    obtain mm3 : num t3.mem B w m = num s.mem B w m := by
      rw [k3.num (n4 m a (by omega_arith) (by omega_arith) (by omega_arith) (Ne.symm ham)) (by simp; decide) fm, mm2]
    obtain x3 : num t3.mem B w x = num s.mem B w x := by
      rw [k3.num (n4 x a (by omega_arith) (by omega_arith) (by omega_arith) hxa) (by simp; decide) fx, x2]
    obtain X4 := e4 z3 (by rw [x3, mm3]; exact hX) (by rw [x3, mm3]; exact hX) (by rw [mm3]; exact hM)
    rw [x3, mm3] at X4
    refine ⟨?_, ?_⟩
    · rw [k6.num (n1 a (Ne.symm hya)) (by simp) fa,
        k4.num (n4 a x (by omega_arith) (by omega_arith) (by omega_arith) (Ne.symm hxa)) (by simp; decide) fa, A3]
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
  obtain fz := h.fit64 (j := z) (by omega_arith)
  obtain fm := h.fit64 (j := m) (by omega_arith)
  obtain zk : num u.mem B w z = num s0.mem B w z := inv.keep.num (by simp; omega_arith) (by simp; decide) fz
  obtain mk : num u.mem B w m = num s0.mem B w m := inv.keep.num (by simp; omega_arith) (by simp; decide) fm
  refine WP.mono (mulModStep_ok h hN hi) fun u' ⟨h', k', r', c', y', v'⟩ => ?_
  refine ⟨⟨h', inv.keep.trans k', (inv.regs.trans r').mono, ?_, fun hZ hA hX hM => ?_⟩, c'⟩
  · rw [y', inv.yv, Nat.div_div_eq_div_mul, Nat.pow_succ]
  · obtain ⟨va, vx⟩ := inv.value hZ hA hX hM
    obtain M0 : 0 < num s0.mem B w m := by omega_arith
    obtain aLt : num u.mem B w a < num u.mem B w m := by rw [va, mk]; exact Nat.mod_lt _ M0
    obtain xLt : num u.mem B w x < num u.mem B w m := by rw [vx, mk]; exact Nat.mod_lt _ M0
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
  obtain start : MulI s B Z w N z y x a m t 0 s :=
    ⟨h, KeyWorkspace.Keep.refl _ _ _ _ _, Keep.refl _ _, by rw [Nat.pow_zero, Nat.div_one],
      fun _ hA hX _ => ⟨by rw [Nat.pow_zero, Nat.mod_one, Nat.zero_mul, Nat.add_zero, Nat.mod_eq_of_lt hA],
        by rw [Nat.pow_zero, Nat.one_mul, Nat.mod_eq_of_lt hX]⟩⟩
  refine WP.mono (wp_countdown (body := mulModStep z y x a m t) (cnt := .r4) (N := k) hk' hk
    (MulI s B Z w N z y x a m t) (fun i _ u inv _ => mulModBody_ok hN hi inv) start c)
    fun u inv => ⟨inv.ws, inv.keep, inv.regs, fun hZ hA hX hM => (inv.value hZ hA hX hM).1⟩

end VG.Proof.Rsa.PPC64LE.Keys

end

end

/-! ### `Rsa.PPC64LE.KcCkPre`, which this module and modules that import it used -/

section

/-! # `vg_rsa_check_key` and `vg_rsa_check_crt_key` on PPC64LE: their preconditions' `KPre` -/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.KeyCheck

open VG VG.PPC64LE

/-- The working space of `vg_rsa_check_key`. -/
abbrev ckB (s0 : State) : Addr := PPC64LE.stackArg s0 8
abbrev ckZ (s0 : State) : Nat := (PPC64LE.stackArg s0 9).toNat * 8
/-- The modulus' length. -/
abbrev kK (s0 : State) : Nat := (s0.gpr .r4).toNat

theorem ck_kpre {s0 : State} (h : ckP.pre s0) : KPre s0 (ckB s0) (ckZ s0) (kK s0) 8 10 := by
  obtain ⟨hsp, hrd, hwr, -, -, -, -, -, -, -, -, hsa, -, -, -, -, -, -, -, -, nw, ⟨hk, hk'⟩, -, -, -, -, -, -,
    -, -, -, -, -, hsl⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  exact ⟨by rw [hwr]; simp, nw, by simp only [ckZ, kK]; omega_using [hsl], hk, hk', by omega_using [hsp], by rw [hrd]; simp, hsa, rfl,
    by decide, rfl⟩

end VG.Proof.Rsa.PPC64LE.KeyCheck

end

end

/-! ### `Rsa.PPC64LE.KcBase`, which this module and modules that import it used -/

section

/-! # The checks of an RSA key on PPC64LE: the state between the steps

As on ARMv7 (`Proof/Rsa/Arm/KcBase.lean`). `Geo`: the working space (`B`,
`Z` bytes) and the modulus' length `K`, which two runs share; `Vals`: the
numbers read, which they may not. `Stg g s₀ A live c s`: from the state `s₀`
the checks start from, the steps so far wrote only the arrays and the header
words they may and the registers `bodyRegs`, the arrays `live` hold `A`,
and the mask is `c`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.KeyCheck

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (sOdd sB sC)
open VG.Impl.Rsa.PPC64LE.KeyCheck
open VG.Proof.Rsa.KeyWorkspace (arr S num slot Arrs upd upd_ne upd_self)

structure Geo where
  B : Addr
  Z : Nat
  K : Nat

/-- `w = ⌈K / 4⌉`. -/
abbrev Geo.w (g : Geo) : Nat := (g.K + 3) / 4

structure Vals where
  n : Nat
  e : Nat
  p : Nat
  q : Nat
  dP : Nat
  dQ : Nat
  qI : Nat
  d : Nat

/-- The arrays after the numbers are read. -/
def vals (v : Vals) : Nat → Nat :=
  upd (upd (upd (upd (upd (upd (upd (upd (fun _ => 0) aE v.e) aN v.n) aD v.d) aP v.p) aQ v.q) aDP v.dP)
    aDQ v.dQ) aQI v.qI

/-- The header words the checks write. -/
abbrev bodySlots : List Nat := [sOdd, sB, sC, sF, sMask]

/-- The registers the checks may change. -/
abbrev bodyRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

/-- The arrays through a step that writes none of them. -/
theorem arrsKeep {m m' : Mem} {B : Addr} {w : Nat} {A : Nat → Nat} {live : List Nat} {js ds : List Nat}
    (h : Arrs m B w A live) (k : KeyWorkspace.Keep B w js ds m m')
    (hj : ∀ j ∈ live, j ∉ js) (hd : ∀ d ∈ ds, d + 4 ≤ KeyWorkspace.hdr)
    (fit : ∀ j ∈ live, arr w j + S w ≤ 2 ^ 64) : Arrs m' B w A live := fun j hj' => by
  rw [k.num (fun i hi e => hj j hj' (by subst e; exact hi)) hd (fit j hj'), h j hj']

/-- Between the steps. -/
structure Stg (g : Geo) (s0 : State) (A : Nat → Nat) (live : List Nat) (c : Bool) (s : State) : Prop where
  ws : Ws s g.B g.Z g.w nArr
  keep : KeyWorkspace.Keep g.B g.w (List.range nArr) bodySlots s0.mem s.mem
  regs : Keep bodyRegs s0 s
  arrs : Arrs s.mem g.B g.w A live
  live_lt : ∀ j ∈ live, j < nArr
  vdTop : w32 s.mem g.B (arr g.w aVD + 4 * g.w) = 0
  mask : slot s.mem g.B sMask = if c then 1 else 0

/-- A step from `Stg`. -/
theorem Stg.next {g : Geo} {s0 s t : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {js ds : List Nat} {rs : List Reg} (hw : Ws t g.B g.Z g.w nArr)
    (k : KeyWorkspace.Keep g.B g.w js ds s.mem t.mem) (hjs : ∀ j ∈ js, j < nArr)
    (hds : ∀ d ∈ ds, d ∈ bodySlots) (r : Keep rs s t) (hrs : ∀ x ∈ rs, x ∈ bodyRegs) {A' : Nat → Nat}
    {live' : List Nat} {c' : Bool} (ha : Arrs t.mem g.B g.w A' live') (hl : ∀ j ∈ live', j < nArr)
    (vd : w32 t.mem g.B (arr g.w aVD + 4 * g.w) = 0)
    (mk : slot t.mem g.B sMask = if c' then 1 else 0) : Stg g s0 A' live' c' t :=
  ⟨hw, h.keep.trans (k.mono (fun j hj => List.mem_range.2 (hjs j hj)) hds),
    (h.regs.trans r).mono fun x hx => by
      rcases List.mem_append.mp hx with hx | hx
      · exact hx
      · exact hrs x hx, ha, hl, vd, mk⟩

/-- The mask through a step that leaves its slot. -/
theorem Stg.mask_keep {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {js ds : List Nat} {m' : Mem} (k : KeyWorkspace.Keep g.B g.w js ds s.mem m')
    (hd : ∀ d ∈ ds, sMask + 4 ≤ d ∨ d + 4 ≤ sMask) : slot m' g.B sMask = if c then 1 else 0 := by
  rw [k.slot (by decide) hd, h.mask]

/-- The top digit of `aVD` through a step that leaves `aVD`. -/
theorem Stg.vd_keep {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {js ds : List Nat} {m' : Mem} (k : KeyWorkspace.Keep g.B g.w js ds s.mem m')
    (hj : ∀ j ∈ js, j ≠ aVD) (hd : ∀ d ∈ ds, d + 4 ≤ KeyWorkspace.hdr) :
    w32 m' g.B (arr g.w aVD + 4 * g.w) = 0 := by
  rw [k.word (by simp only [S]; omega_using []) hj hd (h.ws.fit64 (by decide)), h.vdTop]

/-- The arrays through a step that writes none of them. -/
theorem Stg.arrs_keep {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {js ds : List Nat} {m' : Mem} (k : KeyWorkspace.Keep g.B g.w js ds s.mem m')
    (hj : ∀ j ∈ live, j ∉ js) (hd : ∀ d ∈ ds, d + 4 ≤ KeyWorkspace.hdr) : Arrs m' g.B g.w A live :=
  arrsKeep h.arrs k hj hd fun j hj' => h.ws.fit64 (h.live_lt j hj')

/-- The arrays through a step that writes `o := v`. -/
theorem Stg.arrs_write {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {js ds : List Nat} {m' : Mem} (k : KeyWorkspace.Keep g.B g.w js ds s.mem m')
    {o v : Nat} (e : num m' g.B g.w o = v) (hj : ∀ j ∈ live, j = o ∨ j ∉ js)
    (hd : ∀ d ∈ ds, d + 4 ≤ KeyWorkspace.hdr) : Arrs m' g.B g.w (upd A o v) live := by
  intro j hj'
  by_cases e' : j = o
  · subst e'; rw [upd_self]; exact e
  · rw [upd_ne _ _ e', k.num (fun i hi ei => ((hj j hj').resolve_left e') (by subst ei; exact hi)) hd
      (h.ws.fit64 (h.live_lt j hj')), h.arrs j hj']

/-- The mask and'ed with a check. -/
theorem acc_bits {x y : Nat} {c d : Bool} (hx : x = if c then 1 else 0) (hy : y = if d then 1 else 0) :
    (if x = 1 ∧ y = 1 then 1 else 0) = if (c && d) then 1 else 0 := by
  subst hx hy; cases c <;> cases d <;> rfl

theorem bit_le {c : Bool} {x : Nat} (h : x = if c then 1 else 0) : x ≤ 1 := by
  subst h; cases c <;> decide

end VG.Proof.Rsa.PPC64LE.KeyCheck

end

end

/-! ### `Rsa.PPC64LE.KcBody`, which only this module used -/

section

/-! ### `Rsa.PPC64LE.KcSetup`, which only this module used -/

section

/-!
# The checks of an RSA key on PPC64LE: the arrays set up

`setup_ok`: `w = ⌈n_len / 4⌉` (`n_len` in `r15`) and the stride into `r29`
and `r30`, and every array zeroed. `LdS`: what the reading of the numbers
keeps: `KBase`, the working space, every array's value (`A`) and its extra
digit 0. `eArr_ok`, `ldStep_ok`: `e` from `r24`, and a number from its bytes.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.KeyCheck

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.KeyCheck (setup eArr loadR nArr aE)
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot Arrs upd upd_ne upd_self)

/-- `w = ⌈K / 4⌉`. -/
abbrev kw (K : Nat) : Nat := (K + 3) / 4

theorem KPre.ws {s0 : State} {B : Addr} {Z K oS na : Nat} (h : KPre s0 B Z K oS na) :
    arr (kw K) nArr ≤ Z ∧ 16 ≤ kw K ∧ kw K ≤ 256 ∧ K ≤ 4 * kw K := by
  have := h.zk; have := h.k64; have := h.k1024
  simp only [arr, S, nArr, VG.Proof.Rsa.KeyWorkspace.hdr, kw]
  omega_arith

theorem ofNat_digits24 (w : Nat) (hw : w ≤ 256) :
    (BitVec.ofNat 64 24 * BitVec.ofNat 64 (S w)) >>> 2 = BitVec.ofNat 64 (24 * (w + 2)) := by
  rw [← BitVec.ofNat_mul]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  simp only [S]
  rw [Nat.mod_eq_of_lt (show 24 * (4 * (w + 2)) < 2 ^ 64 by omega_arith),
    Nat.mod_eq_of_lt (show 24 * (w + 2) < 2 ^ 64 by omega_arith)]
  omega_arith

/-- `setup`: `w` and the stride, and every digit of the arrays 0. -/
theorem setup_ok {s0 s : State} {B : Addr} {Z K oS na : Nat} (hp : KPre s0 B Z K oS na) (h : KBase B Z s0 s)
    (h15 : s.gpr .r15 = BitVec.ofNat 64 K) :
    WP isa setup s fun t => KBase B Z s0 t ∧ Ws t B Z (kw K) nArr ∧
      (∀ j < nArr, ∀ i < kw K + 2, w32 t.mem B (arr (kw K) j + 4 * i) = 0) ∧
      Keep (.r29 :: .r30 :: opRegs) s t := by
  obtain ⟨fits, hw16, hw, -⟩ := hp.ws
  have nw := hp.nowrap
  obtain hs : Scr s B Z := Scr.of_mem (by rw [h.wr]; exact hp.wr) nw
  obtain hkv : (BitVec.ofNat 64 K).toNat ≤ 1024 := by rw [BitVec.toNat_ofNat]; have := hp.k1024; omega_arith
  rw [setup, WP.seq_iff]
  obtain hb : WP isa (.block ([.addi .r29 .r15 3, .lsr .d .r29 .r29 2] ++
      VG.Impl.Rsa.PPC64LE.Keys.stride ++ [.li .r8 nArr, .mul .r8 .r8 .r30, .lsr .d .r8 .r8 2])) s fun u =>
        (u.gpr .r29 = BitVec.ofNat 64 (kw K) ∧ u.gpr .r30 = BitVec.ofNat 64 (S (kw K)) ∧
          u.gpr .r8 = BitVec.ofNat 64 (nArr * (kw K + 2)) ∧ u.mem = s.mem) ∧ Keep [.r8, .r29, .r30] s u := by
    refine WP.keep _ ?_ (by decide)
    obtain e3 := CrtValues.ofNat_add3_shr2 _ hkv
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hp.k1024; omega_arith)] at e3
    prun [VG.Impl.Rsa.PPC64LE.Keys.stride, h15, e3, CrtValues.ofNat_stride, ofNat_digits24 _ hw, nArr]
  refine WP.mono hb fun u ⟨⟨u29, u30, u8, um⟩, ku⟩ => ?_
  obtain hu : Ws u B Z (kw K) nArr :=
    ⟨hs.congr ku.wr, fits, by omega_arith, by omega_arith, u29, u30, (ku.gpr _ (by decide)).trans h.r31⟩
  obtain hn : 160 + 4 * (nArr * (kw K + 2)) ≤ Z := by
    simp only [arr, S, nArr, VG.Proof.Rsa.KeyWorkspace.hdr] at fits ⊢; omega_arith
  refine WP.mono (zeroArrays_ok hu u8 (by simp only [nArr]; omega_arith) (by simp only [nArr]; omega_arith) hn)
    fun t ⟨ht, z, out, kt⟩ => ⟨?_, ht, fun j hj i hi => ?_, (ku.trans kt).mono⟩
  · exact h.of_outside (by rw [← um]; exact out) hn (ku.trans kt)
  · have hb : j * (kw K + 2) + i < nArr * (kw K + 2) := by
      have := Nat.mul_le_mul_right (kw K + 2) (show j + 1 ≤ nArr by omega_arith)
      rw [Nat.add_mul, Nat.one_mul] at this; omega_arith
    have := z (j * (kw K + 2) + i) hb
    rw [show 160 + 4 * (j * (kw K + 2) + i) = arr (kw K) j + 4 * i by
      simp only [arr, S, VG.Proof.Rsa.KeyWorkspace.hdr]; grind] at this
    exact this

/-- What the reading of the numbers keeps. -/
structure LdS (B : Addr) (Z K : Nat) (s0 : State) (A : Nat → Nat) (t : State) : Prop where
  base : KBase B Z s0 t
  ws : Ws t B Z (kw K) nArr
  arrs : Arrs t.mem B (kw K) A (List.range nArr)
  top : ∀ j < nArr, w32 t.mem B (arr (kw K) j + 4 * kw K) = 0

/-- `setup`'s arrays: every one 0. -/
theorem LdS.of_setup {B : Addr} {Z K : Nat} {s0 t : State} (b : KBase B Z s0 t) (w : Ws t B Z (kw K) nArr)
    (z : ∀ j < nArr, ∀ i < kw K + 2, w32 t.mem B (arr (kw K) j + 4 * i) = 0) :
    LdS B Z K s0 (fun _ => 0) t :=
  ⟨b, w, fun j hj => CrtValues.val32_of_zero fun i hi => z j (List.mem_range.mp hj) i (by omega_arith),
    fun j hj => z j hj _ (by omega_arith)⟩

/-- `loadR rP rL j`: array `j`, 0, := the `L` bytes at `P`. -/
theorem ldStep_ok {B : Addr} {Z K : Nat} {s0 t : State} {A : Nat → Nat} (hI : LdS B Z K s0 A t) {j : Nat}
    (hj : j < nArr) (hA : A j = 0) {rP rL : Reg} (hrP : rP ≠ .r0) (hrL : rL ≠ .r0) (hrL6 : rL ≠ .r6)
    {P : Addr} {L : Nat} (hP : t.gpr rP = P) (hL : t.gpr rL = BitVec.ofNat 64 L) (hL1 : 1 ≤ L)
    (hLw : L ≤ 4 * kw K) (hrd : (⟨P, L⟩ : Region) ∈ s0.rd) (hd : (⟨P, L⟩ : Region).Disjoint ⟨B, Z⟩)
    (hPw : P.toNat + L ≤ 2 ^ 64) :
    WP isa (seqs (loadR rP rL j)) t fun u =>
      LdS B Z K s0 (upd A j (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem P L))) u ∧ Keep [.r0, .r5, .r6, .r8] t u := by
  have h := hI.ws
  obtain fit : ∀ i < nArr, arr (kw K) i + S (kw K) ≤ 2 ^ 64 := fun i hi => h.fit64 hi
  rw [loadR, wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (CrtValues.mv2_ok (s := t) (d₁ := .r6) (d₂ := .r8) hrP hrL hrL6 (by decide))
    fun u ⟨⟨u6, u8, um⟩, ku⟩ => ?_
  rw [show seqs [VG.Impl.Rsa.PPC64LE.CrtValues.load j] = VG.Impl.Rsa.PPC64LE.CrtValues.load j from rfl]
  obtain hu := h.of_keep ku
  obtain b1 := hI.base.of_regs ku um
  obtain hc : ∀ i < L, (⟨P, L⟩ : Region).Contains (off P i) 1 := fun i hi =>
    Offset.contains_base _ (by omega_arith) (by omega_arith)
  obtain hz : val32 u.mem B (arr (kw K) j) (kw K) = 0 := by
    rw [um]; exact (hI.arrs.get (List.mem_range.mpr hj)).trans hA
  refine WP.mono (load_ok hu hj (by decide) (u6.trans hP) (u8.trans hL) hL1 hLw
    (fun i hi => ⟨_, List.mem_append_left _ (by rw [ku.rd, hI.base.rd]; exact hrd), hc i hi⟩)
    (fun i hi x hx e => by have := CrtValues.past_of_disjoint hd (hc i hi); rw [e] at this; omega_arith)
    (fun p hp => by rw [← off_add]; exact VG.Proof.Bignum.byte_zero_of_val32 hz hp))
    fun v ⟨hv, k, val, kv, o⟩ => ⟨⟨b1.of_keep k hI.ws.nowrap (by simp; exact h.arr_fit hj) (by simp)
      h.hdr_le kv, hv, fun i hi => ?_, fun i hi => ?_⟩, (ku.trans kv).mono⟩
  · by_cases e : i = j
    · subst e
      rw [upd_self, val]
      congr 1
      simp only [Spec.Rsa.bytesAt]
      refine List.map_congr_left fun c hc' => ?_
      rw [um]
      exact hI.base.frame _ (CrtValues.past_of_disjoint hd (hc c (List.mem_range.mp hc')))
    · rw [upd_ne _ _ e, CrtValues.num_out o (Ne.symm e) (fit _ (List.mem_range.mp hi)), um]
      exact hI.arrs.get hi
  · rw [CrtValues.top_out o (fit _ hi), um]; exact hI.top i hi

theorem shl_shr31 {E : Nat} (hE : E < 2 ^ 33) : (BitVec.ofNat 64 E <<< 31) >>> 31 = BitVec.ofNat 64 E := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (show E < 2 ^ 64 by omega_arith),
    Nat.mod_eq_of_lt (show E * 2 ^ 31 < 2 ^ 64 by omega_arith), Nat.mul_div_cancel _ (by decide)]

/-- A number whose two low digits are written and whose others are kept from 0. -/
theorem val32_two {m m' : Mem} {B : Addr} {d w : Nat} (hw : 2 ≤ w) (hz : val32 m B d w = 0)
    (o : ∀ i, 2 ≤ i → i < w → w32 m' B (d + 4 * i) = w32 m B (d + 4 * i)) :
    val32 m' B d w = w32 m' B d + 2 ^ 32 * w32 m' B (d + 4) := by
  obtain ⟨n, rfl⟩ : ∃ n, w = 2 + n := ⟨w - 2, by omega_arith⟩
  obtain e := val32_append m B d 2 n
  obtain e' := val32_append m' B d 2 n
  rw [hz] at e
  obtain rest : val32 m B (d + 4 * 2) n = 0 := by
    have : 0 ≤ val32 m B d 2 := Nat.zero_le _
    rcases Nat.eq_zero_or_pos (val32 m B (d + 4 * 2) n) with h | h
    · exact h
    · have : 2 ^ (32 * 2) ≤ 2 ^ (32 * 2) * val32 m B (d + 4 * 2) n := Nat.le_mul_of_pos_right _ h
      omega_arith
  obtain rest' : val32 m' B (d + 4 * 2) n = 0 := by
    rw [← rest]
    refine val32_congr fun i hi => ?_
    rw [show d + 4 * 2 + 4 * i = d + 4 * (i + 2) by omega_arith]
    exact o (i + 2) (by omega_arith) (by omega_arith)
  rw [e', rest', Nat.mul_zero, Nat.add_zero]
  simp only [val32, Nat.mul_zero, Nat.add_zero]

/-- `eArr`: `e`, below `2^33`, from `r24 = e · 2^31` into its array, which is 0. -/
theorem eArr_ok {B : Addr} {Z K : Nat} {s0 t : State} {A : Nat → Nat} (hI : LdS B Z K s0 A t)
    (hw2 : 2 ≤ kw K) (hA : A aE = 0) {E : Nat} (h24 : t.gpr .r24 = BitVec.ofNat 64 E <<< 31)
    (hE : E < 2 ^ 33) :
    WP isa (.block eArr) t fun u => LdS B Z K s0 (upd A aE E) u ∧ Keep [.r0, .r5] t u := by
  have h := hI.ws
  obtain fit : ∀ i < nArr, arr (kw K) i + S (kw K) ≤ 2 ^ 64 := fun i hi => h.fit64 hi
  obtain fE := h.arr_fit (j := aE) (by decide)
  obtain fE' := fit aE (by decide)
  have hS : S (kw K) = 4 * (kw K + 2) := rfl
  have hs := h.scr
  unfold eArr
  refine ptr_ok h (r := .r5) (by decide) (by decide) (by decide) (show aE < 2 ^ 15 by decide) ?_
  let d := arr (kw K) aE
  let lo : BitVec 32 := (BitVec.ofNat 64 E).setWidth 32
  let hi : BitVec 32 := (BitVec.ofNat 64 E >>> 32).setWidth 32
  obtain hb : WP isa (.block [.lsr .d .r0 .r24 31, .store .w .r0 .r5 0, .lsr .d .r0 .r0 32, .store .w .r0 .r5 4])
      (t.write .r5 (off B d)) fun u =>
        u.mem = (t.mem.writeW (off B d) lo).writeW (off B (d + 4)) hi ∧ Keep [.r0, .r5] t u := by
    refine WP.mono (WP.keep [.r0] (Q := fun u => u.mem = (t.mem.writeW (off B d) lo).writeW (off B (d + 4)) hi)
      ?_ (by decide)) fun u ⟨m, k⟩ => ⟨m, ((Keep.write _ _ _).trans k).mono⟩
    prun [h24, shl_shr31 hE, exec_store_w (show Reg.r5 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
      exec_store_w (show Reg.r5 ≠ .r0 by decide) (show 4 < 2 ^ 15 by decide),
      hs.st (d := d) (n := 4) (by omega_arith), hs.st (d := d + 4) (n := 4) (by omega_arith), off_add]
    rfl
  refine WP.mono hb fun u ⟨um, ku⟩ => ?_
  obtain o1 : Outside B d 4 t.mem (t.mem.writeW (off B d) lo) := writeW32_outside _ _ _ (by omega_arith)
  obtain o2 : Outside B (d + 4) 4 (t.mem.writeW (off B d) lo) u.mem := by
    rw [um]; exact writeW32_outside _ _ _ (by omega_arith)
  obtain o : Outside B d 8 t.mem u.mem := (o1.mono (by omega_arith) (by omega_arith)).trans (o2.mono (by omega_arith) (by omega_arith))
  obtain k : KeyWorkspace.Keep B (kw K) [aE] [] t.mem u.mem :=
    KeyWorkspace.Keep.of_arr (d := 0) (by simpa using o) (by omega_arith) (by simp)
  refine ⟨⟨hI.base.of_keep k hI.ws.nowrap (by simp; exact fE) (by simp) h.hdr_le ku, h.of_keep ku,
    fun j hj => ?_, fun j hj => ?_⟩, ku⟩
  · by_cases e : j = aE
    · subst e
      rw [upd_self]
      obtain hz : val32 t.mem B d (kw K) = 0 := (hI.arrs.get (List.mem_range.mpr (by decide))).trans hA
      change val32 u.mem B d (kw K) = E
      rw [val32_two hw2 hz fun i hi hi' => o.w32 (by omega_arith) (by omega_arith)]
      obtain w0 : w32 u.mem B d = lo.toNat := by
        rw [o2.w32 (by omega_arith) (by omega_arith)]; exact w32_write_self _ _ _ _
      obtain w1 : w32 u.mem B (d + 4) = hi.toNat := by rw [um]; exact w32_write_self _ _ _ _
      rw [w0, w1]
      simp only [lo, hi, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
        Nat.shiftRight_eq_div_pow]
      rw [Nat.mod_eq_of_lt (show E < 2 ^ 64 by omega_arith), Nat.mod_eq_of_lt (show E / 2 ^ 32 < 2 ^ 32 by omega_arith)]
      omega_arith
    · rw [upd_ne _ _ e]
      have := VG.Proof.Rsa.KeyWorkspace.arr_disj (w := kw K) e
      obtain fj := fit j (List.mem_range.mp hj)
      rw [show num u.mem B (kw K) j = num t.mem B (kw K) j from o.val32 (by omega_arith) (by omega_arith)]
      exact hI.arrs.get hj
  · have fj := fit j hj
    by_cases e : j = aE
    · subst e; rw [o.w32 (by omega_arith) (by omega_arith)]; exact hI.top _ hj
    · have := VG.Proof.Rsa.KeyWorkspace.arr_disj (w := kw K) e
      rw [o.w32 (by omega_arith) (by omega_arith)]; exact hI.top _ hj

end VG.Proof.Rsa.PPC64LE.KeyCheck

end

end


/-!
# The checks of an RSA key on PPC64LE: from the set-up to the mask

`prep_ok`: `setup` and `e`'s array; `Stg.base`: the checks keep `KBase`;
`ret_ok`: the mask returned.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.KeyCheck

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.KeyCheck
open VG.Proof.Rsa.KeyWorkspace (arr S num slot Arrs upd upd_ne upd_self)

/-- `setup` and `e`'s array. -/
theorem prep_ok {s0 s : State} {B : Addr} {Z K oS na : Nat} (hp : KPre s0 B Z K oS na) (h : KBase B Z s0 s)
    (h15 : s.gpr .r15 = BitVec.ofNat 64 K) {E : Nat} (h24 : s.gpr .r24 = BitVec.ofNat 64 E <<< 31)
    (hE : E < 2 ^ 33) {rest : List (Prog isa)} (hrest : rest ≠ []) {Q : State → Prop}
    (k : ∀ t, LdS B Z K s0 (upd (fun _ => 0) aE E) t → Keep (.r29 :: .r30 :: opRegs) s t →
      WP isa (Impl.Rsa.PPC64LE.Keys.seqs rest) t Q) :
    WP isa (Impl.Rsa.PPC64LE.Keys.seqs (setup :: .block eArr :: rest)) s Q := by
  obtain ⟨-, hw16, -, -⟩ := hp.ws
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (setup_ok hp h h15) fun t1 ⟨b1, w1, z1, k1⟩ => ?_
  rw [wp_seqs_cons hrest]
  obtain l1 := LdS.of_setup b1 w1 z1
  refine WP.mono (eArr_ok l1 (by omega_using [hw16]) rfl (by rw [k1.gpr _ (by decide)]; exact h24) hE)
    fun t ⟨lt, kt⟩ => k t lt ((k1.trans kt).mono)

/-- The checks keep `KBase`. -/
theorem Stg.base {g : Geo} {s0 sS t : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g sS A live c t) (hb : KBase g.B g.Z s0 sS) (hnw : g.B.toNat + g.Z ≤ 2 ^ 64) :
    KBase g.B g.Z s0 t :=
  hb.of_keep h.keep hnw (fun j hj => h.ws.arr_fit (List.mem_range.mp hj)) (by decide) h.ws.hdr_le h.regs

/-- `ret`: the mask's bit in `r3`. -/
theorem ret_ok {g : Geo} {sS t : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g sS A live c t) :
    WP isa (.block ret) t fun u => (u.gpr .r3 = BitVec.ofNat 64 (if c then 1 else 0) ∧ u.mem = t.mem) ∧
      Keep [.r3] t u := by
  have hs := h.ws.scr
  have hz := h.ws.hdr_le
  refine WP.keep _ ?_ (by decide)
  prun [Impl.Rsa.PPC64LE.KeyCheck.ret, h.ws.r31,
      exec_load_w (show Reg.r31 ≠ .r0 by decide) (show sMask < 2 ^ 15 by decide),
    hs.ld (d := sMask) (n := 4) (by unfold sMask; simp only [KeyWorkspace.hdr] at hz; omega_using [hz]),
    CrtValues.ofNat_slot _ h.mask]

end VG.Proof.Rsa.PPC64LE.KeyCheck

end

end

/-! ### `Rsa.PPC64LE.KcChecks`, which only this module used -/

section

/-! ### `Rsa.PPC64LE.KcOps`, which only this module used -/

section

/-! # The checks of an RSA key on PPC64LE: the steps

As on ARMv7 (`Proof/Rsa/Arm/KcOps.lean`, `KcDiv.lean`), each from `Stg`:
copies, clearing a low bit, comparisons and'ed into the mask (`ltA_ok`,
`eqA_ok`), products modulo a number (`mulA_ok`) and divisions (`divA_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.KeyCheck

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (seqs copy clrLow andS stBorrow mulMod sOdd sB sC)
open VG.Impl.Rsa.PPC64LE.KeyCheck
open VG.Proof.Rsa.KeyWorkspace (arr S num slot Arrs upd upd_ne upd_self)

theorem opRegs_body : ∀ x ∈ opRegs, x ∈ bodyRegs := by decide
theorem r4opRegs_body : ∀ x ∈ (.r4 :: opRegs), x ∈ bodyRegs := by decide

theorem Stg.sub {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {live' : List Nat} (hs : ∀ j ∈ live', j ∈ live) : Stg g s0 A live' c s :=
  { h with arrs := h.arrs.sub hs, live_lt := fun j hj => h.live_lt j (hs j hj) }

theorem Stg.congr' {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {A' : Nat → Nat} (e : ∀ j ∈ live, A j = A' j) : Stg g s0 A' live c s :=
  { h with arrs := fun j hj => (h.arrs j hj).trans (e j hj) }

/-- `copy o a`, `o` then tracked. -/
theorem Stg.copy_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {o a : Nat} (ho : o < nArr) (ha : a ∈ live) (hoa : o ≠ a) :
    WP isa (copy o a) s (Stg g s0 (upd A o (A a)) (o :: live) c) := by
  refine WP.mono (Keys.copy_ok h.ws ho (h.live_lt a ha) (by decide) hoa) fun t ⟨ht, k, e, r, top⟩ => ?_
  refine h.next ht k (by simpa using ho) (by simp) r opRegs_body ?_ ?_ ?_ (h.mask_keep k (by simp))
  · have e' : num t.mem g.B g.w o = A a := e.trans (h.arrs.get ha)
    exact (h.arrs_write k e' (fun j _ => (Decidable.em (j = o)).imp_right fun n => by simpa using n)
      (by simp)).cons (by rw [upd_self]; exact e')
  · intro j hj
    rcases List.mem_cons.mp hj with rfl | hj'
    · exact ho
    · exact h.live_lt j hj'
  · by_cases hv : o = aVD
    · subst hv; rw [top, h.vdTop]
    · exact h.vd_keep k (by simpa using hv) (by simp)

/-- `clrLow j`. -/
theorem Stg.clrLow_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {j : Nat} (hj : j ∈ live) :
    WP isa (.block (clrLow j)) s (Stg g s0 (upd A j (2 * (A j / 2))) live c) := by
  rw [← List.append_nil (clrLow j)]
  refine Keys.clrLow_ok h.ws (h.live_lt j hj) (by decide) fun t ht k e r top => WP.block_nil ?_
  refine h.next ht k (by simpa using h.live_lt j hj) (by simp) r opRegs_body
    (h.arrs_write k (by rw [e, h.arrs.get hj]) (fun i _ => (Decidable.em (i = j)).imp_right fun n => by
      simpa using n) (by simp)) h.live_lt ?_ (h.mask_keep k (by simp))
  by_cases hv : j = aVD
  · subst hv; rw [top, h.vdTop]
  · exact h.vd_keep k (by simpa using hv) (by simp)

/-- The check in `sF` and'ed into the mask. -/
theorem Stg.acc_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c d : Bool}
    (h : Stg g s0 A live c s) (hf : slot s.mem g.B sF = if d then 1 else 0) :
    WP isa (.block acc) s (Stg g s0 A live (c && d)) := by
  rw [acc, ← List.append_nil (andS sMask sMask sF)]
  refine andS_ok h.ws (by decide) (by decide) (by decide) (bit_le h.mask) (bit_le hf)
    fun t ht k e r => WP.block_nil ?_
  refine h.next ht k (by simp) (by decide) r opRegs_body (h.arrs_keep k (by simp) (by decide)) h.live_lt
    (h.vd_keep k (by simp) (by decide)) ?_
  rw [e, acc_bits h.mask hf]

/-- `ltA a b`: the mask and'ed with `[a] < [b]`. -/
theorem Stg.ltA_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {a b : Nat} (ha : a ∈ live) (hb : b ∈ live) (hW : aW ∉ live) :
    WP isa (seqs (ltA a b)) s (Stg g s0 A live (c && decide (A a < A b))) := by
  obtain na := h.live_lt a ha
  obtain nb := h.live_lt b hb
  obtain hWa : aW ≠ a := fun e => hW (e ▸ ha)
  obtain hWb : aW ≠ b := fun e => hW (e ▸ hb)
  rw [ltA, wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h.ws (o := aW) (a := a) (b := b) (by decide) na nb (by decide) hWa hWb)
    fun t1 ⟨h1, k1, v1, b1, r1⟩ => ?_
  obtain g1 : Stg g s0 A live c t1 :=
    h.next h1 k1 (by decide) (by simp) r1 opRegs_body
      (h.arrs_keep k1 (fun j hj e => hW (by simp at e; exact e ▸ hj)) (by simp)) h.live_lt
      (h.vd_keep k1 (by decide) (by simp)) (h.mask_keep k1 (by simp))
  rw [show seqs [.block (stBorrow sF ++ acc)] = .block (stBorrow sF ++ acc) from rfl]
  refine stBorrow_ok h1 (by decide) b1 fun t2 h2 k2 s2 r2 => ?_
  obtain g2 : Stg g s0 A live c t2 :=
    g1.next h2 k2 (by simp) (by decide) r2 opRegs_body (g1.arrs_keep k2 (by simp) (by decide))
      g1.live_lt (g1.vd_keep k2 (by simp) (by decide)) (g1.mask_keep k2 (by decide))
  refine g2.acc_ok ?_
  rw [s2]
  obtain hb' := VG.Proof.Rsa.borrow_iff (P := 2 ^ (32 * g.w)) v1 (val32_lt _ _ _ _) b1
  rw [h.arrs.get ha, h.arrs.get hb] at hb'
  by_cases hlt : A a < A b
  · have : (t1.gpr .r9).toNat = 1 := by
      have : ¬ (t1.gpr .r9).toNat = 0 := fun e => by have := hb'.mp e; omega_arith
      omega_arith
    simp [hlt, this]
  · have : (t1.gpr .r9).toNat = 0 := hb'.mpr (by omega_arith)
    simp [hlt, this]

/-- `eqA a b`: the mask and'ed with `[a] = [b]`. -/
theorem Stg.eqA_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {a b : Nat} (ha : a ∈ live) (hb : b ∈ live) :
    WP isa (seqs (eqA a b)) s (Stg g s0 A live (c && decide (A a = A b))) := by
  obtain na := h.live_lt a ha
  obtain nb := h.live_lt b hb
  rw [eqA, wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (eqS_ok h.ws (d := sF) (a := a) (b := b) na nb (by decide) (by decide))
    fun t1 ⟨h1, k1, e1, r1⟩ => ?_
  obtain g1 : Stg g s0 A live c t1 :=
    h.next h1 k1 (by simp) (by decide) r1 opRegs_body (h.arrs_keep k1 (by simp) (by decide)) h.live_lt
      (h.vd_keep k1 (by simp) (by decide)) (h.mask_keep k1 (by decide))
  rw [show seqs [.block acc] = .block acc from rfl]
  refine g1.acc_ok ?_
  rw [e1, h.arrs.get ha, h.arrs.get hb]
  by_cases he : A a = A b <;> simp [he]

/-- A count into `r4`. -/
theorem cnt33_ok (u : State) :
    WP isa (.block cnt33) u fun u' => (u'.gpr .r4 = BitVec.ofNat 64 33 ∧ u'.mem = u.mem) ∧ Keep [.r4] u u' := by
  refine WP.keep _ ?_ (by decide)
  prun [cnt33]

/-- `mulA y x m cnt`: `[aA] := ([y] mod 2^k) [x] mod [m]`, `k` the count `cnt` sets. -/
theorem Stg.mulA_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {y x m : Nat} {cnt : List Instr} {k : Nat}
    (hy : y ∈ live) (hx : x ∈ live) (hm : m ∈ live) (hz : aZ ∈ live) (hA0 : A aZ = 0)
    (hmi : MulIdx nArr aZ aY aX aA m aT) (hxY : x ≠ aY)
    (hfree : ∀ j ∈ live, j = aA ∨ j ∉ mulArrs aY aX aA aT) (hk : 0 < k) (hk' : k < 2 ^ 64)
    (hcnt : ∀ u : State, Ws u g.B g.Z g.w nArr → Keep bodyRegs s0 u → WP isa (.block cnt) u fun u' =>
      (u'.gpr .r4 = BitVec.ofNat 64 k ∧ u'.mem = u.mem) ∧ Keep [.r4] u u') :
    WP isa (seqs (mulA y x m cnt)) s fun t => ∃ R,
      (A x < A m → 2 * A m ≤ 2 ^ (32 * g.w) → R = A y % 2 ^ k * A x % A m) ∧
      Stg g s0 (upd A aA R) (aA :: live) c t := by
  obtain free : ∀ j ∈ live, j ≠ aA → j ≠ aY ∧ j ≠ aX ∧ j ∉ mulArrs aY aX aA aT := fun j hj hja => by
    rcases hfree j hj with e | n
    · exact absurd e hja
    · exact ⟨fun e => n (by simp [e]), fun e => n (by simp [e]), n⟩
  obtain yY : y ≠ aY := by
    rcases hfree y hy with e | n
    · rw [e]; decide
    · exact fun e => n (by simp [e])
  unfold mulA
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (h.copy_ok (o := aY) (a := y) (by decide) hy yY.symm) fun t1 h1 => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (h1.copy_ok (o := aX) (a := x) (by decide) (List.mem_cons_of_mem _ hx) (fun e => ?_))
    fun t2 h2 => ?_
  · rcases hfree x hx with e' | n
    · exact absurd (e.trans e') (by decide)
    · exact n (by simp [← e])
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (h2.copy_ok (o := aA) (a := aZ) (by decide)
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hz)) (by decide)) fun t3 h3 => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (hcnt t3 h3.ws h3.regs) fun t4 ⟨⟨c4, m4⟩, u4⟩ => ?_
  obtain k4 : KeyWorkspace.Keep g.B g.w [] [] t3.mem t4.mem := by
    rw [m4]; exact KeyWorkspace.Keep.refl _ _ _ _ _
  obtain h4 := h3.next (h3.ws.of_keep u4) k4 (by simp) (by simp) u4 (by decide)
    (h3.arrs_keep k4 (by simp) (by simp)) h3.live_lt (h3.vd_keep k4 (by simp) (by simp))
    (h3.mask_keep k4 (by simp))
  rw [show seqs [mulMod aZ aY aX aA m aT] = mulMod aZ aY aX aA m aT from rfl]
  refine WP.mono (mulMod_ok h4.ws (by decide) hmi hk hk' c4) fun t ⟨ht, k5, r5, v5⟩ => ?_
  -- The values `mulMod` starts from.
  have mi := hmi
  obtain ⟨_, _, _, _, _, hmT, _, _, _, hzm, _, _, hym, _, hxm, ham⟩ := mi
  obtain gZ : num t4.mem g.B g.w aZ = 0 := by
    rw [h4.arrs.get (by simp [hz]), upd_ne (j := aA) _ _ (by decide), upd_ne (j := aX) _ _ (by decide),
      upd_ne (j := aY) _ _ (by decide), hA0]
  obtain gA : num t4.mem g.B g.w aA = 0 := by
    rw [h4.arrs.get (by simp), upd_self, upd_ne (j := aX) _ _ (by decide), upd_ne (j := aY) _ _ (by decide), hA0]
  obtain gY : num t4.mem g.B g.w aY = A y := by
    rw [h4.arrs.get (by simp), upd_ne (j := aA) _ _ (by decide), upd_ne (j := aX) _ _ (by decide), upd_self]
  obtain gX : num t4.mem g.B g.w aX = A x := by
    rw [h4.arrs.get (by simp), upd_ne (j := aA) _ _ (by decide), upd_self, upd_ne (j := aY) _ _ hxY]
  obtain gM : num t4.mem g.B g.w m = A m := by
    rw [h4.arrs.get (by simp [hm]), upd_ne (j := aA) _ _ (Ne.symm ham), upd_ne (j := aX) _ _ (Ne.symm hxm),
      upd_ne (j := aY) _ _ (Ne.symm hym)]
  refine ⟨num t.mem g.B g.w aA, fun hlt hM => ?_, ?_⟩
  · rw [gZ, gA, gX, gM, gY] at v5
    rw [v5 rfl (by omega_arith) hlt hM, Nat.zero_add]
  · refine h4.next ht k5 (by decide) (by decide) r5 r4opRegs_body ?_
      (fun j hj => (List.mem_cons.mp hj).elim (fun e => by rw [e]; decide) (h.live_lt j))
      (h4.vd_keep k5 (by decide) (by decide)) (h4.mask_keep k5 (by decide))
    intro j hj'
    by_cases e : j = aA
    · subst e; rw [upd_self]
    · have hj : j ∈ live := (List.mem_cons.mp hj').resolve_left e
      obtain ⟨jY, jX, jn⟩ := free j hj e
      rw [upd_ne _ _ e, k5.num (j := j) (fun i hi ei => jn (by subst ei; exact hi)) (by decide)
          (h.ws.fit64 (h.live_lt j hj)),
        h4.arrs.get (by simp [hj]), upd_ne (j := aA) _ _ e, upd_ne (j := aX) _ _ jX, upd_ne (j := aY) _ _ jY]

/-- `divA len a d`: `[a] / [d]` in `aVQ`, `[a] mod [d]` in `aVR`, for a
divisor of `L` bytes (`L` in `len`). -/
theorem Stg.divA_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {a d : Nat} (ha : a ∈ live) (hd : d ∈ live)
    (hfree : ∀ j ∈ live, j ∉ [aVQ, aVR, aVD, aVT]) {len : Reg} (hlr : len ∉ bodyRegs) (hl12 : len ≠ .r12)
    {L : Nat} (hl : s.gpr len = BitVec.ofNat 64 L) (hL1 : 1 ≤ L) (hL : L < 2 ^ 32) (hlt : A d < 2 ^ (8 * L)) :
    WP isa (seqs (divA len a d)) s fun t => ∃ Xq Xr, (0 < A d → Xr = A a % A d ∧ Xq = A a / A d) ∧
      Stg g s0 (upd (upd A aVQ Xq) aVR Xr) (aVR :: aVQ :: live) c t := by
  obtain aQ : a ≠ aVQ := fun e => hfree a ha (by simp [e])
  obtain dQ : d ≠ aVQ := fun e => hfree d hd (by simp [e])
  obtain dD : d ≠ aVD := fun e => hfree d hd (by simp [e])
  obtain hl0 : len ≠ .r0 := fun e => hlr (by rw [e]; decide)
  unfold divA
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (h.copy_ok (o := aVQ) (a := a) (by decide) ha (Ne.symm aQ)) fun t1 h1 => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (h1.copy_ok (o := aVD) (a := d) (by decide) (List.mem_cons_of_mem _ hd) (Ne.symm dD))
    fun t2 h2 => ?_
  obtain l2 : t2.gpr len = BitVec.ofNat 64 L := by
    rw [h2.regs.gpr _ hlr, ← h.regs.gpr _ hlr]; exact hl
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (WP.keep [.r12] (Q := fun x => x.gpr .r12 = BitVec.ofNat 64 L ∧ x.mem = t2.mem)
    (by prun [l2, exec_addi hl0 (show 0 < 2 ^ 15 by decide), BitVec.add_zero]) (by cases len <;> decide))
    fun t3 ⟨⟨t12, tm⟩, k3⟩ => ?_
  obtain h3ws : Ws t3 g.B g.Z g.w nArr := h2.ws.of_keep k3
  rw [show seqs [VG.Impl.Rsa.PPC64LE.Div.divP aVQ aVR aVD aVT] = VG.Impl.Rsa.PPC64LE.Div.divP aVQ aVR aVD aVT
    from rfl]
  obtain fq : num t3.mem g.B g.w aVQ = A a := by
    rw [tm, h2.arrs.get (by simp), upd_ne (j := aVD) _ _ (by decide), upd_self]
  obtain fd : num t3.mem g.B g.w aVD = A d := by
    rw [tm, h2.arrs.get (by simp), upd_self, upd_ne _ _ dQ]
  refine WP.mono (divP_ok h3ws (q := aVQ) (r := aVR) (d := aVD) (t := aVT) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [tm]; exact h2.vdTop) t12 hL1 hL (by rw [fd]; exact hlt))
    fun t ⟨ht, k, r, v⟩ => ⟨num t.mem g.B g.w aVQ, num t.mem g.B g.w aVR, fun pos => ?_, ?_⟩
  · obtain ⟨vq, vr⟩ := v (by rw [fd]; exact pos)
    rw [fq, fd] at vq vr
    obtain lt : num1 t.mem g.B g.w aVR < 2 ^ (32 * g.w) := by
      rw [vr]
      exact Nat.lt_of_lt_of_le (Nat.mod_lt _ pos) (by rw [← fd]; exact Nat.le_of_lt (val32_lt _ _ _ _))
    exact ⟨(VG.Proof.Rsa.PPC64LE.CrtValues.num_of_num1 lt).trans vr, vq⟩
  · have k' : KeyWorkspace.Keep g.B g.w [aVQ, aVR, aVT] [] t2.mem t.mem := by rw [← tm]; exact k
    refine h2.next ht k' (by decide) (by simp) (k3.trans r) (by decide) ?_ ?_ (h2.vd_keep k' (by decide) (by simp))
      (h2.mask_keep k' (by simp))
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · rw [upd_self]
      rcases List.mem_cons.mp hj with rfl | hj
      · rw [upd_ne _ _ (by decide), upd_self]
      obtain hn := hfree j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
      rw [upd_ne _ _ hn.2.1, upd_ne _ _ hn.1, k'.num (by simp; omega_arith) (by simp)
        (h.ws.fit64 (h.live_lt j hj)), h2.arrs.get (by simp [hj]), upd_ne _ _ hn.2.2.1, upd_ne _ _ hn.1]
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · decide
      rcases List.mem_cons.mp hj with rfl | hj
      · decide
      exact h.live_lt j hj

end VG.Proof.Rsa.PPC64LE.KeyCheck

end

end


/-! # The checks of an RSA key on PPC64LE

As on ARMv7 (`Proof/Rsa/Arm/KcStart.lean`, `KcChecks.lean`, `KcBody.lean`):
from the arrays read (`vals`), `start_ok`: `1`, the mask of `p` odd, `p q mod
2^(32 w)`, `p | 1` and `0` or Montgomery's `n 2^(-32 w) mod (p | 1)`; `crtChecks_ok`:
the checks of `vg_rsa_check_crt_key` and'ed into the mask (`crtBitsM`);
`dChecks_ok`: those of `d` (`keyBitsM`).
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.KeyCheck

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (seqs setOne bitOf sOdd sB sC copy orOne)
open VG.Impl.Rsa.PPC64LE.KeyCheck
open VG.Proof.Rsa.KeyWorkspace (arr S num slot Arrs upd upd_ne upd_self arr_disj)
open VG.Proof.Rsa.PPC64LE.MontKey (mulLo_ok montMul_ok montMulC_ok cntLen_ok mkRegs val32_low)

/-! ## The products

The product truncated to `w` digits (`Stg.mulLo_ok`) and Montgomery's
multiplication modulo `p | 1`, in `aVD` (`Stg.montP_ok`). -/

theorem mkRegs_body : ∀ x ∈ mkRegs, x ∈ bodyRegs := by decide

/-- `orOne j`. -/
theorem Stg.orOne_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {j : Nat} (hj : j ∈ live) :
    WP isa (.block (VG.Impl.Rsa.PPC64LE.Keys.orOne j)) s (Stg g s0 (upd A j (2 * (A j / 2) + 1)) live c) := by
  rw [← List.append_nil (VG.Impl.Rsa.PPC64LE.Keys.orOne j)]
  refine orOne_top_ok h.ws (h.live_lt j hj) (by decide) fun t ht k e r top => WP.block_nil ?_
  refine h.next ht k (by simpa using h.live_lt j hj) (by simp) r KeyCheck.opRegs_body
    (h.arrs_write k (by rw [e, h.arrs.get hj]) (fun i _ => (Decidable.em (i = j)).imp_right fun n => by
      simpa using n) (by simp)) h.live_lt ?_ (h.mask_keep k (by simp))
  by_cases hv : j = aVD
  · subst hv; rw [top, h.vdTop]
  · exact h.vd_keep k (by simpa using hv) (by simp)

/-- `mulLo o x y r19`: `[o] := [x] [y] mod 2^(32 w)`, for `[x] < 2^(8 L)`,
`L = p_len` in `r19`. -/
theorem Stg.mulLo_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {o x y : Nat} (ho : o < nArr) (hx : x ∈ live) (hy : y ∈ live)
    (hfree : ∀ j ∈ live, j ≠ o) (hoVD : o ≠ aVD) {L : Nat} (hl : s.gpr .r19 = BitVec.ofNat 64 L) (hL1 : 1 ≤ L)
    (hLw : L ≤ 4 * g.w) (hxL : A x < 2 ^ (8 * L)) :
    WP isa (VG.Impl.Rsa.PPC64LE.MontKey.mulLo o x y .r19) s
      (Stg g s0 (upd A o (A x * A y % 2 ^ (32 * g.w))) (o :: live) c) := by
  obtain nx := h.live_lt x hx
  obtain ny := h.live_lt y hy
  refine WP.mono (VG.Proof.Rsa.PPC64LE.MontKey.mulLo_ok h.ws (by decide) ho nx ny (fun e => hfree x hx e.symm) (fun e => hfree y hy e.symm)
    hl hL1 hLw (by decide) (by decide)) fun t ⟨ht, k, v, r⟩ => ?_
  obtain vx : val32 s.mem g.B (arr g.w x) ((L + 3) / 4) = A x :=
    val32_low (h.arrs.get hx) (by omega_using [hLw]) (Nat.lt_of_lt_of_le hxL (Nat.pow_le_pow_right (by decide) (by omega_using [])))
  obtain e : num t.mem g.B g.w o = A x * A y % 2 ^ (32 * g.w) := by rw [v, vx, h.arrs.get hy]
  refine h.next ht k (by simpa using ho) (by simp) r mkRegs_body
    ((h.arrs_write k e (fun j hj => .inr (by simpa using hfree j hj)) (by simp)).cons (by rw [upd_self]; exact e))
    (fun j hj => (List.mem_cons.mp hj).elim (fun e => e ▸ ho) (h.live_lt j)) (h.vd_keep k (by simpa using hoVD) (by simp))
    (h.mask_keep k (by simp))

/-- `mulHalf o x y r19`: `[o] := [x] [y]`, for `[x]` and `[y]` below `2^(8 L)`, `L = p_len` in `r19`
with `2 ⌈L / 4⌉ ≤ w`. -/
theorem Stg.mulHalf_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {o x y : Nat} (ho : o < nArr) (hx : x ∈ live) (hy : y ∈ live)
    (hfree : ∀ j ∈ live, j ≠ o) (hoVD : o ≠ aVD) {L : Nat} (hl : s.gpr .r19 = BitVec.ofNat 64 L) (hL1 : 1 ≤ L)
    (hLw : 2 * ((L + 3) / 4) ≤ g.w) (hxL : A x < 2 ^ (8 * L)) (hyL : A y < 2 ^ (8 * L)) :
    WP isa (VG.Impl.Rsa.PPC64LE.MontKey.mulHalf o x y .r19) s
      (Stg g s0 (upd A o (A x * A y % 2 ^ (32 * g.w))) (o :: live) c) := by
  obtain nx := h.live_lt x hx
  obtain ny := h.live_lt y hy
  refine WP.mono (VG.Proof.Rsa.PPC64LE.MontKey.mulHalf_ok h.ws (by decide) ho nx ny (fun e => hfree x hx e.symm)
    (fun e => hfree y hy e.symm) hl hL1 hLw (by decide) (by decide)) fun t ⟨ht, k, v, r⟩ => ?_
  obtain lt : ∀ {X : Nat}, X < 2 ^ (8 * L) → X < 2 ^ (32 * ((L + 3) / 4)) := fun hX =>
    Nat.lt_of_lt_of_le hX (Nat.pow_le_pow_right (by decide) (by omega_using []))
  obtain vx : val32 s.mem g.B (arr g.w x) ((L + 3) / 4) = A x := val32_low (h.arrs.get hx) (by omega_using [hLw]) (lt hxL)
  obtain vy : val32 s.mem g.B (arr g.w y) ((L + 3) / 4) = A y := val32_low (h.arrs.get hy) (by omega_using [hLw]) (lt hyL)
  obtain hlt : A x * A y < 2 ^ (32 * g.w) :=
    calc A x * A y < 2 ^ (32 * ((L + 3) / 4)) * 2 ^ (32 * ((L + 3) / 4)) := Nat.mul_lt_mul'' (lt hxL) (lt hyL)
      _ ≤ 2 ^ (32 * g.w) := by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega_using [hLw])
  obtain e : num t.mem g.B g.w o = A x * A y % 2 ^ (32 * g.w) := by rw [v, vx, vy, Nat.mod_eq_of_lt hlt]
  refine h.next ht k (by simpa using ho) (by simp) r mkRegs_body
    ((h.arrs_write k e (fun j hj => .inr (by simpa using hfree j hj)) (by simp)).cons (by rw [upd_self]; exact e))
    (fun j hj => (List.mem_cons.mp hj).elim (fun e => e ▸ ho) (h.live_lt j)) (h.vd_keep k (by simpa using hoVD) (by simp))
    (h.mask_keep k (by simp))

/-- `mulLo o x y len`, the length of `[x]` in `len`. -/
theorem Stg.mulLoR_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {o x y : Nat} (ho : o < nArr) (hx : x ∈ live) (hy : y ∈ live)
    (hfree : ∀ j ∈ live, j ≠ o) (hoVD : o ≠ aVD) {len : Reg} (hr : len ∉ [.r5, .r8, .r10]) (hl0 : len ≠ .r0) {L : Nat}
    (hl : s.gpr len = BitVec.ofNat 64 L) (hL1 : 1 ≤ L) (hLw : L ≤ 4 * g.w) (hxL : A x < 2 ^ (8 * L)) :
    WP isa (VG.Impl.Rsa.PPC64LE.MontKey.mulLo o x y len) s
      (Stg g s0 (upd A o (A x * A y % 2 ^ (32 * g.w))) (o :: live) c) := by
  obtain nx := h.live_lt x hx
  obtain ny := h.live_lt y hy
  refine WP.mono (VG.Proof.Rsa.PPC64LE.MontKey.mulLo_ok h.ws (by decide) ho nx ny (fun e => hfree x hx e.symm)
    (fun e => hfree y hy e.symm) hl hL1 hLw hr hl0) fun t ⟨ht, k, v, r⟩ => ?_
  obtain vx : val32 s.mem g.B (arr g.w x) ((L + 3) / 4) = A x :=
    val32_low (h.arrs.get hx) (by omega_using [hLw]) (Nat.lt_of_lt_of_le hxL (Nat.pow_le_pow_right (by decide) (by omega_using [])))
  obtain e : num t.mem g.B g.w o = A x * A y % 2 ^ (32 * g.w) := by rw [v, vx, h.arrs.get hy]
  refine h.next ht k (by simpa using ho) (by simp) r mkRegs_body
    ((h.arrs_write k e (fun j hj => .inr (by simpa using hfree j hj)) (by simp)).cons (by rw [upd_self]; exact e))
    (fun j hj => (List.mem_cons.mp hj).elim (fun e => e ▸ ho) (h.live_lt j)) (h.vd_keep k (by simpa using hoVD) (by simp))
    (h.mask_keep k (by simp))

/-- `montP a x y`: `[a] := [x] [y] 2^(-32 w) mod (p | 1)`, the modulus in
`aVD`: for `[y] < (p | 1)`, below it and congruent. -/
theorem Stg.montP_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {a x y : Nat} (ha : a < nArr) (hx : x ∈ live) (hy : y ∈ live) (hVD : aVD ∈ live)
    (hfree : ∀ j ∈ live, j ≠ a ∧ j ≠ aT) (haT : a ≠ aT) (hyVD : aVD ≠ y) {L : Nat} (hl : s.gpr .r19 = BitVec.ofNat 64 L)
    (hL1 : 1 ≤ L) (hLw : (L + 3) / 4 ≤ g.w) (hodd : A aVD % 2 = 1) (hmt : A aVD < 2 ^ (32 * ((L + 3) / 4)))
    (hYt : A y < 2 ^ (32 * ((L + 3) / 4))) :
    WP isa (montP a x y) s fun t => ∃ R, (A y < A aVD → R < A aVD ∧
      R * 2 ^ (32 * g.w) % A aVD = A x * A y % A aVD) ∧ Stg g s0 (upd A a R) (a :: live) c t := by
  obtain nx := h.live_lt x hx
  obtain ny := h.live_lt y hy
  obtain nm := h.live_lt aVD hVD
  obtain hax : a ≠ x := fun e => (hfree x hx).1 e.symm
  obtain hay : a ≠ y := fun e => (hfree y hy).1 e.symm
  obtain ham : a ≠ aVD := fun e => (hfree aVD hVD).1 e.symm
  obtain htx : aT ≠ x := fun e => (hfree x hx).2 e.symm
  obtain hty : aT ≠ y := fun e => (hfree y hy).2 e.symm
  refine WP.mono (montMul_ok h.ws (by decide) ha nx ny nm (by decide) hax hay ham haT
    htx hty (by decide) hyVD hl hL1 hLw (by decide) (by decide) (h.arrs.get hVD) hmt hodd (h.arrs.get hy) hYt)
    fun t ⟨ht, k, nmv, nY, top, cg, r⟩ => ⟨num t.mem g.B g.w a, fun hlt => by
      have := cg hlt; rw [h.arrs.get hx] at this; exact this, ?_⟩
  obtain hnl : ∀ j ∈ [a, aT, aVD, y], j < nArr := by
    intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl
    · exact ha
    · decide
    · exact nm
    · exact ny
  refine h.next ht k hnl (by simp) r mkRegs_body ?_ ?_ top (h.mask_keep k (by simp))
  · intro j hj
    rcases List.mem_cons.mp hj with rfl | hj'
    · rw [upd_self]
    · obtain ⟨hja, hjt⟩ := hfree j hj'
      rw [upd_ne _ _ hja]
      by_cases e1 : j = aVD
      · subst e1; exact nmv
      · by_cases e2 : j = y
        · subst e2; exact nY
        · rw [k.num (by
            intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
            rcases hz with rfl | rfl | rfl | rfl <;> omega_arith) (by simp) (h.ws.fit64 (h.live_lt j hj')),
            h.arrs.get hj']
  · intro j hj
    rcases List.mem_cons.mp hj with rfl | hj'
    · exact ha
    · exact h.live_lt j hj'

/-- `montPq a x y`: `[a] := [x] [y] 2^(-32 c) mod (p | 1)`, `c = ⌈Q / 4⌉`
for `Q` in `r21`, `[x] < 2^(32 c)`: for `[y] < (p | 1)`, below it and
congruent. -/
theorem Stg.montPq_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {a x y : Nat} (ha : a < nArr) (hx : x ∈ live) (hy : y ∈ live) (hVD : aVD ∈ live)
    (hfree : ∀ j ∈ live, j ≠ a ∧ j ≠ aT) (haT : a ≠ aT) (hyVD : aVD ≠ y) {L : Nat} (hl : s.gpr .r19 = BitVec.ofNat 64 L)
    (hL1 : 1 ≤ L) (hLw : (L + 3) / 4 ≤ g.w) (hodd : A aVD % 2 = 1) (hmt : A aVD < 2 ^ (32 * ((L + 3) / 4)))
    (hYt : A y < 2 ^ (32 * ((L + 3) / 4))) {Q : Nat} (hq : s.gpr .r21 = BitVec.ofNat 64 Q) (hQ1 : 1 ≤ Q)
    (hQw : (Q + 3) / 4 ≤ g.w) (hQ32 : Q < 2 ^ 32) (hX : A x < 2 ^ (32 * ((Q + 3) / 4))) :
    WP isa (montPq a x y) s fun t => ∃ R, (A y < A aVD → R < A aVD ∧
      R * 2 ^ (32 * ((Q + 3) / 4)) % A aVD = A x * A y % A aVD) ∧ Stg g s0 (upd A a R) (a :: live) c t := by
  obtain nx := h.live_lt x hx
  obtain ny := h.live_lt y hy
  obtain nm := h.live_lt aVD hVD
  obtain hax : a ≠ x := fun e => (hfree x hx).1 e.symm
  obtain hay : a ≠ y := fun e => (hfree y hy).1 e.symm
  obtain ham : a ≠ aVD := fun e => (hfree aVD hVD).1 e.symm
  obtain htx : aT ≠ x := fun e => (hfree x hx).2 e.symm
  obtain hty : aT ≠ y := fun e => (hfree y hy).2 e.symm
  refine WP.mono (montMulC_ok h.ws (by decide) ha nx ny nm (by decide) hax hay ham haT
    htx hty (by decide) hyVD hl hL1 hLw (by decide) (by decide) (h.arrs.get hVD) hmt hodd (h.arrs.get hy) hYt
    (c := (Q + 3) / 4) (by omega_using [hQ1]) hQw (by rw [h.arrs.get hx]; exact hX)
    fun u ku _ => cntLen_ok (by decide) ((ku.gpr _ (by decide)).trans hq) hQ32)
    fun t ⟨ht, k, nmv, nY, top, cg, r⟩ => ⟨num t.mem g.B g.w a, fun hlt => by
      have := cg hlt; rw [h.arrs.get hx] at this; exact this, ?_⟩
  obtain hnl : ∀ j ∈ [a, aT, aVD, y], j < nArr := by
    intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl
    · exact ha
    · decide
    · exact nm
    · exact ny
  refine h.next ht k hnl (by simp) r mkRegs_body ?_ ?_ top (h.mask_keep k (by simp))
  · intro j hj
    rcases List.mem_cons.mp hj with rfl | hj'
    · rw [upd_self]
    · obtain ⟨hja, hjt⟩ := hfree j hj'
      rw [upd_ne _ _ hja]
      by_cases e1 : j = aVD
      · subst e1; exact nmv
      · by_cases e2 : j = y
        · subst e2; exact nY
        · rw [k.num (by
            intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
            rcases hz with rfl | rfl | rfl | rfl <;> omega_arith) (by simp) (h.ws.fit64 (h.live_lt j hj')),
            h.arrs.get hj']
  · intro j hj
    rcases List.mem_cons.mp hj with rfl | hj'
    · exact ha
    · exact h.live_lt j hj'

/-! ## The checks -/


/-- The arrays the checks start from. -/
abbrev live0 : List Nat := [aZ, aOne, aN, aE, aP, aQ, aDP, aDQ, aQI, aD]

/-- The arrays after `start`: `p q mod 2^(32 w)` in `aVQ`, `p | 1` in `aVD` and
Montgomery's `n` in `aVR`. -/
abbrev aStart (v : Vals) (L M : Nat) : Nat → Nat :=
  upd (upd (upd (upd (vals v) aOne 1) aVQ L) aVD (2 * (v.p / 2) + 1)) aVR M
abbrev liveS : List Nat := aVR :: aVD :: aVQ :: live0

/-- The arrays the checks of `d` use. -/
abbrev aFin (v : Vals) : Nat → Nat := upd (upd (vals v) aM1 (2 * (v.p / 2))) aM2 (2 * (v.q / 2))
abbrev liveFin : List Nat := [aZ, aN, aD, aDP, aDQ, aM1, aM2]

theorem mulIdx_m1 : MulIdx nArr aZ aY aX aA aM1 aT := by decide
theorem mulIdx_m2 : MulIdx nArr aZ aY aX aA aM2 aT := by decide
theorem mulIdx_p : MulIdx nArr aZ aY aX aA aP aT := by decide

theorem mask_mod2 (x : Nat) : x % 2 = if decide (x % 2 = 1) then 1 else 0 := by
  rcases Nat.mod_two_eq_zero_or_one x with e | e <;> simp [e]

/-- `p | 1` is odd, and below `2^(8 a)` with `p`. -/
theorem or1_lt {p a : Nat} (h : p < 2 ^ (8 * a)) (ha : 1 ≤ a) : 2 * (p / 2) + 1 < 2 ^ (8 * a) := by
  have : 2 ^ (8 * a) = 2 * 2 ^ (8 * a - 1) := by rw [← Nat.pow_succ']; congr 1; omega_using [ha]
  omega_using [h, this]

theorem pow8_le (a : Nat) : 2 ^ (8 * a) ≤ 2 ^ (32 * ((a + 3) / 4)) :=
  Nat.pow_le_pow_right (by decide) (by omega_using [])

/-- `p | 1` is `p` for an odd `p`. -/
theorem or1_odd {p : Nat} (h : p % 2 = 1) : 2 * (p / 2) + 1 = p := by omega_using [h]

/-- `shape`: `r0 = 0` exactly for `Shape`. -/
theorem shape_ok {s : State} {w pL qL : Nat} (hw : s.gpr .r29 = BitVec.ofNat 64 w) (hp : s.gpr .r19 = BitVec.ofNat 64 pL)
    (hq : s.gpr .r21 = BitVec.ofNat 64 qL) (hw' : w < 2 ^ 32) (hp' : pL < 2 ^ 32) (hq' : qL < 2 ^ 32) :
    WP isa (.block shape) s fun t => (t.gpr .r0 = 0 ↔ Shape w pL qL) ∧ t.mem = s.mem ∧ Keep [.r0, .r3, .r12] s t := by
  refine WP.mono (WP.keep [.r0, .r3, .r12] (Q := fun t => (t.gpr .r0 = 0 ↔ Shape w pL qL) ∧ t.mem = s.mem) (by
    unfold shape
    prun [hw, hp, hq]
    exact shape_bits hw' hp' hq') (by decide)) fun t ⟨⟨h0, hm⟩, k'⟩ => ⟨h0, hm, k'⟩

/-- An array tracked by its value. -/
theorem Stg.addLive {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {j : Nat} (hj : j < nArr) :
    Stg g s0 (upd A j (num s.mem g.B g.w j)) (j :: live) c s :=
  { h with
    arrs := fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · rw [upd_self]
      · by_cases e : x = j
        · subst e; rw [upd_self]
        · rw [upd_ne _ _ e]; exact h.arrs x hx
    live_lt := fun x hx => (List.mem_cons.mp hx).elim (fun e => e ▸ hj) (h.live_lt x) }

/-- `[r] := [a] mod [d]` by words: `[d]` copied to `[m]`, its top word made not
zero, then `KeyDiv.divW` through `[t]` and the save area `[sv]`; exact when
`[d]`'s top word (of `w / 4`) is not zero. -/
theorem Stg.divCopy_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {a d r m t sv : Nat} (ha : a ∈ live) (hd : d ∈ live)
    (hr : r < nArr) (hm : m < nArr) (ht : t < nArr) (hsv : sv < nArr)
    (hfree : ∀ j ∈ live, j ∉ [r, m, t, sv]) (hrm : r ≠ m) (hrt : r ≠ t) (hrsv : r ≠ sv) (hmt : m ≠ t)
    (hmsv : m ≠ sv) (htsv : t ≠ sv) (hrV : r ≠ aVD) (htV : t ≠ aVD) (hsvV : sv ≠ aVD)
    (hw : g.w = 4 * (g.w / 4)) (hw16 : 16 ≤ g.w) (hlt : A d < 2 ^ (64 * (g.w / 4)))
    {top : Option Nat} (hk : ∀ k, top = some k → k ≤ g.w / 4)
    (hXa : A a < 2 ^ (64 * VG.Proof.Rsa.PPC64LE.KeyDiv.xw (g.w / 4) top)) :
    WP isa (seqs [copy m d, .block (VG.Impl.Rsa.PPC64LE.KeyDiv.fixTop m),
      VG.Impl.Rsa.PPC64LE.KeyDiv.divW a r m t sv top]) s fun u => ∃ Xr,
      (2 ^ (64 * (g.w / 4 - 1)) ≤ A d → Xr = A a % A d) ∧ Stg g s0 (upd A r Xr) (r :: live) c u := by
  obtain aR : a ≠ r := fun e => hfree a ha (by simp [e])
  obtain aM : a ≠ m := fun e => hfree a ha (by simp [e])
  obtain aT : a ≠ t := fun e => hfree a ha (by simp [e])
  obtain aS : a ≠ sv := fun e => hfree a ha (by simp [e])
  obtain dM : d ≠ m := fun e => hfree d hd (by simp [e])
  have := h.ws.wle
  have hnw := h.ws.nowrap
  obtain fD := h.ws.fit64 (show aVD < nArr by decide)
  obtain fM := h.ws.fit64 hm
  simp only [S] at fD fM
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (h.copy_ok (o := m) (a := d) hm hd (Ne.symm dM)) fun s2 h2 => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (VG.Proof.Rsa.PPC64LE.KeyDiv.fixTop_ok h2.ws (m := m) hm (by decide) hw (by omega_using [hw16]))
    fun s3 ⟨m3, w3, k3⟩ => ?_
  obtain hd2 : num s2.mem g.B g.w m = A d := by rw [h2.arrs.get (by simp), upd_self]
  obtain hdv : wordsVal s2.mem g.B (arr g.w m) (g.w / 4) = A d := by
    rw [wordsVal_eq_val32]
    exact VG.Proof.Rsa.PPC64LE.MontKey.val32_low hd2 (by omega_using [])
      (by rw [show 32 * (2 * (g.w / 4)) = 64 * (g.w / 4) by omega_using []]; exact hlt)
  obtain ft := VG.Proof.Rsa.PPC64LE.KeyDiv.fixTop_val (mem := s2.mem) (B := g.B) (d := arr g.w m)
    (wd := g.w / 4) (by omega_using [hw16]) (by omega_using [fM])
  rw [← m3] at ft
  obtain ⟨hT, hfix⟩ := ft
  obtain o3 : Outside g.B (arr g.w m + 8 * (g.w / 4 - 1)) 8 s2.mem s3.mem := by
    rw [m3]; exact writeW_outside _ g.B _ (by omega_using [fM])
  obtain kD : KeyWorkspace.Keep g.B g.w [m] [] s2.mem s3.mem :=
    KeyWorkspace.Keep.of_arr (o := m) o3 (by simp only [S]; omega_using []) (by simp)
  obtain ha3 : num s3.mem g.B g.w a = A a := by
    rw [kD.num (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact Ne.symm aM)
      (by simp) (h.ws.fit64 (h.live_lt a ha)), h2.arrs.get (by simp [ha]), upd_ne _ _ aM]
  rw [show ∀ x : Prog isa, seqs [x] = x from fun _ => rfl]
  obtain hX3 : wordsVal s3.mem g.B (arr g.w a) (2 * (g.w / 4)) < 2 ^ (64 * VG.Proof.Rsa.PPC64LE.KeyDiv.xw (g.w / 4) top) := by
    rw [wordsVal_eq_val32, show 2 * (2 * (g.w / 4)) = g.w by omega_using [hw]]
    show num s3.mem g.B g.w a < _
    rw [ha3]; exact hXa
  refine WP.mono (VG.Proof.Rsa.PPC64LE.KeyDiv.divWAt_ok w3 (h.live_lt a ha) hr hm ht hsv aR aT aS hrm hrt hrsv
    hmt hmsv htsv (by decide) hw (by omega_using [hw16]) hk hT) fun u ⟨tr, hu, ku, mu⟩ =>
      ⟨num u.mem g.B g.w r, fun hb => by rw [tr hX3, ha3, hfix (by rw [hdv]; exact hb), hdv], ?_⟩
  obtain k : KeyWorkspace.Keep g.B g.w [m, r, t, sv] [] s2.mem u.mem :=
    (kD.mono (by simp) (by simp)).trans (mu.mono (by simp) (by simp))
  refine h2.next hu k (by simp; omega_using [hr, hm, ht, hsv, hrm, hrt, hrsv, hmt, hmsv, htsv, hrV, htV, hsvV, aR, aM, aT, aS, dM]) (by simp) (k3.trans ku) (by decide) ?_ ?_ ?_ (h2.mask_keep k (by simp))
  · intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · rw [upd_self]
    obtain hn := hfree j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    rw [upd_ne _ _ hn.1, k.num (by simp; omega_using [hr, hm, ht, hsv, hrm, hrt, hrsv, hmt, hmsv, htsv, hrV, htV, hsvV, aR, aM, aT, aS, dM, hn]) (by simp) (h.ws.fit64 (h.live_lt j hj)),
      h2.arrs.get (by simp [hj]), upd_ne _ _ hn.2.1]
  · intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact hr
    exact h.live_lt j hj
  · have v3 : w32 s3.mem g.B (arr g.w aVD + 4 * g.w) = 0 := by
      obtain dd : arr g.w aVD + 4 * g.w + 4 ≤ arr g.w m + 8 * (g.w / 4 - 1) ∨
          arr g.w m + 8 * (g.w / 4 - 1) + 8 ≤ arr g.w aVD + 4 * g.w := by
        by_cases e : m = aVD
        · subst e; omega_using [hw16]
        · have := arr_disj (w := g.w) e; simp only [S] at this; omega_using [this]
      rw [o3.w32 dd (by omega_using [fD])]; exact h2.vdTop
    rw [← v3]
    exact congrArg BitVec.toNat (VG.Proof.Rsa.PPC64LE.InvBatch.keep_word mu (b := 32) (o := 4 * g.w)
      (by simp only [S]; omega_using []) (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        exacts [hrV, htV, hsvV]) (fun d hd => absurd hd (by simp)) fD)

/-- `start`: `1`, the mask of `p` odd, `p q mod 2^(32 w)`, `p | 1` and, for
a balanced key, `0`, else Montgomery's `n` modulo `p | 1`: either is `0`
exactly when `p ∣ n`, where `p q mod 2^(32 w) = n`. -/
theorem start_ok {g : Geo} {s0 : State} {v : Vals} (hw : Ws s0 g.B g.Z g.w nArr)
    (ha : Arrs s0.mem g.B g.w (vals v) live0) (vd : w32 s0.mem g.B (arr g.w aVD + 4 * g.w) = 0)
    {pa qa : Nat} (pa1 : 1 ≤ pa) (paw : pa ≤ 4 * g.w) (plt : v.p < 2 ^ (8 * pa))
    (p19 : s0.gpr .r19 = BitVec.ofNat 64 pa) (qa2 : qa < 2 ^ 32) (qlt : v.q < 2 ^ (8 * qa))
    (q21 : s0.gpr .r21 = BitVec.ofNat 64 qa) :
    WP isa (seqs start) s0 fun t => ∃ L M, L = v.p * v.q % 2 ^ (32 * g.w) ∧
      (v.p % 2 = 1 → 2 ≤ v.p → L = v.n → (Shape g.w pa qa → 2 ^ (64 * (g.w / 4 - 1)) ≤ v.p) →
        (M = 0 ↔ v.n % v.p = 0)) ∧
      Stg g s0 (aStart v L M) liveS (decide (v.p % 2 = 1)) t := by
  obtain fit : ∀ j < nArr, arr g.w j + S g.w ≤ 2 ^ 64 := fun j hj => hw.fit64 hj
  rw [start, wp_seqs_cons (by simp)]
  refine setOne_ok hw (j := aOne) (by decide) (by decide) fun t1 h1 k1 e1 r1 => ?_
  rw [← List.append_nil (bitOf sMask aP)]
  refine bitOf_ok h1 (j := aP) (sl := sMask) (by decide) (by decide) (by decide)
    fun t2 h2 k2 e2 r2 => WP.block_nil ?_
  obtain o1 : num s0.mem g.B g.w aOne = 0 := by rw [ha.get (by decide)]; rfl
  obtain p1 : num t1.mem g.B g.w aP = v.p := by
    rw [k1.num (by decide) (by simp) (fit _ (by decide)), ha.get (by decide)]; rfl
  obtain hl0 : ∀ j ∈ live0, j < nArr := by decide
  obtain g2 : Stg g s0 (upd (vals v) aOne 1) live0 (decide (v.p % 2 = 1)) t2 := by
    refine ⟨h2, ?_, (r1.trans r2).mono, ?_, ?_, ?_, ?_⟩
    · exact (k1.mono (js' := List.range nArr) (ds' := bodySlots)
        (fun j hj => by rw [List.mem_singleton.mp hj]; decide) (by simp)).trans
        (k2.mono (js' := List.range nArr) (ds' := bodySlots) (by simp) (by decide))
    · intro j hj
      by_cases e : j = aOne
      · subst e
        rw [upd_self, k2.num (by simp) (by simp; decide) (fit _ (by decide)), e1, o1]
      · have hjn : j < nArr := hl0 j hj
        rw [upd_ne _ _ e, k2.num (by simp) (by simp; decide) (fit _ hjn),
          k1.num (fun k hk ek => e (by rw [List.mem_singleton.mp hk] at ek; exact ek.symm)) (by simp)
            (fit _ hjn), ha.get hj]
    · exact hl0
    · rw [k2.word (by simp only [S]; omega_using []) (by simp) (by simp; decide) (fit _ (by decide)),
        k1.word (by simp only [S]; omega_using []) (by simp; decide) (by simp) (fit _ (by decide)), vd]
    · rw [e2, p1]; exact mask_mod2 v.p
  obtain r19 : ∀ {t : State} {A live c}, Stg g s0 A live c t → t.gpr .r19 = BitVec.ofNat 64 pa :=
    fun h => (h.regs.gpr _ (by decide)).trans p19
  -- The guard.
  rw [wp_seqs_cons (by simp)]
  have := hw.wle
  obtain pa32 : pa < 2 ^ 32 := by omega_using [paw, this]
  refine WP.mono (shape_ok (g2.ws.r29) (r19 g2) ((g2.regs.gpr _ (by decide)).trans q21) (by omega_using [this]) pa32 qa2)
    fun s4 ⟨z4, m4, k4⟩ => ?_
  obtain g4 := g2.next (g2.ws.of_keep k4) (js := []) (ds := []) (by rw [m4]; exact KeyWorkspace.Keep.refl _ _ _ _ _)
    (by simp) (by simp) k4 (by decide) (by rw [m4]; exact g2.arrs) g2.live_lt (by rw [m4]; exact g2.vdTop)
    (by rw [m4]; exact g2.mask)
  rw [show ∀ x : Prog isa, seqs [x] = x from fun _ => rfl]
  refine WP.ite (s4.gpr .r0 == 0) (eval_zero s4 .r0) (fun hz => ?_) (fun hz => ?_)
  · -- `0`: with `p q` exact, `p q mod 2^(32 w) = n` gives `n mod p = 0`.
    obtain ⟨p8, hpw, hpq, p32⟩ := z4.1 (by simpa using hz)
    -- `p q`, over the primes' `w / 2` digits.
    rw [wp_seqs_cons (by simp)]
    refine WP.mono (g4.mulHalf_ok (o := aVQ) (x := aP) (y := aQ) (by decide) (by decide) (by decide) (by decide)
      (by decide) (r19 g4) pa1 (by omega_using [p8, hpw]) (by rw [upd_ne _ _ (by decide)]; exact plt)
      (by rw [upd_ne _ _ (by decide)]; rw [show 8 * pa = 8 * qa by omega_using [hpq]]; exact qlt)) fun t3 g3 => ?_
    rw [wp_seqs_cons (by simp)]
    refine WP.mono (g3.copy_ok (o := aVR) (a := aZ) (by decide) (by decide) (by decide)) fun s5 g5 => ?_
    rw [wp_seqs_cons (by simp)]
    refine WP.mono (g5.copy_ok (o := aVD) (a := aP) (by decide) (by decide) (by decide)) fun s6 g6 => ?_
    rw [show ∀ x : Prog isa, seqs [x] = x from fun _ => rfl]
    refine WP.mono (g6.orOne_ok (j := aVD) (by decide)) fun t g7 => ⟨v.p * v.q % 2 ^ (32 * g.w), 0, rfl,
      fun _ _ hL _ => ?_, ?_⟩
    · have hlt : v.p * v.q < 2 ^ (32 * g.w) :=
        calc v.p * v.q < 2 ^ (8 * pa) * 2 ^ (8 * qa) := Nat.mul_lt_mul'' plt qlt
          _ = 2 ^ (32 * g.w) := by rw [← Nat.pow_add]; congr 1; omega_using [hpw, hpq]
      rw [Nat.mod_eq_of_lt hlt] at hL
      rw [← hL, Nat.mul_mod_right]
    refine (g7.sub (live' := liveS) (by decide)).congr' fun j hj => ?_
    simp only [liveS, live0, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · -- `p q mod 2^(32 w)`, then Montgomery's `n`.
    rw [wp_seqs_cons (by simp)]
    refine WP.mono (g4.mulLo_ok (o := aVQ) (x := aP) (y := aQ) (by decide) (by decide) (by decide) (by decide)
      (by decide) (r19 g4) pa1 paw (by rw [upd_ne _ _ (by decide)]; exact plt)) fun t3 g3 => ?_
    rw [wp_seqs_cons (by simp)]
    refine WP.mono (g3.copy_ok (o := aVD) (a := aP) (by decide) (by decide) (by decide)) fun t4 g4' => ?_
    rw [wp_seqs_cons (by simp)]
    refine WP.mono (g4'.orOne_ok (j := aVD) (by decide)) fun t5 g5 => ?_
    obtain hm := or1_lt plt pa1
    refine WP.mono (g5.montP_ok (a := aVR) (x := aN) (y := aOne) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (r19 g5) pa1 (by omega_using [paw]) (by show (2 * (v.p / 2) + 1) % 2 = 1; omega_using [])
      (by show 2 * (v.p / 2) + 1 < _; exact Nat.lt_of_lt_of_le hm (pow8_le pa))
      (by show 1 < _; exact Nat.one_lt_two_pow (by omega_using [pa1]))) fun t ⟨M, hM, g6⟩ => ?_
    refine ⟨v.p * v.q % 2 ^ (32 * g.w), M, rfl, fun podd p2 _ _ => ?_, g6.congr' fun j hj => ?_⟩
    · have hM' : 1 < 2 * (v.p / 2) + 1 → M < 2 * (v.p / 2) + 1 ∧
          M * 2 ^ (32 * g.w) % (2 * (v.p / 2) + 1) = v.n * 1 % (2 * (v.p / 2) + 1) := hM
      obtain e1 : 2 * (v.p / 2) + 1 = v.p := or1_odd podd
      rw [e1, Nat.mul_one] at hM'
      obtain ⟨Mlt, Mc⟩ := hM' (by omega_using [p2])
      exact VG.Proof.Rsa.mont_zero_iff podd Mlt Mc
    · simp only [live0, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- `shape` and `qInvMod`: `[aA]` and `[aY]` equal exactly when `q qInv ≡ 1 (mod p)`,
for an odd `p ≥ 2`, `qInv < p`, and, for a balanced key, `p`'s top word not zero. -/
theorem Stg.qInv_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) (hQ : aQ ∈ live) (hQI : aQI ∈ live) (hP : aP ∈ live) (hO : aOne ∈ live)
    (hV : aVD ∈ live) (hfree : ∀ j ∈ live, j ∉ [aA, aY, aX, aVT, aW, aT])
    (o1 : A aOne = 1) (vd : A aVD = 2 * (A aP / 2) + 1)
    {pa qa : Nat} (pa1 : 1 ≤ pa) (paw : pa ≤ 4 * g.w) (qa1 : 1 ≤ qa) (qaw : qa ≤ 4 * g.w) (qa2 : qa < 2 ^ 32)
    (p19 : s0.gpr .r19 = BitVec.ofNat 64 pa) (q21 : s0.gpr .r21 = BitVec.ofNat 64 qa)
    (plt : A aP < 2 ^ (8 * pa)) (qlt : A aQ < 2 ^ (8 * qa)) (ilt : A aQI < 2 ^ (8 * pa)) :
    WP isa (seqs [.block shape, qInvMod]) s fun t => ∃ A₁ A₂,
      (A aQI < A aP → A aP % 2 = 1 → 2 ≤ A aP → (Shape g.w pa qa → 2 ^ (64 * (g.w / 4 - 1)) ≤ A aP) →
        (A₁ = A₂ ↔ A aQ * A aQI % A aP = 1)) ∧
      Stg g s0 (upd (upd A aA A₁) aY A₂) (aA :: aY :: live) c t := by
  have := h.ws.wle
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (shape_ok h.ws.r29 ((h.regs.gpr _ (by decide)).trans p19)
    ((h.regs.gpr _ (by decide)).trans q21) (by omega_using [this]) (by omega_using [paw, this]) qa2) fun s1 ⟨z1, m1, k1⟩ => ?_
  obtain h1 : Stg g s0 A live c s1 :=
    h.next (h.ws.of_keep k1) (js := []) (ds := []) (by rw [m1]; exact KeyWorkspace.Keep.refl _ _ _ _ _)
      (by simp) (by simp) k1 (by decide) (by rw [m1]; exact h.arrs) h.live_lt (by rw [m1]; exact h.vdTop)
      (by rw [m1]; exact h.mask)
  obtain r19 : ∀ {t : State} {A live c}, Stg g s0 A live c t → t.gpr .r19 = BitVec.ofNat 64 pa :=
    fun h' => (h'.regs.gpr _ (by decide)).trans p19
  obtain r21 : ∀ {t : State} {A live c}, Stg g s0 A live c t → t.gpr .r21 = BitVec.ofNat 64 qa :=
    fun h' => (h'.regs.gpr _ (by decide)).trans q21
  obtain nf : ∀ j, j ∈ [aA, aY, aX, aVT, aW, aT] → j ∉ live := fun j hj hl => hfree j hl hj
  rw [show ∀ x : Prog isa, seqs [x] = x from fun _ => rfl]
  refine WP.ite (s1.gpr .r0 == 0) (eval_zero s1 .r0) (fun hz => ?_) (fun hz => ?_)
  · -- By words: `q qInv` exactly, modulo `p`.
    obtain ⟨p8, hpw, hpq, p32⟩ := z1.1 (by simpa using hz)
    rw [show [VG.Impl.Rsa.PPC64LE.MontKey.mulHalf aX aQ aQI .r19, copy aY aP, Code.block (VG.Impl.Rsa.PPC64LE.KeyDiv.fixTop aY),
        VG.Impl.Rsa.PPC64LE.KeyDiv.divW aX aA aY aVT aW, copy aY aOne] =
      [VG.Impl.Rsa.PPC64LE.MontKey.mulHalf aX aQ aQI .r19] ++ ([copy aY aP, Code.block (VG.Impl.Rsa.PPC64LE.KeyDiv.fixTop aY),
        VG.Impl.Rsa.PPC64LE.KeyDiv.divW aX aA aY aVT aW] ++ [copy aY aOne]) from rfl,
      wp_seqs_append (by simp) (by simp), show ∀ x : Prog isa, seqs [x] = x from fun _ => rfl]
    refine WP.mono (h1.mulHalf_ok (o := aX) (x := aQ) (y := aQI) (by decide) hQ hQI
      (fun j hj e => nf aX (by simp) (e ▸ hj)) (by decide) (r19 h1) pa1 (by omega_using [p8, hpw])
      (by rw [hpq]; exact qlt) ilt) fun s2 g2 => ?_
    rw [wp_seqs_append (by simp) (by simp)]
    obtain hX : upd A aX (A aQ * A aQI % 2 ^ (32 * g.w)) aX = A aQ * A aQI := by
      rw [upd_self, Nat.mod_eq_of_lt]
      calc A aQ * A aQI < 2 ^ (8 * qa) * 2 ^ (8 * pa) := Nat.mul_lt_mul'' qlt ilt
        _ = 2 ^ (32 * g.w) := by rw [← Nat.pow_add]; congr 1; omega_using [hpw, hpq]
    refine WP.mono (g2.divCopy_ok (a := aX) (d := aP) (r := aA) (m := aY) (t := aVT) (sv := aW)
      (by simp) (by simp [hP]) (by decide) (by decide) (by decide) (by decide)
      (fun j hj => by
        rcases List.mem_cons.mp hj with rfl | hj
        · decide
        · exact fun hm => hfree j hj (by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
            rcases hm with e | e | e | e <;> simp [e]))
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by omega_using [p8, hpw]) (by omega_using [hpw, p32])
      (by rw [upd_ne _ _ (by decide), show 64 * (g.w / 4) = 8 * pa by omega_using [p8, hpw]]; exact plt) (top := none)
      (fun _ e => nomatch e)
      (by rw [hX]; simp only [VG.Proof.Rsa.PPC64LE.KeyDiv.xw]
          calc A aQ * A aQI < 2 ^ (8 * qa) * 2 ^ (8 * pa) := Nat.mul_lt_mul'' qlt ilt
            _ = 2 ^ (64 * (2 * (g.w / 4))) := by rw [← Nat.pow_add]; congr 1; omega_using [p8, hpw, hpq]))
      fun s3 ⟨Xr, hX3, g3⟩ => ?_
    refine WP.mono (g3.copy_ok (o := aY) (a := aOne) (by decide) (by simp [hO]) (by decide)) fun t g4 =>
      ⟨Xr, 1, fun _ _ p2 ht => ?_, ?_⟩
    · have hb : 2 ^ (64 * (g.w / 4 - 1)) ≤ upd A aX (A aQ * A aQI % 2 ^ (32 * g.w)) aP := ht ⟨p8, hpw, hpq, p32⟩
      rw [hX3 hb, hX, show upd A aX (A aQ * A aQI % 2 ^ (32 * g.w)) aP = A aP from upd_ne _ _ (by decide)]
    · refine (g4.sub (live' := aA :: aY :: live) (fun j hj => by
        simp only [List.mem_cons] at hj ⊢; rcases hj with e | e | e <;> simp [e])).congr' fun j hj => ?_
      by_cases e1 : j = aY
      · subst e1; rw [upd_self, upd_self, upd_ne _ _ (by decide), upd_ne _ _ (by decide), o1]
      · by_cases e2 : j = aA
        · subst e2; rw [upd_ne _ _ (by decide), upd_self, upd_ne _ _ (by decide), upd_self]
        · have hj' : j ∈ live := by
            rcases List.mem_cons.mp hj with e | hj
            · exact absurd e e2
            rcases List.mem_cons.mp hj with e | hj
            · exact absurd e e1
            exact hj
          obtain e3 : j ≠ aX := fun e => hfree j hj' (by simp [e])
          rw [upd_ne _ _ e1, upd_ne _ _ e2, upd_ne _ _ e3, upd_ne _ _ e1, upd_ne _ _ e2]
  · -- Montgomery's `q qInv` and `1 · 1` modulo `p | 1`.
    obtain hm := or1_lt plt pa1
    rw [wp_seqs_cons (by simp)]
    refine WP.mono (h1.montPq_ok (a := aA) (x := aQ) (y := aQI) (by decide) hQ hQI hV
      (fun j hj => ⟨fun e => nf aA (by simp) (e ▸ hj), fun e => nf aT (by simp) (e ▸ hj)⟩) (by decide)
      (by decide) (r19 h1) pa1 (by omega_using [paw]) (by rw [vd]; omega_using [])
      (by rw [vd]; exact Nat.lt_of_lt_of_le hm (pow8_le pa))
      (by exact Nat.lt_of_lt_of_le ilt (pow8_le pa)) (r21 h1) qa1 (by omega_using [qaw]) qa2
      (Nat.lt_of_lt_of_le qlt (pow8_le qa))) fun t14 ⟨A₁, hA₁, h14⟩ => ?_
    rw [show ∀ x : Prog isa, seqs [x] = x from fun _ => rfl]
    refine WP.mono (h14.montPq_ok (a := aY) (x := aOne) (y := aOne) (by decide) (by simp [hO]) (by simp [hO])
      (by simp [hV]) (fun j hj => by
        rcases List.mem_cons.mp hj with rfl | hj
        · exact ⟨by decide, by decide⟩
        · exact ⟨fun e => nf aY (by simp) (e ▸ hj), fun e => nf aT (by simp) (e ▸ hj)⟩) (by decide)
      (by decide) (r19 h14) pa1 (by omega_using [paw])
      (by rw [upd_ne _ _ (by decide), vd]; omega_using [])
      (by rw [upd_ne _ _ (by decide), vd]; exact Nat.lt_of_lt_of_le hm (pow8_le pa))
      (by rw [upd_ne _ _ (by decide), o1]; exact Nat.one_lt_two_pow (by omega_using [pa1])) (r21 h14) qa1 (by omega_using [qaw]) qa2
      (by rw [upd_ne _ _ (by decide), o1]; exact Nat.one_lt_two_pow (by omega_using [qa1]))) fun t ⟨A₂, hA₂, h15⟩ =>
        ⟨A₁, A₂, fun hlt podd p2 _ => ?_, ?_⟩
    · rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), vd, o1] at hA₂
      rw [vd] at hA₁
      obtain e1 : 2 * (A aP / 2) + 1 = A aP := or1_odd podd
      rw [e1] at hA₁ hA₂
      obtain ⟨l1, c1⟩ := hA₁ hlt
      obtain ⟨l2, c2⟩ := hA₂ (by omega_using [p2])
      rw [Nat.one_mul] at c2
      exact VG.Proof.Rsa.mont_eq_iff podd p2 l1 l2 c1 c2
    · exact h15.sub (live' := aA :: aY :: live) (fun j hj => by
        simp only [List.mem_cons] at hj ⊢; rcases hj with e | e | e <;> simp [e])

/-- `r4 := 8`. -/
theorem len8_ok (u : State) :
    WP isa (.block len8) u fun u' => (u'.gpr .r4 = BitVec.ofNat 64 8 ∧ u'.mem = u.mem) ∧ Keep [.r4] u u' := by
  refine WP.keep _ ?_ (by decide)
  prun [len8]

/-- `shape` and `eMod x m`: `[aA] := e [x] mod [m]` (`e < 2^33` in `aE`), for
`[x] < [m]` and, for a balanced key, `[m]`'s top word not zero; `[x]` and
`[m]` of `xa` bytes, `p_len` for a balanced key. -/
theorem Stg.eMod_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {x m : Nat} (hx : x ∈ live) (hm : m ∈ live) (hE : aE ∈ live) (hz : aZ ∈ live)
    (hA0 : A aZ = 0) (hmi : MulIdx nArr aZ aY aX aA m aT) (hxY : x ≠ aY)
    (hfree : ∀ j ∈ live, j ∉ [aA, aY, aX, aVT, aW] ∧ j ∉ mulArrs aY aX aA aT)
    (he : A aE < 2 ^ 33) {pa qa xa : Nat} (p19 : s0.gpr .r19 = BitVec.ofNat 64 pa)
    (q21 : s0.gpr .r21 = BitVec.ofNat 64 qa) (pa2 : pa < 2 ^ 32) (qa2 : qa < 2 ^ 32)
    (hxa : A x < 2 ^ (8 * xa)) (hma : A m < 2 ^ (8 * xa)) (hxaS : Shape g.w pa qa → xa = pa) :
    WP isa (seqs [.block shape, eMod x m]) s fun t => ∃ R,
      (A x < A m → 2 * A m ≤ 2 ^ (32 * g.w) → (Shape g.w pa qa → 2 ^ (64 * (g.w / 4 - 1)) ≤ A m) →
        R = A aE % 2 ^ 33 * A x % A m) ∧
      Stg g s0 (upd A aA R) (aA :: live) c t := by
  have := h.ws.wle
  obtain mX : m ≠ aX := fun e => (hfree m hm).1 (by simp [e])
  obtain xX : x ≠ aX := fun e => (hfree x hx).1 (by simp [e])
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (shape_ok h.ws.r29 ((h.regs.gpr _ (by decide)).trans p19)
    ((h.regs.gpr _ (by decide)).trans q21) (by omega_using [this]) pa2 qa2) fun s1 ⟨z1, m1, k1⟩ => ?_
  obtain h1 : Stg g s0 A live c s1 :=
    h.next (h.ws.of_keep k1) (js := []) (ds := []) (by rw [m1]; exact KeyWorkspace.Keep.refl _ _ _ _ _)
      (by simp) (by simp) k1 (by decide) (by rw [m1]; exact h.arrs) h.live_lt (by rw [m1]; exact h.vdTop)
      (by rw [m1]; exact h.mask)
  rw [show ∀ y : Prog isa, seqs [y] = y from fun _ => rfl]
  unfold eMod
  refine WP.ite (s1.gpr .r0 == 0) (eval_zero s1 .r0) (fun hz => ?_) (fun _ => ?_)
  · -- By words: `e [x]` exactly, modulo `[m]`.
    obtain hS : Shape g.w pa qa := z1.1 (by simpa using hz)
    obtain ⟨p8, hpw, hpq', p32⟩ := id hS
    rw [hxaS hS] at hxa hma
    rw [wp_seqs_cons (List.cons_ne_nil _ _)]
    refine WP.mono (len8_ok s1) fun s2 ⟨⟨c2, m2⟩, u2⟩ => ?_
    obtain k2 : KeyWorkspace.Keep g.B g.w [] [] s1.mem s2.mem := by
      rw [m2]; exact KeyWorkspace.Keep.refl _ _ _ _ _
    obtain h2 := h1.next (h1.ws.of_keep u2) k2 (by simp) (by simp) u2 (by decide)
      (h1.arrs_keep k2 (by simp) (by simp)) h1.live_lt (h1.vd_keep k2 (by simp) (by simp)) (h1.mask_keep k2 (by simp))
    rw [wp_seqs_cons (List.cons_ne_nil _ _)]
    refine WP.mono (h2.mulLoR_ok (o := aX) (x := aE) (y := x) (by decide) hE hx
      (fun j hj e => (hfree j hj).1 (by simp [e])) (by decide) (by decide) (by decide) c2 (by decide) (by omega_using [hpw, p32])
      (Nat.lt_trans he (by decide))) fun s3 g3 => ?_
    obtain hX : upd A aX (A aE * A x % 2 ^ (32 * g.w)) aX = A aE * A x := by
      rw [upd_self, Nat.mod_eq_of_lt]
      calc A aE * A x < 2 ^ 33 * 2 ^ (8 * pa) := Nat.mul_lt_mul'' he hxa
        _ = 2 ^ (33 + 8 * pa) := by rw [← Nat.pow_add]
        _ ≤ 2 ^ (32 * g.w) := Nat.pow_le_pow_right (by decide) (by omega_using [hpw, p32])
    refine WP.mono (g3.divCopy_ok (a := aX) (d := m) (r := aA) (m := aY) (t := aVT) (sv := aW)
      (by simp) (by simp [hm]) (by decide) (by decide) (by decide) (by decide)
      (fun j hj => by
        rcases List.mem_cons.mp hj with rfl | hj
        · decide
        · exact fun hm' => (hfree j hj).1 (by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hm' ⊢
            rcases hm' with e | e | e | e <;> simp [e]))
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by omega_using [p8, hpw]) (by omega_using [hpw, p32])
      (by rw [upd_ne _ _ mX, show 64 * (g.w / 4) = 8 * pa by omega_using [p8, hpw]]; exact hma) (top := some 1)
      (fun k e => by obtain rfl := Option.some.inj e; omega_using [hpw, p32])
      (by rw [hX]; simp only [VG.Proof.Rsa.PPC64LE.KeyDiv.xw]
          calc A aE * A x < 2 ^ 33 * 2 ^ (8 * pa) := Nat.mul_lt_mul'' he hxa
            _ = 2 ^ (33 + 8 * pa) := by rw [← Nat.pow_add]
            _ ≤ 2 ^ (64 * (g.w / 4 + 1)) := Nat.pow_le_pow_right (by decide) (by omega_using [p8, hpw])))
      fun t ⟨Xr, hX3, gt⟩ => ⟨Xr, fun _ _ ht => ?_, ?_⟩
    · have hb : 2 ^ (64 * (g.w / 4 - 1)) ≤ upd A aX (A aE * A x % 2 ^ (32 * g.w)) m := by
        rw [upd_ne _ _ mX]; exact ht hS
      rw [hX3 hb, hX, upd_ne _ _ mX, Nat.mod_eq_of_lt he]
    · refine (gt.sub (live' := aA :: live) (fun j hj => by
        simp only [List.mem_cons] at hj ⊢; rcases hj with e | e <;> simp [e])).congr' fun j hj => ?_
      by_cases e2 : j = aA
      · subst e2; rw [upd_self, upd_self]
      · have hj' : j ∈ live := by
          rcases List.mem_cons.mp hj with e | hj
          · exact absurd e e2
          exact hj
        obtain e3 : j ≠ aX := fun e => (hfree j hj').1 (by simp [e])
        rw [upd_ne _ _ e2, upd_ne _ _ e3, upd_ne _ _ e2]
  · -- Bit-serially.
    exact WP.mono (h1.mulA_ok (y := aE) (x := x) (m := m) (k := 33) hE hx hm hz hA0 hmi hxY
      (fun j hj => .inr (hfree j hj).2) (by decide) (by decide) fun u _ _ => cnt33_ok u)
      fun t ⟨R, hR, ht⟩ => ⟨R, fun a b _ => hR a b, ht⟩

/-- The checks of `vg_rsa_check_crt_key`. -/
theorem crtChecks_ok {g : Geo} {s0 s : State} {v : Vals} {L M : Nat}
    (h : Stg g s0 (aStart v L M) liveS (decide (v.p % 2 = 1)) s)
    {pa qa : Nat} (pa1 : 1 ≤ pa) (paw : pa ≤ 4 * g.w) (plt : v.p < 2 ^ (8 * pa)) (qlt : v.qI < 2 ^ (8 * pa))
    (p19 : s0.gpr .r19 = BitVec.ofNat 64 pa) (qa1 : 1 ≤ qa) (qaw : qa ≤ 4 * g.w) (qa2 : qa < 2 ^ 32) (qqlt : v.q < 2 ^ (8 * qa))
    (q21 : s0.gpr .r21 = BitVec.ofNat 64 qa) (he : v.e < 2 ^ 33) (dplt : v.dP < 2 ^ (8 * pa))
    (dqlt : v.dQ < 2 ^ (8 * qa)) :
    WP isa (seqs crtChecks) s fun t => ∃ R₁ R₂ A₁ A₂ : Nat,
      (v.dP < 2 * (v.p / 2) → 2 * (2 * (v.p / 2)) ≤ 2 ^ (32 * g.w) →
        (Shape g.w pa qa → 2 ^ (64 * (g.w / 4 - 1)) ≤ 2 * (v.p / 2)) →
        R₁ = v.e % 2 ^ 33 * v.dP % (2 * (v.p / 2))) ∧
      (v.dQ < 2 * (v.q / 2) → 2 * (2 * (v.q / 2)) ≤ 2 ^ (32 * g.w) →
        (Shape g.w pa qa → 2 ^ (64 * (g.w / 4 - 1)) ≤ 2 * (v.q / 2)) →
        R₂ = v.e % 2 ^ 33 * v.dQ % (2 * (v.q / 2))) ∧
      (v.qI < v.p → v.p % 2 = 1 → 2 ≤ v.p → (Shape g.w pa qa → 2 ^ (64 * (g.w / 4 - 1)) ≤ v.p) →
        (A₁ = A₂ ↔ v.q * v.qI % v.p = 1)) ∧
      Stg g s0 (aFin v) liveFin
        (VG.Proof.Rsa.crtBitsM v.n v.p v.q v.dP v.dQ v.qI L M R₁ R₂ A₁ A₂) t := by
  have wpos := h.ws.wpos
  have wle := h.ws.wle
  obtain r19 : ∀ {t : State} {A live c}, Stg g s0 A live c t → t.gpr .r19 = BitVec.ofNat 64 pa :=
    fun h => (h.regs.gpr _ (by decide)).trans p19
  unfold crtChecks
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [wp_seqs_append (by simp [eqA]) (by simp [eqA])]
  refine WP.mono (h.eqA_ok (a := aVQ) (b := aN) (by decide) (by decide)) fun t1 h1 => ?_
  rw [wp_seqs_append (by simp [eqA]) (by simp)]
  refine WP.mono (h1.eqA_ok (a := aVR) (b := aZ) (by decide) (by decide)) fun t2 h2 => ?_
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (h2.copy_ok (o := aM1) (a := aP) (by decide) (by decide) (by decide)) fun t3 h3 => ?_
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (h3.clrLow_ok (j := aM1) (by decide)) fun t4 h4 => ?_
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (h4.copy_ok (o := aM2) (a := aQ) (by decide) (by decide) (by decide)) fun t5 h5 => ?_
  rw [wp_seqs_cons (by simp [ltA])]
  refine WP.mono (h5.clrLow_ok (j := aM2) (by decide)) fun t6 h6 => ?_
  -- `dP`.
  obtain pa2 : pa < 2 ^ 32 := by omega_using [paw, wle]
  obtain m1lt : 2 * (v.p / 2) < 2 ^ (8 * pa) := Nat.lt_of_le_of_lt (by omega_using []) plt
  obtain m2lt : 2 * (v.q / 2) < 2 ^ (8 * qa) := Nat.lt_of_le_of_lt (by omega_using []) qqlt
  rw [wp_seqs_append (by simp [ltA]) (by simp)]
  refine WP.mono (h6.ltA_ok (a := aDP) (b := aM1) (by decide) (by decide) (by decide)) fun t7 h7 => ?_
  rw [show ∀ r : List (Prog isa), (Code.block shape :: eMod aDP aM1 :: r) = [Code.block shape, eMod aDP aM1] ++ r
    from fun _ => rfl, wp_seqs_append (by simp) (by simp [eqA])]
  refine WP.mono (h7.eMod_ok (x := aDP) (m := aM1) (xa := pa) (by decide) (by decide) (by decide) (by decide) rfl
    mulIdx_m1 (by decide) (by decide) he p19 q21 pa2 qa2 dplt m1lt (fun _ => rfl))
    fun t8 ⟨R₁, hR₁, h8⟩ => ?_
  rw [wp_seqs_append (by simp [eqA]) (by simp [ltA])]
  refine WP.mono (h8.eqA_ok (a := aA) (b := aOne) (by decide) (by decide)) fun t9 h9 => ?_
  -- `dQ`.
  rw [wp_seqs_append (by simp [ltA]) (by simp)]
  refine WP.mono (h9.ltA_ok (a := aDQ) (b := aM2) (by decide) (by decide) (by decide)) fun t10 h10 => ?_
  rw [show ∀ r : List (Prog isa), (Code.block shape :: eMod aDQ aM2 :: r) = [Code.block shape, eMod aDQ aM2] ++ r
    from fun _ => rfl, wp_seqs_append (by simp) (by simp [eqA])]
  obtain h10' := h10.sub (live' := aM2 :: aM1 :: liveS) (by decide)
  refine WP.mono (h10'.eMod_ok (x := aDQ) (m := aM2) (xa := qa) (by decide) (by decide) (by decide) (by decide) rfl
    mulIdx_m2 (by decide) (by decide) he p19 q21 pa2 qa2 dqlt m2lt (fun hs => hs.2.2.1.symm))
    fun t11 ⟨R₂, hR₂, h11⟩ => ?_
  rw [wp_seqs_append (by simp [eqA]) (by simp [ltA])]
  refine WP.mono (h11.eqA_ok (a := aA) (b := aOne) (by decide) (by decide)) fun t12 h12 => ?_
  -- `qInv`: Montgomery's `q qInv` and `1 · 1` compared.
  rw [wp_seqs_append (by simp [ltA]) (by simp)]
  refine WP.mono (h12.ltA_ok (a := aQI) (b := aP) (by decide) (by decide) (by decide)) fun t13 h13 => ?_
  obtain h13' := h13.sub (live' := aVD :: aOne :: aQ :: aQI :: aN :: aZ :: aD :: aDP :: aDQ :: aM1 :: aM2 :: aP :: [])
    (by decide)
  rw [show (Code.block shape :: qInvMod :: eqA aA aY : List (Prog isa)) = [Code.block shape, qInvMod] ++ eqA aA aY
    from rfl, wp_seqs_append (by simp) (by simp [eqA])]
  refine WP.mono (h13'.qInv_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl
    pa1 paw qa1 qaw qa2 p19 q21 plt qqlt qlt) fun t15 ⟨A₁, A₂, hA, h15⟩ => ?_
  refine WP.mono (h15.eqA_ok (a := aA) (b := aY) (by decide) (by decide)) fun t h16 => ?_
  refine ⟨R₁, R₂, A₁, A₂, hR₁, hR₂, hA, (h16.sub (live' := liveFin) (by decide)).congr' fun j hj => ?_⟩
  · simp only [liveFin, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem aFin_d (v : Vals) : aFin v aD = v.d := rfl
theorem aFin_n (v : Vals) : aFin v aN = v.n := rfl
/-- `divK len a d`: `[a] mod [d]` in `aVR`, for a divisor of `L` bytes (`L`
in `len`): by words for a balanced key (`Shape`), exact when the divisor's
top word is not zero; else bit-serial, exact. -/
theorem Stg.divK_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {a d : Nat} (ha : a ∈ live) (hd : d ∈ live)
    (hfree : ∀ j ∈ live, j ∉ [aVQ, aVR, aVD, aVT]) {len : Reg} (hlr : len ∉ bodyRegs) (hl12 : len ≠ .r12)
    {L : Nat} (hl : s.gpr len = BitVec.ofNat 64 L) (hL1 : 1 ≤ L) (hL : L < 2 ^ 32) (hlt : A d < 2 ^ (8 * L))
    {pL qL : Nat} (hp : s.gpr .r19 = BitVec.ofNat 64 pL) (hq : s.gpr .r21 = BitVec.ofNat 64 qL)
    (hp' : pL < 2 ^ 32) (hq' : qL < 2 ^ 32) (hLs : Shape g.w pL qL → L = pL) :
    WP isa (seqs (divK len a d)) s fun t => ∃ Xq Xr,
      (0 < A d → (Shape g.w pL qL → 2 ^ (64 * (g.w / 4 - 1)) ≤ A d) → Xr = A a % A d) ∧
      Stg g s0 (upd (upd A aVQ Xq) aVR Xr) (aVR :: aVQ :: live) c t := by
  obtain hN : aVR ≠ aVQ := by decide
  obtain aR : a ≠ aVR := fun e => hfree a ha (by simp [e])
  obtain aT : a ≠ aVT := fun e => hfree a ha (by simp [e])
  obtain aQ : a ≠ aVQ := fun e => hfree a ha (by simp [e])
  obtain dR : d ≠ aVR := fun e => hfree d hd (by simp [e])
  obtain dT : d ≠ aVT := fun e => hfree d hd (by simp [e])
  obtain dQ : d ≠ aVQ := fun e => hfree d hd (by simp [e])
  unfold divK
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have := h.ws.wle
  refine WP.mono (shape_ok h.ws.r29 hp hq (by omega_using [this]) hp' hq') fun s1 ⟨z1, m1, k1⟩ => ?_
  obtain h1 : Stg g s0 A live c s1 :=
    h.next (h.ws.of_keep k1) (js := []) (ds := []) (by rw [m1]; exact KeyWorkspace.Keep.refl _ _ _ _ _)
      (by simp) (by simp) k1 (by decide) (by rw [m1]; exact h.arrs) h.live_lt (by rw [m1]; exact h.vdTop)
      (by rw [m1]; exact h.mask)
  rw [show ∀ x : Prog isa, seqs [x] = x from fun _ => rfl]
  refine WP.ite (s1.gpr .r0 == 0) (eval_zero s1 .r0) (fun hz => ?_) (fun hz => ?_)
  · -- By words.
    obtain hS : Shape g.w pL qL := z1.1 (by simpa using hz)
    obtain hLp := hLs hS
    obtain ⟨p8, hpw, hpq, p32⟩ := hS
    have := h.ws.wle
    refine WP.mono (h1.divCopy_ok (r := aVR) (m := aVD) (t := aVT) (sv := aVQ) ha hd (by decide) (by decide)
      (by decide) (by decide) (fun j hj => by have := hfree j hj; simp_all) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega_using [p8, hpw]) (by omega_using [hpw, p32])
      (by rw [hLp] at hlt; rw [show 64 * (g.w / 4) = 8 * pL by omega_using [p8, hpw]]; exact hlt) (top := none) (fun _ e => nomatch e)
      (by
        simp only [VG.Proof.Rsa.PPC64LE.KeyDiv.xw]
        rw [show 64 * (2 * (g.w / 4)) = 32 * g.w by omega_using [p8, hpw], ← h.arrs.get ha]
        exact val32_lt _ _ _ _)) fun u ⟨Xr, hX, hu⟩ =>
        ⟨num u.mem g.B g.w aVQ, Xr, fun _ hb => hX (hb ⟨p8, hpw, hpq, p32⟩), ?_⟩
    refine ((hu.addLive (j := aVQ) (by decide)).sub (live' := aVR :: aVQ :: live) ?_).congr' ?_
    · intro j hj; simp only [List.mem_cons] at hj ⊢; rcases hj with e | e | e <;> simp [e]
    · intro j hj
      by_cases e1 : j = aVR
      · subst e1; rw [upd_ne _ _ (by decide), upd_self, upd_self]
      · by_cases e2 : j = aVQ
        · subst e2; rw [upd_self, upd_ne _ _ (by decide), upd_self]
        · rw [upd_ne _ _ e2, upd_ne _ _ e1, upd_ne _ _ e1, upd_ne _ _ e2]
  · -- Bit-serial.
    refine WP.mono (h1.divA_ok ha hd hfree hlr hl12 ((k1.gpr len (fun hm => hlr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm; rcases hm with rfl | rfl | rfl <;> decide))).trans hl)
      hL1 hL hlt) fun t ⟨Xq, Xr, hv, ht⟩ => ⟨Xq, Xr, fun hp0 _ => (hv hp0).1, ht⟩

theorem aFin_m1 (v : Vals) : aFin v aM1 = 2 * (v.p / 2) := rfl
theorem aFin_m2 (v : Vals) : aFin v aM2 = 2 * (v.q / 2) := rfl

/-- The checks of `d`: `d < n`, and its remainders modulo `p - 1` and `q - 1`
compared with `dP` and `dQ`; the remainders exact but by words for a
balanced key, where the divisor's top word must not be zero. -/
theorem dChecks_ok {g : Geo} {s0 s : State} {v : Vals} {c : Bool} (h : Stg g s0 (aFin v) liveFin c s)
    {pA qA : Nat} (pa1 : 1 ≤ pA) (pa2 : pA < 2 ^ 32) (plt : v.p < 2 ^ (8 * pA))
    (p19 : s0.gpr .r19 = BitVec.ofNat 64 pA) (qa1 : 1 ≤ qA) (qa2 : qA < 2 ^ 32) (qlt : v.q < 2 ^ (8 * qA))
    (q21 : s0.gpr .r21 = BitVec.ofNat 64 qA) :
    WP isa (seqs dChecks) s fun t => ∃ Y₁ Y₂,
      (0 < 2 * (v.p / 2) → (Shape g.w pA qA → 2 ^ (64 * (g.w / 4 - 1)) ≤ 2 * (v.p / 2)) →
        Y₁ = v.d % (2 * (v.p / 2))) ∧
      (0 < 2 * (v.q / 2) → (Shape g.w pA qA → 2 ^ (64 * (g.w / 4 - 1)) ≤ 2 * (v.q / 2)) →
        Y₂ = v.d % (2 * (v.q / 2))) ∧
      ∃ A live, Stg g s0 A live (c && decide (v.d < v.n) && decide (Y₁ = v.dP) && decide (Y₂ = v.dQ)) t := by
  unfold dChecks
  simp only [List.append_assoc]
  rw [wp_seqs_append (by simp [ltA]) (by simp [divK])]
  refine WP.mono (h.ltA_ok (a := aD) (b := aN) (by decide) (by decide) (by decide)) fun t1 h1 => ?_
  rw [aFin_d, aFin_n] at h1
  rw [wp_seqs_append (by simp [divK]) (by simp [eqA])]
  obtain r1 : ∀ x ∈ [Reg.r19, .r21], t1.gpr x = s0.gpr x := fun x hx => h1.regs.gpr x (by revert x hx; decide)
  refine WP.mono (h1.divK_ok (a := aD) (d := aM1) (by decide) (by decide) (by decide) (len := .r19) (by decide)
    (by decide) ((r1 .r19 (by decide)).trans p19) pa1 pa2 (by rw [aFin_m1]; omega_using [plt])
    ((r1 .r19 (by decide)).trans p19) ((r1 .r21 (by decide)).trans q21) pa2 qa2 (fun _ => rfl))
    fun t2 ⟨Xq, Y₁, hv1, h2⟩ => ?_
  rw [aFin_d, aFin_m1] at hv1
  rw [wp_seqs_append (by simp [eqA]) (by simp [divK])]
  refine WP.mono (h2.eqA_ok (a := aVR) (b := aDP) (by decide) (by decide)) fun t3 h3 => ?_
  obtain h3' : Stg g s0 (aFin v) liveFin (c && decide (v.d < v.n) && decide (Y₁ = v.dP)) t3 := by
    obtain e : upd (upd (aFin v) aVQ Xq) aVR Y₁ aVR = Y₁ := by rw [upd_self]
    have e2 : upd (upd (aFin v) aVQ Xq) aVR Y₁ aDP = v.dP := rfl
    rw [e, e2] at h3
    exact (h3.sub (live' := liveFin) (by decide)).congr' fun j hj => by
      simp only [liveFin, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [wp_seqs_append (by simp [divK]) (by simp [eqA])]
  obtain r3 : ∀ x ∈ [Reg.r19, .r21], t3.gpr x = s0.gpr x := fun x hx => h3'.regs.gpr x (by revert x hx; decide)
  refine WP.mono (h3'.divK_ok (a := aD) (d := aM2) (by decide) (by decide) (by decide) (len := .r21) (by decide)
    (by decide) ((r3 .r21 (by decide)).trans q21) qa1 qa2 (by rw [aFin_m2]; omega_using [qlt])
    ((r3 .r19 (by decide)).trans p19) ((r3 .r21 (by decide)).trans q21) pa2 qa2
    (fun hs => by obtain ⟨_, _, e, _⟩ := hs; omega_using [e]))
    fun t4 ⟨Xq', Y₂, hv2, h4⟩ => ?_
  rw [aFin_d, aFin_m2] at hv2
  refine WP.mono (h4.eqA_ok (a := aVR) (b := aDQ) (by decide) (by decide)) fun t h5 => ?_
  obtain e : upd (upd (aFin v) aVQ Xq') aVR Y₂ aVR = Y₂ := by rw [upd_self]
  have e2 : upd (upd (aFin v) aVQ Xq') aVR Y₂ aDQ = v.dQ := rfl
  rw [e, e2] at h5
  exact ⟨Y₁, Y₂, hv1, hv2, _, _, h5⟩

end VG.Proof.Rsa.PPC64LE.KeyCheck

end

end


/-!
# `vg_rsa_check_key` on PPC64LE: the checks of a valid public key

`CkRegs s0 t`: the pointers and lengths the entry keeps in `r14`–`r26`.
`ck_valid`: for a valid modulus and exponent, the arrays set up, the numbers
read and checked, and `checkKey`'s bit returned in `r3`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.KeyCheck

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.KeyCheck
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot Arrs upd upd_ne upd_self)
open VG.Proof.Bignum.PPC64LE.Pub (sat)

/-- The pointers and lengths of `vg_rsa_check_key`, kept by the entry. -/
structure CkRegs (s0 t : State) : Prop where
  r14 : t.gpr .r14 = s0.gpr .r3
  r15 : t.gpr .r15 = s0.gpr .r4
  r16 : t.gpr .r16 = s0.gpr .r7
  r17 : t.gpr .r17 = s0.gpr .r8
  r18 : t.gpr .r18 = s0.gpr .r9
  r19 : t.gpr .r19 = s0.gpr .r10
  r20 : t.gpr .r20 = PPC64LE.stackArg s0 0
  r21 : t.gpr .r21 = PPC64LE.stackArg s0 1
  r22 : t.gpr .r22 = PPC64LE.stackArg s0 2
  r23 : t.gpr .r23 = PPC64LE.stackArg s0 4
  r26 : t.gpr .r26 = PPC64LE.stackArg s0 6

/-- The registers `CkRegs` is about. -/
abbrev ckRegs : List Reg := [.r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r26]

theorem CkRegs.of_keep {s0 t u : State} (h : CkRegs s0 t) {rs : List Reg} (k : Keep rs t u)
    (hr : ∀ r ∈ ckRegs, r ∉ rs := by decide) : CkRegs s0 u := by
  obtain e : ∀ r ∈ ckRegs, u.gpr r = t.gpr r := fun r hr' => k.gpr r (hr r hr')
  exact ⟨(e _ (by decide)).trans h.r14, (e _ (by decide)).trans h.r15, (e _ (by decide)).trans h.r16,
    (e _ (by decide)).trans h.r17, (e _ (by decide)).trans h.r18, (e _ (by decide)).trans h.r19,
    (e _ (by decide)).trans h.r20, (e _ (by decide)).trans h.r21, (e _ (by decide)).trans h.r22,
    (e _ (by decide)).trans h.r23, (e _ (by decide)).trans h.r26⟩

/-- The registers the valid branch may change. -/
abbrev validRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .r29, .r30]

/-- `checkKey` of the arguments. -/
abbrev ckOk (s0 : State) : Bool :=
  Spec.Rsa.checkKey (Spec.Rsa.bytesAt s0.mem (s0.gpr .r3) (s0.gpr .r4).toNat)
    (Spec.Rsa.bytesAt s0.mem (s0.gpr .r5) (s0.gpr .r6).toNat)
    (Spec.Rsa.bytesAt s0.mem (s0.gpr .r7) (s0.gpr .r8).toNat)
    (Spec.Rsa.bytesAt s0.mem (s0.gpr .r9) (s0.gpr .r10).toNat)
    (Spec.Rsa.bytesAt s0.mem (PPC64LE.stackArg s0 0) (PPC64LE.stackArg s0 1).toNat)
    (Spec.Rsa.bytesAt s0.mem (PPC64LE.stackArg s0 2) (s0.gpr .r10).toNat)
    (Spec.Rsa.bytesAt s0.mem (PPC64LE.stackArg s0 4) (PPC64LE.stackArg s0 1).toNat)
    (Spec.Rsa.bytesAt s0.mem (PPC64LE.stackArg s0 6) (s0.gpr .r10).toNat)

theorem len_bytes (m : Mem) (p : Addr) (L : Nat) : (Spec.Rsa.bytesAt m p L).length = L := by
  simp [Spec.Rsa.bytesAt]

theorem ck_valid {s0 s : State} (h0 : ckP.pre s0) (hb : KBase (ckB s0) (ckZ s0) s0 s) (hr : CkRegs s0 s)
    (h24 : s.gpr .r24 = BitVec.ofNat 64
      (sat (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r5) (s0.gpr .r6).toNat))) <<< 31)
    (hmv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r3) (kK s0))) (kK s0) = true)
    (hev : Spec.Rsa.exponentValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r5) (s0.gpr .r6).toNat))
      = true) :
    WP isa (seqs (([setup, .block eArr] : List (Prog isa)) ++ VG.Impl.Rsa.PPC64LE.CheckKey.loads ++
        (start ++ crtChecks ++ dChecks) ++ ([.block ret] : List (Prog isa)))) s fun t =>
      KBase (ckB s0) (ckZ s0) s0 t ∧ t.gpr .r3 = BitVec.ofNat 64 (if ckOk s0 then 1 else 0) ∧
        Keep validRegs s t := by
  obtain hp := ck_kpre h0
  obtain ⟨-, hrd, -, dn, -, dd, dpp, dq, ddp, ddq, dqi, -, wn, -, wd, wp, wq, wdp, wdq, wqi, -, -, -, -, d1, d2,
    p1, p2, q1, q2, edp, eqi, edq, -⟩ := id h0
  obtain ⟨-, hw16, -, hkw⟩ := hp.ws
  have hK : (s0.gpr .r4).toNat = kK s0 := rfl
  rw [edp] at ddp wdp
  rw [eqi] at dqi wqi
  rw [edq] at ddq wdq
  obtain he' : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r5) (s0.gpr .r6).toNat) < 2 ^ 33 := by
    simp only [Spec.Rsa.exponentValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hev; exact hev.2
  obtain hsat : sat (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r5) (s0.gpr .r6).toNat)) =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r5) (s0.gpr .r6).toNat) := by
    unfold sat; omega_arith
  rw [hsat] at h24
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine prep_ok hp hb (by rw [hr.r15]; exact CrtValues.ofNat_toNat64 _) h24 he'
    (by simp [VG.Impl.Rsa.PPC64LE.CheckKey.loads]) fun t0 l0 k0 => ?_
  obtain R0 := hr.of_keep k0
  simp only [VG.Impl.Rsa.PPC64LE.CheckKey.loads, List.append_assoc]
  obtain hl : ∀ (a b : Reg) (j : Nat) (r : List (Prog isa)), r ≠ [] → ∀ {u : State} {Q : State → Prop},
      WP isa (seqs (loadR a b j)) u (fun t => WP isa (seqs r) t Q) → WP isa (seqs (loadR a b j ++ r)) u Q :=
    fun a b j r hr _ _ h => (wp_seqs_append (by simp [loadR]) hr).mpr h
  -- `n`.
  refine hl _ _ _ _ (by simp) (WP.mono (ldStep_ok l0 (j := aN) (by decide) rfl (rP := .r14) (rL := .r15)
    (by decide) (by decide) (by decide) R0.r14 (by rw [R0.r15]; exact CrtValues.ofNat_toNat64 _)
    (by omega_arith) (by omega_arith) (by rw [hrd]; simp) dn wn) fun t1 ⟨l1, k1⟩ => ?_)
  obtain R1 := R0.of_keep k1
  -- `d`.
  refine hl _ _ _ _ (by simp) (WP.mono (ldStep_ok l1 (j := aD) (by decide) rfl (rP := .r16) (rL := .r17)
    (by decide) (by decide) (by decide) R1.r16 (by rw [R1.r17]; exact CrtValues.ofNat_toNat64 _)
    d1 (by omega_arith) (by rw [hrd]; simp) dd wd) fun t2 ⟨l2, k2⟩ => ?_)
  obtain R2 := R1.of_keep k2
  -- `p`.
  refine hl _ _ _ _ (by simp) (WP.mono (ldStep_ok l2 (j := aP) (by decide) rfl (rP := .r18) (rL := .r19)
    (by decide) (by decide) (by decide) R2.r18 (by rw [R2.r19]; exact CrtValues.ofNat_toNat64 _)
    p1 (by omega_arith) (by rw [hrd]; simp) dpp wp) fun t3 ⟨l3, k3⟩ => ?_)
  obtain R3 := R2.of_keep k3
  -- `q`.
  refine hl _ _ _ _ (by simp) (WP.mono (ldStep_ok l3 (j := aQ) (by decide) rfl (rP := .r20) (rL := .r21)
    (by decide) (by decide) (by decide) R3.r20 (by rw [R3.r21]; exact CrtValues.ofNat_toNat64 _)
    q1 (by omega_arith) (by rw [hrd]; simp) dq wq) fun t4 ⟨l4, k4⟩ => ?_)
  obtain R4 := R3.of_keep k4
  -- `dP`.
  refine hl _ _ _ _ (by simp) (WP.mono (ldStep_ok l4 (j := aDP) (by decide) rfl (rP := .r22) (rL := .r19)
    (by decide) (by decide) (by decide) R4.r22 (by rw [R4.r19]; exact CrtValues.ofNat_toNat64 _)
    p1 (by omega_arith) (by rw [hrd, edp]; simp) ddp wdp) fun t5 ⟨l5, k5⟩ => ?_)
  obtain R5 := R4.of_keep k5
  -- `dQ`.
  refine hl _ _ _ _ (by simp) (WP.mono (ldStep_ok l5 (j := aDQ) (by decide) rfl (rP := .r23) (rL := .r21)
    (by decide) (by decide) (by decide) R5.r23 (by rw [R5.r21]; exact CrtValues.ofNat_toNat64 _)
    q1 (by omega_arith) (by rw [hrd, edq]; simp) ddq wdq) fun t6 ⟨l6, k6⟩ => ?_)
  obtain R6 := R5.of_keep k6
  -- `qInv`.
  refine hl _ _ _ _ (by simp [start]) (WP.mono (ldStep_ok l6 (j := aQI) (by decide) rfl (rP := .r26)
    (rL := .r19) (by decide) (by decide) (by decide) R6.r26 (by rw [R6.r19]; exact CrtValues.ofNat_toNat64 _)
    p1 (by omega_arith) (by rw [hrd, eqi]; simp) dqi wqi) fun t7 ⟨l7, k7⟩ => ?_)
  -- The checks.
  let g : Geo := ⟨ckB s0, ckZ s0, kK s0⟩
  let v : Vals := ⟨Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r3) (s0.gpr .r4).toNat),
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r5) (s0.gpr .r6).toNat),
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r9) (s0.gpr .r10).toNat),
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (PPC64LE.stackArg s0 0) (PPC64LE.stackArg s0 1).toNat),
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (PPC64LE.stackArg s0 2) (s0.gpr .r10).toNat),
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (PPC64LE.stackArg s0 4) (PPC64LE.stackArg s0 1).toNat),
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (PPC64LE.stackArg s0 6) (s0.gpr .r10).toNat),
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r7) (s0.gpr .r8).toNat)⟩
  obtain a7 : Arrs t7.mem g.B g.w (vals v) live0 := l7.arrs.sub (by decide)
  rw [wp_seqs_append (by simp [start]) (by simp [crtChecks, eqA])]
  have wl7 := l7.ws.wle
  obtain pw : (s0.gpr .r10).toNat ≤ 4 * g.w := by show _ ≤ 4 * ((kK s0 + 3) / 4); omega_arith
  obtain qw : (PPC64LE.stackArg s0 1).toNat ≤ 4 * g.w := by show _ ≤ 4 * ((kK s0 + 3) / 4); omega_arith
  obtain p19 : t7.gpr .r19 = BitVec.ofNat 64 (s0.gpr .r10).toNat :=
    ((R6.of_keep k7).r19).trans (CrtValues.ofNat_toNat64 _)
  obtain q21 : t7.gpr .r21 = BitVec.ofNat 64 (PPC64LE.stackArg s0 1).toNat :=
    ((R6.of_keep k7).r21).trans (CrtValues.ofNat_toNat64 _)
  refine WP.mono (start_ok (g := g) (v := v) l7.ws a7 (l7.top _ (by decide)) p1 pw
    (lt_pow8_of_len _ (len_bytes _ _ _)) p19 (by omega_arith)
    (lt_pow8_of_len _ (len_bytes _ _ _)) q21) fun t8 ⟨L, M, hL, hM, g8⟩ => ?_
  rw [wp_seqs_append (by simp [crtChecks, eqA]) (by simp [dChecks, ltA])]
  have wl : (kK s0 + 3) / 4 ≤ 1024 := g8.ws.wle
  refine WP.mono (crtChecks_ok g8 p1 pw (lt_pow8_of_len _ (len_bytes _ _ _)) (lt_pow8_of_len _ (len_bytes _ _ _))
    p19 q1 qw (by omega_arith) (lt_pow8_of_len _ (len_bytes _ _ _)) q21 he'
    (lt_pow8_of_len _ (len_bytes _ _ _)) (lt_pow8_of_len _ (len_bytes _ _ _)))
    fun t9 ⟨R₁, R₂, A₁, A₂, hR₁, hR₂, hA, g9⟩ => ?_
  rw [wp_seqs_append (by simp [dChecks, ltA]) (by simp)]
  refine WP.mono (dChecks_ok g9 (pA := (s0.gpr .r10).toNat) (qA := (PPC64LE.stackArg s0 1).toNat) p1
    (by omega_arith) (lt_pow8_of_len _ (len_bytes _ _ _)) (((R6.of_keep k7).r19).trans (CrtValues.ofNat_toNat64 _))
    q1 (by omega_arith) (lt_pow8_of_len _ (len_bytes _ _ _)) (((R6.of_keep k7).r21).trans (CrtValues.ofNat_toNat64 _)))
    fun t10 ⟨Y₁, Y₂, hY₁, hY₂, A, live, g10⟩ => ?_
  rw [show seqs [.block ret] = .block ret from rfl]
  refine WP.mono (ret_ok g10) fun t ⟨⟨t3, tm⟩, kt⟩ => ⟨?_, ?_, ?_⟩
  · exact (g10.base l7.base hp.nowrap).of_regs kt tm
  · rw [t3]
    congr 2
    obtain e := ck_bitsM'' (k := kK s0) (w := g.w) rfl hmv hev (lt_pow_len _ (len_bytes _ _ _))
      (lt_pow_of_len _ (by rw [len_bytes]; exact p2)) (lt_pow_of_len _ (by rw [len_bytes]; exact q2))
      (by omega_arith) (pow_kw _) (lt_pow8_of_len _ (len_bytes _ _ _)) (lt_pow8_of_len _ (len_bytes _ _ _))
      hL hM hR₁ hR₂ hA hY₁ hY₂
    rw [show ckOk s0 = Spec.Rsa.keyValid (kK s0) _ _ _ _ _ _ _ _ by
      simp only [ckOk, Spec.Rsa.checkKey, len_bytes]; rfl, e]
    rfl
  · exact (((((((((k0.trans k1).trans k2).trans k3).trans k4).trans k5).trans k6).trans k7).trans
      g10.regs).trans kt).mono

end VG.Proof.Rsa.PPC64LE.KeyCheck
