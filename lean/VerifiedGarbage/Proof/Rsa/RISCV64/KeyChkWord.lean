module

public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyWordDiv
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyChkBase
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyOps
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyDiv
public import VerifiedGarbage.Proof.Rsa.RISCV64.RdOps
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreR2
import VerifiedGarbage.Proof.Bignum.CrtFrame
public import VerifiedGarbage.Impl.Rsa.RISCV64.MulMod
import VerifiedGarbage.Proof.Rsa.MulModArithmetic
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64

/-! ### `Rsa.RISCV64.KeyChkOps`, which this module and modules that import it used -/

section

/-! ### `Rsa.RISCV64.KeyMulMod`, which only this module used -/

section

/-! # `mulMod` on RISC-V: `[a] = ([a] + ([y] mod 2^k) [x]) mod [m]`

As on PPC64LE (`Proof/Rsa/PPC64LE/KcCk.lean`), in words of 64 bits.
`addMod_ok`: `[o] = ([a] + [b]) mod [m]` for `[a], [b] < [m]`,
`2 [m] ≤ 2^(64 w)` and `[z] = 0`. `mulMod_ok`: `k = s7` steps of
`mulModStep`, each adding the selected `[x]` to `[a]` and doubling `[x]`
modulo `[m]`, and halving `[y]`. From `[a], [x] < [m]` with
`2 [m] ≤ 2^(64 w)` and `[z] = 0`, `[a]` ends as
`([a] + ([y] mod 2^k) [x]) mod [m]`.
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.Keys

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Rsa.RISCV64.Keys (seqs addMod mulHead mulTail mulModStep mulMod sB sC stBorrow sel bitOf half
  sub3)

/-- `seqs (addMod o a b m z t)`: `[o] := ([a] + [b]) mod [m]`, through `t`, `t + 1`, `t + 2` and the
slot `sC`. -/
theorem addMod_ok {s : State} {B : Addr} {Z w N o a b m z t : Nat} (h : Ws s B Z w N)
    (hN : N ≤ 2048) (ho : o < N) (ha : a < N) (hb : b < N) (hm : m < N) (hz : z < N) (ht : t + 2 < N)
    (htz : t ≠ z) (htb : t ≠ b) (hat : a ≠ t) (hat1 : a ≠ t + 1) (hmt : m ≠ t) (hmt1 : m ≠ t + 1)
    (hmt2 : m ≠ t + 2) (hot1 : o ≠ t + 1) (hot2 : o ≠ t + 2) :
    WP isa (seqs (addMod o a b m z t)) s fun u => Ws u B Z w N ∧
      Frame B w [t, t + 1, t + 2, o] [sC] s.mem u.mem ∧ Keep opRegs s u ∧
      (num s.mem B w z = 0 → num s.mem B w a < num s.mem B w m → num s.mem B w b < num s.mem B w m →
        2 * num s.mem B w m ≤ 2 ^ (64 * w) →
        num u.mem B w o = (num s.mem B w a + num s.mem B w b) % num s.mem B w m) := by
  simp only [addMod, seqs]
  rw [WP.seq_iff]
  refine WP.mono (sub3_ok h (o := t) (a := z) (b := b) (by omega_arith) hz hb hN htz htb)
    fun t1 ⟨h1, k1, v1, b1, r1⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (sub3_ok h1 (o := t + 1) (a := a) (b := t) (by omega_arith) ha (by omega_arith) hN (Ne.symm hat1)
    (by omega_arith)) fun t2 ⟨h2, k2, v2, b2, r2⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (sub3_ok h2 (o := t + 2) (a := t + 1) (b := m) ht (by omega_arith) hm hN (by omega_arith)
    (Ne.symm hmt2)) fun t3 ⟨h3, k3, v3, b3, r3⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (stBorrow_ok h3 (sl := sC) (by decide) (by decide)) fun t4 ⟨h4, k4, s4, r4⟩ => ?_
  refine WP.mono (sel_ok h4 (o := o) (a := t + 2) (b := t + 1) (sl := sC) ho ht (by omega_arith) hN hot2 hot1
    (by decide) (by decide) (by rw [s4]; exact b3)) fun u ⟨hu, k5, v5, r5⟩ => ?_
  refine ⟨hu, Frame.join (Frame.join (js := [t, t + 1, t + 2, o]) (ds := [sC])
    (Frame.join (js := [t, t + 1, t + 2, o]) (ds := [sC]) k1 k2) k3)
    (Frame.join (js := [t, t + 1, t + 2, o]) (ds := [sC]) k4 k5),
    Keep.trans' (Keep.trans' (Keep.trans' r1 r2) r3) (Keep.trans' (r4.mono (by decide)) r5), fun hZ hA hB hM => ?_⟩
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
    rw [k4.num (by simp) (by decide) ft1, T3]
  obtain U4 : num t4.mem B w (t + 2) = num t3.mem B w (t + 2) := k4.num (by simp) (by decide) ft2
  rw [v5, s4, T4, U4]
  rw [hZ] at v1
  rw [a1] at v2
  rw [m2] at v3
  exact VG.Proof.Rsa.addMod_impl hA hB hM (by rw [Nat.add_comm] at v1; omega_arith) (wordsVal_lt _ _ _ _) b1
    (by omega_arith) (wordsVal_lt _ _ _ _) b2 (by omega_arith) (wordsVal_lt _ _ _ _) b3

/-- `mulHead`: `[t]` is `[x]` if `[y]` is odd, `[z]` if not. -/
theorem mulHead_ok {s : State} {B : Addr} {Z w N z y x t : Nat} (h : Ws s B Z w N)
    (hN : N ≤ 2048) (ht : t < N) (hz : z < N) (hy : y < N) (hx : x < N) (htz : t ≠ z) (htx : t ≠ x) :
    WP isa (mulHead z y x t) s fun u => Ws u B Z w N ∧ Frame B w [t] [sB] s.mem u.mem ∧
      Keep opRegs s u ∧
      num u.mem B w t = (if num s.mem B w y % 2 = 0 then num s.mem B w z else num s.mem B w x) := by
  rw [mulHead, WP.seq_iff]
  refine WP.mono (bitOf_ok h (sl := sB) hy hN (by decide) (by decide)) fun t1 ⟨h1, k1, e1, r1⟩ => ?_
  refine WP.mono (sel_ok h1 (o := t) (a := z) (b := x) (sl := sB) ht hz hx hN htz htx (by decide) (by decide)
    (by rw [e1]; omega_arith)) fun u ⟨hu, k2, e2, r2⟩ =>
      ⟨hu, Frame.join k1 k2, Keep.trans' r1 r2, ?_⟩
  rw [e2, e1, k1.num (by simp) (by decide) (h.fit64 hz), k1.num (by simp) (by decide) (h.fit64 hx)]

/-- `mulTail`: `[y]` halved, `s7` decremented. -/
theorem mulTail_ok {s : State} {B : Addr} {Z w N y : Nat} (h : Ws s B Z w N) (hN : N ≤ 2048) (hy : y < N) :
    WP isa (mulTail y) s fun u => Ws u B Z w N ∧ Frame B w [y] [] s.mem u.mem ∧
      Keep (.s7 :: opRegs) s u ∧ u.gpr .s7 = s.gpr .s7 - BitVec.ofNat 64 1 ∧
      num u.mem B w y = num s.mem B w y / 2 := by
  simp only [mulTail, seqs]
  rw [WP.seq_iff]
  obtain b0 : WP isa (.block [.li .t4 0]) s fun u => (u.gpr .t4 = 0 ∧ u.mem = s.mem) ∧ Keep [.t4] s u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [fin64_exec_li_zero]
  refine WP.mono b0 fun t5 ⟨⟨u4, m5⟩, k5⟩ => ?_
  obtain h5 := h.of_keep k5
  rw [WP.seq_iff]
  refine WP.mono (half_ok h5 (j := y) hy hN (by rw [u4]; decide)) fun t6 ⟨h6, k6, e6, _, r6⟩ => ?_
  obtain b7 : WP isa (.block [.addi .s7 .s7 (-1)]) t6 fun u =>
      (u.gpr .s7 = t6.gpr .s7 - BitVec.ofNat 64 1 ∧ u.mem = t6.mem) ∧ Keep [.s7] t6 u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun []
  refine WP.mono b7 fun u ⟨⟨u7, m7⟩, k7⟩ => ?_
  obtain r7eq : t6.gpr .s7 = s.gpr .s7 := by rw [r6.gpr (r := .s7) (by decide), k5.gpr (r := .s7) (by decide)]
  rw [u4, m5] at e6
  rw [m5] at k6
  refine ⟨h6.of_keep k7, by rw [m7]; exact k6, Keep.trans' (Keep.trans' (k5.mono (by decide)) (r6.mono (by decide)))
    (k7.mono (by decide)), by rw [u7, r7eq], ?_⟩
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
    (hN : N ≤ 2048) (hi : MulIdx N z y x a m t) :
    WP isa (mulModStep z y x a m t) s fun u => Ws u B Z w N ∧
      Frame B w (mulArrs y x a t) [sB, sC] s.mem u.mem ∧ Keep (.s7 :: opRegs) s u ∧
      u.gpr .s7 = s.gpr .s7 - BitVec.ofNat 64 1 ∧
      num u.mem B w y = num s.mem B w y / 2 ∧
      (num s.mem B w z = 0 → num s.mem B w a < num s.mem B w m → num s.mem B w x < num s.mem B w m →
        2 * num s.mem B w m ≤ 2 ^ (64 * w) →
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
  obtain n2 : ∀ j, j ≠ t → ∀ k ∈ [t], k ≠ j := fun j hj k hk => by
    rw [List.mem_singleton] at hk; subst hk; exact Ne.symm hj
  obtain n4 : ∀ j o, j ≠ t + 1 → j ≠ t + 1 + 1 → j ≠ t + 1 + 2 → j ≠ o →
      ∀ k ∈ [t + 1, t + 1 + 1, t + 1 + 2, o], k ≠ j := fun j o h1 h2 h3 h4 k hk => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> exact Ne.symm (by with_reducible assumption)
  obtain n1 : ∀ j, j ≠ y → ∀ k ∈ [y], k ≠ j := fun j hj k hk => by
    rw [List.mem_singleton] at hk; subst hk; exact Ne.symm hj
  obtain fz := h.fit64 zN
  obtain fy := h.fit64 yN
  obtain fx := h.fit64 xN
  obtain fa := h.fit64 aN
  obtain fm := h.fit64 mN
  simp only [mulModStep, seqs]
  rw [WP.seq_iff]
  refine WP.mono (mulHead_ok h hN tN zN yN xN (by omega_arith) (by omega_arith)) fun t2 ⟨h2, k2, r2, e2⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (addMod_ok h2 (o := a) (a := a) (b := t) (m := m) (z := z) (t := t + 1) hN aN aN tN mN zN t1N
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith))
    fun t3 ⟨h3, k3, r3, e3⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (addMod_ok h3 (o := x) (a := x) (b := x) (m := m) (z := z) (t := t + 1) hN xN xN xN mN zN t1N
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith))
    fun t4 ⟨h4, k4, r4, e4⟩ => ?_
  refine WP.mono (mulTail_ok h4 hN yN) fun u ⟨hu, k6, r6, c6, e6⟩ => ?_
  obtain r7eq : t4.gpr .s7 = s.gpr .s7 := by
    rw [r4.gpr (r := .s7) (by decide), r3.gpr (r := .s7) (by decide), r2.gpr (r := .s7) (by decide)]
  refine ⟨hu, Frame.join (Frame.join (js := mulArrs y x a t) (ds := [sB, sC])
    (Frame.join (js := mulArrs y x a t) (ds := [sB, sC]) k2 k3) k4) k6,
    Keep.trans' (Keep.trans' (Keep.trans' (r2.mono (by decide)) (r3.mono (by decide))) (r4.mono (by decide))) r6,
    by rw [c6, r7eq], ?_, fun hZ hA hX hM => ?_⟩
  · rw [e6, k4.num (n4 y x (by omega_arith) (by omega_arith) (by omega_arith) hyx) (by decide) fy,
      k3.num (n4 y a (by omega_arith) (by omega_arith) (by omega_arith) hya) (by decide) fy,
      k2.num (n2 y (by omega_arith)) (by decide) fy]
  · -- The values each step reads.
    obtain z2 : num t2.mem B w z = 0 := by rw [k2.num (n2 z (by omega_arith)) (by decide) fz, hZ]
    obtain mm2 : num t2.mem B w m = num s.mem B w m := k2.num (n2 m (by omega_arith)) (by decide) fm
    obtain a2 : num t2.mem B w a = num s.mem B w a := k2.num (n2 a (by omega_arith)) (by decide) fa
    obtain x2 : num t2.mem B w x = num s.mem B w x := k2.num (n2 x (by omega_arith)) (by decide) fx
    obtain d2 : num t2.mem B w t = num s.mem B w y % 2 * num s.mem B w x := by
      rw [e2, hZ]
      rcases Nat.mod_two_eq_zero_or_one (num s.mem B w y) with e | e <;> simp [e]
    obtain dlt : num t2.mem B w t < num s.mem B w m := by
      rw [d2]; rcases Nat.mod_two_eq_zero_or_one (num s.mem B w y) with e | e <;> simp [e] <;> omega_arith
    obtain A3 := e3 z2 (by rw [a2, mm2]; exact hA) (by rw [mm2]; exact dlt) (by rw [mm2]; exact hM)
    rw [a2, mm2, d2] at A3
    obtain z3 : num t3.mem B w z = 0 := by
      rw [k3.num (n4 z a (by omega_arith) (by omega_arith) (by omega_arith) hza) (by decide) fz, z2]
    obtain mm3 : num t3.mem B w m = num s.mem B w m := by
      rw [k3.num (n4 m a (by omega_arith) (by omega_arith) (by omega_arith) (Ne.symm ham)) (by decide) fm, mm2]
    obtain x3 : num t3.mem B w x = num s.mem B w x := by
      rw [k3.num (n4 x a (by omega_arith) (by omega_arith) (by omega_arith) hxa) (by decide) fx, x2]
    obtain X4 := e4 z3 (by rw [x3, mm3]; exact hX) (by rw [x3, mm3]; exact hX) (by rw [mm3]; exact hM)
    rw [x3, mm3] at X4
    refine ⟨?_, ?_⟩
    · rw [k6.num (n1 a (Ne.symm hya)) (by simp) fa,
        k4.num (n4 a x (by omega_arith) (by omega_arith) (by omega_arith) (Ne.symm hxa)) (by decide) fa, A3]
    · rw [k6.num (n1 x (Ne.symm hyx)) (by simp) fx, X4]

/-- The state after `i` of the `k` steps. -/
structure MulI (s0 : State) (B : Addr) (Z w N z y x a m t : Nat) (k i : Nat) (u : State) : Prop where
  ws : Ws u B Z w N
  frame : Frame B w (mulArrs y x a t) [sB, sC] s0.mem u.mem
  regs : Keep (.s7 :: opRegs) s0 u
  cnt : u.gpr .s7 = BitVec.ofNat 64 (k - i)
  yv : num u.mem B w y = num s0.mem B w y / 2 ^ i
  value : num s0.mem B w z = 0 → num s0.mem B w a < num s0.mem B w m → num s0.mem B w x < num s0.mem B w m →
    2 * num s0.mem B w m ≤ 2 ^ (64 * w) →
    num u.mem B w a = (num s0.mem B w a + num s0.mem B w y % 2 ^ i * num s0.mem B w x) % num s0.mem B w m ∧
    num u.mem B w x = 2 ^ i * num s0.mem B w x % num s0.mem B w m

theorem mulModBody_ok {s0 u : State} {B : Addr} {Z w N z y x a m t k i : Nat} (hN : N ≤ 2048)
    (hi : MulIdx N z y x a m t) (hik : i < k) (inv : MulI s0 B Z w N z y x a m t k i u) :
    WP isa (mulModStep z y x a m t) u fun u' =>
      MulI s0 B Z w N z y x a m t k (i + 1) u' ∧ u'.gpr .s7 = u.gpr .s7 - BitVec.ofNat 64 1 := by
  have h := inv.ws
  have hi' := hi
  obtain ⟨ht, hz, hy, hx, ha, hm, hzy, hzx, hza, hzm, hyx, hya, hym, hxa, hxm, ham⟩ := hi'
  obtain fz := h.fit64 (j := z) (by omega_arith)
  obtain fm := h.fit64 (j := m) (by omega_arith)
  obtain zk : num u.mem B w z = num s0.mem B w z := inv.frame.num (by simp; omega_arith) (by decide) fz
  obtain mk : num u.mem B w m = num s0.mem B w m := inv.frame.num (by simp; omega_arith) (by decide) fm
  refine WP.mono (mulModStep_ok h hN hi) fun u' ⟨h', k', r', c', y', v'⟩ => ?_
  refine ⟨⟨h', inv.frame.trans k', Keep.trans' inv.regs r', ?_, ?_, fun hZ hA hX hM => ?_⟩, c'⟩
  · rw [c', inv.cnt]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_using [hik]
  · rw [y', inv.yv, Nat.div_div_eq_div_mul, Nat.pow_succ]
  · obtain ⟨va, vx⟩ := inv.value hZ hA hX hM
    obtain M0 : 0 < num s0.mem B w m := by omega_arith
    obtain aLt : num u.mem B w a < num u.mem B w m := by rw [va, mk]; exact Nat.mod_lt _ M0
    obtain xLt : num u.mem B w x < num u.mem B w m := by rw [vx, mk]; exact Nat.mod_lt _ M0
    obtain ⟨va', vx'⟩ := v' (by rw [zk, hZ]) aLt xLt (by rw [mk]; exact hM)
    rw [va', vx', va, vx, inv.yv, mk]
    exact ⟨VG.Proof.Rsa.mulMod_arith, VG.Proof.Rsa.double_arith⟩

/-- `mulMod z y x a m t` with `s7 = k > 0`. -/
theorem mulMod_ok {s : State} {B : Addr} {Z w N z y x a m t k : Nat} (h : Ws s B Z w N)
    (hN : N ≤ 2048) (hi : MulIdx N z y x a m t) (hk : 0 < k) (hk' : k < 2 ^ 64)
    (c : s.gpr .s7 = BitVec.ofNat 64 k) :
    WP isa (mulMod z y x a m t) s fun u => Ws u B Z w N ∧
      Frame B w (mulArrs y x a t) [sB, sC] s.mem u.mem ∧ Keep (.s7 :: opRegs) s u ∧ u.gpr .s7 = 0 ∧
      (num s.mem B w z = 0 → num s.mem B w a < num s.mem B w m → num s.mem B w x < num s.mem B w m →
        2 * num s.mem B w m ≤ 2 ^ (64 * w) →
        num u.mem B w a = (num s.mem B w a + num s.mem B w y % 2 ^ k * num s.mem B w x) % num s.mem B w m) := by
  obtain start : MulI s B Z w N z y x a m t k 0 s :=
    ⟨h, Frame.refl _ _ _ _ _, Keep.refl _ _, by rw [c, Nat.sub_zero], by rw [Nat.pow_zero, Nat.div_one],
      fun _ hA hX _ => ⟨by rw [Nat.pow_zero, Nat.mod_one, Nat.zero_mul, Nat.add_zero, Nat.mod_eq_of_lt hA],
        by rw [Nat.pow_zero, Nat.one_mul, Nat.mod_eq_of_lt hX]⟩⟩
  refine WP.mono (wp_countdown (body := mulModStep z y x a m t) (cnt := .s7) (N := k) hk' hk
    (MulI s B Z w N z y x a m t k) (fun i hik u inv _ => mulModBody_ok hN hi hik inv) start c)
    fun u inv => ⟨inv.ws, inv.frame, inv.regs, by rw [inv.cnt, Nat.sub_self]; rfl,
      fun hZ hA hX hM => (inv.value hZ hA hX hM).1⟩

end VG.Proof.Rsa.RISCV64.Keys

end

end

/-! # The checks of an RSA key on RISC-V: the steps

As on PPC64LE (`Proof/Rsa/PPC64LE/KcOps.lean`), each from `Stg`: copies,
clearing a low bit, comparisons and'ed into the mask (`ltA_ok`, `eqA_ok`),
products modulo a number (`mulA_ok`) and divisions (`divA_ok`); and the
Montgomery checks' steps: the modulus `m` (`setM_ok`), Montgomery products
on the arrays 16–23 (`mont_ok`), the low product (`mulLow_ok`) and a
selection (`sel_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.KeyCheck

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys
open VG.Impl.Rsa.RISCV64.Keys (seqs copy clrLow orOne eqS sel ptr mov andS stBorrow mulMod sOdd sB sC)
open VG.Impl.Rsa.RISCV64.KeyCheck
open VG.Proof.Rsa.KeyWorkspace (upd upd_ne upd_self)

theorem kc_seqs_cons {c : Prog isa} {l : List (Prog isa)} (hl : l ≠ []) {s : State} {Q : State → Prop} :
    WP isa (seqs (c :: l)) s Q ↔ WP isa c s (fun t => WP isa (seqs l) t Q) := by
  match l, hl with
  | _ :: _, _ => exact WP.seq_iff

theorem kc_seqs_append {l₁ l₂ : List (Prog isa)} (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) {s : State}
    {Q : State → Prop} :
    WP isa (seqs (l₁ ++ l₂)) s Q ↔ WP isa (seqs l₁) s (fun t => WP isa (seqs l₂) t Q) := by
  induction l₁ generalizing s with
  | nil => exact absurd rfl h₁
  | cons c l ih =>
    rcases l with _ | ⟨d, l⟩
    · exact kc_seqs_cons h₂
    · rw [List.cons_append, kc_seqs_cons (by simp), kc_seqs_cons (by simp)]
      exact ⟨fun h => WP.mono h fun t ht => (ih (by simp)).mp ht,
        fun h => WP.mono h fun t ht => (ih (by simp)).mpr ht⟩

theorem opRegs_body : ∀ x ∈ opRegs, x ∈ bodyRegs := by decide

/-- `copy o a`, `o` then tracked. -/
theorem Stg.copy_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {o a : Nat} (ho : o < nArr) (ha : a ∈ live) (hoa : o ≠ a) :
    WP isa (copy o a) s (Stg g s0 (upd A o (A a)) (o :: live) c) := by
  refine WP.mono (Keys.copy_ok h.ws ho (h.live_lt a ha) (by decide) hoa) fun t ⟨ht, k, e, r, out⟩ => ?_
  refine h.next ht k (by simpa using ho) (by simp) r opRegs_body ?_ ?_ ?_ (h.mask_keep k (by simp))
  · have e' : num t.mem g.B g.w o = A a := e.trans (h.arrs.get ha)
    exact (h.arrs_write k e' (fun j _ => (Decidable.em (j = o)).imp_right fun n => by simpa using n)
      (by simp)).cons (by rw [upd_self]; exact e')
  · intro j hj
    rcases List.mem_cons.mp hj with rfl | hj'
    · exact ho
    · exact h.live_lt j hj'
  · by_cases hv : o = aVD
    · subst hv
      have hS : S g.w = 8 * (g.w + 2) := rfl
      rw [out.word (by omega_using []) (by have := h.ws.fit64 (j := aVD) (by decide); omega_using [hS, this]), h.vdTop]
    · exact h.vd_keep k (by simpa using hv) (by simp)

/-- `clrLow j`, for `j` not the divisor. -/
theorem Stg.clrLow_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {j : Nat} (hj : j ∈ live) (hjv : j ≠ aVD) :
    WP isa (.block (clrLow j)) s (Stg g s0 (upd A j (2 * (A j / 2))) live c) := by
  refine WP.mono (Keys.clrLow_ok h.ws (h.live_lt j hj) (by decide)) fun t ⟨ht, k, e, r⟩ => ?_
  exact h.next ht k (by simpa using h.live_lt j hj) (by simp) r opRegs_body
    (h.arrs_write k (by rw [e, h.arrs.get hj, Nat.mul_comm]) (fun i _ => (Decidable.em (i = j)).imp_right fun n => by
      simpa using n) (by simp)) h.live_lt (h.vd_keep k (by simpa using hjv) (by simp))
    (h.mask_keep k (by simp))

/-- The check in `sF` and'ed into the mask. -/
theorem Stg.acc_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c d : Bool}
    (h : Stg g s0 A live c s) (hf : slot s.mem g.B sF = if d then 1 else 0) :
    WP isa (.block acc) s (Stg g s0 A live (c && d)) := by
  refine WP.mono (andS_ok h.ws (d := sMask) (a := sMask) (b := sF) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (bit_le h.mask) (bit_le hf)) fun t ⟨ht, k, e, r⟩ => ?_
  refine h.next ht k (by simp) (by decide) r opRegs_body (h.arrs_keep k (by simp) (by decide)) h.live_lt
    (h.vd_keep k (by simp) (by decide)) ?_
  rw [e, acc_bits h.mask hf]

/-- `ltA a b`: the mask and'ed with `[a] < [b]`, which the slot `sF` holds. -/
theorem Stg.ltA_ok' {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {a b : Nat} (ha : a ∈ live) (hb : b ∈ live) (hW : aW ∉ live) :
    WP isa (seqs (ltA a b)) s fun t => slot t.mem g.B sF = (if A a < A b then 1 else 0) ∧
      Stg g s0 A live (c && decide (A a < A b)) t := by
  have na := h.live_lt a ha
  have nb := h.live_lt b hb
  have hWa : aW ≠ a := fun e => hW (e ▸ ha)
  have hWb : aW ≠ b := fun e => hW (e ▸ hb)
  rw [ltA, kc_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h.ws (o := aW) (a := a) (b := b) (by decide) na nb (by decide) hWa hWb)
    fun t1 ⟨h1, k1, v1, b1, r1⟩ => ?_
  have g1 : Stg g s0 A live c t1 :=
    h.next h1 k1 (by decide) (by simp) r1 opRegs_body
      (h.arrs_keep k1 (fun j hj e => hW (by simp at e; exact e ▸ hj)) (by simp)) h.live_lt
      (h.vd_keep k1 (by decide) (by simp)) (h.mask_keep k1 (by simp))
  rw [show seqs [.block (stBorrow sF ++ acc)] = .block (stBorrow sF ++ acc) from rfl, WP.block_append_iff]
  refine WP.mono (stBorrow_ok h1 (sl := sF) (by decide) (by decide)) fun t2 ⟨h2, k2, s2, r2⟩ => ?_
  have g2 : Stg g s0 A live c t2 :=
    g1.next h2 k2 (by simp) (by decide) r2 (by simp) (g1.arrs_keep k2 (by simp) (by decide))
      g1.live_lt (g1.vd_keep k2 (by simp) (by decide)) (g1.mask_keep k2 (by decide))
  suffices hF : slot t2.mem g.B sF = if decide (A a < A b) then 1 else 0 by
    refine WP.mono (andS_ok g2.ws (d := sMask) (a := sMask) (b := sF) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (bit_le g2.mask) (bit_le hF)) fun t ⟨ht, k, e, r⟩ => ⟨?_, ?_⟩
    · rw [k.slot (by decide) (by decide), hF]; simp
    · refine g2.next ht k (by simp) (by decide) r opRegs_body (g2.arrs_keep k (by simp) (by decide))
        g2.live_lt (g2.vd_keep k (by simp) (by decide)) ?_
      rw [e, acc_bits g2.mask hF]
  rw [s2]
  have lo : num t1.mem g.B g.w aW < 2 ^ (64 * g.w) := wordsVal_lt _ _ _ _
  have la : num s.mem g.B g.w a < 2 ^ (64 * g.w) := wordsVal_lt _ _ _ _
  have lb : num s.mem g.B g.w b < 2 ^ (64 * g.w) := wordsVal_lt _ _ _ _
  rw [h.arrs.get ha, h.arrs.get hb] at v1
  rw [h.arrs.get ha] at la
  rw [h.arrs.get hb] at lb
  by_cases hlt : A a < A b
  · have : (t1.gpr .t4).toNat = 1 := by
      rcases Nat.lt_or_ge (t1.gpr .t4).toNat 1 with e | e
      · have : (t1.gpr .t4).toNat = 0 := by omega_using [e]
        rw [this, Nat.mul_zero, Nat.add_zero] at v1; omega
      · omega_using [b1, e]
    simp [hlt, this]
  · have : (t1.gpr .t4).toNat = 0 := by
      rcases Nat.lt_or_ge (t1.gpr .t4).toNat 1 with e | e
      · omega_using [e]
      · have : (t1.gpr .t4).toNat = 1 := by omega_using [b1, e]
        rw [this, Nat.mul_one] at v1; omega
    simp [hlt, this]

/-- `ltA a b`: the mask and'ed with `[a] < [b]`. -/
theorem Stg.ltA_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {a b : Nat} (ha : a ∈ live) (hb : b ∈ live) (hW : aW ∉ live) :
    WP isa (seqs (ltA a b)) s (Stg g s0 A live (c && decide (A a < A b))) :=
  WP.mono (h.ltA_ok' ha hb hW) fun _ h => h.2

/-- `eqA a b`: the mask and'ed with `[a] = [b]`. -/
theorem Stg.eqA_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {a b : Nat} (ha : a ∈ live) (hb : b ∈ live) :
    WP isa (seqs (eqA a b)) s (Stg g s0 A live (c && decide (A a = A b))) := by
  have na := h.live_lt a ha
  have nb := h.live_lt b hb
  rw [eqA, kc_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (eqS_ok h.ws (d := sF) (a := a) (b := b) na nb (by decide) (by decide) (by decide))
    fun t1 ⟨h1, k1, e1, r1⟩ => ?_
  have g1 : Stg g s0 A live c t1 :=
    h.next h1 k1 (by simp) (by decide) r1 opRegs_body (h.arrs_keep k1 (by simp) (by decide)) h.live_lt
      (h.vd_keep k1 (by simp) (by decide)) (h.mask_keep k1 (by decide))
  rw [show seqs [.block acc] = .block acc from rfl]
  refine g1.acc_ok ?_
  rw [e1, h.arrs.get ha, h.arrs.get hb]
  by_cases he : A a = A b <;> simp [he]

/-- `33` into `s7`. -/
theorem cnt33_ok (u : State) :
    WP isa (.block cnt33) u fun u' => (u'.gpr .s7 = BitVec.ofNat 64 33 ∧ u'.mem = u.mem) ∧ Keep [.s7] u u' := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  have e : exec (.li .s7 33) u = some (u.write .s7 (BitVec.ofNat 64 33)) := by
    rw [exec_li (by decide)]; rfl
  brun [cnt33, e]

/-- `mulA y x m cnt`: `[aA] := ([y] mod 2^k) [x] mod [m]`, `k` the count `cnt` sets. -/
theorem Stg.mulA_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {y x m : Nat} {cnt : List Instr} {k : Nat}
    (hy : y ∈ live) (hx : x ∈ live) (hm : m ∈ live) (hz : aZ ∈ live) (hA0 : A aZ = 0)
    (hmi : MulIdx nArr aZ aY aX aA m aT) (hxY : x ≠ aY)
    (hfree : ∀ j ∈ live, j = aA ∨ j ∉ mulArrs aY aX aA aT) (hk : 0 < k) (hk' : k < 2 ^ 64)
    (hcnt : ∀ u : State, Keep bodyRegs s0 u → WP isa (.block cnt) u fun u' =>
      (u'.gpr .s7 = BitVec.ofNat 64 k ∧ u'.mem = u.mem) ∧ Keep [.s7] u u') :
    WP isa (seqs (mulA y x m cnt)) s fun t => ∃ R,
      (A x < A m → 2 * A m ≤ 2 ^ (64 * g.w) → R = A y % 2 ^ k * A x % A m) ∧
      Stg g s0 (upd A aA R) (aA :: live) c t := by
  have free : ∀ j ∈ live, j ≠ aA → j ≠ aY ∧ j ≠ aX ∧ j ∉ mulArrs aY aX aA aT := fun j hj hja => by
    rcases hfree j hj with e | n
    · exact absurd e hja
    · exact ⟨fun e => n (by simp [e]), fun e => n (by simp [e]), n⟩
  have yY : y ≠ aY := by
    rcases hfree y hy with e | n
    · rw [e]; decide
    · exact fun e => n (by simp [e])
  unfold mulA
  rw [kc_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (h.copy_ok (o := aY) (a := y) (by decide) hy yY.symm) fun t1 h1 => ?_
  rw [kc_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (h1.copy_ok (o := aX) (a := x) (by decide) (List.mem_cons_of_mem _ hx) (fun e => ?_))
    fun t2 h2 => ?_
  · rcases hfree x hx with e' | n
    · exact absurd (e.trans e') (by decide)
    · exact n (by simp [← e])
  rw [kc_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (h2.copy_ok (o := aA) (a := aZ) (by decide)
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hz)) (by decide)) fun t3 h3 => ?_
  rw [kc_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (hcnt t3 h3.regs) fun t4 ⟨⟨c4, m4⟩, u4⟩ => ?_
  have k4 : Keys.Frame g.B g.w [] [] t3.mem t4.mem := by
    rw [m4]; exact Keys.Frame.refl _ _ _ _ _
  have h4 := h3.next (h3.ws.of_keep u4) k4 (by simp) (by simp) u4 (by decide)
    (h3.arrs_keep k4 (by simp) (by simp)) h3.live_lt (h3.vd_keep k4 (by simp) (by simp))
    (h3.mask_keep k4 (by simp))
  rw [show seqs [mulMod aZ aY aX aA m aT] = mulMod aZ aY aX aA m aT from rfl]
  refine WP.mono (mulMod_ok h4.ws (by decide) hmi hk hk' c4) fun t ⟨ht, k5, r5, _, v5⟩ => ?_
  obtain ⟨_, _, _, _, _, _, _, _, _, hzm, _, _, hym, _, hxm, ham⟩ := hmi
  have gZ : num t4.mem g.B g.w aZ = 0 := by
    rw [h4.arrs.get (by simp [hz]), upd_ne (j := aA) _ _ (by decide), upd_ne (j := aX) _ _ (by decide),
      upd_ne (j := aY) _ _ (by decide), hA0]
  have gA : num t4.mem g.B g.w aA = 0 := by
    rw [h4.arrs.get (by simp), upd_self, upd_ne (j := aX) _ _ (by decide), upd_ne (j := aY) _ _ (by decide), hA0]
  have gY : num t4.mem g.B g.w aY = A y := by
    rw [h4.arrs.get (by simp), upd_ne (j := aA) _ _ (by decide), upd_ne (j := aX) _ _ (by decide), upd_self]
  have gX : num t4.mem g.B g.w aX = A x := by
    rw [h4.arrs.get (by simp), upd_ne (j := aA) _ _ (by decide), upd_self, upd_ne (j := aY) _ _ hxY]
  have gM : num t4.mem g.B g.w m = A m := by
    rw [h4.arrs.get (by simp [hm]), upd_ne (j := aA) _ _ (Ne.symm ham), upd_ne (j := aX) _ _ (Ne.symm hxm),
      upd_ne (j := aY) _ _ (Ne.symm hym)]
  refine ⟨num t.mem g.B g.w aA, fun hlt hM => ?_, ?_⟩
  · rw [gZ, gA, gX, gM, gY] at v5
    rw [v5 rfl (by omega_using [hlt]) hlt hM,
      Nat.zero_add]
  · refine h4.next ht k5 (by decide) (by decide) r5 (by decide) ?_
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

/-- `divA a d len`: `[a] / [d]` in `aVQ`, `[a] mod [d]` in `aVR`, for `[d]`
below `2^(8 L)`, `L` in `len` from the start. -/
theorem Stg.divA_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {a d : Nat} (ha : a ∈ live) (hd : d ∈ live)
    (hfree : ∀ j ∈ live, j ∉ [aVQ, aVR, aVD, aVT]) {len : Reg} {L : Nat}
    (hl : s0.gpr len = BitVec.ofNat 64 L) (hlb : len ∉ bodyRegs) (hL1 : 1 ≤ L) (hLw : L ≤ 8 * g.w)
    (hD : A d < 2 ^ (8 * L)) :
    WP isa (seqs (divA a d len)) s fun t => ∃ Xq Xr, (0 < A d → Xr = A a % A d ∧ Xq = A a / A d) ∧
      Stg g s0 (upd (upd A aVQ Xq) aVR Xr) (aVR :: aVQ :: live) c t := by
  have aQ : a ≠ aVQ := fun e => hfree a ha (by simp [e])
  have dQ : d ≠ aVQ := fun e => hfree d hd (by simp [e])
  have dD : d ≠ aVD := fun e => hfree d hd (by simp [e])
  unfold divA
  rw [kc_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (h.copy_ok (o := aVQ) (a := a) (by decide) ha (Ne.symm aQ)) fun t1 h1 => ?_
  rw [kc_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (h1.copy_ok (o := aVD) (a := d) (by decide) (List.mem_cons_of_mem _ hd) (Ne.symm dD))
    fun t2 h2 => ?_
  rw [show seqs [VG.Impl.Rsa.RISCV64.Div.divL aVQ aVR aVD len] = VG.Impl.Rsa.RISCV64.Div.divL aVQ aVR aVD len
    from rfl]
  have fq : num t2.mem g.B g.w aVQ = A a := by
    rw [h2.arrs.get (by simp), upd_ne (j := aVD) _ _ (by decide), upd_self]
  have fd : num t2.mem g.B g.w aVD = A d := by
    rw [h2.arrs.get (by simp), upd_self, upd_ne _ _ dQ]
  refine WP.mono (divL_ok h2.ws (q := aVQ) (r := aVR) (d := aVD) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ((h2.regs.gpr hlb).trans hl) hL1 hLw h2.vdTop
    (by rw [fd]; exact hD))
    fun t ⟨ht, k, r, _, v⟩ => ⟨num t.mem g.B g.w aVQ, num t.mem g.B g.w aVR, fun pos => ?_, ?_⟩
  · obtain ⟨vq, -, vr, -⟩ := v (by rw [fd]; exact pos)
    rw [fq, fd] at vq vr
    exact ⟨vr, vq⟩
  · refine h2.next ht k (by decide) (by simp) r (by decide) ?_ ?_ (h2.vd_keep k (by decide) (by simp))
      (h2.mask_keep k (by simp))
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · rw [upd_self]
      rcases List.mem_cons.mp hj with rfl | hj
      · rw [upd_ne _ _ (by decide), upd_self]
      have hn := hfree j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
      rw [upd_ne _ _ hn.2.1, upd_ne _ _ hn.1, k.num (by simp; omega_using [hn]) (by simp)
        (h.ws.fit64 (h.live_lt j hj)), h2.arrs.get (by simp [hj]), upd_ne _ _ hn.2.2.1, upd_ne _ _ hn.1]
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · decide
      rcases List.mem_cons.mp hj with rfl | hj
      · decide
      exact h.live_lt j hj

/-! ## The Montgomery checks' steps -/

/-- `eqS sF a b`: the slot `sF` := `[a] = [b]`. -/
theorem Stg.eqS_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {a b : Nat} (ha : a ∈ live) (hb : b ∈ live) :
    WP isa (eqS sF a b) s fun t => slot t.mem g.B sF = (if A a = A b then 1 else 0) ∧
      Stg g s0 A live c t := by
  refine WP.mono (Keys.eqS_ok h.ws (d := sF) (a := a) (b := b) (h.live_lt a ha) (h.live_lt b hb) (by decide)
    (by decide) (by decide)) fun t ⟨ht, k, e, r⟩ => ⟨by rw [e, h.arrs.get ha, h.arrs.get hb], ?_⟩
  exact h.next ht k (by simp) (by decide) r opRegs_body (h.arrs_keep k (by simp) (by decide)) h.live_lt
    (h.vd_keep k (by simp) (by decide)) (h.mask_keep k (by decide))

/-- `orOne j`, for `j` not the divisor. -/
theorem Stg.orOne_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {j : Nat} (hj : j ∈ live) (hjv : j ≠ aVD) :
    WP isa (.block (orOne j)) s (Stg g s0 (upd A j (A j / 2 * 2 + 1)) live c) := by
  refine WP.mono (Keys.orOne_ok h.ws (h.live_lt j hj) (by decide)) fun t ⟨ht, k, e, r⟩ => ?_
  exact h.next ht k (by simpa using h.live_lt j hj) (by simp) r opRegs_body
    (h.arrs_write k (by rw [e, h.arrs.get hj]) (fun i _ => (Decidable.em (i = j)).imp_right fun n => by
      simpa using n) (by simp)) h.live_lt (h.vd_keep k (by simpa using hjv) (by simp))
    (h.mask_keep k (by simp))

/-- `orSlot2 j sl`: the low word of `[j]` or'ed with the slot `sl` shifted left. -/
theorem orSlot2_ws_ok {s : State} {B : Addr} {Z w N j sl : Nat} (h : Ws s B Z w N) (hj : j < N)
    (hN : N ≤ 2048) (hsl : sl + 8 ≤ hdr) (hsl8 : sl % 8 = 0) :
    WP isa (.block (orSlot2 j sl)) s fun t => Ws t B Z w N ∧ Keys.Frame B w [j] [] s.mem t.mem ∧
      num t.mem B w j = (word s.mem B (arr w j) ||| word s.mem B sl <<< 1).toNat +
        2 ^ 64 * (num s.mem B w j / 2 ^ 64) ∧ Keep opRegs s t := by
  have fit := h.fit64 hj
  have fit' := h.arr_fit hj
  have nw := h.nowrap
  have hS : S w = 8 * (w + 2) := rfl
  have hz := h.hdr_le
  have := h.wpos
  unfold orSlot2
  rw [← List.append_nil (ptr .t0 j ++ _), List.append_assoc]
  refine ptr_ok h (by decide) (by decide) (show j < 2048 by omega_arith) ?_
  have hk : WP isa (.block ([.load .d .t5 .t0 0, .load .d .t6 .s11 sl, .shift .sll .d .t6 .t6 1,
        .logic .or .t5 .t5 .t6, .store .d .t5 .t0 0] ++ []))
      (s.write .t0 (off B (arr w j))) fun u =>
        (u.mem = s.mem.writeW (off B (arr w j)) (word s.mem B (arr w j) ||| word s.mem B sl <<< 1)) ∧
          Keep [.t5, .t6] (s.write .t0 (off B (arr w j))) u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [h.s11, h.scr.ld (d := arr w j) (n := 8) (by omega_arith),
      h.scr.al8 (d := arr w j) (by omega_arith) (arr_al _ _),
      h.scr.st (d := arr w j) (n := 8) (by omega_arith),
      h.scr.ld (d := sl) (n := 8) (by omega_arith), h.scr.al8 (d := sl) (by omega_arith) hsl8,
      show sl < 2048 by simp only [hdr_eq] at hsl; omega_arith]
  refine WP.mono hk fun u ⟨mu, ku⟩ => ?_
  have kt : Keep opRegs s u := ((Keep.write _ _ _).trans ku).mono (by decide)
  have lw := low_write (m := s.mem) (B := B) h.wpos fit (word s.mem B (arr w j) ||| word s.mem B sl <<< 1)
  rw [← mu] at lw
  exact ⟨h.of_keep kt, lw.1, lw.2, kt⟩

/-- `orSlot2 j sF`, the slot 1 only when `[j] = 1`: `[j]` plus twice the slot. -/
theorem Stg.orSlot2_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {j : Nat} (hj : j ∈ live) (hjv : j ≠ aVD) {f : Nat}
    (hf : slot s.mem g.B sF = f) (hf1 : f ≤ 1) (hf2 : f = 1 → A j = 1) :
    WP isa (.block (orSlot2 j sF)) s (Stg g s0 (upd A j (A j + 2 * f)) live c) := by
  have hjn := h.live_lt j hj
  refine WP.mono (orSlot2_ws_ok h.ws hjn (by decide) (by decide) (by decide)) fun t ⟨ht, k, e, r⟩ => ?_
  have val : num t.mem g.B g.w j = A j + 2 * f := by
    rw [e, ← h.arrs.get hj]
    have m64 := wordsVal_mod64 s.mem g.B (d := arr g.w j) (k := g.w) h.ws.wpos
    have dm := Nat.div_add_mod (num s.mem g.B g.w j) (2 ^ 64)
    change num s.mem g.B g.w j % 2 ^ 64 = _ at m64
    have hw : word s.mem g.B sF = BitVec.ofNat 64 f := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hf1])]
      exact hf
    rw [hw]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hf1 with rfl | rfl
    · simp only [Nat.mul_zero, Nat.add_zero]
      rw [show (BitVec.ofNat 64 0 <<< 1 : BitVec 64) = 0#64 by decide, BitVec.or_zero, ← m64]
      omega_using []
    · have a1 : num s.mem g.B g.w j = 1 := (h.arrs.get hj).trans (hf2 rfl)
      have w1 : word s.mem g.B (arr g.w j) = 1#64 := by
        apply BitVec.eq_of_toNat_eq
        rw [← m64, a1]; rfl
      rw [w1, a1, show (1#64 ||| BitVec.ofNat 64 1 <<< 1 : BitVec 64) = 3#64 by decide]
      rfl
  exact h.next ht k (by simpa using hjn) (by simp) r opRegs_body
    (h.arrs_write k val (fun i _ => (Decidable.em (i = j)).imp_right fun n => by simpa using n) (by simp))
    h.live_lt (h.vd_keep k (by simpa using hjv) (by simp)) (h.mask_keep k (by simp))

/-- The modulus of the Montgomery checks: `p | 1`, or 3 if that is 1. -/
def mOf (p : Nat) : Nat := if p / 2 * 2 + 1 = 1 then 3 else p / 2 * 2 + 1

theorem mOf_odd (p : Nat) : mOf p % 2 = 1 := by unfold mOf; split <;> omega_using []
theorem mOf_ge (p : Nat) : 3 ≤ mOf p := by unfold mOf; split <;> omega_arith
theorem mOf_eq {p : Nat} (h : p % 2 = 1) (h3 : 3 ≤ p) : mOf p = p := by unfold mOf; split <;> omega_arith

/-- `setM`: `[mM] := mOf p`, from `[aOne] = 1`. -/
theorem Stg.setM_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) (hP : aP ∈ live) (hO : aOne ∈ live) (hO1 : A aOne = 1) :
    WP isa (seqs setM) s (Stg g s0 (upd A mM (mOf (A aP))) (mM :: live) c) := by
  unfold setM
  rw [kc_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (h.copy_ok (o := mM) (a := aP) (by decide) hP (by decide)) fun t1 h1 => ?_
  rw [kc_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (h1.orOne_ok (j := mM) (by simp) (by decide)) fun t2 h2 => ?_
  rw [kc_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (h2.eqS_ok (a := mM) (b := aOne) (by simp) (by simp [hO])) fun t3 ⟨f3, h3⟩ => ?_
  rw [show seqs [.block (orSlot2 mM sF)] = .block (orSlot2 mM sF) from rfl]
  simp only [upd_self, upd_ne _ _ (show aOne ≠ mM by decide), hO1] at f3
  refine WP.mono (h3.orSlot2_ok (j := mM) (by simp) (by decide) f3 (by split <;> omega_using [])
    (fun e => by simp only [upd_self]; split at e <;> first | with_reducible assumption | omega)) fun t h4 => ?_
  refine (h4.congr' fun j _ => ?_)
  by_cases e : j = mM
  · subst e
    simp only [upd_self, mOf]
    split <;> omega_arith
  · simp only [upd_ne _ _ e]

/-- `16 S` and the slots of `tail`'s arrays: array `16 + j` of the key working space. -/
theorem arr_tail (w j : Nat) : arr w (16 + j) = 16 * S w + VG.Proof.Bignum.slot w j := by
  show hdr + (16 + j) * (8 * (w + 2)) = 16 * (8 * (w + 2)) + (VG.Impl.Bignum.hdrBytes + j * (8 * (w + 2)))
  rw [Nat.add_mul, hdr_eq, show VG.Impl.Bignum.hdrBytes = 256 from rfl]
  omega_arith

theorem moff_off (p : Addr) (a b : Nat) : Mont.off (Mont.off p a) b = Mont.off p (a + b) := by
  simp only [Mont.off, BitVec.add_assoc, BitVec.ofNat_add]

theorem wordsVal_off (m : Mem) (B : Addr) (c d k : Nat) :
    wordsVal m (Mont.off B c) d k = wordsVal m B (c + d) k := by
  induction k generalizing d with
  | zero => rfl
  | succ k ih =>
    simp only [wordsVal, ih, Mont.word, moff_off, Nat.add_assoc]

/-- The working space, from array 16. -/
theorem scr16 {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w nArr) :
    Scr s (Mont.off B (16 * S w)) (Z - 16 * S w) := by
  have hf := h.fits
  have nw := h.nowrap
  have h24 : arr w nArr = hdr + 24 * S w := rfl
  rw [h24, hdr_eq] at hf
  obtain ⟨⟨B₀, o, L, hm, hb, hL, hL'⟩, _, ha⟩ := h.scr
  have h16 : 16 * S w + 8 * S w ≤ Z := by omega_arith
  have hlt : 16 * S w < 2 ^ 64 := by omega_arith
  have hlt' : B.toNat + 16 * S w < 2 ^ 64 := by omega_arith
  have e : (Mont.off B (16 * S w)).toNat = B.toNat + 16 * S w := by
    simp only [Mont.off, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := 16 * S w) hlt, Nat.mod_eq_of_lt hlt']
  have hS8 : (16 * S w) % 8 = 0 := by
    show (16 * (8 * (w + 2))) % 8 = 0
    rw [Nat.mul_left_comm]; exact Nat.mul_mod_right _ _
  refine ⟨⟨B₀, o + 16 * S w, L, hm, ?_, ?_, hL'⟩, ?_, ?_⟩
  · rw [hb, moff_off]
  · have := Nat.sub_add_cancel (Nat.le_trans (Nat.le_add_right _ _) h16)
    omega_arith
  · rw [e]; have := Nat.sub_add_cancel (Nat.le_trans (Nat.le_add_right _ _) h16); omega_arith
  · rw [e]; omega_arith

/-- The registers `mont`'s setup writes. -/
abbrev montPreRegs : List Reg := [.a7, .s0, .s1, .s2, .s3, .t1, .t0, .a5, .a6, .a2, .a3, .a4]

/-- `mont`'s setup: `-[mM]⁻¹ mod 2⁶⁴` into `t1`, `w` into `t0`, and the arrays' addresses. -/
theorem mont_pre_ok {s : State} {B : Addr} {Z w : Nat} (W : Ws s B Z w nArr) {o a b : Nat}
    (ho : o < 24) (ha : a < 24) (hb : b < 24) (hodd : num s.mem B w mM % 2 = 1) :
    WP isa (.block (ptr .a7 mM ++ VG.Impl.Bignum.RISCV64.Precompute.minv ++ [mov .t0 .s9] ++ ptr .a5 (mM + 2) ++
      ptr .a6 (mM + 3) ++ ptr .a2 o ++ ptr .a3 a ++ ptr .a4 b)) s fun u =>
      u.gpr .a7 = Mont.off B (arr w mM) ∧ u.gpr .a5 = Mont.off B (arr w (mM + 2)) ∧
      u.gpr .a6 = Mont.off B (arr w (mM + 3)) ∧ u.gpr .a2 = Mont.off B (arr w o) ∧
      u.gpr .a3 = Mont.off B (arr w a) ∧ u.gpr .a4 = Mont.off B (arr w b) ∧
      u.gpr .t0 = BitVec.ofNat 64 w ∧
      ((Mont.word s.mem B (arr w mM)).toNat * (u.gpr .t1).toNat + 1) % 2 ^ 64 = 0 ∧ u.mem = s.mem ∧
      Keep montPreRegs s u := by
  have fit := W.arr_fit (j := mM) (by decide)
  have hS : S w = 8 * (w + 2) := rfl
  refine ptr_ok W (r := .a7) (by decide) (by decide) (show mM < 2048 by decide) ?_
  show WP isa (.block (VG.Impl.Bignum.RISCV64.Precompute.minv ++ ([mov .t0 .s9] ++ (ptr .a5 (mM + 2) ++
    (ptr .a6 (mM + 3) ++ (ptr .a2 o ++ (ptr .a3 a ++ ptr .a4 b))))))) _ _
  rw [WP.block_append_iff]
  have W1 := W.of_keep (Keep.write s .a7 (Mont.off B (arr w mM)))
  have hodd' : (Mont.word (s.write .a7 (Mont.off B (arr w mM))).mem B (arr w mM)).toNat % 2 = 1 := by
    rw [mem_write, ← wordsVal_mod2 _ _ W.wpos]; exact hodd
  refine WP.mono (minv_ok W1.scr (d := arr w mM) (gpr_write_self _ _ _) (arr_al _ _) (by omega_arith) hodd')
    fun t1 ⟨⟨hinv, m1⟩, k1⟩ => ?_
  have W2 := W1.of_keep k1
  have t9 : t1.gpr .s9 = BitVec.ofNat 64 w := W2.s9
  rw [WP.block_append_iff]
  have hm : WP isa (.block [mov .t0 .s9]) t1 fun v =>
      (v.gpr .t0 = BitVec.ofNat 64 w ∧ v.mem = t1.mem) ∧ Keep [.t0] t1 v := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [mov, add_ofNat_zero', t9]
  refine WP.mono hm fun t2 ⟨⟨e0, m2⟩, k2⟩ => ?_
  have W3 := W2.of_keep k2
  have a7 : t2.gpr .a7 = Mont.off B (arr w mM) := by
    rw [k2.gpr (by decide), k1.gpr (by decide), gpr_write_self]
  have t1' : t2.gpr .t1 = t1.gpr .t1 := k2.gpr (by decide)
  have mm : t2.mem = s.mem := by rw [m2, m1, mem_write]
  have kk : Keep (([.a7] ++ [.s0, .s1, .s2, .s3, .t1]) ++ [.t0]) s t2 :=
    ((Keep.write s .a7 _).trans k1).trans k2
  show WP isa (.block (ptr .a5 (mM + 2) ++ (ptr .a6 (mM + 3) ++ (ptr .a2 o ++ (ptr .a3 a ++ ptr .a4 b))))) _ _
  refine ptr_ok W3 (r := .a5) (by decide) (by decide) (show mM + 2 < 2048 by decide) ?_
  show WP isa (.block (ptr .a6 (mM + 3) ++ (ptr .a2 o ++ (ptr .a3 a ++ ptr .a4 b)))) _ _
  refine ptr_ok (W3.of_keep (Keep.write _ _ _)) (r := .a6) (by decide) (by decide)
    (show mM + 3 < 2048 by decide) ?_
  show WP isa (.block (ptr .a2 o ++ (ptr .a3 a ++ ptr .a4 b))) _ _
  refine ptr_ok ((W3.of_keep (Keep.write _ _ _)).of_keep (Keep.write _ _ _)) (r := .a2) (by decide)
    (by decide) (show o < 2048 by omega_using [ho]) ?_
  show WP isa (.block (ptr .a3 a ++ ptr .a4 b)) _ _
  refine ptr_ok (((W3.of_keep (Keep.write _ _ _)).of_keep (Keep.write _ _ _)).of_keep (Keep.write _ _ _))
    (r := .a3) (by decide) (by decide) (show a < 2048 by omega_using [ha]) ?_
  show WP isa (.block (ptr .a4 b ++ [])) _ _
  refine ptr_ok ((((W3.of_keep (Keep.write _ _ _)).of_keep (Keep.write _ _ _)).of_keep
    (Keep.write _ _ _)).of_keep (Keep.write _ _ _)) (r := .a4) (by decide) (by decide)
    (show b < 2048 by omega_using [hb]) ?_
  refine WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_write, reduceCtorEq, ite_false, a7]
  · simp only [gpr_write, reduceCtorEq, ite_false, ite_true]
  · simp only [gpr_write, reduceCtorEq, ite_false, ite_true]
  · simp only [gpr_write, reduceCtorEq, ite_false, ite_true]
  · simp only [gpr_write, reduceCtorEq, ite_false, ite_true]
  · simp only [gpr_write, reduceCtorEq, ite_false, ite_true]
  · simp only [gpr_write, reduceCtorEq, ite_false, e0]
  · simp only [gpr_write, reduceCtorEq, ite_false, t1']
    simpa only [mem_write] using hinv
  · simp only [mem_write, mm]
  · exact ((((((kk.trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).trans
      (Keep.write _ _ _)).trans (Keep.write _ _ _))).mono (by decide)

/-- `mont o a b`: `[o] := [a] [b] R⁻¹ mod [mM]`, `R = 2^(64 w)`, for `[mM]` odd and `[b] < [mM]`. -/
theorem Stg.mont_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) (hw2 : 2 ≤ g.w) {o a b : Nat}
    (ho : o ∈ [mA, mB, mO, mO2]) (ha : a ∈ [mA, mB, mO, mO2]) (hb : b ∈ [mA, mB, mO, mO2])
    (hM : mM ∈ live) (ha' : a ∈ live) (hb' : b ∈ live) (hodd : A mM % 2 = 1) (hlt : A b < A mM)
    (hfree : ∀ j ∈ live, j ≠ mM + 2 ∧ j ≠ mM + 3) :
    WP isa (mont o a b) s fun t => ∃ R, (R < A mM ∧ R * 2 ^ (64 * g.w) % A mM = A a * A b % A mM) ∧
      Stg g s0 (upd A o R) (o :: live) c t := by
  have rel : ∀ x ∈ [mA, mB, mO, mO2], ∃ x', x = 16 + x' ∧ x' < 8 ∧ x' ≠ 0 ∧ x' ≠ 2 ∧ x' ≠ 3 := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    exacts [⟨1, rfl, by decide⟩, ⟨4, rfl, by decide⟩, ⟨5, rfl, by decide⟩, ⟨6, rfl, by decide⟩]
  obtain ⟨o', rfl, o8, -, o2, o3⟩ := rel o ho
  obtain ⟨a', rfl, a8, -, a2, -⟩ := rel a ha
  obtain ⟨b', rfl, b8, -, b2, -⟩ := rel b hb
  have W := h.ws
  have fits := W.fits
  have nw := W.nowrap
  have hlt64 : 16 * S g.w < 2 ^ 64 := by
    have : arr g.w nArr = 256 + 24 * S g.w := rfl
    omega_arith
  have addr : ∀ j, Mont.off (Mont.off g.B (16 * S g.w)) (VG.Proof.Bignum.slot g.w j) =
      Mont.off g.B (arr g.w (16 + j)) := fun j => by rw [moff_off, arr_tail]
  have wv : ∀ (m : Mem) j, wordsVal m (Mont.off g.B (16 * S g.w)) (VG.Proof.Bignum.slot g.w j) g.w =
      num m g.B g.w (16 + j) := fun m j => by rw [wordsVal_off, ← arr_tail]
  have hoddM : num s.mem g.B g.w mM % 2 = 1 := by rw [h.arrs.get hM]; exact hodd
  unfold mont
  rw [WP.seq_iff]
  refine WP.mono (mont_pre_ok W (o := 16 + o') (a := 16 + a') (b := 16 + b') (by omega_using [o8]) (by omega_using [a8])
    (by omega_using [b8]) hoddM) fun u ⟨u7, u5, u6, u2, u3, u4, u0, uinv, um, ku⟩ => ?_
  have hsu : Scr u (Mont.off g.B (16 * S g.w)) (g.Z - 16 * S g.w) := (scr16 W).congr ku.2.2
  have hZ : VG.Proof.Bignum.slot g.w 8 ≤ g.Z - 16 * S g.w := by
    have := arr_tail g.w 8
    have : arr g.w nArr = arr g.w (16 + 8) := rfl
    omega_arith
  have w0 : Mont.word u.mem (Mont.off g.B (16 * S g.w)) (VG.Proof.Bignum.slot g.w 0) =
      Mont.word s.mem g.B (arr g.w mM) := by
    simp only [Mont.word]; rw [addr 0, um]; rfl
  have nM : num s.mem g.B g.w (16 + 0) = A mM := h.arrs.get hM
  refine WP.mono (tail_ok hsu (o := o') (a := a') (b := b') o8 a8 b8 o2 o3 a2 b2 hw2
    (by have := W.wle; omega_using [this]) hZ (by rw [u2]; exact (addr o').symm) (by rw [u3]; exact (addr a').symm)
    (by rw [u4]; exact (addr b').symm) (by rw [u5]; exact (addr 2).symm) (by rw [u6]; exact (addr 3).symm)
    (by rw [u7]; exact (addr 0).symm) u0 (by rw [w0]; exact uinv)
    (by rw [wv, wv, um, h.arrs.get hb', nM]; exact hlt))
    fun t ⟨⟨r1, r2, ar⟩, kt⟩ => ?_
  rw [wv, wv, um, nM] at r1
  rw [wv, wv, wv, wv, um, nM, h.arrs.get ha', h.arrs.get hb'] at r2
  have fr : Keys.Frame g.B g.w [16 + 2, 16 + 3, 16 + o'] [] s.mem t.mem := by
    intro x hx
    rw [← um]
    refine ar x fun j hj => ?_
    have hj' : (arr g.w (16 + j), S g.w) ∈ ranges g.w [16 + 2, 16 + 3, 16 + o'] [] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      simp only [ranges, List.map_cons, List.map_nil, List.append_nil, List.mem_cons, List.not_mem_nil,
        or_false]
      rcases hj with rfl | rfl | rfl <;> simp
    have hx' := hx _ hj'
    have hjl : j < 8 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; omega_using [o8, hj]
    have f24 : arr g.w (16 + j) + S g.w ≤ 2 ^ 64 := W.fit64 (by simp only [nArr]; omega_using [hjl])
    have e := arr_tail g.w j
    have hr : (16 * S g.w ≤ ofs g.B x ∧ ofs (Mont.off g.B (16 * S g.w)) x = ofs g.B x - 16 * S g.w) ∨
        (ofs g.B x < 16 * S g.w ∧ 2 ^ 64 - 16 * S g.w ≤ ofs (Mont.off g.B (16 * S g.w)) x) :=
      VG.Proof.Bignum.ofs_rebase g.B x hlt64
    simp only [S, VG.Proof.Bignum.ofs, Mont.ofs] at hx' e f24 hr ⊢
    rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h2]; omega_arith
    · omega_arith
  refine ⟨num t.mem g.B g.w (16 + o'), ⟨r1, r2⟩, ?_⟩
  have hjs : ∀ j ∈ [16 + 2, 16 + 3, 16 + o'], j < nArr := by
    intro j hj
    simp only [nArr, List.mem_cons, List.not_mem_nil, or_false] at hj ⊢
    omega_using [o8, hj]
  have hvd : ∀ j ∈ [16 + 2, 16 + 3, 16 + o'], j ≠ aVD := by
    intro j hj
    simp only [aVD, List.mem_cons, List.not_mem_nil, or_false] at hj ⊢
    omega_using [hj]
  refine h.next (W.of_keep (ku.trans kt)) fr hjs (by simp) (ku.trans kt) (by decide) ?_ ?_
    (h.vd_keep fr hvd (by simp)) (h.mask_keep fr (by simp))
  · refine (h.arrs_write fr rfl (fun j hj => ?_) (by simp)).cons (by rw [upd_self])
    have := hfree j hj
    by_cases e : j = 16 + o'
    · exact .inl e
    · right; simp only [List.mem_cons, List.not_mem_nil, or_false, mM] at this ⊢; omega_using [this, e]
  · intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · simp only [nArr]; omega_using [o8]
    · exact h.live_lt j hj

/-- `sel o a b sF`: `[o] := [a]` if the slot `sF` is 0, else `[b]`. -/
theorem Stg.sel_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {o a b : Nat} (ho : o < nArr) (ha : a ∈ live) (hb : b ∈ live)
    (hoa : o ≠ a) (hob : o ≠ b) (hov : o ≠ aVD) {f : Nat} (hf : slot s.mem g.B sF = f) (hf1 : f ≤ 1) :
    WP isa (sel o a b sF) s (Stg g s0 (upd A o (if f = 0 then A a else A b)) (o :: live) c) := by
  refine WP.mono (Keys.sel_ok h.ws ho (h.live_lt a ha) (h.live_lt b hb) (by decide) hoa hob (by decide)
    (by decide) (by rw [hf]; exact hf1)) fun t ⟨ht, k, e, r⟩ => ?_
  have e' : num t.mem g.B g.w o = if f = 0 then A a else A b := by
    rw [e, hf, h.arrs.get ha, h.arrs.get hb]
  refine h.next ht k (by simpa using ho) (by simp) r opRegs_body
    ((h.arrs_write k e' (fun j _ => (Decidable.em (j = o)).imp_right fun n => by simpa using n)
      (by simp)).cons (by rw [upd_self]; exact e')) ?_ (h.vd_keep k (by simpa using hov) (by simp))
    (h.mask_keep k (by simp))
  intro j hj
  rcases List.mem_cons.mp hj with rfl | hj'
  · exact ho
  · exact h.live_lt j hj'

/-- `mulLow o y x`: `[o] := [y] [x] mod 2^(64 w)`, from `[o] = 0`. -/
theorem Stg.mulLow_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {o y x : Nat} (ho : o ∈ live) (hy : y ∈ live) (hx : x ∈ live)
    (hoy : o ≠ y) (hox : o ≠ x) (hov : o ≠ aVD) (hz : A o = 0) :
    WP isa (VG.Impl.Rsa.RISCV64.RecoverDet.mulLow o y x) s
      (Stg g s0 (upd A o (A y * A x % 2 ^ (64 * g.w))) live c) := by
  have hon := h.live_lt o ho
  refine WP.mono (Keys.mulLow_ok h.ws hon (h.live_lt y hy) (h.live_lt x hx) (by decide) hoy hox
    (by rw [h.arrs.get ho, hz])) fun t ⟨ht, k, _, e, r⟩ => ?_
  have e' : num t.mem g.B g.w o = A y * A x % 2 ^ (64 * g.w) := by
    rw [e, h.arrs.get hy, h.arrs.get hx]
  exact h.next ht k (by simpa using hon) (by simp) r (by decide)
    (h.arrs_write k e' (fun j _ => (Decidable.em (j = o)).imp_right fun n => by simpa using n) (by simp))
    h.live_lt (h.vd_keep k (by simpa using hov) (by simp)) (h.mask_keep k (by simp))

/-- `mulHalf o y x`: `[o] := [y] [x]`, from `[o] = 0`, for `[y]` and `[x]` below `2^(64 (w / 2))`. -/
theorem Stg.mulHalf_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {o y x : Nat} (ho : o ∈ live) (hy : y ∈ live) (hx : x ∈ live)
    (hoy : o ≠ y) (hox : o ≠ x) (hov : o ≠ aVD) (hz : A o = 0) (hw2 : g.w % 2 = 0)
    (hY : A y < 2 ^ (64 * (g.w / 2))) (hX : A x < 2 ^ (64 * (g.w / 2))) :
    WP isa (VG.Impl.Rsa.RISCV64.RecoverDet.mulHalf o y x) s
      (Stg g s0 (upd A o (A y * A x % 2 ^ (64 * g.w))) live c) := by
  have hon := h.live_lt o ho
  refine WP.mono (Keys.mulHalf_ok h.ws hon (h.live_lt y hy) (h.live_lt x hx) (by decide) hoy hox hw2
    (by rw [h.arrs.get ho, hz]) (by rw [h.arrs.get hy]; exact hY) (by rw [h.arrs.get hx]; exact hX))
    fun t ⟨ht, k, _, e, r⟩ => ?_
  have e' : num t.mem g.B g.w o = A y * A x % 2 ^ (64 * g.w) := by
    rw [e, h.arrs.get hy, h.arrs.get hx]
  exact h.next ht k (by simpa using hon) (by simp) r (by decide)
    (h.arrs_write k e' (fun j _ => (Decidable.em (j = o)).imp_right fun n => by simpa using n) (by simp))
    h.live_lt (h.vd_keep k (by simpa using hov) (by simp)) (h.mask_keep k (by simp))

end VG.Proof.Rsa.RISCV64.KeyCheck

end

end

/-! # The checks of an RSA key on RISC-V: division by words

`Stg.divWA_ok`: `divWA a d`, `[aVR] := [a] mod [d]` by words
(`Proof/Rsa/RISCV64/KeyWordDiv.lean`), exact for `2^(64 (v - 1)) ≤ [d] <
2^(64 v)`, `v = w / 2`: `aVR` zeroed, `[d]` copied to `aVD`, its top word made
not zero (`fixTop_ok`), and `divW_ok`. -/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.KeyCheck

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys
open VG.Impl.Rsa.RISCV64.Keys (seqs copy)
open VG.Impl.Rsa.RISCV64.KeyCheck
open VG.Proof.Rsa.KeyWorkspace (upd upd_ne upd_self)

/-- The arrays the checks start from. -/
abbrev live0 : List Nat := [aZ, aOne, aN, aE, aP, aQ, aDP, aDQ, aQI, aD]

/-- The arrays after `start`. -/
abbrev aStart (v : Vals) : Nat → Nat := upd (vals v) aOne 1

/-- The arrays the checks of `d` use. -/
abbrev aFin (v : Vals) : Nat → Nat := upd (upd (vals v) aM1 (2 * (v.p / 2))) aM2 (2 * (v.q / 2))
abbrev liveFin : List Nat := [aZ, aN, aD, aDP, aDQ, aM1, aM2]

/-- `divWA a d`: `[aVR] := [a] mod [d]` by words, exact for `2^(64 (v - 1)) ≤
[d] < 2^(64 v)`; `aVR` then tracked, `aVD` and `aVT` written. -/
theorem Stg.divWA_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {a d : Nat} (ha : a ∈ live) (hd : d ∈ live) (hz : aZ ∈ live) (hA0 : A aZ = 0)
    (hfree : ∀ j ∈ live, j ∉ [aVR, aVD, aVT]) (hw : 8 ≤ g.w) (hwl : g.w ≤ 128) (hw2 : g.w % 2 = 0) :
    WP isa (seqs (divWA a d)) s fun t => ∃ X,
      (2 ^ (64 * (g.w / 2 - 1)) ≤ A d → A d < 2 ^ (64 * (g.w / 2)) → X = A a % A d) ∧
      Stg g s0 (upd A aVR X) (aVR :: live) c t := by
  obtain aR : a ≠ aVR := fun e => hfree a ha (by simp [e])
  obtain aD : a ≠ aVD := fun e => hfree a ha (by simp [e])
  obtain aT : a ≠ aVT := fun e => hfree a ha (by simp [e])
  obtain dR : d ≠ aVR := fun e => hfree d hd (by simp [e])
  obtain dD : d ≠ aVD := fun e => hfree d hd (by simp [e])
  obtain zR : aZ ≠ aVR := by decide
  have hS : S g.w = 8 * (g.w + 2) := rfl
  have hwl := h.ws.wle
  unfold divWA
  rw [kc_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (h.copy_ok (o := aVR) (a := aZ) (by decide) hz (Ne.symm zR)) fun t1 h1 => ?_
  rw [kc_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (h1.copy_ok (o := aVD) (a := d) (by decide) (List.mem_cons_of_mem _ hd) (Ne.symm dD))
    fun t2 h2 => ?_
  obtain nR : num t2.mem g.B g.w aVR = 0 := by rw [h2.arrs.get (by simp), upd_ne _ _ (by decide), upd_self, hA0]
  obtain nD : num t2.mem g.B g.w aVD = A d := by rw [h2.arrs.get (by simp), upd_self, upd_ne _ _ dR]
  rw [kc_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (fixTop_ok h2.ws (m := aVD) (by decide) (by decide) (by omega_using [hw]))
    fun t3 ⟨w3, f3, v3, p3, _, _, k3, o3⟩ => ?_
  rw [show seqs [VG.Impl.Rsa.RISCV64.WordDiv.divW a aVR aVD aVT] = VG.Impl.Rsa.RISCV64.WordDiv.divW a aVR aVD aVT
    from rfl]
  obtain fitR := h.ws.fit64 (j := aVR) (by decide)
  obtain r0 : wordsVal t3.mem g.B (arr g.w aVR) (g.w / 2 + 1) = 0 := by
    rw [f3.words (fun k hk => by simp at hk; subst hk; have := arr_disj (w := g.w) (j := aVD) (k := aVR) (by decide); omega_using [hS, this])
      (by simp) (by omega_using [hS, fitR])]
    exact wordsVal_zero_part (d := arr g.w aVR) (a := 0) (c := g.w / 2 + 1) nR (by omega_using [hw]) |>.symm ▸ by simp
  refine WP.mono (divW_ok w3 (a := a) (r := aVR) (m := aVD) (t := aVT) (by decide) (h.live_lt a ha) (by decide)
    (by decide) (by decide) (Ne.symm aR) (by decide) (by decide) (by decide) aT (by omega_using [hw]) (by omega_arith) hw2 r0 p3)
    fun t ⟨w4, f4, k4, x4, top4, hi4⟩ => ?_
  -- `[a]` in `t3`, and `[aVR]`'s `w` words.
  obtain na : num t3.mem g.B g.w a = A a := by
    rw [f3.num (by simp; exact aD.symm) (by simp) (h.ws.fit64 (h.live_lt a ha)), h2.arrs.get (by simp [ha]),
      upd_ne _ _ aD, upd_ne _ _ aR]
  generalize hM : wordsVal t3.mem g.B (arr g.w aVD) (g.w / 2) = M at x4
  rw [na] at x4
  obtain hR : num t.mem g.B g.w aVR = A a % M := by
    obtain e1 := wordsVal_append t.mem g.B (arr g.w aVR) (g.w / 2) (g.w - g.w / 2)
    obtain e2 := wordsVal_append t.mem g.B (arr g.w aVR + 8 * (g.w / 2)) 1 (g.w - g.w / 2 - 1)
    rw [show g.w / 2 + (g.w - g.w / 2) = g.w by omega_using []] at e1
    rw [show 1 + (g.w - g.w / 2 - 1) = g.w - g.w / 2 by omega_using [hw], show arr g.w aVR + 8 * (g.w / 2) + 8 * 1 =
      arr g.w aVR + 8 * (g.w / 2 + 1) by omega_using [], show g.w - g.w / 2 - 1 = g.w - 1 - g.w / 2 by omega_using [], hi4] at e2
    obtain z2 : wordsVal t3.mem g.B (arr g.w aVR + 8 * (g.w / 2 + 1)) (g.w - 1 - g.w / 2) = 0 := by
      rw [f3.words (fun k hk => by simp at hk; subst hk; have := arr_disj (w := g.w) (j := aVD) (k := aVR) (by decide); omega_using [hS, this])
        (by simp) (by omega_using [hS, fitR])]
      exact wordsVal_zero_part nR (by omega_using [hw])
    obtain w1 : wordsVal t.mem g.B (arr g.w aVR + 8 * (g.w / 2)) 1 = 0 := by
      simp only [wordsVal, top4]; rfl
    rw [z2, w1, Nat.mul_zero, Nat.add_zero] at e2
    show wordsVal t.mem g.B (arr g.w aVR) g.w = _
    rw [e1, e2, Nat.mul_zero, Nat.add_zero, x4]
  obtain F : Keys.Frame g.B g.w [aVD, aVR, aVT] [] t2.mem t.mem :=
    (f3.mono (js' := [aVD, aVR, aVT]) (by simp) (by simp)).trans (f4.mono (js' := [aVD, aVR, aVT]) (by simp) (by simp))
  refine ⟨A a % M, fun hlo hhi => ?_, ?_⟩
  · -- The divisor is `[d]`, whose top word is not zero.
    obtain mv : wordsVal t2.mem g.B (arr g.w aVD) (g.w / 2) = A d := words_low (by omega_using []) nD hhi
    obtain tp := top_pos (m := t2.mem) (B := g.B) (d := arr g.w aVD) (v := g.w / 2) (by omega_using [hw]) (by rw [mv]; exact hlo)
    rw [← hM, v3, mv, ite_eq_right (by omega_using [tp]), Nat.add_zero]
  · refine h2.next w4 F (by decide) (by simp) (k3.trans k4) (by decide) ?_ ?_ ?_ (h2.mask_keep F (by simp))
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · rw [upd_self]; exact hR
      obtain hn := hfree j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
      rw [upd_ne _ _ hn.1, F.num
        (by simp; exact ⟨Ne.symm hn.2.1, Ne.symm hn.1, Ne.symm hn.2.2⟩) (by simp) (h.ws.fit64 (h.live_lt j hj)),
        h2.arrs.get (by simp [hj]), upd_ne _ _ hn.2.1, upd_ne _ _ hn.1]
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · decide
      · exact h.live_lt j hj
    · have fitD := h.ws.fit64 (j := aVD) (by decide)
      rw [f4.word (by omega_using []) (by decide) (by simp) fitD, o3.word (by omega_using [hw]) (by omega_using [hS, fitD]), h2.vdTop]

/-- Arrays the word path's helpers write: none of them is tracked. -/
abbrev Free (live : List Nat) : Prop := ∀ j ∈ live, j ∉ [aVQ, aVR, aVD, aVT, aW]

/-- `mulQ y x ++ eqA aVQ b`: the mask and'ed with `[y] [x] mod 2^(64 w) = [b]`. -/
theorem Stg.mulEq_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {y x b : Nat} (hy : y ∈ live) (hx : x ∈ live) (hb : b ∈ live) (hz : aZ ∈ live)
    (hA0 : A aZ = 0) (hf : Free live) :
    WP isa (seqs (mulQ y x ++ eqA aVQ b)) s
      (Stg g s0 A live (c && decide (A y * A x % 2 ^ (64 * g.w) = A b))) := by
  obtain yQ : y ≠ aVQ := fun e => hf y hy (by simp [e])
  obtain xQ : x ≠ aVQ := fun e => hf x hx (by simp [e])
  obtain bQ : b ≠ aVQ := fun e => hf b hb (by simp [e])
  unfold mulQ
  rw [List.cons_append, kc_seqs_cons (by simp [eqA])]
  refine WP.mono (h.copy_ok (o := aVQ) (a := aZ) (by decide) hz (by decide)) fun t1 h1 => ?_
  rw [List.cons_append, List.nil_append, kc_seqs_cons (by simp [eqA])]
  refine WP.mono (h1.mulLow_ok (o := aVQ) (y := y) (x := x) (by simp) (by simp [hy]) (by simp [hx]) (Ne.symm yQ)
    (Ne.symm xQ) (by decide) (by rw [upd_self, hA0])) fun t2 h2 => ?_
  refine WP.mono (h2.eqA_ok (a := aVQ) (b := b) (by simp) (by simp [hb])) fun t h3 => ?_
  simp only [upd_self, upd_ne _ _ bQ, upd_ne _ _ yQ, upd_ne _ _ xQ] at h3
  refine (h3.sub (live' := live) (fun j hj => by simp [hj])).congr' fun j hj => ?_
  obtain jQ : j ≠ aVQ := fun e => hf j hj (by simp [e])
  rw [upd_ne _ _ jQ, upd_ne _ _ jQ]

/-- `mulQH y x ++ eqA aVQ b`: the mask and'ed with `[y] [x] mod 2^(64 w) = [b]`, for `[y]` and `[x]`
below `2^(64 (w / 2))`. -/
theorem Stg.mulEqH_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {y x b : Nat} (hy : y ∈ live) (hx : x ∈ live) (hb : b ∈ live) (hz : aZ ∈ live)
    (hA0 : A aZ = 0) (hf : Free live) (hw2 : g.w % 2 = 0)
    (hY : A y < 2 ^ (64 * (g.w / 2))) (hX : A x < 2 ^ (64 * (g.w / 2))) :
    WP isa (seqs (mulQH y x ++ eqA aVQ b)) s
      (Stg g s0 A live (c && decide (A y * A x % 2 ^ (64 * g.w) = A b))) := by
  obtain yQ : y ≠ aVQ := fun e => hf y hy (by simp [e])
  obtain xQ : x ≠ aVQ := fun e => hf x hx (by simp [e])
  obtain bQ : b ≠ aVQ := fun e => hf b hb (by simp [e])
  unfold mulQH
  rw [List.cons_append, kc_seqs_cons (by simp [eqA])]
  refine WP.mono (h.copy_ok (o := aVQ) (a := aZ) (by decide) hz (by decide)) fun t1 h1 => ?_
  rw [List.cons_append, List.nil_append, kc_seqs_cons (by simp [eqA])]
  refine WP.mono (h1.mulHalf_ok (o := aVQ) (y := y) (x := x) (by simp) (by simp [hy]) (by simp [hx]) (Ne.symm yQ)
    (Ne.symm xQ) (by decide) (by rw [upd_self, hA0]) hw2 (by rw [upd_ne _ _ yQ]; exact hY)
    (by rw [upd_ne _ _ xQ]; exact hX)) fun t2 h2 => ?_
  refine WP.mono (h2.eqA_ok (a := aVQ) (b := b) (by simp) (by simp [hb])) fun t h3 => ?_
  simp only [upd_self, upd_ne _ _ bQ, upd_ne _ _ yQ, upd_ne _ _ xQ] at h3
  refine (h3.sub (live' := live) (fun j hj => by simp [hj])).congr' fun j hj => ?_
  obtain jQ : j ≠ aVQ := fun e => hf j hj (by simp [e])
  rw [upd_ne _ _ jQ, upd_ne _ _ jQ]

/-- `divWA a d ++ eqA aVR b`: the mask and'ed with `Y = [b]`, `Y` `[a] mod [d]`
for `2^(64 (v - 1)) ≤ [d] < 2^(64 v)`. -/
theorem Stg.divEq_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {a d b : Nat} (ha : a ∈ live) (hd : d ∈ live) (hb : b ∈ live) (hz : aZ ∈ live)
    (hA0 : A aZ = 0) (hf : ∀ j ∈ live, j ∉ [aVR, aVD, aVT]) (hw : 8 ≤ g.w) (hwl : g.w ≤ 128) (hw2 : g.w % 2 = 0) :
    WP isa (seqs (divWA a d ++ eqA aVR b)) s fun t => ∃ Y,
      (2 ^ (64 * (g.w / 2 - 1)) ≤ A d → A d < 2 ^ (64 * (g.w / 2)) → Y = A a % A d) ∧
      Stg g s0 A live (c && decide (Y = A b)) t := by
  obtain bR : b ≠ aVR := fun e => hf b hb (by simp [e])
  rw [kc_seqs_append (by simp [divWA]) (by simp [eqA])]
  refine WP.mono (h.divWA_ok ha hd hz hA0 hf hw hwl hw2) fun t1 ⟨Y, hY, h1⟩ => ?_
  refine WP.mono (h1.eqA_ok (a := aVR) (b := b) (by simp) (by simp [hb])) fun t h2 => ⟨Y, hY, ?_⟩
  rw [upd_self, upd_ne _ _ bR] at h2
  refine (h2.sub (live' := live) (fun j hj => by simp [hj])).congr' fun j hj => ?_
  obtain jR : j ≠ aVR := fun e => hf j hj (by simp [e])
  rw [upd_ne _ _ jR]

/-- `mulModOne y x d`: the mask and'ed with `X = 1`, `X` `([y] [x] mod
2^(64 w)) mod [d]` for `2^(64 (v - 1)) ≤ [d] < 2^(64 v)`. -/
theorem Stg.mulModOne_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {y x d : Nat} (hy : y ∈ live) (hx : x ∈ live) (hd : d ∈ live) (hz : aZ ∈ live)
    (hA0 : A aZ = 0) (ho : aOne ∈ live) (hA1 : A aOne = 1) (hf : Free live) (hw : 8 ≤ g.w) (hwl : g.w ≤ 128) (hw2 : g.w % 2 = 0) :
    WP isa (seqs (mulModOne y x d)) s fun t => ∃ X,
      (2 ^ (64 * (g.w / 2 - 1)) ≤ A d → A d < 2 ^ (64 * (g.w / 2)) → X = A y * A x % 2 ^ (64 * g.w) % A d) ∧
      Stg g s0 A live (c && decide (X = 1)) t := by
  obtain yQ : y ≠ aVQ := fun e => hf y hy (by simp [e])
  obtain xQ : x ≠ aVQ := fun e => hf x hx (by simp [e])
  obtain dQ : d ≠ aVQ := fun e => hf d hd (by simp [e])
  unfold mulModOne mulQ
  simp only [List.cons_append, List.nil_append]
  rw [kc_seqs_cons (by simp [divWA])]
  refine WP.mono (h.copy_ok (o := aVQ) (a := aZ) (by decide) hz (by decide)) fun t1 h1 => ?_
  rw [kc_seqs_cons (by simp [divWA])]
  refine WP.mono (h1.mulLow_ok (o := aVQ) (y := y) (x := x) (by simp) (by simp [hy]) (by simp [hx]) (Ne.symm yQ)
    (Ne.symm xQ) (by decide) (by rw [upd_self, hA0])) fun t2 h2 => ?_
  obtain hf2 : ∀ j ∈ aVQ :: live, j ∉ [aVR, aVD, aVT] := fun j hj => by
    rcases List.mem_cons.mp hj with rfl | hj
    · decide
    · have := hf j hj; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this ⊢
      exact ⟨this.2.1, this.2.2.1, this.2.2.2.1⟩
  refine WP.mono (h2.divEq_ok (a := aVQ) (d := d) (b := aOne) (by simp) (by simp [hd]) (by simp [ho]) (by simp [hz])
    (by rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), hA0]) hf2 hw hwl hw2) fun t ⟨X, hX, h3⟩ => ⟨X, ?_, ?_⟩
  · intro hlo hhi
    simp only [upd_self, upd_ne _ _ dQ, upd_ne _ _ yQ, upd_ne _ _ xQ] at hX
    exact hX hlo hhi
  · simp only [upd_ne _ _ (by decide : aOne ≠ aVQ), hA1] at h3
    refine (h3.sub (live' := live) (fun j hj => by simp [hj])).congr' fun j hj => ?_
    obtain jQ : j ≠ aVQ := fun e => hf j hj (by simp [e])
    rw [upd_ne _ _ jQ, upd_ne _ _ jQ]


/-- The mask of the checks by words: `p` odd, `p q mod 2^(64 w) = n`, `qInv < p`,
`(q qInv mod 2^(64 w)) mod p = 1` (`Xq`), `dP < p - 1`, `(e dP mod 2^(64 w)) mod
(p - 1) = 1` (`X₁`), and the same for `q` (`X₂`). -/
def crtBitsW (n p q dP dQ qI L Xq X₁ X₂ : Nat) : Bool :=
  decide (p % 2 = 1) && decide (L = n) && decide (qI < p) && decide (Xq = 1) &&
    decide (dP < 2 * (p / 2)) && decide (X₁ = 1) && decide (dQ < 2 * (q / 2)) && decide (X₂ = 1)

/-- The checks of `vg_rsa_check_crt_key`, by words. -/
theorem crtChecksW_ok {g : Geo} {s0 s : State} {v : Vals}
    (h : Stg g s0 (aStart v) live0 (decide (v.p % 2 = 1)) s) (hw : 8 ≤ g.w) (hwl : g.w ≤ 128) (hw2 : g.w % 2 = 0)
    (hpB : v.p < 2 ^ (64 * (g.w / 2))) (hqB : v.q < 2 ^ (64 * (g.w / 2))) :
    WP isa (seqs crtChecksW) s fun t => ∃ Xq X₁ X₂ : Nat,
      (InW g.w v.p → Xq = v.q * v.qI % 2 ^ (64 * g.w) % v.p) ∧
      (InW g.w (2 * (v.p / 2)) → X₁ = v.e * v.dP % 2 ^ (64 * g.w) % (2 * (v.p / 2))) ∧
      (InW g.w (2 * (v.q / 2)) → X₂ = v.e * v.dQ % 2 ^ (64 * g.w) % (2 * (v.q / 2))) ∧
      Stg g s0 (aFin v) liveFin
        (crtBitsW v.n v.p v.q v.dP v.dQ v.qI (v.p * v.q % 2 ^ (64 * g.w)) Xq X₁ X₂) t := by
  unfold crtChecksW
  simp only [List.append_assoc]
  obtain f0 : Free live0 := by decide
  rw [← List.append_assoc (mulQH aP aQ), kc_seqs_append (by simp [mulQH]) (by simp [ltA])]
  refine WP.mono (h.mulEqH_ok (y := aP) (x := aQ) (b := aN) (by decide) (by decide) (by decide) (by decide) rfl f0
    hw2 hpB hqB) fun t1 h1 => ?_
  rw [kc_seqs_append (by simp [ltA]) (by simp [mulModOne, mulQ])]
  refine WP.mono (h1.ltA_ok (a := aQI) (b := aP) (by decide) (by decide) (by decide)) fun t2 h2 => ?_
  rw [kc_seqs_append (by simp [mulModOne, mulQ]) (by simp)]
  refine WP.mono (h2.mulModOne_ok (y := aQ) (x := aQI) (d := aP) (by decide) (by decide) (by decide) (by decide) rfl
    (by decide) rfl f0 hw hwl hw2) fun t3 ⟨Xq, hXq, h3⟩ => ?_
  simp only [List.cons_append, List.nil_append]
  rw [kc_seqs_cons (by simp)]
  refine WP.mono (h3.copy_ok (o := aM1) (a := aP) (by decide) (by decide) (by decide)) fun t4 h4 => ?_
  rw [kc_seqs_cons (by simp)]
  refine WP.mono (h4.clrLow_ok (j := aM1) (by decide) (by decide)) fun t5 h5 => ?_
  rw [kc_seqs_cons (by simp)]
  refine WP.mono (h5.copy_ok (o := aM2) (a := aQ) (by decide) (by decide) (by decide)) fun t6 h6 => ?_
  rw [kc_seqs_cons (by simp [ltA])]
  refine WP.mono (h6.clrLow_ok (j := aM2) (by decide) (by decide)) fun t7 h7 => ?_
  obtain f7 : Free (aM2 :: aM1 :: live0) := by decide
  -- `dP`.
  rw [kc_seqs_append (by simp [ltA]) (by simp [mulModOne, mulQ])]
  refine WP.mono (h7.ltA_ok (a := aDP) (b := aM1) (by decide) (by decide) (by decide)) fun t8 h8 => ?_
  rw [kc_seqs_append (by simp [mulModOne, mulQ]) (by simp [ltA])]
  refine WP.mono (h8.mulModOne_ok (y := aE) (x := aDP) (d := aM1) (by decide) (by decide) (by decide) (by decide) rfl
    (by decide) rfl f7 hw hwl hw2) fun t9 ⟨X₁, hX₁, h9⟩ => ?_
  -- `dQ`.
  rw [kc_seqs_append (by simp [ltA]) (by simp [mulModOne, mulQ])]
  refine WP.mono (h9.ltA_ok (a := aDQ) (b := aM2) (by decide) (by decide) (by decide)) fun t10 h10 => ?_
  refine WP.mono (h10.mulModOne_ok (y := aE) (x := aDQ) (d := aM2) (by decide) (by decide) (by decide) (by decide)
    rfl (by decide) rfl f7 hw hwl hw2) fun t h11 => ?_
  obtain ⟨X₂, hX₂, h11⟩ := h11
  refine ⟨Xq, X₁, X₂, fun hi => hXq hi.1 hi.2, fun hi => hX₁ hi.1 hi.2, fun hi => hX₂ hi.1 hi.2,
    (h11.sub (live' := liveFin) (by decide)).congr' fun j hj => ?_⟩
  simp only [liveFin, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The checks of `d`, by words. -/
theorem dChecksW_ok {g : Geo} {s0 s : State} {v : Vals} {c : Bool} (h : Stg g s0 (aFin v) liveFin c s)
    (hw : 8 ≤ g.w) (hwl : g.w ≤ 128) (hw2 : g.w % 2 = 0) :
    WP isa (seqs dChecksW) s fun t => ∃ Y₁ Y₂,
      (InW g.w (2 * (v.p / 2)) → Y₁ = v.d % (2 * (v.p / 2))) ∧ (InW g.w (2 * (v.q / 2)) → Y₂ = v.d % (2 * (v.q / 2))) ∧
      ∃ A live, Stg g s0 A live (c && decide (v.d < v.n) && decide (Y₁ = v.dP) && decide (Y₂ = v.dQ)) t := by
  unfold dChecksW
  simp only [List.append_assoc]
  obtain ff : ∀ j ∈ liveFin, j ∉ [aVR, aVD, aVT] := by decide
  rw [kc_seqs_append (by simp [ltA]) (by simp [divWA])]
  refine WP.mono (h.ltA_ok (a := aD) (b := aN) (by decide) (by decide) (by decide)) fun t1 h1 => ?_
  rw [← List.append_assoc, kc_seqs_append (by simp [divWA]) (by simp [divWA])]
  refine WP.mono (h1.divEq_ok (a := aD) (d := aM1) (b := aDP) (by decide) (by decide) (by decide) (by decide) rfl ff
    hw hwl hw2) fun t2 ⟨Y₁, hY₁, h2⟩ => ?_
  refine WP.mono (h2.divEq_ok (a := aD) (d := aM2) (b := aDQ) (by decide) (by decide) (by decide) (by decide) rfl ff
    hw hwl hw2) fun t ⟨Y₂, hY₂, h3⟩ => ⟨Y₁, Y₂, fun hi => hY₁ hi.1 hi.2, fun hi => hY₂ hi.1 hi.2, _, _, h3⟩


theorem kc_exec_li32 {s : State} {d : Reg} : exec (.li d 32) s = some (s.write d 32#64) := by
  rw [exec_li (by decide)]; rfl

/-- `shape`: `t0 = 0` exactly for `p_len` (`s5`) a multiple of 8 and at least
32, equal to `q_len` (`s6`) and to `4 w` (`s9`). -/
theorem shape_ok {s : State} {pl ql w : Nat} (h5 : s.gpr .s5 = BitVec.ofNat 64 pl)
    (h6 : s.gpr .s6 = BitVec.ofNat 64 ql) (h9 : s.gpr .s9 = BitVec.ofNat 64 w) (hpl : pl < 2 ^ 32)
    (hql : ql < 2 ^ 32) (hw : w ≤ 1024) :
    WP isa (.block shape) s fun t =>
      ((t.gpr .t0 = 0 ↔ (pl % 8 = 0 ∧ 4 * w = pl ∧ pl = ql ∧ 32 ≤ pl)) ∧ t.mem = s.mem) ∧ Keep [.t0, .t1] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  obtain hP : ∀ x : Nat, x < 2 ^ 32 → (BitVec.ofNat 64 x).toNat = x := fun x hx => by
    rw [BitVec.toNat_ofNat]; omega_using [hx]
  unfold shape
  brun [h5, h6, h9, kc_exec_li32]
  simp only [bv_or0, bv_xor0, bv_lt_ite0]
  obtain l2 : BitVec.ofNat 64 w <<< 2 = BitVec.ofNat 64 (4 * w) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hP w (by omega_using [hw]), BitVec.toNat_ofNat]; omega_using []
  simp only [l2, bv_and7, hP pl hpl, BitVec.lt_def, show (32#64).toNat = 32 from rfl, Nat.not_lt]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    refine ⟨h1, ?_, ?_, h4⟩
    · have := congrArg BitVec.toNat h2; rw [hP _ (by omega_using [hw]), hP pl hpl] at this; exact this
    · have := congrArg BitVec.toNat h3; rw [hP pl hpl, hP ql hql] at this; exact this
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨⟨h1, by rw [h2]⟩, by rw [h3]⟩, h4⟩


end VG.Proof.Rsa.RISCV64.KeyCheck
