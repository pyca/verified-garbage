module
public import VerifiedGarbage.Impl.Rsa.Arm.MulMod
public import VerifiedGarbage.Proof.Rsa.Arm.KeyOps

import VerifiedGarbage.Proof.Rsa.MulModArithmetic
import VerifiedGarbage.Proof.Rsa.Arm.AddMod
import VerifiedGarbage.Proof.Rsa.Arm.InvParts
import VerifiedGarbage.Proof.Rsa.Arm.KeyBits
import VerifiedGarbage.Proof.Framework.Block
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Rsa.KeyMath

/-! # `mulMod` on ARMv7: `[a] = ([a] + ([y] mod 2^k) [x]) mod [m]`

`mulMod_ok`: `k = r6` steps of `mulModStep`, each adding the selected `[x]`
to `[a]` and doubling `[x]` modulo `[m]`, and halving `[y]`. From `[a], [x] <
[m]` with `2 [m] ≤ 2^(32 w)` and `[z] = 0`, `[a]` ends as
`([a] + ([y] mod 2^k) [x]) mod [m]`.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Keys
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm

/-- The arrays of `mulMod z y x a m t`: each below `N`, `t` above the
others, which are distinct. -/
abbrev MulIdx (N z y x a m t : Nat) : Prop :=
  t + 3 < N ∧ z < t ∧ y < t ∧ x < t ∧ a < t ∧ m < t ∧ z ≠ y ∧ z ≠ x ∧ z ≠ a ∧ z ≠ m ∧ y ≠ x ∧ y ≠ a ∧
    y ≠ m ∧ x ≠ a ∧ x ≠ m ∧ a ≠ m

/-- The arrays `mulMod` writes. -/
abbrev mulArrs (y x a t : Nat) : List Nat := [y, x, a, t, t + 1, t + 2, t + 3]

/-- One step's arithmetic. -/
theorem mulMod_arith {A0 X0 Y0 M i : Nat} :
    ((A0 + Y0 % 2 ^ i * X0) % M + (Y0 / 2 ^ i) % 2 * (2 ^ i * X0 % M)) % M =
      (A0 + Y0 % 2 ^ (i + 1) * X0) % M :=
  VG.Proof.Rsa.mulMod_arith

theorem double_arith {X0 M i : Nat} : (2 ^ i * X0 % M + 2 ^ i * X0 % M) % M = 2 ^ (i + 1) * X0 % M :=
  VG.Proof.Rsa.double_arith

theorem nm0 {j : Nat} : ∀ k ∈ ([] : List Nat), k ≠ j := fun _ h => absurd h List.not_mem_nil

theorem nm1 {a j : Nat} (h : j ≠ a) : ∀ k ∈ [a], k ≠ j := by
  intro k hk; rw [List.mem_singleton] at hk; subst hk; exact h.symm

theorem nm4 {a b c d j : Nat} (ha : j ≠ a) (hb : j ≠ b) (hc : j ≠ c) (hd : j ≠ d) :
    ∀ k ∈ [a, b, c, d], k ≠ j := by
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl <;> exact Ne.symm (by assumption)

/-- `mulHead`: `[t]` is `[x]` if `[y]` is odd, `[z]` if not. -/
theorem mulHead_ok {s : State} {B : BitVec 32} {Z w N z y x t : Nat} (h : Ws s B Z w N)
    (hN : N ≤ 256) (ht : t < N) (hz : z < N) (hy : y < N) (hx : x < N) (htz : t ≠ z) (htx : t ≠ x) :
    WP isa (mulHead z y x t) s fun u => Ws u B Z w N ∧ Keep B w [t] [sB] s.mem u.mem ∧ Rest opRegs s u ∧
      num u.mem B w t = (if num s.mem B w y % 2 = 0 then num s.mem B w z else num s.mem B w x) := by
  have hsB : sB + 4 ≤ hdr := by decide
  rw [mulHead, WP.seq_iff, ← List.append_nil (bitOf sB y)]
  refine bitOf_ok h hy hN hsB fun t1 h1 k1 e1 r1 => WP.block_nil ?_
  refine WP.mono (sel_ok h1 (o := t) (a := z) (b := x) (sl := sB) ht hz hx hN htz htx hsB
    (by rw [e1]; omega_arith)) fun u ⟨hu, k2, e2, r2⟩ => ⟨hu, k1.mono.trans k2.mono, r1.trans r2, ?_⟩
  rw [e2, e1, k1.num nm0 (by decide) (h.fit64 hz), k1.num nm0 (by decide) (h.fit64 hx)]

/-- `mulTail`: `[y]` halved, `r6` decremented. -/
theorem mulTail_ok {s : State} {B : BitVec 32} {Z w N y : Nat} (h : Ws s B Z w N) (hN : N ≤ 256) (hy : y < N) :
    WP isa (mulTail y) s fun u => Ws u B Z w N ∧ Keep B w [y] [] s.mem u.mem ∧ Rest (.r6 :: opRegs) s u ∧
      u.gpr .r6 = s.gpr .r6 - 1 ∧ u.z = (s.gpr .r6 - 1 == 0) ∧ num u.mem B w y = num s.mem B w y / 2 := by
  rw [mulTail, wp_seqs_cons (List.cons_ne_nil _ _)]
  refine wp_mov (op2_imm (by decide)) fun t5 u5 => WP.block_nil ?_
  have h5 := h.of_upd u5 (by decide) (by decide) (by decide)
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (half_ok h5 (j := y) hy hN (by rw [u5.gpr]; decide)) fun t6 ⟨h6, k6, e6, r6⟩ => ?_
  refine wp_subs (op2_imm (by decide)) fun u u7 hz7 => WP.block_nil ?_
  have r6eq : t6.gpr .r6 = s.gpr .r6 := by rw [r6.gpr _ (by decide), u5.other _ (by decide)]
  rw [u5.gpr, u5.mem] at e6
  rw [u5.mem] at k6
  refine ⟨h6.of_upd u7 (by decide) (by decide) (by decide), by rw [u7.mem]; exact k6,
    (u5.rest (by simp)).trans ((r6.mono (by simp)).trans (u7.rest (by simp))), by rw [u7.gpr, r6eq],
    by rw [hz7, r6eq], ?_⟩
  rw [u7.mem, e6, show (0 : BitVec 32).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]

/-- One step. -/
theorem mulModStep_ok {s : State} {B : BitVec 32} {Z w N z y x a m t : Nat} (h : Ws s B Z w N)
    (hN : N ≤ 256) (hi : MulIdx N z y x a m t) :
    WP isa (mulModStep z y x a m t) s fun u => Ws u B Z w N ∧
      Keep B w (mulArrs y x a t) [sB, sC] s.mem u.mem ∧ Rest (.r6 :: opRegs) s u ∧
      u.gpr .r6 = s.gpr .r6 - 1 ∧ u.z = (s.gpr .r6 - 1 == 0) ∧
      num u.mem B w y = num s.mem B w y / 2 ∧
      (num s.mem B w z = 0 → num s.mem B w a < num s.mem B w m → num s.mem B w x < num s.mem B w m →
        2 * num s.mem B w m ≤ 2 ^ (32 * w) →
        num u.mem B w a = (num s.mem B w a + num s.mem B w y % 2 * num s.mem B w x) % num s.mem B w m ∧
        num u.mem B w x = (num s.mem B w x + num s.mem B w x) % num s.mem B w m) := by
  obtain ⟨ht, hz, hy, hx, ha, hm, hzy, hzx, hza, hzm, hyx, hya, hym, hxa, hxm, ham⟩ := hi
  -- The indices' facts, while the context is small.
  have zN : z < N := by omega_arith
  have yN : y < N := by omega_arith
  have xN : x < N := by omega_arith
  have aN : a < N := by omega_arith
  have mN : m < N := by omega_arith
  have tN : t < N := by omega_arith
  have t1N : t + 1 + 2 < N := by omega_arith
  have tz : t ≠ z := by omega_arith
  have tx : t ≠ x := by omega_arith
  have t1z : t + 1 ≠ z := by omega_arith
  have t1t : t + 1 ≠ t := by omega_arith
  have at0 : a ≠ t := by omega_arith
  have at1 : a ≠ t + 1 := by omega_arith
  have at2 : a ≠ t + 1 + 1 := by omega_arith
  have at3 : a ≠ t + 1 + 2 := by omega_arith
  have xt1 : x ≠ t + 1 := by omega_arith
  have xt2 : x ≠ t + 1 + 1 := by omega_arith
  have xt3 : x ≠ t + 1 + 2 := by omega_arith
  have mt1 : m ≠ t + 1 := by omega_arith
  have mt2 : m ≠ t + 1 + 1 := by omega_arith
  have mt3 : m ≠ t + 1 + 2 := by omega_arith
  have t1x : t + 1 ≠ x := by omega_arith
  have yt0 : y ≠ t := by omega_arith
  have yt1 : y ≠ t + 1 := by omega_arith
  have yt2 : y ≠ t + 1 + 1 := by omega_arith
  have yt3 : y ≠ t + 1 + 2 := by omega_arith
  have zt1 : z ≠ t + 1 := by omega_arith
  have zt2 : z ≠ t + 1 + 1 := by omega_arith
  have zt3 : z ≠ t + 1 + 2 := by omega_arith
  have mt0 : m ≠ t := by omega_arith
  have xt0 : x ≠ t := by omega_arith
  have zt0 : z ≠ t := by omega_arith
  have fz := h.fit64 zN
  have fy := h.fit64 yN
  have fx := h.fit64 xN
  have fa := h.fit64 aN
  have fm := h.fit64 mN
  rw [mulModStep, wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (mulHead_ok h hN tN zN yN xN tz tx) fun t2 ⟨h2, k2, r2, e2⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (addMod_ok h2 (o := a) (a := a) (b := t) (m := m) (z := z) (t := t + 1) hN aN aN tN mN zN t1N
    t1z t1t at1 at2 mt1 mt2 mt3 at2 at3) fun t3 ⟨h3, k3, r3, e3⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (addMod_ok h3 (o := x) (a := x) (b := x) (m := m) (z := z) (t := t + 1) hN xN xN xN mN zN t1N
    t1z t1x xt1 xt2 mt1 mt2 mt3 xt2 xt3) fun t4 ⟨h4, k4, r4, e4⟩ => ?_
  refine WP.mono (mulTail_ok h4 hN yN) fun u ⟨hu, k6, r6, c6, z6, e6⟩ => ?_
  have r6eq : t4.gpr .r6 = s.gpr .r6 := by
    rw [r4.gpr _ (by decide), r3.gpr _ (by decide), r2.gpr _ (by decide)]
  refine ⟨hu, ((k2.mono.trans k3.mono).trans k4.mono).trans k6.mono,
    (r2.mono (by simp)).trans ((r3.mono (by simp)).trans ((r4.mono (by simp)).trans r6)),
    by rw [c6, r6eq], by rw [z6, r6eq], ?_, fun hZ hA hX hM => ?_⟩
  · rw [e6, k4.num (nm4 yt1 yt2 yt3 hyx) (by decide) fy, k3.num (nm4 yt1 yt2 yt3 hya) (by decide) fy,
      k2.num (nm1 yt0) (by decide) fy]
  · -- The values each step reads.
    have z2 : num t2.mem B w z = 0 := by rw [k2.num (nm1 zt0) (by decide) fz, hZ]
    have mm2 : num t2.mem B w m = num s.mem B w m := k2.num (nm1 mt0) (by decide) fm
    have a2 : num t2.mem B w a = num s.mem B w a := k2.num (nm1 at0) (by decide) fa
    have x2 : num t2.mem B w x = num s.mem B w x := k2.num (nm1 xt0) (by decide) fx
    have d2 : num t2.mem B w t = num s.mem B w y % 2 * num s.mem B w x := by
      rw [e2, hZ]
      rcases Nat.mod_two_eq_zero_or_one (num s.mem B w y) with e | e <;> simp [e]
    have dlt : num t2.mem B w t < num s.mem B w m := by
      rw [d2]; rcases Nat.mod_two_eq_zero_or_one (num s.mem B w y) with e | e <;> simp [e] <;> omega_arith
    have A3 := e3 z2 (by rw [a2, mm2]; exact hA) (by rw [mm2]; exact dlt) (by rw [mm2]; exact hM)
    rw [a2, mm2, d2] at A3
    have z3 : num t3.mem B w z = 0 := by rw [k3.num (nm4 zt1 zt2 zt3 hza) (by decide) fz, z2]
    have mm3 : num t3.mem B w m = num s.mem B w m := by rw [k3.num (nm4 mt1 mt2 mt3 ham.symm) (by decide) fm, mm2]
    have x3 : num t3.mem B w x = num s.mem B w x := by rw [k3.num (nm4 xt1 xt2 xt3 hxa) (by decide) fx, x2]
    have X4 := e4 z3 (by rw [x3, mm3]; exact hX) (by rw [x3, mm3]; exact hX) (by rw [mm3]; exact hM)
    rw [x3, mm3] at X4
    refine ⟨?_, ?_⟩
    · rw [k6.num (nm1 hya.symm) (by decide) fa, k4.num (nm4 at1 at2 at3 hxa.symm) (by decide) fa, A3]
    · rw [k6.num (nm1 hyx.symm) (by decide) fx, X4]

end VG.Proof.Rsa.Arm.Keys

namespace VG.Proof.Rsa.Arm.Keys
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm

/-- The state after `i` of the `k` steps. -/
structure MulI (s0 : State) (B : BitVec 32) (Z w N z y x a m t k i : Nat) (u : State) : Prop where
  ws : Ws u B Z w N
  keep : Keep B w (mulArrs y x a t) [sB, sC] s0.mem u.mem
  rest : Rest (.r6 :: opRegs) s0 u
  count : u.gpr .r6 = BitVec.ofNat 32 (k - i)
  yv : num u.mem B w y = num s0.mem B w y / 2 ^ i
  value : num s0.mem B w z = 0 → num s0.mem B w a < num s0.mem B w m → num s0.mem B w x < num s0.mem B w m →
    2 * num s0.mem B w m ≤ 2 ^ (32 * w) →
    num u.mem B w a = (num s0.mem B w a + num s0.mem B w y % 2 ^ i * num s0.mem B w x) % num s0.mem B w m ∧
    num u.mem B w x = 2 ^ i * num s0.mem B w x % num s0.mem B w m

theorem mulModBody_ok {s0 u : State} {B : BitVec 32} {Z w N z y x a m t k i : Nat} (hN : N ≤ 256)
    (hi : MulIdx N z y x a m t) (hk : k < 2 ^ 32) (inv : MulI s0 B Z w N z y x a m t k i u) (hik : i < k) :
    WP isa (mulModStep z y x a m t) u fun u' =>
      MulI s0 B Z w N z y x a m t k (i + 1) u' ∧ u'.z = decide (i + 1 = k) := by
  have h := inv.ws
  have hi' := hi
  obtain ⟨ht, hz, hy, hx, ha, hm, hzy, hzx, hza, hzm, hyx, hya, hym, hxa, hxm, ham⟩ := hi'
  have fz := h.fit64 (j := z) (by omega_arith)
  have fm := h.fit64 (j := m) (by omega_arith)
  have zk : num u.mem B w z = num s0.mem B w z := inv.keep.num (by simp; omega_arith) (by decide) fz
  have mk : num u.mem B w m = num s0.mem B w m := inv.keep.num (by simp; omega_arith) (by decide) fm
  refine WP.mono (mulModStep_ok h hN hi) fun u' ⟨h', k', r', c', z', y', v'⟩ => ?_
  have cnt : u.gpr .r6 - 1 = BitVec.ofNat 32 (k - (i + 1)) := by
    rw [inv.count]
    change BitVec.ofNat 32 (k - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_arith)]
    congr 1
  refine ⟨⟨h', inv.keep.trans k', inv.rest.trans r', by rw [c', cnt], ?_, fun hZ hA hX hM => ?_⟩, ?_⟩
  · rw [y', inv.yv, Nat.div_div_eq_div_mul, Nat.pow_succ]
  · obtain ⟨va, vx⟩ := inv.value hZ hA hX hM
    have M0 : 0 < num s0.mem B w m := by omega_arith
    have aLt : num u.mem B w a < num u.mem B w m := by rw [va, mk]; exact Nat.mod_lt _ M0
    have xLt : num u.mem B w x < num u.mem B w m := by rw [vx, mk]; exact Nat.mod_lt _ M0
    obtain ⟨va', vx'⟩ := v' (by rw [zk, hZ]) aLt xLt (by rw [mk]; exact hM)
    rw [va', vx', va, vx, inv.yv, mk]
    exact ⟨mulMod_arith, double_arith⟩
  · rw [z', cnt, ofNat_beq_zero (by omega_arith)]
    simp only [show k - (i + 1) = 0 ↔ i + 1 = k by omega_arith]

/-- `mulMod z y x a m t` with `r6 = k > 0`. -/
theorem mulMod_ok {s : State} {B : BitVec 32} {Z w N z y x a m t k : Nat} (h : Ws s B Z w N)
    (hN : N ≤ 256) (hi : MulIdx N z y x a m t) (hk : 0 < k) (hk' : k < 2 ^ 32)
    (c : s.gpr .r6 = BitVec.ofNat 32 k) :
    WP isa (mulMod z y x a m t) s fun u => Ws u B Z w N ∧
      Keep B w (mulArrs y x a t) [sB, sC] s.mem u.mem ∧ Rest (.r6 :: opRegs) s u ∧
      (num s.mem B w z = 0 → num s.mem B w a < num s.mem B w m → num s.mem B w x < num s.mem B w m →
        2 * num s.mem B w m ≤ 2 ^ (32 * w) →
        num u.mem B w a = (num s.mem B w a + num s.mem B w y % 2 ^ k * num s.mem B w x) % num s.mem B w m) := by
  have start : MulI s B Z w N z y x a m t k 0 s :=
    ⟨h, Keep.refl _ _ _ _ _, Rest.refl _ _, by rw [c, Nat.sub_zero], by rw [Nat.pow_zero, Nat.div_one],
      fun _ hA hX _ => ⟨by rw [Nat.pow_zero, Nat.mod_one, Nat.zero_mul, Nat.add_zero, Nat.mod_eq_of_lt hA],
        by rw [Nat.pow_zero, Nat.one_mul, Nat.mod_eq_of_lt hX]⟩⟩
  refine WP.loop (M := isa) (fun j u => ∃ i, i + j = k ∧ 0 < j ∧ MulI s B Z w N z y x a m t k i u) ?_ k s
    ⟨0, by omega_arith, hk, start⟩
  intro j u ⟨i, hij, hj, inv⟩
  refine WP.mono (mulModBody_ok hN hi hk' inv (by omega_arith)) fun u' ⟨iu, hz⟩ => ?_
  by_cases e : i + 1 = k
  · left
    refine ⟨by change some (!u'.z) = some false; simp [hz, e], iu.ws, iu.keep, iu.rest, fun hZ hA hX hM => ?_⟩
    have v := (iu.value hZ hA hX hM).1
    rw [e] at v
    exact v
  · right
    exact ⟨by change some (!u'.z) = some true; simp [hz, e], j - 1, by omega_arith, i + 1, by omega_arith, by omega_arith, iu⟩

end VG.Proof.Rsa.Arm.Keys
