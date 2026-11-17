module

public import VerifiedGarbage.Proof.Rsa.Arm.KcBase
import VerifiedGarbage.Proof.Rsa.Arm.InvParts
import VerifiedGarbage.Proof.Rsa.Arm.KeyWord
import VerifiedGarbage.Proof.Rsa.Arm.KeyBits
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Impl.Rsa.Arm.MulMod
public import VerifiedGarbage.Proof.Rsa.Arm.KeyOps
import VerifiedGarbage.Proof.Rsa.MulModArithmetic
import VerifiedGarbage.Proof.Rsa.Arm.AddMod
import VerifiedGarbage.Proof.Framework.Block
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Rsa.KeyMath

/-! ### `Rsa.Arm.MulMod`, which this module and modules that import it used -/

section

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
  obtain hsB : sB + 4 ≤ hdr := by decide
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
  obtain h5 := h.of_upd u5 (by decide) (by decide) (by decide)
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (half_ok h5 (j := y) hy hN (by rw [u5.gpr]; decide)) fun t6 ⟨h6, k6, e6, r6⟩ => ?_
  refine wp_subs (op2_imm (by decide)) fun u u7 hz7 => WP.block_nil ?_
  obtain r6eq : t6.gpr .r6 = s.gpr .r6 := by rw [r6.gpr _ (by decide), u5.other _ (by decide)]
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
  obtain zN : z < N := by omega_arith
  obtain yN : y < N := by omega_arith
  obtain xN : x < N := by omega_arith
  obtain aN : a < N := by omega_arith
  obtain mN : m < N := by omega_arith
  obtain tN : t < N := by omega_arith
  obtain t1N : t + 1 + 2 < N := by omega_arith
  obtain tz : t ≠ z := by omega_arith
  obtain tx : t ≠ x := by omega_arith
  obtain t1z : t + 1 ≠ z := by omega_arith
  obtain t1t : t + 1 ≠ t := by omega_arith
  obtain at0 : a ≠ t := by omega_arith
  obtain at1 : a ≠ t + 1 := by omega_arith
  obtain at2 : a ≠ t + 1 + 1 := by omega_arith
  obtain at3 : a ≠ t + 1 + 2 := by omega_arith
  obtain xt1 : x ≠ t + 1 := by omega_arith
  obtain xt2 : x ≠ t + 1 + 1 := by omega_arith
  obtain xt3 : x ≠ t + 1 + 2 := by omega_arith
  obtain mt1 : m ≠ t + 1 := by omega_arith
  obtain mt2 : m ≠ t + 1 + 1 := by omega_arith
  obtain mt3 : m ≠ t + 1 + 2 := by omega_arith
  obtain t1x : t + 1 ≠ x := by omega_arith
  obtain yt0 : y ≠ t := by omega_arith
  obtain yt1 : y ≠ t + 1 := by omega_arith
  obtain yt2 : y ≠ t + 1 + 1 := by omega_arith
  obtain yt3 : y ≠ t + 1 + 2 := by omega_arith
  obtain zt1 : z ≠ t + 1 := by omega_arith
  obtain zt2 : z ≠ t + 1 + 1 := by omega_arith
  obtain zt3 : z ≠ t + 1 + 2 := by omega_arith
  obtain mt0 : m ≠ t := by omega_arith
  obtain xt0 : x ≠ t := by omega_arith
  obtain zt0 : z ≠ t := by omega_arith
  obtain fz := h.fit64 zN
  obtain fy := h.fit64 yN
  obtain fx := h.fit64 xN
  obtain fa := h.fit64 aN
  obtain fm := h.fit64 mN
  rw [mulModStep, wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (mulHead_ok h hN tN zN yN xN tz tx) fun t2 ⟨h2, k2, r2, e2⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (addMod_ok h2 (o := a) (a := a) (b := t) (m := m) (z := z) (t := t + 1) hN aN aN tN mN zN t1N
    t1z t1t at1 at2 mt1 mt2 mt3 at2 at3) fun t3 ⟨h3, k3, r3, e3⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (addMod_ok h3 (o := x) (a := x) (b := x) (m := m) (z := z) (t := t + 1) hN xN xN xN mN zN t1N
    t1z t1x xt1 xt2 mt1 mt2 mt3 xt2 xt3) fun t4 ⟨h4, k4, r4, e4⟩ => ?_
  refine WP.mono (mulTail_ok h4 hN yN) fun u ⟨hu, k6, r6, c6, z6, e6⟩ => ?_
  obtain r6eq : t4.gpr .r6 = s.gpr .r6 := by
    rw [r4.gpr _ (by decide), r3.gpr _ (by decide), r2.gpr _ (by decide)]
  refine ⟨hu, ((k2.mono.trans k3.mono).trans k4.mono).trans k6.mono,
    (r2.mono (by simp)).trans ((r3.mono (by simp)).trans ((r4.mono (by simp)).trans r6)),
    by rw [c6, r6eq], by rw [z6, r6eq], ?_, fun hZ hA hX hM => ?_⟩
  · rw [e6, k4.num (nm4 yt1 yt2 yt3 hyx) (by decide) fy, k3.num (nm4 yt1 yt2 yt3 hya) (by decide) fy,
      k2.num (nm1 yt0) (by decide) fy]
  · -- The values each step reads.
    obtain z2 : num t2.mem B w z = 0 := by rw [k2.num (nm1 zt0) (by decide) fz, hZ]
    obtain mm2 : num t2.mem B w m = num s.mem B w m := k2.num (nm1 mt0) (by decide) fm
    obtain a2 : num t2.mem B w a = num s.mem B w a := k2.num (nm1 at0) (by decide) fa
    obtain x2 : num t2.mem B w x = num s.mem B w x := k2.num (nm1 xt0) (by decide) fx
    obtain d2 : num t2.mem B w t = num s.mem B w y % 2 * num s.mem B w x := by
      rw [e2, hZ]
      rcases Nat.mod_two_eq_zero_or_one (num s.mem B w y) with e | e <;> simp [e]
    obtain dlt : num t2.mem B w t < num s.mem B w m := by
      rw [d2]; rcases Nat.mod_two_eq_zero_or_one (num s.mem B w y) with e | e <;> simp [e] <;> omega_arith
    obtain A3 := e3 z2 (by rw [a2, mm2]; exact hA) (by rw [mm2]; exact dlt) (by rw [mm2]; exact hM)
    rw [a2, mm2, d2] at A3
    obtain z3 : num t3.mem B w z = 0 := by rw [k3.num (nm4 zt1 zt2 zt3 hza) (by decide) fz, z2]
    obtain mm3 : num t3.mem B w m = num s.mem B w m := by rw [k3.num (nm4 mt1 mt2 mt3 ham.symm) (by decide) fm, mm2]
    obtain x3 : num t3.mem B w x = num s.mem B w x := by rw [k3.num (nm4 xt1 xt2 xt3 hxa) (by decide) fx, x2]
    obtain X4 := e4 z3 (by rw [x3, mm3]; exact hX) (by rw [x3, mm3]; exact hX) (by rw [mm3]; exact hM)
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
  obtain fz := h.fit64 (j := z) (by omega_arith)
  obtain fm := h.fit64 (j := m) (by omega_arith)
  obtain zk : num u.mem B w z = num s0.mem B w z := inv.keep.num (by simp; omega_arith) (by decide) fz
  obtain mk : num u.mem B w m = num s0.mem B w m := inv.keep.num (by simp; omega_arith) (by decide) fm
  refine WP.mono (mulModStep_ok h hN hi) fun u' ⟨h', k', r', c', z', y', v'⟩ => ?_
  obtain cnt : u.gpr .r6 - 1 = BitVec.ofNat 32 (k - (i + 1)) := by
    rw [inv.count]
    change BitVec.ofNat 32 (k - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_arith)]
    congr 1
  refine ⟨⟨h', inv.keep.trans k', inv.rest.trans r', by rw [c', cnt], ?_, fun hZ hA hX hM => ?_⟩, ?_⟩
  · rw [y', inv.yv, Nat.div_div_eq_div_mul, Nat.pow_succ]
  · obtain ⟨va, vx⟩ := inv.value hZ hA hX hM
    obtain M0 : 0 < num s0.mem B w m := by omega_arith
    obtain aLt : num u.mem B w a < num u.mem B w m := by rw [va, mk]; exact Nat.mod_lt _ M0
    obtain xLt : num u.mem B w x < num u.mem B w m := by rw [vx, mk]; exact Nat.mod_lt _ M0
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
  obtain start : MulI s B Z w N z y x a m t k 0 s :=
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
    obtain v := (iu.value hZ hA hX hM).1
    rw [e] at v
    exact v
  · right
    exact ⟨by change some (!u'.z) = some true; simp [hz, e], j - 1, by omega_arith, i + 1, by omega_arith, by omega_arith, iu⟩

end VG.Proof.Rsa.Arm.Keys

end

end

/-! # The checks of an RSA key on ARMv7: the steps on `Stg`

`copy`, `clrLow`, the comparisons `ltA` and `eqA` (and'ed into the mask)
and `mulA`, each from `Stg` to `Stg`.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.KeyCheck
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.KeyCheck
open VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm

theorem opRegs_body : ∀ x ∈ opRegs, x ∈ bodyRegs := by decide
theorem r6opRegs_body : ∀ x ∈ (.r6 :: opRegs), x ∈ bodyRegs := by decide

theorem Stg.sub {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {live' : List Nat} (hs : ∀ j ∈ live', j ∈ live) : Stg g s0 A live' c s :=
  { h with arrs := h.arrs.sub hs, live_lt := fun j hj => h.live_lt j (hs j hj) }

theorem Stg.congr {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {A' : Nat → Nat} (e : live.map A = live.map A') : Stg g s0 A' live c s :=
  { h with arrs := h.arrs.congr e }

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
  have na := h.live_lt a ha
  have nb := h.live_lt b hb
  have hWa : aW ≠ a := fun e => hW (e ▸ ha)
  have hWb : aW ≠ b := fun e => hW (e ▸ hb)
  rw [ltA, wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h.ws (o := aW) (a := a) (b := b) (by decide) na nb (by decide) hWa hWb)
    fun t1 ⟨h1, k1, v1, b1, r1⟩ => ?_
  have g1 : Stg g s0 A live c t1 :=
    h.next h1 k1 (by decide) (by simp) r1 opRegs_body
      (h.arrs_keep k1 (fun j hj e => hW (by simp at e; exact e ▸ hj)) (by simp)) h.live_lt
      (h.vd_keep k1 (by decide) (by simp)) (h.mask_keep k1 (by simp))
  refine wp_strSlot h1 (d := sF) (by decide) fun t2 m2 => ?_
  have k2 : Keep g.B g.w [] [sF] t1.mem t2.mem := by
    rw [m2.mem]; exact keep_write _ _ (by simp) (by decide)
  have g2 : Stg g s0 A live c t2 :=
    g1.next (h1.of_mupd m2) k2 (by simp) (by decide) (m2.rest []) (by simp) (g1.arrs_keep k2 (by simp) (by decide))
      g1.live_lt (g1.vd_keep k2 (by simp) (by decide)) (g1.mask_keep k2 (by decide))
  refine g2.acc_ok ?_
  rw [m2.mem, slot_write_self]
  have hb' := borrow_iff (P := 2 ^ (32 * g.w)) v1 (val32_lt _ _ _ _) b1
  rw [h.arrs.get ha, h.arrs.get hb] at hb'
  by_cases hlt : A a < A b
  · have : (t1.gpr .r11).toNat = 1 := by have := (not_congr hb').mpr (by omega_using [hlt]); omega_using [b1, this]
    simp [hlt, this]
  · have : (t1.gpr .r11).toNat = 0 := hb'.mpr (by omega_using [hlt])
    simp [hlt, this]

/-- `eqA a b`: the mask and'ed with `[a] = [b]`. -/
theorem Stg.eqA_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {a b : Nat} (ha : a ∈ live) (hb : b ∈ live) (hW : aW ∉ live) :
    WP isa (seqs (eqA a b)) s (Stg g s0 A live (c && decide (A a = A b))) := by
  have na := h.live_lt a ha
  have nb := h.live_lt b hb
  have hWa : aW ≠ a := fun e => hW (e ▸ ha)
  have hWb : aW ≠ b := fun e => hW (e ▸ hb)
  rw [eqA, wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (eqS_ok h.ws (d := sF) (a := a) (b := b) (t := aW) (by decide) na nb (by decide) hWa hWb
    (by decide)) fun t1 ⟨h1, k1, e1, r1⟩ => ?_
  have g1 : Stg g s0 A live c t1 :=
    h.next h1 k1 (by decide) (by decide) r1 opRegs_body
      (h.arrs_keep k1 (fun j hj e => hW (by simp at e; exact e ▸ hj)) (by decide)) h.live_lt
      (h.vd_keep k1 (by decide) (by decide)) (h.mask_keep k1 (by decide))
  refine g1.acc_ok ?_
  rw [e1, h.arrs.get ha, h.arrs.get hb]
  by_cases he : A a = A b <;> simp [he]

/-- `cnt33`: `r6 = 33`. -/
theorem cnt33_ok (u : State) : WP isa (.block cnt33) u fun u' => Upd u u' .r6 (BitVec.ofNat 32 33) :=
  wp_mov (op2_imm (by decide)) fun _ up => WP.block_nil up

/-- `cntW`: `r6 = 32 w`. -/
theorem cntW_ok {u : State} {B : BitVec 32} {Z w N : Nat} (h : Ws u B Z w N) :
    WP isa (.block cntW) u fun u' => Upd u u' .r6 (BitVec.ofNat 32 (32 * w)) := by
  refine wp_mov (op2_lsl (by decide)) fun u' up => WP.block_nil ?_
  have hw := h.wle
  refine ⟨?_, up.other, up.mem, up.rd, up.wr, up.sp⟩
  rw [up.gpr, h.r9]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega_using []

/-- `mulA y x m cnt`: `[aA] := ([y] mod 2^k) [x] mod [m]`, `k` the count `cnt` sets. -/
theorem Stg.mulA_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {y x m : Nat} {cnt : List Instr} {k : Nat}
    (hy : y ∈ live) (hx : x ∈ live) (hm : m ∈ live) (hz : aZ ∈ live) (hA0 : A aZ = 0)
    (hmi : MulIdx nArr aZ aY aX aA m aT) (hxY : x ≠ aY)
    (hfree : ∀ j ∈ live, j = aA ∨ j ∉ mulArrs aY aX aA aT) (hk : 0 < k) (hk' : k < 2 ^ 32)
    (hcnt : ∀ u : State, Ws u g.B g.Z g.w nArr → WP isa (.block cnt) u fun u' => Upd u u' .r6 (BitVec.ofNat 32 k)) :
    WP isa (seqs (mulA y x m cnt)) s fun t => ∃ R,
      (A x < A m → 2 * A m ≤ 2 ^ (32 * g.w) → R = A y % 2 ^ k * A x % A m) ∧
      Stg g s0 (upd A aA R) (aA :: live) c t := by
  have free : ∀ j ∈ live, j ≠ aA → j ≠ aY ∧ j ≠ aX ∧ j ∉ mulArrs aY aX aA aT := fun j hj hja => by
    rcases hfree j hj with e | n
    · exact absurd e hja
    · exact ⟨fun e => n (by simp [e]), fun e => n (by simp [e]), n⟩
  have yY : y ≠ aY := by
    rcases hfree y hy with e | n
    · rw [e]; decide
    · exact fun e => n (by simp [e])
  have zA : aZ ≠ aA := by decide
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
  refine WP.mono (hcnt t3 h3.ws) fun t4 u4 => ?_
  have k4 : Keep g.B g.w [] [] t3.mem t4.mem := by rw [u4.mem]; exact Keep.refl _ _ _ _ _
  have h4 := h3.next (h3.ws.of_upd u4 (by decide) (by decide) (by decide)) k4 (by simp) (by simp)
    (u4.rest (ws := [.r6]) (by simp)) (by decide) (h3.arrs_keep k4 (by simp) (by simp)) h3.live_lt
    (h3.vd_keep k4 (by simp) (by simp)) (h3.mask_keep k4 (by simp))
  have c4 : t4.gpr .r6 = BitVec.ofNat 32 k := u4.gpr
  refine WP.mono (mulMod_ok h4.ws (by decide) hmi hk hk' c4) fun t ⟨ht, k5, r5, v5⟩ => ?_
  -- The values `mulMod` starts from.
  have mi := hmi
  obtain ⟨_, _, _, _, _, hmT, _, _, _, hzm, _, _, hym, _, hxm, ham⟩ := mi
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
    rw [v5 rfl (by omega_using [hlt]) hlt hM, Nat.zero_add]
  · refine h4.next ht k5 (by decide) (by decide) r5 r6opRegs_body ?_
      (fun j hj => (List.mem_cons.mp hj).elim (fun e => by rw [e]; decide) (h.live_lt j))
      (h4.vd_keep k5 (by decide) (by decide)) (h4.mask_keep k5 (by decide))
    intro j hj'
    by_cases e : j = aA
    · subst e; rw [upd_self]
    · have hj : j ∈ live := (List.mem_cons.mp hj').resolve_left e
      obtain ⟨jY, jX, jn⟩ := free j hj e
      rw [upd_ne _ _ e, k5.num (j := j) (fun i hi ei => jn (by subst ei; exact hi)) (by decide) (h.ws.fit64 (h.live_lt j hj)),
        h4.arrs.get (by simp [hj]), upd_ne (j := aA) _ _ e, upd_ne (j := aX) _ _ jX, upd_ne (j := aY) _ _ jY]

end VG.Proof.Rsa.Arm.KeyCheck
