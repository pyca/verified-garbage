module

public import VerifiedGarbage.Proof.Rsa.X86.KcStart
public import VerifiedGarbage.Proof.Rsa.KeyCheckMath
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.MulMod
import VerifiedGarbage.Proof.Rsa.X86.KcOps
import VerifiedGarbage.Proof.Rsa.X86.InvParts
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Half
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
import VerifiedGarbage.Proof.Rsa.MulModArithmetic
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Rsa.X86.DivCount
import VerifiedGarbage.Proof.Framework.X86.Inline
public import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Ops

/-! # The checks of an RSA key on i686: the checks after the division of `n` by `p`

`crtChecks_ok`: from the quotient `X₁` and remainder `X₂` of `n / p`, the
mask is and'ed with `n / p = q`, `n mod p = 0`, `dP < p - 1`, `e dP ≡ 1`,
`dQ < q - 1`, `e dQ ≡ 1`, `qInv < p` and `q qInv ≡ 1` (`crtBits`), the
products known when their factor is below their modulus; `p - 1` and `q - 1`
are left in `aM1` and `aM2`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.KeyCheck VG.Impl.Rsa.X86.KeyCheckRt
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa.X86.KeyRt (MulIdx)

/-! ## `mulMod` counting in `esi`'s high half -/

section MulHi
open VG.Proof.Rsa.X86.KeyRt (RtWs kw MulIdx mulArrs nm1 nm4 mulHead_ok addMod_ok half_ok)
open VG.Impl.Rsa.X86.Keys (sB sC)
open VG.Impl.Rsa.X86.KeyCheckRt (lay stepUnit mulTailHi mulModStepHi mulModHi)

variable {B : Addr} {Z len N : Nat}

/-- `mulTailHi`: `[y]` halved, `esi` less `2^16`. -/
theorem mulTailHi_ok {full : Bool} {s : State} (h : RtWs (lay full) s B Z len N) {y : Nat} (hy : y < N) :
    WP isa (mulTailHi full y) s fun u => RtWs (lay full) u B Z len N ∧ Keep B (kw len) [y] [] s.mem u.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s u ∧
      u.gpr .esi = s.gpr .esi - BitVec.ofNat 32 stepUnit ∧
      u.cf = some (decide ((s.gpr .esi - BitVec.ofNat 32 stepUnit).toNat < stepUnit)) ∧
      num u.mem B (kw len) y = num s.mem B (kw len) y / 2 := by
  rw [mulTailHi, wp_seqs_cons (List.cons_ne_nil _ _)]
  refine wp_movS rfl fun t5 U _ => WP.block_nil ?_
  have h5 : RtWs (lay full) t5 B Z len N := h.keep U.keeps (by decide) (by decide) (by rw [U.mem]; exact fun _ _ => rfl)
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (half_ok h5 (j := y) hy (by rw [U.gpr]; decide)) fun t6 ⟨h6, k6, e6, r6⟩ => ?_
  refine wp_subS rfl fun t7 T7 _ => wp_cmpi fun u T cf _ => WP.block_nil ?_
  have countEq : t6.gpr .esi = s.gpr .esi := (r6.1 _ (by decide)).trans (U.other _ (by decide))
  have rest : Keeps [.esi] t6 u := T7.keeps.trans (T.keeps _)
  have mem : u.mem = t6.mem := T.mem.trans T7.mem
  rw [U.gpr, U.mem] at e6
  rw [U.mem] at k6
  refine ⟨h6.keep rest (by decide) (by decide) (by rw [mem]; exact fun _ _ => rfl), by rw [mem]; exact k6,
    (U.keeps.mono (by simp)).trans ((r6.mono (by simp)).trans (rest.mono (by simp))),
    by rw [T.gpr, T7.gpr, countEq], by rw [cf, T7.gpr, countEq]; rfl, ?_⟩
  rw [mem, e6, show (0 : BitVec 32).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]

/-- One step. -/
theorem mulModStepHi_ok {full : Bool} {s : State} (h : RtWs (lay full) s B Z len N) {z y x a m t : Nat}
    (hi : MulIdx N z y x a m t) :
    WP isa (mulModStepHi full z y x a m t) s fun u => RtWs (lay full) u B Z len N ∧
      Keep B (kw len) (mulArrs y x a t) [sB, sC] s.mem u.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s u ∧
      u.gpr .esi = s.gpr .esi - BitVec.ofNat 32 stepUnit ∧
      u.cf = some (decide ((s.gpr .esi - BitVec.ofNat 32 stepUnit).toNat < stepUnit)) ∧
      num u.mem B (kw len) y = num s.mem B (kw len) y / 2 ∧
      (num s.mem B (kw len) z = 0 → num s.mem B (kw len) a < num s.mem B (kw len) m →
        num s.mem B (kw len) x < num s.mem B (kw len) m → 2 * num s.mem B (kw len) m ≤ 2 ^ (32 * kw len) →
        num u.mem B (kw len) a =
          (num s.mem B (kw len) a + num s.mem B (kw len) y % 2 * num s.mem B (kw len) x) % num s.mem B (kw len) m ∧
        num u.mem B (kw len) x = (num s.mem B (kw len) x + num s.mem B (kw len) x) % num s.mem B (kw len) m) := by
  obtain ⟨ht, hz, hy, hx, ha, hm, hzy, hzx, hza, hzm, hyx, hya, hym, hxa, hxm, ham⟩ := hi
  -- The indices' facts, while the context is small.
  have zN : z < N := by omega_arith
  have yN : y < N := by omega_arith
  have xN : x < N := by omega_arith
  have aN : a < N := by omega_arith
  have mN : m < N := by omega_arith
  have tN : t < N := by omega_arith
  have t1N : t + 1 + 2 < N := by omega_arith
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
  have fz := h.ws.fit64 zN
  have fy := h.ws.fit64 yN
  have fx := h.ws.fit64 xN
  have fa := h.ws.fit64 aN
  have fm := h.ws.fit64 mN
  rw [mulModStepHi, wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (mulHead_ok h tN zN yN xN zt0.symm) fun t2 ⟨h2, k2, r2, e2⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (addMod_ok h2 (o := a) (a := a) (b := t) (m := m) (z := z) (t := t + 1) aN aN tN mN zN t1N
    at1 mt1 mt2 at3) fun t3 ⟨h3, k3, r3, e3⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (addMod_ok h3 (o := x) (a := x) (b := x) (m := m) (z := z) (t := t + 1) xN xN xN mN zN t1N
    xt1 mt1 mt2 xt3) fun t4 ⟨h4, k4, r4, e4⟩ => ?_
  refine WP.mono (mulTailHi_ok h4 yN) fun u ⟨hu, k6, esi, c6, z6, e6⟩ => ?_
  have esieq : t4.gpr .esi = s.gpr .esi := by
    rw [r4.1 _ (by decide), r3.1 _ (by decide), r2.1 _ (by decide)]
  refine ⟨hu, ((k2.mono.trans k3.mono).trans k4.mono).trans k6.mono,
    (r2.mono (by simp)).trans ((r3.mono (by simp)).trans ((r4.mono (by simp)).trans esi)),
    by rw [c6, esieq], by rw [z6, esieq], ?_, fun hZ hA hX hM => ?_⟩
  · rw [e6, k4.num (nm4 yt1 yt2 yt3 hyx) (by decide) fy, k3.num (nm4 yt1 yt2 yt3 hya) (by decide) fy,
      k2.num (nm1 yt0) (by decide) fy]
  · -- The values each step reads.
    have z2 : num t2.mem B (kw len) z = 0 := by rw [k2.num (nm1 zt0) (by decide) fz, hZ]
    have mm2 : num t2.mem B (kw len) m = num s.mem B (kw len) m := k2.num (nm1 mt0) (by decide) fm
    have a2 : num t2.mem B (kw len) a = num s.mem B (kw len) a := k2.num (nm1 at0) (by decide) fa
    have x2 : num t2.mem B (kw len) x = num s.mem B (kw len) x := k2.num (nm1 xt0) (by decide) fx
    have d2 : num t2.mem B (kw len) t = num s.mem B (kw len) y % 2 * num s.mem B (kw len) x := by
      rw [e2, hZ]
      rcases Nat.mod_two_eq_zero_or_one (num s.mem B (kw len) y) with e | e <;> simp [e]
    have dlt : num t2.mem B (kw len) t < num s.mem B (kw len) m := by
      rw [d2]; rcases Nat.mod_two_eq_zero_or_one (num s.mem B (kw len) y) with e | e <;> simp [e] <;> omega_arith
    have A3 := e3 z2 (by rw [a2, mm2]; exact hA) (by rw [mm2]; exact dlt) (by rw [mm2]; exact hM)
    rw [a2, mm2, d2] at A3
    have z3 : num t3.mem B (kw len) z = 0 := by rw [k3.num (nm4 zt1 zt2 zt3 hza) (by decide) fz, z2]
    have mm3 : num t3.mem B (kw len) m = num s.mem B (kw len) m := by
      rw [k3.num (nm4 mt1 mt2 mt3 ham.symm) (by decide) fm, mm2]
    have x3 : num t3.mem B (kw len) x = num s.mem B (kw len) x := by
      rw [k3.num (nm4 xt1 xt2 xt3 hxa) (by decide) fx, x2]
    have X4 := e4 z3 (by rw [x3, mm3]; exact hX) (by rw [x3, mm3]; exact hX) (by rw [mm3]; exact hM)
    rw [x3, mm3] at X4
    refine ⟨?_, ?_⟩
    · rw [k6.num (nm1 hya.symm) (by decide) fa, k4.num (nm4 at1 at2 at3 hxa.symm) (by decide) fa, A3]
    · rw [k6.num (nm1 hyx.symm) (by decide) fx, X4]

/-- The state after `i` of the `k` steps, with `o` in `esi`'s low half. -/
structure MulHiI (full : Bool) (s0 : State) (B : Addr) (Z len N z y x a m t k o i : Nat) (u : State) : Prop where
  ws : RtWs (lay full) u B Z len N
  keep : Keep B (kw len) (mulArrs y x a t) [sB, sC] s0.mem u.mem
  rest : Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s0 u
  count : u.gpr .esi = BitVec.ofNat 32 ((k - i) * stepUnit + o)
  yv : num u.mem B (kw len) y = num s0.mem B (kw len) y / 2 ^ i
  value : num s0.mem B (kw len) z = 0 → num s0.mem B (kw len) a < num s0.mem B (kw len) m →
    num s0.mem B (kw len) x < num s0.mem B (kw len) m → 2 * num s0.mem B (kw len) m ≤ 2 ^ (32 * kw len) →
    num u.mem B (kw len) a =
      (num s0.mem B (kw len) a + num s0.mem B (kw len) y % 2 ^ i * num s0.mem B (kw len) x) % num s0.mem B (kw len) m ∧
    num u.mem B (kw len) x = 2 ^ i * num s0.mem B (kw len) x % num s0.mem B (kw len) m

theorem mulModHiBody_ok {full : Bool} {s0 u : State} {z y x a m t k o i : Nat}
    (hi : MulIdx N z y x a m t) (hk : k * stepUnit + o < 2 ^ 32) (ho : o < stepUnit)
    (inv : MulHiI full s0 B Z len N z y x a m t k o i u) (hik : i < k) :
    WP isa (mulModStepHi full z y x a m t) u fun u' =>
      MulHiI full s0 B Z len N z y x a m t k o (i + 1) u' ∧ u'.cf = some (decide (i + 1 = k)) := by
  have h := inv.ws
  have hi' := hi
  obtain ⟨ht, hz, hy, hx, ha, hm, hzy, hzx, hza, hzm, hyx, hya, hym, hxa, hxm, ham⟩ := hi'
  have fz := h.ws.fit64 (j := z) (by omega_arith)
  have fm := h.ws.fit64 (j := m) (by omega_arith)
  have zk : num u.mem B (kw len) z = num s0.mem B (kw len) z := inv.keep.num (by simp; omega_arith) (by decide) fz
  have mk : num u.mem B (kw len) m = num s0.mem B (kw len) m := inv.keep.num (by simp; omega_arith) (by decide) fm
  refine WP.mono (mulModStepHi_ok h hi) fun u' ⟨h', k', r', c', f', y', v'⟩ => ?_
  have le : (k - (i + 1)) * stepUnit + o + stepUnit = (k - i) * stepUnit + o := by
    have : k - i = k - (i + 1) + 1 := by omega
    rw [this, Nat.succ_mul]; omega
  have bound : (k - i) * stepUnit + o < 2 ^ 32 :=
    Nat.lt_of_le_of_lt (Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) _) hk
  have cnt : u.gpr .esi - BitVec.ofNat 32 stepUnit = BitVec.ofNat 32 ((k - (i + 1)) * stepUnit + o) := by
    rw [inv.count, ← le, BitVec.ofNat_sub_ofNat_of_le _ _ (by unfold stepUnit; omega) (by omega),
      Nat.add_sub_cancel]
  refine ⟨⟨h', inv.keep.trans k', inv.rest.trans r', by rw [c', cnt], ?_, fun hZ hA hX hM => ?_⟩, ?_⟩
  · rw [y', inv.yv, Nat.div_div_eq_div_mul, Nat.pow_succ]
  · obtain ⟨va, vx⟩ := inv.value hZ hA hX hM
    have M0 : 0 < num s0.mem B (kw len) m := by omega_arith
    have aLt : num u.mem B (kw len) a < num u.mem B (kw len) m := by rw [va, mk]; exact Nat.mod_lt _ M0
    have xLt : num u.mem B (kw len) x < num u.mem B (kw len) m := by rw [vx, mk]; exact Nat.mod_lt _ M0
    obtain ⟨va', vx'⟩ := v' (by rw [zk, hZ]) aLt xLt (by rw [mk]; exact hM)
    rw [va', vx', va, vx, inv.yv, mk]
    exact ⟨VG.Proof.Rsa.mulMod_arith, VG.Proof.Rsa.double_arith⟩
  · rw [f', cnt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    congr 1
    simp only [decide_eq_decide]
    constructor
    · intro hlt
      rcases Nat.eq_zero_or_pos (k - (i + 1)) with e | e
      · omega
      · have := Nat.mul_le_mul_right stepUnit e; omega
    · intro e
      rw [show k - (i + 1) = 0 by omega, Nat.zero_mul, Nat.zero_add]
      exact ho

/-- `mulModHi z y x a m t` with `esi = 2^16 k + o`, `k > 0` and `o < 2^16`: `mulMod`'s product, and
`esi = o`. -/
theorem mulModHi_ok {full : Bool} {s : State} (h : RtWs (lay full) s B Z len N) {z y x a m t k o : Nat}
    (hi : MulIdx N z y x a m t) (hk : 0 < k) (hk' : k * stepUnit + o < 2 ^ 32) (ho : o < stepUnit)
    (c : s.gpr .esi = BitVec.ofNat 32 (k * stepUnit + o)) :
    WP isa (mulModHi full z y x a m t) s fun u => RtWs (lay full) u B Z len N ∧
      Keep B (kw len) (mulArrs y x a t) [sB, sC] s.mem u.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s u ∧
      u.gpr .esi = BitVec.ofNat 32 o ∧
      (num s.mem B (kw len) z = 0 → num s.mem B (kw len) a < num s.mem B (kw len) m →
        num s.mem B (kw len) x < num s.mem B (kw len) m → 2 * num s.mem B (kw len) m ≤ 2 ^ (32 * kw len) →
        num u.mem B (kw len) a =
          (num s.mem B (kw len) a + num s.mem B (kw len) y % 2 ^ k * num s.mem B (kw len) x) %
            num s.mem B (kw len) m) := by
  have start : MulHiI full s B Z len N z y x a m t k o 0 s :=
    ⟨h, Keep.refl _ _ _ _ _, Keeps.refl _ _, by rw [c, Nat.sub_zero], by rw [Nat.pow_zero, Nat.div_one],
      fun _ hA hX _ => ⟨by rw [Nat.pow_zero, Nat.mod_one, Nat.zero_mul, Nat.add_zero, Nat.mod_eq_of_lt hA],
        by rw [Nat.pow_zero, Nat.one_mul, Nat.mod_eq_of_lt hX]⟩⟩
  refine WP.loop (M := isa) (fun j u => ∃ i, i + j = k ∧ 0 < j ∧ MulHiI full s B Z len N z y x a m t k o i u) ?_ k s
    ⟨0, by omega_arith, hk, start⟩
  intro j u ⟨i, hij, hj, inv⟩
  refine WP.mono (mulModHiBody_ok hi hk' ho inv (by omega_arith)) fun u' ⟨iu, hc⟩ => ?_
  by_cases e : i + 1 = k
  · left
    refine ⟨by change u'.cf.map (!·) = some false; simp [hc, e], iu.ws, iu.keep, iu.rest, ?_, fun hZ hA hX hM => ?_⟩
    · rw [iu.count, e, Nat.sub_self, Nat.zero_mul, Nat.zero_add]
    · have v := (iu.value hZ hA hX hM).1
      rw [e] at v
      exact v
  · right
    exact ⟨by change u'.cf.map (!·) = some true; simp [hc, e], j - 1, by omega_arith, i + 1, by omega_arith, by omega_arith, iu⟩

end MulHi

/-! ## The three product checks, in one loop -/

section Products
open VG.Impl.Rsa.X86.KeyCheckRt (stepUnit cnt33Hi qBitsHi operands choose productCheck products mulModHi)
open VG.Proof.Rsa.X86.KeyRt (RtWs MulIdx mulArrs)

theorem rot13 {a : Nat} (h : a < 2 ^ 13) :
    (BitVec.ofNat 32 a).rotateRight 13 = BitVec.ofNat 32 (8 * a * stepUnit) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_rotateRight]
  simp only [BitVec.toNat_ofNat, stepUnit]
  rw [Nat.mod_eq_of_lt (by omega : a < 2 ^ 32), Nat.mod_eq_of_lt (by omega : 8 * a * 65536 < 2 ^ 32)]
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.div_eq_of_lt (by omega)]
  simp
  omega

/-- What a check's step count leaves: `esi` up by `2^16 k`. -/
def Stepped (k : Nat) (u u' : State) : Prop :=
  Keeps [.eax, .esi] u u' ∧ u'.mem = u.mem ∧ u'.gpr .esi = u.gpr .esi + BitVec.ofNat 32 (k * stepUnit)

theorem cnt33Hi_ok (u : State) : WP isa (.block cnt33Hi) u (Stepped 33 u) :=
  wp_addS rfl fun _ T _ => WP.block_nil ⟨T.keeps.mono (by decide), T.mem, T.gpr⟩

theorem qBitsHi_ok {full : Bool} {u : State} {B : Addr} {Z a : Nat}
    (c : VG.Proof.Bignum.X86.CallArgument u B Z (qLenArg full) (BitVec.ofNat 32 a)) (ha : a < 2 ^ 13) :
    WP isa (.block (qBitsHi full)) u (Stepped (8 * a) u) := by
  unfold qBitsHi
  refine wp_movS c.readSrc fun t1 u1 _ => wp_ror ⟨by decide, by decide⟩ fun t2 u2 => wp_addS rfl fun t3 u3 _ =>
    WP.block_nil ⟨(u1.keeps.mono (by decide)).trans ((u2.keeps.mono (by decide)).trans (u3.keeps.mono (by decide))),
      by rw [u3.mem, u2.mem, u1.mem], ?_⟩
  have e1 : t2.gpr .eax = BitVec.ofNat 32 (8 * a * stepUnit) := by rw [u2.gpr, u1.gpr, rot13 ha]
  have e2 : t2.gpr .esi = u.gpr .esi := by rw [u2.other _ (by decide), u1.other _ (by decide)]
  rw [u3.gpr, e1, e2]

/-- A step from `Stg` that writes no memory and only the registers `rs`. -/
theorem Stg.regs {g : Geo} {s0 s t : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {rs : List Reg} (K : Keeps rs s t) (mem : t.mem = s.mem)
    (hrs : ∀ x ∈ rs, x ∈ bodyRegs) : Stg g s0 A live c t := by
  have k : Keep g.B g.w [] [] s.mem t.mem := by rw [mem]; exact Keep.refl _ _ _ _ _
  exact h.next (h.ws.keep K (by intro e; have := hrs _ e; simp [bodyRegs] at this)
      (by intro e; have := hrs _ e; simp [bodyRegs] at this) (by rw [mem]; exact fun _ _ => rfl))
    k (by simp) (by simp) K hrs (h.arrs_keep k (by simp) (by simp)) h.live_lt
    (h.vd_keep k (by simp) (by simp)) (h.mask_keep k (by simp))

/-- `operands y x m cnt`: `[aY] := [y]`, `[aX] := [x]`, `[aVD] := [m]`, then `esi` up by `2^16 k`. -/
theorem Stg.operands_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {y x m k : Nat} {cnt : List Instr}
    (hy : y ∈ live) (hx : x ∈ live) (hm : m ∈ live)
    (hyY : y ≠ aY) (hxY : x ≠ aY) (hxX : x ≠ aX) (hmY : m ≠ aY) (hmX : m ≠ aX) (hmV : m ≠ aVD)
    (hcnt : ∀ u : State, RtWs g.L u g.B g.Z g.len nArr → Keeps bodyRegs s0 u → Outside g.B 0 g.Z s0.mem u.mem →
      WP isa (.block cnt) u (Stepped k u)) :
    WP isa (operands g.full y x m cnt) s fun u =>
      Stg g s0 (upd (upd (upd A aY (A y)) aX (A x)) aVD (A m)) (aVD :: aX :: aY :: live) c u ∧
      u.gpr .esi = s.gpr .esi + BitVec.ofNat 32 (k * stepUnit) := by
  unfold operands
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (WP.and (h.copy_ok (o := aY) (a := y) (by decide) hy hyY.symm)
    (VG.Proof.Rsa.X86.KeyRt.copy_ok h.ws (o := aY) (a := y) (by decide) (h.live_lt y hy) hyY.symm))
    fun t1 ⟨h1, _, _, _, r1, _⟩ => ?_
  have hx1 : x ∈ aY :: live := List.mem_cons_of_mem _ hx
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (WP.and (h1.copy_ok (o := aX) (a := x) (by decide) hx1 hxX.symm)
    (VG.Proof.Rsa.X86.KeyRt.copy_ok h1.ws (o := aX) (a := x) (by decide) (h1.live_lt x hx1) hxX.symm))
    fun t2 ⟨h2, _, _, _, r2, _⟩ => ?_
  rw [upd_ne _ _ hxY] at h2
  have hm2 : m ∈ aX :: aY :: live := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm)
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (WP.and (h2.copy_ok (o := aVD) (a := m) (by decide) hm2 hmV.symm)
    (VG.Proof.Rsa.X86.KeyRt.copy_ok h2.ws (o := aVD) (a := m) (by decide) (h2.live_lt m hm2) hmV.symm))
    fun t3 ⟨h3, _, _, _, r3, _⟩ => ?_
  rw [upd_ne _ _ hmX, upd_ne _ _ hmY] at h3
  refine WP.mono (hcnt t3 h3.ws h3.rest (VG.Proof.Rsa.X86.KeyRt.keep_outside h3.ws.ws h3.keep
    (fun j hj => List.mem_range.mp hj) (by decide))) fun u ⟨K, mem, e⟩ => ⟨h3.regs K mem (by decide), ?_⟩
  rw [e, r3.1 _ (by decide), r2.1 _ (by decide), r1.1 _ (by decide)]

/-- `mulModHi` from `Stg`, with `esi = 2^16 k + o`: `[aA] := ([aY] mod 2^k) [aX] mod [m]`. -/
theorem Stg.mulHi_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {m k o : Nat}
    (hm : m ∈ live) (hz : aZ ∈ live) (ha : aA ∈ live) (hA0 : A aZ = 0) (hAA : A aA = 0)
    (hmi : MulIdx nArr aZ aY aX aA m aT) (hfree : ∀ j ∈ live, j = aA ∨ j ∉ mulArrs aY aX aA aT)
    (hk : 0 < k) (hk' : k * stepUnit + o < 2 ^ 32) (ho : o < stepUnit)
    (e : s.gpr .esi = BitVec.ofNat 32 (k * stepUnit + o)) :
    WP isa (mulModHi g.full aZ aY aX aA m aT) s fun t => ∃ R,
      (num s.mem g.B g.w aX < A m → 2 * A m ≤ 2 ^ (32 * g.w) →
        R = num s.mem g.B g.w aY % 2 ^ k * num s.mem g.B g.w aX % A m) ∧
      Stg g s0 (upd A aA R) live c t ∧ t.gpr .esi = BitVec.ofNat 32 o := by
  refine WP.mono (mulModHi_ok h.ws hmi hk hk' ho e) fun t ⟨ht, k5, r5, e5, v5⟩ => ?_
  have gZ : num s.mem g.B g.w aZ = 0 := by rw [h.arrs.get hz, hA0]
  have gA : num s.mem g.B g.w aA = 0 := by rw [h.arrs.get ha, hAA]
  have gM : num s.mem g.B g.w m = A m := h.arrs.get hm
  refine ⟨num t.mem g.B g.w aA, fun hlt hM => ?_, ?_, e5⟩
  · rw [gZ, gA, gM] at v5
    rw [v5 rfl (by omega) hlt hM, Nat.zero_add]
  · refine h.next ht k5 (by decide) (by decide) r5 allRegs_body ?_ h.live_lt
      (h.vd_keep k5 (by decide) (by decide)) (h.mask_keep k5 (by decide))
    intro j hj
    by_cases ej : j = aA
    · subst ej; rw [upd_self]
    · have n := (hfree j hj).resolve_left ej
      rw [upd_ne _ _ ej, k5.num (fun i hi ei => n (by subst ei; exact hi)) (by decide)
        (h.ws.ws.fit64 (h.live_lt j hj)), h.arrs.get hj]

theorem noEsi_ltA (full : Bool) :
    ∀ i ∈ instrs (seqs (ltA full aX aVD)), VG.X86.Taint.clobbers i .esi = false := by
  have h : (instrs (seqs (ltA full aX aVD))).all (fun i => !VG.X86.Taint.clobbers i .esi) = true := by
    rw [← Code.allInstrs_eq]; cases full <;> decide +kernel
  intro i hi
  simpa using List.all_eq_true.mp h i hi

theorem noEsi_copy (full : Bool) :
    ∀ i ∈ instrs (VG.Impl.Rsa.X86.KeyRt.copy (lay full) aA aZ), VG.X86.Taint.clobbers i .esi = false := by
  have h : (instrs (VG.Impl.Rsa.X86.KeyRt.copy (lay full) aA aZ)).all (fun i => !VG.X86.Taint.clobbers i .esi) = true := by
    rw [← Code.allInstrs_eq]; cases full <;> decide +kernel
  intro i hi
  simpa using List.all_eq_true.mp h i hi

theorem noEsi_eqA (full : Bool) :
    ∀ i ∈ instrs (seqs (eqA full aA aOne)), VG.X86.Taint.clobbers i .esi = false := by
  have h : (instrs (seqs (eqA full aA aOne))).all (fun i => !VG.X86.Taint.clobbers i .esi) = true := by
    rw [← Code.allInstrs_eq]; cases full <;> decide +kernel
  intro i hi
  simpa using List.all_eq_true.mp h i hi

/-- What one check needs of the arrays it does not write. -/
structure Base (A : Nat → Nat) (live : List Nat) : Prop where
  zero : aZ ∈ live
  one : aOne ∈ live
  zeroV : A aZ = 0
  oneV : A aOne = 1
  free : ∀ j ∈ live, j ∉ [aY, aX, aA, aVD, aT, aT + 1, aT + 2, aT + 3, aW]

/-- A check's product: what it is when `[x] < [m]`. -/
def Prod (g : Geo) (A : Nat → Nat) (y x m k R : Nat) : Prop :=
  A x < A m → 2 * A m ≤ 2 ^ (32 * g.w) → R = A y % 2 ^ k * A x % A m

/-- A check after its operands: `[x] < [m]`, the product, `= 1`, and `esi` counted down. -/
theorem Stg.checkRest_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    {y x m k i : Nat}
    (h : Stg g s0 (upd (upd (upd A aY (A y)) aX (A x)) aVD (A m)) (aVD :: aX :: aY :: live) c s)
    (b : Base A live) (hk : 0 < k) (hk' : k * stepUnit + i < 2 ^ 32) (hi : 1 ≤ i) (hi' : i < stepUnit)
    (e : s.gpr .esi = BitVec.ofNat 32 (k * stepUnit + i)) :
    WP isa (seqs (ltA g.full aX aVD ++ ([VG.Impl.Rsa.X86.KeyRt.copy (lay g.full) aA aZ,
      mulModHi g.full aZ aY aX aA aVD aT] : List (Prog isa)) ++ eqA g.full aA aOne ++
      ([.block [.alu .sub .esi (.imm 1), .alu .cmp .esi (.imm 0)]] : List (Prog isa)))) s fun t => ∃ R, Prod g A y x m k R ∧
      Stg g s0 A live ((c && decide (A x < A m)) && decide (R = 1)) t ∧
      t.gpr .esi = BitVec.ofNat 32 (i - 1) ∧ t.zf = some (decide (i - 1 = 0)) := by
  have nW : aW ∉ live := fun hw => b.free aW hw (by decide)
  have nV : aVD ∉ live := fun hw => b.free aVD hw (by decide)
  have nX : aX ∉ live := fun hw => b.free aX hw (by decide)
  have nY : aY ∉ live := fun hw => b.free aY hw (by decide)
  have nA : aA ∉ live := fun hw => b.free aA hw (by decide)
  have vX : upd (upd (upd A aY (A y)) aX (A x)) aVD (A m) aX = A x := by
    rw [upd_ne _ _ (by decide), upd_self]
  have vV : upd (upd (upd A aY (A y)) aX (A x)) aVD (A m) aVD = A m := upd_self _ _ _
  have keepA : ∀ j ∈ live, upd (upd (upd A aY (A y)) aX (A x)) aVD (A m) j = A j := fun j hj => by
    rw [upd_ne _ _ (by rintro rfl; exact nV hj), upd_ne _ _ (by rintro rfl; exact nX hj),
      upd_ne _ _ (by rintro rfl; exact nY hj)]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  -- `[x] < [m]`.
  rw [wp_seqs_append (by simp [ltA]) (by simp)]
  refine WP.mono (WP.gpr (h.ltA_ok (a := aX) (b := aVD) (by simp) (by simp) (by simp [nW]; decide))
    (noEsi_ltA g.full)) fun t1 ⟨h1, e1⟩ => ?_
  rw [vX, vV] at h1
  -- `[aA] := 0`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (WP.gpr (h1.copy_ok (o := aA) (a := aZ) (by decide) (by simp [b.zero]) (by decide))
    (noEsi_copy g.full)) fun t2 ⟨h2, e2⟩ => ?_
  have gY : num t2.mem g.B g.w aY = A y := by
    rw [h2.arrs.get (by simp), upd_ne _ _ (by decide), upd_ne _ _ (by decide), upd_ne _ _ (by decide), upd_self]
  have gX : num t2.mem g.B g.w aX = A x := by rw [h2.arrs.get (by simp), upd_ne _ _ (by decide), vX]
  have z0 : upd (upd (upd A aY (A y)) aX (A x)) aVD (A m) aZ = 0 := by
    rw [keepA _ b.zero, b.zeroV]
  rw [z0] at h2
  have h2' := h2.sub (live' := aA :: aVD :: live) fun j hj => by
    simp only [List.mem_cons] at hj ⊢
    rcases hj with hj | hj | hj <;> simp [hj]
  -- The product.
  rw [wp_seqs_cons (by simp [eqA])]
  refine WP.mono (h2'.mulHi_ok (m := aVD) (k := k) (o := i) (by simp) (by simp [b.zero]) (by simp)
    (by rw [upd_ne _ _ (by decide), z0]) (upd_self _ _ _) (by decide)
    (by
      intro j hj
      simp only [List.mem_cons] at hj
      rcases hj with rfl | rfl | hj
      · exact .inl rfl
      · exact .inr (by decide)
      · refine .inr fun hm => b.free j hj ?_
        simp only [mulArrs, List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
    hk hk' hi' (by rw [e2, e1, e])) fun t3 ⟨R, hR, h3, e3⟩ => ?_
  rw [gY, gX, upd_ne _ _ (by decide), vV] at hR
  -- `= 1`.
  rw [wp_seqs_append (by simp [eqA]) (by simp)]
  refine WP.mono (WP.gpr (h3.eqA_ok (a := aA) (b := aOne) (by simp) (by simp [b.one]) (by simp [nW]; decide))
    (noEsi_eqA g.full)) fun t4 ⟨h4, e4⟩ => ?_
  have one4 : upd (upd (upd (upd (upd A aY (A y)) aX (A x)) aVD (A m)) aA 0) aA R aOne = 1 := by
    rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), keepA _ b.one, b.oneV]
  rw [upd_self, one4] at h4
  refine WP.mono (VG.Proof.Rsa.X86.Div.count_ok t4) fun t ⟨ct, zt, mt, kt⟩ => ?_
  have h5 := (h4.regs kt mt (by decide)).sub (live' := live) (fun j hj => by simp [hj])
  refine ⟨R, fun hlt hM => hR hlt hM, h5.congr' fun j hj => ?_, ?_, ?_⟩
  · rw [upd_ne _ _ (by rintro rfl; exact nA hj), upd_ne _ _ (by rintro rfl; exact nA hj), keepA j hj]
  · rw [ct, e4, e3]
    exact BitVec.ofNat_sub_ofNat_of_le (w := 32) i 1 (by decide) hi
  · rw [zt, e4, e3, show BitVec.ofNat 32 i - 1 = BitVec.ofNat 32 (i - 1) from
      BitVec.ofNat_sub_ofNat_of_le (w := 32) i 1 (by decide) hi, ofNat_beq_zero (by unfold stepUnit at hi'; omega)]

/-- Check `i`'s multiplier, multiplicand, modulus and steps (3: `e dP`, 2: `e dQ`, 1: `q qInv`). -/
def opY (i : Nat) : Nat := if i = 1 then aQ else aE
def opX (i : Nat) : Nat := if i = 3 then aDP else if i = 2 then aDQ else aQI
def opM (i : Nat) : Nat := if i = 3 then aM1 else if i = 2 then aM2 else aP
def opK (qa i : Nat) : Nat := if i = 1 then 8 * qa else 33

/-- The arrays the checks read. -/
abbrev inputsLive : List Nat := [aE, aP, aQ, aDP, aDQ, aQI, aM1, aM2]

/-- `choose`: check `i`'s operands, and its steps in `esi`'s high half. -/
theorem Stg.choose_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) (b : Base A live) (hlive : ∀ j ∈ inputsLive, j ∈ live) {qa i : Nat}
    (hi : i = 1 ∨ i = 2 ∨ i = 3) (e : s.gpr .esi = BitVec.ofNat 32 i)
    (qarg : VG.Proof.Bignum.X86.CallArgument s0 g.B g.Z (qLenArg g.full) (BitVec.ofNat 32 qa)) (qa2 : qa < 2 ^ 13) :
    WP isa (choose g.full) s fun u =>
      Stg g s0 (upd (upd (upd A aY (A (opY i))) aX (A (opX i))) aVD (A (opM i))) (aVD :: aX :: aY :: live) c u ∧
      u.gpr .esi = BitVec.ofNat 32 (opK qa i * stepUnit + i) := by
  have nf : ∀ j ∈ inputsLive, j ∈ live ∧ j ≠ aY ∧ j ≠ aX ∧ j ≠ aVD := fun j hj =>
    ⟨hlive j hj, fun e => b.free j (hlive j hj) (by simp [e]), fun e => b.free j (hlive j hj) (by simp [e]),
      fun e => b.free j (hlive j hj) (by simp [e])⟩
  have ops : ∀ {u : State} {y x m k : Nat} {cnt : List Instr}, Stg g s0 A live c u →
      u.gpr .esi = BitVec.ofNat 32 i → y ∈ inputsLive → x ∈ inputsLive → m ∈ inputsLive →
      (∀ u : State, RtWs g.L u g.B g.Z g.len nArr → Keeps bodyRegs s0 u → Outside g.B 0 g.Z s0.mem u.mem →
        WP isa (.block cnt) u (Stepped k u)) →
      WP isa (operands g.full y x m cnt) u fun u' =>
        Stg g s0 (upd (upd (upd A aY (A y)) aX (A x)) aVD (A m)) (aVD :: aX :: aY :: live) c u' ∧
        u'.gpr .esi = BitVec.ofNat 32 (k * stepUnit + i) := by
    intro u y x m k cnt hu eu hy hx hm hcnt
    obtain ⟨ly, yY, -, -⟩ := nf y hy
    obtain ⟨lx, xY, xX, -⟩ := nf x hx
    obtain ⟨lm, mY, mX, mV⟩ := nf m hm
    refine WP.mono (hu.operands_ok ly lx lm yY xY xX mY mX mV hcnt) fun u' ⟨h', e'⟩ => ⟨h', ?_⟩
    rw [e', eu, BitVec.ofNat_add_ofNat, Nat.add_comm]
  have c33 : ∀ u : State, RtWs g.L u g.B g.Z g.len nArr → Keeps bodyRegs s0 u → Outside g.B 0 g.Z s0.mem u.mem →
      WP isa (.block cnt33Hi) u (Stepped 33 u) := fun u _ _ _ => cnt33Hi_ok u
  have cq : ∀ u : State, RtWs g.L u g.B g.Z g.len nArr → Keeps bodyRegs s0 u → Outside g.B 0 g.Z s0.mem u.mem →
      WP isa (.block (qBitsHi g.full)) u (Stepped (8 * qa) u) := fun _ _ K O => qBitsHi_ok (qarg.keep K (by decide) O) qa2
  unfold choose
  refine WP.seq (wp_cmpi fun u U _ z => WP.block_nil ?_)
  have hu := h.regs (U.keeps []) U.mem (by decide)
  have eu : u.gpr .esi = BitVec.ofNat 32 i := by rw [U.gpr]; exact e
  rw [e] at z
  rcases hi with rfl | rfl | rfl
  · refine WP.ite false (by change u.zf = _; rw [z]; decide) (fun f => absurd f (by decide)) fun _ => ?_
    refine WP.seq (wp_cmpi fun u₂ U₂ _ z₂ => WP.block_nil ?_)
    have hu₂ := hu.regs (U₂.keeps []) U₂.mem (by decide)
    have eu₂ : u₂.gpr .esi = BitVec.ofNat 32 1 := by rw [U₂.gpr]; exact eu
    rw [eu] at z₂
    refine WP.ite false (by change u₂.zf = _; rw [z₂]; decide) (fun f => absurd f (by decide)) fun _ => ?_
    exact ops hu₂ eu₂ (by decide) (by decide) (by decide) cq
  · refine WP.ite false (by change u.zf = _; rw [z]; decide) (fun f => absurd f (by decide)) fun _ => ?_
    refine WP.seq (wp_cmpi fun u₂ U₂ _ z₂ => WP.block_nil ?_)
    have hu₂ := hu.regs (U₂.keeps []) U₂.mem (by decide)
    have eu₂ : u₂.gpr .esi = BitVec.ofNat 32 2 := by rw [U₂.gpr]; exact eu
    rw [eu] at z₂
    refine WP.ite true (by change u₂.zf = _; rw [z₂]; decide) (fun _ => ?_) fun f => absurd f (by decide)
    exact ops hu₂ eu₂ (by decide) (by decide) (by decide) c33
  · refine WP.ite true (by change u.zf = _; rw [z]; decide) (fun _ => ?_) fun f => absurd f (by decide)
    exact ops hu eu (by decide) (by decide) (by decide) c33

/-- One check, from `esi = i`. -/
theorem Stg.product_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) (b : Base A live) (hlive : ∀ j ∈ inputsLive, j ∈ live) {qa i : Nat}
    (hi : i = 1 ∨ i = 2 ∨ i = 3) (e : s.gpr .esi = BitVec.ofNat 32 i)
    (qarg : VG.Proof.Bignum.X86.CallArgument s0 g.B g.Z (qLenArg g.full) (BitVec.ofNat 32 qa))
    (qa1 : 1 ≤ qa) (qa2 : qa < 2 ^ 13) :
    WP isa (productCheck g.full) s fun t => ∃ R, Prod g A (opY i) (opX i) (opM i) (opK qa i) R ∧
      Stg g s0 A live ((c && decide (A (opX i) < A (opM i))) && decide (R = 1)) t ∧
      t.gpr .esi = BitVec.ofNat 32 (i - 1) ∧ t.zf = some (decide (i - 1 = 0)) := by
  have hk : 0 < opK qa i := by unfold opK; split <;> omega
  have hk' : opK qa i * stepUnit + i < 2 ^ 32 := by unfold opK stepUnit; split <;> omega
  rw [show productCheck g.full = seqs (choose g.full :: (ltA g.full aX aVD ++
    ([VG.Impl.Rsa.X86.KeyRt.copy (lay g.full) aA aZ, mulModHi g.full aZ aY aX aA aVD aT] : List (Prog isa)) ++
    eqA g.full aA aOne ++ ([.block [.alu .sub .esi (.imm 1), .alu .cmp .esi (.imm 0)]] : List (Prog isa)))) from rfl, wp_seqs_cons (by simp [ltA])]
  refine WP.mono (h.choose_ok b hlive hi e qarg qa2) fun u ⟨hu, eu⟩ => ?_
  exact hu.checkRest_ok b hk hk' (by omega) (by unfold stepUnit; omega) eu

/-- The three checks: `dP`, `dQ`, then `qInv`. -/
theorem Stg.products_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) (b : Base A live) (hlive : ∀ j ∈ inputsLive, j ∈ live) {qa : Nat}
    (qarg : VG.Proof.Bignum.X86.CallArgument s0 g.B g.Z (qLenArg g.full) (BitVec.ofNat 32 qa))
    (qa1 : 1 ≤ qa) (qa2 : qa < 2 ^ 13) :
    WP isa (products g.full) s fun t => ∃ R₁ R₂ R₃, Prod g A aE aDP aM1 33 R₁ ∧ Prod g A aE aDQ aM2 33 R₂ ∧
      Prod g A aQ aQI aP (8 * qa) R₃ ∧
      Stg g s0 A live ((((((c && decide (A aDP < A aM1)) && decide (R₁ = 1)) && decide (A aDQ < A aM2)) &&
        decide (R₂ = 1)) && decide (A aQI < A aP)) && decide (R₃ = 1)) t := by
  unfold products
  refine WP.seq (wp_movi fun u U => WP.block_nil ?_)
  have hu := h.regs U.keeps U.mem (by decide)
  refine WP.loop (M := isa) (fun n u =>
      (n = 3 ∧ Stg g s0 A live c u ∧ u.gpr .esi = BitVec.ofNat 32 3) ∨
      (n = 2 ∧ ∃ R₁, Prod g A aE aDP aM1 33 R₁ ∧
        Stg g s0 A live ((c && decide (A aDP < A aM1)) && decide (R₁ = 1)) u ∧ u.gpr .esi = BitVec.ofNat 32 2) ∨
      (n = 1 ∧ ∃ R₁ R₂, Prod g A aE aDP aM1 33 R₁ ∧ Prod g A aE aDQ aM2 33 R₂ ∧
        Stg g s0 A live ((((c && decide (A aDP < A aM1)) && decide (R₁ = 1)) && decide (A aDQ < A aM2)) &&
          decide (R₂ = 1)) u ∧ u.gpr .esi = BitVec.ofNat 32 1)) ?_ 3 u (.inl ⟨rfl, hu, U.gpr⟩)
  rintro n v (⟨rfl, hv, ev⟩ | ⟨rfl, R₁, p₁, hv, ev⟩ | ⟨rfl, R₁, R₂, p₁, p₂, hv, ev⟩)
  · refine WP.mono (hv.product_ok b hlive (.inr (.inr rfl)) ev qarg qa1 qa2) fun t ⟨R, pR, ht, et, zt⟩ => ?_
    simp only [opY, opX, opM, opK] at pR ht
    exact .inr ⟨by change t.zf.map (!·) = _; rw [zt]; rfl, 2, by omega, .inr (.inl ⟨rfl, R, pR, ht, et⟩)⟩
  · refine WP.mono (hv.product_ok b hlive (.inr (.inl rfl)) ev qarg qa1 qa2) fun t ⟨R, pR, ht, et, zt⟩ => ?_
    simp only [opY, opX, opM, opK] at pR ht
    exact .inr ⟨by change t.zf.map (!·) = _; rw [zt]; rfl, 1, by omega, .inr (.inr ⟨rfl, R₁, R, p₁, pR, ht, et⟩)⟩
  · refine WP.mono (hv.product_ok b hlive (.inl rfl) ev qarg qa1 qa2) fun t ⟨R, pR, ht, _, zt⟩ => ?_
    simp only [opY, opX, opM, opK] at pR ht
    exact .inl ⟨by change t.zf.map (!·) = _; rw [zt]; rfl, R₁, R₂, R, p₁, p₂, pR, ht⟩

end Products

/-- The arrays after the division of `n` by `p`. -/
abbrev aDivN (v : Vals) (X₁ X₂ : Nat) : Nat → Nat := upd (upd (upd (vals v) aOne 1) aVQ X₁) aVR X₂

/-- The arrays the checks of `d` use. -/
abbrev aFin (v : Vals) : Nat → Nat := upd (upd (vals v) aM1 (2 * (v.p / 2))) aM2 (2 * (v.q / 2))
abbrev liveFin : List Nat := [aZ, aN, aD, aDP, aDQ, aM1, aM2]

theorem mulIdx_m1 : MulIdx nArr aZ aY aX aA aM1 aT := by decide
theorem mulIdx_m2 : MulIdx nArr aZ aY aX aA aM2 aT := by decide
theorem mulIdx_p : MulIdx nArr aZ aY aX aA aP aT := by decide

theorem crtChecks_ok {g : Geo} {s0 s : State} {v : Vals} {X₁ X₂ : Nat}
    (h : Stg g s0 (aDivN v X₁ X₂) (aVR :: aVQ :: live0) (decide (v.p % 2 = 1)) s)
    (hq : ∃ a, 1 ≤ a ∧ a ≤ 1024 ∧ v.q < 2 ^ (8 * a) ∧
      VG.Proof.Bignum.X86.CallArgument s0 g.B g.Z (qLenArg g.full) (BitVec.ofNat 32 a)) :
    WP isa (crtChecks g.full) s fun t => ∃ R₁ R₂ R₃ : Nat,
      (v.dP < 2 * (v.p / 2) → 2 * (2 * (v.p / 2)) ≤ 2 ^ (32 * g.w) →
        R₁ = v.e % 2 ^ 33 * v.dP % (2 * (v.p / 2))) ∧
      (v.dQ < 2 * (v.q / 2) → 2 * (2 * (v.q / 2)) ≤ 2 ^ (32 * g.w) →
        R₂ = v.e % 2 ^ 33 * v.dQ % (2 * (v.q / 2))) ∧
      (v.qI < v.p → 2 * v.p ≤ 2 ^ (32 * g.w) → R₃ = v.q * v.qI % v.p) ∧
      Stg g s0 (aFin v) liveFin
        (VG.Proof.Rsa.crtBits v.p v.q v.dP v.dQ v.qI X₁ X₂ R₁ R₂ R₃) t := by
  obtain ⟨qa, qa1, qa2, qlt, qarg⟩ := hq
  have wpos := h.ws.ws.wpos
  have wle := h.ws.ws.wle
  unfold crtChecks
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [wp_seqs_append (by simp [eqA]) (by simp [eqA])]
  refine WP.mono (h.eqA_ok (a := aVQ) (b := aQ) (by decide) (by decide) (by decide)) fun t1 h1 => ?_
  rw [wp_seqs_append (by simp [eqA]) (by simp)]
  refine WP.mono (h1.eqA_ok (a := aVR) (b := aZ) (by decide) (by decide) (by decide)) fun t2 h2 => ?_
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (h2.copy_ok (o := aM1) (a := aP) (by decide) (by decide) (by decide)) fun t3 h3 => ?_
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (h3.clrLow_ok (j := aM1) (by decide)) fun t4 h4 => ?_
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (h4.copy_ok (o := aM2) (a := aQ) (by decide) (by decide) (by decide)) fun t5 h5 => ?_
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (h5.clrLow_ok (j := aM2) (by decide)) fun t6 h6 => ?_
  -- The products.
  refine WP.mono (h6.products_ok ⟨by decide, by decide, rfl, rfl, by decide⟩ (by decide) qarg qa1 (by omega)) fun t ⟨R₁, R₂, R₃, hR₁, hR₂, hR₃, h7⟩ => ?_
  refine ⟨R₁, R₂, R₃, hR₁, hR₂, fun hlt hM => ?_, (h7.sub (live' := liveFin) (by decide)).congr rfl⟩
  refine (hR₃ hlt hM).trans ?_
  show v.q % 2 ^ (8 * qa) * v.qI % v.p = _
  rw [Nat.mod_eq_of_lt qlt]

end VG.Proof.Rsa.X86.KeyCheck
