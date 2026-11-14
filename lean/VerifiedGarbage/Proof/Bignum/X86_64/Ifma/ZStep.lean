module

public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.ZSym
public import VerifiedGarbage.Proof.Bignum.AmmD52
import VerifiedGarbage.Proof.Framework.KernelRfl

/-!
# RSA with AVX512_IFMA on x86-64: a step of the multiplication modulo `-1 (mod 2¹⁰⁴)`

`zStep`, a step of `ammCoreZ` (`Impl/Rsa/X86_64/CrtIfma.lean`), against
`AmmD52.step`, the multiplication as the registers hold it: from the two
sets of limbs of `AmmD52.St` in the roles of step `i`, with the low halves
of the first row's products with the limb `b` already in the first set
(`ZAcc`), and the operands' rows in their registers (`ZCon`), the step
leaves `AmmD52.step`'s limbs in the roles of step `i + 1`, with the low
halves of the next limb's products unless the step is the last
(`zStep_ok`).

The registers after the step are terms in those before it (`expZ`), which
`ZSym`'s run of the step gives: the kernel checks it for each step of a
block of the layout (`zStep_run2048`).
-/
-- separate module: a change to the loop or the stores of `ZCore` does not check the steps' terms and proofs again.

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64
open VG.Proof.Bignum.Amm52 (lo hi lo_lt hi_lt)
open VG.Proof.Bignum.AmmD52 (Ops St Ok lowS stepQ pend)
open VG.Impl.Rsa.X86_64.CrtIfma
open VG.Proof.Bignum.X86_64.AmmSym (Ctx Keeps)
open VG.Proof.X25519.X86_64.Ifma (mad52 mad52_toNat)
open VG.Proof.Poly1305.X86_64.Avx2 (sel4)

/-- The layouts whose multiplication is `ammCoreZ`. -/
def ZOk (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : Prop := l = lay2048z

/-! ## The registers after a step, as terms -/

section Terms

variable (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay)

/-- The registers' numbers (`zB`, …, `zT`). -/
def znB (k i : Nat) : Nat := (k + i) % l.R
def znU (k i : Nat) : Nat := l.R + (k + i) % l.R
def znBq (par : Nat) : Nat := 2 * l.R + par
def znUq (par : Nat) : Nat := 2 * l.R + 2 + par
def znC : Nat := 2 * l.R + 4
def znA (k : Nat) : Nat := 2 * l.R + 5 + k
def znM (k : Nat) : Nat := 3 * l.R + 4 + k
def znK : Nat := 4 * l.R + 6
def znT : Nat := 4 * l.R + 7

/-- The bytes the multiplication loads from each base. -/
def limZ : Reg → Nat
  | .r8 => l.D + l.NB
  | .r9 => l.D + 32 * (l.R - 1) + 8
  | .r10 => l.D + l.oMs + l.NB
  | _ => 0

/-- The sum of the two sets' role 0. -/
def zSum (i : Nat) : ZT := .add (.reg (znU l 0 i)) (.reg (znB l 0 i))

/-- `u`: quadword 0 of each lane's sum, in each of its quadwords. -/
def zQ (i : Nat) : ZT := .perm (zSum l i) 0

/-- The next limb of the second operand, of each lane. -/
def zBn (i : Nat) : ZT := .ins (.bcy .r9 (l.off (i + 1))) (.bcy .r9 (l.D + l.off (i + 1)))

/-- The first set's role `κ` after step `i`. -/
def zBT (i : Nat) (last : Bool) (κ : Nat) : ZT :=
  if κ = 0 then .mad true .zero (.reg (znBq l (i % 2))) (.reg (znA l (l.R - 1)))
  else if κ = 1 then
    .add (.mad true (.mad false
        (if last then .reg (znB l 1 i) else .mad false (.reg (znB l 1 i)) (zBn l i) (.reg (znA l 0)))
        (.reg (znBq l (i % 2))) (.reg (znA l 1))) (.reg (znBq l (i % 2))) (.reg (znA l 0)))
      (.shr (zSum l i) 52)
  else .mad true (.mad false (.reg (znB l κ i)) (.reg (znBq l (i % 2))) (.reg (znA l κ)))
    (.reg (znBq l (i % 2))) (.reg (znA l (κ - 1)))

/-- The second set's role `κ` after step `i`. -/
def zUT (i : Nat) (κ : Nat) : ZT :=
  if κ = 0 then
    .mad true (.mad false (.mad false (.mad true (.and (.perm (zSum l i) 0xF9) (.reg (znK l)))
          (.reg (znUq l ((i + 1) % 2))) (.reg (znM l l.R)))
        (.reg (znUq l ((i + 1) % 2))) (.reg (znM l (l.R + 1))))
      (zQ l i) (.reg (znM l l.R))) (zQ l i) (.reg (znM l (l.R - 1)))
  else if κ = 1 then .reg (znU l 1 i)
  else .mad true (.mad false (.reg (znU l κ i)) (zQ l i) (.reg (znM l κ))) (zQ l i) (.reg (znM l (κ - 1)))

/-- The role at step `i` of the register whose number is `r` modulo `R`. -/
def roleZ (r i : Nat) : Nat := (r % l.R + l.R - i % l.R) % l.R

/-- The registers after step `i`. -/
def expZ (i : Nat) (last : Bool) (r : Nat) : ZT :=
  if r < l.R then zBT l i last (roleZ l r i)
  else if r < 2 * l.R then zUT l i (roleZ l r i)
  else if r = znUq l (i % 2) then zQ l i
  else if r = znC l then .shr (zSum l i) 52
  else if last then .reg r
  else if r = znBq l ((i + 1) % 2) then zBn l i
  else if r = znT l then .bcy .r9 (l.D + l.off (i + 1))
  else .reg r

end Terms

/-- `ZSym`'s run of each step of a block of `lay2048z`, with a limb of the
second operand after it or none. -/
theorem zStep_run2048 :
    ((List.range 6).map fun i => [false, true].map fun last =>
      (ZSym.init.run (limZ lay2048z) (zStep lay2048z i last)).map fun σ => (List.range 32).map σ.reg) =
    (List.range 6).map fun i => [false, true].map fun last =>
      some ((List.range 32).map (expZ lay2048z i last)) := by
  kernel_rfl

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

theorem ZOk.R (hz : ZOk l) : l.R = 6 := by rw [hz]; rfl

/-- The run of step `i`. -/
theorem run_zStep (hz : ZOk l) {i : Nat} (hi : i < l.R) (last : Bool) :
    ∃ σ, ZSym.init.run (limZ l) (zStep l i last) = some σ ∧ ∀ r < 32, σ.reg r = expZ l i last r := by
  obtain rfl := hz
  have h1 := List.map_inj_left.1 zStep_run2048 i (List.mem_range.2 hi)
  have h2 := List.map_inj_left.1 h1 last (by cases last <;> simp)
  obtain ⟨σ, e, h3⟩ := Option.map_eq_some_iff.1 h2
  exact ⟨σ, e, fun r hr => List.map_inj_left.1 h3 r (List.mem_range.2 hr)⟩

/-! ## The step against the model -/

theorem mad_lo' (c x y : Nat) :
    mad52 false (BitVec.ofNat 64 c) (BitVec.ofNat 64 x) (BitVec.ofNat 64 y) = BitVec.ofNat 64 (c + lo y x) := by
  apply BitVec.eq_of_toNat_eq
  rw [mad52_toNat]
  simp only [Bool.false_eq_true, ite_false, BitVec.toNat_ofNat]
  have e : ∀ v : Nat, v % 2 ^ 64 % 2 ^ 52 = v % 2 ^ 52 := fun v => Nat.mod_mod_of_dvd _ (by decide)
  rw [e, e, Nat.mul_comm, show y % 2 ^ 52 * (x % 2 ^ 52) % 2 ^ 52 = lo y x from rfl, Nat.mod_add_mod]

theorem mad_hi' (c x y : Nat) :
    mad52 true (BitVec.ofNat 64 c) (BitVec.ofNat 64 x) (BitVec.ofNat 64 y) = BitVec.ofNat 64 (c + hi y x) := by
  apply BitVec.eq_of_toNat_eq
  rw [mad52_toNat]
  simp only [ite_true, BitVec.toNat_ofNat]
  have e : ∀ v : Nat, v % 2 ^ 64 % 2 ^ 52 = v % 2 ^ 52 := fun v => Nat.mod_mod_of_dvd _ (by decide)
  rw [e, e, Nat.mul_comm, show y % 2 ^ 52 * (x % 2 ^ 52) / 2 ^ 52 = hi y x from rfl, Nat.mod_add_mod]

theorem lo_modr (x y : Nat) : lo x (y % 2 ^ 52) = lo x y := by unfold lo; rw [Nat.mod_mod]
theorem hi_modr (x y : Nat) : hi x (y % 2 ^ 52) = hi x y := by unfold hi; rw [Nat.mod_mod]

/-- The operands' rows in their registers: quadword `k` is column `k % 4`
of lane `k / 4`, limb `R (k % 4) + kk` of row `kk`. -/
structure ZCon (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (s : State) (o : Nat → Ops) : Prop where
  a : ∀ kk < l.R, ∀ k < 8, qz s (zA l kk) k = BitVec.ofNat 64 ((o (k / 4)).a (l.R * (k % 4) + kk))
  m : ∀ kk, 1 ≤ kk → kk < l.R → ∀ k < 8,
    qz s (zM l kk) k = BitVec.ofNat 64 ((o (k / 4)).ms (l.R * (k % 4) + kk))
  m0 : ∀ k < 8, qz s (zM l l.R) k = BitVec.ofNat 64 ((o (k / 4)).ms (l.R * ((k % 4 + 1) % 4)))
  m1 : ∀ k < 8, qz s (zM l (l.R + 1)) k = BitVec.ofNat 64 ((o (k / 4)).ms (l.R * ((k % 4 + 1) % 4) + 1))
  k : ∀ k < 8, qz s (zK l) k = if k % 4 < 3 then mask52 else 0

/-- The two sets of limbs `st` in the roles of step `i`, the first with the
low halves of row 0's products with the limb `b`; `w`, whose low 52 bits
are the `u` before; and a bound of the limbs. -/
structure ZAcc (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (s : State) (i : Nat) (o : Nat → Ops) (st : Nat → St)
    (b w : Nat → Nat) (Bd : Nat) : Prop where
  bs : ∀ kk < l.R, ∀ k < 8, qz s (zB l kk i) k = BitVec.ofNat 64 ((st (k / 4)).bs (l.R * (k % 4) + kk) +
    if kk = 0 then lo ((o (k / 4)).a (l.R * (k % 4))) (b (k / 4)) else 0)
  us : ∀ kk < l.R, ∀ k < 8, qz s (zU l kk i) k = BitVec.ofNat 64 ((st (k / 4)).us (l.R * (k % 4) + kk))
  up : ∀ k < 8, qz s (zUq l ((i + 1) % 2)) k = BitVec.ofNat 64 (w (k / 4))
  wq : ∀ p < 2, w p % 2 ^ 52 = (st p).qp
  bd : ∀ p < 2, ∀ j, (st p).bs j < Bd ∧ (st p).us j < Bd

/-- What a step starts from. -/
structure ZIn (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (s : State) (i : Nat) (o : Nat → Ops) (st : Nat → St)
    (b w : Nat → Nat) (Bd : Nat) : Prop where
  acc : ZAcc l s i o st b w Bd
  con : ZCon l s o
  bq : ∀ k < 8, qz s (zBq l (i % 2)) k = BitVec.ofNat 64 (b (k / 4))
  ok : ∀ p < 2, Ok l.L (o p)
  hBd : Bd ≤ 2 ^ 62

section Eval

variable {s : State} {i : Nat} {o : Nat → Ops} {st : Nat → St} {b w : Nat → Nat} {Bd : Nat}

theorem ZIn.sum (h : ZIn l s i o st b w Bd) (hR : l.R = 6) {k : Nat} (hk : k < 8) :
    (zSum l i).eval s k = BitVec.ofNat 64 (lowS (o (k / 4)) (st (k / 4)) (b (k / 4)) (l.R * (k % 4))) := by
  simp only [zSum, ZT.eval]
  rw [show qz s (vreg (znU l 0 i)) k = _ from h.acc.us 0 (by omega_using [hR]) k hk,
    show qz s (vreg (znB l 0 i)) k = _ from h.acc.bs 0 (by omega_using [hR]) k hk, ite_eq_left rfl, Nat.add_zero,
    ← BitVec.ofNat_add]
  congr 1; unfold lowS; omega_using []

theorem ZIn.sum_lt (h : ZIn l s i o st b w Bd) {p : Nat} (hp : p < 2) (j : Nat) :
    lowS (o p) (st p) (b p) j < 2 ^ 64 := by
  have := h.acc.bd p hp j; have := lo_lt ((o p).a j) (b p); have := h.hBd
  unfold lowS; omega_arith

/-- `u`'s register: limb 0's sum of each lane. -/
theorem ZIn.q (h : ZIn l s i o st b w Bd) (hR : l.R = 6) {k : Nat} (hk : k < 8) :
    (zQ l i).eval s k = BitVec.ofNat 64 (lowS (o (k / 4)) (st (k / 4)) (b (k / 4)) 0) := by
  simp only [zQ, ZT.eval]
  rw [show sel4 0 (k % 4) = 0 by unfold sel4; rw [Nat.zero_div, Nat.zero_mod], Nat.add_zero,
    h.sum hR (by omega_using [hk]), show 4 * (k / 4) / 4 = k / 4 by omega_using [], show 4 * (k / 4) % 4 = 0 by omega_using [], Nat.mul_zero]

/-- The next limb's register. -/
theorem zBn_eval {bn : Nat → Nat}
    (hb0 : s.mem.readW (s.gpr .r9 + BitVec.ofNat 64 (l.off (i + 1))) 64 = BitVec.ofNat 64 (bn 0))
    (hb1 : s.mem.readW (s.gpr .r9 + BitVec.ofNat 64 (l.D + l.off (i + 1))) 64 = BitVec.ofNat 64 (bn 1))
    {k : Nat} (hk : k < 8) : (zBn l i).eval s k = BitVec.ofNat 64 (bn (k / 4)) := by
  simp only [zBn, ZT.eval]
  by_cases h4 : k < 4
  · rw [ite_eq_left h4, ite_eq_left h4, hb0, show k / 4 = 0 by omega_using [h4]]
  · rw [ite_eq_right h4, ite_eq_left (by omega_using [hk]), hb1, show k / 4 = 1 by omega_using [hk, h4]]

/-- The first set's role `kk` after the step: the model's, with the low
halves of row 0's products with the next limb `bn` (0 after the last step). -/
theorem ZIn.bT (h : ZIn l s i o st b w Bd) (hR : l.R = 6) {last : Bool} {bn : Nat → Nat}
    (hbn : last = false → ∀ k < 8, (zBn l i).eval s k = BitVec.ofNat 64 (bn (k / 4)))
    (hl : last = true → ∀ p, bn p = 0) {kk : Nat} (hkk : kk < 6) {k : Nat} (hk : k < 8) :
    (zBT l i last ((kk + 1) % 6)).eval s k =
      BitVec.ofNat 64 ((AmmD52.step l.L l.R (o (k / 4)) (st (k / 4)) (b (k / 4))).bs (l.R * (k % 4) + kk) +
        if kk = 0 then lo ((o (k / 4)).a (l.R * (k % 4))) (bn (k / 4)) else 0) := by
  have hB : qz s (vreg (znBq l (i % 2))) k = _ := h.bq k hk
  have hA : ∀ j < 6, qz s (vreg (znA l j)) k = _ := fun j hj => h.con.a j (by omega_using [hR, hj]) k hk
  have hb : ∀ j < 6, qz s (vreg (znB l j i)) k = _ := fun j hj => h.acc.bs j (by omega_using [hR, hj]) k hk
  rcases (by omega_using [hkk] : kk = 0 ∨ kk = 5 ∨ (1 ≤ kk ∧ kk ≤ 4)) with rfl | rfl | hk'
  · -- role 0, which was role 1
    show (zBT l i last 1).eval s k = _
    rw [zBT, ite_eq_right (by decide), ite_eq_left rfl, ite_eq_left rfl]
    have hs := h.sum_lt (show k / 4 < 2 by omega_using [hk]) (l.R * (k % 4))
    cases last with
    | false =>
      simp only [ZT.eval, Bool.false_eq_true, ite_false]
      rw [hb 1 (by decide), hbn rfl k hk, hA 0 (by decide), hB, hA 1 (by decide), h.sum hR hk,
        ite_eq_right (by decide), mad_lo', mad_lo', mad_hi', AmmSym.shr_ofNat hs, ← BitVec.ofNat_add]
      congr 1
      simp only [AmmD52.step, hR, Nat.add_zero]
      rw [ite_eq_left (by omega_using [])]
      omega_using []
    | true =>
      simp only [ZT.eval, ite_true]
      rw [hb 1 (by decide), hA 0 (by decide), hB, hA 1 (by decide), h.sum hR hk,
        ite_eq_right (by decide), mad_lo', mad_hi', AmmSym.shr_ofNat hs, ← BitVec.ofNat_add, hl rfl]
      congr 1
      simp only [AmmD52.step, hR, Nat.add_zero, lo, Nat.zero_mod, Nat.mul_zero]
      rw [ite_eq_left (by omega_using [])]
  · -- the top role, which was role 0
    show (zBT l i last 0).eval s k = _
    rw [zBT, ite_eq_left rfl, ite_eq_right (by decide)]
    simp only [ZT.eval]
    rw [hB, show l.R - 1 = 5 by omega_using [hR], hA 5 (by decide), show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl, mad_hi']
    congr 1
    simp only [AmmD52.step, hR]
    rw [ite_eq_right (by omega_using []), ite_eq_left (by omega_using [])]
    omega_using []
  · -- the roles between
    rw [Nat.mod_eq_of_lt (by omega_using [hk']), zBT, ite_eq_right (by omega_using []), ite_eq_right (by omega_using [hk']),
      ite_eq_right (by omega_using [hk'])]
    simp only [ZT.eval]
    rw [hb (kk + 1) (by omega_using [hk']), hB, hA (kk + 1) (by omega_using [hk']), Nat.add_sub_cancel, hA kk (by omega_using [hkk]),
      ite_eq_right (by omega_using []), mad_lo', mad_hi']
    congr 1
    simp only [AmmD52.step, hR, Nat.add_assoc]
    rw [ite_eq_right (by omega_using [hk']), ite_eq_right (by omega_using [hk'])]
    omega_using []

/-- The second set's role `kk` after the step. -/
theorem ZIn.uT (h : ZIn l s i o st b w Bd) (hR : l.R = 6) (hL : l.L = 24) {kk : Nat} (hkk : kk < 6) {k : Nat}
    (hk : k < 8) :
    (zUT l i ((kk + 1) % 6)).eval s k =
      BitVec.ofNat 64 ((AmmD52.step l.L l.R (o (k / 4)) (st (k / 4)) (b (k / 4))).us (l.R * (k % 4) + kk)) := by
  have hp : k / 4 < 2 := by omega_using [hk]
  have hM : ∀ j, 1 ≤ j → j < 6 → qz s (vreg (znM l j)) k = _ := fun j h1 hj => h.con.m j h1 (by omega_using [hR, hj]) k hk
  have hu : ∀ j < 6, qz s (vreg (znU l j i)) k = _ := fun j hj => h.acc.us j (by omega_using [hR, hj]) k hk
  have hq := h.q hR hk
  rcases (by omega_using [hkk] : kk = 0 ∨ kk = 5 ∨ (1 ≤ kk ∧ kk ≤ 4)) with rfl | rfl | hk'
  · -- role 0, which was role 1
    show (zUT l i 1).eval s k = _
    rw [zUT, ite_eq_right (by decide), ite_eq_left rfl]
    simp only [ZT.eval]
    rw [hu 1 (by decide)]
    congr 1
    simp only [AmmD52.step, hR, Nat.add_zero]
    rw [ite_eq_left (by omega_using [])]
  · -- the top role, which was role 0
    show (zUT l i 0).eval s k = _
    rw [zUT, ite_eq_left rfl]
    simp only [ZT.eval]
    have hUp : qz s (vreg (znUq l ((i + 1) % 2))) k = _ := h.acc.up k hk
    have hm0 : qz s (vreg (znM l l.R)) k = _ := h.con.m0 k hk
    have hm1 : qz s (vreg (znM l (l.R + 1))) k = _ := h.con.m1 k hk
    have hK : qz s (vreg (znK l)) k = _ := h.con.k k hk
    rw [hq, hUp, hm0, hm1, hK, show l.R - 1 = 5 by omega_using [hR], hM 5 (by decide) (by decide)]
    by_cases h3 : k % 4 < 3
    · have e1 : sel4 0xF9 (k % 4) = k % 4 + 1 := by
        rcases (by omega_using [h3] : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2) with e | e | e <;> rw [e] <;> rfl
      have hs := h.sum_lt hp (l.R * (k % 4 + 1))
      rw [e1, h.sum hR (show 4 * (k / 4) + (k % 4 + 1) < 8 by omega_using [hk, h3]),
        show (4 * (k / 4) + (k % 4 + 1)) / 4 = k / 4 by omega_using [h3],
        show (4 * (k / 4) + (k % 4 + 1)) % 4 = k % 4 + 1 by omega_using [h3], ite_eq_left h3, AmmSym.and_mask hs,
        Nat.mod_eq_of_lt (show k % 4 + 1 < 4 by omega_using [h3]), mad_hi', mad_lo', mad_lo', mad_hi']
      congr 1
      have e2 : l.R * (k % 4) + 5 + 1 = l.R * (k % 4 + 1) := by rw [hR]; omega_using []
      simp only [AmmD52.step, pend]
      rw [ite_eq_right (by rw [hR]; omega_using []), ite_eq_left (by rw [hR]; omega_using []), ite_eq_left (by rw [hR, hL]; omega_using [h3]),
        ite_eq_left (by rw [hR]; omega_using []), e2, stepQ, lo_modr, hi_modr, ← h.acc.wq _ hp, hi_modr, lo_modr]
      omega_using []
    · have e3 : k % 4 = 3 := by omega_using [h3]
      have hz : ∀ x : BitVec 64, x &&& 0 = 0 := fun x => BitVec.and_zero
      rw [ite_eq_right h3, hz, e3, show (3 + 1) % 4 = 0 from rfl, Nat.mul_zero, Nat.zero_add,
        (h.ok _ hp).ms0, (h.ok _ hp).ms1, show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl, mad_hi', mad_lo',
        mad_lo', mad_hi', AmmD52.hi_zero, AmmD52.lo_zero, AmmD52.lo_zero]
      congr 1
      simp only [AmmD52.step]
      rw [ite_eq_right (by rw [hR] <;> omega_using []), ite_eq_left (by rw [hR] <;> omega),
        ite_eq_right (by rw [hR, hL] <;> omega_using []), stepQ, hi_modr]
  · -- the roles between
    rw [Nat.mod_eq_of_lt (by omega_using [hk']), zUT, ite_eq_right (by omega_using []), ite_eq_right (by omega_using [hk'])]
    simp only [ZT.eval]
    rw [hu (kk + 1) (by omega_using [hk']), hq, hM (kk + 1) (by omega_using []) (by omega_using [hk']), Nat.add_sub_cancel,
      hM kk (by omega_using [hk']) (by omega_using [hkk]), mad_lo', mad_hi']
    congr 1
    simp only [AmmD52.step, Nat.add_assoc]
    rw [ite_eq_right (by rw [hR]; omega_using [hk']), ite_eq_right (by rw [hR]; omega_using [hk']), stepQ, lo_modr, hi_modr]

end Eval

/-! ## The registers' terms -/

theorem expZ_B (hR : l.R = 6) {i kk : Nat} (_ : kk < 6) (last : Bool) :
    expZ l i last ((kk + (i + 1)) % l.R) = zBT l i last ((kk + 1) % 6) := by
  rw [expZ, ite_eq_left (by rw [hR]; exact Nat.mod_lt _ (by decide))]
  congr 1
  simp only [roleZ, hR]; omega_using []

theorem expZ_U (hR : l.R = 6) {i kk : Nat} (_ : kk < 6) (last : Bool) :
    expZ l i last (l.R + (kk + (i + 1)) % l.R) = zUT l i ((kk + 1) % 6) := by
  have := Nat.mod_lt (kk + (i + 1)) (show 0 < 6 by decide)
  rw [expZ, ite_eq_right (by omega_using []), ite_eq_left (by rw [hR]; omega_using [])]
  congr 1
  simp only [roleZ, hR]; omega_using []

theorem expZ_q (hR : l.R = 6) (i : Nat) (last : Bool) : expZ l i last (znUq l (i % 2)) = zQ l i := by
  have := Nat.mod_lt i (show 0 < 2 by decide)
  rw [expZ, ite_eq_right (by simp only [znUq]; omega), ite_eq_right (by simp only [znUq]; omega_using []), ite_eq_left rfl]

theorem expZ_bn (hR : l.R = 6) (i : Nat) : expZ l i false (znBq l ((i + 1) % 2)) = zBn l i := by
  have := Nat.mod_lt i (show 0 < 2 by decide)
  have := Nat.mod_lt (i + 1) (show 0 < 2 by decide)
  rw [expZ, ite_eq_right (by simp only [znBq]; omega), ite_eq_right (by simp only [znBq]; omega_using []),
    ite_eq_right (by simp only [znBq, znUq]; omega_using []), ite_eq_right (by simp only [znBq, znC]; omega_using []),
    ite_eq_right (by decide), ite_eq_left rfl]

/-- The registers of the operands' rows and of the mask stay. -/
theorem expZ_keep (hR : l.R = 6) (i : Nat) (last : Bool) {r : Nat} (h1 : 2 * l.R + 5 ≤ r) (h2 : r ≤ 4 * l.R + 6) :
    expZ l i last r = .reg r := by
  have := Nat.mod_lt i (show 0 < 2 by decide)
  have := Nat.mod_lt (i + 1) (show 0 < 2 by decide)
  rw [expZ, ite_eq_right (by omega), ite_eq_right (by omega_using [h1]), ite_eq_right (by simp only [znUq]; omega_using [h1]),
    ite_eq_right (by simp only [znC]; omega_using [h1])]
  cases last with
  | true => rfl
  | false =>
    rw [ite_eq_right (by decide), ite_eq_right (by simp only [znBq]; omega_using [h1]), ite_eq_right (by simp only [znT]; omega_using [h2])]

/-! ## The step -/

/-- What the vector code keeps. -/
structure ZKeep (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mxcsr : s'.mxcsr = s.mxcsr

theorem ZRel.keep {σ : ZSym} {s₀ s : State} (h : ZRel σ s₀ s) : ZKeep s₀ s := ⟨h.gpr, h.mem, h.rd, h.wr, h.mxcsr⟩

theorem ZKeep.trans {s₁ s₂ s₃ : State} (h₁ : ZKeep s₁ s₂) (h₂ : ZKeep s₂ s₃) : ZKeep s₁ s₃ :=
  ⟨h₂.gpr.trans h₁.gpr, h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.mxcsr.trans h₁.mxcsr⟩

theorem ZOk.L (hz : ZOk l) : l.L = 24 := by rw [hz]; rfl

/-- Step `i` of a block: `AmmD52.step`'s limbs in the roles of step `i + 1`,
with the low halves of row 0's products with the next limb `bn` (read at
`r9`, or 0 after the last step). -/
theorem zStep_ok (hz : ZOk l) {s : State} {i : Nat} (hi : i < l.R) {o : Nat → Ops} {st : Nat → St}
    {b w : Nat → Nat} {Bd : Nat} (h : ZIn l s i o st b w Bd) (last : Bool) {bn : Nat → Nat}
    (hb0 : last = false →
      s.mem.readW (s.gpr .r9 + BitVec.ofNat 64 (l.off (i + 1))) 64 = BitVec.ofNat 64 (bn 0))
    (hb1 : last = false →
      s.mem.readW (s.gpr .r9 + BitVec.ofNat 64 (l.D + l.off (i + 1))) 64 = BitVec.ofNat 64 (bn 1))
    (hl : last = true → ∀ p, bn p = 0) (hc : Ctx (limZ l) s) :
    WP isa (.block (zStep l i last)) s fun s' =>
      ZAcc l s' (i + 1) o (fun p => AmmD52.step l.L l.R (o p) (st p) (b p)) bn
        (fun p => lowS (o p) (st p) (b p) 0) (Bd + 2 ^ 56) ∧
      ZCon l s' o ∧ (last = false → ∀ k < 8, qz s' (zBq l ((i + 1) % 2)) k = BitVec.ofNat 64 (bn (k / 4))) ∧
      ZKeep s s' := by
  have hR := hz.R
  have hL := hz.L
  obtain ⟨σ, e, hσ⟩ := run_zStep hz hi last
  have hbn : last = false → ∀ k < 8, (zBn l i).eval s k = BitVec.ofNat 64 (bn (k / 4)) := fun h0 k hk =>
    zBn_eval (hb0 h0) (hb1 h0) hk
  have hm6 : ∀ x, x % l.R < 6 := fun x => by rw [hR]; exact Nat.mod_lt _ (by decide)
  have h2a := Nat.mod_lt i (show 0 < 2 by decide)
  have h2b := Nat.mod_lt (i + 1) (show 0 < 2 by decide)
  -- a register the step keeps
  have keep : ∀ r, 2 * l.R + 5 ≤ r → r ≤ 4 * l.R + 6 → ∀ s' : State, ZRel σ s s' → ∀ k < 8,
      qz s' (vreg r) k = qz s (vreg r) k := fun r h1 h2 s' hs k hk => by
    rw [hs.reg _ k hk, vi_vreg _ (by omega_using [hR, h2]), hσ _ (by omega_using [hR, h2]), expZ_keep hR i last h1 h2]; rfl
  refine WP.mono (zrun_ok hc (ZRel.init s) e) fun s' hs => ⟨⟨fun kk hkk k hk => ?_, fun kk hkk k hk => ?_,
    fun k hk => ?_, fun p _ => rfl, fun p hp => ?_⟩, ⟨fun kk hkk k hk => ?_, fun kk h1 hkk k hk => ?_,
      fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩, fun h0 k hk => ?_, hs.keep⟩
  · have := hm6 (kk + (i + 1))
    rw [show zB l kk (i + 1) = vreg ((kk + (i + 1)) % l.R) from rfl, hs.reg _ k hk, vi_vreg _ (by omega_using [this]),
      hσ _ (by omega_using [this]), expZ_B hR (by omega_using [hR, hkk]) last]
    exact h.bT hR hbn hl (by omega_using [hR, hkk]) hk
  · have := hm6 (kk + (i + 1))
    rw [show zU l kk (i + 1) = vreg (l.R + (kk + (i + 1)) % l.R) from rfl, hs.reg _ k hk, vi_vreg _ (by omega_using [hR, this]),
      hσ _ (by omega_using [hR, this]), expZ_U hR (by omega_using [hR, hkk]) last]
    exact h.uT hR hL (by omega_using [hR, hkk]) hk
  · rw [show (i + 1 + 1) % 2 = i % 2 by omega_using [], show zUq l (i % 2) = vreg (znUq l (i % 2)) from rfl,
      hs.reg _ k hk, vi_vreg _ (by simp only [znUq]; omega_using [hR]), hσ _ (by simp only [znUq]; omega_using [hR]), expZ_q hR]
    exact h.q hR hk
  · obtain ⟨h1, h2⟩ := AmmD52.step_lt (N := l.L) (R := l.R) (o := o p) (b := b p) h.hBd
      (fun j => (h.acc.bd p hp j).1) (fun j => (h.acc.bd p hp j).2)
    exact fun j => ⟨h1 j, h2 j⟩
  · rw [show zA l kk = vreg (2 * l.R + 5 + kk) from rfl, keep _ (by omega_using []) (by omega_using [hkk]) s' hs k hk]
    exact h.con.a kk hkk k hk
  · rw [show zM l kk = vreg (3 * l.R + 4 + kk) from rfl, keep _ (by omega_using [hi]) (by omega_using [hkk]) s' hs k hk]
    exact h.con.m kk h1 hkk k hk
  · rw [show zM l l.R = vreg (3 * l.R + 4 + l.R) from rfl, keep _ (by omega_using [hi]) (by omega_using []) s' hs k hk]
    exact h.con.m0 k hk
  · rw [show zM l (l.R + 1) = vreg (3 * l.R + 4 + (l.R + 1)) from rfl, keep _ (by omega_using []) (by omega_using []) s' hs k hk]
    exact h.con.m1 k hk
  · rw [show zK l = vreg (4 * l.R + 6) from rfl, keep _ (by omega_using []) (by omega_using []) s' hs k hk]
    exact h.con.k k hk
  · subst h0
    rw [show zBq l ((i + 1) % 2) = vreg (znBq l ((i + 1) % 2)) from rfl, hs.reg _ k hk,
      vi_vreg _ (by simp only [znBq]; omega_using [hR]), hσ _ (by simp only [znBq]; omega_using [hR]), expZ_bn hR]
    exact hbn rfl k hk

end VG.Proof.Bignum.X86_64.Ifma
