module

public import VerifiedGarbage.Proof.Rsa.Arm.Inv.Geo
public import VerifiedGarbage.Proof.Rsa.Divstep.Inv30Def
public import VerifiedGarbage.Impl.Rsa.Arm.Inverse
public import VerifiedGarbage.Proof.Rsa.Arm.KeyOps

/-! # `inverse` on ARMv7: what callers use

`InvLaw`: for `a` in array 0 and `m` in array `aM`, each `k` words (`k` in
`r9`), for an odd `m > 1`, `inverse` leaves `gcd(a, m)` in array 1 and
`inv30 k a m` in array 3, each zero-filled to the stride's `W` words, and
`x = inv30 k a m` is below `m` with `x a ≡ gcd(a, m) (mod m)`. Its proofs
(`InvLoop.lean`) import the algebra of the divsteps' convergence, so callers
take it as an instance, which the registrations supply, rather than import
them. `inverse_ok` is the case `k = W`.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Keys
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm VG.Proof.Rsa.Arm.Inv

/-- The arrays and header words `inverse` may write. -/
abbrev invArrs : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, aT1, aT2, aT3, aT4]
abbrev invSlots : List Nat := [sOdd, sB, sC]

class InvLaw : Prop where
  inverseK_ok {σ : State} {B : BitVec 32} {Z W k N : Nat} (h : Gk σ B Z W k N) (hN15 : 15 ≤ N)
      (hN : N ≤ 256) :
    WP isa VG.Impl.Rsa.Arm.Keys.inverse σ fun t => Gk t B Z W k N ∧ Keep B W invArrs invSlots σ.mem t.mem ∧
      Rest (.r6 :: opRegs) σ t ∧
      (nk σ.mem B W aM k % 2 = 1 → 1 < nk σ.mem B W aM k →
        nk t.mem B W 1 W = Nat.gcd (nk σ.mem B W 0 k) (nk σ.mem B W aM k) ∧
        nk t.mem B W 3 W = VG.Proof.Rsa.Divstep.inv30 k (nk σ.mem B W 0 k) (nk σ.mem B W aM k))
  inv30_spec {n a m : Nat} (hm : m % 2 = 1) (h1 : 1 < m) (ha : a < 2 ^ (32 * n)) (hmn : m < 2 ^ (32 * n)) :
    (m : Int) ∣ (VG.Proof.Rsa.Divstep.inv30 n a m : Int) * a - Nat.gcd a m ∧
      VG.Proof.Rsa.Divstep.inv30 n a m < m

/-- The bank at `j`: `(u, v, x₁, x₂)`. -/
def bank (m : Mem) (B : BitVec 32) (w j : Nat) : Nat × Nat × Nat × Nat :=
  (num m B w j, num m B w (j + 1), num m B w (j + 2), num m B w (j + 3))

theorem inverse_ok [InvLaw] {s : State} {B : BitVec 32} {Z w N : Nat} (h : Ws s B Z w N) (hN15 : 15 ≤ N) (hN : N ≤ 256) :
    WP isa VG.Impl.Rsa.Arm.Keys.inverse s fun t => Ws t B Z w N ∧ Keep B w invArrs invSlots s.mem t.mem ∧
      Rest (.r6 :: opRegs) s t ∧
      (num s.mem B w aNM + num s.mem B w aM = 2 ^ (32 * w) → num s.mem B w aZero = 0 →
        num s.mem B w aM % 2 = 1 → 1 < num s.mem B w aM →
        bank s.mem B w 0 = (num s.mem B w 0, num s.mem B w aM, 1, 0) →
        num t.mem B w 1 = Nat.gcd (num s.mem B w 0) (num s.mem B w aM) ∧
        (num s.mem B w aM : Int) ∣ (num t.mem B w 3 : Int) * num s.mem B w 0 - num t.mem B w 1 ∧
        num t.mem B w 3 < num s.mem B w aM) := by
  have g : Gk s B Z w w N := ⟨h.nowrap, h.writable, h.fits, h.wpos, le_refl _, h.wle, h.r7, h.r8, h.r9⟩
  refine WP.mono (InvLaw.inverseK_ok g hN15 hN) fun t ⟨gt, kt, rt, v⟩ =>
    ⟨⟨gt.nowrap, gt.writable, gt.fits, gt.kpos, gt.wle, gt.r7, gt.r8, gt.r9⟩, kt, rt,
      fun _ _ hmo hm1 _ => ?_⟩
  obtain ⟨v1, v3⟩ := v hmo hm1
  obtain ⟨d, l⟩ := InvLaw.inv30_spec hmo hm1 (val32_lt _ _ _ _) (val32_lt _ _ _ _)
    (n := w) (a := num s.mem B w 0) (m := num s.mem B w aM)
  refine ⟨v1, ?_, by change nk t.mem B w 3 w < _; rw [v3]; exact l⟩
  change _ ∣ (nk t.mem B w 3 w : Int) * _ - nk t.mem B w 1 w
  rw [v1, v3]
  exact d

end VG.Proof.Rsa.Arm.Keys
