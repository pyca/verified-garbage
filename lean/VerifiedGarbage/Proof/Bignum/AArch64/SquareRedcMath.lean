module

public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.TCB.AArch64.Isa
import VerifiedGarbage.Proof.Bignum.AArch64.MulAdd

/-! Low-word cancellation and pending high carries for REDC. -/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.Square
open VG VG.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64

def redcU (x inv : BitVec 64) : BitVec 64 := BitVec.ofNat 64 (x.toNat*inv.toNat)

theorem wv_low (m : Mem) (B : Addr) (d n : Nat) :
    wv m B d (n+1) = (word m B d).toNat + 2 ^ 64*wv m B (d+8) n := by
  rw [Nat.add_comm n 1, wv_add]; simp [wv]

theorem wv_mod_word (m : Mem) (B : Addr) (e : Nat) {w : Nat} (hw : 1 ≤ w) :
    wv m B e w % 2 ^ 64 = (word m B e).toNat := by
  rw [show w = (w - 1) + 1 by omega, wv_low]
  simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod, Nat.add_zero,
    Nat.mod_eq_of_lt (word m B e).isLt]

/-- A number split just before and just after its word `w`. -/
theorem wv_at_word (m : Mem) (B : Addr) (e w n : Nat) (hw : w < n) :
    wv m B e n = wv m B e w + 2 ^ (64 * w) *
      ((word m B (e + 8 * w)).toNat + 2 ^ 64 * wv m B (e + 8 * w + 8) (n - (w + 1))) := by
  have hn : n = w + ((n - (w + 1)) + 1) := by omega
  have h := wv_add m B e w ((n - (w + 1)) + 1)
  rw [← hn, wv_low] at h
  exact h

/-- The multiply-add cancels its low word. -/
theorem redc_low {s t : State} {B : Addr} {e eN w C : Nat} {minv : BitVec 64} (hw : 1 ≤ w)
    (hinv : ((word s.mem B eN).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hv : wv t.mem B e w + 2 ^ (64 * w) * C = wv s.mem B e w +
      (redcU (word s.mem B e) minv).toNat * wv s.mem B eN w) : word t.mem B e = 0 := by
  have hR : 2 ^ (64 * w) % 2 ^ 64 = 0 := by
    rw [show 64 * w = 64 + 64 * (w - 1) by omega, Nat.pow_add]
    simp only [Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod]
  apply BitVec.eq_of_toNat_eq
  change (word t.mem B e).toNat = 0
  rw [← wv_mod_word _ _ _ hw]
  calc
    wv t.mem B e w % 2 ^ 64 = (wv t.mem B e w + 2 ^ (64 * w) * C) % 2 ^ 64 := by
      simp only [Nat.add_mod, Nat.mul_mod, hR, Nat.zero_mul, Nat.zero_mod, Nat.add_zero, Nat.mod_mod]
    _ = (wv s.mem B e w + (redcU (word s.mem B e) minv).toNat * wv s.mem B eN w) % 2 ^ 64 := congrArg (· % 2 ^ 64) hv
    _ = ((word s.mem B e).toNat + (redcU (word s.mem B e) minv).toNat * (word s.mem B eN).toNat) % 2 ^ 64 := by
      simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, wv_mod_word _ _ _ hw,
        Nat.mod_eq_of_lt (word s.mem B e).isLt, Nat.mod_eq_of_lt (word s.mem B eN).isLt]
    _ = 0 := by
      rw [Nat.add_comm]
      exact mont_low _ _ _ hinv

theorem carry2_nat (a b : Bool) :
    (BitVec.ofNat 64 a.toNat + BitVec.ofNat 64 b.toNat).toNat = a.toNat+b.toNat := by
  have ha := Bool.toNat_le a; have hb := Bool.toNat_le b
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega_arith

/-- Two additions retain their complete sum in one low word and a high carry. -/
theorem add3_val (x c p : BitVec 64) :
    let b0 := decide (2 ^ 64 ≤ x.toNat+c.toNat)
    let b1 := decide (2 ^ 64 ≤ (x+c).toNat+p.toNat)
    (x+c+p).toNat + 2 ^ 64*(b0.toNat+b1.toNat) = x.toNat+c.toNat+p.toNat := by
  dsimp only
  have h0 := adc_toNat x c false
  have h1 := adc_toNat (x+c) p false
  change (x+c+BitVec.ofNat 64 0).toNat + 2 ^ 64*
    (decide (2 ^ 64 ≤ x.toNat+c.toNat)).toNat = x.toNat+c.toNat at h0
  change (x+c+p+BitVec.ofNat 64 0).toNat + 2 ^ 64*
    (decide (2 ^ 64 ≤ (x+c).toNat+p.toNat)).toNat = (x+c).toNat+p.toNat at h1
  rw [add_ofNat0] at h0 h1
  omega_arith

end VG.Proof.Bignum.AArch64.Square
