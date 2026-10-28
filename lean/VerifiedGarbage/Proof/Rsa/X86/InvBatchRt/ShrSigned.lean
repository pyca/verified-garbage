module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Shr
import VerifiedGarbage.Proof.Weierstrass.X86.InvRedMath
import VerifiedGarbage.Proof.Divstep.Tc32Words
import VerifiedGarbage.Proof.Framework.Omega

/-! # The shift right by 30 of a signed value it divides

`shrSigned_ok`: `shr30_ok` for a value divisible by `2 ^ 30`, as the batches' rows give it.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Weierstrass.X86.Inv (sext32 shr_word32 wordClob)

variable {L : Lay} {B : Addr} {Z len N : Nat}

/-- `shr30` of a signed value divisible by `2 ^ 30`. -/
theorem shrSigned_ok {s : State} (h : Bx L s B Z len N) {dst src : Ref} (hdh : dst.half = 0)
    (hev : nw len % 2 = 0) (hsz : rv (kw len) src + 4 * (nw len + 1) ≤ Z)
    (hdz : rv (kw len) dst + 4 * (nw len + 1) ≤ Z)
    (sep : rv (kw len) dst + 4 * (nw len + 1) ≤ rv (kw len) src ∨ rv (kw len) src + 4 * (nw len + 1) ≤ rv (kw len) dst)
    {y z : Int}
    (hy : (val32 s.mem B (rv (kw len) src) (nw len + 1) : Int) % ((2 ^ (32 * (nw len + 1)) : Nat) : Int) =
      y % ((2 ^ (32 * (nw len + 1)) : Nat) : Int))
    (hy1 : -((2 ^ (32 * nw len) * 2 ^ 31 : Nat) : Int) ≤ y)
    (hy2 : y < ((2 ^ (32 * nw len) * 2 ^ 31 : Nat) : Int)) (hz : y = 2 ^ 30 * z) :
    WP isa (shr30 L dst src) s fun u =>
      Bx L u B Z len N ∧
      (val32 u.mem B (rv (kw len) dst) (nw len + 1) : Int) % ((2 ^ (32 * (nw len + 1)) : Nat) : Int) =
        z % ((2 ^ (32 * (nw len + 1)) : Nat) : Int) ∧
      Keeps wordClob s u ∧ Outside B (rv (kw len) dst) (4 * (nw len + 1)) s.mem u.mem := by
  refine WP.mono (shr30_ok h hdh hev hsz hdz sep) fun u ⟨Bu, V, K, O⟩ => ⟨Bu, ?_, K, O⟩
  have Q : 2 ^ (32 * (nw len + 1)) = 2 * (2 ^ (32 * nw len) * 2 ^ 31) := by
    rw [pow32_succ]; omega
  simp only [sext32, Nat.add_sub_cancel, VG.Proof.Weierstrass.X86.Inv.sign32, Q] at V
  rw [Q] at hy ⊢
  exact Divstep.W32.shr_nat (c := 2 ^ 30) (B := 2 ^ 32) rfl rfl
    (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _))
    (by have := val32_lt s.mem B (rv (kw len) src) (nw len + 1); rw [Q] at this; exact this) hy hy1 hy2 hz V

end VG.Proof.Rsa.X86.InvBatchRt
