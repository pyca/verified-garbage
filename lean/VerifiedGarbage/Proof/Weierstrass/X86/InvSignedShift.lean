import VerifiedGarbage.Proof.Weierstrass.X86.InvShift
import VerifiedGarbage.Proof.Weierstrass.X86.InvRedMath

/-! # Exact division of a signed matrix row by the batch scale -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Inv
  VG.Proof.Mont.X86 VG.Proof.Mont

theorem shrSigned_ok {s : State} {base : Addr} {size dst src n : Nat}
    (hs : Scr s base size) (hn : 1 ≤ n) (ha : src + 4 * n ≤ size) (hd : dst + 4 * n ≤ size)
    (sep : dst + 4 * n ≤ src ∨ src + 4 * n ≤ dst) {y z : Int}
    (hy : (val32 s.mem base src n : Int) % ((2 ^ (32 * n) : Nat) : Int) =
      y % ((2 ^ (32 * n) : Nat) : Int))
    (hy1 : -((2 ^ (32 * (n - 1)) * 2 ^ 31 : Nat) : Int) ≤ y)
    (hy2 : y < ((2 ^ (32 * (n - 1)) * 2 ^ 31 : Nat) : Int)) (hz : y = 2 ^ 30 * z) :
    WP isa (.block (shr30 dst src n)) s fun u =>
      (val32 u.mem base dst n : Int) % ((2 ^ (32 * n) : Nat) : Int) =
        z % ((2 ^ (32 * n) : Nat) : Int) ∧
      Keeps [.eax, .ebx, .ecx] s u ∧ Outside base dst (4 * n) s.mem u.mem := by
  refine WP.mono (shr30_ok hs hn ha hd sep) fun u ⟨V, K, O⟩ => ⟨?_, K, O⟩
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hy1 hy2 ⊢
  have Q : 2 ^ (32 * (j + 1)) = 2 * (2 ^ (32 * j) * 2 ^ 31) := by
    rw [pow32_succ, show (2 : Nat) ^ 32 = 2 * 2 ^ 31 from rfl]
    ring
  simp only [sext32, Nat.add_sub_cancel, sign32, Q] at V
  rw [Q] at hy ⊢
  exact Divstep.W32.shr_nat (c := 2 ^ 30) (B := 2 ^ 32) rfl rfl
    (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _))
    (by have := val32_lt s.mem base src (j + 1); rw [Q] at this; exact this) hy hy1 hy2 hz V

end VG.Proof.Weierstrass.X86.Inv
