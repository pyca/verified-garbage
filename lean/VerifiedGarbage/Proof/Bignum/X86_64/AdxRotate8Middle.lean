import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8MiddleInv

/-! The loop over all higher modulus blocks, including the one-block case. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

theorem middles_ok {s : State} {B : Addr} {Z w e n : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hH : Hdr s.mem B w mi) (hdi : s.gpr .rdi = B)
    (hc : s.gpr .rcx = off B e) (hp : s.gpr .rbp = off B (slot w aN + 64))
    (ho : s.gpr .rsi = off B (e + 64)) (hz : s.zf = some (decide (n = 0)))
    (hZ : slot w 8 ≤ Z) (hw : w = 8 * (n + 1))
    (he : hdrBytes + 16 ≤ e) (heZ : e + 8 * (w + 8) ≤ Z)
    (hsep : slot w aN + 8 * w ≤ e - 8) :
    WP isa (.ite .ne (.loop AdxRotate8.middle .ne) (.block [])) s (MiddleInv s B Z w e n mi) := by
  have h0 : MiddleInv s B Z w e 0 mi s := ⟨hs, hH, hdi, hc,
    by simpa only [Nat.zero_add, Nat.mul_one] using hp,
    by simpa only [Nat.zero_add, Nat.mul_one] using ho,
    Keep.refl _ _, BlockOut.refl _ _ _ _ _, by
      simp only [wv, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero]⟩
  by_cases hn : n = 0
  · refine WP.ite false (by simp [eval, hz, hn]) (by simp) (fun _ => WP.block_nil ?_)
    rw [hn]; exact h0
  · refine WP.ite true (by simp [eval, hz, hn]) (fun _ => ?_) (by simp)
    exact wp_upto (a := 0) (N := n) (by omega) (MiddleInv s B Z w e · mi)
      (fun _ _ hi _ h => middleStep_ok hZ hw hi he heZ hsep h) (fun _ h => h) h0
end VG.Proof.Bignum.X86_64.AdxRotate8
