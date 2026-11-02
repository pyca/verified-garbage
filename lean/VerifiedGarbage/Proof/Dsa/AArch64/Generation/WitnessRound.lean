module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.SampleRound
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.WitnessMont
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Kernel
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.KernelFrame
import VerifiedGarbage.Proof.Framework.Omega

/-! The chosen witness is tested by the shared callable windowed round. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 VG.Proof.MillerRabin.AArch64

def witnessRoundRanges (w : Nat) : List (Nat × Nat) := witnessMontRanges w ++ Caller.callRanges w

theorem witnessRound_ok (M : Mont) (K : Kernel) {s : State} {B : Addr} {Z w N b : Nat}
    (h : ModulusReady s B Z w N) (h4 : 4 ≤ w) (h128 : w ≤ 128)
    (hEZ : slot w aE + 8 * (w + 2) ≤ Z) (hodd : N % 2 = 1) (h3 : 3 ≤ N)
    (hx : wv s.mem B (slot w aX) w = b) :
    WP isa (Impl.Dsa.AArch64.Generation.witnessRound M.mm K.run) s fun t =>
      ModulusReady t B Z w N ∧ word t.mem B (8 * kFlag) = mask (Proof.MillerRabin.Round.round N b) ∧
      Frm B (witnessRoundRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  unfold Impl.Dsa.AArch64.Generation.witnessRound
  refine WP.seq (WP.mono (witnessMont_ok M h hEZ hodd (by omega) hx)
    fun u ⟨hu, hxu, fu, ku⟩ => ?_)
  have hcu : MrCtx u B Z w N (wv u.mem B (slot w aB) w) :=
    ⟨hu.ws, hu.inverse, hu.modulus, rfl, hu.r1, hu.rm1⟩
  refine WP.mono (K.ok (b := b) hcu hu.exponent h4 h128 hEZ hodd h3
    (by simpa only [Nat.mod_mul_mod] using hxu))
    fun t ⟨_, _, hflag, ft, kt⟩ => ?_
  exact ⟨kernel_preserves_modulus hu hEZ ft kt, hflag,
    (fu.mono fun r hr => List.mem_append_left _ hr).trans
      (ft.mono fun r hr => List.mem_append_right _ hr), (ku.trans kt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64.Generation
