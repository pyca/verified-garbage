module

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Load
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Prepared
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Load
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.Framework.Omega

/-! # Preserve the prepared Miller–Rabin modulus when loading a DSA witness -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Proof.Ffdh.X86_64.ParameterCandidate

theorem loadWitness_ok {s : State} {B p : Addr} {Z w N sp sl : Nat} {mi : BitVec 64} {bs : List Byte}
    (h : ModulusReady s B Z w mi N) (hd : MrDims B Z w)
    (hsp : sp < 32) (hsl : sl < 32)
    (hp : word s.mem B (8 * sp) = p) (hl : word s.mem B (8 * sl) = BitVec.ofNat 64 bs.length)
    (hsrc : Src s B Z p bs) (hk1 : 1 ≤ bs.length) (hk31 : bs.length < 2 ^ 31)
    (hkw : (bs.length + 7) / 8 ≤ w) :
    WP isa (Impl.Dsa.X86_64.Generation.loadPadded aXm sp sl) s fun t =>
      ModulusReady t B Z w mi N ∧ wv t.mem B (slot w aXm) w = Spec.Rsa.os2ip bs ∧
      Frm B [(slot w aXm, 8 * (w + 2))] s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (loadPadded_ok h.good hd.z (by have := hd.w4; omega)
    (by have := hd.w128; omega) (by decide : aXm < 8) hsp hsl hp hl hsrc hk1 hk31 hkw)
    fun t ⟨hg, hv, ho, hk⟩ => ?_
  have hf : Frm B [(slot w aXm, 8 * (w + 2))] s.mem t.mem := Frm.of_outside ho (by simp)
  exact ⟨h.of_frm hd hf hk hg.rdi (by rng_disj) (by rng_disj) (by rng_disj), hv, hf, hk⟩

end VG.Proof.Dsa.X86_64.Generation
