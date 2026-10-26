module
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.SeedSearch
public import VerifiedGarbage.Proof.Dsa.Generation.SeedResult
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedOutcome
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hashes

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedPrime
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedGeneratorFinish
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSuccess
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import Mathlib.Algebra.Group.Nat.Defs

/-! # Bounded p search, generator search, and final validation form one native continuation -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout
open VG.Proof.MillerRabin.X86_64


variable {checkName : String}

theorem seedPrimeFinish_ok (H : GenerationHashes) (M : Mont) (Sq : MontS) (K : Kernel)
    {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (seed : GenerationTape p.geo) (hlen : seed.bytes.length = p.geo.qLen)
    (hseed : GenerationTapeMemory seed s) (h1 : W 1 = seed.ptr)
    (hq : Spec.Rsa.bytesAt s.mem (off p.geo.B q) p.geo.qLen =
      Spec.Dsa.encodeBE p.geo.qLen (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes))
    {used : Nat} (h16 : W 16 = BitVec.ofNat 64 used) (hu : used ≤ p.rand.bytes.length) :
    WP isa (.seq (Impl.Dsa.X86_64.Generation.primeSearch H.sha1 H.sha256 M.mm K.run p.geo.pLen p.geo.qLen)
      (Impl.Dsa.X86_64.Generation.onSuccess
        (.seq (Impl.Dsa.X86_64.Generation.generatorSearch Sq.mm M.mm p.geo.pLen)
          (Impl.Dsa.X86_64.Generation.onSuccess (Impl.Dsa.X86_64.Generation.finishDomain (checkName := checkName) Sq.mm M.mm p.geo.pLen p.geo.qLen))))) s
      (SeedFinished p W (VG.Proof.Dsa.Generation.primeResult (8 * p.geo.pLen) (8 * p.geo.qLen)
        (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) seed.bytes
        ((Spec.Dsa.generationChunks p.geo.pLen p.hs.bytes).map Spec.Dsa.decodeBE) (p.rand.bytes.drop used)) s) := by
  have qfit : Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes < 256 ^ p.geo.qLen := by
    have shape := VG.Proof.Dsa.Generation.qCandidate_shape
      (by rcases p.geo.qWidth with hh | hh <;> omega : 2 ≤ 8 * p.geo.qLen) seed.bytes
    simpa only [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul] using shape.2.2
  refine WP.seq (WP.mono (seedPrime_ok H M K h seed hlen hseed h1 hq h16 hu)
    fun u ⟨Wu, usedu, huu, mu, u16, slots, bqu, result, fu, ru, wu⟩ => ?_)
  rcases result with ⟨h19, hr⟩ | ⟨h19, value, hr, domain, bp, be⟩ | ⟨h19, hr⟩
  · apply onSuccess_generation_ok mu
    · intro _ _ _ _ hs
      have impossible : (0 : BitVec 64) = 1 := h19.symm.trans hs
      exact False.elim (by cases impossible)
    · intro t mt hm kt _
      refine ⟨Wu, usedu, mt, huu, u16, slots, Or.inl ⟨h19, ?_⟩, ?_, kt.2.1.trans ru, kt.2.2.trans wu⟩
      · simp only [VG.Proof.Dsa.Generation.primeResult, hr]
      · rw [hm]; exact fu
  · apply onSuccess_generation_ok mu
    · intro v mv hm kv _
      have bv : Spec.Rsa.bytesAt v.mem (off p.geo.B VG.Impl.Dsa.Generation.Layout.p) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen value := hm ▸ bp
      have ev : Spec.Rsa.bytesAt v.mem (off p.geo.B exponent) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen
          ((value - 1) / Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) := hm ▸ be
      have qv : Spec.Rsa.bytesAt v.mem (off p.geo.B q) p.geo.qLen = Spec.Dsa.encodeBE p.geo.qLen
          (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) := hm ▸ bqu
      have call := seedGeneratorFinish_ok (checkName := checkName) M Sq mv value (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes)
        domain qfit bv ev qv u16 huu
      have expected : VG.Proof.Dsa.Generation.primeResult (8 * p.geo.pLen) (8 * p.geo.qLen)
          (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) seed.bytes
          ((Spec.Dsa.generationChunks p.geo.pLen p.hs.bytes).map Spec.Dsa.decodeBE) (p.rand.bytes.drop used) =
          VG.Proof.Dsa.Generation.generatorResult value (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes)
          ((Spec.Dsa.generationChunks p.geo.pLen p.hs.bytes).map Spec.Dsa.decodeBE) (p.rand.bytes.drop usedu) := by
        simp only [VG.Proof.Dsa.Generation.primeResult, hr]
      rw [expected]
      refine WP.mono call fun t ht => ?_
      exact ht.prepend slots (by rw [hm]; exact fu) (kv.2.1.trans ru) (kv.2.2.trans wu)
    · intro _ _ _ _ hn
      exact False.elim (hn h19)
  · apply onSuccess_generation_ok mu
    · intro _ _ _ _ hs
      have impossible : (3 : BitVec 64) = 1 := h19.symm.trans hs
      exact False.elim (by cases impossible)
    · intro t mt hm kt _
      refine ⟨Wu, usedu, mt, huu, u16, slots, Or.inr (Or.inl ⟨h19, ?_⟩), ?_, kt.2.1.trans ru, kt.2.2.trans wu⟩
      · simp only [VG.Proof.Dsa.Generation.primeResult, hr]
      · rw [hm]; exact fu

end VG.Proof.Dsa.X86_64.Generation
