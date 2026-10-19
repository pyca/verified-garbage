module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedSubgroup
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedPrimeFinish
import VerifiedGarbage.Proof.Framework.Omega

/-! # A complete native seed attempt implements all parameter-generation decisions -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout
open VG.Proof.MillerRabin.X86_64

theorem seedAttempt_ok (H : GenerationHashes) (M : Mont) (Sq : MontS) (K : Kernel)
    {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (seed : GenerationTape p.geo) (hlen : seed.bytes.length = p.geo.qLen)
    (hseed : GenerationTapeMemory seed s) (h1 : W 1 = seed.ptr)
    {used : Nat} (h16 : W 16 = BitVec.ofNat 64 used) (hu : used ≤ p.rand.bytes.length) :
    WP isa (Impl.Dsa.X86_64.Generation.seedAttempt H.sha1 H.sha256 Sq.mm M.mm K.run p.geo.pLen p.geo.qLen) s
      (SeedFinished p W (VG.Proof.Dsa.Generation.seedResult (8 * p.geo.pLen) (8 * p.geo.qLen) seed.bytes
        ((Spec.Dsa.generationChunks p.geo.pLen p.hs.bytes).map Spec.Dsa.decodeBE) (p.rand.bytes.drop used)) s) := by
  unfold Impl.Dsa.X86_64.Generation.seedAttempt
  refine WP.seq (WP.mono (seedSubgroup_ok H M K h seed hlen hseed h1 h16 hu)
    fun u ⟨usedu, status, huu, mu, bqu, fail, result, fu, ru, wu⟩ => ?_)
  let Wu := upd (upd (seedWords W p.geo.qLen) 16 (BitVec.ofNat 64 usedu)) 19 status
  have u16 : Wu 16 = BitVec.ofNat 64 usedu := by simp [Wu, upd]
  have u19 : Wu 19 = status := by simp [Wu, upd]
  have slots : ∀ k ∈ searchSlots, Wu k = W k := by
    intro k hk
    simp only [searchSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | rfl
      | simpa [Wu, seedWords, upd] using ((h.slots 28 (by simp [generationSlots])).trans p.hashLenSlot).symm
  have u1 : Wu 1 = seed.ptr := (slots 1 (by simp [searchSlots])).trans h1
  have seedu := hseed.frame fu ru wu
  cases qr : Spec.Dsa.probablePrime (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) (p.rand.bytes.drop used) with
  | none =>
    have hs : Wu 19 = 0 := u19.trans (fail qr)
    apply onSuccess_generation_ok mu
    · intro _ _ _ _ accepted
      have impossible : (0 : BitVec 64) = 1 := hs.symm.trans accepted
      exact False.elim (by cases impossible)
    · intro t mt hm kt _
      refine ⟨Wu, usedu, mt, huu, u16, slots, Or.inl ⟨hs, ?_⟩, ?_, kt.2.1.trans ru, kt.2.2.trans wu⟩
      · simp only [VG.Proof.Dsa.Generation.seedResult, qr]
      · rw [hm]; exact fu
  | some pair =>
    rcases pair with ⟨accepted, rest⟩
    obtain ⟨hs, cursor⟩ := result accepted rest qr
    have suffix : p.rand.bytes.drop usedu = rest := by
      rw [cursor]
      exact VG.Proof.Dsa.Generation.probablePrime_cursor qr
    cases accepted with
    | false =>
      have hstatus : Wu 19 = 3 := u19.trans hs
      apply onSuccess_generation_ok mu
      · intro _ _ _ _ accepted
        have impossible : (3 : BitVec 64) = 1 := hstatus.symm.trans accepted
        exact False.elim (by cases impossible)
      · intro t mt hm kt _
        refine ⟨Wu, usedu, mt, huu, u16, slots, Or.inr (Or.inl ⟨hstatus, ?_⟩), ?_, kt.2.1.trans ru, kt.2.2.trans wu⟩
        · simp only [VG.Proof.Dsa.Generation.seedResult, qr, suffix]
        · rw [hm]; exact fu
    | true =>
      have hstatus : Wu 19 = 1 := u19.trans hs
      apply onSuccess_generation_ok mu
      · intro v mv hm kv _
        have seedv := seedu.frame (p := p) (by rw [hm]; exact Frame.refl _ _) kv.2.1 kv.2.2
        have qv : Spec.Rsa.bytesAt v.mem (off p.geo.B q) p.geo.qLen =
            Spec.Dsa.encodeBE p.geo.qLen (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) := hm ▸ bqu
        have call := seedPrimeFinish_ok H M Sq K mv seed hlen seedv u1 qv u16 huu
        have expected : VG.Proof.Dsa.Generation.seedResult (8 * p.geo.pLen) (8 * p.geo.qLen) seed.bytes
            ((Spec.Dsa.generationChunks p.geo.pLen p.hs.bytes).map Spec.Dsa.decodeBE) (p.rand.bytes.drop used) =
            VG.Proof.Dsa.Generation.primeResult (8 * p.geo.pLen) (8 * p.geo.qLen)
            (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) seed.bytes
            ((Spec.Dsa.generationChunks p.geo.pLen p.hs.bytes).map Spec.Dsa.decodeBE) (p.rand.bytes.drop usedu) := by
          simp only [VG.Proof.Dsa.Generation.seedResult, qr, suffix]
        rw [expected]
        refine WP.mono call fun t ht => ?_
        exact ht.prepend slots (by rw [hm]; exact fu) (kv.2.1.trans ru) (kv.2.2.trans wu)
      · intro _ _ _ _ hn
        exact False.elim (hn hstatus)

end VG.Proof.Dsa.X86_64.Generation
