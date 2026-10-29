module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hashes
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Context
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedArguments
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeTest

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSeed
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SubgroupState
import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Subgroup
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.QBuild
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SourceFrame
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import Mathlib.Algebra.Group.Nat.Defs
/-! # Complete first phase of a seed attempt, retaining every retry input -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/Subgroup.lean`, which only this module imported.
section

/-! # Complete native subgroup-candidate generation and primality testing -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.RsaOaep.X86_64 VG.Proof.RsaOaep.X86_64
open VG.Proof.MillerRabin.X86_64 VG.Impl.RsaKeyGen.X86_64.Candidate

theorem subgroup_ok {G1 G256 : Impl.Pbkdf2.Md.X86_64.Stream}
    (h1 : Pbkdf2.Md.X86_64.Calls.StreamOK G1) (h256 : Pbkdf2.Md.X86_64.Calls.StreamOK G256)
    (he1 : ∀ x, Spec.Mgf1.sha1.hash x = h1.SH.H.hash x)
    (he256 : ∀ x, Spec.Mgf1.sha256.hash x = h256.SH.H.hash x)
    (hs1 : ∀ x, (Spec.Mgf1.sha1.hash x).length = G1.D)
    (hs256 : ∀ x, (Spec.Mgf1.sha256.hash x).length = G256.D)
    (hd1 : G1.D = 20) (hd256 : G256.D = 32) (T : PrimeTest)
    {p : SubgroupPlan} {used : Nat} {s : State} (h : SubgroupState p used s) :
    WP isa (Impl.Dsa.X86_64.Generation.subgroup G1 G256 T.run p.prime.len) s fun t =>
      let res := Spec.Dsa.probablePrime p.prime.N (p.prime.rand.drop used)
      ∃ used' status V', used' ≤ p.prime.rand.length ∧
        Lay t p.prime.sp p.hash ∧
        Rep t.mem p.prime.sp p.hash V' (upd (upd p.W 16 (BitVec.ofNat 64 used')) 19 status) ∧
        Spec.Rsa.bytesAt t.mem p.output p.prime.len = Spec.Dsa.encodeBE p.prime.len p.prime.N ∧
        (res = none → status = BitVec.ofNat 64 0) ∧
        (∀ b rest, res = some (b, rest) → status = BitVec.ofNat 64 (if b then 1 else 3) ∧
          used' = p.prime.rand.length - rest.length) ∧
        Frame p.changed s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨V, R⟩ := h.rep
  have plen : p.prime.len ≤ 32 := by rcases p.width with hh | hh <;> omega
  unfold Impl.Dsa.X86_64.Generation.subgroup
  refine WP.seq (WP.mono (qCandidate_ok h1 h256 he1 he256 hs1 hs256 hd1 hd256 p.width
    h.layout R h.label p.outputSlot h.outputWrite (fun i hi j hj => ?_) p.outputHash)
    fun u ⟨uq, urd, uwr, _, fu, Lu, Vu, Ru⟩ => ?_)
  · have he := p.outputHash.scratch j hj (oDig + i) (by unfold oDig oRsa; omega)
    simpa only [off_off] using Ne.symm he
  have ubytes : Spec.Rsa.bytesAt u.mem p.output p.prime.len = Spec.Dsa.encodeBE p.prime.len p.prime.N := by
    rw [uq, h.seed, ← p.modulus]
  have tapeU := source_of_frame h.tape fu p.tapeHash p.prime.randMax urd uwr
  have hc : Impl.Dsa.X86_64.ProbablePrime.candidate (8 * p.prime.len) = Impl.Dsa.Generation.Layout.q := by
    unfold Impl.Dsa.X86_64.ProbablePrime.candidate
    rcases p.width with hh | hh <;> rw [hh] <;> decide
  have hin : PrimeCallInputs (8 * p.prime.len) p.prime.sp p.hash (p.W 5) p.prime.rp p.prime.rand
      p.prime.N used p.W Vu u := {
    layout := Lu
    rep := Ru
    arena := rfl
    arenaWrite := h.arena.congr uwr
    tapePtr := p.tapePtr
    tapeLength := p.tapeLength
    usedSlot := h.usedSlot
    usedBound := h.usedBound
    tapeSize := p.prime.randMax
    tapeCover := by rw [urd, uwr]; exact h.tapeCover
    tapeBytes := bytes_of_src tapeU
    candidate := by
      rw [hc, Nat.mul_div_cancel_left _ (by decide)]
      change Spec.Dsa.decodeBE (Spec.Rsa.bytesAt u.mem (p.W 5 + BitVec.ofNat 64 Impl.Dsa.Generation.Layout.q)
        p.prime.len) = p.prime.N
      rw [p.outputPtr, ubytes, VG.Proof.Dsa.decodeBE_os2ip]
      exact p.encoding
    odd := by
      rw [p.modulus]
      exact (VG.Proof.Dsa.Generation.qCandidate_shape
        (show 2 ≤ 8 * p.prime.len by rcases p.width with hh | hh <;> omega) p.seed).1
    bitLen := p.bits }
  have hch : primeCallChanged (8 * p.prime.len) p.prime.sp (p.W 5) =
      p.primeWrites ++ [⟨p.prime.sp, frameBytes⟩] := by
    rw [SubgroupPlan.primeWrites, ← p.base, ← p.witnessPtr, primeCallChanged,
      Nat.mul_div_cancel_left _ (by decide)]
    rfl
  refine WP.mono (primeCall_ok T (by rcases p.width with hh | hh <;> rw [hh] <;> unfold ProbablePrime.Supported <;> decide) hin p.geometry)
    fun t ⟨used', status, hb, Lt, Rt, he, hr, ft, rdt, wrt⟩ => ?_
  rw [hch] at ft
  refine ⟨used', status, Vu, hb, Lt, Rt, ?_, he, hr, ?_, rdt.trans urd, wrt.trans uwr⟩
  · rw [VG.Proof.Dsa.Generation.frame_bytesAt ft (by
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact p.outputPrime r hr
      · rcases List.mem_singleton.mp hr with rfl; exact p.outputFrame) (by omega), ubytes]
  · exact (fu.mono (by intro r hr; simp only [SubgroupPlan.changed, List.mem_append]; exact Or.inl (Or.inl hr))).trans
      (ft.mono (by intro r hr; simp only [SubgroupPlan.changed, List.append_assoc]; exact List.mem_append_right _ hr))

end VG.Proof.Dsa.X86_64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout
open VG.Proof.MillerRabin.X86_64

theorem seedSubgroup_ok (H : GenerationHashes) (T : PrimeTest)
    {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (seed : GenerationTape p.geo) (hlen : seed.bytes.length = p.geo.qLen)
    (hseed : GenerationTapeMemory seed s) (h1 : W 1 = seed.ptr) {used : Nat}
    (h16 : W 16 = BitVec.ofNat 64 used) (hu : used ≤ p.rand.bytes.length) :
    WP isa (.seq (.block (Impl.Dsa.X86_64.Generation.seedArguments p.geo.qLen))
      (Impl.Dsa.X86_64.Generation.subgroup H.sha1 H.sha256 T.run p.geo.qLen)) s fun t =>
      let res := Spec.Dsa.probablePrime (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) (p.rand.bytes.drop used)
      ∃ used' status, used' ≤ p.rand.bytes.length ∧
        GenerationMemory p (upd (upd (seedWords W p.geo.qLen) 16 (BitVec.ofNat 64 used')) 19 status) t ∧
        Spec.Rsa.bytesAt t.mem (off p.geo.B q) p.geo.qLen =
          Spec.Dsa.encodeBE p.geo.qLen (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) ∧
        (res = none → status = BitVec.ofNat 64 0) ∧
        (∀ b rest, res = some (b, rest) → status = BitVec.ofNat 64 (if b then 1 else 3) ∧
          used' = p.rand.bytes.length - rest.length) ∧
        Frame p.changed s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  refine WP.seq (WP.mono (prepareSeed_ok h) fun u ⟨huMem, fu, ku⟩ => ?_)
  have hseedU := hseed.frame fu ku.2.1 ku.2.2
  have hb : W 5 = p.geo.B := (h.slots 5 (by simp [generationSlots])).trans p.baseSlot
  have h0 : seedWords W p.geo.qLen 0 = off p.geo.B q := by simp [seedWords, upd, hb]
  have h27 : seedWords W p.geo.qLen 27 = seed.ptr := by simp [seedWords, upd, h1]
  have h16u : seedWords W p.geo.qLen 16 = BitVec.ofNat 64 used := by simpa [seedWords, upd] using h16
  have state := huMem.subgroupState seed hlen hseedU h0 h27 h16u hu
  refine WP.mono (subgroup_ok H.h1 H.h256 H.hash1 H.hash256 H.size1 H.size256 H.width1 H.width256 T state)
    fun t ⟨used', status, Vt, bound, Lt, Rt, bytes, fail, result, ft, rd, wr⟩ => ?_
  have ff := huMem.subgroup_frame seed hlen h0 ft
  refine ⟨used', status, bound, huMem.frame Lt ⟨Vt, Rt⟩ ?_ ff rd wr,
    bytes, fail, result, fu.trans ff, rd.trans ku.2.1, wr.trans ku.2.2⟩
  intro k hk
  simp only [generationSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end VG.Proof.Dsa.X86_64.Generation
