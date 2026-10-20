module

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSeed
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hashes
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Context
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedArguments
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Subgroup
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextFrame

/-! # Complete first phase of a seed attempt, retaining every retry input -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout
open VG.Proof.MillerRabin.X86_64

theorem seedSubgroup_ok (H : GenerationHashes) (M : Mont) (K : Kernel)
    {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (seed : GenerationTape p.geo) (hlen : seed.bytes.length = p.geo.qLen)
    (hseed : GenerationTapeMemory seed s) (h1 : W 1 = seed.ptr) {used : Nat}
    (h16 : W 16 = BitVec.ofNat 64 used) (hu : used ≤ p.rand.bytes.length) :
    WP isa (.seq (.block (Impl.Dsa.X86_64.Generation.seedArguments p.geo.qLen))
      (Impl.Dsa.X86_64.Generation.subgroup H.sha1 H.sha256 M.mm K.run p.geo.qLen)) s fun t =>
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
  refine WP.mono (subgroup_ok H.h1 H.h256 H.hash1 H.hash256 H.size1 H.size256 H.width1 H.width256 M K state)
    fun t ⟨used', status, Vt, bound, Lt, Rt, bytes, fail, result, ft, rd, wr⟩ => ?_
  have ff := huMem.subgroup_frame seed hlen h0 ft
  refine ⟨used', status, bound, huMem.frame Lt ⟨Vt, Rt⟩ ?_ ff rd wr,
    bytes, fail, result, fu.trans ff, rd.trans ku.2.1, wr.trans ku.2.2⟩
  intro k hk
  simp only [generationSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end VG.Proof.Dsa.X86_64.Generation
