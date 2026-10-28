module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TestWitnessCT
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.StoredWitness
public import VerifiedGarbage.Proof.Dsa.Generation.WitnessBytes
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ForceSample
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TestWitnessCT
meta import VerifiedGarbage.Impl.Dsa.X86_64.Generation.StoredWitness
meta import VerifiedGarbage.Proof.Dsa.Generation.WitnessBytes
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ForceSample
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Fixed-address transformation of a nonuniform DSA witness -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem forceSampleArgs_state {p : SamplePublic} {s : State} (h : SampleBefore p s) :
    WP isa (.block [.mov .rbx (.reg .rdi), .mov .rcx (.mem (hdr kUsedP)), .mov .rdi (.mem (hdr kOut))]) s
      (fun t => t.gpr .rdi = p.prime.p ∧ t.gpr .rcx = BitVec.ofNat 64 p.bytes.length) := by
  obtain ⟨mi, h⟩ := h
  have hl : ∀ k < 32, InRegions (s.rd ++ s.wr) (off p.prime.B (8 * k)) 8 := fun k hk =>
    h.ready.good.scr.ld (by
      have := hdr_lt_slot p.prime.w 8 hk
      have := p.prime.dims.z
      omega)
  xrun [State.ea, hdr, hdrOff, h.ready.good.rdi, hl kOut (by decide), hl kUsedP (by decide), h.ptr, h.len]

theorem forceStoredWitness_ct : RelCT isa (Two SampleBefore)
    (Impl.Dsa.X86_64.Generation.forceStoredWitness kOut kUsedP) (fun _ _ => True) := by
  unfold Impl.Dsa.X86_64.Generation.forceStoredWitness
  simp only [seqs]
  refine RelCT.seq (two_post (two_taint [.rdi] ?_ (by taint_decide))
    (fun _ _ h => forceSampleArgs_state h)) ?_
  · intro p s t hs ht r hr
    simp only [List.mem_singleton] at hr
    subst r
    obtain ⟨mi, hs⟩ := hs
    obtain ⟨mi', ht⟩ := ht
    exact hs.ready.good.rdi.trans ht.ready.good.rdi.symm
  · refine RelCT.seq (two_taint [.rdi, .rcx] (by
      intro p s t hs ht r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hs.1.trans ht.1.symm
      · exact hs.2.trans ht.2.symm) (by taint_decide)) ?_
    exact RelCT.taint (A := taint) (Taint.ofRegs [])
      (fun _ _ _ => Taint.agree_ofRegs (by intro r hr; simp at hr)) (by taint_decide)

def SamplePublic.forced (p : SamplePublic) : SamplePublic :=
  ⟨p.prime, VG.Proof.Dsa.Generation.forcedWitnessBytes p.bytes,
    (VG.Proof.Dsa.Generation.forcedWitnessBytes_length
      (by rw [p.length]; exact p.prime.len2)).trans p.length⟩

theorem forceSample_state {p : SamplePublic} {s : State} (h : SampleBefore p s) :
    WP isa (Impl.Dsa.X86_64.Generation.forceStoredWitness kOut kUsedP) s
      (SampleBefore p.forced) := by
  obtain ⟨mi, h⟩ := h
  exact WP.mono (forceSample_ok h p.prime.dims
    (by rw [p.length]; exact p.prime.len2)
    (by rw [p.length]; have := p.prime.lenDraw; have := p.prime.drawMax; omega))
    fun _ ht => ⟨mi, ht.1⟩

end VG.Proof.Dsa.X86_64.Generation
