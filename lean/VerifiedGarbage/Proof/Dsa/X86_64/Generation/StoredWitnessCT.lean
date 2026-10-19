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
    WP isa (.block [.mov .rbx (.reg .rdi), .mov .rdi (.mem (hdr kOut))]) s
      (fun t => t.gpr .rdi = p.prime.p) := by
  obtain ⟨mi, h⟩ := h
  have hl : InRegions (s.rd ++ s.wr) (off p.prime.B (8 * kOut)) 8 :=
    h.ready.good.scr.ld (by
      have := hdr_lt_slot p.prime.w 8 (show kOut < 32 by decide)
      have := p.prime.dims.z
      omega)
  xrun [State.ea, hdr, hdrOff, h.ready.good.rdi, hl, h.ptr]

theorem forceStoredWitness_ct (len : Nat)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi])
      (.block (Impl.Dsa.X86_64.Generation.forceWitness len)) hc).isSome = true) : RelCT isa (Two SampleBefore)
    (Impl.Dsa.X86_64.Generation.forceStoredWitness kOut len) (fun _ _ => True) := by
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
  · refine RelCT.seq (two_taint [.rdi] (by
      intro p s t hs ht r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact hs.trans ht.symm) ht) ?_
    exact RelCT.taint (A := taint) (Taint.ofRegs [])
      (fun _ _ _ => Taint.agree_ofRegs (by intro r hr; simp at hr)) (by taint_decide)

def SamplePublic.forced (p : SamplePublic) : SamplePublic :=
  ⟨p.prime, VG.Proof.Dsa.Generation.forcedWitnessBytes p.bytes,
    (VG.Proof.Dsa.Generation.forcedWitnessBytes_length
      (by rw [p.length]; exact p.prime.len2)).trans p.length⟩

theorem forceSample_state {p : SamplePublic} {s : State} (h : SampleBefore p s) :
    WP isa (Impl.Dsa.X86_64.Generation.forceStoredWitness kOut p.bytes.length) s
      (SampleBefore p.forced) := by
  obtain ⟨mi, h⟩ := h
  exact WP.mono (forceSample_ok h p.prime.dims
    (by rw [p.length]; exact p.prime.len2)
    (by rw [p.length]; have := p.prime.lenDraw; have := p.prime.drawMax; omega))
    fun _ ht => ⟨mi, ht.1⟩

end VG.Proof.Dsa.X86_64.Generation
