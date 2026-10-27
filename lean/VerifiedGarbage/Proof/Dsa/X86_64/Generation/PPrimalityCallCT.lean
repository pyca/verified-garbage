module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PPrimalityCTState
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateWidthCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeCallCT
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Proof.Dsa.Encoding
public import Mathlib.Algebra.Group.Nat.Defs

/-! # Instantiate the public width guard and primality call for a p candidate -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Dsa.Generation VG.Impl.Dsa.Generation.Layout

def PPrimalityPublic.width (p : PPrimalityPublic)
    (hb : p.plan.construct.value < 2 ^ (8 * p.plan.construct.len)) : CandidateWidthPublic where
  B := p.plan.construct.B
  F := p.plan.construct.hash.F
  Z := p.plan.construct.Z
  w := p.plan.construct.len / 8
  ptr := off (p.plan.construct.hash.W 5) Impl.Dsa.Generation.Layout.p
  len := p.plan.construct.len
  value := p.plan.construct.value
  positive := by rcases p.plan.construct.width with h | h | h <;> omega
  fits := by simpa only [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] using hb

theorem pPrimality_width {p : PPrimalityPublic} {s : State} (h : PPrimalityAfter p s) :
    CandidateWidthBefore (p.width h.fits) s := by
  refine ⟨h.ws, h.layout.rsp, h.pointer, h.bytes, ?_⟩
  have read := h.source.rd 0 (by
    rw [VG.Proof.Dsa.encodeBE_length]
    exact (p.width h.fits).positive)
  simpa only [PPrimalityPublic.width, off, BitVec.add_zero] using read

def PPrimalityPublic.primeCall (p : PPrimalityPublic)
    (domain : PDomain p.plan.construct.len p.plan.construct.value) : PrimeCallPublic (8 * p.plan.construct.len) where
  F := p.plan.construct.hash.F
  S := p.plan.construct.hash.S
  A := p.plan.construct.hash.W 5
  rp := p.plan.rp
  rand := p.plan.rand
  N := p.plan.construct.value
  used := p.used
  geometry := (p.plan.call domain).geometry

theorem pPrimality_primeCall {p : PPrimalityPublic} {s : State} (h : PPrimalityAfter p s)
    (domain : PDomain p.plan.construct.len p.plan.construct.value) :
    PrimeCallBefore (8 * p.plan.construct.len) (p.primeCall domain) s := by
  obtain ⟨V, W, R, hw, hu⟩ := h.frame
  have hc : Impl.Dsa.X86_64.ProbablePrime.candidate (8 * p.plan.construct.len) = Impl.Dsa.Generation.Layout.p := by
    change (if 8 * p.plan.construct.len ≤ 256 then _ else _) = _
    exact ite_eq_right (by rcases p.plan.construct.width with hh | hh | hh <;> omega)
  exact ⟨W, V, {
    layout := h.layout
    rep := R
    arena := hw.1 5 (by decide)
    arenaWrite := h.arena
    tapePtr := hw.2.1
    tapeLength := hw.2.2
    usedSlot := hu
    usedBound := h.usedBound
    tapeSize := p.plan.randMax
    tapeCover := h.tapeCover
    tapeBytes := bytes_of_src h.tape
    candidate := by
      rw [hc, Nat.mul_div_cancel_left _ (by decide)]
      change Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
        (off (p.plan.construct.hash.W 5) Impl.Dsa.Generation.Layout.p) p.plan.construct.len) = _
      rw [h.bytes]
      exact VG.Proof.Dsa.decodeBE_encodeBE (p.width domain.upper).fits
    odd := h.odd
    bitLen := (p.plan.prime domain).bitLength_eq }⟩

end VG.Proof.Dsa.X86_64.Generation
