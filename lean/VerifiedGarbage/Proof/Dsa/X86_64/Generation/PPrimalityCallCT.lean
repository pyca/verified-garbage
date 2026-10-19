module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PPrimalityCTState
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateWidthCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CheckPrimeCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Arithmetic

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

def PPrimalityPublic.call (p : PPrimalityPublic) (domain : PDomain p.plan.construct.len p.plan.construct.value) :
    PrimeFramePublic where
  bytes := {
    call := {
      draw := ⟨p.plan.prime domain, p.used⟩
      arena := p.plan.construct.hash.W 5
      wr := p.wr
      layout := p.header
      base := p.plan.construct.base.symm
      width := (p.plan.call domain).wordsMax
      tab := (p.plan.call domain).tableRoom
      large := domain.large
      policy := domain.policy }
    source := off (p.plan.construct.hash.W 5) Impl.Dsa.Generation.Layout.p
    bytes := Spec.Dsa.encodeBE p.plan.construct.len p.plan.construct.value
    length := VG.Proof.Dsa.encodeBE_length _ _
    value := by
      rw [← VG.Proof.Dsa.decodeBE_os2ip]
      exact VG.Proof.Dsa.decodeBE_encodeBE (p.width domain.upper).fits }
  candidate := Impl.Dsa.Generation.Layout.p
  candidateBound := by decide
  checksBound := (p.plan.call domain).checksMax
  checks := domain.checks.symm
  source := rfl
  witness := rfl
  separate := p.plan.construct.frameHeaders
  outside := p.plan.construct.frameOutside

theorem pPrimality_call {p : PPrimalityPublic} {s : State} (h : PPrimalityAfter p s)
    (domain : PDomain p.plan.construct.len p.plan.construct.value) :
    CheckPrimeBefore (p.plan.construct.len / 8) Impl.Dsa.Generation.Layout.p p.plan.construct.len
      p.plan.construct.len (if p.plan.construct.len ≤ 256 then 64 else 128) (p.call domain) s := by
  obtain ⟨V, W, R, hw, hu⟩ := h.frame
  refine ⟨?_, h.ws.scr, h.ws.rdi, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨h.layout.rsp, ?_, ?_, ?_, ?_, ?_, h.tape, h.source, h.writable, h.wr, h.usedBound⟩
  · intro k hk; exact h.layout.ld (by unfold VG.Impl.RsaOaep.X86_64.frameBytes; omega)
  · exact (R.fr 5 (by decide)).trans (hw.1 5 (by decide))
  · exact (R.fr 13 (by decide)).trans hw.2.1
  · exact (R.fr 15 (by decide)).trans hw.2.2
  · exact (R.fr 16 (by decide)).trans hu

end VG.Proof.Dsa.X86_64.Generation
