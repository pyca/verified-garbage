module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeFrameCTState
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CheckPrime
import VerifiedGarbage.Proof.Framework.Omega

/-! # Workspace initialization preserves the public frame arguments and input tapes -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64

theorem primeWorkspace_ready {p : PrimeFramePublic} {s : State}
    (h : PrimeFrameInputs p s)
    (hs : Scr s p.bytes.call.draw.prime.B p.bytes.call.draw.prime.Z)
    (hdi : s.gpr .x0 = p.bytes.call.draw.prime.B) :
    WP isa (Impl.Dsa.AArch64.Generation.workspace p.bytes.call.draw.prime.w) s (PrimeFrameState p) := by
  have hz := p.bytes.call.draw.prime.z256
  have hroom : slot p.bytes.call.draw.prime.w 16 ≤ p.bytes.call.draw.prime.Z :=
    Nat.le_trans (slot_mono _ (by decide)) p.bytes.call.draw.prime.room
  refine WP.mono (workspace_ok hs hdi hroom (by have := p.bytes.call.draw.prime.w4; omega)
    (by have := p.bytes.call.width; omega)) fun t ⟨hg, _, hf, hk⟩ => ?_
  have hr : ∀ r ∈ workspaceRanges, r.1 + r.2 ≤ p.bytes.call.draw.prime.Z := by
    intro r hr
    simp only [workspaceRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only <;> omega
  have headers (k : Nat) (hkw : k < 34) :
      VG.Proof.Bignum.word t.mem p.F (8 * k) = VG.Proof.Bignum.word s.mem p.F (8 * k) :=
    frame_word_of_workspace hf hr (p.outside k hkw)
  refine { good := hg
           stack := hk.sp.trans h.stack
           read := fun k hkw => by rw [hk.rd, hk.wr]; exact h.read k hkw
           arena := (headers 5 (by decide)).trans h.arena
           tapePtr := (headers 14 (by decide)).trans h.tapePtr
           tapeLength := (headers 15 (by decide)).trans h.tapeLength
           used := (headers 16 (by decide)).trans h.used
           tape := h.tape.congrK (InScr.of_frm hf hr) hk
           source := h.source.congrK (InScr.of_frm hf hr) hk
           writable := fun i hi => by rw [hk.wr]; exact h.writable i hi
           usedBound := h.usedBound }

end VG.Proof.Dsa.AArch64.Generation
