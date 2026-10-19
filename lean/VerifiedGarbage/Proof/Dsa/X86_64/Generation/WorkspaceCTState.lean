module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeFrameCTState
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CheckPrime
import VerifiedGarbage.Proof.Framework.Omega

/-! # Workspace initialization preserves the public frame arguments and input tapes -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

theorem primeWorkspace_ready {p : PrimeFramePublic} {s : State}
    (h : PrimeFrameInputs p s)
    (hs : Scr s p.bytes.call.draw.prime.B p.bytes.call.draw.prime.Z)
    (hdi : s.gpr .rdi = p.bytes.call.draw.prime.B) :
    WP isa (Impl.Dsa.X86_64.Generation.workspace p.bytes.call.draw.prime.w) s (PrimeFrameState p) := by
  have hz := p.bytes.call.draw.prime.z256
  have hroom : slot p.bytes.call.draw.prime.w 16 ≤ p.bytes.call.draw.prime.Z :=
    Nat.le_trans (slot_mono _ (by decide)) p.bytes.call.draw.prime.room
  refine WP.mono (workspace_ok hs hdi hroom (by have := p.bytes.call.draw.prime.dims.w4; omega)
    (by have := p.bytes.call.width; omega)) fun t ⟨_, hg, hf, hk⟩ => ?_
  have hr : ∀ r ∈ [(48, 80), (224, 8)], r.1 + r.2 ≤ p.bytes.call.draw.prime.Z := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only <;> omega
  have headers (k : Nat) (hkw : k < 37) :
      word t.mem p.bytes.call.draw.prime.sp (8 * k) = word s.mem p.bytes.call.draw.prime.sp (8 * k) :=
    frame_word_of_workspace hf hr (p.outside k hkw)
  refine { good := ⟨0, hg⟩
           stack := (hk.gpr (by decide)).trans h.stack
           read := fun k hkw => by rw [hk.2.1, hk.2.2]; exact h.read k hkw
           arena := (headers 5 (by decide)).trans h.arena
           tapePtr := (headers 13 (by decide)).trans h.tapePtr
           tapeLength := (headers 15 (by decide)).trans h.tapeLength
           used := (headers 16 (by decide)).trans h.used
           tape := h.tape.congrK (InScr.of_frm hf hr) hk
           source := h.source.congrK (InScr.of_frm hf hr) hk
           writable := fun i hi => by rw [hk.2.2]; exact h.writable i hi
           wr := hk.2.2.trans h.wr
           usedBound := h.usedBound }

end VG.Proof.Dsa.X86_64.Generation
