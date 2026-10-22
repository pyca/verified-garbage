module

public import VerifiedGarbage.Proof.MillerRabin.X86.Body
public import VerifiedGarbage.Proof.MillerRabin.X86.Stack
import VerifiedGarbage.Proof.Framework.Sig

/-! # Functional correctness and cdecl preservation against the shared contract -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt numAt wOf)

theorem SnapshotReady.num_same {s σ : State} {j : Nat} (ready : SnapshotReady s σ)
    (A : RoundABI s) (hj : j < 28) :
    numAt σ.mem (wsOf s) (wOf s.mem (wsOf s)) j = numAt s.mem (wsOf s) (wOf s.mem (wsOf s)) j := by
  have facts := round_facts_of (bytes := bytesOf s) rfl ready.width ready.layout ready.prepared ready.length
  have bound := array_fits_bytes facts.fit hj
  exact VG.Proof.MillerRabin.Workspace.numAt_congr (frame_workspace_same A ready.frame)
    (by dsimp only [bytesOf] at bound; omega)

theorem body_result_correct {s t : State} (A : RoundABI s) (result : BodyResult s t) :
    abiPreserved s (freed VG.Impl.MillerRabin.X86.frameBytes t) ∧
      (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact stackBytes).post s
        (freed VG.Impl.MillerRabin.X86.frameBytes t) := by
  rcases result with ⟨registers, frame, σ, ready, value, kept⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    by_cases esp : r = .esp
    · subst r
      rw [freed_esp, registers .esp hr, allocFrame_esp, BitVec.sub_add_cancel]
    · rw [freed_gpr _ _ esp, registers r hr, allocFrame_gpr _ _ esp]
  · exact A.return_unchanged frame
  · sig_post [Spec.MillerRabin.roundContract, Spec.MillerRabin.roundSig, abi, argSlots, argVal, argBytes]
    refine ⟨?_, ?_⟩
    · intro b hb
      have candidate : val32 σ.mem (wsOf s) 256 (2 * wOf s.mem (wsOf s)) =
          numAt s.mem (wsOf s) (wOf s.mem (wsOf s)) 0 := by
        rw [← candidate_value, ready.num_same A (by decide : 0 < 28)]
      have correct := final_flag_correct ready.width ready.prepared (b := b) (by
        rw [ready.num_same A (by decide : 5 < 28), candidate]
        exact hb)
      rw [candidate] at correct
      rw [BitVec.setWidth_append_eq_right, value, correct]
      cases Spec.MillerRabin.round (numAt s.mem (wsOf s) (wOf s.mem (wsOf s)) 0) b <;> rfl
    · intro i hi headers arrays table
      exact (kept i hi headers arrays table).trans (frame_workspace_same A ready.frame i hi)

theorem round_correct (s : State)
    (h : (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact stackBytes).pre s) :
    ∃ tr t, Exec isa code s tr t ∧ abiPreserved s t ∧
      (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact stackBytes).post s t := by
  have A := roundAbi_of h
  exact WP.frameAlloc (by decide) (by decide) (by decide)
    (Nat.le_trans (by decide : VG.Impl.MillerRabin.X86.frameBytes ≤ stackBytes) A.stackLow) body_noSp
    (WP.mono (body_ok A) fun _ result => body_result_correct A result)

end VG.Proof.MillerRabin.X86
