module

public import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Finish
import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Entry
import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Loop
import VerifiedGarbage.Proof.Ffdh.GenerationBounds
import VerifiedGarbage.Proof.Framework.Sig

/-! # The parameter search against its contract (x86)

The entry, the loop from its first state and the finish run the search from
the tape's start (`operation_ok`), which is `sievedParameterSearch`; so the
code meets `vg_ffdh_generate_parameters_sieved`'s contract (`correct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.PSearch

open VG VG.X86 VG.X86.Wp VG.Spec.Ffdh
open VG.Proof.Dsa.X86 (argumentPointer)

/-- The search the contract specifies. -/
abbrev searchOf (o : State) : ParameterSearchResult :=
  sievedParameterSearch (ofState o).bits (ofState o).gen (ofState o).attempts (ofState o).rand

theorem tail_zero (o : State) : (ofState o).tail 0 (ofState o).attempts = searchOf o := by
  simp only [PPub.tail, ptail, List.drop_zero, Generation.consume_zero]

theorem operation_ok {o : State} (A : PSearchABI o) :
    WP isa Impl.Ffdh.X86.ParamSearch.code o (Fin o (searchOf o)) := by
  unfold Impl.Ffdh.X86.ParamSearch.code
  refine WP.seq (WP.mono (entry_ok A) fun s hs => ?_)
  refine WP.seq (WP.mono (loop_ok hs) fun t ht => ?_)
  rw [tail_zero] at ht
  exact finish_ok ht

theorem correct (s : State) (h : contract.pre s) :
    ∃ trace t, Exec isa Impl.Ffdh.X86.ParamSearch.code s trace t ∧ abiPreserved s t ∧ contract.post s t := by
  obtain ⟨trace, t, E, F⟩ := operation_ok (pSearchABI_of h)
  refine ⟨trace, t, E, ⟨F.saved, F.ret⟩, ?_⟩
  have out := F.output
  unfold Output at out
  sig_post [contract, Spec.Ffdh.sievedParameterSearchContract, Spec.Ffdh.parameterSearchSig, abi, argSlots, argVal,
    argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts]
  refine ⟨?_, ?_, F.used, F.policy⟩
  · rw [BitVec.setWidth_append_eq_right, F.eax, toNat_ofNat_lt (by have := status_le (searchOf s); omega)]
    rfl
  · show Spec.Rsa.bytesAt t.mem ((arg s 0).setWidth 64) (arg s 1).toNat = (match searchOf s with
      | .accepted p _ => Spec.Rsa.i2osp p (arg s 1).toNat
      | _ => List.replicate (arg s 1).toNat 0)
    revert out
    cases searchOf s <;> exact id

end VG.Proof.Ffdh.X86.PSearch
