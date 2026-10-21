module

import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.DispatchHead
import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Body
public import VerifiedGarbage.Impl.Mont.X86.PreparedSquare
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Compact.Correct
import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.EntryTransport

/-! # Equal operand indices use the verified symmetric square -/

@[expose] public section
namespace VG.Proof.Mont.X86.PreparedSquare
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Spec.Rsa.Mont hiding Keeps

theorem dispatch_ok {s : State} (h : (mulContract abi 16).pre s) :
    WP isa VG.Impl.Mont.X86.PreparedSquare.dispatch s fun u => abiPreserved s u ∧ Compact.Result s u.mem := by
  have A := Compact.entry_of h
  unfold VG.Impl.Mont.X86.PreparedSquare.dispatch
  refine WP.seq (WP.mono (dispatchHead_ok A) ?_)
  rintro t ⟨zf, mem, K⟩
  have sp := K.1 .esp (by decide)
  have ht := pre_transport h mem sp K.2.1 K.2.2
  refine WP.ite (decide (arg s 3 = arg s 4)) zf ?_ ?_
  · intro same
    have eq : arg s 3 = arg s 4 := of_decide_eq_true same
    have teq : arg t 3 = arg t 4 := by rw [argument_transport mem sp, argument_transport mem sp]; exact eq
    refine WP.mono (body_ok (Compact.entry_of ht) teq) ?_
    rintro u ⟨abi, R⟩
    exact ⟨abi_transport K mem abi, (result_transport mem sp _).mp R⟩
  · intro _
    obtain ⟨tr, u, E, abi, R⟩ := Compact.correct t ht
    sig_post [mulContract, sig, VG.X86.abi, argSlots, argVal, argBytes] at R
    exact ⟨tr, u, E, abi_transport K mem abi, (result_transport mem sp _).mp R⟩

theorem correct (s : State) (h : (mulContract abi 16).pre s) :
    ∃ tr t, Exec isa VG.Impl.Mont.X86.PreparedSquare.dispatch s tr t ∧ abiPreserved s t ∧ (mulContract abi 16).post s t := by
  obtain ⟨tr, t, E, abi, R⟩ := dispatch_ok h
  refine ⟨tr, t, E, abi, ?_⟩
  sig_post [mulContract, sig, VG.X86.abi, argSlots, argVal, argBytes]
  exact R

end VG.Proof.Mont.X86.PreparedSquare
