module

import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveSetup
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveContext
import VerifiedGarbage.Proof.Framework.X86.SymFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveCandidateSlots

/-! # The static table and stack setup have public memory addresses -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.X86 VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.Sieve

theorem setup_trace {g : Geometry} (v : g.Valid) {c d : Nat} (low : 4 ≤ g.sp.toNat) :
    RelCT isa (fun s t => Context g c s ∧ Context g d t ∧ s.gpr .edi = g.candidate ∧ t.gpr .edi = g.candidate)
      (.seq (.block (candidateSlots stackSlots g.w))
        (.seq tableAddress (.block (tableSlots stackSlots g.w))))
      (VG.X86.Taint.Agree (τr [.esp])) := by
  have first : RelCT isa (fun s t => Context g c s ∧ Context g d t ∧ s.gpr .edi = g.candidate ∧ t.gpr .edi = g.candidate)
      (.block (candidateSlots stackSlots g.w))
      (fun s t => s.gpr .esp = g.sp ∧ t.gpr .esp = g.sp) := by
    intro s t tr ur u z ⟨S, T, Ps, Pt⟩ E G
    have A : VG.X86.Taint.Agree (τr [.esp]) s t :=
      agree_regs (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact S.stack.sp.trans T.stack.sp.symm)
    have trace := ((erased_relCT (τ := τr [.esp]) (σ := τr [.esp]) (.block (candidateSlots stackSlots g.w)) (.block (candidateSlots stackSlots 0)) (.block []) rfl rfl rfl (by decide +kernel))
      _ _ _ _ _ _ A E G).1
    have U := wp_result (candidateSlots_ok v S Ps) E
    have Z := wp_result (candidateSlots_ok v T Pt) G
    exact ⟨trace, U.1.context.stack.sp, Z.1.context.stack.sp⟩
  have middle : RelCT isa (fun s t => s.gpr .esp = g.sp ∧ t.gpr .esp = g.sp)
      tableAddress (VG.X86.Taint.Agree (τr [.esp])) := by
    intro s t tr ur u z ⟨S, T⟩ E G
    have Ls : 4 ≤ (s.gpr .esp).toNat := by rw [S]; exact low
    have Lt : 4 ≤ (t.gpr .esp).toNat := by rw [T]; exact low
    have U := wp_result (symFrame_ok VG.Impl.RsaKeyGen.TrialTable32.symbol s Ls) E
    have Z := wp_result (symFrame_ok VG.Impl.RsaKeyGen.TrialTable32.symbol t Lt) G
    refine ⟨?_, agree_regs (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact
      (U.gpr .esp (by decide)).trans (S.trans (T.symm.trans (Z.gpr .esp (by decide)).symm)))⟩
    rw [symFrame_trace Ls E, symFrame_trace Lt G, S, T]
  exact RelCT.seq first (RelCT.seq middle (erased_relCT (.block (tableSlots stackSlots g.w)) (.block (tableSlots stackSlots 0)) (.block []) rfl rfl rfl (by decide +kernel)))

end VG.Proof.RsaKeyGen.X86.Sieve
