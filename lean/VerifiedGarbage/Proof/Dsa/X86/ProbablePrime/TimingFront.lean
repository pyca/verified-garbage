module

public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Enter

import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Load
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportLoadTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessLoadTiming
import VerifiedGarbage.Proof.MillerRabin.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Impl.RsaKeyGen.X86.LowWord
import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateSave
import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
/-! # The entry and the import leak only public pointers and the candidate's width -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/LowWordTiming.lean`, which only this module imported.
section

/-! # Low-word updates have no secret-dependent addresses or branches -/

section
namespace VG.Proof.RsaKeyGen.X86.LowWord
open VG VG.X86 VG.Proof.Dsa.X86 VG.Impl.RsaKeyGen.X86.LowWord

theorem decrement_trace (out : Nat) :
    RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block (decrement out))
      (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
  erased_relCT (.block (decrement out)) (.block (decrement 0)) (.block [])
    rfl rfl rfl (by decide +kernel)

theorem increment_trace (out : Nat) :
    RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block (increment out))
      (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
  erased_relCT (.block (increment out)) (.block (increment 0)) (.block [])
    rfl rfl rfl (by decide +kernel)

end VG.Proof.RsaKeyGen.X86.LowWord
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidateSaveTiming.lean`, which only this module imported.
section

/-! # Saving and restoring the candidate have fixed public loop bounds -/

section
namespace VG.Proof.RsaKeyGen.X86.CandidateSave
open VG VG.X86 VG.Proof.Dsa.X86 VG.Impl.RsaKeyGen.X86.CandidateSave

theorem copy_trace (n src dst : Nat) :
    RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (VG.Impl.Rsa.X86.Div.copyWords n src dst)
      (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
  erased_relCT (VG.Impl.Rsa.X86.Div.copyWords n src dst)
    (VG.Impl.Rsa.X86.Div.copyWords 1 0 0) (VG.Taint.hintOf taint (τr [.esp,
        .edi]) (Code.erase (VG.Impl.Rsa.X86.Div.copyWords 1 0 0)))
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

theorem save_trace (n src dst : Nat) :
    RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (save n src dst)
      (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
  RelCT.seq (copy_trace n src dst) (LowWord.decrement_trace dst)

theorem restore_trace (n src dst : Nat) :
    RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (restore n src dst)
      (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
  RelCT.seq (copy_trace n src dst) (LowWord.increment_trace dst)

theorem restore_workspace_trace (n src dst : Nat) :
    RelCT isa (VG.X86.Taint.Agree (VG.Proof.Mont.X86.Dynamic.workspaceTaint false)) (restore n src dst)
      (VG.X86.Taint.Agree (VG.Proof.Mont.X86.Dynamic.workspaceTaint false)) := by
  unfold restore
  apply RelCT.seq (R := VG.X86.Taint.Agree (VG.Proof.Mont.X86.Dynamic.workspaceTaint false))
  · exact erased_relCT (VG.Impl.Rsa.X86.Div.copyWords n src dst)
      (VG.Impl.Rsa.X86.Div.copyWords 1 0 0)
      (VG.Taint.hintOf taint (VG.Proof.Mont.X86.Dynamic.workspaceTaint false)
        (Code.erase (VG.Impl.Rsa.X86.Div.copyWords 1 0 0))) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)
  · exact erased_relCT (.block (VG.Impl.RsaKeyGen.X86.LowWord.increment dst))
      (.block (VG.Impl.RsaKeyGen.X86.LowWord.increment 0)) (.block []) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

end VG.Proof.RsaKeyGen.X86.CandidateSave
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86.ProbablePrime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Dsa.X86.ProbablePrime

def EntryPair (E : Environment) (c : Nat) (entropy : List Byte) (s t : State) : Prop :=
  EntryInput E c entropy s ∧ EntryInput E c entropy t

def InputPair (E : Environment) (c : Nat) (entropy : List Byte) (s t : State) : Prop :=
  (Input E c entropy s ∧ w32 s.mem E.base 152 = 0) ∧ (Input E c entropy t ∧ w32 t.mem E.base 152 = 0)

def LoadedPair (E : Environment) (c : Nat) (entropy : List Byte) (s t : State) : Prop :=
  Loaded E c entropy s ∧ Loaded E c entropy t

theorem Input.agree {E : Environment} {c : Nat} {entropy : List Byte} {s t : State}
    (I : Input E c entropy s) (J : Input E c entropy t) : VG.X86.Taint.Agree (τr [.esp, .edi]) s t := by
  apply agree_regs
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact I.stack.trans J.stack.symm
  · exact BitVec.eq_of_toNat_eq (I.scratch.edi_toNat.trans J.scratch.edi_toNat.symm)

theorem pointer_ok {E : Environment} {c : Nat} {entropy : List Byte} {s : State} (S : EntryInput E c entropy s) :
    WP isa (.block [.mov .edi (.mem (VG.Impl.Mont.X86.Compact.arg 0))]) s fun t =>
      t.gpr .edi = E.argument 0 ∧ Keeps [.edi] s t :=
  wp_movS (S.read 0 (by decide)) fun _ T _ => WP.block_nil ⟨T.gpr, T.keeps⟩

theorem enter_trace {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} :
    RelCT isa (EntryPair E c entropy) (.block enter) (InputPair E c entropy) := by
  have pointer : RelCT isa (EntryPair E c entropy) (.block [.mov .edi (.mem (VG.Impl.Mont.X86.Compact.arg 0))])
      (VG.X86.Taint.Agree (τr [.esp, .edi])) := by
    intro s t tr ur u z ⟨S, T⟩ A B
    have raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block [.mov .edi (.mem (VG.Impl.Mont.X86.Compact.arg 0))])
        (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl
    have agree : VG.X86.Taint.Agree (τr [.esp]) s t := agree_regs (by
      intro r mem; obtain rfl := List.mem_singleton.mp mem; exact S.sp.trans T.sp.symm)
    have resultS := wp_result (pointer_ok S) A
    have resultT := wp_result (pointer_ok T) B
    refine ⟨(raw _ _ _ _ _ _ agree A B).1, agree_regs ?_⟩
    intro r mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · rw [resultS.2.1 .esp (by decide), resultT.2.1 .esp (by decide)]; exact S.sp.trans T.sp.symm
    · exact resultS.1.trans resultT.1.symm
  have copies : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi]))
      (.block (copy 2 28 ++ (copy 3 32 ++ (copy 1 40 ++ (copy 4 44 ++ [.mov .eax (.imm 0), .store (VG.Impl.Mont.X86.sc 152) .eax])))))
      (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
    erased_relCT _ (.block (copy 2 28 ++ (copy 3 32 ++ (copy 1 40 ++ (copy 4 44 ++
      [.mov .eax (.imm 0), .store (VG.Impl.Mont.X86.sc 152) .eax]))))) (.block []) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)
  have raw : RelCT isa (EntryPair E c entropy) (.block enter) (fun _ _ => True) := by
    unfold enter
    simp only [List.append_assoc]
    exact RelCT.block_append ((RelCT.seq pointer copies).mono (fun _ _ H => H) (fun _ _ _ => trivial))
  intro s t tr ur u z P A B
  obtain ⟨IU, countU, _, _⟩ := wp_result (enter_ok v P.1) A
  obtain ⟨IZ, countZ, _, _⟩ := wp_result (enter_ok v P.2) B
  exact ⟨(raw _ _ _ _ _ _ P A B).1, ⟨IU, countU⟩, ⟨IZ, countZ⟩⟩

theorem source_trace (x : Nat) : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi]))
    (.block [.mov .esi (.reg .edi), .alu .add .esi (.imm (BitVec.ofNat 32 x))])
    (VG.X86.Taint.Agree (τr [.esp, .edi, .esi])) :=
  erased_relCT _ (.block [.mov .esi (.reg .edi), .alu .add .esi (.imm 0)]) (.block []) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)
    (by decide +kernel)

theorem load_trace {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} (odd : c % 2 = 1) :
    RelCT isa (InputPair E c entropy) (load E.words E.width) (LoadedPair E c entropy) := by
  have pointer := source_trace (scratchBytes E.width)
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (load E.words E.width)
      (VG.X86.Taint.Agree (τr [.esp, .edi])) := by
    have imported : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi, .esi]))
        (VG.Impl.RsaKeyGen.X86.Import.load E.words (VG.Impl.Bignum.X86.PublicContext.slot E.width 0))
        (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
      (VG.Proof.RsaKeyGen.X86.Import.load_trace _ _).mono (fun _ _ H => H)
        (fun _ _ H => taint.le_sound (by decide +kernel) H)
    have zeros : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi]))
        (.block (VG.Impl.RsaKeyGen.X86.WitnessLoad.zeros
          (VG.Impl.Bignum.X86.PublicContext.slot E.width 0 + 4 * E.words) (2 * E.width - E.words)))
        (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
      (VG.Proof.RsaKeyGen.X86.WitnessLoad.zeros_trace _ _).mono (fun _ _ H => taint.le_sound (by decide +kernel) H)
        (fun _ _ H => taint.le_sound (by decide +kernel) H)
    unfold load VG.Impl.RsaKeyGen.X86.WitnessLoad.zeroTail
    exact RelCT.seq pointer (RelCT.seq imported (RelCT.seq zeros
      (VG.Proof.RsaKeyGen.X86.CandidateSave.save_trace _ _ _)))
  intro s t tr ur u z P A B
  obtain ⟨LU, _, _, _⟩ := wp_result (load_ok v P.1.1 P.1.2 odd) A
  obtain ⟨LZ, _, _, _⟩ := wp_result (load_ok v P.2.1 P.2.2 odd) B
  exact ⟨(raw _ _ _ _ _ _ (P.1.1.agree P.2.1) A B).1, LU, LZ⟩

end VG.Proof.Dsa.X86.ProbablePrime
