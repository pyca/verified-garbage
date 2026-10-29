module

public import VerifiedGarbage.Proof.Dsa.X86.StreamTiming
public import VerifiedGarbage.Proof.Dsa.X86.CoreReduce

import VerifiedGarbage.Proof.Dsa.X86.CoreSetupTiming
import VerifiedGarbage.Proof.Dsa.X86.CoreStoreTiming
import VerifiedGarbage.Proof.Dsa.X86.PointerTiming
import VerifiedGarbage.Proof.Dsa.X86.CoreSetup
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Dsa.X86.RedCall
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.X86.Pointer
import VerifiedGarbage.Proof.Mont.X86.ContextFrame
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.TCB.X86.Isa
import VerifiedGarbage.TCB.X86.State
/-! # Complete streaming reduction calls have secret-independent traces -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/CoreStreamSource.lean`, which only this module imported.
section

/-! # The public byte-source pointer for scalar reduction -/

section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem streamSource_ok {s : State} {base : Addr} {size n m : Nat}
    (h : Context n m base size s) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size) (p : Pointer) :
    WP isa (.block (Core.pointer p)) s fun t =>
      Context n m base size t ∧ t.gpr .esi = pointerValue base s p ∧ t.mem = s.mem ∧ Keeps [.esi] s t :=
  WP.mono (pointer_ok h.scr hz p) fun u ⟨Pu, Ku, Mu⟩ =>
    ⟨⟨h.scr.of_keeps Ku (by decide), h.size_le, Mu ▸ h.modulus, h.gt_one, Mu ▸ h.inverse⟩, Pu, Mu, Ku⟩

end VG.Proof.Dsa.X86
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

structure ReductionPre (base : Addr) (size qLen inputLen : Nat) (input : Pointer) (src : Src) (s : State) : Prop where
  scr : Scr s base size
  modulusReady : OperandReady s base ((qLen + 7) / 8) (.input .q) qLen
  inputReady : StreamInput s base (contextBytes ((qLen + 7) / 8)) (pointerValue base s input) inputLen
  len : LenOperand base size ((qLen + 7) / 8) s src inputLen
  large : 255 < Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .q)).setWidth 64) qLen)
  odd : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .q)).setWidth 64) qLen) % 2 = 1
  room : Pow.Room (s.gpr .esp) base size
  stack : Region.Disjoint ⟨(pointerValue base s input).setWidth 64, inputLen⟩ (callStack (s.gpr .esp))
  lenFit : inputLen < 2 ^ 32

theorem movLen_trace {src : Src} (hf : LenForm src) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint true)) (.block [.mov .ebx src]) (fun _ _ => True) := by
  intro s t tr ur s' t' A E F
  obtain ⟨τ, H⟩ : ∃ τ, taint.checkBlock (workspaceTaint true) [.mov .ebx src] = some τ := by
    rcases hf with ⟨v, rfl⟩ | ⟨d, rfl⟩
    · exact ⟨_, rfl⟩
    · refine ⟨workspaceTaint true, ?_⟩
      rw [← VG.X86.Taint.checkBlock_erase _ _ rfl]
      change taint.checkBlock (workspaceTaint true) [.mov .ebx (.mem (sc 0))] = _
      rfl
  have C : VG.Taint.check taint (workspaceTaint true) (.block [.mov .ebx src]) (.block []) = some τ := H
  exact ⟨(VG.Taint.check_sound C A E F).1, trivial⟩

theorem coreReduce_relCT (base : Addr) (size qLen inputLen output : Nat) (input : Pointer) (src : Src)
    (hf : LenForm src) (hz : Layout.saved ≤ size) (hu : usedBytes ≤ size) (h4 : 4 ≤ qLen) (hmax : qLen ≤ 384)
    (hw4 : qLen % 4 = 0) :
    RelCT isa (fun s t => ReductionPre base size qLen inputLen input src s ∧
      ReductionPre base size qLen inputLen input src t ∧
      pointerValue base s (.input .q) = pointerValue base t (.input .q) ∧
      pointerValue base s input = pointerValue base t input ∧ s.gpr .esp = t.gpr .esp)
      (Core.reduce qLen src input output) (VG.X86.Taint.Agree (workspaceTaint true)) := by
  have hn48 : (qLen + 7) / 8 ≤ 48 := by omega
  have Hn : contextBytes ((qLen + 7) / 8) ≤ 8192 :=
    Nat.le_trans (VG.Proof.Dsa.X86.Layout.context_bound hn48) (by decide)
  have sz : 8256 ≤ size := hz
  have bound : slot ((qLen + 7) / 8) 0 + 8 * ((qLen + 7) / 8) ≤ contextBytes ((qLen + 7) / 8) := by
    have H := slot_bound (n := (qLen + 7) / 8) (i := 0) (by decide)
    simp only [stride] at H
    omega
  unfold Core.reduce
  dsimp only
  apply RelCT.assoc
  -- the modulus, then the bytes' address and length
  have loadCT := ((coreLoad_relCT ((qLen + 7) / 8) qLen (slot ((qLen + 7) / 8) 0) (.input .q) base size hz).mono
      (P' := fun (s t : State) => ReductionPre base size qLen inputLen input src s ∧
        ReductionPre base size qLen inputLen input src t ∧
        pointerValue base s (.input .q) = pointerValue base t (.input .q) ∧
        pointerValue base s input = pointerValue base t input ∧ s.gpr .esp = t.gpr .esp)
      (fun _ _ H => ⟨H.1.scr, H.2.1.scr, H.2.2.1⟩) (fun _ _ h => h)).wpDep
    (F := fun (σ u : State) => Scr u base size ∧ pointerValue base u input = pointerValue base σ input)
    fun s t ⟨P, Q, _⟩ => by
      have go : ∀ σ, ReductionPre base size qLen inputLen input src σ → WP isa
          (Core.load ((qLen + 7) / 8) qLen (slot ((qLen + 7) / 8) 0) (.input .q)) σ
          fun u => Scr u base size ∧ pointerValue base u input = pointerValue base σ input := by
        intro σ R
        refine WP.mono (coreLoad_ok R.scr hz (by omega) h4 (by omega) hw4
          R.modulusReady.toReadableComponent (R.modulusReady.slot (by decide))) fun u ⟨_, K, O⟩ => ?_
        exact ⟨R.scr.of_keeps K (by decide),
          pointerValue_keep K (by decide) (O.mono (by omega) (by omega)) Hn input⟩
      exact ⟨go s P, go t Q⟩
  have headCT := RelCT.seq loadCT (RelCT.block_append (RelCT.seq ((pointer_relCT input base size hz).mono
      (fun _ _ ⟨_, σ₁, σ₂, ⟨_, _, _, I, _⟩, ⟨S₁, E₁⟩, ⟨S₂, E₂⟩⟩ => ⟨S₁, S₂, by rw [E₁, E₂, I]⟩) (fun _ _ h => h))
    (movLen_trace hf)))
  have head := headCT.wpDep (F := fun (σ w : State) =>
      Red.CallIn ((qLen + 7) / 8)
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt σ.mem ((pointerValue base σ (.input .q)).setWidth 64) qLen))
        w base size (pointerValue base σ input) inputLen ∧ Keeps powerClob σ w)
    fun s t ⟨P, Q, _⟩ => by
      have go : ∀ σ, ReductionPre base size qLen inputLen input src σ → WP isa _ σ fun w =>
          Red.CallIn ((qLen + 7) / 8)
            (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt σ.mem ((pointerValue base σ (.input .q)).setWidth 64) qLen))
            w base size (pointerValue base σ input) inputLen ∧ Keeps powerClob σ w := fun σ R =>
        WP.mono (reduceHead_ok R.len R.scr hz R.room rfl h4 hmax hw4 R.modulusReady R.inputReady R.stack
          R.lenFit rfl R.large R.odd) fun w ⟨C, _, K⟩ => ⟨C, K⟩
      exact ⟨go s P, go t Q⟩
  have hn : 0 < (qLen + 7) / 8 := by omega
  refine RelCT.seq (R := Red.CallReady ((qLen + 7) / 8)) (head.mono (fun _ _ h => h) ?_) ?_
  · rintro w₁ w₂ ⟨_, σ₁, σ₂, ⟨_, _, _, I, SP⟩, ⟨C₁, K₁⟩, ⟨C₂, K₂⟩⟩
    rw [← I] at C₂
    refine ⟨by rw [K₁.1 _ (by decide), K₂.1 _ (by decide)]; exact SP, fun r hr => ?_, base, size, _, _, _, _, hu, C₁, C₂⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [C₁.ebx, C₂.ebx]
    · rw [C₁.esi, C₂.esi]
    · exact Red.edi_eq C₁.scr C₂.scr
  refine RelCT.seq (R := VG.X86.Taint.Agree (workspaceTaint false)) ?_ (coreStore_workspace_relCT qLen output)
  refine ((Red.call_relCT _ hn).wpDep (F := fun (σ x : State) => x.gpr .edi = σ.gpr .edi) fun s t H => ?_).mono
    (fun _ _ h => h) fun x₁ x₂ ⟨_, σ₁, σ₂, ⟨_, RG, _⟩, e₁, e₂⟩ => ?_
  · obtain ⟨_, _, _, _, _, _, _, _, U, C₁, C₂⟩ := H
    exact ⟨WP.mono (Red.call_ok C₁ U hn hn48) fun _ ⟨_, _, K⟩ => K.1 _ (by decide),
      WP.mono (Red.call_ok C₂ U hn hn48) fun _ ⟨_, _, K⟩ => K.1 _ (by decide)⟩
  · apply agree_regs (rs := [.edi])
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    rw [e₁, e₂]; exact RG _ (by simp)

end VG.Proof.Dsa.X86
