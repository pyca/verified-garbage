module

public import VerifiedGarbage.Impl.Dsa.X86.Validate
public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.Proof.Dsa.X86.CallTiming
import VerifiedGarbage.Proof.Dsa.X86.CallValidationTiming
import VerifiedGarbage.Proof.Dsa.X86.CallPowerTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Dsa.X86.Pointer
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.Dsa.X86.PointerTiming
import VerifiedGarbage.Proof.Dsa.X86.ValidationBlocksTiming
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Dsa.X86.StageMinus
public import VerifiedGarbage.Proof.Dsa.X86.StreamTiming
public import VerifiedGarbage.Proof.Dsa.X86.StageArithmetic
import VerifiedGarbage.Proof.Dsa.X86.CoreSetup
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Mont.X86.ContextFrame
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.TCB.X86.Isa
import VerifiedGarbage.TCB.X86.State
import VerifiedGarbage.Proof.Dsa.X86.Persistent
import VerifiedGarbage.Proof.Weierstrass.MontContract

/-! ### `Dsa.X86.CallReduceTiming`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86.CoreReduceTiming`, which only this module used -/

section

/-! # Complete streaming reduction calls have secret-independent traces -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/CoreStreamSource.lean`, which only this module imported.
section

/-! # The public byte-source pointer for scalar reduction -/

section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

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
  have hn48 : (qLen + 7) / 8 ≤ 48 := by omega_using [hmax]
  have Hn : contextBytes ((qLen + 7) / 8) ≤ 8192 :=
    Nat.le_trans (VG.Proof.Dsa.X86.Layout.context_bound hn48) (by decide)
  have sz : 8256 ≤ size := hz
  have bound : slot ((qLen + 7) / 8) 0 + 8 * ((qLen + 7) / 8) ≤ contextBytes ((qLen + 7) / 8) := by
    have H := slot_bound (n := (qLen + 7) / 8) (i := 0) (by decide)
    simp only [stride] at H
    omega_using [H]
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
        refine WP.mono (coreLoad_ok R.scr hz (by omega_using [Hn, sz, bound]) h4 (by omega_using []) hw4
          R.modulusReady.toReadableComponent (R.modulusReady.slot (by decide))) fun u ⟨_, K, O⟩ => ?_
        exact ⟨R.scr.of_keeps K (by decide),
          pointerValue_keep K (by decide) (O.mono (by omega_using []) (by omega_using [bound])) Hn input⟩
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
  have hn : 0 < (qLen + 7) / 8 := by omega_using [h4]
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

end

end


/-! # Streaming reduction stages retain the public call layout -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem CallReady.stream {L : CallLayout} {s : State} {p : Pointer} {len n : Nat}
    (R : CallReady L s) (O : CallOperand L p len) (hl : ∀ o, p = .local o → 0 < len) (hn : n ≤ 48) :
    StreamInput s L.base (contextBytes n) (pointerValue L.base s p) len := by
  rcases O with ⟨full, member, le⟩ | ⟨offset, rfl, lo, hi⟩
  · exact ((R.buffers (p, full) member).prefix le).stream (R.moduli.context hn)
  · exact localStream R.moduli.scr (hl _ rfl) (Nat.le_trans hi R.moduli.extent)
      (Nat.le_trans (VG.Proof.Dsa.X86.Layout.context_bound hn) (Nat.le_trans (by decide : 7048 ≤ r) lo))

theorem CallReady.stack {L : CallLayout} {s : State} {p : Pointer} {len : Nat}
    (R : CallReady L s) (O : CallOperand L p len) (hl : ∀ o, p = .local o → 0 < len) :
    Region.Disjoint ⟨(pointerValue L.base s p).setWidth 64, len⟩ (callStack (s.gpr .esp)) := by
  rcases O with ⟨full, member, le⟩ | ⟨offset, rfl, lo, hi⟩
  · exact ((R.buffers (p, full) member).prefix le).stack
  · exact localStack R.moduli.scr R.moduli.room (hl _ rfl) (Nat.le_trans hi R.moduli.extent)

theorem callReduce_relCT (L : CallLayout) (input : Pointer) (src : Src) (len output : Nat) (hf : LenForm src)
    (hsrc : ∀ s, CallReady L s → LenOperand L.base L.size ((L.qLen + 7) / 8) s src len)
    (Q : CallOperand L (.input .q) L.qLen) (I : CallOperand L input len)
    (hl : ∀ o, input = .local o → 0 < len) (hlen : len < 2 ^ 32)
    (ho : r ≤ output) (hb : output + L.qLen ≤ usedBytes) :
    RelCT isa (CallPair L) (Core.reduce L.qLen src input output) (CallPair L) := by
  have W := L.lengths
  have N : (L.qLen + 7) / 8 ≤ 48 := by omega_using [W]
  have hw4 : L.qLen % 4 = 0 := by have H := L.widths; unfold Spec.Dsa.lengthsValid at H; omega_using [H]
  have pre (s : State) (R : CallReady L s) : ReductionPre L.base L.size L.qLen len input src s := by
    refine ⟨R.moduli.scr, R.moduli.qReady, R.stream I hl N, hsrc s R, ?_, ?_, R.moduli.room, R.stack I hl, hlen⟩
    · change 255 < operandValue s L.base (.input .q) L.qLen
      rw [R.moduli.qValue]; exact R.moduli.qLarge
    · change operandValue s L.base (.input .q) L.qLen % 2 = 1
      rw [R.moduli.qValue]; exact R.moduli.qOdd
  refine call_stage (Q := VG.X86.Taint.Agree (workspaceTaint true)) ?_ ?_
  · apply (coreReduce_relCT L.base L.size L.qLen len output input src hf L.saved L.extent (by omega_using [W]) (by omega_using [W])
      hw4).mono ?_ (fun _ _ h => h)
    intro s t H
    exact ⟨pre s H.1, pre t H.2, H.pointer Q, H.pointer I, H.1.sp.trans H.2.sp.symm⟩
  · intro s R
    exact WP.mono (stageReduce_ok (hsrc s R) R.moduli (R.stream I hl N) (R.stack I hl) hlen ho hb)
      fun _ H => H.2.toStageFrame.execution (.inl ⟨ho, hb⟩)

/-- The saved digest prefix, as a length operand. -/
theorem CallReady.prefixOperand {L : CallLayout} {s : State} (R : CallReady L s) :
    LenOperand L.base L.size ((L.qLen + 7) / 8) s Core.digestPrefix L.digestPrefix :=
  LenOperand.prefix L.saved (by have := L.lengths; omega_using [this]) R.prefixLen

end VG.Proof.Dsa.X86

end

end

/-! ### `Dsa.X86.CallMinusTiming`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86.MinusTiming`, which only this module used -/

section

/-! # Constant-time formation of the fixed public modulus decrements -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem validateMinus_relCT (len amount output : Nat) (modulus : Field) (base : Addr) (size : Nat) (hz : Layout.saved ≤ size) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧
      pointerValue base s (.input modulus) = pointerValue base t (.input modulus))
      (Validate.minus len modulus amount output) (VG.X86.Taint.Agree (workspaceTaint true)) := by
  unfold Validate.minus
  dsimp only
  refine RelCT.seq (coreLoad_relCT _ _ _ _ base size hz) ?_
  exact (RelCT.seq (modulusMinus_relCT _ amount) (coreStore_workspace_relCT len output)).mono
    (fun _ _ h => taint.le_sound
      (show taint.le (workspaceTaint false) (workspaceTaint true) = true from rfl) h)
    (fun _ _ h => h)

end VG.Proof.Dsa.X86

end

end


/-! # Public modulus decrements retain the call layout -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem callMinusP_relCT (L : CallLayout) (output : Nat) (P : CallOperand L (.input .p) L.pLen)
    (ho : r ≤ output) (hb : output + L.pLen ≤ usedBytes) :
    RelCT isa (CallPair L) (Validate.minus L.pLen .p 1 output) (CallPair L) := by
  refine call_stage (Q := VG.X86.Taint.Agree (workspaceTaint true)) ?_ ?_
  · exact (validateMinus_relCT L.pLen 1 output .p L.base L.size L.saved).mono
      (fun _ _ H => ⟨H.1.moduli.scr, H.2.moduli.scr, H.pointer P⟩) (fun _ _ h => h)
  · intro s R
    exact WP.mono (stageMinusP_ok R.moduli (by have := R.moduli.pLarge; omega_using [this]) ho hb)
      fun _ H => H.2.toStageFrame.execution (.inl ⟨ho, hb⟩)

theorem callMinusQ_relCT (L : CallLayout) (output : Nat) (Q : CallOperand L (.input .q) L.qLen)
    (ho : r ≤ output) (hb : output + L.qLen ≤ usedBytes) :
    RelCT isa (CallPair L) (Validate.minus L.qLen .q 2 output) (CallPair L) := by
  refine call_stage (Q := VG.X86.Taint.Agree (workspaceTaint true)) ?_ ?_
  · exact (validateMinus_relCT L.qLen 2 output .q L.base L.size L.saved).mono
      (fun _ _ H => ⟨H.1.moduli.scr, H.2.moduli.scr, H.pointer Q⟩) (fun _ _ h => h)
  · intro s R
    exact WP.mono (stageMinusQ_ok R.moduli (by have := R.moduli.qLarge; omega_using [this]) ho hb)
      fun _ H => H.2.toStageFrame.execution (.inl ⟨ho, hb⟩)

end VG.Proof.Dsa.X86

end

end

/-! # Constant-time domain and key validation -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem CallOperand.localBuffer (L : CallLayout) (offset len : Nat)
    (lo : r ≤ offset) (hi : offset + len ≤ usedBytes) : CallOperand L (.local offset) len :=
  .inr ⟨offset, rfl, lo, hi⟩

theorem callDomain_relCT (L : CallLayout)
    (P : CallOperand L (.input .p) L.pLen) (Q : CallOperand L (.input .q) L.qLen)
    (G : CallOperand L (.input .g) L.pLen) (Y : CallOperand L (.input .y) L.pLen) :
    RelCT isa (CallPair L) (Validate.domain L.pLen L.qLen) (CallPair L) := by
  have W := L.lengths
  have T := CallOperand.localBuffer L t L.pLen (by decide) (by change 14944 + L.pLen ≤ 15712; omega_using [W])
  have U := CallOperand.localBuffer L u L.qLen (by decide) (by change 14816 + L.qLen ≤ 15712; omega_using [W])
  have A := L.aligned
  exact RelCT.seq (RelCT.seq
    (callRange_relCT L L.pLen .p (.input .g) true P G (by omega_using [W]) (by omega_using [W]) A.1)
    (callRange_relCT L L.pLen .p (.input .y) true P Y (by omega_using [W]) (by omega_using [W]) A.1))
    (RelCT.seq (callMinusP_relCT L t P (by decide) (by change 14944 + L.pLen ≤ 15712; omega_using [W]))
    (RelCT.seq (callReduce_relCT (hl := fun _ _ => by have := L.lengths; omega_using [W]) L (.local t) (.imm (BitVec.ofNat 32 L.pLen)) L.pLen u (.inl ⟨_, rfl⟩)
      (fun s _ => LenOperand.imm _ _ _ s _) Q T (by omega_using [W]) (by decide)
      (by change 14816 + L.qLen ≤ 15712; omega_using [W]))
    (RelCT.seq (callZero_relCT L L.qLen (.local u) false U (by omega_using [W]) (by omega_using [W]) A.2)
    (RelCT.seq (callMinusQ_relCT L qMinusTwo Q (by decide)
      (by change 14912 + L.qLen ≤ 15712; omega_using [W])) (RelCT.block_nil (fun _ _ h => h))))))

theorem callSubgroup_relCT (L : CallLayout)
    (P : CallOperand L (.input .p) L.pLen) (Q : CallOperand L (.input .q) L.qLen)
    (G : CallOperand L (.input .g) L.pLen) (Y : CallOperand L (.input .y) L.pLen) :
    RelCT isa (CallPair L) (Validate.subgroup L.pLen L.qLen) (CallPair L) := by
  have W := L.lengths
  have bound : t + L.pLen ≤ usedBytes := by change 14944 + L.pLen ≤ 15712; omega_using [W]
  have T := CallOperand.localBuffer L t L.pLen (by decide) bound
  have A := L.aligned
  exact RelCT.seq (callPowerP_relCT L (.input .g) (.input .q) t P G Q (by decide) bound)
    (RelCT.seq (callOne_relCT L L.pLen (.local t) T (by omega_using [W]) (by omega_using [W]) A.1)
    (RelCT.seq (callPowerP_relCT L (.input .y) (.input .q) t P Y Q (by decide) bound)
    (RelCT.seq (callOne_relCT L L.pLen (.local t) T (by omega_using [W]) (by omega_using [W]) A.1)
      (RelCT.block_nil (fun _ _ h => h)))))

theorem callPublicKey_relCT (L : CallLayout)
    (P : CallOperand L (.input .p) L.pLen) (Q : CallOperand L (.input .q) L.qLen)
    (G : CallOperand L (.input .g) L.pLen) (Y : CallOperand L (.input .y) L.pLen) :
    RelCT isa (CallPair L) (Validate.publicKey L.pLen L.qLen) (CallPair L) :=
  RelCT.seq (callDomain_relCT L P Q G Y) (callSubgroup_relCT L P Q G Y)

theorem callPrivateKey_relCT (L : CallLayout)
    (P : CallOperand L (.input .p) L.pLen) (Q : CallOperand L (.input .q) L.qLen)
    (G : CallOperand L (.input .g) L.pLen) (Y : CallOperand L (.input .y) L.pLen)
    (X : CallOperand L (.input .x) L.qLen) (K : CallOperand L (.input .nonce) L.qLen) :
    RelCT isa (CallPair L) (Validate.privateKey L.pLen L.qLen) (CallPair L) := by
  have W := L.lengths
  have bound : t + L.pLen ≤ usedBytes := by change 14944 + L.pLen ≤ 15712; omega_using [W]
  have T := CallOperand.localBuffer L t L.pLen (by decide) bound
  have A := L.aligned
  exact RelCT.seq (RelCT.seq
    (callRange_relCT L L.qLen .q (.input .x) false Q X (by omega_using [W]) (by omega_using [W]) A.2)
    (callRange_relCT L L.qLen .q (.input .nonce) false Q K (by omega_using [W]) (by omega_using [W]) A.2))
    (RelCT.seq (callPowerP_relCT L (.input .g) (.input .x) t P G X (by decide) bound)
    (RelCT.seq (callEqual_relCT L L.pLen (.local t) (.input .y) T Y (by omega_using [W]) (by omega_using [W]) A.1)
      (RelCT.block_nil (fun _ _ h => h))))

end VG.Proof.Dsa.X86
