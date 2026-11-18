module

import VerifiedGarbage.Proof.Dsa.OutputBytes
public import VerifiedGarbage.Proof.Dsa.X86.ShapeCall
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
public import VerifiedGarbage.Proof.Dsa.X86.CoreFrame
public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.Impl.Dsa.X86.Shape
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Dsa.X86.ShapeModuli
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.X86.KeyTiming
import VerifiedGarbage.Proof.Dsa.X86.PointerTiming
import VerifiedGarbage.Proof.Dsa.X86.Pointer
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Dsa.X86.FailureTiming
public import VerifiedGarbage.Proof.Dsa.X86.SignatureTiming
import VerifiedGarbage.Proof.Dsa.X86.OutputTiming
import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Impl.Dsa.X86.SignVerify
public import VerifiedGarbage.Proof.Dsa.X86.CallTiming
public import VerifiedGarbage.Proof.Dsa.X86.CallPowerTiming
public import VerifiedGarbage.Proof.Dsa.Accepted
public import VerifiedGarbage.Proof.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Dsa.X86.Execution
public import VerifiedGarbage.Proof.Dsa.X86.Moduli
import VerifiedGarbage.Proof.Dsa.X86.PrivateKey
import VerifiedGarbage.Proof.Dsa.X86.StageChecks
import VerifiedGarbage.Proof.Dsa.X86.Persistent
import VerifiedGarbage.Proof.Dsa.X86.StageArithmetic
import VerifiedGarbage.Proof.Dsa.X86.StagePower
import VerifiedGarbage.Proof.Weierstrass.MontContract
public import VerifiedGarbage.Impl.Dsa.X86.Arith
import VerifiedGarbage.Proof.Dsa.X86.StackFrame
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Dsa.X86.EntryTiming
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Impl.Dsa.Layout
import VerifiedGarbage.Proof.Dsa.X86.Layout
public import VerifiedGarbage.Impl.Dsa.X86.Arithmetic
import VerifiedGarbage.Proof.Mont.X86.ExponentTiming

/-! ### `Dsa.X86.BodyTiming`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86.VerifyTiming`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86.CallProductTiming`, which only this module used -/

section

/-! ### `Dsa.X86.CoreProductTiming`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86.ArithmeticTiming`, which only this module used -/

section

/-! # Constant-time ordinary modular products and sums -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86 VG.Proof.Mont.X86.Dynamic

theorem ordinaryMul_relCT (n : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (ordinaryMul n)
      (VG.X86.Taint.Agree (workspaceTaint false)) :=
  checkedProgramChange (τ' := rowTaint false) (hint := .seq (workspaceTaint false) (mulHint false) (mulHint false))
    (exponent_check_seq taint (mul_check false _ _ _ _ _ _) (by rfl) (mul_check false _ _ _ _ _ _)) rfl

theorem ordinaryAdd_relCT (n : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint true)) (ordinaryAdd n)
      (VG.X86.Taint.Agree (workspaceTaint true)) :=
  checkedProgramChange (hint := addHint true) (add_check true _ _ _ _ _) rfl

end VG.Proof.Dsa.X86

end

end

/-! ### `Dsa.X86.MulTiming`, which only this module used -/

section

/-! # Traces of the IA-32 DSA product and of its calls

Two runs from the same stack pointer and working space leak the same trace:
the saves read the argument and store through public pointers, and the
context's setup, the product and the restores are checked by taint, which
the values of the numbers do not reach. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Mul
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Impl.Dsa.X86.Arith VG.Proof.Mont.X86.Dynamic

theorem body_relCT (n : Nat) :
    RelCT isa (fun s t => s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧
      readSrc s (.mem (at_ .esp 4)) = some (arg s 0) ∧
      readSrc t (.mem (at_ .esp 4)) = some (arg t 0))
      (mulBody n) (fun _ _ => True) := by
  unfold mulBody
  have saveCT : RelCT isa (fun s t => s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧
      readSrc s (.mem (at_ .esp 4)) = some (arg s 0) ∧
      readSrc t (.mem (at_ .esp 4)) = some (arg t 0))
      (.block VG.Impl.Dsa.X86.Pow.save) (VG.X86.Taint.Agree (workspaceTaint false)) := by
    unfold VG.Impl.Dsa.X86.Pow.save
    rw [List.append_assoc]
    exact RelCT.block_append (RelCT.seq (scratchArgument_relCT 0)
      (checkedProgramChange (σ := workspaceTaint false) (hint := .block []) rfl rfl))
  refine RelCT.seq saveCT (RelCT.seq (contextSetup_relCT n) (RelCT.seq (ordinaryMul_relCT n) ?_))
  exact (checkedProgramChange (σ := { regs := .ofList [], flags := false }) (hint := .block []) (by rfl) rfl).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)

theorem body_readArg {n : Nat} {s t : State} {tr : List Leak}
    (E : Exec isa (mulBody n) s tr t) :
    readSrc s (.mem (at_ .esp 4)) = some (arg s 0) := by
  change s.load32 (argAddr s 0) = some (arg s 0)
  unfold State.load32
  split
  · rfl
  · rename_i h
    cases E with
    | seq E _ =>
      cases E with
      | block H =>
        simp only [VG.Impl.Dsa.X86.Pow.save, VG.Impl.Dsa.X86.Pow.slots, List.map_cons, List.map_nil,
          List.cons_append, List.nil_append, execBlock, isa, exec, readSrc, State.load32] at H
        simp only [show s.ea (at_ .esp 4) = argAddr s 0 from rfl, h, ↓reduceIte, Option.map_none] at H
        cases H

theorem framed_relCT (n : Nat) :
    RelCT isa (fun s t => s.gpr .esp = t.gpr .esp ∧ s.gpr .edi = t.gpr .edi ∧ 12 ≤ (s.gpr .esp).toNat)
      (.frame (.push [.eax, .edi]) (.call (mulName n) (mulBody n)) (.pop .eax 2))
      (fun _ _ => True) := by
  refine RelCT.frame (R := fun _ _ => True) (fun _ _ H => H.1) ?_
  rintro _ _ tr ur sf tf ⟨s, t, ⟨SP, DI, fit⟩, rfl, rfl⟩ E F
  cases E with
  | call C E R =>
    cases F with
    | call D F S =>
      rw [call_callEntry, Option.some.injEq] at C D
      subst C D
      have sp : (pushed [Reg.eax, .edi] s).callEntry.gpr .esp =
          (pushed [Reg.eax, .edi] t).callEntry.gpr .esp := by
        rw [callEntry_esp', callEntry_esp', SP]
      have args : arg (pushed [Reg.eax, .edi] s).callEntry 0 =
          arg (pushed [Reg.eax, .edi] t).callEntry 0 := by
        rw [callEntry_arg (rs := [.eax, .edi]) (s := s) fit (by decide) (by decide),
          callEntry_arg (rs := [.eax, .edi]) (s := t) (by rw [← SP]; exact fit) (by decide) (by decide)]
        exact DI
      have traces := (body_relCT n) _ _ _ _ _ _ ⟨sp, args, body_readArg E, body_readArg F⟩ E F
      have r := (ret_gpr R .esp).1
      have q := (ret_gpr S .esp).1
      refine ⟨?_, trivial⟩
      simp only [r, q, State.callEntry_esp, pushed_esp, SP, traces.1]

theorem call_relCT (n : Nat) :
    RelCT isa (fun s t => s.gpr .esp = t.gpr .esp ∧ s.gpr .edi = t.gpr .edi ∧ 12 ≤ (s.gpr .esp).toNat)
      (mulCall n) (fun _ _ => True) := by
  unfold mulCall
  refine RelCT.seq ?_ (framed_relCT n)
  intro s t tr ur sf tf H E F
  have W (s : State) : WP isa (.block [.mov .eax (.imm (BitVec.ofNat 32 (contextBytes n / 8)))]) s
      (fun t => VG.Proof.Mont.X86.Keeps [.eax] s t ∧ t.mem = s.mem) :=
    wp_movS rfl fun _ U _ => WP.block_nil ⟨U.keeps, U.mem⟩
  have K := wp_result (W s) E
  have L := wp_result (W t) F
  refine ⟨?_, ?_⟩
  · cases E with
    | block E => cases F with
      | block F =>
        simp only [execBlock, isa, exec, readSrc, Option.map_some, addrs, srcAddrs, List.map_nil,
          List.nil_append, Option.some.injEq, Prod.mk.injEq] at E F
        exact E.2.symm.trans F.2
  · dsimp only
    rw [K.1.1 .esp (by decide), L.1.1 .esp (by decide), K.1.1 .edi (by decide), L.1.1 .edi (by decide)]
    exact ⟨H.1, H.2.1, H.2.2⟩

end VG.Proof.Dsa.X86.Mul

end

end


/-! # Complete modular products have secret-independent execution traces -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem productTail_relCT (base : Addr) (size n len output : Nat)
    (hz : contextBytes n ≤ size) (hu : usedBytes ≤ size) (hn : 0 < n) (hn48 : n ≤ 48) :
    RelCT isa (PowerPair base size n) (.seq (Arith.mulCall n) (Core.store len output))
      (VG.X86.Taint.Agree (workspaceTaint true)) := by
  refine RelCT.seq ?_ (coreStore_workspace_relCT len output)
  intro s t tr ur sf tf ⟨S, T, SP⟩ E F
  have DI : s.gpr .edi = t.gpr .edi := BitVec.eq_of_toNat_eq (S.scr.edi_toNat.trans T.scr.edi_toNat.symm)
  have CT := (Mul.call_relCT n) _ _ _ _ _ _ ⟨SP, DI, by have := S.room.1; omega_using [this]⟩ E F
  obtain ⟨_, _, K⟩ := wp_result (Mul.call_ok S.scr S.room hz hu hn hn48 rfl S.large S.odd) E
  obtain ⟨_, _, L⟩ := wp_result (Mul.call_ok T.scr T.room hz hu hn hn48 rfl T.large T.odd) F
  refine ⟨CT.1, agree_regs (rs := [.edi]) ?_⟩
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  rw [K.1 .edi (by decide), L.1 .edi (by decide), DI]

theorem coreProductMod_relCT (base : Addr) (size len output : Nat) (modulus : Field) (a b : Pointer)
    (hz : Layout.saved ≤ size) (hu : usedBytes ≤ size) (h4 : 4 ≤ len) (hmax : len ≤ 384)
    (hw4 : len % 4 = 0) :
    RelCT isa (PowerAgree base size len len modulus a b)
      (Core.productMod len modulus a b output) (VG.X86.Taint.Agree (workspaceTaint true)) := by
  have hn : (len + 7) / 8 ≤ 48 := by omega_using [hmax]
  have cb := VG.Proof.Dsa.X86.Layout.context_bound hn
  have sz : 8256 ≤ size := hz
  unfold Core.productMod
  dsimp only
  refine RelCT.seq ?_ (productTail_relCT base size _ len output (by omega_using [cb, sz]) hu (by omega_using [h4]) hn)
  have H := (powerHead_relCT base size len len modulus a b hz h4 hmax hw4).mono
    (fun _ _ (P : PowerAgree base size len len modulus a b _ _) => P.1) (fun _ _ A => A)
  refine (H.wpDep (F := fun s t => PowerReady base size ((len + 7) / 8) t ∧ Keeps loadClob s t)
    (fun s t P => ⟨powerHead_ok P.1.1 P.2.1 hz h4 hmax h4 (Nat.le_refl _) hw4 hw4,
      powerHead_ok P.1.2.1 P.2.2.1 hz h4 hmax h4 (Nat.le_refl _) hw4 hw4⟩)).mono (fun _ _ P => P) ?_
  rintro s t ⟨_, a, b, P, ⟨S, K⟩, ⟨T, L⟩⟩
  exact ⟨S, T, (K.1 .esp (by decide)).trans (P.2.2.2.trans (L.1 .esp (by decide)).symm)⟩

theorem coreSum_relCT (base : Addr) (size len output : Nat) (a b : Pointer)
    (hz : Layout.saved ≤ size) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0) :
    RelCT isa (ArithmeticAgree base size len len .q a b)
      (Core.sum len a b output) (VG.X86.Taint.Agree (workspaceTaint true)) := by
  unfold Core.sum
  dsimp only
  apply RelCT.assoc
  refine RelCT.seq (arithmeticHead_relCT base size len len .q a b hz h4 hmax hw4) ?_
  refine RelCT.seq (ordinaryAdd_relCT _) ?_
  exact (coreStore_workspace_relCT len output).mono
    (fun _ _ h => taint.le_sound (show taint.le (workspaceTaint false) (workspaceTaint true) = true from rfl) h)
    (fun _ _ h => h)

end VG.Proof.Dsa.X86

end

end

/-! # Product stages retain public layout and caller operands -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem callProductP_relCT (L : CallLayout) (a b : Pointer) (output : Nat)
    (P : CallOperand L (.input .p) L.pLen) (A : CallOperand L a L.pLen) (B : CallOperand L b L.pLen)
    (ho : r ≤ output) (hb : output + L.pLen ≤ usedBytes) :
    RelCT isa (CallPair L) (Core.productMod L.pLen .p a b output) (CallPair L) := by
  have W := L.lengths
  refine call_stage (Q := VG.X86.Taint.Agree (workspaceTaint true)) ?_ ?_
  · apply (coreProductMod_relCT L.base L.size L.pLen output .p a b L.saved L.extent (by omega_using [W]) (by omega_using [W])
      L.aligned.1).mono ?_ (fun _ _ h => h)
    intro s t H
    exact ⟨⟨H.1.arithmeticP A B (by omega_using [W]), H.2.arithmeticP A B (by omega_using [W]), H.pointer P, H.pointer A, H.pointer B⟩,
      H.1.moduli.room, H.2.moduli.room, H.1.sp.trans H.2.sp.symm⟩
  · intro s R
    exact WP.mono (stageProductP_ok R.moduli (R.operand A (by omega_using [W]) (by omega_using [W]))
      (R.operand B (by omega_using [W]) (by omega_using [W])) ho hb) fun _ H => H.2.toStageFrame.execution (.inl ⟨ho, hb⟩)

theorem callProductQ_relCT (L : CallLayout) (a b : Pointer) (output : Nat)
    (Q : CallOperand L (.input .q) L.qLen) (A : CallOperand L a L.qLen) (B : CallOperand L b L.qLen)
    (ho : r ≤ output) (hb : output + L.qLen ≤ usedBytes) :
    RelCT isa (CallPair L) (Core.product L.qLen a b output) (CallPair L) := by
  have W := L.lengths
  refine call_stage (Q := VG.X86.Taint.Agree (workspaceTaint true)) ?_ ?_
  · apply (coreProductMod_relCT L.base L.size L.qLen output .q a b L.saved L.extent (by omega_using [W]) (by omega_using [W])
      L.aligned.2).mono ?_ (fun _ _ h => h)
    intro s t H
    exact ⟨⟨H.1.arithmeticQ A B, H.2.arithmeticQ A B, H.pointer Q, H.pointer A, H.pointer B⟩,
      H.1.moduli.room, H.2.moduli.room, H.1.sp.trans H.2.sp.symm⟩
  · intro s R
    exact WP.mono (stageProduct_ok R.moduli (R.operand A (by omega_using [W]) (by omega_using [W]))
      (R.operand B (by omega_using [W]) (by omega_using [W])) ho hb) fun _ H => H.2.toStageFrame.execution (.inl ⟨ho, hb⟩)

end VG.Proof.Dsa.X86

end

end

/-! ### `Dsa.X86.SignTiming`, which the modules that import this one used -/

section

/-! ### `Dsa.X86.SignFinishTiming`, which only this module used -/

section

/-! # Constant-time signing arithmetic with reduced addition operands -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

def SumReady (L : CallLayout) (s : State) : Prop :=
  operandValue s L.base (.local z) L.qLen < L.q ∧ operandValue s L.base (.local u) L.qLen < L.q

theorem signSumInputs_ok (L : CallLayout)
    (X : CallOperand L (.input .x) L.qLen) (D : CallOperand L (.input .digest) L.digestPrefix)
    (hd : L.digestPrefix < 2 ^ 32) (s0 : State) (R : CallReady L s0) :
    WP isa (.seq (Core.product L.qLen (.input .x) (.local r) u)
      (Core.reduce L.qLen Core.digestPrefix (.input .digest) z)) s0 (SumReady L) := by
  have W := L.lengths
  have N : (L.qLen + 7) / 8 ≤ 48 := by omega_using [W]
  have qp : 0 < L.q := by have := R.moduli.qLarge; omega_using [this]
  refine WP.seq (WP.mono (stageProduct_ok R.moduli (R.operand X (by omega_using [W]) N)
    (R.moduli.scalarReady (by decide) N) (by decide) (R.moduli.scalarFit (by decide))) fun s1 ⟨M1, F1⟩ => ?_)
  have R1 := R.keep (F1.toStageFrame.execution (.inl ⟨by decide, R.moduli.scalarFit (by decide)⟩))
  have U1 := F1.scalar_value R.moduli (by decide) (Nat.lt_trans (Nat.mod_lt _ qp) R.moduli.valueBounds.2)
  refine WP.mono (stageReduce_ok R1.prefixOperand M1 (R1.stream D (fun _ h => by cases h) N) (R1.stack D (fun _ h => by cases h)) hd (by decide) (M1.scalarFit (by decide))) fun s2 ⟨_, F2⟩ => ?_
  constructor
  · rw [F2.scalar_value M1 (by decide) (Nat.lt_trans (Nat.mod_lt _ qp) M1.valueBounds.2)]
    exact Nat.mod_lt _ qp
  · rw [F2.toStageFrame.scalar_keep M1 (by decide) (by decide) (by decide), U1]
    exact Nat.mod_lt _ qp

theorem signSum_relCT (L : CallLayout) (Q : CallOperand L (.input .q) L.qLen) :
    RelCT isa (fun s t => CallPair L s t ∧ SumReady L s ∧ SumReady L t)
      (Core.sum L.qLen (.local z) (.local u) v) (CallPair L) := by
  have W := L.lengths
  have Z := CallOperand.localBuffer L z L.qLen (by decide) (by change 14880 + L.qLen ≤ 15712; omega_using [W])
  have U := CallOperand.localBuffer L u L.qLen (by decide) (by change 14816 + L.qLen ≤ 15712; omega_using [W])
  have CT := coreSum_relCT L.base L.size L.qLen v (.local z) (.local u) L.saved (by omega_using [W]) (by omega_using [W]) L.aligned.2
  intro s t tr ur sf tf ⟨H, S, T⟩ E F
  have A : ArithmeticAgree L.base L.size L.qLen L.qLen .q (.local z) (.local u) s t :=
    ⟨H.1.arithmeticQ Z U, H.2.arithmeticQ Z U, H.pointer Q, H.pointer Z, H.pointer U⟩
  have frame (s : State) (R : CallReady L s) (B : SumReady L s) :
      WP isa (Core.sum L.qLen (.local z) (.local u) v) s (CallReady L) := by
    exact WP.mono (stageSum_ok R.moduli (R.operand Z (by omega_using [W]) (by omega_using [W]))
      (R.operand U (by omega_using [W]) (by omega_using [W])) B.1 B.2 (by decide) (R.moduli.scalarFit (by decide)))
      fun _ H => R.keep (H.2.toStageFrame.execution (.inl ⟨by decide, R.moduli.scalarFit (by decide)⟩))
  exact ⟨(CT _ _ _ _ _ _ A E F).1, wp_result (frame s H.1 S) E, wp_result (frame t H.2 T) F⟩

theorem callSignFinish_relCT (L : CallLayout)
    (Q : CallOperand L (.input .q) L.qLen) (X : CallOperand L (.input .x) L.qLen)
    (D : CallOperand L (.input .digest) L.digestPrefix) (hd : L.digestPrefix < 2 ^ 32) :
    RelCT isa (CallPair L) (Core.signFinish L.qLen) (CallPair L) := by
  have W := L.lengths
  have R := CallOperand.localBuffer L r L.qLen (by decide) (by change 14720 + L.qLen ≤ 15712; omega_using [W])
  have I := CallOperand.localBuffer L inverse L.qLen (by decide) (by change 14784 + L.qLen ≤ 15712; omega_using [W])
  have V := CallOperand.localBuffer L v L.qLen (by decide) (by change 14848 + L.qLen ≤ 15712; omega_using [W])
  unfold Core.signFinish Core.sequence
  dsimp only [List.foldr]
  apply RelCT.assoc
  refine RelCT.seq ((RelCT.seq
    (callProductQ_relCT L (.input .x) (.local r) u Q X R (by decide) (by change 14816 + L.qLen ≤ 15712; omega_using [W]))
    (callReduce_relCT (hl := fun _ h => by cases h) L (.input .digest) Core.digestPrefix L.digestPrefix z (.inr ⟨_, rfl⟩)
      (fun _ R => R.prefixOperand) Q D hd (by decide) (by change 14880 + L.qLen ≤ 15712; omega_using [W]))).wp
    (fun s t H => ⟨signSumInputs_ok L X D hd s H.1, signSumInputs_ok L X D hd t H.2⟩)) ?_
  exact RelCT.seq (signSum_relCT L Q)
    (RelCT.seq (callProductQ_relCT L (.local inverse) (.local v) VG.Impl.Dsa.Layout.s Q I V
      (by decide) (by change 14752 + L.qLen ≤ 15712; omega_using [W])) (RelCT.block_nil (fun _ _ h => h)))

end VG.Proof.Dsa.X86

end

end


/-! # Constant-time signing computation -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem callSignStart_relCT (L : CallLayout)
    (P : CallOperand L (.input .p) L.pLen) (Q : CallOperand L (.input .q) L.qLen)
    (G : CallOperand L (.input .g) L.pLen) (K : CallOperand L (.input .nonce) L.qLen) :
    RelCT isa (CallPair L) (Core.signStart L.pLen L.qLen) (CallPair L) := by
  have W := L.lengths
  have T := CallOperand.localBuffer L t L.pLen (by decide) (by change 14944 + L.pLen ≤ 15712; omega_using [W])
  have E := CallOperand.localBuffer L qMinusTwo L.qLen (by decide) (by change 14912 + L.qLen ≤ 15712; omega_using [W])
  exact RelCT.seq (callPowerP_relCT L (.input .g) (.input .nonce) t P G K (by decide)
    (by change 14944 + L.pLen ≤ 15712; omega_using [W]))
    (RelCT.seq (callReduce_relCT (hl := fun _ _ => by have := L.lengths; omega_using [W]) L (.local t) (.imm (BitVec.ofNat 32 L.pLen)) L.pLen r (.inl ⟨_, rfl⟩)
      (fun s _ => LenOperand.imm _ _ _ s _) Q T (by omega_using [W]) (by decide)
      (by change 14720 + L.qLen ≤ 15712; omega_using [W]))
    (RelCT.seq (callPowerQ_relCT L (.input .nonce) (.local qMinusTwo) inverse Q K E (by decide)
      (by change 14784 + L.qLen ≤ 15712; omega_using [W])) (RelCT.block_nil (fun _ _ h => h))))

theorem callSign_relCT (L : CallLayout)
    (P : CallOperand L (.input .p) L.pLen) (Q : CallOperand L (.input .q) L.qLen)
    (G : CallOperand L (.input .g) L.pLen) (K : CallOperand L (.input .nonce) L.qLen)
    (X : CallOperand L (.input .x) L.qLen) (D : CallOperand L (.input .digest) L.digestPrefix)
    (hd : L.digestPrefix < 2 ^ 32) :
    RelCT isa (CallPair L) (Core.sign L.pLen L.qLen) (CallPair L) :=
  RelCT.seq (callSignStart_relCT L P Q G K) (callSignFinish_relCT L Q X D hd)

theorem callSignCompute_relCT (L : CallLayout)
    (P : CallOperand L (.input .p) L.pLen) (Q : CallOperand L (.input .q) L.qLen)
    (G : CallOperand L (.input .g) L.pLen) (Y : CallOperand L (.input .y) L.pLen)
    (K : CallOperand L (.input .nonce) L.qLen) (X : CallOperand L (.input .x) L.qLen)
    (D : CallOperand L (.input .digest) L.digestPrefix) (hd : L.digestPrefix < 2 ^ 32) :
    RelCT isa (CallPair L) (SignVerify.signCompute L.pLen L.qLen) (CallPair L) := by
  have W := L.lengths
  have R := CallOperand.localBuffer L r L.qLen (by decide) (by change 14720 + L.qLen ≤ 15712; omega_using [W])
  have S := CallOperand.localBuffer L s L.qLen (by decide) (by change 14752 + L.qLen ≤ 15712; omega_using [W])
  exact RelCT.seq (callPublicKey_relCT L P Q G Y)
    (RelCT.seq (callPrivateKey_relCT L P Q G Y X K)
    (RelCT.seq (callSign_relCT L P Q G K X D hd)
    (RelCT.seq (RelCT.seq
      (callZero_relCT L L.qLen (.local r) true R (by omega_using [W]) (by omega_using [W]) L.aligned.2)
      (callZero_relCT L L.qLen (.local s) true S (by omega_using [W]) (by omega_using [W]) L.aligned.2))
      (RelCT.block_nil (fun _ _ h => h)))))

end VG.Proof.Dsa.X86

end

end

/-! ### `Dsa.X86.SignCompute`, which the modules that import this one used -/

section

/-! # Signing arithmetic and all post-shape acceptance conditions -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/SignFinish.lean`, which only this module imported.
section

/-! # The remaining scalar arithmetic of a signing attempt -/

section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem signFinish_ok {base : Addr} {size pLen qLen p q digestLen x digest rv inv : Nat} {s0 : State}
    (M : Moduli base size pLen qLen p q s0)
    (X : CallerBuffer s0 base size (.input .x) qLen) (D : CallerBuffer s0 base size (.input .digest) digestLen)
    (hd : digestLen ≤ 32)
    (hP : pointerValue base s0 (.input .digestPrefixLen) = BitVec.ofNat 32 digestLen)
    (hx : operandValue s0 base (.input .x) qLen = x) (hD : operandValue s0 base (.input .digest) digestLen = digest)
    (hr : operandValue s0 base (.local r) qLen = rv)
    (hi : operandValue s0 base (.local VG.Impl.Dsa.Layout.inverse) qLen = inv) :
    WP isa (Core.signFinish qLen) s0 fun s4 =>
      Moduli base size pLen qLen p q s4 ∧ operandValue s4 base (.local r) qLen = rv ∧
      operandValue s4 base (.local VG.Impl.Dsa.Layout.s) qLen = inv * ((digest % q + x * rv % q) % q) % q ∧
      Execution base s0 s4 ∧
      flagW base (Layout.field .mask) s4 = flagW base (Layout.field .mask) s0 := by
  have L := M.lengths
  obtain nq : (qLen + 7) / 8 ≤ 48 := by omega
  obtain qp : 0 < q := by have := M.qLarge; omega
  unfold Core.signFinish Core.sequence
  dsimp only [List.foldr]
  refine WP.seq (WP.mono (stageProduct_ok M (X.ready (M.context nq)) (M.scalarReady (by decide) nq)
    (by decide) (M.scalarFit (by decide))) fun s1 ⟨M1, R1⟩ => ?_)
  obtain E1 := R1.toStageFrame.execution (.inl ⟨by decide, M.scalarFit (by decide)⟩)
  obtain U1 : operandValue s1 base (.local u) qLen = x * rv % q := by
    obtain V := R1.scalar_value M (by decide) (Nat.lt_trans (Nat.mod_lt _ qp) M.valueBounds.2)
    rw [hx, hr] at V
    exact V
  obtain D1 := E1.buffer D (by decide)
  refine WP.seq (WP.mono (stageReduce_ok (LenOperand.prefix M1.saved nq (E1.prefixLen.trans hP)) M1 (D1.stream (M1.context nq)) D1.stack (by omega)
    (by decide) (M1.scalarFit (by decide))) fun s2 ⟨M2, R2⟩ => ?_)
  obtain E2 := R2.toStageFrame.execution (.inl ⟨by decide, M1.scalarFit (by decide)⟩)
  obtain E12 := E1.trans E2
  obtain Z2 : operandValue s2 base (.local z) qLen = digest % q := by
    obtain V := R2.scalar_value M1 (by decide) (Nat.lt_trans (Nat.mod_lt _ qp) M.valueBounds.2)
    rw [E1.value D (by decide) M.extent, hD] at V
    exact V
  obtain U2 : operandValue s2 base (.local u) qLen = x * rv % q := by
    rw [R2.toStageFrame.scalar_keep M1 (by decide) (by decide) (by decide), U1]
  refine WP.seq (WP.mono (stageSum_ok M2 (M2.scalarReady (by decide) nq) (M2.scalarReady (by decide) nq)
    (by rw [Z2]; exact Nat.mod_lt _ qp) (by rw [U2]; exact Nat.mod_lt _ qp)
    (by decide) (M2.scalarFit (by decide))) fun s3 ⟨M3, R3⟩ => ?_)
  obtain E3 := R3.toStageFrame.execution (.inl ⟨by decide, M2.scalarFit (by decide)⟩)
  obtain E123 := E12.trans E3
  obtain V3 : operandValue s3 base (.local v) qLen = (digest % q + x * rv % q) % q := by
    obtain V := R3.scalar_value M2 (by decide) (Nat.lt_trans (Nat.mod_lt _ qp) M.valueBounds.2)
    rw [Z2, U2] at V
    exact V
  obtain I3 : operandValue s3 base (.local VG.Impl.Dsa.Layout.inverse) qLen = inv := by
    rw [R3.toStageFrame.scalar_keep M2 (by decide) (by decide) (by decide),
      R2.toStageFrame.scalar_keep M1 (by decide) (by decide) (by decide),
      R1.toStageFrame.scalar_keep M (by decide) (by decide) (by decide), hi]
  refine WP.seq (WP.mono (stageProduct_ok M3 (M3.scalarReady (by decide) nq) (M3.scalarReady (by decide) nq)
    (by decide) (M3.scalarFit (by decide))) fun s4 ⟨M4, R4⟩ => ?_)
  refine WP.block_nil ⟨M4, ?_, ?_, ⟨E123.trans (R4.toStageFrame.execution (.inl ⟨by decide, M3.scalarFit (by decide)⟩)), ?_⟩⟩
  · rw [R4.toStageFrame.scalar_keep M3 (by decide) (by decide) (by decide),
      R3.toStageFrame.scalar_keep M2 (by decide) (by decide) (by decide),
      R2.toStageFrame.scalar_keep M1 (by decide) (by decide) (by decide),
      R1.toStageFrame.scalar_keep M (by decide) (by decide) (by decide), hr]
  · have V := R4.scalar_value M3 (by decide) (Nat.lt_trans (Nat.mod_lt _ qp) M.valueBounds.2)
    rw [I3, V3] at V
    exact V

  · rw [R4.toStageFrame.mask_keep (by decide), R3.toStageFrame.mask_keep (by decide), R2.toStageFrame.mask_keep (by decide), R1.toStageFrame.mask_keep (by decide)]

end VG.Proof.Dsa.X86
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/SignStart.lean`, which only this module imported.
section

/-! # The nonce power, reduced r, and Fermat inverse in signing -/

section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem signStart_ok {base : Addr} {size pLen qLen p q g k : Nat} {s0 : State}
    (M : Moduli base size pLen qLen p q s0)
    (G : CallerBuffer s0 base size (.input .g) pLen) (K : CallerBuffer s0 base size (.input .nonce) qLen)
    (hg : operandValue s0 base (.input .g) pLen = g) (hk : operandValue s0 base (.input .nonce) qLen = k)
    (hq2 : operandValue s0 base (.local qMinusTwo) qLen = q - 2) :
    WP isa (Core.signStart pLen qLen) s0 fun s3 =>
      Moduli base size pLen qLen p q s3 ∧
      operandValue s3 base (.local r) qLen = g ^ k % p % q ∧
      operandValue s3 base (.local VG.Impl.Dsa.Layout.inverse) qLen = k ^ (q - 2) % q ∧
      Execution base s0 s3 ∧
      flagW base (Layout.field .mask) s3 = flagW base (Layout.field .mask) s0 := by
  have L := M.lengths
  have A := M.aligned
  obtain np : (pLen + 7) / 8 ≤ 48 := by omega
  obtain nq : (qLen + 7) / 8 ≤ 48 := by omega
  obtain qp : 0 < q := by have := M.qLarge; omega
  obtain pp : 0 < p := by have := M.pLarge; omega
  unfold Core.signStart Core.sequence
  dsimp only [List.foldr]
  refine WP.seq (WP.mono (stagePowerP_ok M (G.ready (M.context np)) (K.ready (M.context np))
    (by decide) (M.wideFit (by decide))) fun s1 ⟨M1, R1⟩ => ?_)
  obtain E1 := R1.toStageFrame.execution (.inl ⟨by decide, M.wideFit (by decide)⟩)
  obtain V1 : operandValue s1 base (.local VG.Impl.Dsa.Layout.t) pLen = g ^ k % p := by
    obtain V := R1.wide_value M (by decide) (Nat.lt_trans (Nat.mod_lt _ pp) M.valueBounds.1)
    rw [hg, hk] at V
    exact V
  refine WP.seq (WP.mono (stageReduce_ok (LenOperand.imm _ _ _ _ _) M1 (M1.wideStream (by decide) nq) (M1.wideStack (by decide)) (by omega)
    (by decide) (M1.scalarFit (by decide))) fun s2 ⟨M2, R2⟩ => ?_)
  obtain E2 := R2.toStageFrame.execution (.inl ⟨by decide, M1.scalarFit (by decide)⟩)
  obtain E12 := E1.trans E2
  obtain V2 : operandValue s2 base (.local r) qLen = g ^ k % p % q := by
    obtain V := R2.scalar_value M1 (by decide) (Nat.lt_trans (Nat.mod_lt _ qp) M.valueBounds.2)
    rw [V1] at V
    exact V
  obtain Q2 : operandValue s2 base (.local qMinusTwo) qLen = q - 2 := by
    rw [R2.toStageFrame.scalar_keep M1 (by decide) (by decide) (by decide),
      R1.toStageFrame.scalar_keep_wide M (by decide) (by decide), hq2]
  obtain K2 := E12.buffer K (by decide)
  obtain VK2 : operandValue s2 base (.input .nonce) qLen = k := (E12.value K (by decide) M.extent).trans hk
  refine WP.seq (WP.mono (stagePowerQ_ok M2 (K2.ready (M2.context nq))
    (M2.scalarReady (by decide) nq) (by decide) (M2.scalarFit (by decide))) fun s3 ⟨M3, R3⟩ => ?_)
  refine WP.block_nil ⟨M3, ?_, ?_, ⟨E12.trans (R3.toStageFrame.execution (.inl ⟨by decide, M2.scalarFit (by decide)⟩)), ?_⟩⟩
  · rw [R3.toStageFrame.scalar_keep M2 (by decide) (by decide) (by decide), V2]
  · have V := R3.scalar_value M2 (by decide) (Nat.lt_trans (Nat.mod_lt _ qp) M.valueBounds.2)
    rw [VK2, Q2] at V
    exact V

  · rw [R3.toStageFrame.mask_keep (by decide), R2.toStageFrame.mask_keep (by decide), R1.toStageFrame.mask_keep (by decide)]

end VG.Proof.Dsa.X86
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/SignArithmetic.lean`, which only this module imported.
section

/-! # Complete arithmetic schedule of an x86 DSA signing attempt -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem signArithmetic_ok {base : Addr} {size pLen qLen p q g k x digestLen digest : Nat} {s0 : State}
    (M : Moduli base size pLen qLen p q s0)
    (G : CallerBuffer s0 base size (.input .g) pLen)
    (K : CallerBuffer s0 base size (.input .nonce) qLen)
    (X : CallerBuffer s0 base size (.input .x) qLen)
    (D : CallerBuffer s0 base size (.input .digest) digestLen)
    (hd : digestLen ≤ 32)
    (hP : pointerValue base s0 (.input .digestPrefixLen) = BitVec.ofNat 32 digestLen)
    (hg : operandValue s0 base (.input .g) pLen = g)
    (hk : operandValue s0 base (.input .nonce) qLen = k)
    (hx : operandValue s0 base (.input .x) qLen = x)
    (hD : operandValue s0 base (.input .digest) digestLen = digest)
    (hq2 : operandValue s0 base (.local qMinusTwo) qLen = q - 2) :
    WP isa (Core.sign pLen qLen) s0 fun sf =>
      Moduli base size pLen qLen p q sf ∧
      operandValue sf base (.local r) qLen = g ^ k % p % q ∧
      operandValue sf base (.local VG.Impl.Dsa.Layout.s) qLen =
        k ^ (q - 2) % q * ((digest % q + x * (g ^ k % p % q) % q) % q) % q ∧
      Execution base s0 sf ∧
      flagW base (Layout.field .mask) sf = flagW base (Layout.field .mask) s0 := by
  unfold Core.sign
  refine WP.seq (WP.mono (signStart_ok M G K hg hk hq2) fun s1 ⟨M1, R1, I1, E1, F1⟩ => ?_)
  refine WP.mono (signFinish_ok M1 (E1.buffer X (by decide)) (E1.buffer D (by decide)) hd (E1.prefixLen.trans hP)
    ((E1.value X (by decide) M.extent).trans hx)
    ((E1.value D (by decide) M.extent).trans hD) R1 I1) ?_
  intro sf H
  exact ⟨H.1, H.2.1, H.2.2.1, E1.trans H.2.2.2.1, H.2.2.2.2.trans F1⟩

end VG.Proof.Dsa.X86
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem signCompute_ok {base : Addr} {size pLen qLen p q g y x k digestLen digest : Nat} {s0 : State}
    (M : Moduli base size pLen qLen p q s0)
    (G : CallerBuffer s0 base size (.input .g) pLen)
    (Y : CallerBuffer s0 base size (.input .y) pLen)
    (X : CallerBuffer s0 base size (.input .x) qLen)
    (K : CallerBuffer s0 base size (.input .nonce) qLen)
    (D : CallerBuffer s0 base size (.input .digest) digestLen)
    (hd : digestLen ≤ 32)
    (hP : pointerValue base s0 (.input .digestPrefixLen) = BitVec.ofNat 32 digestLen)
    (hg : operandValue s0 base (.input .g) pLen = g)
    (hy : operandValue s0 base (.input .y) pLen = y)
    (hx : operandValue s0 base (.input .x) qLen = x)
    (hk : operandValue s0 base (.input .nonce) qLen = k)
    (hD : operandValue s0 base (.input .digest) digestLen = digest) :
    let rv := g ^ k % p % q
    let sv := k ^ (q - 2) % q * ((digest % q + x * rv % q) % q) % q
    WP isa (SignVerify.signCompute pLen qLen) s0 fun sf =>
      Moduli base size pLen qLen p q sf ∧
      operandValue sf base (.local r) qLen = rv ∧
      operandValue sf base (.local VG.Impl.Dsa.Layout.s) qLen = sv ∧
      flagW base (Layout.field .mask) sf = flagW base (Layout.field .mask) s0 &&&
        mask32 (publicChecks p q g y ∧ (0 < x ∧ x < q) ∧ (0 < k ∧ k < q) ∧
          g ^ x % p = y ∧ rv ≠ 0 ∧ sv ≠ 0) ∧ Execution base s0 sf := by
  dsimp only
  have L := M.lengths
  have A := M.aligned
  obtain nq : (qLen + 7) / 8 ≤ 48 := by omega_using [L]
  unfold SignVerify.signCompute Core.sequence
  dsimp only [List.foldr]
  refine WP.seq (WP.mono (publicKey_ok M G Y hg hy) fun s1 ⟨M1, F1, Q1, E1⟩ => ?_)
  refine WP.seq (WP.mono (privateKey_ok M1 (E1.buffer G (by decide)) (E1.buffer Y (by decide))
    (E1.buffer X (by decide)) (E1.buffer K (by decide))
    ((E1.value G (by decide) M.extent).trans hg) ((E1.value Y (by decide) M.extent).trans hy)
    ((E1.value X (by decide) M.extent).trans hx) ((E1.value K (by decide) M.extent).trans hk))
    fun s2 ⟨M2, F2, Q2, E2⟩ => ?_)
  obtain E12 := E1.trans E2
  refine WP.seq (WP.mono (signArithmetic_ok M2 (E12.buffer G (by decide)) (E12.buffer K (by decide))
    (E12.buffer X (by decide)) (E12.buffer D (by decide)) hd (E12.prefixLen.trans hP)
    ((E12.value G (by decide) M.extent).trans hg) ((E12.value K (by decide) M.extent).trans hk)
    ((E12.value X (by decide) M.extent).trans hx) ((E12.value D (by decide) M.extent).trans hD)
    (Q2.trans Q1)) fun s3 ⟨M3, R3, S3, E3, F3⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (stageZero_ok M3 (by omega_using [L]) (by omega_using [L]) (by omega_using [A])
    (M3.scalarReady (by decide) nq) true) fun s4 ⟨M4, F4, A4⟩ => ?_))
  obtain E4 := A4.execution (.inr ⟨rfl, rfl⟩)
  refine WP.mono (stageZero_ok M4 (by omega_using [L]) (by omega_using [L]) (by omega_using [A]) (M4.scalarReady (by decide) nq) true)
    fun sf ⟨Mf, F5, A5⟩ => ?_
  refine WP.block_nil ⟨Mf, ?_, ?_, ?_, (((E12.trans E3).trans E4).trans (A5.execution (.inr ⟨rfl, rfl⟩)))⟩
  · rw [A5.scalar_keep_mask M4 (by decide), A4.scalar_keep_mask M3 (by decide), R3]
  · rw [A5.scalar_keep_mask M4 (by decide), A4.scalar_keep_mask M3 (by decide), S3]
  · rw [F5, F4, F3, F2, F1, A4.scalar_keep_mask M3 (by decide), R3, S3]
    simp only [ite_true, BitVec.and_assoc, mask32_and, and_assoc]

end VG.Proof.Dsa.X86

end

end

/-! # Constant-time verification arithmetic and validation -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem callVerifyScalars_relCT (L : CallLayout)
    (Q : CallOperand L (.input .q) L.qLen) (R : CallOperand L (.input .signature) L.qLen)
    (S : CallOperand L .signatureS L.qLen) (D : CallOperand L (.input .digest) L.digestPrefix)
    (hd : L.digestPrefix < 2 ^ 32) :
    RelCT isa (CallPair L) (Core.verifyScalars L.qLen) (CallPair L) := by
  have W := L.lengths
  have E := CallOperand.localBuffer L qMinusTwo L.qLen (by decide) (by change 14912 + L.qLen ≤ 15712; omega_using [W])
  have I := CallOperand.localBuffer L inverse L.qLen (by decide) (by change 14784 + L.qLen ≤ 15712; omega_using [W])
  have Z := CallOperand.localBuffer L z L.qLen (by decide) (by change 14880 + L.qLen ≤ 15712; omega_using [W])
  exact RelCT.seq (callPowerQ_relCT L .signatureS (.local qMinusTwo) inverse Q S E (by decide) (by change 14784 + L.qLen ≤ 15712; omega_using [W]))
    (RelCT.seq (callReduce_relCT (hl := fun _ h => by cases h) L (.input .digest) Core.digestPrefix L.digestPrefix z (.inr ⟨_, rfl⟩)
      (fun _ R => R.prefixOperand) Q D hd (by decide) (by change 14880 + L.qLen ≤ 15712; omega_using [W]))
    (RelCT.seq (callProductQ_relCT L (.local z) (.local inverse) u Q Z I (by decide) (by change 14816 + L.qLen ≤ 15712; omega_using [W]))
    (RelCT.seq (callProductQ_relCT L (.input .signature) (.local inverse) v Q R I (by decide) (by change 14848 + L.qLen ≤ 15712; omega_using [W]))
    (RelCT.block_nil (fun _ _ h => h)))))

theorem callVerifyPowers_relCT (L : CallLayout)
    (P : CallOperand L (.input .p) L.pLen) (Q : CallOperand L (.input .q) L.qLen)
    (G : CallOperand L (.input .g) L.pLen) (Y : CallOperand L (.input .y) L.pLen) :
    RelCT isa (CallPair L) (Core.verifyPowers L.pLen L.qLen) (CallPair L) := by
  have W := L.lengths
  have U := CallOperand.localBuffer L u L.qLen (by decide) (by change 14816 + L.qLen ≤ 15712; omega_using [W])
  have V := CallOperand.localBuffer L v L.qLen (by decide) (by change 14848 + L.qLen ≤ 15712; omega_using [W])
  have T := CallOperand.localBuffer L t L.pLen (by decide) (by change 14944 + L.pLen ≤ 15712; omega_using [W])
  have T2 := CallOperand.localBuffer L t2 L.pLen (by decide) (by change 15328 + L.pLen ≤ 15712; omega_using [W])
  exact RelCT.seq (callPowerP_relCT L (.input .g) (.local u) t P G U (by decide) (by change 14944 + L.pLen ≤ 15712; omega_using [W]))
    (RelCT.seq (callPowerP_relCT L (.input .y) (.local v) t2 P Y V (by decide) (by change 15328 + L.pLen ≤ 15712; omega_using [W]))
    (RelCT.seq (callProductP_relCT L (.local t) (.local t2) t P T T2 (by decide) (by change 14944 + L.pLen ≤ 15712; omega_using [W]))
    (RelCT.seq (callReduce_relCT (hl := fun _ _ => by have := L.lengths; omega_using [W]) L (.local t) (.imm (BitVec.ofNat 32 L.pLen)) L.pLen u (.inl ⟨_, rfl⟩)
      (fun s _ => LenOperand.imm _ _ _ s _) Q T (by omega_using [W]) (by decide) (by change 14816 + L.qLen ≤ 15712; omega_using [W]))
    (RelCT.block_nil (fun _ _ h => h)))))

theorem callVerify_relCT (L : CallLayout)
    (P : CallOperand L (.input .p) L.pLen) (Q : CallOperand L (.input .q) L.qLen)
    (G : CallOperand L (.input .g) L.pLen) (Y : CallOperand L (.input .y) L.pLen)
    (R : CallOperand L (.input .signature) L.qLen) (S : CallOperand L .signatureS L.qLen)
    (D : CallOperand L (.input .digest) L.digestPrefix) (hd : L.digestPrefix < 2 ^ 32) :
    RelCT isa (CallPair L) (Core.verify L.pLen L.qLen) (CallPair L) :=
  RelCT.seq (callVerifyScalars_relCT L Q R S D hd) (callVerifyPowers_relCT L P Q G Y)

theorem callVerifyCompute_relCT (L : CallLayout)
    (P : CallOperand L (.input .p) L.pLen) (Q : CallOperand L (.input .q) L.qLen)
    (G : CallOperand L (.input .g) L.pLen) (Y : CallOperand L (.input .y) L.pLen)
    (R : CallOperand L (.input .signature) L.qLen) (S : CallOperand L .signatureS L.qLen)
    (D : CallOperand L (.input .digest) L.digestPrefix) (hd : L.digestPrefix < 2 ^ 32) :
    RelCT isa (CallPair L) (SignVerify.verifyCompute L.pLen L.qLen) (CallPair L) := by
  have W := L.lengths
  have U := CallOperand.localBuffer L u L.qLen (by decide) (by change 14816 + L.qLen ≤ 15712; omega_using [W])
  exact RelCT.seq (callPublicKey_relCT L P Q G Y)
    (RelCT.seq (RelCT.seq (callRange_relCT L L.qLen .q (.input .signature) false Q R (by omega_using [W]) (by omega_using [W]) L.aligned.2)
      (callRange_relCT L L.qLen .q .signatureS false Q S (by omega_using [W]) (by omega_using [W]) L.aligned.2))
    (RelCT.seq (callVerify_relCT L P Q G Y R S D hd)
    (RelCT.seq (callEqual_relCT L L.qLen (.local u) (.input .signature) U R (by omega_using [W]) (by omega_using [W]) L.aligned.2)
    (RelCT.block_nil (fun _ _ h => h)))))

end VG.Proof.Dsa.X86

end

end

/-! # Constant-time post-shape DSA bodies, including status and output -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem CallPair.workspace {L : CallLayout} {s t : State} (H : CallPair L s t) :
    VG.X86.Taint.Agree (workspaceTaint false) s t := by
  apply agree_regs (rs := [.edi])
  intro reg hr
  obtain rfl := List.mem_singleton.mp hr
  exact BitVec.eq_of_toNat_eq (H.1.moduli.scr.edi_toNat.trans H.2.moduli.scr.edi_toNat.symm)

theorem callVerifyBody_relCT (L : CallLayout)
    (P : CallOperand L (.input .p) L.pLen) (Q : CallOperand L (.input .q) L.qLen)
    (G : CallOperand L (.input .g) L.pLen) (Y : CallOperand L (.input .y) L.pLen)
    (R : CallOperand L (.input .signature) L.qLen) (S : CallOperand L .signatureS L.qLen)
    (D : CallOperand L (.input .digest) L.digestPrefix) (hd : L.digestPrefix < 2 ^ 32) :
    RelCT isa (CallPair L) (SignVerify.verifyBody L.pLen L.qLen)
      (VG.X86.Taint.Agree (workspaceTaint false)) :=
  RelCT.seq (callVerifyCompute_relCT L P Q G Y R S D hd)
    (result_relCT.mono (fun _ _ H => H.workspace) (fun _ _ h => h))

theorem signatureReady_compute {L : CallLayout} {out : BitVec 32} {s0 : State}
    (R : CallReady L s0) (O : SignatureReady L out s0)
    (G : (.input .g, L.pLen) ∈ L.inputs) (Y : (.input .y, L.pLen) ∈ L.inputs)
    (X : (.input .x, L.qLen) ∈ L.inputs) (K : (.input .nonce, L.qLen) ∈ L.inputs)
    (D : ∃ full, (.input .digest, full) ∈ L.inputs ∧ L.digestPrefix ≤ full) (hd : L.digestPrefix ≤ 32) :
    WP isa (SignVerify.signCompute L.pLen L.qLen) s0 (SignatureReady L out) := by
  refine WP.mono (signCompute_ok R.moduli (R.buffers _ G) (R.buffers _ Y)
    (R.buffers _ X) (R.buffers _ K) ((R.buffers _ D.choose_spec.1).prefix D.choose_spec.2) hd R.prefixLen
    rfl rfl rfl rfl rfl) fun sf ⟨M, _, _, F, E⟩ => ?_
  refine ⟨M, ?_, ?_, O.fits, ?_, O.apart⟩
  · obtain ⟨accepted, mask⟩ := O.mask
    rw [mask] at F
    cases accepted
    · simp only [Bool.false_eq_true, ite_false] at F
      exact ⟨false, F.trans BitVec.zero_and⟩
    · simp only [ite_true, BitVec.allOnes_and] at F
      unfold mask32 at F
      split at F
      · exact ⟨true, F⟩
      · exact ⟨false, F⟩
  · rw [runFrame_pointer E.mem E.keeps (by decide) (by decide)]
    exact O.pointer
  · intro e k h
    rw [E.keeps.2.2]
    exact O.write e k h

theorem callSignBody_relCT (L : CallLayout) (out : BitVec 32)
    (P : CallOperand L (.input .p) L.pLen) (Q : CallOperand L (.input .q) L.qLen)
    (G : (.input .g, L.pLen) ∈ L.inputs) (Y : (.input .y, L.pLen) ∈ L.inputs)
    (X : (.input .x, L.qLen) ∈ L.inputs) (K : (.input .nonce, L.qLen) ∈ L.inputs)
    (D : ∃ full, (.input .digest, full) ∈ L.inputs ∧ L.digestPrefix ≤ full) (hd : L.digestPrefix ≤ 32) :
    RelCT isa (fun s t => CallPair L s t ∧ SignatureReady L out s ∧ SignatureReady L out t)
      (SignVerify.signBody L.pLen L.qLen) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold SignVerify.signBody
  refine RelCT.seq (M := isa) (R := fun s t => SignatureReady L out s ∧ SignatureReady L out t) ?_ ?_
  · have C := callSignCompute_relCT L P Q (.inl ⟨_, G, Nat.le_refl _⟩)
      (.inl ⟨_, Y, Nat.le_refl _⟩) (.inl ⟨_, K, Nat.le_refl _⟩) (.inl ⟨_, X, Nat.le_refl _⟩)
      (.inl D) (by omega_using [hd])
    intro s t tr ur sf tf ⟨H, S, T⟩ E F
    exact ⟨(C _ _ _ _ _ _ H E F).1,
      wp_result (signatureReady_compute H.1 S G Y X K D hd) E,
      wp_result (signatureReady_compute H.2 T G Y X K D hd) F⟩
  · apply RelCT.assoc
    exact RelCT.seq (writeSignature_relCT L out) (result_relCT.mono
      (fun _ _ h => taint.le_sound (show taint.le (workspaceTaint false) (workspaceTaint true) = true from rfl) h)
      (fun _ _ h => h))

end VG.Proof.Dsa.X86

end

end

/-! ### `Dsa.X86.ShapeTiming`, which only this module used -/

section

/-! # Shape inspection traces do not depend on domain values -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/ShapeBlocksTiming.lean`, which only this module imported.
section

/-! # Fixed-address shape masks and digest clamping -/

section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86 VG.Proof.Mont.X86.Dynamic

theorem widthMask_relCT (n a tmp bits : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (widthMask n a tmp bits)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold widthMask
  refine RelCT.seq (lessThanConstant_relCT n a tmp _) ?_
  refine RelCT.seq (checkedBlockInvariant (τ' := workspaceTaint false) rfl rfl) ?_
  split
  · exact RelCT.seq (lessThanConstant_relCT n a tmp _) (checkedBlockInvariant (τ' := workspaceTaint false) rfl rfl)
  · exact checkedBlockInvariant (τ' := workspaceTaint false) rfl rfl

theorem optionalWidth_relCT (n a tmp bits : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (optionalWidth n a tmp bits)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold optionalWidth
  split
  · exact widthMask_relCT n a tmp bits
  · exact checkedBlockInvariant (τ' := { workspaceTaint false with regs := .ofList [.edi, .edx] }) rfl rfl

theorem saveWidth_relCT (n bits output : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (Shape.saveWidth n bits output)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold Shape.saveWidth
  refine RelCT.seq (optionalWidth_relCT n _ _ bits) (checkedBlockInvariant (τ' := workspaceTaint false) ?_ rfl)
  rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint false) = true from rfl)]
  change taint.checkBlock (workspaceTaint false) [.store (sc 0) .edx] = _
  rfl

theorem threeWidths_relCT (n a b c output : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (Shape.threeWidths n a b c output)
      (VG.X86.Taint.Agree (workspaceTaint false)) :=
  RelCT.seq (saveWidth_relCT n a output) (RelCT.seq (saveWidth_relCT n b (output + 4))
    (saveWidth_relCT n c (output + 8)))

theorem loadWidths_relCT (len a b c output : Nat) (modulus : VG.Impl.Dsa.Layout.Field) (base : Addr) (size : Nat)
    (hz : Layout.saved ≤ size) :
    RelCT isa (fun s t => VG.Proof.Mont.X86.Scr s base size ∧ VG.Proof.Mont.X86.Scr t base size ∧
      pointerValue base s (.input modulus) = pointerValue base t (.input modulus))
      (Shape.loadWidths len modulus a b c output) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold Shape.loadWidths
  exact RelCT.seq (coreLoad_relCT _ len _ (.input modulus) base size hz)
    ((threeWidths_relCT _ a b c output).mono (fun _ _ h => taint.le_sound
      (show taint.le (workspaceTaint false) (workspaceTaint true) = true from rfl) h) (fun _ _ h => h))

theorem saveParity_relCT (n : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (.block (Shape.saveParity n))
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  apply checkedBlockInvariant (τ' := workspaceTaint false) ?_ rfl
  rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint false) = true from rfl)]
  change taint.checkBlock (workspaceTaint false) [.mov .eax (.mem (sc 0)), .store (sc 0) .eax] = _
  rfl

theorem parity_relCT (n : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (.block (Shape.parity n))
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  apply checkedBlockInvariant (τ' := workspaceTaint false) ?_ rfl
  rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint false) = true from rfl)]
  change taint.checkBlock (workspaceTaint false)
    [.mov .edx (.mem (sc 0)), .alu .and .edx (.mem (sc 0)), .alu .and .edx (.imm 0),
      .mov .eax (.imm 0), .alu .sub .eax (.reg .edx), .store (sc 0) .eax] = _
  rfl

theorem combine_relCT :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (.block Shape.combine)
      (VG.X86.Taint.Agree (workspaceTaint false)) :=
  checkedBlockInvariant (τ' := workspaceTaint false) rfl rfl

theorem digestPrefix_relCT :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) Shape.digestPrefix
      (VG.X86.Taint.Agree (workspaceTaint false)) :=
  checkedBlockInvariant (τ' := workspaceTaint false) rfl rfl

end VG.Proof.Dsa.X86
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem inspectP_relCT (len : Nat) (base : Addr) (size : Nat) (hz : Layout.saved ≤ size) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧
      pointerValue base s (.input .p) = pointerValue base t (.input .p))
      (Shape.inspectP len) (VG.X86.Taint.Agree (workspaceTaint false)) :=
  RelCT.seq (loadWidths_relCT len 1024 2048 3072 32 .p base size hz) (saveParity_relCT _)

theorem inspectQ_relCT (len : Nat) (base : Addr) (size : Nat) (hz : Layout.saved ≤ size) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧
      pointerValue base s (.input .q) = pointerValue base t (.input .q))
      (Shape.inspectQ len) (VG.X86.Taint.Agree (workspaceTaint false)) :=
  RelCT.seq (loadWidths_relCT len 160 224 256 44 .q base size hz)
    (RelCT.block_append (RelCT.seq (parity_relCT _) combine_relCT))

theorem shape_relCT (pLen qLen : Nat) (base : Addr) (size : Nat)
    (hz : Layout.saved ≤ size) (h4 : 4 ≤ pLen) (hmax : pLen ≤ 384) (hw4 : pLen % 4 = 0) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧
      OperandReady s base 48 (.input .p) pLen ∧ OperandReady t base 48 (.input .p) pLen ∧
      pointerValue base s (.input .p) = pointerValue base t (.input .p) ∧
      pointerValue base s (.input .q) = pointerValue base t (.input .q))
      (Shape.check pLen qLen) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold Shape.check Core.sequence
  dsimp only [List.foldr]
  refine RelCT.seq (M := isa) (R := fun s t => Scr s base size ∧ Scr t base size ∧
    pointerValue base s (.input .q) = pointerValue base t (.input .q)) ?_ ?_
  · intro s t tr ur sf tf ⟨S, T, A, B, P, Q⟩ E F
    have trace := (inspectP_relCT pLen base size hz _ _ _ _ _ _ ⟨S, T, P⟩ E F).1
    obtain ⟨_, _, _, _, K1, O1⟩ := wp_result (inspectP_ok S hz h4 hmax hw4 A rfl) E
    obtain ⟨_, _, _, _, K2, O2⟩ := wp_result (inspectP_ok T hz h4 hmax hw4 B rfl) F
    have P1 := pointerValue_keep K1 (by decide) O1 (by decide : contextBytes 48 ≤ 8192) (.input .q)
    have P2 := pointerValue_keep K2 (by decide) O2 (by decide : contextBytes 48 ≤ 8192) (.input .q)
    exact ⟨trace, S.of_keeps K1 (by decide), T.of_keeps K2 (by decide), P1.trans (Q.trans P2.symm)⟩
  · exact RelCT.seq (inspectQ_relCT qLen base size hz)
      (RelCT.seq digestPrefix_relCT (RelCT.seq
        (checkedBlockInvariant (τ' := workspaceTaint false) rfl rfl) (RelCT.block_nil (fun _ _ h => h))))

end VG.Proof.Dsa.X86

end

end


/-! # Complete public shape rejection and verification -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem shapeCall_relCT (L : CallLayout) (digestLen : Nat)
    (P : (.input .p, L.pLen) ∈ L.inputs) (Q : (.input .q, L.qLen) ∈ L.inputs)
    (stable : ∀ input ∈ L.inputs, ShapePointer input.1)
    (hd : L.digestPrefix = min digestLen (Spec.Dsa.bitLength L.q / 8)) :
    RelCT isa (fun s t => ShapeCallReady L digestLen s ∧ ShapeCallReady L digestLen t)
      (Shape.check L.pLen L.qLen)
      (fun s t => (VG.X86.Taint.Agree (workspaceTaint false) s t ∧
        (shapeValid L.p L.q → ShapedCall L digestLen s ∧ ShapedCall L digestLen t)) ∧
        s.zf = some (!decide (shapeValid L.p L.q)) ∧ t.zf = some (!decide (shapeValid L.p L.q))) := by
  have W := L.lengths
  intro s t tr ur sf tf ⟨S, T⟩ E F
  have ctx : VG.Impl.Mont.X86.Dynamic.contextBytes 48 ≤ L.size := by
    have H : 15712 ≤ L.size := L.extent
    change 7048 ≤ L.size; omega_using [H]
  obtain ⟨trace, A⟩ := shape_relCT L.pLen L.qLen L.base L.size L.saved (by omega_using [W]) (by omega_using [W]) L.aligned.1
    _ _ _ _ _ _ ⟨S.scr, T.scr, (S.buffers _ P).ready ctx, (T.buffers _ P).ready ctx,
      (S.pointers _ P).trans (T.pointers _ P).symm, (S.pointers _ Q).trans (T.pointers _ Q).symm⟩ E F
  obtain ⟨Z1, M1, _, _⟩ := wp_result (shapeCall_ok S P Q stable hd) E
  obtain ⟨Z2, M2, _, _⟩ := wp_result (shapeCall_ok T P Q stable hd) F
  exact ⟨trace, ⟨A, fun h => ⟨M1 h, M2 h⟩⟩, Z1, Z2⟩

theorem verifySized_relCT (L : CallLayout) (digestLen : Nat)
    (P : (.input .p, L.pLen) ∈ L.inputs) (Q : (.input .q, L.qLen) ∈ L.inputs)
    (G : (.input .g, L.pLen) ∈ L.inputs) (Y : (.input .y, L.pLen) ∈ L.inputs)
    (R : (.input .signature, L.qLen) ∈ L.inputs) (S : (.signatureS, L.qLen) ∈ L.inputs)
    (D : (.input .digest, digestLen) ∈ L.inputs)
    (stable : ∀ input ∈ L.inputs, ShapePointer input.1)
    (hd : L.digestPrefix = min digestLen (Spec.Dsa.bitLength L.q / 8)) :
    RelCT isa (fun s t => ShapeCallReady L digestLen s ∧ ShapeCallReady L digestLen t)
      (Entry.sized false L.pLen L.qLen) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold Entry.sized
  refine RelCT.seq (shapeCall_relCT L digestLen P Q stable hd)
    (fixedChoice_relCT (!decide (shapeValid L.p L.q)) ?_)
  by_cases valid : shapeValid L.p L.q
  · simp only [valid, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    have B := shape_digest_width valid
    have CT := callVerifyBody_relCT L (.inl ⟨_, P, Nat.le_refl _⟩) (.inl ⟨_, Q, Nat.le_refl _⟩)
      (.inl ⟨_, G, Nat.le_refl _⟩) (.inl ⟨_, Y, Nat.le_refl _⟩)
      (.inl ⟨_, R, Nat.le_refl _⟩) (.inl ⟨_, S, Nat.le_refl _⟩)
      (.inl ⟨_, D, by rw [hd]; exact Nat.min_le_left _ _⟩) (by rw [hd]; omega_using [B])
    exact CT.mono (fun _ _ H => ⟨(H.2 True.intro).1.ready, (H.2 True.intro).2.ready⟩) (fun _ _ h => h)
  · simp only [valid, decide_false, Bool.not_false, ite_true]
    exact verifyFailure_relCT.mono (fun _ _ H => H.1) (fun _ _ h => h)

end VG.Proof.Dsa.X86
