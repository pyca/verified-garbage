module

public import Init.Prelude
public import VerifiedGarbage.Impl.Dsa.X86.CombKey
public import VerifiedGarbage.Spec.Dsa.Generate
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Impl.Dsa.X86.CombGenerate
import VerifiedGarbage.Proof.Dsa.X86.GenerateTiming
import VerifiedGarbage.Proof.Dsa.X86.GenerateParameters
import VerifiedGarbage.Proof.Dsa.X86.KeyTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Impl.Dsa.X86.Comb
public import VerifiedGarbage.Proof.Dsa.X86.CallTiming
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Dsa.X86.ShapeCall
import VerifiedGarbage.Proof.Dsa.X86.VerifySizedTiming
import VerifiedGarbage.Proof.Dsa.X86.OutputTiming
import VerifiedGarbage.Proof.Dsa.X86.FailureTiming
import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
public import VerifiedGarbage.Proof.Dsa.X86.CheckingOperationCT
public import VerifiedGarbage.Proof.Dsa.X86.Comb.Checking
import VerifiedGarbage.Proof.Dsa.X86.ParameterBuffers
import VerifiedGarbage.Proof.Dsa.X86.InstalledInputs
import VerifiedGarbage.Proof.Dsa.X86.ABIResources
public import VerifiedGarbage.Proof.Dsa.X86.CheckingABI
public import VerifiedGarbage.Proof.Dsa.X86.Installed
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckInvoke
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CallResult
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.InvokeTiming
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Context
import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.List.Basic
public import VerifiedGarbage.Proof.Dsa.X86.DerivingOperationCT
public import VerifiedGarbage.Proof.Dsa.X86.Comb.Correct
import VerifiedGarbage.Proof.Dsa.X86.Comb.CanonicalFrame
import VerifiedGarbage.Proof.Dsa.X86.StageChecks
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.X86.ShapeSavedFrame
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Invoke
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CallPre
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckPre
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Impl.Dsa.X86.GenerateKey
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckCall
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Correct
public import VerifiedGarbage.Proof.Dsa.X86.ScheduleFrame
public import VerifiedGarbage.Impl.Dsa.X86.CombCore
public import VerifiedGarbage.Proof.Dsa.X86.CallerBuffer
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Dsa.X86.CallPowerTiming
public import VerifiedGarbage.Proof.Dsa.X86.Comb.Layout
public import VerifiedGarbage.Proof.Dsa.X86.PowEntry
public import VerifiedGarbage.Proof.Dsa.X86.StackFrame
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Dsa.X86.PowCallFrame
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Dsa.X86.Comb.PublicVerified
import VerifiedGarbage.Proof.Dsa.X86.Comb.SelectTable
import VerifiedGarbage.Proof.Dsa.X86.CorePowerLoad
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Mont.OutsFrame
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Dsa.X86.DerivingABI
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Entry
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Call
public import VerifiedGarbage.Proof.Dsa.X86.OutputFrame
public import VerifiedGarbage.Proof.Mont.X86.PowerStep
public import VerifiedGarbage.Impl.Dsa.X86.Generate
import VerifiedGarbage.Proof.Dsa.X86.DerivingOperation
import VerifiedGarbage.Proof.Dsa.X86.DerivingEntry
import VerifiedGarbage.Impl.Dsa.X86.Entry
import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Spec.Dsa.Derive
import VerifiedGarbage.Proof.Dsa.X86.StagePower
import VerifiedGarbage.Proof.Dsa.X86.Persistent
import VerifiedGarbage.Proof.Dsa.X86.DeriveCompute
public import VerifiedGarbage.Proof.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Dsa.X86.Execution
public import VerifiedGarbage.Proof.Dsa.X86.Moduli
public import VerifiedGarbage.Proof.Ecdsa.X86.Flags

/-! ### `Dsa.X86.Comb.Deriving`, which only this module used -/

section

/-! ### `Dsa.X86.Comb.DeriveCompute`, which this module and modules that import it used -/

section

/-! # Derivation computes y and accumulates the private and public ranges -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.X86.Comb
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem deriveCompute_ok {base : Addr} {size pLen qLen p q g x : Nat} {s0 : State}
    (M : Moduli base size pLen qLen p q s0)
    (G : CallerBuffer s0 base size (.input .g) pLen)
    (X : CallerBuffer s0 base size (.input .nonce) qLen)
    (hg : operandValue s0 base (.input .g) pLen = g)
    (hx : operandValue s0 base (.input .nonce) qLen = x)
    (domain : (1<g ∧ g<p) ∧ (p-1)%q=0 ∧ g^q%p=1)
    (sizeComb : (layout ((pLen+7)/8) ((qLen+3)/4)).size≤size)
    (C : canonical ((pLen+7)/8) ((qLen+3)/4) p g base s0.mem) :
    WP isa (deriveCompute pLen qLen) s0 fun sf =>
      Moduli base size pLen qLen p q sf ∧
      flagW base (Layout.field .mask) sf = flagW base (Layout.field .mask) s0 &&&
        mask32 (((1 < g ∧ g < p) ∧ (p - 1) % q = 0 ∧ g ^ q % p = 1) ∧
          (0 < x ∧ x < q) ∧ (1 < g ^ x % p ∧ g ^ x % p < p)) ∧
      operandValue sf base (.local t2) pLen = g ^ x % p ∧
      Execution base s0 sf := by
  have L := M.lengths
  have A := M.aligned
  have np : (pLen + 7) / 8 ≤ 48 := by omega_using [L]
  have nq : (qLen + 7) / 8 ≤ 48 := by omega_using [L]
  have pp : 0 < p := by have := M.pLarge; omega_using [domain]
  unfold deriveCompute Core.sequence
  dsimp only [List.foldr]
  refine WP.seq (WP.mono (validateRange_ok M.scr M.saved rfl (by omega_using [L]) (by omega_using [L]) A.2
    M.qReady (X.ready (M.context nq)) false) fun s2 ⟨F2,K2,O2⟩ => ?_)
  have R2 := StageFrame.of_frame K2 (by decide) O2 nq
  have E12 := R2.execution (.inr ⟨rfl,rfl⟩)
  have M2 := M.keep E12.mem E12.keeps (by decide) (by decide)
  have C2 := canonical_check (supported_widths M.widths) nq C O2
  refine WP.seq (WP.mono (stagePrivate_ok M2
    ((E12.buffer G (by decide)).ready (M2.context np))
    ((E12.buffer X (by decide)).ready (M2.context np))
    (by decide) sizeComb (by rw [E12.value G (by decide) M.extent,hg]; exact C2)) fun s3 ⟨M3, R3⟩ => ?_)
  have E3 := R3.toStageFrame.execution (.inl ⟨by decide, M2.wideFit (by decide)⟩)
  have Y3 : operandValue s3 base (.local t2) pLen = g ^ x % p := by
    have V := R3.wide_value M2 (by decide) (Nat.lt_trans (Nat.mod_lt _ pp) M.valueBounds.1)
    rw [E12.value G (by decide) M.extent, E12.value X (by decide) M.extent, hg, hx] at V
    exact V
  refine WP.seq (WP.mono (stageRange_ok M3 (by omega_using [L]) (by omega_using [L]) (by omega_using [A])
    M3.pReady (M3.wideReady (by decide) np) true) fun sf ⟨Mf, F4, R4⟩ => ?_)
  refine WP.block_nil ⟨Mf, ?_, (stageWide_keep_mask R4 M3 (by decide)).trans Y3,
    (E12.trans E3).trans (R4.execution (.inr ⟨rfl, rfl⟩))⟩
  have qValue := M.qValue
  unfold operandValue at hx qValue
  rw [F4, R3.toStageFrame.mask_keep (by decide), F2, Y3, hx, qValue, M3.pValue]
  simp only [domain, true_and]
  simp only [Bool.false_eq_true, ite_false, ite_true, BitVec.and_assoc, mask32_and, and_assoc]

end VG.Proof.Dsa.X86.Comb

end

end

/-! # Derivation reads the caller's parameters and explicit scalar -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/Comb/DerivingSized.lean`, which only this module imported.
section

/-! The internal derivation consumes the retained table under validated parameters. -/

section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Comb

theorem derivingSized_spec {base : Addr} {size pLen qLen p q g x : Nat}
    {s : State} {out : BitVec 32} {params scalar : List Byte}
    (scr : Scr s base size) (extent : usedBytes ≤ size) (widths : Spec.Dsa.lengthsValid pLen qLen)
    (Params : CallerBuffer s base size (.input .p) (2 * pLen + qLen))
    (P : CallerBuffer s base size (.input .p) pLen)
    (Q : CallerBuffer s base size (.input .q) qLen)
    (G : CallerBuffer s base size (.input .g) pLen)
    (X : CallerBuffer s base size (.input .nonce) qLen)
    (hp : operandValue s base (.input .p) pLen = p)
    (hq : operandValue s base (.input .q) qLen = q)
    (hg : operandValue s base (.input .g) pLen = g)
    (hx : operandValue s base (.input .nonce) qLen = x)
    (paramBytes : Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .p)).setWidth 64) (2 * pLen + qLen) = params)
    (scalarBytes : Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .nonce)).setWidth 64) qLen = scalar)
    (ho : pointerValue base s (.input .out) = out)
    (hf : out.toNat + (3 * pLen + 2 * qLen) ≤ 2 ^ 32)
    (hw : ∀ i < 3 * pLen + 2 * qLen, InRegions s.wr (off (out.setWidth 64) i) 1)
    (ha : Region.Disjoint ⟨base, size⟩ ⟨out.setWidth 64, 3 * pLen + 2 * qLen⟩)
    (pa : Region.Disjoint ⟨(pointerValue base s (.input .p)).setWidth 64, 2 * pLen + qLen⟩
      ⟨out.setWidth 64, 3 * pLen + 2 * qLen⟩)
    (xa : Region.Disjoint ⟨(pointerValue base s (.input .nonce)).setWidth 64, qLen⟩
      ⟨out.setWidth 64, 3 * pLen + 2 * qLen⟩)
    (paramsValue : Spec.Dsa.paramsBytes pLen qLen params = ⟨p, q, g⟩)
    (valid : Spec.Dsa.parametersValid (Spec.Dsa.paramsBytes pLen qLen params))
    (sizeComb : (layout ((pLen+7)/8) ((qLen+3)/4)).size≤size)
    (C : parameterContext base pLen qLen params s.mem) :
    let result := Spec.Dsa.deriveKeyBytes pLen qLen params scalar
    WP isa (deriveSized pLen qLen) s fun sf =>
      (sf.gpr .eax).toNat = Spec.Dsa.signStatus result ∧
      Spec.Rsa.bytesAt sf.mem (out.setWidth 64) (3 * pLen + 2 * qLen) =
        result.getD (List.replicate (3 * pLen + 2 * qLen) 0) ∧
      Keeps powerClob s sf ∧ StackOutputFrame (s.gpr .esp) base (out.setWidth 64) usedBytes
        (3 * pLen + 2 * qLen) s.mem sf.mem ∧
      ∀ regs, VG.X86.Spill.Saved s.mem (off base) regs Entry.savedRegisters →
        VG.X86.Spill.Saved sf.mem (off base) regs Entry.savedRegisters := by
  have sup := supported_widths widths
  unfold parameterContext at C
  rw [paramsValue] at C valid
  have domain := (generationChecks_spec (parametersValid_shape valid)).mpr valid
  exact deriveSizedWith_spec scr extent widths Params P Q G X hp hq hg hx paramBytes scalarBytes
    ho hf hw ha pa xa paramsValue deriveCompute (canonical ((pLen+7)/8) ((qLen+3)/4) p g base) C
    (fun O C => canonical_outs sup C (Outs.of_outside (rs := [(0,8248)]) (shapeFrame_outside O) (by simp)) (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      apply Or.inr
      change 8248≤context ((pLen+7)/8)
      unfold context; split <;> omega))
    (fun M G X hg hx C => deriveCompute_ok M G X hg hx domain sizeComb C)

end VG.Proof.Dsa.X86.Comb
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Comb

def deriveContext (s : State) : Mem → Prop :=
  parameterContext (argumentPointer s 7) (arg s 4).toNat (arg s 6).toNat
    (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat)

def validParameters (s : State) : Prop :=
  Spec.Dsa.parametersValid (Spec.Dsa.paramsBytes (arg s 4).toNat (arg s 6).toNat
    (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat))

theorem derivingInstalled_spec {s t : State} (A : DerivingABI s)
    (I : Installed (argumentPointer s 7) ((arg s 8).toNat * 8) Generate.deriveArguments 2 4 6 s t)
    (O : Outside (argumentPointer s 7) 0 8272 s.mem t.mem)
    (valid : validParameters s) (C : deriveContext s s.mem) :
    let result := Spec.Dsa.deriveKeyBytes (arg s 4).toNat (arg s 6).toNat
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 5) (arg s 6).toNat)
    WP isa (deriveSized (arg s 4).toNat (arg s 6).toNat) t fun sf =>
      (sf.gpr .eax).toNat = Spec.Dsa.signStatus result ∧
      Spec.Rsa.bytesAt sf.mem (argumentPointer s 0) (arg s 1).toNat =
        result.getD (List.replicate (arg s 1).toNat 0) ∧
      Keeps powerClob t sf ∧ StackOutputFrame (t.gpr .esp) (argumentPointer s 7)
        (argumentPointer s 0) usedBytes (arg s 1).toNat t.mem sf.mem ∧
      ∀ regs, VG.X86.Spill.Saved t.mem (off (argumentPointer s 7)) regs Entry.savedRegisters →
        VG.X86.Spill.Saved sf.mem (off (argumentPointer s 7)) regs Entry.savedRegisters := by
  dsimp only
  have L : 0 < (arg s 4).toNat ∧ 0 < (arg s 6).toNat := by
    have H := A.lengths; unfold Spec.Dsa.lengthsValid at H; omega_using [H]
  obtain ⟨Params, Bytes⟩ := I.input (by decide : (2, .p) ∈ Generate.deriveArguments) A.keyBound
    (by rw [A.rd, A.wr]; simp) A.keyScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowKey.symm)
  obtain ⟨X, XBytes⟩ := I.input (by decide : (5, .nonce) ∈ Generate.deriveArguments) A.scalarBound
    (by rw [A.rd, A.wr]; simp) A.scalarScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowScalar.symm)
  obtain ⟨Qptr, Gptr, _⟩ := I.pointers (by decide)
  obtain ⟨P, Q, G, Value⟩ := parameters_buffers Params L.1 L.2
    (by have := A.keyLength; omega_using [this]) Bytes Qptr Gptr
  rw [A.outLength]
  have Ct : deriveContext s t.mem := by
    unfold deriveContext parameterContext at C ⊢
    apply canonical_outs (supported_widths A.lengths) C (Outs.of_outside (rs := [(0,8272)]) O (by simp))
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    apply Or.inr
    change 8272≤context (((arg s 4).toNat+7)/8)
    unfold context; split <;> omega_using []
  have fits := Nat.le_trans (context_fits A.lengths) (Nat.mul_le_mul_right 8 A.scratchLength)
  apply derivingSized_spec (out := arg s 0) I.scr A.used A.lengths
    (by rw [← A.keyLength]; exact Params) P Q G X rfl rfl rfl rfl
    (by rw [← A.keyLength]; exact Bytes) XBytes (I.arguments (0, .out) (by decide))
    (by rw [← A.outLength]; exact A.outBound) ?_ (by rw [← A.outLength]; exact A.outScratch.symm)
    (by rw [I.arguments (2, .p) (by decide), ← A.keyLength, ← A.outLength]; exact A.keyOut)
    (by rw [I.arguments (5, .nonce) (by decide), ← A.outLength]; exact A.scalarOut) Value valid fits Ct
  intro i hi
  rw [I.keeps.2.2, A.wr]
  refine ⟨_, List.mem_cons_self, Offset.contains_base _ (by have := A.outLength; omega_using [hi, this]) ?_⟩
  have := A.outBound
  have := A.outLength
  omega_using [hi]

theorem derivingOperation_spec {s : State} (A : DerivingABI s)
    (valid : validParameters s) (C : deriveContext s s.mem) :
    let result := Spec.Dsa.deriveKeyBytes (arg s 4).toNat (arg s 6).toNat
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 5) (arg s 6).toNat)
    WP isa deriveKey s fun sf =>
      (sf.gpr .eax).toNat = Spec.Dsa.signStatus result ∧
      Spec.Rsa.bytesAt sf.mem (argumentPointer s 0) (arg s 1).toNat =
        result.getD (List.replicate (arg s 1).toNat 0) ∧
      abiPreserved s sf ∧
      StackOutputFrame (s.gpr .esp) (argumentPointer s 7) (argumentPointer s 0) ((arg s 8).toNat * 8) (arg s 1).toNat s.mem sf.mem ∧
      sf.rd = s.rd ∧ sf.wr = s.wr :=
  derivingOperationWith_spec deriveSized A (fun I O => derivingInstalled_spec A I O valid C)

end VG.Proof.Dsa.X86.Comb

end

end

/-! ### `Dsa.X86.KeyRandom.InvokeFrame`, which only this module used -/

section

/-! Returning from either internal invocation restores the sampler's ready state. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.KeyRandom
open VG VG.X86 VG.Proof.Mont

theorem Ready.returned {s₀ t u : State} (R : Ready s₀ t) (rd : u.rd=t.rd) (wr : u.wr=t.wr)
    (sp : u.gpr .esp=t.gpr .esp) (F : Frame (rWrites s₀) t.mem u.mem) : Ready s₀ u :=
  ⟨⟨by rw [sp]; exact R.rf.esp, by rw [wr]; exact R.rf.wr, by rw [wr]; exact R.rf.args,
    R.rf.nowrap⟩,rd.trans R.rd,wr.trans R.wr,R.frame.trans F⟩

theorem deriveFrame_outer {s₀ : State} {m m' : Mem} (F : Frame (callWrites s₀) m m') :
    Frame (rWrites s₀) m m' := by
  apply F.sub
  intro r hr
  simp only [callWrites,callWr,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl
  · exact ⟨_,by simp [rWrites,rOut],fun _ h => h⟩
  · exact ⟨_,by simp [rWrites,rScratch],fun _ h => h⟩
  · exact ⟨rStack s₀,by simp [rWrites],stk_sub s₀ (by decide)⟩
  · refine ⟨rStack s₀,by simp [rWrites],?_⟩
    have H := Offset.sub_base (rCall s₀) (d := 0) (n := 112) (k := 232) (by decide)
    rwa [BitVec.add_zero] at H

theorem checkFrame_outer {s₀ : State} {m m' : Mem} (F : Frame (CheckCall.callWrites s₀) m m') :
    Frame (rWrites s₀) m m' := by
  apply F.sub
  intro r hr
  simp only [CheckCall.callWrites,CheckCall.callWr,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl
  · exact ⟨_,by simp [rWrites,rScratch],fun _ h => h⟩
  · exact ⟨rStack s₀,by simp [rWrites],stk_sub s₀ (by decide)⟩
  · refine ⟨rStack s₀,by simp [rWrites],?_⟩
    have H := Offset.sub_base (rCall s₀) (d := 0) (n := 112) (k := 232) (by decide)
    rwa [BitVec.add_zero] at H

theorem invocation_below {s₀ t : State} (A : KeyABI s₀) (R : Ready s₀ t) :
    below (t.gpr .esp) 112=⟨rCall s₀,112⟩ := by
  have low : 112≤(t.gpr .esp).toNat := by have := esp_toNat A R; have := rLow_toNat A; have := A.stackLow; omega_arith
  apply congrArg (fun base => Region.mk base 112)
  rw [Taint.sub_setWidth low,R.rf.esp]
  unfold rBase off rLow rCall
  bv_omega

end VG.Proof.Dsa.X86.KeyRandom

end

end

/-! ### `Dsa.X86.KeyRandom.InlineInvoke`, which only this module used -/

section

/-! A shared inlined cdecl boundary for the checker and prevalidated derivation. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.KeyRandom
open VG VG.X86

theorem inlineInvoke_ok {body : Prog isa} {s : State} {rd wr : List Region} {Q : Mem → BitVec 32 → Prop}
    (safe : NoSp body) (depth : stackUse body≤108) (low : 112≤(s.gpr .esp).toNat)
    (reads : Covers (rd++wr) (s.rd++s.wr)) (writes : Covers wr s.wr)
    (correct : WP isa body ((allocated 4 s).withRegions rd wr) fun u =>
      abiPreserved ((allocated 4 s).withRegions rd wr) u ∧ Q u.mem (u.gpr .eax))
    (hQ : ∀ m m' ax, Frame [below (s.gpr .esp) 112] m m' → Q m ax → Q m' ax) :
    WP isa (VG.Impl.Dsa.X86.Comb.invoke body) s fun u =>
      u.rd=s.rd ∧ u.wr=s.wr ∧ (∀ r∈calleeSaved, u.gpr r=s.gpr r) ∧
      Frame (wr++[below (s.gpr .esp) 112]) s.mem u.mem ∧ Q u.mem (u.gpr .eax) := by
  have readWide : Covers (rd++wr) ((allocated 4 s).rd++(allocated 4 s).wr) :=
    reads.trans (Covers.append (Covers.refl _) (Covers.of_mem fun _ hr => List.mem_cons_of_mem _ hr))
  have writeWide : Covers wr (allocated 4 s).wr :=
    writes.trans (Covers.of_mem fun _ hr => List.mem_cons_of_mem _ hr)
  refine WP.alloc (by decide) (by omega_using [low]) safe
    (WP.narrowSp correct readWide writeWide safe
      (by rw [allocated_esp,sub_toNat (by omega_using [low])]; omega_using [depth, low])
      (Q := fun v => v.rd = (allocated 4 s).rd ∧ v.wr = (allocated 4 s).wr ∧
        Frame (wr ++ [below ((allocated 4 s).gpr .esp) (stackUse body)]) (allocated 4 s).mem v.mem ∧
        (∀ r ∈ calleeSaved, v.gpr r = (allocated 4 s).gpr r) ∧ Q v.mem (v.gpr .eax))
      fun v rdv wrv F ⟨ABI,V⟩ => ⟨rdv,wrv,F,ABI.1,V⟩)
    fun v m uu ⟨rdv,wrv,F,saved,V⟩ fl => ?_
  have fl' : Frame [below (s.gpr .esp) 112] v.mem m := fl.sub fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_,List.mem_singleton_self _,below_sub (by decide) low⟩
  refine ⟨rdv,?_,?_,?_,?_⟩
  · change v.wr.tail=s.wr
    rw [wrv]; rfl
  · intro r hr
    by_cases esp : r=.esp
    · subst r
      rw [freed_esp]
      change v.gpr .esp + BitVec.ofNat 32 4 = _
      rw [saved .esp hr]
      change s.gpr .esp-4+4=s.gpr .esp
      exact BitVec.sub_add_cancel _ _
    · rw [freed_gpr _ _ esp]
      change v.gpr r = _
      rw [saved r hr]
      exact allocated_gpr _ _ esp
  · show Frame _ s.mem m
    refine (F.sub ?_).trans (fl'.sub ?_)
    · intro r hr
      rcases List.mem_append.mp hr with hr|hr
      · exact ⟨r,List.mem_append_left _ hr,fun _ h => h⟩
      · obtain rfl := List.mem_singleton.mp hr
        exact ⟨_,List.mem_append_right _ (List.mem_singleton_self _),
          below_inner (by omega_using [depth]) low⟩
    · intro r hr
      exact ⟨r,List.mem_append_right _ hr,fun _ h => h⟩
  · rw [freed_gpr _ _ (by decide)]
    exact hQ _ _ _ fl' V

end VG.Proof.Dsa.X86.KeyRandom

end

end

/-! ### `Dsa.X86.KeyRandom.AllocatedArgs`, which only this module used -/

section

/-! An inlined cdecl body reserves the return-address slot without a call. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.KeyRandom
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86

theorem allocated_arg {s₀ t : State} (h : Ready s₀ t) {i : Nat} (hi : i<11) (rd wr : List Region) :
    arg ((allocated 4 t).withRegions rd wr) i=slot t.mem (rBase s₀) (4*i) := by
  change t.mem.readW ((t.gpr .esp-4+BitVec.ofNat 32 (4+4*i)).setWidth 64) 32=_
  rw [show t.gpr .esp-4+BitVec.ofNat 32 (4+4*i)=t.gpr .esp+BitVec.ofNat 32 (4*i) by
    rw [BitVec.ofNat_add]
    bv_omega]
  rw [h.rf.ptr (by unfold argOff VG.Impl.Dsa.X86.KeyRandom.frameBytes; omega_using [hi])]

theorem derivingABI_congr {s t : State} (A : DerivingABI s)
    (sp : t.gpr .esp=s.gpr .esp) (args : ∀ i<9, arg t i=arg s i)
    (rd : t.rd=s.rd) (wr : t.wr=s.wr) : DerivingABI t := by
  constructor
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),args 6 (by decide),args 7 (by decide),args 8 (by decide),rd,wr] using A.stackLow
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),args 6 (by decide),args 7 (by decide),args 8 (by decide),rd,wr] using A.stackBound
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),args 6 (by decide),args 7 (by decide),args 8 (by decide),rd,wr] using A.rd
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),args 6 (by decide),args 7 (by decide),args 8 (by decide),rd,wr] using A.wr
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),args 6 (by decide),args 7 (by decide),args 8 (by decide),rd,wr] using A.outScratch
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),args 6 (by decide),args 7 (by decide),args 8 (by decide),rd,wr] using A.keyOut
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),args 6 (by decide),args 7 (by decide),args 8 (by decide),rd,wr] using A.scalarOut
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),args 6 (by decide),args 7 (by decide),args 8 (by decide),rd,wr] using A.retOut
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),args 6 (by decide),args 7 (by decide),args 8 (by decide),rd,wr] using A.outBound
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),args 6 (by decide),args 7 (by decide),args 8 (by decide),rd,wr] using A.keyScratch
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),args 6 (by decide),args 7 (by decide),args 8 (by decide),rd,wr] using A.scalarScratch
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),args 6 (by decide),args 7 (by decide),args 8 (by decide),rd,wr] using A.scratchArgs
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),args 6 (by decide),args 7 (by decide),args 8 (by decide),rd,wr] using A.retScratch
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),args 6 (by decide),args 7 (by decide),args 8 (by decide),rd,wr] using A.belowScratch
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),args 6 (by decide),args 7 (by decide),args 8 (by decide),rd,wr] using A.belowKey
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),args 6 (by decide),args 7 (by decide),args 8 (by decide),rd,wr] using A.belowScalar
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),args 6 (by decide),args 7 (by decide),args 8 (by decide),rd,wr] using A.keyBound
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),args 6 (by decide),args 7 (by decide),args 8 (by decide),rd,wr] using A.scalarBound
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),args 6 (by decide),args 7 (by decide),args 8 (by decide),rd,wr] using A.scratchBound
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),args 6 (by decide),args 7 (by decide),args 8 (by decide),rd,wr] using A.lengths
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),args 6 (by decide),args 7 (by decide),args 8 (by decide),rd,wr] using A.keyLength
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),args 6 (by decide),args 7 (by decide),args 8 (by decide),rd,wr] using A.outLength
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),args 6 (by decide),args 7 (by decide),args 8 (by decide),rd,wr] using A.scratchLength

theorem checkingABI_congr {s t : State} (A : CheckingABI s)
    (sp : t.gpr .esp=s.gpr .esp) (args : ∀ i<6, arg t i=arg s i)
    (rd : t.rd=s.rd) (wr : t.wr=s.wr) : CheckingABI t := by
  constructor
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),rd,wr] using A.stackLow
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),rd,wr] using A.stackBound
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),rd,wr] using A.rd
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),rd,wr] using A.wr
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),rd,wr] using A.keyScratch
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),rd,wr] using A.scratchArgs
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),rd,wr] using A.retScratch
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),rd,wr] using A.belowScratch
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),rd,wr] using A.belowKey
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),rd,wr] using A.keyBound
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),rd,wr] using A.scratchBound
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),rd,wr] using A.lengths
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),rd,wr] using A.keyLength
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),rd,wr] using A.scratchLength

theorem allocated_derivingABI {s₀ t : State} (A : KeyABI s₀) (R : Ready s₀ t) (C : CallSlots s₀ t) :
    DerivingABI ((allocated 4 t).withRegions (callRd s₀) (callWr s₀)) := by
  apply derivingABI_congr (t := (allocated 4 t).withRegions (callRd s₀) (callWr s₀)) (derivingABI_of (call_pre A R C)) rfl ?_ rfl rfl
  intro i hi
  rw [allocated_arg R (by omega_using [hi]),ce_arg A R C _ _ hi]
  exact C i hi

theorem allocated_checkingABI {s₀ t : State} (A : KeyABI s₀) (R : Ready s₀ t) (C : CheckCall.CallSlots s₀ t) :
    CheckingABI ((allocated 4 t).withRegions (CheckCall.callRd s₀) (CheckCall.callWr s₀)) := by
  apply checkingABI_congr (t := (allocated 4 t).withRegions (CheckCall.callRd s₀) (CheckCall.callWr s₀)) (checkingABI_of (CheckCall.call_pre A R C)) rfl ?_ rfl rfl
  intro i hi
  rw [allocated_arg R (by omega_using [hi]),CheckCall.ce_arg A R C _ _ hi]
  exact C i hi

end VG.Proof.Dsa.X86.KeyRandom

end

end

/-! ### `Dsa.X86.Comb.KeyInvariant`, which only this module used -/

section

/-! The checked domain and canonical table retained across rejection sampling. -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/Comb/SamplerFrame.lean`, which only this module imported.
section

/-! The rejection sampler writes only its stack frame, preserving the retained comb. -/

section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Proof.Mont VG.Proof.Dsa.X86.KeyRandom
open VG.Impl.Dsa.X86.Comb

theorem samplerFrame {s₀ : State} {m m' : Mem} {rs : List (Nat × Nat)}
    (O : Outs (rBase s₀) rs m m') (fits : ∀ r∈rs, r.1+r.2≤120) :
    Frame [rStack s₀] m m' := by
  refine (O.frame fits).sub ?_
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  refine ⟨rStack s₀,List.mem_singleton_self _,?_⟩
  rw [rBase, rLow_off]
  exact Offset.sub_base (rCall s₀) (d := 88 + 24) (n := 120) (k := 232) (by decide)

theorem sampler_context_kept {s₀ : State} {n e p g : Nat} {m m' : Mem}
    (A : KeyABI s₀) (F : Frame [rStack s₀] m m')
    (fits : context n+8*Proof.Dsa.FixedBaseComb.contextWords (layout n e)≤(arg s₀ 10).toNat*8)
    (C : canonical n e p g (argumentPointer s₀ 9) m) :
    canonical n e p g (argumentPointer s₀ 9) m' := by
  unfold canonical
  rw [VG.Proof.Rsa.wordsAt_frame F (by have := A.scratchBound; omega) (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact A.stackScratchWide.symm.sub_left (Offset.sub_base (argumentPointer s₀ 9)
      (d := context n) (n := 8*Proof.Dsa.FixedBaseComb.contextWords (layout n e))
      (k := (arg s₀ 10).toNat*8) fits))]
  exact C

end VG.Proof.Dsa.X86.Comb
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Proof.Dsa.X86.KeyRandom VG.Impl.Dsa.X86.Comb

/-- Include the caller's resource evidence so arbitrary sampler writes can be
shown disjoint from this context. -/
def keyInvariant (s : State) (mem : Mem) : Prop :=
  KeyABI s ∧ parameterContext (argumentPointer s 9) (arg s 5).toNat (arg s 6).toNat (rInput s).key mem

/-- The invariant holds whatever the stack's bytes are. -/
theorem keyInvariant_frame {s : State} {m m' : Mem} (F : Frame [rStack s] m m') (h : keyInvariant s m) :
    keyInvariant s m' := by
  obtain ⟨A,C⟩ := h
  refine ⟨A,?_⟩
  unfold parameterContext at C ⊢
  apply sampler_context_kept A F ?_ C
  have S := context_fits A.lengths
  have Gen := A.scratchLength
  unfold Spec.Dsa.generationScratchWords at Gen
  unfold Spec.Dsa.scratchWords at S
  have layoutSize : context (((arg s 5).toNat+7)/8)+8*Proof.Dsa.FixedBaseComb.contextWords
      (layout (((arg s 5).toNat+7)/8) (((arg s 6).toNat+3)/4))=
      (layout (((arg s 5).toNat+7)/8) (((arg s 6).toNat+3)/4)).size := by
    have sup := supported_widths A.lengths
    rcases sup with ⟨h,e⟩|⟨h,e⟩|⟨h,e⟩|⟨h,e⟩|⟨h,e⟩ <;> rw [h,e] <;> rfl
  rw [layoutSize]
  omega_using [S, Gen]

theorem keyInvariant_stable : StableScratch keyInvariant :=
  fun O fits h => keyInvariant_frame (samplerFrame O fits) h

end VG.Proof.Dsa.X86.Comb

end

end

/-! ### `Dsa.X86.Comb.StageTiming`, which only this module used -/

section

/-! ### `Dsa.X86.Comb.CorePowerTiming`, which only this module used -/

section

/-! ### `Dsa.X86.Comb.CallTiming`, which only this module used -/

section

/-! ### `Dsa.X86.WorkspaceCallTiming`, which only this module used -/

section

/-! Relational timing at the common cdecl workspace boundary. -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86

def WorkspacePair (base : Addr) (size : Nat) (P : Mem → Mem → Prop) (s t : State) : Prop :=
  Scr s base size ∧ Scr t base size ∧ Pow.Room (s.gpr .esp) base size ∧
    Pow.Room (t.gpr .esp) base size ∧ s.gpr .esp=t.gpr .esp ∧ P s.mem t.mem

theorem workspaceCall_entry {s : State} {base : Addr} {size : Nat}
    (S : Scr s base size) (room : Pow.Room (s.gpr .esp) base size) :
    Pow.Entry (pushed [Reg.eax,.edi] s).callEntry base size := by
  have low := room.1
  have bound := (s.gpr .esp).isLt
  have fit : 4*[Reg.eax,.edi].length+4≤(s.gpr .esp).toNat := by simp; omega_using [low]
  have sp : ((pushed [Reg.eax,.edi] s).callEntry.gpr .esp).toNat=(s.gpr .esp).toNat-12 :=
    callEntry_espNat fit
  refine ⟨?_,?_,?_,S.nowrap,?_⟩
  · rw [callEntry_argAddr0]
    refine ⟨below (s.gpr .esp) 8,List.mem_append_right _ (List.mem_cons_self ..),?_⟩
    change ((s.gpr .esp-BitVec.ofNat 32 8).setWidth 64-
      (s.gpr .esp-BitVec.ofNat 32 8).setWidth 64).toNat+4≤8
    rw [BitVec.sub_self]
    decide
  · rw [callEntry_arg fit (by decide) (by decide)]
    exact S.edi
  · exact List.mem_cons_of_mem _ S.wr
  · unfold StkOk
    rw [sp]
    have sep := room.2
    constructor <;> omega_arith

theorem workspaceCall_relCT {base : Addr} {size bytes : Nat} {P : Mem → Mem → Prop}
    {body : Prog isa} {name : String}
    (stable : ∀ {s t m n}, WorkspacePair base size P s t →
      Frame [below (s.gpr .esp) 12] s.mem m → Frame [below (t.gpr .esp) 12] t.mem n → P m n)
    (timing : RelCT isa (fun s t => Pow.Entry s base size ∧ Pow.Entry t base size ∧
      s.gpr .esp=t.gpr .esp ∧ P s.mem t.mem) body (fun _ _ => True)) :
    RelCT isa (WorkspacePair base size P)
      (.seq (.block [.mov .eax (.imm (BitVec.ofNat 32 (bytes/8)))])
        (.frame (.push [.eax,.edi]) (.call name body) (.pop .eax 2))) (fun _ _ => True) := by
  refine RelCT.seq (R := WorkspacePair base size P) ?_ ?_
  · intro s t tr ur sf tf ⟨S,T,RS,RT,SP,H⟩ E F
    have W (s : State) : WP isa (.block [.mov .eax (.imm (BitVec.ofNat 32 (bytes/8)))]) s
        fun u => Keeps [.eax] s u ∧ u.mem=s.mem :=
      wp_movS rfl fun _ U _ => WP.block_nil ⟨U.keeps,U.mem⟩
    obtain ⟨K,M⟩ := wp_result (W s) E
    obtain ⟨L,N⟩ := wp_result (W t) F
    refine ⟨?_,S.of_keeps K (by decide),T.of_keeps L (by decide),?_,?_,?_,?_⟩
    · cases E with
      | block E => cases F with
        | block F =>
          simp only [execBlock,isa,exec,readSrc,Option.map_some,addrs,srcAddrs,List.map_nil,
            List.nil_append,Option.some.injEq,Prod.mk.injEq] at E F
          exact E.2.symm.trans F.2
    · rw [K.1 .esp (by decide)]; exact RS
    · rw [L.1 .esp (by decide)]; exact RT
    · rw [K.1 .esp (by decide),L.1 .esp (by decide)]; exact SP
    · rw [M,N]; exact H
  · refine RelCT.frame (R := fun _ _ => True) (fun _ _ H => H.2.2.2.2.1) ?_
    rintro _ _ tr ur sf tf ⟨s,t,H,rfl,rfl⟩ E F
    have H0 := H
    obtain ⟨S,T,RS,RT,SP,_⟩ := H
    cases E with
    | call C E R => cases F with
      | call D F Q =>
        rw [call_callEntry,Option.some.injEq] at C D
        subst C D
        have fitS : 4*[Reg.eax,.edi].length+4≤(s.gpr .esp).toNat := by have := RS.1; simp; omega_using [this]
        have fitT : 4*[Reg.eax,.edi].length+4≤(t.gpr .esp).toNat := by have := RT.1; simp; omega_using [this]
        have trace := (timing _ _ _ _ _ _ ⟨workspaceCall_entry S RS,workspaceCall_entry T RT,
          by rw [callEntry_esp',callEntry_esp',SP],
          stable H0 (callEntry_frame (rs := [Reg.eax,.edi]) (s := s) fitS (by decide)) (callEntry_frame (rs := [Reg.eax,.edi]) (s := t) fitT (by decide))⟩ E F).1
        have r := (ret_gpr R .esp).1
        have q := (ret_gpr Q .esp).1
        refine ⟨?_,trivial⟩
        simp only [r,q,State.callEntry_esp,pushed_esp,SP,trace]

end VG.Proof.Dsa.X86

end

end


/-! The public and secret exponent calls share a proved relational calling boundary. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

theorem entry_readArg {s : State} {base : Addr} {size : Nat} (E : Pow.Entry s base size) :
    readSrc s (.mem (VG.Impl.Mont.X86.at_ .esp 4))=some (arg s 0) := by
  change s.load32 (argAddr s 0)=some (arg s 0)
  unfold State.load32
  rw [ite_eq_left E.arg]
  rfl

theorem entry_arg_eq {s t : State} {base : Addr} {size : Nat}
    (E : Pow.Entry s base size) (F : Pow.Entry t base size) : arg s 0=arg t 0 := by
  have H := congrArg (fun x : BitVec 64 => x.setWidth 32) (E.base_eq.trans F.base_eq.symm)
  simpa only [BitVec.setWidth_setWidth_of_le _ (by decide : 32≤64),BitVec.setWidth_eq] using H

def PublicValues (n e m g x : Nat) (base : Addr) (mem : Mem) : Prop :=
  wordsVal mem base (slot n 0) n=m ∧ wordsVal mem base (slot n 5) n=g ∧ val32 mem base (slot n 8) e=x

theorem publicBodyWide_relCT {n e size : Nat} (h : Supported n e) (base : Addr) (m g x : Nat)
    (fits : (layout n e).size≤size) (hm : 1<m) (odd : m%2=1) :
    RelCT isa (fun s t => Pow.Entry s base size ∧ Pow.Entry t base size ∧ s.gpr .esp=t.gpr .esp ∧
      PublicValues n e m g x base s.mem ∧ PublicValues n e m g x base t.mem)
      (body true n e) (fun _ _ => True) := by
  intro s t tr ur sf tf ⟨S,T,SP,A,B⟩ E F
  obtain ⟨u,Eu⟩ := publicNarrowRun h S fits A.1 hm odd E
  obtain ⟨v,Ev⟩ := publicNarrowRun h T fits B.1 hm odd F
  have Sn := (narrowResources S fits).1
  have Tn := (narrowResources T fits).1
  exact publicBody_relCT h base m g x hm odd _ _ _ _ _ _
    ⟨⟨Sn,A.1,A.2.1,A.2.2⟩,⟨Tn,B.1,B.2.1,B.2.2⟩,SP,entry_arg_eq Sn Tn,
      entry_readArg Sn,entry_readArg Tn⟩ Eu Ev

theorem privateCall_relCT {n e : Nat} (h : Supported n e) (base : Addr) (size : Nat) :
    RelCT isa (WorkspacePair base size (fun _ _ => True)) (call false n e) (fun _ _ => True) := by
  apply workspaceCall_relCT (fun _ _ _ => trivial)
  intro s t tr ur sf tf ⟨S,T,SP,_⟩ E F
  exact private_body_relCT h _ _ _ _ _ _ ⟨SP,entry_arg_eq S T,entry_readArg S,entry_readArg T⟩ E F

theorem publicCall_relCT {n e : Nat} (h : Supported n e) (base : Addr) (size m g x : Nat)
    (fits : (layout n e).size≤size) (hm : 1<m) (odd : m%2=1) :
    RelCT isa (WorkspacePair base size (fun a b => PublicValues n e m g x base a ∧ PublicValues n e m g x base b))
      (call true n e) (fun _ _ => True) := by
  apply workspaceCall_relCT (timing := publicBodyWide_relCT h base m g x fits hm odd)
  intro s t a b ⟨S,T,RS,RT,_,A,B⟩ Fa Fb
  have keep {s : State} {mem : Mem} (S : Scr s base size) (R : Pow.Room (s.gpr .esp) base size)
      (V : PublicValues n e m g x base s.mem) (F : Frame [below (s.gpr .esp) 12] s.mem mem) :
      PublicValues n e m g x base mem := by
    have bounds : slot n 0+8*n≤(layout n e).size ∧ slot n 5+8*n≤(layout n e).size ∧
        slot n 8+4*e≤(layout n e).size := by
      rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide
    have vals := fun d k hd => Pow.frame_val32 R S.nowrap F (d := d) (k := k) hd
    refine ⟨?_,?_,(vals _ _ (by omega_using [fits, bounds])).trans V.2.2⟩
    · rw [wordsVal_eq_val32,vals _ _ (by omega_using [fits, bounds]),←wordsVal_eq_val32]; exact V.1
    · rw [wordsVal_eq_val32,vals _ _ (by omega_using [fits, bounds]),←wordsVal_eq_val32]; exact V.2.1
  exact ⟨keep S RS A Fa,keep T RT B Fb⟩

end VG.Proof.Dsa.X86.Comb

end

end


/-! Constant-time composition of byte staging, comb calls, and byte output. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Comb

def PowerAgree (prepare : Bool) (base : Addr) (size len bl : Nat) (modulus : Field) (a b : Pointer)
    (s t : State) : Prop :=
  VG.Proof.Dsa.X86.PowerAgree base size len bl modulus a b s t ∧
  (prepare=true → operandValue s base (.input modulus) len=operandValue t base (.input modulus) len ∧
    operandValue s base a len=operandValue t base a len ∧ operandValue s base b bl=operandValue t base b bl) ∧
  (prepare=false → canonical ((len+7)/8) ((bl+3)/4) (operandValue s base (.input modulus) len)
    (operandValue s base a len) base s.mem ∧
    canonical ((len+7)/8) ((bl+3)/4) (operandValue t base (.input modulus) len)
      (operandValue t base a len) base t.mem)

theorem corePower_relCT (prepare : Bool) (base : Addr) (size len bl output : Nat)
    (modulus : Field) (a b : Pointer) (sup : Supported ((len+7)/8) ((bl+3)/4))
    (hz : VG.Impl.Dsa.X86.Layout.saved≤size) (hu : usedBytes≤size)
    (h4 : 4≤len) (hmax : len≤384) (hw4 : len%4=0) (he : 8≤bl) (hel : bl≤len) (hew : bl%4=0)
    (fits : (layout ((len+7)/8) ((bl+3)/4)).size≤size) :
    RelCT isa (PowerAgree prepare base size len bl modulus a b)
      (power prepare len bl modulus a b output) (fun _ _ => True) := by
  intro s t tr ur sf tf ⟨⟨⟨S,T,PM,PA,PB⟩,RS,RT,SP⟩,Pub,Priv⟩ E F
  have hn : (len+7)/8≤48 := by omega_using [hmax]
  have ctx : contextBytes ((len+7)/8)≤size :=
    Nat.le_trans (VG.Proof.Dsa.X86.Layout.context_bound hn) (Nat.le_trans (by decide) hu)
  have table := table_layout sup
  cases E with | seq Es Es => cases Es with | seq Cs Os =>
  cases F with | seq Et Et => cases Et with | seq Ct Ot =>
  have Head := (powerHead_relCT base size len bl modulus a b hz h4 hmax hw4
    _ _ _ _ _ _ ⟨S,T,PM,PA,PB⟩ Es Et).1
  obtain ⟨Ms,Gs,Xs,Fs,Ks⟩ := wp_result (coreLoadPower_ok S.scr hz rfl h4 hmax hw4 he hel hew
    S.modulusReady S.leftReady S.rightReady rfl ctx) Es
  obtain ⟨Mt,Gt,Xt,Ft,Kt⟩ := wp_result (coreLoadPower_ok T.scr hz rfl h4 hmax hw4 he hel hew
    T.modulusReady T.leftReady T.rightReady rfl ctx) Et
  have Ss := S.scr.of_keeps Ks (by decide)
  have Ts := T.scr.of_keeps Kt (by decide)
  have RSw := RS
  rw [← Ks.1 .esp (by decide)] at RSw
  have RTw := RT
  rw [← Kt.1 .esp (by decide)] at RTw
  have SPw : _ = _ := (Ks.1 .esp (by decide)).trans (SP.trans (Kt.1 .esp (by decide)).symm)
  have preserve {u v : State} (O : Outside base 0 (contextBytes ((len+7)/8)) u.mem v.mem)
      {m g : Nat} (C : canonical ((len+7)/8) ((bl+3)/4) m g base u.mem) :
      canonical ((len+7)/8) ((bl+3)/4) m g base v.mem := by
    apply canonical_outs sup C (Outs.of_outside (rs := [(0,contextBytes ((len+7)/8))]) O (by simp))
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact .inr (by simpa only [Nat.zero_add] using table.apart)
  have Ps := fun eq : prepare=false => preserve Fs (Priv eq).1
  have Pt := fun eq : prepare=false => preserve Ft (Priv eq).2
  simp only [operandValue] at Ps Pt
  rw [← Gs] at Ps
  rw [← Gt] at Pt
  have CallTrace := by
    cases prepare with
    | false => exact (privateCall_relCT sup base size _ _ _ _ _ _ ⟨Ss,Ts,RSw,RTw,SPw,trivial⟩ Cs Ct).1
    | true =>
      obtain ⟨M,G,X⟩ := Pub rfl
      exact (publicCall_relCT sup base size (operandValue s base (.input modulus) len)
        (operandValue s base a len) (operandValue s base b bl) fits S.large S.odd
        _ _ _ _ _ _ ⟨Ss,Ts,RSw,RTw,SPw,⟨Ms,Gs,Xs⟩,
          ⟨Mt.trans M.symm,Gt.trans G.symm,Xt.trans X.symm⟩⟩ Cs Ct).1
  obtain ⟨_,_,Kcs⟩ := wp_result (call_ok sup prepare Ss RSw fits hu Ms S.large S.odd Ps) Cs
  obtain ⟨_,_,Kct⟩ := wp_result (call_ok sup prepare Ts RTw fits hu Mt T.large T.odd Pt) Ct
  have DI : _ = _ := BitVec.eq_of_toNat_eq (Ss.edi_toNat.trans Ts.edi_toNat.symm)
  have Store := (coreStore_workspace_relCT len output _ _ _ _ _ _ (agree_regs (rs := [.edi]) (by
    intro r hr; obtain rfl := List.mem_singleton.mp hr
    rw [Kcs.1 .edi (by decide),Kct.1 .edi (by decide)]
    exact DI)) Os Ot).1
  exact ⟨by simp only [Head,CallTrace,Store],trivial⟩

end VG.Proof.Dsa.X86.Comb

end

end

/-! Comb stages retain the common public caller layout. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Comb

theorem keepSchedule {L : CallLayout} {s t : State} (R : CallReady L s)
    (E : ScheduleFrame L.base L.size s t) : CallReady L t := by
  refine ⟨(E.keeps.1 .esp (by decide)).trans R.sp, E.moduli R.moduli, ?_, ?_, ?_⟩
  · intro input hi; exact E.buffer (R.buffers input hi) (L.stable input hi)
  · intro input hi; exact (E.pointer (L.stable input hi)).trans (R.pointers input hi)
  · exact (E.pointer (p := .input .digestPrefixLen) (by decide)).trans R.prefixLen

def StageAgree (prepare : Bool) (L : CallLayout) (a b : Pointer) (s t : State) : Prop :=
  CallPair L s t ∧
  (prepare=true → operandValue s L.base a L.pLen=operandValue t L.base a L.pLen ∧
    operandValue s L.base b L.qLen=operandValue t L.base b L.qLen) ∧
  (prepare=false → canonical ((L.pLen+7)/8) ((L.qLen+3)/4) L.p
    (operandValue s L.base a L.pLen) L.base s.mem ∧
    canonical ((L.pLen+7)/8) ((L.qLen+3)/4) L.p
      (operandValue t L.base a L.pLen) L.base t.mem)

theorem stagePower_relCT (prepare : Bool) (L : CallLayout) (a b : Pointer) (output : Nat)
    (P : CallOperand L (.input .p) L.pLen) (A : CallOperand L a L.pLen) (B : CallOperand L b L.qLen)
    (ho : output∈Layout.wideValues)
    (fits : (layout ((L.pLen+7)/8) ((L.qLen+3)/4)).size≤L.size) :
    RelCT isa (StageAgree prepare L a b) (power prepare L.pLen L.qLen .p a b output) (CallPair L) := by
  have W := L.lengths
  intro s t tr ur sf tf H E F
  have Pair := H.1
  have CT := corePower_relCT prepare L.base L.size L.pLen L.qLen output .p a b
    (supported_widths L.widths) L.saved L.extent (by omega_using [W]) (by omega_using [W]) L.aligned.1
    (by omega_using [W]) (by omega_using [W]) L.aligned.2 fits
  have M := Pair.1.moduli.pValue.trans Pair.2.moduli.pValue.symm
  have Trace := (CT _ _ _ _ _ _ ⟨⟨⟨Pair.1.arithmeticP A B (by omega_using [W]),
    Pair.2.arithmeticP A B (by omega_using [W]),Pair.pointer P,Pair.pointer A,Pair.pointer B⟩,
    Pair.1.moduli.room,Pair.2.moduli.room,Pair.1.sp.trans Pair.2.sp.symm⟩,
    fun eq => ⟨M,H.2.1 eq⟩,fun eq => by
      rw [Pair.1.moduli.pValue,Pair.2.moduli.pValue]; exact H.2.2 eq⟩ E F).1
  have S := wp_result (stagePower_ok prepare Pair.1.moduli
    (Pair.1.operand A (by omega_using [W]) (by omega_using [W])) (Pair.1.operand B (by omega_using [W]) (by omega_using [W])) ho fits
    (fun eq => (H.2.2 eq).1)) E
  have T := wp_result (stagePower_ok prepare Pair.2.moduli
    (Pair.2.operand A (by omega_using [W]) (by omega_using [W])) (Pair.2.operand B (by omega_using [W]) (by omega_using [W])) ho fits
    (fun eq => (H.2.2 eq).2)) F
  exact ⟨Trace,keepSchedule Pair.1 S.2.2.2.2.1,keepSchedule Pair.2 T.2.2.2.2.1⟩

end VG.Proof.Dsa.X86.Comb

end

end

/-! ### `Dsa.X86.KeyRandom.Verified`, which only this module used -/

section

/-! # The x86 key generator meets the existing bounded-tape contract -/
@[expose] public section
namespace VG.Proof.Dsa.X86.KeyRandom
open VG VG.X86 VG.Impl.Dsa.X86.GenerateKey

def satState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x20005 then 16 else if a = 0x20008 then 168 else if a = 0x20009 then 1 else if a = 0x2000d then 112 else if a = 0x20011 then 32 else if a = 0x20014 then 20 else if a = 0x20015 then 1 else if a = 0x20018 then 128 else if a = 0x2001c then 20 else if a = 0x20021 then 80 else if a = 0x20029 then 128 else if a = 0x2002d then 36 else 0
  rd := [⟨0x2000, 276⟩, ⟨0x5000, 0⟩]
  wr := [⟨0x1000, 424⟩, ⟨0x7000, 8⟩, ⟨0x8000, 73728⟩, ⟨0x20004, 44⟩]

theorem satisfiable : ∃ s, (Spec.Dsa.generateKeyContract abi 232).pre s := by
  have a0 : arg satState 0 = 4096 := by decide
  have a1 : arg satState 1 = 424 := by decide
  have a2 : arg satState 2 = 28672 := by decide
  have a3 : arg satState 3 = 8192 := by decide
  have a4 : arg satState 4 = 276 := by decide
  have a5 : arg satState 5 = 128 := by decide
  have a6 : arg satState 6 = 20 := by decide
  have a7 : arg satState 7 = 20480 := by decide
  have a8 : arg satState 8 = 0 := by decide
  have a9 : arg satState 9 = 32768 := by decide
  have a10 : arg satState 10 = 9216 := by decide
  have e : argAddr satState 0 = 0x20004 := by decide
  have esp : satState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, abi, argSlots, argVal, argBytes,
    stackBelow] [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, e, esp, satState] using satState

/-- An internal checker may establish an invariant for an inlined derivation. -/
theorem verifiedWith {I : State → Mem → Prop} (C : CheckInvoke I) (D : DeriveInvoke I)
    (stable : StableScratch I) (nc : NoSp C.code) (nd : NoSp D.code)
    (ctC : CheckInvokeCT C) (ctD : DeriveInvokeCT D) :
    Verified target (codeWith C.code D.code) (Spec.Dsa.generateKeyContract abi 232) :=
  ⟨generateKeyWith_correct C D stable nc nd,
    generateKeyWith_constantTime C D stable ctC ctD, satisfiable⟩

end VG.Proof.Dsa.X86.KeyRandom

end

end

/-! ### `Dsa.X86.Comb.GenerationStack`, which only this module used -/

section

/-! Structural stack bounds for the two internal generation bodies. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb

theorem check_noSp : NoSp checkParameters := NoSp.of_all (by decide +kernel)
theorem derive_noSp : NoSp deriveKey := NoSp.of_all (by decide +kernel)
theorem check_invoke_noSp : NoSp (invoke checkParameters) := NoSp.of_all (by decide +kernel)
theorem derive_invoke_noSp : NoSp (invoke deriveKey) := NoSp.of_all (by decide +kernel)

theorem check_depth : stackUse checkParameters≤108 := by decide +kernel
theorem derive_depth : stackUse deriveKey≤108 := by decide +kernel

end VG.Proof.Dsa.X86.Comb

end

end

/-! ### `Dsa.X86.Comb.InvokeInputs`, which only this module used -/

section

/-! Shared facts about the inlined bodies' allocated cdecl arguments. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Proof.Dsa.X86.KeyRandom

theorem check_allocated_args {s t : State} (R : Ready s t) (C : CheckCall.CallSlots s t)
    (i : Nat) (hi : i<6) :
    arg ((allocated 4 t).withRegions (CheckCall.callRd s) (CheckCall.callWr s)) i=
      CheckCall.callVal s (t.gpr .esp) i := by
  rw [allocated_arg R (by omega_using [hi])]; exact C i hi

theorem derive_allocated_args {s t : State} (R : Ready s t) (C : CallSlots s t)
    (i : Nat) (hi : i<9) :
    arg ((allocated 4 t).withRegions (callRd s) (callWr s)) i=callVal s (t.gpr .esp) i := by
  rw [allocated_arg R (by omega_using [hi])]; exact C i hi

theorem check_allocated_params {s t : State} (A : KeyABI s) (R : Ready s t) (C : CheckCall.CallSlots s t) :
    checkingParams ((allocated 4 t).withRegions (CheckCall.callRd s) (CheckCall.callWr s))=
      Spec.Dsa.paramsBytes (arg s 5).toNat (arg s 6).toNat (rInput s).key := by
  unfold checkingParams
  simp only [argumentPointer,check_allocated_args R C 0 (by decide),check_allocated_args R C 1 (by decide),
    check_allocated_args R C 2 (by decide),check_allocated_args R C 3 (by decide),CheckCall.callVal]
  change Spec.Dsa.paramsBytes _ _ (Spec.Rsa.bytesAt t.mem (argumentPointer s 3) (arg s 4).toNat)=_
  rw [callKey A R]

theorem derive_allocated_params {s t : State} (A : KeyABI s) (R : Ready s t) (C : CallSlots s t) :
    derivingParams ((allocated 4 t).withRegions (callRd s) (callWr s))=
      Spec.Dsa.paramsBytes (arg s 5).toNat (arg s 6).toNat (rInput s).key := by
  unfold derivingParams
  simp only [argumentPointer,derive_allocated_args R C 2 (by decide),derive_allocated_args R C 3 (by decide),
    derive_allocated_args R C 4 (by decide),derive_allocated_args R C 6 (by decide),callVal]
  change Spec.Dsa.paramsBytes _ _ (Spec.Rsa.bytesAt t.mem (argumentPointer s 3) (arg s 4).toNat)=_
  rw [callKey A R]

theorem derive_allocated_valid {s t : State} (A : KeyABI s) (R : Ready s t) (C : CallSlots s t)
    (checked : KeyRandom.checked s=true) :
    validParameters ((allocated 4 t).withRegions (callRd s) (callWr s)) := by
  change Spec.Dsa.parametersValid (derivingParams _)
  rw [derive_allocated_params A R C]
  unfold KeyRandom.checked Spec.Dsa.checkParametersBytes at checked
  simp only [Bool.and_eq_true,decide_eq_true_eq] at checked
  exact checked.2

theorem derive_allocated_context {s t : State} (A : KeyABI s) (R : Ready s t) (C : CallSlots s t)
    (context : keyInvariant s t.mem) :
    deriveContext ((allocated 4 t).withRegions (callRd s) (callWr s)) t.mem := by
  unfold deriveContext parameterContext
  change canonical _ _ (derivingParams _).p (derivingParams _).g _ _
  rw [derive_allocated_params A R C]
  simp only [argumentPointer,derive_allocated_args R C 4 (by decide),derive_allocated_args R C 6 (by decide),
    derive_allocated_args R C 7 (by decide),callVal]
  exact context.2

end VG.Proof.Dsa.X86.Comb

end

end

/-! ### `Dsa.X86.Comb.CheckInvoke`, which only this module used -/

section

/-! Invoke the checking body internally and retain its canonical table. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Proof.Dsa.X86.KeyRandom VG.Impl.Dsa.X86.Comb

def checkInvoke : CheckInvoke keyInvariant where
  code := invoke checkParameters
  correct := by
    intro s₀ t A R C
    obtain ⟨reads,writes⟩ := CheckCall.call_covers A R
    have low : 112≤(t.gpr .esp).toNat := by have := CheckCall.esp_toNat A R; have := rLow_toNat A; have := A.stackLow; omega_arith
    let v := (allocated 4 t).withRegions (CheckCall.callRd s₀) (CheckCall.callWr s₀)
    have args (i : Nat) (hi : i<6) : arg v i=CheckCall.callVal s₀ (t.gpr .esp) i := by
      rw [allocated_arg R (by omega_using [hi])]
      exact C i hi
    have body : WP isa checkParameters v fun u => abiPreserved v u ∧
        (u.gpr .eax).toNat=(if CheckCall.callResult s₀ t then 1 else 0) ∧
        (CheckCall.callResult s₀ t=true → keyInvariant s₀ u.mem) := by
      refine WP.mono (checkingOperation_spec (allocated_checkingABI A R C)) fun u ⟨V,ABI,_,_,_,I⟩ => ?_
      have V' := V
      simp only [args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),
        argumentPointer,CheckCall.callVal] at V'
      refine ⟨ABI,V',?_⟩
      intro ok
      have Inv : checkContext v u.mem := I (by
        simp only [argumentPointer,args 0 (by decide),args 1 (by decide),args 2 (by decide),
          args 3 (by decide),CheckCall.callVal]
        exact ok)
      refine ⟨A,?_⟩
      unfold checkContext parameterContext at Inv
      simp only [argumentPointer,args 0 (by decide),args 1 (by decide),args 2 (by decide),
        args 3 (by decide),args 4 (by decide),CheckCall.callVal] at Inv
      change parameterContext (argumentPointer s₀ 9) (arg s₀ 5).toNat (arg s₀ 6).toNat
        (Spec.Rsa.bytesAt t.mem (argumentPointer s₀ 3) (arg s₀ 4).toNat) u.mem at Inv
      rw [callKey A R] at Inv
      exact Inv
    have stackOf : ∀ {m m' : Mem}, Frame [below (t.gpr .esp) 112] m m' → Frame [rStack s₀] m m' := fun F => by
      rw [invocation_below A R] at F
      exact F.sub fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
    refine WP.mono (inlineInvoke_ok (Q := fun mem ax => ax.toNat=(if CheckCall.callResult s₀ t then 1 else 0) ∧
      (CheckCall.callResult s₀ t=true → keyInvariant s₀ mem)) check_noSp check_depth low reads writes body
      fun _ _ _ F ⟨e,I⟩ => ⟨e,fun h => keyInvariant_frame (stackOf F) (I h)⟩) fun u ⟨rd,wr,K,F,V,I⟩ => ?_
    rw [invocation_below A R] at F
    have Frame : VG.Frame (CheckCall.callWrites s₀) t.mem u.mem := F
    refine ⟨R.returned rd wr (K .esp (by simp [calleeSaved])) (checkFrame_outer Frame),Frame,K,?_,I⟩
    apply BitVec.eq_of_toNat_eq
    rw [V]
    cases CheckCall.callResult s₀ t <;> rfl

end VG.Proof.Dsa.X86.Comb

end

end

/-! ### `Dsa.X86.KeyRandom.InlineInvokeTiming`, which only this module used -/

section

/-! Inlining a cdecl body adds no observable trace beyond the body's execution. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.KeyRandom
open VG VG.X86

theorem inlineInvoke_trace {body : Prog isa} {s t : State} {rd wr : List Region} {tr : List Leak}
    (reads : Covers (rd++wr) (s.rd++s.wr)) (writes : Covers wr s.wr)
    (terminates : WP isa body ((allocated 4 s).withRegions rd wr) (fun _ => True))
    (E : Exec isa (VG.Impl.Dsa.X86.Comb.invoke body) s tr t) :
    ∃ u, Exec isa body ((allocated 4 s).withRegions rd wr) tr u := by
  cases E with
  | frame push run pop =>
    have eq := alloc_some push
    subst eq
    have readWide : Covers (rd++wr) ((allocated 4 s).rd++(allocated 4 s).wr) :=
      reads.trans (Covers.append (Covers.refl _) (Covers.of_mem fun _ hr => List.mem_cons_of_mem _ hr))
    have writeWide : Covers wr (allocated 4 s).wr :=
      writes.trans (Covers.of_mem fun _ hr => List.mem_cons_of_mem _ hr)
    obtain ⟨trace,u,Run,_⟩ := terminates
    obtain ⟨rfl,_⟩ := Exec.det run (regionModel.inline Run readWide writeWide).1
    exact ⟨u,by simpa only [isa,addrs,List.map_nil,List.nil_append,List.append_nil] using Run⟩

end VG.Proof.Dsa.X86.KeyRandom

end

end

/-! ### `Dsa.X86.Comb.DeriveBodyTiming`, which only this module used -/

section

/-! Private comb computation followed by the shared output copies. -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/Comb/DeriveComputeTiming.lean`, which only this module imported.
section

/-! The private schedule uses the retained context and never branches on x. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Comb

def ContextReady (L : CallLayout) (s : State) : Prop :=
  canonical ((L.pLen+7)/8) ((L.qLen+3)/4) L.p (operandValue s L.base (.input .g) L.pLen) L.base s.mem

theorem deriveCompute_relCT (L : CallLayout)
    (P : CallOperand L (.input .p) L.pLen) (Q : CallOperand L (.input .q) L.qLen)
    (G : (.input .g,L.pLen)∈L.inputs) (X : (.input .nonce,L.qLen)∈L.inputs)
    (fits : (layout ((L.pLen+7)/8) ((L.qLen+3)/4)).size≤L.size) :
    RelCT isa (fun s t => CallPair L s t ∧ ContextReady L s ∧ ContextReady L t)
      (deriveCompute L.pLen L.qLen) (CallPair L) := by
  have W := L.lengths
  have nq : (L.qLen+7)/8≤48 := by omega_using [W]
  have Xop : CallOperand L (.input .nonce) L.qLen := .inl ⟨_,X,Nat.le_refl _⟩
  have Gop : CallOperand L (.input .g) L.pLen := .inl ⟨_,G,Nat.le_refl _⟩
  have bound : t2+L.pLen≤usedBytes := by change 15328+L.pLen≤15712; omega_using [W]
  have Y := CallOperand.localBuffer L t2 L.pLen (by decide) bound
  unfold deriveCompute Core.sequence
  dsimp only [List.foldr]
  refine RelCT.seq (R := fun s t => CallPair L s t ∧ ContextReady L s ∧ ContextReady L t) ?_
    (RelCT.seq ?_ (RelCT.seq
      (callRange_relCT L L.pLen .p (.local t2) true P Y (by omega_using [W]) (by omega_using [W]) L.aligned.1)
      (RelCT.block_nil (fun _ _ h => h))))
  · intro s t tr ur sf tf ⟨Pair,Cs,Ct⟩ E F
    have H := callRange_relCT L L.qLen .q (.input .nonce) false Q Xop
      (by omega_using [W]) (by omega_using [W]) L.aligned.2 _ _ _ _ _ _ Pair E F
    have keep {u v : State} (R : CallReady L u) (C : ContextReady L u)
        {trace : List Leak} (Ev : Exec isa (Validate.range L.qLen .q (.input .nonce) false) u trace v) :
        ContextReady L v := by
      obtain ⟨_,K,O⟩ := wp_result (validateRange_ok R.moduli.scr L.saved rfl
        (by omega_using [W]) (by omega_using [W]) L.aligned.2 R.moduli.qReady
        ((R.buffers _ X).ready (R.moduli.context nq)) false) Ev
      have Ex := (StageFrame.of_frame K (by decide) O nq).execution (.inr ⟨rfl,rfl⟩)
      unfold ContextReady
      rw [Ex.value (R.buffers _ G) (by change StablePointer (.input .g); decide) L.extent]
      exact canonical_check (supported_widths L.widths) nq C O
    exact ⟨H.1,H.2,keep Pair.1 Cs E,keep Pair.2 Ct F⟩
  · apply (stagePower_relCT false L (.input .g) (.input .nonce) t2 P Gop Xop (by decide) fits).mono
      ?_ (fun _ _ H => H)
    intro s t ⟨Pair,Cs,Ct⟩
    exact ⟨Pair,fun h => Bool.noConfusion h,fun _ => ⟨Cs,Ct⟩⟩

end VG.Proof.Dsa.X86.Comb
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Comb
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

def DomainReady (L : CallLayout) (s : State) : Prop :=
  let g := operandValue s L.base (.input .g) L.pLen
  (1<g ∧ g<L.p) ∧ (L.p-1)%L.q=0 ∧ g^L.q%L.p=1

theorem deriveBody_relCT (L : CallLayout) (out : BitVec 32)
    (P : (.input .p,L.pLen)∈L.inputs) (Q : (.input .q,L.qLen)∈L.inputs)
    (G : (.input .g,L.pLen)∈L.inputs) (X : (.input .nonce,L.qLen)∈L.inputs)
    (Params : (.input .p,2*L.pLen+L.qLen)∈L.inputs)
    (ho : out.toNat+(3*L.pLen+2*L.qLen)≤2^32)
    (A : Region.Disjoint ⟨L.base,L.size⟩ ⟨out.setWidth 64,3*L.pLen+2*L.qLen⟩)
    (fits : (layout ((L.pLen+7)/8) ((L.qLen+3)/4)).size≤L.size) :
    RelCT isa (fun s t => CallPair L s t ∧ KeyOutputReady L out s ∧ KeyOutputReady L out t ∧
      ContextReady L s ∧ ContextReady L t ∧ DomainReady L s ∧ DomainReady L t)
      (.seq (deriveCompute L.pLen L.qLen) (Generate.writeKey L.pLen L.qLen))
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  have W := L.lengths
  refine RelCT.seq (R := fun s t => CallPair L s t ∧ KeyOutputReady L out s ∧ KeyOutputReady L out t) ?_ ?_
  · intro s t tr ur sf tf ⟨Pair,S,T,Cs,Ct,Ds,Dt⟩ E F
    have H := deriveCompute_relCT L (.inl ⟨_,P,Nat.le_refl _⟩) (.inl ⟨_,Q,Nat.le_refl _⟩)
      G X fits _ _ _ _ _ _ ⟨Pair,Cs,Ct⟩ E F
    have Es := (wp_result (deriveCompute_ok Pair.1.moduli (Pair.1.buffers _ G)
      (Pair.1.buffers _ X) rfl rfl Ds fits Cs) E).2.2.2
    have Et := (wp_result (deriveCompute_ok Pair.2.moduli (Pair.2.buffers _ G)
      (Pair.2.buffers _ X) rfl rfl Dt fits Ct) F).2.2.2
    exact ⟨H.1,H.2,S.keep Es,T.keep Et⟩
  · apply (writeKey_relCT L.base L.size L.pLen L.qLen out L.saved ho (by omega_using [W]) A).mono ?_ (fun _ _ h => h)
    intro s t ⟨Pair,S,T⟩
    exact ⟨S.writeReady Pair.1 Params X A,T.writeReady Pair.2 Params X A,
      Pair.pointer (.inl ⟨_,P,Nat.le_refl _⟩),Pair.pointer (.inl ⟨_,X,Nat.le_refl _⟩)⟩

end VG.Proof.Dsa.X86.Comb

end

end

/-! ### `Dsa.X86.Comb.DeriveInvoke`, which only this module used -/

section

/-! The internal prevalidated body is called only with the checked retained context. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Proof.Dsa.X86.KeyRandom VG.Impl.Dsa.X86.Comb

def deriveInvoke : DeriveInvoke keyInvariant where
  code := invoke deriveKey
  correct := by
    intro s₀ t A R C checked context
    obtain ⟨reads,writes⟩ := call_covers A R
    have low : 112≤(t.gpr .esp).toNat := by have := esp_toNat A R; have := rLow_toNat A; have := A.stackLow; omega_arith
    let v := (allocated 4 t).withRegions (callRd s₀) (callWr s₀)
    have args (i : Nat) (hi : i<9) : arg v i=callVal s₀ (t.gpr .esp) i := by
      rw [allocated_arg R (by omega_using [hi])]
      exact C i hi
    have valid := derive_allocated_valid A R C checked
    have contextV := derive_allocated_context A R C context
    have result : Spec.Dsa.deriveKeyBytes (arg v 4).toNat (arg v 6).toNat
        (Spec.Rsa.bytesAt v.mem (argumentPointer v 2) (arg v 3).toNat)
        (Spec.Rsa.bytesAt v.mem (argumentPointer v 5) (arg v 6).toNat)=callResult s₀ t := by
      simp only [argumentPointer,args 2 (by decide),args 3 (by decide),args 4 (by decide),
        args 5 (by decide),args 6 (by decide),callVal]
      rw [esp_ptr R (d := VG.Impl.Dsa.X86.KeyRandom.oNonce) (by decide)]
      rfl
    let Q := fun mem (ax : BitVec 32) => ax.toNat=Spec.Dsa.signStatus (callResult s₀ t) ∧
      Spec.Rsa.bytesAt mem (argumentPointer s₀ 0) (arg s₀ 1).toNat=
        (callResult s₀ t).getD (List.replicate (arg s₀ 1).toNat 0)
    have body : WP isa deriveKey v fun u => abiPreserved v u ∧ Q u.mem (u.gpr .eax) := by
      refine WP.mono (derivingOperation_spec (allocated_derivingABI A R C) valid contextV)
        fun u ⟨V,B,ABI,_⟩ => ?_
      rw [result] at V B
      simp only [argumentPointer,args 0 (by decide),args 1 (by decide),callVal] at B
      exact ⟨ABI,V,B⟩
    have stackOf : ∀ {m m' : Mem}, Frame [below (t.gpr .esp) 112] m m' → Frame [rStack s₀] m m' := fun F => by
      rw [invocation_below A R] at F
      exact F.sub fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
    refine WP.mono (inlineInvoke_ok (Q := Q) derive_noSp derive_depth low reads writes body
      fun _ _ _ F ⟨e,B⟩ => ⟨e,by
        rw [rBytes_frame (stackOf F) (fun r hr => by
          obtain rfl := List.mem_singleton.mp hr; exact A.stackOutWide.symm) (by have := A.outBound; omega)]
        exact B⟩)
      fun u ⟨rd,wr,K,F,V,B⟩ => ?_
    rw [invocation_below A R] at F
    have Frame : VG.Frame (callWrites s₀) t.mem u.mem := F
    refine ⟨R.returned rd wr (K .esp (by simp [calleeSaved])) (deriveFrame_outer Frame),Frame,K,?_,B⟩
    apply BitVec.eq_of_toNat_eq
    rw [V,BitVec.toNat_ofNat]
    unfold Spec.Dsa.signStatus
    split <;> rfl

end VG.Proof.Dsa.X86.Comb

end

end

/-! Full correctness, constant time, and satisfiability for retained-table key generation. -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/Comb/ParametersTiming.lean`, which only this module imported.
section

/-! Public parameter preparation may branch only on the public domain values. -/

section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Comb
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

def PublicGenerator (L : CallLayout) (s t : State) : Prop :=
  CallPair L s t ∧ operandValue s L.base (.input .g) L.pLen=operandValue t L.base (.input .g) L.pLen

theorem parameters_relCT (L : CallLayout)
    (P : CallOperand L (.input .p) L.pLen) (Q : CallOperand L (.input .q) L.qLen)
    (G : (.input .g,L.pLen)∈L.inputs)
    (fits : (layout ((L.pLen+7)/8) ((L.qLen+3)/4)).size≤L.size) :
    RelCT isa (PublicGenerator L) (parameters L.pLen L.qLen) (CallPair L) := by
  have W := L.lengths
  have Gop : CallOperand L (.input .g) L.pLen := .inl ⟨_,G,Nat.le_refl _⟩
  have bound : t+L.pLen≤usedBytes := by change 14944+L.pLen≤15712; omega
  have T := CallOperand.localBuffer L t L.pLen (by decide) bound
  change RelCT isa (PublicGenerator L) (.seq (Generate.domain L.pLen L.qLen)
    (.seq (power true L.pLen L.qLen .p (.input .g) (.input .q) t)
      (Validate.isOne L.pLen (.local t)))) (CallPair L)
  refine RelCT.seq (R := PublicGenerator L) ?_ (RelCT.seq ?_
    (callOne_relCT L L.pLen (.local t) T (by omega) (by omega) L.aligned.1))
  · intro s t tr ur sf tf ⟨Pair,Eq⟩ E F
    have H := generateDomain_relCT L P Q Gop _ _ _ _ _ _ Pair E F
    have Es := (wp_result (generateDomain_ok Pair.1.moduli (Pair.1.buffers _ G) rfl) E).2.2
    have Et := (wp_result (generateDomain_ok Pair.2.moduli (Pair.2.buffers _ G) rfl) F).2.2
    exact ⟨H.1,H.2,(Es.value (Pair.1.buffers _ G) (by change StablePointer (.input .g); decide) L.extent).trans
      (Eq.trans (Et.value (Pair.2.buffers _ G) (by change StablePointer (.input .g); decide) L.extent).symm)⟩
  · apply (stagePower_relCT true L (.input .g) (.input .q) _ P Gop Q (by decide) fits).mono
      ?_ (fun _ _ H => H)
    intro s t ⟨Pair,Eq⟩
    exact ⟨Pair,fun _ => ⟨Eq,Pair.1.moduli.qValue.trans Pair.2.moduli.qValue.symm⟩,
      fun h => Bool.noConfusion h⟩

end VG.Proof.Dsa.X86.Comb
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/Comb/CheckingSizedTiming.lean`, which only this module imported.
section

/-! The comb checker branches on public shape and public parameter values. -/

section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Comb

theorem checkingSized_relCT (L : CallLayout) (digestLen : Nat)
    (P : (.input .p,L.pLen)∈L.inputs) (Q : (.input .q,L.qLen)∈L.inputs)
    (G : (.input .g,L.pLen)∈L.inputs)
    (stable : ∀ input∈L.inputs, ShapePointer input.1)
    (hd : L.digestPrefix=min digestLen (Spec.Dsa.bitLength L.q/8))
    (fits : (layout ((L.pLen+7)/8) ((L.qLen+3)/4)).size≤L.size) :
    RelCT isa (fun s t => ShapeCallReady L digestLen s ∧ ShapeCallReady L digestLen t ∧
      operandValue s L.base (.input .g) L.pLen=operandValue t L.base (.input .g) L.pLen)
      (checkSized L.pLen L.qLen) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  let R := fun s t => VG.X86.Taint.Agree (workspaceTaint false) s t ∧
    (shapeValid L.p L.q → PublicGenerator L s t)
  change RelCT isa _ (.seq (Shape.check L.pLen L.qLen) (.ite .e _ _)) _
  refine RelCT.seq (M := isa) (R := fun s t => R s t ∧ s.zf=some (!decide (shapeValid L.p L.q)) ∧
      t.zf=some (!decide (shapeValid L.p L.q))) ?_
    (fixedChoice_relCT (!decide (shapeValid L.p L.q)) ?_)
  · intro s t tr ur sf tf ⟨S,T,Eq⟩ E F
    have CT := shapeCall_relCT L digestLen P Q stable hd _ _ _ _ _ _ ⟨S,T⟩ E F
    obtain ⟨Zs,Ms,Ks,Fs⟩ := wp_result (shapeCall_ok S P Q stable hd) E
    obtain ⟨Zt,Mt,Kt,Ft⟩ := wp_result (shapeCall_ok T P Q stable hd) F
    have bound : 8248≤L.size := by have := L.extent; change 15712≤L.size at this; omega
    have Es := (S.buffers _ G).value_keep_shape Fs Ks (by decide)
      (by change ShapePointer (.input .g); decide) bound
    have Et := (T.buffers _ G).value_keep_shape Ft Kt (by decide)
      (by change ShapePointer (.input .g); decide) bound
    exact ⟨CT.1,⟨CT.2.1.1,fun h => ⟨⟨(Ms h).ready,(Mt h).ready⟩,Es.trans (Eq.trans Et.symm)⟩⟩,Zs,Zt⟩
  · by_cases valid : shapeValid L.p L.q
    · simp only [valid,decide_true,Bool.not_true,Bool.false_eq_true,ite_false]
      exact (RelCT.seq (parameters_relCT L (.inl ⟨_,P,Nat.le_refl _⟩)
        (.inl ⟨_,Q,Nat.le_refl _⟩) G fits)
        (result_relCT.mono (fun _ _ H => H.workspace) (fun _ _ h => h))).mono
        (fun _ _ H => H.2 valid) (fun _ _ h => h)
    · simp only [valid,decide_false,Bool.not_false,ite_true]
      exact verifyFailure_relCT.mono (fun _ _ H => H.1) (fun _ _ h => h)

end VG.Proof.Dsa.X86.Comb
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/Comb/CheckingOperationTiming.lean`, which only this module imported.
section

/-! Whole checker timing reuses the common entry and dispatch proof. -/

section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Comb
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

theorem checkingInstalled_generator {s t : State} (A : CheckingABI s)
    (I : Installed (argumentPointer s 4) ((arg s 5).toNat*8) Generate.checkArguments 0 2 3 s t) :
    operandValue t (argumentPointer s 4) (.input .g) (arg s 2).toNat=(checkingParams s).g := by
  have L : 0<(arg s 2).toNat ∧ 0<(arg s 3).toNat := by
    have H := A.lengths; unfold Spec.Dsa.lengthsValid at H; omega
  obtain ⟨Params,Bytes⟩ := I.input (by decide : (0,.p)∈Generate.checkArguments) A.keyBound
    (by rw [A.rd,A.wr]; simp) A.keyScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowKey.symm)
  obtain ⟨Qptr,Gptr,_⟩ := I.pointers (by decide)
  obtain ⟨_,_,_,Value⟩ := parameters_buffers Params L.1 L.2
    (by have := A.keyLength; omega) Bytes Qptr Gptr
  exact (congrArg (fun k : Spec.Dsa.Params => k.g) Value).symm

theorem checkingOperation_agrees {s t : State} (A : CheckingABI s) (B : CheckingABI t)
    (args : ∀ i<6, arg s i=arg t i) (SP : s.gpr .esp=t.gpr .esp)
    (P : (checkingParams s).p=(checkingParams t).p)
    (Q : (checkingParams s).q=(checkingParams t).q)
    (G : (checkingParams s).g=(checkingParams t).g)
    {tr ur : List Leak} {sf tf : State}
    (E : Exec isa checkParameters s tr sf) (F : Exec isa checkParameters t ur tf) : tr=ur := by
  let L := checkingLayout s A
  have LayoutEq := checkingLayout_eq A B args SP P Q
  have DL := args 2 (by decide)
  refine checkingOperationWith_agrees A B args SP P Q checkSized ?_ E F
  apply (checkingSized_relCT L (arg s 2).toNat
    (by simp [L,checkingLayout,checkingInputs]) (by simp [L,checkingLayout,checkingInputs])
    (by simp [L,checkingLayout,checkingInputs]) (checkingInputs_shape _ _) rfl
    (Nat.le_trans (context_fits A.lengths) (Nat.mul_le_mul_right 8 A.scratchLength))).mono ?_
      (fun _ _ h => h)
  intro u v H
  refine ⟨checkingInstalled_ready A H.1,?_,?_⟩
  · simpa only [L,LayoutEq,DL] using checkingInstalled_ready B H.2
  · have V := checkingInstalled_generator B H.2
    have Base := congrArg (fun x : BitVec 32 => x.setWidth 64) (args 4 (by decide))
    change operandValue u (argumentPointer s 4) (.input .g) (arg s 2).toNat = _
    rw [checkingInstalled_generator A H.1,G]
    simpa only [L,checkingLayout,Base,DL] using V.symm

end VG.Proof.Dsa.X86.Comb
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/Comb/CheckInvokeTiming.lean`, which only this module imported.
section

/-! The internal checker receives only public domain values. -/

section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Proof.Dsa.X86.KeyRandom VG.Impl.Dsa.X86.Comb

theorem checkInvoke_ct : CheckInvokeCT checkInvoke := by
  intro s t tr ur sf tf ⟨s₀,t₀,A,B,Pub,Key,R,S,C,D⟩ E F
  let u := (allocated 4 s).withRegions (CheckCall.callRd s₀) (CheckCall.callWr s₀)
  let v := (allocated 4 t).withRegions (CheckCall.callRd t₀) (CheckCall.callWr t₀)
  have Au : CheckingABI u := allocated_checkingABI A R C
  have Bv : CheckingABI v := allocated_checkingABI B S D
  obtain ⟨rs,ws⟩ := CheckCall.call_covers A R
  obtain ⟨rt,wt⟩ := CheckCall.call_covers B S
  obtain ⟨uf,Eu⟩ := inlineInvoke_trace rs ws ((checkingOperation_spec Au).mono (fun _ _ => trivial)) E
  obtain ⟨vf,Ev⟩ := inlineInvoke_trace rt wt ((checkingOperation_spec Bv).mono (fun _ _ => trivial)) F
  have SP := esp_of_rf R.rf (pub_rBase Pub ▸ S.rf)
  have args (i : Nat) (hi : i<6) : arg u i=arg v i := by
    rw [check_allocated_args R C i hi,check_allocated_args S D i hi]
    interval_cases i <;> simp only [CheckCall.callVal] <;> exact pub_arg Pub _ (by decide)
  have KeyEq : (rInput s₀).key=(rInput t₀).key :=
    (List.map_injective_iff.mpr (fun _ _ h => BitVec.eq_of_toNat_eq h)) Key
  have Params : checkingParams u=checkingParams v := by
    rw [check_allocated_params A R C,check_allocated_params B S D,
      pub_arg Pub 5 (by decide),pub_arg Pub 6 (by decide),KeyEq]
  exact ⟨checkingOperation_agrees Au Bv args (by change s.gpr .esp-4=t.gpr .esp-4; rw [SP])
    (congrArg Spec.Dsa.Params.p Params) (congrArg Spec.Dsa.Params.q Params)
    (congrArg Spec.Dsa.Params.g Params) Eu Ev,trivial⟩

end VG.Proof.Dsa.X86.Comb
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/Comb/DeriveSizedTiming.lean`, which only this module imported.
section

/-! # Derivation branches only on the public domain shape -/

section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Comb

theorem deriveSized_relCT (L : CallLayout) (out : BitVec 32) (digestLen : Nat)
    (P : (.input .p, L.pLen) ∈ L.inputs) (Q : (.input .q, L.qLen) ∈ L.inputs)
    (G : (.input .g, L.pLen) ∈ L.inputs) (X : (.input .nonce, L.qLen) ∈ L.inputs)
    (Params : (.input .p, 2 * L.pLen + L.qLen) ∈ L.inputs)
    (stable : ∀ input ∈ L.inputs, ShapePointer input.1)
    (hd : L.digestPrefix = min digestLen (Spec.Dsa.bitLength L.q / 8))
    (ho : out.toNat + (3 * L.pLen + 2 * L.qLen) ≤ 2 ^ 32)
    (A : Region.Disjoint ⟨L.base, L.size⟩ ⟨out.setWidth 64, 3 * L.pLen + 2 * L.qLen⟩)
    (fits : (layout ((L.pLen+7)/8) ((L.qLen+3)/4)).size≤L.size) :
    RelCT isa (fun s t => ShapeCallReady L digestLen s ∧ ShapeCallReady L digestLen t ∧
      KeyOutputReady L out s ∧ KeyOutputReady L out t ∧
      ContextReady L s ∧ ContextReady L t ∧ DomainReady L s ∧ DomainReady L t)
      (deriveSized L.pLen L.qLen) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  let R := fun s t => (shapeValid L.p L.q → CallPair L s t) ∧
    Scr s L.base L.size ∧ Scr t L.base L.size ∧ KeyOutputReady L out s ∧ KeyOutputReady L out t ∧
      ContextReady L s ∧ ContextReady L t ∧ DomainReady L s ∧ DomainReady L t
  change RelCT isa _ (.seq (Shape.check L.pLen L.qLen) (.ite .e _ _)) _
  refine RelCT.seq (M := isa) (R := fun s t => R s t ∧ s.zf = some (!decide (shapeValid L.p L.q)) ∧
      t.zf = some (!decide (shapeValid L.p L.q))) ?_
    (fixedChoice_relCT (!decide (shapeValid L.p L.q)) ?_)
  · intro s t tr ur sf tf ⟨S, T, Os, Ot, Cs, Ct, Ds, Dt⟩ E F
    have Trace := (shapeCall_relCT L digestLen P Q stable hd _ _ _ _ _ _ ⟨S, T⟩ E F).1
    obtain ⟨Zs, Ms, Ks, Fs⟩ := wp_result (shapeCall_ok S P Q stable hd) E
    obtain ⟨Zt, Mt, Kt, Ft⟩ := wp_result (shapeCall_ok T P Q stable hd) F
    have keep {a b : State} (A : ShapeCallReady L digestLen a)
        (K : Keeps shapeClob a b) (O : Outs L.base shapeRanges a.mem b.mem)
        (C : ContextReady L a) (D : DomainReady L a) : ContextReady L b ∧ DomainReady L b := by
      have bound : 8248≤L.size := by have := L.extent; change 15712≤L.size at this; omega
      have V := (A.buffers _ G).value_keep_shape O K (by decide)
        (by change ShapePointer (.input .g); decide) bound
      unfold ContextReady DomainReady at *
      rw [V]
      refine ⟨?_,D⟩
      apply canonical_outs (supported_widths L.widths) C
        (Outs.of_outside (rs := [(0,8248)]) (shapeFrame_outside O) (by simp))
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      apply Or.inr
      change 8248≤context ((L.pLen+7)/8)
      unfold context; split <;> omega
    have Sc := keep S Ks Fs Cs Ds
    have Tc := keep T Kt Ft Ct Dt
    exact ⟨Trace, ⟨fun h => ⟨(Ms h).ready, (Mt h).ready⟩,
      S.scr.of_keeps Ks (by decide), T.scr.of_keeps Kt (by decide), Os.shape Fs Ks, Ot.shape Ft Kt,
      Sc.1,Tc.1,Sc.2,Tc.2⟩, Zs, Zt⟩
  · by_cases valid : shapeValid L.p L.q
    · simp only [valid, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
      exact (deriveBody_relCT L out P Q G X Params ho A fits).mono
        (fun _ _ H => ⟨H.1 valid, H.2.2.2⟩) (fun _ _ h => h)
    · simp only [valid, decide_false, Bool.not_false, ite_true]
      exact (deriveFailure_relCT L.pLen L.qLen L.base L.size L.saved).mono
        (fun _ _ H => ⟨H.2.1, H.2.2.1, H.2.2.2.1.pointer.trans H.2.2.2.2.1.pointer.symm⟩) (fun _ _ h => h)

end VG.Proof.Dsa.X86.Comb
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/Comb/DerivingOperationTiming.lean`, which only this module imported.
section

/-! Whole internal derivation timing retains the validated table through entry and dispatch. -/

section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Comb
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

theorem deriveContext_prefix {s : State} (A : DerivingABI s) {a b : Mem}
    (O : Outside (argumentPointer s 7) 0 8272 a b) (C : deriveContext s a) : deriveContext s b := by
  apply canonical_outs (supported_widths A.lengths) C (Outs.of_outside (rs := [(0,8272)]) O (by simp))
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  apply Or.inr
  change 8272≤context (((arg s 4).toNat+7)/8)
  unfold context; split <;> omega

theorem derivingInstalled_context {s t : State} (A : DerivingABI s)
    (I : Installed (argumentPointer s 7) ((arg s 8).toNat*8) Generate.deriveArguments 2 4 6 s t)
    (C : deriveContext s t.mem) (D : validParameters s) :
    ContextReady (derivingLayout s A) t ∧ DomainReady (derivingLayout s A) t := by
  have L : 0<(arg s 4).toNat ∧ 0<(arg s 6).toNat := by
    have H := A.lengths; unfold Spec.Dsa.lengthsValid at H; omega
  obtain ⟨Params,Bytes⟩ := I.input (by decide : (2,.p)∈Generate.deriveArguments) A.keyBound
    (by rw [A.rd,A.wr]; simp) A.keyScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowKey.symm)
  obtain ⟨Qptr,Gptr,_⟩ := I.pointers (by decide)
  obtain ⟨_,_,_,Value⟩ := parameters_buffers Params L.1 L.2
    (by have := A.keyLength; omega) Bytes Qptr Gptr
  have G := (congrArg (fun k : Spec.Dsa.Params => k.g) Value).symm
  change operandValue t (argumentPointer s 7) (.input .g) (arg s 4).toNat=(derivingParams s).g at G
  unfold ContextReady DomainReady
  dsimp only [derivingLayout]
  rw [G]
  refine ⟨C,?_⟩
  have H := (generationChecks_spec (parametersValid_shape D)).mpr D
  exact H

theorem derivingOperation_agrees {s t : State} (A : DerivingABI s) (B : DerivingABI t)
    (args : ∀ i<9, arg s i=arg t i) (SP : s.gpr .esp=t.gpr .esp)
    (P : (derivingParams s).p=(derivingParams t).p)
    (Q : (derivingParams s).q=(derivingParams t).q)
    (Ds : validParameters s) (Dt : validParameters t)
    (Cs : deriveContext s s.mem) (Ct : deriveContext t t.mem)
    {tr ur : List Leak} {sf tf : State}
    (E : Exec isa deriveKey s tr sf) (F : Exec isa deriveKey t ur tf) : tr=ur := by
  let L := derivingLayout s A
  have LayoutEq := derivingLayout_eq A B args SP P Q
  have DL := args 4 (by decide)
  refine derivingOperationWith_agrees A B args SP P Q deriveSized (deriveContext s) (deriveContext t)
    Cs Ct (deriveContext_prefix A) (deriveContext_prefix B) ?_ E F
  apply (deriveSized_relCT L (arg s 0) (arg s 4).toNat
    (by simp [L,derivingLayout,derivingInputs]) (by simp [L,derivingLayout,derivingInputs])
    (by simp [L,derivingLayout,derivingInputs]) (by simp [L,derivingLayout,derivingInputs])
    (by simp [L,derivingLayout,derivingInputs]) (derivingInputs_shape _ _) rfl
    (by change (arg s 0).toNat+(3*(arg s 4).toNat+2*(arg s 6).toNat)≤_
        rw [←A.outLength]; exact A.outBound)
    (by change Region.Disjoint _ ⟨argumentPointer s 0,3*(arg s 4).toNat+2*(arg s 6).toNat⟩
        rw [←A.outLength]; exact A.outScratch.symm)
    (Nat.le_trans (context_fits A.lengths) (Nat.mul_le_mul_right 8 A.scratchLength))).mono ?_
      (fun _ _ h => h)
  intro u v ⟨I,J,Ci,Cj⟩
  have SI := derivingInstalled_context A I Ci Ds
  have TJ := derivingInstalled_context B J Cj Dt
  refine ⟨derivingInstalled_ready A I,?_,derivingInstalled_output A I,?_,SI.1,?_,SI.2,?_⟩
  · simpa only [L,LayoutEq,DL] using derivingInstalled_ready B J
  · simpa only [L,LayoutEq,args 0 (by decide)] using derivingInstalled_output B J
  · simpa only [L,LayoutEq] using TJ.1
  · simpa only [L,LayoutEq] using TJ.2

end VG.Proof.Dsa.X86.Comb
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/Comb/DeriveInvokeTiming.lean`, which only this module imported.
section

/-! The prevalidated internal body runs with public parameters and a secret scalar. -/

section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Proof.Dsa.X86.KeyRandom VG.Impl.Dsa.X86.Comb

theorem deriveInvoke_ct : DeriveInvokeCT deriveInvoke := by
  intro s t tr ur sf tf ⟨s₀,t₀,A,B,Pub,Key,R,S,C,D,_,OkS,OkT,Cs,Ct⟩ E F
  let u := (allocated 4 s).withRegions (callRd s₀) (callWr s₀)
  let v := (allocated 4 t).withRegions (callRd t₀) (callWr t₀)
  have Au : DerivingABI u := allocated_derivingABI A R C
  have Bv : DerivingABI v := allocated_derivingABI B S D
  have Vu := derive_allocated_valid A R C OkS
  have Vv := derive_allocated_valid B S D OkT
  have Cu := derive_allocated_context A R C Cs
  have Cv := derive_allocated_context B S D Ct
  obtain ⟨rs,ws⟩ := call_covers A R
  obtain ⟨rt,wt⟩ := call_covers B S
  obtain ⟨uf,Eu⟩ := inlineInvoke_trace rs ws ((derivingOperation_spec Au Vu Cu).mono (fun _ _ => trivial)) E
  obtain ⟨vf,Ev⟩ := inlineInvoke_trace rt wt ((derivingOperation_spec Bv Vv Cv).mono (fun _ _ => trivial)) F
  have SP := esp_of_rf R.rf (pub_rBase Pub ▸ S.rf)
  have args (i : Nat) (hi : i<9) : arg u i=arg v i := by
    rw [derive_allocated_args R C i hi,derive_allocated_args S D i hi]
    interval_cases i <;> simp only [callVal,SP] <;> exact pub_arg Pub _ (by decide)
  have KeyEq : (rInput s₀).key=(rInput t₀).key :=
    (List.map_injective_iff.mpr (fun _ _ h => BitVec.eq_of_toNat_eq h)) Key
  have Params : derivingParams u=derivingParams v := by
    rw [derive_allocated_params A R C,derive_allocated_params B S D,
      pub_arg Pub 5 (by decide),pub_arg Pub 6 (by decide),KeyEq]
  exact ⟨derivingOperation_agrees Au Bv args (by change s.gpr .esp-4=t.gpr .esp-4; rw [SP])
    (congrArg Spec.Dsa.Params.p Params) (congrArg Spec.Dsa.Params.q Params) Vu Vv Cu Cv Eu Ev,trivial⟩

end VG.Proof.Dsa.X86.Comb
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb

theorem key_verified : Verified target generateKey (Spec.Dsa.generateKeyContract abi 232) :=
  KeyRandom.verifiedWith checkInvoke deriveInvoke keyInvariant_stable
    check_invoke_noSp derive_invoke_noSp checkInvoke_ct deriveInvoke_ct

end VG.Proof.Dsa.X86.Comb
