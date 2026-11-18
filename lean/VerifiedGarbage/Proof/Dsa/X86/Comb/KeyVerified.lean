module

public import Init.Prelude
public import VerifiedGarbage.Impl.Dsa.X86.CombKey
public import VerifiedGarbage.Spec.Dsa.Generate
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Dsa.X86.Comb.GenerationStack
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Verified
public import VerifiedGarbage.Impl.Dsa.X86.CombGenerate
import VerifiedGarbage.Proof.Dsa.X86.Comb.StageTiming
import VerifiedGarbage.Proof.Dsa.X86.GenerateTiming
import VerifiedGarbage.Proof.Dsa.X86.GenerateDomain
import VerifiedGarbage.Proof.Dsa.X86.CallValidationTiming
import VerifiedGarbage.Proof.Dsa.X86.KeyTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Impl.Dsa.X86.Comb
public import VerifiedGarbage.Proof.Dsa.X86.CallTiming
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Dsa.X86.ShapeCall
import VerifiedGarbage.Proof.Dsa.X86.VerifySizedTiming
import VerifiedGarbage.Proof.Dsa.X86.BodyTiming
import VerifiedGarbage.Proof.Dsa.X86.OutputTiming
import VerifiedGarbage.Proof.Dsa.X86.FailureTiming
import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
public import VerifiedGarbage.Proof.Dsa.X86.CheckingOperationCT
import VerifiedGarbage.Proof.Dsa.X86.Comb.Checking
import VerifiedGarbage.Proof.Dsa.X86.ParameterBuffers
import VerifiedGarbage.Proof.Dsa.X86.InstalledInputs
import VerifiedGarbage.Proof.Dsa.X86.ABIResources
import VerifiedGarbage.Proof.Dsa.X86.CheckingABI
import VerifiedGarbage.Proof.Dsa.X86.Installed
public import VerifiedGarbage.Proof.Dsa.X86.Comb.KeyInvariant
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckInvoke
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.AllocatedArgs
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.InlineInvoke
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.InvokeFrame
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CallResult
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.InvokeTiming
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Context
import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.List.Basic
import VerifiedGarbage.Proof.Dsa.X86.DeriveFailureTiming
public import VerifiedGarbage.Proof.Dsa.X86.KeyOutputReady
public import VerifiedGarbage.Proof.Dsa.X86.Comb.Core
import VerifiedGarbage.Proof.Dsa.X86.Comb.DeriveCompute
import VerifiedGarbage.Proof.Dsa.X86.Comb.CanonicalFrame
import VerifiedGarbage.Proof.Dsa.X86.ValidateRange
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.X86.ShapeSavedFrame
public import VerifiedGarbage.Proof.Dsa.X86.Comb.Deriving
public import VerifiedGarbage.Proof.Dsa.X86.DerivingOperationCT
import VerifiedGarbage.Proof.Dsa.X86.GenerateParameters
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Invoke
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CallPre
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckPre

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
