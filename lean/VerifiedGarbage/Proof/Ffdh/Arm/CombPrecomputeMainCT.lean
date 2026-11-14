module

public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeCTState
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputePrefix
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeMetadataCT
public import VerifiedGarbage.Impl.Bignum.Arm.MontCall
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyPrepareLaw
public import VerifiedGarbage.Impl.Ffdh.Arm.NormalizedPrepare
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
import VerifiedGarbage.Proof.Ffdh.Arm.NormalizedPrepareAt
import VerifiedGarbage.Proof.Ffdh.Arm.NormalizedPrepareCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpSharedCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.Arm.CachedSampleBound
import VerifiedGarbage.Proof.Ffdh.Arm.CachedSamplePolicy
public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeCore
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeTableState
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeBasis
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProductState
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProductRound
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeControlCT
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProductLoadCT
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeSquaresCT
import VerifiedGarbage.Proof.Bignum.Arm.MontCallOpCT
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProduct
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProductLoad
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProducts
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProductInit
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeSquareState
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeBasisStore
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeSquares
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeInitialCT
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeTableInit
import VerifiedGarbage.Proof.Rsa.FixedBaseCombTable
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeInitialStore
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeMontgomeryOutCT
meta import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
meta import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeCTState
public import VerifiedGarbage.Proof.Ffdh.Arm.VettedBoundInstance
meta import VerifiedGarbage.Proof.Ffdh.Arm.VettedBoundInstance
meta import VerifiedGarbage.Proof.Ffdh.Arm.Context
meta import VerifiedGarbage.Proof.Ffdh.Arm.CachedSamplePolicy
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeMontgomeryOut
meta import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeMontgomeryOut

/-! ### `Ffdh.Arm.CombPrecomputePrefixCT`, which only this module used -/

section

/-! ### `Ffdh.Arm.NormalizedPrepareAtCT`, which only this module used -/

section

/-! # The shared native key-preparation boundary hides modulus values -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem normalizedPrepareAt24_ct (backend : MontBackend) {p : Inputs} {slots : List Nat}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots)
    (large : 1 < p.P) (odd : p.P % 2 = 1) (normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P) :
    RelCT isa (fun s t => (Context p slots s ∧ KeyCallMemory p s) ∧
      (Context p slots t ∧ KeyCallMemory p t) ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.NormalizedPrepare.prepareAt
        (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) 24) (fun _ _ => True) := by
  have family (sp0 : BitVec 32) :
      RelCT isa (fun s t => (Context p slots s ∧ KeyCallMemory p s ∧ s.sp = sp0) ∧
        (Context p slots t ∧ KeyCallMemory p t ∧ t.sp = sp0) ∧ s.sp = t.sp)
        (VG.Impl.Ffdh.Arm.NormalizedPrepare.prepareAt
          (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) 24) (fun _ _ => True) := by
    let correct := fun o a b ho ha hb v input => backend.correct v (base := p.base) (len := p.len) (w := p.w) (o := o) (a := a) (b := b) input ho ha hb
    let K := TwoExp.sharedMontgomery p.base sp0 p.len p.w backend.name backend.mul correct backend.stackOk
    have timing : TwoExp.MontgomeryTiming K :=
      TwoExp.sharedMontgomeryTiming p.base sp0 p.len p.w backend.name backend.mul correct backend.stackOk
        (fun _ _ _ ho ha hb => backend.rawCT ho ha hb)
    have argsInput (s : State) (h : Context p slots s ∧ KeyCallMemory p s ∧ s.sp = sp0) :
        WP isa (.block (VG.Impl.Ffdh.Arm.Domain.prepareArgs 24)) s fun u =>
          PrepareInput p.base p.domain p.len p.k u ∧ TwoExp.CallReady p.base sp0 p.len u ∧ 2 ^ (64 * (p.w - 1)) ≤ Spec.Rsa.os2ip (Spec.Rsa.bytesAt u.mem (State.addr p.domain) p.k) := by
      refine WP.mono (prepareArgs_ok s 24 h.1 stable h24 h32 h0) ?_
      rintro u ⟨contextU, stack, _, countU, _, _, restU⟩
      have sourceU := contextU.pBytes
      have bytes : Spec.Rsa.bytesAt u.mem (State.addr p.domain) p.k = p.dom.take p.k := by
        simpa only [p.pLength] using sourceU.bytes
      refine ⟨?_, ⟨(h.2.1.after restU).stack, restU.sp.trans h.2.2⟩, by rw [bytes]; exact normalized⟩
      exact ⟨contextU.workspace, by rw [stack.savedOutput]; exact stack, contextU.ptr, countU,
        p.minLength, p.maxLength, p.publicSpace,
        by rw [← p.pLength]; exact sourceU.fits,
        by rw [← p.pLength]; exact sourceU.readable,
        by rw [← p.pLength]; exact sourceU.separate,
        by rw [bytes]; exact large, by rw [bytes]; exact odd⟩
    unfold VG.Impl.Ffdh.Arm.NormalizedPrepare.prepareAt
    exact relCT_chain ((prepareArgs_ct 24).mono (fun _ _ h => h.2.2) (fun _ _ h => h))
      argsInput argsInput (normalizedPrepare_ct K timing p.width.2.2.2.2)
  intro s t tr1 tr2 u v h e1 e2
  exact family s.sp s t tr1 tr2 u v
    ⟨⟨h.1.1, h.1.2, rfl⟩, ⟨h.2.1.1, h.2.1.2, h.2.2.symm⟩, h.2.2⟩ e1 e2

end VG.Proof.Ffdh.Arm

end

end


/-! Public recognition and policy metadata fix the precomputation schedule. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont

private def Prepared (p : Inputs) (s : State) : Prop :=
  Context p slots s ∧ VettedGroups.environment.holds p s

private def Bounded (p : Inputs) (s : State) : Prop :=
  Locals p.base p.len s ∧ s.mem.readW (off (State.addr s.sp) 4) 32=p.output ∧
    s.mem.readW (off (State.addr s.sp) 20) 32=BitVec.ofNat 32 (Proof.Ffdh.ScalarWidth.width (bits p)) ∧
    s.mem.readW (off (State.addr s.sp) 68) 32=(Proof.Ffdh.ScalarWidth.mask (bits p)).setWidth 32

theorem prefix_ct (backend : MontBackend) {p : Inputs} {sp : BitVec 32}
    (valid : Spec.Ffdh.domainValid p.k p.dom=true) :
    RelCT isa (fun s t => EnterInput p sp s ∧ EnterInput p sp t ∧
      VettedGroups.environment.publicRel s t ∧ s.sp=t.sp)
      (prefixCode backend) (fun _ _ => True) := by
  have modulusValid := Proof.Ffdh.domainValid_mod valid
  change Spec.Rsa.modulusValid p.P p.k=true at modulusValid
  have facts := Proof.Bignum.valid_facts modulusValid p.minLength
  have params : Spec.Ffdh.parametersValid (Spec.Ffdh.domainOf p.k p.dom)=true := by
    have h := valid
    unfold Spec.Ffdh.domainValid at h
    simp only [Bool.and_eq_true] at h
    exact h.1
  have positive : 0<bits p := CachedSample.generation_positive params
  have bound : bits p≤8192 := CachedSample.bits_bound p
  have prepare (s : State) (h : EnterInput p sp s) :
      WP isa (VG.Impl.Ffdh.Arm.NormalizedPrepare.prepareAt
        (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) 24) s (Prepared p) := by
    refine WP.mono_syms (normalizedPrepareAt24_ok backend s h.context h.calls (by decide)
      (by decide) (by decide) (by decide) facts.2.1 facts.1 facts.2.2) ?_
    rintro u ⟨context,_,_,_,frame,rest⟩ syms
    refine ⟨context,VettedGroups.environment.stable h.environment (frame.sub ?_) rest syms⟩
    intro r hr
    simp only [keyPrepareWrites,prepareAtWrites,prepareWrites,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false,or_assoc] at hr
    rcases hr with rfl|rfl|rfl|rfl
    · exact ⟨_,by simp [keyCallWrites,keyWrites],fun _ h => h⟩
    · exact ⟨⟨State.addr s.sp,72⟩,by simp [keyCallWrites,keyWrites],Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨State.addr s.sp,72⟩,by simp [keyCallWrites,keyWrites],Offset.sub_base _ (by decide)⟩
    · exact ⟨_,by simp [keyCallWrites,keyWrites],fun _ h => h⟩
  have bounded (s : State) (h : Prepared p s) : WP isa VettedBound.code s (Bounded p) := by
    refine WP.mono (VettedBound.law.correct s h.1 h.2 facts.2.2 facts.1
      (by decide) (by intro d hd; revert d; decide) (by decide) (by decide) (by decide) (by decide)) ?_
    rintro t ⟨context,width,mask,_,_⟩
    have widthEq : (ScalarLayout.vetted p).width=Proof.Ffdh.ScalarWidth.width (bits p) := by
      have value := CachedSample.layout_width p positive
      unfold Proof.Ffdh.ScalarWidth.width
      change (ScalarLayout.vetted p).width=max 1 ((bits p+7)/8)
      rw [Nat.max_eq_right (by omega_using [positive])]
      exact value
    rw [widthEq] at width
    exact ⟨context.locals,context.saved 4 (by simp [slots]),width,mask⟩
  have prepareTrace := normalizedPrepareAt24_ct backend (p:=p) (slots:=slots)
    (by decide) (by decide) (by decide) (by decide) facts.2.1 facts.1 facts.2.2
  have preparedCT := prepareTrace.mono
    (P':=fun (s t : State) => EnterInput p sp s ∧ EnterInput p sp t ∧ VettedGroups.environment.publicRel s t ∧ s.sp=t.sp)
    (fun _ _ h => ⟨⟨h.1.context,h.1.calls⟩,⟨h.2.1.context,h.2.1.calls⟩,h.2.2.2⟩) (fun _ _ _ => trivial)
  have stage := (relCT_keep_sp preparedCT (fun _ _ h => h.2.2.2)).wpDep
    (fun s t h => ⟨prepare s h.1,prepare t h.2.1⟩)
  have preserved : RelCT isa (fun s t => EnterInput p sp s ∧ EnterInput p sp t ∧
      VettedGroups.environment.publicRel s t ∧ s.sp=t.sp)
      (VG.Impl.Ffdh.Arm.NormalizedPrepare.prepareAt
        (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) 24)
      (fun s t => Prepared p s ∧ Prepared p t ∧ VettedGroups.environment.publicRel s t ∧ s.sp=t.sp) := by
    intro s t tr1 tr2 u v h e1 e2
    obtain ⟨trace,_sp,_a,_b,_eq,left,right⟩ := stage _ _ _ _ _ _ h e1 e2
    exact ⟨trace,left,right,VettedGroups.environment.public_stable h.2.2.1 (Exec.syms e1) (Exec.syms e2),
      (Exec.rdwr e1).2.2.trans (h.2.2.2.trans (Exec.rdwr e2).2.2.symm)⟩
  have boundTrace := (VettedBound.law.ct (p:=p) (slots:=slots) (by decide)
    (by intro d hd; revert d; decide) facts.2.2 facts.1 (by decide) (by decide) (by decide) (by decide)).mono
      (P':=fun (s t : State) => Prepared p s ∧ Prepared p t ∧ VettedGroups.environment.publicRel s t ∧ s.sp=t.sp)
      (fun _ _ h => h) (fun _ _ _ => trivial)
  have boundStage := (relCT_keep_sp boundTrace (fun _ _ h => h.2.2.2)).wpDep
    (fun s t h => ⟨bounded s h.1,bounded t h.2.1⟩)
  have boundedCT : RelCT isa (fun s t => Prepared p s ∧ Prepared p t ∧
      VettedGroups.environment.publicRel s t ∧ s.sp=t.sp) VettedBound.code
      (fun s t => Bounded p s ∧ Bounded p t ∧ s.sp=t.sp) := by
    apply boundStage.mono (fun _ _ h => h)
    intro s t h
    obtain ⟨spEq,_a,_b,_old,left,right⟩ := h
    exact ⟨left,right,spEq⟩
  unfold prefixCode
  exact preserved.seq (boundedCT.seq (combMetadata_ct positive bound))

end VG.Proof.Ffdh.Arm.CombBuilder

end

end

/-! ### `Ffdh.Arm.CombPrecomputeTableCT`, which only this module used -/

section

/-! ### `Ffdh.Arm.CombPrecomputeTableLoopCT`, which only this module used -/

section

/-! ### `Ffdh.Arm.CombPrecomputeProductsCT`, which only this module used -/

section

/-! ### `Ffdh.Arm.CombPrecomputeProductLoopCT`, which only this module used -/

section

/-! Subset multiplication visits each public index once before the next basis. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/CombPrecomputeProductBodyCT.lean`, which only this module imported.
section

/-! Each public subset extension loads, multiplies, and exports at fixed public indices. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)

structure ProductBodyInput (p : Inputs) (sp : BitVec 32) (j low : Nat) (s : State) : Prop where
  core : Core p sp s
  power : Power5 p (2^(j*Spec.Rsa.FixedBaseComb.rows (bits p))) s
  table : TablePrefix p (2^j+low) s.mem
  count : ProductCount sp (2^j) low s

private structure Loaded (p : Inputs) (sp : BitVec 32) (j low : Nat) (s : State) : Prop where
  core : Core p sp s
  power : Power5 p (2^(j*Spec.Rsa.FixedBaseComb.rows (bits p))) s
  count : ProductCount sp (2^j) low s
  selected : numAt s.mem (State.addr p.base) p.w 1=entryValue p low

theorem productBody_ct (backend : MontBackend) {p : Inputs} {sp : BitVec 32} {j low : Nat}
    (bound : 2^j+low<32) :
    RelCT isa (fun s t => ProductBodyInput p sp j low s ∧ ProductBodyInput p sp j low t ∧ s.sp=t.sp)
      (.seq VG.Impl.Ffdh.Arm.CombPrecompute.productLoad
        (.seq (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul 6 1 5)
          VG.Impl.Ffdh.Arm.CombPrecompute.productStore)) (fun _ _ => True) := by
  have loaded (s : State) (h : ProductBodyInput p sp j low s) :
      WP isa VG.Impl.Ffdh.Arm.CombPrecompute.productLoad s (Loaded p sp j low) := by
    refine WP.mono (productLoad_ok (low:=low) (count:=2^j+low) s h.core h.power h.table (by omega_using [bound])
      (by have := Nat.two_pow_pos j; omega_using [this]) (by rw [h.core.memory.fixed]; exact h.count.2)) ?_
    rintro t ⟨core,power,selected,_,_,frame,_⟩
    have wide : Frame [⟨State.addr p.base,8*p.len⟩,FrameStack.belowA s.sp 48] s.mem t.mem := frame.mono (by simp)
    exact ⟨core,power,h.count.after_frame h.core.memory (product_body_arithmetic h.core.memory wide),selected⟩
  let Stored := fun s : State => Memory p sp s ∧
    s.mem.readW (off (State.addr s.sp) 36) 32=BitVec.ofNat 32 (2^j) ∧
    s.mem.readW (off (State.addr s.sp) 40) 32=BitVec.ofNat 32 low
  have multiplied (s : State) (h : Loaded p sp j low s) :
      WP isa (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul 6 1 5) s Stored := by
    refine WP.mono (product6_ok backend s h.core h.power h.selected) ?_
    rintro t ⟨core,_,_,_,frame,_⟩
    have count := h.count.after_frame h.core.memory (product_body_arithmetic h.core.memory frame)
    exact ⟨core.memory,by rw [core.memory.fixed]; exact count.1,by rw [core.memory.fixed]; exact count.2⟩
  have operand (a : Nat) (ha : a=1 ∨ a=5 ∨ a=6) : Proof.Rsa.Mont.Operand a := by
    rcases ha with rfl|rfl|rfl <;> simp [Proof.Rsa.Mont.Operand,Proof.Rsa.Mont.aAcc,Proof.Rsa.Mont.aTmp]
  have op := montCallOp_ct backend.name backend.mul (base:=p.base) (len:=p.len) (w:=p.w)
    (backend.rawCT (operand 6 (by simp)) (operand 1 (by simp)) (operand 5 (by simp)))
    (operand 6 (by simp)) (operand 1 (by simp)) (operand 5 (by simp))
  refine relCT_chain (productLoad_ct.mono
    (fun _ _ h => ⟨⟨h.1.core.memory,by rw [h.1.core.memory.fixed]; exact h.1.count.2⟩,
      ⟨h.2.1.core.memory,by rw [h.2.1.core.memory.fixed]; exact h.2.1.count.2⟩,h.2.2⟩)
    (fun _ _ h => h)) loaded loaded ?_
  exact relCT_chain (op.mono
    (fun _ _ h => ⟨h.1.core.memory.ready,h.2.1.core.memory.ready,h.1.core.memory.calls.stack,
      h.2.1.core.memory.calls.stack,power5_bound h.1.core ⟨_,h.1.power⟩,
      power5_bound h.2.1.core ⟨_,h.2.1.power⟩,h.2.2⟩) (fun _ _ _ => trivial))
    multiplied multiplied productStore_ct

end VG.Proof.Ffdh.Arm.CombBuilder
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm

private theorem productRound_ct (backend : MontBackend) {p : Inputs} {sp : BitVec 32} {j low : Nat}
    (bound : 2^j+low<32) :
    RelCT isa (fun s t => ProductBodyInput p sp j low s ∧ ProductBodyInput p sp j low t ∧ s.sp=t.sp)
      (.seq VG.Impl.Ffdh.Arm.CombPrecompute.productLoad
        (.seq (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul 6 1 5)
          (.seq VG.Impl.Ffdh.Arm.CombPrecompute.productStore
            (.block VG.Impl.Ffdh.Arm.CombPrecompute.productNext)))) (fun _ _ => True) := by
  have grouped := (relCT_keep_sp (productBody_ct backend (p:=p) (sp:=sp) bound) (fun _ _ h => h.2.2)).seq productNext_ct
  intro s t tr1 tr2 u v h e1 e2
  cases e1 with
  | seq load1 tail1 =>
    cases tail1 with
    | seq op1 tail1 =>
      cases tail1 with
      | seq store1 next1 =>
        cases e2 with
        | seq load2 tail2 =>
          cases tail2 with
          | seq op2 tail2 =>
            cases tail2 with
            | seq store2 next2 =>
              simpa only [List.append_assoc] using grouped _ _ _ _ _ _ h
                (.seq (.seq load1 (.seq op1 store1)) next1)
                (.seq (.seq load2 (.seq op2 store2)) next2)

theorem productsLoop_ct (backend : MontBackend) {p : Inputs} {sp : BitVec 32} {j start : Nat}
    (hj : j<5) (hstart : start<2^j) :
    RelCT isa (fun s t => ProductBodyInput p sp j start s ∧ ProductBodyInput p sp j start t ∧ s.sp=t.sp)
      (.loop (.seq VG.Impl.Ffdh.Arm.CombPrecompute.productLoad
        (.seq (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul 6 1 5)
          (.seq VG.Impl.Ffdh.Arm.CombPrecompute.productStore
            (.block VG.Impl.Ffdh.Arm.CombPrecompute.productNext)))) .ne) (fun _ _ => True) := by
  have high : 2^j≤16 := Nat.pow_le_pow_right (n:=2) (i:=j) (j:=4) (by decide) (by omega_using [hj])
  let I := fun k s t => ∃low, low+k=2^j ∧ 0<k ∧
    ProductBodyInput p sp j low s ∧ ProductBodyInput p sp j low t ∧ s.sp=t.sp
  have step : ∀k, RelCT isa (I k)
      (.seq VG.Impl.Ffdh.Arm.CombPrecompute.productLoad
        (.seq (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul 6 1 5)
          (.seq VG.Impl.Ffdh.Arm.CombPrecompute.productStore
            (.block VG.Impl.Ffdh.Arm.CombPrecompute.productNext))))
      (fun u v => isa.eval .ne u=isa.eval .ne v ∧ (isa.eval .ne u=some false → True) ∧
        (isa.eval .ne u=some true → ∃m<k,I m u v)) := by
    intro k s t tr1 tr2 u v h e1 e2
    obtain ⟨low,parts,positive,left,right,spEq⟩ := h
    have bound : 2^j+low<32 := by omega_using [high, parts, positive]
    obtain ⟨trace,sp'⟩ := relCT_keep_sp (productRound_ct backend (p:=p) (sp:=sp) bound) (fun _ _ h => h.2.2)
      s t tr1 tr2 u v ⟨left,right,spEq⟩ e1 e2
    obtain ⟨_,_,run1,core1,power1,table1,count1,z1,_,_,_⟩ := product_round_ok backend s
      left.core hj (by omega_using [parts, positive]) left.power left.table bound left.count
    obtain ⟨_,_,run2,core2,power2,table2,count2,z2,_,_,_⟩ := product_round_ok backend t
      right.core hj (by omega_using [parts, positive]) right.power right.table bound right.count
    obtain ⟨_,rfl⟩ := Exec.det e1 run1
    obtain ⟨_,rfl⟩ := Exec.det e2 run2
    refine ⟨trace,?_,fun _ => trivial,?_⟩
    · change some (!u.z)=some (!v.z)
      rw [z1,z2]
    · intro again
      have nz : low+1≠2^j := by
        intro eq
        change some (!u.z)=some true at again
        simp only [z1,eq,decide_true,Bool.not_true,Option.some.injEq,Bool.false_eq_true] at again
      exact ⟨k-1,by omega_using [positive],low+1,by omega_using [parts, positive],by omega_using [parts, positive, nz],
        ⟨core1,power1,table1,count1⟩,⟨core2,power2,table2,count2⟩,sp'⟩
  exact (RelCT.loop I step (2^j-start)).mono
    (fun _ _ h => ⟨start,by omega_using [hstart],by omega_using [hstart],h.1,h.2.1,h.2.2⟩) (fun _ _ h => h)

end VG.Proof.Ffdh.Arm.CombBuilder

end

end


/-! A public basis number fixes the entire subset-product schedule. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont

structure ProductsInput (p : Inputs) (sp : BitVec 32) (j : Nat) (s : State) : Prop where
  core : Core p sp s
  power : Power5 p (2^(j*Spec.Rsa.FixedBaseComb.rows (bits p))) s
  table : TablePrefix p (2^j+1) s.mem
  high : s.mem.readW (off (State.addr sp) 36) 32=BitVec.ofNat 32 (2^j)

theorem products_ct (backend : MontBackend) {p : Inputs} {sp : BitVec 32} {j : Nat}
    (hj : j<5) (positive : 0<j) :
    RelCT isa (fun s t => ProductsInput p sp j s ∧ ProductsInput p sp j t ∧ s.sp=t.sp)
      (VG.Impl.Ffdh.Arm.CombPrecompute.products (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul))
      (fun _ _ => True) := by
  have initialized (s : State) (h : ProductsInput p sp j s) :
      WP isa (.block [.mov .r3 (.imm 1),.addSp .r12 0,VG.Impl.Ffdh.Arm.Domain.st .r3 40]) s
        (ProductBodyInput p sp j 1) := by
    refine WP.mono (productsInit_state s h.core h.power h.high) ?_
    rintro t ⟨core,power,high,low,frame,_⟩
    have ctx : WorkspaceEq (State.addr p.output) (bytes p) s.mem t.mem := by
      apply WorkspaceEq.of_frame (by have := h.core.memory.output.fits; omega_using [this]) frame
      intro r hr
      rw [List.mem_singleton] at hr
      subst r
      exact h.core.memory.localSeparate.symm.sub_right (Offset.sub_base _ (by decide))
    have table : TablePrefix p (2^j+1) t.mem := by
      intro digit hd
      have highBound : 2^j≤16 := Nat.pow_le_pow_right (n:=2) (i:=j) (j:=4) (by decide) (by omega_using [hj])
      rw [ctx.read (entryOffset p digit) (8*p.w) (entry_bound p (by omega_using [hd, highBound]))]
      exact h.table digit hd
    exact ⟨core,power,table,high,low⟩
  have one : 1<2^j := by
    have lt := Nat.pow_lt_pow_right (by decide : 1<2) positive
    exact lt
  unfold VG.Impl.Ffdh.Arm.CombPrecompute.products
  exact relCT_chain ((controlInit_ct 1 40).mono (fun _ _ h => h.2.2) (fun _ _ h => h))
    initialized initialized (productsLoop_ct backend hj one)

end VG.Proof.Ffdh.Arm.CombBuilder

end

end

/-! Exactly four public basis rounds construct all thirty-two comb entries. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/CombPrecomputeBasisCT.lean`, which only this module imported.
section

/-! A public tooth number determines the squares and dense subset extensions. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont

structure BasisInput (p : Inputs) (sp : BitVec 32) (j : Nat) (s : State) : Prop where
  core : Core p sp s
  power : Power5 p (2^((j-1)*Spec.Rsa.FixedBaseComb.rows (bits p))) s
  table : TablePrefix p (2^j) s.mem
  high : s.mem.readW (off (State.addr sp) 36) 32=BitVec.ofNat 32 (2^j)

private structure Squared (p : Inputs) (sp : BitVec 32) (j : Nat) (s : State) : Prop where
  core : Core p sp s
  power : Power5 p (2^(j*Spec.Rsa.FixedBaseComb.rows (bits p))) s
  table : TablePrefix p (2^j) s.mem
  high : s.mem.readW (off (State.addr sp) 36) 32=BitVec.ofNat 32 (2^j)

theorem basis_ct (backend : MontBackend) {p : Inputs} {sp : BitVec 32} {j : Nat}
    (hj : j<5) (jpositive : 0<j) (positive : 0<Spec.Rsa.FixedBaseComb.rows (bits p))
    (fits : Spec.Rsa.FixedBaseComb.rows (bits p)<2^32) :
    RelCT isa (fun s t => BasisInput p sp j s ∧ BasisInput p sp j t ∧ s.sp=t.sp)
      (VG.Impl.Ffdh.Arm.CombPrecompute.basis (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul))
      (fun _ _ => True) := by
  have high : 2^j≤16 := Nat.pow_le_pow_right (n:=2) (i:=j) (j:=4) (by decide) (by omega_using [hj])
  have exponent : 2^Spec.Rsa.FixedBaseComb.rows (bits p)*2^((j-1)*Spec.Rsa.FixedBaseComb.rows (bits p))=
      2^(j*Spec.Rsa.FixedBaseComb.rows (bits p)) := by
    rw [←Nat.pow_add]
    congr 1
    calc
      _ = 1*Spec.Rsa.FixedBaseComb.rows (bits p)+(j-1)*Spec.Rsa.FixedBaseComb.rows (bits p) := by rw [Nat.one_mul]
      _ = (1+(j-1))*Spec.Rsa.FixedBaseComb.rows (bits p) := (Nat.add_mul _ _ _).symm
      _ = _ := by rw [show 1+(j-1)=j by omega_using [jpositive]]
  have squared (s : State) (h : BasisInput p sp j s) :
      WP isa (VG.Impl.Ffdh.Arm.CombPrecompute.squares (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) s
        (Squared p sp j) := by
    refine WP.mono (squares_ok backend s h.core h.power positive fits) ?_
    rintro t ⟨core,power,ctx,frame,_⟩
    rw [exponent] at power
    have table : TablePrefix p (2^j) t.mem := by
      intro digit hd
      rw [ctx.read (entryOffset p digit) (8*p.w) (entry_bound p (by omega_using [high, hd]))]
      exact h.table digit hd
    exact ⟨core,power,table,(h.core.memory.squareNarrowRead36 frame).trans h.high⟩
  have stored (s : State) (h : Squared p sp j s) :
      WP isa (.seq (.block [.ldrSp .r3 36]) (VG.Impl.Ffdh.Arm.CombPrecompute.store 5)) s (ProductsInput p sp j) := by
    refine WP.mono (basisStore_ok s h.core hj h.power h.table h.high) ?_
    rintro t ⟨core,power,table,saved,_,_,_⟩
    exact ⟨core,power,table,saved⟩
  have products := (relCT_keep_sp (products_ct backend (p:=p) (sp:=sp) hj jpositive) (fun _ _ h => h.2.2)).seq basisNext_ct
  unfold VG.Impl.Ffdh.Arm.CombPrecompute.basis
  refine relCT_chain ((squares_ct backend positive fits).mono
    (fun _ _ h => ⟨⟨h.1.core,⟨_,h.1.power⟩⟩,⟨h.2.1.core,⟨_,h.2.1.power⟩⟩,h.2.2⟩) (fun _ _ h => h))
    squared squared ?_
  apply RelCT.assoc
  exact relCT_chain (basisStore_ct.mono
    (fun _ _ h => ⟨⟨h.1.core.memory,by rw [h.1.core.memory.fixed]; exact h.1.high⟩,
      ⟨h.2.1.core.memory,by rw [h.2.1.core.memory.fixed]; exact h.2.1.high⟩,h.2.2⟩) (fun _ _ h => h))
    stored stored products

end VG.Proof.Ffdh.Arm.CombBuilder
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm

theorem tableLoop_ct (backend : MontBackend) {p : Inputs} {sp : BitVec 32} {start : Nat}
    (first : 0<start) (last : start<5) (positive : 0<Spec.Rsa.FixedBaseComb.rows (bits p))
    (fits : Spec.Rsa.FixedBaseComb.rows (bits p)<2^32) :
    RelCT isa (fun s t => BasisInput p sp start s ∧ BasisInput p sp start t ∧ s.sp=t.sp)
      (.loop (VG.Impl.Ffdh.Arm.CombPrecompute.basis
        (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) .ne) (fun _ _ => True) := by
  let I := fun k s t => ∃j, j+k=5 ∧ 0<k ∧ 0<j ∧
    BasisInput p sp j s ∧ BasisInput p sp j t ∧ s.sp=t.sp
  have step : ∀k, RelCT isa (I k) (VG.Impl.Ffdh.Arm.CombPrecompute.basis
      (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul))
      (fun u v => isa.eval .ne u=isa.eval .ne v ∧ (isa.eval .ne u=some false → True) ∧
        (isa.eval .ne u=some true → ∃m<k,I m u v)) := by
    intro k s t tr1 tr2 u v h e1 e2
    obtain ⟨j,parts,kpos,jpos,left,right,spEq⟩ := h
    have hj : j<5 := by omega_using [parts, kpos]
    obtain ⟨trace,sp'⟩ := relCT_keep_sp (basis_ct backend (p:=p) (sp:=sp) hj jpos positive fits)
      (fun _ _ h => h.2.2) s t tr1 tr2 u v ⟨left,right,spEq⟩ e1 e2
    obtain ⟨_,_,run1,core1,power1,table1,high1,z1,_,_,_⟩ := basis_ok backend s left.core hj jpos
      positive fits left.power left.table left.high
    obtain ⟨_,_,run2,core2,power2,table2,high2,z2,_,_,_⟩ := basis_ok backend t right.core hj jpos
      positive fits right.power right.table right.high
    obtain ⟨_,rfl⟩ := Exec.det e1 run1
    obtain ⟨_,rfl⟩ := Exec.det e2 run2
    refine ⟨trace,?_,fun _ => trivial,?_⟩
    · change some (!u.z)=some (!v.z)
      rw [z1,z2]
    · intro again
      have nz : j≠4 := by
        intro eq
        change some (!u.z)=some true at again
        simp only [z1,eq,decide_true,Bool.not_true,Option.some.injEq,Bool.false_eq_true] at again
      exact ⟨k-1,by omega_using [kpos],j+1,by omega_using [parts, kpos],by omega_using [parts, kpos, nz],by omega_using [],
        ⟨core1,by simpa only [Nat.add_sub_cancel] using power1,table1,high1⟩,
        ⟨core2,by simpa only [Nat.add_sub_cancel] using power2,table2,high2⟩,sp'⟩
  exact (RelCT.loop I step (5-start)).mono
    (fun _ _ h => ⟨start,by omega_using [last],by omega_using [last],first,h.1,h.2.1,h.2.2⟩) (fun _ _ h => h)

end VG.Proof.Ffdh.Arm.CombBuilder

end

end


/-! Public basis and subset loops construct every canonical context entry. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont

private structure InitialDone (p : Inputs) (sp : BitVec 32) (s : State) : Prop where
  core : Core p sp s
  power : Power5 p 1 s
  table : TablePrefix p 2 s.mem

theorem table_ct (backend : MontBackend) {p : Inputs} {sp : BitVec 32} (odd : p.P%2=1)
    (positive : 0<Spec.Rsa.FixedBaseComb.rows (bits p)) (fits : Spec.Rsa.FixedBaseComb.rows (bits p)<2^32) :
    RelCT isa (fun s t => InitialInput p sp s ∧ InitialInput p sp t ∧ s.sp=t.sp)
      (VG.Impl.Ffdh.Arm.CombPrecompute.table (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul))
      (fun _ _ => True) := by
  have initial (s : State) (h : InitialInput p sp s) :
      WP isa (VG.Impl.Ffdh.Arm.CombPrecompute.initial (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) s
        (InitialDone p sp) := by
    refine WP.mono (initial_ok backend s h.1 h.2.1 h.2.2 odd) ?_
    rintro t ⟨memory,table,value,one,modulus,r2,_,_,_⟩
    refine ⟨⟨memory,modulus,odd,r2,one⟩,?_,table⟩
    change _ = _
    rw [value,entryValue]
    have e := VG.Proof.Rsa.FixedBaseComb.exponent_tooth (bits p) 0 (by decide)
    simpa only [Nat.pow_zero,Nat.zero_mul] using congrArg
      (fun E => Spec.Rsa.powMod p.G E p.P*2^(64*p.w)%p.P) e
  have initialized (s : State) (h : InitialDone p sp s) :
      WP isa (.block [.mov .r3 (.imm 2),.addSp .r12 0,VG.Impl.Ffdh.Arm.Domain.st .r3 36]) s
        (BasisInput p sp 1) := by
    refine WP.mono (tableInit_state s h.core h.power) ?_
    rintro t ⟨core,power,saved,frame,_⟩
    have ctx := h.core.memory.controlContextEq (by decide) frame
    have table : TablePrefix p 2 t.mem := by
      intro digit hd
      rw [ctx.read (entryOffset p digit) (8*p.w) (entry_bound p (by omega_using [hd]))]
      exact h.table digit hd
    exact ⟨core,by simpa only [Nat.sub_self,Nat.zero_mul,Nat.pow_zero] using power,table,saved⟩
  unfold VG.Impl.Ffdh.Arm.CombPrecompute.table
  exact relCT_chain (initial_ct backend odd) initial initial
    (relCT_chain ((controlInit_ct 2 36).mono (fun _ _ h => h.2.2) (fun _ _ h => h)) initialized initialized
      (tableLoop_ct backend (by decide : 0<1) (by decide : 1<5) positive fits))

end VG.Proof.Ffdh.Arm.CombBuilder

end

end


/-! The complete public comb precomputation trace depends only on public inputs. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont

theorem main_ct (backend : MontBackend) {p : Inputs} {sp : BitVec 32}
    (valid : Spec.Ffdh.domainValid p.k p.dom=true) :
    RelCT isa (fun s t => EnterInput p sp s ∧ EnterInput p sp t ∧
      VettedGroups.environment.publicRel s t ∧ s.sp=t.sp)
      (VG.Impl.Ffdh.Arm.CombPrecompute.main
        (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) VettedBound.code) (fun _ _ => True) := by
  have params : Spec.Ffdh.parametersValid (Spec.Ffdh.domainOf p.k p.dom)=true := by
    have h := valid
    unfold Spec.Ffdh.domainValid at h
    simp only [Bool.and_eq_true] at h
    exact h.1
  have positiveBits : 0<bits p := CachedSample.generation_positive params
  have bitsBound : bits p≤8192 := CachedSample.bits_bound p
  have positive : 0<Spec.Rsa.FixedBaseComb.rows (bits p) := by
    unfold Spec.Rsa.FixedBaseComb.rows Spec.Rsa.FixedBaseComb.teeth
    omega_using [positiveBits]
  have fits : Spec.Rsa.FixedBaseComb.rows (bits p)<2^32 := by
    unfold Spec.Rsa.FixedBaseComb.rows Spec.Rsa.FixedBaseComb.teeth
    omega_using [bitsBound]
  have odd : p.P%2=1 := by
    have modulus := Proof.Ffdh.domainValid_mod valid
    change Spec.Rsa.modulusValid p.P p.k=true at modulus
    exact (Proof.Bignum.valid_facts modulus p.minLength).1
  have prefixWP (s : State) (h : EnterInput p sp s) : WP isa (prefixCode backend) s (InitialInput p sp) := by
    refine WP.mono (prefix_ok backend s h.context h.environment h.calls h.output
      h.workspaceSeparate h.domainSeparate (by rw [h.fixed]; exact h.localSeparate)
      (by rw [h.fixed]; exact h.callSeparate) valid) ?_
    rintro t ⟨memory,_,modulus,r2,_,_⟩
    exact ⟨by simpa only [h.fixed] using memory,modulus,r2⟩
  have prefixTrace := (relCT_keep_sp (prefix_ct backend (p:=p) (sp:=sp) valid) (fun _ _ h => h.2.2.2)).wpDep
    (fun s t h => ⟨prefixWP s h.1,prefixWP t h.2.1⟩)
  have prefixStage : RelCT isa (fun s t => EnterInput p sp s ∧ EnterInput p sp t ∧
      VettedGroups.environment.publicRel s t ∧ s.sp=t.sp) (prefixCode backend)
      (fun s t => InitialInput p sp s ∧ InitialInput p sp t ∧ s.sp=t.sp) := by
    apply prefixTrace.mono (fun _ _ h => h)
    intro s t h
    obtain ⟨spEq,_a,_b,_old,left,right⟩ := h
    exact ⟨left,right,spEq⟩
  have serialized (s : State) (h : InitialInput p sp s) :
      WP isa VG.Impl.Ffdh.Arm.CombPrecompute.montgomeryOut s (InitialInput p sp) := by
    refine WP.mono (montgomeryOut_ok s h.1) ?_
    rintro t ⟨memory,ws,_,_,_,_⟩
    have fit := h.1.ready.width ▸ h.1.ready.layout.2.2.1
    exact ⟨memory,(ws.number fit (by decide : 0<8)).trans h.2.1,
      (ws.number fit (by decide : 4<8)).trans h.2.2⟩
  have done : RelCT isa (fun _ _ => True) (VG.Impl.Ffdh.Arm.Domain.ret 1) (fun _ _ => True) := by
    apply RelCT.taint (A:=taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  have tail := relCT_chain (montgomeryOut_ct.mono
    (fun _ _ h => ⟨h.1.1,h.2.1.1,h.2.2⟩) (fun _ _ h => h)) serialized serialized
    ((table_ct backend odd positive fits).seq done)
  have grouped := prefixStage.seq tail
  intro s t tr1 tr2 u v h e1 e2
  unfold VG.Impl.Ffdh.Arm.CombPrecompute.main at e1 e2
  cases e1 with
  | seq prepare1 tail1 =>
    cases tail1 with
    | seq bound1 tail1 =>
      cases tail1 with
      | seq metadata1 tail1 =>
        cases e2 with
        | seq prepare2 tail2 =>
          cases tail2 with
          | seq bound2 tail2 =>
            cases tail2 with
            | seq metadata2 tail2 =>
              simpa only [List.append_assoc] using grouped _ _ _ _ _ _ h
                (.seq (.seq prepare1 (.seq bound1 metadata1)) tail1)
                (.seq (.seq prepare2 (.seq bound2 metadata2)) tail2)

end VG.Proof.Ffdh.Arm.CombBuilder
