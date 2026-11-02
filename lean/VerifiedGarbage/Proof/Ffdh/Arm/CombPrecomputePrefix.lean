module

public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeInput
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeMetadataAll
import VerifiedGarbage.Proof.Ffdh.Arm.NormalizedPrepareAt
public import VerifiedGarbage.Proof.Ffdh.Arm.VettedBoundInstance
import VerifiedGarbage.Proof.Ffdh.Arm.CachedSamplePolicy
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticExternal
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleEnvironment
public import VerifiedGarbage.Proof.Ffdh.ScalarWidth
public import VerifiedGarbage.Spec.Rsa.FixedBaseComb
public import VerifiedGarbage.Impl.Ffdh.Arm.NormalizedPrepare
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyCallMemory
import VerifiedGarbage.Proof.Ffdh.Arm.CachedSampleBound
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeEntry

/-! Preparation and reviewed-width metadata establish the shared comb-builder memory. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

namespace CombBuilder

theorem headerWords (m : Mem) (a : Addr) (N width rows : Nat) :
    Spec.Rsa.wordsAt (((m.writeW (off a 0) (BitVec.ofNat 64 N)).writeW
      (off a 8) (BitVec.ofNat 64 width)).writeW (off a 16) (BitVec.ofNat 64 rows)) a 3 =
      [BitVec.ofNat 64 N,BitVec.ofNat 64 width,BitVec.ofNat 64 rows] := by
  change [_,_,_]=_
  dsimp only
  rw [List.cons.injEq]
  constructor
  · rw [Mem.readW_writeW_sep (Offset.sep a (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (Offset.sep a (by decide) (by decide) (by decide)) (by decide)]
    exact Mem.readW_writeW_self64 _ _ _
  · rw [List.cons.injEq]
    constructor
    · rw [Mem.readW_writeW_sep (Offset.sep a (by decide) (by decide) (by decide)) (by decide)]
      exact Mem.readW_writeW_self64 _ _ _
    · exact congrArg (fun x => [x]) (Mem.readW_writeW_self64 _ _ _)

theorem metadataState_ok (s : State) {p : Inputs}
    (context : Context p slots s) (ready : ArithmeticReady p.base p.len p.w s)
    (calls : KeyCallMemory p s) (output : OutputBuffer p.output (bytes p) s)
    (workspaceSeparate : Region.Disjoint ⟨State.addr p.base,8*p.len⟩ ⟨State.addr p.output,bytes p⟩)
    (domainSeparate : Region.Disjoint ⟨State.addr p.domain,p.dom.length⟩ ⟨State.addr p.output,bytes p⟩)
    (localSeparate : Region.Disjoint ⟨State.addr s.sp,72⟩ ⟨State.addr p.output,bytes p⟩)
    (callSeparate : Region.Disjoint ⟨State.addr p.output,bytes p⟩ (FrameStack.belowA s.sp 48))
    (positive : 0<bits p) (bound : bits p≤8192)
    (width : s.mem.readW (off (State.addr s.sp) 20) 32=BitVec.ofNat 32 (Proof.Ffdh.ScalarWidth.width (bits p)))
    (mask : s.mem.readW (off (State.addr s.sp) 68) 32=(Proof.Ffdh.ScalarWidth.mask (bits p)).setWidth 32) :
    WP isa VG.Impl.Ffdh.Arm.CombPrecompute.metadata s fun t =>
      Memory p s.sp t ∧ WorkspaceEq (State.addr p.base) (8*p.len) s.mem t.mem ∧
      Spec.Rsa.wordsAt t.mem (State.addr p.output) 3=
        [BitVec.ofNat 64 (bits p),BitVec.ofNat 64 (Proof.Ffdh.ScalarWidth.width (bits p)),
          BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows (bits p))] ∧
      Frame (combMetadataWrites s p.output) s.mem t.mem ∧ Rest roundClobbers s t := by
  have prefixFit : 24≤bytes p := by
    unfold bytes Spec.Ffdh.generationPrecomputedWords
    omega_arith
  have headerSub : (⟨State.addr p.output,24⟩ : Region).Sub ⟨State.addr p.output,bytes p⟩ :=
    by simpa only [off,BitVec.add_zero] using (Offset.sub_base (State.addr p.output) (d:=0) (n:=24) (k:=bytes p) prefixFit)
  have headerSep := localSeparate.sub_right headerSub
  have ws : OutputBuffer p.output 24 s := ⟨by have := output.fits; omega_arith,
    by
      obtain ⟨r,hr,h⟩ := output.writable
      exact ⟨r,hr,by change (State.addr p.output-r.base).toNat+24≤r.len; change (State.addr p.output-r.base).toNat+bytes p≤r.len at h; omega_arith⟩⟩
  refine WP.mono (combMetadata_ok s context.locals ws headerSep positive bound
    (context.saved 4 (by decide)) width mask) ?_
  rintro t ⟨mem,frame,restSmall⟩
  have rest : Rest roundClobbers s t := restSmall.mono (by simp [combMetadataClobbers,roundClobbers])
  have workspaceSep : ∀ r∈combMetadataWrites s p.output,
      (⟨State.addr p.base,8*p.len⟩ : Region).Disjoint r := by
    intro r hr
    simp only [combMetadataWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · exact context.locals.separate.symm.sub_right (Offset.sub_base _ (by decide))
    · exact context.locals.separate.symm.sub_right (Offset.sub_base _ (by decide))
    · exact workspaceSeparate.sub_right headerSub
  have baseSep : ∀ r∈combMetadataWrites s p.output,
      (⟨State.addr s.sp,4⟩ : Region).Disjoint r := by
    intro r hr
    simp only [combMetadataWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · exact Offset.base_disjoint _ (by decide) (by decide)
    · exact Offset.base_disjoint _ (by decide) (by decide)
    · exact headerSep.sub_left (by simpa only [off,BitVec.add_zero] using
        (Offset.sub_base (State.addr s.sp) (d:=0) (n:=4) (k:=72) (by decide)))
  have ptr : t.gpr .r0=p.base := (restSmall.gpr .r0 (by simp [combMetadataClobbers])).trans context.ptr
  obtain ⟨readyT,workspace⟩ := ready.after_external frame workspaceSep baseSep rest ptr
  have contextT := context.after_frame frame rest ptr (by
    intro r hr
    simp only [combMetadataWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · exact context.domainStack.sub_right (Offset.sub_base _ (by decide))
    · exact context.domainStack.sub_right (Offset.sub_base _ (by decide))
    · exact domainSeparate.sub_right headerSub) (by
    intro d hd r hr
    simp only [slots,List.mem_cons,List.not_mem_nil,or_false] at hd
    simp only [combMetadataWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by decide)
    · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by decide)
    · exact headerSep.sub_left (Offset.sub_base _ (by omega_arith)))
  let initial := (s.mem.writeW (off (State.addr s.sp) 16) (BitVec.ofNat 32 (bits p))).writeW
        (off (State.addr s.sp) 44) (BitVec.ofNat 32 (Spec.Rsa.FixedBaseComb.rows (bits p)))
  have save {d : Nat} (fit : d+4≤72) :
      (((initial.writeW (off (State.addr p.output) 0) (BitVec.ofNat 64 (bits p))).writeW
        (off (State.addr p.output) 8) (BitVec.ofNat 64 (Proof.Ffdh.ScalarWidth.width (bits p)))).writeW
        (off (State.addr p.output) 16) (BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows (bits p)))).readW
        (off (State.addr s.sp) d) 32 = initial.readW (off (State.addr s.sp) d) 32 := by
    have sub := Offset.sub_base (State.addr s.sp) (d:=d) (n:=4) (k:=72) fit
    have sep (e : Nat) (he : e+8≤24) : Mem.Sep (off (State.addr s.sp) d) 4 (off (State.addr p.output) e) 8 :=
      (headerSep.sub_left sub |>.sub_right (Offset.sub_base _ he)).sep (Region.contains_self _ _) (Region.contains_self _ _)
    rw [Mem.readW_writeW_sep (sep 16 (by decide)) (by decide),
      Mem.readW_writeW_sep (sep 8 (by decide)) (by decide),
      Mem.readW_writeW_sep (sep 0 (by decide)) (by decide)]
  refine ⟨⟨contextT,readyT,calls.after rest,rest.sp,output.after rest,
    workspaceSeparate,domainSeparate,localSeparate,callSeparate,?_,?_⟩,workspace,?_,frame,rest⟩
  · rw [mem,save (d:=16) (by decide),
      Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),Mem.readW_writeW_self32]
  · rw [mem,save (d:=44) (by decide),Mem.readW_writeW_self32]
  · rw [mem]
    exact headerWords _ _ _ _ _


def prefixCode (backend : MontBackend) : Prog isa :=
  .seq (VG.Impl.Ffdh.Arm.NormalizedPrepare.prepareAt
    (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) 24)
    (.seq VettedBound.code VG.Impl.Ffdh.Arm.CombPrecompute.metadata)

theorem prefix_ok (backend : MontBackend) (s : State) {p : Inputs}
    (context : Context p slots s) (environment : VettedGroups.environment.holds p s)
    (calls : KeyCallMemory p s) (output : OutputBuffer p.output (bytes p) s)
    (workspaceSeparate : Region.Disjoint ⟨State.addr p.base,8*p.len⟩ ⟨State.addr p.output,bytes p⟩)
    (domainSeparate : Region.Disjoint ⟨State.addr p.domain,p.dom.length⟩ ⟨State.addr p.output,bytes p⟩)
    (localSeparate : Region.Disjoint ⟨State.addr s.sp,72⟩ ⟨State.addr p.output,bytes p⟩)
    (callSeparate : Region.Disjoint ⟨State.addr p.output,bytes p⟩ (FrameStack.belowA s.sp 48))
    (valid : Spec.Ffdh.domainValid p.k p.dom = true) :
    WP isa (prefixCode backend) s fun t => Memory p s.sp t ∧
      Spec.Rsa.wordsAt t.mem (State.addr p.output) 3=
        [BitVec.ofNat 64 (bits p),BitVec.ofNat 64 ((bits p+7)/8),
          BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows (bits p))] ∧
      numAt t.mem (State.addr p.base) p.w 0=p.P ∧
      numAt t.mem (State.addr p.base) p.w 4=2^(128*p.w)%p.P ∧
      Frame (combPrecomputeWrites p s) s.mem t.mem ∧ Rest roundClobbers s t := by
  have modulusValid := Proof.Ffdh.domainValid_mod valid
  change Spec.Rsa.modulusValid p.P p.k=true at modulusValid
  have facts := Proof.Bignum.valid_facts modulusValid p.minLength
  have params : Spec.Ffdh.parametersValid (Spec.Ffdh.domainOf p.k p.dom)=true := by
    have v := valid
    unfold Spec.Ffdh.domainValid at v
    simp only [Bool.and_eq_true] at v
    exact v.1
  have positive : 0<bits p := CachedSample.generation_positive params
  have bound : bits p≤8192 := CachedSample.bits_bound p
  have localNarrow {a : State} {d : Nat} (fit : d+4≤72) :
      (⟨off (State.addr a.sp) d,4⟩ : Region).Sub ⟨State.addr a.sp,72⟩ := Offset.sub_base _ fit
  have prepFrame {u : State} (f : Frame (keyPrepareWrites p s) s.mem u.mem) :
      Frame (combPrecomputeWrites p s) s.mem u.mem := by
    apply f.sub
    intro r hr
    simp only [keyPrepareWrites,prepareAtWrites,prepareWrites,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hr
    rcases hr with rfl|rfl|rfl|rfl
    · exact ⟨_,by simp [combPrecomputeWrites],fun _ h => h⟩
    · exact ⟨_,by simp [combPrecomputeWrites],localNarrow (by decide)⟩
    · exact ⟨_,by simp [combPrecomputeWrites],localNarrow (by decide)⟩
    · exact ⟨_,by simp [combPrecomputeWrites],fun _ h => h⟩
  rw [prefixCode,WP.seq_iff]
  refine WP.mono_syms (normalizedPrepareAt24_ok backend s context calls (by decide)
    (by decide) (by decide) (by decide) facts.2.1 facts.1 facts.2.2) ?_
  rintro u ⟨ctxU,readyU,modU,r2U,frameU,restU⟩ symsU
  have envU := VettedGroups.environment.stable environment
    (frameU.sub (by
      intro r hr
      simp only [keyPrepareWrites,prepareAtWrites,prepareWrites,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hr
      rcases hr with rfl|rfl|rfl|rfl
      · exact ⟨_,by simp [keyCallWrites,keyWrites],fun _ h => h⟩
      · exact ⟨_,by simp [keyCallWrites,keyWrites],localNarrow (by decide)⟩
      · exact ⟨_,by simp [keyCallWrites,keyWrites],localNarrow (by decide)⟩
      · exact ⟨_,by simp [keyCallWrites,keyWrites],fun _ h => h⟩)) restU symsU
  rw [WP.seq_iff]
  refine WP.mono (VettedBound.law.correct u ctxU envU facts.2.2 facts.1
    (by decide) (by intro d hd; revert d; decide) (by decide) (by decide) (by decide) (by decide)) ?_
  rintro v ⟨ctxV,widthV,maskV,frameV,restV⟩
  have rV := restU.trans restV
  have sepLocal : ∀r∈[⟨off (State.addr u.sp) 20,4⟩,⟨off (State.addr u.sp) 68,4⟩],
      (⟨State.addr p.base,8*p.len⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> exact ctxU.locals.separate.symm.sub_right (Offset.sub_base _ (by decide))
  have sepZero : ∀r∈[⟨off (State.addr u.sp) 20,4⟩,⟨off (State.addr u.sp) 68,4⟩],
      (⟨State.addr u.sp,4⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> exact Offset.base_disjoint _ (by decide) (by decide)
  have ptrV := ctxV.ptr
  obtain ⟨readyV,workspaceV⟩ := readyU.after_external frameV sepLocal sepZero restV ptrV
  have fit := readyU.width ▸ readyU.layout.2.2.1
  have modV := (workspaceV.number fit (by decide : 0<8)).trans modU
  have r2V := (workspaceV.number fit (by decide : 4<8)).trans r2U
  have widthEq : (ScalarLayout.vetted p).width=Proof.Ffdh.ScalarWidth.width (bits p) :=
    by
      have width := CachedSample.layout_width p positive
      unfold Proof.Ffdh.ScalarWidth.width
      change (ScalarLayout.vetted p).width= max 1 ((bits p+7)/8)
      rw [Nat.max_eq_right (by omega_arith)]
      exact width
  rw [widthEq] at widthV
  have maskEq : (ScalarLayout.vetted p).mask=(Proof.Ffdh.ScalarWidth.mask (bits p)).setWidth 32 := rfl
  rw [maskEq] at maskV
  refine WP.mono (metadataState_ok v ctxV readyV (calls.after rV) (output.after rV)
    workspaceSeparate domainSeparate (by rw [rV.sp]; exact localSeparate)
    (by rw [rV.sp]; exact callSeparate) positive bound widthV maskV) ?_
  rintro t ⟨memory,workspaceT,header,frameT,restT⟩
  have memoryT : Memory p s.sp t := by simpa only [rV.sp] using memory
  have fitV := readyV.width ▸ readyV.layout.2.2.1
  have widthNat : Proof.Ffdh.ScalarWidth.width (bits p)=(bits p+7)/8 := by
    unfold Proof.Ffdh.ScalarWidth.width
    exact Nat.max_eq_right (by omega_arith)
  rw [widthNat] at header
  refine ⟨memoryT,header,(workspaceT.number fitV (by decide : 0<8)).trans modV,
    (workspaceT.number fitV (by decide : 4<8)).trans r2V,?_,rV.trans restT⟩
  refine (prepFrame frameU).trans (?_ : Frame (combPrecomputeWrites p s) u.mem t.mem)
  refine (frameV.sub ?_).trans (frameT.sub ?_)
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;>
      exact ⟨⟨State.addr s.sp,72⟩,by simp [combPrecomputeWrites],by rw [restU.sp]; exact Offset.sub_base _ (by decide)⟩
  · intro r hr
    simp only [combMetadataWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · exact ⟨⟨State.addr s.sp,72⟩,by simp [combPrecomputeWrites],by rw [rV.sp]; exact Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨State.addr s.sp,72⟩,by simp [combPrecomputeWrites],by rw [rV.sp]; exact Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨State.addr p.output,bytes p⟩,by simp [combPrecomputeWrites],Region.sub_prefix (by unfold bytes Spec.Ffdh.generationPrecomputedWords; omega_arith)⟩


theorem enteredPrefix_ok (backend : MontBackend) (s : State) {p : Inputs}
    (h : CombPrecomputeFnInput p s) :
    WP isa (.seq (.block VG.Impl.Ffdh.Arm.CombPrecompute.entry) (prefixCode backend)) (entered s) fun t =>
      Memory p (entered s).sp t ∧
      Spec.Rsa.wordsAt t.mem (State.addr p.output) 3=
        [BitVec.ofNat 64 (bits p),BitVec.ofNat 64 ((bits p+7)/8),
          BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows (bits p))] ∧
      numAt t.mem (State.addr p.base) p.w 0=p.P ∧
      numAt t.mem (State.addr p.base) p.w 4=2^(128*p.w)%p.P ∧
      Frame (combPrecomputeWrites p (entered s)) (entered s).mem t.mem := by
  rw [WP.seq_iff]
  refine WP.mono_syms (withAllRest (combEntry_ok (entered s) h.args h.incomingCount h.incomingBase
    h.outputReg h.domainReg h.domainLengthReg)) ?_
  rintro u ⟨⟨ctxU,frameU⟩,restU⟩ symsU
  have context : Context p slots u :=
    ⟨⟨ctxU.workspace,ctxU.locals,ctxU.domain,ctxU.domainStack,fun d hd =>
      ctxU.saved d (by simp only [slots,List.mem_cons,List.not_mem_nil,or_false] at hd ⊢; omega_arith)⟩,ctxU.ptr⟩
  have environment := VettedGroups.environment.stable h.environment
    (frameU.mono (by simp [keyCallWrites,keyWrites])) restU symsU
  refine WP.mono (prefix_ok backend u context environment (h.calls.after restU) (h.output.after restU)
    h.workspaceSeparate h.domainSeparate (by rw [restU.sp]; exact h.localSeparate)
    (by rw [restU.sp]; exact h.callSeparate) h.valid) ?_
  rintro t ⟨memory,header,modulus,r2,frameT,_restT⟩
  refine ⟨by simpa only [restU.sp] using memory,header,modulus,r2,?_⟩
  have fullU : Frame (combPrecomputeWrites p (entered s)) (entered s).mem u.mem :=
    frameU.mono (by simp [combPrecomputeWrites])
  exact fullU.trans (by simpa only [combPrecomputeWrites,restU.sp] using frameT)

end CombBuilder
end VG.Proof.Ffdh.Arm
