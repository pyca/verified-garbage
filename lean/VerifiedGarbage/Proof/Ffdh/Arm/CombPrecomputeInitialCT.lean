module

public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeStoreMemory
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAt
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Arm.SharedWindowApplyCT
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpSharedCT
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Ffdh.Arm.Block
meta import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
meta import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeState
meta import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeState
import VerifiedGarbage.Proof.Rsa.FixedBaseCombTable
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Bignum.Arm.ExpState
import VerifiedGarbage.Proof.Bignum.Arm.SharedWindowArithmetic
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpShared
public import VerifiedGarbage.Impl.Bignum.Arm.SharedWindow
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
meta import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeStoreMemory
meta import VerifiedGarbage.Proof.Rsa.FixedBaseCombTable
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Bignum.Arm.ExpState
meta import VerifiedGarbage.Proof.Ffdh.Arm.ImportAt
meta import VerifiedGarbage.Proof.Bignum.Arm.SharedWindowArithmetic
meta import VerifiedGarbage.Proof.Bignum.Arm.TwoExpShared
meta import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
meta import VerifiedGarbage.Impl.Bignum.Arm.SharedWindow
meta import VerifiedGarbage.Impl.Ffdh.Arm.Domain
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeArgs
import VerifiedGarbage.Proof.Bignum.Arm.ExportArrayCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT

/-! ### `Ffdh.Arm.CombPrecomputeStoreCT`, which this module and modules that import it used -/

section

/-! Canonical context exports have public addresses, widths, and table indices. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt)
open VG.Proof.X25519.Arm (wp_mov op2_imm)

theorem store_ct {p : Inputs} {sp : BitVec 32} {digit o : Nat} (ho : o<8) :
    RelCT isa (fun s t => (Memory p sp s ∧ s.gpr .r3=BitVec.ofNat 32 digit) ∧
      (Memory p sp t ∧ t.gpr .r3=BitVec.ofNat 32 digit) ∧ s.sp=t.sp)
      (VG.Impl.Ffdh.Arm.CombPrecompute.store o) (fun _ _ => True) := by
  let Input := fun s : State => Memory p sp s ∧ s.gpr .r3=BitVec.ofNat 32 digit
  let dst := p.output+BitVec.ofNat 32 (24+8*p.w*(digit+2))
  let Ready := fun s : State => SmallFnReady p.base p.len p.w o s ∧ s.gpr .r4=dst
  have args (s : State) (h : Input s) :
      WP isa (.block (VG.Impl.Ffdh.Arm.CombPrecompute.tableArgs ++
        [.mov .r2 (.imm (BitVec.ofNat 32 o))])) s Ready := by
    have fit := h.1.ready.layout.2.2.1
    rw [h.1.ready.width] at fit
    have size : 52≤8*p.len := by simp only [arrAt,Proof.Rsa.Mont.hdrBytes] at fit; omega_using [fit]
    have header := nativeHeader_of_layout s.mem p.base h.1.ready.workspace.nowrap
      (Nat.le_refl _) h.1.ready.layout
    rw [h.1.ready.width] at header
    rw [WP.block_append_iff]
    refine WP.mono (combTableArgs_raw_ok s h.1.ready.workspace h.1.context.locals size h.1.ready.ptr
      header.count (h.1.context.saved 4 (by simp [slots])) h.2) ?_
    rintro u ⟨⟨dstU,ptrU,memU⟩,restU⟩
    rw [combTableAddress] at dstU
    refine wp_mov (op2_imm (by
      apply encodable_byte
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega_using [ho] : o<2^32)]
      omega_using [ho])) fun v moved => WP.block_nil ?_
    have memV := moved.mem.trans memU
    exact ⟨⟨h.1.ready.workspace.congr (moved.wr.trans restU.wr),
      by rw [memV]; exact h.1.ready.layout,
      by rw [memV]; exact h.1.ready.width,
      (moved.other .r0 (by decide)).trans ptrU,moved.gpr⟩,
      (moved.other .r4 (by decide)).trans dstU⟩
  have load : RelCT isa (fun s t => s.gpr .r0=t.gpr .r0 ∧ s.sp=t.sp)
      (.block [.ldrSp .r4 4]) (fun s t => s.gpr .r0=t.gpr .r0) := by
    intro s t tr1 tr2 u v h e1 e2
    have ku : u.gpr .r0=s.gpr .r0 := Exec.gpr (h:=e1) (hn:=Or.inl rfl) (by decide)
    have kv : v.gpr .r0=t.gpr .r0 := Exec.gpr (h:=e2) (hn:=Or.inl rfl) (by decide)
    exact ⟨(loadStack_ct .r4 4 _ _ _ _ _ _ h.2 e1 e2).1,ku.trans (h.1.trans kv.symm)⟩
  have restTrace : RelCT isa (fun s t => s.gpr .r0=t.gpr .r0)
      (.block ([.ldr .r1 .r0 48, .mov .r1 (.shifted .r1 .lsl 3),
        .dp .add .r3 .r3 (.imm 2), .mul .r3 .r3 .r1,
        .dp .add .r4 .r4 (.reg .r3), .dp .add .r4 .r4 (.imm 24)] ++
        [.mov .r2 (.imm (BitVec.ofNat 32 o))])) (fun _ _ => True) := by
    have cases : o=0 ∨ o=1 ∨ o=2 ∨ o=3 ∨ o=4 ∨ o=5 ∨ o=6 ∨ o=7 := by omega_using [ho]
    rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      (apply RelCT.taint (A:=taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
       intro s t h
       apply Taint.agree_ofRegs
       intro r hr
       simp only [List.mem_singleton] at hr
       subst r
       exact h)
  have trace : RelCT isa (fun s t => Input s ∧ Input t ∧ s.sp=t.sp)
      (.block (VG.Impl.Ffdh.Arm.CombPrecompute.tableArgs ++
        [.mov .r2 (.imm (BitVec.ofNat 32 o))])) (fun _ _ => True) :=
    (RelCT.block_append (load.seq restTrace)).mono
      (fun _ _ h => ⟨h.1.1.ready.ptr.trans h.2.1.1.ready.ptr.symm,h.2.2⟩) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.CombPrecompute.store
  exact relCT_chain trace args args ((exportArray_ct ho).mono
    (fun _ _ h => ⟨h.1.1,h.2.1.1,h.1.2,h.2.1.2⟩) (fun _ _ h => h))

end VG.Proof.Ffdh.Arm.CombBuilder

end

end

/-! ### `Ffdh.Arm.CombPrecomputeInitialStore`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.CombPrecomputeInitial`, which this module and modules that import it used -/

section

/-! Import the generator and reuse shared Montgomery initialization for the first two entries. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt Operand arrAt)
open VG.Proof.X25519.Arm (Rest)

private theorem operand (a : Nat) (ha : a=0 ∨ a=4) : Operand a := by
  rcases ha with rfl|rfl <;> simp [Operand,Proof.Rsa.Mont.aAcc,Proof.Rsa.Mont.aTmp]

theorem initialValues_ok (backend : MontBackend) (s : State) {p : Inputs} {sp : BitVec 32}
    (h : Memory p sp s) (modulus : numAt s.mem (State.addr p.base) p.w 0=p.P)
    (r2 : numAt s.mem (State.addr p.base) p.w 4=2^(128*p.w)%p.P) (odd : p.P%2=1) :
    WP isa (.seq (VG.Impl.Ffdh.Arm.Domain.importAt 1 56 32)
      (VG.Impl.Bignum.Arm.SharedWindow.init (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul))) s
      fun t => Memory p sp t ∧ ExpState p.base p.len p.w p.P p.G 0 t ∧
        Frame [⟨State.addr p.base,8*p.len⟩,FrameStack.belowA s.sp 48] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [WP.seq_iff]
  refine WP.mono (importAt_ok s 1 56 32 h.context (by decide) (by decide) (by decide) h.ready
    (by decide) (by decide) h.context.gBytes (by rw [p.gLength]; have := p.minLength; omega_using [this])
    (by rw [p.gLength]; exact p.width.2.2.2.1) (by change BitVec.ofNat 32 p.k=_; rw [p.gLength])) ?_
  rintro u ⟨_contextU,readyU,generator,keeps,frameU,restU⟩
  have frameU' : Frame [⟨State.addr p.base,8*p.len⟩,FrameStack.belowA s.sp 48] s.mem u.mem :=
    frameU.mono (by simp)
  have memU := h.after_arithmetic readyU frameU' restU
  have fits : arrAt p.w 8≤8*p.len := h.ready.width ▸ h.ready.layout.2.2.1
  have modulusU := (keeps_array_num keeps fits (operand 0 (by simp)) (by decide)).trans modulus
  have r2U := (keeps_array_num keeps fits (operand 4 (by simp)) (by decide)).trans r2
  let K := TwoExp.sharedMontgomery p.base sp p.len p.w backend.name backend.mul
    (fun _ _ _ ho ha hb v input => backend.correct v input ho ha hb) backend.stackOk
  have callU : TwoExp.CallReady p.base sp p.len u := ⟨memU.calls.stack,memU.fixed⟩
  have r2bound : numAt u.mem (State.addr p.base) p.w 4<p.P := by
    rw [r2U]
    exact Nat.mod_lt _ (by rw [← modulusU]; have := readyU.modulus; omega_using [this])
  have r2value : numAt u.mem (State.addr p.base) p.w 4%p.P=2^(64*p.w)*2^(64*p.w)%p.P := by
    rw [r2U,Nat.mod_mod,← Nat.pow_add,show 64*p.w+64*p.w=128*p.w by omega_using []]
  refine WP.mono (sharedWindowInit_ok K u readyU callU modulusU odd generator r2bound r2value) ?_
  rintro t ⟨exp,_headers,_call,frameT,restT⟩
  have localFrame : Frame [⟨State.addr p.base,8*p.len⟩,FrameStack.belowA u.sp 48] u.mem t.mem := by
    simpa only [K,← memU.fixed] using frameT
  have memT := memU.after_arithmetic exp.ready localFrame restT
  refine ⟨memT,exp,frameU'.trans ?_,restU.trans restT⟩
  simpa only [restU.sp] using localFrame

end VG.Proof.Ffdh.Arm.CombBuilder

end

end

/-! Store Montgomery one and the generator as the first two canonical entries. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt arrAt)
open VG.Proof.X25519.Arm (Rest wp_mov op2_imm)

private theorem memoryOfMem {p : Inputs} {sp : BitVec 32} {s t : State}
    (h : Memory p sp s) (mem : t.mem=s.mem) (rest : Rest roundClobbers s t)
    (ptr : t.gpr .r0=p.base) : Memory p sp t := by
  exact h.after_arithmetic (h.ready.of_mem mem rest ptr) (by rw [mem]; exact Frame.refl _ _) rest

private theorem eqTrans {B : Addr} {size : Nat} {m1 m2 m3 : Mem}
    (a : WorkspaceEq B size m1 m2) (b : WorkspaceEq B size m2 m3) : WorkspaceEq B size m1 m3 :=
  ⟨fun d n fit => (b.read d n fit).trans (a.read d n fit)⟩

private theorem storeWhole {p : Inputs} {digit : Nat} {m m' : Mem} (hd : digit<32)
    (frame : Frame [⟨off (State.addr p.output) (entryOffset p digit),8*p.w⟩] m m') :
    Frame [⟨State.addr p.output,bytes p⟩] m m' := by
  apply frame.sub
  intro r hr
  rw [List.mem_singleton] at hr
  subst r
  exact ⟨_,List.mem_singleton_self _,entry_sub p hd⟩

theorem initial_ok (backend : MontBackend) (s : State) {p : Inputs} {sp : BitVec 32}
    (h : Memory p sp s) (modulus : numAt s.mem (State.addr p.base) p.w 0=p.P)
    (r2 : numAt s.mem (State.addr p.base) p.w 4=2^(128*p.w)%p.P) (odd : p.P%2=1) :
    WP isa (VG.Impl.Ffdh.Arm.CombPrecompute.initial
      (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) s fun t =>
      Memory p sp t ∧ TablePrefix p 2 t.mem ∧
      numAt t.mem (State.addr p.base) p.w 5=entryValue p 1 ∧
      numAt t.mem (State.addr p.base) p.w 7=1 ∧
      numAt t.mem (State.addr p.base) p.w 0=p.P ∧
      numAt t.mem (State.addr p.base) p.w 4=2^(128*p.w)%p.P ∧
      WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem t.mem ∧
      Frame [⟨State.addr p.base,8*p.len⟩,⟨State.addr p.output,bytes p⟩,FrameStack.belowA sp 48] s.mem t.mem ∧
      Rest roundClobbers s t := by
  have values := initialValues_ok backend s h modulus r2 odd
  rw [WP.seq_iff] at values
  rw [VG.Impl.Ffdh.Arm.CombPrecompute.initial,WP.seq_iff]
  refine WP.mono values fun u initWP => ?_
  rw [WP.seq_iff]
  refine WP.mono initWP ?_
  rintro v ⟨memoryV,exp,frameV,restV⟩
  have fit : arrAt p.w 8≤8*p.len := exp.ready.width ▸ exp.ready.layout.2.2.1
  have six : numAt v.mem (State.addr p.base) p.w 6=entryValue p 0 := by
    have value := exp.powerValue
    rw [Nat.mod_eq_of_lt exp.powerBound] at value
    simpa only [entryValue,VG.Proof.Rsa.FixedBaseComb.exponent_zero,VG.Proof.Bignum.powMod_eq,
      Nat.pow_zero,Nat.one_mul,Nat.mod_mul_mod] using value
  have exponentOne : Spec.Rsa.FixedBaseComb.exponent (bits p) 1=1 := by
    simpa only [Nat.pow_zero,Nat.zero_mul] using VG.Proof.Rsa.FixedBaseComb.exponent_tooth (bits p) 0 (by decide)
  have five : numAt v.mem (State.addr p.base) p.w 5=entryValue p 1 := by
    have value := exp.inputValue
    rw [Nat.mod_eq_of_lt exp.inputBound] at value
    simpa only [entryValue,exponentOne,VG.Proof.Bignum.powMod_eq,Nat.pow_one,Nat.mod_mul_mod] using value
  have headV := headEq_arithmetic h frameV
  have frameV' : Frame [⟨State.addr p.base,8*p.len⟩,⟨State.addr p.output,bytes p⟩,FrameStack.belowA sp 48] s.mem v.mem := by
    rw [h.fixed] at frameV
    exact frameV.mono (by simp)
  rw [WP.seq_iff]
  refine wp_mov (op2_imm (by decide)) fun a move0 => WP.block_nil ?_
  have restA : Rest roundClobbers v a := move0.rest (by simp [roundClobbers])
  have memoryA := memoryOfMem memoryV move0.mem restA ((move0.other .r0 (by decide)).trans exp.ready.ptr)
  rw [WP.seq_iff]
  refine WP.mono (combStoreMemory_ok a memoryA (by decide : 0<32) (by decide : 6<8) move0.gpr) ?_
  rintro b ⟨memoryB,workspaceB,valueB,frameB,restB⟩
  have empty : TablePrefix p 0 a.mem := by intro i hi; omega
  have valueB' : (b.mem.read (off (State.addr p.output) (entryOffset p 0)) (8*p.w)).toNat=entryValue p 0 := by
    rw [valueB,move0.mem,six]
  have tableB := TablePrefix.extend memoryA empty (by decide : 0<32) frameB valueB'
  have fiveB : numAt b.mem (State.addr p.base) p.w 5=entryValue p 1 := by
    rw [workspaceB.number fit (by decide : 5<8),move0.mem,five]
  have oneB : numAt b.mem (State.addr p.base) p.w 7=1 := by
    rw [workspaceB.number fit (by decide : 7<8),move0.mem,exp.one]
  have modB : numAt b.mem (State.addr p.base) p.w 0=p.P := by
    rw [workspaceB.number fit (by decide : 0<8),move0.mem,exp.modulus]
  have r2B : numAt b.mem (State.addr p.base) p.w 4=2^(128*p.w)%p.P := by
    rw [workspaceB.number fit (by decide : 4<8),move0.mem,exp.r2]
  have headB : WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem b.mem := by
    have headA : WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem a.mem := by rw [move0.mem]; exact headV
    exact eqTrans headA (headEq_store memoryA (by decide : 0<32) frameB)
  have wholeB := storeWhole (by decide : 0<32) frameB
  have fB : Frame [⟨State.addr p.base,8*p.len⟩,⟨State.addr p.output,bytes p⟩,FrameStack.belowA sp 48] s.mem b.mem := by
    refine Frame.trans ?_ (wholeB.mono (by simp))
    rw [move0.mem]
    exact frameV'
  have rB := restV.trans (restA.trans restB)
  rw [WP.seq_iff]
  refine wp_mov (op2_imm (by decide)) fun c move1 => WP.block_nil ?_
  have restC : Rest roundClobbers b c := move1.rest (by simp [roundClobbers])
  have memoryC := memoryOfMem memoryB move1.mem restC ((move1.other .r0 (by decide)).trans memoryB.ready.ptr)
  refine WP.mono (combStoreMemory_ok c memoryC (by decide : 1<32) (by decide : 5<8) move1.gpr) ?_
  rintro t ⟨memoryT,workspaceT,valueT,frameT,restT⟩
  have tableC : TablePrefix p 1 c.mem := by rw [move1.mem]; exact tableB
  have valueT' : (t.mem.read (off (State.addr p.output) (entryOffset p 1)) (8*p.w)).toNat=entryValue p 1 := by
    rw [valueT,move1.mem,fiveB]
  have tableT := TablePrefix.extend memoryC tableC (by decide : 1<32) frameT valueT'
  have headT : WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem t.mem := by
    have headC : WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem c.mem := by rw [move1.mem]; exact headB
    exact eqTrans headC (headEq_store memoryC (by decide : 1<32) frameT)
  have wholeT := storeWhole (by decide : 1<32) frameT
  refine ⟨memoryT,tableT,?_,?_,?_,?_,headT,?_,rB.trans (restC.trans restT)⟩
  · rw [workspaceT.number fit (by decide : 5<8),move1.mem]; exact fiveB
  · rw [workspaceT.number fit (by decide : 7<8),move1.mem]; exact oneB
  · rw [workspaceT.number fit (by decide : 0<8),move1.mem]; exact modB
  · rw [workspaceT.number fit (by decide : 4<8),move1.mem]; exact r2B
  · refine Frame.trans ?_ (wholeT.mono (by simp))
    rw [move1.mem]
    exact fB

end VG.Proof.Ffdh.Arm.CombBuilder

end

end

/-! Public generator initialization and the first two table exports have fixed traces. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (wp_mov op2_imm)

def InitialInput (p : Inputs) (sp : BitVec 32) (s : State) : Prop :=
  Memory p sp s ∧ numAt s.mem (State.addr p.base) p.w 0=p.P ∧
    numAt s.mem (State.addr p.base) p.w 4=2^(128*p.w)%p.P

private theorem moveZero_ct : RelCT isa (fun _ _ => True)
    (.block [.mov .r3 (.imm 0)]) (fun _ _ => True) := by
  apply RelCT.taint (A:=taint) (Taint.ofRegs []) _ (by taint_decide)
  intro s t _
  exact Taint.agree_ofRegs (by simp)

private theorem moveOne_ct : RelCT isa (fun _ _ => True)
    (.block [.mov .r3 (.imm 1)]) (fun _ _ => True) := by
  apply RelCT.taint (A:=taint) (Taint.ofRegs []) _ (by taint_decide)
  intro s t _
  exact Taint.agree_ofRegs (by simp)

private theorem move_ready (digit : BitVec 32) (enc : VG.Arm.encodable digit=true)
    (s : State) {p : Inputs} {sp : BitVec 32} (h : Memory p sp s) :
    WP isa (.block [.mov .r3 (.imm digit)]) s fun t => Memory p sp t ∧ t.gpr .r3=digit := by
  refine wp_mov (op2_imm enc) fun t moved => WP.block_nil ?_
  have rest := moved.rest (by simp [roundClobbers] : .r3∈roundClobbers)
  have ready := h.ready.of_mem moved.mem rest ((moved.other .r0 (by decide)).trans h.ready.ptr)
  exact ⟨h.after_arithmetic ready (by rw [moved.mem]; exact Frame.refl _ _) rest,moved.gpr⟩

theorem initialValues_ct (backend : MontBackend) {p : Inputs} {sp : BitVec 32} (odd : p.P%2=1) :
    RelCT isa (fun s t => InitialInput p sp s ∧ InitialInput p sp t ∧ s.sp=t.sp)
      (.seq (VG.Impl.Ffdh.Arm.Domain.importAt 1 56 32)
        (VG.Impl.Bignum.Arm.SharedWindow.init (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)))
      (fun _ _ => True) := by
  let K := TwoExp.sharedMontgomery p.base sp p.len p.w backend.name backend.mul
    (fun _ _ _ ho ha hb v input => backend.correct v input ho ha hb) backend.stackOk
  have timing : TwoExp.MontgomeryTiming K := TwoExp.sharedMontgomeryTiming p.base sp p.len p.w
    backend.name backend.mul (fun _ _ _ ho ha hb v input => backend.correct v input ho ha hb)
    backend.stackOk (fun _ _ _ ho ha hb => backend.rawCT ho ha hb)
  let Ready := fun s : State => ExpInitReady p.base p.len p.w s ∧ TwoExp.CallReady p.base sp p.len s
  have imported (s : State) (h : InitialInput p sp s) :
      WP isa (VG.Impl.Ffdh.Arm.Domain.importAt 1 56 32) s Ready := by
    refine WP.mono (importAt_ok s 1 56 32 h.1.context (by decide) (by simp [slots]) (by simp [slots])
      h.1.ready (by decide) (by decide) h.1.context.gBytes
      (by rw [p.gLength]; have := p.minLength; omega_using [this])
      (by rw [p.gLength]; exact p.width.2.2.2.1) (by change BitVec.ofNat 32 p.k=_; rw [p.gLength])) ?_
    rintro u ⟨_,ready,_,keeps,frame,rest⟩
    have memory := h.1.after_arithmetic ready (frame.mono (by simp)) rest
    have fit := h.1.ready.width ▸ h.1.ready.layout.2.2.1
    have modulus := (keeps_array_num keeps fit (by simp [Proof.Rsa.Mont.Operand,Proof.Rsa.Mont.aAcc,Proof.Rsa.Mont.aTmp]) (by decide : 0≠1)).trans h.2.1
    have r2 := (keeps_array_num keeps fit (by simp [Proof.Rsa.Mont.Operand,Proof.Rsa.Mont.aAcc,Proof.Rsa.Mont.aTmp]) (by decide : 4≠1)).trans h.2.2
    exact ⟨⟨ready,by rw [r2,modulus]; exact Nat.mod_lt _ (by have := ready.modulus; rw [modulus] at this; omega_using [odd])⟩,
      memory.calls.stack,memory.fixed⟩
  exact relCT_chain ((importAt_ct (p:=p) (slots:=slots) (k:=p.k) (by decide) (by simp [slots])
    (by simp [slots]) rfl (by decide : 1<8)).mono
    (fun _ _ h => ⟨⟨h.1.1.context,h.1.1.ready⟩,⟨h.2.1.1.context,h.2.1.1.ready⟩,h.2.2⟩) (fun _ _ h => h))
    imported imported (SharedWindow.init_ct K timing)

theorem initial_ct (backend : MontBackend) {p : Inputs} {sp : BitVec 32} (odd : p.P%2=1) :
    RelCT isa (fun s t => InitialInput p sp s ∧ InitialInput p sp t ∧ s.sp=t.sp)
      (VG.Impl.Ffdh.Arm.CombPrecompute.initial (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul))
      (fun _ _ => True) := by
  have values (s : State) (h : InitialInput p sp s) :
      WP isa (.seq (VG.Impl.Ffdh.Arm.Domain.importAt 1 56 32)
        (VG.Impl.Bignum.Arm.SharedWindow.init (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul))) s
        (Memory p sp) := WP.mono (initialValues_ok backend s h.1 h.2.1 h.2.2 odd) (fun _ h => h.1)
  have store (o digit : Nat) (ho : o<8) (hd : digit<32) (s : State)
      (h : Memory p sp s ∧ s.gpr .r3=BitVec.ofNat 32 digit) :
      WP isa (VG.Impl.Ffdh.Arm.CombPrecompute.store o) s (Memory p sp) :=
    WP.mono (combStoreMemory_ok s h.1 hd ho h.2) (fun _ h => h.1)
  apply RelCT.assoc
  refine relCT_chain (initialValues_ct backend odd) values values ?_
  refine relCT_chain (moveZero_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h))
    (fun s h => move_ready 0 (by decide) s h) (fun s h => move_ready 0 (by decide) s h) ?_
  refine relCT_chain (store_ct (digit:=0) (by decide : 6<8)) (store 6 0 (by decide) (by decide))
    (store 6 0 (by decide) (by decide)) ?_
  exact relCT_chain (moveOne_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h))
    (fun s h => move_ready 1 (by decide) s h) (fun s h => move_ready 1 (by decide) s h)
    (store_ct (digit:=1) (by decide : 5<8))

end VG.Proof.Ffdh.Arm.CombBuilder
