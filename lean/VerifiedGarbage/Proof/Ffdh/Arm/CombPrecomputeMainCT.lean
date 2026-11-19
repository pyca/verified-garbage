module

public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeMetadataCT
public import VerifiedGarbage.Impl.Bignum.Arm.MontCall
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyPrepareLaw
public import VerifiedGarbage.Impl.Ffdh.Arm.NormalizedPrepare
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
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
import VerifiedGarbage.Proof.Ffdh.Arm.CachedSamplePolicy
public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeCore
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeStoreMemory
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProductLoadCT
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeSquareState
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeInitialCT
import VerifiedGarbage.Proof.Rsa.FixedBaseCombTable
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeMontgomeryOutCT
meta import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Ffdh.Arm.VettedBoundInstance
meta import VerifiedGarbage.Proof.Ffdh.Arm.VettedBoundInstance
meta import VerifiedGarbage.Proof.Ffdh.Arm.Context
meta import VerifiedGarbage.Proof.Ffdh.Arm.CachedSamplePolicy
meta import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeMontgomeryOutCT
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.OffsetBelow
meta import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeSquareState
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeState
public import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsEnvironment
import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticExternal
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleEnvironment
public import VerifiedGarbage.Proof.Ffdh.ScalarWidth
public import VerifiedGarbage.Spec.Rsa.FixedBaseComb
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyCallMemory
import VerifiedGarbage.Proof.Ffdh.Arm.NormalizedPrepare
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpShared
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeMem
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProductStore
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeArgs
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.ImportArrayLayout
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Rsa.FixedBaseCombMont
public import VerifiedGarbage.Proof.Ffdh.Arm.Frame
import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.Proof.Ffdh.Arm.IncomingWord
public import VerifiedGarbage.Spec.Ffdh.Contract
import VerifiedGarbage.Proof.Ffdh.Arm.EntryStore
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Ffdh.Arm.DomainPointers
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
meta import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeState
meta import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsEnvironment
meta import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeMetadataCT
meta import VerifiedGarbage.Proof.Ffdh.Domain
meta import VerifiedGarbage.Proof.Framework.Arm.Syms
meta import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticExternal
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Ffdh.Arm.Block
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Ffdh.Arm.SampleEnvironment
meta import VerifiedGarbage.Proof.Ffdh.ScalarWidth
meta import VerifiedGarbage.Spec.Rsa.FixedBaseComb
meta import VerifiedGarbage.Impl.Ffdh.Arm.NormalizedPrepare
meta import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeyCallMemory
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeyPrepareLaw
meta import VerifiedGarbage.Proof.Ffdh.Arm.NormalizedPrepare
meta import VerifiedGarbage.Proof.Bignum.Arm.TwoExpShared
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeCore
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Impl.Bignum.Arm.MontCall
meta import VerifiedGarbage.Proof.Framework.OffsetBelow
meta import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeStoreMemory
meta import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeMem
meta import VerifiedGarbage.Proof.Rsa.FixedBaseCombTable
meta import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProductStore
meta import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeArgs
meta import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
meta import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
meta import VerifiedGarbage.Proof.Bignum.Arm.ImportArrayLayout
meta import VerifiedGarbage.Proof.Framework.CallLay
meta import VerifiedGarbage.Proof.Rsa.FixedBaseCombMont
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Ffdh.Arm.Frame
meta import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
meta import VerifiedGarbage.Proof.Ffdh.Arm.IncomingWord
meta import VerifiedGarbage.Spec.Ffdh.Contract
meta import VerifiedGarbage.Proof.Ffdh.Arm.EntryStore
meta import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
meta import VerifiedGarbage.Proof.Ffdh.Arm.DomainPointers
meta import VerifiedGarbage.Impl.Ffdh.Arm.Domain
meta import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Bignum.Arm.PcEntryCT

/-! ### `Ffdh.Arm.CombPrecomputeControlCT`, which only this module used -/

section

/-! Fixed public counter accesses do not expose the residues being multiplied. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont

private theorem add_ct : RelCT isa (fun s t => s.sp=t.sp)
    (.block [.dp .add .r3 .r3 (.reg .r2)]) (fun s t => s.sp=t.sp) := by
  apply relCT_keep_sp _ (fun _ _ h => h)
  apply RelCT.taint (A:=taint) (Taint.ofRegs []) _ (by taint_decide)
  intro s t _
  exact Taint.agree_ofRegs (by simp)

theorem productStore_ct {p : Inputs} {sp : BitVec 32} {high low : Nat} :
    RelCT isa (fun s t =>
      (Memory p sp s ∧ s.mem.readW (off (State.addr s.sp) 36) 32=BitVec.ofNat 32 high ∧
        s.mem.readW (off (State.addr s.sp) 40) 32=BitVec.ofNat 32 low) ∧
      (Memory p sp t ∧ t.mem.readW (off (State.addr t.sp) 36) 32=BitVec.ofNat 32 high ∧
        t.mem.readW (off (State.addr t.sp) 40) 32=BitVec.ofNat 32 low) ∧ s.sp=t.sp)
      VG.Impl.Ffdh.Arm.CombPrecompute.productStore (fun _ _ => True) := by
  have args (s : State) (h : Memory p sp s ∧
      s.mem.readW (off (State.addr s.sp) 36) 32=BitVec.ofNat 32 high ∧
      s.mem.readW (off (State.addr s.sp) 40) 32=BitVec.ofNat 32 low) :
      WP isa (.block [.ldrSp .r3 36,.ldrSp .r2 40,.dp .add .r3 .r3 (.reg .r2)]) s
        (fun t => Memory p sp t ∧ t.gpr .r3=BitVec.ofNat 32 (high+low)) := by
    refine WP.mono (productStoreArgs_ok s h.1.context.locals h.2.1 h.2.2) ?_
    rintro t ⟨⟨index,mem,ptr⟩,rest⟩
    exact ⟨h.1.of_mem mem rest (ptr.trans h.1.ready.ptr),index⟩
  have headCT := RelCT.block_append ((stackLoads_ct [(.r3,36),(.r2,40)]).seq add_ct)
  unfold VG.Impl.Ffdh.Arm.CombPrecompute.productStore
  exact relCT_chain (headCT.mono (fun _ _ h => h.2.2) (fun _ _ _ => trivial)) args args
    (store_ct (digit:=high+low) (by decide : 6<8))

private theorem inc_ct : RelCT isa (fun s t => s.sp=t.sp)
    (.block [.dp .add .r3 .r3 (.imm 1)]) (fun s t => s.sp=t.sp) := by
  apply relCT_keep_sp _ (fun _ _ h => h)
  apply RelCT.taint (A:=taint) (Taint.ofRegs []) _ (by taint_decide)
  intro s t _
  exact Taint.agree_ofRegs (by simp)

private theorem cmp_ct : RelCT isa (fun s t => s.sp=t.sp)
    (.block [.cmp .r3 (.reg .r2)]) (fun s t => s.sp=t.sp) := by
  apply relCT_keep_sp _ (fun _ _ h => h)
  apply RelCT.taint (A:=taint) (Taint.ofRegs []) _ (by taint_decide)
  intro s t _
  exact Taint.agree_ofRegs (by simp)

theorem productNext_ct : RelCT isa (fun s t => s.sp=t.sp)
    (.block VG.Impl.Ffdh.Arm.CombPrecompute.productNext) (fun _ _ => True) := by
  have finish := RelCT.block_append ((loadStack_ct .r2 36).seq cmp_ct)
  have store := RelCT.block_append (stackAddr_ct.seq ((storeLocal_ct .r3 40).mono
    (fun _ _ h => h) (fun _ _ h => h.2)))
  exact (RelCT.block_append ((loadStack_ct .r3 40).seq
    (RelCT.block_append (inc_ct.seq (RelCT.block_append (store.seq finish)))))).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)

theorem basisNext_ct : RelCT isa (fun s t => s.sp=t.sp)
    (.block VG.Impl.Ffdh.Arm.CombPrecompute.basisNext) (fun _ _ => True) := by
  have double : RelCT isa (fun s t => s.sp=t.sp)
      (.block [.dp .add .r3 .r3 (.reg .r3)]) (fun s t => s.sp=t.sp) := by
    apply relCT_keep_sp _ (fun _ _ h => h)
    apply RelCT.taint (A:=taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  have compare : RelCT isa (fun _ _ => True) (.block [.cmp .r3 (.imm 32)]) (fun _ _ => True) := by
    apply RelCT.taint (A:=taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  exact RelCT.block_append ((loadStack_ct .r3 36).seq (RelCT.block_append (double.seq
    (RelCT.block_append (stackAddr_ct.seq (RelCT.block_append (((storeLocal_ct .r3 36).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)).seq compare)))))))


theorem controlInit_ct (value : BitVec 32) (d : Nat) : RelCT isa (fun s t => s.sp=t.sp)
    (.block [.mov .r3 (.imm value),.addSp .r12 0,.str .r3 .r12 d]) (fun _ _ => True) := by
  have mov : RelCT isa (fun s t => s.sp=t.sp) (.block [.mov .r3 (.imm value)])
      (fun s t => s.sp=t.sp) := single_ct (fun _ _ _ => rfl)
        (fun _ _ _ _ h e1 e2 => (exec_sp e1).trans (h.trans (exec_sp e2).symm))
  exact RelCT.block_append (mov.seq (RelCT.block_append (stackAddr_ct.seq
    ((storeLocal_ct .r3 d).mono (fun _ _ h => h) (fun _ _ _ => trivial)))))

theorem basisStore_ct {p : Inputs} {sp : BitVec 32} {high : Nat} :
    RelCT isa (fun s t =>
      (Memory p sp s ∧ s.mem.readW (off (State.addr s.sp) 36) 32=BitVec.ofNat 32 high) ∧
      (Memory p sp t ∧ t.mem.readW (off (State.addr t.sp) 36) 32=BitVec.ofNat 32 high) ∧ s.sp=t.sp)
      (.seq (.block [.ldrSp .r3 36]) (VG.Impl.Ffdh.Arm.CombPrecompute.store 5)) (fun _ _ => True) := by
  have loaded (s : State) (h : Memory p sp s ∧
      s.mem.readW (off (State.addr s.sp) 36) 32=BitVec.ofNat 32 high) :
      WP isa (.block [.ldrSp .r3 36]) s (fun t => Memory p sp t ∧ t.gpr .r3=BitVec.ofNat 32 high) := by
    refine WP.mono (localLoad_ok s .r3 h.1.context.locals (d:=36) (by decide)) ?_
    rintro t ⟨reg,mem,rest⟩
    exact ⟨h.1.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.1.ready.ptr),reg.trans h.2⟩
  exact relCT_chain ((loadStack_ct .r3 36).mono (fun _ _ h => h.2.2) (fun _ _ _ => trivial))
    loaded loaded (store_ct (digit:=high) (by decide : 5<8))

end VG.Proof.Ffdh.Arm.CombBuilder

end

end

/-! ### `Ffdh.Arm.CombPrecomputeCTState`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.CombPrecomputeProductCounterState`, which only this module used -/

section

/-! ### `Ffdh.Arm.CombPrecomputeProductCounter`, which this module and modules that import it used -/

section

/-! Public subset and basis counters advance without changing arithmetic arrays. -/
@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Impl.Ffdh.Arm.CombPrecompute
open VG.Proof.X25519.Arm (Rest)

theorem Memory.controlRead {p : Inputs} {sp : BitVec 32} {s t : State}
    (h : Memory p sp s)
    (frame : Frame [⟨State.addr p.base,8*p.len⟩,⟨State.addr p.output,bytes p⟩,
      FrameStack.belowA s.sp 48] s.mem t.mem) (d : Nat) (hd : d+4≤72) :
    t.mem.readW (off (State.addr s.sp) d) 32=s.mem.readW (off (State.addr s.sp) d) 32 := by
  have sub := Offset.sub_base (State.addr s.sp) (d:=d) (n:=4) (k:=72) hd
  apply frame.readW (r:=⟨off (State.addr s.sp) d,4⟩) (Region.contains_self _ _) _ (by decide)
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl
  · exact h.context.locals.separate.sub_left sub
  · rw [h.fixed] at sub ⊢
    exact h.localSeparate.sub_left sub
  · have sep : (⟨State.addr s.sp,72⟩ : Region).Disjoint (FrameStack.belowA s.sp 48) := by
      rw [FrameStack.belowA,FrameStack.addr_sub' h.calls.stack.fit]
      exact (Offset.below_disjoint _ (by decide)).symm
    exact sep.sub_left sub

theorem productNext_raw (s : State) {base : BitVec 32} {len low high : Nat}
    (locals : Locals base len s) (lowFit : low+1<2^32) (highFit : high<2^32)
    (savedLow : s.mem.readW (off (State.addr s.sp) 40) 32=BitVec.ofNat 32 low)
    (savedHigh : s.mem.readW (off (State.addr s.sp) 36) 32=BitVec.ofNat 32 high) :
    WP isa (.block productNext) s fun t =>
      (t.mem=s.mem.writeW (off (State.addr s.sp) 40) (BitVec.ofNat 32 (low+1)) ∧
        t.z=decide (low+1=high)) ∧ Rest [.r2,.r3,.r12] s t := by
  have a40 : State.addr (s.sp+BitVec.ofNat 32 40)=off (State.addr s.sp) 40 := addr_add (by have := locals.space.nowrap; omega_using [this])
  have a36 : State.addr (s.sp+BitVec.ofNat 32 36)=off (State.addr s.sp) 36 := addr_add (by have := locals.space.nowrap; omega_using [this])
  have read40 := locals.read (d:=40) (by decide)
  have read36 := locals.read (d:=36) (by decide)
  have write := locals.space.write (off:=40) (by decide)
  have add : BitVec.ofNat 32 low+1=BitVec.ofNat 32 (low+1) := (BitVec.ofNat_add _ _).symm
  have keep36 : (s.mem.writeW (off (State.addr s.sp) 40) (BitVec.ofNat 32 (low+1))).readW
      (off (State.addr s.sp) 36) 32=s.mem.readW (off (State.addr s.sp) 36) 32 := by
    have frame : Frame [⟨off (State.addr s.sp) 40,4⟩] s.mem
        (s.mem.writeW (off (State.addr s.sp) 40) (BitVec.ofNat 32 (low+1))) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    apply frame.readW (r:=⟨off (State.addr s.sp) 36,4⟩) (Region.contains_self _ _) _ (by decide)
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact Offset.disjoint _ (by decide) (by decide) (by decide)
  refine withRest_all (c:=.block productNext) [.r2,.r3,.r12] ?_ (by rfl) rfl
  unfold productNext VG.Impl.Ffdh.Arm.Domain.st
  ffrun [a40,a36,read40,read36,write,savedLow,savedHigh,add,keep36,off,BitVec.add_zero,subFlags]
  by_cases eq : low+1=high
  · rw [eq,BitVec.sub_self]
    simp
  · simp only [eq,decide_false,beq_eq_false_iff_ne,ne_eq]
    intro h
    have same := BitVec.sub_eq_iff_eq_add.mp h
    have := congrArg BitVec.toNat same
    simp only [BitVec.toNat_add] at this
    simp only [BitVec.toNat_ofNat] at this
    have hm := Nat.mod_eq_of_lt lowFit
    have hn := Nat.mod_eq_of_lt highFit
    simp only [hm,hn] at this
    change low+1=(0+high)%2^32 at this
    rw [Nat.zero_add,hn] at this
    exact eq this

theorem basisNext_raw (s : State) {base : BitVec 32} {len high : Nat}
    (locals : Locals base len s) (fit : 2*high<2^32)
    (saved : s.mem.readW (off (State.addr s.sp) 36) 32=BitVec.ofNat 32 high) :
    WP isa (.block basisNext) s fun t =>
      (t.mem=s.mem.writeW (off (State.addr s.sp) 36) (BitVec.ofNat 32 (2*high)) ∧
        t.z=decide (2*high=32)) ∧ Rest [.r3,.r12] s t := by
  have a36 : State.addr (s.sp+BitVec.ofNat 32 36)=off (State.addr s.sp) 36 := addr_add (by have := locals.space.nowrap; omega_using [this])
  have read := locals.read (d:=36) (by decide)
  have write := locals.space.write (off:=36) (by decide)
  have add : BitVec.ofNat 32 high+BitVec.ofNat 32 high=BitVec.ofNat 32 (2*high) := by
    rw [← BitVec.ofNat_add,Nat.two_mul]
  refine withRest_all (c:=.block basisNext) [.r3,.r12] ?_ (by rfl) rfl
  unfold basisNext VG.Impl.Ffdh.Arm.Domain.st
  ffrun [a36,read,write,saved,add,off,BitVec.add_zero,subFlags]
  by_cases eq : 2*high=32
  · rw [eq]
    decide
  · simp only [eq,decide_false,beq_eq_false_iff_ne,ne_eq]
    intro h
    have same := BitVec.sub_eq_iff_eq_add.mp h
    have := congrArg BitVec.toNat same
    simp only [BitVec.toNat_add] at this
    simp only [BitVec.toNat_ofNat] at this
    have hm := Nat.mod_eq_of_lt fit
    simp only [hm] at this
    exact eq this

end VG.Proof.Ffdh.Arm.CombBuilder

end

end

/-! Incrementing a subset counter preserves the canonical builder state. -/
@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem productNext_state (s : State) {p : Inputs} {sp : BitVec 32} {E low high : Nat}
    (h : Core p sp s) (power : Power5 p E s)
    (lowFit : low+1<2^32) (highFit : high<2^32)
    (savedLow : s.mem.readW (off (State.addr sp) 40) 32=BitVec.ofNat 32 low)
    (savedHigh : s.mem.readW (off (State.addr sp) 36) 32=BitVec.ofNat 32 high) :
    WP isa (.block VG.Impl.Ffdh.Arm.CombPrecompute.productNext) s fun t =>
      Core p sp t ∧ Power5 p E t ∧
      t.mem.readW (off (State.addr sp) 36) 32=BitVec.ofNat 32 high ∧
      t.mem.readW (off (State.addr sp) 40) 32=BitVec.ofNat 32 (low+1) ∧
      t.z=decide (low+1=high) ∧
      Frame [⟨off (State.addr sp) 40,4⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (productNext_raw s h.memory.context.locals lowFit highFit
    (by rw [h.memory.fixed];exact savedLow) (by rw [h.memory.fixed];exact savedHigh)) ?_
  rintro t ⟨⟨mem,zero⟩,rest⟩
  have raw : Frame [⟨off (State.addr s.sp) 40,4⟩] s.mem t.mem := by
    rw [mem]
    exact (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
  have r : Rest roundClobbers s t := rest.mono (by simp [roundClobbers])
  have next := h.memory.after_control (by simp) raw r ((rest.gpr .r0 (by simp)).trans h.memory.context.ptr)
  refine ⟨h.after_workspace next.1 next.2,power.after_workspace h next.2,?_,?_,zero,?_,r⟩
  · have keep := raw.readW (w:=32) (r:=⟨off (State.addr s.sp) 36,4⟩) (Region.contains_self _ _)
      (by intro region hr; rw [List.mem_singleton] at hr; subst region
          exact Offset.disjoint _ (by decide) (by decide) (by decide)) (by decide)
    rw [h.memory.fixed] at keep
    exact keep.trans savedHigh
  · rw [mem,h.memory.fixed,Mem.readW_writeW_self32]
  · rw [←h.memory.fixed]
    exact raw

end VG.Proof.Ffdh.Arm.CombBuilder

end

end

/-! ### `Ffdh.Arm.CombPrecomputeInput`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.CombPrecomputeEntry`, which this module and modules that import it used -/

section

/-! Retain the public precomputation ABI arguments in the existing FFDH frame. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure CombEntryRegs (p : Inputs) (s : State) : Prop where
  output : s.gpr .r0 = p.output
  domain : s.gpr .r2 = p.domain
  domainLength : s.gpr .r3 = BitVec.ofNat 32 p.dom.length
  stackBase : s.gpr .r12 = s.sp

theorem CombEntryRegs.after {p : Inputs} {s t : State}
    (h : CombEntryRegs p s) (rest : Rest [] s t) : CombEntryRegs p t :=
  ⟨(rest.gpr .r0 (by simp)).trans h.output,(rest.gpr .r2 (by simp)).trans h.domain,
    (rest.gpr .r3 (by simp)).trans h.domainLength,
    (rest.gpr .r12 (by simp)).trans (h.stackBase.trans rest.sp.symm)⟩

theorem combEntryArgs_ok (s : State) {p : Inputs}
    (h : ArgumentMemory p [] s)
    (incomingCount : IncomingWord (BitVec.ofNat 32 p.k) 128 s)
    (incomingBase : IncomingWord p.base 132 s)
    (output : s.gpr .r0 = p.output) (domain : s.gpr .r2 = p.domain)
    (domainLength : s.gpr .r3 = BitVec.ofNat 32 p.dom.length) :
    WP isa (.block VG.Impl.Ffdh.Arm.CombPrecompute.entryArgs) s fun t =>
      Context p [0,32,28,24,4] t ∧ Frame [⟨State.addr s.sp,72⟩] s.mem t.mem := by
  unfold VG.Impl.Ffdh.Arm.CombPrecompute.entryArgs VG.Impl.Ffdh.Arm.Domain.st
  refine wp_stackAddr (by decide) fun u moved => ?_
  have restU : Rest [.r12] s u := moved.rest (by simp)
  have argsU := h.of_mem moved.mem restU
  have frameU : Frame [⟨State.addr s.sp,72⟩] s.mem u.mem := by rw [moved.mem]; exact Frame.refl _ _
  have countU := incomingCount.after (by decide) frameU restU
  have baseU := incomingBase.after (by decide) frameU restU
  have regsU : CombEntryRegs p u :=
    ⟨(moved.other .r0 (by decide)).trans output,(moved.other .r2 (by decide)).trans domain,
      (moved.other .r3 (by decide)).trans domainLength,by rw [moved.gpr,moved.sp,BitVec.add_zero]⟩
  refine wp_store_arg .r0 4 argsU (by decide) (by decide) (by decide) regsU.output regsU.stackBase fun v argsV frameV restV => ?_
  have regsV := regsU.after restV
  have countV := countU.after (by decide) frameV restV
  have baseV := baseU.after (by decide) frameV restV
  rw [restU.sp] at frameV
  have fullV := frameU.trans frameV
  refine wp_store_arg .r2 24 argsV (by decide) (by decide) (by decide) regsV.domain regsV.stackBase fun w argsW frameW restW => ?_
  have regsW := regsV.after restW
  have countW := countV.after (by decide) frameW restW
  have baseW := baseV.after (by decide) frameW restW
  rw [restV.sp,restU.sp] at frameW
  have fullW := fullV.trans frameW
  refine wp_store_arg .r3 28 argsW (by decide) (by decide) (by decide) regsW.domainLength regsW.stackBase fun x argsX frameX restX => ?_
  have regsX := regsW.after restX
  have countX := countW.after (by decide) frameX restX
  have baseX := baseW.after (by decide) frameX restX
  rw [restW.sp,restV.sp,restU.sp] at frameX
  have fullX := fullW.trans frameX
  refine wp_retain_incoming .r3 (by decide) argsX (by decide) countX (by decide) (by decide) (by decide)
    regsX.stackBase fun y argsY frameY restY _ stackY => ?_
  have baseY := baseX.after (by decide) frameY restY
  rw [restX.sp,restW.sp,restV.sp,restU.sp] at frameY
  have fullY := fullX.trans frameY
  refine wp_retain_incoming .r0 (by decide) argsY (by decide) baseY (by decide) (by decide) (by decide)
    stackY fun t argsT frameT restT ptr _ => WP.block_nil ?_
  refine ⟨⟨argsT,ptr⟩,?_⟩
  rw [restY.sp,restX.sp,restW.sp,restV.sp,restU.sp] at frameT
  exact fullY.trans frameT

theorem combEntry_ok (s : State) {p : Inputs}
    (h : ArgumentMemory p [] s)
    (incomingCount : IncomingWord (BitVec.ofNat 32 p.k) 128 s)
    (incomingBase : IncomingWord p.base 132 s)
    (output : s.gpr .r0 = p.output) (domain : s.gpr .r2 = p.domain)
    (domainLength : s.gpr .r3 = BitVec.ofNat 32 p.dom.length) :
    WP isa (.block VG.Impl.Ffdh.Arm.CombPrecompute.entry) s fun t =>
      Context p [60,56,0,32,28,24,4] t ∧ Frame [⟨State.addr s.sp,72⟩] s.mem t.mem := by
  rw [VG.Impl.Ffdh.Arm.CombPrecompute.entry, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (withAllRest (combEntryArgs_ok s h incomingCount incomingBase output domain domainLength)) ?_
  rintro u ⟨⟨contextU,frameU⟩,restU⟩
  refine WP.mono (prepareArgs_ok u 24 contextU (by decide) (by decide) (by decide) (by decide)) ?_
  rintro v ⟨contextV,_,source,count,stack,frameV,restV⟩
  have narrowV : Frame [⟨State.addr s.sp,72⟩] u.mem v.mem := by
    apply frameV.sub
    intro r hr
    simp only [prepareWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    refine ⟨⟨State.addr s.sp,72⟩,by simp,?_⟩
    rcases hr with rfl | rfl
    · rw [restU.sp]; exact Offset.sub_base (State.addr s.sp) (d := 8) (n := 4) (k := 72) (by decide)
    · rw [restU.sp]; exact Offset.sub_base (State.addr s.sp) (d := 12) (n := 4) (k := 72) (by decide)
  have stackV : v.gpr .r12 = v.sp := stack.trans restV.sp.symm
  refine WP.mono (domainPointers_ok v contextV (by decide) source count stackV) ?_
  rintro t ⟨contextT,frameT,restT⟩
  refine ⟨contextT,frameU.trans (narrowV.trans ?_)⟩
  apply frameT.sub
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  refine ⟨⟨State.addr s.sp,72⟩,by simp,?_⟩
  rcases hr with rfl | rfl
  · rw [restV.sp,restU.sp]; exact Offset.sub_base (State.addr s.sp) (d := 56) (n := 4) (k := 72) (by decide)
  · rw [restV.sp,restU.sp]; exact Offset.sub_base (State.addr s.sp) (d := 60) (n := 4) (k := 72) (by decide)

end VG.Proof.Ffdh.Arm

end

end

/-! Native ABI inputs for initializing one public comb context. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

def combPrecomputeWrites (p : Inputs) (s : State) : List Region :=
  [⟨State.addr p.base,8*p.len⟩,⟨State.addr p.output,CombBuilder.bytes p⟩,
    ⟨State.addr s.sp,72⟩,FrameStack.belowA s.sp 48]

structure CombPrecomputeFnInput (p : Inputs) (s : State) : Prop where
  stackFits : 176 ≤ s.sp.toNat
  args : ArgumentMemory p [] (entered s)
  incomingCount : IncomingWord (BitVec.ofNat 32 p.k) 128 (entered s)
  incomingBase : IncomingWord p.base 132 (entered s)
  outputReg : s.gpr .r0 = p.output
  domainReg : s.gpr .r2 = p.domain
  domainLengthReg : s.gpr .r3 = BitVec.ofNat 32 p.dom.length
  calls : KeyCallMemory p (entered s)
  output : OutputBuffer p.output (CombBuilder.bytes p) (entered s)
  workspaceSeparate : Region.Disjoint ⟨State.addr p.base,8*p.len⟩ ⟨State.addr p.output,CombBuilder.bytes p⟩
  domainSeparate : Region.Disjoint ⟨State.addr p.domain,p.dom.length⟩ ⟨State.addr p.output,CombBuilder.bytes p⟩
  localSeparate : Region.Disjoint ⟨State.addr (entered s).sp,72⟩ ⟨State.addr p.output,CombBuilder.bytes p⟩
  callSeparate : Region.Disjoint ⟨State.addr p.output,CombBuilder.bytes p⟩ (FrameStack.belowA (entered s).sp 48)
  valid : Spec.Ffdh.domainValid p.k p.dom
  environment : VettedGroups.environment.holds p (entered s)
  saved : ∀ r ∈ combPrecomputeWrites p (entered s),
    (⟨State.addr (pcPushed s).sp,56⟩ : Region).Disjoint r

end VG.Proof.Ffdh.Arm

end

end

/-! ### `Ffdh.Arm.CombPrecomputeTableInit`, which the modules that import this one used -/

section

/-! ### `Ffdh.Arm.CombPrecomputeBasis`, which the modules that import this one used -/

section

/-! ### `Ffdh.Arm.CombPrecomputeProductState`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.CombPrecomputeProduct`, which this module and modules that import it used -/

section

/-! One shared Montgomery product combines a table entry with the public basis. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Keeps Operand)
open VG.Proof.X25519.Arm (Rest)

theorem product6_ok (backend : MontBackend) (s : State) {p : Inputs} {sp : BitVec 32} {exponent low : Nat}
    (h : Core p sp s) (power : Power5 p exponent s)
    (selected : numAt s.mem (State.addr p.base) p.w 1 = entryValue p low) :
    WP isa (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul 6 1 5) s fun t =>
      Core p sp t ∧ Power5 p exponent t ∧
      numAt t.mem (State.addr p.base) p.w 6 =
        VG.Spec.Rsa.powMod p.G (VG.Spec.Rsa.FixedBaseComb.exponent (bits p) low + exponent) p.P * 2^(64*p.w) % p.P ∧
      Keeps (State.addr p.base) p.len p.w 6 s.mem t.mem ∧
      Frame [⟨State.addr p.base,8*p.len⟩,FrameStack.belowA s.sp 48] s.mem t.mem ∧ Rest roundClobbers s t := by
  let K := TwoExp.sharedMontgomery p.base sp p.len p.w backend.name backend.mul
    (fun _ _ _ ho ha hb v input => backend.correct v input ho ha hb) backend.stackOk
  have persistent : TwoExp.CallReady p.base sp p.len s := ⟨h.memory.calls.stack,h.memory.fixed⟩
  have operand : Operand 5 := by simp [Operand,Proof.Rsa.Mont.aAcc,Proof.Rsa.Mont.aTmp]
  have positive : 0 < p.P := by have := h.memory.ready.modulus; rw [h.modulus] at this; omega_using [this]
  have bound : numAt s.mem (State.addr p.base) p.w 5 < numAt s.mem (State.addr p.base) p.w 0 := by
    rw [h.modulus,power]
    exact Nat.mod_lt _ positive
  refine WP.mono (K.op_ok s 6 1 5 h.memory.ready persistent (by simp [Operand,Proof.Rsa.Mont.aAcc,Proof.Rsa.Mont.aTmp]) (by simp [Operand,Proof.Rsa.Mont.aAcc,Proof.Rsa.Mont.aTmp]) operand (by decide) bound) ?_
  rintro t ⟨ready,_,canonical,value,keeps,_,frame,rest⟩
  have frame' : Frame [⟨State.addr p.base,8*p.len⟩,FrameStack.belowA s.sp 48] s.mem t.mem := by
    simpa only [K,h.memory.fixed] using frame
  have memory := h.memory.after_arithmetic ready frame' rest
  have core := h.after_array memory keeps (by decide) (by decide) (by decide)
  rw [h.modulus] at canonical value
  have encoded := VG.Proof.Rsa.FixedBaseComb.mont_product_encoded
    (VG.Proof.Bignum.coprime_pow2 h.odd (64*p.w)) canonical (show numAt s.mem (State.addr p.base) p.w 1 = _ from selected) power value
  have fit := h.memory.ready.width ▸ h.memory.ready.layout.2.2.1
  have powerT : Power5 p exponent t := (keeps_array_num keeps fit operand (by decide)).trans power
  exact ⟨core,powerT,encoded,keeps,frame',rest⟩


theorem product_entry_value (p : Inputs) {j low : Nat} (hj : j < 5) (hlow : low < 2^j) :
    VG.Spec.Rsa.powMod p.G
      (VG.Spec.Rsa.FixedBaseComb.exponent (bits p) low + 2^(j*VG.Spec.Rsa.FixedBaseComb.rows (bits p))) p.P *
      2^(64*p.w) % p.P = entryValue p (2^j+low) := by
  unfold entryValue
  rw [VG.Proof.Rsa.FixedBaseComb.exponent_add_tooth (bits p) j low hj hlow]

end VG.Proof.Ffdh.Arm.CombBuilder

end

end

/-! ### `Ffdh.Arm.CombPrecomputeProductLoad`, which this module and modules that import it used -/

section

/-! A subset product reads a previously completed canonical table entry. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/CombPrecomputeEntryBounds.lean`, which only this module imported.
section

/-! Each packed table entry is a disjoint slice of the context output. -/

section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Mont

theorem entry_geometry {p : Inputs} {sp : BitVec 32} {s : State} {digit : Nat}
    (h : Memory p sp s) (hd : digit < 32) :
    let src := p.output + BitVec.ofNat 32 (entryOffset p digit)
    State.addr src = off (State.addr p.output) (entryOffset p digit) ∧
      src.toNat + 8*p.w ≤ 2^32 ∧
      InRegions (s.rd++s.wr) (State.addr src) (8*p.w) ∧
      Region.Disjoint ⟨State.addr p.base,8*p.len⟩ ⟨State.addr src,8*p.w⟩ := by
  dsimp only
  have bound := entry_bound p hd
  have hw := p.width.1
  have small : p.output.toNat + entryOffset p digit < 2^32 := by have := h.output.fits; omega
  have address : State.addr (p.output + BitVec.ofNat 32 (entryOffset p digit)) =
      off (State.addr p.output) (entryOffset p digit) := addr_add small
  have fit : (p.output + BitVec.ofNat 32 (entryOffset p digit)).toNat + 8*p.w ≤ 2^32 := by
    simp only [BitVec.toNat_add,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : entryOffset p digit < 2^32),Nat.mod_eq_of_lt small]
    have := h.output.fits
    omega
  have write := CallLay.inRegions_sub h.output.writable bound
    (by have := h.output.fits; omega : bytes p < 2^64)
  obtain ⟨r,hr,contains⟩ := write
  refine ⟨address,fit,?_,?_⟩
  · rw [address]
    exact ⟨r,List.mem_append_right _ hr,contains⟩
  · rw [address]
    exact h.workspaceSeparate.sub_right (entry_sub p hd)

end VG.Proof.Ffdh.Arm.CombBuilder
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand)
open VG.Proof.X25519.Arm (Rest wp_mov op2_imm)

theorem productLoad_ok (s : State) {p : Inputs} {sp : BitVec 32} {count low exponent : Nat}
    (h : Core p sp s) (power : Power5 p exponent s) (table : TablePrefix p count s.mem)
    (hc : count ≤ 32) (hl : low < count)
    (savedLow : s.mem.readW (off (State.addr s.sp) 40) 32 = BitVec.ofNat 32 low) :
    WP isa VG.Impl.Ffdh.Arm.CombPrecompute.productLoad s fun t =>
      Core p sp t ∧ Power5 p exponent t ∧ numAt t.mem (State.addr p.base) p.w 1 = entryValue p low ∧
      TablePrefix p count t.mem ∧ WorkspaceEq (State.addr p.output) (bytes p) s.mem t.mem ∧
      Frame [⟨State.addr p.base,8*p.len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have geometry := entry_geometry h.memory (by omega_using [hc, hl] : low < 32)
  obtain ⟨address,sourceFit,read,sep⟩ := geometry
  have header := nativeHeader_of_layout s.mem p.base h.memory.ready.workspace.nowrap (Nat.le_refl _) h.memory.ready.layout
  rw [h.memory.ready.width] at header
  have savedCtx := h.memory.context.saved 4 (by simp [slots])
  change s.mem.readW (off (State.addr s.sp) 4) 32 = p.output at savedCtx
  have fit : 52 ≤ 8*p.len := by
    have := h.memory.ready.layout.2.2.1
    rw [h.memory.ready.width] at this
    simp only [Proof.Rsa.Mont.arrAt,Proof.Rsa.Mont.hdrBytes] at this
    omega_using [this]
  rw [VG.Impl.Ffdh.Arm.CombPrecompute.productLoad,WP.seq_iff,WP.block_append_iff,WP.block_append_iff]
  refine WP.mono (localLoad_ok s .r3 h.memory.context.locals (d := 40) (by decide)) ?_
  rintro u ⟨loaded,memU,restU⟩
  have ptrU := (restU.gpr .r0 (by simp)).trans h.memory.ready.ptr
  refine WP.mono (combTableArgs_raw_ok u (ctx := p.output) (h.memory.ready.workspace.congr restU.wr)
    (h.memory.context.locals.after restU) fit ptrU (by rw [memU]; exact header.count)
    (by rw [memU,restU.sp]; exact savedCtx) (loaded.trans savedLow)) ?_
  rintro v ⟨⟨output,ptrV,memV⟩,restV⟩
  rw [combTableAddress] at output
  refine wp_mov (op2_imm (by decide)) fun z moved => WP.block_nil ?_
  have rz : Rest roundClobbers s z :=
    (restU.mono (by simp [roundClobbers])).trans (restV.trans (moved.rest (by simp [roundClobbers])))
  have mz : z.mem = s.mem := moved.mem.trans (memV.trans memU)
  have pz := (moved.other .r0 (by decide)).trans ptrV
  have coreZ := h.of_mem mz rz pz
  have shape : LayoutFrameReady p.base p.len p.w z :=
    ⟨⟨coreZ.memory.ready.workspace,coreZ.memory.ready.layout,coreZ.memory.ready.width,pz⟩,
      coreZ.memory.ready.stackRead,coreZ.memory.ready.stackSep,coreZ.memory.ready.saved⟩
  have sourceZ : z.gpr .r4 = p.output + BitVec.ofNat 32 (entryOffset p low) :=
    (moved.other .r4 (by decide)).trans output
  refine WP.mono (importArrayLayout_ok z shape (by decide) sourceFit
    (by rw [rz.rd,rz.wr]; exact read) sep moved.gpr sourceZ) ?_
  rintro t ⟨shapeT,value,keeps,frame,rest,sourceT⟩
  obtain ⟨readyT,_⟩ := coreZ.memory.ready.after_array (by decide : 1 ≠ 0) keeps frame rest shapeT.ptr
  have frameWide : Frame [⟨State.addr p.base,8*p.len⟩,FrameStack.belowA z.sp 48] z.mem t.mem :=
    frame.mono (by intro r hr; have eq := List.mem_singleton.mp hr; subst r; simp)
  have memoryT := coreZ.memory.after_arithmetic readyT frameWide rest
  have coreT := coreZ.after_array memoryT keeps (by decide) (by decide) (by decide)
  have arrayFit := coreZ.memory.ready.width ▸ coreZ.memory.ready.layout.2.2.1
  have op5 : Operand 5 := by simp [Operand,Proof.Rsa.Mont.aAcc,Proof.Rsa.Mont.aTmp]
  have powerT : Power5 p exponent t :=
    (keeps_array_num keeps arrayFit op5 (by decide)).trans (power.of_mem mz)
  rw [mz,address] at value
  have selected := value.trans (table low hl)
  rw [mz] at frame
  have contextEq : WorkspaceEq (State.addr p.output) (bytes p) s.mem t.mem :=
    WorkspaceEq.of_frame (by have := h.memory.output.fits; omega_using [this]) frame
      (by intro r hr; have eq := List.mem_singleton.mp hr; subst r; exact h.memory.workspaceSeparate.symm)
  have tableT : TablePrefix p count t.mem := by
    intro digit hd
    rw [contextEq.read (entryOffset p digit) (8*p.w) (entry_bound p (by omega_using [hc, hd]))]
    exact table digit hd
  exact ⟨coreT,powerT,selected,tableT,contextEq,frame,rz.trans rest⟩

end VG.Proof.Ffdh.Arm.CombBuilder

end

end

/-! Shared memory boundaries for the public subset-product loop. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

def productWrites (p : Inputs) (sp : BitVec 32) : List Region :=
  [⟨State.addr p.base,8*p.len⟩,⟨State.addr p.output,bytes p⟩,
    ⟨State.addr sp,72⟩,FrameStack.belowA sp 48]

def ProductCount (sp : BitVec 32) (high low : Nat) (s : State) : Prop :=
  s.mem.readW (off (State.addr sp) 36) 32=BitVec.ofNat 32 high ∧
  s.mem.readW (off (State.addr sp) 40) 32=BitVec.ofNat 32 low


def productBodyWrites (p : Inputs) (sp : BitVec 32) : List Region :=
  [⟨State.addr p.base,8*p.len⟩,⟨State.addr p.output,bytes p⟩,FrameStack.belowA sp 48]

theorem ProductCount.after_frame {p : Inputs} {sp : BitVec 32} {s t : State} {high low : Nat}
    (count : ProductCount sp high low s) (h : Memory p sp s)
    (frame : Frame (productBodyWrites p sp) s.mem t.mem) : ProductCount sp high low t := by
  have frame' : Frame [⟨State.addr p.base,8*p.len⟩,⟨State.addr p.output,bytes p⟩,
      FrameStack.belowA s.sp 48] s.mem t.mem := by simpa only [productBodyWrites,h.fixed] using frame
  constructor
  · rw [←h.fixed,h.controlRead frame' 36 (by decide),h.fixed]
    exact count.1
  · rw [←h.fixed,h.controlRead frame' 40 (by decide),h.fixed]
    exact count.2

theorem product_body_arithmetic {p : Inputs} {sp : BitVec 32} {s t : State}
    (h : Memory p sp s)
    (frame : Frame [⟨State.addr p.base,8*p.len⟩,FrameStack.belowA s.sp 48] s.mem t.mem) :
    Frame (productBodyWrites p sp) s.mem t.mem := by
  apply frame.mono
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · simp [productBodyWrites]
  · simp [productBodyWrites,h.fixed]

theorem product_body_store {p : Inputs} {sp : BitVec 32} {s t : State} {digit : Nat}
    (hd : digit < 32)
    (frame : Frame [⟨off (State.addr p.output) (entryOffset p digit),8*p.w⟩] s.mem t.mem) :
    Frame (productBodyWrites p sp) s.mem t.mem := by
  apply frame.sub
  intro r hr
  have eq := List.mem_singleton.mp hr
  subst r
  exact ⟨_,by simp [productBodyWrites],entry_sub p hd⟩


theorem Memory.controlContextEq {p : Inputs} {sp : BitVec 32} {s t : State} {d : Nat}
    (h : Memory p sp s) (hd : d+4≤72)
    (frame : Frame [⟨off (State.addr sp) d,4⟩] s.mem t.mem) :
    WorkspaceEq (State.addr p.output) (bytes p) s.mem t.mem := by
  apply WorkspaceEq.of_frame (by have := h.output.fits; omega_using [this]) frame
  intro r hr
  have eq := List.mem_singleton.mp hr
  subst r
  exact h.localSeparate.symm.sub_right (Offset.sub_base _ hd)

end VG.Proof.Ffdh.Arm.CombBuilder

end

end

/-! ### `Ffdh.Arm.CombPrecomputeProducts`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.CombPrecomputeProductInit`, which this module and modules that import it used -/

section

/-! Public initialization and advancement between comb subset blocks. -/
@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

private theorem productsInit_raw (s : State) {base : BitVec 32} {len : Nat}
    (locals : Locals base len s) :
    WP isa (.block [.mov .r3 (.imm 1),.addSp .r12 0,VG.Impl.Ffdh.Arm.Domain.st .r3 40]) s fun t =>
      t.mem=s.mem.writeW (off (State.addr s.sp) 40) (1:BitVec 32) ∧ Rest [.r3,.r12] s t := by
  have addr : State.addr (s.sp+BitVec.ofNat 32 40)=off (State.addr s.sp) 40 := addr_add (by have := locals.space.nowrap; omega_using [this])
  have write := locals.space.write (off:=40) (by decide)
  refine withRest_all (c:=.block _) [.r3,.r12] ?_ (by rfl) rfl
  unfold VG.Impl.Ffdh.Arm.Domain.st
  ffrun [addr,write,off,BitVec.add_zero]

theorem productsInit_state (s : State) {p : Inputs} {sp : BitVec 32} {E high : Nat}
    (h : Core p sp s) (power : Power5 p E s)
    (savedHigh : s.mem.readW (off (State.addr sp) 36) 32=BitVec.ofNat 32 high) :
    WP isa (.block [.mov .r3 (.imm 1),.addSp .r12 0,VG.Impl.Ffdh.Arm.Domain.st .r3 40]) s fun t =>
      Core p sp t ∧ Power5 p E t ∧
      t.mem.readW (off (State.addr sp) 36) 32=BitVec.ofNat 32 high ∧
      t.mem.readW (off (State.addr sp) 40) 32=1 ∧
      Frame [⟨off (State.addr sp) 40,4⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (productsInit_raw s h.memory.context.locals) ?_
  rintro t ⟨mem,rest⟩
  have raw : Frame [⟨off (State.addr s.sp) 40,4⟩] s.mem t.mem := by
    rw [mem]
    exact (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
  have r : Rest roundClobbers s t := rest.mono (by simp [roundClobbers])
  have next := h.memory.after_control (by simp) raw r ((rest.gpr .r0 (by simp)).trans h.memory.context.ptr)
  refine ⟨h.after_workspace next.1 next.2,power.after_workspace h next.2,?_,?_,?_,r⟩
  · have keep := raw.readW (w:=32) (r:=⟨off (State.addr s.sp) 36,4⟩) (Region.contains_self _ _)
      (by intro region hr; rw [List.mem_singleton] at hr; subst region
          exact Offset.disjoint _ (by decide) (by decide) (by decide)) (by decide)
    rw [h.memory.fixed] at keep
    exact keep.trans savedHigh
  · rw [mem,h.memory.fixed,Mem.readW_writeW_self32]
  · rw [←h.memory.fixed]
    exact raw

theorem basisNext_state (s : State) {p : Inputs} {sp : BitVec 32} {E high : Nat}
    (h : Core p sp s) (power : Power5 p E s) (fit : 2*high<2^32)
    (savedHigh : s.mem.readW (off (State.addr sp) 36) 32=BitVec.ofNat 32 high) :
    WP isa (.block VG.Impl.Ffdh.Arm.CombPrecompute.basisNext) s fun t =>
      Core p sp t ∧ Power5 p E t ∧
      t.mem.readW (off (State.addr sp) 36) 32=BitVec.ofNat 32 (2*high) ∧
      t.z=decide (2*high=32) ∧
      Frame [⟨off (State.addr sp) 36,4⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (basisNext_raw s h.memory.context.locals fit (by rw [h.memory.fixed];exact savedHigh)) ?_
  rintro t ⟨⟨mem,zero⟩,rest⟩
  have raw : Frame [⟨off (State.addr s.sp) 36,4⟩] s.mem t.mem := by
    rw [mem]
    exact (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
  have r : Rest roundClobbers s t := rest.mono (by simp [roundClobbers])
  have next := h.memory.after_control (by simp) raw r ((rest.gpr .r0 (by simp)).trans h.memory.context.ptr)
  refine ⟨h.after_workspace next.1 next.2,power.after_workspace h next.2,?_,zero,?_,r⟩
  · rw [mem,h.memory.fixed,Mem.readW_writeW_self32]
  · rw [←h.memory.fixed]
    exact raw

end VG.Proof.Ffdh.Arm.CombBuilder

end

end

/-! ### `Ffdh.Arm.CombPrecomputeProductRound`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.CombPrecomputeProductBody`, which only this module used -/

section

/-! One public subset extension reuses the shared Montgomery helper. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem productBody_ok (backend : MontBackend) (s : State) {p : Inputs} {sp : BitVec 32} {j low : Nat}
    (h : Core p sp s) (hj : j<5) (hlow : low<2^j)
    (power : Power5 p (2^(j*Spec.Rsa.FixedBaseComb.rows (bits p))) s)
    (table : TablePrefix p (2^j+low) s.mem) (bound : 2^j+low<32)
    (count : ProductCount sp (2^j) low s) :
    WP isa (.seq VG.Impl.Ffdh.Arm.CombPrecompute.productLoad
      (.seq (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul 6 1 5)
        VG.Impl.Ffdh.Arm.CombPrecompute.productStore)) s fun t =>
      Core p sp t ∧ Power5 p (2^(j*Spec.Rsa.FixedBaseComb.rows (bits p))) t ∧
      TablePrefix p (2^j+low+1) t.mem ∧ ProductCount sp (2^j) low t ∧
      WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem t.mem ∧
      Frame (productBodyWrites p sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [WP.seq_iff]
  have countBound : 2^j+low≤32 := by omega_using [bound]
  have lowBound : low<2^j+low := by have := Nat.two_pow_pos j; omega_using [hlow]
  refine WP.mono (productLoad_ok s h power table countBound lowBound (by rw [h.memory.fixed]; exact count.2)) ?_
  rintro u ⟨coreU,powerU,selected,tableU,ctxU,frameU,restU⟩
  have wideU : Frame [⟨State.addr p.base,8*p.len⟩,FrameStack.belowA s.sp 48] s.mem u.mem :=
    frameU.mono (by intro r hr; have eq := List.mem_singleton.mp hr; subst r; simp)
  have bodyU := product_body_arithmetic h.memory wideU
  have countU := count.after_frame h.memory bodyU
  rw [WP.seq_iff]
  refine WP.mono (product6_ok backend u coreU powerU selected) ?_
  rintro v ⟨coreV,powerV,value,keeps,frameV,restV⟩
  have bodyV := product_body_arithmetic coreU.memory frameV
  have countV := countU.after_frame coreU.memory bodyV
  have tableV := tableU.after_arithmetic coreU.memory countBound frameV
  rw [product_entry_value p hj hlow] at value
  refine WP.mono (productStore_ok v coreV powerV tableV bound value
    (by rw [coreV.memory.fixed]; exact countV.1) (by rw [coreV.memory.fixed]; exact countV.2)) ?_
  rintro t ⟨coreT,powerT,tableT,headerT,frameT,restT⟩
  have bodyT := product_body_store (sp:=sp) bound frameT
  have countT := countV.after_frame coreV.memory bodyT
  have headerV := headEq_arithmetic coreU.memory frameV
  have headerU : WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem u.mem := by
    refine ⟨?_⟩
    intro d n hd
    exact ctxU.read d n (by have := bytes_eq p; omega_using [hd, this])
  have header : WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem t.mem := by
    refine ⟨?_⟩
    intro d n hd
    exact (headerT.read d n hd).trans ((headerV.read d n hd).trans (headerU.read d n hd))
  exact ⟨coreT,powerT,tableT,countT,header,bodyU.trans (bodyV.trans bodyT),restU.trans (restV.trans restT)⟩

end VG.Proof.Ffdh.Arm.CombBuilder

end

end


/-! A public subset extension followed by its descending loop measure. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem product_round_ok (backend : MontBackend) (s : State) {p : Inputs} {sp : BitVec 32} {j low : Nat}
    (h : Core p sp s) (hj : j<5) (hlow : low<2^j)
    (power : Power5 p (2^(j*Spec.Rsa.FixedBaseComb.rows (bits p))) s)
    (table : TablePrefix p (2^j+low) s.mem) (bound : 2^j+low<32)
    (count : ProductCount sp (2^j) low s) :
    WP isa (.seq VG.Impl.Ffdh.Arm.CombPrecompute.productLoad
      (.seq (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul 6 1 5)
        (.seq VG.Impl.Ffdh.Arm.CombPrecompute.productStore
          (.block VG.Impl.Ffdh.Arm.CombPrecompute.productNext)))) s fun t =>
      Core p sp t ∧ Power5 p (2^(j*Spec.Rsa.FixedBaseComb.rows (bits p))) t ∧
      TablePrefix p (2^j+(low+1)) t.mem ∧ ProductCount sp (2^j) (low+1) t ∧
      t.z=decide (low+1=2^j) ∧
      WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem t.mem ∧
      Frame (productWrites p sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  suffices grouped : WP isa (.seq
      (.seq VG.Impl.Ffdh.Arm.CombPrecompute.productLoad
        (.seq (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul 6 1 5)
          VG.Impl.Ffdh.Arm.CombPrecompute.productStore))
      (.block VG.Impl.Ffdh.Arm.CombPrecompute.productNext)) s fun t =>
      Core p sp t ∧ Power5 p (2^(j*Spec.Rsa.FixedBaseComb.rows (bits p))) t ∧
      TablePrefix p (2^j+(low+1)) t.mem ∧ ProductCount sp (2^j) (low+1) t ∧
      t.z=decide (low+1=2^j) ∧
      WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem t.mem ∧
      Frame (productWrites p sp) s.mem t.mem ∧ Rest roundClobbers s t by
    obtain ⟨trace,t,exec,post⟩ := grouped
    cases exec with
    | seq hab hd =>
      cases hab with
      | seq ha hbc =>
        cases hbc with
        | seq hb hc => exact ⟨_,_,.seq ha (.seq hb (.seq hc hd)),post⟩
  rw [WP.seq_iff]
  refine WP.mono (productBody_ok backend s h hj hlow power table bound count) ?_
  rintro u ⟨core,pow,tableU,countU,headerU,frameU,restU⟩
  have highFit : 2^j<2^32 := Nat.pow_lt_pow_right (by decide) (by omega_using [hj])
  have lowFit : low+1<2^32 := by omega_using [hlow, bound]
  refine WP.mono (productNext_state u core pow lowFit highFit countU.2 countU.1) ?_
  rintro t ⟨coreT,powT,highT,lowT,zero,frameT,restT⟩
  have ctxT := core.memory.controlContextEq (by decide) frameT
  have tableT : TablePrefix p (2^j+(low+1)) t.mem := by
    intro digit hd
    rw [ctxT.read (entryOffset p digit) (8*p.w) (entry_bound p (by omega_using [bound, hd]))]
    apply tableU digit
    omega_using [hd]
  have header : WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem t.mem := by
    refine ⟨?_⟩
    intro d n hd
    exact (ctxT.read d n (by have := bytes_eq p; omega_using [hd, this])).trans (headerU.read d n hd)
  have wholeU : Frame (productWrites p sp) s.mem u.mem := frameU.mono (by intro r hr; simp only [productBodyWrites,List.mem_cons,List.not_mem_nil,or_false] at hr; rcases hr with rfl|rfl|rfl <;> simp [productWrites])
  have wholeT : Frame (productWrites p sp) u.mem t.mem := frameT.sub (by
    intro r hr
    have eq := List.mem_singleton.mp hr
    subst r
    exact ⟨⟨State.addr sp,72⟩,by simp [productWrites],Offset.sub_base _ (by decide)⟩)
  exact ⟨coreT,powT,tableT,⟨highT,lowT⟩,zero,header,wholeU.trans wholeT,restU.trans restT⟩

end VG.Proof.Ffdh.Arm.CombBuilder

end

end

/-! The subset-product runtime loop fills one contiguous half of the table. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem products_loop_ok (backend : MontBackend) (s : State) {p : Inputs} {sp : BitVec 32} {j low : Nat}
    (h : Core p sp s) (hj : j<5) (hlow : low<2^j)
    (power : Power5 p (2^(j*Spec.Rsa.FixedBaseComb.rows (bits p))) s)
    (table : TablePrefix p (2^j+low) s.mem)
    (count : ProductCount sp (2^j) low s) :
    WP isa (.loop (.seq VG.Impl.Ffdh.Arm.CombPrecompute.productLoad
      (.seq (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul 6 1 5)
        (.seq VG.Impl.Ffdh.Arm.CombPrecompute.productStore
          (.block VG.Impl.Ffdh.Arm.CombPrecompute.productNext)))) .ne) s fun t =>
      Core p sp t ∧ Power5 p (2^(j*Spec.Rsa.FixedBaseComb.rows (bits p))) t ∧
      TablePrefix p (2*2^j) t.mem ∧ ProductCount sp (2^j) (2^j) t ∧
      WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem t.mem ∧
      Frame (productWrites p sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  have highBound : 2^j≤16 := by
    have := Nat.pow_le_pow_right (by decide : 0<2) (by omega_using [hj] : j≤4)
    exact this
  let I := fun k t => 0<k ∧ k≤2^j ∧ Core p sp t ∧
    Power5 p (2^(j*Spec.Rsa.FixedBaseComb.rows (bits p))) t ∧
    TablePrefix p (2^j+(2^j-k)) t.mem ∧ ProductCount sp (2^j) (2^j-k) t ∧
    WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem t.mem ∧
    Frame (productWrites p sp) s.mem t.mem ∧ Rest roundClobbers s t
  refine WP.loop (M:=isa) I ?_ (2^j-low) s ?_
  · intro k u hu
    obtain ⟨positive,bounded,core,pow,tab,counter,header,frame,rest⟩ := hu
    refine WP.mono (product_round_ok backend u core hj (by omega_using [hlow, positive]) pow tab (by omega_using [highBound, positive]) counter) ?_
    rintro t ⟨coreT,powT,tableT,countT,zero,headerT,frameT,restT⟩
    have next : 2^j-k+1=2^j-(k-1) := by omega_using [positive, bounded]
    rw [next] at tableT countT zero
    have headerAll : WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem t.mem := by
      refine ⟨?_⟩
      intro d n hd
      exact (headerT.read d n hd).trans (header.read d n hd)
    by_cases last : k-1=0
    · left
      refine ⟨?_,coreT,powT,?_,?_,headerAll,frame.trans frameT,rest.trans restT⟩
      · change some (!t.z)=some false
        simp only [zero,last,Nat.sub_zero,decide_true,Bool.not_true]
      · simpa only [last,Nat.sub_zero,←Nat.two_mul] using tableT
      · simpa only [last,Nat.sub_zero] using countT
    · right
      refine ⟨?_,k-1,by omega_using [positive],by omega_using [last],by omega_using [bounded],coreT,powT,tableT,countT,headerAll,frame.trans frameT,rest.trans restT⟩
      change some (!t.z)=some true
      have neq : 2^j-(k-1)≠2^j := by omega_using [hlow, last]
      simp only [zero,neq,decide_false,Bool.not_false]
  · refine ⟨by omega_using [hlow],by omega_using [hlow],h,power,?_,?_,⟨fun _ _ _ => rfl⟩,Frame.refl _ _,Rest.refl _ _⟩
    · simpa only [Nat.sub_sub_self (by omega_using [hlow] : low≤2^j)] using table
    · simpa only [Nat.sub_sub_self (by omega_using [hlow] : low≤2^j)] using count


theorem products_ok (backend : MontBackend) (s : State) {p : Inputs} {sp : BitVec 32} {j : Nat}
    (h : Core p sp s) (hj : j<5) (positive : 0<j)
    (power : Power5 p (2^(j*Spec.Rsa.FixedBaseComb.rows (bits p))) s)
    (table : TablePrefix p (2^j+1) s.mem)
    (saved : s.mem.readW (off (State.addr sp) 36) 32=BitVec.ofNat 32 (2^j)) :
    WP isa (VG.Impl.Ffdh.Arm.CombPrecompute.products
      (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) s fun t =>
      Core p sp t ∧ Power5 p (2^(j*Spec.Rsa.FixedBaseComb.rows (bits p))) t ∧
      TablePrefix p (2*2^j) t.mem ∧
      t.mem.readW (off (State.addr sp) 36) 32=BitVec.ofNat 32 (2^j) ∧
      WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem t.mem ∧
      Frame (productWrites p sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.CombPrecompute.products,WP.seq_iff]
  refine WP.mono (productsInit_state s h power saved) ?_
  rintro u ⟨core,pow,highU,lowU,frameU,restU⟩
  have ctxU := h.memory.controlContextEq (by decide) frameU
  have tableU : TablePrefix p (2^j+1) u.mem := by
    intro digit hd
    rw [ctxU.read (entryOffset p digit) (8*p.w) (entry_bound p (by
      have := Nat.pow_le_pow_right (by decide : 0<2) (by omega_using [hj] : j≤4)
      omega_using [hd, this]))]
    exact table digit hd
  have oneLow : 1<2^j := by have := Nat.pow_lt_pow_right (by decide : 1<2) positive; exact this
  refine WP.mono (products_loop_ok backend u core hj oneLow pow tableU ⟨highU,lowU⟩) ?_
  rintro t ⟨coreT,powT,tableT,countT,headerT,frameT,restT⟩
  have header : WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem t.mem := by
    refine ⟨?_⟩
    intro d n hd
    exact (headerT.read d n hd).trans (ctxU.read d n (by have := bytes_eq p; omega_using [hd, this]))
  have wholeU : Frame (productWrites p sp) s.mem u.mem := frameU.sub (by
    intro r hr
    have eq := List.mem_singleton.mp hr
    subst r
    exact ⟨⟨State.addr sp,72⟩,by simp [productWrites],Offset.sub_base _ (by decide)⟩)
  exact ⟨coreT,powT,tableT,countT.1,header,wholeU.trans frameT,restU.trans restT⟩

end VG.Proof.Ffdh.Arm.CombBuilder

end

end

/-! ### `Ffdh.Arm.CombPrecomputeBasisStore`, which this module and modules that import it used -/

section

/-! Publish the newly squared basis element before filling its subsets. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem basisStore_ok (s : State) {p : Inputs} {sp : BitVec 32} {j : Nat}
    (h : Core p sp s) (hj : j<5)
    (power : Power5 p (2^(j*Spec.Rsa.FixedBaseComb.rows (bits p))) s)
    (table : TablePrefix p (2^j) s.mem)
    (saved : s.mem.readW (off (State.addr sp) 36) 32=BitVec.ofNat 32 (2^j)) :
    WP isa (.seq (.block [.ldrSp .r3 36]) (VG.Impl.Ffdh.Arm.CombPrecompute.store 5)) s fun t =>
      Core p sp t ∧ Power5 p (2^(j*Spec.Rsa.FixedBaseComb.rows (bits p))) t ∧
      TablePrefix p (2^j+1) t.mem ∧
      t.mem.readW (off (State.addr sp) 36) 32=BitVec.ofNat 32 (2^j) ∧
      WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem t.mem ∧
      Frame (productBodyWrites p sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  have bound : 2^j<32 := Nat.pow_lt_pow_right (by decide) hj
  rw [WP.seq_iff]
  refine WP.mono (localLoad_ok s .r3 h.memory.context.locals (d:=36) (by decide)) ?_
  rintro u ⟨index,mem,rest⟩
  have ptr := (rest.gpr .r0 (by simp)).trans h.memory.ready.ptr
  have coreU := h.of_mem mem rest ptr
  have index' : u.gpr .r3=BitVec.ofNat 32 (2^j) := by rw [index,h.memory.fixed];exact saved
  refine WP.mono (combStoreMemory_ok u coreU.memory bound (by decide) index') ?_
  rintro t ⟨memory,workspace,written,frame,restT⟩
  have coreT := coreU.after_workspace memory workspace
  have powerU := power.of_mem mem
  have powerT := powerU.after_workspace coreU workspace
  have value : VG.Proof.Rsa.Mont.numAt u.mem (State.addr p.base) p.w 5=entryValue p (2^j) := by
    rw [powerU,entryValue,VG.Proof.Rsa.FixedBaseComb.exponent_tooth (bits p) j hj]
  have tableU : TablePrefix p (2^j) u.mem := by rw [mem];exact table
  have tableT := tableU.extend coreU.memory bound frame (written.trans value)
  have header := headEq_store coreU.memory bound frame
  have body := product_body_store (sp:=sp) bound frame
  have preserved := coreU.memory.controlRead (by simpa only [productBodyWrites,coreU.memory.fixed] using body) 36 (by decide)
  rw [coreU.memory.fixed,mem] at preserved
  rw [mem] at header body
  have wholeRest := (rest.mono (by simp [roundClobbers])).trans restT
  exact ⟨coreT,powerT,tableT,preserved.trans saved,header,body,wholeRest⟩

end VG.Proof.Ffdh.Arm.CombBuilder

end

end

/-! ### `Ffdh.Arm.CombPrecomputeSquares`, which this module and modules that import it used -/

section

/-! The public descending counter performs exactly d shared basis squares. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem square_round_ok (backend : MontBackend) (s : State) {p : Inputs} {sp : BitVec 32} {E n : Nat}
    (h : Core p sp s) (power : Power5 p E s) (positive : 0<n) (fits : n<2^32)
    (counter : SquareCount sp n s) :
    WP isa (.seq (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul 5 5 5)
      (.block VG.Impl.Ffdh.Arm.CombPrecompute.squaresNext)) s fun t =>
      Core p sp t ∧ Power5 p (2*E) t ∧ SquareCount sp (n-1) t ∧ t.z=decide (n-1=0) ∧
      Frame (squareNarrowWrites p sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [WP.seq_iff]
  refine WP.mono (square5_ok backend s h power) ?_
  rintro u ⟨core,pow,_keeps,frame,rest⟩
  have preserved : SquareCount sp n u := by
    change u.mem.readW (off (State.addr sp) 68) 32=BitVec.ofNat 32 n
    have sub : (⟨off (State.addr sp) 68,4⟩ : Region).Sub ⟨State.addr sp,72⟩ := Offset.sub_base _ (by decide)
    rw [frame.readW (r:=⟨off (State.addr sp) 68,4⟩) (Region.contains_self _ _) (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl
      · exact h.memory.context.locals.separate.sub_left (by rw [h.memory.fixed]; exact sub)
      · have fit : 48≤sp.toNat := by rw [←h.memory.fixed]; exact h.memory.calls.stack.fit
        rw [h.memory.fixed,FrameStack.belowA,FrameStack.addr_sub' fit]
        exact ((Offset.below_disjoint _ (by decide : 48+72≤2^64)).symm).sub_left sub) (by decide)]
    exact counter
  refine WP.mono (squaresNext_state u core pow positive fits preserved) ?_
  rintro t ⟨coreT,powT,countT,zero,frameT,restT⟩
  have frameS : Frame (squareNarrowWrites p sp) s.mem u.mem := frame.sub (by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · exact ⟨_,by simp [squareNarrowWrites],fun _ hx => hx⟩
    · rw [h.memory.fixed]
      exact ⟨_,by simp [squareNarrowWrites],fun _ hx => hx⟩)
  exact ⟨coreT,powT,countT,zero,frameS.trans frameT,rest.trans restT⟩

theorem squares_loop_ok (backend : MontBackend) (s : State) {p : Inputs} {sp : BitVec 32} {E D : Nat}
    (h : Core p sp s) (power : Power5 p E s) (positive : 0<D) (fits : D<2^32)
    (counter : SquareCount sp D s) :
    WP isa (.loop (.seq (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul 5 5 5)
      (.block VG.Impl.Ffdh.Arm.CombPrecompute.squaresNext)) .ne) s fun t =>
      Core p sp t ∧ Power5 p (2^D*E) t ∧ SquareCount sp 0 t ∧
      Frame (squareNarrowWrites p sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  let I := fun k t => 0<k ∧ k≤D ∧ Core p sp t ∧ Power5 p (2^(D-k)*E) t ∧ SquareCount sp k t ∧
    Frame (squareNarrowWrites p sp) s.mem t.mem ∧ Rest roundClobbers s t
  refine WP.loop (M:=isa) I ?_ D s ?_
  · intro k u hu
    obtain ⟨hk,bound,core,pow,count,frame,rest⟩ := hu
    refine WP.mono (square_round_ok backend u core pow hk (by omega_using [fits, bound]) count) ?_
    rintro t ⟨coreT,powT,countT,zero,frameT,restT⟩
    have exponent : 2*(2^(D-k)*E)=2^(D-(k-1))*E := by
      rw [show D-(k-1)=(D-k)+1 by omega_using [hk, bound],Nat.pow_succ]
      ac_rfl
    rw [exponent] at powT
    by_cases last : k-1=0
    · left
      refine ⟨?_,coreT,?_,?_,frame.trans frameT,rest.trans restT⟩
      · change some (!t.z)=some false
        simp only [zero,last,decide_true,Bool.not_true]
      · simpa only [last,Nat.sub_zero] using powT
      · simpa only [last] using countT
    · right
      refine ⟨?_,k-1,by omega_using [hk],by omega_using [last],by omega_using [bound],coreT,powT,countT,frame.trans frameT,rest.trans restT⟩
      change some (!t.z)=some true
      simp only [zero,last,decide_false,Bool.not_false]
  · refine ⟨positive,by omega_using [],h,?_,counter,Frame.refl _ _,Rest.refl _ _⟩
    simpa only [Nat.sub_self,Nat.pow_zero,Nat.one_mul] using power

theorem squares_ok (backend : MontBackend) (s : State) {p : Inputs} {sp : BitVec 32} {E : Nat}
    (h : Core p sp s) (power : Power5 p E s)
    (positive : 0<Spec.Rsa.FixedBaseComb.rows (bits p))
    (fits : Spec.Rsa.FixedBaseComb.rows (bits p)<2^32) :
    WP isa (VG.Impl.Ffdh.Arm.CombPrecompute.squares
      (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) s fun t =>
      Core p sp t ∧ Power5 p (2^Spec.Rsa.FixedBaseComb.rows (bits p)*E) t ∧
      WorkspaceEq (State.addr p.output) (bytes p) s.mem t.mem ∧
      Frame (squareNarrowWrites p sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.CombPrecompute.squares,WP.seq_iff]
  refine WP.mono (squaresInit_state s h power) ?_
  rintro u ⟨core,pow,count,frame,rest⟩
  refine WP.mono (squares_loop_ok backend u core pow positive fits count) ?_
  rintro t ⟨coreT,powT,_countT,frameT,restT⟩
  have all := frame.trans frameT
  exact ⟨coreT,powT,h.memory.squareNarrowContextEq all,all,rest.trans restT⟩

end VG.Proof.Ffdh.Arm.CombBuilder

end

end

/-! One public basis round fills the next dense half of the comb table. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem basis_ok (backend : MontBackend) (s : State) {p : Inputs} {sp : BitVec 32} {j : Nat}
    (h : Core p sp s) (hj : j<5) (jpositive : 0<j)
    (positive : 0<Spec.Rsa.FixedBaseComb.rows (bits p))
    (fits : Spec.Rsa.FixedBaseComb.rows (bits p)<2^32)
    (power : Power5 p (2^((j-1)*Spec.Rsa.FixedBaseComb.rows (bits p))) s)
    (table : TablePrefix p (2^j) s.mem)
    (saved : s.mem.readW (off (State.addr sp) 36) 32=BitVec.ofNat 32 (2^j)) :
    WP isa (VG.Impl.Ffdh.Arm.CombPrecompute.basis
      (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) s fun t =>
      Core p sp t ∧ Power5 p (2^(j*Spec.Rsa.FixedBaseComb.rows (bits p))) t ∧
      TablePrefix p (2^(j+1)) t.mem ∧
      t.mem.readW (off (State.addr sp) 36) 32=BitVec.ofNat 32 (2^(j+1)) ∧
      t.z=decide (j=4) ∧
      WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem t.mem ∧
      Frame (productWrites p sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  have highBound : 2^j≤16 := Nat.pow_le_pow_right (by decide : 0<2) (by omega_using [hj] : j≤4)
  have nextHigh : 2*2^j=2^(j+1) := by rw [Nat.pow_succ]; ac_rfl
  have stop : (2*2^j=32) ↔ j=4 := by
    have cases : j=1 ∨ j=2 ∨ j=3 ∨ j=4 := by omega_using [hj, jpositive]
    rcases cases with rfl|rfl|rfl|rfl <;> decide
  have exponent : 2^Spec.Rsa.FixedBaseComb.rows (bits p)*
      2^((j-1)*Spec.Rsa.FixedBaseComb.rows (bits p))=
      2^(j*Spec.Rsa.FixedBaseComb.rows (bits p)) := by
    rw [←Nat.pow_add]
    congr 1
    calc
      _ = 1*Spec.Rsa.FixedBaseComb.rows (bits p)+(j-1)*Spec.Rsa.FixedBaseComb.rows (bits p) := by rw [Nat.one_mul]
      _ = (1+(j-1))*Spec.Rsa.FixedBaseComb.rows (bits p) := (Nat.add_mul _ _ _).symm
      _ = _ := by rw [show 1+(j-1)=j by omega_using [jpositive]]
  rw [VG.Impl.Ffdh.Arm.CombPrecompute.basis,WP.seq_iff]
  refine WP.mono (squares_ok backend s h power positive fits) ?_
  rintro u ⟨coreU,powerU,ctxU,frameU,restU⟩
  rw [exponent] at powerU
  have tableU : TablePrefix p (2^j) u.mem := by
    intro digit hd
    rw [ctxU.read (entryOffset p digit) (8*p.w) (entry_bound p (by omega_using [highBound, hd]))]
    exact table digit hd
  have savedU := (h.memory.squareNarrowRead36 frameU).trans saved
  have squareFrame : Frame (productWrites p sp) s.mem u.mem := frameU.sub (by
    intro r hr
    simp only [squareNarrowWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · exact ⟨_,by simp [productWrites],fun _ hx => hx⟩
    · exact ⟨⟨State.addr sp,72⟩,by simp [productWrites],Offset.sub_base _ (by decide)⟩
    · exact ⟨_,by simp [productWrites],fun _ hx => hx⟩)
  have grouped : WP isa (.seq
      (.seq (.block [.ldrSp .r3 36]) (VG.Impl.Ffdh.Arm.CombPrecompute.store 5))
      (.seq (VG.Impl.Ffdh.Arm.CombPrecompute.products (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul))
        (.block VG.Impl.Ffdh.Arm.CombPrecompute.basisNext))) u (fun t =>
      Core p sp t ∧ Power5 p (2^(j*Spec.Rsa.FixedBaseComb.rows (bits p))) t ∧
      TablePrefix p (2^(j+1)) t.mem ∧
      t.mem.readW (off (State.addr sp) 36) 32=BitVec.ofNat 32 (2^(j+1)) ∧
      t.z=decide (j=4) ∧ WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem t.mem ∧
      Frame (productWrites p sp) s.mem t.mem ∧ Rest roundClobbers s t) := by
    rw [WP.seq_iff]
    refine WP.mono (basisStore_ok u coreU hj powerU tableU savedU) ?_
    rintro v ⟨coreV,powerV,tableV,savedV,headV,frameV,restV⟩
    rw [WP.seq_iff]
    refine WP.mono (products_ok backend v coreV hj jpositive powerV tableV savedV) ?_
    rintro w ⟨coreW,powerW,tableW,savedW,headW,frameW,restW⟩
    refine WP.mono (basisNext_state w coreW powerW (by omega_using [highBound]) savedW) ?_
    rintro t ⟨coreT,powerT,savedT,zeroT,frameT,restT⟩
    simp only [stop] at zeroT
    rw [nextHigh] at tableW savedT
    have ctxT := coreW.memory.controlContextEq (d:=36) (by decide) (by simpa only [coreW.memory.fixed] using frameT)
    have tableT : TablePrefix p (2^(j+1)) t.mem := by
      intro digit hd
      rw [ctxT.read (entryOffset p digit) (8*p.w) (entry_bound p (by
        rw [←nextHigh] at hd
        omega_using [highBound, hd]))]
      exact tableW digit hd
    have header : WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem t.mem := by
      refine ⟨?_⟩
      intro d n hd
      exact (ctxT.read d n (by rw [bytes_eq]; omega_using [hd])).trans
        ((headW.read d n hd).trans ((headV.read d n hd).trans (ctxU.read d n (by rw [bytes_eq]; omega_using [hd]))))
    have storeFrame : Frame (productWrites p sp) u.mem v.mem := frameV.mono (by
      intro r hr
      simp only [productBodyWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl <;> simp [productWrites])
    have nextFrame : Frame (productWrites p sp) w.mem t.mem := frameT.sub (by
      intro r hr
      have eq := List.mem_singleton.mp hr
      subst r
      exact ⟨⟨State.addr sp,72⟩,by simp [productWrites],Offset.sub_base _ (by decide)⟩)
    exact ⟨coreT,powerT,tableT,savedT,zeroT,header,
      squareFrame.trans (storeFrame.trans (frameW.trans nextFrame)),
      restU.trans (restV.trans (restW.trans restT))⟩
  obtain ⟨trace,t,run,post⟩ := grouped
  cases run with
  | seq ab c =>
    cases ab with
    | seq a b => exact ⟨_,t,.seq a (.seq b c),post⟩

end VG.Proof.Ffdh.Arm.CombBuilder

end

end

/-! Initialize the first nontrivial public comb basis counter. -/
@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

private theorem tableInit_raw (s : State) {base : BitVec 32} {len : Nat}
    (locals : Locals base len s) :
    WP isa (.block [.mov .r3 (.imm 2),.addSp .r12 0,VG.Impl.Ffdh.Arm.Domain.st .r3 36]) s fun t =>
      t.mem=s.mem.writeW (off (State.addr s.sp) 36) (2:BitVec 32) ∧ Rest [.r3,.r12] s t := by
  have addr : State.addr (s.sp+BitVec.ofNat 32 36)=off (State.addr s.sp) 36 := addr_add (by have := locals.space.nowrap; omega_using [this])
  have write := locals.space.write (off:=36) (by decide)
  refine withRest_all (c:=.block _) [.r3,.r12] ?_ (by rfl) rfl
  unfold VG.Impl.Ffdh.Arm.Domain.st
  ffrun [addr,write,off,BitVec.add_zero]

theorem tableInit_state (s : State) {p : Inputs} {sp : BitVec 32} {E : Nat}
    (h : Core p sp s) (power : Power5 p E s) :
    WP isa (.block [.mov .r3 (.imm 2),.addSp .r12 0,VG.Impl.Ffdh.Arm.Domain.st .r3 36]) s fun t =>
      Core p sp t ∧ Power5 p E t ∧
      t.mem.readW (off (State.addr sp) 36) 32=2 ∧
      Frame [⟨off (State.addr sp) 36,4⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (tableInit_raw s h.memory.context.locals) ?_
  rintro t ⟨mem,rest⟩
  have raw : Frame [⟨off (State.addr s.sp) 36,4⟩] s.mem t.mem := by
    rw [mem]
    exact (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
  have r : Rest roundClobbers s t := rest.mono (by simp [roundClobbers])
  have next := h.memory.after_control (by simp) raw r ((rest.gpr .r0 (by simp)).trans h.memory.context.ptr)
  refine ⟨h.after_workspace next.1 next.2,power.after_workspace h next.2,?_,?_,r⟩
  · rw [mem,h.memory.fixed,Mem.readW_writeW_self32]
  · rw [←h.memory.fixed]
    exact raw

end VG.Proof.Ffdh.Arm.CombBuilder

end

end

/-! ### `Ffdh.Arm.CombPrecomputePrefix`, which the modules that import this one used -/

section

/-! ### `Ffdh.Arm.NormalizedPrepareAt`, which this module and modules that import it used -/

section

/-! # Normalized callable modulus preparation within the FFDH argument frame -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Rsa.Mont (numAt)

theorem normalizedPrepareAt24_ok (backend : MontBackend) (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (calls : KeyCallMemory p s)
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots)
    (large : 1 < p.P) (odd : p.P % 2 = 1)
    (normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P) :
    WP isa (VG.Impl.Ffdh.Arm.NormalizedPrepare.prepareAt
      (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) 24) s fun t =>
      Context p slots t ∧ ArithmeticReady p.base p.len p.w t ∧
      numAt t.mem (State.addr p.base) p.w 0 = p.P ∧
      numAt t.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P ∧
      Frame (keyPrepareWrites p s) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.NormalizedPrepare.prepareAt, WP.seq_iff]
  refine WP.mono (prepareArgs_ok s 24 h stable h24 h32 h0) ?_
  rintro u ⟨contextU, stack, _, countU, _, frameU, restU⟩
  have sourceU := contextU.pBytes
  have bytes : Spec.Rsa.bytesAt u.mem (State.addr p.domain) p.k = p.dom.take p.k := by
    simpa only [p.pLength] using sourceU.bytes
  have input : PrepareInput p.base p.domain p.len p.k u :=
    ⟨contextU.workspace, by rw [stack.savedOutput]; exact stack, contextU.ptr, countU,
      p.minLength, p.maxLength, p.publicSpace,
      by rw [← p.pLength]; exact sourceU.fits,
      by rw [← p.pLength]; exact sourceU.readable,
      by rw [← p.pLength]; exact sourceU.separate,
      by rw [bytes]; exact large, by rw [bytes]; exact odd⟩
  let K := TwoExp.sharedMontgomery p.base s.sp p.len p.w backend.name backend.mul
    (fun _ _ _ ho ha hb v input => backend.correct v input ho ha hb) backend.stackOk
  have hp : TwoExp.CallReady p.base s.sp p.len u := ⟨(calls.after restU).stack, restU.sp⟩
  refine WP.mono (normalizedPrepare_ok u K input hp (by rw [bytes]; exact normalized)) ?_
  rintro t ⟨ready, modulus, r2, _, frameT, restT⟩
  rw [bytes] at modulus r2
  have localFrame : Frame [⟨State.addr p.base, 8 * p.len⟩, FrameStack.belowA u.sp 48]
      u.mem t.mem := by simpa only [K, restU.sp] using frameT
  have contextT := contextU.after_call (calls.after restU) localFrame restT ready.ptr
    (fun d hd => (stableSlots_at stable hd).1)
  have frame : Frame (keyPrepareWrites p s) s.mem t.mem :=
    (frameU.mono (by intro r hr; simp only [keyPrepareWrites, prepareAtWrites, List.mem_append,
      List.mem_cons]; exact Or.inl (Or.inr hr))).trans
      (frameT.mono (by
        intro r hr
        simp only [List.mem_cons] at hr
        simp only [keyPrepareWrites, prepareAtWrites, List.mem_append, List.mem_cons]
        rcases hr with hr | hr
        · exact Or.inl (Or.inl hr)
        · exact Or.inr hr))
  exact ⟨contextT, ready, modulus, r2, frame,
    (restU.mono (by simp [roundClobbers])).trans restT⟩

end VG.Proof.Ffdh.Arm

end

end

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
  obtain prefixFit : 24≤bytes p := by
    unfold bytes Spec.Ffdh.generationPrecomputedWords
    omega_arith
  obtain headerSub : (⟨State.addr p.output,24⟩ : Region).Sub ⟨State.addr p.output,bytes p⟩ :=
    by simpa only [off,BitVec.add_zero] using (Offset.sub_base (State.addr p.output) (d:=0) (n:=24) (k:=bytes p) prefixFit)
  obtain headerSep := localSeparate.sub_right headerSub
  obtain ws : OutputBuffer p.output 24 s := ⟨by have := output.fits; omega_arith,
    by
      obtain ⟨r,hr,h⟩ := output.writable
      exact ⟨r,hr,by change (State.addr p.output-r.base).toNat+24≤r.len; change (State.addr p.output-r.base).toNat+bytes p≤r.len at h; omega_arith⟩⟩
  refine WP.mono (combMetadata_ok s context.locals ws headerSep positive bound
    (context.saved 4 (by decide)) width mask) ?_
  rintro t ⟨mem,frame,restSmall⟩
  obtain rest : Rest roundClobbers s t := restSmall.mono (by simp [combMetadataClobbers,roundClobbers])
  obtain workspaceSep : ∀ r∈combMetadataWrites s p.output,
      (⟨State.addr p.base,8*p.len⟩ : Region).Disjoint r := by
    intro r hr
    simp only [combMetadataWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · exact context.locals.separate.symm.sub_right (Offset.sub_base _ (by decide))
    · exact context.locals.separate.symm.sub_right (Offset.sub_base _ (by decide))
    · exact workspaceSeparate.sub_right headerSub
  obtain baseSep : ∀ r∈combMetadataWrites s p.output,
      (⟨State.addr s.sp,4⟩ : Region).Disjoint r := by
    intro r hr
    simp only [combMetadataWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · exact Offset.base_disjoint _ (by decide) (by decide)
    · exact Offset.base_disjoint _ (by decide) (by decide)
    · exact headerSep.sub_left (by simpa only [off,BitVec.add_zero] using
        (Offset.sub_base (State.addr s.sp) (d:=0) (n:=4) (k:=72) (by decide)))
  obtain ptr : t.gpr .r0=p.base := (restSmall.gpr .r0 (by simp [combMetadataClobbers])).trans context.ptr
  obtain ⟨readyT,workspace⟩ := ready.after_external frame workspaceSep baseSep rest ptr
  obtain contextT := context.after_frame frame rest ptr (by
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
    obtain sub := Offset.sub_base (State.addr s.sp) (d:=d) (n:=4) (k:=72) fit
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
  obtain modulusValid := Proof.Ffdh.domainValid_mod valid
  change Spec.Rsa.modulusValid p.P p.k=true at modulusValid
  obtain facts := Proof.Bignum.valid_facts modulusValid p.minLength
  obtain params : Spec.Ffdh.parametersValid (Spec.Ffdh.domainOf p.k p.dom)=true := by
    have v := valid
    unfold Spec.Ffdh.domainValid at v
    simp only [Bool.and_eq_true] at v
    exact v.1
  obtain positive : 0<bits p := CachedSample.generation_positive params
  obtain bound : bits p≤8192 := CachedSample.bits_bound p
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
  obtain envU := VettedGroups.environment.stable environment
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
  obtain rV := restU.trans restV
  obtain sepLocal : ∀r∈[⟨off (State.addr u.sp) 20,4⟩,⟨off (State.addr u.sp) 68,4⟩],
      (⟨State.addr p.base,8*p.len⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> exact ctxU.locals.separate.symm.sub_right (Offset.sub_base _ (by decide))
  obtain sepZero : ∀r∈[⟨off (State.addr u.sp) 20,4⟩,⟨off (State.addr u.sp) 68,4⟩],
      (⟨State.addr u.sp,4⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> exact Offset.base_disjoint _ (by decide) (by decide)
  have ptrV := ctxV.ptr
  obtain ⟨readyV,workspaceV⟩ := readyU.after_external frameV sepLocal sepZero restV ptrV
  obtain fit := readyU.width ▸ readyU.layout.2.2.1
  obtain modV := (workspaceV.number fit (by decide : 0<8)).trans modU
  obtain r2V := (workspaceV.number fit (by decide : 4<8)).trans r2U
  obtain widthEq : (ScalarLayout.vetted p).width=Proof.Ffdh.ScalarWidth.width (bits p) :=
    by
      obtain width := CachedSample.layout_width p positive
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
  obtain memoryT : Memory p s.sp t := by simpa only [rV.sp] using memory
  obtain fitV := readyV.width ▸ readyV.layout.2.2.1
  obtain widthNat : Proof.Ffdh.ScalarWidth.width (bits p)=(bits p+7)/8 := by
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
  obtain context : Context p slots u :=
    ⟨⟨ctxU.workspace,ctxU.locals,ctxU.domain,ctxU.domainStack,fun d hd =>
      ctxU.saved d (by simp only [slots,List.mem_cons,List.not_mem_nil,or_false] at hd ⊢; omega_arith)⟩,ctxU.ptr⟩
  obtain environment := VettedGroups.environment.stable h.environment
    (frameU.mono (by simp [keyCallWrites,keyWrites])) restU symsU
  refine WP.mono (prefix_ok backend u context environment (h.calls.after restU) (h.output.after restU)
    h.workspaceSeparate h.domainSeparate (by rw [restU.sp]; exact h.localSeparate)
    (by rw [restU.sp]; exact h.callSeparate) h.valid) ?_
  rintro t ⟨memory,header,modulus,r2,frameT,_restT⟩
  refine ⟨by simpa only [restU.sp] using memory,header,modulus,r2,?_⟩
  obtain fullU : Frame (combPrecomputeWrites p (entered s)) (entered s).mem u.mem :=
    frameU.mono (by simp [combPrecomputeWrites])
  exact fullU.trans (by simpa only [combPrecomputeWrites,restU.sp] using frameT)

end CombBuilder
end VG.Proof.Ffdh.Arm

end

end

/-! Public geometry retained by the comb-builder timing composition. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm

structure EnterInput (p : Inputs) (sp : BitVec 32) (s : State) : Prop where
  context : Context p slots s
  environment : VettedGroups.environment.holds p s
  calls : KeyCallMemory p s
  output : OutputBuffer p.output (bytes p) s
  workspaceSeparate : Region.Disjoint ⟨State.addr p.base,8*p.len⟩ ⟨State.addr p.output,bytes p⟩
  domainSeparate : Region.Disjoint ⟨State.addr p.domain,p.dom.length⟩ ⟨State.addr p.output,bytes p⟩
  localSeparate : Region.Disjoint ⟨State.addr sp,72⟩ ⟨State.addr p.output,bytes p⟩
  callSeparate : Region.Disjoint ⟨State.addr p.output,bytes p⟩ (FrameStack.belowA sp 48)
  fixed : s.sp=sp
  valid : Spec.Ffdh.domainValid p.k p.dom=true

end VG.Proof.Ffdh.Arm.CombBuilder

end

end

/-! ### `Ffdh.Arm.CombPrecomputeSquaresCT`, which only this module used -/

section

/-! Basis squaring follows its public saved row count, independent of residue values. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)

structure SquareInput (p : Inputs) (sp : BitVec 32) (n : Nat) (s : State) : Prop where
  core : Core p sp s
  power : ∃E, Power5 p E s
  counter : SquareCount sp n s

private theorem counter_after_square {p : Inputs} {sp : BitVec 32} {s t : State} {n : Nat}
    (h : Memory p sp s) (counter : SquareCount sp n s)
    (frame : Frame [⟨State.addr p.base,8*p.len⟩,FrameStack.belowA s.sp 48] s.mem t.mem) :
    SquareCount sp n t := by
  have localEq : WorkspaceEq (State.addr s.sp) 72 s.mem t.mem := by
    apply WorkspaceEq.of_frame (by decide) frame
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · exact h.context.locals.separate
    · rw [FrameStack.belowA,FrameStack.addr_sub' h.calls.stack.fit]
      exact (Offset.below_disjoint _ (by decide)).symm
  have word := localEq.word (d:=68) (bits:=32) (by decide)
  rw [h.fixed] at word
  exact word.trans counter

theorem power5_bound {p : Inputs} {sp : BitVec 32} {s : State}
    (h : Core p sp s) (power : ∃E,Power5 p E s) :
    numAt s.mem (State.addr p.base) p.w 5<numAt s.mem (State.addr p.base) p.w 0 := by
  obtain ⟨E,power⟩ := power
  rw [h.modulus,power]
  apply Nat.mod_lt
  have positive := h.memory.ready.modulus
  rw [h.modulus] at positive
  omega_using [positive]

private theorem square_ct (backend : MontBackend) {p : Inputs} {sp : BitVec 32} {n : Nat} :
    RelCT isa (fun s t => SquareInput p sp n s ∧ SquareInput p sp n t ∧ s.sp=t.sp)
      (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul 5 5 5) (fun _ _ => True) := by
  have operand : Proof.Rsa.Mont.Operand 5 := by
    simp [Proof.Rsa.Mont.Operand,Proof.Rsa.Mont.aAcc,Proof.Rsa.Mont.aTmp]
  exact (montCallOp_ct backend.name backend.mul (backend.rawCT operand operand operand) operand operand operand).mono
    (fun _ _ h => ⟨h.1.core.memory.ready,h.2.1.core.memory.ready,h.1.core.memory.calls.stack,
      h.2.1.core.memory.calls.stack,power5_bound h.1.core h.1.power,power5_bound h.2.1.core h.2.1.power,h.2.2⟩)
    (fun _ _ _ => trivial)

private theorem square_post (backend : MontBackend) (s : State) {p : Inputs} {sp : BitVec 32} {n : Nat}
    (h : SquareInput p sp n s) : WP isa (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul 5 5 5) s
      (SquareInput p sp n) := by
  obtain ⟨E,power⟩ := h.power
  refine WP.mono (square5_ok backend s h.core power) ?_
  rintro t ⟨core,power,_,frame,_⟩
  exact ⟨core,⟨2*E,power⟩,counter_after_square h.core.memory h.counter frame⟩

private theorem squaresInit_ct : RelCT isa (fun s t => s.sp=t.sp)
    (.block VG.Impl.Ffdh.Arm.CombPrecompute.squaresInit) (fun _ _ => True) :=
  RelCT.block_append ((loadStack_ct .r3 44).seq
    (RelCT.block_append (stackAddr_ct.seq ((storeLocal_ct .r3 68).mono (fun _ _ h => h) (fun _ _ _ => trivial)))))

private theorem squaresNext_ct : RelCT isa (fun s t => s.sp=t.sp)
    (.block VG.Impl.Ffdh.Arm.CombPrecompute.squaresNext) (fun _ _ => True) := by
  have sub : RelCT isa (fun s t => s.sp=t.sp) (.block [.subs .r3 .r3 (.imm 1)])
      (fun s t => s.sp=t.sp) := by
    apply relCT_keep_sp _ (fun _ _ h => h)
    apply RelCT.taint (A:=taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  exact RelCT.block_append ((loadStack_ct .r3 68).seq
    (RelCT.block_append (sub.seq (RelCT.block_append (stackAddr_ct.seq
      ((storeLocal_ct .r3 68).mono (fun _ _ h => h) (fun _ _ _ => trivial)))))))

private theorem squareBody_post (backend : MontBackend) (s : State) {p : Inputs} {sp : BitVec 32} {n : Nat}
    (positive : 0<n) (fits : n<2^32) (h : SquareInput p sp n s) :
    WP isa (.seq (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul 5 5 5)
      (.block VG.Impl.Ffdh.Arm.CombPrecompute.squaresNext)) s
      (fun t => SquareInput p sp (n-1) t ∧ t.z=decide (n-1=0)) := by
  rw [WP.seq_iff]
  refine WP.mono (square_post backend s h) ?_
  intro u hu
  obtain ⟨E,power⟩ := hu.power
  refine WP.mono (squaresNext_state u hu.core power positive fits hu.counter) ?_
  rintro t ⟨core,power,count,zero,_,_⟩
  exact ⟨⟨core,⟨E,power⟩,count⟩,zero⟩

theorem squares_ct (backend : MontBackend) {p : Inputs} {sp : BitVec 32}
    (positive : 0<Spec.Rsa.FixedBaseComb.rows (bits p))
    (fits : Spec.Rsa.FixedBaseComb.rows (bits p)<2^32) :
    RelCT isa (fun s t => (Core p sp s ∧ ∃E,Power5 p E s) ∧
      (Core p sp t ∧ ∃E,Power5 p E t) ∧ s.sp=t.sp)
      (VG.Impl.Ffdh.Arm.CombPrecompute.squares (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul))
      (fun _ _ => True) := by
  let I := fun n s t => 0<n ∧ n<2^32 ∧ SquareInput p sp n s ∧ SquareInput p sp n t ∧ s.sp=t.sp
  have step : ∀n, RelCT isa (I n)
      (.seq (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul 5 5 5)
        (.block VG.Impl.Ffdh.Arm.CombPrecompute.squaresNext))
      (fun u v => isa.eval .ne u=isa.eval .ne v ∧ (isa.eval .ne u=some false → True) ∧
        (isa.eval .ne u=some true → ∃m<n,I m u v)) := by
    intro n s t tr1 tr2 u v h e1 e2
    have body := relCT_chain (square_ct backend (p:=p) (sp:=sp) (n:=n))
      (fun s h => square_post backend s h) (fun s h => square_post backend s h)
      (squaresNext_ct.mono (fun _ _ h => h.2.2) (fun _ _ h => h))
    obtain ⟨trace,sp'⟩ := relCT_keep_sp body (fun _ _ h => h.2.2) s t tr1 tr2 u v ⟨h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩ e1 e2
    obtain ⟨_,_,run1,left,z1⟩ := squareBody_post backend s h.1 h.2.1 h.2.2.1
    obtain ⟨_,_,run2,right,z2⟩ := squareBody_post backend t h.1 h.2.1 h.2.2.2.1
    obtain ⟨_,rfl⟩ := Exec.det e1 run1
    obtain ⟨_,rfl⟩ := Exec.det e2 run2
    refine ⟨trace,?_,fun _ => trivial,?_⟩
    · change some (!u.z)=some (!v.z)
      rw [z1,z2]
    · intro again
      have nz : n-1≠0 := by
        intro zero
        change some (!u.z)=some true at again
        simp only [z1,zero,decide_true,Bool.not_true,Option.some.injEq,Bool.false_eq_true] at again
      exact ⟨n-1,by omega_using [nz],by omega_using [nz],by omega,left,right,sp'⟩
  have init (s : State) (h : Core p sp s ∧ ∃E,Power5 p E s) :
      WP isa (.block VG.Impl.Ffdh.Arm.CombPrecompute.squaresInit) s
        (SquareInput p sp (Spec.Rsa.FixedBaseComb.rows (bits p))) := by
    obtain ⟨E,power⟩ := h.2
    refine WP.mono (squaresInit_state s h.1 power) ?_
    rintro t ⟨core,power,count,_,_⟩
    exact ⟨core,⟨E,power⟩,count⟩
  unfold VG.Impl.Ffdh.Arm.CombPrecompute.squares
  exact relCT_chain (squaresInit_ct.mono (fun _ _ h => h.2.2) (fun _ _ h => h)) init init
    ((RelCT.loop I step (Spec.Rsa.FixedBaseComb.rows (bits p))).mono
      (fun _ _ h => ⟨positive,fits,h.1,h.2.1,h.2.2⟩) (fun _ _ h => h))

end VG.Proof.Ffdh.Arm.CombBuilder

end

end

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
