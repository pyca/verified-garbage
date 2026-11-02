module

import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeInitial
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeStoreMemory
import VerifiedGarbage.Proof.Rsa.FixedBaseCombTable
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeTableState

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
