module

public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeCore
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeTableState
public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeStoreMemory
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeMem
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Store a subset product at its public basis-plus-subset index. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem productStoreArgs_ok (s : State) {base : BitVec 32} {len high low : Nat}
    (locals : Locals base len s)
    (highSaved : s.mem.readW (off (State.addr s.sp) 36) 32 = BitVec.ofNat 32 high)
    (lowSaved : s.mem.readW (off (State.addr s.sp) 40) 32 = BitVec.ofNat 32 low) :
    WP isa (.block [.ldrSp .r3 36,.ldrSp .r2 40,.dp .add .r3 .r3 (.reg .r2)]) s fun t =>
      (t.gpr .r3 = BitVec.ofNat 32 (high+low) ∧ t.mem=s.mem ∧ t.gpr .r0=s.gpr .r0) ∧ Rest roundClobbers s t := by
  have a36 : State.addr (s.sp+BitVec.ofNat 32 36)=off (State.addr s.sp) 36 := addr_add (by have := locals.space.nowrap; omega)
  have a40 : State.addr (s.sp+BitVec.ofNat 32 40)=off (State.addr s.sp) 40 := addr_add (by have := locals.space.nowrap; omega)
  have r36 := locals.read (d:=36) (by decide)
  have r40 := locals.read (d:=40) (by decide)
  apply withAllRest
  ffrun [a36,a40,r36,r40,highSaved,lowSaved]
  exact (BitVec.ofNat_add high low).symm


theorem productStore_ok (s : State) {p : Inputs} {sp : BitVec 32} {high low exponent : Nat}
    (h : Core p sp s) (power : Power5 p exponent s)
    (table : TablePrefix p (high+low) s.mem) (bound : high+low < 32)
    (value : VG.Proof.Rsa.Mont.numAt s.mem (State.addr p.base) p.w 6 = entryValue p (high+low))
    (highSaved : s.mem.readW (off (State.addr s.sp) 36) 32 = BitVec.ofNat 32 high)
    (lowSaved : s.mem.readW (off (State.addr s.sp) 40) 32 = BitVec.ofNat 32 low) :
    WP isa VG.Impl.Ffdh.Arm.CombPrecompute.productStore s fun t =>
      Core p sp t ∧ Power5 p exponent t ∧ TablePrefix p (high+low+1) t.mem ∧
      WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem t.mem ∧
      Frame [⟨off (State.addr p.output) (entryOffset p (high+low)),8*p.w⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.CombPrecompute.productStore,WP.seq_iff]
  refine WP.mono (productStoreArgs_ok s h.memory.context.locals highSaved lowSaved) ?_
  rintro u ⟨⟨index,mem,ptrEq⟩,rest⟩
  have ptr := ptrEq.trans h.memory.ready.ptr
  have coreU := h.of_mem mem rest ptr
  refine WP.mono (combStoreMemory_ok u coreU.memory bound (by decide) index) ?_
  rintro t ⟨memory,workspace,written,frame,restT⟩
  have coreT := coreU.after_workspace memory workspace
  have powerT := (power.of_mem mem).after_workspace coreU workspace
  have tableU : TablePrefix p (high+low) u.mem := by rw [mem]; exact table
  have valueU : VG.Proof.Rsa.Mont.numAt u.mem (State.addr p.base) p.w 6 = entryValue p (high+low) := by rw [mem]; exact value
  have tableT := tableU.extend coreU.memory bound frame (written.trans valueU)
  have header := headEq_store coreU.memory bound frame
  rw [mem] at frame header
  exact ⟨coreT,powerT,tableT,header,frame,rest.trans restT⟩

end VG.Proof.Ffdh.Arm.CombBuilder
