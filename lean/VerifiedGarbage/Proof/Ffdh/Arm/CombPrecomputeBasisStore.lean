module

public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeCore
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProductState
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeStoreMemory
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProductCounter
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeMem
import VerifiedGarbage.Proof.Rsa.FixedBaseCombTable
import VerifiedGarbage.Proof.Framework.Block

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
