module

public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeTableState
public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeStore
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! Context stores retain the entire arithmetic workspace and caller geometry. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Spec.Rsa.Mont (arrAt numAt)
open VG.Proof.X25519.Arm (Rest)

theorem combStoreMemory_ok (s : State) {p : Inputs} {sp : BitVec 32} {digit o : Nat}
    (h : CombBuilder.Memory p sp s) (hd : digit < 32) (ho : o < 8)
    (index : s.gpr .r3 = BitVec.ofNat 32 digit) :
    WP isa (VG.Impl.Ffdh.Arm.CombPrecompute.store o) s fun t =>
      CombBuilder.Memory p sp t ∧ WorkspaceEq (State.addr p.base) (8*p.len) s.mem t.mem ∧
      (t.mem.read (off (State.addr p.output) (CombBuilder.entryOffset p digit)) (8*p.w)).toNat =
        numAt s.mem (State.addr p.base) p.w o ∧
      Frame [⟨off (State.addr p.output) (CombBuilder.entryOffset p digit),8*p.w⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  have bound := CombBuilder.entry_bound p hd
  have hw := p.width.1
  have small : p.output.toNat + CombBuilder.entryOffset p digit < 2^32 := by
    have := h.output.fits
    omega
  have address : State.addr (p.output + BitVec.ofNat 32 (CombBuilder.entryOffset p digit)) =
      off (State.addr p.output) (CombBuilder.entryOffset p digit) := addr_add small
  have address' : State.addr (p.output + BitVec.ofNat 32 (24+8*p.w*(digit+2))) =
      off (State.addr p.output) (CombBuilder.entryOffset p digit) := address
  have dstFit : (p.output + BitVec.ofNat 32 (CombBuilder.entryOffset p digit)).toNat + 8*p.w ≤ 2^32 := by
    simp only [BitVec.toNat_add,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : CombBuilder.entryOffset p digit < 2^32),Nat.mod_eq_of_lt small]
    have := h.output.fits
    omega
  have write := CallLay.inRegions_sub h.output.writable bound
    (by have := h.output.fits; omega : CombBuilder.bytes p < 2^64)
  have subset := CombBuilder.entry_sub p hd
  have sep := h.workspaceSeparate.sub_right subset
  have header := nativeHeader_of_layout s.mem p.base h.ready.workspace.nowrap (Nat.le_refl _) h.ready.layout
  rw [h.ready.width] at header
  have saved := h.context.saved 4 (by simp [CombBuilder.slots])
  change s.mem.readW (off (State.addr s.sp) 4) 32 = p.output at saved
  refine WP.mono (combStore_ok s h.ready.workspace h.context.locals h.ready.layout h.ready.width ho h.ready.ptr
    header.count saved index dstFit (by rw [address']; exact write) (by rw [address']; exact sep)) ?_
  rintro t ⟨value,frame,ptr,rest⟩
  change t.mem.read (State.addr (p.output + BitVec.ofNat 32 (CombBuilder.entryOffset p digit))) (8*p.w) = _ at value
  rw [address] at value
  rw [address'] at frame
  have whole : Frame [⟨State.addr p.output,CombBuilder.bytes p⟩] s.mem t.mem := by
    apply frame.sub
    intro r hr
    have eq := List.mem_singleton.mp hr
    subst r
    exact ⟨_,by simp,subset⟩
  obtain ⟨memory,workspace⟩ := h.after_external whole rest ptr
  exact ⟨memory,workspace,congrArg BitVec.toNat value,frame,rest⟩

end VG.Proof.Ffdh.Arm
