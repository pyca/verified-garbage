module

public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeTableState
public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute

import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.Arm.Locals
import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Rsa.MontContract
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeArgs
import VerifiedGarbage.Proof.Bignum.Arm.ExportArray
import VerifiedGarbage.Proof.Ffdh.Arm.Block
/-! Context stores retain the entire arithmetic workspace and caller geometry. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/CombPrecomputeStore.lean`, which only this module imported.
section

/-! Store a public residue at its canonical comb-table index. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Impl.Ffdh.Arm VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt Layout wOf)
open VG.Proof.X25519.Arm (Rest wp_mov op2_imm)

theorem combStore_ok (s : State) {base ctx : BitVec 32} {len w digit o : Nat}
    (ws : Workspace s base (8*len)) (locals : Locals base len s)
    (layout : Layout s.mem (State.addr base) len) (width : wOf s.mem (State.addr base) = w)
    (ho : o < 8) (ptr : s.gpr .r0 = base)
    (count : s.mem.readW (off (State.addr base) 48) 32 = BitVec.ofNat 32 w)
    (saved : s.mem.readW (off (State.addr s.sp) 4) 32 = ctx)
    (index : s.gpr .r3 = BitVec.ofNat 32 digit)
    (dstFit : (ctx + BitVec.ofNat 32 (24+8*w*(digit+2))).toNat + 8*w ≤ 2^32)
    (write : InRegions s.wr (State.addr (ctx + BitVec.ofNat 32 (24+8*w*(digit+2)))) (8*w))
    (sep : Region.Disjoint ⟨State.addr base,8*len⟩
      ⟨State.addr (ctx + BitVec.ofNat 32 (24+8*w*(digit+2))),8*w⟩) :
    WP isa (CombPrecompute.store o) s fun t =>
      t.mem.read (State.addr (ctx + BitVec.ofNat 32 (24+8*w*(digit+2)))) (8*w) =
        s.mem.read (off (State.addr base) (arrAt w o)) (8*w) ∧
      Frame [⟨State.addr (ctx + BitVec.ofNat 32 (24+8*w*(digit+2))),8*w⟩] s.mem t.mem ∧
      t.gpr .r0 = base ∧ Rest roundClobbers s t := by
  have fit := layout.2.2.1
  rw [width] at fit
  have size : 52 ≤ 8*len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fit; omega
  rw [CombPrecompute.store, WP.seq_iff, WP.block_append_iff]
  refine WP.mono (combTableArgs_raw_ok s ws locals size ptr count saved index) ?_
  rintro u ⟨⟨output, pu, memU⟩, restU⟩
  rw [combTableAddress] at output
  refine wp_mov (op2_imm (by
    apply encodable_byte
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : o < 2^32)]
    omega)) fun v moved => WP.block_nil ?_
  have restV : Rest roundClobbers u v := moved.rest (by simp [roundClobbers])
  have memV : v.mem = s.mem := moved.mem.trans memU
  refine WP.mono (exportArray_ok v (ws.congr (restV.wr.trans restU.wr))
    (by rw [memV]; exact layout) (by rw [memV]; exact width) ho dstFit
    (by rw [restV.wr, restU.wr]; exact write) sep
    ((moved.other .r0 (by decide)).trans pu) moved.gpr
    ((moved.other .r4 (by decide)).trans output)) ?_
  rintro t ⟨value, frame, pt, _, restT⟩
  rw [memV] at value frame
  exact ⟨value, frame, pt, restU.trans (restV.trans restT)⟩

end VG.Proof.Ffdh.Arm
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt)
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
