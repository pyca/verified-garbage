module

public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeTableState
public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeCore

import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeMem
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeArgs
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.ImportArrayLayout
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.CallLay
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
  have geometry := entry_geometry h.memory (by omega : low < 32)
  obtain ⟨address,sourceFit,read,sep⟩ := geometry
  have header := nativeHeader_of_layout s.mem p.base h.memory.ready.workspace.nowrap (Nat.le_refl _) h.memory.ready.layout
  rw [h.memory.ready.width] at header
  have savedCtx := h.memory.context.saved 4 (by simp [slots])
  change s.mem.readW (off (State.addr s.sp) 4) 32 = p.output at savedCtx
  have fit : 52 ≤ 8*p.len := by
    have := h.memory.ready.layout.2.2.1
    rw [h.memory.ready.width] at this
    simp only [Proof.Rsa.Mont.arrAt,Proof.Rsa.Mont.hdrBytes] at this
    omega
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
    WorkspaceEq.of_frame (by have := h.memory.output.fits; omega) frame
      (by intro r hr; have eq := List.mem_singleton.mp hr; subst r; exact h.memory.workspaceSeparate.symm)
  have tableT : TablePrefix p count t.mem := by
    intro digit hd
    rw [contextEq.read (entryOffset p digit) (8*p.w) (entry_bound p (by omega))]
    exact table digit hd
  exact ⟨coreT,powerT,selected,tableT,contextEq,frame,rz.trans rest⟩

end VG.Proof.Ffdh.Arm.CombBuilder
