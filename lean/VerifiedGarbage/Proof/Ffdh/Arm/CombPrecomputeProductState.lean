module

import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProductStore
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProductCounter
import VerifiedGarbage.Proof.Framework.Offset
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
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Impl.Bignum.Arm.MontCall
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpShared
import VerifiedGarbage.Proof.Rsa.FixedBaseCombMont
import VerifiedGarbage.Proof.Rsa.FixedBaseCombTable
import VerifiedGarbage.Proof.Bignum.Math

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
