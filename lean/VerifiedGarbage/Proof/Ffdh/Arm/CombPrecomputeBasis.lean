module

public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeCore
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Impl.Bignum.Arm.MontCall
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeSquareState
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeSquare
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeStoreMemory
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProductCounter
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeMem
import VerifiedGarbage.Proof.Rsa.FixedBaseCombTable
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProductStore
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProductCounterState
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeTableState
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeArgs
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.ImportArrayLayout
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpShared
import VerifiedGarbage.Proof.Rsa.FixedBaseCombMont
import VerifiedGarbage.Proof.Bignum.Math

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
