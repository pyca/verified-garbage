module

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
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeState

/-! ### `Ffdh.Arm.CombPrecomputeTableState`, which this module and modules that import it used -/

section

/-! The public table is filled in increasing, densely packed entry order. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm

def entryOffset (p : Inputs) (digit : Nat) : Nat := 24 + 8*p.w*(digit+2)
def entryValue (p : Inputs) (digit : Nat) : Nat :=
  Spec.Rsa.powMod p.G (Spec.Rsa.FixedBaseComb.exponent (bits p) digit) p.P * 2^(64*p.w) % p.P

def TablePrefix (p : Inputs) (count : Nat) (m : Mem) : Prop :=
  ∀ digit < count,
    (m.read (off (State.addr p.output) (entryOffset p digit)) (8*p.w)).toNat = entryValue p digit

theorem bytes_eq (p : Inputs) : bytes p = 24 + 272*p.w := by
  simp only [bytes,Spec.Ffdh.generationPrecomputedWords,Spec.Rsa.FixedBaseComb.precomputedWords,
    Spec.Rsa.precomputedWords,Spec.Rsa.FixedBaseComb.entries,Spec.Rsa.FixedBaseComb.teeth,Inputs.w]
  omega_using []

theorem entry_bound (p : Inputs) {digit : Nat} (hd : digit < 32) :
    entryOffset p digit + 8*p.w ≤ bytes p := by
  have bound := Nat.mul_le_mul_left (8*p.w) (by omega_using [hd] : digit+3 ≤ 34)
  simp only [Nat.mul_add] at bound
  rw [entryOffset,bytes_eq]
  simp only [Nat.mul_add]
  omega_using [bound]

theorem entry_sub (p : Inputs) {digit : Nat} (hd : digit < 32) :
    (⟨off (State.addr p.output) (entryOffset p digit),8*p.w⟩ : Region).Sub
      ⟨State.addr p.output,bytes p⟩ := Offset.sub_base _ (entry_bound p hd)

theorem TablePrefix.after_arithmetic {p : Inputs} {sp : BitVec 32} {s t : State} {count : Nat}
    (h : Memory p sp s) (table : TablePrefix p count s.mem) (countFit : count ≤ 32)
    (frame : Frame [⟨State.addr p.base,8*p.len⟩,FrameStack.belowA s.sp 48] s.mem t.mem) :
    TablePrefix p count t.mem := by
  intro digit hd
  have subset := entry_sub p (by omega_using [countFit, hd] : digit < 32)
  have separate : ∀ r ∈ [⟨State.addr p.base,8*p.len⟩,FrameStack.belowA s.sp 48],
      (⟨off (State.addr p.output) (entryOffset p digit),8*p.w⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact h.workspaceSeparate.symm.sub_left subset
    · rw [h.fixed]
      exact h.callSeparate.sub_left subset
  have fit := entry_bound p (by omega_using [countFit, hd] : digit < 32)
  have read := frame.read (r := ⟨off (State.addr p.output) (entryOffset p digit),8*p.w⟩)
    (Region.contains_self _ _) separate (by have := h.output.fits; omega_using [fit, this])
  rw [read]
  exact table digit hd

theorem TablePrefix.extend {p : Inputs} {sp : BitVec 32} {s t : State} {count : Nat}
    (h : Memory p sp s) (table : TablePrefix p count s.mem) (countFit : count < 32)
    (frame : Frame [⟨off (State.addr p.output) (entryOffset p count),8*p.w⟩] s.mem t.mem)
    (value : (t.mem.read (off (State.addr p.output) (entryOffset p count)) (8*p.w)).toNat =
      entryValue p count) : TablePrefix p (count+1) t.mem := by
  intro digit hd
  by_cases old : digit < count
  · have order := Nat.mul_le_mul_left (8*p.w) (by omega_using [old] : digit+3 ≤ count+2)
    simp only [Nat.mul_add] at order
    have digitFit := entry_bound p (by omega_using [countFit, hd] : digit < 32)
    have countBound := entry_bound p countFit
    have separate : (⟨off (State.addr p.output) (entryOffset p digit),8*p.w⟩ : Region).Disjoint
        ⟨off (State.addr p.output) (entryOffset p count),8*p.w⟩ := by
      apply Offset.disjoint
      · left
        simp only [entryOffset,Nat.mul_add]
        omega_using [order]
      · have := h.output.fits
        omega_using [digitFit, this]
      · have := h.output.fits
        omega_using [countBound, this]
    have read := frame.read (r := ⟨off (State.addr p.output) (entryOffset p digit),8*p.w⟩)
      (Region.contains_self _ _) (by intro r hr; have eq := List.mem_singleton.mp hr; subst r; exact separate)
      (by have := h.output.fits; omega_using [digitFit, this])
    rw [read]
    exact table digit old
  · have eq : digit = count := by omega_using [hd, old]
    subst digit
    exact value

theorem headEq_arithmetic {p : Inputs} {sp : BitVec 32} {s t : State}
    (h : Memory p sp s)
    (frame : Frame [⟨State.addr p.base,8*p.len⟩,FrameStack.belowA s.sp 48] s.mem t.mem) :
    WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem t.mem := by
  have sub : (⟨State.addr p.output,24+16*p.w⟩ : Region).Sub ⟨State.addr p.output,bytes p⟩ := by
    apply Region.sub_prefix
    rw [bytes_eq]
    omega_using []
  apply WorkspaceEq.of_frame (by have := h.output.fits; rw [bytes_eq] at this; omega_using [this]) frame
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl
  · exact h.workspaceSeparate.symm.sub_left sub
  · rw [h.fixed]
    exact h.callSeparate.sub_left sub

theorem headEq_store {p : Inputs} {sp : BitVec 32} {s t : State} {digit : Nat}
    (h : Memory p sp s) (hd : digit < 32)
    (frame : Frame [⟨off (State.addr p.output) (entryOffset p digit),8*p.w⟩] s.mem t.mem) :
    WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem t.mem := by
  have bound := entry_bound p hd
  have order := Nat.mul_le_mul_left (8*p.w) (by omega_using [] : 2 ≤ digit+2)
  have sep : (⟨State.addr p.output,24+16*p.w⟩ : Region).Disjoint
      ⟨off (State.addr p.output) (entryOffset p digit),8*p.w⟩ := by
    apply Offset.base_disjoint
    · simp only [entryOffset]
      omega_using [order]
    · have := h.output.fits
      omega_using [bound, this]
  apply WorkspaceEq.of_frame (by have := h.output.fits; rw [bytes_eq] at this; omega_using [this]) frame
  intro r hr
  have eq := List.mem_singleton.mp hr
  subst r
  exact sep

end VG.Proof.Ffdh.Arm.CombBuilder

end

end

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
    omega_using [bound, hw, this]
  have address : State.addr (p.output + BitVec.ofNat 32 (CombBuilder.entryOffset p digit)) =
      off (State.addr p.output) (CombBuilder.entryOffset p digit) := addr_add small
  have address' : State.addr (p.output + BitVec.ofNat 32 (24+8*p.w*(digit+2))) =
      off (State.addr p.output) (CombBuilder.entryOffset p digit) := address
  have dstFit : (p.output + BitVec.ofNat 32 (CombBuilder.entryOffset p digit)).toNat + 8*p.w ≤ 2^32 := by
    simp only [BitVec.toNat_add,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega_using [small] : CombBuilder.entryOffset p digit < 2^32),Nat.mod_eq_of_lt small]
    have := h.output.fits
    omega_using [bound, this]
  have write := CallLay.inRegions_sub h.output.writable bound
    (by have := h.output.fits; omega_using [this] : CombBuilder.bytes p < 2^64)
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
