module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivFnInput
import VerifiedGarbage.Proof.Rsa.Arm.PrivRegions
import VerifiedGarbage.Proof.Bignum.Arm.LayoutPreserved
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions

/-! ### `Rsa.Arm.PrivEntryInput`, which only this module used -/

section

/-! # Native inputs before entering the wrapper's two stack frames -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont

structure PrivEntryInput (g : PrivGeometry) (bs : Fin 8 → List Byte) (s : State) : Prop where
  valid : g.Valid
  stackFit : stackBytes ≤ s.sp.toNat
  base : g.stack = s.sp - BitVec.ofNat 32 56 - BitVec.ofNat 32 frameBytes
  source : ∀ i, PublicBytes (g.sources i) (g.sourceLength i) (bs i) s
  outputWrite : InRegions s.wr (State.addr g.output) g.length
  workspaceWrite : InRegions s.wr (State.addr g.workspace) (8 * g.scratchLength)
  argumentsRead : InRegions (s.rd ++ s.wr) (State.addr s.sp) 64
  arguments : ∀ j < 16, s.mem.readW (off (State.addr s.sp) (4 * j)) 32 = g.argument j
  output : s.gpr .r0 = g.output
  modulus : s.gpr .r2 = g.sources 0
  count : s.gpr .r3 = BitVec.ofNat 32 g.length

theorem PrivEntryInput.enteredSp {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivEntryInput g bs s) : (entered s).sp = g.stack := h.base.symm

theorem PrivEntryInput.savedAddr {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivEntryInput g bs s) : State.addr (pcPushed s).sp = g.savedRegion.base := by
  have eq : (pcPushed s).sp = g.stack + BitVec.ofNat 32 frameBytes := by
    rw [h.base]; exact (BitVec.sub_add_cancel _ _).symm
  rw [eq, h.valid.offsetAddr (by simp only [frameBytes]; decide)]; rfl

theorem PrivEntryInput.argumentsAddr {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivEntryInput g bs s) : State.addr s.sp = g.argumentsRegion.base := by
  have eq : s.sp = g.stack + BitVec.ofNat 32 (frameBytes + 56) := by
    rw [h.base, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel, BitVec.sub_add_cancel]
  rw [eq, h.valid.offsetAddr (by simp only [frameBytes]; decide)]; rfl

theorem PrivEntryInput.enteredFrame {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivEntryInput g bs s) : Frame [g.savedRegion] s.mem (entered s).mem := by
  have f := FrameStack.pushed_frameA
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr])
    (s := s) (by change 56 ≤ s.sp.toNat; have := h.stackFit; simp only [stackBytes] at this; omega_using [this])
  change Frame [⟨State.addr (pcPushed s).sp, 56⟩] s.mem (entered s).mem at f
  rw [h.savedAddr] at f
  exact f

theorem entered_read {s : State} {p : Addr} {n : Nat} (read : InRegions (s.rd ++ s.wr) p n) :
    InRegions ((entered s).rd ++ (entered s).wr) p n := by
  obtain ⟨r, hr, hc⟩ := read
  refine ⟨r, ?_, hc⟩
  rcases List.mem_append.mp hr with hr | hr
  · exact List.mem_append_left _ hr
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))

theorem entered_write {s : State} {p : Addr} {n : Nat} (write : InRegions s.wr p n) :
    InRegions (entered s).wr p n := by
  obtain ⟨r, hr, hc⟩ := write
  exact ⟨r, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr), hc⟩
end VG.Proof.Rsa.Arm

end

end


/-! # Entering both frames preserves every input and incoming stack argument -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont

theorem PrivEntryInput.enteredSource {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivEntryInput g bs s) (i : Fin 8) :
    PublicBytes (g.sources i) (g.sourceLength i) (bs i) (entered s) := by
  refine ⟨(h.source i).fits, entered_read (h.source i).read, ?_⟩
  have sep : ∀ r ∈ [g.savedRegion], (g.sourceRegion i).Disjoint r := by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact ((h.valid.stackSources i).sub_left h.valid.savedSub).symm
  exact (rsa_bytes_frame h.enteredFrame (by have := (h.source i).fits; omega_using [this]) sep).trans (h.source i).bytes

theorem PrivEntryInput.enteredArguments {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivEntryInput g bs s) (j : Nat) (hj : j < 16) :
    (entered s).mem.readW (off (State.addr g.stack) (arg j)) 32 = g.argument j := by
  have sep : ∀ r ∈ [g.savedRegion], g.argumentsRegion.Disjoint r := by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact (h.valid.stackArguments.sub_left h.valid.savedSub).symm
  have eq := (WorkspaceEq.of_frame (base := g.argumentsRegion.base) (size := 64) (by decide) h.enteredFrame sep).word
    (d := 4 * j) (bits := 32) (by omega_using [hj])
  have address : off g.argumentsRegion.base (4 * j) = off (State.addr g.stack) (arg j) :=
    Offset.add_add _ (frameBytes + 56) (4 * j)
  rw [address] at eq
  rw [eq]
  have incoming := h.arguments j hj
  rw [h.argumentsAddr, address] at incoming
  exact incoming

theorem PrivEntryInput.ready {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivEntryInput g bs s) : PrivFnInput g bs s := by
  refine ⟨h.stackFit, ⟨h.valid, h.enteredSp, ?_, h.enteredSource,
    entered_write h.outputWrite, entered_write h.workspaceWrite, ?_, h.enteredArguments⟩,
    h.output, h.modulus, h.count⟩
  · refine ⟨by have := h.valid.stackHigh; omega_using [this], ?_⟩
    change (⟨State.addr g.stack, frameBytes⟩ : Region) ∈
      ⟨State.addr (entered s).sp, frameBytes⟩ :: (pcPushed s).wr
    rw [h.enteredSp]
    exact List.mem_cons_self
  · rw [← h.argumentsAddr]
    exact entered_read h.argumentsRead
end VG.Proof.Rsa.Arm
