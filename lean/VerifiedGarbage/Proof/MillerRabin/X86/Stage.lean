module

public import VerifiedGarbage.Proof.MillerRabin.X86.ProtectedContext
public import VerifiedGarbage.Proof.MillerRabin.X86.WorkingGeometry
public import VerifiedGarbage.Proof.Mont.X86.OutsZ
import VerifiedGarbage.Proof.Framework.Offset

/-! # A shared framing invariant for the i686 primality round's stages

The modulus, inverse, exponent and Montgomery constants stay readable from
the initial snapshot. The loop may write its declared workspace ranges,
the public table cursor and the existing multiplication's call frame.
Saved registers and protected-byte backups remain unchanged.
-/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86

def stageAreas (base : Addr) (w : Nat) (sp : BitVec 32) : List Region :=
  (workingRanges w).map (fun r => ⟨off base r.1, r.2⟩) ++
    [⟨off (byteAddr sp) VG.Impl.MillerRabin.X86.tableCursor, 4⟩, below sp 40]

structure Stage (base : Addr) (bytes w : Nat) (σ s : State) : Prop where
  context : ProtectedContext s base bytes
  stack : s.gpr .esp = σ.gpr .esp
  room : CallRoom (s.gpr .esp) base bytes
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  changed : Frame (stageAreas base w (σ.gpr .esp)) σ.mem s.mem

namespace Stage

theorem initial {σ : State} {base : Addr} {bytes w : Nat}
    (ctx : ProtectedContext σ base bytes) (R : CallRoom (σ.gpr .esp) base bytes) :
    Stage base bytes w σ σ := ⟨ctx, rfl, R, rfl, rfl, Frame.refl _ _⟩

theorem after {σ s t : State} {base : Addr} {bytes w : Nat} {rs : List Reg}
    (h : Stage base bytes w σ s) (K : Keeps rs s t)
    (F : Frame (stageAreas base w (σ.gpr .esp)) s.mem t.mem)
    (di : .edi ∉ rs := by decide) (esp : .esp ∉ rs := by decide) : Stage base bytes w σ t := by
  have sp := K.1 .esp esp
  exact ⟨h.context.of_keeps K di esp, sp.trans h.stack, by rw [sp]; exact h.room, K.2.1.trans h.rd, K.2.2.trans h.wr, h.changed.trans F⟩

theorem of_registers {σ s t : State} {base : Addr} {bytes w : Nat} {rs : List Reg}
    (h : Stage base bytes w σ s) (K : Keeps rs s t) (mem : t.mem = s.mem)
    (di : .edi ∉ rs := by decide) (esp : .esp ∉ rs := by decide) : Stage base bytes w σ t :=
  h.after K (mem ▸ Frame.refl _ _) di esp

theorem read_workspace {σ s : State} {base : Addr} {bytes w d n : Nat}
    (h : Stage base bytes w σ s) (hf : VG.Spec.Rsa.Mont.arrAt w 28 ≤ bytes)
    (hd : d + n ≤ bytes) (static : StaticRange w d n) :
    s.mem.read (off base d) n = σ.mem.read (off base d) n := by
  have nw := h.context.ws.nowrap
  refine h.changed.read (r := ⟨off base d, n⟩) (Region.contains_self _ _) ?_ (by omega)
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    have bound := working_bounds w p hp
    exact Offset.disjoint _ (static p hp) (by omega) (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have sub : Region.Sub ⟨off (byteAddr (s.gpr .esp)) VG.Impl.MillerRabin.X86.tableCursor, 4⟩
          ⟨byteAddr (s.gpr .esp), VG.Impl.MillerRabin.X86.frameBytes⟩ :=
        Offset.sub_base _ (by decide)
      simpa only [h.stack] using
        (h.context.apart.sub_left (Offset.sub_base _ hd)).sub_right sub
    · simpa only [h.stack] using h.room.apart.symm.sub_left (Offset.sub_base _ hd)

theorem read_workspace32 {σ s : State} {base : Addr} {bytes w d : Nat}
    (h : Stage base bytes w σ s) (hf : VG.Spec.Rsa.Mont.arrAt w 28 ≤ bytes)
    (hd : d + 4 ≤ bytes) (static : StaticRange w d 4) :
    s.mem.readW (off base d) 32 = σ.mem.readW (off base d) 32 := by
  simpa only [Mem.readW] using congrArg (BitVec.setWidth 32) (h.read_workspace hf hd static)

theorem read_stack {σ s : State} {base : Addr} {bytes w d n : Nat}
    (h : Stage base bytes w σ s) (hf : VG.Spec.Rsa.Mont.arrAt w 28 ≤ bytes)
    (hd : d + n ≤ VG.Impl.MillerRabin.X86.frameBytes)
    (cursor : d + n ≤ VG.Impl.MillerRabin.X86.tableCursor ∨ VG.Impl.MillerRabin.X86.tableCursor + 4 ≤ d) :
    s.mem.read (off (byteAddr (σ.gpr .esp)) d) n = σ.mem.read (off (byteAddr (σ.gpr .esp)) d) n := by
  have nw := h.context.ws.nowrap
  refine h.changed.read (r := ⟨off (byteAddr (σ.gpr .esp)) d, n⟩) (Region.contains_self _ _) ?_
    (by simp only [VG.Impl.MillerRabin.X86.frameBytes] at hd; omega)
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    have bound := Nat.le_trans (working_bounds w p hp) hf
    simpa only [h.stack] using
      (h.context.apart.symm.sub_left (Offset.sub_base _ hd)).sub_right (Offset.sub_base _ bound)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint _ cursor
        (by simp only [VG.Impl.MillerRabin.X86.frameBytes] at hd; omega) (by decide)
    · have low : 40 ≤ (σ.gpr .esp).toNat := by rw [← h.stack]; exact h.room.low
      change Region.Disjoint ⟨off ((σ.gpr .esp).setWidth 64) d, n⟩
        ⟨(σ.gpr .esp - BitVec.ofNat 32 40).setWidth 64, 40⟩
      rw [Taint.sub_setWidth low]
      exact Offset.disjoint_below _
        (by simp only [VG.Impl.MillerRabin.X86.frameBytes] at hd; omega)

end Stage
end VG.Proof.MillerRabin.X86
