module

public import VerifiedGarbage.Proof.Bignum.Arm.PcStack
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Saved arguments of the ten-argument ARMv7 public RSA entry point

The 56-byte frame is followed by six incoming stack arguments. Slot 48
is caller-clobbered storage for the secret input-acceptance bit.
-/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure PublicStack (base dst np ep xp : BitVec 32) (len k eLen : Nat) (s : State) : Prop where
  nowrap : s.sp.toNat + 80 ≤ 2 ^ 32
  frameWritable : (⟨State.addr s.sp, 56⟩ : Region) ∈ s.wr
  argumentsRead : InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 56) 24
  separate : Region.Disjoint ⟨State.addr s.sp, 80⟩ ⟨State.addr base, 8 * len⟩
  savedBase : s.mem.readW (State.addr s.sp) 32 = base
  savedOutput : s.mem.readW (off (State.addr s.sp) 4) 32 = dst
  savedModulus : s.mem.readW (off (State.addr s.sp) 8) 32 = np
  savedCount : s.mem.readW (off (State.addr s.sp) 12) 32 = BitVec.ofNat 32 k
  exponent : s.mem.readW (off (State.addr s.sp) 56) 32 = ep
  exponentCount : s.mem.readW (off (State.addr s.sp) 60) 32 = BitVec.ofNat 32 eLen
  input : s.mem.readW (off (State.addr s.sp) 64) 32 = xp

theorem PublicStack.read {s : State} {base dst np ep xp : BitVec 32} {len k eLen d : Nat}
    (h : PublicStack base dst np ep xp len k eLen s) (fit : d + 4 ≤ 80)
    (aligned : d + 4 ≤ 56 ∨ 56 ≤ d) : InRegions (s.rd ++ s.wr) (off (State.addr s.sp) d) 4 := by
  rcases aligned with low | high
  · exact ⟨_, List.mem_append_right _ h.frameWritable, Offset.contains_base _ low (by omega)⟩
  · have read := CallLay.inRegions_sub h.argumentsRead (off := d - 56) (l := 4) (by omega) (by decide)
    have addr : off (State.addr s.sp) 56 + BitVec.ofNat 64 (d - 56) = off (State.addr s.sp) d := by
      change State.addr s.sp + BitVec.ofNat 64 56 + BitVec.ofNat 64 (d - 56) = _
      rw [Offset.add_add, show 56 + (d - 56) = d by omega]
    rw [addr] at read
    exact read

theorem PublicStack.pcStack {s : State} {base dst np ep xp : BitVec 32} {len k eLen : Nat}
    (h : PublicStack base dst np ep xp len k eLen s) : PcStack base dst np len k s :=
  ⟨by have := h.nowrap; omega,
    ⟨_, List.mem_append_right _ h.frameWritable, by simp [Region.Contains]⟩,
    h.separate.sub_left (Region.sub_prefix (by decide)), h.savedBase, h.savedOutput, h.savedModulus, h.savedCount⟩

theorem PublicStack.after_workspace {s t : State} {base dst np ep xp : BitVec 32} {len k eLen : Nat} {rs : List Reg}
    (h : PublicStack base dst np ep xp len k eLen s)
    (frame : Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem) (rest : Rest rs s t) :
    PublicStack base dst np ep xp len k eLen t := by
  have eq : WorkspaceEq (State.addr s.sp) 80 s.mem t.mem := WorkspaceEq.of_frame (by decide) frame
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.separate)
  refine ⟨by rw [rest.sp]; exact h.nowrap, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rest.wr, rest.sp]; exact h.frameWritable
  · rw [rest.rd, rest.wr, rest.sp]; exact h.argumentsRead
  · rw [rest.sp]; exact h.separate
  · rw [rest.sp]
    have word := eq.word (d := 0) (bits := 32) (by decide)
    simp only [off, BitVec.add_zero] at word
    exact word.trans h.savedBase
  · rw [rest.sp, eq.word (d := 4) (bits := 32) (by decide)]; exact h.savedOutput
  · rw [rest.sp, eq.word (d := 8) (bits := 32) (by decide)]; exact h.savedModulus
  · rw [rest.sp, eq.word (d := 12) (bits := 32) (by decide)]; exact h.savedCount
  · rw [rest.sp, eq.word (d := 56) (bits := 32) (by decide)]; exact h.exponent
  · rw [rest.sp, eq.word (d := 60) (bits := 32) (by decide)]; exact h.exponentCount
  · rw [rest.sp, eq.word (d := 64) (bits := 32) (by decide)]; exact h.input

theorem PublicStack.after_acceptance {s t : State} {base dst np ep xp : BitVec 32} {len k eLen : Nat}
    {rs : List Reg} {value : BitVec 32} (h : PublicStack base dst np ep xp len k eLen s)
    (mem : t.mem = s.mem.writeW (off (State.addr s.sp) 48) value) (rest : Rest rs s t) :
    PublicStack base dst np ep xp len k eLen t := by
  have outside := writeW32_outside s.mem (State.addr s.sp) (d := 48) value (by decide)
  rw [← mem] at outside
  refine ⟨by rw [rest.sp]; exact h.nowrap, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rest.wr, rest.sp]; exact h.frameWritable
  · rw [rest.rd, rest.wr, rest.sp]; exact h.argumentsRead
  · rw [rest.sp]; exact h.separate
  · rw [rest.sp]
    have keep := outside_read32 outside (d := 0) (by decide) (by decide)
    simp only [off, BitVec.add_zero] at keep
    exact keep.trans h.savedBase
  · rw [rest.sp, outside_read32 outside (d := 4) (by decide) (by decide)]; exact h.savedOutput
  · rw [rest.sp, outside_read32 outside (d := 8) (by decide) (by decide)]; exact h.savedModulus
  · rw [rest.sp, outside_read32 outside (d := 12) (by decide) (by decide)]; exact h.savedCount
  · rw [rest.sp, outside_read32 outside (d := 56) (by decide) (by decide)]; exact h.exponent
  · rw [rest.sp, outside_read32 outside (d := 60) (by decide) (by decide)]; exact h.exponentCount
  · rw [rest.sp, outside_read32 outside (d := 64) (by decide) (by decide)]; exact h.input

end VG.Proof.Bignum.Arm
