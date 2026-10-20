module

public import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-!
# A call with its working space pushed, on ARMv7

A core that takes its working space as a stack argument is called in a frame
that pushes it (`push {r12, lr}`, with its address in `r12`, at `[sp]` on
entry to the callee), as the streaming RC2 functions call theirs
(`Proof/Rc2/Arm/Stream/Common.lean`): the state the callee runs from
(`view`), its stack argument (`arg0`), and the regions it is given, which
the frame's push covers (`cov`).
-/

@[expose] public section

namespace VG.Proof.Modes.Arm.Push

open VG VG.Arm VG.Arm.FrameStack

theorem storeWords_two (m : Mem) (a : BitVec 32) (x y : BitVec 32) :
    storeWords m a [x, y] = (m.writeW (State.addr a) x).writeW (State.addr (a + 4)) y := rfl

/-- The callee's stack argument. -/
abbrev argR (s : State) : Region := ⟨State.addr s.sp - 8, 4⟩

/-- The state the callee runs from, with the permissions it is given. -/
abbrev view (s : State) (rd wr : List Region) : State :=
  (pushed [.r12, .lr] s).callEntry.withRegions rd wr

theorem e8 : BitVec.ofNat 32 (4 * [Reg.r12, Reg.lr].length) = 8 := rfl

section
variable {s : State} (hsp : 8 ≤ s.sp.toNat)
include hsp

theorem hA : State.addr (s.sp - 8) = State.addr s.sp - 8 := addr_sub' (k := 8) hsp

theorem hA4 : State.addr (s.sp - 8 + BitVec.ofNat 32 4) = State.addr s.sp - 8 + 4 := by
  have := s.sp.isLt
  have e : (s.sp - 8).toNat = s.sp.toNat - 8 := BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hsp)
  rw [addr_add (by rw [e]; omega), hA hsp]; rfl

theorem amem : (pushed [.r12, .lr] s).mem =
    (s.mem.writeW (State.addr s.sp - 8) (s.gpr .r12)).writeW (State.addr s.sp - 8 + 4) (s.gpr .lr) := by
  show storeWords s.mem (s.sp - BitVec.ofNat 32 (4 * [Reg.r12, Reg.lr].length)) [s.gpr .r12, s.gpr .lr] = _
  rw [e8, storeWords_two, hA hsp, show (s.sp - 8 + 4 : BitVec 32) = s.sp - 8 + BitVec.ofNat 32 4 from rfl,
    hA4 hsp]

theorem sa0 (rd wr : List Region) : stackArgAddr (view s rd wr) 0 = State.addr s.sp - 8 := by
  unfold stackArgAddr
  simp only [State.withRegions_sp, State.callEntry_sp, pushed_sp, e8]
  rw [show s.sp - 8 + BitVec.ofNat 32 (4 * 0) = s.sp - 8 from BitVec.add_zero _, hA hsp]

theorem arg0 (rd wr : List Region) : stackArg (view s rd wr) 0 = s.gpr .r12 := by
  rw [stackArg, sa0 hsp, State.withRegions_mem, State.callEntry_mem, amem hsp, Mem.readW_writeW_sep
    (Offset.sep_base (State.addr s.sp - 8) (n := 4) (e := 4) (k := 4) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_self32]

theorem view_sp (rd wr : List Region) : (view s rd wr).sp.toNat = s.sp.toNat - 8 := by
  simp only [State.withRegions_sp, State.callEntry_sp, pushed_sp, e8]
  exact BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hsp)

theorem view_addr (rd wr : List Region) : State.addr (view s rd wr).sp = State.addr s.sp - 8 := by
  simp only [State.withRegions_sp, State.callEntry_sp, pushed_sp, e8]; exact hA hsp

/-- The push changes memory only in the 8 bytes below the stack pointer. -/
theorem fA : Frame [belowA s.sp 8] s.mem (pushed [.r12, .lr] s).mem := pushed_frameA (rs := [.r12, .lr]) hsp

/-- The callee's regions, which the frame covers with `s`'s. -/
theorem cov {rd wr : List Region} (hr : Covers rd (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    Covers (rd ++ argR s :: wr) ((pushed [.r12, .lr] s).rd ++ (pushed [.r12, .lr] s).wr) := by
  intro x n' ⟨r, hr', hc⟩
  rcases List.mem_append.mp hr' with h' | h'
  · obtain ⟨r', hr'', hc'⟩ := hr x n' ⟨r, h', hc⟩
    refine ⟨r', ?_, hc'⟩
    rcases List.mem_append.mp hr'' with h'' | h''
    · exact List.mem_append_left _ h''
    · exact List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_of_mem _ h'')
  · rcases List.mem_cons.mp h' with rfl | h'
    · have eb : (⟨State.addr (s.sp - BitVec.ofNat 32 (4 * [Reg.r12, Reg.lr].length)),
          4 * [Reg.r12, Reg.lr].length⟩ : Region) = ⟨State.addr s.sp - 8, 8⟩ := by rw [e8, hA hsp]; rfl
      refine ⟨⟨State.addr s.sp - 8, 8⟩, List.mem_append_right _ (by rw [pushed_wr, eb]; exact List.mem_cons_self ..),
        ?_⟩
      simp only [Region.Contains] at hc ⊢; omega
    · obtain ⟨r', hr'', hc'⟩ := hw x n' ⟨r, h', hc⟩
      exact ⟨r', List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr''), hc'⟩

end

theorem covW {s : State} {wr : List Region} (hw : Covers wr s.wr) : Covers wr (pushed [.r12, .lr] s).wr := by
  intro x n' hi
  obtain ⟨r', hr', hc'⟩ := hw x n' hi
  exact ⟨r', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩

theorem view_gpr (s : State) (rd wr : List Region) (r : Reg) (hr : r ∉ linkRegs) :
    (view s rd wr).gpr r = s.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr]

theorem view_mem (s : State) (rd wr : List Region) : (view s rd wr).mem = (pushed [.r12, .lr] s).mem := by
  rw [State.withRegions_mem, State.callEntry_mem]

end VG.Proof.Modes.Arm.Push
