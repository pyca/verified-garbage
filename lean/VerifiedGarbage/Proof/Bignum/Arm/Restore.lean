module

public import VerifiedGarbage.Impl.Bignum.Arm.MontFn
public import VerifiedGarbage.Proof.Bignum.Arm.Stack
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! # Restore the saved registers before the frame pops its first word -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem mont_restore_ok (s : State) (g : Reg → BitVec 32)
    (fit : s.sp.toNat + 36 ≤ 2 ^ 32) (frame : (⟨State.addr s.sp, 36⟩ : Region) ∈ s.wr)
    (saved : Spill.Saved s.mem (State.addr s.sp) g montSaved) :
    WP isa (.block MontFn.restore) s fun t =>
      (∀ r ∈ [.r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr], t.gpr r = g r) ∧
      t.mem = s.mem ∧ Rest roundClobbers s t := by
  have read (t : State) (wr : t.wr = s.wr) (d : Nat) (hd : d + 4 ≤ 36) :
      InRegions (t.rd ++ t.wr) (off (State.addr s.sp) d) 4 := by
    refine ⟨⟨State.addr s.sp, 36⟩, List.mem_append_right _ ?_, Offset.contains_base _ hd (by omega)⟩
    rw [wr]; exact frame
  unfold MontFn.restore
  refine wp_loadStack (a := off (State.addr s.sp) 4) (by decide) ?_ (read s rfl 4 (by decide)) fun s1 u1 => ?_
  · exact addr_add (by omega)
  have sp1 := u1.sp
  have wr1 := u1.wr
  refine wp_loadStack (a := off (State.addr s.sp) 8) (by decide) ?_ (read s1 wr1 8 (by decide)) fun s2 u2 => ?_
  · rw [sp1]; exact addr_add (by omega)
  have sp2 := u2.sp.trans sp1
  have wr2 := u2.wr.trans wr1
  refine wp_loadStack (a := off (State.addr s.sp) 12) (by decide) ?_ (read s2 wr2 12 (by decide)) fun s3 u3 => ?_
  · rw [sp2]; exact addr_add (by omega)
  have sp3 := u3.sp.trans sp2
  have wr3 := u3.wr.trans wr2
  refine wp_loadStack (a := off (State.addr s.sp) 16) (by decide) ?_ (read s3 wr3 16 (by decide)) fun s4 u4 => ?_
  · rw [sp3]; exact addr_add (by omega)
  have sp4 := u4.sp.trans sp3
  have wr4 := u4.wr.trans wr3
  refine wp_loadStack (a := off (State.addr s.sp) 20) (by decide) ?_ (read s4 wr4 20 (by decide)) fun s5 u5 => ?_
  · rw [sp4]; exact addr_add (by omega)
  have sp5 := u5.sp.trans sp4
  have wr5 := u5.wr.trans wr4
  refine wp_loadStack (a := off (State.addr s.sp) 24) (by decide) ?_ (read s5 wr5 24 (by decide)) fun s6 u6 => ?_
  · rw [sp5]; exact addr_add (by omega)
  have sp6 := u6.sp.trans sp5
  have wr6 := u6.wr.trans wr5
  refine wp_loadStack (a := off (State.addr s.sp) 28) (by decide) ?_ (read s6 wr6 28 (by decide)) fun s7 u7 => ?_
  · rw [sp6]; exact addr_add (by omega)
  have sp7 := u7.sp.trans sp6
  have wr7 := u7.wr.trans wr6
  refine wp_loadStack (a := off (State.addr s.sp) 32) (by decide) ?_ (read s7 wr7 32 (by decide)) fun s8 u8 => WP.block_nil ?_
  · rw [sp7]; exact addr_add (by omega)
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [u8.other .r5 (by decide), u7.other .r5 (by decide), u6.other .r5 (by decide), u5.other .r5 (by decide), u4.other .r5 (by decide), u3.other .r5 (by decide), u2.other .r5 (by decide), u1.gpr]
      exact saved (.r5, 4) (by decide)
    · rw [u8.other .r6 (by decide), u7.other .r6 (by decide), u6.other .r6 (by decide), u5.other .r6 (by decide), u4.other .r6 (by decide), u3.other .r6 (by decide), u2.gpr, u1.mem]
      exact saved (.r6, 8) (by decide)
    · rw [u8.other .r7 (by decide), u7.other .r7 (by decide), u6.other .r7 (by decide), u5.other .r7 (by decide), u4.other .r7 (by decide), u3.gpr, u2.mem, u1.mem]
      exact saved (.r7, 12) (by decide)
    · rw [u8.other .r8 (by decide), u7.other .r8 (by decide), u6.other .r8 (by decide), u5.other .r8 (by decide), u4.gpr, u3.mem, u2.mem, u1.mem]
      exact saved (.r8, 16) (by decide)
    · rw [u8.other .r9 (by decide), u7.other .r9 (by decide), u6.other .r9 (by decide), u5.gpr, u4.mem, u3.mem, u2.mem, u1.mem]
      exact saved (.r9, 20) (by decide)
    · rw [u8.other .r10 (by decide), u7.other .r10 (by decide), u6.gpr, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
      exact saved (.r10, 24) (by decide)
    · rw [u8.other .r11 (by decide), u7.gpr, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
      exact saved (.r11, 28) (by decide)
    · rw [u8.gpr, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
      exact saved (.lr, 32) (by decide)
  · rw [u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans ((u6.rest (by decide)).trans ((u7.rest (by decide)).trans ((u8.rest (by decide)))))))))

end VG.Proof.Bignum.Arm
