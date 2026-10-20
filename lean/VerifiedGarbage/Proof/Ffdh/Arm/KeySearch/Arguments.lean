module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.ArgumentContext
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.ArgumentBlocks

/-! Exact AAPCS arguments and stack-memory effects of the nested key attempt. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

def callMem (p : KeyPublic) (used : Nat) (m : Mem) (sp : BitVec 32) : Mem :=
  ((((((m.writeW (off (State.addr sp) 0) p.dp).writeW
    (off (State.addr sp) 4) (BitVec.ofNat 32 p.dlen)).writeW
    (off (State.addr sp) 8) (BitVec.ofNat 32 p.len)).writeW
    (off (State.addr sp) 12) (p.rp + BitVec.ofNat 32 used)).writeW
    (off (State.addr sp) 16) (BitVec.ofNat 32 p.len)).writeW
    (off (State.addr sp) 20) p.scratch).writeW
    (off (State.addr sp) 24) (BitVec.ofNat 32 p.capacity)

theorem arguments_ok (s : State) {p : KeyPublic} {used keys scalars : Nat}
    (h : Controller p.control s) (stack : Workspace s s.sp 32)
    (separate : (⟨State.addr p.control, 128⟩ : Region).Disjoint ⟨State.addr s.sp, 32⟩)
    (headers : Slots s.mem p.control (p.headers used keys scalars)) :
    WP isa (.block VG.Impl.Ffdh.Arm.KeySearch.arguments) s fun t =>
      (ArgumentContext p used keys scalars t ∧ t.mem = callMem p used s.mem s.sp) ∧
      Rest [.r0, .r1, .r2, .r3, .r9, .r12] s t := by
  refine withRest [.r0, .r1, .r2, .r3, .r9, .r12] ?_ (by
    intro r hr i hi
    have checked : (instrs (.block VG.Impl.Ffdh.Arm.KeySearch.arguments : Prog isa)).all
        (fun i => !(clobbers i r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have f := List.all_eq_true.mp checked i hi
    cases hc : clobbers i r <;> simp_all) (by rfl)
  change WP isa (.block ([VG.Impl.Ffdh.Arm.KeySearch.ldf .r0 5, VG.Impl.Ffdh.Arm.KeySearch.ldf .r1 2,
    VG.Impl.Ffdh.Arm.KeySearch.ldf .r2 6, VG.Impl.Ffdh.Arm.KeySearch.ldf .r3 2, .addSp .r12 0] ++ _)) s _
  rw [WP.block_append_iff]
  refine WP.mono (argumentHead_ok s h
    (headers (5, p.xp) (by simp [KeyPublic.headers])) (headers (6, p.yp) (by simp [KeyPublic.headers]))
    (headers (2, BitVec.ofNat 32 p.len) (by simp [KeyPublic.headers]))) ?_
  rintro u ⟨⟨x, xlen, y, ylen, ptr, mem⟩, rest⟩
  have context : ArgumentContext p used keys scalars u :=
    ⟨⟨h.space.congr rest.wr, (rest.gpr .r4 (by simp)).trans h.ptr⟩,
      by rw [rest.sp]; exact stack.congr rest.wr,
      by rw [rest.sp]; exact separate,
      by rw [mem]; exact headers,
      by rw [rest.sp]; exact ptr, x, xlen, y, ylen⟩
  refine wp_argumentCopy (j := 7) (d := 0) context (by decide) (by decide)
    (context.headers (7, p.dp) (by simp [KeyPublic.headers])) fun s1 c1 m1 r1 => ?_
  have sp1 := r1.sp.trans rest.sp
  refine wp_argumentCopy (j := 8) (d := 4) c1 (by decide) (by decide)
    (c1.headers (8, BitVec.ofNat 32 p.dlen) (by simp [KeyPublic.headers])) fun s2 c2 m2 r2 => ?_
  have sp2 := r2.sp.trans sp1
  refine wp_argumentStore (d := 8) c2 (by decide) fun s3 c3 m3 r3 => ?_
  have sp3 := r3.sp.trans sp2
  refine wp_argumentCopy (j := 9) (d := 12) c3 (by decide) (by decide)
    (c3.headers (9, p.rp + BitVec.ofNat 32 used) (by simp [KeyPublic.headers])) fun s4 c4 m4 r4 => ?_
  have sp4 := r4.sp.trans sp3
  refine wp_argumentStore (d := 16) c4 (by decide) fun s5 c5 m5 r5 => ?_
  have sp5 := r5.sp.trans sp4
  refine wp_argumentCopy (j := 12) (d := 20) c5 (by decide) (by decide)
    (c5.headers (12, p.scratch) (by simp [KeyPublic.headers])) fun s6 c6 m6 r6 => ?_
  have sp6 := r6.sp.trans sp5
  refine wp_argumentCopy (j := 13) (d := 24) c6 (by decide) (by decide)
    (c6.headers (13, BitVec.ofNat 32 p.capacity) (by simp [KeyPublic.headers])) fun s7 c7 m7 _ => ?_
  apply WP.block_nil
  refine ⟨c7, ?_⟩
  rw [m7, m6, m5, m4, m3, m2, m1, mem, sp6, sp5, sp4, sp3, sp2, sp1, rest.sp]
  rfl

theorem callMem_frame (p : KeyPublic) (used : Nat) (m : Mem) (sp : BitVec 32) :
    Frame [⟨State.addr sp, 32⟩] m (callMem p used m sp) := by
  unfold callMem
  exact (((((((Frame.refl _ _).writeW (by simp) _ (Offset.contains_base _ (by decide : 0 + 4 ≤ 32) (by decide))).writeW
    (by simp) _ (Offset.contains_base _ (by decide : 4 + 4 ≤ 32) (by decide))).writeW
    (by simp) _ (Offset.contains_base _ (by decide : 8 + 4 ≤ 32) (by decide))).writeW
    (by simp) _ (Offset.contains_base _ (by decide : 12 + 4 ≤ 32) (by decide))).writeW
    (by simp) _ (Offset.contains_base _ (by decide : 16 + 4 ≤ 32) (by decide))).writeW
    (by simp) _ (Offset.contains_base _ (by decide : 20 + 4 ≤ 32) (by decide))).writeW
    (by simp) _ (Offset.contains_base _ (by decide : 24 + 4 ≤ 32) (by decide))

end VG.Proof.Ffdh.Arm.KeySearch
