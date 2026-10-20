module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Controller
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Each attempt consumes exactly the public domain width from the entropy
tape, independent of its secret acceptance status. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

def advanceValues (m : Mem) (base : BitVec 32) : List (Nat × BitVec 32) :=
  [(9, lowWord m base 9 + lowWord m base 2),
    (10, lowWord m base 10 - lowWord m base 2),
    (11, lowWord m base 11 + lowWord m base 2)]

theorem advanceLoads_ok (s : State) {base : BitVec 32} (h : Controller base s) :
    WP isa (.block VG.Impl.Ffdh.Arm.KeySearch.advanceLoads) s fun t =>
      (t.gpr .r9 = s.gpr .r0 ∧ t.gpr .r10 = lowWord s.mem base 2 ∧
        t.gpr .r11 = lowWord s.mem base 9 ∧ t.gpr .r12 = lowWord s.mem base 10 ∧
        t.gpr .r3 = lowWord s.mem base 11 ∧ t.mem = s.mem) ∧ Rest [.r3, .r9, .r10, .r11, .r12] s t := by
  refine withRest [.r3, .r9, .r10, .r11, .r12] ?_ (by
    intro r hr i hi
    have checked : (instrs (.block VG.Impl.Ffdh.Arm.KeySearch.advanceLoads : Prog isa)).all
        (fun i => !(clobbers i r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have f := List.all_eq_true.mp checked i hi
    cases hc : clobbers i r <;> simp_all) (by rfl)
  unfold VG.Impl.Ffdh.Arm.KeySearch.advanceLoads VG.Impl.Ffdh.Arm.KeySearch.ldf lowWord
  ffrun [h.addr (by decide : 2 < 16), h.addr (by decide : 9 < 16), h.addr (by decide : 10 < 16), h.addr (by decide : 11 < 16),
    h.read (by decide : 2 < 16), h.read (by decide : 9 < 16), h.read (by decide : 10 < 16), h.read (by decide : 11 < 16)]

theorem advance_ok (s : State) {base : BitVec 32} (h : Controller base s) :
    WP isa (.block VG.Impl.Ffdh.Arm.KeySearch.advance) s fun t =>
      (t.gpr .r9 = s.gpr .r0 ∧ t.mem = writeLow s.mem base (advanceValues s.mem base)) ∧
      Rest [.r3, .r9, .r10, .r11, .r12] s t := by
  refine withRest [.r3, .r9, .r10, .r11, .r12] ?_ (by
    intro r hr i hi
    have checked : (instrs (.block VG.Impl.Ffdh.Arm.KeySearch.advance : Prog isa)).all
        (fun i => !(clobbers i r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have f := List.all_eq_true.mp checked i hi
    cases hc : clobbers i r <;> simp_all) (by rfl)
  rw [VG.Impl.Ffdh.Arm.KeySearch.advance, WP.block_append_iff]
  refine WP.mono (advanceLoads_ok s h) ?_
  rintro u ⟨⟨status, width, ptr, length, used, mem⟩, rest⟩
  have context : Controller base u := ⟨h.space.congr rest.wr, (rest.gpr .r4 (by simp)).trans h.ptr⟩
  unfold VG.Impl.Ffdh.Arm.KeySearch.advanceUpdate VG.Impl.Ffdh.Arm.KeySearch.stf writeLow advanceValues
  simp only [List.foldl_cons, List.foldl_nil]
  ffrun [status, width, ptr, length, used, mem,
    context.addr (by decide : 9 < 16), context.addr (by decide : 10 < 16), context.addr (by decide : 11 < 16),
    context.write (by decide : 9 < 16), context.write (by decide : 10 < 16), context.write (by decide : 11 < 16)]

def scalarValues (m : Mem) (base : BitVec 32) : List (Nat × BitVec 32) :=
  [(1, lowWord m base 1 - 1), (14, 4)]

def publicValues (m : Mem) (base : BitVec 32) : List (Nat × BitVec 32) :=
  [(0, lowWord m base 0 - 1), (1, 128), (14, 4)]

theorem rejectedScalar_ok (s : State) {base : BitVec 32} (h : Controller base s) :
    WP isa (.block VG.Impl.Ffdh.Arm.KeySearch.rejectedScalar) s fun t =>
      t.mem = writeLow s.mem base (scalarValues s.mem base) ∧ Rest [.r10, .r11] s t := by
  refine withRest [.r10, .r11] ?_ (by
    intro r hr i hi
    have checked : (instrs (.block VG.Impl.Ffdh.Arm.KeySearch.rejectedScalar : Prog isa)).all
        (fun i => !(clobbers i r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have f := List.all_eq_true.mp checked i hi
    cases hc : clobbers i r <;> simp_all) (by rfl)
  unfold VG.Impl.Ffdh.Arm.KeySearch.rejectedScalar VG.Impl.Ffdh.Arm.KeySearch.ldf VG.Impl.Ffdh.Arm.KeySearch.stf
    writeLow scalarValues lowWord
  simp only [List.foldl_cons, List.foldl_nil]
  ffrun [h.addr (by decide : 1 < 16), h.addr (by decide : 14 < 16), h.read (by decide : 1 < 16),
    h.write (by decide : 1 < 16), h.write (by decide : 14 < 16)]

theorem rejectedPublic_ok (s : State) {base : BitVec 32} (h : Controller base s) :
    WP isa (.block VG.Impl.Ffdh.Arm.KeySearch.rejectedPublic) s fun t =>
      t.mem = writeLow s.mem base (publicValues s.mem base) ∧ Rest [.r10, .r11, .r12] s t := by
  refine withRest [.r10, .r11, .r12] ?_ (by
    intro r hr i hi
    have checked : (instrs (.block VG.Impl.Ffdh.Arm.KeySearch.rejectedPublic : Prog isa)).all
        (fun i => !(clobbers i r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have f := List.all_eq_true.mp checked i hi
    cases hc : clobbers i r <;> simp_all) (by rfl)
  unfold VG.Impl.Ffdh.Arm.KeySearch.rejectedPublic VG.Impl.Ffdh.Arm.KeySearch.ldf VG.Impl.Ffdh.Arm.KeySearch.stf
    writeLow publicValues lowWord
  simp only [List.foldl_cons, List.foldl_nil]
  ffrun [h.addr (by decide : 0 < 16), h.addr (by decide : 1 < 16), h.addr (by decide : 14 < 16),
    h.read (by decide : 0 < 16), h.write (by decide : 0 < 16), h.write (by decide : 1 < 16), h.write (by decide : 14 < 16)]

end VG.Proof.Ffdh.Arm.KeySearch
