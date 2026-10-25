module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.ArgumentContext
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Controller
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Load the candidate's first four AAPCS arguments and locate its stack arguments. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont VG.Proof.Ffdh.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Controller lowWord)
open VG.Proof.X25519.Arm (Rest)

theorem argumentHead_ok (s : State) {p : SearchParams} {used : Nat}
    (h : Controller p.control s) (stack : Workspace s s.sp 24)
    (separate : (⟨State.addr p.control, 128⟩ : Region).Disjoint ⟨State.addr s.sp, 24⟩)
    (headers : ∀ j ∈ searchSlots, lowWord s.mem p.control j = searchValues p used j) :
    WP isa (.block [VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r0 5, VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r1 1,
      .dp .add .r2 .r4 (.imm 112), VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r3 7, .addSp .r12 0]) s fun t =>
      (ArgumentContext p used t ∧ t.mem = s.mem) ∧ Rest [.r0, .r1, .r2, .r3, .r12] s t := by
  have raw : WP isa (.block [VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r0 5, VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r1 1,
      .dp .add .r2 .r4 (.imm 112), VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r3 7, .addSp .r12 0]) s fun t =>
      (t.gpr .r0 = p.c.out ∧ t.gpr .r1 = BitVec.ofNat 32 p.c.length ∧
        t.gpr .r2 = p.control + 112#32 ∧ t.gpr .r3 = BitVec.ofNat 32 p.c.bits ∧
        t.gpr .r12 = s.sp ∧ t.mem = s.mem) ∧ Rest [.r0, .r1, .r2, .r3, .r12] s t := by
    refine withRest_all [.r0, .r1, .r2, .r3, .r12] ?_ (by rfl) (by rfl)
    have out := headers 5 (by simp [searchSlots])
    have width := headers 1 (by simp [searchSlots])
    have bits := headers 7 (by simp [searchSlots])
    unfold VG.Impl.Ffdh.Arm.ParameterSearch.ldf
    unfold lowWord searchValues at out width bits
    have addr40 := controllerAddr h 40 (by decide)
    have addr8 := controllerAddr h 8 (by decide)
    have addr56 := controllerAddr h 56 (by decide)
    rw [h.ptr] at addr40 addr8 addr56
    ffrun [addr40, addr8, addr56,
      h.space.read (off := 40) (by decide), h.space.read (off := 8) (by decide), h.space.read (off := 56) (by decide),
      out, width, bits, h.ptr, BitVec.add_zero]
    rfl
  refine WP.mono raw ?_
  rintro t ⟨⟨out, width, up, bits, pointer, mem⟩, rest⟩
  have context : ArgumentContext p used t := ⟨⟨h.space.congr rest.wr, (rest.gpr .r4 (by simp)).trans h.ptr⟩,
    by rw [rest.sp]; exact stack.congr rest.wr,
    by rw [rest.sp]; exact separate, by rw [mem]; exact headers,
    by rw [rest.sp]; exact pointer, out, width, up, bits⟩
  exact ⟨⟨context, mem⟩, rest⟩

end VG.Proof.Ffdh.Arm.ParameterSearch
