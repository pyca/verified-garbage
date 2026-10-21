module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Controller
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Compare
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Compare two public native controller fields without changing memory. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Ffdh.Arm VG.Proof.X25519.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Controller lowWord)

theorem fieldLoads_ok (s : State) {base : BitVec 32} {i j : Nat}
    (h : Controller base s) (hi : i < 16) (hj : j < 16) :
    WP isa (.block [VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r9 i,
      VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r10 j]) s fun t =>
      (t.gpr .r9 = lowWord s.mem base i ∧ t.gpr .r10 = lowWord s.mem base j ∧ t.mem = s.mem) ∧
        Rest [.r9, .r10] s t := by
  refine withRest [.r9, .r10] ?_ (by
    intro r hr op hop
    have checked : (instrs (.block [VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r9 i,
        VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r10 j] : Prog isa)).all
        (fun op => !(clobbers op r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have f := List.all_eq_true.mp checked op hop
    cases hc : clobbers op r <;> simp_all) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.ldf lowWord
  ffrun [show 8 * i < 4096 by omega, show 8 * j < 4096 by omega,
    h.addr hi, h.addr hj, h.read hi, h.read hj]

theorem fieldGuard_ok (s : State) {base : BitVec 32} {i j x y : Nat}
    (h : Controller base s) (hi : i < 16) (hj : j < 16)
    (xFits : x < 2 ^ 32) (yFits : y < 2 ^ 32)
    (left : lowWord s.mem base i = BitVec.ofNat 32 x)
    (right : lowWord s.mem base j = BitVec.ofNat 32 y) :
    WP isa (.block ([VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r9 i,
      VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r10 j] ++ VG.Impl.Ffdh.Arm.ParameterSearch.less)) s fun t =>
      (t.z = decide (x < y) ∧ t.mem = s.mem) ∧ Rest [.r9, .r10, .r11] s t := by
  rw [WP.block_append_iff]
  refine WP.mono (fieldLoads_ok s h hi hj) ?_
  rintro u ⟨⟨loadX, loadY, memU⟩, restU⟩
  refine WP.mono (less_ok u) ?_
  rintro t ⟨⟨flag, memT⟩, restT⟩
  rw [loadX, loadY, left, right, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt xFits, Nat.mod_eq_of_lt yFits] at flag
  exact ⟨⟨flag, memT.trans memU⟩, (restU.mono (by simp)).trans (restT.mono (by simp))⟩

end VG.Proof.Ffdh.Arm.ParameterSearch
