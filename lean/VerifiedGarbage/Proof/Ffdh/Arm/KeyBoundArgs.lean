module

public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Ffdh.Arm.KeyGeometry
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Ffdh.Arm.QTest
public import VerifiedGarbage.Proof.Ffdh.Arm.Context

/-! Select the public bound and its full encoded length from native saved arguments. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem keyBoundSelect_ok (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h60 : 60 ∈ slots) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.withQ (.block [.ldrSp .r4 60]) (.block [.ldrSp .r4 24])) s fun t =>
      (t.gpr .r4 = p.boundSource ∧ t.mem = s.mem) ∧ Rest [.r3, .r4] s t := by
  refine withRest_all [.r3, .r4] ?_ (by rfl) (by rfl)
  rw [VG.Impl.Ffdh.Arm.Domain.withQ, WP.seq_iff]
  refine WP.mono (qTest_ok s h h28 h32) ?_
  rintro u ⟨⟨zero, memU⟩, restU⟩
  have contextU := h.of_mem memU restU ((restU.gpr .r0 (by simp)).trans h.ptr)
  refine WP.ite p.hasQ (by simp only [eval, zero, Bool.not_not]) ?_ ?_
  · intro hasQ
    refine WP.mono (localLoad_ok u .r4 contextU.locals (d := 60) (by decide)) ?_
    rintro t ⟨value, memT, _⟩
    rw [contextU.saved 60 h60] at value
    exact ⟨by rw [Inputs.boundSource, ite_eq_left hasQ]; exact value, memT.trans memU⟩
  · intro hasQ
    refine WP.mono (localLoad_ok u .r4 contextU.locals (d := 24) (by decide)) ?_
    rintro t ⟨value, memT, _⟩
    rw [contextU.saved 24 h24] at value
    exact ⟨by rw [Inputs.boundSource, ite_eq_right (by rw [hasQ]; decide)]; exact value, memT.trans memU⟩

theorem keyBoundArgs_ok (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h60 : 60 ∈ slots) :
    WP isa VG.Impl.Ffdh.Arm.Domain.GenerateKey.boundArgs s fun t =>
      (t.gpr .r4 = p.boundSource ∧ t.gpr .r6 = BitVec.ofNat 32 p.k ∧ t.mem = s.mem) ∧ Rest [.r3, .r4, .r6] s t := by
  refine withRest_all [.r3, .r4, .r6] ?_ (by rfl) (by rfl)
  rw [VG.Impl.Ffdh.Arm.Domain.GenerateKey.boundArgs, WP.seq_iff]
  refine WP.mono (keyBoundSelect_ok s h h24 h28 h32 h60) ?_
  rintro u ⟨⟨ptr, memU⟩, restU⟩
  have contextU := h.of_mem memU restU ((restU.gpr .r0 (by simp)).trans h.ptr)
  refine WP.mono (localLoad_ok u .r6 contextU.locals (d := 32) (by decide)) ?_
  rintro t ⟨count, memT, restT⟩
  rw [contextU.saved 32 h32] at count
  exact ⟨(restT.gpr .r4 (by simp)).trans ptr, count, memT.trans memU⟩

end VG.Proof.Ffdh.Arm
