module

public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
import VerifiedGarbage.Proof.Ffdh.Arm.Subgroup
import VerifiedGarbage.Proof.Ffdh.Arm.QTest
import VerifiedGarbage.Proof.Ffdh.Arm.Branch
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack

/-! The optional subgroup check of an imported public value. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)

 def publicTailFlag (p : Inputs) (y : Nat) : BitVec 32 :=
  if p.hasQ = true then (if Spec.Rsa.powMod y p.Q p.P = 1 then 1 else 0) else 1

theorem checkPublicTail_ok (s : State) {p : Inputs} {slots : List Nat} {yb : List Byte}
    (h : Context p slots s) (stable : stableSlots slots = true)
    (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h60 : 60 ∈ slots)
    (ready : ArithmeticReady p.base p.len p.w s)
    (modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P) (odd : p.P % 2 = 1)
    (r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P)
    (value : Octets p.base p.publicValue p.len yb s) (length : yb.length = p.k) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.withQ
      (.seq (VG.Impl.Ffdh.Arm.Domain.subgroup 36) VG.Impl.Ffdh.Arm.Domain.finishFlag)
      (VG.Impl.Ffdh.Arm.Domain.ret 1)) s fun t =>
        t.gpr .r0 = publicTailFlag p (Spec.Rsa.os2ip yb) ∧ Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem t.mem := by
  rw [VG.Impl.Ffdh.Arm.Domain.withQ, WP.seq_iff]
  refine WP.mono (qTest_ok s h h28 h32) ?_
  rintro u ⟨⟨zero, memU⟩, restU⟩
  have frameU : Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem u.mem := by rw [memU]; exact Frame.refl _ _
  have ptrU := (restU.gpr .r0 (by simp)).trans ready.ptr
  have readyU := ready.of_mem memU restU ptrU
  have contextU := h.after_workspace frameU restU ptrU (fun d hd => (stableSlots_at stable hd).1)
  have valueU := value.after_workspace frameU restU
  refine WP.ite p.hasQ (by simp only [eval, zero, Bool.not_not]) ?_ ?_
  · intro hasQ
    rw [WP.seq_iff]
    refine WP.mono (subgroup_ok u 36 contextU stable h36 h60 h32 hasQ readyU
      (by rw [memU]; exact modulus) odd (by rw [memU]; exact r2) valueU length) ?_
    rintro v ⟨_, _, flag, _, _, frameV, _⟩
    refine WP.mono (finishFlag_ok v) ?_
    rintro t ⟨⟨result, memT⟩, _⟩
    refine ⟨?_, ?_⟩
    · rw [result, flag]
      exact (ite_eq_left hasQ).symm
    · rw [memT]; exact frameU.trans frameV
  · intro hasQ
    refine WP.mono (ret_ok u 1 (by decide)) ?_
    rintro t ⟨⟨result, memT⟩, _⟩
    refine ⟨?_, ?_⟩
    · rw [result]
      exact (ite_eq_right (by rw [hasQ]; decide)).symm
    · rw [memT]; exact frameU

end VG.Proof.Ffdh.Arm
