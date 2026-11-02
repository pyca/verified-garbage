module

public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Proof.Ffdh.Arm.DomainQChecks
import VerifiedGarbage.Proof.Ffdh.Arm.QTest
import VerifiedGarbage.Proof.Ffdh.Arm.Branch
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack

/-! A domain without q needs only the modulus and generator checks; with q,
the order, divisibility, and subgroup checks run in native code. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)

def domainTailFlag (p : Inputs) : BitVec 32 := if p.hasQ = true then domainQFlag p else 1

theorem domainTail_ok (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots)
    (h56 : 56 ∈ slots) (h60 : 60 ∈ slots)
    (ready : ArithmeticReady p.base p.len p.w s)
    (modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P) (large : 1 < p.P) (odd : p.P % 2 = 1)
    (r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.withQ VG.Impl.Ffdh.Arm.Domain.CheckDomain.qChecks
      (VG.Impl.Ffdh.Arm.Domain.ret 1)) s fun t =>
        t.gpr .r0 = domainTailFlag p ∧ Frame (prepareAtWrites p s) s.mem t.mem := by
  rw [VG.Impl.Ffdh.Arm.Domain.withQ, WP.seq_iff]
  refine WP.mono (qTest_ok s h h28 h32) ?_
  rintro u ⟨⟨zero, memU⟩, restU⟩
  have ptrU := (restU.gpr .r0 (by simp)).trans ready.ptr
  have contextU := h.of_mem memU restU ptrU
  have readyU := ready.of_mem memU restU ptrU
  refine WP.ite p.hasQ (by simp only [eval, zero, Bool.not_not]) ?_ ?_
  · intro hasQ
    refine WP.mono (domainQChecks_ok u contextU stable h0 h24 h32 h56 h60 hasQ readyU
      (by rw [memU]; exact modulus) large odd (by rw [memU]; exact r2)) ?_
    rintro t ⟨result, frame⟩
    refine ⟨by rw [domainTailFlag, ite_eq_left hasQ]; exact result, ?_⟩
    rw [memU] at frame
    simpa only [prepareAtWrites, prepareWrites, restU.sp] using frame
  · intro hasQ
    refine WP.mono (ret_ok u 1 (by decide)) ?_
    rintro t ⟨⟨result, memT⟩, _⟩
    refine ⟨by rw [domainTailFlag, ite_eq_right (by rw [hasQ]; decide)]; exact result, ?_⟩
    rw [memT, memU]; exact Frame.refl _ _

end VG.Proof.Ffdh.Arm
