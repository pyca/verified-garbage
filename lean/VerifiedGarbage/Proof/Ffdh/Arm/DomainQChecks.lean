module

public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
import VerifiedGarbage.Proof.Ffdh.Arm.DomainQRange
import VerifiedGarbage.Proof.Ffdh.Arm.DomainDivides
import VerifiedGarbage.Proof.Ffdh.Arm.Subgroup
import VerifiedGarbage.Proof.Ffdh.Arm.Branch
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareAt
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack

/-! Native subgroup-order validation, divisibility, and generator subgroup membership. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)

def domainQFlag (p : Inputs) : BitVec 32 :=
  if 2 < p.Q ∧ p.Q < p.P - 1 ∧ p.Q % 2 = 1 then
    if p.P % p.Q = 1 then if Spec.Rsa.powMod p.G p.Q p.P = 1 then 1 else 0 else 0 else 0

theorem domainQChecks_ok (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots) (h56 : 56 ∈ slots) (h60 : 60 ∈ slots)
    (hasQ : p.hasQ = true) (ready : ArithmeticReady p.base p.len p.w s)
    (modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P) (large : 1 < p.P) (odd : p.P % 2 = 1)
    (r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P) :
    WP isa VG.Impl.Ffdh.Arm.Domain.CheckDomain.qChecks s fun t =>
      t.gpr .r0 = domainQFlag p ∧ Frame (prepareAtWrites p s) s.mem t.mem := by
  have extend {m m' : Mem} (f : Frame [⟨State.addr p.base, 8 * p.len⟩] m m') : Frame (prepareAtWrites p s) m m' :=
    f.mono (by intro r hr; rw [List.mem_singleton] at hr; subst r; exact List.mem_cons_self)
  rw [VG.Impl.Ffdh.Arm.Domain.CheckDomain.qChecks, WP.seq_iff]
  refine WP.mono (qRange_ok s h stable h60 h32 hasQ ready modulus odd r2) ?_
  rintro u ⟨contextU, _, flagU, _, _, frameU, restU⟩
  rw [VG.Impl.Ffdh.Arm.Domain.ifFlag, WP.seq_iff]
  refine WP.mono (testFlag_ok u) ?_
  rintro v ⟨⟨zeroV, memV⟩, restV⟩
  by_cases qValid : 2 < p.Q ∧ p.Q < p.P - 1 ∧ p.Q % 2 = 1
  · refine WP.ite true (by change some (!v.z) = some true; rw [zeroV, flagU, qRangeFlag, ite_eq_left qValid]; rfl) ?_ (by intro hf; cases hf)
    intro _
    have contextV := contextU.of_mem memV restV ((restV.gpr .r0 (by simp)).trans contextU.ptr)
    rw [WP.seq_iff]
    refine WP.mono (domainDivides_ok v contextV stable h0 h24 h32 h60 hasQ (by omega) qValid.2.2) ?_
    rintro w ⟨contextW, dividesW, frameW, restW⟩
    rw [VG.Impl.Ffdh.Arm.Domain.ifFlag, WP.seq_iff]
    refine WP.mono (testFlag_ok w) ?_
    rintro x ⟨⟨zeroX, memX⟩, restX⟩
    by_cases divides : p.P % p.Q = 1
    · refine WP.ite true (by change some (!x.z) = some true; rw [zeroX, dividesW, ite_eq_left divides]; rfl) ?_ (by intro hf; cases hf)
      intro _
      have contextX := contextW.of_mem memX restX ((restX.gpr .r0 (by simp)).trans contextW.ptr)
      have pStack : Region.Disjoint ⟨State.addr p.domain, p.k⟩ ⟨State.addr x.sp, 72⟩ :=
        contextX.domainStack.sub_left (Region.sub_prefix (by rw [p.domainLength]; split <;> omega))
      rw [WP.seq_iff]
      refine WP.mono (prepareAt_ok x 24 contextX stable h24 h32 h0 contextX.pBytes p.pLength pStack large odd) ?_
      rintro y ⟨contextY, readyY, modY, r2Y, frameY, restY⟩
      rw [WP.seq_iff]
      refine WP.mono (subgroup_ok y 56 contextY stable h56 h60 h32 hasQ readyY modY odd r2Y contextY.gBytes p.gLength) ?_
      rintro z ⟨_, _, flagZ, _, _, frameZ, _⟩
      refine WP.mono (finishFlag_ok z) ?_
      rintro t ⟨⟨result, memT⟩, _⟩
      refine ⟨by rw [result, flagZ, domainQFlag, ite_eq_left qValid, ite_eq_left divides]; rfl, ?_⟩
      have frameW' : Frame (prepareAtWrites p s) u.mem w.mem := by
        rw [memV] at frameW
        simpa only [prepareAtWrites, prepareWrites, restV.sp, restW.sp, restU.sp] using frameW
      have frameY' : Frame (prepareAtWrites p s) w.mem y.mem := by
        rw [memX] at frameY
        simpa only [prepareAtWrites, prepareWrites, restX.sp, restW.sp, restV.sp, restU.sp] using frameY
      rw [memT]
      exact (((extend frameU).trans frameW').trans frameY').trans (extend frameZ)
    · refine WP.ite false (by change some (!x.z) = some false; rw [zeroX, dividesW, ite_eq_right divides]; rfl) (by intro ht; cases ht) ?_
      intro _
      refine WP.mono (ret_ok x 0 (by decide)) ?_
      rintro t ⟨⟨result, memT⟩, _⟩
      refine ⟨by rw [result, domainQFlag, ite_eq_left qValid, ite_eq_right divides], ?_⟩
      rw [memT, memX]
      rw [memV] at frameW
      exact (extend frameU).trans (by simpa only [prepareAtWrites, prepareWrites, restV.sp, restU.sp] using frameW)
  · refine WP.ite false (by change some (!v.z) = some false; rw [zeroV, flagU, qRangeFlag, ite_eq_right qValid]; rfl) (by intro ht; cases ht) ?_
    intro _
    refine WP.mono (ret_ok v 0 (by decide)) ?_
    rintro t ⟨⟨result, memT⟩, _⟩
    exact ⟨by rw [result, domainQFlag, ite_eq_right qValid], by rw [memT, memV]; exact extend frameU⟩

end VG.Proof.Ffdh.Arm
