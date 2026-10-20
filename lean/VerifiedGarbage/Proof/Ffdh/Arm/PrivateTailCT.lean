module

public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
import VerifiedGarbage.Proof.Ffdh.Arm.PrivateTail
import VerifiedGarbage.Proof.Ffdh.Arm.PrivateMatchCT
import VerifiedGarbage.Proof.Ffdh.Arm.FlagCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
public import VerifiedGarbage.Proof.Ffdh.Arm.PrivateState
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.BranchCT
import VerifiedGarbage.Proof.Ffdh.Arm.SubgroupCT
import VerifiedGarbage.Proof.Ffdh.Arm.QTest
import VerifiedGarbage.Proof.Ffdh.Arm.Subgroup

/-! Private-key subgroup branches depend on the public value, followed by constant-time consistency checking. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

structure PrivateMember (p : Inputs) (slots : List Nat) (yb xb : List Byte) (s : State) : Prop extends
    PrivateReady p slots yb xb s where
  flag : s.gpr .r11 = if Spec.Rsa.powMod (Spec.Rsa.os2ip yb) p.Q p.P = 1 then 1 else 0

theorem PrivateMember.after_mem {p : Inputs} {slots : List Nat} {yb xb : List Byte} {s t : State}
    (h : PrivateMember p slots yb xb s) (mem : t.mem = s.mem) (rest : VG.Proof.X25519.Arm.Rest [] s t) :
    PrivateMember p slots yb xb t :=
  ⟨h.toPrivateReady.after_mem mem rest ((rest.gpr .r0 (by simp)).trans h.context.ptr),
    (rest.gpr .r11 (by simp)).trans h.flag⟩

theorem privateTail_ct {p : Inputs} {slots : List Nat} {yb xb1 xb2 : List Byte}
    (stable : stableSlots slots = true) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h36 : 36 ∈ slots)
    (h40 : 40 ∈ slots) (h44 : 44 ∈ slots) (h56 : 56 ∈ slots) (h60 : 60 ∈ slots)
    (peerLength : yb.length = p.k) (positive : 0 < xb1.length) (fits : xb1.length < 2 ^ 32)
    (count : p.slotValue 44 = BitVec.ofNat 32 xb1.length) (length : xb1.length = xb2.length) (odd : p.P % 2 = 1) :
    RelCT isa (fun s t => PrivateReady p slots yb xb1 s ∧ PrivateReady p slots yb xb2 t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.CheckPrivate.tail (fun _ _ => True) := by
  let Q := fun (xb : List Byte) (s : State) => PrivateReady p slots yb xb s ∧ s.z = !p.hasQ
  have tests := qTest_ct.mono
    (P' := fun (s t : State) => PrivateReady p slots yb xb1 s ∧ PrivateReady p slots yb xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  have wpTest (s : State) {xb : List Byte} (h : PrivateReady p slots yb xb s) :
      WP isa VG.Impl.Ffdh.Arm.Domain.qTest s (Q xb) := by
    refine WP.mono (qTest_ok s h.context h28 h32) ?_
    rintro u ⟨⟨zero, mem⟩, rest⟩
    exact ⟨h.after_mem mem rest ((rest.gpr .r0 (by simp)).trans h.context.ptr), zero⟩
  have matchCT := privateMatch_ct stable h32 h36 h40 h44 h56 peerLength positive fits count length odd
  have branches : RelCT isa (fun s t => Q xb1 s ∧ Q xb2 t ∧ s.sp = t.sp)
      (.ite .ne (.seq (VG.Impl.Ffdh.Arm.Domain.subgroup 36)
        (VG.Impl.Ffdh.Arm.Domain.ifFlag VG.Impl.Ffdh.Arm.Domain.CheckPrivate.matchPublic (VG.Impl.Ffdh.Arm.Domain.ret 0)))
        VG.Impl.Ffdh.Arm.Domain.CheckPrivate.matchPublic) (fun _ _ => True) := by
    apply iteKnownPair_ct p.hasQ (fun s h => by simp only [eval, h.2, Bool.not_not])
      (fun s h => by simp only [eval, h.2, Bool.not_not])
    · intro hasQ
      have subgroup := (subgroup_ct stable h36 h60 h32 hasQ peerLength odd).mono
        (P' := fun (s t : State) => PrivateReady p slots yb xb1 s ∧ PrivateReady p slots yb xb2 t ∧ s.sp = t.sp)
        (fun _ _ h => ⟨⟨h.1.context, h.1.ready, h.1.modulus, h.1.r2, h.1.value⟩,
          ⟨h.2.1.context, h.2.1.ready, h.2.1.modulus, h.2.1.r2, h.2.1.value⟩, h.2.2⟩) (fun _ _ h => h)
      have wpSubgroup (s : State) {xb : List Byte} (h : PrivateReady p slots yb xb s) :
          WP isa (VG.Impl.Ffdh.Arm.Domain.subgroup 36) s (PrivateMember p slots yb xb) := by
        refine WP.mono (subgroup_ok s 36 h.context stable h36 h60 h32 hasQ h.ready h.modulus odd h.r2 h.value peerLength) ?_
        rintro u ⟨context, ready, flag, modulus, r2, frame, rest⟩
        exact ⟨⟨context, ready, modulus, r2, h.value.after_workspace frame rest, h.scalar.after_workspace frame rest⟩, flag⟩
      have matched : RelCT isa (fun s t => PrivateMember p slots yb xb1 s ∧ PrivateMember p slots yb xb2 t ∧ s.sp = t.sp)
          (VG.Impl.Ffdh.Arm.Domain.ifFlag VG.Impl.Ffdh.Arm.Domain.CheckPrivate.matchPublic (VG.Impl.Ffdh.Arm.Domain.ret 0))
          (fun _ _ => True) := by
        apply ifFlag_pair_ct (decide (Spec.Rsa.powMod (Spec.Rsa.os2ip yb) p.Q p.P = 1))
          (fun _ h => by simpa only [decide_eq_true_eq] using h.flag)
          (fun _ h => by simpa only [decide_eq_true_eq] using h.flag)
          (fun _ _ h mem rest => h.after_mem mem rest) (fun _ _ h mem rest => h.after_mem mem rest)
        · intro _
          exact matchCT.mono (fun _ _ h => ⟨h.1.toPrivateReady, h.2.1.toPrivateReady, h.2.2⟩) (fun _ _ h => h)
        · intro _
          exact (ret_ct 0).mono (fun _ _ _ => trivial) (fun _ _ h => h)
      exact (relCT_chain subgroup (fun s h => wpSubgroup s h) (fun s h => wpSubgroup s h) matched).mono
        (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h)
    · intro _
      exact matchCT.mono (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.CheckPrivate.tail VG.Impl.Ffdh.Arm.Domain.withQ
  exact relCT_chain tests (fun s h => wpTest s h) (fun s h => wpTest s h) branches

end VG.Proof.Ffdh.Arm
