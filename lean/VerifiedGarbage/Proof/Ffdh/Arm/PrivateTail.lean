module

public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Proof.Ffdh.Arm.PrivateMatch
import VerifiedGarbage.Proof.Ffdh.Arm.Subgroup
import VerifiedGarbage.Proof.Ffdh.Arm.QTest
import VerifiedGarbage.Proof.Ffdh.Arm.Branch
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack

/-! Imported public subgroup membership precedes native private-key consistency checking. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)

def privateTailFlag (p : Inputs) (yb xb : List Byte) : BitVec 32 :=
  if p.hasQ = true then
    if Spec.Rsa.powMod (Spec.Rsa.os2ip yb) p.Q p.P = 1 then privateMatchFlag p yb xb else 0
  else privateMatchFlag p yb xb

theorem privateTail_ok (s : State) {p : Inputs} {slots : List Nat} {yb xb : List Byte}
    (h : Context p slots s) (stable : stableSlots slots = true)
    (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h40 : 40 ∈ slots)
    (h44 : 44 ∈ slots) (h56 : 56 ∈ slots) (h60 : 60 ∈ slots)
    (ready : ArithmeticReady p.base p.len p.w s)
    (modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P) (odd : p.P % 2 = 1)
    (r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P)
    (value : Octets p.base p.publicValue p.len yb s) (length : yb.length = p.k)
    (scalar : Octets p.base p.privateValue p.len xb s) (positive : 0 < xb.length) (fits : xb.length < 2 ^ 32)
    (count : p.slotValue 44 = BitVec.ofNat 32 xb.length) :
    WP isa VG.Impl.Ffdh.Arm.Domain.CheckPrivate.tail s fun t =>
      t.gpr .r0 = privateTailFlag p yb xb ∧ Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem t.mem := by
  rw [VG.Impl.Ffdh.Arm.Domain.CheckPrivate.tail, VG.Impl.Ffdh.Arm.Domain.withQ, WP.seq_iff]
  refine WP.mono (qTest_ok s h h28 h32) ?_
  rintro u ⟨⟨zero, memU⟩, restU⟩
  have ptrU := (restU.gpr .r0 (by simp)).trans h.ptr
  have contextU := h.of_mem memU restU ptrU
  have readyU := ready.of_mem memU restU ptrU
  have frameU : Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem u.mem := by rw [memU]; exact Frame.refl _ _
  have valueU := value.after_workspace frameU restU
  have scalarU := scalar.after_workspace frameU restU
  refine WP.ite p.hasQ (by simp only [eval, zero, Bool.not_not]) ?_ ?_
  · intro hasQ
    rw [WP.seq_iff]
    refine WP.mono (subgroup_ok u 36 contextU stable h36 h60 h32 hasQ readyU
      (by rw [memU]; exact modulus) odd (by rw [memU]; exact r2) valueU length) ?_
    rintro v ⟨contextV, readyV, memberFlag, modV, r2V, frameV, restV⟩
    rw [VG.Impl.Ffdh.Arm.Domain.ifFlag, WP.seq_iff]
    refine WP.mono (testFlag_ok v) ?_
    rintro w ⟨⟨zeroW, memW⟩, restW⟩
    by_cases member : Spec.Rsa.powMod (Spec.Rsa.os2ip yb) p.Q p.P = 1
    · refine WP.ite true (by change some (!w.z) = some true; rw [zeroW, memberFlag, ite_eq_left member]; rfl) ?_ (by intro hf; cases hf)
      intro _
      have ptrW := (restW.gpr .r0 (by simp)).trans contextV.ptr
      have contextW := contextV.of_mem memW restW ptrW
      have readyW := readyV.of_mem memW restW ptrW
      have frameW : Frame [⟨State.addr p.base, 8 * p.len⟩] v.mem w.mem := by rw [memW]; exact Frame.refl _ _
      refine WP.mono (privateMatch_ok w contextW stable h32 h36 h40 h44 h56 readyW
        (by rw [memW]; exact modV) odd (by rw [memW]; exact r2V)
        ((valueU.after_workspace frameV restV).after_workspace frameW restW) length
        ((scalarU.after_workspace frameV restV).after_workspace frameW restW) positive fits count) ?_
      rintro t ⟨result, frameT⟩
      exact ⟨by rw [privateTailFlag, ite_eq_left hasQ, ite_eq_left member]; exact result,
        ((frameU.trans frameV).trans frameW).trans frameT⟩
    · refine WP.ite false (by change some (!w.z) = some false; rw [zeroW, memberFlag, ite_eq_right member]; rfl) (by intro ht; cases ht) ?_
      intro _
      refine WP.mono (ret_ok w 0 (by decide)) ?_
      rintro t ⟨⟨result, memT⟩, _⟩
      exact ⟨by rw [result, privateTailFlag, ite_eq_left hasQ, ite_eq_right member], by rw [memT, memW]; exact frameU.trans frameV⟩
  · intro hasQ
    refine WP.mono (privateMatch_ok u contextU stable h32 h36 h40 h44 h56 readyU
      (by rw [memU]; exact modulus) odd (by rw [memU]; exact r2) valueU length scalarU positive fits count) ?_
    rintro t ⟨result, frameT⟩
    exact ⟨by rw [privateTailFlag, ite_eq_right (by rw [hasQ]; decide)]; exact result, frameU.trans frameT⟩

end VG.Proof.Ffdh.Arm
