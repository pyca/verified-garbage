module

import VerifiedGarbage.Proof.Ffdh.Arm.PublicScan
public import VerifiedGarbage.Proof.Ffdh.Arm.Power
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ffdh.Arm.PublicScan
public import VerifiedGarbage.Proof.Ffdh.Arm.Octets
public import VerifiedGarbage.Proof.Ffdh.Lead

/-! The retained public exponent suffix has the same integer value. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

namespace PublicScan

theorem input_ok (s : State) {base src ep : BitVec 32} {len w M : Nat} {bb eb : List Byte}
    (h : PowerInput base src ep len w M bb eb s) :
    WP isa VG.Impl.Ffdh.Arm.PublicScan.code s fun t =>
      PowerInput base src (ep + BitVec.ofNat 32 (VG.Proof.Ffdh.lead eb)) len w M bb
        (eb.drop (VG.Proof.Ffdh.lead eb)) t ∧ t.mem = s.mem ∧
      Rest [.r1,.r2,.r3,.r4,.r6,.r8,.r9,.r11] s t := by
  refine WP.mono (code_ok s h.exponentBytes h.exponentPositive h.exponentFits h.exponent h.exponentCount) ?_
  rintro t ⟨epT,countT,sourceT,baseCountT,mem,rest⟩
  have frame : Frame [⟨State.addr base,8*len⟩] s.mem t.mem := by rw [mem];exact Frame.refl _ _
  have leadLt := VG.Proof.Ffdh.lead_lt (bs:=eb) (by intro e;rw [e] at h; have := h.exponentPositive; simp at this)
  have exponent := (h.exponentBytes.after_workspace frame rest).slice
    (d:=VG.Proof.Ffdh.lead eb) (k:=eb.length-VG.Proof.Ffdh.lead eb) (by omega) (by omega)
  rw [List.take_of_length_le (by simp)] at exponent
  exact ⟨⟨h.ready.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.ready.ptr),
    by rw [mem];exact h.modulus,h.odd,by rw [mem];exact h.r2,
    h.baseBytes.after_workspace frame rest,exponent,h.basePositive,h.baseFits,
    by simp only [List.length_drop];omega,
    by simp only [List.length_drop];have := h.exponentFits;omega,
    sourceT.trans h.source,baseCountT.trans h.count,epT,by simpa only [List.length_drop] using countT⟩,
    mem,rest⟩

/-- Any region disjoint from the full public exponent remains disjoint from
its retained suffix, including the shared Montgomery helper's stack. -/
theorem suffix_separate {base ep : BitVec 32} {len : Nat} {eb : List Byte} {s : State}
    (source : Octets base ep len eb s) (positive : 0 < eb.length) {region : Region}
    (separate : Region.Disjoint ⟨State.addr ep,eb.length⟩ region) :
    Region.Disjoint
      ⟨State.addr (ep+BitVec.ofNat 32 (VG.Proof.Ffdh.lead eb)),
        (eb.drop (VG.Proof.Ffdh.lead eb)).length⟩ region := by
  have leadLt := VG.Proof.Ffdh.lead_lt (bs:=eb) (by intro e;rw [e] at positive;simp at positive)
  have bound : ep.toNat + VG.Proof.Ffdh.lead eb < 2^32 := by have := source.fits;omega
  rw [VG.Arm.addr_add bound,List.length_drop]
  exact separate.sub_left (Offset.sub_base _ (by omega))

end PublicScan
end VG.Proof.Ffdh.Arm
