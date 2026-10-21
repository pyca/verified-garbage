module

public import VerifiedGarbage.Impl.Ffdh.Arm.PublicScan
public import VerifiedGarbage.Proof.Ffdh.Arm.Octets
public import VerifiedGarbage.Proof.Ffdh.Lead
import VerifiedGarbage.Proof.Ffdh.Arm.KeyScan
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Reuse the key generator's checked public-bound scan for subgroup exponents. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm
open VG.Proof.X25519.Arm (Rest)

namespace PublicScan
open VG.Impl.Ffdh.Arm.PublicScan

theorem enter_ok (s : State) : WP isa (.block enter) s fun t =>
    (t.gpr .r4 = s.gpr .r1 ∧ t.gpr .r6 = s.gpr .r2 ∧
      t.gpr .r8 = s.gpr .r4 ∧ t.gpr .r9 = s.gpr .r6 ∧ t.mem = s.mem) ∧
    Rest [.r4,.r6,.r8,.r9] s t := by
  refine withRest [.r4,.r6,.r8,.r9] ?_ (by
    intro r hr i hi
    have checked : (instrs (.block enter : Prog isa)).all (fun i => !(clobbers i r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have f := List.all_eq_true.mp checked i hi
    cases hc : clobbers i r <;> simp_all) (by rfl)
  unfold enter
  ffrun []

theorem leave_ok (s : State) : WP isa (.block leave) s fun t =>
    (t.gpr .r1 = s.gpr .r4 ∧ t.gpr .r2 = s.gpr .r6 ∧
      t.gpr .r4 = s.gpr .r8 ∧ t.gpr .r6 = s.gpr .r9 ∧ t.mem = s.mem) ∧
    Rest [.r1,.r2,.r4,.r6] s t := by
  refine withRest [.r1,.r2,.r4,.r6] ?_ (by
    intro r hr i hi
    have checked : (instrs (.block leave : Prog isa)).all (fun i => !(clobbers i r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have f := List.all_eq_true.mp checked i hi
    cases hc : clobbers i r <;> simp_all) (by rfl)
  unfold leave
  ffrun []

theorem code_ok (s : State) {base src : BitVec 32} {len : Nat} {bs : List Byte}
    (source : Octets base src len bs s) (positive : 0 < bs.length) (fits : bs.length < 2^32)
    (ptr : s.gpr .r1 = src) (count : s.gpr .r2 = BitVec.ofNat 32 bs.length) :
    WP isa code s fun t =>
      t.gpr .r1 = src + BitVec.ofNat 32 (VG.Proof.Ffdh.lead bs) ∧
      t.gpr .r2 = BitVec.ofNat 32 (bs.length - VG.Proof.Ffdh.lead bs) ∧
      t.gpr .r4 = s.gpr .r4 ∧ t.gpr .r6 = s.gpr .r6 ∧
      t.mem = s.mem ∧ Rest [.r1,.r2,.r3,.r4,.r6,.r8,.r9,.r11] s t := by
  rw [code, WP.seq_iff]
  refine WP.mono (enter_ok s) ?_
  rintro u ⟨⟨p4,p6,p8,p9,memU⟩,restU⟩
  have frameU : Frame [] s.mem u.mem := by rw [memU]; exact Frame.refl _ _
  have sourceU := source.after_frame frameU restU (by simp)
  have scan_ok : WP isa scan u fun v =>
      v.gpr .r4 = src + BitVec.ofNat 32 (VG.Proof.Ffdh.lead bs) ∧
      v.gpr .r6 = BitVec.ofNat 32 (bs.length - VG.Proof.Ffdh.lead bs) ∧
      v.gpr .r3 = (bs.getD (VG.Proof.Ffdh.lead bs) 0).setWidth 32 ∧
      v.mem = u.mem ∧ Rest [.r3,.r4,.r6,.r11] u v :=
    keyScan_ok u sourceU positive fits (p4.trans ptr) (p6.trans count)
  rw [WP.seq_iff]
  refine WP.mono scan_ok ?_
  rintro v ⟨v4,v6,_,memV,restV⟩
  refine WP.mono (leave_ok v) ?_
  rintro t ⟨⟨t1,t2,t4,t6,memT⟩,restT⟩
  exact ⟨t1.trans v4,t2.trans v6,
    t4.trans ((restV.gpr .r8 (by simp)).trans p8),
    t6.trans ((restV.gpr .r9 (by simp)).trans p9),
    memT.trans (memV.trans memU),
    ((restU.mono (by simp)).trans (restV.mono (by simp))).trans (restT.mono (by simp))⟩

end PublicScan
end VG.Proof.Ffdh.Arm
