module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Reject
import VerifiedGarbage.Proof.Framework.AArch64.Simd64

/-! # Save and reload rejection continuation cursors -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem

def checkpointW (w16 : Bool) (p aP : Addr) (L : List Zq) (m : Mem) : Prop :=
  m.readW p 64=cAddr w16 aP L.length ∧
    (m.readW (p+8) 64).toNat=256-L.length

abbrev checkpoint := checkpointW false

theorem load_checkpoint (s : State) {slot : Nat} (ho : slot+8<32768) (ha : slot%8=0)
    (h0 : InRegions (s.rd++s.wr) (s.gpr .x19+BitVec.ofNat 64 slot) 8)
    (h1 : InRegions (s.rd++s.wr) (s.gpr .x19+BitVec.ofNat 64 (slot+8)) 8) :
    WP isa (.block [.ldr .x .x3 .x19 slot,.ldr .x .x4 .x19 (slot+8)]) s fun u =>
      Only [.x3,.x4] s u ∧ u.v=s.v ∧
      u.gpr .x3=s.mem.readW (s.gpr .x19+BitVec.ofNat 64 slot) 64 ∧
      u.gpr .x4=s.mem.readW (s.gpr .x19+BitVec.ofNat 64 (slot+8)) 64 := by
  have hw : WP isa (.block [.ldr .x .x3 .x19 slot,.ldr .x .x4 .x19 (slot+8)]) s fun u =>
      Only [.x3,.x4] s u ∧
      u.gpr .x3=s.mem.readW (s.gpr .x19+BitVec.ofNat 64 slot) 64 ∧
      u.gpr .x4=s.mem.readW (s.gpr .x19+BitVec.ofNat 64 (slot+8)) 64 := by
    refine wp_ldrx (by omega) rfl h0 fun a ha ea => wp_ldrx (by omega)
      (by rw [ha.get .x19]) (by rw [ha.rd,ha.wr]; exact h1) fun u hu eu => wp_nil ?_
    refine ⟨(ha.trans hu).mono (by decide),by rw [hu.get .x3,ea],?_⟩
    rw [eu,ha.mem]
  exact WP.mono (WP.keepV (by rfl) hw) fun _ ⟨⟨hk,h3,h4⟩,hv⟩ => ⟨hk,hv,h3,h4⟩

theorem store_checkpoint (s : State) {slot : Nat} (ho : slot+8<32768) (ha : slot%8=0)
    (h0 : InRegions s.wr (s.gpr .x19+BitVec.ofNat 64 slot) 8)
    (h1 : InRegions s.wr (s.gpr .x19+BitVec.ofNat 64 (slot+8)) 8) :
    WP isa (.block [.str .x .x3 .x19 slot,.str .x .x4 .x19 (slot+8)]) s fun u =>
      Keep [] s u ∧ u.v=s.v ∧
      Frame [⟨s.gpr .x19+BitVec.ofNat 64 slot,16⟩] s.mem u.mem ∧
      u.mem.readW (s.gpr .x19+BitVec.ofNat 64 slot) 64=s.gpr .x3 ∧
      u.mem.readW (s.gpr .x19+BitVec.ofNat 64 (slot+8)) 64=s.gpr .x4 := by
  let p := s.gpr .x19+BitVec.ofNat 64 slot
  have he : s.gpr .x19+BitVec.ofNat 64 (slot+8)=p+8 := by simp only [p,BitVec.ofNat_add,BitVec.add_assoc]; rfl
  have hw : WP isa (.block [.str .x .x3 .x19 slot,.str .x .x4 .x19 (slot+8)]) s fun u =>
      Keep [] s u ∧ u.mem=(s.mem.writeW p (s.gpr .x3)).writeW (p+8) (s.gpr .x4) := by
    refine wp_strx (by omega) rfl h0 fun a ha => wp_strx (by omega)
      (by rw [ha.gpr]) (by rw [ha.wr]; exact h1) fun u hu => wp_nil ?_
    refine ⟨(ha.keep.trans hu.keep).mono (by decide),?_⟩
    rw [hu.mem,ha.mem,ha.gpr,he]
  refine WP.mono (WP.keepV (by rfl) hw) fun u ⟨⟨hk,hm⟩,hv⟩ => ⟨hk,hv,?_,?_,?_⟩
  · rw [hm]
    change Frame [⟨p,16⟩] s.mem _
    apply Frame.writeW (r := ⟨p,16⟩) (Frame.writeW (r := ⟨p,16⟩) (Frame.refl _ _) (by simp) _ ?_) (by simp) _ ?_
    · simpa only [ptr_zero] using Offset.contains_base p (d := 0) (n := 8) (k := 16) (by decide) (by decide)
    · exact Offset.contains_base p (d := 8) (n := 8) (k := 16) (by decide) (by decide)
  · change u.mem.readW p 64=_
    have hsep : Mem.Sep p 8 (p+8) 8 := by
      simpa only [ptr_zero,show BitVec.ofNat 64 8=(8 : BitVec 64) from rfl] using Offset.sep p (d := 0) (e := 8) (n := 8) (k := 8) (by decide) (by decide) (by decide)
    rw [hm,Mem.readW_writeW_sep hsep (by decide),Mem.readW_writeW_self64]
  · rw [he,hm,Mem.readW_writeW_self64]

end VG.Proof.MlKem.AArch64.Paired
