module

public import VerifiedGarbage.Proof.Sm4.AArch64.Serial.State
public import VerifiedGarbage.Proof.Sm4.AArch64.Serial.Copy
public import VerifiedGarbage.Proof.Sm4.AArch64.ModeCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sm4.CtrCipher
import VerifiedGarbage.Proof.Sm4.AArch64.Serial.Prepare

/-! # The serial SM4 core's prepared state -/

@[expose] public section

namespace VG.Proof.Sm4.AArch64.Serial

open VG VG.AArch64 VG.Impl.Sm4.AArch64.Serial
open VG.Proof.Modes.AArch64 (ScrIn coreRegion)
open VG.Proof.Sm4.AArch64 (KeyArgs)

theorem prepare_wp {s : State} {B : Addr} {rs : List Region} {k : Spec.Sm4.Schedule}
    (hB : s.gpr .x5 = B) (hs : ScrIn s B core.total)
    (hR : (⟨B,8*core.total⟩ : Region) ∈ rs) (hk : KeyArgs s rs k) :
    WP isa core.prepare s fun t => Ready t.mem B k ∧ t.gpr .x5 = B ∧
      t.gpr .x23 = s.gpr .x23 ∧ t.gpr .x24 = s.gpr .x24 ∧
      Frame [coreRegion core B] s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨p,hp,rfl,hin,hfit,hdis⟩ := hk
  have hw : InRegions s.wr B (8*396) := ⟨_,hs.wr,by change (⟨B,3264⟩ : Region).Contains B 3168; simp [Region.Contains]⟩
  have hkey : Region.Disjoint ⟨p,128⟩ ⟨B,8*core.total⟩ := hdis _ hR
  change WP isa (.seq (.block preparedTable) copySchedule) s _
  refine WP.seq (WP.mono (preparedTable_wp hB hw) fun a ⟨aw,ag,ard,awr,af⟩ => ?_)
  have ab : a.gpr .x5 = B := (ag _ (by decide)).trans hB
  have ap : a.gpr .x0 = p := (ag _ (by decide)).trans hp
  have preserved : ∀ j < 128, a.mem (p+BitVec.ofNat 64 j) = s.mem (p+BitVec.ofNat 64 j) := by
    intro j hj
    exact af.bytes (R := ⟨p,128⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst r
      exact hkey.sub_right (Region.sub_prefix (by decide))) (by show 128 ≤ 2^64; decide) hj
  have readKey : InRegions (a.rd ++ a.wr) (a.gpr .x0) 128 := by
    rw [ard,awr,ap]
    exact ⟨_,List.mem_append_left _ hin,Region.contains_self _ _⟩
  have writeKey : InRegions a.wr (a.gpr .x5 + BitVec.ofNat 64 256) 128 := by
    rw [awr,ab]
    exact ⟨_,hs.wr,VG.Offset.contains_base B (by decide : 256+128 ≤ 3264) (by decide)⟩
  have sepKey : Region.Disjoint ⟨a.gpr .x0,128⟩ ⟨a.gpr .x5+BitVec.ofNat 64 256,128⟩ := by
    rw [ap,ab]
    exact hkey.sub_right (VG.Offset.sub_base B (by decide : 256+128 ≤ 3264))
  refine WP.mono (copySchedule_wp readKey writeKey sepKey) fun t ⟨tc,tf,tg,trd,twr⟩ => ?_
  have table : ∀ j < 256, t.mem (B+BitVec.ofNat 64 j) = Spec.Sm4.sbox.getD j 0 := by
    intro j hj
    have tf' : Frame [⟨B+BitVec.ofNat 64 256,128⟩] a.mem t.mem := by simpa only [ab] using tf
    rw [tf'.bytes (R := ⟨B,256⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst r
      exact VG.Offset.base_disjoint B (by decide : 256 ≤ 256) (by decide : 256+128 ≤ 2^64)) (by show 256 ≤ 2^64; decide) hj]
    exact preparedTable_bytes aw j hj
  have copied : Spec.Sm4.scheduleAt t.mem (B+BitVec.ofNat 64 256) = Spec.Sm4.scheduleAt s.mem p := by
    apply copied_schedule
    intro j hj
    have e := tc j hj
    rw [ab,ap,preserved j hj] at e
    exact e
  have keyWords : ∀ i < 32, t.mem.readW (B+BitVec.ofNat 64 (256+4*i)) 32 =
      (Spec.Sm4.scheduleAt s.mem p).getD i 0 := by
    intro i hi
    rw [← VG.Offset.add_add B 256 (4*i),schedule_readW _ _ i hi,copied]
  refine ⟨⟨table,?_⟩,?_,?_,?_,?_,trd.trans ard,twr.trans awr⟩
  · simpa only [hp] using keyWords
  · exact (tg _ (by decide) (by decide) (by decide) (by decide)).trans ab
  · exact (tg _ (by decide) (by decide) (by decide) (by decide)).trans (ag _ (by decide))
  · exact (tg _ (by decide) (by decide) (by decide) (by decide)).trans (ag _ (by decide))
  · refine (af.sub (fun r hr => ?_)).trans (tf.sub (fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst r
      exact ⟨_,List.mem_cons_self,Region.sub_prefix (by decide : 256 ≤ 3168)⟩
    · simp only [List.mem_singleton] at hr; subst r
      exact ⟨_,List.mem_cons_self,by rw [ab]; exact VG.Offset.sub_base B (by decide : 256+128 ≤ 3168)⟩

end VG.Proof.Sm4.AArch64.Serial
