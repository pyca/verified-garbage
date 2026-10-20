module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.InitCall
public import VerifiedGarbage.Proof.MlKem.AArch64.Lay
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Squeeze
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cover
import VerifiedGarbage.Proof.Framework.Offset

/-! # Saved-register initialization and the first three matrix blocks -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3 (iterF)

def startRegs : List Reg := initRegs++squeezeRegs

theorem start_ok {s : State} {p seed : Addr} {sb ss a b k : Nat}
    (hss : ss<65536) (hsb : sb+32≤32768) (h8 : sb%8=0)
    (hp : s.gpr .x28+BitVec.ofNat 64 ss=p)
    (ha : s.gpr .x28+BitVec.ofNat 64 sb=seed)
    (hin : ∀j<4, InRegions (s.rd++s.wr) (seed+BitVec.ofNat 64 (8*j)) 8)
    (hc : Covers [⟨p,2048⟩] s.wr)
    (hsep : (Region.mk seed 32).Disjoint ⟨p,2048⟩) :
    WP isa (.seq (.block (Impl.MlKem.AArch64.Paired.init sb ss a b k)) Impl.MlKem.AArch64.Paired.squeeze) s fun t =>
      Keep startRegs s t ∧ Frame [⟨p,2048⟩] s.mem t.mem ∧ Noise.Saved p s t.mem ∧
      t.gpr .x19=p ∧ t.gpr .x22=0 ∧
      PairAt t.mem p (iterF 3 (seedState s.mem seed a k)) (iterF 3 (seedState s.mem seed b k)) ∧
      Blocks t.mem (p+400) 3 (seedState s.mem seed a k) ∧
      Blocks t.mem (p+904) 3 (seedState s.mem seed b k) := by
  have iw {o l : Nat} (h : o+l≤2048) := Noise.inScratch hc h (by decide)
  refine WP.seq (WP.mono (init_ok hss hsb h8 hp ha hin
    (fun j hj => iw (by omega)) (fun j hj => iw (by omega))
    (hsep.sub_right (Offset.sub_base p (by decide)))
    (hsep.sub_right (Region.sub_prefix (by decide : 400≤2048)))
    (Offset.disjoint_base p (by decide) (by decide))) fun u ⟨ku,fu,sv,h19,h20,h21,h22,pair⟩ => ?_)
  refine WP.mono (squeeze_ok h19 h20 h21 (by rw [h22]; rfl) pair
    (fun i hi => by
      rw [ku.rd,ku.wr]
      obtain ⟨r,hr,hh⟩ := iw (by omega : 16*i+16≤2048)
      exact ⟨r,List.mem_append_right _ hr,hh⟩)
    (fun j hj i hi => by
      rw [ku.wr]; change InRegions s.wr ((p+BitVec.ofNat 64 400+BitVec.ofNat 64 (168*j))+BitVec.ofNat 64 (8*i)) 8
      rw [BitVec.add_assoc,BitVec.add_assoc,← BitVec.ofNat_add,← BitVec.ofNat_add]
      exact iw (by omega))
    (fun j hj i hi => by
      rw [ku.wr]; change InRegions s.wr ((p+BitVec.ofNat 64 904+BitVec.ofNat 64 (168*j))+BitVec.ofNat 64 (8*i)) 8
      rw [BitVec.add_assoc,BitVec.add_assoc,← BitVec.ofNat_add,← BitVec.ofNat_add]
      exact iw (by omega))
    (Offset.disjoint p (by decide) (by decide) (by decide))
    (Offset.base_disjoint p (by decide) (by decide))
    (Offset.base_disjoint p (by decide) (by decide))
    (Offset.disjoint p (by decide) (by decide) (by decide))
    (Offset.disjoint p (by decide) (by decide) (by decide))
    (Offset.base_disjoint p (by decide) (by decide))
    (by
      rw [ku.wr]
      have ha : Covers [pairR p] s.wr := by
        simpa only [BitVec.add_zero,pairR] using (Noise.coversScratch (off := 0) (len := 400) hc (by decide))
      exact Noise.coversTwo ha (Noise.coversScratch (off := 1536) (len := 136) hc (by decide)))) fun t ht => ?_
  refine ⟨(ku.trans ht.keep),?_,?_,ht.ptr,?_,ht.pair,ht.oa,ht.ob⟩
  · have fi : Frame [⟨p,2048⟩] s.mem u.mem := fu.sub (by
      intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨p,2048⟩,by simp,Offset.sub_base p (by decide)⟩
      · exact ⟨⟨p,2048⟩,by simp,Region.sub_prefix (by decide : 400≤2048)⟩)
    exact fi.trans (ht.frame.sub (by
      intro r hr; simp only [squeezeWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨p,2048⟩,by simp,Region.sub_prefix (by decide : 400≤2048)⟩
      · exact ⟨⟨p,2048⟩,by simp,Offset.sub_base p (by decide)⟩
      · exact ⟨⟨p,2048⟩,by simp,Offset.sub_base p (by decide)⟩
      · exact ⟨⟨p,2048⟩,by simp,Offset.sub_base p (by decide)⟩))
  · apply sv.frame ht.frame
    intro r hr; simp only [squeezeWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Offset.disjoint_base p (by decide) (by decide)
    · exact Offset.disjoint p (by decide) (by decide) (by decide)
    · exact Offset.disjoint p (by decide) (by decide) (by decide)
    · exact Offset.disjoint p (by decide) (by decide) (by decide)
  · apply BitVec.eq_of_toNat_eq; exact ht.count

end VG.Proof.MlKem.AArch64.Paired
