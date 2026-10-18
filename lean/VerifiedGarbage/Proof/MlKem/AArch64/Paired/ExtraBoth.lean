module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Memory
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cover

/-! # Resume both public matrix streams and combine their success flags -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem

def bothWrites (p a b : Addr) : List Region :=
  [polyRegion a,polyRegion b,⟨p+1680,16⟩,⟨p+1696,16⟩]
def bothRegs : List Reg := [.x0,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x22,.x23]
def extraBoth (w16 : Bool := false) : Prog isa := .seq (Impl.MlKem.AArch64.Paired.extraReject 400 1680 .x22 w16)
  (.seq (Impl.MlKem.AArch64.Paired.extraReject 904 1696 .x23 w16)
    (.block [.logic .and .x .x6 .x22 .x23]))

structure BothPostW (w16 : Bool) (L M : List Zq) (p a b : Addr) (s u : State) : Prop where
  keep : Keep bothRegs s u
  frame : Frame (bothWrites p a b) s.mem u.mem
  left : Rej8.Scalar.CoeffsW w16 u.mem a L
  right : Rej8.Scalar.CoeffsW w16 u.mem b M
  saveLeft : checkpointW w16 (p+1680) a L u.mem
  saveRight : checkpointW w16 (p+1696) b M u.mem
  flagLeft : (u.gpr .x22).toNat=if L.length=256 then 1 else 0
  flagRight : (u.gpr .x23).toNat=if M.length=256 then 1 else 0
  flagBoth : (u.gpr .x6).toNat=if L.length=256 ∧ M.length=256 then 1 else 0
  constants : Rej8.Constants u

abbrev BothPost := BothPostW false

theorem extraBoth_ok {w16 : Bool} {s : State} {p a b : Addr} {L M : List Zq} {A B : Nat→Byte}
    (hp : s.gpr .x19=p) (hc : Covers [⟨p,2048⟩] s.wr)
    (da : (Region.mk p 2048).Disjoint (polyRegion a))
    (db : (Region.mk p 2048).Disjoint (polyRegion b))
    (dab : (polyRegion a).Disjoint (polyRegion b))
    (ea : Rej8.EnvW w16 56 A (p+400) a s) (eb : Rej8.EnvW w16 56 B (p+904) b s)
    (dt : ∀mask<256,(Region.mk (s.gpr .x16+BitVec.ofNat 64 (16*mask)) 16).Disjoint ⟨p,2048⟩)
    (cs : Rej8.Constants s) (hl : L.length≤256) (hm : M.length≤256)
    (ca : Rej8.Scalar.CoeffsW w16 s.mem a L) (cb : Rej8.Scalar.CoeffsW w16 s.mem b M)
    (sa : checkpointW w16 (p+1680) a L s.mem) (sb : checkpointW w16 (p+1696) b M s.mem) :
    WP isa (extraBoth w16) s (BothPostW w16 (sampleAfter L A 56) (sampleAfter M B 56) p a b s) := by
  have iw {o l : Nat} (h : o+l≤2048) := Noise.inScratch hc h (by decide)
  have ax := extra_ok s (buf:=400) (slot:=1680) (flag:=.x22) (by decide) (by decide) (by decide)
    (by decide) (by rw [hp]; exact ea) cs hl ca (by rw [hp]; exact sa)
    (by rw [hp]; exact iw (by decide)) (by rw [hp]; exact iw (by decide))
    (by rw [hp]; exact da.symm.sub_right (Offset.sub_base p (by decide)))
  have axc := Rej8.WP.constants ax cs (by cases w16 <;> rfl)
  refine WP.seq (WP.mono axc fun t ⟨qa,ct⟩ => ?_)
  have t19 : t.gpr .x19=p := (qa.keep.get .x19).trans hp
  have af : Frame [polyRegion a,⟨p+1680,16⟩] s.mem t.mem := by
    have h := qa.frame
    rw [hp] at h
    exact h
  have be : Rej8.EnvW w16 56 B (t.gpr .x19+904) b t := by
    rw [t19]
    apply eb.frame qa.keep.rd qa.keep.wr (qa.keep.get .x16) af
    · intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl
      · exact da.sub_left (Offset.sub_base p (by decide))
      · exact Offset.disjoint p (by decide) (by decide) (by decide)
    · intro mask hmask r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl
      · exact ea.tableDisj mask hmask
      · exact (dt mask hmask).sub_right (Offset.sub_base p (by decide))
  have bc : Rej8.Scalar.CoeffsW w16 t.mem b M := coeffs_frame cb hm af (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · exact dab.symm
    · exact db.symm.sub_right (Offset.sub_base p (by decide)))
  have bs : checkpointW w16 (t.gpr .x19+1696) b M t.mem := by
    rw [t19]
    exact checkpoint_frame sb af (by
      intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl
      · exact da.sub_left (Offset.sub_base p (by decide))
      · exact Offset.disjoint p (by decide) (by decide) (by decide))
  have bx := extra_ok t (buf:=904) (slot:=1696) (flag:=.x23) (by decide) (by decide) (by decide)
    (by decide) be ct hm bc bs
    (by rw [qa.keep.wr,t19]; exact iw (by decide))
    (by rw [qa.keep.wr,t19]; exact iw (by decide))
    (by rw [t19]; exact db.symm.sub_right (Offset.sub_base p (by decide)))
  refine WP.seq (WP.mono (Rej8.WP.constants bx ct (by cases w16 <;> rfl)) fun v ⟨bt,cv⟩ => ?_)
  have bf : Frame [polyRegion b,⟨p+1696,16⟩] t.mem v.mem := by
    have h := bt.frame
    rw [t19] at h
    exact h
  have ac : Rej8.Scalar.CoeffsW w16 v.mem a (sampleAfter L A 56) :=
    coeffs_frame qa.coeffs (sampleAfter_length_le hl A 56) bf (by
      intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl
      · exact dab
      · exact da.symm.sub_right (Offset.sub_base p (by decide)))
  have ast : checkpointW w16 (p+1680) a (sampleAfter L A 56) v.mem :=
    checkpoint_frame (by have h := qa.checkpoint; rw [hp] at h; exact h) bf (by
      intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl
      · exact db.sub_left (Offset.sub_base p (by decide))
      · exact Offset.disjoint p (by decide) (by decide) (by decide))
  have finish : WP isa (.block [.logic .and .x .x6 .x22 .x23]) v fun u =>
      Only [.x6] v u ∧ u.gpr .x6=v.gpr .x22 &&& v.gpr .x23 := by
    exact wp_and fun u hu eu => wp_nil ⟨hu,eu⟩
  refine WP.mono (WP.keepV (by rfl) finish) fun u ⟨⟨ku,eu⟩,vu⟩ => ?_
  refine ⟨((qa.keep.trans bt.keep).trans ku.keep).mono (by decide),?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [ku.mem]
    exact (af.mono (by intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr; rcases hr with rfl|rfl <;> simp [bothWrites])).trans
      (bf.mono (by intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr; rcases hr with rfl|rfl <;> simp [bothWrites]))
  · rw [ku.mem]; exact ac
  · rw [ku.mem]; exact bt.coeffs
  · rw [ku.mem]; exact ast
  · rw [ku.mem]; have h := bt.checkpoint; rw [t19] at h; exact h
  · rw [ku.get .x22,bt.keep.get .x22,qa.flagValue]
  · rw [ku.get .x23,bt.flagValue]
  · rw [eu,BitVec.toNat_and,bt.keep.get .x22,qa.flagValue,bt.flagValue]
    split_ifs <;> simp_all
  · exact ⟨by rw [vu]; exact cv.index,by rw [vu]; exact cv.mask,
      by simpa only [vu] using cv.q,by simpa only [vu] using cv.weights,by simpa only [vu] using cv.zero⟩

end VG.Proof.MlKem.AArch64.Paired
