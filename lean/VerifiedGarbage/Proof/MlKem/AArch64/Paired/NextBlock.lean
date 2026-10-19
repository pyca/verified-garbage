module
public import VerifiedGarbage.Proof.MlKem.AArch64.Lay
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.SqueezeBlock
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Probe

import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Constants
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cover
import VerifiedGarbage.Proof.Framework.Offset

/-! # The next paired SHAKE128 block and rejection-constant refresh -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.Sha3.AArch64.Neon

theorem pair_frame {m m' : Mem} {p : Addr} {A B : Spec.Sha3.State} {rs : List Region}
    (h : PairAt m p A B) (hf : Frame rs m m') (hd : ∀r∈rs,(pairR p).Disjoint r) :
    PairAt m' p A B := by
  intro i hi
  rw [hf.read (pair_contains p hi) hd (by decide)]
  exact h i hi

theorem rate_frame {m m' : Mem} {p : Addr} {A : Spec.Sha3.State} {rs : List Region}
    (h : Rate21 m p A) (hf : Frame rs m m') (hd : ∀r∈rs,(rateR21 p).Disjoint r) :
    Rate21 m' p A := by
  intro i hi
  have hc : (rateR21 p).Contains (outAddr p i) 8 :=
    Offset.contains_base p (by omega) (by omega)
  rw [hf.readW hc hd (by decide)]
  exact h i hi

def nextBlock : Prog isa := .seq (.block [.addImm .x .x20 .x19 400,.addImm .x .x21 .x19 904])
  (.seq (Impl.Sha3.AArch64.Neon.X2.call true .x19 .x19 1536)
    (.block (Impl.Sha3.AArch64.Neon.X2.squeeze 21 .x19 .x20 .x21 ++ Impl.MlKem.AArch64.Rej8.rejConsts)))

def nextWrites (p : Addr) : List Region :=
  [pairR p,rateR21 (p+400),rateR21 (p+904),X2.callR (p+1536),⟨p+1408,8⟩]

def nextRegs : List Reg := [.x0,.x1,.x6,.x7,.x9,.x16,.x17,.x20,.x21]

theorem nextBlock_ok {s : State} {p : Addr} {A B : Spec.Sha3.State}
    (hp : s.gpr .x19=p) (hc : Covers [⟨p,2048⟩] s.wr) (pair : PairAt s.mem p A B) :
    WP isa nextBlock s fun u => Keep nextRegs s u ∧ Frame [⟨p,2048⟩] s.mem u.mem ∧
      Frame (nextWrites p) s.mem u.mem ∧ u.gpr .x19=p ∧ PairAt u.mem p (Spec.Sha3.keccakF A) (Spec.Sha3.keccakF B) ∧
      Rate21 u.mem (p+400) (Spec.Sha3.keccakF A) ∧ Rate21 u.mem (p+904) (Spec.Sha3.keccakF B) ∧
      Rej8.Constants u ∧ u.gpr .x16=u.syms "VG_MLKEM_REJ_SHUFFLE" := by
  have iw {o l : Nat} (h : o+l≤2048) := Noise.inScratch hc h (by decide)
  have prep : WP isa (.block [.addImm .x .x20 .x19 400,.addImm .x .x21 .x19 904]) s fun a =>
      Only [.x20,.x21] s a ∧ a.gpr .x20=p+400 ∧ a.gpr .x21=p+904 := by
    refine wp_addImm (by decide) fun a ha ea => wp_addImm (by decide) fun b hb eb => wp_nil ?_
    exact ⟨(ha.trans hb).mono (by decide),by rw [hb.get .x20,ea,hp]; rfl,by rw [eb,ha.get .x19,hp]; rfl⟩
  refine WP.seq (WP.mono prep fun a ⟨ha,a20,a21⟩ => ?_)
  have asq := squeezeBlock_ok (hp := (ha.get .x19).trans hp) (ha := a20) (hb := a21)
    (hw := by rw [ha.get .x19,hp]) (hp1 := by decide) (hp6 := by decide) (hp7 := by decide)
    (ha6 := by decide) (ha7 := by decide) (hb6 := by decide) (hb7 := by decide)
    (hpc := by decide) (hac := by decide) (hbc := by decide)
    (by rw [ha.mem]; exact pair)
    (fun i hi => by rw [ha.rd,ha.wr]; exact in_rd_wr (iw (by omega)))
    (fun i hi => by
      rw [ha.wr]
      change InRegions s.wr (p+BitVec.ofNat 64 400+BitVec.ofNat 64 (8*i)) 8
      rw [BitVec.add_assoc,←BitVec.ofNat_add]
      exact iw (by omega))
    (fun i hi => by
      rw [ha.wr]
      change InRegions s.wr (p+BitVec.ofNat 64 904+BitVec.ofNat 64 (8*i)) 8
      rw [BitVec.add_assoc,←BitVec.ofNat_add]
      exact iw (by omega))
    (Offset.disjoint p (by decide) (by decide) (by decide))
    (Offset.base_disjoint p (by decide) (by decide))
    (Offset.base_disjoint p (by decide) (by decide))
    (Offset.base_disjoint p (by decide) (by decide))
    (by
      rw [ha.wr]
      exact Noise.coversTwo
        (by simpa only [BitVec.add_zero,pairR] using Noise.coversScratch (off := 0) (len := 400) hc (by decide))
        (Noise.coversScratch (off := 1536) (len := 136) hc (by decide)))
  refine WP.seq (WP.mono (WP.seq_iff.mp asq) fun c hsq => ?_)
  apply WP.block_append_iff.mpr
  refine WP.mono hsq fun b ⟨hb,pb,ba,bb,fb,vb⟩ => ?_
  have kb : Keep blockRegs a b := ⟨hb.gpr,hb.rd,hb.wr,hb.sp,vb⟩
  have b19 : b.gpr .x19=p := (hb.gpr .x19 (by decide)).trans ((ha.get .x19).trans hp)
  have fb' : Frame [⟨p,2048⟩] s.mem b.mem := by
    rw [←ha.mem]
    exact fb.sub (by
      intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl|rfl
      · exact ⟨⟨p,2048⟩,by simp,Region.sub_prefix (by decide : 400≤2048)⟩
      · exact ⟨⟨p,2048⟩,by simp,Offset.sub_base p (by decide)⟩
      · exact ⟨⟨p,2048⟩,by simp,Offset.sub_base p (by decide)⟩
      · exact ⟨⟨p,2048⟩,by simp,Offset.sub_base p (by decide)⟩)
  refine WP.mono (Rej8.constants_ok b (by rw [kb.wr,ha.wr,b19]; exact iw (by decide))) fun u ⟨ku,cu,mu,tu⟩ => ?_
  have fu : Frame [⟨p+1408,8⟩] b.mem u.mem := by
    rw [mu,b19]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨((ha.keep.trans kb).trans ku).mono (by decide),?_,?_,by rw [ku.get .x19,b19],?_,?_,?_,cu,tu⟩
  · exact fb'.trans (fu.sub (by intro r hr; rw [List.mem_singleton.mp hr]; exact
      ⟨⟨p,2048⟩,by simp,Offset.sub_base p (by decide)⟩))
  · have fb0 : Frame (nextWrites p) s.mem b.mem := by
      rw [←ha.mem]
      exact fb.mono (by
        intro r hr
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl|rfl|rfl <;> simp [nextWrites])
    exact fb0.trans (fu.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; simp [nextWrites]))
  · exact pair_frame pb fu (by intro r hr; rw [List.mem_singleton.mp hr]; exact Offset.base_disjoint p (by decide) (by decide))
  · exact rate_frame ba fu (by intro r hr; rw [List.mem_singleton.mp hr]; exact Offset.disjoint p (by decide) (by decide) (by decide))
  · exact rate_frame bb fu (by intro r hr; rw [List.mem_singleton.mp hr]; exact Offset.disjoint p (by decide) (by decide) (by decide))

end VG.Proof.MlKem.AArch64.Paired
