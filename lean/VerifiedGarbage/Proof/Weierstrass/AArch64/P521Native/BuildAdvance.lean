module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.BuildFrame
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Omega

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass

theorem build_store_point_split : buildStoreCopy .x20 27 1288 0=
    buildStoreCopy .x20 9 1288 0 ++ buildStoreCopy .x20 9 1360 72 ++
      buildStoreCopy .x20 9 1432 144 := by lit_decide

theorem build_store_point_ok {base table : Addr} {s : State}
    (hs : Scr s base 8192) (pt : PtrW s .x20 table 216)
    (apart : Region.Disjoint ⟨base,8192⟩ ⟨table,216⟩) :
    WP isa (.block (buildStoreCopy .x20 27 1288 0)) s fun t =>
      wordsVal t.mem table 0 9=wordsVal s.mem base 1288 9 ∧
      wordsVal t.mem table 72 9=wordsVal s.mem base 1360 9 ∧
      wordsVal t.mem table 144 9=wordsVal s.mem base 1432 9 ∧
      KeepRegs [.x1] s t ∧ Outside table 0 216 s.mem t.mem := by
  rw [build_store_point_split,WP.block_append_iff,WP.block_append_iff]
  refine WP.mono (build_store_copy_ok (by decide : Reg.x20≠.x1) apart 9 hs pt
    (by decide) (by decide) (by decide) (by decide)) fun u ⟨xu,ku,fu⟩ => ?_
  have hu := hs.of_keepRegs ku (by decide)
  have pu := pt.of_keepRegs ku (by decide)
  have wu := (fu.mono (by decide) (by decide : 0+8*9≤0+216)).unch_far apart
  refine WP.mono (build_store_copy_ok (by decide : Reg.x20≠.x1) apart 9 hu pu
    (a:=1360) (o:=72) (by decide) (by decide) (by decide) (by decide)) fun v ⟨yv,kv,fv⟩ => ?_
  have hv := hu.of_keepRegs kv (by decide)
  have pv := pu.of_keepRegs kv (by decide)
  have wv := (fv.mono (by decide) (by decide : 72+8*9≤0+216)).unch_far apart
  refine WP.mono (build_store_copy_ok (by decide : Reg.x20≠.x1) apart 9 hv pv
    (a:=1432) (o:=144) (by decide) (by decide) (by decide) (by decide)) fun t ⟨zt,kt,ft⟩ => ?_
  refine ⟨?_,?_,?_,ku.trans (kv.trans kt),?_⟩
  · rw [ft.wordsVal (Or.inl (by decide)) (by decide),fv.wordsVal (Or.inl (by decide)) (by decide),xu]
  · rw [ft.wordsVal (Or.inl (by decide)) (by decide),yv]
    exact wu.wordsVal (by intro w hw; rw [List.mem_singleton.mp hw]; exact Or.inl (by decide)) (by decide)
  · rw [zt,wv.wordsVal (by intro w hw; rw [List.mem_singleton.mp hw]; exact Or.inl (by decide)) (by decide)]
    exact wu.wordsVal (by intro w hw; rw [List.mem_singleton.mp hw]; exact Or.inl (by decide)) (by decide)
  · exact (fu.mono (by decide) (by decide : 0+72≤0+216)).trans
      ((fv.mono (by decide) (by decide : 72+72≤0+216)).trans
        (ft.mono (by decide) (by decide : 144+72≤0+216)))

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass

def buildAdvance : Prog isa := .seq (.block (buildStoreCopy .x20 27 1288 0)) (.block buildCopyPoint)

theorem build_advance_ok {base table : Addr} {s : State}
    (hs : Scr s base 8192) (pt : PtrW s .x20 table 216)
    (apart : Region.Disjoint ⟨base,8192⟩ ⟨table,216⟩) :
    WP isa buildAdvance s fun t =>
      (∀c,c<3 → wordsVal t.mem table (72*c) 9=wordsVal s.mem base (1288+72*c) 9) ∧
      (∀c,c<3 → wordsVal t.mem base (1504+72*c) 9=wordsVal s.mem base (1288+72*c) 9) ∧
      KeepRegs [.x1] s t ∧
      (∀x,8192≤ofs base x → (ofs table x<0 ∨ 216≤ofs table x) → t.mem x=s.mem x) ∧
      Unch base [(1504,72),(1576,72),(1648,72),(8192,2^64)] s.mem t.mem := by
  rw [buildAdvance,WP.seq_iff]
  refine WP.mono (build_store_point_ok hs pt apart) fun u ⟨xu,yu,zu,ku,fu⟩ => ?_
  have hu := hs.of_keepRegs ku (by decide)
  have wu := fu.unch_far apart
  refine WP.mono (build_copy_point_ok hu) fun t ⟨xt,yt,zt,kt,ft⟩ => ?_
  have tableKept (d : Nat) (hd : d+72≤216) : wordsVal t.mem table d 9=wordsVal u.mem table d 9 := by
    have oa : Outside base 0 8192 u.mem t.mem := ft.outside (by
      intro w hw; simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl|rfl|rfl <;> decide)
    have tableFrame := oa.unch_far apart.symm
    exact tableFrame.wordsVal
      (by intro w hw; rw [List.mem_singleton.mp hw]; exact Or.inl (by omega_arith)) (by omega_arith)
  refine ⟨?_,?_,ku.trans kt,?_,?_⟩
  · intro c hc
    have cases : c=0 ∨ c=1 ∨ c=2 := by omega_arith
    rcases cases with rfl|rfl|rfl
    · rw [tableKept 0 (by decide)]; exact xu
    · rw [tableKept 72 (by decide)]; exact yu
    · rw [tableKept 144 (by decide)]; exact zu
  · intro c hc
    have cases : c=0 ∨ c=1 ∨ c=2 := by omega_arith
    rcases cases with rfl|rfl|rfl
    all_goals try simp only [Nat.mul_zero,Nat.add_zero,Nat.mul_one]
    · rw [xt]; exact wu.wordsVal (by intro w hw; rw [List.mem_singleton.mp hw]; exact Or.inl (by decide)) (by decide)
    · rw [yt]; exact wu.wordsVal (by intro w hw; rw [List.mem_singleton.mp hw]; exact Or.inl (by decide)) (by decide)
    · rw [zt]; exact wu.wordsVal (by intro w hw; rw [List.mem_singleton.mp hw]; exact Or.inl (by decide)) (by decide)
  · intro x hx ht
    exact (ft.far (by
      intro w hw
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl|rfl|rfl <;> simp only <;> omega_arith)).trans (fu x ht)
  · exact (wu.trans ft).mono (by
      intro w hw
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw ⊢
      rcases hw with rfl|rfl|rfl|rfl <;> simp)

end VG.Proof.Weierstrass.AArch64.P521Native
