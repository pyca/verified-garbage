module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.BuildFrame
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Omega

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG.Impl.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass

def buildSeedStore : List Instr := buildStoreCopy .x26 9 2800 0 ++
  buildStoreCopy .x26 9 3160 72 ++ buildStoreCopy .x26 9 424 144

theorem build_seed_store_source : (outerBlock007.take 55).drop 1=buildSeedStore := by lit_decide

theorem build_seed_store_ok {base table : Addr} {s : State}
    (hs : Scr s base 8192) (pt : PtrW s .x26 table 216)
    (apart : Region.Disjoint ⟨base,8192⟩ ⟨table,216⟩) :
    WP isa (.block (buildSeedStore)) s fun t =>
      wordsVal t.mem table 0 9=wordsVal s.mem base 2800 9 ∧
      wordsVal t.mem table 72 9=wordsVal s.mem base 3160 9 ∧
      wordsVal t.mem table 144 9=wordsVal s.mem base 424 9 ∧
      KeepRegs [.x1] s t ∧ Outside table 0 216 s.mem t.mem := by
  rw [buildSeedStore,WP.block_append_iff,WP.block_append_iff]
  refine WP.mono (build_store_copy_ok (by decide : Reg.x26≠.x1) apart 9 hs pt (a:=2800) (o:=0)
    (by decide) (by decide) (by decide) (by decide)) fun u ⟨xu,ku,fu⟩ => ?_
  have hu := hs.of_keepRegs ku (by decide)
  have pu := pt.of_keepRegs ku (by decide)
  have wu := (fu.mono (by decide) (by decide : 0+8*9≤0+216)).unch_far apart
  refine WP.mono (build_store_copy_ok (by decide : Reg.x26≠.x1) apart 9 hu pu
    (a:=3160) (o:=72) (by decide) (by decide) (by decide) (by decide)) fun v ⟨yv,kv,fv⟩ => ?_
  have hv := hu.of_keepRegs kv (by decide)
  have pv := pu.of_keepRegs kv (by decide)
  have wv := (fv.mono (by decide) (by decide : 72+8*9≤0+216)).unch_far apart
  refine WP.mono (build_store_copy_ok (by decide : Reg.x26≠.x1) apart 9 hv pv
    (a:=424) (o:=144) (by decide) (by decide) (by decide) (by decide)) fun t ⟨zt,kt,ft⟩ => ?_
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
