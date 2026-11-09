module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Correct
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Local
public import VerifiedGarbage.Proof.Ed448.Ref

import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Algebra.Group.Nat.Defs
import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Timing
import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Proof.Ed448.WnafWide.Limit
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.X448.AArch64.Main
import VerifiedGarbage.Impl.Ed448.AArch64.Sparse
import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.AffineSpec
import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.X448.AArch64.Base.Add
import VerifiedGarbage.Proof.X448.AArch64.Base.AddDefs
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Joint
public import VerifiedGarbage.Spec.Ed448.Contract
/-! Correctness and timing against the unchanged reviewed Ed448 equation contract. -/

-- Formerly `VerifiedGarbage/Proof/Ed448/AArch64/Sparse/LocalCorrect.lean`, which only this module imported.
section

/-! The sparse equation meets the local correctness, ABI and timing interface. -/

section

namespace VG.Proof.Ed448.AArch64.Sparse
open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Proof.X448.AArch64 (ofs far)
open VG.Impl.Ed448.WnafWide (scalarLimit)

private theorem prepare_pre {s:State} (h:verifyEquationLocal.pre s) :
    PrepareInput (s.gpr .x3) (signatureScalar s) (challengeScalar s) s:=by
  obtain ⟨hr,hw,hpk,hsg,hch,hn,hb⟩:=h
  refine ⟨rfl,by rw [hw];simp,hn,?_,?_,?_,?_,?_,?_,held_baseTable hb ?_,rfl,rfl⟩
  · intro i hi
    exact ⟨⟨s.gpr .x0,57⟩,by rw [hr];simp,Offset.contains_base _ hi (by omega)⟩
  · intro i hi
    exact ⟨⟨s.gpr .x1,114⟩,by rw [hr];simp,Offset.contains_base _ hi (by omega)⟩
  · intro i hi
    exact ⟨⟨s.gpr .x2,57⟩,by rw [hr];simp,Offset.contains_base _ hi (by omega)⟩
  · intro i hi;exact far hpk hi (by decide)
  · intro i hi;exact far hsg hi (by decide)
  · intro i hi;exact far hch hi (by decide)
  · rw [hr,baseWords_length];simp

private theorem scalar_bound (m:Mem) (p:Addr) :
    Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m p 57)<scalarLimit:=by
  have h:=VG.Proof.Ed448.decodeLE_lt' (Spec.Ed448.bytesAt m p 57)
  have hl:(Spec.Ed448.bytesAt m p 57).length=57:=by simp [Spec.Ed448.bytesAt]
  rwa [hl,←WnafWide.scalarLimit_eq] at h

theorem equation_ok (hA:AffineOk) (hR:VG.Proof.Ed448.RecoverOk) (s:State) (h:verifyEquationLocal.pre s) :
    ∃ tr t,Exec isa VG.Impl.Ed448.AArch64.Sparse.verifyEquation s tr t ∧
      abiPreserved s t ∧ verifyEquationLocal.post s t:=by
  have p:=prepare_pre h
  obtain ⟨tr,t,e,hg,hv,hr⟩:=correct hA hR p.h3 p.hw p.hn p.rpk p.rsg p.rch p.fpk p.fsg p.fch p.bt
  exact ⟨tr,t,e,⟨hg,Exec.sp e,hv⟩,hr⟩

theorem equation_ct (hA:AffineOk) (hR:VG.Proof.Ed448.RecoverOk) :
    ConstantTime isa verifyEquationLocal.pre verifyEquationLocal.pub VG.Impl.Ed448.AArch64.Sparse.verifyEquation:=by
  intro s t tr tr' u v hs ht hp es et
  obtain ⟨hsp,h0,h1,h2,h3,hsy,hS,hK⟩:=hp
  have hd:=verifyEquation_ct hA hR (s.gpr .x3) (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) s.sp
    (s.syms baseSym) (signatureScalar s) (challengeScalar s)
    (scalar_bound _ _) (scalar_bound _ _)
  apply (hd s t tr tr' u v ?_ es et).1
  refine ⟨⟨⟨prepare_pre hs,rfl,rfl,rfl⟩,rfl,rfl⟩,⟨?_,hsp.symm,hsy.symm⟩⟩
  rw [h3,hS,hK]
  exact ⟨prepare_pre ht,h0.symm,h1.symm,h2.symm⟩

theorem equation_eqOk (hA:AffineOk) (hR:VG.Proof.Ed448.RecoverOk) : EqOk:=⟨equation_ok hA hR,equation_ct hA hR⟩

end VG.Proof.Ed448.AArch64.Sparse
end

end

-- Formerly `VerifiedGarbage/Proof/Ed448/AArch64/Sparse/Affine.lean`, which only this module imported.
section

/-! Inline affine addition with the existing verified interleaved field formula. -/

section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.X448.AArch64 (slot ACC)
open VG.Impl.X448.AArch64.Fast (saved)
open VG.Proof.X448.AArch64 (Scr Keeps Outside Outside2 ofs)
open VG.Proof.X448.AArch64.Weak (Index)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd Same fclob indeps_ops_mul2)
open VG.Proof.X448.AArch64.Base (affEnv)
open VG.Proof.Curve448.AArch64.Fast (Mb)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

private theorem mask_ok {s:State} {base:Addr} (hs:Scr s base) :
    WP isa (.block [.movz .x .x12 0xffff 0,.movk .x .x12 0x0fff 1]) s fun t =>
      Keeps [] s t ∧ t.mem=s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,State.read,Size.bits,Nat.reduceMul,
    Nat.reduceLT,ite_true,RegUpd.gpr_write,BitVec.setWidth_eq,Option.some.injEq,exists_eq_left']
  refine ⟨⟨fun r _ => ?_,rfl,rfl⟩,rfl⟩
  by_cases h:r= .x12
  · subst r
    simp only [RegUpd.gpr_write,ite_true,hs.mask]
    rfl
  · simp only [RegUpd.gpr_write,h,ite_false]

theorem addAffine_ok {s:State} {base:Addr} (hs:Scr s base) (hb:BEnv s.mem base)
    (hz:Bnd Mb s.mem base (slot 19)) :
    WP isa VG.Impl.Ed448.AArch64.Sparse.addAffine s fun t =>
      AffineKeep base s t ∧ BEnv t.mem base ∧
      Same base (VG.Proof.X448.AArch64.Base.temps++[5,3,4]) s.mem t.mem ∧
      Bnd Mb t.mem base (slot 3) ∧ Bnd Mb t.mem base (slot 4) ∧ Bnd Mb t.mem base (slot 5) ∧
      EV t.mem base=affEnv 3 4 5 6 7 (EV s.mem base) := by
  unfold VG.Impl.Ed448.AArch64.Sparse.addAffine
  rw [WP.seq_iff,List.append_assoc,WP.block_append_iff]
  refine WP.mono (save_ok hs) fun a ⟨sv,fo,ag,ar,aw⟩ => ?_
  have ak:Keeps [] s a:=⟨fun _ _ => congrFun ag _,ar,aw⟩
  have ha:Scr a base:=hs.of_keeps ak (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mask_ok ha) fun b ⟨bk,bm⟩ => ?_
  have hb':Scr b base:=ha.of_keeps bk (by decide)
  have bb:BEnv b.mem base:=by rw [bm];exact save_bounds fo hb
  have bz:Bnd Mb b.mem base (slot 19):=by
    rw [bm]
    intro j hj
    rw [fo.limbs (Or.inl (by decide)) (by decide) (by omega)]
    exact hz j hj
  refine WP.mono (VG.Proof.X448.AArch64.Base.addAffine_ok 3 4 5 6 7
    (by decide) (by decide) (by decide) hb' bb bz
    (indeps_ops_mul2 _ _ _ _ _ _ _ (by decide +kernel))
    (indeps_ops_mul2 _ _ _ _ _ _ _ (by decide +kernel))
    (indeps_ops_mul2 _ _ _ _ _ _ _ (by decide +kernel))
    (indeps_ops_mul2 _ _ _ _ _ _ _ (by decide +kernel)))
    fun c ⟨ck,cb,cs,cx,cy,cz,ce⟩ => ?_
  have hsv:Saved base s.gpr c.mem:=fun i hi => by
    rw [ck.mem.word (Or.inr (by simp only [GSAVE];omega)) (Or.inr (by simp only [ACC,GSAVE];omega)) (by simp only [GSAVE];omega),bm]
    exact sv i hi
  refine WP.mono (restore_ok (ck.scr hb') hsv) fun t ⟨tg,tm,tk⟩ => ?_
  refine ⟨⟨?_,tg,?_⟩,?_,?_,?_,?_,?_,?_⟩
  · exact ((ak.mono (by decide)).trans (bk.mono (by decide))).trans
      (ck.regs.trans (tk.mono (by decide)))
  · intro x hx hy hz
    rw [tm,ck.mem x hx hy,bm,fo x hz]
  · rw [tm]
    exact cb
  · intro i hi j hj
    rw [tm,cs i hi j hj,bm]
    have h:=i.isLt
    exact fo.limbs (Or.inl (by simp only [slot,GSAVE];omega)) (by simp only [slot];omega) (by omega)
  · rw [tm]
    exact cx
  · rw [tm]
    exact cy
  · rw [tm]
    exact cz
  · rw [tm,ce,bm,save_env fo]

theorem affine_ok : AffineOk:=⟨fun hs hb hz => addAffine_ok hs hb hz⟩

end VG.Proof.Ed448.AArch64.Sparse
end

end

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse
open VG VG.AArch64 VG.Impl.Ed448.AArch64.Sparse

theorem verified_eqOk (hR:VG.Proof.Ed448.RecoverOk) : EqOk:=equation_eqOk affine_ok hR

end VG.Proof.Ed448.AArch64.Sparse
