module

public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Local
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Correct
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Timing
import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Proof.Ed448.WnafWide.Limit
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.X448.AArch64.Main

/-! The sparse equation meets the local correctness, ABI and timing interface. -/

@[expose] public section

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
