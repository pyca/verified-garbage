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
public import VerifiedGarbage.Proof.Ed448.Contract
import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.X448.AArch64.Base.Add
import VerifiedGarbage.Proof.X448.AArch64.Base.AddDefs
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Joint
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

def verifyEquationSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x4000 | _ => 0
  sp := 0x8000
  mem := Sparse.satMem
  rd := [⟨0x1000, 57⟩, ⟨0x2000, 114⟩, ⟨0x3000, 57⟩, ⟨0x100000, 8192⟩]
  wr := [⟨0x4000, 8192⟩]
  syms _ := 0x100000

private theorem byteMap_inj : ∀ {xs ys:List Byte},xs.map (·.toNat)=ys.map (·.toNat) → xs=ys
  | [],[],_ => rfl
  | a::xs,b::ys,h => by
    simp only [List.map_cons,List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1,byteMap_inj h.2]

private theorem bytes_drop (m:Mem) (p:Addr) :
    (Spec.Ed448.bytesAt m p 114).drop 57=Spec.Ed448.bytesAt m (p+BitVec.ofNat 64 57) 57:=by
  refine List.ext_getElem (by simp [Spec.Ed448.bytesAt]) fun i _ _ => ?_
  simp only [Spec.Ed448.bytesAt,List.getElem_drop,List.getElem_map,List.getElem_range]
  rw [Offset.add_add]

/-- The shared contract's precondition, from its facts. -/
theorem verifyEquation_spec_pre {s : State}
    (hrd : s.rd = [⟨s.gpr .x0, 57⟩, ⟨s.gpr .x1, 114⟩, ⟨s.gpr .x2, 57⟩,
      ⟨s.syms baseSym, 8 * baseWords.length⟩])
    (hw : s.wr = [⟨s.gpr .x3, 8192⟩])
    (h1 : Region.Disjoint ⟨s.gpr .x0, 57⟩ ⟨s.gpr .x3, 8192⟩)
    (h2 : Region.Disjoint ⟨s.gpr .x1, 114⟩ ⟨s.gpr .x3, 8192⟩)
    (h3 : Region.Disjoint ⟨s.gpr .x2, 57⟩ ⟨s.gpr .x3, 8192⟩)
    (f0 : (s.gpr .x0).toNat + 57 ≤ 2 ^ 64) (f1 : (s.gpr .x1).toNat + 114 ≤ 2 ^ 64)
    (f2 : (s.gpr .x2).toNat + 57 ≤ 2 ^ 64) (f3 : (s.gpr .x3).toNat + 8192 ≤ 2 ^ 64)
    (ht : BaseHeld s [⟨s.gpr .x3, 8192⟩])
    (hal : (s.syms baseSym).toNat % 64 = 0) :
    (Proof.Ed448.verifyEquationContract (AArch64.abi.withConsts baseConsts)).pre s := by
  sig_pre [Proof.Ed448.verifyEquationContract, Proof.Ed448.verifyEquationSig, Spec.Ed448.scratchWords,
    AArch64.abi, AArch64.argRegs, baseConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
    stackBelow]
  obtain ⟨held, fit, hdw⟩ := ht
  exact ⟨by rw [hrd]; rfl, held, fit, by rw [hw]; exact hdw, hal, by rw [hrd]; rfl, hw, h1, h2, h3, f0, f1,
    f2, f3⟩

theorem verifyEquation_sat :
    (Proof.Ed448.verifyEquationContract (AArch64.abi.withConsts baseConsts)).pre verifyEquationSat := by
  have hl := baseWords_length
  have held : ∀ i < baseWords.length, verifyEquationSat.mem.readW (verifyEquationSat.syms baseSym +
      BitVec.ofNat 64 (8 * i)) 64 = baseWords.getD i 0 := satMem_held
  refine verifyEquation_spec_pre (by rw [hl]; rfl) rfl (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide)) (by decide) (by decide)
    (by decide) (by decide) ⟨held, ?_, ?_⟩ (by decide)
  all_goals rw [hl]
  · decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r rfl; exact Region.disjoint_of_sep (by decide)

theorem verifyEquation_implies :
    verifyEquationLocal.Implies (Proof.Ed448.verifyEquationContract (AArch64.abi.withConsts baseConsts)) where
  pre s h := by
    sig_pre [Proof.Ed448.verifyEquationContract, Proof.Ed448.verifyEquationSig, Spec.Ed448.scratchWords,
      AArch64.abi, AArch64.argRegs, baseConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
      stackBelow] at h
    obtain ⟨hd, hheld, hfit, hdw, -, ht, hw, h1, h2, h3, -, -, -, h4⟩ := h
    refine ⟨?_, hw, h1, h2, h3, h4, hheld, hfit, by rw [hw] at hdw; exact hdw⟩
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
  post s t _ h := by
    sig_post [Proof.Ed448.verifyEquationContract, Proof.Ed448.verifyEquationSig,
      Spec.Ed448.scratchWords, AArch64.abi, AArch64.argRegs, baseConsts_eq, Abi.withConsts]
    have h' : t.gpr .x0 = _ := h
    rw [h']
    generalize Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt s.mem (s.gpr .x0) 57)
      (Spec.Ed448.bytesAt s.mem (s.gpr .x1) 114) (Spec.Ed448.bytesAt s.mem (s.gpr .x2) 57) = b
    cases b <;> rfl
  pub s t _ _ h := by
    sig_pub [Proof.Ed448.verifyEquationContract, Proof.Ed448.verifyEquationSig,
      Spec.Ed448.scratchWords, AArch64.abi, AArch64.argRegs, baseConsts_eq, Abi.withConsts] at h
    obtain ⟨sp,hsy,bytes,pk,sig,ch,base⟩:=h
    have hb:=byteMap_inj bytes
    obtain ⟨first,last⟩:=List.append_inj' hb (by simp [Spec.Ed448.bytesAt])
    obtain ⟨_,middle⟩:=List.append_inj' first (by simp [Spec.Ed448.bytesAt])
    refine ⟨sp,pk,sig,ch,base,hsy,?_,congrArg Spec.Ed448.decodeLE last⟩
    have hd:=congrArg (fun bs => Spec.Ed448.decodeLE (bs.drop 57)) middle
    rw [bytes_drop,bytes_drop] at hd
    exact hd
  sat := ⟨verifyEquationSat, verifyEquation_sat⟩

theorem verified_eqOk (hR:VG.Proof.Ed448.RecoverOk) : EqOk:=equation_eqOk affine_ok hR

theorem verifyEquation_verified (hR:VG.Proof.Ed448.RecoverOk) :
    Verified AArch64.target VG.Impl.Ed448.AArch64.Sparse.verifyEquation
      (Proof.Ed448.verifyEquationContract (AArch64.abi.withConsts baseConsts)):=
  Verified.of_correct (equation_ok affine_ok hR) (equation_ct affine_ok hR) verifyEquation_implies

end VG.Proof.Ed448.AArch64.Sparse
