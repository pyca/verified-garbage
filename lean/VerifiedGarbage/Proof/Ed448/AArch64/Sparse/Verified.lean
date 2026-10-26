module

import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.LocalCorrect
import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Affine
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
public import Mathlib.Algebra.Group.Nat.Defs
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Correct
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Local
public import VerifiedGarbage.Proof.Ed448.Ref

/-! Correctness and timing against the unchanged reviewed Ed448 equation contract. -/

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
    (Spec.Ed448.verifyEquationContract (AArch64.abi.withConsts baseConsts)).pre s := by
  sig_pre [Spec.Ed448.verifyEquationContract, Spec.Ed448.verifyEquationSig, Spec.Ed448.scratchWords,
    AArch64.abi, AArch64.argRegs, baseConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
    stackBelow]
  obtain ⟨held, fit, hdw⟩ := ht
  exact ⟨by rw [hrd]; rfl, held, fit, by rw [hw]; exact hdw, hal, by rw [hrd]; rfl, hw, h1, h2, h3, f0, f1,
    f2, f3⟩

theorem verifyEquation_sat :
    (Spec.Ed448.verifyEquationContract (AArch64.abi.withConsts baseConsts)).pre verifyEquationSat := by
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
    verifyEquationLocal.Implies (Spec.Ed448.verifyEquationContract (AArch64.abi.withConsts baseConsts)) where
  pre s h := by
    sig_pre [Spec.Ed448.verifyEquationContract, Spec.Ed448.verifyEquationSig, Spec.Ed448.scratchWords,
      AArch64.abi, AArch64.argRegs, baseConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
      stackBelow] at h
    obtain ⟨hd, hheld, hfit, hdw, -, ht, hw, h1, h2, h3, -, -, -, h4⟩ := h
    refine ⟨?_, hw, h1, h2, h3, h4, hheld, hfit, by rw [hw] at hdw; exact hdw⟩
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
  post s t _ h := by
    sig_post [Spec.Ed448.verifyEquationContract, Spec.Ed448.verifyEquationSig,
      Spec.Ed448.scratchWords, AArch64.abi, AArch64.argRegs, baseConsts_eq, Abi.withConsts]
    have h' : t.gpr .x0 = _ := h
    rw [h']
    generalize Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt s.mem (s.gpr .x0) 57)
      (Spec.Ed448.bytesAt s.mem (s.gpr .x1) 114) (Spec.Ed448.bytesAt s.mem (s.gpr .x2) 57) = b
    cases b <;> rfl
  pub s t _ _ h := by
    sig_pub [Spec.Ed448.verifyEquationContract, Spec.Ed448.verifyEquationSig,
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
      (Spec.Ed448.verifyEquationContract (AArch64.abi.withConsts baseConsts)):=
  Verified.of_correct (equation_ok affine_ok hR) (equation_ct affine_ok hR) verifyEquation_implies

end VG.Proof.Ed448.AArch64.Sparse
