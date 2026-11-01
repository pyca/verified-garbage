module

public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Top3
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Top1
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract

/-! # DSA's probable-prime test on ARMv7: the body's start (`in_c`) -/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Impl.Dsa.Arm.ProbablePrime (keyOff keyWords layout)
open VG.Impl.RsaKeyGen.Arm.Candidate (aoR aoRl aoP aoS aoSl aoEl aoPl foL foUsed)

section
variable {bits : Nat} {s t : State}

theorem rS_eq (h : CIn bits s) :
    (mkP bits s).rS = ⟨State.addr (s.gpr .r0) + BitVec.ofNat 64 keyOff, keyWords bits * 8⟩ := by
  have := h.fw; have := h.size
  have : 0 < keyWords bits := by simp [keyWords, Spec.Rsa.scratchWords]
  show (⟨State.addr (s.gpr .r0 + BitVec.ofNat 32 keyOff), keyWords bits * 8⟩ : Region) = _
  rw [addr_add (by simp only [keyOff] at *; omega)]

theorem rC_eq (h : CIn bits s) : (mkP bits s).rC = ⟨fB s + BitVec.ofNat 64 0, 56⟩ := by
  show (⟨State.addr (s.sp - BitVec.ofNat 32 88 - BitVec.ofNat 32 56), 56⟩ : Region) = _
  rw [BitVec.sub_sub, ← BitVec.ofNat_add, below_eq h.spLo (a := 88 + 56) (by decide)]

theorem rF_eq (h : CIn bits s) : (mkP bits s).rF = ⟨fB s + BitVec.ofNat 64 56, 88⟩ := by
  show (⟨State.addr (mkP bits s).sp, 88⟩ : Region) = _; rw [spP h]

theorem rFr_eq (h : CIn bits s) : (mkP bits s).rFr = ⟨fB s + BitVec.ofNat 64 56, 56⟩ := by
  show (⟨State.addr (mkP bits s).sp, 56⟩ : Region) = _; rw [spP h]

/-- The body's start. -/
theorem in_c (hb : Bits bits) (h : CIn bits s) (o : PreOut bits s t) : In (mkP bits s) (sx bits s t) := by
  have spLo := h.spLo; have spHi := h.spHi; have fw := h.fw; have size := h.size
  obtain ⟨k1, k2, hlen, hkw, hchk⟩ := hb.facts
  simp only [keyOff] at size
  have kpos : 0 < keyWords bits := by simp [keyWords, Spec.Rsa.scratchWords]
  have hL : (mkP bits s).len = Impl.Dsa.Arm.ProbablePrime.len bits := rfl
  have spN : (mkP bits s).sp.toNat = s.sp.toNat - 88 := sub_toNat' (by omega_arith)
  have subS : Region.Sub (mkP bits s).rS (cW s) := by
    rw [rS_eq h]; exact Offset.sub_base _ (by simp only [keyOff]; omega_arith)
  have subCd : Region.Sub (mkP bits s).rCd (cW s) := Region.sub_prefix (by
    show Impl.Dsa.Arm.ProbablePrime.len bits ≤ _; omega_arith)
  have subF : Region.Sub (mkP bits s).rF (cF s) := by rw [rF_eq h]; exact cF_sub (by decide)
  have subFr : Region.Sub (mkP bits s).rFr (cF s) := by rw [rFr_eq h]; exact cF_sub (by decide)
  have subC : Region.Sub (mkP bits s).rC (cF s) := by rw [rC_eq h]; exact cF_sub (by decide)
  have rdm : ∀ r ∈ cCd bits s :: s.rd, r ∈ (sx bits s t).rd ++ (sx bits s t).wr := fun r hr =>
    List.mem_append_left _ hr
  have M : (sx bits s t).mem = (pcPushed t).mem := rfl
  have tsp : t.sp - BitVec.ofNat 32 56 = (mkP bits s).sp := pushed_sp o
  have saved := pc_push_saved t (by
    rw [o.rest.sp]; show 56 ≤ (s.sp - BitVec.ofNat 32 32).toNat
    rw [sub_toNat' (by omega_arith)]; omega_arith)
  rw [show (t.sp - 56 : BitVec 32) = (mkP bits s).sp from tsp] at saved
  have bCd := bytesT h o (R := (mkP bits s).rCd) (h.FW.sub_right subCd) (by
    show Impl.Dsa.Arm.ProbablePrime.len bits ≤ _; omega_arith)
  have bR := bytesT h o (R := cR s) h.FR (by have := h.fr; show (s.gpr .r3).toNat ≤ _; omega_arith)
  have hcv : cv (mkP bits s) (sx bits s t) =
      Proof.Dsa.ProbablePrime.candidateAt (layout bits) s.mem (State.addr (s.gpr .r0)) := by
    show Spec.Rsa.os2ip (Spec.Rsa.bytesAt (pcPushed t).mem (mkP bits s).rCd.base (mkP bits s).rCd.len) = _
    rw [bCd]
    show _ = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 0) (bits / 8))
    rw [BitVec.add_zero]; rfl
  refine ⟨pushed_sp o, by omega_arith, by omega_arith, rfl, ⟨cR s, rdm _ (List.mem_cons_of_mem _ (by rw [h.rd]; exact List.mem_cons_self)), Region.contains_self _ _⟩,
    ⟨cCd bits s, rdm _ List.mem_cons_self, Region.contains_self _ _⟩,
    ⟨(mkP bits s).rAl, List.mem_append_right _ (by simp [xRegs]), ?_⟩, hb, rfl, k1, k2, Nat.mul_mod_right _ _,
    by show Spec.Rsa.scratchWords (8 * Impl.Dsa.Arm.ProbablePrime.words bits) ≤ keyWords bits; rw [hkw], h.fu, h.fr, by show (s.gpr .r0).toNat + Impl.Dsa.Arm.ProbablePrime.len bits ≤ _; omega_arith,
    BitVec.isLt _, ?_,
    h.wU.sub_left subS, h.wR.sub_left subS, ?_, (h.FW.symm.sub_left subS).sub_right subF,
    (h.FW.symm.sub_left subS).sub_right subC, h.rU.symm, h.wU.symm.sub_right subCd, h.FU.symm.sub_right subF,
    h.FU.symm.sub_right subC, h.FR.symm.sub_right subFr, h.FR.symm.sub_right subC,
    (h.FW.symm.sub_left subCd).sub_right subFr, (h.FW.symm.sub_left subCd).sub_right subC,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [hcv]; exact h.odd, by rw [hcv]; exact h.bl, hcv, bR⟩
  · show (⟨State.addr ((mkP bits s).sp + BitVec.ofNat 32 56), 32⟩ : Region).Contains
      (State.addr (mkP bits s).sp + BitVec.ofNat 64 56) 32
    rw [addr_add (by omega_arith)]; exact Region.contains_self _ _
  · show (s.gpr .r0 + BitVec.ofNat 32 keyOff).toNat + keyWords bits * 8 ≤ _
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := keyOff) (by simp only [keyOff]; omega_arith),
      Nat.mod_eq_of_lt (by simp only [keyOff]; omega_arith)]
    simp only [keyOff]; omega_arith
  · rw [rS_eq h]; exact Offset.disjoint_base _ (by simp only [keyOff]; omega_arith) (by simp only [keyOff]; omega_arith)
  · show (pcPushed t).mem.readW (State.addr (mkP bits s).sp + BitVec.ofNat 64 4) 32 = _
    rw [saved (.r1, 4) (by simp [pcAllSaved]), o.r1]; rfl
  · show (pcPushed t).mem.readW (State.addr (mkP bits s).sp + BitVec.ofNat 64 8) 32 = _
    rw [saved (.r2, 8) (by simp [pcAllSaved]), o.r2]; rfl
  · exact allocW h o (k := 4) (v := s.gpr .r0) (by simp [allocVals])
  · exact allocW h o (k := 0) (v := BitVec.ofNat 32 (Impl.Dsa.Arm.ProbablePrime.len bits)) (by simp [allocVals])
  · exact allocW h o (k := 8) (v := BitVec.ofNat 32 (Impl.Dsa.Arm.ProbablePrime.draw bits)) (by simp [allocVals])
  · show _ = BitVec.ofNat 32 (Spec.Dsa.primeChecks bits)
    rw [← hchk]
    exact allocW h o (k := 28) (v := BitVec.ofNat 32 (Impl.Dsa.Arm.ProbablePrime.checks bits)) (by simp [allocVals])
  · exact allocW h o (k := 12) (v := s.gpr .r2) (by simp [allocVals])
  · show _ = BitVec.ofNat 32 (s.gpr .r3).toNat
    rw [show BitVec.ofNat 32 (s.gpr .r3).toNat = s.gpr .r3 by simp]
    exact allocW h o (k := 16) (v := s.gpr .r3) (by simp [allocVals])
  · exact allocW h o (k := 20) (v := s.gpr .r0 + BitVec.ofNat 32 keyOff) (by simp [allocVals])
  · exact allocW h o (k := 24) (v := BitVec.ofNat 32 (keyWords bits)) (by simp [allocVals])

end

end VG.Proof.Dsa.Arm.Prime
