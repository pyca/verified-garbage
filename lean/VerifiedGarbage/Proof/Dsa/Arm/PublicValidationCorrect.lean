module

public import VerifiedGarbage.Proof.Dsa.Arm.PublicValidationABI
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Arm.PublicValidationBody
public import VerifiedGarbage.Proof.Dsa.ModPowContract
public import VerifiedGarbage.Proof.Dsa.PublicValidationContract

/-! # Functional correctness against the public validation contract -/

@[expose] public section
namespace VG.Proof.Dsa.Arm.PublicValidation
open VG VG.Arm VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Impl.Dsa.Arm.PublicValidation
open VG.Proof.Dsa.PublicValidation (component)
open VG.Proof.Dsa.ModPow (numAt)

theorem correct {pLen qLen nP nQ : Nat} (wp : Width pLen nP) (wq : Width qLen nQ)
    (qp : qLen ≤ pLen) (q32 : qLen ≤ 32) (s : State) (H : (armContract pLen qLen).pre s) :
    ∃ tr t, Exec isa (body pLen qLen) s tr t ∧ abiPreserved s t ∧ (armContract pLen qLen).post s t := by
  obtain ⟨hz, hk, pp, pq, pg, py, hP, hPo, hQ, hQo⟩ := H.2.2.2.2.2
  change 3 * pLen + qLen ≤ keyLen s at hk
  have E := entry H
  have Ip := keyInput (offset := 0) (len := pLen) H (f := .p) (by decide) (by omega) (by simpa only [layout, BitVec.add_zero] using pp)
  have Iq := keyInput (offset := pLen) (len := qLen) H (f := .q) (by decide) (by omega) pq
  have Ig := keyInput (offset := pLen + qLen) (len := pLen) H (f := .g) (by decide) (by omega) pg
  have Iy := keyInput (offset := 2 * pLen + qLen) (len := pLen) H (f := .y) (by decide) (by omega) py
  obtain ⟨tr, t, Ex, F, V, O, Regs, SP, _, _⟩ :=
    body_ok E (by change 15713 ≤ size s at hz; omega) wp wq qp q32 Ip Iq Ig Iy hP hPo hQ hQo
  refine ⟨tr, t, Ex, ⟨Regs, SP⟩, ?_, V, ?_⟩
  · change (maskW (ws s) t).toNat = _
    rw [F]
    change _ = if publicChecks _ _ _ _ then (maskW (ws s) s).toNat else 0
    split <;> rename_i h
    all_goals simp only [layout] at h
    · simp only [VG.Proof.Ecdsa.Arm.mask32, h, ↓reduceIte, BitVec.and_allOnes]
    · simp only [VG.Proof.Ecdsa.Arm.mask32, h, ↓reduceIte]
      change (maskW (ws s) s &&& (0#32)).toNat = 0
      simp only [BitVec.and_zero, BitVec.toNat_zero]
  · intro i hi hj
    apply O
    intro r hr
    rw [show ofs (ws s) (ws s + BitVec.ofNat 64 i) = i by
      simp only [ofs]; rw [Mem.sub_ofNat_toNat _ (by have := E.nowrap; omega)]]
    exact hj r hr

end VG.Proof.Dsa.Arm.PublicValidation
