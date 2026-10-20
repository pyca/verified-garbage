module
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.ReadonlyCalls
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TransformTables
public import VerifiedGarbage.Proof.MlKem.AArch64.DecapsA
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit

import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemReadonlyTransform
import VerifiedGarbage.Proof.MlKem.AArch64.KemEnc

/-! # Finish decryption after the fused secret-vector product -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Decaps
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
variable {P : KemLay}

theorem readonly_m_tail {s₀ s : State} (hp : Pre P (deL P) s₀) (hc : Calls P)
    (ht : Optimized.TransformTables s)
    (hk : KB P (deL P) s₀ s) (hx : s.gpr .x24=1)
    (t₄ : PolyIs s.mem (sA (deL P) s₀ (TP P))
      (KPke.dotK (dcS (KPke.dkPke P.params (dkD P s₀)))
        (fun j => ntt (KPke.dcU P.params (cD P s₀) j)) P.k)) :
    WPs [Ntt16.Readonly.nttInvAt (TP P),P.ddLAt .x26 (32*P.du*P.k) P.dv (EP P),subAt (EP P) (TP P),
      ceAt (EP P) 1 .x28 MB] s fun t => KB P (deL P) s₀ t ∧ t.gpr .x24=1 ∧
        bytesAt t.mem (sA (deL P) s₀ MB) 32=mD P s₀ := by
  have hw := hp.wf
  refine WPs.cons (WP.mono (readonly_nttInv_ok hp (po_TP hw) hk t₄.1 ht) fun s₅ ⟨kb₅, f₅, t₅, x₅⟩ => ?_)
  rw [t₄.2] at t₅
  have fv : 32 * P.du * P.k + 32 * P.dv ≤ (deL P).len 1 := by
    simp only [deL, List.getD_cons_zero, List.getD_cons_succ, KemLay.ctLen]
    rw [Nat.mul_add, Nat.mul_assoc]
  refine WPs.cons (WP.mono (ddL_ok hp hc (k := 1) (o := 32 * P.du * P.k) (d := P.dv) (off := EP P) (by decide)
    fv (.inr rfl) (po_EP hw) (.inl (by dek)) kb₅) fun s₆ ⟨kb₆, f₆, p₆, x₆⟩ => ?_)
  rw [slice_eq kb₅ (b := 1) (by decide) fv] at p₆
  have t₆ := polyIs_frame f₆ (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact papart hp (po_TP hw) (po_EP hw) (.inr (by kom))) t₅
  refine WPs.cons (WP.mono (sub_ok hp (po_EP hw) (po_TP hw) (.inl (by kom)) kb₆ p₆.1 t₆.1)
    fun s₇ ⟨kb₇, f₇, p₇, x₇⟩ => ?_)
  rw [p₆.2, t₆.2] at p₇
  refine WPs.single (WP.mono (ce_ok hp (off := EP P) (d := 1) (k := 3) (o := MB) (po_EP hw) (by decide)
    (by decide) (by dek) (by dek) (.inr ⟨by kom, .inl (by kom)⟩) kb₇ p₇.1) fun s₈ ⟨kb₈, f₈, b₈, x₈⟩ => ?_)
  refine ⟨kb₈, by rw [x₈, x₇, x₆, x₅, hx], ?_⟩
  rw [show sA (deL P) s₀ MB = kA s₀ ((deL P).slot 3) + BitVec.ofNat 64 MB from rfl, b₈, p₇.2, mD, KPke.decM,
    KPke.kpkeDecrypt_eq]
  rfl


end VG.Proof.MlKem.AArch64.Decaps
