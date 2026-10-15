module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemVInv
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemReadonlyTransform
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Finish the ciphertext scalar component after its fused product -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
variable {P : KemLay} {L : Layout}
variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

theorem readonly_v_tail {s₀ s : State} (hp : Pre P L s₀) (hc : Calls P)
    {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co)
    {mE mB : Mem} {v : BitVec 64} {rv mv : List Byte} {T : Nat → Poly}
    (e₀ : VInv P L s₀ kC co mE mB v rv mv P.k P.k s)
    (ht : Optimized.TransformTables s)
    (t₀ : PolyIs s.mem (sA L s₀ (TP P)) (KPke.dotK T (encY rv) P.k)) :
    WPs [Ntt16.Readonly.nttInvAt (TP P),prfCbdWith keccak.callee (2*P.k) (EP P),addAt (TP P) (EP P),
      ddAt .x28 MB 1 (EP P),addAt (TP P) (EP P),P.ceLAt (TP P) P.dv (slotReg kC) (co+32*P.du*P.k)] s
      (fun t => VInv P L s₀ kC co mE mB v rv mv P.k P.k t ∧
        bytesAt t.mem (kA s₀ (L.slot kC)+BitVec.ofNat 64 (co+32*P.du*P.k)) (32*P.dv)=
          compressEncode P.dv (vPoly P T rv mv)) := by
  have hw := hp.wf
  refine WPs.cons (WP.mono (readonly_nttInv_ok hp (po_TP hw) e₀.kb t₀.1 ht) fun s₁ ⟨kb₁, f₁, t₁, x₁⟩ => ?_)
  have e₁ := e₀.frame_far hp kb₁ x₁ f₁ (far_mul hp A (Nat.le_refl _) (Nat.le_refl _) (by lom) (by lom))
  rw [t₀.2] at t₁
  refine WPs.cons (WP.mono (prfCbd_ok hp (N := 2 * P.k) (by lom) (po_EP hw) e₁.kb e₁.r)
    fun s₂ ⟨kb₂, f₂, p₂, x₂⟩ => ?_)
  have e₂ := e₁.frame_far hp kb₂ x₂ f₂ (far_pcW hp A (Nat.le_refl _) (Nat.le_refl _) (by lom) (by lom))
  have fTP : ∀ r ∈ pcW L s₀ (EP P), (polyRegion (sA L s₀ (TP P))).Disjoint r := fun r hr => by
    rcases mem6 hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact sdisj hp (po_TP hw).le (by lom) (by lom)
    · exact sdisj hp (po_TP hw).le (by lom) (by lom)
    · exact below_R hp hp.scb (hp.fs (po_TP hw).le)
    · exact sdisj hp (po_TP hw).le (by lom) (by lom)
    · exact sdisj hp (po_TP hw).le (by lom) (by lom)
    · exact papart hp (po_TP hw) (po_EP hw) (by lom)
  have t₂ := polyIs_frame f₂ fTP t₁
  refine WPs.cons (WP.mono (add_ok hp (po_TP hw) (po_EP hw) (.inr (by lom)) e₂.kb t₂.1 p₂.1)
    fun s₃ ⟨kb₃, f₃, t₃, x₃⟩ => ?_)
  have e₃ := e₂.frame_far hp kb₃ x₃ f₃ (far_one hp A (Nat.le_refl _) (Nat.le_refl _) (by lom) (by lom))
  rw [t₂.2, p₂.2] at t₃
  refine WPs.cons (WP.mono (dd_ok hp (k := 3) (o := MB) (d := 1) (off := EP P) (by decide)
    (hp.fs (by lom)) (by decide) (po_EP hw) (.inr (.inl (by lom))) e₃.kb)
    fun s₄ ⟨kb₄, f₄, p₄, x₄⟩ => ?_)
  have e₄ := e₃.frame_far hp kb₄ x₄ f₄ (far_one hp A (Nat.le_refl _) (Nat.le_refl _) (by lom) (by lom))
  have t₄ := polyIs_frame f₄ (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact papart hp (po_TP hw) (po_EP hw) (by lom)) t₃
  have hm : bytesAt s₃.mem (kA s₀ (L.slot 3) + BitVec.ofNat 64 MB) (32 * 1) = mv := e₃.m
  rw [hm] at p₄
  refine WPs.cons (WP.mono (add_ok hp (po_TP hw) (po_EP hw) (.inr (by lom)) e₄.kb t₄.1 p₄.1)
    fun s₅ ⟨kb₅, f₅, t₅, x₅⟩ => ?_)
  have e₅ := e₄.frame_far hp kb₅ x₅ f₅ (far_one hp A (Nat.le_refl _) (Nat.le_refl _) (by lom) (by lom))
  rw [t₄.2, p₄.2] at t₅
  have fC := A.fC
  have hmk := Nat.mul_assoc 32 P.du P.k
  refine WPs.single (WP.mono (ceL_ok hp hc (off := TP P) (d := P.dv) (k := kC) (o := co + 32 * P.du * P.k)
    (po_TP hw) (.inr rfl) A.hkC A.wC (by lom) (by
      rcases A.sC with hC | hC
      · exact .inl hC
      · exact .inr ⟨by subst hC; lom, .inr (by subst hC; lom)⟩)
    e₅.kb t₅.1) fun s₆ ⟨kb₆, f₆, b₆, x₆⟩ => ?_)
  refine ⟨e₅.frame_far hp kb₆ x₆ f₆ fun r hr => by
    rw [List.mem_singleton.mp hr]; exact far_ct hp A (Nat.le_refl _) (by lom), ?_⟩
  rw [b₆, t₅.2]


end VG.Proof.MlKem.AArch64.Kem
