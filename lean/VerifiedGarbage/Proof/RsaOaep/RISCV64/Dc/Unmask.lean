module

-- separate module: it builds in parallel with `Label`, `Scan`, `Buf`, `Shift` and `Out`, which `Correct` also needs.

public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Priv
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Mgf
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Main

/-!
# RSAES-OAEP decryption on RISC-V: the unmasking

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/Dc/Unmask.lean`), with encryption's MGF1
(`mgfXor_ok`): `unmask_ok`, the seed unmasked with MGF1 of `maskedDB`, then
`DB` with MGF1 of the seed, in `EM`'s place.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.RISCV64.Dec

open VG VG.RISCV64 VG.Impl.RsaOaep.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only wp_li wp_addi wp_subi wp_nil)
open VG.Proof.RsaOaep (mixV srcB)
open VG.Proof.RsaOaep.RISCV64 (Base Fits view off offs mgfXor_ok MFit sub_k)

section
variable {s : State} (P : PreD s) {m : Mem} {rc : Nat}
include P

/-- EME-OAEP's unmasking, in place. -/
theorem unmask_ok {H G : Hash} (hG : HashOK G) (hF : G.F ≤ 208) {Gs : Spec.Mgf1.Hash}
    (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs) {D : Nat}
    (hD : H.D = D) (hD0 : 0 < D) (hD64 : D ≤ 64) (hk : 2 * D + 2 ≤ kk s) {t : State}
    (h : Base (SD s) (VD s rc) (withMem s m) t) {rest : Prog isa} {Q : State → Prop}
    (k : ∀ t', Base (SD s) (VD s rc) (withMem s m) t' → (∀ x < kk s, view t'.mem (Sd s) x =
        mixV (mixV (view t.mem (Sd s)) (Spec.Mgf1.mgf1 Gs (srcB (view t.mem (Sd s)) (1 + D) (kk s - D - 1)) D) 1 D)
          (Spec.Mgf1.mgf1 Gs (srcB (mixV (view t.mem (Sd s))
            (Spec.Mgf1.mgf1 Gs (srcB (view t.mem (Sd s)) (1 + D) (kk s - D - 1)) D) 1 D) 1 D) (kk s - D - 1))
          (1 + D) (kk s - D - 1) x) → WP isa rest t' Q) :
    WP isa (.seq (.block (seedArgs H)) (.seq (mgfXor G) (.seq (.block (dbArgs H)) (.seq (mgfXor G) rest)))) t Q := by
  obtain ⟨hE, hSt, hDg, hCt, hRs⟩ := offs
  have hk2 := P.k2
  have ek : kk s = (s.gpr .a4).toNat := rfl
  have PF : Fits (SD s) (withMem s m) := fits P rfl rfl
  have h1 : ∀ {w : State}, Base (SD s) (VD s rc) (withMem s m) w → w.gpr .s1 = s.gpr .a4 := fun hw => Base.dk hw
  subst hD
  -- The seed with MGF1 of `maskedDB`.
  refine WP.seq (wp_addi (imm := oEm + 1 + H.D) (h := by omega) fun t₁ o₁ e₁ =>
    wp_subi (imm := H.D + 1) (h := by omega) fun t₂ o₂ e₂ => wp_addi (imm := oEm + 1) (h := by omega)
    fun t₃ o₃ e₃ => wp_li (imm := H.D) (by omega) fun t₄ o₄ e₄ => wp_nil ?_)
  have k₄ : Only [.s6, .s7, .s8, .s9] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  have b₄ := h.only PF k₄
  refine WP.seq (WP.mono (mgfXor_ok PF hG hF hGh hGl hGv (src := 1 + H.D) (srcLen := kk s - H.D - 1)
    (dst := 1) (dstLen := H.D) ⟨by omega, by omega, .inr (by omega), by omega⟩ b₄
    (by rw [o₄.get .s6, o₃.get .s6, o₂.get .s6, e₁, h.s0, hE, Nat.zero_add])
    (by rw [o₄.get .s7, o₃.get .s7, e₂, o₁.get .s1, h1 h, sub_k (by omega)]; congr 1)
    (by rw [o₄.get .s8, e₃, o₂.get .s0, o₁.get .s0, h.s0, hE])
    (by rw [e₄]))
    fun t₅ ⟨b₅, v₅⟩ => ?_)
  -- `maskedDB` with MGF1 of the seed.
  refine WP.seq (wp_addi (imm := oEm + 1) (h := by omega) fun t₆ o₆ e₆ => wp_li (imm := H.D) (by omega)
    fun t₇ o₇ e₇ => wp_addi (imm := oEm + 1 + H.D) (h := by omega) fun t₈ o₈ e₈ =>
    wp_subi (imm := H.D + 1) (h := by omega) fun t₉ o₉ e₉ => wp_nil ?_)
  have k₉ : Only [.s6, .s7, .s8, .s9] t₅ t₉ := (o₆.trans (o₇.trans (o₈.trans o₉))).mono
  have b₉ := b₅.only PF k₉
  refine WP.seq (WP.mono (mgfXor_ok PF hG hF hGh hGl hGv (src := 1) (srcLen := H.D) (dst := 1 + H.D)
    (dstLen := kk s - H.D - 1) ⟨by omega, by omega, .inl (by omega), by omega⟩ b₉
    (by rw [o₉.get .s6, o₈.get .s6, o₇.get .s6, e₆, b₅.s0, hE])
    (by rw [o₉.get .s7, o₈.get .s7, e₇])
    (by rw [o₉.get .s8, e₈, o₇.get .s0, o₆.get .s0, b₅.s0, hE, Nat.zero_add])
    (by rw [e₉, o₈.get .s1, o₇.get .s1, o₆.get .s1, h1 b₅, sub_k (by omega)]; congr 1))
    fun t₁₀ ⟨b₁₀, v₁₀⟩ => k t₁₀ b₁₀ fun x hx => ?_)
  have V4 : view t₄.mem (Sd s) = view t.mem (Sd s) := by rw [k₄.mem]
  have V9 : view t₉.mem (Sd s) = view t₅.mem (Sd s) := by rw [k₉.mem]
  rw [V4] at v₅
  rw [V9] at v₁₀
  have kp : ∀ {o}, o < kk s → Proof.RsaOaep.RISCV64.Kp o := fun ho => ⟨by omega, .inl (by omega)⟩
  have hsrc : srcB (view t₅.mem (Sd s)) 1 H.D = srcB (mixV (view t.mem (Sd s))
      (Spec.Mgf1.mgf1 Gs (srcB (view t.mem (Sd s)) (1 + H.D) (kk s - H.D - 1)) H.D) 1 H.D) 1 H.D :=
    List.map_congr_left fun i hi => v₅ _ (kp (by have := List.mem_range.mp hi; omega))
  rw [v₁₀ x (kp hx), hsrc, mixV, mixV]
  split
  · rw [v₅ x (kp hx)]
  · rw [v₅ x (kp hx)]

end

end VG.Proof.RsaOaep.RISCV64.Dec
