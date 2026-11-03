module

public import VerifiedGarbage.Proof.RsaOaep.RISCV64.MgfT
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Label
public import VerifiedGarbage.Proof.RsaOaep.Encode
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Syms

/-!
# RSAES-OAEP encryption on RISC-V: `EM`

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/Main.lean`): `em_ok`, `EM` before masking (`encEm`,
the label's hash and `copyLh`, as `RsaOaep.EmAt`); `mask_ok`, `DB` masked
with MGF1 of the seed and the seed with MGF1 of `maskedDB`, which leaves
EME-OAEP's encoding at `S` (`RsaOaep.emOf`, by `RsaOaep.em_mask`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.RISCV64

open VG VG.RISCV64 VG.Impl.RsaOaep.RISCV64 VG.WriteBytes
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Kept MemTo wp_li wp_addi wp_subi wp_mov wp_nil)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)
open VG.Proof.RsaOaep (mixV srcB EmAt emOf em_mask)
open VG.Proof.Mgf1 (ifp ifn)

/-- The seed's and the message's bytes, the label's, and the message's length,
from the entry state. -/
abbrev seedB (D : Nat) (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 2) D
abbrev msgB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat
abbrev labB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .a6) (s.gpr .a7).toNat
abbrev kk (s : State) : Nat := (s.gpr .a3).toNat
abbrev mLen (s : State) : Nat := (stackArg s 1).toNat

theorem sub_k {x : BitVec 64} {a : Nat} (h : a ≤ x.toNat) : x - BitVec.ofNat 64 a = BitVec.ofNat 64 (x.toNat - a) := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := a) (by omega), Nat.mod_eq_of_lt (a := x.toNat - a) (by omega)]; omega

section
variable {D : Nat} {s : State} (P : PreO D s)
include P

/-- `EM` before masking: `encEm`, the label's hash and `copyLh`. -/
theorem em_ok {H : Hash} (hH : HashOK H) (hF : H.F ≤ 208) {Hs : Spec.Mgf1.Hash}
    (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hD : H.D = D) {t : State} (E : Entered s t)
    (hk : 2 * D + 2 + mLen s ≤ kk s) {rest : Prog isa} {Q : State → Prop}
    (k : ∀ t', Base S vO s t' → t'.syms = t.syms →
      EmAt (view t'.mem (S s)) (kk s) D (seedB D s) (Hs.hash (labB s)) (msgB s) (mLen s) → WP isa rest t' Q) :
    WP isa (.seq (encEm H) (.seq (hashLabel H) (.seq (copyLh H) rest))) t Q := by
  have hD0 := hH.hD0
  have hD64 := hH.hD64
  have F := hfits hH
  obtain ⟨_, hSt, hDg, hCt, hRs⟩ := offs
  refine WP.seq (WP.mono_syms (encEm_ok P hD (by omega) (by omega) E hk) fun t₁ ⟨b₁, g6, g7, hp⟩ y₁ => ?_)
  refine WP.seq (WP.mono_syms (hashLabel_ok P hH hF b₁ g6 g7) fun t₂ ⟨b₂, _, s₂, d₂⟩ y₂ => ?_)
  refine WP.seq (WP.mono_syms (copyLh_ok P hH hD b₂) fun t₃ ⟨b₃, _, m₃⟩ y₃ =>
    k t₃ b₃ (y₃.trans (y₂.trans y₁)) ?_)
  have hlh : Spec.Rsa.bytesAt t₂.mem (off (S s) oDig) D = Hs.hash (labB s) := by
    rw [hHh, ← d₂, ← hD]
  refine emAt_of hp hk P.k2 fun o ho => ?_
  rw [m₃, view_wb _ _ (by rw [bytesAt_length]; omega) (by omega), bytesAt_length, hlh,
    s₂ o (by omega) (by simp; omega)]

omit P in
/-- The bytes at `S`, from the view. -/
theorem bytesAt_S (m : Mem) (S : Addr) (n : Nat) :
    Spec.Rsa.bytesAt m (off S 0) n = (List.range n).map (view m S) := by
  rw [bytesAt_view]; simp only [srcB, Nat.zero_add]

/-- `DB` masked with MGF1 of the seed, then the seed with MGF1 of `maskedDB`:
EME-OAEP's encoding at `S`. -/
theorem mask_ok {H G : Hash} (hG : HashOK G) (hF : G.F ≤ 208) {f : Fns}
    (T : TabS G f 7 S s (stackArg s 7)) {Gs : Spec.Mgf1.Hash}
    (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs) (hD : H.D = D)
    (hD0 : 0 < D) (hD64 : D ≤ 64) {sd lh m : List Byte} (hsd : sd.length = D) (hlh : lh.length = D)
    (hm : m.length = mLen s) (hk : 2 * D + 2 + mLen s ≤ kk s) {t : State} (h : Base S vO s t)
    (hsy : t.syms = s.syms) (he : EmAt (view t.mem (S s)) (kk s) D sd lh m (mLen s)) {rest : Prog isa} {Q : State → Prop}
    (k : ∀ t', Base S vO s t' → Spec.Rsa.bytesAt t'.mem (off (S s) 0) (kk s) = emOf Gs D (kk s) (mLen s) sd lh m →
      WP isa rest t' Q) :
    WP isa (.seq (.block (dbArgs H)) (.seq (mgfXorT f 7) (.seq (.block (seedArgs H)) (.seq (mgfXorT f 7) rest)))) t Q :=
    by
  obtain ⟨hE, hSt, hDg, hCt, hRs⟩ := offs
  have hk2 := P.k2
  have ek : kk s = (s.gpr .a3).toNat := rfl
  subst hD
  -- `DB` with MGF1 of the seed.
  refine WP.seq (WP.of_syms (wp_addi (imm := oEm + 1) (h := by omega) fun t₁ o₁ e₁ => wp_li (imm := H.D) (by omega)
    fun t₂ o₂ e₂ => wp_addi (imm := oEm + 1 + H.D) (h := by omega) fun t₃ o₃ e₃ =>
    wp_subi (imm := H.D + 1) (h := by omega) fun t₄ o₄ e₄ => wp_nil fun y₄ => ?_))
  have k₄ : Only [.s6, .s7, .s8, .s9] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  have b₄ := h.only P.fits k₄
  refine WP.seq (WP.mono (mgfXorT_ok P.fits hG hF T hGh hGl hGv (src := 1) (srcLen := H.D) (dst := 1 + H.D)
    (dstLen := kk s - H.D - 1) ⟨by omega, by omega, .inl (by omega), by omega⟩ b₄ (y₄.trans hsy)
    (by rw [o₄.get .s6, o₃.get .s6, o₂.get .s6, e₁, h.s0, hE])
    (by rw [o₄.get .s7, o₃.get .s7, e₂])
    (by rw [o₄.get .s8, e₃, o₂.get .s0, o₁.get .s0, h.s0, hE, Nat.zero_add])
    (by rw [e₄, o₃.get .s1, o₂.get .s1, o₁.get .s1, h.s1, sub_k (by omega)]; congr 1))
    fun t₅ ⟨⟨b₅, v₅⟩, y₅⟩ => ?_)
  -- The seed with MGF1 of `maskedDB`.
  refine WP.seq (WP.of_syms (wp_addi (imm := oEm + 1 + H.D) (h := by omega) fun t₆ o₆ e₆ =>
    wp_subi (imm := H.D + 1) (h := by omega) fun t₇ o₇ e₇ => wp_addi (imm := oEm + 1) (h := by omega)
    fun t₈ o₈ e₈ => wp_li (imm := H.D) (by omega) fun t₉ o₉ e₉ => wp_nil fun y₉ => ?_))
  have k₉ : Only [.s6, .s7, .s8, .s9] t₅ t₉ := (o₆.trans (o₇.trans (o₈.trans o₉))).mono
  have b₉ := b₅.only P.fits k₉
  refine WP.seq (WP.mono (mgfXorT_ok P.fits hG hF T hGh hGl hGv (src := 1 + H.D) (srcLen := kk s - H.D - 1)
    (dst := 1) (dstLen := H.D) ⟨by omega, by omega, .inr (by omega), by omega⟩ b₉ (y₉.trans y₅)
    (by rw [o₉.get .s6, o₈.get .s6, o₇.get .s6, e₆, b₅.s0, hE, Nat.zero_add])
    (by rw [o₉.get .s7, o₈.get .s7, e₇, o₆.get .s1, b₅.s1, sub_k (by omega)]; congr 1)
    (by rw [o₉.get .s8, e₈, o₇.get .s0, o₆.get .s0, b₅.s0, hE])
    (by rw [e₉]))
    fun t₁₀ ⟨⟨b₁₀, v₁₀⟩, _⟩ => k t₁₀ b₁₀ ?_)
  -- `EM`.
  have hdb := he.db hlh hm hk
  generalize hDB : lh ++ Spec.RsaOaep.zeros (kk s - mLen s - 2 * H.D - 2) ++ 0x01 :: m = db at hdb
  have hdbl : db.length = kk s - H.D - 1 := by
    rw [← hDB]; simp [Spec.RsaOaep.zeros, hlh, hm]; omega
  have V4 : view t₄.mem (S s) = view t.mem (S s) := by rw [k₄.mem]
  have V9 : view t₉.mem (S s) = view t₅.mem (S s) := by rw [k₉.mem]
  rw [V4] at v₅
  rw [V9] at v₁₀
  have hsrc : srcB (view t₅.mem (S s)) (1 + H.D) (kk s - H.D - 1) =
      srcB (mixV (view t.mem (S s)) (Spec.Mgf1.mgf1 Gs (srcB (view t.mem (S s)) 1 H.D) (kk s - H.D - 1)) (1 + H.D)
        (kk s - H.D - 1)) (1 + H.D) (kk s - H.D - 1) :=
    List.map_congr_left fun i hi => v₅ _ ⟨by have := List.mem_range.mp hi; omega, .inl (by have := List.mem_range.mp hi; omega)⟩
  rw [bytesAt_S]
  refine (List.map_congr_left fun i hi => ?_).trans ((em_mask hGv (by omega) hsd hdbl he.z0 he.sd hdb).trans ?_)
  · have hi := List.mem_range.mp hi
    rw [v₁₀ i ⟨by omega, .inl (by omega)⟩, hsrc, mixV, mixV]
    split
    · rw [v₅ i ⟨by omega, .inl (by omega)⟩]
    · rw [v₅ i ⟨by omega, .inl (by omega)⟩]
  · rw [← hDB]; rfl

end

end VG.Proof.RsaOaep.RISCV64
