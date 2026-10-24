module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Mgf
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Label
public import VerifiedGarbage.Proof.RsaOaep.Encode
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Em
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Entry

/-!
# RSAES-OAEP encryption on PPC64LE: `EM`

Untrusted: everything here is checked by Lean. `em_ok`: `EM` before masking
(`encEm`, the label's hash and `copyLh`, as `RsaOaep.EmAt`); `mask_ok`: `DB`
masked with MGF1 of the seed and the seed with MGF1 of `maskedDB`, which
leaves EME-OAEP's encoding at `S` (`RsaOaep.emOf`, by `RsaOaep.em_mask`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.WriteBytes
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_li wp_addi wp_subi wp_mov wp_nil)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)
open VG.Proof.RsaOaep (mixV srcB EmAt emOf)
open VG.Proof.Mgf1 (ifp ifn)

/-- The seed's and the message's bytes, the label's, and the message's length,
from the entry state. -/
abbrev seedB (D : Nat) (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 2) D
abbrev msgB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat
abbrev labB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .r10).toNat
abbrev kk (s : State) : Nat := (s.gpr .r6).toNat
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
theorem em_ok {H : Hash} (hH : HashOK H) {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x)
    (hD : H.D = D) {t : State} (E : Entered s t) (hk : 2 * D + 2 + mLen s ≤ kk s) {rest : Prog isa}
    {Q : State → Prop}
    (k : ∀ t', Base s t' → EmAt (view t'.mem (S s)) (kk s) D (seedB D s) (Hs.hash (labB s)) (msgB s) (mLen s) →
      WP isa rest t' Q) :
    WP isa (.seq (encEm H) (.seq (hashLabel H) (.seq (copyLh H) rest))) t Q := by
  have hD0 := hH.hD0
  have hD64 := hH.hD64
  have hDF := hH.hDF
  have F := hfits hH
  obtain ⟨_, hSt, hDg, hCt, hW, hRs⟩ := offs
  refine WP.seq (WP.mono (encEm_ok P hD (by omega) (by omega) E hk) fun t₁ ⟨b₁, hp⟩ => ?_)
  refine WP.seq (WP.mono (hashLabel_ok P hH b₁) fun t₂ ⟨b₂, _, s₂, d₂⟩ => ?_)
  refine WP.seq (WP.mono (copyLh_ok P hH hD b₂) fun t₃ ⟨b₃, _, m₃⟩ => k t₃ b₃ ?_)
  have hlh : Spec.Rsa.bytesAt t₂.mem (off (S s) oDig) D = Hs.hash (labB s) := by
    rw [hHh, hH.hashTake, ← d₂, ← hD]
    simp only [Spec.Rsa.bytesAt]
    rw [← List.map_take, List.take_range, Nat.min_eq_left hDF]
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
theorem mask_ok {H G : Hash} (hG : HashOK G) {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x)
    (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs) (hD : H.D = D) (hD0 : 0 < D) (hD64 : D ≤ 64)
    {sd lh m : List Byte} (hsd : sd.length = D) (hlh : lh.length = D) (hm : m.length = mLen s)
    (hk : 2 * D + 2 + mLen s ≤ kk s) {t : State} (h : Base s t)
    (he : EmAt (view t.mem (S s)) (kk s) D sd lh m (mLen s)) {rest : Prog isa} {Q : State → Prop}
    (k : ∀ t', Base s t' → Spec.Rsa.bytesAt t'.mem (off (S s) 0) (kk s) = emOf Gs D (kk s) (mLen s) sd lh m →
      WP isa rest t' Q) :
    WP isa (.seq (.block (dbArgs H)) (.seq (mgfXor G) (.seq (.block (seedArgs H)) (.seq (mgfXor G) rest)))) t Q := by
  obtain ⟨hE, hSt, hDg, hCt, hW, hRs⟩ := offs
  have hk2 := P.k2
  have ek : kk s = (s.gpr .r6).toNat := rfl
  subst hD
  -- `DB` with MGF1 of the seed.
  refine WP.seq (wp_addi (h := by omega) fun t₁ o₁ e₁ => wp_li (by omega) fun t₂ o₂ e₂ =>
    wp_addi (h := by omega) fun t₃ o₃ e₃ => wp_subi (h := by omega) fun t₄ o₄ e₄ => wp_nil ?_)
  have k₄ : Only [.r24, .r25, .r26, .r27] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  have b₄ := h.only P k₄
  refine WP.seq (WP.mono (mgfXor_ok P hG hGh hGl hGv (src := 1) (srcLen := H.D) (dst := 1 + H.D)
    (dstLen := kk s - H.D - 1) ⟨by omega, by omega, .inl (by omega), by omega⟩ b₄
    (by rw [o₄.get .r24, o₃.get .r24, o₂.get .r24, e₁, h.r14, hE])
    (by rw [o₄.get .r25, o₃.get .r25, e₂])
    (by rw [o₄.get .r26, e₃, o₂.get .r14, o₁.get .r14, h.r14, hE, Nat.zero_add])
    (by rw [e₄, o₃.get .r15, o₂.get .r15, o₁.get .r15, h.r15, sub_k (by omega)]; congr 1))
    fun t₅ ⟨b₅, v₅⟩ => ?_)
  -- The seed with MGF1 of `maskedDB`.
  refine WP.seq (wp_addi (h := by omega) fun t₆ o₆ e₆ => wp_subi (h := by omega) fun t₇ o₇ e₇ =>
    wp_addi (h := by omega) fun t₈ o₈ e₈ => wp_li (by omega) fun t₉ o₉ e₉ => wp_nil ?_)
  have k₉ : Only [.r24, .r25, .r26, .r27] t₅ t₉ := (o₆.trans (o₇.trans (o₈.trans o₉))).mono
  have b₉ := b₅.only P k₉
  refine WP.seq (WP.mono (mgfXor_ok P hG hGh hGl hGv (src := 1 + H.D) (srcLen := kk s - H.D - 1) (dst := 1)
    (dstLen := H.D) ⟨by omega, by omega, .inr (by omega), by omega⟩ b₉
    (by rw [o₉.get .r24, o₈.get .r24, o₇.get .r24, e₆, b₅.r14, hE, Nat.zero_add])
    (by rw [o₉.get .r25, o₈.get .r25, e₇, o₆.get .r15, b₅.r15, sub_k (by omega)]; congr 1)
    (by rw [o₉.get .r26, e₈, o₇.get .r14, o₆.get .r14, b₅.r14, hE])
    (by rw [e₉]))
    fun t₁₀ ⟨b₁₀, v₁₀⟩ => k t₁₀ b₁₀ ?_)
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
    List.map_congr_left fun i hi => v₅ _ (by have := List.mem_range.mp hi; omega)
  rw [bytesAt_S]
  refine (List.map_congr_left fun i hi => ?_).trans ((em_mask hGv (by omega) hsd hdbl he.z0 he.sd hdb).trans ?_)
  · have hi := List.mem_range.mp hi
    rw [v₁₀ i (by omega), hsrc, mixV, mixV]
    split
    · rw [v₅ i (by omega)]
    · rw [v₅ i (by omega)]
  · rw [← hDB]; rfl

end

end VG.Proof.RsaOaep.PPC64LE
