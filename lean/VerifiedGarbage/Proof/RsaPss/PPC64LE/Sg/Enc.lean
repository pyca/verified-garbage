module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Blocks
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.EnView
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Hash
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Mgf
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Fixed
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Checks
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Entry

/-!
# RSASSA-PSS signing on PPC64LE: the encoding

Untrusted: everything here is checked by Lean. `signEnc_ok`: after the
checks, `M'` and its hash `H`, `EM`'s writes, MGF1's mask and `clearTop`
leave `encEm` (`Sg/Spec.lean`) at `scratch`, with `Base`, for the private
operation that follows.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE.Sg

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE.Sign VG.WriteBytes
open VG.Impl.RsaOaep.PPC64LE (oEm oSt oDig oW oRsa)
open VG.Impl.RsaPss.PPC64LE (oY)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off off_off view view_wb view_w8 fx hiRegs offs mgfXor_ok MFit)
open VG.Proof.RsaOaep (mixV srcB range_ext map_range_getD')
open VG.Proof.RsaPss.PPC64LE (hashFixedG_ok)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

section
variable {Gs : Spec.Mgf1.Hash} {s : State} (P : PreS Gs.len s) {H : Hash} (hH : HashOK H)
  (hGh : ∀ x, Gs.hash x = hH.SH.H.hash x) (hGl : Gs.len = H.D) (hGv : Proof.Mgf1.Valid Gs)
include P hH hGh hGl hGv

theorem signEnc_ok {t : State} (E : Entered s t) (h0 : s.mem (s.gpr .r5) ≠ 0)
    (hfit : Gs.len + (stackArg s 10).toNat + 2 ≤ kk s - loN s) {Q : State → Prop}
    (k : ∀ t', Base Ss vS s t' → Spec.Rsa.bytesAt t'.mem (off (Ss s) oEm) (kk s) = encEm Gs s →
      WP isa priv t' Q) :
    WP isa (signMain H) t Q := by
  have F := fits P
  have hD0 : 0 < Gs.len := hGl ▸ hH.hD0
  have hD64 : Gs.len ≤ 64 := hGl ▸ hH.hD64
  have hDF := hH.hDF
  have hFD := hH.hFD64
  have hk2 : kk s ≤ 1024 := P.k2
  have hl1 := loN_le s
  obtain ⟨hE, hSt, hDg, _, _, hR⟩ := offs
  have hY : oY = 2560 := rfl
  have hsalt : (saltB s).length = (stackArg s 10).toNat := bytesAt_length _ _ _
  have hhl : (hS Gs s).length = Gs.len := hGv.2 _
  unfold signMain
  -- `M'` and `H`.
  refine WP.seq (WP.mono (mPrime_ok P hGl.symm hD0 hD64 E.base (by omega)) fun t₁ ⟨b₁, _, m₁⟩ => ?_)
  refine WP.seq (WP.mono (hashFixedG_ok F hH hGl.symm (sl := (stackArg s 10).toNat)
    (by show stackArg s 10 = _; rw [ofNat_toNat]) b₁ (by omega)) fun t₂ ⟨b₂, _, _, d₂⟩ => ?_)
  have hM : Spec.Sha256.bytesAt t₁.mem (off (Ss s) oY) (8 + Gs.len + (stackArg s 10).toNat) =
      Spec.RsaPss.zeros 8 ++ digB Gs.len s ++ saltB s := by
    have := mPrime_bytes t.mem (Ss s) (digB Gs.len s) (saltB s) (bytesAt_length _ _ _) (by rw [hsalt]; omega)
    rw [hsalt] at this
    rw [m₁]; exact this
  have hh : ∀ i < Gs.len, view t₂.mem (Ss s) (oDig + i) = (hS Gs s).getD i 0 := by
    intro i hi
    have := congrArg (fun l => l.getD i 0) d₂
    simp only [show Spec.Sha256.bytesAt t₂.mem (off (Ss s) oDig) H.FD = Spec.Rsa.bytesAt t₂.mem (off (Ss s) oDig) H.FD
      from rfl, bytesAt_eq_view, map_range_getD' _ (show i < H.FD by omega), hM] at this
    rw [this, hS, hGh, hH.hashTake]
    simp [List.getD_eq_getElem?_getD, show i < H.D by omega]
  -- `EM` before masking.
  refine WP.seq (WP.mono (clearEm_ok P b₂) fun t₃ ⟨b₃, _, m₃⟩ => ?_)
  refine WP.seq (WP.mono (putSalt_ok P hGl.symm hD64 b₃ (by omega)) fun t₄ ⟨b₄, _, m₄⟩ => ?_)
  have hdig : Spec.Rsa.bytesAt t₄.mem (off (Ss s) oDig) Gs.len = hS Gs s := by
    rw [bytesAt_eq_view]
    refine range_ext hhl fun i hi => ?_
    rw [m₄, view_wb _ _ (by rw [hsalt]; omega) (by omega), ifn (by omega), view_w8 _ _ (by omega) (by omega),
      ifn (by omega), m₃, view_wb _ _ (by simp; omega) (by omega), ifn (by simp only [List.length_replicate]; omega)]
    exact hh i (by omega)
  refine WP.seq (WP.mono (putH_ok P hGl.symm hD0 hD64 b₄ (by omega)) fun t₅ ⟨b₅, _, m₅⟩ => ?_)
  have hpre : ∀ o < kk s, view t₅.mem (Ss s) o = emPre (kk s) Gs.len (stackArg s 10).toNat (saltB s) (hS Gs s) o :=
    fun o ho => emPre_of hsalt hhl hk2 (by omega) m₃ m₄ (by rw [m₅, hdig]) ho
  -- MGF1 and `clearTop`.
  refine WP.seq (WP.mono (dbArgs_ok P hGl.symm hD64 b₅ h0 (by omega)) fun t₆ ⟨b₆, v₆, x24, x25, x26, x27⟩ => ?_)
  have hsrc : srcB (view t₆.mem (Ss s)) (oEm + (kk s - Gs.len - 1)) Gs.len = hS Gs s := by
    refine range_ext hhl fun i hi => ?_
    rw [v₆, hpre _ (by omega)]
    simp only [emPre, hE, Nat.zero_add]
    rw [ifn (by omega), ifp (by omega), show kk s - Gs.len - 1 + i - (kk s - Gs.len - 1) = i by omega]
  refine WP.seq (WP.mono (mgfXor_ok F hH hGh hGl hGv (src := oEm + (kk s - Gs.len - 1)) (srcLen := Gs.len)
    (dst := oEm + loN s) (dstLen := kk s - loN s - Gs.len - 1) ⟨by omega, by omega, .inr (by omega), by omega⟩
    b₆ x24 (by rw [x25]) x26 x27) fun t₇ ⟨b₇, v₇⟩ => ?_)
  refine WP.seq (WP.mono (clearTop_ok P b₇ h0) fun t₈ ⟨b₈, m₈⟩ => ?_)
  refine k t₈ b₈ ?_
  rw [bytesAt_eq_view]
  unfold encEm
  refine List.map_congr_left fun o ho => ?_
  have ho := List.mem_range.mp ho
  rw [m₈, view_w8 _ _ (by omega) (by omega), hE, Nat.zero_add, Nat.zero_add]
  have e7 : ∀ x < kk s, view t₇.mem (Ss s) x = mixV (view t₆.mem (Ss s)) (Spec.Mgf1.mgf1 Gs (hS Gs s)
      (kk s - loN s - Gs.len - 1)) (loN s) (kk s - loN s - Gs.len - 1) x := fun x hx => by
    rw [v₇ x (by omega), hsrc, hE, Nat.zero_add]
  rw [e7 o ho, e7 (loN s) (by omega)]
  have := emT_of (saltB s) (hS Gs s) (Spec.Mgf1.mgf1 Gs (hS Gs s) (kk s - loN s - Gs.len - 1)) (cS s)
    (k := kk s) (sl := (stackArg s 10).toNat) hhl hl1 rfl (by omega) (V := view t₆.mem (Ss s))
    (fun x hx => by rw [v₆]; exact hpre x hx) ho
  by_cases hl : o = loN s
  · subst hl; rw [ifp rfl]; rw [ifp rfl] at this; exact this
  · rw [ifn hl]; rw [ifn hl] at this; exact this

end

end VG.Proof.RsaPss.PPC64LE.Sg
