module

public import VerifiedGarbage.Proof.RsaPss.RISCV64.Sg.Em
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Hash
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Mgf
import VerifiedGarbage.Proof.RsaPss.RISCV64.Hash
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# RSASSA-PSS signing on RISC-V: the encoding

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPss/PPC64LE/Sg/Blocks.lean`, `Sg/Enc.lean`): `dbArgs_ok`, MGF1's
registers for masking `DB` (`dbLen` bytes at `lo`) with `H` (at
`k - hLen - 1`); `clearTop_ok`, `DB`'s first byte ANDed with the mask `c` of
the modulus' first byte, read again through the saved `n`; and
`signEnc_ok`: after the checks, `M'` and its hash `H`, `EM`'s writes, MGF1's
mask and `clearTop` leave `encEm` (`Sg/Spec.lean`) at `scratch`, with `Base`
and the saved arguments, for the private operation that follows.
-/

@[expose] public section

namespace VG.Proof.RsaPss.RISCV64.Sg

open VG VG.RISCV64 VG.Impl.RsaPss.RISCV64.Sign VG.WriteBytes
open VG.Impl.RsaOaep.RISCV64 (oEm oSt oDig oCtr oRsa)
open VG.Impl.RsaPss.RISCV64 (oY)
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.RsaOaep.RISCV64 (Base Fits SC off off_off view view_wb view_w8 sc_in sc_inR sc_inW offs hfits
  mgfXor_ok MFit kR)
open VG.Proof.RsaOaep (mixV srcB range_ext map_range_getD')
open VG.Proof.RsaPss.RISCV64 (hashFixedG_ok smB loB cmB)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Kept MemTo wp_li wp_addi wp_subi wp_add wp_sub wp_mov wp_lbu wp_ld
  wp_srl wp_or wp_and wp_sb wp_nil)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

theorem lo_reg {s t : State} (h : Base Ss vS s t) (h0 : s.mem (s.gpr .a2) ≠ 0) :
    t.gpr .s3 = BitVec.ofNat 64 (loN s) := by rw [Base.slo h, lo_eq h0]

/-- The mask `c` of the byte `b`, as a byte. -/
theorem and_mask (b : Byte) (x : BitVec 64) : ((b.setWidth 64 &&& x).setWidth 8 : Byte) = b &&& x.setWidth 8 := by
  rw [BitVec.setWidth_and]
  congr 1
  exact BitVec.setWidth_setWidth_of_le _ (by decide)

section
variable {D : Nat} {s : State} (P : PreS D s)
include P

/-- MGF1's registers. -/
theorem dbArgs_ok {H : Hash} (hD : H.D = D) (hD64 : D ≤ 64) {t : State}
    (h : Base Ss vS s t) (h0 : s.mem (s.gpr .a2) ≠ 0) (hfit : D + 2 ≤ kk s - loN s) :
    WP isa (.block (dbArgs H)) t fun t' => Base Ss vS s t' ∧ t'.mem = t.mem ∧
      t'.gpr .s6 = off (Ss s) (kk s - D - 1) ∧ t'.gpr .s7 = BitVec.ofNat 64 D ∧
      t'.gpr .s8 = off (Ss s) (loN s) ∧ t'.gpr .s9 = BitVec.ofNat 64 (kk s - loN s - D - 1) := by
  have F := fits P
  have hk2 : kk s ≤ 1024 := P.k2
  have hl1 := loN_le s
  refine wp_add fun t₁ o₁ e₁ => wp_subi (imm := H.D + 1) (h := by omega) fun t₂ o₂ e₂ =>
    wp_li (imm := H.D) (by omega) fun t₃ o₃ e₃ => wp_add fun t₄ o₄ e₄ => wp_sub fun t₅ o₅ e₅ =>
    wp_subi (imm := H.D + 1) (h := by omega) fun t₆ o₆ e₆ => wp_nil ?_
  have k₆ : Only [.s6, .s7, .s8, .s9] t t₆ := (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans o₆))))).mono
  have k₃ : Only [.s6, .s7] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  have k₄ : Only [.s6, .s7, .s8] t t₄ := (k₃.trans o₄).mono
  refine ⟨h.only F k₆, k₆.mem, ?_, ?_, ?_, ?_⟩
  · rw [o₆.get .s6, o₅.get .s6, o₄.get .s6, o₃.get .s6, e₂, e₁, addr_k P h (by omega), hD, Nat.sub_add_eq]
  · rw [o₆.get .s7, o₅.get .s7, o₄.get .s7, e₃, hD]
  · rw [o₆.get .s8, o₅.get .s8, e₄, k₃.get .s0, k₃.get .s3, h.s0, lo_reg h h0]
  · rw [e₆, e₅, k₄.get .s1, k₄.get .s3, Base.sk h, Base.slo h, k_lo P h0, hD,
      Offset.ofNat_sub_ofNat (by omega), Nat.sub_add_eq]

/-- `clearTop`: `DB`'s first byte ANDed with `c`, saved on entry. -/
theorem clearTop_ok {t : State} (h : Base Ss vS s t) (sp : Spilled s t.mem) (h0 : s.mem (s.gpr .a2) ≠ 0) :
    WP isa (.block clearTop) t fun t' => Base Ss vS s t' ∧
      t'.mem = t.mem.writeW (off (Ss s) (loN s)) (view t.mem (Ss s) (loN s) &&& cS s) := by
  have F := fits P
  have hl1 := loN_le s
  have hP : oP = 1352 := rfl
  have hR : oRsa = 8192 := rfl
  simp only [clearTop]
  refine wp_ld (a := off (Ss s) (oP + 40)) (by rw [h.s0]) (oP_al P 5)
    (by rw [h.wr]; exact sc_inR F (by omega) _) fun t₁ o₁ e₁ => wp_add fun t₂ o₂ e₂ => ?_
  have x2 : t₂.gpr .a1 = off (Ss s) (loN s) := by rw [e₂, o₁.get .s0, o₁.get .s3, lo_reg h h0, h.s0]
  have K₂ : Only [.t2, .a1] t t₂ := (o₁.trans o₂).mono
  refine wp_lbu (a := off (Ss s) (loN s)) (by rw [x2, BitVec.add_zero])
    (by rw [K₂.wr, h.wr]; exact sc_inR F (o := loN s) (n := 1) (by omega) _) fun t₃ o₃ e₃ =>
    wp_and fun t₄ o₄ e₄ => ?_
  have K₄ : Only [.t2, .a1, .a2] t t₄ := (K₂.trans (o₃.trans o₄)).mono
  refine wp_sb (a := off (Ss s) (loN s)) (by rw [o₄.get .a1, o₃.get .a1, x2, BitVec.add_zero])
    (by rw [K₄.wr, h.wr]; exact sc_inW F (by omega)) fun t' m' => wp_nil ?_
  have hv : (t₄.gpr .a2).setWidth 8 = view t.mem (Ss s) (loN s) &&& cS s := by
    rw [e₄, e₃, o₃.get .t2, o₂.get .t2, e₁, sp.c, K₂.mem, and_mask]; rfl
  have hm : t'.mem = t.mem.writeW (off (Ss s) (loN s)) (view t.mem (Ss s) (loN s) &&& cS s) := by
    rw [m'.mem, hv, K₄.mem]
  refine ⟨(h.only F K₄).keep F m'.keep (R := [⟨off (Ss s) (loN s), 1⟩])
    (by rw [hm, ← K₄.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (sc_in (by omega))), hm⟩

end

section
variable {Gs : Spec.Mgf1.Hash} {s : State} (P : PreS Gs.len s) {H : Hash} (hH : HashOK H) (hF : H.F ≤ 208)
  (hGh : ∀ x, Gs.hash x = hH.SH.H.hash x) (hGl : Gs.len = H.D) (hGv : Proof.Mgf1.Valid Gs)
include P hH hF hGh hGl hGv

/-- After the checks: `encEm` at `scratch`, with `Base` and the saved
arguments. -/
theorem signEnc_ok {t : State} (E : Entered s t) (h0 : s.mem (s.gpr .a2) ≠ 0)
    (hfit : Gs.len + (stackArg s 10).toNat + 2 ≤ kk s - loN s) {Q : State → Prop}
    (k : ∀ t', Base Ss vS s t' → Spilled s t'.mem →
      Spec.Rsa.bytesAt t'.mem (off (Ss s) 0) (kk s) = encEm Gs s → WP isa priv t' Q) :
    WP isa (signMain H) t Q := by
  have F := fits P
  have hD0 : 0 < Gs.len := hGl ▸ hH.hD0
  have hD64 : Gs.len ≤ 64 := hGl ▸ hH.hD64
  have hk2 : kk s ≤ 1024 := P.k2
  have hl1 := loN_le s
  have Fh := hfits hH
  obtain ⟨hE, hSt, hDg, hCt, hR⟩ := offs
  have hY : oY = 2048 := rfl
  have hP : oP = 1352 := rfl
  have hsalt : (saltB s).length = (stackArg s 10).toNat := bytesAt_length _ _ _
  have hdl : (digB Gs.len s).length = Gs.len := bytesAt_length _ _ _
  have hhl : (hS Gs s).length = Gs.len := hGv.2 _
  unfold signMain hashM
  -- `M'` and `H`.
  refine WP.seq (WP.mono (mPrime_ok P hGl.symm hD0 hD64 E.base (by omega)) fun t₁ ⟨b₁, m₁⟩ => ?_)
  refine WP.seq (WP.seq (wp_mov fun t₂ o₂ e₂ => wp_nil ?_))
  refine WP.mono (hashFixedG_ok F hH hF hGl.symm (sl := (stackArg s 10).toNat)
    (by rw [e₂, Base.ssl b₁, ofNat_toNat]) (b₁.only F o₂) (by omega)) fun t₃ ⟨b₃, _, s₃, d₃⟩ => ?_
  have hM : Spec.Sha256.bytesAt t₂.mem (off (Ss s) oY) (8 + Gs.len + (stackArg s 10).toNat) =
      Spec.RsaPss.zeros 8 ++ digB Gs.len s ++ saltB s := by
    have := mPrime_bytes t.mem (Ss s) (digB Gs.len s) (saltB s) hdl (by rw [hsalt]; omega)
    rw [hsalt] at this
    rw [o₂.mem, m₁]; exact this
  have hh : ∀ i < Gs.len, view t₃.mem (Ss s) (oDig + i) = (hS Gs s).getD i 0 := by
    intro i hi
    have := congrArg (fun l => l.getD i 0) d₃
    simp only [show Spec.Sha256.bytesAt t₃.mem (off (Ss s) oDig) H.D = Spec.Rsa.bytesAt t₃.mem (off (Ss s) oDig) H.D
      from rfl, bytesAt_eq_view, map_range_getD' _ (show i < H.D by omega), hM] at this
    rw [this]; simp only [hS, hGh]
  -- `EM` before masking.
  refine WP.seq (WP.mono (clearEm_ok P b₃) fun t₄ ⟨b₄, m₄⟩ => ?_)
  refine WP.seq (WP.mono (putSalt_ok P hGl.symm hD64 b₄ (by omega)) fun t₅ ⟨b₅, m₅⟩ => ?_)
  have hdig : Spec.Rsa.bytesAt t₅.mem (off (Ss s) oDig) Gs.len = hS Gs s := by
    rw [bytesAt_eq_view]
    refine range_ext hhl fun i hi => ?_
    rw [m₅, view_wb _ _ (by rw [hsalt]; omega) (by omega), ifn (by omega), view_w8 _ _ (by omega) (by omega),
      ifn (by omega), m₄, view_wb _ _ (by rw [List.length_replicate]; omega) (by omega),
      ifn (by rw [List.length_replicate]; omega)]
    exact hh i (by omega)
  refine WP.seq (WP.mono (putH_ok P hGl.symm hD0 hD64 b₅ (by omega)) fun t₆ ⟨b₆, m₆⟩ => ?_)
  have hpre : ∀ o < kk s, view t₆.mem (Ss s) o =
      emPre (kk s) Gs.len (stackArg s 10).toNat (saltB s) (hS Gs s) o :=
    fun o ho => emPre_of hsalt hhl hk2 (by omega) m₄ m₅ (by rw [m₆, hdig]) ho
  -- MGF1 and `clearTop`.
  refine WP.seq (WP.mono (dbArgs_ok P hGl.symm hD64 b₆ h0 (by omega)) fun t₇ ⟨b₇, v₇, x6, x7, x8, x9⟩ => ?_)
  have hsrc : srcB (view t₇.mem (Ss s)) (kk s - Gs.len - 1) Gs.len = hS Gs s := by
    refine range_ext hhl fun i hi => ?_
    rw [v₇, hpre _ (by omega)]
    simp only [emPre]
    rw [ifn (by omega), ifp (by omega), show kk s - Gs.len - 1 + i - (kk s - Gs.len - 1) = i by omega]
  refine WP.seq (WP.mono (mgfXor_ok F hH hF hGh hGl hGv (src := kk s - Gs.len - 1) (srcLen := Gs.len)
    (dst := loN s) (dstLen := kk s - loN s - Gs.len - 1) ⟨by omega, by omega, .inr (by omega), by omega⟩
    b₇ x6 x7 x8 x9) fun t₈ ⟨b₈, v₈⟩ => ?_)
  have sp₈ : Spilled s t₈.mem := E.sp.of_view fun o h1 h2 => by
    rw [v₈ o ⟨by omega, .inr (by omega)⟩, mixV, ifn (by omega), v₇, m₆, view_w8 _ _ (by omega) (by omega),
      ifn (by omega), hdig, view_wb _ _ (by rw [hhl]; omega) (by omega), ifn (by rw [hhl]; omega), m₅,
      view_wb _ _ (by rw [hsalt]; omega) (by omega), ifn (by omega), view_w8 _ _ (by omega) (by omega),
      ifn (by omega), m₄, view_wb _ _ (by rw [List.length_replicate]; omega) (by omega),
      ifn (by rw [List.length_replicate]; omega), s₃ o (by omega) (by simp; omega), o₂.mem, m₁,
      view_wb _ _ (by rw [hsalt]; omega) (by omega), ifn (by omega),
      view_wb _ _ (by rw [hdl]; omega) (by omega), ifn (by omega),
      view_wb _ _ (by rw [List.length_replicate]; omega) (by omega), ifn (by omega)]
  refine WP.seq (WP.mono (clearTop_ok P b₈ sp₈ h0) fun t₉ ⟨b₉, m₉⟩ => ?_)
  refine k t₉ b₉ (sp₈.of_view fun o h1 h2 => by rw [m₉, view_w8 _ _ (by omega) (by omega), ifn (by omega)]) ?_
  rw [bytesAt_eq_view]
  unfold encEm
  refine List.map_congr_left fun o ho => ?_
  have ho := List.mem_range.mp ho
  rw [Nat.zero_add, m₉, view_w8 _ _ (by omega) (by omega)]
  have e8 : ∀ x < kk s, view t₈.mem (Ss s) x = mixV (view t₇.mem (Ss s)) (Spec.Mgf1.mgf1 Gs (hS Gs s)
      (kk s - loN s - Gs.len - 1)) (loN s) (kk s - loN s - Gs.len - 1) x := fun x hx => by
    rw [v₈ x ⟨by omega, .inl (by omega)⟩, hsrc]
  rw [e8 o ho, e8 (loN s) (by omega)]
  have := emT_of (saltB s) (hS Gs s) (Spec.Mgf1.mgf1 Gs (hS Gs s) (kk s - loN s - Gs.len - 1)) (cS s)
    (k := kk s) (sl := (stackArg s 10).toNat) hhl hl1 rfl (by omega) (V := view t₇.mem (Ss s))
    (fun x hx => by rw [v₇]; exact hpre x hx) ho
  by_cases hl : o = loN s
  · subst hl; rw [ifp rfl]; rw [ifp rfl] at this; exact this
  · rw [ifn hl]; rw [ifn hl] at this; exact this

end

end VG.Proof.RsaPss.RISCV64.Sg
