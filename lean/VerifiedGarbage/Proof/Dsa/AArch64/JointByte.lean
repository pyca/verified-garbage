module
public import VerifiedGarbage.Proof.Dsa.AArch64.JointWindow

import VerifiedGarbage.Proof.Dsa.AArch64.JointWindows
import VerifiedGarbage.Proof.Bignum.AArch64.CrtExp
import VerifiedGarbage.Proof.Bignum.AArch64.CrtBuild
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Loading a pair of exponent bytes without secret-dependent addresses -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

/-- After `i` bytes of both exponents (`L` bytes `eb` at `ep` and `fb` at
`fp`) from `t₀`. -/
structure JointByteInv (t₀ : State) (P : Addr) (w : Nat) (minv : BitVec 64)
    (n xc g y : Nat) (ep fp : Addr) (L : Nat) (eb fb : List Byte) (i : Nat) (t : State) : Prop where
  ctx : CExpCtx t P w minv n xc
  tab : JointTab t.mem P w n g y
  ylt : wv t.mem P (slot w aY) w < n
  val : wv t.mem P (slot w aY) w % n = (g ^ pre eb i * y ^ pre fb i) * 2 ^ (64 * w) % n
  idx : word t.mem P (8 * Crt.sI) = BitVec.ofNat 64 i
  e : word t.mem P (8 * Crt.sExp) = ep
  f : word t.mem P (8 * Joint.sExp2) = fp
  len : word t.mem P (8 * Crt.sExpLen) = BitVec.ofNat 64 L
  frm : Frm P (crtExpRanges w) t₀.mem t.mem
  keep : Keep mmRegs t₀ t

/-- Both bytes into `sV`, and the window count 4. -/
theorem jointByteHead_ok {t : State} {P ep fp : Addr} {w n xc i : Nat} {minv : BitVec 64}
    (hc : CExpCtx t P w minv n xc)
    (hi : word t.mem P (8 * Crt.sI) = BitVec.ofNat 64 i)
    (he : word t.mem P (8 * Crt.sExp) = ep) (hf : word t.mem P (8 * Joint.sExp2) = fp)
    {v z : Byte}
    (hrE : InRegions (t.rd ++ t.wr) (ep + BitVec.ofNat 64 i) 1)
    (hrF : InRegions (t.rd ++ t.wr) (fp + BitVec.ofNat 64 i) 1)
    (hv : t.mem (ep + BitVec.ofNat 64 i) = v) (hz : t.mem (fp + BitVec.ofNat 64 i) = z) :
    WP isa (.block Joint.byteHead) t fun u =>
      u.mem = (t.mem.writeW (off P (8 * Crt.sV)) (BitVec.ofNat 64 (256 * v.toNat + z.toNat))).writeW
        (off P (8 * Crt.sBit)) (BitVec.ofNat 64 4) ∧ Keep [.x3, .x4, .x5] t u := by
  have hv' := v.isLt
  refine WP.keep _ ?_ (by decide) (by decide) (by decide +kernel)
  brun [Joint.byteHead, hc.good.x0, hdr_enc (show Crt.sExp < 32 by decide), hdr_enc (show Crt.sI < 32 by decide),
    hdr_enc (show Joint.sExp2 < 32 by decide), hdr_enc (show Crt.sV < 32 by decide),
    hdr_enc (show Crt.sBit < 32 by decide), hc.ld (i := Crt.sExp) (by decide),
    hc.ld (i := Crt.sI) (by decide), hc.ld (i := Joint.sExp2) (by decide), he, hi, hf, hrE, hrF, zext_byte, hv, hz,
    shl_ofNat (show v.toNat * 2 ^ 8 < 2 ^ 64 by omega_arith), ofNat_add_ofNat,
    hc.st (i := Crt.sV) (by decide), hc.st (i := Crt.sBit) (by decide)]
  rw [show v.toNat * 2 ^ 8 + z.toNat = 256 * v.toNat + z.toNat by omega_arith]
  rfl

/-- Read one byte from each exponent, run four joint windows, and advance. -/
theorem jointByte_ok (M : Mont) {t₀ t : State} {P : Addr} {w n xc g y : Nat}
    {minv : BitVec 64} {ep fp : Addr} {L : Nat} {eb fb : List Byte} {i : Nat}
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) n)
    (hL : eb.length = L) (hF : fb.length = L) (hL' : L < 2 ^ 31) (hi : i < L)
    (hrd : ∀ i < L, InRegions (t₀.rd ++ t₀.wr) (ep + BitVec.ofNat 64 i) 1)
    (hbytes : ∀ i (h : i < L), t₀.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega_arith))
    (hout : ∀ i < L, slot w 8 + tabBytes w ≤ ofs P (ep + BitVec.ofNat 64 i))
    (frd : ∀ i < L, InRegions (t₀.rd ++ t₀.wr) (fp + BitVec.ofNat 64 i) 1)
    (fbytes : ∀ i (h : i < L), t₀.mem (fp + BitVec.ofNat 64 i) = fb[i]'(by omega_arith))
    (fout : ∀ i < L, slot w 8 + tabBytes w ≤ ofs P (fp + BitVec.ofNat 64 i))
    (hI : JointByteInv t₀ P w minv n xc g y ep fp L eb fb i t) :
    WP isa (seqs [.block Joint.byteHead, .loop (seqs (Joint.window M.mm)) (.nonzero .x .x3),
      .block Joint.byteNext]) t fun t' =>
      JointByteInv t₀ P w minv n xc g y ep fp L eb fb (i + 1) t' ∧ ((t'.gpr .x3).toNat ≠ 0 ↔ i + 1 ≠ L) := by
  have hn := hI.ctx.scrT.nowrap
  let v := (eb[i]'(by omega_arith)).toNat
  let z := (fb[i]'(by omega_arith)).toNat
  have hv : v < 256 := (eb[i]'(by omega_arith)).isLt
  have hz : z < 256 := (fb[i]'(by omega_arith)).isLt
  have er : InRegions (t.rd ++ t.wr) (ep + BitVec.ofNat 64 i) 1 := by
    rw [hI.keep.rd, hI.keep.wr]; exact hrd i hi
  have fr : InRegions (t.rd ++ t.wr) (fp + BitVec.ofNat 64 i) 1 := by
    rw [hI.keep.rd, hI.keep.wr]; exact frd i hi
  have ev : t.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega_arith) := by
    rw [hI.frm _ fun r hr => Or.inr (by have := (crtExpRanges_ok w r hr).2; have := hout i hi; omega_arith)]
    exact hbytes i hi
  have fv : t.mem (fp + BitVec.ofNat 64 i) = fb[i]'(by omega_arith) := by
    rw [hI.frm _ fun r hr => Or.inr (by have := (crtExpRanges_ok w r hr).2; have := fout i hi; omega_arith)]
    exact fbytes i hi
  simp only [seqs]
  refine WP.seq (WP.mono (jointByteHead_ok hI.ctx hI.idx hI.e hI.f er fr ev fv)
    fun t₁ ⟨hm₁, k₁⟩ => ?_)
  have o1 := writeW_outside t.mem P (d := 8 * Crt.sV) (BitVec.ofNat 64 (256 * v + z)) (by decide)
  have o2 := writeW_outside (t.mem.writeW (off P (8 * Crt.sV)) (BitVec.ofNat 64 (256 * v + z))) P
    (d := 8 * Crt.sBit) (BitVec.ofNat 64 4) (by decide)
  rw [← hm₁] at o2
  have f₁ : Frm P (crtWinRanges w) t.mem t₁.mem :=
    (Frm.of_outside o1 (by simp [crtWinRanges])).trans (Frm.of_outside o2 (by simp [crtWinRanges]))
  have hc₁ := hI.ctx.of_win f₁ k₁.wr (k₁.gpr .x0 (by decide))
  have hY0 := slot_le (w := w) (show aY < 8 by decide)
  have hYe : wv t₁.mem P (slot w aY) w = wv t.mem P (slot w aY) w := by
    rw [o2.wv (by have := hdr_lt_slot w aY (show Crt.sBit < 32 by decide); omega_arith) (by omega_arith),
      o1.wv (by have := hdr_lt_slot w aY (show Crt.sV < 32 by decide); omega_arith) (by omega_arith)]
  have hB0 : JointWinInv t₁ P w minv n xc g y (pre eb i) (pre fb i) v z 0 t₁ := by
    refine ⟨hc₁, hI.tab.of_win f₁ hn, hYe ▸ hI.ylt, ?_, ?_, ?_, Frm.refl _ _ _, Keep.refl _ _⟩
    · rw [hYe, hI.val, Nat.pow_zero, Nat.mul_one, Nat.mul_one, Nat.sub_zero,
        Nat.div_eq_of_lt (show v < 4 ^ 4 from hv), Nat.div_eq_of_lt (show z < 4 ^ 4 from hz),
        Nat.add_zero, Nat.add_zero]
    · rw [o2.word (by decide) (by decide), word_writeW_self, Nat.pow_zero, Nat.mul_one]
    · rw [hm₁, word_writeW_self]
  refine WP.seq (WP.mono (jointWins_ok M hw hw' hR hv hz hB0) fun t₂ h₂ => ?_)
  -- The next byte.
  have hc₂ := h₂.ctx
  have hh₂ : ∀ k < 32, k ≠ Crt.sV → k ≠ Crt.sBit → k ≠ Crt.sNib → k ≠ Crt.sEnt → k ≠ Crt.sJ →
      word t₂.mem P (8 * k) = word t.mem P (8 * k) := fun k hk h1 h2 h3 h4 h5 => by
    rw [h₂.frm.word_eq (crtWinRanges_hdr w hk h1 h2 h3 h4 h5) (by omega_arith), hm₁,
      hdrStore_hdr (i := Crt.sBit) _ _ _ (by decide) hk (Ne.symm h2),
      hdrStore_hdr (i := Crt.sV) _ _ _ (by decide) hk (Ne.symm h1)]
  have hidx₂ := (hh₂ Crt.sI (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hI.idx
  have he₂ := (hh₂ Crt.sExp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hI.e
  have hf₂ := (hh₂ Joint.sExp2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hI.f
  have hlen₂ := (hh₂ Crt.sExpLen (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
    hI.len
  have hlen₂' : (t₂.mem.writeW (off P (8 * Crt.sI)) (BitVec.ofNat 64 (i + 1))).readW (off P (8 * Crt.sExpLen)) 64 =
      BitVec.ofNat 64 L := by
    rw [← hlen₂]; exact hdrStore_hdr (i := Crt.sI) _ _ _ (by decide) (by decide) (by decide)
  refine WP.mono (WP.keep [.x3, .x4] (Q := fun t' => t'.mem = t₂.mem.writeW (off P (8 * Crt.sI))
      (BitVec.ofNat 64 (i + 1)) ∧ t'.gpr .x3 = BitVec.ofNat 64 L - BitVec.ofNat 64 (i + 1)) (by
    brun [Joint.byteNext, hc₂.good.x0, hdr_enc (show Crt.sI < 32 by decide),
      hdr_enc (show Crt.sExpLen < 32 by decide),
      hc₂.ld (i := Crt.sI) (by decide), hc₂.st (i := Crt.sI) (by decide), hidx₂, ofNat_add_ofNat,
      hc₂.ld (i := Crt.sExpLen) (by decide), hlen₂']) (by decide) (by decide) (by decide +kernel))
    fun t' ⟨⟨hm', h3'⟩, k'⟩ => ⟨?_, ?_⟩
  · have o' := writeW_outside t₂.mem P (d := 8 * Crt.sI) (BitVec.ofNat 64 (i + 1)) (by decide)
    rw [← hm'] at o'
    have f' : Frm P (crtExpRanges w) t₂.mem t'.mem := Frm.of_outside o' (by simp [crtExpRanges])
    have hYe : wv t'.mem P (slot w aY) w = wv t₂.mem P (slot w aY) w :=
      o'.wv (by have := hdr_lt_slot w aY (show Crt.sI < 32 by decide); omega_arith) (by omega_arith)
    refine ⟨hc₂.of_frm f' k'.wr (k'.gpr .x0 (by decide)), ?_, hYe ▸ h₂.ylt, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact ⟨by rw [o'.word (by decide) (by decide)]; exact h₂.tab.tab,
        fun j hj => by rw [o'.wv (by have := hdr_lt_slot w (8 + j) (show Crt.sI < 32 by decide); omega_arith)
          (by have := ent_le w hj; omega_arith)]; exact h₂.tab.lt j hj,
        fun j hj => by rw [o'.wv (by have := hdr_lt_slot w (8 + j) (show Crt.sI < 32 by decide); omega_arith)
          (by have := ent_le w hj; omega_arith)]; exact h₂.tab.val j hj⟩
    · rw [hYe, h₂.val, pre_succ eb (by omega_arith), pre_succ fb (by omega_arith)]
      simp only [Nat.reducePow, Nat.reduceSub, Nat.pow_zero, Nat.div_one]
      simp only [v, z]
      ac_rfl
    · rw [hm', word_writeW_self]
    · rw [hm', hdrStore_hdr (i := Crt.sI) _ _ _ (by decide) (by decide) (by decide)]; exact he₂
    · rw [hm', hdrStore_hdr (i := Crt.sI) _ _ _ (by decide) (by decide) (by decide)]; exact hf₂
    · rw [hm', hdrStore_hdr (i := Crt.sI) _ _ _ (by decide) (by decide) (by decide)]; exact hlen₂
    · exact ((hI.frm.trans (f₁.mono (crtWinRanges_sub w))).trans
        (h₂.frm.mono (crtWinRanges_sub w))).trans f'
    · exact (((hI.keep.trans k₁).trans h₂.keep).trans k').mono (by decide)
  · rw [h3', VG.Offset.ofNat_sub_ofNat (show i + 1 ≤ L by omega_arith), cnt_ne (by omega_arith)]
    omega_arith

/-- Both equal-length exponent strings are scanned sequentially. -/
theorem jointBytes_ok (M : Mont) {t : State} {P : Addr} {w n xc g y : Nat}
    {minv : BitVec 64} {ep fp : Addr} {L : Nat} {eb fb : List Byte}
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) n)
    (hL : eb.length = L) (hF : fb.length = L) (hL0 : 0 < L) (hL' : L < 2 ^ 31)
    (hrd : ∀ i < L, InRegions (t.rd ++ t.wr) (ep + BitVec.ofNat 64 i) 1)
    (hbytes : ∀ i (h : i < L), t.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega_arith))
    (hout : ∀ i < L, slot w 8 + tabBytes w ≤ ofs P (ep + BitVec.ofNat 64 i))
    (frd : ∀ i < L, InRegions (t.rd ++ t.wr) (fp + BitVec.ofNat 64 i) 1)
    (fbytes : ∀ i (h : i < L), t.mem (fp + BitVec.ofNat 64 i) = fb[i]'(by omega_arith))
    (fout : ∀ i < L, slot w 8 + tabBytes w ≤ ofs P (fp + BitVec.ofNat 64 i))
    (h : JointByteInv t P w minv n xc g y ep fp L eb fb 0 t) :
    WP isa (Joint.bytes M.mm) t (JointByteInv t P w minv n xc g y ep fp L eb fb L) :=
  count_loop (cr := .x3) (n := L) hL0 (JointByteInv t P w minv n xc g y ep fp L eb fb)
    (fun _ hi _ hI => jointByte_ok M hw hw' hR hL hF hL' hi hrd hbytes hout frd fbytes fout hI) h

end VG.Proof.Dsa.AArch64
