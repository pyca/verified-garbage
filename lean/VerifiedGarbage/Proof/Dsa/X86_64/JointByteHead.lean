module

public import VerifiedGarbage.Proof.Dsa.X86_64.JointByte
public import VerifiedGarbage.Proof.Dsa.X86_64.JointWindows

/-! # Loading a pair of exponent bytes without secret-dependent addresses -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem jointByteHeadInv_ok {t₀ t : State} {P : Addr} {w n xc g y : Nat}
    {minv : BitVec 64} {ep fp : Addr} {L : Nat} {eb fb : List Byte} {i : Nat}
    (hL : eb.length = L) (hF : fb.length = L) (hi : i < L)
    (hrd : ∀ i < L, InRegions (t₀.rd ++ t₀.wr) (ep + BitVec.ofNat 64 i) 1)
    (hbytes : ∀ i (h : i < L), t₀.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega))
    (hout : ∀ i < L, slot w 8 + tabBytes w ≤ ofs P (ep + BitVec.ofNat 64 i))
    (frd : ∀ i < L, InRegions (t₀.rd ++ t₀.wr) (fp + BitVec.ofNat 64 i) 1)
    (fbytes : ∀ i (h : i < L), t₀.mem (fp + BitVec.ofNat 64 i) = fb[i]'(by omega))
    (fout : ∀ i < L, slot w 8 + tabBytes w ≤ ofs P (fp + BitVec.ofNat 64 i))
    (hI : JointByteInv t₀ P w minv n xc g y ep fp L eb fb i t) :
    WP isa (.block Joint.byteHead) t fun t₁ =>
      JointWinInv t₁ P w minv n xc g y (pre eb i) (pre fb i)
        (eb[i]'(by omega)).toNat (fb[i]'(by omega)).toNat 0 t₁ := by
  have hn := hI.ctx.scrT.nowrap
  let v := (eb[i]'(by omega)).toNat
  let z := (fb[i]'(by omega)).toNat
  have hv : v < 256 := (eb[i]'(by omega)).isLt
  have hz : z < 256 := (fb[i]'(by omega)).isLt
  have er : InRegions (t.rd ++ t.wr) (ep + BitVec.ofNat 64 i) 1 := by
    rw [hI.keep.2.1, hI.keep.2.2]; exact hrd i hi
  have fr : InRegions (t.rd ++ t.wr) (fp + BitVec.ofNat 64 i) 1 := by
    rw [hI.keep.2.1, hI.keep.2.2]; exact frd i hi
  have ev : t.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega) := by
    rw [hI.frm _ fun r hr => Or.inr (by have := (crtExpRanges_ok w r hr).2; have := hout i hi; omega)]
    exact hbytes i hi
  have fv : t.mem (fp + BitVec.ofNat 64 i) = fb[i]'(by omega) := by
    rw [hI.frm _ fun r hr => Or.inr (by have := (crtExpRanges_ok w r hr).2; have := fout i hi; omega)]
    exact fbytes i hi
  refine WP.mono (jointByteHead_ok hI.ctx hI.idx hI.e hI.f er fr ev fv)
    fun t₁ ⟨hm₁, k₁⟩ => ?_
  have o1 := writeW_outside t.mem P (d := 8 * Crt.sV) (BitVec.ofNat 64 (256 * v + z)) (by decide)
  have o2 := writeW_outside (t.mem.writeW (off P (8 * Crt.sV)) (BitVec.ofNat 64 (256 * v + z))) P
    (d := 8 * Crt.sBit) (4 : BitVec 64) (by decide)
  rw [← hm₁] at o2
  have f₁ : Frm P (crtWinRanges w) t.mem t₁.mem :=
    (Frm.of_outside o1 (by simp [crtWinRanges])).trans (Frm.of_outside o2 (by simp [crtWinRanges]))
  have hc₁ := hI.ctx.of_win f₁ k₁.2.2 (k₁.gpr (by decide))
  have hY0 := slot_le (w := w) (show aY < 8 by decide)
  have hYe : wv t₁.mem P (slot w aY) w = wv t.mem P (slot w aY) w := by
    rw [o2.wv (by have := hdr_lt_slot w aY (show Crt.sBit < 32 by decide); omega) (by omega),
      o1.wv (by have := hdr_lt_slot w aY (show Crt.sV < 32 by decide); omega) (by omega)]
  have hB0 : JointWinInv t₁ P w minv n xc g y (pre eb i) (pre fb i) v z 0 t₁ := by
    refine ⟨hc₁, hI.tab.of_win f₁ hn, hYe ▸ hI.ylt, ?_, ?_, ?_, Frm.refl _ _ _, Keep.refl _ _⟩
    · rw [hYe, hI.val, Nat.pow_zero, Nat.mul_one, Nat.mul_one, Nat.sub_zero,
        Nat.div_eq_of_lt (show v < 4 ^ 4 from hv), Nat.div_eq_of_lt (show z < 4 ^ 4 from hz),
        Nat.add_zero, Nat.add_zero]
    · rw [o2.word (by decide) (by decide), word_writeW_self, Nat.pow_zero, Nat.mul_one]
    · rw [hm₁, word_writeW_self]; rfl
  exact hB0

end VG.Proof.Dsa.X86_64
