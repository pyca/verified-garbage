module

public import VerifiedGarbage.Proof.Bignum.AArch64.WindowRawTriangle
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightDiagonal

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowRaw
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64.ProductEight (productBase)
open VG.Proof.Bignum.AArch64.SquareEight (diagonal_finish_ok)
open VG.Impl.Bignum.AArch64.WindowRaw

theorem raw_ok {s : State} {B : Addr} {Z k : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hH : Hdr s.mem B (8*k) minv)
    (hZ : slot (8*k) 8 ≤ Z) (hk : 0 < k) (hk' : k < 2 ^ 56)
    {a : Nat} (ha : a < 8) (ha1 : a ≠ Public.aAcc) (ha2 : a ≠ Public.aTmp) :
    WP isa (VG.Impl.Bignum.AArch64.WindowRaw.square a) s fun t =>
      wv t.mem B (productBase k) (16*k) =
        wv s.mem B (slot (8*k) a) (8*k) * wv s.mem B (slot (8*k) a) (8*k) ∧
      Outside B (productBase k) (8*(16*k+2)) s.mem t.mem ∧
      t.gpr .x8 = off B (productBase k) ∧ t.gpr .x10 = off B (slot (8*k) Public.aN) ∧
      t.gpr .x12 = BitVec.ofNat 64 (8*k) ∧ t.gpr .x15 = minv ∧ t.gpr .x7 = 0 ∧ Keep regs s t := by
  have hn := hs.nowrap
  have hP : productBase k+8*(16*k+2) ≤ Z := by
    unfold productBase slot Public.aAcc at *
    omega
  have hA : slot (8*k) a+64*k ≤ Z := by
    have := slot_le (w := 8*k) ha
    omega
  have sep : slot (8*k) a+64*k ≤ productBase k ∨
      productBase k+8*(16*k+2) ≤ slot (8*k) a := by
    have := slot_sep (w := 8*k) ha1
    have := slot_sep (w := 8*k) ha2
    unfold productBase slot Public.aAcc Public.aTmp at *
    omega
  have hp : WP isa (.seq (triangle a) VG.Impl.Bignum.AArch64.WideLoops.diagonal) s (fun t =>
      wv t.mem B (productBase k) (16*k) =
        wv s.mem B (slot (8*k) a) (8*k) * wv s.mem B (slot (8*k) a) (8*k) ∧
      Outside B (productBase k) (8*(16*k+2)) s.mem t.mem ∧
      t.gpr .x8 = off B (productBase k) ∧ t.gpr .x10 = off B (slot (8*k) Public.aN) ∧
      t.gpr .x12 = BitVec.ofNat 64 (8*k) ∧ t.gpr .x15 = minv ∧ t.gpr .x7 = 0 ∧ Keep regs s t) :=
    WP.seq (WP.mono (triangle_ok hs h0 hH hZ hk hk' ha ha1 ha2)
      (fun v ⟨hv, ho, h8, h9, h10, h12, h15, h7, kv⟩ => by
        have hcross : Square.crossValue v.mem B (slot (8*k) a) (8*k) =
            Square.crossValue s.mem B (slot (8*k) a) (8*k) := by
          apply Square.crossValue_congr
          intro j hj
          exact ho.word (by omega) (by omega)
        have hread := ho.wv (d := slot (8*k) a) (k := 8*k) (by omega) (by omega)
        exact WP.mono (diagonal_finish_ok (hs.congr kv.wr) h8 h9 h12 h7 hk hk' hP hA sep
          (hv.trans hcross.symm)) fun t ⟨ht, hto, kt⟩ =>
            ⟨by simpa only [hread] using ht, ho.trans hto,
              (kt.gpr _ (by decide)).trans h8, (kt.gpr _ (by decide)).trans h10,
              (kt.gpr _ (by decide)).trans h12, (kt.gpr _ (by decide)).trans h15,
              (kt.gpr _ (by decide)).trans h7, (kv.trans kt).mono (by decide)⟩))
  exact hp

theorem raw_width_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (hw : 16 ≤ w) (hw' : w < 2 ^ 31) (hmod : w % 8 = 0)
    {a : Nat} (ha : a < 8) (ha1 : a ≠ Public.aAcc) (ha2 : a ≠ Public.aTmp) :
    WP isa (VG.Impl.Bignum.AArch64.WindowRaw.square a) s fun t =>
      wv t.mem B (slot w Public.aAcc+16) (2*w) =
        wv s.mem B (slot w a) w * wv s.mem B (slot w a) w ∧
      Outside B (slot w Public.aAcc+16) (8*(2*w+2)) s.mem t.mem ∧
      t.gpr .x8 = off B (slot w Public.aAcc+16) ∧ t.gpr .x10 = off B (slot w Public.aN) ∧
      t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x15 = minv ∧ t.gpr .x7 = 0 ∧ Keep regs s t := by
  have he : w = 8*(w/8) := by omega
  have hH' : Hdr s.mem B (8*(w/8)) minv := he ▸ hH
  have hZ' : slot (8*(w/8)) 8 ≤ Z := he ▸ hZ
  have hlen : 16*(w/8) = 2*w := by omega
  have hp := raw_ok hs h0 hH' hZ' (by omega) (by omega) ha ha1 ha2
  simpa only [productBase, ← he, hlen] using hp

end VG.Proof.Bignum.AArch64.WindowRaw
