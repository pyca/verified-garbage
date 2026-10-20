module

public import VerifiedGarbage.Impl.Dsa.AArch64.PublicPower
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtTab
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Direct selection of a public exponentiation-table digit -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.PublicPower
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.PublicPower

/-- Registers for a direct selection, without changing memory. -/
theorem selectHead_ok {s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc v : Nat}
    (hc : CExpCtx s P wx minv X Xc) (hw' : wx < 2 ^ 30) (hv : v < 16)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot wx 8))
    (hn : word s.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa (.block selectHead) s fun t =>
      (t.gpr .x12 = BitVec.ofNat 64 wx ∧ t.gpr .x16 = off P (slot wx (8 + v)) ∧
        t.gpr .x17 = off P (slot wx Crt.aT) ∧ t.mem = s.mem) ∧
      Keep [.x3, .x4, .x12, .x16, .x17] s t := by
  refine WP.keep _ ?_ (by decide) (by decide) (by decide +kernel)
  brun [selectHead, hc.good.x0, hdr_enc (show sW < 32 by decide), hdr_enc (show Crt.sNib < 32 by decide),
    hdr_enc (show Crt.sTab < 32 by decide), hdr_enc (sArr_lt (show Crt.aT < 8 by decide)),
    hc.ld (i := sW) (by decide), hc.ld (i := Crt.sNib) (by decide), hc.ld (i := Crt.sTab) (by decide),
    hc.ld (i := sArr Crt.aT) (sArr_lt (by decide)), hc.good.hdr.hw, hc.good.hdr.harr Crt.aT (by decide), ht, hn]
  have hp : (wx + 2) * v < 2 ^ 40 := by
    have := Nat.mul_le_mul (show wx + 2 ≤ 2 ^ 30 + 2 by omega) (show v ≤ 16 by omega); omega
  rw [show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, ofNat_add_ofNat, ← BitVec.ofNat_mul,
    shl3_ofNat (show 8 * ((wx + 2) * v) < 2 ^ 64 by omega), VG.Offset.add_add]
  congr 1
  unfold slot
  rw [Nat.add_mul (8 : Nat) v]
  grind

/-- Copy the selected table entry; only the destination array changes. -/
theorem select_ok {s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc v : Nat}
    (hc : CExpCtx s P wx minv X Xc) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hv : v < 16)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot wx 8))
    (hn : word s.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa select s fun t => CExpCtx t P wx minv X Xc ∧
      wv t.mem P (slot wx Crt.aT) wx = wv s.mem P (slot wx (8 + v)) wx ∧
      Outside P (slot wx Crt.aT) (8 * wx) s.mem t.mem ∧ Keep mmRegs s t := by
  have hT := slot_le (w := wx) (show Crt.aT < 8 by decide)
  have hE := ent_le wx hv
  have hE0 := slot_mono wx (show 8 ≤ 8 + v by omega)
  have hsep := slot_mono wx (show Crt.aT + 1 ≤ 8 by decide)
  have hz := hc.scrT.nowrap
  unfold select
  refine WP.seq (WP.mono (selectHead_ok hc hw' hv ht hn) fun u ⟨⟨h12, h16, h17, hm⟩, hk⟩ => ?_)
  have hs := hc.scrT.congr hk.wr
  refine WP.mono (copyWords_ok h16 h17 h12 (by omega) (by omega) (by omega)
    (fun i hi => hs.ld (by omega)) (fun i hi => hs.st (by omega))
    (fun i hi b hb => by rw [ofs_off P (by omega)]; omega)) fun t ⟨hval, _, hf, _, _, hkt⟩ => ?_
  rw [hm] at hf hval
  have k := (hk.trans hkt).mono (show ∀ r ∈ [.x3, .x4, .x12, .x16, .x17] ++ [.x3, .x14, .x16, .x17], r ∈ mmRegs by
    decide)
  exact ⟨hc.of_win (Frm.of_outside (hf.mono (o' := slot wx Crt.aT) (n' := 8 * (wx + 2)) (by omega) (by omega))
    (by simp [crtWinRanges])) k.wr (k.gpr .x0 (by decide)), hval, hf, k⟩

end VG.Proof.Dsa.AArch64.PublicPower
