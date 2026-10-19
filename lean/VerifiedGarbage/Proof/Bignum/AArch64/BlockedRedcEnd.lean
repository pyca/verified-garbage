module
public import VerifiedGarbage.Proof.Bignum.AArch64.Run

import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Ed25519.Word64

@[expose] public section

namespace VG.Proof.Bignum.AArch64.BlockedRedc
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)

theorem shl3_ofNat {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n <<< 3 = BitVec.ofNat 64 (8 * n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt hn, BitVec.toNat_ofNat]
  congr 1
  exact Nat.mul_comm n 8

theorem endSetup_ok {s : State} {B : Addr} {Z e w : Nat}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (h8 : s.gpr .x8 = off B e)
    (hZ : 256 ≤ Z) (hw : w < 2 ^ 64)
    (hW : word s.mem B (8 * sW) = BitVec.ofNat 64 w) :
    WP isa (.block [ldh .x12 sW, .lsl .x .x16 .x12 3, .add .x .x16 .x8 .x16]) s fun t =>
      (t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x16 = off B (e + 8 * w) ∧ t.mem = s.mem) ∧
      Keep [.x12, .x16] s t := by
  refine WP.keep [.x12, .x16] ?_ rfl rfl rfl
  brun [h0, h8, hW, shl3_ofNat hw, hs.ld (show 8 * sW + 8 ≤ Z by unfold sW; omega)]

theorem endStores_ok {s : State} {B : Addr} {Z e w : Nat}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B (e + 8 * w))
    (h7 : s.gpr .x7 = 0) (hT : e + 8 * (w + 2) ≤ Z) :
    WP isa (.block [st .x10 .x16, st .x7 .x16 8]) s fun t =>
      (wv t.mem B e (w + 2) = wv s.mem B e w + 2 ^ (64 * w) * (s.gpr .x10).toNat ∧
        Outside B (e + 8 * w) 16 s.mem t.mem) ∧ Keep [] s t := by
  have hn := hs.nowrap
  refine WP.mono (WP.keep [] (Q := fun t =>
    t.mem = (s.mem.writeW (off B (e + 8 * w)) (s.gpr .x10)).writeW
      (off B (e + 8 * w + 8)) (0 : Word))
    (by brun [h16, h7, hs.st (show e + 8 * w + 8 ≤ Z by omega),
      hs.st (show e + 8 * w + 8 + 8 ≤ Z by omega)]) rfl rfl rfl) fun t ⟨hm, kt⟩ => ?_
  refine ⟨⟨?_, ?_⟩, kt⟩
  · have he : wv ((s.mem.writeW (off B (e + 8 * w)) (s.gpr .x10)).writeW
          (off B (e + 8 * w + 8)) (0 : Word)) B e (w + 2) =
        wv s.mem B e w + 2 ^ (64 * w) * (s.gpr .x10).toNat := by
      rewrite [show e + 8 * w + 8 = e + 8 * (w + 1) by omega,
        show w + 2 = (w + 1) + 1 by omega,
        wv_writeW_top _ B e (w + 1) _ (by omega), wv_writeW_top _ B e w _ (by omega)]
      simp only [show (0 : Word).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]
    exact (congrArg (fun m : Mem => wv m B e (w + 2)) hm).trans he
  · have ho := ((writeW_outside s.mem B (s.gpr .x10) (d := e + 8 * w) (by omega)).mono (n' := 16)
      (Nat.le_refl _) (by omega)).trans
      ((writeW_outside (s.mem.writeW (off B (e + 8 * w)) (s.gpr .x10)) B (0 : Word)
        (d := e + 8 * w + 8) (by omega)).mono (by omega) (by omega))
    intro x hx
    exact (congrArg (fun m : Mem => m x) hm).trans (ho x hx)

theorem endModulus_ok {s : State} {B : Addr} {Z : Nat}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hZ : 256 ≤ Z) :
    WP isa (.block [ldh .x10 (sArr Public.aN)]) s fun t =>
      (t.gpr .x10 = word s.mem B (8 * sArr Public.aN) ∧ t.mem = s.mem) ∧ Keep [.x10] s t := by
  refine WP.keep [.x10] ?_ rfl rfl rfl
  brun [h0, hs.ld (show 8 * sArr Public.aN + 8 ≤ Z by unfold sArr Public.aN; omega)]

end VG.Proof.Bignum.AArch64.BlockedRedc
