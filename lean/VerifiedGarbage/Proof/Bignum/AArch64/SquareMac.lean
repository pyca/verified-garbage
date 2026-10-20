module

public import VerifiedGarbage.Impl.Bignum.AArch64.Square
public import VerifiedGarbage.Proof.Bignum.AArch64.MulAdd
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! A deferred-carry MAC at a fixed position in a four-word square block. -/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.Square
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem macAt_ok (s : State) (k : Nat) {B : Addr} {Z eD eS : Nat}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B eD)
    (h17 : s.gpr .x17 = off B eS) (h7 : s.gpr .x7 = 0)
    (hS : eS + 8*k + 8 ≤ Z) (hD : eD + 8*k + 8 ≤ Z)
    (hc : carry s < 2 ^ 64) (hk : k < 4) :
    WP isa (.block (VG.Impl.Bignum.AArch64.Square.macAt k)) s fun t =>
      (∃ lo : BitVec 64, t.mem = s.mem.writeW (off B (eD + 8*k)) lo ∧
        lo.toNat + 2 ^ 64 * carry t =
          (s.gpr .x1).toNat * (word s.mem B (eS + 8*k)).toNat +
          carry s + (word s.mem B (eD + 8*k)).toNat ∧ carry t < 2 ^ 64) ∧
      Keep [.x2, .x3, .x4] s t := by
  have enc : (8*k) % 8 = 0 ∧ 8*k < 32768 :=
    ⟨by omega, by omega⟩
  refine WP.keep [.x2, .x3, .x4] ?_ rfl rfl rfl
  unfold VG.Impl.Bignum.AArch64.Square.macAt carry
  unfold carry at hc
  brun [h16, h17, h7, enc, hs.ld hS, hs.ld hD, hs.st hD]
  simp only [Bool.toNat_false, Nat.add_zero, add_ofNat0, add_zero64]
  refine ⟨_, rfl, ?_⟩
  simpa only [Nat.add_assoc] using (mac_val (s.gpr .x1)
    (word s.mem B (eS + 8*k)) (s.gpr .x2) (word s.mem B (eD + 8*k)) s.c hc)

end VG.Proof.Bignum.AArch64.Square
