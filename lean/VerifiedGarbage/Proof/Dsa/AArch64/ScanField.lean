module
public import VerifiedGarbage.Impl.Dsa.AArch64.Checks
public import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup
public import VerifiedGarbage.Proof.Dsa.DomainShape

import VerifiedGarbage.Proof.Dsa.AArch64.SignificantLoop
import VerifiedGarbage.Proof.Dsa.AArch64.Operands
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract

/-! # Scanning modulus buffers through the saved DSA fields -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem scanField_ok {s : State} {B p : Addr} {Z : Nat} (hs : Scr s B Z)
    (hdi : s.gpr .x0 = B) (hZ : pWorkspace ≤ Z) (fp fl : Field) {bytes : List Byte}
    (hp : word s.mem B fp.offset = p)
    (hl : word s.mem B fl.offset = BitVec.ofNat 64 bytes.length)
    (hsrc : Src s B Z p bytes) (h1 : 0 < bytes.length) (h64 : bytes.length < 2 ^ 64) :
    WP isa (.seq (.block [Core.field .x1 fp, Core.field .x9 fl])
      Checks.significant) s fun t =>
      t.gpr .x8 = BitVec.ofNat 64 (VG.Proof.Dsa.significant bytes).1 ∧
      t.gpr .x10 = (VG.Proof.Dsa.significant bytes).2.zeroExtend 64 ∧
      t.mem = s.mem ∧ Keep [.x3, .x8, .x10, .x1, .x9] s t := by
  refine WP.seq (WP.mono (WP.keep [.x1, .x9] (Q := fun u =>
    u.gpr .x1 = p ∧ u.gpr .x9 = BitVec.ofNat 64 bytes.length ∧ u.mem = s.mem) ?_ rfl rfl rfl)
    fun u ⟨⟨hup, hul, hum⟩, hku⟩ => ?_)
  · brun [Core.field, hdi, field_enc fp, field_enc fl, hp, hl,
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds fp).2 hZ),
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds fl).2 hZ)]
  refine WP.mono (significant_ok hup hul (hsrc.congrK (by rw [hum]; exact InScr.refl _ _ _) hku) h1 h64)
    fun t ⟨ht8, ht9, htm, hkt⟩ => ⟨ht8, ht9, htm.trans hum, (hku.trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64
