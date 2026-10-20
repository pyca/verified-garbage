module
public import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyCheck
public import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyDerive

import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyDerivePre
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.DeriveVerified

/-! # Verified call of key derivation from the generation controller -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64

theorem keygen_derive_call (v : Backend) {s t : State} (h : GenerateKeyABI v.stack s)
    (hsp : t.sp = randomBase s)
    (hw : word t.mem (randomBase s) 0 = stackArg s 2)
    (hdi : t.gpr .x0 = s.gpr .x0) (hsi : t.gpr .x1 = s.gpr .x1)
    (hdx : t.gpr .x2 = s.gpr .x3) (hcx : t.gpr .x3 = s.gpr .x4)
    (h8 : t.gpr .x4 = s.gpr .x5) (h9 : t.gpr .x5 = off (randomBase s) Random.oNonce)
    (h6 : t.gpr .x6 = s.gpr .x6) (h7 : t.gpr .x7 = stackArg s 1)
    (hrd : t.rd = s.rd) (hwr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr) :
    WP isa (.call (keygenDeriveName v) (Generate.deriveKey v.mul)) t fun u =>
      let res := Spec.Dsa.deriveKeyBytes (keygenInput s).pLen (keygenInput s).qLen
        (Spec.Rsa.bytesAt t.mem (s.gpr .x3) (s.gpr .x4).toNat)
        (Spec.Rsa.bytesAt t.mem (off (randomBase s) Random.oNonce) (s.gpr .x6).toNat)
      u.rd = t.rd ∧ u.wr = t.wr ∧ u.sp = t.sp ∧
      (∀ r ∈ preserved, r ≠ .x30 → u.gpr r = t.gpr r) ∧
      Frame (keygenDeriveWr s ++ [below (randomBase s) v.stack]) t.mem u.mem ∧
      ((u.gpr .x0).setWidth 32).toNat = Spec.Dsa.signStatus res ∧
      Spec.Rsa.bytesAt u.mem (s.gpr .x0) (s.gpr .x1).toNat =
        res.getD (List.replicate (s.gpr .x1).toNat 0) ∧
      (∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64) := by
  obtain ⟨hc, hcw⟩ := keygen_derive_covers h hrd hwr
  have hd := v.deriveDepth
  have hb := v.stackBound
  refine WP.callFV v.deriveVerified.1
    (keygen_derive_pre h hsp hw hdi hsi hdx hcx h8 h9 h6 h7) hc hcw
    (fun u hur huw husp hf huc hv hp => ?_) (by omega)
  sig_post [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, deriveStackArgs] at hp
  simp only [hdi, hsi, hdx, hcx, h8, h9, h6] at hp
  refine ⟨hur, huw, husp, huc, ?_, hp.1, hp.2, hv⟩
  rw [hsp] at hf
  exact Frame.below_mono hf hd (by omega)

end VG.Proof.Dsa.AArch64
