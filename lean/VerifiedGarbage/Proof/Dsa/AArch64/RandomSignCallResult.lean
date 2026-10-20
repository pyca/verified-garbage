module

public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCall
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallLayout
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallPre
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.SigningABI

/-! The supplied-nonce call's result, with the wrapper's argument mapping. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64

def randomCallResult (s t : State) : Option (List Byte) :=
  Spec.Dsa.signBytes (s.gpr .x5).toNat (s.gpr .x6).toNat
    (Spec.Rsa.bytesAt t.callEntry.mem (s.gpr .x3) (s.gpr .x4).toNat)
    (Spec.Rsa.bytesAt t.callEntry.mem (off (randomBase s) Random.oNonce) (s.gpr .x6).toNat)
    (Spec.Rsa.bytesAt t.callEntry.mem (s.gpr .x7) (stackArg s 0).toNat)

theorem random_signer_outcome (v : Backend) {s t : State} (h : RandomSignABI v.stack s)
    (hsp : t.sp = randomBase s)
    (hw : ∀ i < 3, word t.mem (randomBase s) (8 * i) = randomCallArg s i)
    (hdi : t.gpr .x0 = s.gpr .x0) (hsi : t.gpr .x1 = s.gpr .x1)
    (hdx : t.gpr .x2 = s.gpr .x3) (hcx : t.gpr .x3 = s.gpr .x4)
    (h8 : t.gpr .x4 = s.gpr .x5) (h9 : t.gpr .x5 = off (randomBase s) Random.oNonce)
    (h6 : t.gpr .x6 = s.gpr .x6) (h7 : t.gpr .x7 = s.gpr .x7)
    (hrd : t.rd = s.rd) (hwr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr) :
    WP isa (.call (randomSignerName v) (SignVerify.sign v.mul)) t fun u =>
      u.rd = t.rd ∧ u.wr = t.wr ∧ u.sp = t.sp ∧
      (∀ r ∈ preserved, r ≠ .x30 → u.gpr r = t.gpr r) ∧
      Frame (randomCallWr s ++ [below (randomBase s) v.stack]) t.mem u.mem ∧
      ((u.gpr .x0).setWidth 32).toNat = Spec.Dsa.signStatus (randomCallResult s t) ∧
      Spec.Rsa.bytesAt u.mem (s.gpr .x0) (s.gpr .x1).toNat =
        (randomCallResult s t).getD (List.replicate (s.gpr .x1).toNat 0) ∧
      ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64 := by
  obtain ⟨hc, hcw⟩ := random_call_covers h hrd hwr
  refine WP.mono (random_signer_call v
    (random_call_pre h hsp hw hdi hsi hdx hcx h8 h9 h6 h7) hc hcw)
    fun u ⟨hur, huw, husp, huc, hf, hp, hv⟩ => ?_
  have hE (i : Nat) (hi : i < 3) :
      stackArg (t.callEntry.withRegions (randomCallRd s) (randomCallWr s)) i = randomCallArg s i :=
    (random_call_stackArg hsp _ _ i).trans (hw i hi)
  sig_post [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, dsaSignStackArgs] at hp
  sig_post [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, dsaSignStackArgs] at hp
  simp only [hdi, hsi, hdx, hcx, h8, h9, h6, h7, hE 0 (by decide),
    randomCallArg] at hp
  exact ⟨hur, huw, husp, huc, by rw [hsp] at hf; exact hf, hp.1, hp.2, hv⟩

end VG.Proof.Dsa.AArch64
