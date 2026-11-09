module

public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCall
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallLayout
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignInputs
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

/-- The signer's validity of the wrapper's key, which the signer's contract
asks of the key it is called with. -/
def RandomValid (S : Signer) (s : State) : Prop :=
  S.valid (randomInput s).pLen (randomInput s).qLen (randomInput s).key = true

/-- The signer's contract at the wrapper's call boundary, for a key the
signer accepts. -/
theorem random_call_pre_with (S : Signer) {s t : State} (h : RandomSignABI S.stack s)
    (hsp : t.sp = randomBase s)
    (hw : ∀ i < 3, word t.mem (randomBase s) (8 * i) = randomCallArg s i)
    (hdi : t.gpr .x0 = s.gpr .x0) (hsi : t.gpr .x1 = s.gpr .x1)
    (hdx : t.gpr .x2 = s.gpr .x3) (hcx : t.gpr .x3 = s.gpr .x4)
    (h8 : t.gpr .x4 = s.gpr .x5) (h9 : t.gpr .x5 = off (randomBase s) Random.oNonce)
    (h6 : t.gpr .x6 = s.gpr .x6) (h7 : t.gpr .x7 = s.gpr .x7)
    (hkey : Spec.Rsa.bytesAt t.mem (s.gpr .x3) (s.gpr .x4).toNat = (randomInput s).key)
    (hv : RandomValid S s) :
    (signContractWith S.valid abi S.stack).pre (t.callEntry.withRegions (randomCallRd s) (randomCallWr s)) := by
  refine signWith_of_pre (random_call_pre h hsp hw hdi hsi hdx hcx h8 h9 h6 h7) ?_
  simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    State.callEntry_gpr _ (r := .x4) (by decide), State.callEntry_gpr _ (r := .x6) (by decide),
    State.callEntry_gpr _ (r := .x2) (by decide), State.callEntry_gpr _ (r := .x3) (by decide),
    h8, h6, hdx, hcx, hkey]
  exact hv

theorem random_signer_outcome (S : Signer) {s t : State} (h : RandomSignABI S.stack s)
    (hsp : t.sp = randomBase s)
    (hw : ∀ i < 3, word t.mem (randomBase s) (8 * i) = randomCallArg s i)
    (hdi : t.gpr .x0 = s.gpr .x0) (hsi : t.gpr .x1 = s.gpr .x1)
    (hdx : t.gpr .x2 = s.gpr .x3) (hcx : t.gpr .x3 = s.gpr .x4)
    (h8 : t.gpr .x4 = s.gpr .x5) (h9 : t.gpr .x5 = off (randomBase s) Random.oNonce)
    (h6 : t.gpr .x6 = s.gpr .x6) (h7 : t.gpr .x7 = s.gpr .x7)
    (hrd : t.rd = s.rd) (hwr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr)
    (hkey : Spec.Rsa.bytesAt t.mem (s.gpr .x3) (s.gpr .x4).toNat = (randomInput s).key)
    (hv : RandomValid S s) :
    WP isa (.call S.name S.code) t fun u =>
      u.rd = t.rd ∧ u.wr = t.wr ∧ u.sp = t.sp ∧
      (∀ r ∈ preserved, r ≠ .x30 → u.gpr r = t.gpr r) ∧
      Frame (randomCallWr s ++ [below (randomBase s) S.stack]) t.mem u.mem ∧
      ((u.gpr .x0).setWidth 32).toNat = Spec.Dsa.signStatus (randomCallResult s t) ∧
      Spec.Rsa.bytesAt u.mem (s.gpr .x0) (s.gpr .x1).toNat =
        (randomCallResult s t).getD (List.replicate (s.gpr .x1).toNat 0) ∧
      ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64 := by
  obtain ⟨hc, hcw⟩ := random_call_covers h hrd hwr
  refine WP.mono (random_signer_call S
    (random_call_pre_with S h hsp hw hdi hsi hdx hcx h8 h9 h6 h7 hkey hv) hc hcw)
    fun u ⟨hur, huw, husp, huc, hf, hp, hv⟩ => ?_
  have hE (i : Nat) (hi : i < 3) :
      stackArg (t.callEntry.withRegions (randomCallRd s) (randomCallWr s)) i = randomCallArg s i :=
    (random_call_stackArg hsp _ _ i).trans (hw i hi)
  sig_post [signContractWith, Spec.Dsa.signSig, abi, argRegs, dsaSignStackArgs] at hp
  sig_post [signContractWith, Spec.Dsa.signSig, abi, argRegs, dsaSignStackArgs] at hp
  simp only [hdi, hsi, hdx, hcx, h8, h9, h6, h7, hE 0 (by decide),
    randomCallArg] at hp
  exact ⟨hur, huw, husp, huc, by rw [hsp] at hf; exact hf, hp.1, hp.2, hv⟩

end VG.Proof.Dsa.AArch64
