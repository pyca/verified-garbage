module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCall
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallLayout
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignInputs
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallPre
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.SigningABI
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallMemory
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallGeometry
import VerifiedGarbage.Proof.Framework.Offset

/-! The supplied-nonce call's result, with the wrapper's argument mapping. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64

def randomCallResult (s t : State) : Option (List Byte) :=
  Spec.Dsa.signBytes (s.gpr .r9).toNat (stackArg s 0).toNat
    (Spec.Rsa.bytesAt t.callEntry.mem (s.gpr .rcx) (s.gpr .r8).toNat)
    (Spec.Rsa.bytesAt t.callEntry.mem (off (randomBase s) Random.oNonce) (stackArg s 0).toNat)
    (Spec.Rsa.bytesAt t.callEntry.mem (stackArg s 1) (stackArg s 2).toNat)

/-- The signer's validity of the wrapper's key, which the signer's contract
asks of the key it is called with. -/
def RandomValid (S : Signer) (s : State) : Prop :=
  S.valid (randomInput s).pLen (randomInput s).qLen (randomInput s).key = true

/-- Writing the return address leaves the key unchanged. -/
theorem random_callEntry_key {extra : Nat} {s t : State} (h : RandomSignABI extra s)
    (hsp : t.gpr .rsp = randomBase s) :
    Spec.Rsa.bytesAt t.callEntry.mem (s.gpr .rcx) (s.gpr .r8).toNat =
      Spec.Rsa.bytesAt t.mem (s.gpr .rcx) (s.gpr .r8).toNat := by
  have hsub : Region.Sub ⟨randomBase s - 8, 8⟩ (below (s.gpr .rsp) (extra + 256)) := by
    rw [random_callBase extra s]
    exact Offset.sub_base _ (by omega)
  exact random_callEntry_bytes hsp
    (((h.stackKey.sub_left hsub).symm).sep (Region.contains_self _ _) (Region.contains_self _ _)) (s.gpr .r8).isLt

/-- The signer's contract at the wrapper's call boundary, for a key the
signer accepts. -/
theorem random_call_pre_with (S : Signer) {s t : State} (h : RandomSignABI S.stack s)
    (hsp : t.gpr .rsp = randomBase s)
    (hw : ∀ i < 5, word t.mem (randomBase s) (8 * i) = randomCallArg s i)
    (hdi : t.gpr .rdi = s.gpr .rdi) (hsi : t.gpr .rsi = s.gpr .rsi)
    (hdx : t.gpr .rdx = s.gpr .rcx) (hcx : t.gpr .rcx = s.gpr .r8)
    (h8 : t.gpr .r8 = s.gpr .r9) (h9 : t.gpr .r9 = off (randomBase s) Random.oNonce)
    (hkey : Spec.Rsa.bytesAt t.mem (s.gpr .rcx) (s.gpr .r8).toNat = (randomInput s).key)
    (hv : RandomValid S s) :
    (signContractWith S.valid abi S.stack).pre (t.callEntry.withRegions (randomCallRd s) (randomCallWr s)) := by
  have hpre := random_call_pre h hsp hw hdi hsi hdx hcx h8 h9
  have hE0 : stackArg (t.callEntry.withRegions (randomCallRd s) (randomCallWr s)) 0 = randomCallArg s 0 :=
    (random_call_stackArg hsp _ _ (by decide)).trans (hw 0 (by decide))
  refine signWith_of_pre hpre ?_
  simp only [hE0, State.withRegions_gpr, State.withRegions_mem, State.callEntry_gpr _ (r := .r8) (by decide),
    State.callEntry_gpr _ (r := .rdx) (by decide), State.callEntry_gpr _ (r := .rcx) (by decide),
    h8, hdx, hcx]
  rw [random_callEntry_key h hsp, hkey]
  exact hv

theorem random_signer_outcome (S : Signer) {s t : State} (h : RandomSignABI S.stack s)
    (hsp : t.gpr .rsp = randomBase s)
    (hw : ∀ i < 5, word t.mem (randomBase s) (8 * i) = randomCallArg s i)
    (hdi : t.gpr .rdi = s.gpr .rdi) (hsi : t.gpr .rsi = s.gpr .rsi)
    (hdx : t.gpr .rdx = s.gpr .rcx) (hcx : t.gpr .rcx = s.gpr .r8)
    (h8 : t.gpr .r8 = s.gpr .r9) (h9 : t.gpr .r9 = off (randomBase s) Random.oNonce)
    (hrd : t.rd = s.rd) (hwr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr)
    (hkey : Spec.Rsa.bytesAt t.mem (s.gpr .rcx) (s.gpr .r8).toNat = (randomInput s).key)
    (hv : RandomValid S s) :
    WP isa (.call S.name S.code) t fun u =>
      u.rd = t.rd ∧ u.wr = t.wr ∧ (∀ r ∈ calleeSaved, u.gpr r = t.gpr r) ∧
      Frame (randomCallWr s ++ [below (randomBase s) (S.stack + 8)]) t.mem u.mem ∧
      ((u.gpr .rax).setWidth 32).toNat = Spec.Dsa.signStatus (randomCallResult s t) ∧
      Spec.Rsa.bytesAt u.mem (s.gpr .rdi) (s.gpr .rsi).toNat =
        (randomCallResult s t).getD (List.replicate (s.gpr .rsi).toNat 0) ∧
      u.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 := by
  obtain ⟨hc, hcw⟩ := random_call_covers h hrd hwr
  have hpre := random_call_pre_with S h hsp hw hdi hsi hdx hcx h8 h9 hkey hv
  refine WP.mono (random_signer_call S hpre hc hcw)
    fun u ⟨hur, huw, huc, hf, ⟨w, hwm, hwg, hp⟩, hmx⟩ => ?_
  have hE (i : Nat) (hi : i < 5) :
      stackArg (t.callEntry.withRegions (randomCallRd s) (randomCallWr s)) i = randomCallArg s i :=
    (random_call_stackArg hsp _ _ hi).trans (hw i hi)
  sig_post [signContractWith, Spec.Dsa.signSig, abi, argRegs, stackArgs_five] at hp
  sig_post [signContractWith, Spec.Dsa.signSig, abi, argRegs, stackArgs_five] at hp
  simp only [hdi, hsi, hdx, hcx, h8, h9, hE 0 (by decide), hE 1 (by decide), hE 2 (by decide),
    randomCallArg, hwm, hwg .rax (by decide)] at hp
  refine ⟨hur, huw, huc, ?_, hp.1, hp.2, hmx⟩
  rw [hsp] at hf
  exact VG.X86_64.Frame.below_mono hf (by have := S.depth; omega) (by have := S.stackBound; omega)

end VG.Proof.Dsa.X86_64
