module

public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignPublic
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallResult
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallPre
import VerifiedGarbage.Proof.Dsa.AArch64.SigningABI

/-! Instantiate the supplied-nonce signer's leakage contract at a wrapper call. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64

structure RandomSignCallState {extra : Nat} {s : State} (h : RandomSignABI extra s) (t : State) : Prop where
  sp : t.sp = randomBase s
  args : ∀ i < 3, word t.mem (randomBase s) (8 * i) = randomCallArg s i
  di : t.gpr .x0 = s.gpr .x0
  si : t.gpr .x1 = s.gpr .x1
  dx : t.gpr .x2 = s.gpr .x3
  cx : t.gpr .x3 = s.gpr .x4
  r8 : t.gpr .x4 = s.gpr .x5
  r9 : t.gpr .x5 = off (randomBase s) Random.oNonce
  x6 : t.gpr .x6 = s.gpr .x6
  x7 : t.gpr .x7 = s.gpr .x7
  rd : t.rd = s.rd
  wr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr
  key : Spec.Rsa.bytesAt t.mem (s.gpr .x3) (s.gpr .x4).toNat = (randomInput s).key

def randomCallPublicKey (s t : State) : List Nat :=
  Spec.Dsa.publicBytesLeak (s.gpr .x5).toNat (s.gpr .x6).toNat
    (Spec.Rsa.bytesAt t.callEntry.mem (s.gpr .x3) (s.gpr .x4).toNat)

theorem random_call_public {valid : Nat → Nat → List Byte → Bool} {extra : Nat} {s t a b : State}
    {hs : RandomSignABI extra s} {ht : RandomSignABI extra t}
    (ha : RandomSignCallState hs a) (hb : RandomSignCallState ht b) (hp : RandomSignPublicAgree s t)
    (hk : randomCallPublicKey s a = randomCallPublicKey t b)
    (hr : Spec.Dsa.signStatus (randomCallResult s a) = Spec.Dsa.signStatus (randomCallResult t b)) :
    (signContractWith valid abi extra).pub
      (a.callEntry.withRegions (randomCallRd s) (randomCallWr s))
      (b.callEntry.withRegions (randomCallRd t) (randomCallWr t)) := by
  have hA (i : Nat) (hi : i < 3) :
      stackArg (a.callEntry.withRegions (randomCallRd s) (randomCallWr s)) i = randomCallArg s i :=
    (random_call_stackArg ha.sp _ _ i).trans (ha.args i hi)
  have hB (i : Nat) (hi : i < 3) :
      stackArg (b.callEntry.withRegions (randomCallRd t) (randomCallWr t)) i = randomCallArg t i :=
    (random_call_stackArg hb.sp _ _ i).trans (hb.args i hi)
  sig_pub [signContractWith, Spec.Dsa.signSig, abi, argRegs, dsaSignStackArgs]
  simp only [ha.sp, hb.sp, ha.di, hb.di, ha.si, hb.si, ha.dx, hb.dx, ha.cx, hb.cx, ha.r8, hb.r8, ha.r9, hb.r9, ha.x6, hb.x6, ha.x7, hb.x7,
    hA 0 (by decide), hA 1 (by decide), hA 2 (by decide),
    hB 0 (by decide), hB 1 (by decide), hB 2 (by decide), randomCallArg]
  refine ⟨?_, ?_, hp.regs .x0 (by decide), hp.regs .x1 (by decide), hp.regs .x3 (by decide),
    hp.regs .x4 (by decide), hp.regs .x5 (by decide), ?_, hp.regs .x6 (by decide), hp.regs .x7 (by decide),
    hp.args 0 (by decide), hp.args 3 (by decide), hp.args 4 (by decide)⟩
  · rw [hp.base]
  · simp only [randomCallPublicKey, randomCallResult, State.callEntry] at hk hr
    rw [hk, hr]
  · rw [hp.base]

def RandomSignCallRelated (S : Signer) (a b : State) : Prop :=
  ∃ s t, ∃ hs : RandomSignABI S.stack s, ∃ ht : RandomSignABI S.stack t,
    RandomValid S s ∧ RandomValid S t ∧ RandomSignCallState hs a ∧ RandomSignCallState ht b ∧ RandomSignPublicAgree s t ∧
    randomCallPublicKey s a = randomCallPublicKey t b ∧
    Spec.Dsa.signStatus (randomCallResult s a) = Spec.Dsa.signStatus (randomCallResult t b)

theorem random_signer_ct (S : Signer) : RelCT isa (RandomSignCallRelated S)
    (.call S.name S.code) (fun _ _ => True) := by
  apply VG.AArch64.RelCT.callEx S.verified.1 S.verified.2.1
  intro a b ⟨s, t, hs, ht, hvs, hvt, ha, hb, hp, hk, hr⟩
  obtain ⟨hca, hwa⟩ := random_call_covers hs ha.rd ha.wr
  obtain ⟨hcb, hwb⟩ := random_call_covers ht hb.rd hb.wr
  exact ⟨randomCallRd s, randomCallWr s, randomCallRd t, randomCallWr t,
    random_call_pre_with S hs ha.sp ha.args ha.di ha.si ha.dx ha.cx ha.r8 ha.r9 ha.x6 ha.x7 ha.key hvs,
    random_call_pre_with S ht hb.sp hb.args hb.di hb.si hb.dx hb.cx hb.r8 hb.r9 hb.x6 hb.x7 hb.key hvt,
    random_call_public ha hb hp hk hr, hca, hwa, hcb, hwb⟩

end VG.Proof.Dsa.AArch64
