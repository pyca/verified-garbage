module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignPublic
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallResult
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallPre
import VerifiedGarbage.Proof.Dsa.X86_64.SigningABI

/-! Instantiate the supplied-nonce signer's leakage contract at a wrapper call. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64

structure RandomSignCallState {extra : Nat} {s : State} (h : RandomSignABI extra s) (t : State) : Prop where
  sp : t.gpr .rsp = randomBase s
  args : ∀ i < 5, word t.mem (randomBase s) (8 * i) = randomCallArg s i
  di : t.gpr .rdi = s.gpr .rdi
  si : t.gpr .rsi = s.gpr .rsi
  dx : t.gpr .rdx = s.gpr .rcx
  cx : t.gpr .rcx = s.gpr .r8
  r8 : t.gpr .r8 = s.gpr .r9
  r9 : t.gpr .r9 = off (randomBase s) Random.oNonce
  rd : t.rd = s.rd
  wr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr

def randomCallPublicKey (s t : State) : List Nat :=
  Spec.Dsa.publicBytesLeak (s.gpr .r9).toNat (stackArg s 0).toNat
    (Spec.Rsa.bytesAt t.callEntry.mem (s.gpr .rcx) (s.gpr .r8).toNat)

theorem random_call_public {extra : Nat} {s t a b : State}
    {hs : RandomSignABI extra s} {ht : RandomSignABI extra t}
    (ha : RandomSignCallState hs a) (hb : RandomSignCallState ht b) (hp : RandomSignPublicAgree s t)
    (hk : randomCallPublicKey s a = randomCallPublicKey t b)
    (hr : Spec.Dsa.signStatus (randomCallResult s a) = Spec.Dsa.signStatus (randomCallResult t b)) :
    (Spec.Dsa.signContract abi extra).pub
      (a.callEntry.withRegions (randomCallRd s) (randomCallWr s))
      (b.callEntry.withRegions (randomCallRd t) (randomCallWr t)) := by
  have hA (i : Nat) (hi : i < 5) :
      stackArg (a.callEntry.withRegions (randomCallRd s) (randomCallWr s)) i = randomCallArg s i :=
    (random_call_stackArg ha.sp _ _ hi).trans (ha.args i hi)
  have hB (i : Nat) (hi : i < 5) :
      stackArg (b.callEntry.withRegions (randomCallRd t) (randomCallWr t)) i = randomCallArg t i :=
    (random_call_stackArg hb.sp _ _ hi).trans (hb.args i hi)
  sig_pub [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five, List.range, List.range.loop]
  simp only [ha.sp, hb.sp, ha.di, hb.di, ha.si, hb.si, ha.dx, hb.dx, ha.cx, hb.cx, ha.r8, hb.r8, ha.r9, hb.r9,
    hA 0 (by decide), hA 1 (by decide), hA 2 (by decide), hA 3 (by decide), hA 4 (by decide),
    hB 0 (by decide), hB 1 (by decide), hB 2 (by decide), hB 3 (by decide), hB 4 (by decide), randomCallArg]
  refine ⟨?_, ?_, hp.regs .rdi (by decide), hp.regs .rsi (by decide), hp.regs .rcx (by decide),
    hp.regs .r8 (by decide), hp.regs .r9 (by decide), ?_, hp.args 0 (by decide), hp.args 1 (by decide),
    hp.args 2 (by decide), hp.args 5 (by decide), hp.args 6 (by decide)⟩
  · rw [hp.base]
  · simp only [randomCallPublicKey, randomCallResult, State.callEntry_mem, ha.sp, hb.sp] at hk hr
    rw [hk, hr]
  · rw [hp.base]

def RandomSignCallRelated (v : Backend) (a b : State) : Prop :=
  ∃ s t, ∃ hs : RandomSignABI v.stack s, ∃ ht : RandomSignABI v.stack t,
    RandomSignCallState hs a ∧ RandomSignCallState ht b ∧ RandomSignPublicAgree s t ∧
    randomCallPublicKey s a = randomCallPublicKey t b ∧
    Spec.Dsa.signStatus (randomCallResult s a) = Spec.Dsa.signStatus (randomCallResult t b)

theorem random_signer_ct (v : Backend) : RelCT isa (RandomSignCallRelated v)
    (.call (randomSignerName v) (SignVerify.sign v.sq v.mul)) (fun _ _ => True) := by
  apply VG.X86_64.RelCT.callEx v.signVerified.1 v.signVerified.2.1
  intro a b ⟨s, t, hs, ht, ha, hb, hp, hk, hr⟩
  obtain ⟨hca, hwa⟩ := random_call_covers hs ha.rd ha.wr
  obtain ⟨hcb, hwb⟩ := random_call_covers ht hb.rd hb.wr
  exact ⟨randomCallRd s, randomCallWr s, randomCallRd t, randomCallWr t,
    random_call_pre hs ha.sp ha.args ha.di ha.si ha.dx ha.cx ha.r8 ha.r9,
    random_call_pre ht hb.sp hb.args hb.di hb.si hb.dx hb.cx hb.r8 hb.r9,
    random_call_public ha hb hp hk hr, hca, hwa, hcb, hwb,
    ha.sp.trans (hp.base.trans hb.sp.symm)⟩

end VG.Proof.Dsa.X86_64
