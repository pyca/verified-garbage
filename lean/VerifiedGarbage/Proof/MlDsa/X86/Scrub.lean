module

import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.X86.ScrubCall
meta import VerifiedGarbage.Proof.Framework.X86.ScrubCall

public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Impl.MlDsa.X86.Fn
public import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Inst
public import VerifiedGarbage.Proof.MlDsa.X86.PkTr
public import VerifiedGarbage.Proof.MlDsa.X86.PreparedKey
public import VerifiedGarbage.Proof.MlDsa.X86.Verify.Inst
public import VerifiedGarbage.Proof.MlDsa.X86.Message.Verified
import VerifiedGarbage.Proof.Sha3.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86.ScrubFn
meta import VerifiedGarbage.Impl.MlDsa.X86.Fn
meta import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Inst
meta import VerifiedGarbage.Proof.MlDsa.X86.PkTr
meta import VerifiedGarbage.Proof.MlDsa.X86.PreparedKey
meta import VerifiedGarbage.Proof.MlDsa.X86.Verify.Inst
meta import VerifiedGarbage.Proof.MlDsa.X86.Message.Verified
meta import VerifiedGarbage.Proof.Sha3.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-DSA's functions on x86 (32-bit), as emitted

ML-DSA's public functions keep secrets in the frames of the functions they
call, and none makes an indirect call. Each is emitted with its cleanup
(`Impl.MlDsa.X86.Fn`, `Impl.Scrub.X86.scrubAll`): a wipe of the stack its
contract reserves below `esp`, then the registers a callee may change
cleared, but the result's bits. Their postconditions read the memory on
return only within their outputs, and those of verification not at all
(`X86.Scrub.PostOut`, by `postOut_of_local`), stated once for the three
parameter sets. What the cleanup needs of the code (`X86.Scrub.scrubFSide`:
its frames and calls within the wipe, no indirect call, no MMX) is evaluated
once for each parameter set (`lit_decide`) when this module is built. The
theorems about the functions as emitted (`…_scrubbed`, by
`X86.Scrub.verifiedScrubbedAll`) are stated once, for the parameter set `p` of
the module `module` (`Inst`), which the registration binds.

The message functions call the functions on `μ` as they are verified,
without the cleanup, under names of their own (`Impl.MlDsa.X86.Sign.entryName`,
…): their own cleanup covers the frames of those calls.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Scrub

open VG VG.X86 VG.X86.Scrub VG.Spec.MlDsa
open VG.Proof.MlDsa.X86.KeyGen (NoSp.spSafe)

/-! ## The postconditions -/

/-- The `n` bytes at `q` read the memory only within a region at `q` of at
least `n` bytes. -/
theorem bytesAt_of {m₁ m₂ : Mem} {q : Addr} {N n : Nat} (hn : n ≤ N)
    (h : ∀ a, Region.Contains ⟨q, N⟩ a 1 → m₁ a = m₂ a) :
    Spec.Sha3.bytesAt m₂ q n = Spec.Sha3.bytesAt m₁ q n := by
  simp only [Spec.Sha3.bytesAt]
  refine List.map_congr_left fun i hi => (h _ ?_).symm
  have hi := List.mem_range.mp hi
  simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  have := Nat.mod_le i (2 ^ 64)
  omega_using [hn, hi]

section
variable (p : Params) (stack : Nat)

theorem keyGenOut : PostOut (keyGenContract p X86.abi stack) ((keyGenSig p).retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [seed, pk, sk, sc], _ =>
      simp only [keyGenSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      show Outcome _ r (Spec.Sha3.bytesAt m₂ pk p.pkLen, Spec.Sha3.bytesAt m₂ sk p.skLen)
      rw [bytesAt_of (Nat.le_refl _) hb.2.1, bytesAt_of (Nat.le_refl _) hb.2.2.1]
      exact h

theorem pkTrOut : PostOut (pkTrContract p X86.abi stack) ((pkTrSig p).retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [pk, tr, sc], _ =>
      simp only [pkTrSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      show Spec.Sha3.bytesAt m₂ tr 64 = _
      rw [bytesAt_of (Nat.le_refl _) hb.2.1]
      exact h

theorem signOut : PostOut (signContract p X86.abi stack) ((signSig p).retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sk, mu, rnd, sig, sc], _ =>
      simp only [signSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      show Outcome _ r (Spec.Sha3.bytesAt m₂ sig p.sigLen)
      rw [bytesAt_of (Nat.le_refl _) hb.2.2.2.1]
      exact h

theorem preparedSignOut :
    PostOut (Spec.MlDsa.preparedSignContract p X86.abi stack) ((Spec.MlDsa.preparedSignSig p).retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sk, mu, rnd, sig, sc], _ =>
      simp only [Spec.MlDsa.preparedSignSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      show Outcome _ r (Spec.Sha3.bytesAt m₂ sig p.sigLen)
      rw [bytesAt_of (Nat.le_refl _) hb.2.2.2.1]
      exact h

theorem signMessageOut : PostOut (signMessageContract p X86.abi stack) ((signMessageSig p).retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sk, msg, ml, ctx, cl, rnd, sig, sc], _ =>
      simp only [signMessageSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      have e := bytesAt_of (n := p.sigLen) (Nat.le_refl _) hb.2.2.2.2.1
      show match formatMessage (Spec.Sha3.bytesAt m ctx ((ArgWord.int X86.abi.ptrBits).ofRaw cl).toNat)
          (Spec.Sha3.bytesAt m msg ((ArgWord.int X86.abi.ptrBits).ofRaw ml).toNat) with
        | none => r = 2
        | some M' => Outcome (fun b => signInternal p b (Spec.Sha3.bytesAt m sk p.skLen) M'
            (Spec.Sha3.bytesAt m rnd 32)) r (Spec.Sha3.bytesAt m₂ sig p.sigLen)
      rw [e]
      exact h

theorem preparedSignMessageOut :
    PostOut (preparedSignMessageContract p X86.abi stack) ((preparedSignMessageSig p).retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sk, msg, ml, ctx, cl, rnd, sig, sc], _ =>
      simp only [preparedSignMessageSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      have e := bytesAt_of (n := p.sigLen) (Nat.le_refl _) hb.2.2.2.2.1
      show match formatMessage (Spec.Sha3.bytesAt m ctx ((ArgWord.int X86.abi.ptrBits).ofRaw cl).toNat)
          (Spec.Sha3.bytesAt m msg ((ArgWord.int X86.abi.ptrBits).ofRaw ml).toNat) with
        | none => r = 2
        | some M' => Outcome (fun b => signInternal p b (Spec.Sha3.bytesAt m sk p.skLen) M'
            (Spec.Sha3.bytesAt m rnd 32)) r (Spec.Sha3.bytesAt m₂ sig p.sigLen)
      rw [e]
      exact h

theorem verifyOut : PostOut (verifyContract p X86.abi stack) ((verifySig p).retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen _ h => by
    match vs, hlen with
    | [_, _, _, _], _ => exact h

theorem preparedVerifyOut :
    PostOut (Spec.MlDsa.preparedVerifyContract p X86.abi stack) ((Spec.MlDsa.preparedVerifySig p).retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen _ h => by
    match vs, hlen with
    | [_, _, _, _], _ => exact h

theorem verifyMessageCachedOut :
    PostOut (verifyMessageCachedContract p X86.abi stack) ((verifyMessageCachedSig p).retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen _ h => by
    match vs, hlen with
    | [_, _, _, _, _, _, _, _], _ => exact h

theorem preparedVerifyMessageOut :
    PostOut (preparedVerifyMessageContract p X86.abi stack) ((preparedVerifyMessageSig p).retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen _ h => by
    match vs, hlen with
    | [_, _, _, _, _, _, _, _], _ => exact h

end

/-! ### Prepared keys -/

theorem agreeBuf {m₁ m₂ : Mem} {q : Addr} {N : Nat} (hN : N < 2 ^ 64)
    (h : ∀ a, Region.Contains ⟨q, N⟩ a 1 → m₁ a = m₂ a) :
    ∀ i < N, m₂ (q + BitVec.ofNat 64 i) = m₁ (q + BitVec.ofNat 64 i) := fun i hi =>
  (h _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hN, hi]))).symm

theorem bytesAt_congr {m₁ m₂ : Mem} {q : Addr} {n N : Nat} (hn : n ≤ N)
    (h : ∀ i < N, m₂ (q + BitVec.ofNat 64 i) = m₁ (q + BitVec.ofNat 64 i)) :
    Spec.Sha3.bytesAt m₂ q n = Spec.Sha3.bytesAt m₁ q n :=
  List.map_congr_left fun i hi => h i (by have := List.mem_range.mp hi; omega_using [hn, this])

/-- A polynomial stored in the `1024` bytes at `q + d` of a buffer of `N`
bytes at `q`, in memories that agree on the buffer. -/
theorem polyStored_congr {m₁ m₂ : Mem} {q : Addr} {d N : Nat} {f : Poly} (hd : d + 4 * n ≤ N)
    (h : ∀ i < N, m₂ (q + BitVec.ofNat 64 i) = m₁ (q + BitVec.ofNat 64 i))
    (hf : PolyStored m₁ (q + BitVec.ofNat 64 d) f) : PolyStored m₂ (q + BitVec.ofNat 64 d) f := by
  intro i hi
  rw [← hf i hi]
  congr 1
  apply Mem.readW_congr
  intro t ht
  rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  exact h _ (by simp only [n] at hi hd; omega_using [hd, hi, ht])

variable {p : Params}

theorem key_bytes (h3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    preparedPublicKeyBytes p < 2 ^ 64 ∧ preparedSecretKeyBytes p < 2 ^ 64 := by
  rcases h3 with rfl | rfl | rfl <;> decide

theorem preparePublicOut (h3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) (stack : Nat) :
    PostOut (preparePublicKeyContract p X86.abi stack) ((preparePublicKeySig p).retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨pk, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨prep, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [preparePublicKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hw := agreeBuf (key_bytes h3).1 hb.2.1
    obtain ⟨h₁, h₂⟩ := h
    change Spec.Sha3.bytesAt m₁ prep p.pkLen = Spec.Sha3.bytesAt m pk p.pkLen at h₁
    change PreparedPublicKey p m₁ prep at h₂
    change Spec.Sha3.bytesAt m₂ prep p.pkLen = Spec.Sha3.bytesAt m pk p.pkLen ∧ PreparedPublicKey p m₂ prep
    have e := bytesAt_congr (n := p.pkLen) (by simp [preparedPublicKeyBytes]) hw
    refine ⟨?_, fun i hi => ?_⟩
    · exact e.trans h₁
    · rw [e]
      exact polyStored_congr (N := preparedPublicKeyBytes p)
        (by simp only [preparedPublicKeyBytes]; have := Nat.mul_le_mul_left (4 * n) (show i + 1 ≤ p.k by omega_using [hi])
            rw [Nat.mul_add, Nat.mul_one] at this; omega_using [this]) hw (h₂ i hi)

theorem prepareSecretOut (h3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) (stack : Nat) :
    PostOut (prepareSecretKeyContract p X86.abi stack) ((prepareSecretKeySig p).retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨sk, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨prep, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [prepareSecretKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hw := agreeBuf (key_bytes h3).2 hb.2.1
    obtain ⟨h₁, h₂⟩ := h
    change Spec.Sha3.bytesAt m₁ prep p.skLen = Spec.Sha3.bytesAt m sk p.skLen at h₁
    change PreparedSecretKey p m₁ prep at h₂
    change Spec.Sha3.bytesAt m₂ prep p.skLen = Spec.Sha3.bytesAt m sk p.skLen ∧ PreparedSecretKey p m₂ prep
    have e := bytesAt_congr (n := p.skLen) (by simp [preparedSecretKeyBytes]) hw
    refine ⟨?_, fun i hi => ?_⟩
    · exact e.trans h₁
    · rw [e]
      exact polyStored_congr (N := preparedSecretKeyBytes p)
        (by simp only [preparedSecretKeyBytes]
            have := Nat.mul_le_mul_left (4 * n) (show i + 1 ≤ p.ℓ + 2 * p.k by omega_using [hi])
            rw [Nat.mul_add, Nat.mul_one] at this; omega_using [this]) hw (h₂ i hi)

/-! ## The parameter sets -/

/-- The parameter set `p` of the module `module`, which names the functions
the code calls. -/
def Inst (p : Params) (module : String) : Prop :=
  (p = mlDsa44 ∧ module = "mldsa44") ∨ (p = mlDsa65 ∧ module = "mldsa65") ∨ (p = mlDsa87 ∧ module = "mldsa87")

theorem Inst.params {module : String} (h : Inst p module) : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87 := by
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
  exacts [.inl rfl, .inr (.inl rfl), .inr (.inr rfl)]

theorem Inst.mem {module : String} (h : Inst p module) : p ∈ Message.params := by
  simp only [Message.params, List.mem_cons, List.not_mem_nil, or_false]; exact h.params

section
variable {module : String} (h : Inst p module)
include h

/-! ### The functions on `μ` and the message functions, as verified -/

theorem signFn : Message.SignFn p (Message.plainKey p.skLen) (Impl.MlDsa.X86.Sign.signOf p module) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [Message.sign44Fn, Message.sign65Fn, Message.sign87Fn]

theorem signPreparedFn : Message.SignFn p (Message.secretKey p) (Impl.MlDsa.X86.Sign.signPreparedOf p module) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [Message.signPrepared44Fn, Message.signPrepared65Fn, Message.signPrepared87Fn]

theorem verifyFn : Message.VerifyFn p (Message.plainKey p.pkLen) (Impl.MlDsa.X86.Verify.verifyOf p module) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [Message.verify44Fn, Message.verify65Fn, Message.verify87Fn]

theorem verifyPreparedFn : Message.VerifyFn p (Message.publicKey p) (Impl.MlDsa.X86.Verify.verifyPreparedOf p module) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [Message.verifyPrepared44Fn, Message.verifyPrepared65Fn, Message.verifyPrepared87Fn]

theorem sign_verified :
    Verified X86.target (Impl.MlDsa.X86.Sign.signOf p module) (signContract p X86.abi 136) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [Message.sign44_verified, Message.sign65_verified, Message.sign87_verified]

theorem signPrepared_verified :
    Verified X86.target (Impl.MlDsa.X86.Sign.signPreparedOf p module) (preparedSignContract p X86.abi 136) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [Message.signPrepared44_verified, Message.signPrepared65_verified, Message.signPrepared87_verified]

theorem verify_verified :
    Verified X86.target (Impl.MlDsa.X86.Verify.verifyOf p module) (verifyContract p X86.abi 136) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [Message.verify44_verified, Message.verify65_verified, Message.verify87_verified]

theorem verifyPrepared_verified :
    Verified X86.target (Impl.MlDsa.X86.Verify.verifyPreparedOf p module) (preparedVerifyContract p X86.abi 136) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [Message.verifyPrepared44_verified, Message.verifyPrepared65_verified, Message.verifyPrepared87_verified]

theorem signMessage_verified :
    Verified X86.target
      (Impl.MlDsa.X86.Message.signMessage (Impl.MlDsa.X86.Sign.entryName module) (Impl.MlDsa.X86.Sign.signOf p module) p)
      (signMessageContract p X86.abi 176) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [Message.signMessage44_verified, Message.signMessage65_verified, Message.signMessage87_verified]

theorem preparedSignMessage_verified :
    Verified X86.target
      (Impl.MlDsa.X86.Message.signMessage (Impl.MlDsa.X86.Sign.preparedEntryName module)
        (Impl.MlDsa.X86.Sign.signPreparedOf p module) p)
      (preparedSignMessageContract p X86.abi 176) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [Message.signMessagePrepared44_verified, Message.signMessagePrepared65_verified,
    Message.signMessagePrepared87_verified]

theorem verifyMessageCached_verified :
    Verified X86.target
      (Impl.MlDsa.X86.Message.verifyMessageCached (Impl.MlDsa.X86.Verify.entryName module)
        (Impl.MlDsa.X86.Verify.verifyOf p module) p)
      (verifyMessageCachedContract p X86.abi 172) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [Message.verifyMessageCached44_verified, Message.verifyMessageCached65_verified,
    Message.verifyMessageCached87_verified]

theorem preparedVerifyMessage_verified :
    Verified X86.target
      (Impl.MlDsa.X86.Message.verifyMessageCached (Impl.MlDsa.X86.Verify.preparedEntryName module)
        (Impl.MlDsa.X86.Verify.verifyPreparedOf p module) p)
      (preparedVerifyMessageContract p X86.abi 172) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [Message.verifyMessagePrepared44_verified, Message.verifyMessagePrepared65_verified,
    Message.verifyMessagePrepared87_verified]

/-! ### What the cleanup needs of the code -/

omit h in
private theorem core_side {f : Prog isa} (hf : calleeSide f 136 = true) :
    scrubFSide f [] 136 = true := by
  simp only [calleeSide, Bool.and_eq_true, decide_eq_true_eq, calleeOk_iff] at hf
  simp only [scrubFSide, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨⟨⟨⟨hf.1, tablesCall_of_noIcall hf.2.1 _⟩, hf.2.2⟩, by decide⟩, by decide⟩

private theorem sign_callee : calleeSide (Impl.MlDsa.X86.Sign.signOf p module) 136 = true := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> lit_decide

theorem sign_side : scrubFSide (Impl.MlDsa.X86.Sign.signOf p module) [] 136 = true :=
  core_side (sign_callee h)

private theorem signPrepared_callee : calleeSide (Impl.MlDsa.X86.Sign.signPreparedOf p module) 136 = true := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> lit_decide

theorem signPrepared_side : scrubFSide (Impl.MlDsa.X86.Sign.signPreparedOf p module) [] 136 = true :=
  core_side (signPrepared_callee h)

private theorem verify_callee : calleeSide (Impl.MlDsa.X86.Verify.verifyOf p module) 136 = true := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> lit_decide

theorem verify_side : scrubFSide (Impl.MlDsa.X86.Verify.verifyOf p module) [] 136 = true :=
  core_side (verify_callee h)

private theorem verifyPrepared_callee : calleeSide (Impl.MlDsa.X86.Verify.verifyPreparedOf p module) 136 = true := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> lit_decide

theorem verifyPrepared_side : scrubFSide (Impl.MlDsa.X86.Verify.verifyPreparedOf p module) [] 136 = true :=
  core_side (verifyPrepared_callee h)

omit h in
private theorem signMessage_of_callee (params : Params) (n : String) (f : Prog isa)
    (hf : calleeSide f 136 = true) :
    scrubFSide (Impl.MlDsa.X86.Message.signMessage n f params) [] 176 = true := by
  apply scrubFSide_of_fillB (a := Impl.MlDsa.X86.Message.signMessage "" (holeStub 136) params)
  · fillB_calls
  · kernel_rfl

omit h in
private theorem verifyMessageCached_of_callee (params : Params) (n : String) (f : Prog isa)
    (hf : calleeSide f 136 = true) :
    scrubFSide (Impl.MlDsa.X86.Message.verifyMessageCached n f params) [] 172 = true := by
  apply scrubFSide_of_fillB (a := Impl.MlDsa.X86.Message.verifyMessageCached "" (holeStub 136) params)
  · fillB_calls
  · kernel_rfl

theorem signMessage_side :
    scrubFSide (Impl.MlDsa.X86.Message.signMessage (Impl.MlDsa.X86.Sign.entryName module)
      (Impl.MlDsa.X86.Sign.signOf p module) p) [] 176 = true :=
  signMessage_of_callee p _ _ (sign_callee h)

theorem preparedSignMessage_side :
    scrubFSide (Impl.MlDsa.X86.Message.signMessage (Impl.MlDsa.X86.Sign.preparedEntryName module)
      (Impl.MlDsa.X86.Sign.signPreparedOf p module) p) [] 176 = true :=
  signMessage_of_callee p _ _ (signPrepared_callee h)

theorem verifyMessageCached_side :
    scrubFSide (Impl.MlDsa.X86.Message.verifyMessageCached (Impl.MlDsa.X86.Verify.entryName module)
      (Impl.MlDsa.X86.Verify.verifyOf p module) p) [] 172 = true :=
  verifyMessageCached_of_callee p _ _ (verify_callee h)

theorem preparedVerifyMessage_side :
    scrubFSide (Impl.MlDsa.X86.Message.verifyMessageCached (Impl.MlDsa.X86.Verify.preparedEntryName module)
      (Impl.MlDsa.X86.Verify.verifyPreparedOf p module) p) [] 172 = true :=
  verifyMessageCached_of_callee p _ _ (verifyPrepared_callee h)

end

section
variable (h3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87)
include h3

theorem keyGen_side :
    scrubFSide (Impl.MlDsa.X86.KeyGen.keyGen Impl.MlDsa.X86.KeyGen.prims p) [] 96 = true := by
  rcases h3 with rfl | rfl | rfl <;> lit_decide

theorem pkTr_side : scrubFSide (Impl.MlDsa.X86.PkTr.pkTr p) [] 56 = true := by
  rcases h3 with rfl | rfl | rfl <;> lit_decide

theorem preparePublic_side :
    scrubFSide (Impl.MlDsa.X86.PreparedKey.preparePublic Impl.MlDsa.X86.Verify.prims p) [] 96 = true := by
  rcases h3 with rfl | rfl | rfl <;> lit_decide

theorem prepareSecret_side :
    scrubFSide (Impl.MlDsa.X86.PreparedKey.prepareSecret Impl.MlDsa.X86.Verify.prims p) [] 96 = true := by
  rcases h3 with rfl | rfl | rfl <;> lit_decide

end

/-! ## The functions, as emitted

Each function with its cleanup (`Impl.MlDsa.X86.Fn`), of the parameter set
`p` of the module `module` (`name` is its `Api`'s): it meets its contract in
constant time and returns without secret residue (`VerifiedScrubbed`), which
is what its registration binds. -/

section

/-- `vg_<module>_keygen`. -/
theorem keyGen_scrubbed (module name : String) (h3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    VerifiedScrubbed X86.target (Impl.MlDsa.X86.Fn.keyGen p) (keyGenContract p X86.abi 96) 32 :=
  verifiedScrubbedAll (api := keyGenApi p module name)
    { code := Impl.MlDsa.X86.KeyGen.keyGen Impl.MlDsa.X86.KeyGen.prims p
      verified := KeyGen.keyGen_verified KeyGen.prims_ok p h3
      spSafe := NoSp.spSafe (KeyGen.keyGen_nosp p) }
    (by exact keyGenOut p _) (keyGen_side h3)

/-- `vg_<module>_pk_tr`. -/
theorem pkTr_scrubbed (module name : String) (h3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    VerifiedScrubbed X86.target (Impl.MlDsa.X86.Fn.pkTr p) (pkTrContract p X86.abi 56) 0 :=
  verifiedScrubbedAll (api := pkTrApi p module name)
    { code := Impl.MlDsa.X86.PkTr.pkTr p
      verified := PkTr.pkTr_verified p h3
      spSafe := NoSp.spSafe (PkTr.pkTr_nosp p) }
    (by exact pkTrOut p _) (pkTr_side h3)

/-- `vg_<module>_prepare_verifying_key`. -/
theorem preparePublic_scrubbed (module name : String) (h3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    VerifiedScrubbed X86.target (Impl.MlDsa.X86.Fn.preparePublic p) (preparePublicKeyContract p X86.abi 96) 0 :=
  verifiedScrubbedAll (api := preparePublicKeyApi p module name)
    { code := Impl.MlDsa.X86.PreparedKey.preparePublic Impl.MlDsa.X86.Verify.prims p
      verified := PreparedKey.public_verified Verify.prims_ok h3
      spSafe := NoSp.spSafe (PreparedKey.public_nosp Verify.prims_ok p) }
    (by exact preparePublicOut h3 _) (preparePublic_side h3)

/-- `vg_<module>_prepare_signing_key`. -/
theorem prepareSecret_scrubbed (module name : String) (h3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    VerifiedScrubbed X86.target (Impl.MlDsa.X86.Fn.prepareSecret p) (prepareSecretKeyContract p X86.abi 96) 0 :=
  verifiedScrubbedAll (api := prepareSecretKeyApi p module name)
    { code := Impl.MlDsa.X86.PreparedKey.prepareSecret Impl.MlDsa.X86.Verify.prims p
      verified := PreparedKey.secret_verified Verify.prims_ok h3
      spSafe := NoSp.spSafe (PreparedKey.secret_nosp Verify.prims_ok p) }
    (by exact prepareSecretOut h3 _) (prepareSecret_side h3)

theorem keyGen_spSafe (p : Params) : (Impl.MlDsa.X86.Fn.keyGen p).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (NoSp.spSafe (KeyGen.keyGen_nosp p))

theorem pkTr_spSafe (p : Params) : (Impl.MlDsa.X86.Fn.pkTr p).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (NoSp.spSafe (PkTr.pkTr_nosp p))

theorem preparePublic_spSafe (p : Params) :
    (Impl.MlDsa.X86.Fn.preparePublic p).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (NoSp.spSafe (PreparedKey.public_nosp Verify.prims_ok p))

theorem prepareSecret_spSafe (p : Params) :
    (Impl.MlDsa.X86.Fn.prepareSecret p).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (NoSp.spSafe (PreparedKey.secret_nosp Verify.prims_ok p))

variable {module : String} (h : Inst p module)
include h

/-- `vg_<module>_sign`. -/
theorem sign_scrubbed (name : String) :
    VerifiedScrubbed X86.target (Impl.MlDsa.X86.Fn.sign p module) (signContract p X86.abi 136) 32 :=
  verifiedScrubbedAll (api := signApi p module name)
    { code := Impl.MlDsa.X86.Sign.signOf p module
      verified := sign_verified h
      spSafe := NoSp.spSafe (signFn h).nosp }
    (by exact signOut p _) (sign_side h)

/-- `vg_<module>_sign_prepared`. -/
theorem signPrepared_scrubbed (name : String) :
    VerifiedScrubbed X86.target (Impl.MlDsa.X86.Fn.signPrepared p module) (preparedSignContract p X86.abi 136) 32 :=
  verifiedScrubbedAll (api := preparedSignApi p module name)
    { code := Impl.MlDsa.X86.Sign.signPreparedOf p module
      verified := signPrepared_verified h
      spSafe := NoSp.spSafe (signPreparedFn h).nosp }
    (by exact preparedSignOut p _) (signPrepared_side h)

/-- `vg_<module>_verify`. -/
theorem verify_scrubbed (name : String) :
    VerifiedScrubbed X86.target (Impl.MlDsa.X86.Fn.verify p module) (verifyContract p X86.abi 136) 32 :=
  verifiedScrubbedAll (api := verifyApi p module name)
    { code := Impl.MlDsa.X86.Verify.verifyOf p module
      verified := verify_verified h
      spSafe := NoSp.spSafe (verifyFn h).nosp }
    (by exact verifyOut p _) (verify_side h)

/-- `vg_<module>_verify_prepared`. -/
theorem verifyPrepared_scrubbed (name : String) :
    VerifiedScrubbed X86.target (Impl.MlDsa.X86.Fn.verifyPrepared p module) (preparedVerifyContract p X86.abi 136) 32 :=
  verifiedScrubbedAll (api := preparedVerifyApi p module name)
    { code := Impl.MlDsa.X86.Verify.verifyPreparedOf p module
      verified := verifyPrepared_verified h
      spSafe := NoSp.spSafe (verifyPreparedFn h).nosp }
    (by exact preparedVerifyOut p _) (verifyPrepared_side h)

/-- `vg_<module>_sign_message`. -/
theorem signMessage_scrubbed (name : String) :
    VerifiedScrubbed X86.target (Impl.MlDsa.X86.Fn.signMessage p module) (signMessageContract p X86.abi 176) 32 :=
  verifiedScrubbedAll (api := signMessageApi p module name)
    { code := Impl.MlDsa.X86.Message.signMessage (Impl.MlDsa.X86.Sign.entryName module)
        (Impl.MlDsa.X86.Sign.signOf p module) p
      verified := signMessage_verified h
      spSafe := NoSp.spSafe (Message.signMessage_nosp p (signFn h).nosp) }
    (by exact signMessageOut p _) (signMessage_side h)

/-- `vg_<module>_sign_message_prepared`. -/
theorem preparedSignMessage_scrubbed (name : String) :
    VerifiedScrubbed X86.target (Impl.MlDsa.X86.Fn.preparedSignMessage p module)
      (preparedSignMessageContract p X86.abi 176) 32 :=
  verifiedScrubbedAll (api := preparedSignMessageApi p module name)
    { code := Impl.MlDsa.X86.Message.signMessage (Impl.MlDsa.X86.Sign.preparedEntryName module)
        (Impl.MlDsa.X86.Sign.signPreparedOf p module) p
      verified := preparedSignMessage_verified h
      spSafe := NoSp.spSafe (Message.signMessage_nosp p (signPreparedFn h).nosp) }
    (by exact preparedSignMessageOut p _) (preparedSignMessage_side h)

/-- `vg_<module>_verify_message_cached`. -/
theorem verifyMessageCached_scrubbed (name : String) :
    VerifiedScrubbed X86.target (Impl.MlDsa.X86.Fn.verifyMessageCached p module)
      (verifyMessageCachedContract p X86.abi 172) 32 :=
  verifiedScrubbedAll (api := verifyMessageCachedApi p module name)
    { code := Impl.MlDsa.X86.Message.verifyMessageCached (Impl.MlDsa.X86.Verify.entryName module)
        (Impl.MlDsa.X86.Verify.verifyOf p module) p
      verified := verifyMessageCached_verified h
      spSafe := NoSp.spSafe (Message.verifyMessageCached_nosp p (verifyFn h).nosp) }
    (by exact verifyMessageCachedOut p _) (verifyMessageCached_side h)

/-- `vg_<module>_verify_message_prepared`. -/
theorem preparedVerifyMessage_scrubbed (name : String) :
    VerifiedScrubbed X86.target (Impl.MlDsa.X86.Fn.preparedVerifyMessage p module)
      (preparedVerifyMessageContract p X86.abi 172) 32 :=
  verifiedScrubbedAll (api := preparedVerifyMessageApi p module name)
    { code := Impl.MlDsa.X86.Message.verifyMessageCached (Impl.MlDsa.X86.Verify.preparedEntryName module)
        (Impl.MlDsa.X86.Verify.verifyPreparedOf p module) p
      verified := preparedVerifyMessage_verified h
      spSafe := NoSp.spSafe (Message.verifyMessageCached_nosp p (verifyPreparedFn h).nosp) }
    (by exact preparedVerifyMessageOut p _) (preparedVerifyMessage_side h)

/-! ### That the code writes `esp` only in its frames and calls -/

theorem sign_spSafe : (Impl.MlDsa.X86.Fn.sign p module).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (NoSp.spSafe (signFn h).nosp)

theorem signPrepared_spSafe : (Impl.MlDsa.X86.Fn.signPrepared p module).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (NoSp.spSafe (signPreparedFn h).nosp)

theorem verify_spSafe : (Impl.MlDsa.X86.Fn.verify p module).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (NoSp.spSafe (verifyFn h).nosp)

theorem verifyPrepared_spSafe : (Impl.MlDsa.X86.Fn.verifyPrepared p module).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (NoSp.spSafe (verifyPreparedFn h).nosp)

theorem signMessage_spSafe : (Impl.MlDsa.X86.Fn.signMessage p module).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (NoSp.spSafe (Message.signMessage_nosp p (signFn h).nosp))

theorem preparedSignMessage_spSafe :
    (Impl.MlDsa.X86.Fn.preparedSignMessage p module).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (NoSp.spSafe (Message.signMessage_nosp p (signPreparedFn h).nosp))

theorem verifyMessageCached_spSafe :
    (Impl.MlDsa.X86.Fn.verifyMessageCached p module).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (NoSp.spSafe (Message.verifyMessageCached_nosp p (verifyFn h).nosp))

theorem preparedVerifyMessage_spSafe :
    (Impl.MlDsa.X86.Fn.preparedVerifyMessage p module).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (NoSp.spSafe (Message.verifyMessageCached_nosp p (verifyPreparedFn h).nosp))

end

end VG.Proof.MlDsa.X86.Scrub
