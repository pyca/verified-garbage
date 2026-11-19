module

public import VerifiedGarbage.Spec.MlDsa.Contract
public import VerifiedGarbage.Spec.MlDsa.PreparedKey
public import VerifiedGarbage.Spec.MlDsa.PkTr
public import VerifiedGarbage.Spec.MlDsa.CachedVerify
public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Inst
public import VerifiedGarbage.Proof.MlDsa.RISCV64.PkTr
public import VerifiedGarbage.Proof.MlDsa.RISCV64.PreparedKey.Inst
public import VerifiedGarbage.Proof.MlDsa.RISCV64.Message.Inst
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# ML-DSA on RISC-V, without secret residue

Key generation, `pk_tr`, the preparation of keys, signing and verification
(of a message representative or of a message, with a key or a prepared key),
each followed by
`Impl.Scrub.RISCV64.scrubTail` (`RISCV64.Scrub.withScrub`), which clears the
caller-saved registers and the stack their frames used (1072 to 1184
bytes). The postconditions of all but verification read the memory on return
only within their outputs, and those of verification not at all
(`RISCV64.Scrub.PostOut`); the proofs are PPC64LE's (`Proof/MlDsa/PPC64LE/Scrub.lean`), for this target's
scrub.

Signing and verifying a message call the signing or verification of a
message representative as the internal `vg_mldsa*_sign_core`, … (an `_core`
suffix to each name), whose code is that of the exported functions without
the clearing (`Message/Inst.lean`), so that the stack is cleared once.
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Scrub

open VG.RISCV64 VG.RISCV64.Scrub VG.Spec.MlDsa

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

theorem pub_bytes : ∀ p, (p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) → preparedPublicKeyBytes p < 2 ^ 64 := by
  rintro p (rfl | rfl | rfl) <;> decide
theorem sec_bytes : ∀ p, (p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) → preparedSecretKeyBytes p < 2 ^ 64 := by
  rintro p (rfl | rfl | rfl) <;> decide

theorem pubOut (stack : Nat) {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    PostOut (preparePublicKeyContract p RISCV64.abi stack) ((preparePublicKeySig p).retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [pk, prep, sc], _ =>
      simp only [preparePublicKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      have hw := agreeBuf (pub_bytes p hp) hb.2.1
      obtain ⟨h₁, h₂⟩ := h
      change Spec.Sha3.bytesAt m₁ prep p.pkLen = Spec.Sha3.bytesAt m pk p.pkLen at h₁
      change PreparedPublicKey p m₁ prep at h₂
      change Spec.Sha3.bytesAt m₂ prep p.pkLen = Spec.Sha3.bytesAt m pk p.pkLen ∧ PreparedPublicKey p m₂ prep
      have e := bytesAt_congr (n := p.pkLen) (by simp [preparedPublicKeyBytes]) hw
      refine ⟨e.trans h₁, fun i hi => ?_⟩
      rw [e]
      exact polyStored_congr (N := preparedPublicKeyBytes p)
        (by simp only [preparedPublicKeyBytes]; have := Nat.mul_le_mul_left (4 * n) (show i + 1 ≤ p.k by omega_using [hi])
            rw [Nat.mul_add, Nat.mul_one] at this; omega_using [this]) hw (h₂ i hi)

theorem secOut (stack : Nat) {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    PostOut (prepareSecretKeyContract p RISCV64.abi stack) ((prepareSecretKeySig p).retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sk, prep, sc], _ =>
      simp only [prepareSecretKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      have hw := agreeBuf (sec_bytes p hp) hb.2.1
      obtain ⟨h₁, h₂⟩ := h
      change Spec.Sha3.bytesAt m₁ prep p.skLen = Spec.Sha3.bytesAt m sk p.skLen at h₁
      change PreparedSecretKey p m₁ prep at h₂
      change Spec.Sha3.bytesAt m₂ prep p.skLen = Spec.Sha3.bytesAt m sk p.skLen ∧ PreparedSecretKey p m₂ prep
      have e := bytesAt_congr (n := p.skLen) (by simp [preparedSecretKeyBytes]) hw
      refine ⟨e.trans h₁, fun i hi => ?_⟩
      rw [e]
      exact polyStored_congr (N := preparedSecretKeyBytes p)
        (by simp only [preparedSecretKeyBytes]
            have := Nat.mul_le_mul_left (4 * n) (show i + 1 ≤ p.ℓ + 2 * p.k by omega_using [hi])
            rw [Nat.mul_add, Nat.mul_one] at this; omega_using [this]) hw (h₂ i hi)

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

theorem keyGenOut : PostOut (keyGenContract p RISCV64.abi stack) ((keyGenSig p).retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [seed, pk, sk, sc], _ =>
      simp only [keyGenSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      show Outcome _ r (Spec.Sha3.bytesAt m₂ pk p.pkLen, Spec.Sha3.bytesAt m₂ sk p.skLen)
      rw [bytesAt_of (Nat.le_refl _) hb.2.1, bytesAt_of (Nat.le_refl _) hb.2.2.1]
      exact h

theorem pkTrOut : PostOut (pkTrContract p RISCV64.abi stack) ((pkTrSig p).retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [pk, tr, sc], _ =>
      simp only [pkTrSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      show Spec.Sha3.bytesAt m₂ tr 64 = _
      rw [bytesAt_of (Nat.le_refl _) hb.2.1]
      exact h

end

section
variable (p : Params) (stack : Nat)

theorem signOut : PostOut (signContract p RISCV64.abi stack) ((signSig p).retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sk, mu, rnd, sig, sc], _ =>
      simp only [signSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      show Outcome _ r (Spec.Sha3.bytesAt m₂ sig p.sigLen)
      rw [bytesAt_of (Nat.le_refl _) hb.2.2.2.1]
      exact h

theorem preparedSignOut : PostOut (Spec.MlDsa.preparedSignContract p RISCV64.abi stack) ((Spec.MlDsa.preparedSignSig p).retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sk, mu, rnd, sig, sc], _ =>
      simp only [Spec.MlDsa.preparedSignSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      show Outcome _ r (Spec.Sha3.bytesAt m₂ sig p.sigLen)
      rw [bytesAt_of (Nat.le_refl _) hb.2.2.2.1]
      exact h

theorem signMessageOut : PostOut (signMessageContract p RISCV64.abi stack) ((signMessageSig p).retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sk, msg, ml, ctx, cl, rnd, sig, sc], _ =>
      simp only [signMessageSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      have e := bytesAt_of (n := p.sigLen) (Nat.le_refl _) hb.2.2.2.2.1
      show match formatMessage (Spec.Sha3.bytesAt m ctx ((ArgWord.int RISCV64.abi.ptrBits).ofRaw cl).toNat)
          (Spec.Sha3.bytesAt m msg ((ArgWord.int RISCV64.abi.ptrBits).ofRaw ml).toNat) with
        | none => r = 2
        | some M' => Outcome (fun b => signInternal p b (Spec.Sha3.bytesAt m sk p.skLen) M'
            (Spec.Sha3.bytesAt m rnd 32)) r (Spec.Sha3.bytesAt m₂ sig p.sigLen)
      rw [e]
      exact h

theorem preparedSignMessageOut :
    PostOut (preparedSignMessageContract p RISCV64.abi stack) ((preparedSignMessageSig p).retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sk, msg, ml, ctx, cl, rnd, sig, sc], _ =>
      simp only [preparedSignMessageSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      have e := bytesAt_of (n := p.sigLen) (Nat.le_refl _) hb.2.2.2.2.1
      show match formatMessage (Spec.Sha3.bytesAt m ctx ((ArgWord.int RISCV64.abi.ptrBits).ofRaw cl).toNat)
          (Spec.Sha3.bytesAt m msg ((ArgWord.int RISCV64.abi.ptrBits).ofRaw ml).toNat) with
        | none => r = 2
        | some M' => Outcome (fun b => signInternal p b (Spec.Sha3.bytesAt m sk p.skLen) M'
            (Spec.Sha3.bytesAt m rnd 32)) r (Spec.Sha3.bytesAt m₂ sig p.sigLen)
      rw [e]
      exact h

theorem verifyOut : PostOut (verifyContract p RISCV64.abi stack) ((verifySig p).retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen _ h => by
    match vs, hlen with
    | [_, _, _, _], _ => exact h

theorem preparedVerifyOut : PostOut (Spec.MlDsa.preparedVerifyContract p RISCV64.abi stack) ((Spec.MlDsa.preparedVerifySig p).retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen _ h => by
    match vs, hlen with
    | [_, _, _, _], _ => exact h

theorem verifyMessageCachedOut :
    PostOut (verifyMessageCachedContract p RISCV64.abi stack) ((verifyMessageCachedSig p).retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen _ h => by
    match vs, hlen with
    | [_, _, _, _, _, _, _, _], _ => exact h

theorem preparedVerifyMessageOut :
    PostOut (preparedVerifyMessageContract p RISCV64.abi stack) ((preparedVerifyMessageSig p).retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen _ h => by
    match vs, hlen with
    | [_, _, _, _, _, _, _, _], _ => exact h

end

/-! ## The registrations -/

def keyGen44Reg : Registration Spec.MlDsa.keyGen44Api RISCV64.target :=
  withScrub {
      code := Impl.MlDsa.RISCV64.KeyGen.keyGen44
      verified := Proof.MlDsa.RISCV64.KeyGen.keyGen44_verified }
    (by exact keyGenOut mlDsa44 _)

def keyGen65Reg : Registration Spec.MlDsa.keyGen65Api RISCV64.target :=
  withScrub {
      code := Impl.MlDsa.RISCV64.KeyGen.keyGen65
      verified := Proof.MlDsa.RISCV64.KeyGen.keyGen65_verified }
    (by exact keyGenOut mlDsa65 _)

def keyGen87Reg : Registration Spec.MlDsa.keyGen87Api RISCV64.target :=
  withScrub {
      code := Impl.MlDsa.RISCV64.KeyGen.keyGen87
      verified := Proof.MlDsa.RISCV64.KeyGen.keyGen87_verified }
    (by exact keyGenOut mlDsa87 _)

def pkTr44Reg : Registration Spec.MlDsa.pkTr44Api RISCV64.target :=
  withScrub {
      code := Impl.MlDsa.RISCV64.PkTr.pkTr mlDsa44
      verified := Proof.MlDsa.RISCV64.PkTr.pkTr44_verified }
    (by exact pkTrOut mlDsa44 _)

def pkTr65Reg : Registration Spec.MlDsa.pkTr65Api RISCV64.target :=
  withScrub {
      code := Impl.MlDsa.RISCV64.PkTr.pkTr mlDsa65
      verified := Proof.MlDsa.RISCV64.PkTr.pkTr65_verified }
    (by exact pkTrOut mlDsa65 _)

def pkTr87Reg : Registration Spec.MlDsa.pkTr87Api RISCV64.target :=
  withScrub {
      code := Impl.MlDsa.RISCV64.PkTr.pkTr mlDsa87
      verified := Proof.MlDsa.RISCV64.PkTr.pkTr87_verified }
    (by exact pkTrOut mlDsa87 _)

def preparePublic44Reg : Registration (preparePublicKeyApi mlDsa44 "mldsa44" "ML-DSA-44") RISCV64.target :=
  withScrub {
      code := Impl.MlDsa.RISCV64.PreparedKey.preparePublic mlDsa44
      verified := Proof.MlDsa.RISCV64.PreparedKey.preparePublic44_verified }
    (by exact pubOut _ (.inl rfl))

def prepareSecret44Reg : Registration (prepareSecretKeyApi mlDsa44 "mldsa44" "ML-DSA-44") RISCV64.target :=
  withScrub {
      code := Impl.MlDsa.RISCV64.PreparedKey.prepareSecret mlDsa44
      verified := Proof.MlDsa.RISCV64.PreparedKey.prepareSecret44_verified }
    (by exact secOut _ (.inl rfl))

def preparePublic65Reg : Registration (preparePublicKeyApi mlDsa65 "mldsa65" "ML-DSA-65") RISCV64.target :=
  withScrub {
      code := Impl.MlDsa.RISCV64.PreparedKey.preparePublic mlDsa65
      verified := Proof.MlDsa.RISCV64.PreparedKey.preparePublic65_verified }
    (by exact pubOut _ (.inr (.inl rfl)))

def prepareSecret65Reg : Registration (prepareSecretKeyApi mlDsa65 "mldsa65" "ML-DSA-65") RISCV64.target :=
  withScrub {
      code := Impl.MlDsa.RISCV64.PreparedKey.prepareSecret mlDsa65
      verified := Proof.MlDsa.RISCV64.PreparedKey.prepareSecret65_verified }
    (by exact secOut _ (.inr (.inl rfl)))

def preparePublic87Reg : Registration (preparePublicKeyApi mlDsa87 "mldsa87" "ML-DSA-87") RISCV64.target :=
  withScrub {
      code := Impl.MlDsa.RISCV64.PreparedKey.preparePublic mlDsa87
      verified := Proof.MlDsa.RISCV64.PreparedKey.preparePublic87_verified }
    (by exact pubOut _ (.inr (.inr rfl)))

def prepareSecret87Reg : Registration (prepareSecretKeyApi mlDsa87 "mldsa87" "ML-DSA-87") RISCV64.target :=
  withScrub {
      code := Impl.MlDsa.RISCV64.PreparedKey.prepareSecret mlDsa87
      verified := Proof.MlDsa.RISCV64.PreparedKey.prepareSecret87_verified }
    (by exact secOut _ (.inr (.inr rfl)))

/-! ## Signing and verification -/

def sign44Reg : Registration Spec.MlDsa.sign44Api RISCV64.target :=
  withScrub {
      code := Impl.MlDsa.RISCV64.Sign.sign44
      verified := Proof.MlDsa.RISCV64.PreparedKey.sign44_verified }
    (by exact signOut mlDsa44 _)

def signPrepared44Reg : Registration (preparedSignApi mlDsa44 "mldsa44" "ML-DSA-44") RISCV64.target :=
  withScrub {
      code := Impl.MlDsa.RISCV64.Sign.sign44E true
      verified := Proof.MlDsa.RISCV64.PreparedKey.signPrepared44_verified }
    (by exact preparedSignOut mlDsa44 _)

def verify44Reg : Registration Spec.MlDsa.verify44Api RISCV64.target :=
  withScrub {
      code := Impl.MlDsa.RISCV64.Verify.verify44
      verified := Proof.MlDsa.RISCV64.PreparedKey.verify44_verified }
    (by exact verifyOut mlDsa44 _)

def verifyPrepared44Reg : Registration (preparedVerifyApi mlDsa44 "mldsa44" "ML-DSA-44") RISCV64.target :=
  withScrub {
      code := Impl.MlDsa.RISCV64.Verify.verify44E true
      verified := Proof.MlDsa.RISCV64.PreparedKey.verifyPrepared44_verified }
    (by exact preparedVerifyOut mlDsa44 _)

def signMessage44Reg : Registration Spec.MlDsa.signMessage44Api RISCV64.target :=
  withScrub {
      code := Impl.MlDsa.RISCV64.Message.signMessage (Spec.MlDsa.sign44Api.name ++ "_core")
        Impl.MlDsa.RISCV64.Sign.sign44 mlDsa44
      verified := Proof.MlDsa.RISCV64.Message.signMessage44_verified }
    (by exact signMessageOut mlDsa44 _)

def preparedSignMessage44Reg :
    Registration (preparedSignMessageApi mlDsa44 "mldsa44" "ML-DSA-44") RISCV64.target :=
  withScrub {
      code := Impl.MlDsa.RISCV64.Message.signMessage (Proof.MlDsa.preparedSignName "mldsa44" ++ "_core")
        (Impl.MlDsa.RISCV64.Sign.sign44E true) mlDsa44
      verified := Proof.MlDsa.RISCV64.Message.signMessagePrepared44_verified }
    (by exact preparedSignMessageOut mlDsa44 _)

def verifyMessageCached44Reg :
    Registration (verifyMessageCachedApi mlDsa44 "mldsa44" "ML-DSA-44") RISCV64.target :=
  withScrub {
      code := Impl.MlDsa.RISCV64.Message.verifyMessageCached (Spec.MlDsa.verify44Api.name ++ "_core")
        Impl.MlDsa.RISCV64.Verify.verify44 mlDsa44
      verified := Proof.MlDsa.RISCV64.Message.verifyMessageCached44_verified }
    (by exact verifyMessageCachedOut mlDsa44 _)

def preparedVerifyMessage44Reg :
    Registration (preparedVerifyMessageApi mlDsa44 "mldsa44" "ML-DSA-44") RISCV64.target :=
  withScrub {
      code := Impl.MlDsa.RISCV64.Message.verifyMessageCached (Proof.MlDsa.preparedVerifyName "mldsa44" ++ "_core")
        (Impl.MlDsa.RISCV64.Verify.verify44E true) mlDsa44
      verified := Proof.MlDsa.RISCV64.Message.verifyMessagePrepared44_verified }
    (by exact preparedVerifyMessageOut mlDsa44 _)

def sign65Reg : Registration Spec.MlDsa.sign65Api RISCV64.target :=
  withScrub {
      code := Impl.MlDsa.RISCV64.Sign.sign65
      verified := Proof.MlDsa.RISCV64.PreparedKey.sign65_verified }
    (by exact signOut mlDsa65 _)

def signPrepared65Reg : Registration (preparedSignApi mlDsa65 "mldsa65" "ML-DSA-65") RISCV64.target :=
  withScrub {
      code := Impl.MlDsa.RISCV64.Sign.sign65E true
      verified := Proof.MlDsa.RISCV64.PreparedKey.signPrepared65_verified }
    (by exact preparedSignOut mlDsa65 _)

def verify65Reg : Registration Spec.MlDsa.verify65Api RISCV64.target :=
  withScrub {
      code := Impl.MlDsa.RISCV64.Verify.verify65
      verified := Proof.MlDsa.RISCV64.PreparedKey.verify65_verified }
    (by exact verifyOut mlDsa65 _)

def verifyPrepared65Reg : Registration (preparedVerifyApi mlDsa65 "mldsa65" "ML-DSA-65") RISCV64.target :=
  withScrub {
      code := Impl.MlDsa.RISCV64.Verify.verify65E true
      verified := Proof.MlDsa.RISCV64.PreparedKey.verifyPrepared65_verified }
    (by exact preparedVerifyOut mlDsa65 _)

def signMessage65Reg : Registration Spec.MlDsa.signMessage65Api RISCV64.target :=
  withScrub {
      code := Impl.MlDsa.RISCV64.Message.signMessage (Spec.MlDsa.sign65Api.name ++ "_core")
        Impl.MlDsa.RISCV64.Sign.sign65 mlDsa65
      verified := Proof.MlDsa.RISCV64.Message.signMessage65_verified }
    (by exact signMessageOut mlDsa65 _)

def preparedSignMessage65Reg :
    Registration (preparedSignMessageApi mlDsa65 "mldsa65" "ML-DSA-65") RISCV64.target :=
  withScrub {
      code := Impl.MlDsa.RISCV64.Message.signMessage (Proof.MlDsa.preparedSignName "mldsa65" ++ "_core")
        (Impl.MlDsa.RISCV64.Sign.sign65E true) mlDsa65
      verified := Proof.MlDsa.RISCV64.Message.signMessagePrepared65_verified }
    (by exact preparedSignMessageOut mlDsa65 _)

def verifyMessageCached65Reg :
    Registration (verifyMessageCachedApi mlDsa65 "mldsa65" "ML-DSA-65") RISCV64.target :=
  withScrub {
      code := Impl.MlDsa.RISCV64.Message.verifyMessageCached (Spec.MlDsa.verify65Api.name ++ "_core")
        Impl.MlDsa.RISCV64.Verify.verify65 mlDsa65
      verified := Proof.MlDsa.RISCV64.Message.verifyMessageCached65_verified }
    (by exact verifyMessageCachedOut mlDsa65 _)

def preparedVerifyMessage65Reg :
    Registration (preparedVerifyMessageApi mlDsa65 "mldsa65" "ML-DSA-65") RISCV64.target :=
  withScrub {
      code := Impl.MlDsa.RISCV64.Message.verifyMessageCached (Proof.MlDsa.preparedVerifyName "mldsa65" ++ "_core")
        (Impl.MlDsa.RISCV64.Verify.verify65E true) mlDsa65
      verified := Proof.MlDsa.RISCV64.Message.verifyMessagePrepared65_verified }
    (by exact preparedVerifyMessageOut mlDsa65 _)

def sign87Reg : Registration Spec.MlDsa.sign87Api RISCV64.target :=
  withScrub {
      code := Impl.MlDsa.RISCV64.Sign.sign87
      verified := Proof.MlDsa.RISCV64.PreparedKey.sign87_verified }
    (by exact signOut mlDsa87 _)

def signPrepared87Reg : Registration (preparedSignApi mlDsa87 "mldsa87" "ML-DSA-87") RISCV64.target :=
  withScrub {
      code := Impl.MlDsa.RISCV64.Sign.sign87E true
      verified := Proof.MlDsa.RISCV64.PreparedKey.signPrepared87_verified }
    (by exact preparedSignOut mlDsa87 _)

def verify87Reg : Registration Spec.MlDsa.verify87Api RISCV64.target :=
  withScrub {
      code := Impl.MlDsa.RISCV64.Verify.verify87
      verified := Proof.MlDsa.RISCV64.PreparedKey.verify87_verified }
    (by exact verifyOut mlDsa87 _)

def verifyPrepared87Reg : Registration (preparedVerifyApi mlDsa87 "mldsa87" "ML-DSA-87") RISCV64.target :=
  withScrub {
      code := Impl.MlDsa.RISCV64.Verify.verify87E true
      verified := Proof.MlDsa.RISCV64.PreparedKey.verifyPrepared87_verified }
    (by exact preparedVerifyOut mlDsa87 _)

def signMessage87Reg : Registration Spec.MlDsa.signMessage87Api RISCV64.target :=
  withScrub {
      code := Impl.MlDsa.RISCV64.Message.signMessage (Spec.MlDsa.sign87Api.name ++ "_core")
        Impl.MlDsa.RISCV64.Sign.sign87 mlDsa87
      verified := Proof.MlDsa.RISCV64.Message.signMessage87_verified }
    (by exact signMessageOut mlDsa87 _)

def preparedSignMessage87Reg :
    Registration (preparedSignMessageApi mlDsa87 "mldsa87" "ML-DSA-87") RISCV64.target :=
  withScrub {
      code := Impl.MlDsa.RISCV64.Message.signMessage (Proof.MlDsa.preparedSignName "mldsa87" ++ "_core")
        (Impl.MlDsa.RISCV64.Sign.sign87E true) mlDsa87
      verified := Proof.MlDsa.RISCV64.Message.signMessagePrepared87_verified }
    (by exact preparedSignMessageOut mlDsa87 _)

def verifyMessageCached87Reg :
    Registration (verifyMessageCachedApi mlDsa87 "mldsa87" "ML-DSA-87") RISCV64.target :=
  withScrub {
      code := Impl.MlDsa.RISCV64.Message.verifyMessageCached (Spec.MlDsa.verify87Api.name ++ "_core")
        Impl.MlDsa.RISCV64.Verify.verify87 mlDsa87
      verified := Proof.MlDsa.RISCV64.Message.verifyMessageCached87_verified }
    (by exact verifyMessageCachedOut mlDsa87 _)

def preparedVerifyMessage87Reg :
    Registration (preparedVerifyMessageApi mlDsa87 "mldsa87" "ML-DSA-87") RISCV64.target :=
  withScrub {
      code := Impl.MlDsa.RISCV64.Message.verifyMessageCached (Proof.MlDsa.preparedVerifyName "mldsa87" ++ "_core")
        (Impl.MlDsa.RISCV64.Verify.verify87E true) mlDsa87
      verified := Proof.MlDsa.RISCV64.Message.verifyMessagePrepared87_verified }
    (by exact preparedVerifyMessageOut mlDsa87 _)

end VG.Proof.MlDsa.RISCV64.Scrub
