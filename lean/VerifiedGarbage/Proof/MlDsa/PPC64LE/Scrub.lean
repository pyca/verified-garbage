module

public import VerifiedGarbage.Spec.MlDsa.Contract
public import VerifiedGarbage.Spec.MlDsa.PreparedKey
public import VerifiedGarbage.Spec.MlDsa.CachedVerify
public import VerifiedGarbage.Spec.MlDsa.PkTr
public import VerifiedGarbage.Proof.Framework.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Message.Inst
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.PreparedKey
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.PkTr
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Inst
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sign.Inst
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Verify.Inst
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-DSA on PPC64LE, without secret residue

Key generation, `pk_tr`, the preparation of keys, signing and verification
(of a message representative or of a message, with a key or a prepared key),
followed by `Impl.Scrub.PPC64LE.scrubTail` (`PPC64LE.Scrub.withScrub`), which
clears the volatile registers and the stack their frames used. The
postconditions of key generation, `pk_tr`, the preparations and signing read
the memory on return only within their outputs, and those of verification
not at all; the proofs are x86-64's (`Proof/MlDsa/X86_64/Scrub.lean`,
`Proof/MlDsa/X86_64/PreparedKey/Scrub.lean`), for this target's scrub.

Signing and verifying a message call the signing or verification of a
message representative: here as the internal `vg_mldsa*_sign_core`, … (an
`_core` suffix to each name), whose code is that of the exported functions
without the clearing (`Message.signMessage_verified`, generic in the name).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub VG.Spec.MlDsa

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
    PostOut (preparePublicKeyContract p PPC64LE.abi stack) ((preparePublicKeySig p).retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨pk, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨prep, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [preparePublicKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hw := agreeBuf (pub_bytes p hp) hb.2.1
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

theorem secOut (stack : Nat) {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    PostOut (prepareSecretKeyContract p PPC64LE.abi stack) ((prepareSecretKeySig p).retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨sk, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨prep, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [prepareSecretKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hw := agreeBuf (sec_bytes p hp) hb.2.1
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

section
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

variable (p : Params) (stack : Nat)

theorem keyGenOut : PostOut (keyGenContract p PPC64LE.abi stack) ((keyGenSig p).retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [seed, pk, sk, sc], _ =>
      simp only [keyGenSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      show Outcome _ r (Spec.Sha3.bytesAt m₂ pk p.pkLen, Spec.Sha3.bytesAt m₂ sk p.skLen)
      rw [bytesAt_of (Nat.le_refl _) hb.2.1, bytesAt_of (Nat.le_refl _) hb.2.2.1]
      exact h

theorem pkTrOut : PostOut (pkTrContract p PPC64LE.abi stack) ((pkTrSig p).retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [pk, tr, sc], _ =>
      simp only [pkTrSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      show Spec.Sha3.bytesAt m₂ tr 64 = _
      rw [bytesAt_of (Nat.le_refl _) hb.2.1]
      exact h

theorem signOut : PostOut (signContract p PPC64LE.abi stack) ((signSig p).retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sk, mu, rnd, sig, sc], _ =>
      simp only [signSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      show Outcome _ r (Spec.Sha3.bytesAt m₂ sig p.sigLen)
      rw [bytesAt_of (Nat.le_refl _) hb.2.2.2.1]
      exact h

theorem preparedSignOut : PostOut (Spec.MlDsa.preparedSignContract p PPC64LE.abi stack) ((Spec.MlDsa.preparedSignSig p).retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sk, mu, rnd, sig, sc], _ =>
      simp only [Spec.MlDsa.preparedSignSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      show Outcome _ r (Spec.Sha3.bytesAt m₂ sig p.sigLen)
      rw [bytesAt_of (Nat.le_refl _) hb.2.2.2.1]
      exact h

theorem signMessageOut : PostOut (signMessageContract p PPC64LE.abi stack) ((signMessageSig p).retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sk, msg, ml, ctx, cl, rnd, sig, sc], _ =>
      simp only [signMessageSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      have e := bytesAt_of (n := p.sigLen) (Nat.le_refl _) hb.2.2.2.2.1
      show match formatMessage (Spec.Sha3.bytesAt m ctx ((ArgWord.int PPC64LE.abi.ptrBits).ofRaw cl).toNat)
          (Spec.Sha3.bytesAt m msg ((ArgWord.int PPC64LE.abi.ptrBits).ofRaw ml).toNat) with
        | none => r = 2
        | some M' => Outcome (fun b => signInternal p b (Spec.Sha3.bytesAt m sk p.skLen) M'
            (Spec.Sha3.bytesAt m rnd 32)) r (Spec.Sha3.bytesAt m₂ sig p.sigLen)
      rw [e]
      exact h

theorem preparedSignMessageOut :
    PostOut (preparedSignMessageContract p PPC64LE.abi stack) ((preparedSignMessageSig p).retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sk, msg, ml, ctx, cl, rnd, sig, sc], _ =>
      simp only [preparedSignMessageSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      have e := bytesAt_of (n := p.sigLen) (Nat.le_refl _) hb.2.2.2.2.1
      show match formatMessage (Spec.Sha3.bytesAt m ctx ((ArgWord.int PPC64LE.abi.ptrBits).ofRaw cl).toNat)
          (Spec.Sha3.bytesAt m msg ((ArgWord.int PPC64LE.abi.ptrBits).ofRaw ml).toNat) with
        | none => r = 2
        | some M' => Outcome (fun b => signInternal p b (Spec.Sha3.bytesAt m sk p.skLen) M'
            (Spec.Sha3.bytesAt m rnd 32)) r (Spec.Sha3.bytesAt m₂ sig p.sigLen)
      rw [e]
      exact h

theorem verifyOut : PostOut (verifyContract p PPC64LE.abi stack) ((verifySig p).retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen _ h => by
    match vs, hlen with
    | [_, _, _, _], _ => exact h

theorem preparedVerifyOut : PostOut (Spec.MlDsa.preparedVerifyContract p PPC64LE.abi stack) ((Spec.MlDsa.preparedVerifySig p).retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen _ h => by
    match vs, hlen with
    | [_, _, _, _], _ => exact h

theorem verifyMessageCachedOut :
    PostOut (verifyMessageCachedContract p PPC64LE.abi stack) ((verifyMessageCachedSig p).retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen _ h => by
    match vs, hlen with
    | [_, _, _, _, _, _, _, _], _ => exact h

theorem preparedVerifyMessageOut :
    PostOut (preparedVerifyMessageContract p PPC64LE.abi stack) ((preparedVerifyMessageSig p).retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen _ h => by
    match vs, hlen with
    | [_, _, _, _, _, _, _, _], _ => exact h

end

def keyGen44Reg : Registration Spec.MlDsa.keyGen44Api PPC64LE.target :=
  withScrub {
      code := Impl.MlDsa.PPC64LE.KeyGen.keyGen44
      verified := Proof.MlDsa.PPC64LE.KeyGen.keyGen44_verified }
    (by exact keyGenOut Spec.MlDsa.mlDsa44 _)

def pkTr44Reg : Registration Spec.MlDsa.pkTr44Api PPC64LE.target :=
  withScrub {
      code := Impl.MlDsa.PPC64LE.PkTr.pkTr Spec.MlDsa.mlDsa44
      verified := Proof.MlDsa.PPC64LE.PkTr.pkTr44_verified }
    (by exact pkTrOut Spec.MlDsa.mlDsa44 _)

def preparePublic44Reg : Registration (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44") PPC64LE.target :=
  withScrub {
      code := Impl.MlDsa.PPC64LE.PreparedKey.preparePublic Spec.MlDsa.mlDsa44
      verified := Proof.MlDsa.PPC64LE.PreparedKey.preparePublic_verified (.inl rfl) }
    (by exact pubOut _ (.inl rfl))

def prepareSecret44Reg : Registration (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44") PPC64LE.target :=
  withScrub {
      code := Impl.MlDsa.PPC64LE.PreparedKey.prepareSecret Spec.MlDsa.mlDsa44
      verified := Proof.MlDsa.PPC64LE.PreparedKey.prepareSecret_verified (.inl rfl) }
    (by exact secOut _ (.inl rfl))

def sign44Reg : Registration Spec.MlDsa.sign44Api PPC64LE.target :=
  withScrub {
      code := Impl.MlDsa.PPC64LE.Sign.sign44
      verified := Proof.MlDsa.PPC64LE.Sign.sign44_verified }
    (by exact signOut Spec.MlDsa.mlDsa44 _)

def signPrepared44Reg : Registration (Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44") PPC64LE.target :=
  withScrub {
      code := Impl.MlDsa.PPC64LE.Sign.signPrepared44
      verified := Proof.MlDsa.PPC64LE.Sign.signPrepared44_verified }
    (by exact preparedSignOut Spec.MlDsa.mlDsa44 _)

def signMessage44Reg : Registration Spec.MlDsa.signMessage44Api PPC64LE.target :=
  withScrub {
      code := Impl.MlDsa.PPC64LE.Message.signMessage (Spec.MlDsa.sign44Api.name ++ "_core")
        Impl.MlDsa.PPC64LE.Sign.sign44 Spec.MlDsa.mlDsa44
      verified := Message.signMessage_verified (.inl rfl) (by decide) Message.sign44Fn _
        (Message.signMessage_sat (.inl rfl)) }
    (by exact signMessageOut Spec.MlDsa.mlDsa44 _)

def preparedSignMessage44Reg : Registration (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44") PPC64LE.target :=
  withScrub {
      code := Impl.MlDsa.PPC64LE.Message.signMessage (Proof.MlDsa.preparedSignName "mldsa44" ++ "_core")
        Impl.MlDsa.PPC64LE.Sign.signPrepared44 Spec.MlDsa.mlDsa44
      verified := Message.signMessage_verified (.inl rfl) (by decide) Message.signPrepared44Fn _
        (Message.preparedSignMessage_sat (.inl rfl)) }
    (by exact preparedSignMessageOut Spec.MlDsa.mlDsa44 _)

def verify44Reg : Registration Spec.MlDsa.verify44Api PPC64LE.target :=
  withScrub {
      code := Impl.MlDsa.PPC64LE.Verify.verify44
      verified := Proof.MlDsa.PPC64LE.Verify.verify44_verified }
    (by exact verifyOut Spec.MlDsa.mlDsa44 _)

def verifyPrepared44Reg : Registration (Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44") PPC64LE.target :=
  withScrub {
      code := Impl.MlDsa.PPC64LE.Verify.verifyPrepared44
      verified := Proof.MlDsa.PPC64LE.Verify.verifyPrepared44_verified }
    (by exact preparedVerifyOut Spec.MlDsa.mlDsa44 _)

def verifyMessageCached44Reg : Registration (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44") PPC64LE.target :=
  withScrub {
      code := Impl.MlDsa.PPC64LE.Message.verifyMessageCached (Spec.MlDsa.verify44Api.name ++ "_core")
        Impl.MlDsa.PPC64LE.Verify.verify44 Spec.MlDsa.mlDsa44
      verified := Message.verifyMessageCached_verified (.inl rfl) (by decide) Message.verify44Fn _
        (Message.verifyMessageCached_sat (.inl rfl)) }
    (by exact verifyMessageCachedOut Spec.MlDsa.mlDsa44 _)

def preparedVerifyMessage44Reg : Registration (Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44") PPC64LE.target :=
  withScrub {
      code := Impl.MlDsa.PPC64LE.Message.verifyMessageCached (Proof.MlDsa.preparedVerifyName "mldsa44" ++ "_core")
        Impl.MlDsa.PPC64LE.Verify.verifyPrepared44 Spec.MlDsa.mlDsa44
      verified := Message.verifyMessageCached_verified (.inl rfl) (by decide) Message.verifyPrepared44Fn _
        (Message.preparedVerifyMessage_sat (.inl rfl)) }
    (by exact preparedVerifyMessageOut Spec.MlDsa.mlDsa44 _)

def keyGen65Reg : Registration Spec.MlDsa.keyGen65Api PPC64LE.target :=
  withScrub {
      code := Impl.MlDsa.PPC64LE.KeyGen.keyGen65
      verified := Proof.MlDsa.PPC64LE.KeyGen.keyGen65_verified }
    (by exact keyGenOut Spec.MlDsa.mlDsa65 _)

def pkTr65Reg : Registration Spec.MlDsa.pkTr65Api PPC64LE.target :=
  withScrub {
      code := Impl.MlDsa.PPC64LE.PkTr.pkTr Spec.MlDsa.mlDsa65
      verified := Proof.MlDsa.PPC64LE.PkTr.pkTr65_verified }
    (by exact pkTrOut Spec.MlDsa.mlDsa65 _)

def preparePublic65Reg : Registration (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65") PPC64LE.target :=
  withScrub {
      code := Impl.MlDsa.PPC64LE.PreparedKey.preparePublic Spec.MlDsa.mlDsa65
      verified := Proof.MlDsa.PPC64LE.PreparedKey.preparePublic_verified (.inr (.inl rfl)) }
    (by exact pubOut _ (.inr (.inl rfl)))

def prepareSecret65Reg : Registration (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65") PPC64LE.target :=
  withScrub {
      code := Impl.MlDsa.PPC64LE.PreparedKey.prepareSecret Spec.MlDsa.mlDsa65
      verified := Proof.MlDsa.PPC64LE.PreparedKey.prepareSecret_verified (.inr (.inl rfl)) }
    (by exact secOut _ (.inr (.inl rfl)))

def sign65Reg : Registration Spec.MlDsa.sign65Api PPC64LE.target :=
  withScrub {
      code := Impl.MlDsa.PPC64LE.Sign.sign65
      verified := Proof.MlDsa.PPC64LE.Sign.sign65_verified }
    (by exact signOut Spec.MlDsa.mlDsa65 _)

def signPrepared65Reg : Registration (Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65") PPC64LE.target :=
  withScrub {
      code := Impl.MlDsa.PPC64LE.Sign.signPrepared65
      verified := Proof.MlDsa.PPC64LE.Sign.signPrepared65_verified }
    (by exact preparedSignOut Spec.MlDsa.mlDsa65 _)

def signMessage65Reg : Registration Spec.MlDsa.signMessage65Api PPC64LE.target :=
  withScrub {
      code := Impl.MlDsa.PPC64LE.Message.signMessage (Spec.MlDsa.sign65Api.name ++ "_core")
        Impl.MlDsa.PPC64LE.Sign.sign65 Spec.MlDsa.mlDsa65
      verified := Message.signMessage_verified (.inr (.inl rfl)) (by decide) Message.sign65Fn _
        (Message.signMessage_sat (.inr (.inl rfl))) }
    (by exact signMessageOut Spec.MlDsa.mlDsa65 _)

def preparedSignMessage65Reg : Registration (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65") PPC64LE.target :=
  withScrub {
      code := Impl.MlDsa.PPC64LE.Message.signMessage (Proof.MlDsa.preparedSignName "mldsa65" ++ "_core")
        Impl.MlDsa.PPC64LE.Sign.signPrepared65 Spec.MlDsa.mlDsa65
      verified := Message.signMessage_verified (.inr (.inl rfl)) (by decide) Message.signPrepared65Fn _
        (Message.preparedSignMessage_sat (.inr (.inl rfl))) }
    (by exact preparedSignMessageOut Spec.MlDsa.mlDsa65 _)

def verify65Reg : Registration Spec.MlDsa.verify65Api PPC64LE.target :=
  withScrub {
      code := Impl.MlDsa.PPC64LE.Verify.verify65
      verified := Proof.MlDsa.PPC64LE.Verify.verify65_verified }
    (by exact verifyOut Spec.MlDsa.mlDsa65 _)

def verifyPrepared65Reg : Registration (Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65") PPC64LE.target :=
  withScrub {
      code := Impl.MlDsa.PPC64LE.Verify.verifyPrepared65
      verified := Proof.MlDsa.PPC64LE.Verify.verifyPrepared65_verified }
    (by exact preparedVerifyOut Spec.MlDsa.mlDsa65 _)

def verifyMessageCached65Reg : Registration (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65") PPC64LE.target :=
  withScrub {
      code := Impl.MlDsa.PPC64LE.Message.verifyMessageCached (Spec.MlDsa.verify65Api.name ++ "_core")
        Impl.MlDsa.PPC64LE.Verify.verify65 Spec.MlDsa.mlDsa65
      verified := Message.verifyMessageCached_verified (.inr (.inl rfl)) (by decide) Message.verify65Fn _
        (Message.verifyMessageCached_sat (.inr (.inl rfl))) }
    (by exact verifyMessageCachedOut Spec.MlDsa.mlDsa65 _)

def preparedVerifyMessage65Reg : Registration (Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65") PPC64LE.target :=
  withScrub {
      code := Impl.MlDsa.PPC64LE.Message.verifyMessageCached (Proof.MlDsa.preparedVerifyName "mldsa65" ++ "_core")
        Impl.MlDsa.PPC64LE.Verify.verifyPrepared65 Spec.MlDsa.mlDsa65
      verified := Message.verifyMessageCached_verified (.inr (.inl rfl)) (by decide) Message.verifyPrepared65Fn _
        (Message.preparedVerifyMessage_sat (.inr (.inl rfl))) }
    (by exact preparedVerifyMessageOut Spec.MlDsa.mlDsa65 _)

def keyGen87Reg : Registration Spec.MlDsa.keyGen87Api PPC64LE.target :=
  withScrub {
      code := Impl.MlDsa.PPC64LE.KeyGen.keyGen87
      verified := Proof.MlDsa.PPC64LE.KeyGen.keyGen87_verified }
    (by exact keyGenOut Spec.MlDsa.mlDsa87 _)

def pkTr87Reg : Registration Spec.MlDsa.pkTr87Api PPC64LE.target :=
  withScrub {
      code := Impl.MlDsa.PPC64LE.PkTr.pkTr Spec.MlDsa.mlDsa87
      verified := Proof.MlDsa.PPC64LE.PkTr.pkTr87_verified }
    (by exact pkTrOut Spec.MlDsa.mlDsa87 _)

def preparePublic87Reg : Registration (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87") PPC64LE.target :=
  withScrub {
      code := Impl.MlDsa.PPC64LE.PreparedKey.preparePublic Spec.MlDsa.mlDsa87
      verified := Proof.MlDsa.PPC64LE.PreparedKey.preparePublic_verified (.inr (.inr rfl)) }
    (by exact pubOut _ (.inr (.inr rfl)))

def prepareSecret87Reg : Registration (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87") PPC64LE.target :=
  withScrub {
      code := Impl.MlDsa.PPC64LE.PreparedKey.prepareSecret Spec.MlDsa.mlDsa87
      verified := Proof.MlDsa.PPC64LE.PreparedKey.prepareSecret_verified (.inr (.inr rfl)) }
    (by exact secOut _ (.inr (.inr rfl)))

def sign87Reg : Registration Spec.MlDsa.sign87Api PPC64LE.target :=
  withScrub {
      code := Impl.MlDsa.PPC64LE.Sign.sign87
      verified := Proof.MlDsa.PPC64LE.Sign.sign87_verified }
    (by exact signOut Spec.MlDsa.mlDsa87 _)

def signPrepared87Reg : Registration (Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87") PPC64LE.target :=
  withScrub {
      code := Impl.MlDsa.PPC64LE.Sign.signPrepared87
      verified := Proof.MlDsa.PPC64LE.Sign.signPrepared87_verified }
    (by exact preparedSignOut Spec.MlDsa.mlDsa87 _)

def signMessage87Reg : Registration Spec.MlDsa.signMessage87Api PPC64LE.target :=
  withScrub {
      code := Impl.MlDsa.PPC64LE.Message.signMessage (Spec.MlDsa.sign87Api.name ++ "_core")
        Impl.MlDsa.PPC64LE.Sign.sign87 Spec.MlDsa.mlDsa87
      verified := Message.signMessage_verified (.inr (.inr rfl)) (by decide) Message.sign87Fn _
        (Message.signMessage_sat (.inr (.inr rfl))) }
    (by exact signMessageOut Spec.MlDsa.mlDsa87 _)

def preparedSignMessage87Reg : Registration (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87") PPC64LE.target :=
  withScrub {
      code := Impl.MlDsa.PPC64LE.Message.signMessage (Proof.MlDsa.preparedSignName "mldsa87" ++ "_core")
        Impl.MlDsa.PPC64LE.Sign.signPrepared87 Spec.MlDsa.mlDsa87
      verified := Message.signMessage_verified (.inr (.inr rfl)) (by decide) Message.signPrepared87Fn _
        (Message.preparedSignMessage_sat (.inr (.inr rfl))) }
    (by exact preparedSignMessageOut Spec.MlDsa.mlDsa87 _)

def verify87Reg : Registration Spec.MlDsa.verify87Api PPC64LE.target :=
  withScrub {
      code := Impl.MlDsa.PPC64LE.Verify.verify87
      verified := Proof.MlDsa.PPC64LE.Verify.verify87_verified }
    (by exact verifyOut Spec.MlDsa.mlDsa87 _)

def verifyPrepared87Reg : Registration (Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87") PPC64LE.target :=
  withScrub {
      code := Impl.MlDsa.PPC64LE.Verify.verifyPrepared87
      verified := Proof.MlDsa.PPC64LE.Verify.verifyPrepared87_verified }
    (by exact preparedVerifyOut Spec.MlDsa.mlDsa87 _)

def verifyMessageCached87Reg : Registration (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87") PPC64LE.target :=
  withScrub {
      code := Impl.MlDsa.PPC64LE.Message.verifyMessageCached (Spec.MlDsa.verify87Api.name ++ "_core")
        Impl.MlDsa.PPC64LE.Verify.verify87 Spec.MlDsa.mlDsa87
      verified := Message.verifyMessageCached_verified (.inr (.inr rfl)) (by decide) Message.verify87Fn _
        (Message.verifyMessageCached_sat (.inr (.inr rfl))) }
    (by exact verifyMessageCachedOut Spec.MlDsa.mlDsa87 _)

def preparedVerifyMessage87Reg : Registration (Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87") PPC64LE.target :=
  withScrub {
      code := Impl.MlDsa.PPC64LE.Message.verifyMessageCached (Proof.MlDsa.preparedVerifyName "mldsa87" ++ "_core")
        Impl.MlDsa.PPC64LE.Verify.verifyPrepared87 Spec.MlDsa.mlDsa87
      verified := Message.verifyMessageCached_verified (.inr (.inr rfl)) (by decide) Message.verifyPrepared87Fn _
        (Message.preparedVerifyMessage_sat (.inr (.inr rfl))) }
    (by exact preparedVerifyMessageOut Spec.MlDsa.mlDsa87 _)

end VG.Proof.MlDsa.PPC64LE.Scrub
