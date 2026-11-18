module

public import VerifiedGarbage.Spec.MlDsa.Contract
public import VerifiedGarbage.Spec.MlDsa.PreparedKey
public import VerifiedGarbage.Spec.MlDsa.PkTr
public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Inst
public import VerifiedGarbage.Proof.MlDsa.RISCV64.PkTr
public import VerifiedGarbage.Proof.MlDsa.RISCV64.PreparedKey.Inst
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# ML-DSA on RISC-V, without secret residue

Key generation, `pk_tr` and the preparation of keys, followed by
`Impl.Scrub.RISCV64.scrubTail` (`RISCV64.Scrub.withScrub`), which clears the
caller-saved registers and the stack their frames used (1168 bytes, the
sponge's, and 1072 for the preparations). Their postconditions read the
memory on return only within their outputs (`RISCV64.Scrub.PostOut`); the
proofs are PPC64LE's (`Proof/MlDsa/PPC64LE/Scrub.lean`), for this target's
scrub.
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

end VG.Proof.MlDsa.RISCV64.Scrub
