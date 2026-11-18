module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Md5
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha1
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha224
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha256
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha384
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512_224
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512_256
public import VerifiedGarbage.Proof.Hmac.AnyKey
public import VerifiedGarbage.Proof.Hmac.Scratch
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# HMAC on RISC-V, without secret residue

Each hash's HMAC `init` and `finalize`, followed by
`Impl.Scrub.RISCV64.scrubTail` (`RISCV64.Scrub.withScrub`). Their
postconditions read the memory on return only within their buffers, as on
x86-64 (`Proof/Pbkdf2/Md/X86_64/ScrubStream.lean`).
-/

@[expose] public section

namespace VG.Proof.Hmac.Stream.RISCV64.Scrub

open VG.RISCV64 VG.RISCV64.Scrub

theorem hmacInitAnyOut (I : Spec.Hmac.Instance) (hR : Proof.Hmac.ReprLocal I.S) (hS : I.S.stateBytes < 2 ^ 64)
    (stack : Nat) : PostOut (I.initAnyKeyContract abi stack) ((Spec.Hmac.initSig I.S).retBits 64) := by
  unfold Spec.Hmac.Instance.initAnyKeyContract Spec.Hmac.initAnyKeyContract
  exact postOut_of_local (leak := none) ScrubAbi.plain (Proof.Hmac.initPostOut_local I.S _ hR hS)

/-- HMAC's `finalize`'s postcondition reads the memory on return only within
`out`, the HMAC's bytes. -/
theorem hmacFinOut (I : Spec.Hmac.Instance) (hD : I.S.digestBytes < 2 ^ 64) (stack : Nat) :
    PostOut (I.finalizeContract abi stack) ((Spec.Hmac.finalizeSig I.S).retBits 64) := by
  unfold Spec.Hmac.Instance.finalizeContract Spec.Hmac.finalizeContract
  exact postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨inn, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨otr, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ct, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨out, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [Spec.Hmac.finalizeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    have ho : ∀ i < I.S.digestBytes, m₂ (out + BitVec.ofNat 64 i) = m₁ (out + BitVec.ofNat 64 i) :=
      fun i hi => (hb.2.2 _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hD, hi]))).symm
    intro k0 text h1 h2 hri hc hro
    show Spec.Sha256.bytesAt m₂ out I.S.digestBytes = _
    rw [Sha256.Stream.bytesAt_congr ho]
    exact h k0 text h1 h2 hri hc hro

/-- `Spec.Hmac.md5I.initAnyKeyApi`. -/
def md5InitAnyKeyReg : Registration Spec.Hmac.md5I.initAnyKeyApi RISCV64.target :=
  withScrub { code := Proof.Hmac.Stream.RISCV64.Md5.hash.init, verified := Proof.Hmac.Stream.RISCV64.Md5.init }
    (hmacInitAnyOut Spec.Hmac.md5I Proof.Hmac.md5_local (by decide) _)

/-- `Spec.Hmac.md5I.finalizeApi`. -/
def md5FinalizeReg : Registration Spec.Hmac.md5I.finalizeApi RISCV64.target :=
  withScrub { code := Proof.Hmac.Stream.RISCV64.Md5.hash.finalize, verified := Proof.Hmac.Stream.RISCV64.Md5.finalize }
    (hmacFinOut Spec.Hmac.md5I (by decide) _)

/-- `Spec.Hmac.sha1I.initAnyKeyApi`. -/
def sha1InitAnyKeyReg : Registration Spec.Hmac.sha1I.initAnyKeyApi RISCV64.target :=
  withScrub { code := Proof.Hmac.Stream.RISCV64.Sha1.hash.init, verified := Proof.Hmac.Stream.RISCV64.Sha1.init }
    (hmacInitAnyOut Spec.Hmac.sha1I Proof.Hmac.sha1_local (by decide) _)

/-- `Spec.Hmac.sha1I.finalizeApi`. -/
def sha1FinalizeReg : Registration Spec.Hmac.sha1I.finalizeApi RISCV64.target :=
  withScrub { code := Proof.Hmac.Stream.RISCV64.Sha1.hash.finalize, verified := Proof.Hmac.Stream.RISCV64.Sha1.finalize }
    (hmacFinOut Spec.Hmac.sha1I (by decide) _)

/-- `Spec.Hmac.sha224I.initAnyKeyApi`. -/
def sha224InitAnyKeyReg : Registration Spec.Hmac.sha224I.initAnyKeyApi RISCV64.target :=
  withScrub { code := Proof.Hmac.Stream.RISCV64.Sha256Family.hash224.init, verified := Proof.Hmac.Stream.RISCV64.Sha224.init }
    (hmacInitAnyOut Spec.Hmac.sha224I Proof.Hmac.sha224_local (by decide) _)

/-- `Spec.Hmac.sha224I.finalizeApi`. -/
def sha224FinalizeReg : Registration Spec.Hmac.sha224I.finalizeApi RISCV64.target :=
  withScrub { code := Proof.Hmac.Stream.RISCV64.Sha256Family.hash224.finalize, verified := Proof.Hmac.Stream.RISCV64.Sha224.finalize }
    (hmacFinOut Spec.Hmac.sha224I (by decide) _)

/-- `Spec.Hmac.sha256I.initAnyKeyApi`. -/
def sha256InitAnyKeyReg : Registration Spec.Hmac.sha256I.initAnyKeyApi RISCV64.target :=
  withScrub { code := Proof.Hmac.Stream.RISCV64.Sha256Family.hash256.init, verified := Proof.Hmac.Stream.RISCV64.Sha256.init }
    (hmacInitAnyOut Spec.Hmac.sha256I Proof.Hmac.sha256_local (by decide) _)

/-- `Spec.Hmac.sha256I.finalizeApi`. -/
def sha256FinalizeReg : Registration Spec.Hmac.sha256I.finalizeApi RISCV64.target :=
  withScrub { code := Proof.Hmac.Stream.RISCV64.Sha256Family.hash256.finalize, verified := Proof.Hmac.Stream.RISCV64.Sha256.finalize }
    (hmacFinOut Spec.Hmac.sha256I (by decide) _)

/-- `Spec.Hmac.sha384I.initAnyKeyApi`. -/
def sha384InitAnyKeyReg : Registration Spec.Hmac.sha384I.initAnyKeyApi RISCV64.target :=
  withScrub { code := Proof.Hmac.Stream.RISCV64.Sha384.hash.init, verified := Proof.Hmac.Stream.RISCV64.Sha384.init }
    (hmacInitAnyOut Spec.Hmac.sha384I Proof.Hmac.sha384_local (by decide) _)

/-- `Spec.Hmac.sha384I.finalizeApi`. -/
def sha384FinalizeReg : Registration Spec.Hmac.sha384I.finalizeApi RISCV64.target :=
  withScrub { code := Proof.Hmac.Stream.RISCV64.Sha384.hash.finalize, verified := Proof.Hmac.Stream.RISCV64.Sha384.finalize }
    (hmacFinOut Spec.Hmac.sha384I (by decide) _)

/-- `Spec.Hmac.sha512I.initAnyKeyApi`. -/
def sha512InitAnyKeyReg : Registration Spec.Hmac.sha512I.initAnyKeyApi RISCV64.target :=
  withScrub { code := Proof.Hmac.Stream.RISCV64.Sha512.hash.init, verified := Proof.Hmac.Stream.RISCV64.Sha512.init }
    (hmacInitAnyOut Spec.Hmac.sha512I Proof.Hmac.sha512_local (by decide) _)

/-- `Spec.Hmac.sha512I.finalizeApi`. -/
def sha512FinalizeReg : Registration Spec.Hmac.sha512I.finalizeApi RISCV64.target :=
  withScrub { code := Proof.Hmac.Stream.RISCV64.Sha512.hash.finalize, verified := Proof.Hmac.Stream.RISCV64.Sha512.finalize }
    (hmacFinOut Spec.Hmac.sha512I (by decide) _)

/-- `Spec.Hmac.sha512_224I.initAnyKeyApi`. -/
def sha512_224InitAnyKeyReg : Registration Spec.Hmac.sha512_224I.initAnyKeyApi RISCV64.target :=
  withScrub { code := Proof.Hmac.Stream.RISCV64.Sha512_224.hash.init, verified := Proof.Hmac.Stream.RISCV64.Sha512_224.init }
    (hmacInitAnyOut Spec.Hmac.sha512_224I Proof.Hmac.sha512_224_local (by decide) _)

/-- `Spec.Hmac.sha512_224I.finalizeApi`. -/
def sha512_224FinalizeReg : Registration Spec.Hmac.sha512_224I.finalizeApi RISCV64.target :=
  withScrub { code := Proof.Hmac.Stream.RISCV64.Sha512_224.hash.finalize, verified := Proof.Hmac.Stream.RISCV64.Sha512_224.finalize }
    (hmacFinOut Spec.Hmac.sha512_224I (by decide) _)

/-- `Spec.Hmac.sha512_256I.initAnyKeyApi`. -/
def sha512_256InitAnyKeyReg : Registration Spec.Hmac.sha512_256I.initAnyKeyApi RISCV64.target :=
  withScrub { code := Proof.Hmac.Stream.RISCV64.Sha512_256.hash.init, verified := Proof.Hmac.Stream.RISCV64.Sha512_256.init }
    (hmacInitAnyOut Spec.Hmac.sha512_256I Proof.Hmac.sha512_256_local (by decide) _)

/-- `Spec.Hmac.sha512_256I.finalizeApi`. -/
def sha512_256FinalizeReg : Registration Spec.Hmac.sha512_256I.finalizeApi RISCV64.target :=
  withScrub { code := Proof.Hmac.Stream.RISCV64.Sha512_256.hash.finalize, verified := Proof.Hmac.Stream.RISCV64.Sha512_256.finalize }
    (hmacFinOut Spec.Hmac.sha512_256I (by decide) _)

end VG.Proof.Hmac.Stream.RISCV64.Scrub
