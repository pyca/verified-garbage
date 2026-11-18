module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Md5
public import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Sha1
public import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Sha224
public import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Sha256
public import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Sha384
public import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Sha512
public import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Sha512_224
public import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Sha512_256
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# PBKDF2 on RISC-V, without secret residue

Each hash's PBKDF2, followed by `Impl.Scrub.RISCV64.scrubTail`
(`RISCV64.Scrub.withScrub`). Its postcondition reads the memory on return
only within `out`, as on x86-64 (`Proof/Pbkdf2/Md/X86_64/ScrubAll.lean`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.RISCV64.Scrub

open VG.RISCV64 VG.RISCV64.Scrub

/-- PBKDF2's postcondition reads the memory on return only within `out`, the
derived key's bytes. -/
theorem pbkdf2Out (I : Spec.Hmac.Instance) (stack : Nat) :
    PostOut (I.pbkdf2Contract abi stack) (Spec.Pbkdf2.pbkdf2Sig.retBits 64) := by
  unfold Spec.Hmac.Instance.pbkdf2Contract Spec.Pbkdf2.pbkdf2Contract
  exact postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨pw, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 6) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨pwLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨salt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨saltLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨c, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨out, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨outLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [Spec.Pbkdf2.pbkdf2Sig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    have ho : ∀ i < outLen.toNat, m₂ (out + BitVec.ofNat 64 i) = m₁ (out + BitVec.ofNat 64 i) :=
      fun i hi => (hb.2.2 _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi]))).symm
    change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.int 32,
      ArgWord.addr, ArgWord.int 64] (Spec.Pbkdf2.pbkdf2Post I.S 64) _ m m₁ r at h
    change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.int 32,
      ArgWord.addr, ArgWord.int 64] (Spec.Pbkdf2.pbkdf2Post I.S 64) _ m m₂ r
    dsimp only [Curry.apply, Spec.Pbkdf2.pbkdf2Post, ArgWord.ofRaw] at h ⊢
    rw [Sha256.Stream.bytesAt_congr fun i hi => ho i (by
      rw [BitVec.toNat_setWidth] at hi; have := Nat.mod_le outLen.toNat (2 ^ 64); omega_using [hi])]
    exact h

/-- `Spec.Hmac.md5I.pbkdf2Api`. -/
def md5Pbkdf2Reg : Registration Spec.Hmac.md5I.pbkdf2Api RISCV64.target :=
  withScrub { code := Proof.Pbkdf2.Whole.RISCV64.Md5.F.pbkdf2, verified := Proof.Pbkdf2.Whole.RISCV64.Md5.pbkdf2 }
    (pbkdf2Out Spec.Hmac.md5I _)

/-- `Spec.Hmac.sha1I.pbkdf2Api`. -/
def sha1Pbkdf2Reg : Registration Spec.Hmac.sha1I.pbkdf2Api RISCV64.target :=
  withScrub { code := Proof.Pbkdf2.Whole.RISCV64.Sha1.F.pbkdf2, verified := Proof.Pbkdf2.Whole.RISCV64.Sha1.pbkdf2 }
    (pbkdf2Out Spec.Hmac.sha1I _)

/-- `Spec.Hmac.sha224I.pbkdf2Api`. -/
def sha224Pbkdf2Reg : Registration Spec.Hmac.sha224I.pbkdf2Api RISCV64.target :=
  withScrub { code := Proof.Pbkdf2.Whole.RISCV64.Sha224.F.pbkdf2, verified := Proof.Pbkdf2.Whole.RISCV64.Sha224.pbkdf2 }
    (pbkdf2Out Spec.Hmac.sha224I _)

/-- `Spec.Hmac.sha256I.pbkdf2Api`. -/
def sha256Pbkdf2Reg : Registration Spec.Hmac.sha256I.pbkdf2Api RISCV64.target :=
  withScrub { code := Proof.Pbkdf2.Whole.RISCV64.Sha256.F.pbkdf2, verified := Proof.Pbkdf2.Whole.RISCV64.Sha256.pbkdf2 }
    (pbkdf2Out Spec.Hmac.sha256I _)

/-- `Spec.Hmac.sha384I.pbkdf2Api`. -/
def sha384Pbkdf2Reg : Registration Spec.Hmac.sha384I.pbkdf2Api RISCV64.target :=
  withScrub { code := Proof.Pbkdf2.Whole.RISCV64.Sha384.F.pbkdf2, verified := Proof.Pbkdf2.Whole.RISCV64.Sha384.pbkdf2 }
    (pbkdf2Out Spec.Hmac.sha384I _)

/-- `Spec.Hmac.sha512I.pbkdf2Api`. -/
def sha512Pbkdf2Reg : Registration Spec.Hmac.sha512I.pbkdf2Api RISCV64.target :=
  withScrub { code := Proof.Pbkdf2.Whole.RISCV64.Sha512.F.pbkdf2, verified := Proof.Pbkdf2.Whole.RISCV64.Sha512.pbkdf2 }
    (pbkdf2Out Spec.Hmac.sha512I _)

/-- `Spec.Hmac.sha512_224I.pbkdf2Api`. -/
def sha512_224Pbkdf2Reg : Registration Spec.Hmac.sha512_224I.pbkdf2Api RISCV64.target :=
  withScrub { code := Proof.Pbkdf2.Whole.RISCV64.Sha512_224.F.pbkdf2, verified := Proof.Pbkdf2.Whole.RISCV64.Sha512_224.pbkdf2 }
    (pbkdf2Out Spec.Hmac.sha512_224I _)

/-- `Spec.Hmac.sha512_256I.pbkdf2Api`. -/
def sha512_256Pbkdf2Reg : Registration Spec.Hmac.sha512_256I.pbkdf2Api RISCV64.target :=
  withScrub { code := Proof.Pbkdf2.Whole.RISCV64.Sha512_256.F.pbkdf2, verified := Proof.Pbkdf2.Whole.RISCV64.Sha512_256.pbkdf2 }
    (pbkdf2Out Spec.Hmac.sha512_256I _)

end VG.Proof.Pbkdf2.Whole.RISCV64.Scrub
