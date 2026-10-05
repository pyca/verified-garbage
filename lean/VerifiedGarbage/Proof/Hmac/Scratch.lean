import VerifiedGarbage.Spec.Hmac.Generic
import VerifiedGarbage.Proof.Md5.Stream
import VerifiedGarbage.Proof.Sha1.Scratch
import VerifiedGarbage.Proof.Sha256.Scratch
import VerifiedGarbage.Proof.Sha512.Scratch
import VerifiedGarbage.Proof.Framework.Offset

/-!
# HMAC's postconditions read memory only within the buffers

`init` and `finalize` keep their working space in a frame of their own
(`Verified.stackScratch`); on x86 and ARMv7, where the frame also holds a
copy of the arguments passed on the stack, that needs their pre- and
postconditions to read the memory on entry only within the function's
buffers: the key (`initPost_local`), and the two streaming states, through
the hash function's `Repr` (`finalizePost_local`, for a hash function whose
`Repr` depends only on its state's bytes: `ReprLocal`, which each instance's
hash function has).
-/

namespace VG.Proof.Hmac

open VG.Spec.Hmac

/-- The streaming states of `S` represent a message by their bytes alone. -/
def ReprLocal (S : StreamingHash) : Prop :=
  ∀ {m₁ m₂ : Mem} {p : Addr} {msg : List Byte},
    (∀ i < S.stateBytes, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) →
    S.Repr m₁ p msg → S.Repr m₂ p msg

theorem md5_local : ReprLocal md5S := fun h hr => Md5.Stream.repr_congr h hr
theorem sha1_local : ReprLocal sha1S := fun h hr => Sha1.Stream.repr_congr h hr
theorem sha256_local : ReprLocal sha256S := fun h hr => Sha256.Stream.repr_congr h hr
theorem sha224_local : ReprLocal sha224S := fun h hr => Sha256.reprFrom_congr h hr
theorem sha384_local : ReprLocal sha384S := fun h hr => Sha512.Stream.repr_congr h hr
theorem sha512_local : ReprLocal sha512S := fun h hr => Sha512.Stream.repr_congr h hr
theorem sha512_224_local : ReprLocal sha512_224S := fun h hr => Sha512.Stream.repr_congr h hr
theorem sha512_256_local : ReprLocal sha512_256S := fun h hr => Sha512.Stream.repr_congr h hr

variable (S : StreamingHash) (pb : Nat)

theorem initPre_local : ∀ vs m₁ m₂, vs.length = ((VG.Spec.Hmac.initSig S).words pb).length →
    (∀ b ∈ Sig.bufs (VG.Spec.Hmac.initSig S).params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply ((VG.Spec.Hmac.initSig S).words pb) (initPre S pb) vs m₁ →
      Curry.apply ((VG.Spec.Hmac.initSig S).words pb) (initPre S pb) vs m₂
  | [_, _, _, _], _, _, _, _, h => h

theorem initPost_local : ∀ vs m₁ m₂ m' r, vs.length = ((VG.Spec.Hmac.initSig S).words pb).length →
    (∀ b ∈ Sig.bufs (VG.Spec.Hmac.initSig S).params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply ((VG.Spec.Hmac.initSig S).words pb) (initPost S pb) vs m₁ m' r →
      Curry.apply ((VG.Spec.Hmac.initSig S).words pb) (initPost S pb) vs m₂ m' r
  | [_, _, key, kl], m₁, m₂, m', r, _, hb, h => by
    simp only [VG.Spec.Hmac.initSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    have hk : ∀ i < (kl.setWidth pb).toNat, m₂ (key + BitVec.ofNat 64 i) = m₁ (key + BitVec.ofNat 64 i) :=
      fun i hi => by
        have := Nat.mod_le kl.toNat (2 ^ pb)
        have := kl.isLt
        rw [BitVec.toNat_setWidth] at hi
        exact (hb.2.2 _ (Offset.contains_base _ (by simp only [Elem.size]; omega) (by omega))).symm
    change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (initPost S pb) _ m₁ m' r
      at h
    change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (initPost S pb) _ m₂ m' r
    dsimp only [Curry.apply, initPost] at h ⊢
    rw [show Spec.Sha256.bytesAt m₂ (ArgWord.addr.ofRaw key) ((ArgWord.int pb).ofRaw kl).toNat =
      Spec.Sha256.bytesAt m₁ key (kl.setWidth pb).toNat from Sha256.Stream.bytesAt_congr hk]
    exact h

theorem finalizePost_local (hR : ReprLocal S) (hS : S.stateBytes < 2 ^ 64) : ∀ vs m₁ m₂ m' r,
    vs.length = ((VG.Spec.Hmac.finalizeSig S).words pb).length →
    (∀ b ∈ Sig.bufs (VG.Spec.Hmac.finalizeSig S).params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply ((VG.Spec.Hmac.finalizeSig S).words pb) (VG.Spec.Hmac.finalizePost S pb) vs m₁ m' r →
      Curry.apply ((VG.Spec.Hmac.finalizeSig S).words pb) (VG.Spec.Hmac.finalizePost S pb) vs m₂ m' r
  | [inn, out, _, _], m₁, m₂, m', r, _, hb, h => by
    simp only [VG.Spec.Hmac.finalizeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hs : ∀ (p : Addr), (∀ a, Region.Contains ⟨p, S.stateBytes⟩ a 1 → m₁ a = m₂ a) →
        ∀ i < S.stateBytes, m₁ (p + BitVec.ofNat 64 i) = m₂ (p + BitVec.ofNat 64 i) :=
      fun p hp i hi => hp _ (Offset.contains_base _ (by omega) (by omega))
    intro k0 text h1 h2 hri hc hro
    exact h k0 text h1 h2 (hR (hs _ hb.1) hri) hc (hR (hs _ hb.2.1) hro)

end VG.Proof.Hmac
