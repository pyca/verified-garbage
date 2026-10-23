module

public import VerifiedGarbage.Spec.Hmac.Generic
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Framework.OmegaLit

/-!
# Streaming states that represent whole blocks, moved

A streaming state that represents a message of whole blocks has an empty
buffer: it represents the message wherever its hash value is, whatever
follows it. HMAC's code over any streaming hash function relies on it: a
state representing the empty message or a block is not changed by writes to
its buffer, and copying the outer state's hash value over the inner one's
makes the inner state represent the outer block.
-/

@[expose] public section

namespace VG.Proof.Hmac.Stream

open VG.Proof.Hmac.Generic.Common (readW_reloc)

theorem md5_reloc (m m' : Mem) (p q : Addr) (msg : List Byte) (hl : msg.length % 64 = 0)
    (h : ∀ i < 16, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i))
    (hr : Spec.Md5.Repr m p msg) : Spec.Md5.Repr m' q msg := by
  refine ⟨?_, ?_⟩
  · rw [← hr.1]
    apply Vector.ext
    intro j hj
    simp only [Spec.Md5.stateAt, Vector.getElem_ofFn]
    exact readW_reloc h (by omega_nat)
  · rw [hl, ← hr.2, hl]; rfl

theorem sha1_reloc (m m' : Mem) (p q : Addr) (msg : List Byte) (hl : msg.length % 64 = 0)
    (h : ∀ i < 20, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i))
    (hr : Spec.Sha1.Repr m p msg) : Spec.Sha1.Repr m' q msg := by
  refine ⟨?_, ?_⟩
  · rw [← hr.1]
    apply Vector.ext
    intro j hj
    simp only [Spec.Sha1.stateAt, Vector.getElem_ofFn]
    exact readW_reloc h (by omega_nat)
  · rw [hl, ← hr.2, hl]; rfl

theorem sha512_reloc (iv : Spec.Sha512.HashValue) (m m' : Mem) (p q : Addr) (msg : List Byte)
    (hl : msg.length % 128 = 0)
    (h : ∀ i < 64, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i))
    (hr : Spec.Sha512.Repr iv m p msg) : Spec.Sha512.Repr iv m' q msg := by
  refine ⟨?_, ?_⟩
  · rw [← hr.1]
    apply Vector.ext
    intro j hj
    simp only [Spec.Sha512.stateAt, Vector.getElem_ofFn]
    exact readW_reloc h (by omega_nat)
  · rw [hl, ← hr.2, hl]; rfl

theorem sha256_reloc (iv : Spec.Sha256.HashValue) (m m' : Mem) (p q : Addr) (msg : List Byte)
    (hl : msg.length % 64 = 0)
    (h : ∀ i < 32, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i))
    (hr : Spec.Sha256.ReprFrom iv m p msg) : Spec.Sha256.ReprFrom iv m' q msg := by
  refine ⟨?_, ?_⟩
  · rw [← hr.1]
    apply Vector.ext
    intro j hj
    simp only [Spec.Sha256.stateAt, Vector.getElem_ofFn]
    exact readW_reloc h (by omega_nat)
  · rw [hl, ← hr.2, hl]; rfl

end VG.Proof.Hmac.Stream
