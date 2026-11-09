module

public import VerifiedGarbage.Spec.Sha256.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Sha256.Stream

-- separate module: target-independent, for every target whose digest keeps its working space in a wiped frame

/-!
# The one-shot digests' postcondition reads memory only within the buffers

On the targets where `vg_<hash>_digest` keeps its working space in a frame of
its own, which it zeroes before returning (`Verified.stackScratchWiped` and
its counterparts), the frame needs the postcondition to read the memory on
entry only within the data (`digestPost_local`), and the memory on return
only within `out` (`digestPostOut_local`). SHA-1's, SHA-256's and SHA-512's
`digestPost` are all `Spec.Sha256.digestPost` for their digest's size and
function.
-/

@[expose] public section

namespace VG.Proof.MdStream.Digest

open VG.Spec.Sha256 (digestSig digestPost bytesAt)

/-- The memory agrees on the `n` bytes at `p`, from its agreeing on the
region. -/
theorem agree_of {m₁ m₂ : Mem} {p : Addr} {n : Nat}
    (h : ∀ a, Region.Contains ⟨p, n⟩ a 1 → m₁ a = m₂ a) :
    ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := by
  intro i hi
  refine (h _ ?_).symm
  by_cases hw : i < 2 ^ 64
  · exact Offset.contains_base _ (by omega) hw
  · simp only [Region.Contains]
    have := (p + BitVec.ofNat 64 i - p).isLt
    omega

variable (D : Nat) (digest : List Byte → List Byte) (pb : Nat)

theorem digestPost_local : ∀ vs m₁ m₂ m' r, vs.length = ((digestSig D).words pb).length →
    (∀ b ∈ Sig.bufs (digestSig D).params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply ((digestSig D).words pb) (digestPost D digest pb) vs m₁ m' r →
      Curry.apply ((digestSig D).words pb) (digestPost D digest pb) vs m₂ m' r
  | [data, len, _], m₁, m₂, m', r, _, hb, h => by
    simp only [digestSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hd := agree_of hb.1
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr] (digestPost D digest pb) _ m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr] (digestPost D digest pb) _ m₂ m' r
    dsimp only [Curry.apply, digestPost, ArgWord.ofRaw] at h ⊢
    have := Nat.mod_le len.toNat (2 ^ pb)
    rw [Proof.Sha256.Stream.bytesAt_congr (n := (len.setWidth pb).toNat) fun i hi =>
      hd i (by rw [BitVec.toNat_setWidth] at hi; omega)]
    exact h

theorem digestPostOut_local : ∀ vs m m₁ m₂ r, vs.length = ((digestSig D).words pb).length →
    (∀ b ∈ Sig.bufs (digestSig D).params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply ((digestSig D).words pb) (digestPost D digest pb) vs m m₁ r →
      Curry.apply ((digestSig D).words pb) (digestPost D digest pb) vs m m₂ r
  | [_, _, out], m, m₁, m₂, r, _, hb, h => by
    simp only [digestSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have ho := agree_of hb.2
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr] (digestPost D digest pb) _ m m₁ r at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr] (digestPost D digest pb) _ m m₂ r
    dsimp only [Curry.apply, digestPost, ArgWord.ofRaw] at h ⊢
    rw [Proof.Sha256.Stream.bytesAt_congr ho]
    exact h

end VG.Proof.MdStream.Digest
