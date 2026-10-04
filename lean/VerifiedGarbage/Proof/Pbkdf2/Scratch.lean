import VerifiedGarbage.Spec.Pbkdf2.Generic
import VerifiedGarbage.Proof.Framework.Offset

/-!
# PBKDF2 with its working space on the stack: locality

`vg_pbkdf2_hmac_<hash>` keeps its working space in a frame of its own
(`Verified.stackScratch`, or `Verified.stackArgScratch` on x86-64, where it
was a stack argument), around code proved with the working space as an
argument (`Spec.Pbkdf2.pbkdf2ScratchContract`, which
`vg_pbkdf2_hmac_<hash>_scratch` is emitted with).

On x86-64, x86 and ARMv7 the frame also holds a copy of the arguments passed
on the stack, which needs the pre- and postcondition to read the memory on
entry only within the function's buffers (`pbkdf2Pre_local`,
`pbkdf2Post_local`): the precondition reads none, the postcondition the
password and the salt.
-/

namespace VG.Proof.Pbkdf2

open VG.Spec.Pbkdf2
open VG.Spec.Sha256 (bytesAt)

private theorem bytesAt_congr {m₁ m₂ : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    bytesAt m₂ p n = bytesAt m₁ p n := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-- The memory agrees on the `n` bytes at `p`, from its agreeing on the
region. -/
private theorem agree_of {m₁ m₂ : Mem} {p : Addr} {n : Nat}
    (h : ∀ a, Region.Contains ⟨p, n⟩ a 1 → m₁ a = m₂ a) :
    ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := by
  intro i hi
  refine (h _ ?_).symm
  by_cases hw : i < 2 ^ 64
  · exact Offset.contains_base _ (by omega) hw
  · simp only [Region.Contains]
    have := (p + BitVec.ofNat 64 i - p).isLt
    omega

variable (S : Spec.Hmac.StreamingHash) (pb : Nat)

theorem pbkdf2Pre_local : ∀ vs m₁ m₂, vs.length = (pbkdf2Sig.words pb).length →
    (∀ b ∈ Sig.bufs pbkdf2Sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (pbkdf2Sig.words pb) (pbkdf2Pre S pb) vs m₁ →
      Curry.apply (pbkdf2Sig.words pb) (pbkdf2Pre S pb) vs m₂
  | [_, _, _, _, _, _, _], _, _, _, _, h => h

theorem pbkdf2Post_local : ∀ vs m₁ m₂ m' r, vs.length = (pbkdf2Sig.words pb).length →
    (∀ b ∈ Sig.bufs pbkdf2Sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (pbkdf2Sig.words pb) (pbkdf2Post S pb) vs m₁ m' r →
      Curry.apply (pbkdf2Sig.words pb) (pbkdf2Post S pb) vs m₂ m' r
  | [pw, pwLen, salt, saltLen, c, out, outLen], m₁, m₂, m', r, _, hb, h => by
    simp only [pbkdf2Sig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hp := agree_of hb.1
    have hs := agree_of hb.2.1
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.int 32,
      ArgWord.addr, ArgWord.int pb] (pbkdf2Post S pb) _ m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.int 32,
      ArgWord.addr, ArgWord.int pb] (pbkdf2Post S pb) _ m₂ m' r
    dsimp only [Curry.apply, pbkdf2Post, ArgWord.ofRaw] at h ⊢
    have h₁ := Nat.mod_le pwLen.toNat (2 ^ pb)
    have h₂ := Nat.mod_le saltLen.toNat (2 ^ pb)
    rw [bytesAt_congr (n := (pwLen.setWidth pb).toNat) fun i hi => hp i (by
        rw [BitVec.toNat_setWidth] at hi; omega),
      bytesAt_congr (n := (saltLen.setWidth pb).toNat) fun i hi => hs i (by
        rw [BitVec.toNat_setWidth] at hi; omega)]
    exact h

end VG.Proof.Pbkdf2
