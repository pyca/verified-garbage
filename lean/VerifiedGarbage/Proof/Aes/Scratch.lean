import VerifiedGarbage.Spec.Aes.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Scratch
import VerifiedGarbage.Proof.Framework.Contract

/-!
# The AES key expansion with its working space as an argument

`vg_aes_expand_key` keeps its working space in a frame of its own
(`Verified.stackScratchWiped`, `Verified.regScratchWiped`), around the code
of `vg_aes_expand_key_scratch`, proved against
`Spec.Aes.expandKeyScratchContract`: that contract gives the frame's, the
shared contract with the `scratch` buffer appended, whatever it holds
(`expandKey_scratch`).

The frames zero the working space before returning, which needs the
postcondition to read the memory on return only within the function's
buffers (`expandKeyPostOut_local`): the key schedule, of at most 240 bytes
for the key lengths the precondition allows. On x86 the frame also holds a
copy of the arguments passed on the stack, which needs the pre- and
postcondition to read the memory on entry only within the buffers too
(`expandKeyPre_local`, `expandKeyPost_local`): the key.
-/

namespace VG.Proof.Aes

open VG.Spec.Aes

/-- The code proved against `expandKeyScratchContract` meets the contract the
frames take: the same signature and precondition, and a postcondition that
holds whenever the precondition does. -/
theorem expandKey_scratch {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (expandKeyScratchContract A stack)) :
    Verified T c (Sig.scratchContract A expandKeySig "scratch" .u64 64 (expandKeyPre A.ptrBits)
      (expandKeyPost A.ptrBits) false stack) := by
  refine Verified.of_implies h ⟨fun _ hs => hs, fun s s' _ hp => ?_, fun _ _ _ _ hp => hp, h.2.2⟩
  change (expandKeyScratchSig.contract A
    (pre := fun key keyLen schedule _scratch => expandKeyPre A.ptrBits key keyLen schedule)
    (post := fun key keyLen schedule _scratch => expandKeyPost A.ptrBits key keyLen schedule)
    (stack := stack)).post s s'
  revert hp
  simp only [expandKeyScratchContract, Sig.contract]
  split
  · exact id
  · rename_i vals _
    generalize vals s = vs
    rcases vs with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, vs⟩⟩⟩⟩ <;>
      exact fun hp _ => hp

/-! ## Locality -/

section

variable {m₁ m₂ : Mem} {p : Addr}

private theorem bytesAt_congr {n : Nat}
    (h : ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    bytesAt m₂ p n = bytesAt m₁ p n := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-- The memory agrees on the `n` bytes at `p`, from its agreeing on the
region. -/
private theorem agree_of {n : Nat} (h : ∀ a, Region.Contains ⟨p, n⟩ a 1 → m₁ a = m₂ a) :
    ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := by
  intro i hi
  refine (h _ ?_).symm
  by_cases hw : i < 2 ^ 64
  · exact Offset.contains_base _ (by omega) hw
  · simp only [Region.Contains]
    have := (p + BitVec.ofNat 64 i - p).isLt
    omega

end

variable (pb : Nat)

theorem expandKeyPre_local : ∀ vs m₁ m₂, vs.length = (expandKeySig.words pb).length →
    (∀ b ∈ Sig.bufs expandKeySig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (expandKeySig.words pb) (expandKeyPre pb) vs m₁ →
      Curry.apply (expandKeySig.words pb) (expandKeyPre pb) vs m₂
  | [_, _, _], _, _, _, _, h => h

theorem expandKeyPost_local : ∀ vs m₁ m₂ m' r, vs.length = (expandKeySig.words pb).length →
    (∀ b ∈ Sig.bufs expandKeySig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (expandKeySig.words pb) (expandKeyPost pb) vs m₁ m' r →
      Curry.apply (expandKeySig.words pb) (expandKeyPost pb) vs m₂ m' r
  | [key, kl, _], m₁, m₂, m', r, _, hb, h => by
    simp only [expandKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hk := agree_of hb.1
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr] (expandKeyPost pb) _ m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr] (expandKeyPost pb) _ m₂ m' r
    dsimp only [Curry.apply, expandKeyPost, ArgWord.ofRaw] at h ⊢
    have := Nat.mod_le kl.toNat (2 ^ pb)
    rw [bytesAt_congr (n := (kl.setWidth pb).toNat) fun i hi => hk i (by
      rw [BitVec.toNat_setWidth] at hi; omega)]
    exact h

theorem expandKeyPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (expandKeySig.words pb).length →
    (∀ b ∈ Sig.bufs expandKeySig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (expandKeySig.words pb) (expandKeyPost pb) vs m m₁ r →
      Curry.apply (expandKeySig.words pb) (expandKeyPost pb) vs m m₂ r
  | [_, _, sch], m, m₁, m₂, r, _, hb, h => by
    simp only [expandKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hs := agree_of hb.2
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr] (expandKeyPost pb) _ m m₁ r at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr] (expandKeyPost pb) _ m m₂ r
    dsimp only [Curry.apply, expandKeyPost, ArgWord.ofRaw] at h ⊢
    intro hk
    rw [bytesAt_congr fun i hi => hs i (by simp only [rounds] at hi; omega)]
    exact h hk

end VG.Proof.Aes
