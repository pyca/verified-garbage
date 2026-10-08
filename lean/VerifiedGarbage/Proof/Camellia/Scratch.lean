import VerifiedGarbage.Spec.Camellia.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Scratch

/-!
# Camellia with its working space as an argument

`vg_camellia_expand_key` and the ECB functions keep their working space in a
frame of their own, which they zero before returning
(`Verified.stackScratchWiped`), around code proved with the working space as
a last argument: `expandKeyScratchContract n` and `ecbScratchContract n` are
the shared contracts with a `scratch` buffer of `n` words appended, whatever
it holds (each target lays out its own).

The frame zeroes the buffer after the code, which needs the postconditions
to read the memory on return only within the function's buffers
(`expandKeyPostOut_local`, `ecbPostOut_local`).
-/

namespace VG.Proof.Camellia

open VG.Spec.Camellia

/-- `vg_camellia_expand_key` with `scratch: *mut [u64; n]`. -/
def expandKeyScratchSig (n : Nat) : Sig where
  params := expandKeySig.params ++ [("scratch", .array true .u64 n)]

/-- `expandKeyContract`, whatever `scratch` is. -/
def expandKeyScratchContract {M : ISA} (A : Abi M) (n : Nat) (stack : Nat := 0) : Contract M :=
  (expandKeyScratchSig n).contract A
    (pre := fun key keyLen schedule _scratch => expandKeyPre A.ptrBits key keyLen schedule)
    (post := fun key keyLen schedule _scratch => expandKeyPost A.ptrBits key keyLen schedule)
    (stack := stack)

theorem expandKeyScratchContract_eq {M : ISA} (A : Abi M) (n stack : Nat) :
    expandKeyScratchContract A n stack = Sig.scratchContract A expandKeySig "scratch" .u64 n
      (expandKeyPre A.ptrBits) (expandKeyPost A.ptrBits) false stack := rfl

/-- The ECB functions with `scratch: *mut [u64; n]`. -/
def ecbScratchSig (n : Nat) : Sig where
  params := ecbSig.params ++ [("scratch", .array true .u64 n)]

/-- `ecbContract`, whatever `scratch` is. -/
def ecbScratchContract {M : ISA} (A : Abi M) (direction : Direction) (n : Nat) (stack : Nat := 0) :
    Contract M :=
  (ecbScratchSig n).contract A
    (pre := fun schedule rounds data n _scratch => ecbPre A.ptrBits schedule rounds data n)
    (post := fun schedule rounds data n _scratch => ecbPost direction A.ptrBits schedule rounds data n)
    (stack := stack)

theorem ecbScratchContract_eq {M : ISA} (A : Abi M) (direction : Direction) (n stack : Nat) :
    ecbScratchContract A direction n stack = Sig.scratchContract A ecbSig "scratch" .u64 n
      (ecbPre A.ptrBits) (ecbPost direction A.ptrBits) false stack := rfl

/-! ## Locality -/

theorem bytesAt_congr {m₁ m₂ : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    bytesAt m₂ p n = bytesAt m₁ p n := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

theorem blocksAt_congr {m₁ m₂ : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < 16 * n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    blocksAt m₂ p n = blocksAt m₁ p n := by
  simp only [blocksAt, blockAt]
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  congr 1
  funext j
  have : 16 * i + j.val < 16 * n := by have := j.isLt; omega
  rw [Offset.add_add]
  exact h _ this

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

theorem scheduleLength_rounds_le (k : Nat) : scheduleLength (rounds k) ≤ 34 := by
  simp only [scheduleLength, rounds]; split <;> omega

variable (pb : Nat)

theorem expandKeyPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (expandKeySig.words pb).length →
    (∀ b ∈ Sig.bufs expandKeySig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (expandKeySig.words pb) (expandKeyPost pb) vs m m₁ r →
      Curry.apply (expandKeySig.words pb) (expandKeyPost pb) vs m m₂ r
  | [_, kl, sch], m, m₁, m₂, r, _, hb, h => by
    simp only [expandKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hs := agree_of hb.2
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr] (expandKeyPost pb) _ m m₁ r at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr] (expandKeyPost pb) _ m m₂ r
    dsimp only [Curry.apply, expandKeyPost, ArgWord.ofRaw] at h ⊢
    intro hk
    rw [bytesAt_congr fun i hi => hs i (by
      have := scheduleLength_rounds_le (kl.setWidth pb).toNat
      omega)]
    exact h hk

theorem ecbPostOut_local (direction : Direction) : ∀ vs m m₁ m₂ r,
    vs.length = (ecbSig.words pb).length →
    (∀ b ∈ Sig.bufs ecbSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (ecbSig.words pb) (ecbPost direction pb) vs m m₁ r →
      Curry.apply (ecbSig.words pb) (ecbPost direction pb) vs m m₂ r
  | [_, _, data, n], m, m₁, m₂, r, _, hb, h => by
    simp only [ecbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hd := agree_of hb.2
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
      (ecbPost direction pb) _ m m₁ r at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
      (ecbPost direction pb) _ m m₂ r
    dsimp only [Curry.apply, ecbPost, ArgWord.ofRaw] at h ⊢
    have := Nat.mod_le n.toNat (2 ^ pb)
    intro hR
    rw [blocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by
      rw [BitVec.toNat_setWidth] at hi; omega)]
    exact h hR

end VG.Proof.Camellia
