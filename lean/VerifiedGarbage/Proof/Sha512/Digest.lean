import VerifiedGarbage.Proof.Sha512.Md
import VerifiedGarbage.Proof.Sha512.Word64
import VerifiedGarbage.Spec.Sha512.Contract
import VerifiedGarbage.Proof.Sha512.Stream
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The truncated digests of the SHA-512 family, from the hash value in memory

The final hash value is stored as eight little-endian 64-bit words, and its
output (`md.digest`) is all of them, big-endian. The digests of SHA-384 and
SHA-512/256 are its first 48 and 32 bytes, the first 6 and 4 words
(`digest_take`); that of SHA-512/224 its first 28 bytes, the first 3 words
and the high half of the fourth (`digest_take28`). Every target's
`finalize` of those digests writes them so.
-/

namespace VG.Proof.Sha512

open VG.Proof.MdStream (bytes32 bytes64)

/-- A region holding `n` bytes at `a` holds the first `m` of them. -/
theorem inRegions_prefix {rs : List Region} {a : Addr} {n m : Nat} (h : InRegions rs a n) (hm : m ≤ n) :
    InRegions rs a m := by
  obtain ⟨R, hR, hc⟩ := h
  exact ⟨R, hR, by unfold Region.Contains at *; omega⟩

/-- The output of the hash value at `p`: its words, big-endian. -/
theorem digest_words (mem : Mem) (p : Addr) :
    md.digest (md.stateAt mem p) = (List.range 8).flatMap fun k =>
      bytes64 true (mem.readW (p + BitVec.ofNat 64 (8 * k)) 64) := by
  simp [md, Spec.Sha512.stateAt, Vector.toList_ofFn, List.range_succ, List.ofFn_succ, bytes64,
    Spec.Sha512.wordBytes]

theorem length_flatMap_range {α : Type} (f : Nat → List α) {w : Nat} (hf : ∀ k, (f k).length = w) (n : Nat) :
    ((List.range n).flatMap f).length = w * n := by
  rw [List.length_flatMap, List.map_congr_left (fun x _ => hf x), List.map_const', List.sum_replicate_nat,
    List.length_range, Nat.mul_comm]

/-- The first `w · n` elements of the lists `f k`, each of `w` elements, for
`k < m`, are those for `k < n`. -/
theorem take_flatMap_range {α : Type} (f : Nat → List α) {w : Nat} (hf : ∀ k, (f k).length = w) {n m : Nat}
    (h : n ≤ m) : ((List.range m).flatMap f).take (w * n) = (List.range n).flatMap f := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.range_add, List.flatMap_append, List.take_append_of_le_length (by rw [length_flatMap_range f hf]),
    List.take_of_length_le (by rw [length_flatMap_range f hf])]

/-- The first `n` words of the hash value at `p`, big-endian. -/
theorem digest_take (mem : Mem) (p : Addr) {n : Nat} (hn : n ≤ 8) :
    (md.digest (md.stateAt mem p)).take (8 * n) = (List.range n).flatMap fun k =>
      bytes64 true (mem.readW (p + BitVec.ofNat 64 (8 * k)) 64) := by
  rw [digest_words]
  exact take_flatMap_range _ (fun _ => by simp [bytes64]) hn

/-- The big-endian bytes of a 64-bit word are those of its high half, then
those of its low half. -/
theorem bytes64_hi_lo (hi lo : BitVec 32) : bytes64 true (hi ++ lo) = bytes32 true hi ++ bytes32 true lo := by
  simp only [bytes64, bytes32, ite_true, List.range_succ, List.range_zero, List.nil_append, List.reverse_cons,
    List.reverse_nil, List.map_cons, List.map_nil, List.cons_append, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · ext i hi
    simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_append]
    split <;> first | omega | (congr 1; omega) | rfl

/-- The first 28 bytes of the hash value at `p`: its first 3 words, then the
high half of the fourth, big-endian. -/
theorem digest_take28 (mem : Mem) (p : Addr) :
    (md.digest (md.stateAt mem p)).take 28 = (List.range 3).flatMap (fun k =>
      bytes64 true (mem.readW (p + BitVec.ofNat 64 (8 * k)) 64)) ++
        bytes32 true (mem.readW (p + BitVec.ofNat 64 28) 32) := by
  have h4 := digest_take mem p (n := 4) (by decide)
  have e3 : bytes64 true (mem.readW (p + BitVec.ofNat 64 (8 * 3)) 64) =
      bytes32 true (mem.readW (p + BitVec.ofNat 64 28) 32) ++
        bytes32 true (mem.readW (p + BitVec.ofNat 64 24) 32) := by
    rw [Word64.readW64, bytes64_hi_lo, BitVec.add_assoc]; rfl
  have hl : ((List.range 3).flatMap fun k => bytes64 true (mem.readW (p + BitVec.ofNat 64 (8 * k)) 64)).length =
      24 := length_flatMap_range _ (w := 8) (fun _ => by simp [bytes64]) 3
  have ht : (md.digest (md.stateAt mem p)).take 28 = ((md.digest (md.stateAt mem p)).take (8 * 4)).take 28 := by
    rw [List.take_take]; rfl
  rw [ht, h4, List.range_succ, List.flatMap_append, List.flatMap_singleton, List.take_append, hl,
    List.take_of_length_le (by omega), e3, List.take_append_of_le_length (by simp [bytes32]),
    List.take_of_length_le (by simp [bytes32])]

/-! ## In 32-bit halves

32-bit targets write each word as its high half, then its low half. -/

/-- Word `k` of the hash value at `p`, big-endian: its high half, then its low
half. -/
theorem word_halves (mem : Mem) (p : Addr) (k : Nat) :
    bytes64 true (mem.readW (p + BitVec.ofNat 64 (8 * k)) 64) =
      bytes32 true (mem.readW (p + BitVec.ofNat 64 (8 * k + 4)) 32) ++
        bytes32 true (mem.readW (p + BitVec.ofNat 64 (8 * k)) 32) := by
  rw [Word64.readW64, bytes64_hi_lo, BitVec.add_assoc,
    show BitVec.ofNat 64 (8 * k) + 4 = BitVec.ofNat 64 (8 * k + 4) from (BitVec.ofNat_add _ _).symm]

/-- The first `n` words of the hash value at `p`, big-endian, in halves. -/
theorem digest_take_halves (mem : Mem) (p : Addr) {n : Nat} (hn : n ≤ 8) :
    (md.digest (md.stateAt mem p)).take (8 * n) = (List.range n).flatMap fun k =>
      bytes32 true (mem.readW (p + BitVec.ofNat 64 (8 * k + 4)) 32) ++
        bytes32 true (mem.readW (p + BitVec.ofNat 64 (8 * k)) 32) := by
  rw [digest_take mem p hn]
  simp only [word_halves]

/-- The first 28 bytes of the hash value at `p`, in halves. -/
theorem digest_take28_halves (mem : Mem) (p : Addr) :
    (md.digest (md.stateAt mem p)).take 28 = ((List.range 3).flatMap fun k =>
      bytes32 true (mem.readW (p + BitVec.ofNat 64 (8 * k + 4)) 32) ++
        bytes32 true (mem.readW (p + BitVec.ofNat 64 (8 * k)) 32)) ++
      bytes32 true (mem.readW (p + BitVec.ofNat 64 28) 32) := by
  rw [digest_take28 mem p]
  simp only [word_halves]

/-! ## The contract with the working space as an argument

Each target's `finalize` of the truncated digests takes its working space in
`scratch`, as `Spec.Sha512.finalizeScratchSig` does, and is emitted in a frame
of its own allocating it (`Verified.stackScratch`): it is verified against
this contract first. -/

/-- `vg_<alg>_finalize` with its working space in `scratch`
(`Spec.Sha512.finalizeDigestSig` and the scratch of
`Spec.Sha512.finalizeScratchSig`). -/
def finalizeDigestScratchSig (D : Nat) : Sig where
  params := [("state", .array true .u8 192), ("count", .int .u64 true),
    ("out", .array true .u8 D), ("scratch", .array true .u64 172)]

/-- `Spec.Sha512.finalizeDigestPost`, whatever `scratch` is. -/
def finalizeDigestScratchContract {M : ISA} (A : Abi M) (iv : Spec.Sha512.HashValue) (D : Nat)
    (digest : List Byte → List Byte) (stack : Nat) : Contract M :=
  (finalizeDigestScratchSig D).contract A (post := fun state count out _scratch =>
    Spec.Sha512.finalizeDigestPost iv D digest A.ptrBits state count out) (stack := stack)

/-- `finalizeDigestPost` reads the memory on entry only within the streaming
state (see `finalizePost_local`). -/
theorem finalizeDigestPost_local (iv : Spec.Sha512.HashValue) (D : Nat) (digest : List Byte → List Byte)
    (pb : Nat) : ∀ vs m₁ m₂ m' r, vs.length = ((Spec.Sha512.finalizeDigestSig D).words pb).length →
      (∀ b ∈ Sig.bufs (Spec.Sha512.finalizeDigestSig D).params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply ((Spec.Sha512.finalizeDigestSig D).words pb) (Spec.Sha512.finalizeDigestPost iv D digest pb)
        vs m₁ m' r →
      Curry.apply ((Spec.Sha512.finalizeDigestSig D).words pb) (Spec.Sha512.finalizeDigestPost iv D digest pb)
        vs m₂ m' r
  | [st, ct, ot], m₁, m₂, m', r, _, hb, h => by
    simp only [Spec.Sha512.finalizeDigestSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hb
    have hs : ∀ i < 192, m₂ (st + BitVec.ofNat 64 i) = m₁ (st + BitVec.ofNat 64 i) := fun i hi =>
      (hb.1 _ (Offset.contains_base _ (by simp only [Elem.size]; omega) (by omega))).symm
    intro msg hr hl hc
    exact h msg (Stream.repr_congr (fun i hi => (hs i hi).symm) hr) hl hc

end VG.Proof.Sha512
