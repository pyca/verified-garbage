module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Context
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeometryHash
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PConstructPlan
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeometryPrime
import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
-- Proofs inside exposed definitions (structure values) use these: Lean needs them public.
public import VerifiedGarbage.Proof.Bignum.Octets -- shake: keep
public import VerifiedGarbage.Proof.Dsa.Encoding -- shake: keep
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PPrimalityPlan
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeometryWork
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchPlan
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ArenaSource

/-! ### `Dsa.AArch64.Generation.GeometryPrimality`, which only this module used -/

section

/-! ### `Dsa.AArch64.Generation.GeometryConstruct`, which only this module used -/

section

/-! # Concrete p-candidate construction plan for each accepted subgroup candidate -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

def GenerationGeometry.constructPlan (p : GenerationGeometry) (seed : GenerationTape p)
    (seedLength : seed.bytes.length = p.qLen) (W : Nat → BitVec 64) (offset : Nat)
    (carry : offset + p.count < 2 ^ 32)
    (h1 : W 1 = seed.ptr) (h3 : W 3 = VG.Proof.Bignum.off p.B wrappedSeed)
    (h4 : W 4 = VG.Proof.Bignum.off p.B hashes) (h2 : W 2 = BitVec.ofNat 64 offset)
    (h5 : W 5 = p.B) (h0 : W 0 = VG.Proof.Bignum.off p.B shaped) : PConstructPlan := by
  let N := Spec.Dsa.qCandidate (8 * p.qLen) seed.bytes
  have qshape := VG.Proof.Dsa.Generation.qCandidate_shape
    (show 2 ≤ 8 * p.qLen by rcases p.qWidth with h | h <;> omega_using [h]) seed.bytes
  have qfit : N < 256 ^ p.qLen := by
    change N < (2 ^ 8) ^ p.qLen
    rw [← Nat.pow_mul]
    exact qshape.2.2
  have qdecode : Spec.Rsa.os2ip (Spec.Dsa.encodeBE p.qLen N) = N := VG.Proof.Dsa.decodeBE_encodeBE qfit
  have ha : arithmetic + arithmeticBytes ≤ usedBytes p.pLen := by
    rcases p.width with h | h | h <;> rw [h] <;> decide
  have hs : shaped + p.pLen ≤ usedBytes p.pLen := by
    rcases p.width with h | h | h <;> rw [h] <;> decide
  have hp : VG.Impl.Dsa.Generation.Layout.p + p.pLen ≤ usedBytes p.pLen := by
    rcases p.width with h | h | h <;> rw [h] <;> decide
  have he : exponent + p.pLen ≤ usedBytes p.pLen := by
    rcases p.width with h | h | h <;> rw [h] <;> decide
  have hq : q + p.qLen ≤ usedBytes p.pLen := by
    rcases p.lengths with ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> rw [h1,h2] <;> decide
  have hh : VG.Impl.Dsa.Generation.Layout.hash + oRsa ≤ usedBytes p.pLen := by
    rcases p.width with h | h | h <;> rw [h] <;> decide
  have hhash : hashes + (p.count + 1) * p.qLen ≤ usedBytes p.pLen := by
    have hn := p.hashSizes.2.1
    rcases p.width with h | h | h <;> rw [h] <;> unfold hashes usedBytes domainCheck <;> omega_using [hn]
  have hw : wrappedSeed + p.qLen ≤ usedBytes p.pLen := by
    rcases p.lengths with ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> rw [h1,h2] <;> decide
  have qn : p.qLen ≤ 32 := by rcases p.qWidth with h | h <;> omega_using [h]
  have pn : p.pLen ≤ 384 := by rcases p.width with h | h | h <;> omega_using [h]
  refine {
    hash := p.hashPlan seed seedLength W offset carry h1 h3 h4 h2
    B := VG.Proof.Bignum.off p.B arithmetic
    Z := arithmeticBytes
    len := p.pLen
    qb := Spec.Dsa.encodeBE p.qLen N
    width := p.width
    base := by change W 5 + _ = _; rw [h5]
    workspaceRoom := by rcases p.width with h | h | h <;> rw [h] <;> decide
    qLength := VG.Proof.Dsa.encodeBE_length _ _
    qPositive := by rw [qdecode]; exact Nat.lt_of_lt_of_le (by decide) (p.qShape seed.bytes).2
    qFits := by
      rw [qdecode]
      apply Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left qfit (by decide : 0 < 2))
      change 2 * (2 ^ 8) ^ p.qLen ≤ 2 ^ (64 * (p.pLen / 8))
      rw [← Nat.pow_mul, ← Nat.pow_succ']
      apply Nat.pow_le_pow_right (by decide)
      rcases p.lengths with ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> rw [h1,h2] <;> decide
    hashCount := rfl
    hashRoom := p.hashSizes.2.2
    shapedSlot := by change W 0 = VG.Proof.Bignum.off (W 5) shaped; rw [h5]; exact h0
    shapedOutside := ?_
    shapedHash := ?_
    shapedInput := ?_
    frameHeaders := p.frame_headers
    frameOutside := p.frame_outside
    qHash := ?_
    pOutside := ?_
    exponentOutside := ?_
    pExponent := ?_
    frameArithmetic := ?_
    hashArithmetic := ?_ }
  · change ∀ i < p.pLen, arithmeticBytes ≤ ofs (VG.Proof.Bignum.off p.B arithmetic) (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) shaped) i)
    rw [h5]
    intro i hi
    exact out_scr (p.parts_disjoint hs ha (Or.inl (by unfold shaped arithmetic; omega_using [pn])))
      (Offset.contains_base _ (by omega_using [hi]) (by omega_using [pn, hi]))
  · change HashBufferSeparate p.F p.hash (VG.Proof.Bignum.off (W 5) shaped) p.pLen
    rw [h5]
    exact bufferSeparate_of_regions (by omega_using [pn]) (p.frame_part hs).symm
      (p.parts_disjoint hs hh (Or.inr (by decide)))
  · change ∀ i < p.pLen, ∀ j < p.pLen,
      VG.Proof.Bignum.off (VG.Proof.Bignum.off (VG.Proof.Bignum.off p.B hashes) ((p.count + 1) * p.qLen - p.pLen)) i ≠ VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) shaped) j
    rw [h5]
    intro i hi j hj eq
    have dis := p.parts_disjoint hhash hs (Or.inl (by
      have := p.hashSizes.2.1; unfold hashes shaped; omega_using [this]))
    apply dis (VG.Proof.Bignum.off (VG.Proof.Bignum.off (VG.Proof.Bignum.off p.B hashes) ((p.count + 1) * p.qLen - p.pLen)) i)
    · rw [VG.Proof.Bignum.off_off]
      exact Offset.contains_base _ (by omega_using [p.hashSizes.2.2, hi]) (by omega_using [p.hashSizes.2.1, p.hashSizes.2.2, hi])
    · rw [eq]
      exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [pn, hj])
  · change ∀ r ∈ ⟨VG.Proof.Bignum.off (W 5) shaped, p.pLen⟩ ::
      [⟨VG.Proof.Bignum.off p.B hashes, (p.count + 1) * p.qLen⟩, ⟨VG.Proof.Bignum.off p.B wrappedSeed, p.qLen⟩, ⟨p.hash, oRsa⟩, retR p.F],
      (⟨VG.Proof.Bignum.off (W 5) q, (Spec.Dsa.encodeBE p.qLen N).length⟩ : Region).Disjoint r
    rw [h5, VG.Proof.Dsa.encodeBE_length]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact p.parts_disjoint hq hs (Or.inr (by unfold shaped q; omega_using [pn]))
    · exact p.parts_disjoint hq hhash (Or.inr (by have := p.hashSizes.2.1; unfold hashes q; omega_using [this]))
    · exact p.parts_disjoint hq hw (Or.inr (by unfold wrappedSeed q; omega_using [qn]))
    · exact p.parts_disjoint hq hh (Or.inr (by decide))
    · exact (p.stack_part hq).symm.sub_right (below_sub (by decide) (by decide))
  · change ∀ i < p.pLen, arithmeticBytes ≤ ofs (VG.Proof.Bignum.off p.B arithmetic) (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) VG.Impl.Dsa.Generation.Layout.p) i)
    rw [h5]
    intro i hi
    exact out_scr (p.parts_disjoint hp ha (Or.inl (by unfold VG.Impl.Dsa.Generation.Layout.p arithmetic; omega_using [pn])))
      (Offset.contains_base _ (by omega_using [hi]) (by omega_using [pn, hi]))
  · change ∀ i < p.pLen, arithmeticBytes ≤ ofs (VG.Proof.Bignum.off p.B arithmetic) (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) exponent) i)
    rw [h5]
    intro i hi
    exact out_scr (p.parts_disjoint he ha (Or.inl (by unfold exponent arithmetic; omega_using [pn])))
      (Offset.contains_base _ (by omega_using [hi]) (by omega_using [pn, hi]))
  · change ∀ i < p.pLen, ∀ j < p.pLen, VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) VG.Impl.Dsa.Generation.Layout.p) i ≠ VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) exponent) j
    rw [h5]
    intro i hi j hj eq
    apply (p.parts_disjoint hp he (Or.inl (by unfold VG.Impl.Dsa.Generation.Layout.p exponent; omega_using [pn]))) (VG.Proof.Bignum.off (VG.Proof.Bignum.off p.B VG.Impl.Dsa.Generation.Layout.p) i)
      (Offset.contains_base _ (by omega_using [hi]) (by omega_using [pn, hi]))
    rw [eq]
    exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [pn, hj])
  · change ∀ r ∈ [⟨VG.Proof.Bignum.off p.B arithmetic, arithmeticBytes⟩, ⟨VG.Proof.Bignum.off (W 5) VG.Impl.Dsa.Generation.Layout.p, p.pLen⟩, ⟨VG.Proof.Bignum.off (W 5) exponent, p.pLen⟩],
      (⟨p.F, frameBytes⟩ : Region).Disjoint r
    rw [h5]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact p.frame_part ha
    · exact p.frame_part hp
    · exact p.frame_part he
  · change ∀ r ∈ [⟨VG.Proof.Bignum.off p.B arithmetic, arithmeticBytes⟩, ⟨VG.Proof.Bignum.off (W 5) VG.Impl.Dsa.Generation.Layout.p, p.pLen⟩, ⟨VG.Proof.Bignum.off (W 5) exponent, p.pLen⟩],
      (⟨p.hash, oRsa⟩ : Region).Disjoint r
    rw [h5]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact p.parts_disjoint hh ha (Or.inl (by decide))
    · exact p.parts_disjoint hh hp (Or.inl (by decide))
    · exact p.parts_disjoint hh he (Or.inl (by decide))

end VG.Proof.Dsa.AArch64.Generation

end

end


/-! # Concrete p-primality buffers preserve the generated candidate and exponent -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

def GenerationGeometry.primalityPlan (p : GenerationGeometry) (seed rand : GenerationTape p)
    (seedLength : seed.bytes.length = p.qLen) (W : Nat → BitVec 64) (offset : Nat)
    (carry : offset + p.count < 2 ^ 32)
    (h1 : W 1 = seed.ptr) (h3 : W 3 = VG.Proof.Bignum.off p.B wrappedSeed)
    (h4 : W 4 = VG.Proof.Bignum.off p.B hashes) (h2 : W 2 = BitVec.ofNat 64 offset)
    (h5 : W 5 = p.B) (h0 : W 0 = VG.Proof.Bignum.off p.B shaped)
    (h14 : W 14 = rand.ptr) (h15 : W 15 = BitVec.ofNat 64 rand.bytes.length) : PPrimalityPlan := by
  have bound (d : Nat) (hd : d ≤ domainCheck) (n : Nat) (hn : n ≤ arithmeticBytes) :
      d + n ≤ usedBytes p.pLen := by
    rcases p.width with h | h | h <;> rw [h] <;> unfold usedBytes domainCheck arithmeticBytes at * <;> omega_using [hd, hn]
  have pn : p.pLen ≤ 384 := by rcases p.width with h | h | h <;> omega_using [h]
  have qn : p.qLen ≤ 32 := by rcases p.qWidth with h | h <;> omega_using [h]
  have ha := bound arithmetic (by decide) arithmeticBytes (by rfl)
  have hh := bound VG.Impl.Dsa.Generation.Layout.hash (by decide) oRsa (by decide)
  have hw := bound witness (by decide) p.pLen (by unfold arithmeticBytes; omega_using [pn])
  have hp := bound VG.Impl.Dsa.Generation.Layout.p (by decide) p.pLen (by unfold arithmeticBytes; omega_using [pn])
  have he := bound exponent (by decide) p.pLen (by unfold arithmeticBytes; omega_using [pn])
  refine {
    construct := p.constructPlan seed seedLength W offset carry h1 h3 h4 h2 h5 h0
    rand := rand.bytes
    rp := rand.ptr
    size := rfl
    tapePtr := h14
    tapeLength := h15
    randMax := rand.size
    bufferSeparate := ?_
    bufferOutside := ?_
    tapeBuffer := ?_
    framePrime := ?_
    hashPrime := ?_
    pPrime := ?_
    exponentPrime := ?_
    tapeConstruct := ?_
    hashStack := ?_
    stackSize := p.stackSize
    arenaBound := ?_
    tapeBound := rand.bound
    tapeArena := ?_
    tapeFrame := rand.frame
    tapeStack := rand.stack
    arenaFrame := ?_
    arenaStack := ?_ }
  · change (p.part arithmetic arithmeticBytes).Disjoint ⟨VG.Proof.Bignum.off (W 5) witness, p.pLen⟩
    rw [h5]
    exact p.parts_disjoint ha hw (Or.inr (by unfold witness arithmetic; omega_using [pn]))
  · change ∀ i < p.pLen, arithmeticBytes ≤ ofs (VG.Proof.Bignum.off p.B arithmetic) (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) witness) i)
    rw [h5]
    intro i hi
    exact out_scr (p.parts_disjoint hw ha (Or.inl (by unfold witness arithmetic; omega_using [pn])))
      (Offset.contains_base _ (by omega_using [hi]) (by omega_using [pn, hi]))
  · change (⟨rand.ptr, rand.bytes.length⟩ : Region).Disjoint ⟨VG.Proof.Bignum.off (W 5) witness, p.pLen⟩
    rw [h5]
    exact rand.part hw
  · change ∀ r ∈ [⟨VG.Proof.Bignum.off p.B arithmetic, arithmeticBytes⟩, ⟨VG.Proof.Bignum.off (W 5) witness, p.pLen⟩],
      (⟨p.F, frameBytes⟩ : Region).Disjoint r
    rw [h5]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact p.frame_part ha
    · exact p.frame_part hw
  · change ∀ r ∈ [⟨VG.Proof.Bignum.off p.B arithmetic, arithmeticBytes⟩, ⟨VG.Proof.Bignum.off (W 5) witness, p.pLen⟩],
      (⟨p.hash, oRsa⟩ : Region).Disjoint r
    rw [h5]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact p.parts_disjoint hh ha (Or.inl (by decide))
    · exact p.parts_disjoint hh hw (Or.inl (by decide))
  · change ∀ r ∈ [⟨VG.Proof.Bignum.off p.B arithmetic, arithmeticBytes⟩, ⟨VG.Proof.Bignum.off (W 5) witness, p.pLen⟩,
      below p.F callStack, ⟨p.F, frameBytes⟩],
      (⟨VG.Proof.Bignum.off (W 5) VG.Impl.Dsa.Generation.Layout.p, p.pLen⟩ : Region).Disjoint r
    rw [h5]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact p.parts_disjoint hp ha (Or.inl (by unfold VG.Impl.Dsa.Generation.Layout.p arithmetic; omega_using [pn]))
    · exact p.parts_disjoint hp hw (Or.inl (by unfold VG.Impl.Dsa.Generation.Layout.p witness; omega_using [pn]))
    · exact (p.stack_part hp).symm
    · exact (p.frame_part hp).symm
  · change ∀ r ∈ [⟨VG.Proof.Bignum.off p.B arithmetic, arithmeticBytes⟩, ⟨VG.Proof.Bignum.off (W 5) witness, p.pLen⟩,
      below p.F callStack, ⟨p.F, frameBytes⟩],
      (⟨VG.Proof.Bignum.off (W 5) exponent, p.pLen⟩ : Region).Disjoint r
    rw [h5]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact p.parts_disjoint he ha (Or.inl (by unfold exponent arithmetic; omega_using [pn]))
    · exact p.parts_disjoint he hw (Or.inl (by unfold exponent witness; omega_using [pn]))
    · exact (p.stack_part he).symm
    · exact (p.frame_part he).symm
  · change ∀ r ∈ (⟨VG.Proof.Bignum.off (W 5) shaped, p.pLen⟩ ::
      [⟨VG.Proof.Bignum.off p.B hashes, (p.count + 1) * p.qLen⟩, ⟨VG.Proof.Bignum.off p.B wrappedSeed, p.qLen⟩, ⟨p.hash, oRsa⟩, retR p.F]) ++
      [⟨VG.Proof.Bignum.off p.B arithmetic, arithmeticBytes⟩, ⟨VG.Proof.Bignum.off (W 5) VG.Impl.Dsa.Generation.Layout.p, p.pLen⟩, ⟨VG.Proof.Bignum.off (W 5) exponent, p.pLen⟩],
      (⟨rand.ptr, rand.bytes.length⟩ : Region).Disjoint r
    rw [h5]
    intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rand.part (bound shaped (by decide) p.pLen (by unfold arithmeticBytes; omega_using [pn]))
    · exact rand.part (bound hashes (by decide) ((p.count + 1) * p.qLen) (by
        have := p.hashSizes.2.1; unfold arithmeticBytes; omega_using [this]))
    · exact rand.part (bound wrappedSeed (by decide) p.qLen (by unfold arithmeticBytes; omega_using [qn]))
    · exact rand.part hh
    · exact rand.stack.sub_right (below_sub (by decide) (by decide))
    · exact rand.part ha
    · exact rand.part hp
    · exact rand.part he
  · exact (p.stack_part hh).symm
  all_goals
    have hd : domainCheck ≤ usedBytes p.pLen := by unfold usedBytes; omega_using []
    have hs : Region.Sub ⟨W 5, domainCheck⟩ ⟨p.B, usedBytes p.pLen⟩ := by
      rw [h5]; exact Region.sub_prefix hd
  · change (W 5).toNat + domainCheck ≤ 2 ^ 64
    have := p.arenaBound
    rw [h5]; omega_using [hd, this]
  · exact rand.arena.sub_right hs
  · exact (p.frameArena.sub_right hs).symm
  · exact (p.stackArena.sub_right hs).symm

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # The accepted subgroup supplies the bounded p-search preconditions -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/GeometrySearch.lean`, which only this module imported.
section

/-! # Concrete bounded p-search controller and its unchanged seed and q -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

def GenerationGeometry.searchPlan (p : GenerationGeometry) (seed rand : GenerationTape p)
    (seedLength : seed.bytes.length = p.qLen) (W : Nat → BitVec 64) (offset : Nat)
    (carry : offset + p.count < 2 ^ 32)
    (h1 : W 1 = seed.ptr) (h3 : W 3 = VG.Proof.Bignum.off p.B wrappedSeed)
    (h4 : W 4 = VG.Proof.Bignum.off p.B hashes) (h2 : W 2 = BitVec.ofNat 64 offset)
    (h5 : W 5 = p.B) (h0 : W 0 = VG.Proof.Bignum.off p.B shaped)
    (h14 : W 14 = rand.ptr) (h15 : W 15 = BitVec.ofNat 64 rand.bytes.length) : SearchPlan := by
  let a := p.primalityPlan seed rand seedLength W offset carry h1 h3 h4 h2 h5 h0 h14 h15
  have writes : a.changed = p.pWork := by
    dsimp only [a, PPrimalityPlan.changed, PPrimalityPlan.testWrites, PConstructPlan.changed,
      HashPlan.changed, GenerationGeometry.primalityPlan, GenerationGeometry.constructPlan, GenerationGeometry.hashPlan]
    rw [h5]
    rfl
  have pn : p.pLen ≤ 384 := by rcases p.width with h | h | h <;> omega_using [h]
  have qn : p.qLen ≤ 32 := by rcases p.qWidth with h | h <;> omega_using [h]
  have hc := p.small_bound (d := VG.Impl.Dsa.Generation.Layout.control) (n := 24) (by decide) (by decide)
  have hq := p.small_bound (d := q) (n := p.qLen) (by decide) (by unfold arithmeticBytes; omega_using [qn])
  have hh := p.small_bound (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)
  have hp := p.small_bound (d := VG.Impl.Dsa.Generation.Layout.p) (n := p.pLen) (by decide) (by unfold arithmeticBytes; omega_using [pn])
  have he := p.small_bound (d := exponent) (n := p.pLen) (by decide) (by unfold arithmeticBytes; omega_using [pn])
  refine {
    attempt := a
    C := VG.Proof.Bignum.off p.B VG.Impl.Dsa.Generation.Layout.control
    controlBase := ?_
    controlSeparate := ?_
    frameControl := p.frame_part hc
    hashControl := p.parts_disjoint hh hc (Or.inl (by decide))
    pControl := ?_
    exponentControl := ?_
    seedSeparate := ?_
    qSeparate := ?_
    tapeSeparate := ?_ }
  · change W 5 + _ = _
    rw [h5]
  · change ∀ r ∈ ⟨p.F, frameBytes⟩ :: a.changed,
      (p.part VG.Impl.Dsa.Generation.Layout.control 24).Disjoint r
    rw [writes]
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact (p.frame_part hc).symm
    · exact p.pWork_separate (Or.inl ⟨rfl, rfl⟩) r hr
  · change (⟨VG.Proof.Bignum.off (W 5) VG.Impl.Dsa.Generation.Layout.p, p.pLen⟩ : Region).Disjoint (p.part VG.Impl.Dsa.Generation.Layout.control 24)
    rw [h5]
    exact p.parts_disjoint hp hc (Or.inl (by unfold VG.Impl.Dsa.Generation.Layout.p VG.Impl.Dsa.Generation.Layout.control; omega_using [pn]))
  · change (⟨VG.Proof.Bignum.off (W 5) exponent, p.pLen⟩ : Region).Disjoint (p.part VG.Impl.Dsa.Generation.Layout.control 24)
    rw [h5]
    exact p.parts_disjoint he hc (Or.inl (by unfold exponent VG.Impl.Dsa.Generation.Layout.control; omega_using [pn]))
  · change ∀ r ∈ (p.part VG.Impl.Dsa.Generation.Layout.control 24) :: ⟨p.F, frameBytes⟩ :: a.changed,
      (⟨seed.ptr, p.qLen⟩ : Region).Disjoint r
    rw [writes, ← seedLength]
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact seed.part hc
    rcases List.mem_cons.mp hr with rfl | hr
    · exact seed.frame
    exact seed.pWork r hr
  · change ∀ r ∈ (p.part VG.Impl.Dsa.Generation.Layout.control 24) :: ⟨p.F, frameBytes⟩ :: a.changed,
      (⟨VG.Proof.Bignum.off (W 5) q, (Spec.Dsa.encodeBE p.qLen (Spec.Dsa.qCandidate (8 * p.qLen) seed.bytes)).length⟩ : Region).Disjoint r
    rw [writes, h5, VG.Proof.Dsa.encodeBE_length]
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact p.parts_disjoint hq hc (Or.inl (by unfold q VG.Impl.Dsa.Generation.Layout.control; omega_using [qn]))
    rcases List.mem_cons.mp hr with rfl | hr
    · exact (p.frame_part hq).symm
    exact p.pWork_separate (Or.inr ⟨rfl, rfl⟩) r hr
  · change ∀ r ∈ (p.part VG.Impl.Dsa.Generation.Layout.control 24) :: ⟨p.F, frameBytes⟩ :: a.changed,
      (⟨rand.ptr, rand.bytes.length⟩ : Region).Disjoint r
    rw [writes]
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact rand.part hc
    rcases List.mem_cons.mp hr with rfl | hr
    · exact rand.frame
    exact rand.pWork r hr

end VG.Proof.Dsa.AArch64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

def searchWords (B : Addr) (W : Nat → BitVec 64) : Nat → BitVec 64 :=
  upd (upd (upd W 0 (VG.Proof.Bignum.off B shaped)) 2 0) 25 (VG.Proof.Bignum.off B wrappedSeed)

def GenerationMemory.searchPlan {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (seed : GenerationTape p.geo) (hlen : seed.bytes.length = p.geo.qLen)
    (h1 : W 1 = seed.ptr) : SearchPlan :=
  p.geo.searchPlan seed p.rand hlen (searchWords p.geo.B W) 0
    (by have := p.geo.hashSizes.1; omega_using [this])
    (by simpa [searchWords, upd] using h1)
    (by simpa [searchWords, upd] using (h.slots 3 (by simp [generationSlots])).trans p.wrappedSlot)
    (by simpa [searchWords, upd] using (h.slots 4 (by simp [generationSlots])).trans p.hashesSlot)
    (by simp [searchWords, upd])
    (by simpa [searchWords, upd] using (h.slots 5 (by simp [generationSlots])).trans p.baseSlot)
    (by simp [searchWords, upd])
    (by simpa [searchWords, upd] using (h.slots 14 (by simp [generationSlots])).trans p.randSlot)
    (by simpa [searchWords, upd] using (h.slots 15 (by simp [generationSlots])).trans p.randLengthSlot)

theorem GenerationMemory.searchState {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (seed : GenerationTape p.geo) (hlen : seed.bytes.length = p.geo.qLen)
    (hseed : GenerationTapeMemory seed s) (h1 : W 1 = seed.ptr)
    (hq : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.geo.B q) p.geo.qLen =
      Spec.Dsa.encodeBE p.geo.qLen (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes)) :
    SearchMemory (h.searchPlan seed hlen h1) W s := by
  have pn : p.geo.pLen ≤ 384 := by rcases p.geo.width with hh | hh | hh <;> omega_using [hh]
  have qn : p.geo.qLen ≤ 32 := by rcases p.geo.qWidth with hh | hh <;> omega_using [hh]
  have h5 := (h.slots 5 (by simp [generationSlots])).trans p.baseSlot
  have ha := p.geo.small_bound (d := arithmetic) (n := arithmeticBytes) (by decide) (by rfl)
  have hqbound := p.geo.small_bound (d := q) (n := p.geo.qLen) (by decide) (by unfold arithmeticBytes; omega_using [qn])
  have hb := p.geo.small_bound (d := wrappedSeed) (n := p.geo.qLen) (by decide) (by unfold arithmeticBytes; omega_using [qn])
  have hh := p.geo.small_bound (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)
  have write (d n : Nat) (hd : d ≤ domainCheck) (hn : n ≤ arithmeticBytes) :
      ∀ i < n, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off p.geo.B d) i) 1 := by
    intro i hi
    rw [VG.Proof.Bignum.off_off]
    exact h.scratch.region (by have := p.geo.small_bound hd hn; omega_using [hi, this]) (by decide)
  refine {
    layout := h.layout
    rep := h.rep
    slots := ?_
    label := ?_
    seedRead := ?_
    wrappedWrite := write wrappedSeed p.geo.qLen (by decide) (by unfold arithmeticBytes; omega_using [qn])
    hashWrite := write hashes ((p.geo.count + 1) * p.geo.qLen) (by decide)
      (by have := p.geo.hashSizes.2.1; unfold arithmeticBytes; omega_using [this])
    seed := ?_
    scratch := h.scratch.sub (n := arithmeticBytes) ha (by decide)
    qSource := ?_
    tape := h.rand.source ha
    shapedWrite := ?_
    pWrite := ?_
    exponentWrite := ?_
    witnessWrite := ?_
    arena := (by
      have hb := (h.slots 5 (by simp [generationSlots])).trans p.baseSlot
      have := h.scratch.sub (o := 0) (n := domainCheck) (by unfold usedBytes; omega_using []) (by decide)
      simp only [VG.Proof.Bignum.off, BitVec.add_zero] at this
      change Scr s (W 5) domainCheck
      rw [hb]; exact this)
    tapeCover := h.rand.cover }
  · intro k hk
    change W k = searchWords p.geo.B W k
    have : k ≠ 0 ∧ k ≠ 2 ∧ k ≠ 25 := by simp only [searchSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; omega_using [hk]
    simp [searchWords, upd, this.1, this.2.1, this.2.2]
  · change LabAt s p.geo.F p.geo.hash (searchWords p.geo.B W) (VG.Proof.Bignum.off p.geo.B wrappedSeed) p.geo.qLen
    refine ⟨by simp [searchWords, upd], ?_, by omega_using [qn], ?_, ?_, ?_, ?_⟩
    · simpa [searchWords, upd] using (h.slots 26 (by simp [generationSlots])).trans p.hashLenSlot
    · exact Covers.right (Covers.one (h.scratch.region hb (by rcases p.geo.qWidth with hh | hh <;> omega_using [hh])))
    · exact p.geo.parts_disjoint hb hh (Or.inr (by unfold wrappedSeed VG.Impl.Dsa.Generation.Layout.hash oRsa; omega_using []))
    · exact (p.geo.frame_part hb).symm
    · exact (p.geo.stack_part hb).sub_left (below_sub (a := 16) (by decide) (by decide))
  · change ∀ i < p.geo.qLen, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.off seed.ptr i) 1
    intro i hi
    exact hseed.cover _ _ ⟨⟨seed.ptr, seed.bytes.length⟩, by simp, Offset.contains_base _ (by omega_using [hi, hlen]) (by omega_using [hi, qn])⟩
  · change Spec.Rsa.bytesAt s.mem seed.ptr p.geo.qLen = seed.bytes
    rw [← hlen]; exact hseed.bytes
  · change Src s (VG.Proof.Bignum.off p.geo.B arithmetic) arithmeticBytes (VG.Proof.Bignum.off (W 5) q)
      (Spec.Dsa.encodeBE p.geo.qLen (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes))
    rw [h5]
    apply arena_source h.scratch
    · simpa only [VG.Proof.Dsa.encodeBE_length] using hqbound
    · rw [VG.Proof.Dsa.encodeBE_length]; omega_using [qn]
    · simpa only [VG.Proof.Dsa.encodeBE_length] using hq
    · simpa only [VG.Proof.Dsa.encodeBE_length, GenerationGeometry.part] using p.geo.parts_disjoint hqbound ha (Or.inl (by unfold q arithmetic; omega_using [qn]))
  all_goals
    change ∀ i < p.geo.pLen, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) _) i) 1
    rw [h5]
    apply write _ p.geo.pLen (by decide) (by unfold arithmeticBytes; omega_using [pn])

end VG.Proof.Dsa.AArch64.Generation
