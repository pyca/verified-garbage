module

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeometryWork
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Context
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeometryPrime
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeState
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeCall
public import VerifiedGarbage.Proof.Dsa.AArch64.Run
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Label
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Impl.Dsa.Generation.Layout
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Arithmetic

/-! ### `Dsa.AArch64.Generation.SubgroupState`, which this module and modules that import it used -/

section

/-! # State connecting subgroup hashing to the complete native primality call -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Proof.RsaOaep.AArch64

structure SubgroupPlan where
  prime : PrimeParams
  F : Addr
  hash : Addr
  seedPtr : Addr
  output : Addr
  seed : List Byte
  W : Nat → BitVec 64
  width : prime.len = 20 ∨ prime.len = 32
  words : prime.w = 4
  size : prime.Z = Impl.Dsa.Generation.Layout.arithmeticBytes
  draw : prime.drawBytes = if prime.len = 20 then 24 else 32
  checks : prime.checks = 64
  seedLength : seed.length = prime.len
  modulus : prime.N = Spec.Dsa.qCandidate (8 * prime.len) seed
  base : W 5 + BitVec.ofNat 64 Impl.Dsa.Generation.Layout.arithmetic = prime.B
  outputPtr : W 5 + BitVec.ofNat 64 Impl.Dsa.Generation.Layout.q = output
  outputSlot : W 0 = output
  witnessPtr : W 5 + BitVec.ofNat 64 Impl.Dsa.Generation.Layout.witness = prime.p
  tapePtr : W 14 = prime.rp
  tapeLength : W 15 = BitVec.ofNat 64 prime.rand.length
  frameHeaders : ∀ k < 34, ∀ j < 32,
    Mem.Sep (VG.Proof.Bignum.off F (8 * k)) 8 (VG.Proof.Bignum.off prime.B (8 * j)) 8
  frameOutside : ∀ k < 34, ∀ i < 8, prime.Z ≤ ofs prime.B (VG.Proof.Bignum.off (VG.Proof.Bignum.off F (8 * k)) i)
  outputOutside : ∀ i < prime.len, prime.Z ≤ ofs prime.B (VG.Proof.Bignum.off output i)
  outputFrame : (⟨output, prime.len⟩ : Region).Disjoint ⟨F, frameBytes⟩
  outputScratch : Region.Disjoint ⟨hash, oRsa⟩ ⟨output, prime.len⟩
  tapeHash : ∀ r ∈ [⟨output, prime.len⟩, ⟨hash, oRsa⟩, retR F],
    (⟨prime.rp, prime.rand.length⟩ : Region).Disjoint r
  framePrime : ∀ r ∈ [⟨prime.B, Impl.Dsa.Generation.Layout.arithmeticBytes⟩,
      ⟨prime.p, prime.len⟩, below F callStack], (⟨F, frameBytes⟩ : Region).Disjoint r
  hashPrime : ∀ r ∈ [⟨prime.B, Impl.Dsa.Generation.Layout.arithmeticBytes⟩,
      ⟨prime.p, prime.len⟩, below F callStack], (⟨hash, oRsa⟩ : Region).Disjoint r
  outputPrime : ∀ r ∈ [⟨prime.B, Impl.Dsa.Generation.Layout.arithmeticBytes⟩,
      ⟨prime.p, prime.len⟩, below F callStack], (⟨output, prime.len⟩ : Region).Disjoint r
  geometry : PrimeCallGeometry (8 * prime.len) F hash (W 5) prime.rp prime.rand.length

def SubgroupPlan.hashWrites (p : SubgroupPlan) : List Region :=
  [⟨p.output, p.prime.len⟩, ⟨p.hash, oRsa⟩, retR p.F]

def SubgroupPlan.primeWrites (p : SubgroupPlan) : List Region :=
  [⟨p.prime.B, Impl.Dsa.Generation.Layout.arithmeticBytes⟩, ⟨p.prime.p, p.prime.len⟩,
    below p.F callStack]

def SubgroupPlan.changed (p : SubgroupPlan) : List Region :=
  p.hashWrites ++ p.primeWrites ++ [⟨p.F, frameBytes⟩]

structure SubgroupState (p : SubgroupPlan) (used : Nat) (s : State) : Prop where
  layout : Lay s p.F p.hash
  rep : ∃ V, Rep s.mem p.F p.hash V p.W
  label : LabAt s p.F p.hash p.W p.seedPtr p.prime.len
  seed : Spec.Rsa.bytesAt s.mem p.seedPtr p.prime.len = p.seed
  scratch : Scr s p.prime.B p.prime.Z
  tape : Src s p.prime.B p.prime.Z p.prime.rp p.prime.rand
  outputWrite : ∀ i < p.prime.len, InRegions s.wr (VG.Proof.Bignum.off p.output i) 1
  witnessWrite : ∀ i < p.prime.len, InRegions s.wr (VG.Proof.Bignum.off p.prime.p i) 1
  usedSlot : p.W 16 = BitVec.ofNat 64 used
  usedBound : used ≤ p.prime.rand.length
  arena : Scr s (p.W 5) Impl.Dsa.Generation.Layout.domainCheck
  tapeCover : Covers [⟨p.prime.rp, p.prime.rand.length⟩] (s.rd ++ s.wr)

theorem SubgroupPlan.bits (p : SubgroupPlan) : Spec.Dsa.bitLength p.prime.N = 8 * p.prime.len := by
  rw [p.modulus]
  exact VG.Proof.Dsa.Generation.qCandidate_bitLength (by rcases p.width with h | h <;> omega_using [h]) _

theorem SubgroupPlan.encoding (p : SubgroupPlan) :
    Spec.Rsa.os2ip (Spec.Dsa.encodeBE p.prime.len p.prime.N) = p.prime.N := by
  rw [← VG.Proof.Dsa.decodeBE_os2ip]
  apply VG.Proof.Dsa.decodeBE_encodeBE
  have hshape := VG.Proof.Dsa.Generation.qCandidate_shape
    (show 2 ≤ 8 * p.prime.len by rcases p.width with h | h <;> omega_using [h]) p.seed
  rw [← p.modulus] at hshape
  have hp : 256 ^ p.prime.len = 2 ^ (8 * p.prime.len) := by
    rw [Nat.pow_mul]
  rw [hp]
  exact hshape.2.2

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.ContextSubgroup`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.Generation.GeometrySubgroup`, which this module and modules that import it used -/

section

/-! # Concrete q-phase layout inside the shared generation arena -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

def GenerationGeometry.subgroupPlan (p : GenerationGeometry) (rand seed : GenerationTape p)
    (seedLength : seed.bytes.length = p.qLen) (W : Nat → BitVec 64)
    (h5 : W 5 = p.B) (h0 : W 0 = VG.Proof.Bignum.off p.B q)
    (h14 : W 14 = rand.ptr) (h15 : W 15 = BitVec.ofNat 64 rand.bytes.length) : SubgroupPlan := by
  have ha : arithmetic + arithmeticBytes ≤ usedBytes p.pLen := by
    rcases p.width with h | h | h <;> rw [h] <;> decide
  have hh : VG.Impl.Dsa.Generation.Layout.hash + oRsa ≤ usedBytes p.pLen := by
    rcases p.width with h | h | h <;> rw [h] <;> decide
  have hq : q + p.qLen ≤ usedBytes p.pLen := by
    rcases p.lengths with ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> rw [h1,h2] <;> decide
  have hw : witness + p.qLen ≤ usedBytes p.pLen := by
    rcases p.lengths with ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> rw [h1,h2] <;> decide
  have hqa : (p.part q p.qLen).Disjoint (p.part arithmetic arithmeticBytes) :=
    p.parts_disjoint hq ha (by left; rcases p.qWidth with h | h <;> rw [h] <;> decide)
  have hqh : (p.part q p.qLen).Disjoint (p.part VG.Impl.Dsa.Generation.Layout.hash oRsa) :=
    p.parts_disjoint hq hh (Or.inr (by decide))
  have hqw : (p.part q p.qLen).Disjoint (p.part witness p.qLen) :=
    p.parts_disjoint hq hw (by left; rcases p.qWidth with h | h <;> rw [h] <;> decide)
  have hs : Region.Sub ⟨W 5, domainCheck⟩ ⟨p.B, usedBytes p.pLen⟩ := by
    rw [h5]; exact Region.sub_prefix (by unfold usedBytes; omega_using [])
  exact {
    prime := p.qPrime rand seed.bytes
    F := p.F
    hash := p.hash
    seedPtr := seed.ptr
    output := VG.Proof.Bignum.off p.B q
    seed := seed.bytes
    W := W
    width := p.qWidth
    words := rfl
    size := rfl
    draw := rfl
    checks := rfl
    seedLength := seedLength
    modulus := rfl
    base := by change W 5 + _ = _; rw [h5]; rfl
    outputPtr := by change W 5 + _ = _; rw [h5]
    outputSlot := h0
    witnessPtr := by change W 5 + _ = _; rw [h5]; rfl
    tapePtr := h14
    tapeLength := h15
    frameHeaders := p.frame_headers
    frameOutside := p.frame_outside
    outputOutside := by
      change ∀ i < p.qLen, arithmeticBytes ≤ ofs (VG.Proof.Bignum.off p.B arithmetic) (VG.Proof.Bignum.off (VG.Proof.Bignum.off p.B q) i)
      intro i hi
      exact out_scr hqa (Offset.contains_base _ (by omega_using [hi]) (by rcases p.qWidth with h | h <;> omega_using [hi, h]))
    outputFrame := (p.frame_part hq).symm
    outputScratch := hqh.symm
    tapeHash := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact rand.part hq
      · exact rand.part hh
      · exact rand.stack.sub_right (below_sub (by decide) (by decide))
    framePrime := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact p.frame_part ha
      · exact p.frame_part hw
      · exact p.frame_below
    hashPrime := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact p.parts_disjoint hh ha (Or.inl (by decide))
      · exact p.parts_disjoint hh hw (Or.inl (by decide))
      · exact (p.stack_part hh).symm
    outputPrime := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hqa
      · exact hqw
      · exact (p.stack_part hq).symm
    geometry := {
      stackSize := p.stackSize
      arenaBound := by have := p.arenaBound; rw [h5]; unfold usedBytes at this; omega_using [this]
      tapeBound := rand.bound
      tapeArena := rand.arena.sub_right hs
      tapeFrame := rand.frame
      tapeStack := rand.stack
      arenaFrame := (p.frameArena.sub_right hs).symm
      arenaStack := (p.stackArena.sub_right hs).symm
      hashTest := by
        change ∀ r ∈ [(⟨VG.Proof.Bignum.off (W 5) arithmetic, arithmeticBytes⟩ : Region),
          ⟨VG.Proof.Bignum.off (W 5) witness, 8 * p.qLen / 8⟩,
          below p.F 272], (⟨p.hash, oRsa⟩ : Region).Disjoint r
        rw [h5, Nat.mul_div_cancel_left _ (by decide)]
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact p.parts_disjoint hh ha (Or.inl (by decide))
        · exact p.parts_disjoint hh hw (Or.inl (by decide))
        · exact (p.stack_part hh).symm } }

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # The persistent search state supplies every precondition of the q phase -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

def GenerationMemory.subgroupPlan {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (seed : GenerationTape p.geo) (hlen : seed.bytes.length = p.geo.qLen)
    (h0 : W 0 = VG.Proof.Bignum.off p.geo.B q) : SubgroupPlan :=
  p.geo.subgroupPlan p.rand seed hlen W
    ((h.slots 5 (by simp [generationSlots])).trans p.baseSlot) h0
    ((h.slots 14 (by simp [generationSlots])).trans p.randSlot)
    ((h.slots 15 (by simp [generationSlots])).trans p.randLengthSlot)

theorem GenerationMemory.subgroupState {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (seed : GenerationTape p.geo) (hlen : seed.bytes.length = p.geo.qLen)
    (hseed : GenerationTapeMemory seed s) (h0 : W 0 = VG.Proof.Bignum.off p.geo.B q)
    (h25 : W 25 = seed.ptr) {used : Nat} (h16 : W 16 = BitVec.ofNat 64 used)
    (hu : used ≤ p.rand.bytes.length) : SubgroupState (h.subgroupPlan seed hlen h0) used s := by
  have qn : p.geo.qLen ≤ 32 := by rcases p.geo.qWidth with hh | hh <;> omega_using [hh]
  have ha := p.geo.small_bound (d := arithmetic) (n := arithmeticBytes) (by decide) (by rfl)
  have hh := p.geo.small_bound (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)
  have hq := p.geo.small_bound (d := q) (n := p.geo.qLen) (by decide) (by unfold arithmeticBytes; omega_using [qn])
  have hw := p.geo.small_bound (d := witness) (n := p.geo.qLen) (by decide) (by unfold arithmeticBytes; omega_using [qn])
  refine {
    layout := h.layout
    rep := h.rep
    label := ?_
    seed := ?_
    scratch := h.scratch.sub (n := arithmeticBytes) ha (by decide)
    tape := h.rand.source ha
    outputWrite := ?_
    witnessWrite := ?_
    usedSlot := h16
    usedBound := hu
    arena := (by
      have hb := (h.slots 5 (by simp [generationSlots])).trans p.baseSlot
      have := h.scratch.sub (o := 0) (n := domainCheck) (by unfold usedBytes; omega_using []) (by decide)
      simp only [VG.Proof.Bignum.off, BitVec.add_zero] at this
      change Scr s (W 5) domainCheck
      rw [hb]; exact this)
    tapeCover := h.rand.cover }
  · change LabAt s p.geo.F p.geo.hash W seed.ptr p.geo.qLen
    refine ⟨h25, (h.slots 26 (by simp [generationSlots])).trans p.hashLenSlot, by omega_using [qn], ?_, ?_, ?_, ?_⟩
    · simpa only [hlen] using hseed.cover
    · simpa only [hlen, GenerationGeometry.part, GenerationGeometry.hash] using seed.part hh
    · simpa only [hlen] using seed.frame
    · simpa only [hlen] using (seed.stack.sub_right (below_sub (a := 16) (by decide) (by decide))).symm
  · change Spec.Rsa.bytesAt s.mem seed.ptr p.geo.qLen = seed.bytes
    rw [← hlen]
    exact hseed.bytes
  · change ∀ i < p.geo.qLen, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off p.geo.B q) i) 1
    intro i hi
    rw [VG.Proof.Bignum.off_off]
    exact h.scratch.region (by omega_using [hq, hi]) (by decide)
  · change ∀ i < p.geo.qLen, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off p.geo.B witness) i) 1
    intro i hi
    rw [VG.Proof.Bignum.off_off]
    exact h.scratch.region (by omega_using [hw, hi]) (by decide)

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # Lift phase footprints to the full native parameter-search workspace -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

theorem GenerationContext.frame_parts {p : GenerationContext} {rs : List Region} {m m' : Mem}
    (hf : Frame rs m m')
    (cover : ∀ r ∈ rs, ∃ q ∈ p.changed, Region.Sub r q) : Frame p.changed m m' := by
  intro a ha
  apply hf a
  intro r hr hc
  obtain ⟨q, hq, sub⟩ := cover r hr
  exact ha q hq (sub a hc)

theorem GenerationContext.frame_single {p : GenerationContext} {m m' : Mem}
    (hf : Frame [⟨p.geo.F, frameBytes⟩] m m') : Frame p.changed m m' :=
  hf.mono (by intro r hr; rcases List.mem_singleton.mp hr with rfl; simp [changed])

theorem GenerationMemory.subgroup_frame {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (seed : GenerationTape p.geo) (hlen : seed.bytes.length = p.geo.qLen)
    (h0 : W 0 = VG.Proof.Bignum.off p.geo.B q) {m m' : Mem}
    (hf : Frame (h.subgroupPlan seed hlen h0).changed m m') : Frame p.changed m m' := by
  apply GenerationContext.frame_parts hf
  change ∀ r ∈ [⟨VG.Proof.Bignum.off p.geo.B q, p.geo.qLen⟩, ⟨p.geo.hash, oRsa⟩, retR p.geo.F] ++
    [⟨VG.Proof.Bignum.off p.geo.B arithmetic, arithmeticBytes⟩, ⟨VG.Proof.Bignum.off p.geo.B witness, p.geo.qLen⟩,
      below p.geo.F 272] ++
    [⟨p.geo.F, frameBytes⟩], ∃ out ∈ p.changed, Region.Sub r out
  have qn : p.geo.qLen ≤ 32 := by rcases p.geo.qWidth with hh | hh <;> omega_using [hh]
  have part (d n : Nat) (hd : d ≤ domainCheck) (hn : n ≤ arithmeticBytes) :
      ∃ out ∈ p.changed, Region.Sub (p.geo.part d n) out :=
    ⟨⟨p.geo.B, usedBytes p.geo.pLen⟩, by simp [GenerationContext.changed],
      p.geo.part_sub (p.geo.small_bound hd hn)⟩
  intro r hr
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact part q p.geo.qLen (by decide) (by unfold arithmeticBytes; omega_using [qn])
  · exact part VG.Impl.Dsa.Generation.Layout.hash oRsa (by decide) (by decide)
  · exact ⟨below p.geo.F 272, by simp [GenerationContext.changed], below_sub (by decide) (by decide)⟩
  · exact part arithmetic arithmeticBytes (by decide) (by rfl)
  · exact part witness p.geo.qLen (by decide) (by unfold arithmeticBytes; omega_using [qn])
  · exact ⟨below p.geo.F 272, by simp [GenerationContext.changed], fun _ h => h⟩
  · exact ⟨⟨p.geo.F, frameBytes⟩, by simp [GenerationContext.changed], fun _ h => h⟩

end VG.Proof.Dsa.AArch64.Generation
