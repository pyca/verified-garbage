module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeometryTape
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashPlan
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.BufferSeparate
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.BufferSeparate
public import VerifiedGarbage.Impl.Ffdh.X86_64.Domain
public import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
public import VerifiedGarbage.Proof.Bignum.X86_64.Double
public import VerifiedGarbage.Proof.Dsa.Arithmetic
public import VerifiedGarbage.Proof.Dsa.BitLengthBounds
public import VerifiedGarbage.Proof.Dsa.Digest
public import VerifiedGarbage.Proof.Dsa.Encoding
public import VerifiedGarbage.Proof.Dsa.Generation.Memory
public import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
public import VerifiedGarbage.Proof.Dsa.Generation.SeedAdd
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CopyDigest
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hash
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PHashArgs
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PHashOne
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PSeedHash
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedAdd
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedByte
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SourceFrame
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SourceSlice
public import VerifiedGarbage.Proof.Ffdh.KeyScalar
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Copy
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CutByte
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Masks
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ShapeByte
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessCut
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha1
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha256
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Impl.Ffdh.X86_64.Domain
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.Generation.SeedAdd
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CopyDigest
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hash
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PHashArgs
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PHashOne
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PSeedHash
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedAdd
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedByte
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SourceFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SourceSlice
import VerifiedGarbage.Proof.Ffdh.KeyScalar
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Copy
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CutByte
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Masks
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ShapeByte
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessCut
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha1
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha256
import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf

/-! # Concrete hash-contribution buffers for each supported parameter size -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

def GenerationGeometry.count (p : GenerationGeometry) : Nat := (8 * p.pLen - 1) / (8 * p.qLen)

theorem GenerationGeometry.hashSizes (p : GenerationGeometry) :
    p.count ≤ 11 ∧ (p.count + 1) * p.qLen ≤ 384 ∧ p.pLen ≤ (p.count + 1) * p.qLen := by
  unfold count
  rcases p.lengths with ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> rw [h1,h2] <;> decide

def GenerationGeometry.hashPlan (p : GenerationGeometry) (seed : GenerationTape p)
    (seedLength : seed.bytes.length = p.qLen) (W : Nat → BitVec 64) (offset : Nat)
    (carry : offset + p.count < 2 ^ 32)
    (h1 : W 1 = seed.ptr) (h3 : W 3 = off p.B wrappedSeed)
    (h4 : W 4 = off p.B hashes) (h2 : W 2 = BitVec.ofNat 64 offset) : HashPlan := by
  have hn : p.qLen ≤ 32 := by rcases p.qWidth with h | h <;> omega
  have hw : wrappedSeed + p.qLen ≤ usedBytes p.pLen := by
    have := p.width
    rcases this with h | h | h <;> rw [h] <;> unfold wrappedSeed usedBytes domainCheck <;> omega
  have hh : hashes + (p.count + 1) * p.qLen ≤ usedBytes p.pLen := by
    have hb := p.hashSizes.2.1
    rcases p.width with h | h | h <;> rw [h] <;> unfold hashes usedBytes domainCheck <;> omega
  have hs : VG.Impl.Dsa.Generation.Layout.hash + oRsa ≤ usedBytes p.pLen := by
    rcases p.width with h | h | h <;> rw [h] <;> decide
  have hwh : (p.part wrappedSeed p.qLen).Disjoint (p.part VG.Impl.Dsa.Generation.Layout.hash oRsa) :=
    p.parts_disjoint hw hs (Or.inr (by decide))
  have hhh : (p.part hashes ((p.count + 1) * p.qLen)).Disjoint (p.part VG.Impl.Dsa.Generation.Layout.hash oRsa) :=
    p.parts_disjoint hh hs (Or.inr (by decide))
  exact {
    F := p.F
    S := p.hash
    seedPtr := seed.ptr
    wrapped := off p.B wrappedSeed
    output := off p.B hashes
    len := p.qLen
    count := p.count
    offset := offset
    seed := seed.bytes
    W := W
    width := p.qWidth
    count_le := p.hashSizes.1
    carry := carry
    seed_len := seedLength
    seed_slot := h1
    wrapped_slot := h3
    output_slot := h4
    offset_slot := h2
    wrapped_sep := bufferSeparate_of_regions (len := p.qLen) (by omega) (p.frame_part hw).symm hwh
    output_sep := bufferSeparate_of_regions (len := (p.count + 1) * p.qLen)
      (by omega_using [p.hashSizes.2.1]) (p.frame_part hh).symm hhh
    seed_wrap := by simpa only [seedLength, GenerationGeometry.part, GenerationGeometry.hash] using seed.part hw
    seed_output := by simpa only [seedLength, GenerationGeometry.part, GenerationGeometry.hash] using seed.part hh
    seed_scratch := by simpa only [seedLength, GenerationGeometry.part, GenerationGeometry.hash] using seed.part hs
    seed_stack := by simpa only [seedLength] using seed.stack.sub_right (below_sub (a := 16) (by decide) (by decide))
    output_wrap := p.parts_disjoint hh hw (Or.inr (by unfold wrappedSeed hashes; omega))
    output_scratch := hhh
    output_stack := (p.stack_part hh).symm.sub_right (below_sub (by decide) (by decide)) }

end VG.Proof.Dsa.X86_64.Generation
