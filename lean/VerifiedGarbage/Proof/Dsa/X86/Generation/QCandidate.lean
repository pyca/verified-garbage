module

import VerifiedGarbage.Proof.Dsa.X86.Generation.QArguments
import VerifiedGarbage.Proof.Dsa.X86.Generation.SeedHash
import VerifiedGarbage.Proof.Dsa.X86.Generation.QShape
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Impl.Dsa.X86.Generation.QCandidate
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Dsa.X86.Generation.HashFrame

/-! The native seed hash and byte shaper produce the specification's subgroup candidate. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86

theorem q_candidate {H : Hash} {ok : HashOK H} {s : State}
    {st data digest scratch dst : BitVec 32} {len digestOffset candidateOffset bits : Nat} {seed : List Byte}
    (G : HashGeometry ok st data digest scratch len s) (R : HashRegisters st data scratch len s)
    (digestPosition : scratch + BitVec.ofNat 32 digestOffset = digest)
    (candidatePosition : scratch + BitVec.ofNat 32 candidateOffset = dst)
    (seedBytes : Spec.Sha256.bytesAt s.mem (data.setWidth 64) len = seed)
    (hash : ok.SH.H.hash seed = Spec.Dsa.seedHash bits seed)
    (digestLength : (Spec.Dsa.seedHash bits seed).length = H.D)
    (width : 8 * H.D = bits) (lower : 2 ≤ H.D)
    (dstFit : dst.toNat + H.D ≤ 2 ^ 32)
    (write : InRegions s.wr (dst.setWidth 64) H.D)
    (apart : Region.Disjoint ⟨digest.setWidth 64, H.D⟩ ⟨dst.setWidth 64, H.D⟩) :
    WP isa (qCandidate H digestOffset candidateOffset) s fun t =>
      Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem (dst.setWidth 64) H.D) = Spec.Dsa.qCandidate bits seed ∧
      Frame (hashAreas ok st digest scratch s ++ [⟨dst.setWidth 64, H.D⟩]) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s t := by
  have small : H.D < 2 ^ 32 := by have := ok.hDF; have := ok.hF; omega
  unfold qCandidate
  refine WP.seq (WP.mono (seed_hash G R digestPosition) fun a ⟨A, RA, hashed⟩ => ?_)
  rw [seedBytes, hash] at hashed
  refine WP.seq (WP.mono (q_arguments (digestOffset := digestOffset) (candidateOffset := candidateOffset)
    (len := H.D) RA.scratch) fun b ⟨src, dstReg, count, memory, K⟩ => ?_)
  rw [digestPosition] at src
  rw [candidatePosition] at dstReg
  have sourceRead : InRegions (b.rd ++ b.wr) (digest.setWidth 64) H.D := by
    rw [K.2.1, K.2.2, A.rd, A.wr]
    obtain ⟨region, hr, hc⟩ := G.writable (digest.setWidth 64) H.D
      ⟨⟨digest.setWidth 64, H.F⟩, by simp,
        by simpa only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add] using ok.hDF⟩
    exact ⟨region, List.mem_append_right _ hr, hc⟩
  have destWrite : InRegions b.wr (dst.setWidth 64) H.D := by rw [K.2.2, A.wr]; exact write
  have bytes (i : Nat) (hi : i < (Spec.Dsa.seedHash bits seed).length) :
      b.mem (off (digest.setWidth 64) i) = (Spec.Dsa.seedHash bits seed).getD i 0 := by
    have eq := congrArg (fun bs : List Byte => bs[i]?) hashed
    rw [List.getElem?_take, ite_eq_left (by omega), Spec.Sha256.bytesAt, List.getElem?_map,
      List.getElem?_range (by rw [digestLength] at hi; exact Nat.lt_of_lt_of_le hi ok.hDF)] at eq
    simpa only [Option.map_some, Option.some.injEq, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi, Option.getD_some, memory, off] using eq
  refine WP.mono (q_shape (bs := Spec.Dsa.seedHash bits seed) (by omega) (by omega) (by have := G.digest_fit; have := ok.hDF; omega)
    (by omega) src dstReg (by rw [digestLength]; exact count) (by rw [digestLength]; exact sourceRead) (by rw [digestLength]; exact destWrite)
    (by rw [digestLength]; exact apart) bytes)
    fun t ⟨shaped, FT, KT⟩ => ?_
  refine ⟨?_, ?_, ?_⟩
  · change Spec.Rsa.bytesAt t.mem (dst.setWidth 64) (Spec.Dsa.seedHash bits seed).length = _ at shaped
    rw [← digestLength, shaped]
    exact VG.Proof.Dsa.Generation.qCandidate_octets (by omega) seed (by rw [digestLength]; exact width)
  · have first : Frame (hashAreas ok st digest scratch s ++ [⟨dst.setWidth 64, H.D⟩]) s.mem b.mem := by
      rw [memory]
      exact A.frame.mono (by intro r hr; exact List.mem_append_left _ hr)
    apply first.trans
    rw [digestLength] at FT
    exact FT.mono (by intro r hr; exact List.mem_append_right _ hr)
  · have KA : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s a := by
      refine ⟨?_, A.rd, A.wr⟩
      intro reg hr
      apply A.cs
      cases reg <;> simp_all [calleeSaved]
    exact (KA.trans (K.mono (by decide))).trans (KT.mono (by decide))

end VG.Proof.Dsa.X86.Generation
