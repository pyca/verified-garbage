module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.SeedHash
public import VerifiedGarbage.Proof.Dsa.X86.Generation.QArguments
public import VerifiedGarbage.Proof.Bignum.X86.CopyRead
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.CopyOctets
import VerifiedGarbage.Proof.Framework.Covers

/-! Copy an unchanged digest using the common hash and byte-copy implementations. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Proof.Mont.X86
open VG.Proof.Bignum.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86

theorem hash_copy {H : Hash} {ok : HashOK H} {s : State}
    {st data digest scratch dst : BitVec 32} {len digestOffset destinationOffset : Nat}
    (G : HashGeometry ok st data digest scratch len s) (R : HashRegisters st data scratch len s)
    (digestPosition : scratch + BitVec.ofNat 32 digestOffset = digest)
    (destinationPosition : scratch + BitVec.ofNat 32 destinationOffset = dst)
    (dstFit : dst.toNat + H.D ≤ 2 ^ 32)
    (write : InRegions s.wr (dst.setWidth 64) H.D)
    (apart : Region.Disjoint ⟨digest.setWidth 64, H.D⟩ ⟨dst.setWidth 64, H.D⟩) :
    WP isa (.seq (seedHash H digestOffset)
      (.seq (.block (qArguments digestOffset destinationOffset H.D)) VG.Impl.Bignum.X86.copyBytes)) s fun t =>
      Spec.Rsa.bytesAt t.mem (dst.setWidth 64) H.D =
        ok.SH.H.hash (Spec.Sha256.bytesAt s.mem (data.setWidth 64) len) ∧
      Frame (hashAreas ok st digest scratch s ++ [⟨dst.setWidth 64, H.D⟩]) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s t := by
  refine WP.seq (WP.mono (seed_hash G R digestPosition) fun a ⟨A, RA, hashed⟩ => ?_)
  refine WP.seq (WP.mono (q_arguments (digestOffset := digestOffset) (candidateOffset := destinationOffset)
    (len := H.D) RA.scratch) fun b ⟨src, dest, count, memory, K⟩ => ?_)
  rw [digestPosition] at src
  rw [destinationPosition] at dest
  have sourceRead : InRegions (b.rd ++ b.wr) (digest.setWidth 64) H.D := by
    rw [K.2.1, K.2.2, A.rd, A.wr]
    obtain ⟨region, hr, hc⟩ := G.writable (digest.setWidth 64) H.D
      ⟨⟨digest.setWidth 64, H.F⟩, by simp, by simpa only [Region.Contains, BitVec.sub_self,
        BitVec.toNat_zero, Nat.zero_add] using ok.hDF⟩
    exact ⟨region, List.mem_append_right _ hr, hc⟩
  refine WP.mono (copyBuffers_ok ok.hD0 (by have := ok.hDF; have := ok.hF; omega)
    (by have := G.digest_fit; have := ok.hDF; omega) dstFit sourceRead
    (by rw [K.2.2, A.wr]; exact write) apart src dest count) fun t ⟨copied, _, _, FT, KT⟩ => ?_
  refine ⟨?_, ?_, ?_⟩
  · have copiedBytes := VG.Proof.Bignum.bytesAt_eq_of_read copied
    change Spec.Rsa.bytesAt t.mem (dst.setWidth 64) H.D = Spec.Rsa.bytesAt b.mem (digest.setWidth 64) H.D at copiedBytes
    rw [copiedBytes, memory]
    have take : (Spec.Sha256.bytesAt a.mem (digest.setWidth 64) H.F).take H.D =
        Spec.Rsa.bytesAt a.mem (digest.setWidth 64) H.D := by
      simp only [Spec.Sha256.bytesAt, Spec.Rsa.bytesAt, ← List.map_take, List.take_range, Nat.min_eq_left ok.hDF]
    rw [take] at hashed
    exact hashed
  · have first : Frame (hashAreas ok st digest scratch s ++ [⟨dst.setWidth 64, H.D⟩]) s.mem b.mem := by
      rw [memory]
      exact A.frame.mono (by intro region hr; exact List.mem_append_left _ hr)
    exact first.trans (FT.mono (by intro region hr; exact List.mem_append_right _ hr))
  · have KA : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s a := by
      refine ⟨?_, A.rd, A.wr⟩
      intro reg hr
      apply A.cs
      cases reg <;> simp_all [calleeSaved]
    exact (KA.trans (K.mono (by decide))).trans (KT.mono (by decide))

end VG.Proof.Dsa.X86.Generation
