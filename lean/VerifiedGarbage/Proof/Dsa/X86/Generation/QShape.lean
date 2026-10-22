module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.QShapeEnds
public import VerifiedGarbage.Proof.Dsa.Generation.QShapeMemory
public import VerifiedGarbage.Proof.Bignum.X86.CopyRead
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Digest-to-candidate shaping reuses the existing byte copy and shared mathematics -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Bignum.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Impl.Mont.X86 VG.Impl.Dsa.X86.Generation

theorem q_shape {s : State} {src dst : BitVec 32} {bs : List Byte}
    (hn : 2 ≤ bs.length) (small : bs.length < 2 ^ 32)
    (srcFit : src.toNat + bs.length ≤ 2 ^ 32) (dstFit : dst.toNat + bs.length ≤ 2 ^ 32)
    (source : s.gpr .esi = src) (dest : s.gpr .ebx = dst)
    (count : s.gpr .ecx = BitVec.ofNat 32 bs.length)
    (read : InRegions (s.rd ++ s.wr) (byteAddr src) bs.length)
    (write : InRegions s.wr (byteAddr dst) bs.length)
    (apart : Region.Disjoint ⟨byteAddr src, bs.length⟩ ⟨byteAddr dst, bs.length⟩)
    (bytes : ∀ i < bs.length, s.mem (off (byteAddr src) i) = bs.getD i 0) :
    WP isa qShape s fun t =>
      Spec.Rsa.bytesAt t.mem (byteAddr dst) bs.length =
        VG.Proof.Ffdh.ParameterCandidate.shapedOctets bs 7 ∧
      Frame [⟨byteAddr dst, bs.length⟩] s.mem t.mem ∧ Keeps [.eax, .ebx, .esi, .ecx, .ebp] s t := by
  unfold qShape
  refine WP.seq (wp_movS rfl fun u U _ => WP.block_nil ?_)
  have readU : InRegions (u.rd ++ u.wr) (byteAddr src) bs.length := by rw [U.rd, U.wr]; exact read
  have writeU : InRegions u.wr (byteAddr dst) bs.length := by rw [U.wr]; exact write
  refine WP.seq (WP.mono (copyBuffers_ok (s := u) (by omega) small srcFit dstFit readU writeU apart
    (by rw [U.other .esi (by decide)]; exact source)
    (by rw [U.other .ebx (by decide)]; exact dest)
    (by rw [U.other .ecx (by decide)]; exact count)) ?_)
  rintro v ⟨packed, past, _, frame, K⟩
  have first : v.gpr .ebp = dst := by rw [K.1 .ebp (by decide), U.gpr, dest]
  have copied (i : Nat) (hi : i < bs.length) : v.mem (off (byteAddr dst) i) = bs.getD i 0 := by
    have eq := congrArg (fun b : BitVec (8 * bs.length) => b.extractLsb' (8 * i) 8) packed
    rw [Mem.extractLsb'_read _ _ hi, Mem.extractLsb'_read _ _ hi, U.mem] at eq
    exact eq.trans (bytes i hi)
  have wv (i : Nat) (hi : i < bs.length) : InRegions v.wr (off (byteAddr dst) i) 1 := by
    rw [K.2.2]
    obtain ⟨r, hr, hc⟩ := writeU
    refine ⟨r, hr, hc.byte ?_⟩
    rw [off, BitVec.add_comm (byteAddr dst) (BitVec.ofNat 64 i), BitVec.add_sub_cancel, BitVec.toNat_ofNat]
    omega
  have rv (i : Nat) (hi : i < bs.length) : InRegions (v.rd ++ v.wr) (off (byteAddr dst) i) 1 := by
    obtain ⟨r, hr, hc⟩ := wv i hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (q_shape_ends hn dstFit first past (by simpa only [off, BitVec.add_zero] using rv 0 (by omega))
    (rv _ (by omega)) (by simpa only [off, BitVec.add_zero] using wv 0 (by omega)) (wv _ (by omega))) ?_
  rintro t ⟨memory, L⟩
  refine ⟨?_, ?_, ((U.keeps.mono (by decide)).trans (K.mono (by decide))).trans (L.mono (by decide))⟩
  · rw [memory]
    exact VG.Proof.Dsa.Generation.qShape_memory hn (by omega) copied
  · have frame0 : Frame [⟨byteAddr dst, bs.length⟩] s.mem v.mem := by
      rw [U.mem] at frame
      exact frame
    rw [memory]
    refine (frame0.writeW (r := ⟨byteAddr dst, bs.length⟩) (by simp) _ ?_).writeW
      (r := ⟨byteAddr dst, bs.length⟩) (by simp) _ ?_
    · simpa only [off, BitVec.add_zero] using
        Offset.contains_base (byteAddr dst) (d := 0) (n := 1) (k := bs.length) (by omega) (by decide)
    · exact Offset.contains_base _ (by omega) (by omega)

end VG.Proof.Dsa.X86.Generation
