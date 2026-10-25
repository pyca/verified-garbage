module

public import VerifiedGarbage.Proof.Bignum.Arm.PublicPrecomputeKernel

import VerifiedGarbage.Proof.Bignum.Arm.PcHead
public import VerifiedGarbage.Proof.Bignum.Arm.PcStack
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Bignum.Arm.SetupFrame
import VerifiedGarbage.Proof.Bignum.Arm.Precompute
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeOut
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Block

/-! # Successful public RSA precomputation, from bytes to the output buffer -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

theorem pcValid_ok (s : State) {base dst src : BitVec 32} {len k : Nat}
    (ws : Workspace s base (8 * len)) (stack : PcStack base dst src len k s)
    (hk : 64 ≤ k) (hk' : k ≤ 1024) (space : Spec.Rsa.publicScratchWords k ≤ len)
    (srcFit : src.toNat + k ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (State.addr src) k)
    (srcSep : Region.Disjoint ⟨State.addr src, k⟩ ⟨State.addr base, 8 * len⟩)
    (dstFit : dst.toNat + 16 * Spec.Rsa.modulusWords k ≤ 2 ^ 32)
    (write : InRegions s.wr (State.addr dst) (16 * Spec.Rsa.modulusWords k))
    (dstSep : Region.Disjoint ⟨State.addr base, 8 * len⟩ ⟨State.addr dst, 16 * Spec.Rsa.modulusWords k⟩)
    (ptr : s.gpr .r0 = base) (count : s.gpr .r6 = BitVec.ofNat 32 k)
    (valid : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k)) k = true)
    (kernel : PublicPrecomputeKernel := baselinePublicPrecomputeKernel) : WP isa (PcFn.validWith kernel.code) s fun t =>
      t.gpr .r0 = 1 ∧ Spec.Rsa.wordsAt t.mem (State.addr dst) (2 * Spec.Rsa.modulusWords k) =
        Spec.Rsa.toWords (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k)) (Spec.Rsa.modulusWords k) ++
        Spec.Rsa.toWords (2 ^ (128 * Spec.Rsa.modulusWords k) %
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k)) (Spec.Rsa.modulusWords k) ∧
      Frame [⟨State.addr base, 8 * len⟩, ⟨State.addr dst, 16 * Spec.Rsa.modulusWords k⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  obtain ⟨hw, hw', fits, bytesFit, countFit⟩ := pc_dimensions hk hk' space
  obtain ⟨odd, large, _⟩ := VG.Proof.Bignum.valid_facts valid hk
  rw [PcFn.validWith, WP.seq_iff]
  refine WP.mono (pcHead_ok s hk' count) ?_
  rintro u ⟨limbs, zero, memU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (setup_frame_ok u (ws.congr restU.wr) hw hw' fits
    ((restU.gpr .r0 (by decide)).trans ptr) limbs zero) ?_
  rintro v ⟨layoutV, widthV, ptrV, frameV, restV⟩
  rw [memU] at frameV
  have rv : Rest roundClobbers s v := (restU.mono (by decide)).trans restV
  have stackV := stack.after_workspace frameV rv
  rw [WP.seq_iff]
  refine WP.mono (pcInputs_ok v stackV) ?_
  rintro z ⟨sourceZ, countZ, memZ, restZ⟩
  have rz : Rest roundClobbers s z := rv.trans (restZ.mono (by decide))
  have frameZ : Frame [⟨State.addr base, 8 * len⟩] s.mem z.mem := by rw [memZ]; exact frameV
  have stackZ := stack.after_workspace frameZ rz
  have inputZ := rsa_bytes_frame frameZ (by omega : k < 2 ^ 64)
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact srcSep)
  have stackReadZ : InRegions (z.rd ++ z.wr) (State.addr z.sp) 4 := by
    simpa only [VG.Proof.Mont.off, BitVec.add_zero] using stackZ.read (d := 0) (by decide)
  have stackSepZ := stackZ.separate.sub_left (Region.sub_prefix (show 4 ≤ 16 by decide))
  rw [WP.seq_iff]
  refine WP.mono (kernel.correct z (ws.congr rz.wr) (by rw [memZ]; exact layoutV)
    (by rw [memZ]; exact widthV) (by omega) bytesFit srcFit
    (by rw [rz.rd, rz.wr]; exact read) srcSep ((restZ.gpr .r0 (by decide)).trans ptrV)
    sourceZ countZ stackReadZ stackSepZ stackZ.savedBase
    (by rw [inputZ]; exact large) (by rw [inputZ]; exact odd) countFit) ?_
  rintro a ⟨ready, modulus, r2value, frameA, restA⟩
  rw [inputZ] at modulus r2value
  have ra := rz.trans restA
  have frameSA := frameZ.trans frameA
  have stackA := stack.after_workspace frameSA ra
  rw [WP.seq_iff]
  refine WP.mono (pcOutput_ok a stackA) ?_
  rintro b ⟨outputB, memB, restB⟩
  have rb : Rest roundClobbers s b := ra.trans (restB.mono (by decide))
  refine WP.mono (precomputeOut_ok b (ws.congr rb.wr) (by rw [memB]; exact ready.layout)
    (by rw [memB]; exact ready.width) dstFit (by rw [rb.wr]; exact write) dstSep
    ((restB.gpr .r0 (by decide)).trans ready.ptr) outputB) ?_
  rintro t ⟨result, words, frameT, restT⟩
  rw [memB, modulus, r2value] at words
  rw [memB] at frameT
  exact ⟨result, words, (frameSA.mono (by simp)).trans (frameT.mono (by simp)), rb.trans restT⟩

end VG.Proof.Bignum.Arm
