module

import VerifiedGarbage.Proof.Bignum.Arm.PcHead
public import VerifiedGarbage.Proof.Bignum.Arm.PcStack
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Bignum.Arm.SetupFrame
public import VerifiedGarbage.Proof.Bignum.Arm.Precompute
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeOut
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeCT
public import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeState
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Bignum.Arm.R2Kernel
import VerifiedGarbage.Proof.Bignum.Arm.StackCT

/-! ### `Bignum.Arm.PublicPrecomputeKernel`, which this module and modules that import it used -/

section

/-! ### `Bignum.Arm.PrecomputePublicCT`, which this module and modules that import it used -/

section

/-! Public setup keeps the imported modulus public when selecting an R-squared kernel. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt)

def PublicR2Timing (code : Prog isa) : Prop := ∀ {base : BitVec 32} {len w M : Nat},
  128 * w < 2 ^ 32 → RelCT isa (fun s t =>
    (ArithmeticReady base len w s ∧ numAt s.mem (State.addr base) w 0 = M) ∧
    (ArithmeticReady base len w t ∧ numAt t.mem (State.addr base) w 0 = M) ∧ s.sp = t.sp)
    code (fun _ _ => True)

theorem precomputePublic_ct (kernel : R2Kernel) (timing : PublicR2Timing kernel.code)
    {base src : BitVec 32} {len w k : Nat} {nb : List Byte} (countFits : 128 * w < 2 ^ 32) :
    RelCT isa (fun s t =>
      (PrecomputeInput base src len w k s ∧ Spec.Rsa.bytesAt s.mem (State.addr src) k = nb) ∧
      (PrecomputeInput base src len w k t ∧ Spec.Rsa.bytesAt t.mem (State.addr src) k = nb) ∧ s.sp = t.sp)
      (precomputeWith kernel.code) (fun _ _ => True) := by
  let N := Spec.Rsa.os2ip nb
  let P := fun s : State => PrecomputeInput base src len w k s ∧ Spec.Rsa.bytesAt s.mem (State.addr src) k = nb
  let Q := fun s : State => PrecomputeModulus base len w s ∧ numAt s.mem (State.addr base) w 0 = N
  let R := fun s : State => ArithmeticReady base len w s ∧ numAt s.mem (State.addr base) w 0 = N
  have imported := (relCT_keep_sp ((importModulus_ct (base := base) (src := src) (len := len) (w := w) (k := k)).mono
    (P' := fun (s t : State) => P s ∧ P t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h)) (fun _ _ h => h.2.2)).wp
    (fun s t h =>
      ⟨WP.mono (importModulus_ready_value s h.1.1) (fun u j => (⟨j.1, by rw [j.2, h.1.2]⟩ : Q u)),
       WP.mono (importModulus_ready_value t h.2.1.1) (fun u j => (⟨j.1, by rw [j.2, h.2.1.2]⟩ : Q u))⟩)
  have inverse := (relCT_keep_sp ((precomputeInverse_ct (base := base) (len := len) (w := w)).mono
    (P' := fun (s t : State) => s.sp = t.sp ∧ Q s ∧ Q t)
    (fun _ _ h => ⟨h.2.1.1, h.2.2.1⟩) (fun _ _ h => h)) (fun _ _ h => h.1)).wp
    (fun s t h =>
      ⟨WP.mono (precomputeInverse_ready_value s h.2.1.1) (fun u j => (⟨j.1, j.2.trans h.2.1.2⟩ : R u)),
       WP.mono (precomputeInverse_ready_value t h.2.2.1) (fun u j => (⟨j.1, j.2.trans h.2.2.2⟩ : R u))⟩)
  have tail := inverse.seq ((timing (M := N) countFits).mono
    (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ h => h))
  exact imported.seq tail

end VG.Proof.Bignum.Arm

end

end

/-! Public-key setup callers share one code and proof interface. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

structure PublicPrecomputeKernel where
  code : Prog isa
  correct : PrecomputeLaw code
  ct : ∀ {base src : BitVec 32} {len w k : Nat} {nb : List Byte},
    128 * w < 2 ^ 32 → RelCT isa (fun s t =>
      (PrecomputeInput base src len w k s ∧ Spec.Rsa.bytesAt s.mem (State.addr src) k = nb) ∧
      (PrecomputeInput base src len w k t ∧ Spec.Rsa.bytesAt t.mem (State.addr src) k = nb) ∧ s.sp = t.sp)
      code (fun _ _ => True)

def baselinePublicPrecomputeKernel : PublicPrecomputeKernel where
  code := precompute
  correct := precompute_ok
  ct := by
    intro base src len w k nb fits
    exact (precompute_ct fits).mono (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h)

end VG.Proof.Bignum.Arm

end

end

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
  have inputZ := rsa_bytes_frame frameZ (by omega_using [hk'] : k < 2 ^ 64)
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact srcSep)
  have stackReadZ : InRegions (z.rd ++ z.wr) (State.addr z.sp) 4 := by
    simpa only [VG.Proof.Mont.off, BitVec.add_zero] using stackZ.read (d := 0) (by decide)
  have stackSepZ := stackZ.separate.sub_left (Region.sub_prefix (show 4 ≤ 16 by decide))
  rw [WP.seq_iff]
  refine WP.mono (kernel.correct z (ws.congr rz.wr) (by rw [memZ]; exact layoutV)
    (by rw [memZ]; exact widthV) (by omega_using [hk]) bytesFit srcFit
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
