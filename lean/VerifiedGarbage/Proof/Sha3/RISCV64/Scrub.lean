module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubSel
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sha3.RISCV64.Instances
public import VerifiedGarbage.Proof.Sha3.PostOut
import VerifiedGarbage.Proof.Sha3.RISCV64.Lit
import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
meta import VerifiedGarbage.Proof.Framework.RISCV64.ScrubSel
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Sha3.RISCV64.Instances
meta import VerifiedGarbage.Proof.Sha3.PostOut
meta import VerifiedGarbage.Proof.Sha3.RISCV64.Lit
meta import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Lit

/-!
# SHA-3 and SHAKE on RISC-V, without secret residue

Each instance's `absorb` and `finalize`, and SHAKE's `squeeze`, followed by
`Impl.Scrub.RISCV64.scrubTailSel` (`RISCV64.Scrub.withScrubSel`), which clears the
caller-saved registers and, of the stack its frames used, only the runs of
doublewords that the residue analysis (`RISCV64.rtaint`) finds may differ between
two runs: the permutation's two copies of the state (bytes 192 to 591 of its
frame, at the bottom of the window), and the frames still allocated when a
function stores through a pointer the analysis cannot place (the position in
the state, the output) — every function's state at `a0` is a buffer it knows. Their postconditions
read the memory on return only within their buffers
(`Proof/Sha3/PostOut.lean`).
-/

@[expose] public section

namespace VG.Proof.Sha3.RISCV64

open VG.RISCV64 VG.RISCV64.Scrub

theorem finalizeOut (H : Spec.Sha3.HashFn) (stack : Nat) (hlen : H.len < 2 ^ 64) :
    PostOut (Spec.Sha3.finalizeContract RISCV64.abi H stack) ((Spec.Sha3.finalizeSig H.len).retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha3.PostOut.finalizePost_out H 64 hlen)

theorem xofFinalizeOut (X : Spec.Sha3.Xof) (stack : Nat) :
    PostOut (Spec.Sha3.xofFinalizeContract RISCV64.abi X stack) (Spec.Sha3.xofFinalizeSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha3.PostOut.xofFinalizePost_out X 64)

theorem xofSqueezeOut (X : Spec.Sha3.Xof) (stack : Nat) :
    PostOut (Spec.Sha3.xofSqueezeContract RISCV64.abi X stack) (Spec.Sha3.xofSqueezeSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha3.PostOut.xofSqueezePost_out X)

/-- `vg_sha3_224_finalize`. -/
def finalizeSha3_224Reg : Registration Spec.Sha3.finalizeSha3_224Api RISCV64.target :=
  withScrubSel { code := Impl.Sha3.RISCV64.Instances.finalize Spec.Sha3.hashSha3_224.rate Spec.Sha3.hashSha3_224.len, verified := Proof.Sha3.RISCV64.Instances.finalize_sha3_224 } [(1200, [(24, 54), (140, 10)])]
    (finalizeOut Spec.Sha3.hashSha3_224 _ (by decide))
    (fun hfs hsz hrb => scrubSel_noResidue _ _ [(.a0, 25 * Elem.u64.size)] hfs hsz hrb (finalizeOut Spec.Sha3.hashSha3_224 _ (by decide)) (hbp_firstArray _ rfl)
      (Impl.Sha3.RISCV64.Instances.finalize Spec.Sha3.hashSha3_224.rate Spec.Sha3.hashSha3_224.len) 1200 0 rfl rfl rfl (by exact ⟨_, by taint_decide_ct⟩))

/-- `vg_sha3_256_finalize`. -/
def finalizeSha3_256Reg : Registration Spec.Sha3.finalizeSha3_256Api RISCV64.target :=
  withScrubSel { code := Impl.Sha3.RISCV64.Instances.finalize Spec.Sha3.hashSha3_256.rate Spec.Sha3.hashSha3_256.len, verified := Proof.Sha3.RISCV64.Instances.finalize_sha3_256 } [(1200, [(24, 54), (140, 10)])]
    (finalizeOut Spec.Sha3.hashSha3_256 _ (by decide))
    (fun hfs hsz hrb => scrubSel_noResidue _ _ [(.a0, 25 * Elem.u64.size)] hfs hsz hrb (finalizeOut Spec.Sha3.hashSha3_256 _ (by decide)) (hbp_firstArray _ rfl)
      (Impl.Sha3.RISCV64.Instances.finalize Spec.Sha3.hashSha3_256.rate Spec.Sha3.hashSha3_256.len) 1200 0 rfl rfl rfl (by exact ⟨_, by taint_decide_ct⟩))

/-- `vg_sha3_384_finalize`. -/
def finalizeSha3_384Reg : Registration Spec.Sha3.finalizeSha3_384Api RISCV64.target :=
  withScrubSel { code := Impl.Sha3.RISCV64.Instances.finalize Spec.Sha3.hashSha3_384.rate Spec.Sha3.hashSha3_384.len, verified := Proof.Sha3.RISCV64.Instances.finalize_sha3_384 } [(1200, [(24, 54), (140, 10)])]
    (finalizeOut Spec.Sha3.hashSha3_384 _ (by decide))
    (fun hfs hsz hrb => scrubSel_noResidue _ _ [(.a0, 25 * Elem.u64.size)] hfs hsz hrb (finalizeOut Spec.Sha3.hashSha3_384 _ (by decide)) (hbp_firstArray _ rfl)
      (Impl.Sha3.RISCV64.Instances.finalize Spec.Sha3.hashSha3_384.rate Spec.Sha3.hashSha3_384.len) 1200 0 rfl rfl rfl (by exact ⟨_, by taint_decide_ct⟩))

/-- `vg_sha3_512_finalize`. -/
def finalizeSha3_512Reg : Registration Spec.Sha3.finalizeSha3_512Api RISCV64.target :=
  withScrubSel { code := Impl.Sha3.RISCV64.Instances.finalize Spec.Sha3.hashSha3_512.rate Spec.Sha3.hashSha3_512.len, verified := Proof.Sha3.RISCV64.Instances.finalize_sha3_512 } [(1200, [(24, 54), (140, 10)])]
    (finalizeOut Spec.Sha3.hashSha3_512 _ (by decide))
    (fun hfs hsz hrb => scrubSel_noResidue _ _ [(.a0, 25 * Elem.u64.size)] hfs hsz hrb (finalizeOut Spec.Sha3.hashSha3_512 _ (by decide)) (hbp_firstArray _ rfl)
      (Impl.Sha3.RISCV64.Instances.finalize Spec.Sha3.hashSha3_512.rate Spec.Sha3.hashSha3_512.len) 1200 0 rfl rfl rfl (by exact ⟨_, by taint_decide_ct⟩))

/-- `vg_shake128_finalize`. -/
def finalizeShake128Reg : Registration Spec.Sha3.finalizeShake128Api RISCV64.target :=
  withScrubSel { code := Impl.Sha3.RISCV64.Instances.xofFinalize Spec.Sha3.xofShake128.rate, verified := Proof.Sha3.RISCV64.Instances.finalize_shake128 } [(1136, [(24, 50), (140, 2)])]
    (xofFinalizeOut Spec.Sha3.xofShake128 _)
    (fun hfs hsz hrb => scrubSel_noResidue _ _ [(.a0, 25 * Elem.u64.size)] hfs hsz hrb (xofFinalizeOut Spec.Sha3.xofShake128 _) (hbp_firstArray _ rfl)
      (Impl.Sha3.RISCV64.Instances.xofFinalize Spec.Sha3.xofShake128.rate) 1136 0 rfl rfl rfl (by exact ⟨_, by taint_decide_ct⟩))

/-- `vg_shake128_squeeze`. -/
def squeezeShake128Reg : Registration Spec.Sha3.squeezeShake128Api RISCV64.target :=
  withScrubSel { code := Impl.Sha3.RISCV64.Instances.xofSqueeze Spec.Sha3.xofShake128.rate, verified := Proof.Sha3.RISCV64.Instances.squeeze_shake128 } [(1168, [(24, 50), (140, 6)])]
    (xofSqueezeOut Spec.Sha3.xofShake128 _)
    (fun hfs hsz hrb => scrubSel_noResidue _ _ [(.a0, 25 * Elem.u64.size)] hfs hsz hrb (xofSqueezeOut Spec.Sha3.xofShake128 _) (hbp_firstArray _ rfl)
      (Impl.Sha3.RISCV64.Instances.xofSqueeze Spec.Sha3.xofShake128.rate) 1168 64 rfl rfl rfl (by exact ⟨_, by taint_decide_ct⟩))

/-- `vg_shake256_finalize`. -/
def finalizeShake256Reg : Registration Spec.Sha3.finalizeShake256Api RISCV64.target :=
  withScrubSel { code := Impl.Sha3.RISCV64.Instances.xofFinalize Spec.Sha3.xofShake256.rate, verified := Proof.Sha3.RISCV64.Instances.finalize_shake256 } [(1136, [(24, 50), (140, 2)])]
    (xofFinalizeOut Spec.Sha3.xofShake256 _)
    (fun hfs hsz hrb => scrubSel_noResidue _ _ [(.a0, 25 * Elem.u64.size)] hfs hsz hrb (xofFinalizeOut Spec.Sha3.xofShake256 _) (hbp_firstArray _ rfl)
      (Impl.Sha3.RISCV64.Instances.xofFinalize Spec.Sha3.xofShake256.rate) 1136 0 rfl rfl rfl (by exact ⟨_, by taint_decide_ct⟩))

/-- `vg_shake256_squeeze`. -/
def squeezeShake256Reg : Registration Spec.Sha3.squeezeShake256Api RISCV64.target :=
  withScrubSel { code := Impl.Sha3.RISCV64.Instances.xofSqueeze Spec.Sha3.xofShake256.rate, verified := Proof.Sha3.RISCV64.Instances.squeeze_shake256 } [(1168, [(24, 50), (140, 6)])]
    (xofSqueezeOut Spec.Sha3.xofShake256 _)
    (fun hfs hsz hrb => scrubSel_noResidue _ _ [(.a0, 25 * Elem.u64.size)] hfs hsz hrb (xofSqueezeOut Spec.Sha3.xofShake256 _) (hbp_firstArray _ rfl)
      (Impl.Sha3.RISCV64.Instances.xofSqueeze Spec.Sha3.xofShake256.rate) 1168 64 rfl rfl rfl (by exact ⟨_, by taint_decide_ct⟩))


/-! ## `absorb` -/

theorem absorbOut (rate stack : Nat) :
    PostOut (Spec.Sha3.updateContract RISCV64.abi rate stack) (Spec.Sha3.updateSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha3.PostOut.updatePost_out rate 64)

/-- `vg_sha3_224_update`. -/
def absorbSha3_224Reg : Registration Spec.Sha3.updateSha3_224Api RISCV64.target :=
  withScrubSel { code := Impl.Sha3.RISCV64.Instances.absorb Spec.Sha3.hashSha3_224.rate, verified := Proof.Sha3.RISCV64.Instances.absorb_sha3_224 } [(1168, [(24, 50), (140, 6)])]
    (absorbOut Spec.Sha3.hashSha3_224.rate _)
    (fun hfs hsz hrb => scrubSel_noResidue _ _ [(.a0, 25 * Elem.u64.size)] hfs hsz hrb (absorbOut Spec.Sha3.hashSha3_224.rate _) (hbp_firstArray _ rfl)
      (Impl.Sha3.RISCV64.Instances.absorb Spec.Sha3.hashSha3_224.rate) 1168 64 rfl rfl rfl (by exact ⟨_, by taint_decide_ct⟩))

/-- `vg_sha3_256_update`. -/
def absorbSha3_256Reg : Registration Spec.Sha3.updateSha3_256Api RISCV64.target :=
  withScrubSel { code := Impl.Sha3.RISCV64.Instances.absorb Spec.Sha3.hashSha3_256.rate, verified := Proof.Sha3.RISCV64.Instances.absorb_sha3_256 } [(1168, [(24, 50), (140, 6)])]
    (absorbOut Spec.Sha3.hashSha3_256.rate _)
    (fun hfs hsz hrb => scrubSel_noResidue _ _ [(.a0, 25 * Elem.u64.size)] hfs hsz hrb (absorbOut Spec.Sha3.hashSha3_256.rate _) (hbp_firstArray _ rfl)
      (Impl.Sha3.RISCV64.Instances.absorb Spec.Sha3.hashSha3_256.rate) 1168 64 rfl rfl rfl (by exact ⟨_, by taint_decide_ct⟩))

/-- `vg_sha3_384_update`. -/
def absorbSha3_384Reg : Registration Spec.Sha3.updateSha3_384Api RISCV64.target :=
  withScrubSel { code := Impl.Sha3.RISCV64.Instances.absorb Spec.Sha3.hashSha3_384.rate, verified := Proof.Sha3.RISCV64.Instances.absorb_sha3_384 } [(1168, [(24, 50), (140, 6)])]
    (absorbOut Spec.Sha3.hashSha3_384.rate _)
    (fun hfs hsz hrb => scrubSel_noResidue _ _ [(.a0, 25 * Elem.u64.size)] hfs hsz hrb (absorbOut Spec.Sha3.hashSha3_384.rate _) (hbp_firstArray _ rfl)
      (Impl.Sha3.RISCV64.Instances.absorb Spec.Sha3.hashSha3_384.rate) 1168 64 rfl rfl rfl (by exact ⟨_, by taint_decide_ct⟩))

/-- `vg_sha3_512_update`. -/
def absorbSha3_512Reg : Registration Spec.Sha3.updateSha3_512Api RISCV64.target :=
  withScrubSel { code := Impl.Sha3.RISCV64.Instances.absorb Spec.Sha3.hashSha3_512.rate, verified := Proof.Sha3.RISCV64.Instances.absorb_sha3_512 } [(1168, [(24, 50), (140, 6)])]
    (absorbOut Spec.Sha3.hashSha3_512.rate _)
    (fun hfs hsz hrb => scrubSel_noResidue _ _ [(.a0, 25 * Elem.u64.size)] hfs hsz hrb (absorbOut Spec.Sha3.hashSha3_512.rate _) (hbp_firstArray _ rfl)
      (Impl.Sha3.RISCV64.Instances.absorb Spec.Sha3.hashSha3_512.rate) 1168 64 rfl rfl rfl (by exact ⟨_, by taint_decide_ct⟩))

/-- `vg_shake128_update`. -/
def absorbShake128Reg : Registration Spec.Sha3.updateShake128Api RISCV64.target :=
  withScrubSel { code := Impl.Sha3.RISCV64.Instances.absorb Spec.Sha3.xofShake128.rate, verified := Proof.Sha3.RISCV64.Instances.absorb_shake128 } [(1168, [(24, 50), (140, 6)])]
    (absorbOut Spec.Sha3.xofShake128.rate _)
    (fun hfs hsz hrb => scrubSel_noResidue _ _ [(.a0, 25 * Elem.u64.size)] hfs hsz hrb (absorbOut Spec.Sha3.xofShake128.rate _) (hbp_firstArray _ rfl)
      (Impl.Sha3.RISCV64.Instances.absorb Spec.Sha3.xofShake128.rate) 1168 64 rfl rfl rfl (by exact ⟨_, by taint_decide_ct⟩))

end VG.Proof.Sha3.RISCV64
