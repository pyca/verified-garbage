module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubSel
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Impl.Sha3.RISCV64.Instances
public import VerifiedGarbage.Spec.Sha3.Instances
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sha3.RISCV64.Instances
public import VerifiedGarbage.Proof.Sha3.PostOut
import VerifiedGarbage.Proof.Sha3.RISCV64.Lit
import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
meta import VerifiedGarbage.Proof.Framework.RISCV64.ScrubSel
meta import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
meta import VerifiedGarbage.Impl.Sha3.RISCV64.Instances
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Sha3.RISCV64.Instances
meta import VerifiedGarbage.Proof.Sha3.PostOut
meta import VerifiedGarbage.Proof.Sha3.RISCV64.Lit
meta import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Lit

/-!
# SHA-3 and SHAKE on RISC-V, without secret residue

Each instance's `absorb` and `finalize`, and SHAKE's `squeeze`, as emitted
(`Impl.Sha3.RISCV64.Fn`): the function followed by
`Impl.Scrub.RISCV64.scrubTailSel`, which clears the caller-saved registers
and, of the stack its frames used, only the runs of doublewords that the
residue analysis (`RISCV64.rtaint`) finds may differ between two runs: the
permutation's two copies of the state (bytes 192 to 591 of its frame, at the
bottom of the window), and the frames still allocated when a function stores
through a pointer the analysis cannot place (the position in the state, the
output) — every function's state at `a0` is a buffer it knows. Each theorem
below states that one meets its contract in constant time and returns
without secret residue (`VerifiedScrubbed`, by
`RISCV64.Scrub.verifiedScrubbedSelT`, whose analysis the kernel evaluates
here), which is what its registration binds. Their postconditions read the
memory on return only within their buffers (`Proof/Sha3/PostOut.lean`).
-/

@[expose] public section

namespace VG.Proof.Sha3.RISCV64

open VG.RISCV64 VG.RISCV64.Scrub VG.Spec.Sha3

theorem finalizeOut (H : HashFn) (stack : Nat) (hlen : H.len < 2 ^ 64) :
    PostOut (finalizeContract RISCV64.abi H stack) ((finalizeSig H.len).retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha3.PostOut.finalizePost_out H 64 hlen)

theorem xofFinalizeOut (X : Xof) (stack : Nat) :
    PostOut (xofFinalizeContract RISCV64.abi X stack) (xofFinalizeSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha3.PostOut.xofFinalizePost_out X 64)

theorem xofSqueezeOut (X : Xof) (stack : Nat) :
    PostOut (xofSqueezeContract RISCV64.abi X stack) (xofSqueezeSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha3.PostOut.xofSqueezePost_out X)

theorem absorbOut (rate stack : Nat) :
    PostOut (updateContract RISCV64.abi rate stack) (updateSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha3.PostOut.updatePost_out rate 64)

/-- `vg_sha3_224_update` as emitted (`Impl.Sha3.RISCV64.Fn.update`) meets its contract in
constant time and returns without secret residue. -/
theorem update_sha3_224_scrubbed :
    VerifiedScrubbed target (Impl.Sha3.RISCV64.Fn.update hashSha3_224.rate)
      (updateContract RISCV64.abi hashSha3_224.rate 1168) 64 :=
  verifiedScrubbedSelT (api := updateSha3_224Api) (W := 1168)
    { code := Impl.Sha3.RISCV64.Instances.absorb hashSha3_224.rate,
      verified := Proof.Sha3.RISCV64.Instances.absorb_sha3_224 }
    _ [(.a0, 25 * Elem.u64.size)] (absorbOut _ _) (by lit_decide) (hbp_firstArray _ rfl)
    ⟨_, by taint_decide_ct⟩

/-- `vg_sha3_256_update` as emitted (`Impl.Sha3.RISCV64.Fn.update`) meets its contract in
constant time and returns without secret residue. -/
theorem update_sha3_256_scrubbed :
    VerifiedScrubbed target (Impl.Sha3.RISCV64.Fn.update hashSha3_256.rate)
      (updateContract RISCV64.abi hashSha3_256.rate 1168) 64 :=
  verifiedScrubbedSelT (api := updateSha3_256Api) (W := 1168)
    { code := Impl.Sha3.RISCV64.Instances.absorb hashSha3_256.rate,
      verified := Proof.Sha3.RISCV64.Instances.absorb_sha3_256 }
    _ [(.a0, 25 * Elem.u64.size)] (absorbOut _ _) (by lit_decide) (hbp_firstArray _ rfl)
    ⟨_, by taint_decide_ct⟩

/-- `vg_sha3_384_update` as emitted (`Impl.Sha3.RISCV64.Fn.update`) meets its contract in
constant time and returns without secret residue. -/
theorem update_sha3_384_scrubbed :
    VerifiedScrubbed target (Impl.Sha3.RISCV64.Fn.update hashSha3_384.rate)
      (updateContract RISCV64.abi hashSha3_384.rate 1168) 64 :=
  verifiedScrubbedSelT (api := updateSha3_384Api) (W := 1168)
    { code := Impl.Sha3.RISCV64.Instances.absorb hashSha3_384.rate,
      verified := Proof.Sha3.RISCV64.Instances.absorb_sha3_384 }
    _ [(.a0, 25 * Elem.u64.size)] (absorbOut _ _) (by lit_decide) (hbp_firstArray _ rfl)
    ⟨_, by taint_decide_ct⟩

/-- `vg_sha3_512_update` as emitted (`Impl.Sha3.RISCV64.Fn.update`) meets its contract in
constant time and returns without secret residue. -/
theorem update_sha3_512_scrubbed :
    VerifiedScrubbed target (Impl.Sha3.RISCV64.Fn.update hashSha3_512.rate)
      (updateContract RISCV64.abi hashSha3_512.rate 1168) 64 :=
  verifiedScrubbedSelT (api := updateSha3_512Api) (W := 1168)
    { code := Impl.Sha3.RISCV64.Instances.absorb hashSha3_512.rate,
      verified := Proof.Sha3.RISCV64.Instances.absorb_sha3_512 }
    _ [(.a0, 25 * Elem.u64.size)] (absorbOut _ _) (by lit_decide) (hbp_firstArray _ rfl)
    ⟨_, by taint_decide_ct⟩

/-- `vg_shake128_update` as emitted (`Impl.Sha3.RISCV64.Fn.update`) meets its contract in
constant time and returns without secret residue. -/
theorem update_shake128_scrubbed :
    VerifiedScrubbed target (Impl.Sha3.RISCV64.Fn.update xofShake128.rate)
      (updateContract RISCV64.abi xofShake128.rate 1168) 64 :=
  verifiedScrubbedSelT (api := updateShake128Api) (W := 1168)
    { code := Impl.Sha3.RISCV64.Instances.absorb xofShake128.rate,
      verified := Proof.Sha3.RISCV64.Instances.absorb_shake128 }
    _ [(.a0, 25 * Elem.u64.size)] (absorbOut _ _) (by lit_decide) (hbp_firstArray _ rfl)
    ⟨_, by taint_decide_ct⟩

/-- `vg_sha3_224_finalize` as emitted (`Impl.Sha3.RISCV64.Fn.finalize`) meets its contract in
constant time and returns without secret residue. -/
theorem finalize_sha3_224_scrubbed :
    VerifiedScrubbed target (Impl.Sha3.RISCV64.Fn.finalize hashSha3_224.rate hashSha3_224.len)
      (finalizeContract RISCV64.abi hashSha3_224 (1168 + 32)) 0 :=
  verifiedScrubbedSelT (api := finalizeSha3_224Api) (W := 1200)
    { code := Impl.Sha3.RISCV64.Instances.finalize hashSha3_224.rate hashSha3_224.len,
      verified := Proof.Sha3.RISCV64.Instances.finalize_sha3_224 }
    _ [(.a0, 25 * Elem.u64.size)] (finalizeOut hashSha3_224 _ (by decide)) (by lit_decide)
    (hbp_firstArray _ rfl) ⟨_, by taint_decide_ct⟩

/-- `vg_sha3_256_finalize` as emitted (`Impl.Sha3.RISCV64.Fn.finalize`) meets its contract in
constant time and returns without secret residue. -/
theorem finalize_sha3_256_scrubbed :
    VerifiedScrubbed target (Impl.Sha3.RISCV64.Fn.finalize hashSha3_256.rate hashSha3_256.len)
      (finalizeContract RISCV64.abi hashSha3_256 (1168 + 32)) 0 :=
  verifiedScrubbedSelT (api := finalizeSha3_256Api) (W := 1200)
    { code := Impl.Sha3.RISCV64.Instances.finalize hashSha3_256.rate hashSha3_256.len,
      verified := Proof.Sha3.RISCV64.Instances.finalize_sha3_256 }
    _ [(.a0, 25 * Elem.u64.size)] (finalizeOut hashSha3_256 _ (by decide)) (by lit_decide)
    (hbp_firstArray _ rfl) ⟨_, by taint_decide_ct⟩

/-- `vg_sha3_384_finalize` as emitted (`Impl.Sha3.RISCV64.Fn.finalize`) meets its contract in
constant time and returns without secret residue. -/
theorem finalize_sha3_384_scrubbed :
    VerifiedScrubbed target (Impl.Sha3.RISCV64.Fn.finalize hashSha3_384.rate hashSha3_384.len)
      (finalizeContract RISCV64.abi hashSha3_384 (1168 + 32)) 0 :=
  verifiedScrubbedSelT (api := finalizeSha3_384Api) (W := 1200)
    { code := Impl.Sha3.RISCV64.Instances.finalize hashSha3_384.rate hashSha3_384.len,
      verified := Proof.Sha3.RISCV64.Instances.finalize_sha3_384 }
    _ [(.a0, 25 * Elem.u64.size)] (finalizeOut hashSha3_384 _ (by decide)) (by lit_decide)
    (hbp_firstArray _ rfl) ⟨_, by taint_decide_ct⟩

/-- `vg_sha3_512_finalize` as emitted (`Impl.Sha3.RISCV64.Fn.finalize`) meets its contract in
constant time and returns without secret residue. -/
theorem finalize_sha3_512_scrubbed :
    VerifiedScrubbed target (Impl.Sha3.RISCV64.Fn.finalize hashSha3_512.rate hashSha3_512.len)
      (finalizeContract RISCV64.abi hashSha3_512 (1168 + 32)) 0 :=
  verifiedScrubbedSelT (api := finalizeSha3_512Api) (W := 1200)
    { code := Impl.Sha3.RISCV64.Instances.finalize hashSha3_512.rate hashSha3_512.len,
      verified := Proof.Sha3.RISCV64.Instances.finalize_sha3_512 }
    _ [(.a0, 25 * Elem.u64.size)] (finalizeOut hashSha3_512 _ (by decide)) (by lit_decide)
    (hbp_firstArray _ rfl) ⟨_, by taint_decide_ct⟩

/-- `vg_shake128_finalize` as emitted (`Impl.Sha3.RISCV64.Fn.xofFinalize`) meets its contract in
constant time and returns without secret residue. -/
theorem finalize_shake128_scrubbed :
    VerifiedScrubbed target (Impl.Sha3.RISCV64.Fn.xofFinalize xofShake128.rate)
      (xofFinalizeContract RISCV64.abi xofShake128 1136) 0 :=
  verifiedScrubbedSelT (api := finalizeShake128Api) (W := 1136)
    { code := Impl.Sha3.RISCV64.Instances.xofFinalize xofShake128.rate,
      verified := Proof.Sha3.RISCV64.Instances.finalize_shake128 }
    _ [(.a0, 25 * Elem.u64.size)] (xofFinalizeOut xofShake128 _) (by lit_decide) (hbp_firstArray _ rfl)
    ⟨_, by taint_decide_ct⟩

/-- `vg_shake128_squeeze` as emitted (`Impl.Sha3.RISCV64.Fn.xofSqueeze`) meets its contract in
constant time and returns without secret residue. -/
theorem squeeze_shake128_scrubbed :
    VerifiedScrubbed target (Impl.Sha3.RISCV64.Fn.xofSqueeze xofShake128.rate)
      (xofSqueezeContract RISCV64.abi xofShake128 1168) 64 :=
  verifiedScrubbedSelT (api := squeezeShake128Api) (W := 1168)
    { code := Impl.Sha3.RISCV64.Instances.xofSqueeze xofShake128.rate,
      verified := Proof.Sha3.RISCV64.Instances.squeeze_shake128 }
    _ [(.a0, 25 * Elem.u64.size)] (xofSqueezeOut xofShake128 _) (by lit_decide) (hbp_firstArray _ rfl)
    ⟨_, by taint_decide_ct⟩

/-- `vg_shake256_finalize` as emitted (`Impl.Sha3.RISCV64.Fn.xofFinalize`) meets its contract in
constant time and returns without secret residue. -/
theorem finalize_shake256_scrubbed :
    VerifiedScrubbed target (Impl.Sha3.RISCV64.Fn.xofFinalize xofShake256.rate)
      (xofFinalizeContract RISCV64.abi xofShake256 1136) 0 :=
  verifiedScrubbedSelT (api := finalizeShake256Api) (W := 1136)
    { code := Impl.Sha3.RISCV64.Instances.xofFinalize xofShake256.rate,
      verified := Proof.Sha3.RISCV64.Instances.finalize_shake256 }
    _ [(.a0, 25 * Elem.u64.size)] (xofFinalizeOut xofShake256 _) (by lit_decide) (hbp_firstArray _ rfl)
    ⟨_, by taint_decide_ct⟩

/-- `vg_shake256_squeeze` as emitted (`Impl.Sha3.RISCV64.Fn.xofSqueeze`) meets its contract in
constant time and returns without secret residue. -/
theorem squeeze_shake256_scrubbed :
    VerifiedScrubbed target (Impl.Sha3.RISCV64.Fn.xofSqueeze xofShake256.rate)
      (xofSqueezeContract RISCV64.abi xofShake256 1168) 64 :=
  verifiedScrubbedSelT (api := squeezeShake256Api) (W := 1168)
    { code := Impl.Sha3.RISCV64.Instances.xofSqueeze xofShake256.rate,
      verified := Proof.Sha3.RISCV64.Instances.squeeze_shake256 }
    _ [(.a0, 25 * Elem.u64.size)] (xofSqueezeOut xofShake256 _) (by lit_decide) (hbp_firstArray _ rfl)
    ⟨_, by taint_decide_ct⟩

end VG.Proof.Sha3.RISCV64
