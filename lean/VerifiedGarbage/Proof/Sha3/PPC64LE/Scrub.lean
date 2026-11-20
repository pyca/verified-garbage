module

public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sha3.PPC64LE.Instances
public import VerifiedGarbage.Proof.Sha3.Instances
public import VerifiedGarbage.Proof.Sha3.PostOut
import VerifiedGarbage.Proof.Framework.Lit

/-!
# SHA-3 and SHAKE on PPC64LE, without secret residue

Each instance's `update` and `finalize`, and SHAKE's `squeeze`, as emitted
(`Impl.Sha3.PPC64LE.Fn`): the function followed by its cleanup
(`Impl.Scrub.PPC64LE.scrub`), which zeroes the stack its frames used and
clears the volatile registers it wrote. Each theorem below states that one
meets its contract in constant time and returns without secret residue
(`VerifiedScrubbed`, by `PPC64LE.Scrub.verifiedScrubbed`, whose condition on
the code the kernel evaluates here), which is what its registration binds.
Their postconditions read the memory on return only within their buffers:
the state, through `stateAt` (`Proof/Sha3/PostOut.lean`,
`Proof/Sha3/Instances.lean`), and the output. HMAC-free: SHA-3's callers
(ML-KEM, ML-DSA, Ed448) call their own internal copies of the code, not
these.
-/

@[expose] public section

namespace VG.Proof.Sha3.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub

/-- `vg_sha3_224_finalize` as emitted (`Impl.Sha3.PPC64LE.Fn.finalize`) meets its contract in
constant time and returns without secret residue. -/
theorem finalize_sha3_224_scrubbed :
    VerifiedScrubbed PPC64LE.target (Impl.Sha3.PPC64LE.Fn.finalize Spec.Sha3.hashSha3_224.rate Spec.Sha3.hashSha3_224.len)
      (Spec.Sha3.finalizeContract PPC64LE.abi Spec.Sha3.hashSha3_224 (48 + 704)) 0 :=
  verifiedScrubbed (api := Spec.Sha3.finalizeSha3_224Api)
    { code := Impl.Sha3.PPC64LE.Instances.finalize Spec.Sha3.hashSha3_224.rate Spec.Sha3.hashSha3_224.len
      verified := Proof.Sha3.PPC64LE.Instances.finalize_sha3_224 }
    752 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha3.Instances.finalizePostOut_local 64 Spec.Sha3.hashSha3_224))
    (by dsimp only; lit_decide)

/-- `vg_sha3_256_finalize` as emitted (`Impl.Sha3.PPC64LE.Fn.finalize`) meets its contract in
constant time and returns without secret residue. -/
theorem finalize_sha3_256_scrubbed :
    VerifiedScrubbed PPC64LE.target (Impl.Sha3.PPC64LE.Fn.finalize Spec.Sha3.hashSha3_256.rate Spec.Sha3.hashSha3_256.len)
      (Spec.Sha3.finalizeContract PPC64LE.abi Spec.Sha3.hashSha3_256 (48 + 704)) 0 :=
  verifiedScrubbed (api := Spec.Sha3.finalizeSha3_256Api)
    { code := Impl.Sha3.PPC64LE.Instances.finalize Spec.Sha3.hashSha3_256.rate Spec.Sha3.hashSha3_256.len
      verified := Proof.Sha3.PPC64LE.Instances.finalize_sha3_256 }
    752 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha3.Instances.finalizePostOut_local 64 Spec.Sha3.hashSha3_256))
    (by dsimp only; lit_decide)

/-- `vg_sha3_384_finalize` as emitted (`Impl.Sha3.PPC64LE.Fn.finalize`) meets its contract in
constant time and returns without secret residue. -/
theorem finalize_sha3_384_scrubbed :
    VerifiedScrubbed PPC64LE.target (Impl.Sha3.PPC64LE.Fn.finalize Spec.Sha3.hashSha3_384.rate Spec.Sha3.hashSha3_384.len)
      (Spec.Sha3.finalizeContract PPC64LE.abi Spec.Sha3.hashSha3_384 (48 + 704)) 0 :=
  verifiedScrubbed (api := Spec.Sha3.finalizeSha3_384Api)
    { code := Impl.Sha3.PPC64LE.Instances.finalize Spec.Sha3.hashSha3_384.rate Spec.Sha3.hashSha3_384.len
      verified := Proof.Sha3.PPC64LE.Instances.finalize_sha3_384 }
    752 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha3.Instances.finalizePostOut_local 64 Spec.Sha3.hashSha3_384))
    (by dsimp only; lit_decide)

/-- `vg_sha3_512_finalize` as emitted (`Impl.Sha3.PPC64LE.Fn.finalize`) meets its contract in
constant time and returns without secret residue. -/
theorem finalize_sha3_512_scrubbed :
    VerifiedScrubbed PPC64LE.target (Impl.Sha3.PPC64LE.Fn.finalize Spec.Sha3.hashSha3_512.rate Spec.Sha3.hashSha3_512.len)
      (Spec.Sha3.finalizeContract PPC64LE.abi Spec.Sha3.hashSha3_512 (48 + 704)) 0 :=
  verifiedScrubbed (api := Spec.Sha3.finalizeSha3_512Api)
    { code := Impl.Sha3.PPC64LE.Instances.finalize Spec.Sha3.hashSha3_512.rate Spec.Sha3.hashSha3_512.len
      verified := Proof.Sha3.PPC64LE.Instances.finalize_sha3_512 }
    752 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha3.Instances.finalizePostOut_local 64 Spec.Sha3.hashSha3_512))
    (by dsimp only; lit_decide)

/-- `vg_shake128_finalize` as emitted (`Impl.Sha3.PPC64LE.Fn.xofFinalize`) meets its contract in
constant time and returns without secret residue. -/
theorem finalize_shake128_scrubbed :
    VerifiedScrubbed PPC64LE.target (Impl.Sha3.PPC64LE.Fn.xofFinalize Spec.Sha3.xofShake128.rate)
      (Spec.Sha3.xofFinalizeContract PPC64LE.abi Spec.Sha3.xofShake128 (48 + 672)) 0 :=
  verifiedScrubbed (api := Spec.Sha3.finalizeShake128Api)
    { code := Impl.Sha3.PPC64LE.Instances.xofFinalize Spec.Sha3.xofShake128.rate
      verified := Proof.Sha3.PPC64LE.Instances.finalize_shake128 }
    720 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha3.Instances.xofFinalizePostOut_local 64 Spec.Sha3.xofShake128))
    (by dsimp only; lit_decide)

/-- `vg_shake128_squeeze` as emitted (`Impl.Sha3.PPC64LE.Fn.xofSqueeze`) meets its contract in
constant time and returns without secret residue. -/
theorem squeeze_shake128_scrubbed :
    VerifiedScrubbed PPC64LE.target (Impl.Sha3.PPC64LE.Fn.xofSqueeze Spec.Sha3.xofShake128.rate)
      (Spec.Sha3.xofSqueezeContract PPC64LE.abi Spec.Sha3.xofShake128 (48 + 672)) 64 :=
  verifiedScrubbed (api := Spec.Sha3.squeezeShake128Api)
    { code := Impl.Sha3.PPC64LE.Instances.xofSqueeze Spec.Sha3.xofShake128.rate
      verified := Proof.Sha3.PPC64LE.Instances.squeeze_shake128 }
    720 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha3.Instances.xofSqueezePostOut_local 64 Spec.Sha3.xofShake128))
    (by dsimp only; lit_decide)

/-- `vg_shake256_finalize` as emitted (`Impl.Sha3.PPC64LE.Fn.xofFinalize`) meets its contract in
constant time and returns without secret residue. -/
theorem finalize_shake256_scrubbed :
    VerifiedScrubbed PPC64LE.target (Impl.Sha3.PPC64LE.Fn.xofFinalize Spec.Sha3.xofShake256.rate)
      (Spec.Sha3.xofFinalizeContract PPC64LE.abi Spec.Sha3.xofShake256 (48 + 672)) 0 :=
  verifiedScrubbed (api := Spec.Sha3.finalizeShake256Api)
    { code := Impl.Sha3.PPC64LE.Instances.xofFinalize Spec.Sha3.xofShake256.rate
      verified := Proof.Sha3.PPC64LE.Instances.finalize_shake256 }
    720 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha3.Instances.xofFinalizePostOut_local 64 Spec.Sha3.xofShake256))
    (by dsimp only; lit_decide)

/-- `vg_shake256_squeeze` as emitted (`Impl.Sha3.PPC64LE.Fn.xofSqueeze`) meets its contract in
constant time and returns without secret residue. -/
theorem squeeze_shake256_scrubbed :
    VerifiedScrubbed PPC64LE.target (Impl.Sha3.PPC64LE.Fn.xofSqueeze Spec.Sha3.xofShake256.rate)
      (Spec.Sha3.xofSqueezeContract PPC64LE.abi Spec.Sha3.xofShake256 (48 + 672)) 64 :=
  verifiedScrubbed (api := Spec.Sha3.squeezeShake256Api)
    { code := Impl.Sha3.PPC64LE.Instances.xofSqueeze Spec.Sha3.xofShake256.rate
      verified := Proof.Sha3.PPC64LE.Instances.squeeze_shake256 }
    720 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha3.Instances.xofSqueezePostOut_local 64 Spec.Sha3.xofShake256))
    (by dsimp only; lit_decide)

/-! ## `absorb`: `update` with its working space on the stack -/

/-- `vg_sha3_224_update`: `update`, with its working space in a frame of 672
bytes on the stack (`withStackScratch`), proven from `update`'s proof
(`Verified.stackScratch`). -/
theorem absorb_sha3_224 : Verified PPC64LE.target (Impl.Sha3.PPC64LE.Instances.absorb Spec.Sha3.hashSha3_224.rate)
    (Spec.Sha3.updateContract PPC64LE.abi Spec.Sha3.hashSha3_224.rate (48 + 672)) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Sha3.updateSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Sha3.updatePre Spec.Sha3.hashSha3_224.rate PPC64LE.abi.ptrBits)
    (post := Spec.Sha3.updatePost Spec.Sha3.hashSha3_224.rate PPC64LE.abi.ptrBits) (wa := true)
    (stack := 48) (bytes := 672) Proof.Sha3.PPC64LE.Instances.update_sha3_224 (by decide) (by decide)
    (Proof.Sha3.PostOut.updatePre_local _ _) (Proof.Sha3.PostOut.updatePost_local _ _)
    (fun vs m m₁ m₂ r hl _ hb h => Proof.Sha3.PostOut.updatePost_out _ _ vs m m₁ m₂ r hl hb h)
    (PPC64LE.sat_regs (by decide) (by decide) (by decide) (by show _ < _; decide))

/-- `vg_sha3_224_update` as emitted (`Impl.Sha3.PPC64LE.Fn.update`) meets its contract in
constant time and returns without secret residue. -/
theorem update_sha3_224_scrubbed :
    VerifiedScrubbed PPC64LE.target (Impl.Sha3.PPC64LE.Fn.update Spec.Sha3.hashSha3_224.rate)
      (Spec.Sha3.updateContract PPC64LE.abi Spec.Sha3.hashSha3_224.rate (48 + 672)) 64 :=
  verifiedScrubbed (api := Spec.Sha3.updateSha3_224Api)
    { code := Impl.Sha3.PPC64LE.Instances.absorb Spec.Sha3.hashSha3_224.rate
      verified := absorb_sha3_224 }
    720 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha3.PostOut.updatePost_out Spec.Sha3.hashSha3_224.rate 64))
    (by dsimp only; lit_decide)

/-- `vg_sha3_256_update`: `update`, with its working space in a frame of 672
bytes on the stack (`withStackScratch`), proven from `update`'s proof
(`Verified.stackScratch`). -/
theorem absorb_sha3_256 : Verified PPC64LE.target (Impl.Sha3.PPC64LE.Instances.absorb Spec.Sha3.hashSha3_256.rate)
    (Spec.Sha3.updateContract PPC64LE.abi Spec.Sha3.hashSha3_256.rate (48 + 672)) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Sha3.updateSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Sha3.updatePre Spec.Sha3.hashSha3_256.rate PPC64LE.abi.ptrBits)
    (post := Spec.Sha3.updatePost Spec.Sha3.hashSha3_256.rate PPC64LE.abi.ptrBits) (wa := true)
    (stack := 48) (bytes := 672) Proof.Sha3.PPC64LE.Instances.update_sha3_256 (by decide) (by decide)
    (Proof.Sha3.PostOut.updatePre_local _ _) (Proof.Sha3.PostOut.updatePost_local _ _)
    (fun vs m m₁ m₂ r hl _ hb h => Proof.Sha3.PostOut.updatePost_out _ _ vs m m₁ m₂ r hl hb h)
    (PPC64LE.sat_regs (by decide) (by decide) (by decide) (by show _ < _; decide))

/-- `vg_sha3_256_update` as emitted (`Impl.Sha3.PPC64LE.Fn.update`) meets its contract in
constant time and returns without secret residue. -/
theorem update_sha3_256_scrubbed :
    VerifiedScrubbed PPC64LE.target (Impl.Sha3.PPC64LE.Fn.update Spec.Sha3.hashSha3_256.rate)
      (Spec.Sha3.updateContract PPC64LE.abi Spec.Sha3.hashSha3_256.rate (48 + 672)) 64 :=
  verifiedScrubbed (api := Spec.Sha3.updateSha3_256Api)
    { code := Impl.Sha3.PPC64LE.Instances.absorb Spec.Sha3.hashSha3_256.rate
      verified := absorb_sha3_256 }
    720 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha3.PostOut.updatePost_out Spec.Sha3.hashSha3_256.rate 64))
    (by dsimp only; lit_decide)

/-- `vg_sha3_384_update`: `update`, with its working space in a frame of 672
bytes on the stack (`withStackScratch`), proven from `update`'s proof
(`Verified.stackScratch`). -/
theorem absorb_sha3_384 : Verified PPC64LE.target (Impl.Sha3.PPC64LE.Instances.absorb Spec.Sha3.hashSha3_384.rate)
    (Spec.Sha3.updateContract PPC64LE.abi Spec.Sha3.hashSha3_384.rate (48 + 672)) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Sha3.updateSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Sha3.updatePre Spec.Sha3.hashSha3_384.rate PPC64LE.abi.ptrBits)
    (post := Spec.Sha3.updatePost Spec.Sha3.hashSha3_384.rate PPC64LE.abi.ptrBits) (wa := true)
    (stack := 48) (bytes := 672) Proof.Sha3.PPC64LE.Instances.update_sha3_384 (by decide) (by decide)
    (Proof.Sha3.PostOut.updatePre_local _ _) (Proof.Sha3.PostOut.updatePost_local _ _)
    (fun vs m m₁ m₂ r hl _ hb h => Proof.Sha3.PostOut.updatePost_out _ _ vs m m₁ m₂ r hl hb h)
    (PPC64LE.sat_regs (by decide) (by decide) (by decide) (by show _ < _; decide))

/-- `vg_sha3_384_update` as emitted (`Impl.Sha3.PPC64LE.Fn.update`) meets its contract in
constant time and returns without secret residue. -/
theorem update_sha3_384_scrubbed :
    VerifiedScrubbed PPC64LE.target (Impl.Sha3.PPC64LE.Fn.update Spec.Sha3.hashSha3_384.rate)
      (Spec.Sha3.updateContract PPC64LE.abi Spec.Sha3.hashSha3_384.rate (48 + 672)) 64 :=
  verifiedScrubbed (api := Spec.Sha3.updateSha3_384Api)
    { code := Impl.Sha3.PPC64LE.Instances.absorb Spec.Sha3.hashSha3_384.rate
      verified := absorb_sha3_384 }
    720 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha3.PostOut.updatePost_out Spec.Sha3.hashSha3_384.rate 64))
    (by dsimp only; lit_decide)

/-- `vg_sha3_512_update`: `update`, with its working space in a frame of 672
bytes on the stack (`withStackScratch`), proven from `update`'s proof
(`Verified.stackScratch`). -/
theorem absorb_sha3_512 : Verified PPC64LE.target (Impl.Sha3.PPC64LE.Instances.absorb Spec.Sha3.hashSha3_512.rate)
    (Spec.Sha3.updateContract PPC64LE.abi Spec.Sha3.hashSha3_512.rate (48 + 672)) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Sha3.updateSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Sha3.updatePre Spec.Sha3.hashSha3_512.rate PPC64LE.abi.ptrBits)
    (post := Spec.Sha3.updatePost Spec.Sha3.hashSha3_512.rate PPC64LE.abi.ptrBits) (wa := true)
    (stack := 48) (bytes := 672) Proof.Sha3.PPC64LE.Instances.update_sha3_512 (by decide) (by decide)
    (Proof.Sha3.PostOut.updatePre_local _ _) (Proof.Sha3.PostOut.updatePost_local _ _)
    (fun vs m m₁ m₂ r hl _ hb h => Proof.Sha3.PostOut.updatePost_out _ _ vs m m₁ m₂ r hl hb h)
    (PPC64LE.sat_regs (by decide) (by decide) (by decide) (by show _ < _; decide))

/-- `vg_sha3_512_update` as emitted (`Impl.Sha3.PPC64LE.Fn.update`) meets its contract in
constant time and returns without secret residue. -/
theorem update_sha3_512_scrubbed :
    VerifiedScrubbed PPC64LE.target (Impl.Sha3.PPC64LE.Fn.update Spec.Sha3.hashSha3_512.rate)
      (Spec.Sha3.updateContract PPC64LE.abi Spec.Sha3.hashSha3_512.rate (48 + 672)) 64 :=
  verifiedScrubbed (api := Spec.Sha3.updateSha3_512Api)
    { code := Impl.Sha3.PPC64LE.Instances.absorb Spec.Sha3.hashSha3_512.rate
      verified := absorb_sha3_512 }
    720 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha3.PostOut.updatePost_out Spec.Sha3.hashSha3_512.rate 64))
    (by dsimp only; lit_decide)

/-- `vg_shake128_update`: `update`, with its working space in a frame of 672
bytes on the stack (`withStackScratch`), proven from `update`'s proof
(`Verified.stackScratch`). -/
theorem absorb_shake128 : Verified PPC64LE.target (Impl.Sha3.PPC64LE.Instances.absorb Spec.Sha3.xofShake128.rate)
    (Spec.Sha3.updateContract PPC64LE.abi Spec.Sha3.xofShake128.rate (48 + 672)) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Sha3.updateSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Sha3.updatePre Spec.Sha3.xofShake128.rate PPC64LE.abi.ptrBits)
    (post := Spec.Sha3.updatePost Spec.Sha3.xofShake128.rate PPC64LE.abi.ptrBits) (wa := true)
    (stack := 48) (bytes := 672) Proof.Sha3.PPC64LE.Instances.update_shake128 (by decide) (by decide)
    (Proof.Sha3.PostOut.updatePre_local _ _) (Proof.Sha3.PostOut.updatePost_local _ _)
    (fun vs m m₁ m₂ r hl _ hb h => Proof.Sha3.PostOut.updatePost_out _ _ vs m m₁ m₂ r hl hb h)
    (PPC64LE.sat_regs (by decide) (by decide) (by decide) (by show _ < _; decide))

/-- `vg_shake128_update` as emitted (`Impl.Sha3.PPC64LE.Fn.update`) meets its contract in
constant time and returns without secret residue. -/
theorem update_shake128_scrubbed :
    VerifiedScrubbed PPC64LE.target (Impl.Sha3.PPC64LE.Fn.update Spec.Sha3.xofShake128.rate)
      (Spec.Sha3.updateContract PPC64LE.abi Spec.Sha3.xofShake128.rate (48 + 672)) 64 :=
  verifiedScrubbed (api := Spec.Sha3.updateShake128Api)
    { code := Impl.Sha3.PPC64LE.Instances.absorb Spec.Sha3.xofShake128.rate
      verified := absorb_shake128 }
    720 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha3.PostOut.updatePost_out Spec.Sha3.xofShake128.rate 64))
    (by dsimp only; lit_decide)

end VG.Proof.Sha3.PPC64LE.Scrub
