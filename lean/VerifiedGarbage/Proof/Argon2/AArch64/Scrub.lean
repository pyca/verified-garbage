module

public import VerifiedGarbage.Spec.Argon2.Contract
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.Argon2.AArch64.DeriveVerified
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Argon2 on AArch64, without secret residue

The postcondition of `vg_argon2` reads the memory on return only within
`out` (`ScrubAll.ScrubAllOk`, as x86-64's `Proof/Argon2/X86_64/Scrub.lean`
proves it): each implementation, generic over the BLAKE2b implementation it
calls, returns with every register it may leave secret cleared and its whole
stack zeroed (`ScrubAll.withScrubAll`).
-/

@[expose] public section

namespace VG.Proof.Argon2.AArch64.Scrub

open VG.AArch64 VG.AArch64.ScrubAll

theorem deriveOk (stack : Nat) :
    ScrubAllOk (Spec.Argon2.deriveContract abi stack) stack (Spec.Argon2.deriveSig.retBits abi.ptrBits) :=
  scrubAllOk_args_any (sig := Spec.Argon2.deriveSig) fun
    | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, out, outLen], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Argon2.deriveSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      have ho := hb.2.2.2.2.2.2
      change _ = _ at h
      change Spec.Blake2.bytesAt m₂ out _ = _
      rw [← h]
      simp only [Spec.Blake2.bytesAt]
      refine List.map_congr_left fun i hi => ?_
      have := List.mem_range.mp hi
      simp only [ArgWord.ofRaw, show abi.ptrBits = 64 from rfl, BitVec.toNat_setWidth] at this
      have := Nat.mod_le outLen.toNat (2 ^ 64)
      exact (ho _ (Offset.contains_base _ (by simp only [Elem.size] at *; omega_arith) (by omega_arith))).symm

/-! ## The function, as emitted

`vg_argon2_derive` over `v` with its cleanup
(`Impl.Argon2.AArch64.Derive.Fn.derive`): it meets its contract in constant
time and returns without secret residue (`VerifiedScrubbed`), which is what
its registration binds. What the cleanup needs of the code
(`ScrubAll.scrubSide`) is proved of the function's own instructions here,
once, with code that does nothing in the place of the hash functions, and of
the hash functions where they are defined (`HPrime.Backend.initScrub`,
`updateScrub`, `finalizeScrub`). -/

private theorem derive_all {p : Instr → Bool} (name : String) (h : Impl.Argon2.AArch64.HPrime.Hash)
    (h0 : sideAll p (Impl.Argon2.AArch64.Derive.code "" ⟨"", .block [], "", .block [], "", .block [], ⟨[], [], []⟩⟩) = true)
    (hi : sideAll p h.init = true) (hu : sideAll p h.update = true) (hf : sideAll p h.finalize = true) :
    sideAll p (Impl.Argon2.AArch64.Derive.code name h) = true := by
  simp only [Impl.Argon2.AArch64.Derive.code, Impl.Argon2.AArch64.Derive.body, Impl.Argon2.AArch64.Derive.frame, Impl.Argon2.AArch64.Derive.saved, Impl.Argon2.AArch64.InitialBody.code, Impl.Argon2.AArch64.Initial.code, Impl.Argon2.AArch64.Initial.start, Impl.Argon2.AArch64.Initial.absorb, Impl.Argon2.AArch64.Initial.finish, Impl.Argon2.AArch64.InitFill.code, Impl.Argon2.AArch64.MemoryInit.code, Impl.Argon2.AArch64.MemoryInit.lane, Impl.Argon2.AArch64.MemoryInit.block, Impl.Argon2.AArch64.FillFinish.code, Impl.Argon2.AArch64.Finish.code, Impl.Argon2.AArch64.FinalOutput.code, Impl.Argon2.AArch64.HPrime.code, Impl.Argon2.AArch64.HPrime.first, Impl.Argon2.AArch64.HPrime.chooseLength, Impl.Argon2.AArch64.HPrime.init, Impl.Argon2.AArch64.HPrime.absorbFixed, Impl.Argon2.AArch64.HPrime.update, Impl.Argon2.AArch64.HPrime.absorbInput, Impl.Argon2.AArch64.HPrime.finishInput, Impl.Argon2.AArch64.HPrime.finalize, Impl.Argon2.AArch64.HPrime.finishOutput, Impl.Argon2.AArch64.HPrime.extendDigest, Impl.Argon2.AArch64.HPrime.emitPrefix, Impl.Argon2.AArch64.HPrime.copy, Impl.Argon2.AArch64.HPrime.chain, Impl.Argon2.AArch64.HPrime.next, Impl.Argon2.AArch64.HPrime.copyRemaining, sideAll, Bool.and_eq_true] at h0 ⊢
  simp only [h0, hi, hu, hf, and_self]

private theorem derive_own :
    calleeSide (Impl.Argon2.AArch64.Derive.code "" ⟨"", .block [], "", .block [], "", .block [], ⟨[], [], []⟩⟩) Impl.Argon2.AArch64.Derive.Fn.deriveOwn = true := by
  kernel_rfl

private theorem derive_depth (name : String) (h : Impl.Argon2.AArch64.HPrime.Hash)
    (hi : h.init.aarch64Depth = 0) (hu : h.update.aarch64Depth = 1) (hf : h.finalize.aarch64Depth = 1) :
    16 * (Impl.Argon2.AArch64.Derive.code name h).aarch64Depth ≤ 400 := by
  simp only [Impl.Argon2.AArch64.Derive.code, Impl.Argon2.AArch64.Derive.body, Impl.Argon2.AArch64.Derive.frame, Impl.Argon2.AArch64.Derive.saved, Impl.Argon2.AArch64.InitialBody.code, Impl.Argon2.AArch64.Initial.code, Impl.Argon2.AArch64.Initial.start, Impl.Argon2.AArch64.Initial.absorb, Impl.Argon2.AArch64.Initial.finish, Impl.Argon2.AArch64.InitFill.code, Impl.Argon2.AArch64.MemoryInit.code, Impl.Argon2.AArch64.MemoryInit.lane, Impl.Argon2.AArch64.MemoryInit.block, Impl.Argon2.AArch64.FillFinish.code, Impl.Argon2.AArch64.Finish.code, Impl.Argon2.AArch64.FinalOutput.code, Impl.Argon2.AArch64.HPrime.code, Impl.Argon2.AArch64.HPrime.first, Impl.Argon2.AArch64.HPrime.chooseLength, Impl.Argon2.AArch64.HPrime.init, Impl.Argon2.AArch64.HPrime.absorbFixed, Impl.Argon2.AArch64.HPrime.update, Impl.Argon2.AArch64.HPrime.absorbInput, Impl.Argon2.AArch64.HPrime.finishInput, Impl.Argon2.AArch64.HPrime.finalize, Impl.Argon2.AArch64.HPrime.finishOutput, Impl.Argon2.AArch64.HPrime.extendDigest, Impl.Argon2.AArch64.HPrime.emitPrefix, Impl.Argon2.AArch64.HPrime.copy, Impl.Argon2.AArch64.HPrime.chain, Impl.Argon2.AArch64.HPrime.next, Impl.Argon2.AArch64.HPrime.copyRemaining, Code.aarch64Depth, Instr.frameUnits, hi, hu, hf]
  decide

theorem derive_side (v : Proof.Argon2.AArch64.HPrime.Backend) :
    scrubSide (Impl.Argon2.AArch64.Derive.code ("vg_argon2_hprime" ++ v.suffix) v.hash) 400 0
      (Impl.Argon2.AArch64.Derive.Fn.deriveOwn.union v.hash.clear) [] = true :=
  scrubSide_union (by decide) (derive_depth _ _ v.ok.initDepth v.ok.updateDepth v.ok.finalizeDepth) (by decide)
    (derive_all _ v.hash (sideAll_union_left derive_own) (sideAll_union_right v.initScrub)
      (sideAll_union_right v.updateScrub) (sideAll_union_right v.finalizeScrub)) (by decide)

/-- `vg_argon2_derive` over `v` as emitted, cleanup included. -/
theorem derive_scrubbed (v : Proof.Argon2.AArch64.HPrime.Backend) :
    VerifiedScrubbed AArch64.target (Impl.Argon2.AArch64.Derive.Fn.derive v.hash v.suffix)
      (Spec.Argon2.deriveContract AArch64.abi 400) 0 :=
  verifiedScrubbed (api := Spec.Argon2.deriveApi)
    { suffix := v.suffix
      code := Impl.Argon2.AArch64.Derive.code ("vg_argon2_hprime" ++ v.suffix) v.hash
      verified := Proof.Argon2.AArch64.Derive.verified v _
      spSafe := Proof.Argon2.AArch64.Derive.code_spSafe v _ } _ (deriveOk _) (derive_side v)

end VG.Proof.Argon2.AArch64.Scrub
