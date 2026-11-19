module

public import VerifiedGarbage.Proof.Sha3.AArch64.Permute
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubSide
public import VerifiedGarbage.Impl.Sha3.AArch64.Instances
public import VerifiedGarbage.Proof.Framework.AArch64.Depth
public import VerifiedGarbage.Proof.Framework.AArch64.ModeSim
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Lit
public meta import VerifiedGarbage.TCB.Code
public meta import VerifiedGarbage.TCB.AArch64.Isa
public meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
public meta import VerifiedGarbage.Proof.Framework.TaintSum
public meta import VerifiedGarbage.Proof.Framework.AArch64.TaintMono
public meta import VerifiedGarbage.Impl.Sha3.AArch64.Callee
public meta import VerifiedGarbage.Impl.Sha3.AArch64.Stream
public meta import VerifiedGarbage.Proof.Sha3.AArch64.Sums
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.Sign
public import VerifiedGarbage.Impl.MlDsa.AArch64.Verify.Verify
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.ExpandMask
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.Sign
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Verify.Verify
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.ExpandMask
meta import VerifiedGarbage.Proof.Framework.RegSet
public import VerifiedGarbage.Proof.Sha3.AArch64.Sums
public import VerifiedGarbage.Proof.Framework.TaintSumGeneric
meta import VerifiedGarbage.Proof.Framework.TaintSumGeneric

/-! ### `Sha3.AArch64.Callers.MlDsa`, which this module and modules that import it used -/

section

/-! ### `Sha3.AArch64.Callers.Sums`, which this module and modules that import it used -/

section

/-!
# The summaries of the sponge's callers, for any Keccak backend

The constant-time checks of the sponge's callers (ML-KEM, ML-DSA) use the
summaries of the sponge's functions over a backend's permutation
(`sponge_taint_summaries`) and of ML-KEM's functions. `checkSum` looks
neither at the code of a summarized call nor at the names of calls, so each
caller is checked once for any backend `c` (`taint_decide_generic`,
`Callers/MlDsa.lean`) from the summaries `sums c`, whose
`pre`, `post` and frame are the same for every backend: each function of the
sponge from each set of callee-saved registers public at some call, as
`sponge_taint_summaries ns c saving` states them, ending with the registers
the callers need public. Each backend gives them from its own summaries: those
of a permutation that saves and restores the callee-saved registers with less
public at the end (`Taint.SumOk.weaken`), those of one that keeps them from
their frames (`Taint.SumOk.restrict`).
-/

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Callers

open VG VG.AArch64

/-- The calls of the sponge's functions of the backend `c`, as its summaries
state them (`sponge_taint_summaries`). -/
abbrev absorbCall (c : Impl.Sha3.AArch64.Callee) : Prog isa :=
  .call ("vg_keccak_absorb_scratch" ++ c.suffix) (Impl.Sha3.AArch64.Stream.absorbWith c)
abbrev padCall (c : Impl.Sha3.AArch64.Callee) : Prog isa :=
  .call ("vg_keccak_pad_scratch" ++ c.suffix) (Impl.Sha3.AArch64.Stream.padWith c)
abbrev squeezeCall (c : Impl.Sha3.AArch64.Callee) : Prog isa :=
  .call ("vg_keccak_squeeze_scratch" ++ c.suffix) (Impl.Sha3.AArch64.Stream.squeezeWith c)

/-- ML-KEM's functions' summaries (`MlKemSums`), the same for every backend. -/
abbrev mlkem : List (Taint.Summary isa VectorTaint.taint.T) :=
  [Taint.sumOf MlKemSums.add, Taint.sumOf MlKemSums.sub, Taint.sumOf MlKemSums.ce,
    Taint.sumOf MlKemSums.dd, Taint.sumOf MlKemSums.ce1024, Taint.sumOf MlKemSums.dd1024]

theorem mlkem_ok : Taint.AllOk VectorTaint.taint mlkem :=
  ⟨MlKemSums.add, MlKemSums.sub, MlKemSums.ce, MlKemSums.dd, MlKemSums.ce1024, MlKemSums.dd1024,
    trivial⟩

/-- The summaries of the sponge's callers' checks, for the backend `c`, in
`sponge_taint_decide`'s order: each function of the sponge from each set of
callee-saved registers public at some call, with the registers public at its
end, then ML-KEM's functions'. -/
def sums (c : Impl.Sha3.AArch64.Callee) : List (Taint.Summary isa VectorTaint.taint.T) :=
  let sum (f : Prog isa) (pre post : List Reg) : Taint.Summary isa VectorTaint.taint.T :=
    (f, VectorTaint.ofRegs pre, VectorTaint.ofRegs post, Taint.Frame.bot (A := VectorTaint.taint))
  let perm : Prog isa := .call c.name c.code
  [sum (absorbCall c) [.x0, .x1, .x2, .x3, .x4, .x5, .x23, .x25, .x26, .x27, .x28]
      [.x0, .x25, .x26, .x27, .x28],
    sum (absorbCall c) [.x0, .x1, .x2, .x3, .x4, .x5, .x24, .x25, .x26, .x27, .x28]
      [.x0, .x25, .x26, .x27, .x28],
    sum (absorbCall c) [.x0, .x1, .x2, .x3, .x4, .x5, .x25, .x26, .x27, .x28]
      [.x0, .x25, .x26, .x27, .x28],
    sum (absorbCall c) [.x0, .x1, .x2, .x3, .x4, .x5, .x25, .x26, .x27]
      [.x0, .x25, .x26, .x27],
    sum (absorbCall c) [.x0, .x1, .x2, .x3, .x4, .x5, .x24, .x25, .x26]
      [.x0, .x25, .x26],
    sum (padCall c) [.x0, .x1, .x2, .x4, .x25, .x26, .x27, .x28]
      [.x25, .x26, .x27, .x28],
    sum (padCall c) [.x0, .x1, .x2, .x4, .x25, .x26, .x27]
      [.x25, .x26, .x27],
    sum (padCall c) [.x0, .x1, .x2, .x4, .x25, .x26]
      [.x25, .x26],
    sum (squeezeCall c) [.x0, .x1, .x2, .x3, .x4, .x5, .x25, .x26, .x27, .x28]
      [.x0, .x25, .x26, .x27, .x28],
    sum (squeezeCall c) [.x0, .x1, .x2, .x3, .x4, .x5, .x25, .x26, .x27]
      [.x0, .x25, .x26, .x27],
    sum (squeezeCall c) [.x0, .x1, .x2, .x3, .x4, .x5, .x25, .x26]
      [.x0, .x25, .x26],
    sum perm [.x0, .x1, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28]
      [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28],
    sum perm [.x0, .x1, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]
      [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27],
    sum perm [.x0, .x1, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26]
      [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26],
    sum perm [.x0, .x1, .x19, .x20, .x21, .x22, .x23, .x24]
      [.x19, .x20, .x21, .x22, .x23, .x24],
    sum perm [.x0, .x1, .x25, .x26, .x27, .x28]
      [.x25, .x26, .x27, .x28],
    sum perm [.x0, .x1, .x25, .x26, .x27]
      [.x25, .x26, .x27],
    sum perm [.x0, .x1, .x25, .x26]
      [.x25, .x26],
    sum perm [.x0, .x1]
      []] ++ mlkem

/-- `sums c` holds, from the backend's summaries, in `sums`'s order. -/
theorem sums_ok {c : Impl.Sha3.AArch64.Callee}
    (h : Taint.AllOk VectorTaint.taint (sums c |>.take 19)) : Taint.AllOk VectorTaint.taint (sums c) := by
  have e : sums c = (sums c).take 19 ++ mlkem := rfl
  rw [e]
  exact .append h mlkem_ok

end VG.Proof.Sha3.AArch64.Callers

end

end

/-!
# Constant time of ML-DSA's calls of the sponge, for any Keccak backend

Each check, once for any backend `c` with the summaries `sums c`
(`Callers/Sums.lean`, `taint_decide_generic`), for each backend's
`Permutation` (`Proof/Sha3/AArch64/Variant.lean`).
-/

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Callers

open VG VG.AArch64

theorem mldsaNttTaint (c : Impl.Sha3.AArch64.Callee) (hS : Taint.AllOk VectorTaint.taint (sums c)) :
    ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x3, .x4])
      (Impl.MlDsa.AArch64.Sample.spongeWith c 168 1008) h).isSome = true := by
  taint_decide_generic c := Impl.Sha3.AArch64.Callee.scalar using hS

theorem mldsaBallTaint (c : Impl.Sha3.AArch64.Callee) (hS : Taint.AllOk VectorTaint.taint (sums c)) :
    ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x3, .x4])
      (Impl.MlDsa.AArch64.Sample.spongeWith c 136 272) h).isSome = true := by
  taint_decide_generic c := Impl.Sha3.AArch64.Callee.scalar using hS

theorem mldsaMaskTaint (c : Impl.Sha3.AArch64.Callee) (hS : Taint.AllOk VectorTaint.taint (sums c)) :
    ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x3, .x4])
      (Impl.MlDsa.AArch64.Sample.expandMaskTailWith c) h).isSome = true := by
  taint_decide_generic c := Impl.Sha3.AArch64.Callee.scalar using hS

theorem mldsaSeedsTaint (c : Impl.Sha3.AArch64.Callee) (hS : Taint.AllOk VectorTaint.taint (sums c)) :
    ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
      (Impl.MlDsa.AArch64.KeyGen.shake256With c [⟨.x25, 0, 32⟩, ⟨.x28, 896, 2⟩] [⟨.x28, 1024, 128⟩]) h).isSome = true := by
  taint_decide_generic c := Impl.Sha3.AArch64.Callee.scalar using hS

theorem mldsaTrHashTaint (c : Impl.Sha3.AArch64.Callee) (hS : Taint.AllOk VectorTaint.taint (sums c)) :
    ∀ p : Spec.MlDsa.Params,
      (p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) → ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
      (Impl.MlDsa.AArch64.KeyGen.trHashWith c p) h).isSome = true := by
  intro p hp
  rcases hp with rfl | rfl | rfl <;>
    taint_decide_generic c := Impl.Sha3.AArch64.Callee.scalar using hS

theorem mldsaVerifyHashTaint (c : Impl.Sha3.AArch64.Callee) (hS : Taint.AllOk VectorTaint.taint (sums c)) :
    ∀ p : Spec.MlDsa.Params,
      (p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) → ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
      (Impl.MlDsa.AArch64.KeyGen.shake256With c [⟨.x26, 0, 64⟩,
        ⟨.x28, (Impl.MlDsa.AArch64.Verify.bP p).2, p.k * Impl.MlDsa.AArch64.Verify.w1Len p⟩]
        [⟨.x28, 1024, p.ctildeLen⟩]) h).isSome = true := by
  intro p hp
  rcases hp with rfl | rfl | rfl <;>
    taint_decide_generic c := Impl.Sha3.AArch64.Callee.scalar using hS

theorem mldsaSignDecodeTaint (c : Impl.Sha3.AArch64.Callee) (hS : Taint.AllOk VectorTaint.taint (sums c)) :
    ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x23, .x25, .x26, .x27, .x28])
      (Impl.MlDsa.AArch64.Sign.shakeAtWith c [⟨.x25, 32, 32⟩, ⟨.x27, 0, 32⟩, ⟨.x26, 0, 64⟩] ⟨.x28, 960, 64⟩) h).isSome = true := by
  taint_decide_generic c := Impl.Sha3.AArch64.Callee.scalar using hS

theorem mldsaSignCommitTaint (c : Impl.Sha3.AArch64.Callee) (hS : Taint.AllOk VectorTaint.taint (sums c)) :
    ∀ p : Spec.MlDsa.Params,
      (p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) → ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x23, .x25, .x26, .x27, .x28])
      (Impl.MlDsa.AArch64.Sign.shakeAtWith c [⟨.x26, 0, 64⟩,
        ⟨.x28, 2048, p.k * Impl.MlDsa.AArch64.Sign.w1Len p⟩]
        ⟨.x28, 1040, Impl.MlDsa.AArch64.Sign.cLen p⟩) h).isSome = true := by
  intro p hp
  rcases hp with rfl | rfl | rfl <;>
    taint_decide_generic c := Impl.Sha3.AArch64.Callee.scalar using hS

end VG.Proof.Sha3.AArch64.Callers

end

end

@[expose] public section

namespace VG.Proof.Sha3.AArch64

open VG VG.AArch64

/-- The permutation contract and mechanical facts needed by generic sponge callers. -/
structure Permutation where
  callee : Impl.Sha3.AArch64.Callee
  features : List String
  /-- The `target_vendor` of the CPUs it is faster on, which callers that are
  faster with it only there give their implementations (`Artifact.vendor`). -/
  vendor : Option String := none
  /-- Its code writes, of the registers the calling convention does not
  preserve, only those `callee.clear` lists, writes no PSTATE.DIT and calls
  nothing indirectly (`ScrubAll.calleeSide`, which the kernel evaluates where
  the implementation is defined): what the cleanup of every function that
  calls it needs of it, so that each proves the rest of its own instructions
  only, whatever the implementation. -/
  scrub : AArch64.ScrubAll.calleeSide callee.code callee.clear = true
  /-- An absorb the implementation gives as a whole writes only what
  `vg_sha3_*_update` clears: `Impl.Sha3.AArch64.Fn.updateOwn` and
  `callee.clear`. -/
  absorbOverrideScrub : ∀ code, callee.absorbOverride = some code →
    AArch64.ScrubAll.calleeSide code (Impl.Sha3.AArch64.Fn.updateOwn.union callee.clear) = true
  ok : ∀ s, Proof.Sha3.permuteAArch64.pre s →
    ∃ t s', Exec isa callee.code s t s' ∧ abiPreserved s s' ∧
      Proof.Sha3.permuteAArch64.post s s'
  noFrames : callee.code.noFrames = true
  /-- The permutation never reads or writes PSTATE.DIT, so its callers' runs agree from any
  mode (`ConstantTime.withDit`). -/
  noDit : callee.code.all (fun i => !i.touchesDit) = true
  /-- The summaries of the sponge's and the permutation's calls (`Callers.sums`), with
  which callers' constant-time checks are decided once for every backend. -/
  callerSums : Taint.AllOk VectorTaint.taint (Callers.sums callee)
  /-- An absorb override must prove the same functional and SIMD ABI contract
  as the general loop; it need not obey that loop's syntactic register shape. -/
  absorbOverrideOk : ∀ code, callee.absorbOverride = some code →
    ∀ s, Proof.Sha3.absorbAArch64.pre s →
      ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧
        Proof.Sha3.absorbAArch64.post s s'
  absorbOverrideDepth : ∀ code, callee.absorbOverride = some code → code.aarch64Depth = 1
  absorbOverrideNoDit : ∀ code, callee.absorbOverride = some code → code.all (fun i => !i.touchesDit) = true
  absorbTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
    (Impl.Sha3.AArch64.Stream.absorbWith callee) h).isSome = true
  padTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x4])
    (Impl.Sha3.AArch64.Stream.padWith callee) h).isSome = true
  squeezeTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
    (Impl.Sha3.AArch64.Stream.squeezeWith callee) h).isSome = true

  mldsaNttTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x3, .x4])
    (Impl.MlDsa.AArch64.Sample.spongeWith callee 168 1008) h).isSome = true
  mldsaBallTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x3, .x4])
    (Impl.MlDsa.AArch64.Sample.spongeWith callee 136 272) h).isSome = true
  mldsaMaskTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x3, .x4])
    (Impl.MlDsa.AArch64.Sample.expandMaskTailWith callee) h).isSome = true

  mldsaSeedsTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.KeyGen.shake256With callee [⟨.x25, 0, 32⟩, ⟨.x28, 896, 2⟩] [⟨.x28, 1024, 128⟩]) h).isSome = true
  mldsaTrHashTaint : ∀ p : Spec.MlDsa.Params,
    (p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) → ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.KeyGen.trHashWith callee p) h).isSome = true
  mldsaVerifyHashTaint : ∀ p : Spec.MlDsa.Params,
    (p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) → ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.KeyGen.shake256With callee [⟨.x26, 0, 64⟩,
      ⟨.x28, (Impl.MlDsa.AArch64.Verify.bP p).2, p.k * Impl.MlDsa.AArch64.Verify.w1Len p⟩]
      [⟨.x28, 1024, p.ctildeLen⟩]) h).isSome = true

  mldsaSignDecodeTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x23, .x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.Sign.shakeAtWith callee [⟨.x25, 32, 32⟩, ⟨.x27, 0, 32⟩, ⟨.x26, 0, 64⟩] ⟨.x28, 960, 64⟩) h).isSome = true
  mldsaSignCommitTaint : ∀ p : Spec.MlDsa.Params,
    (p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) → ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x23, .x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.Sign.shakeAtWith callee [⟨.x26, 0, 64⟩,
      ⟨.x28, 2048, p.k * Impl.MlDsa.AArch64.Sign.w1Len p⟩]
      ⟨.x28, 1040, Impl.MlDsa.AArch64.Sign.cLen p⟩) h).isSome = true

theorem fdepth_of_noFrames {c : Prog isa} (h : c.noFrames = true) : c.aarch64Depth = 0 := by
  induction c <;> simp_all [Code.noFrames, Code.aarch64Depth]

theorem Permutation.absorbMain_depth (v : Permutation) :
    (Impl.Sha3.AArch64.Stream.absorbMainWith v.callee).aarch64Depth = 0 := by
  simp only [Impl.Sha3.AArch64.Stream.absorbMainWith, Impl.Sha3.AArch64.Stream.absorbBodyWith, Impl.Sha3.AArch64.Stream.permuteAtWith, Code.aarch64Depth,
    fdepth_of_noFrames v.noFrames, Nat.max_self]

theorem Permutation.absorb_depth (v : Permutation) :
    (Impl.Sha3.AArch64.Stream.absorbWith v.callee).aarch64Depth = 1 := by
  cases h : v.callee.absorbOverride with
  | none =>
    simp only [Impl.Sha3.AArch64.Stream.absorbWith, h,
      Impl.Sha3.AArch64.Stream.absorbGenericWith, Code.aarch64Depth, Instr.frameUnits, v.absorbMain_depth]
  | some code =>
    simpa only [Impl.Sha3.AArch64.Stream.absorbWith, h] using v.absorbOverrideDepth code h

theorem Permutation.padMain_depth (v : Permutation) :
    (Impl.Sha3.AArch64.Stream.padMainWith v.callee).aarch64Depth = 0 := by
  simp only [Impl.Sha3.AArch64.Stream.padMainWith, Code.aarch64Depth,
    fdepth_of_noFrames v.noFrames, Nat.max_self]

theorem Permutation.pad_depth (v : Permutation) :
    (Impl.Sha3.AArch64.Stream.padWith v.callee).aarch64Depth = 1 := by
  simp only [Impl.Sha3.AArch64.Stream.padWith, Code.aarch64Depth, Instr.frameUnits, v.padMain_depth]

theorem Permutation.squeezeMain_depth (v : Permutation) :
    (Impl.Sha3.AArch64.Stream.squeezeMainWith v.callee).aarch64Depth = 0 := by
  simp only [Impl.Sha3.AArch64.Stream.squeezeMainWith, Impl.Sha3.AArch64.Stream.squeezeBodyWith, Impl.Sha3.AArch64.Stream.permuteAtWith, Code.aarch64Depth,
    fdepth_of_noFrames v.noFrames, Nat.max_self]

theorem Permutation.squeeze_depth (v : Permutation) :
    (Impl.Sha3.AArch64.Stream.squeezeWith v.callee).aarch64Depth = 1 := by
  simp only [Impl.Sha3.AArch64.Stream.squeezeWith, Code.aarch64Depth, Instr.frameUnits, v.squeezeMain_depth]

theorem Permutation.absorb_noDit (v : Permutation) :
    (Impl.Sha3.AArch64.Stream.absorbWith v.callee).all (fun i => !i.touchesDit) = true := by
  cases h : v.callee.absorbOverride with
  | none =>
    simp only [Impl.Sha3.AArch64.Stream.absorbWith, h, Impl.Sha3.AArch64.Stream.absorbGenericWith,
      Impl.Sha3.AArch64.Stream.absorbMainWith, Impl.Sha3.AArch64.Stream.absorbBodyWith,
      Impl.Sha3.AArch64.Stream.permuteAtWith, Code.all, v.noDit, Bool.and_true]
    decide
  | some code =>
    simpa only [Impl.Sha3.AArch64.Stream.absorbWith, h] using v.absorbOverrideNoDit code h

theorem Permutation.pad_noDit (v : Permutation) :
    (Impl.Sha3.AArch64.Stream.padWith v.callee).all (fun i => !i.touchesDit) = true := by
  simp only [Impl.Sha3.AArch64.Stream.padWith, Impl.Sha3.AArch64.Stream.padMainWith, Code.all, v.noDit,
    Bool.and_true]
  decide

theorem Permutation.squeeze_noDit (v : Permutation) :
    (Impl.Sha3.AArch64.Stream.squeezeWith v.callee).all (fun i => !i.touchesDit) = true := by
  simp only [Impl.Sha3.AArch64.Stream.squeezeWith, Impl.Sha3.AArch64.Stream.squeezeMainWith,
    Impl.Sha3.AArch64.Stream.squeezeBodyWith, Impl.Sha3.AArch64.Stream.permuteAtWith, Code.all, v.noDit,
    Bool.and_true]
  decide

sponge_taint_summaries ScalarSums Impl.Sha3.AArch64.Callee.scalar

/-- The summaries the sponge's callers' checks use (`Callers.sums`, from this backend's summaries
with their frames: `Taint.SumOk.restrict`). -/
theorem scalarSums : Taint.AllOk VectorTaint.taint (Callers.sums .scalar) :=
  Callers.sums_ok (by
    exact
      .cons (ScalarSums.absorb.restrict (by decide) (by decide)) <|
      .cons (ScalarSums.absorb.restrict (by decide) (by decide)) <|
      .cons (ScalarSums.absorb.restrict (by decide) (by decide)) <|
      .cons (ScalarSums.absorb.restrict (by decide) (by decide)) <|
      .cons (ScalarSums.absorb.restrict (by decide) (by decide)) <|
      .cons (ScalarSums.pad.restrict (by decide) (by decide)) <|
      .cons (ScalarSums.pad.restrict (by decide) (by decide)) <|
      .cons (ScalarSums.pad.restrict (by decide) (by decide)) <|
      .cons (ScalarSums.squeeze.restrict (by decide) (by decide)) <|
      .cons (ScalarSums.squeeze.restrict (by decide) (by decide)) <|
      .cons (ScalarSums.squeeze.restrict (by decide) (by decide)) <|
      .cons (ScalarSums.perm.restrict (by decide) (by decide)) <|
      .cons (ScalarSums.perm.restrict (by decide) (by decide)) <|
      .cons (ScalarSums.perm.restrict (by decide) (by decide)) <|
      .cons (ScalarSums.perm.restrict (by decide) (by decide)) <|
      .cons (ScalarSums.perm.restrict (by decide) (by decide)) <|
      .cons (ScalarSums.perm.restrict (by decide) (by decide)) <|
      .cons (ScalarSums.perm.restrict (by decide) (by decide)) <|
      .cons (ScalarSums.perm.restrict (by decide) (by decide)) <|
      .nil)

def Permutation.scalar : Permutation where
  callee := .scalar
  features := []
  scrub := by lit_decide
  absorbOverrideScrub := by intro code h; cases h
  ok := permute_correct
  noFrames := permute_noFrames
  noDit := by lit_decide
  callerSums := scalarSums
  absorbOverrideOk := by intro code h; cases h
  absorbOverrideDepth := by intro code h; cases h
  absorbOverrideNoDit := by intro code h; cases h
  absorbTaint := Taint.exists_check_of_sumOk_call ScalarSums.absorb (VG.AArch64.VectorTaint.le_refl _) rfl
  padTaint := Taint.exists_check_of_sumOk_call ScalarSums.pad (VG.AArch64.VectorTaint.le_refl _) rfl
  squeezeTaint := Taint.exists_check_of_sumOk_call ScalarSums.squeeze (VG.AArch64.VectorTaint.le_refl _) rfl
  mldsaNttTaint := Callers.mldsaNttTaint _ scalarSums
  mldsaBallTaint := Callers.mldsaBallTaint _ scalarSums
  mldsaMaskTaint := Callers.mldsaMaskTaint _ scalarSums

  mldsaSeedsTaint := Callers.mldsaSeedsTaint _ scalarSums
  mldsaTrHashTaint := Callers.mldsaTrHashTaint _ scalarSums
  mldsaVerifyHashTaint := Callers.mldsaVerifyHashTaint _ scalarSums

  mldsaSignDecodeTaint := Callers.mldsaSignDecodeTaint _ scalarSums
  mldsaSignCommitTaint := Callers.mldsaSignCommitTaint _ scalarSums

end VG.Proof.Sha3.AArch64
