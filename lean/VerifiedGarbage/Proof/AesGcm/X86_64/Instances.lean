module

public import VerifiedGarbage.Proof.Gcm.PrecomputedContract
public import VerifiedGarbage.Proof.AesGcm.X86_64.Flag
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.Flagged
public import VerifiedGarbage.Proof.Gcm.PreparedPowers
public import VerifiedGarbage.Proof.AesGcm.Rounds
public import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.BlkCall
public import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Context
import Mathlib.Data.List.Basic
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Callee
public import VerifiedGarbage.Proof.Gcm.PreparedContract
public import VerifiedGarbage.Proof.Gcm.OutOfPlaceContract
public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.FrontFast
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.StreamTo
public import VerifiedGarbage.Proof.AesGcm.X86_64.VerifiedP
public import VerifiedGarbage.Proof.AesGcm.X86_64.Variant
public import VerifiedGarbage.Proof.AesGcm.X86_64.GhashImpls
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.Short
public import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Ghash
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Pow
import VerifiedGarbage.Proof.Gcm.X86_64.StitchR.Ok
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Tab
public import VerifiedGarbage.Proof.Gcm.Poly
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Bcast
import VerifiedGarbage.Proof.Gcm.Powers
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Loop
import VerifiedGarbage.Proof.AesGcm.X86_64.Fn
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Gcm.Split
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Verified
public import VerifiedGarbage.Proof.AesGcm.X86_64.StreamClrVerified
public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Verified
public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Fn
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.SealFin
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Ok
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Ct
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Ok
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.Verified
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.Gather
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.BlocksVerified
public import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksVerifiedP
public import VerifiedGarbage.Proof.Gcm.Prepared16Contract
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared16.Verified
public import VerifiedGarbage.Proof.AesGcm.ScratchSplit
import VerifiedGarbage.Proof.AesGcm.ScratchPrepared16
import VerifiedGarbage.Proof.AesGcm.Scratch
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.AesGcm.X86_64.Split.Verified
import VerifiedGarbage.Proof.AesGcm.ScratchPreparedTo
public import VerifiedGarbage.Proof.AesGcm.ScratchPrepared16To
public import VerifiedGarbage.Impl.AesGcm.X86_64.StreamTo
import Mathlib.Data.List.Dedup
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.CT
public import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Contract
import VerifiedGarbage.Proof.AesSiv.X86_64.Verified
import VerifiedGarbage.Proof.AesGcm.ScratchGather
public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Contract
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared16.BlocksVerified
public import VerifiedGarbage.Proof.AesGcm.X86_64.OpenTo.Verified
public import VerifiedGarbage.Proof.AesGcm.X86_64.OpenToSplit.Verified
public import VerifiedGarbage.Proof.AesGcm.X86_64.OpenSplit.Fn
public import VerifiedGarbage.Proof.AesGcm.X86_64.OpenSplit.Prefix
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchToDec.Loop
public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.DecTo
public import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Contract
public import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Piece
public import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Call
import VerifiedGarbage.Proof.Framework.X86_64.WidenArray

/-! ### `AesGcm.X86_64.Prepared.StreamCallee`, which only this module used -/

section

/-! # Prepared-context StreamCallee contracts -/

@[expose] public section

set_option linter.unusedSimpArgs false
namespace VG.Proof.AesGcm.X86_64.StreamTo
open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm (arg args rounds)

theorem encSpecPrepared_pre {s : State} (h : encCallPre CtxMode.prepared s) :
    (Proof.AesGcm.streamEncryptPreparedRoundsContract X86_64.abi 2608).pre s := by
  sig_split h
  rename_i a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a₁₇ a₁₈ a₁₉ a₂₀ a₂₁
  have a₂₂ := h
  clear h
  sig_pre [Proof.AesGcm.streamEncryptPreparedRoundsContract, Proof.Gcm.streamCryptPrecomputedSig, Proof.Gcm.streamCryptPrecomputedSig,
    Proof.Gcm.streamCryptPowersPre, X86_64.abi, X86_64.argRegs, List.range, List.range.loop]
  sig_reduce [Proof.AesGcm.streamEncryptPreparedRoundsContract, Proof.Gcm.streamCryptPrecomputedSig, Proof.Gcm.streamCryptPrecomputedSig,
    Proof.Gcm.streamCryptPowersPre, X86_64.abi, X86_64.argRegs, Proof.AesGcm.arg, Proof.AesGcm.args,
    Proof.AesGcm.ret, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop,
    VG.X86_64.below]
  simp only [Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, X86_64.stackArg, X86_64.stackArgAddr,
    VG.X86_64.below, Nat.mul_one, Proof.AesGcm.rounds, CtxMode.prepared, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowersRepr] at *
  sig_and_intros
  all_goals with_reducible assumption

theorem encSpecPrepared_post {s s' : State} (hR : Proof.AesGcm.rounds s)
    (h : (Proof.AesGcm.streamEncryptPreparedRoundsContract X86_64.abi 2608).post s s') :
    Proof.AesGcm.streamEncryptX86_64.post s s' := by
  sig_post [Proof.AesGcm.streamEncryptPreparedRoundsContract, Proof.Gcm.streamCryptPrecomputedSig, Proof.Gcm.streamCryptPrecomputedSig,
    Proof.Gcm.streamCryptPowersPre, X86_64.abi, X86_64.argRegs, Proof.AesGcm.streamEncryptRoundsPost] at h
  sig_reduce [Proof.AesGcm.streamEncryptPreparedRoundsContract, Proof.Gcm.streamCryptPrecomputedSig, Proof.Gcm.streamCryptPrecomputedSig, X86_64.abi,
    X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop] at h
  exact h hR

theorem encSpecPrepared_pub {s₁ s₂ : State} (h : encCallPub s₁ s₂) :
    (Proof.AesGcm.streamEncryptPreparedRoundsContract X86_64.abi 2608).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, aMd⟩ := h
  sig_pub [Proof.AesGcm.streamEncryptPreparedRoundsContract, Proof.Gcm.streamCryptPrecomputedSig, Proof.Gcm.streamCryptPrecomputedSig, X86_64.abi,
    X86_64.argRegs]
  sig_reduce [Proof.AesGcm.streamEncryptPreparedRoundsContract, Proof.Gcm.streamCryptPrecomputedSig, Proof.Gcm.streamCryptPrecomputedSig, X86_64.abi,
    X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop, Proof.AesGcm.arg]
  simp only [Proof.AesGcm.arg, X86_64.stackArg, X86_64.stackArgAddr] at a₈
  sig_and_intros
  all_goals first | with_reducible assumption | trivial

def EncFn.ofPrepared (f : Fn)
    (hv : Verified X86_64.target f.code (Proof.AesGcm.streamEncryptPreparedRoundsContract X86_64.abi 2608))
    (sp : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (xd : f.code.x86_64Depth ≤ 2608)
    (mx : f.code.allInstrs (fun i => !loadsMxcsr i) = true) : EncFn CtxMode.prepared where
  fn := f
  ok s h := by
    obtain ⟨t, s', he, ha, hp⟩ := hv.1 s (encSpecPrepared_pre h)
    exact ⟨t, s', he, ha, encSpecPrepared_post h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hp⟩
  ct s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂ := hv.2.1 s₁ s₂ t₁ t₂ s₁' s₂' (encSpecPrepared_pre h₁) (encSpecPrepared_pre h₂)
    (encSpecPrepared_pub hq) e₁ e₂
  sp := SpSafe.of_all sp
  xd := xd
  mx := mx
  spAll := sp

end VG.Proof.AesGcm.X86_64.StreamTo

end

end

/-! ### `AesGcm.X86_64.Prepared.GatherCallee`, which only this module used -/

section

/-! # Prepared-context GatherCallee contracts -/

@[expose] public section

set_option linter.unusedSimpArgs false
namespace VG.Proof.AesGcm.X86_64.Gather
open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm (arg args rounds)

theorem toSpecPrepared_pre {s : State} (h : toPre CtxMode.prepared s) :
    (Proof.Gcm.streamEncryptToPreparedContract X86_64.abi 4856).pre s := by
  sig_split h
  rename_i a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a₁₇ a₁₈ a₁₉ a₂₀ a₂₁ a₂₂ a₂₃ a₂₄ a₂₅ a₂₆ a₂₇
  have a₂₈ := h
  clear h
  sig_pre [Proof.Gcm.streamEncryptToPreparedContract, Proof.Gcm.streamEncryptToPreparedSig, Proof.Gcm.streamEncryptToPrecomputedSig,
    Proof.Gcm.streamEncryptToPreparedPre, X86_64.abi, X86_64.argRegs, List.range, List.range.loop]
  sig_reduce [Proof.Gcm.streamEncryptToPreparedContract, Proof.Gcm.streamEncryptToPreparedSig, Proof.Gcm.streamEncryptToPrecomputedSig,
    Proof.Gcm.streamEncryptToPreparedPre, X86_64.abi, X86_64.argRegs, Proof.AesGcm.arg, Proof.AesGcm.args,
    Proof.AesGcm.ret, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop,
    VG.X86_64.below]
  simp only [Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, X86_64.stackArg,
    X86_64.stackArgAddr, VG.X86_64.below, Nat.mul_one, Proof.AesGcm.rounds, CtxMode.prepared, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowersRepr] at *
  sig_and_intros
  all_goals first
    | with_reducible assumption
    | omega
    | exact congrArg (BitVec.setWidth 64) a₃

theorem toSpecPrepared_post {s s' : State} (hR : rounds s)
    (h : (Proof.Gcm.streamEncryptToPreparedContract X86_64.abi 4856).post s s') :
    Proof.AesGcm.streamToPost s s' := by
  sig_post [Proof.Gcm.streamEncryptToPreparedContract, Proof.Gcm.streamEncryptToPreparedSig, Proof.Gcm.streamEncryptToPrecomputedSig,
    Proof.Gcm.streamEncryptToPreparedPre, X86_64.abi, X86_64.argRegs, Proof.Gcm.streamEncryptToPost] at h
  sig_reduce [Proof.Gcm.streamEncryptToPreparedContract, Proof.Gcm.streamEncryptToPreparedSig, Proof.Gcm.streamEncryptToPrecomputedSig, X86_64.abi,
    X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop] at h
  exact h hR

theorem toSpecPrepared_pub {s₁ s₂ : State} (h : toPub s₁ s₂) :
    (Proof.Gcm.streamEncryptToPreparedContract X86_64.abi 4856).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, aMd⟩ := h
  sig_pub [Proof.Gcm.streamEncryptToPreparedContract, Proof.Gcm.streamEncryptToPreparedSig, Proof.Gcm.streamEncryptToPrecomputedSig, X86_64.abi,
    X86_64.argRegs]
  sig_reduce [Proof.Gcm.streamEncryptToPreparedContract, Proof.Gcm.streamEncryptToPreparedSig, Proof.Gcm.streamEncryptToPrecomputedSig, X86_64.abi,
    X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop, Proof.AesGcm.arg]
  simp only [Proof.AesGcm.arg, X86_64.stackArg, X86_64.stackArgAddr] at a₈ a₉ a₁₀
  sig_and_intros
  all_goals first | with_reducible assumption | trivial

def ToFn.ofPrepared (f : Fn)
    (hv : Verified X86_64.target f.code (Proof.Gcm.streamEncryptToPreparedContract X86_64.abi 4856))
    (sp : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (xd : f.code.x86_64Depth ≤ 4856)
    (mx : f.code.allInstrs (fun i => !loadsMxcsr i) = true) : ToFn CtxMode.prepared :=
  CallFn.ofSpec f hv (fun _ h => toSpecPrepared_pre h)
    (fun _ _ h h' => toSpecPrepared_post h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h')
    (fun _ _ h => toSpecPrepared_pub h) sp xd mx

end VG.Proof.AesGcm.X86_64.Gather

end

end

/-! ### `AesGcm.X86_64.Prepared.GatherSplit`, which only this module used -/

section

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, x86-64: `vg_aes_gcm_seal_split_prepared` called

Untrusted: everything here is checked by Lean. `vg_aes_gcm_seal_gather_prepared`
copies the slices after the first of a short text to the output and
encrypts the text by a call of `vg_aes_gcm_seal_split_prepared`, by its
shared contract, as `Gather/SplitCallee.lean` does for the other key
contexts.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Gather

open VG VG.X86_64
open VG.Impl.AesGcm.X86_64 (Fn)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm (arg args ret rounds)

theorem splitSpecR_pre {s : State} (h : splitPreK CtxMode.prepared s) :
    (Proof.Gcm.sealSplitPreparedContract X86_64.abi 2672).pre s := by
  sig_split h
  have a₀ := h
  clear h
  sig_pre [Proof.Gcm.sealSplitPreparedContract, Proof.Gcm.sealSplitPreparedSig, Proof.Gcm.sealSplitPrecomputedSig,
    Proof.Gcm.sealSplitPreparedPre, X86_64.abi, X86_64.argRegs, List.range, List.range.loop]
  sig_reduce [Proof.Gcm.sealSplitPreparedContract, Proof.Gcm.sealSplitPreparedSig, Proof.Gcm.sealSplitPrecomputedSig,
    Proof.Gcm.sealSplitPreparedPre, X86_64.abi, X86_64.argRegs, Proof.AesGcm.arg, Proof.AesGcm.args,
    Proof.AesGcm.ret, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop,
    VG.X86_64.below]
  simp only [Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, X86_64.stackArg,
    X86_64.stackArgAddr, VG.X86_64.below, Nat.mul_one, Proof.AesGcm.rounds, CtxMode.prepared, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowersRepr,
    BitVec.setWidth_eq] at *
  sig_and_intros
  all_goals first
    | with_reducible assumption
    | omega

theorem splitSpecR_post {M : CtxMode} {s s' : State}
    (h : (Proof.Gcm.sealSplitPreparedContract X86_64.abi 2672).post s s') (hR : rounds s) :
    (Proof.AesGcm.sealSplitX86_64M M).post s s' := by
  sig_post [Proof.Gcm.sealSplitPreparedContract, Proof.Gcm.sealSplitPreparedSig, Proof.Gcm.sealSplitPrecomputedSig,
    Proof.Gcm.sealSplitPreparedPre, X86_64.abi, X86_64.argRegs, Proof.Gcm.sealSplitPost] at h
  sig_reduce [Proof.Gcm.sealSplitPreparedContract, Proof.Gcm.sealSplitPreparedSig, Proof.Gcm.sealSplitPrecomputedSig,
    X86_64.abi, X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop] at h
  exact h hR

theorem splitSpecR_pub {s₁ s₂ : State} (h : splitPubK s₁ s₂) :
    (Proof.Gcm.sealSplitPreparedContract X86_64.abi 2672).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, aMd⟩ := h
  sig_pub [Proof.Gcm.sealSplitPreparedContract, Proof.Gcm.sealSplitPreparedSig, Proof.Gcm.sealSplitPrecomputedSig,
    X86_64.abi, X86_64.argRegs]
  sig_reduce [Proof.Gcm.sealSplitPreparedContract, Proof.Gcm.sealSplitPreparedSig, Proof.Gcm.sealSplitPrecomputedSig,
    X86_64.abi, X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop, Proof.AesGcm.arg]
  simp only [Proof.AesGcm.arg, X86_64.stackArg, X86_64.stackArgAddr] at a₈ a₉ a₁₀ a₁₁ a₁₂
  sig_and_intros
  all_goals first | with_reducible assumption | trivial

/-- `vg_aes_gcm_seal_split_prepared` from its shared contract. -/
def SplitFn.ofPrepared (f : Fn)
    (hv : Verified X86_64.target f.code (Proof.Gcm.sealSplitPreparedContract X86_64.abi 2672))
    (sp : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (xd : f.code.x86_64Depth ≤ 2672)
    (mx : f.code.allInstrs (fun i => !loadsMxcsr i) = true) : SplitFn CtxMode.prepared :=
  CallFn.ofSpec f hv (fun _ h => splitSpecR_pre h)
    (fun _ _ h h' => splitSpecR_post (M := CtxMode.prepared) h' h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (fun _ _ h => splitSpecR_pub h) sp xd mx

end VG.Proof.AesGcm.X86_64.Gather

end

end

/-! ### `AesGcm.X86_64.Short.Field`, which only this module used -/

section

/-! ### `AesGcm.X86_64.Short.Pow`, which only this module used -/

section

/-!
# AES-GCM's short path on x86-64: the powers of the hash subkey

Untrusted: everything here is checked by Lean, and computes in the field
(`Proof/Gcm/Poly.lean`). `powers` stores the table of powers that `ghash`
reads (`TabF`: group `j`, lane `l` is `Tₖ` with `x · Tₖ = Hᵏ`,
`k = 4 j + 4 - l`, which is `TabOk`, `tabOk_of_F`): `H'`–`H'⁴` in SSE
(`vg_ghash_pclmul`'s `hInv` and `pows`, `powSse_ok`), as group 0
(`pow4_ok`), then each further group from one below it times a power
(`StitchZ.powLoad_ok`, `powMore_ok`), as far as `m'` (in `rax`) needs. The
registers the first block leaves: `powHead_ok`. For the end of a long
`seal`, `finPow` leaves `H'` and `H'²` (`finPow_ok`), which multiply as one
and two steps of `GHASH` (`step1'`, `step2`, `finPow_facts`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Short

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Short VG.WriteBytes
open VG.Proof.AesGcm.X86_64 VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduceB prod Only const_ok ldrev_ok hInv_ok pows_ok)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- The table at `T` holds `n` groups of powers of `H`, in the field: lane
`l` of group `j` is `Tₖ` with `x · Tₖ = Hᵏ`, `k = 4 j + 4 - l`. -/
def TabF (m : Mem) (T : Addr) (H : Block) (n : Nat) : Prop :=
  ∀ j < n, ∀ l < 4, x * φ (m.readW (T + BitVec.ofNat 64 (64 * j + 16 * l)) 128) = φ H ^ (4 * j + 4 - l)

theorem x_φ_hInvF_hpow (H : Block) (k : Nat) :
    x * φ (VG.Proof.Gcm.X86_64.StitchZP.hInvF (Spec.Gcm.hpow H k)) = φ H ^ k := by
  rw [VG.Proof.Gcm.X86_64.StitchZP.hInvF, VG.Proof.Gcm.X86_64.Pclmul.x_φ_hInv, φ_hpow]

/-- `x` has an inverse. -/
theorem x_inv : ∃ y, x * y = 1 := ⟨_, by rw [VG.Proof.Gcm.X86_64.Pclmul.x_φ_hInv, φ_one]⟩

theorem tabOk_of_F {m : Mem} {T : Addr} {H : Block} {n : Nat} (h : TabF m T H n) : TabOk m T H n :=
  fun j hj l hl => φ_inj (by
    obtain ⟨y, hy⟩ := x_inv
    have e := (h j hj l hl).trans (x_φ_hInvF_hpow H (4 * j + 4 - l)).symm
    calc _ = y * (x * φ (m.readW (T + BitVec.ofNat 64 (64 * j + 16 * l)) 128)) := by
          rw [← mul_assoc, mul_comm y x, hy, one_mul]
      _ = _ := by rw [e, ← mul_assoc, mul_comm y x, hy, one_mul])

theorem F_of_tabOk {m : Mem} {T : Addr} {H : Block} {n : Nat} (h : TabOk m T H n) : TabF m T H n :=
  fun j hj l hl => by rw [h j hj l hl, x_φ_hInvF_hpow]

/-- `H'`–`H'⁴` in `xmm3`–`xmm6`, from the hash subkey at `r13 + 240`, and the
mask and the reduction constant in `xmm0` and `xmm1`. -/
theorem powSse_ok (s : State) (hin : InRegions (s.rd ++ s.wr) (s.gpr .r13 + BitVec.ofInt 64 ((240 : Nat) : Int)) 16) :
    WP isa (.block powSse) s fun t =>
      t.xmm .xmm0 = revMask ∧ t.xmm .xmm1 = poly ∧
      x * φ (t.xmm .xmm3) = φ (blockAt s.mem (s.gpr .r13 + BitVec.ofInt 64 ((240 : Nat) : Int))) ∧
      x * φ (t.xmm .xmm4) = φ (blockAt s.mem (s.gpr .r13 + BitVec.ofInt 64 ((240 : Nat) : Int))) ^ 2 ∧
      x * φ (t.xmm .xmm5) = φ (blockAt s.mem (s.gpr .r13 + BitVec.ofInt 64 ((240 : Nat) : Int))) ^ 3 ∧
      x * φ (t.xmm .xmm6) = φ (blockAt s.mem (s.gpr .r13 + BitVec.ofInt 64 ((240 : Nat) : Int))) ^ 4 ∧
      (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  simp only [powSse, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm0 _ s (by decide)) fun s₁ ⟨c₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm1 _ s₁ (by decide)) fun s₂ ⟨c₂, o₂⟩ => ?_
  have o₁₂ := o₁.trans o₂
  rw [WP.block_append_iff]
  refine WP.mono (ldrev_ok .xmm7 .r13 240 s₂ (by decide) (by rw [o₂.xmm _ (by decide), c₁, VG.Proof.Gcm.X86_64.Pclmul.rev_eq])
    (by rw [o₁₂.rd, o₁₂.wr, o₁₂.gpr _ (by decide)]; exact hin)) fun s₃ ⟨l₃, o₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (hInv_ok s₃) fun s₄ ⟨t₄, o₄⟩ => ?_
  have x1 : s₄.xmm .xmm1 = poly := by rw [o₄.xmm _ (by decide), o₃.xmm _ (by decide), c₂]
  refine WP.mono (pows_ok (H := blockAt s.mem (s.gpr .r13 + BitVec.ofInt 64 ((240 : Nat) : Int))) s₄ x1
    (by rw [t₄, l₃, o₁₂.mem, o₁₂.gpr _ (by decide)]))
    fun t ⟨H2, H3, H4, o⟩ => ?_
  have O := o₁₂.trans (o₃.trans (o₄.trans o))
  refine ⟨by rw [o.xmm _ (by decide), o₄.xmm _ (by decide), o₃.xmm _ (by decide), o₂.xmm _ (by decide), c₁,
    VG.Proof.Gcm.X86_64.Pclmul.rev_eq],
    by rw [o.xmm _ (by decide), x1], by rw [o.xmm _ (by decide), t₄, l₃, o₁₂.mem, o₁₂.gpr _ (by decide)],
    H2, H3, H4, O.gpr, O.mem, O.rd, O.wr⟩

/-- The register of `H'⁴⁻ˡ`, lane `l` of group 0. -/
def pr4 : Nat → XReg
  | 0 => .xmm6 | 1 => .xmm5 | 2 => .xmm4 | _ => .xmm3

/-- `H'⁴`, `H'³`, `H'²`, `H'` into the lanes of `zmm8`. -/
theorem pow4a_ok (s : State) :
    WP isa (.block [.vop (.vinserti128 .xmm8 .xmm6 .xmm5 1), .vop (.vinserti128 .xmm9 .xmm4 .xmm3 1),
        .zop (.vshufi32x4 .xmm8 .xmm8 .xmm9 0x44)]) s fun t =>
      (∀ l < 4, t.zlane .xmm8 l = s.xmm (pr4 l)) ∧ ZFrame [.xmm8, .xmm9] s t := by
  refine WP.mono (WP.zframe (rs := [.xmm8, .xmm9]) (by decide)
    (Q := fun t => ∀ l < 4, t.zlane .xmm8 l = s.xmm (pr4 l)) ?_) fun t h => h
  rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil fun l hl => ?_⟩
  simp only [VOp.exec]
  rcases (by omega_arith : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl
  all_goals simp (disch := decide) only [zlane_vshufi32x4, VG.Proof.Gcm.X86_64.StitchZ.shuf44_0, VG.Proof.Gcm.X86_64.StitchZ.shuf44_1,
    VG.Proof.Gcm.X86_64.StitchZ.shuf44_2, VG.Proof.Gcm.X86_64.StitchZ.shuf44_3, VG.Proof.Gcm.X86_64.StitchZ.State.zlane_setV256, State.zlane_setV_ne,
    reduceCtorEq, ↓reduceIte, Nat.one_ne_zero, BitVec.getLsbD_ofNat]
  all_goals simp [State.lane, State.zlane, State.setV, pr4]

/-- Group `j` of the table at `T` holds its powers of `H`. -/
def GrpOk (m : Mem) (T : Addr) (H : Block) (j : Nat) : Prop :=
  ∀ l < 4, x * φ (m.readW (T + BitVec.ofNat 64 (64 * j + 16 * l)) 128) = φ H ^ (4 * j + 4 - l)

/-- A group outside a 64-byte write is kept. -/
theorem GrpOk.keep {m m' : Mem} {T : Addr} {H : Block} {i j : Nat} (h : GrpOk m T H j)
    (f : Frame [⟨T + BitVec.ofNat 64 (64 * i), 64⟩] m m') (hij : i ≠ j) (hi : i < 8) (hj : j < 8) :
    GrpOk m' T H j := fun l hl => by
  rw [f.readW (r := ⟨T + BitVec.ofNat 64 (64 * j + 16 * l), 16⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint T (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
  exact h l hl

/-- `powLoad d k`: group `k + d / 64` from group `k`, times `zmm12`, whose
lanes are `Tₑ`. -/
theorem powLoadG_ok {T : Addr} {H : Block} {d k e : Nat} (hd : d = 64 * (e / 4)) (he : e % 4 = 0)
    (hk : k + d / 64 < 8) (s : State) (hr11 : s.gpr .r11 = T)
    (h1 : ∀ l < 4, s.zlane .xmm1 l = poly) (hB : ∀ l < 4, x * φ (s.zlane .xmm12 l) = φ H ^ e)
    (hG : GrpOk s.mem T H k) (hin : InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 (64 * k)) 64)
    (hout : InRegions s.wr (T + BitVec.ofNat 64 (d + 64 * k)) 64) :
    WP isa (.block (VG.Impl.Gcm.X86_64.StitchZ.powLoad d k)) s fun t =>
      GrpOk t.mem T H (k + d / 64) ∧ Frame [⟨T + BitVec.ofNat 64 (64 * (k + d / 64)), 64⟩] s.mem t.mem ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r, r ≠ .xmm7 → r ≠ .xmm8 → r ≠ .xmm9 → r ≠ .xmm10 → r ≠ .xmm11 → ∀ l < 4, t.zlane r l = s.zlane r l) := by
  have ea : ∀ n : Nat, s.gpr .r11 + BitVec.ofInt 64 ((n : Nat) : Int) = T + BitVec.ofNat 64 n := fun n => by
    rw [hr11, BitVec.ofInt_natCast]
  have hdk : d + 64 * k = 64 * (k + d / 64) := by omega_arith
  refine WP.mono (VG.Proof.Gcm.X86_64.StitchZ.powLoad_ok d k s h1 (by rw [ea]; exact hin) (by rw [ea]; exact hout))
    fun t ⟨⟨v, mt, hv⟩, gt, rdt, wrt, zt⟩ => ⟨fun l hl => ?_, ?_, gt, rdt, wrt, zt⟩
  · have ha : T + BitVec.ofNat 64 (64 * (k + d / 64) + 16 * l) =
        T + BitVec.ofNat 64 (d + 64 * k) + BitVec.ofNat 64 (16 * l) := by
      rw [add_ofNat_ofNat, show d + 64 * k + 16 * l = 64 * (k + d / 64) + 16 * l by omega_arith]
    rw [mt, ea, ha]
    have e := readW_writeW_inside s.mem (T + BitVec.ofNat 64 (d + 64 * k)) v (k := 16 * l) (n := 16)
      (by omega_arith) (by decide)
    rw [show 8 * 16 = 128 from rfl, show 8 * (16 * l) = 128 * l by omega_arith] at e
    rw [e, hv l hl, ea, add_ofNat_ofNat, VG.Proof.Gcm.X86_64.StitchZ.φ_lanemul (hG l hl) (hB l hl)]
    congr 1; omega_arith
  · rw [mt, ea, hdk]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) v (Region.contains_self _ _)

/-- While `powMore` runs: `n` groups of the table at `T`, written only in
the table, and the registers it does not write. -/
structure PI (s₀ : State) (T : Addr) (H : Block) (n : Nat) (t : State) : Prop where
  tab : TabF t.mem T H n
  frame : Frame [⟨T, 512⟩] s₀.mem t.mem
  gpr : t.gpr = s₀.gpr
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  z0 : ∀ l < 4, t.zlane .xmm0 l = s₀.zlane .xmm0 l
  z1 : ∀ l < 4, t.zlane .xmm1 l = s₀.zlane .xmm1 l

/-- Group `n` from group `k` (`powLoad d k`, `n = k + d / 64`). -/
theorem powLoadT_ok {s₀ : State} {T : Addr} {H : Block} {d k e n : Nat} (hd : d = 64 * (e / 4)) (he : e % 4 = 0)
    (hkn : k < n) (hn : n = k + d / 64) (hn8 : n < 8) (t : State) (hI : PI s₀ T H n t)
    (hr11 : t.gpr .r11 = T) (hB : ∀ l < 4, x * φ (t.zlane .xmm12 l) = φ H ^ e)
    (h1 : ∀ l < 4, s₀.zlane .xmm1 l = poly) (hw : Covers [⟨T, 512⟩] s₀.wr) :
    WP isa (.block (VG.Impl.Gcm.X86_64.StitchZ.powLoad d k)) t fun t' =>
      PI s₀ T H (n + 1) t' ∧ ∀ l < 4, t'.zlane .xmm12 l = t.zlane .xmm12 l := by
  have hwt : Covers [⟨T, 512⟩] t.wr := by rw [hI.wr]; exact hw
  refine WP.mono (powLoadG_ok hd he (by omega_arith) t hr11 (fun l hl => by rw [hI.z1 l hl, h1 l hl]) hB
    (hI.tab k hkn) (in_left (in_off hwt (by omega_arith) (by decide)))
    (in_off hwt (by omega_arith) (by decide))) fun t' ⟨g', f', gp', rd', wr', z'⟩ => ⟨⟨fun j hj => ?_, ?_,
      by rw [gp', hI.gpr], by rw [rd', hI.rd], by rw [wr', hI.wr], fun l hl => by rw [z' _ (by decide) (by decide)
      (by decide) (by decide) (by decide) l hl, hI.z0 l hl], fun l hl => by rw [z' _ (by decide) (by decide)
      (by decide) (by decide) (by decide) l hl, hI.z1 l hl]⟩,
    fun l hl => z' _ (by decide) (by decide) (by decide) (by decide) (by decide) l hl⟩
  · by_cases hjn : j = n
    · subst hjn; rw [hn]; exact g'
    · exact GrpOk.keep (hI.tab j (by omega_arith)) (i := n) (by rw [hn]; exact f') (by omega_arith) (by omega_arith) (by omega_arith)
  · exact hI.frame.trans (f'.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base T (by omega_arith)⟩)

/-- The broadcast of a power from the table into `zmm12`. -/
theorem bcastT_ok {s₀ : State} {T : Addr} {H : Block} {n j : Nat} (hj : j < n) (t : State)
    (hI : PI s₀ T H n t) (hr11 : t.gpr .r11 = T) (hw : Covers [⟨T, 512⟩] s₀.wr) (hj8 : j < 8) :
    WP isa (.block [.vbroadcasti32x4 .xmm12 (at_ .r11 (64 * j))]) t fun t' =>
      PI s₀ T H n t' ∧ (∀ l < 4, x * φ (t'.zlane .xmm12 l) = φ H ^ (4 * j + 4)) := by
  have hin : InRegions (t.rd ++ t.wr) (t.gpr .r11 + BitVec.ofNat 64 (64 * j)) 16 := by
    rw [hr11, hI.rd, hI.wr]; exact in_left (in_off hw (by omega_arith) (by decide))
  rw [WP.block_cons_iff]
  refine ⟨_, VG.Proof.Gcm.X86_64.StitchZ.bcast_exec .xmm12 .r11 (64 * j) t hin, WP.block_nil ⟨?_, fun l hl => ?_⟩⟩
  · exact ⟨hI.tab, hI.frame, hI.gpr, hI.rd, hI.wr,
      fun l hl => by rw [State.zlane_setZ_ne _ (by decide) _ _ _ _ hl, hI.z0 l hl],
      fun l hl => by rw [State.zlane_setZ_ne _ (by decide) _ _ _ _ hl, hI.z1 l hl]⟩
  · rw [VG.Proof.Gcm.X86_64.StitchZ.zlane_bcast _ _ _ hl, hr11]
    have := hI.tab j hj 0 (by decide)
    rwa [Nat.mul_zero, Nat.add_zero, Nat.sub_zero] at this

theorem PI.mono {s₀ : State} {T : Addr} {H : Block} {n m : Nat} {t : State} (h : PI s₀ T H n t) (hm : m ≤ n) :
    PI s₀ T H m t :=
  ⟨fun j hj => h.tab j (by omega_arith), h.frame, h.gpr, h.rd, h.wr, h.z0, h.z1⟩

/-- `cmp rax, k` in `powMore`. -/
theorem cmpRax_ok {s₀ : State} {T : Addr} {H : Block} {n g k : Nat} (t : State) (hI : PI s₀ T H n t)
    (hrax : t.gpr .rax = BitVec.ofNat 64 (4 * g)) (hg : g ≤ 8) (hk : k < 2 ^ 31) :
    WP isa (.block [.alu .cmp .rax (imm k)]) t fun t' =>
      t'.cf = some (decide (4 * g < k)) ∧ PI s₀ T H n t' ∧ (∀ l < 4, t'.zlane .xmm12 l = t.zlane .xmm12 l) := by
  apply WP.of_runBlock
  refine ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, imm]; rfl,
    ?_, ?_, ?_⟩
  · rw [cf_arithFlags, hrax, imm_eq hk, toNat_ofNat_of_lt (by omega_arith), toNat_ofNat_of_lt (by omega_arith)]
  · exact ⟨hI.tab, hI.frame, hI.gpr, hI.rd, hI.wr, hI.z0, hI.z1⟩
  · exact fun _ _ => rfl

/-- The groups of powers after the first, as far as `m' = 4 g` needs. -/
theorem powMore_ok {s₀ : State} {T : Addr} {H : Block} {g : Nat} (hg1 : 1 ≤ g) (hg : g ≤ 8) (t : State)
    (hI : PI s₀ T H 1 t) (hr11 : t.gpr .r11 = T) (hrax : t.gpr .rax = BitVec.ofNat 64 (4 * g))
    (h1 : ∀ l < 4, s₀.zlane .xmm1 l = poly) (hw : Covers [⟨T, 512⟩] s₀.wr) :
    WP isa powMore t (PI s₀ T H g) := by
  have r11 : ∀ {n} {t' : State}, PI s₀ T H n t' → t'.gpr .r11 = T := fun h => by rw [h.gpr, ← hI.gpr, hr11]
  have rax : ∀ {n} {t' : State}, PI s₀ T H n t' → t'.gpr .rax = BitVec.ofNat 64 (4 * g) := fun h => by
    rw [h.gpr, ← hI.gpr, hrax]
  refine WP.seq (WP.mono (cmpRax_ok t hI hrax hg (by decide)) fun t₁ ⟨c₁, I₁, _⟩ => ?_)
  refine WP.ite (decide (4 * g < 5)) (by simp only [eval, c₁]) (fun h => WP.block_nil (I₁.mono ?_)) fun h => ?_
  · have := of_decide_eq_true h; omega_arith
  have h₁ : 2 ≤ g := by have := of_decide_eq_false h; omega_arith
  -- `H'⁸`–`H'⁵`.
  rw [show ([.vbroadcasti32x4 .xmm12 (at_ .r11 0)] ++ VG.Impl.Gcm.X86_64.StitchZ.powLoad 64 0 ++
      [.alu .cmp .rax (imm 9)] : List Instr) = [.vbroadcasti32x4 .xmm12 (at_ .r11 (64 * 0))] ++
      (VG.Impl.Gcm.X86_64.StitchZ.powLoad 64 0 ++ [.alu .cmp .rax (imm 9)]) from rfl]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (bcastT_ok (by decide) t₁ I₁ (r11 I₁) hw (by decide)) fun t₂ ⟨I₂, b₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (powLoadT_ok (e := 4) rfl rfl (by decide) rfl (by decide) t₂ I₂ (r11 I₂) b₂ h1 hw)
    fun t₃ ⟨I₃, _⟩ => ?_
  refine WP.mono (cmpRax_ok t₃ I₃ (rax I₃) hg (by decide)) fun t₄ ⟨c₄, I₄, _⟩ => ?_
  refine WP.ite (decide (4 * g < 9)) (by simp only [eval, c₄]) (fun h => WP.block_nil (I₄.mono ?_)) fun h => ?_
  · have := of_decide_eq_true h; omega_arith
  have h₂ : 3 ≤ g := by have := of_decide_eq_false h; omega_arith
  -- `H'¹⁶`–`H'⁹`.
  rw [show ([.vbroadcasti32x4 .xmm12 (at_ .r11 64)] ++
      (List.range 2).flatMap (VG.Impl.Gcm.X86_64.StitchZ.powLoad 128) ++ [.alu .cmp .rax (imm 17)] : List Instr) =
      [.vbroadcasti32x4 .xmm12 (at_ .r11 (64 * 1))] ++ (VG.Impl.Gcm.X86_64.StitchZ.powLoad 128 0 ++
      (VG.Impl.Gcm.X86_64.StitchZ.powLoad 128 1 ++ [.alu .cmp .rax (imm 17)])) from rfl]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (bcastT_ok (by decide) t₄ I₄ (r11 I₄) hw (by decide)) fun t₅ ⟨I₅, b₅⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (powLoadT_ok (e := 8) rfl rfl (by decide) rfl (by decide) t₅ I₅ (r11 I₅) b₅ h1 hw)
    fun t₆ ⟨I₆, z₆⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (powLoadT_ok (e := 8) rfl rfl (by decide) rfl (by decide) t₆ I₆ (r11 I₆)
    (fun l hl => by rw [z₆ l hl]; exact b₅ l hl) h1 hw) fun t₇ ⟨I₇, _⟩ => ?_
  refine WP.mono (cmpRax_ok t₇ I₇ (rax I₇) hg (by decide)) fun t₈ ⟨c₈, I₈, _⟩ => ?_
  refine WP.ite (decide (4 * g < 17)) (by simp only [eval, c₈]) (fun h => WP.block_nil (I₈.mono ?_)) fun h => ?_
  · have := of_decide_eq_true h; omega_arith
  -- `H'³²`–`H'¹⁷`.
  rw [show (.vbroadcasti32x4 .xmm12 (at_ .r11 192) ::
      (List.range 4).flatMap (VG.Impl.Gcm.X86_64.StitchZ.powLoad 256) : List Instr) =
      [.vbroadcasti32x4 .xmm12 (at_ .r11 (64 * 3))] ++ (VG.Impl.Gcm.X86_64.StitchZ.powLoad 256 0 ++
      (VG.Impl.Gcm.X86_64.StitchZ.powLoad 256 1 ++ (VG.Impl.Gcm.X86_64.StitchZ.powLoad 256 2 ++
      VG.Impl.Gcm.X86_64.StitchZ.powLoad 256 3))) from rfl]
  rw [WP.block_append_iff]
  refine WP.mono (bcastT_ok (by decide) t₈ I₈ (r11 I₈) hw (by decide)) fun u₁ ⟨J₁, b₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (powLoadT_ok (e := 16) rfl rfl (by decide) rfl (by decide) u₁ J₁ (r11 J₁) b₁ h1 hw)
    fun u₂ ⟨J₂, z₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (powLoadT_ok (e := 16) rfl rfl (by decide) rfl (by decide) u₂ J₂ (r11 J₂)
    (fun l hl => by rw [z₂ l hl]; exact b₁ l hl) h1 hw) fun u₃ ⟨J₃, z₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (powLoadT_ok (e := 16) rfl rfl (by decide) rfl (by decide) u₃ J₃ (r11 J₃)
    (fun l hl => by rw [z₃ l hl, z₂ l hl]; exact b₁ l hl) h1 hw) fun u₄ ⟨J₄, z₄⟩ => ?_
  refine WP.mono (powLoadT_ok (e := 16) rfl rfl (by decide) rfl (by decide) u₄ J₄ (r11 J₄)
    (fun l hl => by rw [z₄ l hl, z₃ l hl, z₂ l hl]; exact b₁ l hl) h1 hw) fun u₅ ⟨J₅, _⟩ => J₅.mono hg

/-- Group 0 stored. -/
theorem store8_ok (t : State) {T : Addr} (hr11 : t.gpr .r11 = T) (hw : InRegions t.wr T 64) :
    WP isa (.block [.vmovdqu32Store (at_ .r11 0) .xmm8]) t fun t' =>
      t'.mem = t.mem.writeW T (t.zmm .xmm8) ∧ t'.gpr = t.gpr ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      ∀ r l, t'.zlane r l = t.zlane r l := by
  have e : t.gpr .r11 + BitVec.ofInt 64 ((0 : Nat) : Int) = T := by rw [hr11, BitVec.ofInt_natCast, BitVec.add_zero]
  rw [WP.block_cons_iff]
  refine ⟨_, by simp only [isa, exec, State.store512_eq, State.ea, at_, e, hw, ite_true]; rfl, WP.block_nil ?_⟩
  exact ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

/-- The table of powers of the hash subkey, `m' = 4 g` of them at least, at
`W + 1536`. -/
theorem powers_ok {Ctx W SP : Addr} {g : Nat} (s : State) (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s)
    (hmp : s.mem.readW (W + BitVec.ofNat 64 288) 64 = BitVec.ofNat 64 (4 * g)) (hg1 : 1 ≤ g) (hg : g ≤ 8) :
    WP isa powers s fun t =>
      TabOk t.mem (W + BitVec.ofNat 64 1536) (Spec.Gcm.ctxH s.mem Ctx) g ∧
      Frame [⟨W + BitVec.ofNat 64 1536, 512⟩] s.mem t.mem ∧
      (∀ l < 4, t.zlane .xmm0 l = revMask) ∧ (∀ l < 4, t.zlane .xmm1 l = poly) ∧
      (∀ r, r ≠ .rax → r ≠ .r11 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hT : Covers [⟨W + BitVec.ofNat 64 1536, 512⟩] s.wr := he.perm.wC (by decide)
  have e240 : s.gpr .r13 + BitVec.ofInt 64 ((240 : Nat) : Int) = Ctx + BitVec.ofNat 64 240 := by
    rw [he.r13, BitVec.ofInt_natCast]
  rw [powers, show powSse ++ ptr .r11 .r15 tbO ++ pow4 ++ [.mov .rax (.mem (at_ .r15 mpO))] =
    powSse ++ (ptr .r11 .r15 tbO ++ ([.vop (.vinserti128 .xmm8 .xmm6 .xmm5 1), .vop (.vinserti128 .xmm9 .xmm4 .xmm3 1),
      .zop (.vshufi32x4 .xmm8 .xmm8 .xmm9 0x44)] ++ ([.vmovdqu32Store (at_ .r11 0) .xmm8] ++
      (([.vop (.vinserti128 .xmm0 .xmm0 .xmm0 1), .zop (.vshufi32x4 .xmm0 .xmm0 .xmm0 0x44)] ++
        [.vop (.vinserti128 .xmm1 .xmm1 .xmm1 1), .zop (.vshufi32x4 .xmm1 .xmm1 .xmm1 0x44)]) ++
      [.mov .rax (.mem (at_ .r15 mpO))])))) from rfl]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (powSse_ok s (by rw [e240]; exact he.perm.ctxR (by decide)))
    fun s₁ ⟨x0, x1, H1, H2, H3, H4, g₁, m₁, rd₁, wr₁⟩ => ?_
  rw [e240, ← VG.Proof.AesGcm.X86_64.ctxH_eq] at H1 H2 H3 H4
  rw [WP.block_append_iff]
  obtain ⟨s₂, run₂, r11₂, g₂, m₂, rd₂, wr₂, x₂⟩ : ∃ s₂, runBlock isa (ptr .r11 .r15 tbO) s₁ = some s₂ ∧
      s₂.gpr .r11 = W + BitVec.ofNat 64 1536 ∧ (∀ r, r ≠ .r11 → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧
      s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr ∧ ∀ r l, s₂.zlane r l = s₁.zlane r l := by
    refine ⟨_, by xrun [tbO], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, gpr_arithFlags, g₁ _ (by decide : Reg.r15 ≠ .rax), he.r15]
    · intro r hr; simp [gpr_setReg, gpr_arithFlags, hr]
    all_goals first | rfl | exact fun _ _ => rfl
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [WP.block_append_iff]
  refine WP.mono (pow4a_ok s₂) fun s₃ ⟨z8, f₃⟩ => ?_
  rw [WP.block_append_iff]
  have hT₃ : InRegions s₃.wr (W + BitVec.ofNat 64 1536) 64 := by
    rw [f₃.wr, wr₂, wr₁]; exact he.perm.wW (by decide)
  refine WP.mono (store8_ok s₃ (by rw [f₃.gpr, r11₂]) hT₃) fun s₄ ⟨m₄, g₄, rd₄, wr₄, z₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pow4c_ok s₄) fun s₅ ⟨c0, c1, f₅⟩ => ?_
  obtain ⟨s₆, run₆, rax₆, g₆, m₆, rd₆, wr₆, z₆⟩ : ∃ s₆, runBlock isa [.mov .rax (.mem (at_ .r15 mpO))] s₅ = some s₆ ∧
      s₆.gpr .rax = BitVec.ofNat 64 (4 * g) ∧ (∀ r, r ≠ .rax → s₆.gpr r = s₅.gpr r) ∧ s₆.mem = s₅.mem ∧
      s₆.rd = s₅.rd ∧ s₆.wr = s₅.wr ∧ ∀ r l, s₆.zlane r l = s₅.zlane r l := by
    have r15₅ : s₅.gpr .r15 = W := by
      rw [f₅.gpr, g₄, f₃.gpr, g₂ _ (by decide), g₁ _ (by decide), he.r15]
    have mm : s₅.mem.readW (W + BitVec.ofNat 64 288) 64 = BitVec.ofNat 64 (4 * g) := by
      rw [f₅.mem, m₄, ((Frame.refl _ _).writeW (List.mem_singleton_self _) (s₃.zmm .xmm8)
        (Region.contains_self _ _)).readW (r := ⟨W + BitVec.ofNat 64 288, 8⟩) (Region.contains_self _ _)
        (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)) (by decide),
        f₃.mem, m₂, m₁, hmp]
    have r288 : InRegions (s₅.rd ++ s₅.wr) (W + BitVec.ofNat 64 288) 8 := by
      rw [f₅.rd, f₅.wr, rd₄, wr₄, f₃.rd, f₃.wr, rd₂, wr₂, rd₁, wr₁]; exact he.perm.wR (by decide)
    refine ⟨_, by xrun [r15₅, mm, r288, mpO], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · intro r hr; simp [gpr_setReg, hr]
    all_goals first | rfl | exact fun _ _ => rfl
  refine WP.of_runBlock ⟨s₆, run₆, ?_⟩
  -- Group 0 of the table, and what `powMore` keeps.
  have hw₆ : Covers [⟨W + BitVec.ofNat 64 1536, 512⟩] s₆.wr := by
    rw [wr₆, f₅.wr, wr₄, f₃.wr, wr₂, wr₁]; exact hT
  have x2 : ∀ r, s₂.xmm r = s₁.xmm r := fun r => x₂ r 0
  have I₆ : PI s₆ (W + BitVec.ofNat 64 1536) (Spec.Gcm.ctxH s.mem Ctx) 1 s₆ := by
    refine ⟨fun j hj l hl => ?_, Frame.refl _ _, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩
    have hj0 : j = 0 := by omega_arith
    subst hj0
    have e := readW_writeW_inside s₃.mem (W + BitVec.ofNat 64 1536) (s₃.zmm .xmm8) (k := 16 * l) (n := 16)
      (by omega_arith) (by decide)
    rw [show 8 * 16 = 128 from rfl, show 8 * (16 * l) = 128 * l by omega_arith] at e
    rw [m₆, f₅.mem, m₄, Nat.mul_zero, Nat.zero_add, e, VG.Proof.Aes.X86_64.VaesZ.zmm_lane _ _ hl, z8 l hl, x2]
    rcases (by omega_arith : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl
    · exact H4
    · exact H3
    · exact H2
    · rw [show 4 * 0 + 4 - 3 = 1 from rfl, pow_one]; exact H1
  have xs : ∀ r, r ≠ .xmm8 → r ≠ .xmm9 → s₄.xmm r = s₁.xmm r := fun r h8 h9 => by
    rw [show s₄.xmm r = s₄.zlane r 0 from rfl, z₄, f₃.zlane r (by simp [h8, h9]) 0 (by decide)]
    exact x2 r
  refine WP.mono (powMore_ok hg1 hg s₆ I₆
    (by rw [g₆ _ (by decide), f₅.gpr, g₄, f₃.gpr, r11₂]) rax₆
    (fun l hl => by rw [z₆, c1 l hl, xs _ (by decide) (by decide), x1]) hw₆)
    fun t I => ⟨tabOk_of_F I.tab, ?_, fun l hl => ?_, fun l hl => ?_, fun r ha hb => ?_, ?_, ?_⟩
  · have f₄ : Frame [⟨W + BitVec.ofNat 64 1536, 512⟩] s.mem s₆.mem := by
      rw [m₆, f₅.mem, m₄, ← m₁, ← m₂, ← f₃.mem]
      exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) (s₃.zmm .xmm8)
        (Region.contains_self _ _)).sub fun r hr => ⟨_, List.mem_singleton_self _, by
          simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)⟩
    exact f₄.trans I.frame
  · rw [I.z0 l hl, z₆, c0 l hl, xs _ (by decide) (by decide), x0]
  · rw [I.z1 l hl, z₆, c1 l hl, xs _ (by decide) (by decide), x1]
  · rw [I.gpr, g₆ r ha, f₅.gpr, g₄, f₃.gpr, g₂ r hb, g₁ r ha]
  · rw [I.rd, rd₆, f₅.rd, rd₄, f₃.rd, rd₂, rd₁]
  · rw [I.wr, wr₆, f₅.wr, wr₄, f₃.wr, wr₂, wr₁]

/-- `powers`' first block: `r11` at the table and `rax` the powers needed. -/
theorem powHead_ok {Ctx W SP : Addr} {g : Nat} (s : State) (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s)
    (hmp : s.mem.readW (W + BitVec.ofNat 64 288) 64 = BitVec.ofNat 64 (4 * g)) :
    WP isa (.block (powSse ++ ptr .r11 .r15 tbO ++ pow4 ++ ([.mov .rax (.mem (at_ .r15 mpO))] : List Instr))) s
      fun t =>
      t.gpr .rax = BitVec.ofNat 64 (4 * g) ∧ t.gpr .r11 = W + BitVec.ofNat 64 1536 := by
  have e240 : s.gpr .r13 + BitVec.ofInt 64 ((240 : Nat) : Int) = Ctx + BitVec.ofNat 64 240 := by
    rw [he.r13, BitVec.ofInt_natCast]
  rw [show powSse ++ ptr .r11 .r15 tbO ++ pow4 ++ [.mov .rax (.mem (at_ .r15 mpO))] =
    powSse ++ (ptr .r11 .r15 tbO ++ ([.vop (.vinserti128 .xmm8 .xmm6 .xmm5 1), .vop (.vinserti128 .xmm9 .xmm4 .xmm3 1),
      .zop (.vshufi32x4 .xmm8 .xmm8 .xmm9 0x44)] ++ ([.vmovdqu32Store (at_ .r11 0) .xmm8] ++
      (([.vop (.vinserti128 .xmm0 .xmm0 .xmm0 1), .zop (.vshufi32x4 .xmm0 .xmm0 .xmm0 0x44)] ++
        [.vop (.vinserti128 .xmm1 .xmm1 .xmm1 1), .zop (.vshufi32x4 .xmm1 .xmm1 .xmm1 0x44)]) ++
      [.mov .rax (.mem (at_ .r15 mpO))])))) from rfl]
  rw [WP.block_append_iff]
  refine WP.mono (powSse_ok s (by rw [e240]; exact he.perm.ctxR (by decide)))
    fun s₁ ⟨_, _, _, _, _, _, g₁, m₁, rd₁, wr₁⟩ => ?_
  rw [WP.block_append_iff]
  obtain ⟨s₂, run₂, r11₂, g₂, m₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa (ptr .r11 .r15 tbO) s₁ = some s₂ ∧
      s₂.gpr .r11 = W + BitVec.ofNat 64 1536 ∧ (∀ r, r ≠ .r11 → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧
      s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by xrun [tbO], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, gpr_arithFlags, g₁ _ (by decide : Reg.r15 ≠ .rax), he.r15]
    · intro r hr; simp [gpr_setReg, gpr_arithFlags, hr]
    all_goals rfl
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [WP.block_append_iff]
  refine WP.mono (pow4a_ok s₂) fun s₃ ⟨_, f₃⟩ => ?_
  rw [WP.block_append_iff]
  have hT₃ : InRegions s₃.wr (W + BitVec.ofNat 64 1536) 64 := by
    rw [f₃.wr, wr₂, wr₁]; exact he.perm.wW (by decide)
  refine WP.mono (store8_ok s₃ (by rw [f₃.gpr, r11₂]) hT₃) fun s₄ ⟨m₄, g₄, rd₄, wr₄, _⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pow4c_ok s₄) fun s₅ ⟨_, _, f₅⟩ => ?_
  have r15₅ : s₅.gpr .r15 = W := by
    rw [f₅.gpr, g₄, f₃.gpr, g₂ _ (by decide), g₁ _ (by decide), he.r15]
  have mm : s₅.mem.readW (W + BitVec.ofNat 64 288) 64 = BitVec.ofNat 64 (4 * g) := by
    rw [f₅.mem, m₄, ((Frame.refl _ _).writeW (List.mem_singleton_self _) (s₃.zmm .xmm8)
      (Region.contains_self _ _)).readW (r := ⟨W + BitVec.ofNat 64 288, 8⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)) (by decide),
      f₃.mem, m₂, m₁, hmp]
  have r288 : InRegions (s₅.rd ++ s₅.wr) (W + BitVec.ofNat 64 288) 8 := by
    rw [f₅.rd, f₅.wr, rd₄, wr₄, f₃.rd, f₃.wr, rd₂, wr₂, rd₁, wr₁]; exact he.perm.wR (by decide)
  refine WP.of_runBlock ⟨_, by xrun [r15₅, mm, r288, mpO], ?_, ?_⟩
  · simp [gpr_setReg]
  · simp [gpr_setReg, f₅.gpr, g₄, f₃.gpr, r11₂]

/-! ## `H'` and `H'²` for the end of a long `seal` -/

section
open VG.Proof.Gcm.X86_64.Pclmul (const_ok ldrev_ok hInv_ok mul_ok Only)
open VG.Spec.Gcm (Block blockAt)

/-- `H'` in `xmm3` and `H'²` in `xmm6`, from the hash subkey at `r13 + 240`,
and the mask and the reduction constant in `xmm0` and `xmm1`. -/
theorem finPow_ok (s : State) (hin : InRegions (s.rd ++ s.wr) (s.gpr .r13 + BitVec.ofInt 64 ((240 : Nat) : Int)) 16) :
    WP isa (.block finPow) s fun t =>
      t.xmm .xmm0 = revMask ∧ t.xmm .xmm1 = poly ∧
      x * φ (t.xmm .xmm3) = φ (blockAt s.mem (s.gpr .r13 + BitVec.ofInt 64 ((240 : Nat) : Int))) ∧
      x * φ (t.xmm .xmm6) = φ (blockAt s.mem (s.gpr .r13 + BitVec.ofInt 64 ((240 : Nat) : Int))) ^ 2 ∧
      Only [.xmm0, .xmm1, .xmm3, .xmm6, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm12, .xmm13, .xmm14] s t := by
  simp only [finPow, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm0 _ s (by decide)) fun s₁ ⟨c₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm1 _ s₁ (by decide)) fun s₂ ⟨c₂, o₂⟩ => ?_
  have o₁₂ := o₁.trans o₂
  rw [WP.block_append_iff]
  refine WP.mono (ldrev_ok .xmm7 .r13 240 s₂ (by decide) (by rw [o₂.xmm _ (by decide), c₁, VG.Proof.Gcm.X86_64.Pclmul.rev_eq])
    (by rw [o₁₂.rd, o₁₂.wr, o₁₂.gpr _ (by decide)]; exact hin)) fun s₃ ⟨l₃, o₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (hInv_ok s₃) fun s₄ ⟨t₄, o₄⟩ => ?_
  have x1 : s₄.xmm .xmm1 = poly := by rw [o₄.xmm _ (by decide), o₃.xmm _ (by decide), c₂]
  refine WP.mono (mul_ok .xmm6 .xmm3 .xmm3 s₄ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) x1)
    fun t ⟨m, o⟩ => ?_
  have hH : x * φ (s₄.xmm .xmm3) = φ (blockAt s.mem (s.gpr .r13 + BitVec.ofInt 64 ((240 : Nat) : Int))) := by
    rw [t₄, l₃, o₁₂.mem, o₁₂.gpr _ (by decide)]
  have O := o₁₂.trans (o₃.trans (o₄.trans o))
  refine ⟨by rw [o.xmm _ (by decide), o₄.xmm _ (by decide), o₃.xmm _ (by decide), o₂.xmm _ (by decide), c₁,
    VG.Proof.Gcm.X86_64.Pclmul.rev_eq],
    by rw [o.xmm _ (by decide), x1], by rw [o.xmm _ (by decide)]; exact hH, ?_, O.weaken fun r hr => ?_⟩
  · rw [m, show ∀ a : VG.Proof.Gcm.Poly.Q, x * (x * a * a) = (x * a) * (x * a) from fun a => by ring, hH]; ring
  · revert hr; cases r <;> decide

/-- Two blocks, the first with `Y`, in one product: `GHASH` over them from `Y`. -/
theorem step2 (H Y X₁ X₂ T₁ T₂ : Block) (h₁ : x * φ T₁ = φ H) (h₂ : x * φ T₂ = φ H ^ 2) :
    VG.Proof.Gcm.X86_64.Pclmul.reduce ((VG.Proof.Gcm.X86_64.Pclmul.Prod.zero.acc (Y ^^^ X₁) T₂).acc X₂ T₁) =
      Spec.Gcm.ghashFrom H Y [X₁, X₂] := by
  apply φ_inj
  simp only [Spec.Gcm.ghashFrom, List.foldl_cons, List.foldl_nil, VG.Proof.Gcm.X86_64.Pclmul.φ_reduce,
    VG.Proof.Gcm.X86_64.Pclmul.Prod.val_acc, VG.Proof.Gcm.X86_64.Pclmul.Prod.val_zero, φ_mul, φ_xor]
  linear_combination (φ Y + φ X₁) * h₂ + φ X₂ * h₁

/-- Three blocks, `Y` added to the first: `GHASH` over them from `Y`. -/
theorem step3 (H Y X₁ X₂ X₃ T₁ T₂ T₃ : Block) (h₁ : x * φ T₁ = φ H) (h₂ : x * φ T₂ = φ H ^ 2)
    (h₃ : x * φ T₃ = φ H ^ 3) :
    VG.Proof.Gcm.X86_64.Pclmul.reduce
      (((VG.Proof.Gcm.X86_64.Pclmul.Prod.zero.acc (Y ^^^ X₁) T₃).acc X₂ T₂).acc X₃ T₁) =
      Spec.Gcm.ghashFrom H Y [X₁, X₂, X₃] := by
  apply φ_inj
  simp only [Spec.Gcm.ghashFrom, List.foldl_cons, List.foldl_nil, VG.Proof.Gcm.X86_64.Pclmul.φ_reduce,
    VG.Proof.Gcm.X86_64.Pclmul.Prod.val_acc, VG.Proof.Gcm.X86_64.Pclmul.Prod.val_zero, φ_mul, φ_xor]
  linear_combination (φ Y + φ X₁) * h₃ + φ X₂ * h₂ + φ X₃ * h₁

/-- One block, with `Y`: `GHASH` over it from `Y`. -/
theorem step1' (H Y X₁ T₁ : Block) (h₁ : x * φ T₁ = φ H) :
    VG.Proof.Gcm.X86_64.Pclmul.reduce (VG.Proof.Gcm.X86_64.Pclmul.Prod.zero.acc (Y ^^^ X₁) T₁) =
      Spec.Gcm.ghashFrom H Y [X₁] := by
  rw [VG.Proof.Gcm.X86_64.Pclmul.step1 H Y X₁ T₁ h₁]; rfl

/-- `finPow`, as `ShortFacts` states it. -/
theorem finPow_facts (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .r13 + BitVec.ofInt 64 ((240 : Nat) : Int)) 16) :
    WP isa (.block finPow) s fun t =>
      t.xmm .xmm0 = revMask ∧ t.xmm .xmm1 = poly ∧
      IsH1 (blockAt s.mem (s.gpr .r13 + BitVec.ofInt 64 ((240 : Nat) : Int))) (t.xmm .xmm3) ∧
      IsH2 (blockAt s.mem (s.gpr .r13 + BitVec.ofInt 64 ((240 : Nat) : Int))) (t.xmm .xmm3) (t.xmm .xmm6) ∧
      Only [.xmm0, .xmm1, .xmm3, .xmm6, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm12, .xmm13, .xmm14] s t :=
  WP.mono (finPow_ok s hin) fun _ ⟨x0, x1, h1, h2, o⟩ =>
    ⟨x0, x1, fun _ _ => step1' _ _ _ _ h1, fun _ _ _ => step2 _ _ _ _ _ _ h1 h2, o⟩

end

end VG.Proof.AesGcm.X86_64.Short

end

end

/-!
# AES-GCM's short path on x86-64: GHASH of the buffer, in the field

Untrusted: everything here is checked by Lean. With the table of powers
(`TabOk`), the four lanes' sums that `ghash_ok` reduces and adds are `GHASH`
over the `4 g` blocks of the buffer (`gacc_ghash`): lane `l` of group `j` of
the buffer is multiplied by `H⁴ᵍ⁻⁴ʲ⁻ˡ`, which is what `GHASH` from 0 does
with block `4 j + l` of `4 g`. With `Pow.lean`, this is all the short path
needs from the field (`shortFacts`), which the other modules take as an
argument so as not to import its algebra.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Short

open VG VG.X86_64 VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduceB φ_reduceB)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom mul)
open VG.Proof.Gcm (ghashFrom_append ghashFrom_nil blocksAt_add)

theorem φ_ghashFrom4 (H y a b c d : Block) :
    φ (ghashFrom H y [a, b, c, d]) =
      φ y * φ H ^ 4 + φ a * φ H ^ 4 + φ b * φ H ^ 3 + φ c * φ H ^ 2 + φ d * φ H := by
  simp only [ghashFrom, List.foldl_cons, List.foldl_nil, φ_mul, φ_xor]
  ring

/-- After `n` groups, the four lanes' sums are `GHASH` over the first `4 n`
blocks, times the powers of `H` the other groups bring. -/
theorem gacc_field {m : Mem} {G T : Addr} {H : Block} {g : Nat} (hT : TabOk m T H g) :
    ∀ n, n ≤ g → (gacc m G T g 0 n).val + (gacc m G T g 2 n).val + ((gacc m G T g 1 n).val + (gacc m G T g 3 n).val) =
      φ (ghashFrom H 0 (blocksAt m G (4 * n))) * φ H ^ (4 * (g - n))
  | 0, _ => by
    simp only [gacc, List.range_zero, List.foldl_nil, Prod.val_zero, Nat.mul_zero, blocksAt, List.map_nil,
      ghashFrom_nil, φ_zero, zero_mul, add_zero]
  | n + 1, h => by
    have ih := gacc_field (G := G) hT n (by omega_using [h])
    obtain ⟨k, rfl⟩ : ∃ k, g = n + 1 + k := ⟨g - (n + 1), by omega_using [h]⟩
    have t := F_of_tabOk hT k (by omega_using [])
    simp only [gacc_succ, Prod.val_acc]
    rw [show n + 1 + k - 1 - n = k by omega_using [], show 4 * (n + 1) = 4 * n + 4 by omega_using [], blocksAt_add,
      ghashFrom_append, show n + 1 + k - (n + 1) = k by omega_using []]
    rw [show n + 1 + k - n = k + 1 by omega_using []] at ih
    have hb : blocksAt m (G + BitVec.ofNat 64 (16 * (4 * n))) 4 =
        [blockAt m (G + BitVec.ofNat 64 (64 * n + 16 * 0)), blockAt m (G + BitVec.ofNat 64 (64 * n + 16 * 1)),
         blockAt m (G + BitVec.ofNat 64 (64 * n + 16 * 2)), blockAt m (G + BitVec.ofNat 64 (64 * n + 16 * 3))] := by
      simp only [blocksAt, List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.map_cons,
        List.map_nil, add_ofNat_ofNat]
      refine List.cons_eq_cons.mpr ⟨by congr 3; omega_using [], List.cons_eq_cons.mpr ⟨by congr 3; omega_using [],
        List.cons_eq_cons.mpr ⟨by congr 3; omega_using [], List.cons_eq_cons.mpr ⟨by congr 3; omega_using [], rfl⟩⟩⟩⟩
    rw [hb, φ_ghashFrom4]
    have t0 := t 0 (by decide)
    have t1 := t 1 (by decide)
    have t2 := t 2 (by decide)
    have t3 := t 3 (by decide)
    rw [show 4 * k + 4 - 0 = 4 * k + 4 by omega_using []] at t0
    rw [show 4 * k + 4 - 1 = 4 * k + 3 by omega_using []] at t1
    rw [show 4 * k + 4 - 2 = 4 * k + 2 by omega_using []] at t2
    rw [show 4 * k + 4 - 3 = 4 * k + 1 by omega_using []] at t3
    linear_combination ih + φ (blockAt m (G + BitVec.ofNat 64 (64 * n + 16 * 0))) * t0 +
      φ (blockAt m (G + BitVec.ofNat 64 (64 * n + 16 * 1))) * t1 +
      φ (blockAt m (G + BitVec.ofNat 64 (64 * n + 16 * 2))) * t2 +
      φ (blockAt m (G + BitVec.ofNat 64 (64 * n + 16 * 3))) * t3

/-- The four lanes' sums, reduced and added, are `GHASH` over the `4 g`
blocks of the buffer. -/
theorem gacc_ghash {m : Mem} {G T : Addr} {H : Block} {g : Nat} (hT : TabOk m T H g) :
    (reduceB (gacc m G T g 0 g) ^^^ reduceB (gacc m G T g 2 g)) ^^^
      (reduceB (gacc m G T g 1 g) ^^^ reduceB (gacc m G T g 3 g)) = ghashFrom H 0 (blocksAt m G (4 * g)) := by
  apply φ_inj
  rw [φ_xor, φ_xor, φ_xor, φ_reduceB, φ_reduceB, φ_reduceB, φ_reduceB, gacc_field hT g (Nat.le_refl _),
    Nat.sub_self, Nat.mul_zero, pow_zero, mul_one]

/-- What the short path's proofs need from the algebra of the field. -/
theorem shortFacts : ShortFacts :=
  ⟨powers_ok, powHead_ok, gacc_ghash, finPow_facts,
    fun H _ _ => step1' _ _ _ _ (by rw [x_φ_hInvF_hpow, pow_one]),
    fun H _ _ _ => step2 _ _ _ _ _ _ (by rw [x_φ_hInvF_hpow, pow_one]) (x_φ_hInvF_hpow H 2),
    fun H _ _ _ _ => step3 _ _ _ _ _ _ _ _ (by rw [x_φ_hInvF_hpow, pow_one]) (x_φ_hInvF_hpow H 2)
      (x_φ_hInvF_hpow H 3),
    fun np hpn => VG.Proof.Gcm.X86_64.StitchR.setupFinN np hpn hpn.1, VG.Proof.Gcm.X86_64.StitchZHTo.phase1_ok⟩

end VG.Proof.AesGcm.X86_64.Short

end

end

/-! ### `AesGcm.X86_64.Prepared.GatherSeal`, which only this module used -/

section

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, x86-64: `vg_aes_gcm_seal_prepared` called

Untrusted: everything here is checked by Lean. `vg_aes_gcm_seal_gather_prepared`
copies a short text to the output and encrypts it there by a call of
`vg_aes_gcm_seal_prepared`, by its shared contract, as
`Gather/SealCallee.lean` does for the other key contexts.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Gather

open VG VG.X86_64
open VG.Impl.AesGcm.X86_64 (Fn)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm (arg args ret rounds)

theorem sealSpecR_pre {s : State} (h : sealPreK CtxMode.prepared s) :
    (Proof.AesGcm.sealPreparedRoundsContract X86_64.abi 2624).pre s := by
  sig_split h
  rename_i a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a₁₇ a₁₈ a₁₉ a₂₀ a₂₁ a₂₂ a₂₃ a₂₄ a₂₅ a₂₆ a₂₇
    a₂₈ a₂₉ a₃₀ a₃₁
  have a₃₂ := h
  clear h
  sig_pre [Proof.AesGcm.sealPreparedRoundsContract, Proof.Gcm.sealPrecomputedSig, Proof.Gcm.sealPrecomputedSig, Proof.Gcm.sealPowersPre,
    X86_64.abi, X86_64.argRegs, List.range, List.range.loop]
  sig_reduce [Proof.AesGcm.sealPreparedRoundsContract, Proof.Gcm.sealPrecomputedSig, Proof.Gcm.sealPrecomputedSig, Proof.Gcm.sealPowersPre,
    X86_64.abi, X86_64.argRegs, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, X86_64.stackArg,
    X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below]
  simp only [Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, X86_64.stackArg,
    X86_64.stackArgAddr, VG.X86_64.below, Nat.mul_one, Proof.AesGcm.rounds, CtxMode.prepared, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowersRepr] at *
  sig_and_intros
  all_goals with_reducible assumption

theorem sealSpecR_post {s s' : State} (hR : rounds s)
    (h : (Proof.AesGcm.sealPreparedRoundsContract X86_64.abi 2624).post s s') :
    Proof.AesGcm.sealX86_64.post s s' := by
  sig_post [Proof.AesGcm.sealPreparedRoundsContract, Proof.Gcm.sealPrecomputedSig, Proof.Gcm.sealPrecomputedSig, Proof.Gcm.sealPowersPre,
    X86_64.abi, X86_64.argRegs, Proof.AesGcm.sealRoundsPost] at h
  sig_reduce [Proof.AesGcm.sealPreparedRoundsContract, Proof.Gcm.sealPrecomputedSig, Proof.Gcm.sealPrecomputedSig, X86_64.abi, X86_64.argRegs,
    X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop] at h
  exact h hR

theorem sealSpecR_pub {s₁ s₂ : State} (h : sealPubK s₁ s₂) :
    (Proof.AesGcm.sealPreparedRoundsContract X86_64.abi 2624).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, aMd⟩ := h
  sig_pub [Proof.AesGcm.sealPreparedRoundsContract, Proof.Gcm.sealPrecomputedSig, Proof.Gcm.sealPrecomputedSig, X86_64.abi, X86_64.argRegs]
  sig_reduce [Proof.AesGcm.sealPreparedRoundsContract, Proof.Gcm.sealPrecomputedSig, Proof.Gcm.sealPrecomputedSig, X86_64.abi, X86_64.argRegs,
    X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop, Proof.AesGcm.arg]
  simp only [Proof.AesGcm.arg, X86_64.stackArg, X86_64.stackArgAddr] at a₈ a₉ a₁₀
  sig_and_intros
  all_goals first | with_reducible assumption | trivial

/-- `vg_aes_gcm_seal_prepared` from its shared contract. -/
def SealFn.ofPrepared (f : Fn)
    (hv : Verified X86_64.target f.code (Proof.AesGcm.sealPreparedRoundsContract X86_64.abi 2624))
    (sp : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (xd : f.code.x86_64Depth ≤ 2624)
    (mx : f.code.allInstrs (fun i => !loadsMxcsr i) = true) : SealFn CtxMode.prepared :=
  CallFn.ofSpec f hv (fun _ h => sealSpecR_pre h)
    (fun _ _ h h' => sealSpecR_post h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h')
    (fun _ _ h => sealSpecR_pub h) sp xd mx

end VG.Proof.AesGcm.X86_64.Gather

end

end

/-! ### `AesGcm.X86_64.Prepared16.StreamCallee`, which only this module used -/

section

/-! # Sixteen prepared powers: Prepared-context StreamCallee contracts -/

@[expose] public section

set_option linter.unusedSimpArgs false
namespace VG.Proof.AesGcm.X86_64.StreamTo
open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm (arg args rounds)

theorem encSpecPrepared16_pre {s : State} (h : encCallPre CtxMode.prepared16 s) :
    (Proof.AesGcm.streamEncryptPrepared16RoundsContract X86_64.abi 2608).pre s := by
  sig_split h
  rename_i a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a₁₇ a₁₈ a₁₉ a₂₀ a₂₁
  have a₂₂ := h
  clear h
  sig_pre [Proof.AesGcm.streamEncryptPrepared16RoundsContract, Proof.Gcm.streamCryptPrecomputedSig, Proof.Gcm.streamCryptPrecomputedSig,
    Proof.Gcm.streamCryptPrepared16Pre, X86_64.abi, X86_64.argRegs, List.range, List.range.loop]
  sig_reduce [Proof.AesGcm.streamEncryptPrepared16RoundsContract, Proof.Gcm.streamCryptPrecomputedSig, Proof.Gcm.streamCryptPrecomputedSig,
    Proof.Gcm.streamCryptPrepared16Pre, X86_64.abi, X86_64.argRegs, Proof.AesGcm.arg, Proof.AesGcm.args,
    Proof.AesGcm.ret, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop,
    VG.X86_64.below]
  simp only [Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, X86_64.stackArg, X86_64.stackArgAddr,
    VG.X86_64.below, Nat.mul_one, Proof.AesGcm.rounds, CtxMode.prepared16, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr] at *
  sig_and_intros
  all_goals with_reducible assumption

theorem encSpecPrepared16_post {s s' : State} (hR : Proof.AesGcm.rounds s)
    (h : (Proof.AesGcm.streamEncryptPrepared16RoundsContract X86_64.abi 2608).post s s') :
    Proof.AesGcm.streamEncryptX86_64.post s s' := by
  sig_post [Proof.AesGcm.streamEncryptPrepared16RoundsContract, Proof.Gcm.streamCryptPrecomputedSig, Proof.Gcm.streamCryptPrecomputedSig,
    Proof.Gcm.streamCryptPrepared16Pre, X86_64.abi, X86_64.argRegs, Proof.AesGcm.streamEncryptRoundsPost] at h
  sig_reduce [Proof.AesGcm.streamEncryptPrepared16RoundsContract, Proof.Gcm.streamCryptPrecomputedSig, Proof.Gcm.streamCryptPrecomputedSig, X86_64.abi,
    X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop] at h
  exact h hR

theorem encSpecPrepared16_pub {s₁ s₂ : State} (h : encCallPub s₁ s₂) :
    (Proof.AesGcm.streamEncryptPrepared16RoundsContract X86_64.abi 2608).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, aMd⟩ := h
  sig_pub [Proof.AesGcm.streamEncryptPrepared16RoundsContract, Proof.Gcm.streamCryptPrecomputedSig, Proof.Gcm.streamCryptPrecomputedSig, X86_64.abi,
    X86_64.argRegs]
  sig_reduce [Proof.AesGcm.streamEncryptPrepared16RoundsContract, Proof.Gcm.streamCryptPrecomputedSig, Proof.Gcm.streamCryptPrecomputedSig, X86_64.abi,
    X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop, Proof.AesGcm.arg]
  simp only [Proof.AesGcm.arg, X86_64.stackArg, X86_64.stackArgAddr] at a₈
  sig_and_intros
  all_goals first | with_reducible assumption | trivial

def EncFn.ofPrepared16 (f : Fn)
    (hv : Verified X86_64.target f.code (Proof.AesGcm.streamEncryptPrepared16RoundsContract X86_64.abi 2608))
    (sp : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (xd : f.code.x86_64Depth ≤ 2608)
    (mx : f.code.allInstrs (fun i => !loadsMxcsr i) = true) : EncFn CtxMode.prepared16 where
  fn := f
  ok s h := by
    obtain ⟨t, s', he, ha, hp⟩ := hv.1 s (encSpecPrepared16_pre h)
    exact ⟨t, s', he, ha, encSpecPrepared16_post h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hp⟩
  ct s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂ := hv.2.1 s₁ s₂ t₁ t₂ s₁' s₂' (encSpecPrepared16_pre h₁) (encSpecPrepared16_pre h₂)
    (encSpecPrepared16_pub hq) e₁ e₂
  sp := SpSafe.of_all sp
  xd := xd
  mx := mx
  spAll := sp

end VG.Proof.AesGcm.X86_64.StreamTo

end

end

/-! ### `AesGcm.X86_64.Prepared16.GatherCallee`, which only this module used -/

section

/-! # Sixteen prepared powers: Prepared-context GatherCallee contracts -/

@[expose] public section

set_option linter.unusedSimpArgs false
namespace VG.Proof.AesGcm.X86_64.Gather
open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm (arg args rounds)

theorem toSpecPrepared16_pre {s : State} (h : toPre CtxMode.prepared16 s) :
    (Proof.Gcm.streamEncryptToPrepared16Contract X86_64.abi 4856).pre s := by
  sig_split h
  rename_i a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a₁₇ a₁₈ a₁₉ a₂₀ a₂₁ a₂₂ a₂₃ a₂₄ a₂₅ a₂₆ a₂₇
  have a₂₈ := h
  clear h
  sig_pre [Proof.Gcm.streamEncryptToPrepared16Contract, Proof.Gcm.streamEncryptToPreparedSig, Proof.Gcm.streamEncryptToPrecomputedSig,
    Proof.Gcm.streamEncryptToPrepared16Pre, X86_64.abi, X86_64.argRegs, List.range, List.range.loop]
  sig_reduce [Proof.Gcm.streamEncryptToPrepared16Contract, Proof.Gcm.streamEncryptToPreparedSig, Proof.Gcm.streamEncryptToPrecomputedSig,
    Proof.Gcm.streamEncryptToPrepared16Pre, X86_64.abi, X86_64.argRegs, Proof.AesGcm.arg, Proof.AesGcm.args,
    Proof.AesGcm.ret, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop,
    VG.X86_64.below]
  simp only [Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, X86_64.stackArg,
    X86_64.stackArgAddr, VG.X86_64.below, Nat.mul_one, Proof.AesGcm.rounds, CtxMode.prepared16, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr] at *
  sig_and_intros
  all_goals first
    | with_reducible assumption
    | omega
    | exact congrArg (BitVec.setWidth 64) a₃

theorem toSpecPrepared16_post {s s' : State} (hR : rounds s)
    (h : (Proof.Gcm.streamEncryptToPrepared16Contract X86_64.abi 4856).post s s') :
    Proof.AesGcm.streamToPost s s' := by
  sig_post [Proof.Gcm.streamEncryptToPrepared16Contract, Proof.Gcm.streamEncryptToPreparedSig, Proof.Gcm.streamEncryptToPrecomputedSig,
    Proof.Gcm.streamEncryptToPrepared16Pre, X86_64.abi, X86_64.argRegs, Proof.Gcm.streamEncryptToPost] at h
  sig_reduce [Proof.Gcm.streamEncryptToPrepared16Contract, Proof.Gcm.streamEncryptToPreparedSig, Proof.Gcm.streamEncryptToPrecomputedSig, X86_64.abi,
    X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop] at h
  exact h hR

theorem toSpecPrepared16_pub {s₁ s₂ : State} (h : toPub s₁ s₂) :
    (Proof.Gcm.streamEncryptToPrepared16Contract X86_64.abi 4856).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, aMd⟩ := h
  sig_pub [Proof.Gcm.streamEncryptToPrepared16Contract, Proof.Gcm.streamEncryptToPreparedSig, Proof.Gcm.streamEncryptToPrecomputedSig, X86_64.abi,
    X86_64.argRegs]
  sig_reduce [Proof.Gcm.streamEncryptToPrepared16Contract, Proof.Gcm.streamEncryptToPreparedSig, Proof.Gcm.streamEncryptToPrecomputedSig, X86_64.abi,
    X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop, Proof.AesGcm.arg]
  simp only [Proof.AesGcm.arg, X86_64.stackArg, X86_64.stackArgAddr] at a₈ a₉ a₁₀
  sig_and_intros
  all_goals first | with_reducible assumption | trivial

def ToFn.ofPrepared16 (f : Fn)
    (hv : Verified X86_64.target f.code (Proof.Gcm.streamEncryptToPrepared16Contract X86_64.abi 4856))
    (sp : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (xd : f.code.x86_64Depth ≤ 4856)
    (mx : f.code.allInstrs (fun i => !loadsMxcsr i) = true) : ToFn CtxMode.prepared16 :=
  CallFn.ofSpec f hv (fun _ h => toSpecPrepared16_pre h)
    (fun _ _ h h' => toSpecPrepared16_post h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h')
    (fun _ _ h => toSpecPrepared16_pub h) sp xd mx

end VG.Proof.AesGcm.X86_64.Gather

end

end

/-! ### `AesGcm.X86_64.Prepared16.GatherSplit`, which only this module used -/

section

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, x86-64: `vg_aes_gcm_seal_split_prepared` called

Untrusted: everything here is checked by Lean. `vg_aes_gcm_seal_gather_prepared`
copies the slices after the first of a short text to the output and
encrypts the text by a call of `vg_aes_gcm_seal_split_prepared`, by its
shared contract, as `Gather/SplitCallee.lean` does for the other key
contexts.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Gather

open VG VG.X86_64
open VG.Impl.AesGcm.X86_64 (Fn)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm (arg args ret rounds)

theorem splitSpecR16_pre {s : State} (h : splitPreK CtxMode.prepared16 s) :
    (Proof.Gcm.sealSplitPrepared16Contract X86_64.abi 2672).pre s := by
  sig_split h
  have a₀ := h
  clear h
  sig_pre [Proof.Gcm.sealSplitPrepared16Contract, Proof.Gcm.sealSplitPreparedSig, Proof.Gcm.sealSplitPrecomputedSig,
    Proof.Gcm.sealSplitPrepared16Pre, X86_64.abi, X86_64.argRegs, List.range, List.range.loop]
  sig_reduce [Proof.Gcm.sealSplitPrepared16Contract, Proof.Gcm.sealSplitPreparedSig, Proof.Gcm.sealSplitPrecomputedSig,
    Proof.Gcm.sealSplitPrepared16Pre, X86_64.abi, X86_64.argRegs, Proof.AesGcm.arg, Proof.AesGcm.args,
    Proof.AesGcm.ret, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop,
    VG.X86_64.below]
  simp only [Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, X86_64.stackArg,
    X86_64.stackArgAddr, VG.X86_64.below, Nat.mul_one, Proof.AesGcm.rounds, CtxMode.prepared16, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr,
    BitVec.setWidth_eq] at *
  sig_and_intros
  all_goals first
    | with_reducible assumption
    | omega

theorem splitSpecR16_post {M : CtxMode} {s s' : State}
    (h : (Proof.Gcm.sealSplitPrepared16Contract X86_64.abi 2672).post s s') (hR : rounds s) :
    (Proof.AesGcm.sealSplitX86_64M M).post s s' := by
  sig_post [Proof.Gcm.sealSplitPrepared16Contract, Proof.Gcm.sealSplitPreparedSig, Proof.Gcm.sealSplitPrecomputedSig,
    Proof.Gcm.sealSplitPrepared16Pre, X86_64.abi, X86_64.argRegs, Proof.Gcm.sealSplitPost] at h
  sig_reduce [Proof.Gcm.sealSplitPrepared16Contract, Proof.Gcm.sealSplitPreparedSig, Proof.Gcm.sealSplitPrecomputedSig,
    X86_64.abi, X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop] at h
  exact h hR

theorem splitSpecR16_pub {s₁ s₂ : State} (h : splitPubK s₁ s₂) :
    (Proof.Gcm.sealSplitPrepared16Contract X86_64.abi 2672).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, aMd⟩ := h
  sig_pub [Proof.Gcm.sealSplitPrepared16Contract, Proof.Gcm.sealSplitPreparedSig, Proof.Gcm.sealSplitPrecomputedSig,
    X86_64.abi, X86_64.argRegs]
  sig_reduce [Proof.Gcm.sealSplitPrepared16Contract, Proof.Gcm.sealSplitPreparedSig, Proof.Gcm.sealSplitPrecomputedSig,
    X86_64.abi, X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop, Proof.AesGcm.arg]
  simp only [Proof.AesGcm.arg, X86_64.stackArg, X86_64.stackArgAddr] at a₈ a₉ a₁₀ a₁₁ a₁₂
  sig_and_intros
  all_goals first | with_reducible assumption | trivial

/-- `vg_aes_gcm_seal_split_prepared` from its shared contract. -/
def SplitFn.ofPrepared16 (f : Fn)
    (hv : Verified X86_64.target f.code (Proof.Gcm.sealSplitPrepared16Contract X86_64.abi 2672))
    (sp : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (xd : f.code.x86_64Depth ≤ 2672)
    (mx : f.code.allInstrs (fun i => !loadsMxcsr i) = true) : SplitFn CtxMode.prepared16 :=
  CallFn.ofSpec f hv (fun _ h => splitSpecR16_pre h)
    (fun _ _ h h' => splitSpecR16_post (M := CtxMode.prepared16) h' h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (fun _ _ h => splitSpecR16_pub h) sp xd mx

end VG.Proof.AesGcm.X86_64.Gather

end

end

/-! ### `AesGcm.X86_64.Prepared16.GatherSeal`, which only this module used -/

section

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, x86-64: `vg_aes_gcm_seal_prepared` called

Untrusted: everything here is checked by Lean. `vg_aes_gcm_seal_gather_prepared`
copies a short text to the output and encrypts it there by a call of
`vg_aes_gcm_seal_prepared`, by its shared contract, as
`Gather/SealCallee.lean` does for the other key contexts.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Gather

open VG VG.X86_64
open VG.Impl.AesGcm.X86_64 (Fn)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm (arg args ret rounds)

theorem sealSpecR16_pre {s : State} (h : sealPreK CtxMode.prepared16 s) :
    (Proof.AesGcm.sealPrepared16RoundsContract X86_64.abi 2624).pre s := by
  sig_split h
  rename_i a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a₁₇ a₁₈ a₁₉ a₂₀ a₂₁ a₂₂ a₂₃ a₂₄ a₂₅ a₂₆ a₂₇
    a₂₈ a₂₉ a₃₀ a₃₁
  have a₃₂ := h
  clear h
  sig_pre [Proof.AesGcm.sealPrepared16RoundsContract, Proof.Gcm.sealPrecomputedSig, Proof.Gcm.sealPrecomputedSig, Proof.Gcm.sealPrepared16Pre,
    X86_64.abi, X86_64.argRegs, List.range, List.range.loop]
  sig_reduce [Proof.AesGcm.sealPrepared16RoundsContract, Proof.Gcm.sealPrecomputedSig, Proof.Gcm.sealPrecomputedSig, Proof.Gcm.sealPrepared16Pre,
    X86_64.abi, X86_64.argRegs, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, X86_64.stackArg,
    X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below]
  simp only [Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, X86_64.stackArg,
    X86_64.stackArgAddr, VG.X86_64.below, Nat.mul_one, Proof.AesGcm.rounds, CtxMode.prepared16, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr] at *
  sig_and_intros
  all_goals with_reducible assumption

theorem sealSpecR16_post {s s' : State} (hR : rounds s)
    (h : (Proof.AesGcm.sealPrepared16RoundsContract X86_64.abi 2624).post s s') :
    Proof.AesGcm.sealX86_64.post s s' := by
  sig_post [Proof.AesGcm.sealPrepared16RoundsContract, Proof.Gcm.sealPrecomputedSig, Proof.Gcm.sealPrecomputedSig, Proof.Gcm.sealPrepared16Pre,
    X86_64.abi, X86_64.argRegs, Proof.AesGcm.sealRoundsPost] at h
  sig_reduce [Proof.AesGcm.sealPrepared16RoundsContract, Proof.Gcm.sealPrecomputedSig, Proof.Gcm.sealPrecomputedSig, X86_64.abi, X86_64.argRegs,
    X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop] at h
  exact h hR

theorem sealSpecR16_pub {s₁ s₂ : State} (h : sealPubK s₁ s₂) :
    (Proof.AesGcm.sealPrepared16RoundsContract X86_64.abi 2624).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, aMd⟩ := h
  sig_pub [Proof.AesGcm.sealPrepared16RoundsContract, Proof.Gcm.sealPrecomputedSig, Proof.Gcm.sealPrecomputedSig, X86_64.abi, X86_64.argRegs]
  sig_reduce [Proof.AesGcm.sealPrepared16RoundsContract, Proof.Gcm.sealPrecomputedSig, Proof.Gcm.sealPrecomputedSig, X86_64.abi, X86_64.argRegs,
    X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop, Proof.AesGcm.arg]
  simp only [Proof.AesGcm.arg, X86_64.stackArg, X86_64.stackArgAddr] at a₈ a₉ a₁₀
  sig_and_intros
  all_goals first | with_reducible assumption | trivial

/-- `vg_aes_gcm_seal_prepared` from its shared contract. -/
def SealFn.ofPrepared16 (f : Fn)
    (hv : Verified X86_64.target f.code (Proof.AesGcm.sealPrepared16RoundsContract X86_64.abi 2624))
    (sp : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (xd : f.code.x86_64Depth ≤ 2624)
    (mx : f.code.allInstrs (fun i => !loadsMxcsr i) = true) : SealFn CtxMode.prepared16 :=
  CallFn.ofSpec f hv (fun _ h => sealSpecR16_pre h)
    (fun _ _ h h' => sealSpecR16_post h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h')
    (fun _ _ h => sealSpecR16_pub h) sp xd mx

end VG.Proof.AesGcm.X86_64.Gather

end

end

/-! ### `AesGcm.X86_64.Prepared16.Short`, which only this module used -/

section

/-! # Sixteen prepared powers: `seal` and `open` without the short path

`Prepared/Short.lean`'s `sealSelPrepared_framed` and `openSelPrepared_framed`
for a key context of `vg_aes_gcm_prepare16`, for implementations without the
short path (`hs`), whose table of powers is copied from all 48: `SealFin` and
`FastOpen.openFin` around the path for TLS records, at every length. -/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64
open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Gcm.X86_64.Stitch (CtxMode)
variable (v : GcmImpl) (B : BlkFn CtxMode.prepared16)

theorem sealSelPrepared16_framed (hF : Short.ShortFacts) (hs : v.short = false) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2600 3 (v.sealCodeP (v.withBlk B)))
      (Proof.AesGcm.sealPrepared16RoundsContract X86_64.abi 2624) := by
  unfold GcmImpl.sealCodeP; simp only [hs, Bool.false_eq_true, ↓reduceIte]; split
  · exact sealPrepared16Code_framed (sealPrepared16Code_verified (Short.sealFinP_correct v B hF)
      (SealFin.sealFMW_ct v B (FastSeal.sealSel_ok hF v B Short.finKsA_ksOk (SealFin.sealLongOk_mid v B hF))
        (FastSeal.sealSel_rel hF v B Short.finKsA_ksOk Short.finKsA_rel (SealFin.sealLongRel_mid v B hF))))
      (Short.sealFinP_spSafe v B) (Short.sealFinP_xdepth v B)
  · exact sealPrepared16_framed v B

/-- `vg_aes_gcm_open_prepared16`, for implementations without the short path. -/
theorem openSelPrepared16_framed (hF : Short.ShortFacts) (hs : v.short = false) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2608 4 (v.openCodeP (v.withBlk B)))
      (Proof.AesGcm.openPrepared16RoundsContract X86_64.abi 2632) := by
  unfold GcmImpl.openCodeP; simp only [hs, Bool.false_eq_true, ↓reduceIte]
  exact openPrepared16Code_framed (openPrepared16Code_verified (Short.openFinP_correct v B hF)
    (FastOpen.openFinW_ct (FastOpen.openSel_rel hF v B Short.finKsA_ksOk Short.finKsA_rel
      (Short.longRel_openLong v B)))) (Short.openFinP_spSafe v B) (Short.openFinP_xdepth v B)

end VG.Proof.AesGcm.X86_64

end

end

/-! ### `AesGcm.X86_64.Prepared16.Split`, which only this module used -/

section

/-! ### `AesGcm.ScratchSplit16`, which only this module used -/

section

/-!
# AES-GCM `seal_split` with sixteen prepared powers and its working space as an argument

`sealSplitPrepared16ScratchContract`: `sealSplitPreparedScratchContract`
(`ScratchSplit.lean`) with the precondition of `Spec.Gcm.Prepared16`, and
its locality (`sealSplitPrepared16Pre_local`).
-/

@[expose] public section

namespace VG.Proof.AesGcm

open VG.Spec.Gcm Proof.Gcm

/-- `sealSplitPrepared16Contract`, whatever `work` is. -/
def sealSplitPrepared16ScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealSplitPreparedScratchSig.contract A
    (pre := fun ctx rounds nonce nonceLen aad aadLen src srcLen dst len tag _work =>
      sealSplitPrepared16Pre A.ptrBits ctx rounds nonce nonceLen aad aadLen src srcLen dst len tag)
    (post := fun ctx rounds nonce nonceLen aad aadLen src srcLen dst len tag _work =>
      sealSplitPost A.ptrBits ctx rounds nonce nonceLen aad aadLen src srcLen dst len tag)
    (writeArgs := true) (stack := stack)

variable (pb : Nat)

theorem sealSplitPrepared16Pre_local : ∀ vs m₁ m₂, vs.length = (sealSplitPreparedSig.words pb).length →
    (∀ b ∈ Sig.bufs sealSplitPreparedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sealSplitPreparedSig.words pb) (sealSplitPrepared16Pre pb) vs m₁ →
      Curry.apply (sealSplitPreparedSig.words pb) (sealSplitPrepared16Pre pb) vs m₂ := by
  intro vs m₁ m₂ hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 10) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 10
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [sealSplitPreparedSig, sealSplitPrecomputedSig, Sig.bufs, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  have hc := agree_of hb.1
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
    (sealSplitPrepared16Pre pb) _ m₁ at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
    (sealSplitPrepared16Pre pb) _ m₂
  dsimp only [Curry.apply, sealSplitPrepared16Pre, ArgWord.ofRaw] at h ⊢
  exact ⟨h.1, h.2.1, preparedPowers16Repr_congr hc h.2.2⟩

end VG.Proof.AesGcm

end

end

/-! # Sixteen prepared powers: `seal_split` for a key context of `vg_aes_gcm_prepare16`

`sealSplitPrepared16_framed`: `Fast/Verified.lean`'s `sealSplitPrepared_framed`
for `Proof.Gcm.sealSplitPrepared16Contract`, the loops proven for the first
eight pairs (`CtxMode.prepared16`), with a one-pass loop that reads no
other (`hz`: not `StitchZHTo.encN`, which reads all 48 powers). -/

@[expose] public section

set_option linter.unusedSimpArgs false
namespace VG.Proof.AesGcm.X86_64.Split

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.StreamTo (BlkToFn)
open VG.Proof.AesGcm.X86_64.Short (ShortFacts)

theorem splitPrepared16_implies : (Proof.AesGcm.sealSplitX86_64M CtxMode.prepared16).Implies
    (Proof.AesGcm.sealSplitPrepared16ScratchContract X86_64.abi 56) := by
  exact { pre := by sig_implies_pre [Proof.AesGcm.sealSplitPrepared16ScratchContract, Proof.AesGcm.sealSplitPreparedScratchSig, Proof.AesGcm.sealSplitPrecomputedScratchSig, Proof.Gcm.sealSplitPrepared16Pre,
      Proof.Gcm.sealSplitPost, CtxMode.prepared16, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr, Proof.AesGcm.sealSplitX86_64M, Proof.AesGcm.splitPre, Proof.AesGcm.onePub,
      X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk56, Proof.AesGcm.ret,
      Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop,
      VG.X86_64.below, X86_64.argRegs, CtxMode.prepared16, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr]
          post := by sig_implies_post [Proof.AesGcm.sealSplitPrepared16ScratchContract, Proof.AesGcm.sealSplitPreparedScratchSig, Proof.AesGcm.sealSplitPrecomputedScratchSig, Proof.Gcm.sealSplitPrepared16Pre,
      Proof.Gcm.sealSplitPost, CtxMode.prepared16, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr, Proof.AesGcm.sealSplitX86_64M, Proof.AesGcm.splitPre, Proof.AesGcm.onePub,
      X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk56, Proof.AesGcm.ret,
      Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop,
      VG.X86_64.below, X86_64.argRegs, CtxMode.prepared16, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr]
          pub := by sig_implies_pub [Proof.AesGcm.sealSplitPrepared16ScratchContract, Proof.AesGcm.sealSplitPreparedScratchSig, Proof.AesGcm.sealSplitPrecomputedScratchSig, Proof.Gcm.sealSplitPrepared16Pre,
      Proof.Gcm.sealSplitPost, CtxMode.prepared16, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr, Proof.AesGcm.sealSplitX86_64M, Proof.AesGcm.splitPre, Proof.AesGcm.onePub,
      X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk56, Proof.AesGcm.ret,
      Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop,
      VG.X86_64.below, X86_64.argRegs, CtxMode.prepared16, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr]
          sat := ⟨splitSatP, by
            sig_pre [Proof.AesGcm.sealSplitPrepared16ScratchContract, Proof.AesGcm.sealSplitPreparedScratchSig,
              Proof.AesGcm.sealSplitPrecomputedScratchSig, Proof.Gcm.sealSplitPrepared16Pre, X86_64.abi,
              X86_64.argRegs, splitSatP, splitSat]
            sig_and_intros
            all_goals first
              | rfl
              | decide
              | (refine preparedPowers16Repr_of_zero fun i hi => ?_
                 split
                 · next h => exfalso; bv_omega
                 · rfl)
              | exact Region.disjoint_of_sep (by decide)⟩ }

theorem splitFrameSatPrepared16_pre : ∃ s, (Proof.Gcm.sealSplitPrepared16Contract X86_64.abi 2672).pre s := by
  refine ⟨splitFrameSatP, ?_⟩
  sig_pre [Proof.Gcm.sealSplitPrepared16Contract, Proof.Gcm.sealSplitPreparedSig, Proof.Gcm.sealSplitPrecomputedSig,
    Proof.Gcm.sealSplitPrepared16Pre, Proof.Gcm.sealSplitPost, X86_64.abi, X86_64.argRegs, splitFrameSatP,
    splitFrameSat, splitSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (refine preparedPowers16Repr_of_zero fun i hi => ?_
       split
       · next h => exfalso; bv_omega
       · rfl)

section
variable (v : GcmImpl) (B : BlkFn CtxMode.prepared16) (T : BlkToFn CtxMode.prepared16)

theorem sealSplitPrepared16_core (hF : ShortFacts) (hz : ∀ n, v.onePass = some n → n ≠ .z) :
    Verified X86_64.target (SealSplit.«seal» (v.splitMidR (v.withBlk B) T.fn))
      (Proof.AesGcm.sealSplitPrepared16ScratchContract X86_64.abi 56) :=
  Verified.of_correct (k := Proof.AesGcm.sealSplitX86_64M CtxMode.prepared16) (sealSplitR_correct v B T hF (fun n h hzn => absurd hzn (hz n h)))
    (sealSplitM_ct (splitMidR_ok v B T hF (fun n h hzn => absurd hzn (hz n h))) (splitMidR_rel v B T hF (fun n h hzn => absurd hzn (hz n h))))
    splitPrepared16_implies

/-- `vg_aes_gcm_seal_split_prepared`, in its frame. -/
theorem sealSplitPrepared16_framed (hF : ShortFacts) (hz : ∀ n, v.onePass = some n → n ≠ .z) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2616 5 (SealSplit.«seal» (v.splitMidR (v.withBlk B) T.fn)))
      (Proof.Gcm.sealSplitPrepared16Contract X86_64.abi 2672) :=
  X86_64.Verified.stackArgScratch (hpostOut := Proof.AesGcm.sealSplitPrecomputedPostOut_local _) (sig := Proof.Gcm.sealSplitPreparedSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Proof.Gcm.sealSplitPrepared16Pre X86_64.abi.ptrBits)
    (post := Proof.Gcm.sealSplitPost X86_64.abi.ptrBits) (wa := true) (stack := 56)
    (bytes := 2616) (sealSplitPrepared16_core v B T hF hz) (by decide) (by decide) (by decide)
    (sealSplitR_spSafe v B T) (sealSplitR_xdepth v B T) (Proof.AesGcm.sealSplitPrepared16Pre_local _)
    (Proof.AesGcm.sealSplitPrecomputedPost_local _) splitFrameSatPrepared16_pre

end

end VG.Proof.AesGcm.X86_64.Split

end

end

/-! ### `AesGcm.X86_64.Prepared16.StreamTo`, which only this module used -/

section

/-! # Sixteen prepared powers: Prepared-context StreamTo contracts -/

@[expose] public section

set_option linter.unusedSimpArgs false
namespace VG.Proof.AesGcm.X86_64.StreamTo
open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm (arg args rounds)
open VG.Impl.AesGcm.X86_64.StreamTo

theorem streamToPrepared16_implies : (Proof.AesGcm.streamEncryptToX86_64M CtxMode.prepared16).Implies
    (Proof.AesGcm.streamEncryptToPrepared16ScratchContract X86_64.abi 2624) := by
  exact { pre := by sig_implies_pre [Proof.AesGcm.streamEncryptToPrepared16ScratchContract,
      Proof.AesGcm.streamEncryptToPreparedScratchSig, Proof.AesGcm.streamEncryptToPrecomputedScratchSig, Proof.Gcm.streamEncryptToPrepared16Pre,
      Proof.Gcm.streamEncryptToPost, Proof.AesGcm.streamEncryptToX86_64M,
      Proof.AesGcm.streamToPreM, Proof.AesGcm.streamToPost, Proof.AesGcm.streamToPub, X86_64.abi,
      Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stkS, Proof.AesGcm.ret, Proof.AesGcm.rounds,
      X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs, CtxMode.prepared16, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr]
          post := by sig_implies_post [Proof.AesGcm.streamEncryptToPrepared16ScratchContract,
      Proof.AesGcm.streamEncryptToPreparedScratchSig, Proof.AesGcm.streamEncryptToPrecomputedScratchSig, Proof.Gcm.streamEncryptToPrepared16Pre,
      Proof.Gcm.streamEncryptToPost, Proof.AesGcm.streamEncryptToX86_64M,
      Proof.AesGcm.streamToPreM, Proof.AesGcm.streamToPost, Proof.AesGcm.streamToPub, X86_64.abi,
      Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stkS, Proof.AesGcm.ret, Proof.AesGcm.rounds,
      X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs, CtxMode.prepared16, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr]
          pub := by sig_implies_pub [Proof.AesGcm.streamEncryptToPrepared16ScratchContract,
      Proof.AesGcm.streamEncryptToPreparedScratchSig, Proof.AesGcm.streamEncryptToPrecomputedScratchSig, Proof.Gcm.streamEncryptToPrepared16Pre,
      Proof.Gcm.streamEncryptToPost, Proof.AesGcm.streamEncryptToX86_64M,
      Proof.AesGcm.streamToPreM, Proof.AesGcm.streamToPost, Proof.AesGcm.streamToPub, X86_64.abi,
      Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stkS, Proof.AesGcm.ret, Proof.AesGcm.rounds,
      X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs, CtxMode.prepared16, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr]
          sat := ⟨streamToSatP, by
            sig_pre [Proof.AesGcm.streamEncryptToPrepared16ScratchContract,
              Proof.AesGcm.streamEncryptToPreparedScratchSig, Proof.AesGcm.streamEncryptToPrecomputedScratchSig, Proof.Gcm.streamEncryptToPrepared16Pre,
              X86_64.abi, X86_64.argRegs, streamToSatP, streamToSat]
            sig_and_intros
            all_goals first
              | rfl
              | decide
              | exact preparedPowers16Repr_of_zero fun _ _ => rfl
              | exact Region.disjoint_of_sep (by decide)⟩ }

theorem streamEncryptToPrepared16_core (T : BlkToFn CtxMode.prepared16) (E : EncFn CtxMode.prepared16) :
    Verified X86_64.target (encrypt T.fn E.fn)
      (Proof.AesGcm.streamEncryptToPrepared16ScratchContract X86_64.abi 2624) :=
  Verified.of_correct (k := Proof.AesGcm.streamEncryptToX86_64M CtxMode.prepared16) (encrypt_correct T E)
    (encrypt_ct T E) streamToPrepared16_implies

theorem streamToFrameSatPrepared16_pre : ∃ s, (Proof.Gcm.streamEncryptToPrepared16Contract X86_64.abi 4856).pre s := by
  refine ⟨streamToFrameSatP, ?_⟩
  sig_pre [Proof.Gcm.streamEncryptToPrepared16Contract, Proof.Gcm.streamEncryptToPreparedSig, Proof.Gcm.streamEncryptToPrecomputedSig,
    Proof.Gcm.streamEncryptToPrepared16Pre, Proof.Gcm.streamEncryptToPost, X86_64.abi, X86_64.argRegs,
    streamToFrameSatP, streamToFrameSat, streamToSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact preparedPowers16Repr_of_zero fun _ _ => rfl

theorem streamEncryptToPrepared16_framed (T : BlkToFn CtxMode.prepared16) (E : EncFn CtxMode.prepared16) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackArgScratch 2232 3 (encrypt T.fn E.fn))
      (Proof.Gcm.streamEncryptToPrepared16Contract X86_64.abi 4856) :=
  X86_64.Verified.stackArgScratchPre (hpostOut := Proof.AesGcm.streamEncryptToPrecomputedPostOut_local _ _ (fun _ _ _ _ _ _ _ _ _ _ h => h.2.1)) (sig := Proof.Gcm.streamEncryptToPreparedSig) (nm := "scratch")
    (e := .u64) (n := 274) (pre := Proof.Gcm.streamEncryptToPrepared16Pre X86_64.abi.ptrBits)
    (post := Proof.Gcm.streamEncryptToPost X86_64.abi.ptrBits) (wa := true) (stack := 2624)
    (bytes := 2232) (streamEncryptToPrepared16_core T E) (by decide) (by decide) (by decide)
    (encrypt_spAll T E) (encrypt_xdepth T E) (Proof.AesGcm.streamEncryptToPrepared16Pre_local _)
    (Proof.AesGcm.streamEncryptToPrecomputedPost_local _) streamToFrameSatPrepared16_pre

end VG.Proof.AesGcm.X86_64.StreamTo

end

end

/-! ### `AesGcm.X86_64.Prepared16.Gather`, which only this module used -/

section

/-! # Sixteen prepared powers: Prepared-context Gather contracts -/

@[expose] public section

set_option linter.unusedSimpArgs false
namespace VG.Proof.AesGcm.X86_64.Gather
open VG.Proof.AesSiv.X86_64 (filter_true' filter_false' filterMap_some' filterMap_none' pairFacts_ro)
open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm (arg args rounds)
open VG.Impl.AesGcm.X86_64.SealGather

theorem gatherPrePrepared16_of {s : State}
    (h : (Proof.AesGcm.sealGatherPrepared16ScratchContract X86_64.abi 4888).pre s) :
    Proof.AesGcm.sealGatherPreM CtxMode.prepared16 s := by
  sig_pre [Proof.AesGcm.sealGatherPrepared16ScratchContract, Proof.AesGcm.sealGatherPreparedScratchSig, Proof.AesGcm.sealGatherPrecomputedScratchSig,
    Proof.Gcm.sealGatherPrepared16Pre, X86_64.abi, X86_64.argRegs, stackArgs_six, List.append_eq] at h
  rw [Sig.pairFacts, Sig.pairFacts, Sig.pairFacts, pairFacts_ro _ (by simp)] at h
  simp only [List.map_append, List.filter_append, List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.false_eq_true, ite_true, ite_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true,
    List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append, Sig.conj, Bool.true_or, Bool.or_true,
    Bool.false_or, Bool.or_false, List.cons_append, List.singleton_append, Sig.descRegion] at h
  obtain ⟨w₁, w₂, rd, wr, ⟨kd, kt, kw, nd, nt, nw, ad, at_, aw, dt, dw, dds, ⟨dl, da⟩, tw, tds, ⟨tl, ta⟩, wds, wl, wa⟩,
    rk, rn, ra, rdd, rt, rw, ⟨rds, ⟨rl, -⟩, bk, bn, ba, bd, bt, bw, bds, bl, -⟩, ok, on, oa, od, ot, ow, ⟨ods, ol⟩,
    hr, hg, hpw⟩ := h
  simp only [Proof.AesGcm.sealGatherPreM, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, Proof.AesGcm.stkG,
    Proof.AesGcm.slicesG, Proof.AesGcm.rounds, VG.X86_64.below, CtxMode.prepared16, CtxMode.preparedN]
  simp only [show (2 * (64 / 8) : Nat) = 16 from rfl] at *
  exact ⟨rd, wr, kd, kt, kw, nd, nt, nw, ad, at_, aw, dds.symm, tds.symm, wds.symm,
    fun r hr' => ⟨(dl r hr').symm, (tl r hr').symm, (wl r hr').symm⟩, dt, dw, tw, da, ta, wa, rdd, rt, rw,
    bk, bn, ba, bds, bl, bd, bt, bw, ok, on, oa, ods, ol, od, ot, ow, w₁, w₂, hr, hg, hpw⟩

theorem gatherPostPrepared16_of {s s' : State} (h : Proof.AesGcm.sealGatherPostG s s') :
    (Proof.AesGcm.sealGatherPrepared16ScratchContract X86_64.abi 4888).post s s' := by
  sig_post [Proof.AesGcm.sealGatherPrepared16ScratchContract, Proof.AesGcm.sealGatherPreparedScratchSig, Proof.AesGcm.sealGatherPrecomputedScratchSig,
    Proof.AesGcm.sealGatherRoundsPost, X86_64.abi, X86_64.argRegs, stackArgs_six, List.append_eq]
  exact fun _ _ => h

theorem gatherPubPrepared16_of {s₁ s₂ : State}
    (hp : (Proof.AesGcm.sealGatherPrepared16ScratchContract X86_64.abi 4888).pub s₁ s₂) :
    Proof.AesGcm.sealGatherPub s₁ s₂ := by
  sig_pub_keep [Proof.AesGcm.sealGatherPrepared16ScratchContract, Proof.AesGcm.sealGatherPreparedScratchSig, Proof.AesGcm.sealGatherPrecomputedScratchSig,
    Proof.Gcm.sealGatherPrepared16Pre, X86_64.abi, X86_64.argRegs, stackArgs_six, List.append_eq] at hp
  simp only [List.getD_cons_succ, List.getD_cons_zero, Sig.descRegion] at hp
  obtain ⟨q₇, qMd, q₁, q₂, q₃, q₄, q₅, q₆, a₀, a₁, a₂, a₃, a₄, a₅, hd⟩ := hp
  exact ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, a₀, a₁, a₂, a₃, a₄, a₅, fun i hi => hd i (by simpa using hi), qMd⟩

theorem gatherSatPrepared16_pre : ∃ s, (Proof.AesGcm.sealGatherPrepared16ScratchContract X86_64.abi 4888).pre s := by
  refine ⟨gatherSatP, ?_⟩
  sig_pre [Proof.AesGcm.sealGatherPrepared16ScratchContract, Proof.AesGcm.sealGatherPreparedScratchSig, Proof.AesGcm.sealGatherPrecomputedScratchSig,
    Proof.Gcm.sealGatherPrepared16Pre, X86_64.abi, X86_64.argRegs, stackArgs_six, List.append_eq,
    gatherSatP, gatherSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact preparedPowers16Repr_of_zero fun _ hi => by simp only [ctx_low hi, ite_false]

theorem gatherPrepared16_implies : (Proof.AesGcm.sealGatherX86_64M CtxMode.prepared16).Implies
    (Proof.AesGcm.sealGatherPrepared16ScratchContract X86_64.abi 4888) :=
  ⟨fun _ h => gatherPrePrepared16_of h, fun _ _ _ h => gatherPostPrepared16_of h, fun _ _ _ _ h => gatherPubPrepared16_of h, gatherSatPrepared16_pre⟩

/-- `vg_aes_gcm_seal_gather_prepared16`'s code: a TLS record's text sealed by
`Sp` from the entry (`withFront long`), and the others by `sealGather`, with
`I`, `A` and `F` inlined (`callOr`), as no variant of it would call their
512-bit variants. -/
theorem sealGatherPrepared16_core (Sh : ShortFn CtxMode.prepared16) (I : InitFn) (A : AadFn)
    (T : ToFn CtxMode.prepared16) (F : FinFn) (Sp : SplitFn CtxMode.prepared16) (long : Bool) :
    Verified X86_64.target
      (withFront long Sp.fn (sealGather Sh.quick Sh.fast Sh.test Sh.code I.fn A.fn T.fn F.fn true))
      (Proof.AesGcm.sealGatherPrepared16ScratchContract X86_64.abi 4888) :=
  Verified.of_correct (k := Proof.AesGcm.sealGatherX86_64M CtxMode.prepared16)
    (withFront_correct Sh I A T F Sp long true) (withFront_ct Sh I A T F Sp long true) gatherPrepared16_implies

theorem gatherFrameSatPrepared16_pre : ∃ s, (Proof.AesGcm.sealGatherPrepared16RoundsContract X86_64.abi 5128).pre s := by
  refine ⟨gatherFrameSatP, ?_⟩
  sig_pre [Proof.AesGcm.sealGatherPrepared16RoundsContract, Proof.Gcm.sealGatherPrecomputedSig, Proof.Gcm.sealGatherPrecomputedSig,
    Proof.Gcm.sealGatherPrepared16Pre, X86_64.abi, X86_64.argRegs, stackArgs_five, List.append_eq,
    gatherFrameSatP, gatherFrameSat, gatherSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact preparedPowers16Repr_of_zero fun _ hi => by simp only [ctx_low hi, ite_false]

theorem sealGatherPrepared16_framed (Sh : ShortFn CtxMode.prepared16) (I : InitFn)
    (A : AadFn) (T : ToFn CtxMode.prepared16) (F : FinFn) (Sp : SplitFn CtxMode.prepared16) (long : Bool) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 240 5
        (withFront long Sp.fn (sealGather Sh.quick Sh.fast Sh.test Sh.code I.fn A.fn T.fn F.fn true)))
      (Proof.AesGcm.sealGatherPrepared16RoundsContract X86_64.abi 5128) :=
  X86_64.Verified.stackArgScratchL (hpostOut := fun vs m m₁ m₂ r hl _ hb _ => (Proof.AesGcm.sealGatherPrecomputedPostOut_local _) vs m m₁ m₂ r hl hb) (sig := Proof.Gcm.sealGatherPrecomputedSig) (nm := "scratch") (e := .u64)
    (n := 23) (pre := Proof.Gcm.sealGatherPrepared16Pre X86_64.abi.ptrBits)
    (post := Proof.AesGcm.sealGatherRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 4888) (bytes := 240)
    (sealGatherPrepared16_core Sh I A T F Sp long) (by decide) (by decide) (by decide)
    (withFront_spAll Sh I A T F Sp long true) (withFront_xdepth Sh I A T F Sp long true)
    (Proof.AesGcm.sealGatherPrepared16Pre_local _) (Proof.AesGcm.sealGatherPrecomputedPost_local _)
    gatherFrameSatPrepared16_pre

end VG.Proof.AesGcm.X86_64.Gather

end

end

/-!
# AES-GCM on x86-64: the functions a variant's artifacts are built from

The interleaved loops a variant names, with their proofs (which import the
algebra of `Proof/Gcm/Poly.lean`, so that the variants need not), the
implementations a variant names, resolved (`GcmVariant.impl`), and the
instances of the functions its callers call (`sealFn`, `toFn`, `openFn`, …),
with their proofs, for `Generic/AesGcm/X86_64/AesGcm.lean`; and the lengths at which
`vg_aes_gcm_seal_gather` changes path (`copyBelow`, `splitFrom`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64

/-- The loops named `n` interleave counter mode and GHASH correctly. -/
theorem StitchName.ok : (n : StitchName) → Proof.Gcm.X86_64.Stitch.StitchOk n.enc n.dec
  | .vaes => Proof.Gcm.X86_64.Stitch.stitch_ok
  | .vaesAvx512 => Proof.Gcm.X86_64.StitchZ.stitch_ok
  | .aesniAvx => Proof.Gcm.X86_64.StitchAvx8.stitch_ok

/-- The encryption loop named `n`, if it takes all the blocks, meets its
contract for any number of them from 16 on. -/
theorem StitchName.okFull : (n : StitchName) → n.full = true → ∀ s₀, Proof.Gcm.X86_64.Stitch.SPre s₀ →
    WP X86_64.isa n.enc s₀ (Proof.Gcm.X86_64.Stitch.EPost s₀)
  | .aesniAvx, _ => fun _ hp => Proof.Gcm.X86_64.StitchAvx8.enc_ok hp
  | .vaes, h => absurd h (by decide)
  | .vaesAvx512, h => absurd h (by decide)

/-- The loops `p` names, with their proof. -/
def StitchPart.impl (p : StitchPart) : StitchImpl :=
  ⟨p.suffix, p.features, p.name.enc, p.name.dec, p.name.ok, p.name.full, p.name.okFull, p.encP, p.decP⟩

/-- The loops named `n` for a key context of `vg_aes_gcm_init_precomputed`
interleave counter mode and GHASH correctly. -/
theorem StitchName.okP : (n : StitchName) →
    Proof.Gcm.X86_64.Stitch.StitchOkM Proof.Gcm.X86_64.Stitch.CtxMode.powers n.encP n.decP
  | .vaes => Proof.Gcm.X86_64.Stitch.stitch_ok.toM _
  | .vaesAvx512 => Proof.Gcm.X86_64.StitchZP.stitchP_ok.toM
  | .aesniAvx => Proof.Gcm.X86_64.StitchAvx8.stitch_ok.toM _

/-- The loops `p` names for a key context of `vg_aes_gcm_init_precomputed`,
with their proof, if they read the powers of the hash subkey from it. -/
def StitchPart.implP (p : StitchPart) : Option (StitchCode Proof.Gcm.X86_64.Stitch.CtxMode.powers) :=
  p.pieceP.map fun q => ⟨p.name.encP, p.name.decP, false, false, false, false, false, p.name.encP, p.name.decP,
    p.name.okP, Proof.Gcm.X86_64.Stitch.StitchOkSmall.of16 _ _ _, q.enc, q.dec, q.enc, q.dec⟩

/-- The out-of-place loops named `n` interleave counter mode and GHASH
correctly. -/
theorem StitchToName.ok : (n : StitchToName) → (M : Proof.Gcm.X86_64.Stitch.CtxMode) →
    Proof.Gcm.X86_64.Stitch.StitchToOkM M n.enc (if n.full then 1 else 16)
  | .vaes, M => Proof.Gcm.X86_64.StitchTo.stitchTo_ok M
  | .vaesAvx512, M => Proof.Gcm.X86_64.StitchZTo.stitchTo_ok M
  | .aesniAvx, M => Proof.Gcm.X86_64.StitchAvx8.stitchTo_ok M

/-- The out-of-place loops named `n` for a key context of
`vg_aes_gcm_init_precomputed` interleave counter mode and GHASH correctly. -/
theorem StitchToName.okP : (n : StitchToName) →
    Proof.Gcm.X86_64.Stitch.StitchToOkM Proof.Gcm.X86_64.Stitch.CtxMode.powers n.encP
  | .vaes => Proof.Gcm.X86_64.StitchTo.stitchTo_ok _
  | .vaesAvx512 => Proof.Gcm.X86_64.StitchZTo.stitchToP_ok
  | .aesniAvx => fun s₀ hp _ => Proof.Gcm.X86_64.StitchAvx8.stitchTo_ok _ s₀ hp (Nat.mod_one _)

/-- The out-of-place loops a variant names, with their proof. -/
def GcmVariant.stitchTo (v : GcmVariant) : Option (StitchToCode Proof.Gcm.X86_64.Stitch.CtxMode.base) :=
  (v.stitch.bind (·.toPart)).map fun p => ⟨p.name.enc, p.name.full, p.name.ok _, p.piece⟩

/-- The implementations a variant calls. -/
def GcmVariant.impl (v : GcmVariant) : GcmImpl :=
  ⟨v.ctr, v.key, v.gh.impl, v.stitch.map StitchPart.impl, v.stitch.bind StitchPart.implP,
    v.stitch.any (·.name.short), v.stitch.any (·.name.fin), v.stitch.bind (·.name.onePass)⟩

/-- The implementations of AES's CTR mode and of GHASH that the variants `vs`
call, each pair once (by their suffixes), in their order: those AES-GCM's
streaming functions, which call no interleaved loops, are emitted with. -/
def streamPairs (vs : List GcmVariant) : List (Proof.Aes.X86_64.Ctr32Impl × GhashName) :=
  vs.foldl (init := []) fun acc v =>
    if acc.any fun (c, n) => c.suffix ++ n.impl.suffix == v.ctr.suffix ++ v.gh.impl.suffix then acc
    else acc ++ [(v.ctr, v.gh)]

/-- Prepared-context versions of each named interleaved loop (encrypting any
number of blocks from 16 on if `fullR`). -/
theorem StitchName.okR : (n : StitchName) →
    Proof.Gcm.X86_64.Stitch.StitchOkM Proof.Gcm.X86_64.Stitch.CtxMode.prepared n.encR n.decR
      (if n.fullR then 1 else 16) (if n.fullDR then 1 else 16)
  | .vaes => Proof.Gcm.X86_64.StitchR.stitchR_ok.weaken (by decide) (by decide)
  | .vaesAvx512 => Proof.Gcm.X86_64.StitchZH.stitchR_ok.weaken (by decide) (by decide)
  | .aesniAvx => Proof.Gcm.X86_64.StitchAvx8.stitchR_ok

/-- The loops `fullBody` runs on fewer than 16 blocks (from 1 on if
`smallR`). -/
theorem StitchName.okRS : (n : StitchName) →
    Proof.Gcm.X86_64.Stitch.StitchOkSmall Proof.Gcm.X86_64.Stitch.CtxMode.prepared n.encRS n.decRS
      (if n.smallR then 1 else 16) (if n.smallR then 1 else 16)
  | .vaes => Proof.Gcm.X86_64.StitchR.stitchR_ok.small
  | .vaesAvx512 => Proof.Gcm.X86_64.StitchZH.stitchR_ok.small
  | .aesniAvx => Proof.Gcm.X86_64.StitchAvx8.stitchRS_ok

/-- The static and constant-time facts of `encRS` and `decRS`: `encR`'s and
`decR`'s, but for the AES-NI loops'. -/
theorem StitchName.pieceRS : (n : StitchName) → PieceR n →
    Piece n.encRS true n.fullR ∧ Piece n.decRS true n.fullDR
  | .vaes, q => ⟨q.enc, q.dec⟩
  | .vaesAvx512, q => ⟨q.enc, q.dec⟩
  | .aesniAvx, _ => ⟨Proof.Gcm.X86_64.StitchAvx8.encRS_piece, Proof.Gcm.X86_64.StitchAvx8.decRS_piece⟩

def GcmVariant.stitchR (v : GcmVariant) : Option (StitchCode Proof.Gcm.X86_64.Stitch.CtxMode.prepared true) :=
  v.stitch.bind fun p => p.pieceR.map fun q =>
    ⟨p.name.encR, p.name.decR, p.name.fullR, p.name.fullDR, p.name.smallR, p.name.smallR, p.name.small4R,
      p.name.encRS, p.name.decRS, p.name.okR, p.name.okRS, q.enc, q.dec, (p.name.pieceRS q).1, (p.name.pieceRS q).2⟩

theorem StitchToName.okR : (n : StitchToName) →
    Proof.Gcm.X86_64.Stitch.StitchToOkM Proof.Gcm.X86_64.Stitch.CtxMode.prepared n.encR
      (if n.fullR then 1 else 16)
  | .vaes => Proof.Gcm.X86_64.StitchR.stitchTo_ok
  | .vaesAvx512 => Proof.Gcm.X86_64.StitchZHTo.stitchToR_ok
  | .aesniAvx => Proof.Gcm.X86_64.StitchAvx8.stitchToR_ok

def GcmVariant.stitchToR (v : GcmVariant) : Option (StitchToCode Proof.Gcm.X86_64.Stitch.CtxMode.prepared true) :=
  (v.stitch.bind (·.toPart)).bind fun p => p.pieceR.map fun q => ⟨p.name.encR, p.name.fullR, p.name.okR, q.enc⟩

/-- The instance of `vg_aes_gcm_encrypt_blocks_to` of a variant. -/
def blkTo (v : GcmVariant) : StreamTo.BlkToFn Proof.Gcm.X86_64.Stitch.CtxMode.base :=
  .ofBlocks ("vg_aes_gcm_encrypt_blocks_to" ++ v.impl.suffix) v.impl.blkB v.stitchTo

/-- The instance of `vg_aes_gcm_stream_encrypt` calling the implementations `v`. -/
def encFn (v : GcmImpl) : StreamTo.EncFn Proof.Gcm.X86_64.Stitch.CtxMode.base :=
  .ofBase ⟨Spec.Gcm.streamEncryptApi.name ++ v.suffix,
      Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt v.callees)⟩
    (streamEncrypt_framed v) (X86_64.withStackArgScratch_spSafe (streamEncrypt_spSafe v))
    (StreamTo.framed_xdepth (streamEncrypt_xdepth v)) (StreamTo.framed_mx (streamEncrypt_mx v))

/-- The instance of `vg_aes_gcm_stream_encrypt_precomputed` calling the
implementations `v`. -/
def encFnP (v : GcmImpl) : StreamTo.EncFn Proof.Gcm.X86_64.Stitch.CtxMode.powers :=
  .ofPowers ⟨"vg_aes_gcm_stream_encrypt_precomputed" ++ v.suffix,
      Impl.StackScratch.X86_64.withStackArgScratch 2584 1
        (Impl.AesGcm.X86_64.streamEncrypt (v.withBlk v.blkP))⟩
    (streamEncryptP_framed v) (X86_64.withStackArgScratch_spSafe (streamEncryptM_spSafe v v.blkP))
    (StreamTo.framed_xdepth (streamEncryptM_xdepth v v.blkP)) (StreamTo.framed_mx (streamEncryptM_mx v v.blkP))

/-- Below how many bytes `vg_aes_gcm_seal_gather` takes its short path
(copying the text to the output and calling `vg_aes_gcm_seal`, or, from a
first slice holding all the whole blocks, `vg_aes_gcm_seal_split`), rather
than the streaming functions, by the out-of-place interleaved loops a variant
has (`GcmVariant.stitchTo`), as measured on a VAES and AVX-512 Xeon: on
512-bit registers, below 48 blocks, where the streaming functions' calls
cost more than the copy saves; on 256-bit registers, below 16 KiB, where a
slice ending within a block, which the streaming functions buffer, costs
more than the copy saves; and on 128-bit registers (AES-NI and AVX), below
3 KiB, as measured on an AMD EPYC 7763 and a Xeon, where a text of two
slices, the first ending within a block, gains from the streaming functions
from about 3 KiB on. Without them, the streaming path copies the blocks too,
so all texts but those of 2 GiB or more (where the cost of its calls is
negligible) take the copy. -/
def copyBelow (v : GcmVariant) : Nat :=
  match ((v.stitch.bind (·.toPart)).map (·.name) : Option StitchToName) with
  | some .vaesAvx512 => 768
  | some .vaes => 16384
  | some .aesniAvx => 3072
  | none => 2 ^ 31 - 1

theorem copyBelow_lt (v : GcmVariant) : copyBelow v < 2 ^ 31 := by
  unfold copyBelow; split <;> decide

/-- From how many bytes a first slice holding all the whole blocks of a text
on `vg_aes_gcm_seal_gather`'s short path is sealed where it is by
`vg_aes_gcm_seal_split`, rather than copied with the rest and sealed by
`vg_aes_gcm_seal`: without out-of-place interleaved loops, never (their
`vg_aes_gcm_encrypt_blocks_to` copies the blocks and calls
`vg_aes_gcm_encrypt_blocks` anyway); with them, from as many bytes as their
loop needs to beat the copy and `vg_aes_gcm_seal`'s fewer calls, measured by
the Benchmarks workflow on AMD and Intel runners. A 600-byte TLS record's
text was sealed no faster from where it is with VAES or AVX-512, and a
1350-byte one faster; with AES-NI and AVX both were faster. With AVX-512 that
leaves the texts the gathering would otherwise stream (`copyBelow` less a
block). -/
def splitFrom (v : GcmVariant) : Nat :=
  match ((v.stitch.bind (·.toPart)).map (·.name) : Option StitchToName) with
  | some .vaesAvx512 => 752
  | some .vaes => 1024
  | some .aesniAvx => 384
  | none => 2 ^ 31 - 17

theorem splitFrom_pos (v : GcmVariant) : 1 ≤ splitFrom v := by
  unfold splitFrom; split <;> decide

theorem splitFrom_le (v : GcmVariant) : splitFrom v + 16 ≤ copyBelow v := by
  unfold splitFrom copyBelow; split <;> simp_all <;> decide

/-- Whether `vg_aes_gcm_seal_gather_prepared` seals a TLS record's text from
its first slice by `vg_aes_gcm_seal_split_prepared` only when that slice
holds 256 bytes or more (`frontTest`'s `long`): on 512-bit registers, whose
short path of the gathering is faster for less. Elsewhere it does from a
first slice of any length (the path for TLS records is faster than the
others' at every length), but for a text of 256 bytes or more whose first
slice is shorter: the gathering's path for TLS records, which takes it
whole, seals it faster (a 256-byte TLS record, of a 255-byte payload: 22%
faster on Zen 3, with AES-NI and AVX). -/
def tlsLong (v : GcmVariant) : Bool :=
  match ((v.stitch.bind (·.toPart)).map (·.name) : Option StitchToName) with
  | some .vaesAvx512 => true
  | _ => false

theorem sealCode_xdepth (v : GcmImpl) {M : Proof.Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) :
    (v.sealCode (v.withBlk B)).x86_64Depth ≤ 24 := by
  unfold GcmImpl.sealCode; split
  · exact Short.sealM_xdepth v B
  · split
    · exact SealFin.sealFM_xdepth v B
    · exact sealM_xdepth v B

theorem sealCode_mx (v : GcmImpl) {M : Proof.Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) :
    (v.sealCode (v.withBlk B)).allInstrs (fun i => !VG.X86_64.loadsMxcsr i) = true := by
  unfold GcmImpl.sealCode; split
  · exact Short.sealM_mx v B
  · split
    · exact SealFin.sealFM_mx v B
    · exact sealM_mx v B

theorem sealCodeP_xdepth (v : GcmImpl) {M : Proof.Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) :
    (v.sealCodeP (v.withBlk B)).x86_64Depth ≤ 24 := by
  unfold GcmImpl.sealCodeP; split
  · exact Short.sealMP_xdepth v B
  · split
    · exact Short.sealFinP_xdepth v B
    · exact sealM_xdepth v B

theorem sealCodeP_mx (v : GcmImpl) {M : Proof.Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) :
    (v.sealCodeP (v.withBlk B)).allInstrs (fun i => !VG.X86_64.loadsMxcsr i) = true := by
  unfold GcmImpl.sealCodeP; split
  · exact Short.sealMP_mx v B
  · split
    · exact Short.sealFinP_mx v B
    · exact sealM_mx v B

/-- The instance of `vg_aes_gcm_seal` calling the implementations `v`. -/
def sealFn (v : GcmImpl) : Gather.SealFn Proof.Gcm.X86_64.Stitch.CtxMode.base :=
  .ofBase ⟨Spec.Gcm.sealApi.name ++ v.suffix,
      Impl.StackScratch.X86_64.withStackArgScratch 2600 3 (v.sealCode v.callees)⟩
    (sealSel_framed v Short.shortFacts) (X86_64.withStackArgScratch_spSafe (sealCode_spSafe v v.blkB))
    (StreamTo.framed_xdepth (sealCode_xdepth v v.blkB)) (StreamTo.framed_mx (sealCode_mx v v.blkB))

/-- The instance of `vg_aes_gcm_seal_precomputed` calling the implementations `v`. -/
def sealFnP (v : GcmImpl) : Gather.SealFn Proof.Gcm.X86_64.Stitch.CtxMode.powers :=
  .ofPowers ⟨"vg_aes_gcm_seal_precomputed" ++ v.suffix,
      Impl.StackScratch.X86_64.withStackArgScratch 2600 3 (v.sealCode (v.withBlk v.blkP))⟩
    (sealSelP_framed v Short.shortFacts) (X86_64.withStackArgScratch_spSafe (sealCode_spSafe v v.blkP))
    (StreamTo.framed_xdepth (sealCode_xdepth v v.blkP)) (StreamTo.framed_mx (sealCode_mx v v.blkP))

/-- The instance of `vg_aes_gcm_stream_init` calling the implementations `v`,
as an internal function of its own, `vg_aes_gcm_stream_init<suffix>_core`:
`vg_aes_gcm_stream_init` itself has a frame of its own size and clears it
(`Scrub.streamInitReg`). -/
def initFn (v : GcmImpl) : Gather.InitFn :=
  .ofSpec ⟨Spec.Gcm.streamInitApi.name ++ v.gh.suffix ++ "_core",
      Impl.StackScratch.X86_64.withStackScratch 2568 .r8 (Impl.AesGcm.X86_64.streamInit v.callees)⟩
    (streamInit_framed v) (X86_64.withStackScratch_spSafe (by decide) (streamInit_spSafe v))
    (Gather.framedS_xdepth (streamInit_xdepth v)) (Gather.framedS_mx (streamInit_mx v))

/-- The instance of `vg_aes_gcm_stream_aad` calling the implementations `v`,
as `vg_aes_gcm_stream_aad<suffix>_core` (`Scrub.streamAadReg`). -/
def aadFn (v : GcmImpl) : Gather.AadFn :=
  .ofSpec ⟨Spec.Gcm.streamAadApi.name ++ v.gh.suffix ++ "_core",
      Impl.StackScratch.X86_64.withStackScratch 2568 .r9 (Impl.AesGcm.X86_64.streamAad v.callees)⟩
    (streamAad_framed v) (X86_64.withStackScratch_spSafe (by decide) (streamAad_spSafe v))
    (Gather.framedS_xdepth (streamAad_xdepth v)) (Gather.framedS_mx (streamAad_mx v))

/-- The instance of `vg_aes_gcm_stream_finish` calling the implementations `v`,
as an internal function of its own, `vg_aes_gcm_stream_finish<suffix>_core`:
`vg_aes_gcm_stream_finish` itself clears its frame, which over an
implementation of `vg_aes_ctr32` that needs no working space is of its own
size (`Scrub.streamFinishReg`). -/
def finFn (v : GcmImpl) : Gather.FinFn :=
  .ofSpec ⟨Spec.Gcm.streamFinishApi.name ++ v.ctr.suffix ++ v.gh.suffix ++ "_core",
      Impl.StackScratch.X86_64.withStackArgScratch 2576 0 (Impl.AesGcm.X86_64.streamFinish v.callees)⟩
    (streamFinish_framed v) (X86_64.withStackArgScratch_spSafe (streamFinish_spSafe v))
    (StreamTo.framed_xdepth (streamFinish_xdepth v)) (StreamTo.framed_mx (streamFinish_mx v))

/-- The instance of `vg_aes_gcm_stream_encrypt_to` of a variant. -/
def toFn (v : GcmVariant) : Gather.ToFn Proof.Gcm.X86_64.Stitch.CtxMode.base :=
  .ofBase ⟨"vg_aes_gcm_stream_encrypt_to" ++ v.impl.suffix,
      Impl.StackScratch.X86_64.withStackArgScratch 2232 3
        (Impl.AesGcm.X86_64.StreamTo.encrypt (blkTo v).fn (encFn v.impl).fn)⟩
    (StreamTo.streamEncryptTo_framed (blkTo v) (encFn v.impl))
    (X86_64.withStackArgScratch_spSafe (StreamTo.encrypt_spAll (blkTo v) (encFn v.impl)))
    (StreamTo.framed_xdepth (StreamTo.encrypt_xdepth (blkTo v) (encFn v.impl)))
    (StreamTo.framed_mx (StreamTo.encrypt_mx (blkTo v) (encFn v.impl)))

/-- The instance of `vg_aes_gcm_seal_split` of a variant. -/
def splitFn (v : GcmVariant) : Gather.SplitFn Proof.Gcm.X86_64.Stitch.CtxMode.base :=
  .ofBase ⟨"vg_aes_gcm_seal_split" ++ v.impl.suffix,
      Impl.StackScratch.X86_64.withStackArgScratch 2616 5
        (Impl.AesGcm.X86_64.SealSplit.«seal» (v.impl.splitMid (v.impl.withBlk v.impl.blkB) (blkTo v).fn))⟩
    (Split.sealSplit_framed v.impl Short.shortFacts v.impl.blkB (blkTo v))
    (X86_64.withStackArgScratch_spSafe (Split.sealSplit_spSafe v.impl v.impl.blkB (blkTo v)))
    (StreamTo.framed_xdepth (Split.sealSplit_xdepth v.impl v.impl.blkB (blkTo v)))
    (StreamTo.framed_mx (Split.sealSplit_mx v.impl v.impl.blkB (blkTo v)))

/-- The short path of `vg_aes_gcm_seal_gather` of a variant: the text copied
and sealed by `vg_aes_gcm_seal`, or sealed from its first slice by
`vg_aes_gcm_seal_split`. -/
def shortFn (v : GcmVariant) : Gather.ShortFn Proof.Gcm.X86_64.Stitch.CtxMode.base :=
  .ofBoth (sealFn v.impl) (splitFn v) (copyBelow_lt v) (splitFrom_pos v) (splitFrom_le v)

/-- Prepared whole-block implementations, propagated through all callers. -/
def blkR (v : GcmVariant) : BlkFn Proof.Gcm.X86_64.Stitch.CtxMode.prepared :=
  v.impl.blkM v.stitchR ("vg_aes_gcm_encrypt_blocks_prepared" ++ v.impl.suffix)
    ("vg_aes_gcm_decrypt_blocks_prepared" ++ v.impl.suffix)

def blkToR (v : GcmVariant) : StreamTo.BlkToFn Proof.Gcm.X86_64.Stitch.CtxMode.prepared :=
  .ofBlocks ("vg_aes_gcm_encrypt_blocks_to_prepared" ++ v.impl.suffix) (blkR v) v.stitchToR

def encFnR (v : GcmVariant) : StreamTo.EncFn Proof.Gcm.X86_64.Stitch.CtxMode.prepared :=
  .ofPrepared ⟨Spec.Gcm.streamEncryptPreparedApi.name ++ v.impl.suffix,
      Impl.StackScratch.X86_64.withStackArgScratch 2584 1
        (Impl.AesGcm.X86_64.streamEncrypt (v.impl.withBlk (blkR v)))⟩
    (streamEncryptPrepared_framed v.impl (blkR v)) (X86_64.withStackArgScratch_spSafe (streamEncryptM_spSafe v.impl (blkR v)))
    (StreamTo.framed_xdepth (streamEncryptM_xdepth v.impl (blkR v))) (StreamTo.framed_mx (streamEncryptM_mx v.impl (blkR v)))

def toFnR (v : GcmVariant) : Gather.ToFn Proof.Gcm.X86_64.Stitch.CtxMode.prepared :=
  .ofPrepared ⟨"vg_aes_gcm_stream_encrypt_to_prepared" ++ v.impl.suffix,
      Impl.StackScratch.X86_64.withStackArgScratch 2232 3
        (Impl.AesGcm.X86_64.StreamTo.encrypt (blkToR v).fn (encFnR v).fn)⟩
    (StreamTo.streamEncryptToPrepared_framed (blkToR v) (encFnR v))
    (X86_64.withStackArgScratch_spSafe (StreamTo.encrypt_spAll (blkToR v) (encFnR v)))
    (StreamTo.framed_xdepth (StreamTo.encrypt_xdepth (blkToR v) (encFnR v)))
    (StreamTo.framed_mx (StreamTo.encrypt_mx (blkToR v) (encFnR v)))

/-- The instance of `vg_aes_gcm_seal_prepared` of a variant, as an internal
function of its own, `vg_aes_gcm_seal_prepared<suffix>_core`: the function of
that name returns without secret residue. -/
def sealFnR (v : GcmVariant) : Gather.SealFn Proof.Gcm.X86_64.Stitch.CtxMode.prepared :=
  .ofPrepared ⟨Spec.Gcm.sealPreparedApi.name ++ v.impl.suffix ++ "_core",
      Impl.StackScratch.X86_64.withStackArgScratch 2600 3 (v.impl.sealCodeP (v.impl.withBlk (blkR v)))⟩
    (sealSelPrepared_framed v.impl (blkR v) Short.shortFacts)
    (X86_64.withStackArgScratch_spSafe (sealCodeP_spSafe v.impl (blkR v)))
    (StreamTo.framed_xdepth (sealCodeP_xdepth v.impl (blkR v))) (StreamTo.framed_mx (sealCodeP_mx v.impl (blkR v)))

/-- The instance of `vg_aes_gcm_seal_split_prepared` of a variant. -/
def splitFnR (v : GcmVariant) : Gather.SplitFn Proof.Gcm.X86_64.Stitch.CtxMode.prepared :=
  .ofPrepared ⟨"vg_aes_gcm_seal_split_prepared" ++ v.impl.suffix,
      Impl.StackScratch.X86_64.withStackArgScratch 2616 5
        (Impl.AesGcm.X86_64.SealSplit.«seal» (v.impl.splitMidR (v.impl.withBlk (blkR v)) (blkToR v).fn))⟩
    (Split.sealSplitPrepared_framed v.impl (blkR v) (blkToR v) Short.shortFacts)
    (X86_64.withStackArgScratch_spSafe (Split.sealSplitR_spSafe v.impl (blkR v) (blkToR v)))
    (StreamTo.framed_xdepth (Split.sealSplitR_xdepth v.impl (blkR v) (blkToR v)))
    (StreamTo.framed_mx (Split.sealSplitR_mx v.impl (blkR v) (blkToR v)))

/-- The short path of `vg_aes_gcm_seal_gather_prepared` of a variant. -/
def shortFnR (v : GcmVariant) : Gather.ShortFn Proof.Gcm.X86_64.Stitch.CtxMode.prepared :=
  .ofBoth (sealFnR v) (splitFnR v) (copyBelow_lt v) (splitFrom_pos v) (splitFrom_le v)

/-! ## The `_prepared16` artifacts

The 256-bit interleaved loops (`StitchName.vaes`) and the 128-bit ones
(`StitchName.aesniAvx`, which read `H'⁹`–`H'¹⁵`) read only the first eight
pairs of a prepared key context (`StitchR.stitchR_okN 8`,
`StitchAvx8.stitchR_okN 8`); `stitchR16` and `stitchToR16` give them, with
that proof, for the variants that name them,
and `blkR16` and `blkToR16` the instances of the functions their callers
call, as `blkR`, …, `shortFnR` do for the 48 powers. -/

section Prepared16

open Gcm.X86_64.Stitch (CtxMode)

open Gcm.X86_64.Stitch (CtxMode)

/-- Whether a variant's interleaved loops read only the first 16 prepared
powers: the 256-bit and the 128-bit ones. -/
def StitchName.reads16 : StitchName → Bool
  | .vaes => true
  | .vaesAvx512 => false
  | .aesniAvx => true

/-- The loops that read only the first 16 powers, for a key context holding
them. -/
theorem StitchName.okR16 : (n : StitchName) → n.reads16 = true →
    Proof.Gcm.X86_64.Stitch.StitchOkM CtxMode.prepared16 n.encR n.decR
      (if n.fullR then 1 else 16) (if n.fullDR then 1 else 16)
  | .vaes, _ => (Proof.Gcm.X86_64.StitchR.stitchR_okN 8).weaken (by decide) (by decide)
  | .vaesAvx512, h => by cases h
  | .aesniAvx, _ => Proof.Gcm.X86_64.StitchAvx8.stitchR_okN 8

/-- `okR16`'s loops on fewer than 16 blocks. -/
theorem StitchName.okRS16 : (n : StitchName) → n.reads16 = true →
    Proof.Gcm.X86_64.Stitch.StitchOkSmall CtxMode.prepared16 n.encRS n.decRS
      (if n.smallR then 1 else 16) (if n.smallR then 1 else 16)
  | .vaes, _ => (Proof.Gcm.X86_64.StitchR.stitchR_okN 8).small
  | .vaesAvx512, h => by cases h
  | .aesniAvx, _ => Proof.Gcm.X86_64.StitchAvx8.stitchRS_okN 8

/-- The loops of a variant naming ones that read only the first 16 powers,
for a key context of `vg_aes_gcm_prepare16`. -/
def GcmVariant.stitchR16 (v : GcmVariant) : Option (StitchCode CtxMode.prepared16 true) :=
  v.stitch.bind fun p => if h : p.name.reads16 = true then p.pieceR.map fun q =>
      ⟨p.name.encR, p.name.decR, p.name.fullR, p.name.fullDR, p.name.smallR, p.name.smallR, p.name.small4R,
        p.name.encRS, p.name.decRS, p.name.okR16 h, p.name.okRS16 h, q.enc, q.dec,
        (p.name.pieceRS q).1, (p.name.pieceRS q).2⟩
    else none

/-- Whether an out-of-place loop reads only the first 16 prepared powers. -/
def StitchToName.reads16 : StitchToName → Bool
  | .vaes => true
  | .vaesAvx512 => false
  | .aesniAvx => true

/-- The out-of-place loops that read only the first 16 powers, for a key
context holding them. -/
theorem StitchToName.okR16 : (n : StitchToName) → n.reads16 = true →
    Proof.Gcm.X86_64.Stitch.StitchToOkM CtxMode.prepared16 n.encR (if n.fullR then 1 else 16)
  | .vaes, _ => Proof.Gcm.X86_64.StitchR.stitchTo_okN 8
  | .vaesAvx512, h => by cases h
  | .aesniAvx, _ => Proof.Gcm.X86_64.StitchAvx8.stitchToR_okN 8

def GcmVariant.stitchToR16 (v : GcmVariant) : Option (StitchToCode CtxMode.prepared16 true) :=
  (v.stitch.bind (·.toPart)).bind fun p => if h : p.name.reads16 = true then
      p.pieceR.map fun q => ⟨p.name.encR, p.name.fullR, p.name.okR16 h, q.enc⟩
    else none

/-- What the `_prepared16` instances of a variant need besides loops that
read only the first 16 powers: no short path, whose table of powers is copied from all 48, and no
one-pass loop that reads more than 16 (`StitchZHTo.encN`). -/
structure R16 (v : GcmVariant) : Prop where
  short : v.impl.short = false
  onePass : ∀ n, v.impl.onePass = some n → n ≠ .z

/-- Whether a variant's prepared instances read only the first 16 powers:
its loops read no other (`stitchR16`), and `R16` holds. -/
def GcmVariant.r16 (v : GcmVariant) : Option (PLift (R16 v)) :=
  if h : v.stitchR16.isSome = true ∧ v.impl.short = false ∧ v.impl.onePass ≠ some .z then
    some ⟨⟨h.2.1, fun _ hn hz => h.2.2 (hz ▸ hn)⟩⟩
  else none

/-- Whole-block implementations for a key context of `vg_aes_gcm_prepare16`. -/
def blkR16 (v : GcmVariant) : BlkFn Proof.Gcm.X86_64.Stitch.CtxMode.prepared16 :=
  v.impl.blkM v.stitchR16 ("vg_aes_gcm_encrypt_blocks_prepared16" ++ v.impl.suffix)
    ("vg_aes_gcm_decrypt_blocks_prepared16" ++ v.impl.suffix)

def blkToR16 (v : GcmVariant) : StreamTo.BlkToFn Proof.Gcm.X86_64.Stitch.CtxMode.prepared16 :=
  .ofBlocks ("vg_aes_gcm_encrypt_blocks_to_prepared16" ++ v.impl.suffix) (blkR16 v) v.stitchToR16

end Prepared16

/-! ## The instances `vg_aes_gcm_open_to` calls -/

/-- How many bytes at a time `vg_aes_gcm_open_to` of the implementations `v`
copies: 32, with AVX's `vmovdqu`, if their CPUs have AVX, else 16 with SSE2's
`movdqu`. -/
def GcmImpl.copyW (v : GcmImpl) : Impl.ChaCha20Poly1305.X86_64.SealGather.Width :=
  if v.features.contains "avx" then .y32 else .x16

theorem openCode_xdepth (v : GcmImpl) {M : Proof.Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) :
    (v.openCode (v.withBlk B)).x86_64Depth ≤ 24 := by
  unfold GcmImpl.openCode; split
  · exact Short.openM_xdepth v B
  · exact openM_xdepth v B

theorem openCode_mx (v : GcmImpl) {M : Proof.Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) :
    (v.openCode (v.withBlk B)).allInstrs (fun i => !VG.X86_64.loadsMxcsr i) = true := by
  unfold GcmImpl.openCode; split
  · exact Short.openM_mx v B
  · exact openM_mx v B

theorem openCodeP_xdepth (v : GcmImpl) {M : Proof.Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) :
    (v.openCodeP (v.withBlk B)).x86_64Depth ≤ 24 := by
  unfold GcmImpl.openCodeP; split
  · exact Short.openMP_xdepth v B
  · exact Short.openFinP_xdepth v B

theorem openCodeP_mx (v : GcmImpl) {M : Proof.Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) :
    (v.openCodeP (v.withBlk B)).allInstrs (fun i => !VG.X86_64.loadsMxcsr i) = true := by
  unfold GcmImpl.openCodeP; split
  · exact Short.openMP_mx v B
  · exact Short.openFinP_mx v B

/-- The instance of `vg_aes_gcm_open` calling the implementations `v`. -/
def openFn (v : GcmImpl) : OpenTo.OpenFn Proof.Gcm.X86_64.Stitch.CtxMode.base :=
  .ofBase ⟨Spec.Gcm.openApi.name ++ v.suffix,
      Impl.StackScratch.X86_64.withStackArgScratch 2608 4 (v.openCode v.callees)⟩
    (openSel_framed v Short.shortFacts) (X86_64.withStackArgScratch_spSafe (openCode_spSafe v v.blkB))
    (StreamTo.framed_xdepth (openCode_xdepth v v.blkB)) (StreamTo.framed_mx (openCode_mx v v.blkB))

/-- The instance of `vg_aes_gcm_open_prepared` of a variant, as an internal
function of its own, `vg_aes_gcm_open_prepared<suffix>_core`: the function of
that name returns without secret residue. -/
def openFnR (v : GcmVariant) : OpenTo.OpenFn Proof.Gcm.X86_64.Stitch.CtxMode.prepared :=
  .ofPrepared ⟨Spec.Gcm.openPreparedApi.name ++ v.impl.suffix ++ "_core",
      Impl.StackScratch.X86_64.withStackArgScratch 2608 4 (v.impl.openCodeP (v.impl.withBlk (blkR v)))⟩
    (openSelPrepared_framed v.impl (blkR v) Short.shortFacts)
    (X86_64.withStackArgScratch_spSafe (openCodeP_spSafe v.impl (blkR v)))
    (StreamTo.framed_xdepth (openCodeP_xdepth v.impl (blkR v))) (StreamTo.framed_mx (openCodeP_mx v.impl (blkR v)))

/-! ## The instances `vg_aes_gcm_open_to` calls in one pass -/

/-- The prepared powers give the products of a decryption body
(`StitchToDec.PowFinD`). -/
theorem powFinD : Proof.Gcm.X86_64.StitchToDec.PowFinD :=
  fun H => Proof.Gcm.X86_64.Stitch.finD fun _ _ _ _ => Proof.Gcm.X86_64.StitchR.x_φ_hInvF H _

/-- The same, for the 512-bit loops (`StitchZH.PowFinZ`). -/
theorem powFinZ : Proof.Gcm.X86_64.StitchZH.PowFinZ :=
  ⟨fun _ _ hP => Proof.Gcm.X86_64.StitchZ.finZ (Proof.Gcm.X86_64.StitchZP.finP hP),
    Proof.Gcm.X86_64.StitchZP.fin48P⟩

/-- The out-of-place decryption loop of a variant, for a key context of
`vg_aes_gcm_prepare`. -/
def GcmVariant.stitchToDecR (v : GcmVariant) :
    Option (StitchToDecCode Proof.Gcm.X86_64.Stitch.CtxMode.prepared true) :=
  (v.stitch.bind (·.toPart)).bind fun p => p.pieceToDecR.bind (code p.name)
where
  /-- The loop named `n` and its proof. -/
  code : (n : StitchToName) → PieceToDecR n → Option (StitchToDecCode Proof.Gcm.X86_64.Stitch.CtxMode.prepared true)
    | .vaes, q => some ⟨_, Proof.Gcm.X86_64.StitchToDec.decToR_okN powFinD 24, q.dec⟩
    | .vaesAvx512, q => some ⟨_, Proof.Gcm.X86_64.StitchZH.decToR_ok powFinZ, q.dec⟩
    | .aesniAvx, q => some ⟨_, fun s₀ hp _ => Proof.Gcm.X86_64.StitchAvx8.decToR_okN 24 (by decide) s₀ hp (Nat.mod_one _),
        q.dec⟩

/-- The out-of-place decryption loop of a variant, for a key context of
`vg_aes_gcm_prepare16`: the 256-bit loop's and the eight-state AVX loop's
(the 512-bit loop reads more powers than that context holds). -/
def GcmVariant.stitchToDecR16 (v : GcmVariant) :
    Option (StitchToDecCode Proof.Gcm.X86_64.Stitch.CtxMode.prepared16 true) :=
  (v.stitch.bind (·.toPart)).bind fun p => p.pieceToDecR.bind (code p.name)
where
  /-- The loop named `n` and its proof. -/
  code : (n : StitchToName) → PieceToDecR n → Option (StitchToDecCode Proof.Gcm.X86_64.Stitch.CtxMode.prepared16 true)
    | .vaes, q => some ⟨_, Proof.Gcm.X86_64.StitchToDec.decToR_okN powFinD 8, q.dec⟩
    | .aesniAvx, q => some ⟨_, fun s₀ hp _ => Proof.Gcm.X86_64.StitchAvx8.decToR_okN 8 (by decide) s₀ hp (Nat.mod_one _),
        q.dec⟩
    | _, _ => none

/-- The instance of `vg_aes_gcm_decrypt_blocks_to_prepared` of a variant. -/
def blkToDecR (v : GcmVariant) : BlkToDecFn Proof.Gcm.X86_64.Stitch.CtxMode.prepared :=
  .ofBlocks ("vg_aes_gcm_decrypt_blocks_to_prepared" ++ v.impl.suffix) (blkR v) v.stitchToDecR

/-- The instance of `vg_aes_gcm_open_split_prepared` of a variant. -/
def openSplitFnR (v : GcmVariant) : OpenToSplit.OpenSplitFn Proof.Gcm.X86_64.Stitch.CtxMode.prepared :=
  .of ("vg_aes_gcm_open_split_prepared" ++ v.impl.suffix) v.impl (blkR v) (blkToDecR v)

/-! ## `vg_aes_gcm_open_to` in one pass -/

/-- The out-of-place counter mode `vg_aes_gcm_open_to` of a variant decrypts
with on the key context, in one pass and with no copy: that of its
`vg_aes_ctr32` (`Ctr32Impl.ctrTo`). A variant with interleaved loops runs it
only where its prepared key context holds fewer powers than they read,
which the `vg_aes_gcm_prepare` its CPU runs never leaves. -/
def GcmVariant.ctrTo (v : GcmVariant) : Proof.Aes.X86_64.Ctr32ToImpl := v.ctr.ctrTo

/-- The instance of `vg_aes_gcm_decrypt_blocks_to` of a variant, for a key
context of `vg_aes_gcm_init`: `vg_ghash` on the blocks at `src`, then `c`
(`vg_aes_ctr32_to`) from `src` to `dst`. -/
def blkToDecB (v : GcmVariant) (c : Proof.Aes.X86_64.Ctr32ToImpl) :
    BlkToDecFn Proof.Gcm.X86_64.Stitch.CtxMode.base :=
  .ofTo ("vg_aes_gcm_decrypt_blocks_to" ++ v.impl.suffix) v.impl.gh c

/-- The instance of `vg_aes_gcm_open_split` of a variant, decrypting with `c`. -/
def openSplitFnB (v : GcmVariant) (c : Proof.Aes.X86_64.Ctr32ToImpl) :
    OpenToSplit.OpenSplitFn Proof.Gcm.X86_64.Stitch.CtxMode.base :=
  .of ("vg_aes_gcm_open_split" ++ v.impl.suffix) v.impl v.impl.blkB (blkToDecB v c)

/-- `vg_aes_gcm_open_to` of a variant: in one pass, whatever the length, by
`open`'s body out of place (`vg_aes_gcm_open_split`) with its out-of-place
counter mode (`GcmVariant.ctrTo`), in a frame holding its working space. -/
def openToCode (v : GcmVariant) : Prog VG.X86_64.isa :=
  Impl.StackScratch.X86_64.withStackArgScratch Impl.AesGcm.X86_64.OpenToSplit.scratchBytes 6
    (Impl.AesGcm.X86_64.OpenToSplit.openToSplit (openSplitFnB v v.ctrTo).fn)

/-- The stack `openToCode` uses. -/
def openToStack (_ : GcmVariant) : Nat := 2776

theorem openToCode_verified (v : GcmVariant) :
    Verified X86_64.target (openToCode v) (Proof.AesGcm.openToRoundsContract X86_64.abi (openToStack v)) :=
  OpenToSplit.openToSplitBase_framed (openSplitFnB v v.ctrTo)

theorem openToCode_spAll (v : GcmVariant) :
    (openToCode v).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  X86_64.withStackArgScratch_spSafe (OpenToSplit.openToSplit_spAll _ (openSplitFnB v _).spAll)

/-- `openToCode` against the prepared contract, for the implementations
that read only the key context. -/
theorem openToCode_keyed (v : GcmVariant) :
    Verified X86_64.target (openToCode v) (VG.Proof.AesGcm.Flag.openToRoundsContract X86_64.abi (openToStack v)) :=
  Flag.openTo_of_base2776 (openToCode_verified v)

/-- `vg_aes_gcm_open_to_prepared` of a variant: in one pass from
`OpenToSplit.thr` bytes on if it has the out-of-place decryption loop
(`stitchToDecR`), and otherwise by a copy. -/
def openToCodeR (v : GcmVariant) : Prog VG.X86_64.isa :=
  if v.stitchToDecR.isSome then
    Impl.AesGcm.X86_64.OpenToSplit.openToSel Impl.AesGcm.X86_64.OpenToSplit.thr v.impl.copyW (openFnR v).fn
      (openSplitFnR v).fn
  else Impl.AesGcm.X86_64.OpenTo.openTo v.impl.copyW (openFnR v).fn

/-- The stack `openToCodeR` uses. -/
def openToStackR (v : GcmVariant) : Nat := if v.stitchToDecR.isSome then 2776 else 2728

theorem openToCodeR_verified (v : GcmVariant) :
    Verified X86_64.target (openToCodeR v) (Proof.AesGcm.openToPreparedRoundsContract X86_64.abi (openToStackR v)) := by
  unfold openToCodeR openToStackR; split
  · exact OpenToSplit.openToSelPrepared_verified _ v.impl.copyW (openFnR v) (openSplitFnR v)
  · exact OpenTo.openToPrepared_verified v.impl.copyW (openFnR v)

theorem openToCodeR_spAll (v : GcmVariant) :
    (openToCodeR v).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  unfold openToCodeR; split
  · exact OpenToSplit.openToSel_spAll _ v.impl.copyW _ _ (openFnR v).spAll (openSplitFnR v).spAll
  · exact OpenTo.openTo_spAll v.impl.copyW _ (openFnR v).spAll

/-- The stack of `vg_aes_gcm_open_to_prepared` of a variant whose loops read
16 powers. -/
def openToStackR16 (v : GcmVariant) : Nat := if v.stitchToDecR16.isSome then 2776 else 2728

/-! ## The prepared contracts of every implementation

The implementations that read only the key context of `vg_aes_gcm_init`
(256 bytes) are proven against the contracts of the `*_prepared` functions,
whose 1024-byte context begins with it (`Verified.widenFirstArray`); those
that read its first sixteen prepared powers (`*_prepared16`) are proven
against them too, as `PreparedPowersRepr` implies `PreparedPowers16Repr`.
So every implementation has the prepared functions, and their dispatchers a
baseline. -/
/-! ## From the key context -/

theorem sealPrepared_of_base {c : Prog X86_64.isa}
    (h : Verified X86_64.target c (Proof.AesGcm.sealRoundsContract X86_64.abi 2624)) :
    Verified X86_64.target c (Proof.AesGcm.sealPreparedRoundsContract X86_64.abi 2624) :=
  VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 128) (by decide) h
    (fun _ _ _ _ _ _ _ _ _ _ h => h.1) sealFrameSatPrepared_pre

theorem openPrepared_of_base {c : Prog X86_64.isa}
    (h : Verified X86_64.target c (Proof.AesGcm.openRoundsContract X86_64.abi 2632)) :
    Verified X86_64.target c (Proof.AesGcm.openPreparedRoundsContract X86_64.abi 2632) :=
  VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 128) (by decide) h
    (fun _ _ _ _ _ _ _ _ _ _ _ h => h.1) openFrameSatPrepared_pre

theorem streamEncryptPrepared_of_base {c : Prog X86_64.isa}
    (h : Verified X86_64.target c (Proof.AesGcm.streamEncryptRoundsContract X86_64.abi 2608)) :
    Verified X86_64.target c (Proof.AesGcm.streamEncryptPreparedRoundsContract X86_64.abi 2608) :=
  VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 128) (by decide) h
    (fun _ _ _ _ _ _ _ _ h => h.1) streamEncryptFrameSatPrepared_pre

theorem streamDecryptPrepared_of_base {c : Prog X86_64.isa}
    (h : Verified X86_64.target c (Proof.AesGcm.streamDecryptRoundsContract X86_64.abi 2608)) :
    Verified X86_64.target c (Proof.AesGcm.streamDecryptPreparedRoundsContract X86_64.abi 2608) :=
  VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 128) (by decide) h
    (fun _ _ _ _ _ _ _ _ h => h.1) streamDecryptFrameSatPrepared_pre

theorem sealGatherPrepared_of_base {c : Prog X86_64.isa}
    (h : Verified X86_64.target c (Proof.AesGcm.sealGatherRoundsContract X86_64.abi 5128)) :
    Verified X86_64.target c (Proof.AesGcm.sealGatherPreparedRoundsContract X86_64.abi 5128) :=
  VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 128) (by decide) h
    (fun _ _ _ _ _ _ _ _ _ _ _ _ h => ⟨h.1, h.2.1⟩) Gather.gatherFrameSatPrepared_pre

/-- The instance of `vg_aes_gcm_open_prepared` of an implementation that
reads only the key context, as an internal function of its own,
`vg_aes_gcm_open_prepared<suffix>_core`: the function of that name returns
without secret residue. -/
def openFnW (v : GcmImpl) : OpenTo.OpenFn Proof.Gcm.X86_64.Stitch.CtxMode.prepared :=
  .ofPrepared ⟨Spec.Gcm.openPreparedApi.name ++ v.suffix ++ "_core",
      Impl.StackScratch.X86_64.withStackArgScratch 2608 4 (v.openCode v.callees)⟩
    (openPrepared_of_base (openSel_framed v Short.shortFacts))
    (X86_64.withStackArgScratch_spSafe (openCode_spSafe v v.blkB))
    (StreamTo.framed_xdepth (openCode_xdepth v v.blkB)) (StreamTo.framed_mx (openCode_mx v v.blkB))

/-! ## From sixteen prepared powers -/

theorem sealPrepared_of_16 {c : Prog X86_64.isa}
    (h : Verified X86_64.target c (Proof.AesGcm.sealPrepared16RoundsContract X86_64.abi 2624)) :
    Verified X86_64.target c (Proof.AesGcm.sealPreparedRoundsContract X86_64.abi 2624) :=
  VG.X86_64.Verified.widenFirstArray (n := 128) (n' := 128) (by decide) h
    (fun _ _ _ _ _ _ _ _ _ _ h => ⟨h.1, preparedPowers16Repr_of h.2⟩) sealFrameSatPrepared_pre

theorem openPrepared_of_16 {c : Prog X86_64.isa}
    (h : Verified X86_64.target c (Proof.AesGcm.openPrepared16RoundsContract X86_64.abi 2632)) :
    Verified X86_64.target c (Proof.AesGcm.openPreparedRoundsContract X86_64.abi 2632) :=
  VG.X86_64.Verified.widenFirstArray (n := 128) (n' := 128) (by decide) h
    (fun _ _ _ _ _ _ _ _ _ _ _ h => ⟨h.1, preparedPowers16Repr_of h.2⟩) openFrameSatPrepared_pre

theorem streamEncryptPrepared_of_16 {c : Prog X86_64.isa}
    (h : Verified X86_64.target c
      (Proof.AesGcm.streamEncryptPrepared16RoundsContract X86_64.abi 2608)) :
    Verified X86_64.target c (Proof.AesGcm.streamEncryptPreparedRoundsContract X86_64.abi 2608) :=
  VG.X86_64.Verified.widenFirstArray (n := 128) (n' := 128) (by decide) h
    (fun _ _ _ _ _ _ _ _ h => ⟨h.1, preparedPowers16Repr_of h.2⟩)
    streamEncryptFrameSatPrepared_pre

theorem streamDecryptPrepared_of_16 {c : Prog X86_64.isa}
    (h : Verified X86_64.target c
      (Proof.AesGcm.streamDecryptPrepared16RoundsContract X86_64.abi 2608)) :
    Verified X86_64.target c (Proof.AesGcm.streamDecryptPreparedRoundsContract X86_64.abi 2608) :=
  VG.X86_64.Verified.widenFirstArray (n := 128) (n' := 128) (by decide) h
    (fun _ _ _ _ _ _ _ _ h => ⟨h.1, preparedPowers16Repr_of h.2⟩)
    streamDecryptFrameSatPrepared_pre

theorem sealGatherPrepared_of_16 {c : Prog X86_64.isa}
    (h : Verified X86_64.target c
      (Proof.AesGcm.sealGatherPrepared16RoundsContract X86_64.abi 5128)) :
    Verified X86_64.target c (Proof.AesGcm.sealGatherPreparedRoundsContract X86_64.abi 5128) :=
  VG.X86_64.Verified.widenFirstArray (n := 128) (n' := 128) (by decide) h
    (fun _ _ _ _ _ _ _ _ _ _ _ _ h => ⟨h.1, h.2.1, preparedPowers16Repr_of h.2.2⟩)
    Gather.gatherFrameSatPrepared_pre

theorem openToPrepared_of_16 {c : Prog X86_64.isa} {stack : Nat}
    (h : Verified X86_64.target c (Proof.AesGcm.openToPrepared16RoundsContract X86_64.abi stack))
    (hs : ∃ s, (Proof.AesGcm.openToPreparedRoundsContract X86_64.abi stack).pre s) :
    Verified X86_64.target c (Proof.AesGcm.openToPreparedRoundsContract X86_64.abi stack) :=
  VG.X86_64.Verified.widenFirstArray (n := 128) (n' := 128) (by decide) h
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => ⟨h.1, h.2.1, preparedPowers16Repr_of h.2.2⟩) hs

/-! ## The prepared functions, by the flag -/

/-! ### On a prepared key context whose powers are present

`vg_aes_gcm_open_to_prepared`'s code for when the powers are present calls
`vg_aes_gcm_open_prepared` itself, which tests the flag again, so that the
code of `open` on the powers is in one function. The loops that read the
powers are proven for a context of 1024 bytes holding them, and so read them
from the 1032-byte context whose count is at least 48 (`Proof.Gcm.X86_64.Stitch.CtxMode.flagged`). -/

open Gcm.X86_64.Stitch (SPreM SPreTo StitchOkM StitchOkSmall StitchToOkM StitchToDecOkM) in
section

theorem inRegions_1024 {rs : List Region} {a : Addr} (h : InRegions rs a 1032) : InRegions rs a 1024 := by
  obtain ⟨r, hr, hc⟩ := h
  exact ⟨r, hr, by unfold Region.Contains at hc ⊢; omega_using [hc]⟩

theorem sub_1024 (a : Addr) : Region.Sub ⟨a, 1024⟩ ⟨a, 1032⟩ := Region.sub_prefix (by decide)

theorem sPreM_ofFlagged {s₀ : VG.X86_64.State} {lo : Nat} (h : SPreM Proof.Gcm.X86_64.Stitch.CtxMode.flagged s₀ lo) : SPreM Proof.Gcm.X86_64.Stitch.CtxMode.prepared s₀ lo where
  base := h.base
  k_in := inRegions_1024 h.k_in
  wrap_k := by have := h.wrap_k; change _ + 1032 ≤ _ at this; change _ + 1024 ≤ _; omega_using [this]
  d_k := h.d_k.sub_right (sub_1024 _)
  p_k := h.p_k.sub_right (sub_1024 _)
  ok := h.ok.2.2 h.ok.1
  c_k := h.c_k.sub_right (sub_1024 _)
  y_k := h.y_k.sub_right (sub_1024 _)

theorem sPreTo_ofFlagged {s₀ : VG.X86_64.State} (h : SPreTo Proof.Gcm.X86_64.Stitch.CtxMode.flagged s₀) : SPreTo Proof.Gcm.X86_64.Stitch.CtxMode.prepared s₀ :=
  { h with
    k_in := inRegions_1024 h.k_in
    k_c := h.k_c.sub_left (sub_1024 _)
    k_y := h.k_y.sub_left (sub_1024 _)
    k_o := h.k_o.sub_left (sub_1024 _)
    k_p := h.k_p.sub_left (sub_1024 _)
    wrap_k := by have := h.wrap_k; change _ + 1032 ≤ _ at this; change _ + 1024 ≤ _; omega_using [this]
    ok := h.ok.2.2 h.ok.1 }

/-- Loops on the prepared powers, on a context whose powers are present. -/
def StitchCode.flagged {al : Bool} (c : StitchCode Proof.Gcm.X86_64.Stitch.CtxMode.prepared al) : StitchCode Proof.Gcm.X86_64.Stitch.CtxMode.flagged al :=
  { c with
    ok := ⟨fun s hp hn => c.ok.1 s (sPreM_ofFlagged hp) hn, fun s hp hn => c.ok.2 s (sPreM_ofFlagged hp) hn⟩
    okS := ⟨fun s hp hn => c.okS.1 s (sPreM_ofFlagged hp) hn, fun s hp hn => c.okS.2 s (sPreM_ofFlagged hp) hn⟩ }

def StitchToDecCode.flagged {al : Bool} (c : StitchToDecCode Proof.Gcm.X86_64.Stitch.CtxMode.prepared al) :
    StitchToDecCode Proof.Gcm.X86_64.Stitch.CtxMode.flagged al :=
  { c with ok := fun s hp hn => c.ok s (sPreTo_ofFlagged hp) hn }

end

/-- The blocks functions of a variant, on a context whose powers are present:
those of `blkR`. -/
def blkF (v : GcmVariant) : BlkFn Proof.Gcm.X86_64.Stitch.CtxMode.flagged :=
  v.impl.blkM (v.stitchR.map StitchCode.flagged) ("vg_aes_gcm_encrypt_blocks_prepared" ++ v.impl.suffix)
    ("vg_aes_gcm_decrypt_blocks_prepared" ++ v.impl.suffix)

def blkToDecF (v : GcmVariant) : BlkToDecFn Proof.Gcm.X86_64.Stitch.CtxMode.flagged :=
  .ofBlocks ("vg_aes_gcm_decrypt_blocks_to_prepared" ++ v.impl.suffix) (blkF v) (v.stitchToDecR.map StitchToDecCode.flagged)

/-- `vg_aes_gcm_open_split_prepared` of a variant, on a context whose powers
are present. -/
def openSplitFnF (v : GcmVariant) : OpenToSplit.OpenSplitFn Proof.Gcm.X86_64.Stitch.CtxMode.flagged :=
  .of ("vg_aes_gcm_open_split_prepared" ++ v.impl.suffix) v.impl (blkF v) (blkToDecF v)

/-- `vg_aes_gcm_open_prepared` of a variant whose loops read the 48 powers:
by the flag, its code on the powers or its code on the key context. -/
def openCodeF (v : GcmVariant) : Prog VG.X86_64.isa :=
  Impl.Gcm.X86_64.Flag.onFlag 48
    (Impl.StackScratch.X86_64.withStackArgScratch 2608 4 (v.impl.openCodeP (v.impl.withBlk (blkR v))))
    (Impl.StackScratch.X86_64.withStackArgScratch 2608 4 (v.impl.openCode v.impl.callees))

theorem openCodeF_verified (v : GcmVariant) :
    Verified X86_64.target (openCodeF v) (VG.Proof.AesGcm.Flag.openRoundsContractB 48 X86_64.abi 2632) :=
  Flag.open_onFlagB (openSelPrepared_framed v.impl (blkR v) Short.shortFacts) (openSel_framed v.impl Short.shortFacts)

theorem openCodeF_spAll (v : GcmVariant) :
    (openCodeF v).all (fun i => !X86_64.isa.writesSp i) = true :=
  VG.X86_64.onFlag_spSafe (X86_64.withStackArgScratch_spSafe (openCodeP_spSafe v.impl (blkR v)))
    (X86_64.withStackArgScratch_spSafe (openCode_spSafe v.impl v.impl.blkB))

theorem openCodeF_xdepth (v : GcmVariant) : (openCodeF v).x86_64Depth ≤ 2632 := by
  have h₁ : (Impl.StackScratch.X86_64.withStackArgScratch 2608 4
      (v.impl.openCodeP (v.impl.withBlk (blkR v)))).x86_64Depth ≤ 2632 :=
    StreamTo.framed_xdepth (openCodeP_xdepth v.impl (blkR v))
  have h₂ : (Impl.StackScratch.X86_64.withStackArgScratch 2608 4
      (v.impl.openCode v.impl.callees)).x86_64Depth ≤ 2632 :=
    StreamTo.framed_xdepth (openCode_xdepth v.impl v.impl.blkB)
  simp only [openCodeF, Impl.Gcm.X86_64.Flag.onFlag, Code.iteCold, Code.x86_64Depth, Nat.max_le, h₁, h₂,
    Nat.zero_le, and_self]

theorem openCodeF_mx (v : GcmVariant) : (openCodeF v).allInstrs (fun i => !VG.X86_64.loadsMxcsr i) = true := by
  have h₁ : (Impl.StackScratch.X86_64.withStackArgScratch 2608 4
      (v.impl.openCodeP (v.impl.withBlk (blkR v)))).allInstrs (fun i => !VG.X86_64.loadsMxcsr i) = true :=
    StreamTo.framed_mx (openCodeP_mx v.impl (blkR v))
  have h₂ : (Impl.StackScratch.X86_64.withStackArgScratch 2608 4
      (v.impl.openCode v.impl.callees)).allInstrs (fun i => !VG.X86_64.loadsMxcsr i) = true :=
    StreamTo.framed_mx (openCode_mx v.impl v.impl.blkB)
  simp only [openCodeF, Impl.Gcm.X86_64.Flag.onFlag, Code.iteCold, Code.allInstrs, h₁, h₂, Bool.and_true]
  rfl

/-- `vg_aes_gcm_open_prepared` of a variant whose loops read the 48 powers,
for `open_to` to call on a context whose powers are present, as an internal
function of its own, `vg_aes_gcm_open_prepared<suffix>_core`, with the code
as it was: the function of that name returns without secret residue
(`openR_scrubbed`). -/
def openFnF (v : GcmVariant) : OpenTo.OpenFn Proof.Gcm.X86_64.Stitch.CtxMode.flagged :=
  .ofFlagged ⟨Spec.Gcm.openPreparedApi.name ++ v.impl.suffix ++ "_core", openCodeF v⟩ (openCodeF_verified v)
    (openCodeF_spAll v) (openCodeF_xdepth v) (openCodeF_mx v)

/-- `vg_aes_gcm_open_to_prepared`'s code on a context whose powers are
present, of a variant whose loops read the 48 powers. -/
def openToCodeF (v : GcmVariant) : Prog VG.X86_64.isa :=
  if v.stitchToDecR.isSome then
    Impl.AesGcm.X86_64.OpenToSplit.openToSel Impl.AesGcm.X86_64.OpenToSplit.thr v.impl.copyW (openFnF v).fn
      (openSplitFnF v).fn
  else Impl.AesGcm.X86_64.OpenTo.openTo v.impl.copyW (openFnF v).fn

theorem openToCodeF_verified (v : GcmVariant) :
    Verified X86_64.target (openToCodeF v)
      (VG.Proof.AesGcm.Flag.openToFlaggedRoundsContract 48 X86_64.abi (openToStackR v)) := by
  unfold openToCodeF openToStackR; split
  · exact OpenToSplit.openToSelFlagged_verified (by decide) _ v.impl.copyW (openFnF v) (openSplitFnF v)
  · exact OpenTo.openToFlagged_verified (by decide) v.impl.copyW (openFnF v)

theorem openToCodeF_spAll (v : GcmVariant) :
    (openToCodeF v).all (fun i => !X86_64.isa.writesSp i) = true := by
  unfold openToCodeF; split
  · exact OpenToSplit.openToSel_spAll _ _ _ _ (openFnF v).spAll (openSplitFnF v).spAll
  · exact OpenTo.openTo_spAll _ _ (openFnF v).spAll

/-- The stack `openToCodeR_onFlag` uses: the larger of its two branches'. -/
def openToStackF (v : GcmVariant) : Nat := max (openToStackR v) (openToStack v)

/-- `vg_aes_gcm_open_to_prepared` of a variant whose loops read the 48 powers: by
the count, its code calling `vg_aes_gcm_open_prepared`, or `openToCode` on
the key context, which decrypts in one pass with the variant's
out-of-place counter mode. Both branches are proven at the larger of their
stacks. -/
theorem openToCodeR_onFlag (v : GcmVariant) :
    Verified X86_64.target
      (Impl.Gcm.X86_64.Flag.onFlag 48 (openToCodeF v) (openToCode v))
      (VG.Proof.AesGcm.Flag.openToRoundsContract X86_64.abi (openToStackF v)) := by
  have h := openToCodeF_verified v
  have hb := openToCode_verified v
  unfold openToStackF openToStackR openToStack at *
  cases hc : v.stitchToDecR.isSome <;>
    simp only [hc, Bool.false_eq_true, ↓reduceIte] at h hb ⊢
  · exact Flag.openTo_onFlagF2776 (Or.inr rfl) (VG.X86_64.Verified.stack_mono (by decide) h
      (OpenToSplit.toSatF2776_pre (by decide))) hb
  · exact Flag.openTo_onFlagF2776 (Or.inr rfl) h hb

theorem openToCodeR_onFlag_spAll (v : GcmVariant) :
    (Impl.Gcm.X86_64.Flag.onFlag 48 (openToCodeF v) (openToCode v)).all
      (fun i => !X86_64.isa.writesSp i) = true :=
  VG.X86_64.onFlag_spSafe (openToCodeF_spAll v) (openToCode_spAll v)

/-! ### `seal_gather` on a prepared key context whose powers are present

Its code for when the powers are present calls `vg_aes_gcm_seal_prepared` and,
through its encryption out of place, `vg_aes_gcm_stream_encrypt_prepared` by
their public names, as `open_to` calls `vg_aes_gcm_open_prepared`. -/

open Gcm.X86_64.Stitch (SPreTo) in
/-- Out-of-place loops on the prepared powers, on a context whose powers are
present. -/
def StitchToCode.flagged {al : Bool} (c : StitchToCode Proof.Gcm.X86_64.Stitch.CtxMode.prepared al) :
    StitchToCode Proof.Gcm.X86_64.Stitch.CtxMode.flagged al :=
  { c with ok := fun s hp hn => c.ok s (sPreTo_ofFlagged hp) hn }

def blkToF (v : GcmVariant) : StreamTo.BlkToFn Proof.Gcm.X86_64.Stitch.CtxMode.flagged :=
  .ofBlocks ("vg_aes_gcm_encrypt_blocks_to_prepared" ++ v.impl.suffix) (blkF v) (v.stitchToR.map StitchToCode.flagged)

/-- `vg_aes_gcm_seal_prepared` of a variant whose loops read the 48 powers: by
the flag, its code on the powers or its code on the key context. -/
def sealCodeF (v : GcmVariant) : Prog VG.X86_64.isa :=
  Impl.Gcm.X86_64.Flag.onFlag 48
    (Impl.StackScratch.X86_64.withStackArgScratch 2600 3 (v.impl.sealCodeP (v.impl.withBlk (blkR v))))
    (Impl.StackScratch.X86_64.withStackArgScratch 2600 3 (v.impl.sealCode v.impl.callees))

theorem sealCodeF_verified (v : GcmVariant) :
    Verified X86_64.target (sealCodeF v) (VG.Proof.AesGcm.Flag.sealRoundsContractB 48 X86_64.abi 2624) :=
  Flag.seal_onFlagB (sealSelPrepared_framed v.impl (blkR v) Short.shortFacts) (sealSel_framed v.impl Short.shortFacts)

theorem sealCodeF_spAll (v : GcmVariant) : (sealCodeF v).all (fun i => !X86_64.isa.writesSp i) = true :=
  VG.X86_64.onFlag_spSafe (X86_64.withStackArgScratch_spSafe (sealCodeP_spSafe v.impl (blkR v)))
    (X86_64.withStackArgScratch_spSafe (sealCode_spSafe v.impl v.impl.blkB))

theorem sealCodeF_xdepth (v : GcmVariant) : (sealCodeF v).x86_64Depth ≤ 2624 := by
  have h₁ : (Impl.StackScratch.X86_64.withStackArgScratch 2600 3
      (v.impl.sealCodeP (v.impl.withBlk (blkR v)))).x86_64Depth ≤ 2624 :=
    StreamTo.framed_xdepth (sealCodeP_xdepth v.impl (blkR v))
  have h₂ : (Impl.StackScratch.X86_64.withStackArgScratch 2600 3 (v.impl.sealCode v.impl.callees)).x86_64Depth ≤ 2624 :=
    StreamTo.framed_xdepth (sealCode_xdepth v.impl v.impl.blkB)
  simp only [sealCodeF, Impl.Gcm.X86_64.Flag.onFlag, Code.iteCold, Code.x86_64Depth, Nat.max_le, h₁, h₂,
    Nat.zero_le, and_self]

theorem sealCodeF_mx (v : GcmVariant) : (sealCodeF v).allInstrs (fun i => !VG.X86_64.loadsMxcsr i) = true := by
  have h₁ : (Impl.StackScratch.X86_64.withStackArgScratch 2600 3
      (v.impl.sealCodeP (v.impl.withBlk (blkR v)))).allInstrs (fun i => !VG.X86_64.loadsMxcsr i) = true :=
    StreamTo.framed_mx (sealCodeP_mx v.impl (blkR v))
  have h₂ : (Impl.StackScratch.X86_64.withStackArgScratch 2600 3
      (v.impl.sealCode v.impl.callees)).allInstrs (fun i => !VG.X86_64.loadsMxcsr i) = true :=
    StreamTo.framed_mx (sealCode_mx v.impl v.impl.blkB)
  simp only [sealCodeF, Impl.Gcm.X86_64.Flag.onFlag, Code.iteCold, Code.allInstrs, h₁, h₂, Bool.and_true]
  rfl

/-- `vg_aes_gcm_stream_encrypt_prepared` of a variant whose loops read the 48
powers: by the flag, its code on the powers or its code on the key context. -/
def streamEncryptCodeF (v : GcmVariant) : Prog VG.X86_64.isa :=
  Impl.Gcm.X86_64.Flag.onFlag 48
    (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt (v.impl.withBlk (blkR v))))
    (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt v.impl.callees))

theorem streamEncryptCodeF_verified (v : GcmVariant) :
    Verified X86_64.target (streamEncryptCodeF v) (VG.Proof.AesGcm.Flag.streamEncryptRoundsContractB 48 X86_64.abi 2608) :=
  Flag.streamEncrypt_onFlagB (streamEncryptPrepared_framed v.impl (blkR v)) (streamEncrypt_framed v.impl)

theorem streamEncryptCodeF_spAll (v : GcmVariant) :
    (streamEncryptCodeF v).all (fun i => !X86_64.isa.writesSp i) = true :=
  VG.X86_64.onFlag_spSafe (X86_64.withStackArgScratch_spSafe (streamEncryptM_spSafe v.impl (blkR v)))
    (X86_64.withStackArgScratch_spSafe (streamEncrypt_spSafe v.impl))

theorem streamEncryptCodeF_xdepth (v : GcmVariant) : (streamEncryptCodeF v).x86_64Depth ≤ 2608 := by
  have h₁ : (Impl.StackScratch.X86_64.withStackArgScratch 2584 1
      (Impl.AesGcm.X86_64.streamEncrypt (v.impl.withBlk (blkR v)))).x86_64Depth ≤ 2608 :=
    StreamTo.framed_xdepth (streamEncryptM_xdepth v.impl (blkR v))
  have h₂ : (Impl.StackScratch.X86_64.withStackArgScratch 2584 1
      (Impl.AesGcm.X86_64.streamEncrypt v.impl.callees)).x86_64Depth ≤ 2608 :=
    StreamTo.framed_xdepth (streamEncryptM_xdepth v.impl v.impl.blkB)
  simp only [streamEncryptCodeF, Impl.Gcm.X86_64.Flag.onFlag, Code.iteCold, Code.x86_64Depth, Nat.max_le, h₁, h₂,
    Nat.zero_le, and_self]

theorem streamEncryptCodeF_mx (v : GcmVariant) :
    (streamEncryptCodeF v).allInstrs (fun i => !VG.X86_64.loadsMxcsr i) = true := by
  have h₁ : (Impl.StackScratch.X86_64.withStackArgScratch 2584 1
      (Impl.AesGcm.X86_64.streamEncrypt (v.impl.withBlk (blkR v)))).allInstrs (fun i => !VG.X86_64.loadsMxcsr i) = true :=
    StreamTo.framed_mx (streamEncryptM_mx v.impl (blkR v))
  have h₂ : (Impl.StackScratch.X86_64.withStackArgScratch 2584 1
      (Impl.AesGcm.X86_64.streamEncrypt v.impl.callees)).allInstrs (fun i => !VG.X86_64.loadsMxcsr i) = true :=
    StreamTo.framed_mx (streamEncryptM_mx v.impl v.impl.blkB)
  simp only [streamEncryptCodeF, Impl.Gcm.X86_64.Flag.onFlag, Code.iteCold, Code.allInstrs, h₁, h₂, Bool.and_true]
  rfl

/-- The instance of `vg_aes_gcm_stream_encrypt_prepared` of a variant whose
loops read the 48 prepared powers, as an internal function of its own,
`vg_aes_gcm_stream_encrypt_prepared<suffix>_core`, with the code as it was:
the function of that name returns without secret residue
(`streamEncryptR_scrubbed`). -/
def encFnF (v : GcmVariant) : StreamTo.EncFn Proof.Gcm.X86_64.Stitch.CtxMode.flagged :=
  .ofFlagged ⟨Spec.Gcm.streamEncryptPreparedApi.name ++ v.impl.suffix ++ "_core", streamEncryptCodeF v⟩
    (streamEncryptCodeF_verified v) (streamEncryptCodeF_spAll v) (streamEncryptCodeF_xdepth v) (streamEncryptCodeF_mx v)

def toFnF (v : GcmVariant) : Gather.ToFn Proof.Gcm.X86_64.Stitch.CtxMode.flagged :=
  .ofFlagged ⟨"vg_aes_gcm_stream_encrypt_to_prepared" ++ v.impl.suffix,
      Impl.StackScratch.X86_64.withStackArgScratch 2232 3
        (Impl.AesGcm.X86_64.StreamTo.encrypt (blkToF v).fn (encFnF v).fn)⟩
    (StreamTo.streamEncryptToFlagged_framed (by decide) (blkToF v) (encFnF v))
    (X86_64.withStackArgScratch_spSafe (StreamTo.encrypt_spAll (blkToF v) (encFnF v)))
    (StreamTo.framed_xdepth (StreamTo.encrypt_xdepth (blkToF v) (encFnF v)))
    (StreamTo.framed_mx (StreamTo.encrypt_mx (blkToF v) (encFnF v)))

/-- `vg_aes_gcm_seal_prepared` of a variant whose loops read the 48 powers,
as an internal function of its own, `vg_aes_gcm_seal_prepared<suffix>_core`,
with the code as it was: the function of that name returns without secret
residue (`sealR_scrubbed`). -/
def sealFnF (v : GcmVariant) : Gather.SealFn Proof.Gcm.X86_64.Stitch.CtxMode.flagged :=
  .ofFlagged ⟨Spec.Gcm.sealPreparedApi.name ++ v.impl.suffix ++ "_core", sealCodeF v⟩ (sealCodeF_verified v)
    (sealCodeF_spAll v) (sealCodeF_xdepth v) (sealCodeF_mx v)

/-- `splitFrameSatP` with the 1032-byte context. -/
def splitFrameSatF : VG.X86_64.State :=
  { Split.splitFrameSat with
    mem := fun a => if a = 0x1400 then 48 else Split.splitFrameSat.mem a
    rd := [⟨0x1000, 1032⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0, 0⟩, ⟨0x8008, 40⟩] }

theorem splitFrameSatF_pre {t : Nat} (ht : t ≤ 48) :
    ∃ s, (VG.Proof.AesGcm.Flag.sealSplitFlaggedContract t X86_64.abi 2672).pre s := by
  refine ⟨splitFrameSatF, ?_⟩
  sig_pre [VG.Proof.AesGcm.Flag.sealSplitFlaggedContract, VG.Proof.AesGcm.Flag.sealSplitFlaggedSig,
    VG.Proof.AesGcm.Flag.sealSplitFlaggedPre, Proof.Gcm.sealSplitPost, X86_64.abi, X86_64.argRegs, splitFrameSatF,
    Split.splitFrameSat, Split.splitSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (refine VG.Proof.AesGcm.Flag.flaggedPowers_of_zeroMem ht (fun i hi => ?_) (by decide)
       simp only [VG.Proof.AesGcm.Flag.ctx_ne1024 hi, ite_false]
       split
       · next h => exfalso; bv_omega
       · rfl)

/-- `vg_aes_gcm_seal_split_prepared` of a variant, on a context whose powers
are present: its proof on the prepared powers, of the context's first 1024
bytes. -/
def splitFnF (v : GcmVariant) : Gather.SplitFn Proof.Gcm.X86_64.Stitch.CtxMode.flagged :=
  .ofFlagged ⟨"vg_aes_gcm_seal_split_prepared" ++ v.impl.suffix,
      Impl.StackScratch.X86_64.withStackArgScratch 2616 5
        (Impl.AesGcm.X86_64.SealSplit.«seal» (v.impl.splitMidR (v.impl.withBlk (blkR v)) (blkToR v).fn))⟩
    (VG.X86_64.Verified.widenFirstArray (n := 128) (n' := 129) (by decide)
      (Split.sealSplitPrepared_framed v.impl (blkR v) (blkToR v) Short.shortFacts)
      (fun _ _ _ _ _ _ _ _ _ _ _ _ h => ⟨h.1, h.2.1, h.2.2.2.2 h.2.2.1⟩) (splitFrameSatF_pre (by decide)))
    (X86_64.withStackArgScratch_spSafe (Split.sealSplitR_spSafe v.impl (blkR v) (blkToR v)))
    (StreamTo.framed_xdepth (Split.sealSplitR_xdepth v.impl (blkR v) (blkToR v)))
    (StreamTo.framed_mx (Split.sealSplitR_mx v.impl (blkR v) (blkToR v)))

def shortFnF (v : GcmVariant) : Gather.ShortFn Proof.Gcm.X86_64.Stitch.CtxMode.flagged :=
  .ofBoth (sealFnF v) (splitFnF v) (copyBelow_lt v) (splitFrom_pos v) (splitFrom_le v)

/-- `vg_aes_gcm_seal_gather_prepared`'s code on a context whose powers are
present, of a variant whose loops read the 48 powers. -/
def sealGatherCodeF (v : GcmVariant) : Prog VG.X86_64.isa :=
  Impl.StackScratch.X86_64.withStackArgScratch 240 5
    (Impl.AesGcm.X86_64.SealGather.withFront (tlsLong v) (splitFnF v).fn
      (Impl.AesGcm.X86_64.SealGather.sealGather (shortFnF v).quick (shortFnF v).fast (shortFnF v).test
        (shortFnF v).code (initFn v.impl).fn (aadFn v.impl).fn (toFnF v).fn (finFn v.impl).fn))

theorem sealGatherCodeF_spAll (v : GcmVariant) :
    (sealGatherCodeF v).all (fun i => !X86_64.isa.writesSp i) = true :=
  X86_64.withStackArgScratch_spSafe
    (Gather.withFront_spAll (shortFnF v) (initFn v.impl) (aadFn v.impl) (toFnF v) (finFn v.impl) (splitFnF v) (tlsLong v))

/-- `vg_aes_gcm_seal_gather_prepared` of a variant whose loops read the 48
powers: by the flag, its code calling `vg_aes_gcm_seal_prepared` and
`vg_aes_gcm_stream_encrypt_prepared`, or its code on the key context. -/
theorem sealGatherR_onFlag (v : GcmVariant) :
    Verified X86_64.target
      (Impl.Gcm.X86_64.Flag.onFlag 48 (sealGatherCodeF v)
        (Impl.StackScratch.X86_64.withStackArgScratch 240 5
          (Impl.AesGcm.X86_64.SealGather.sealGather (shortFn v).quick (shortFn v).fast (shortFn v).test
            (shortFn v).code (initFn v.impl).fn (aadFn v.impl).fn (toFn v).fn (finFn v.impl).fn)))
      (VG.Proof.AesGcm.Flag.sealGatherRoundsContract X86_64.abi 5128) :=
  Flag.sealGather_onFlagF (Or.inr rfl)
    (Gather.sealGatherFlagged_framed (by decide) (shortFnF v) (initFn v.impl) (aadFn v.impl) (toFnF v) (finFn v.impl)
      (splitFnF v) (tlsLong v))
    (Gather.sealGather_framed (shortFn v) (initFn v.impl) (aadFn v.impl) (toFn v) (finFn v.impl))

/-! ### The 16 powers, on a context whose count is at least 16

The same for the implementations whose loops read 16 powers: their
`open_to` and `seal_gather` call their `vg_aes_gcm_open_prepared`,
`vg_aes_gcm_seal_prepared` and `vg_aes_gcm_stream_encrypt_prepared` by their
public names, which test the count against 16 again. -/

open Gcm.X86_64.Stitch (SPreM SPreTo) in
section

theorem sPreM_ofFlagged16 {s₀ : VG.X86_64.State} {lo : Nat}
    (h : SPreM (Proof.Gcm.X86_64.Stitch.CtxMode.flaggedT 16) s₀ lo) :
    SPreM Proof.Gcm.X86_64.Stitch.CtxMode.prepared16 s₀ lo where
  base := h.base
  k_in := inRegions_1024 h.k_in
  wrap_k := by have := h.wrap_k; change _ + 1032 ≤ _ at this; change _ + 1024 ≤ _; omega_using [this]
  d_k := h.d_k.sub_right (sub_1024 _)
  p_k := h.p_k.sub_right (sub_1024 _)
  ok := h.ok.2.1 h.ok.1
  c_k := h.c_k.sub_right (sub_1024 _)
  y_k := h.y_k.sub_right (sub_1024 _)

theorem sPreTo_ofFlagged16 {s₀ : VG.X86_64.State} (h : SPreTo (Proof.Gcm.X86_64.Stitch.CtxMode.flaggedT 16) s₀) :
    SPreTo Proof.Gcm.X86_64.Stitch.CtxMode.prepared16 s₀ :=
  { h with
    k_in := inRegions_1024 h.k_in
    k_c := h.k_c.sub_left (sub_1024 _)
    k_y := h.k_y.sub_left (sub_1024 _)
    k_o := h.k_o.sub_left (sub_1024 _)
    k_p := h.k_p.sub_left (sub_1024 _)
    wrap_k := by have := h.wrap_k; change _ + 1032 ≤ _ at this; change _ + 1024 ≤ _; omega_using [this]
    ok := h.ok.2.1 h.ok.1 }

/-- Loops on the first 16 prepared powers, on a context whose count is at
least 16. -/
def StitchCode.flagged16 {al : Bool} (c : StitchCode Proof.Gcm.X86_64.Stitch.CtxMode.prepared16 al) :
    StitchCode (Proof.Gcm.X86_64.Stitch.CtxMode.flaggedT 16) al :=
  { c with
    ok := ⟨fun s hp hn => c.ok.1 s (sPreM_ofFlagged16 hp) hn, fun s hp hn => c.ok.2 s (sPreM_ofFlagged16 hp) hn⟩
    okS := ⟨fun s hp hn => c.okS.1 s (sPreM_ofFlagged16 hp) hn, fun s hp hn => c.okS.2 s (sPreM_ofFlagged16 hp) hn⟩ }

def StitchToDecCode.flagged16 {al : Bool} (c : StitchToDecCode Proof.Gcm.X86_64.Stitch.CtxMode.prepared16 al) :
    StitchToDecCode (Proof.Gcm.X86_64.Stitch.CtxMode.flaggedT 16) al :=
  { c with ok := fun s hp hn => c.ok s (sPreTo_ofFlagged16 hp) hn }

def StitchToCode.flagged16 {al : Bool} (c : StitchToCode Proof.Gcm.X86_64.Stitch.CtxMode.prepared16 al) :
    StitchToCode (Proof.Gcm.X86_64.Stitch.CtxMode.flaggedT 16) al :=
  { c with ok := fun s hp hn => c.ok s (sPreTo_ofFlagged16 hp) hn }

end

/-- The blocks functions of a variant whose loops read 16 powers, on a context
whose count is at least 16: those of `blkR16`. -/
def blkF16 (v : GcmVariant) : BlkFn (Proof.Gcm.X86_64.Stitch.CtxMode.flaggedT 16) :=
  v.impl.blkM (v.stitchR16.map StitchCode.flagged16) ("vg_aes_gcm_encrypt_blocks_prepared16" ++ v.impl.suffix)
    ("vg_aes_gcm_decrypt_blocks_prepared16" ++ v.impl.suffix)

def blkToDecF16 (v : GcmVariant) : BlkToDecFn (Proof.Gcm.X86_64.Stitch.CtxMode.flaggedT 16) :=
  .ofBlocks ("vg_aes_gcm_decrypt_blocks_to_prepared16" ++ v.impl.suffix) (blkF16 v)
    (v.stitchToDecR16.map StitchToDecCode.flagged16)

def openSplitFnF16 (v : GcmVariant) : OpenToSplit.OpenSplitFn (Proof.Gcm.X86_64.Stitch.CtxMode.flaggedT 16) :=
  .of ("vg_aes_gcm_open_split_prepared16" ++ v.impl.suffix) v.impl (blkF16 v) (blkToDecF16 v)

def blkToF16 (v : GcmVariant) : StreamTo.BlkToFn (Proof.Gcm.X86_64.Stitch.CtxMode.flaggedT 16) :=
  .ofBlocks ("vg_aes_gcm_encrypt_blocks_to_prepared16" ++ v.impl.suffix) (blkF16 v)
    (v.stitchToR16.map StitchToCode.flagged16)

/-- `vg_aes_gcm_open_prepared` of a variant whose loops read 16 powers: by the
count, its code on them or its code on the key context. -/
def openCodeF16 (v : GcmVariant) : Prog VG.X86_64.isa :=
  Impl.Gcm.X86_64.Flag.onFlag 16
    (Impl.StackScratch.X86_64.withStackArgScratch 2608 4 (v.impl.openCodeP (v.impl.withBlk (blkR16 v))))
    (Impl.StackScratch.X86_64.withStackArgScratch 2608 4 (v.impl.openCode v.impl.callees))

theorem openCodeF16_verified (v : GcmVariant) (r : R16 v) :
    Verified X86_64.target (openCodeF16 v) (VG.Proof.AesGcm.Flag.openRoundsContractB 16 X86_64.abi 2632) :=
  Flag.open_onFlag16B (openSelPrepared16_framed v.impl (blkR16 v) Short.shortFacts r.short)
    (openSel_framed v.impl Short.shortFacts)

theorem openCodeF16_spAll (v : GcmVariant) :
    (openCodeF16 v).all (fun i => !X86_64.isa.writesSp i) = true :=
  VG.X86_64.onFlag_spSafe (X86_64.withStackArgScratch_spSafe (openCodeP_spSafe v.impl (blkR16 v)))
    (X86_64.withStackArgScratch_spSafe (openCode_spSafe v.impl v.impl.blkB))

theorem openCodeF16_xdepth (v : GcmVariant) : (openCodeF16 v).x86_64Depth ≤ 2632 := by
  have h₁ : (Impl.StackScratch.X86_64.withStackArgScratch 2608 4
      (v.impl.openCodeP (v.impl.withBlk (blkR16 v)))).x86_64Depth ≤ 2632 :=
    StreamTo.framed_xdepth (openCodeP_xdepth v.impl (blkR16 v))
  have h₂ : (Impl.StackScratch.X86_64.withStackArgScratch 2608 4
      (v.impl.openCode v.impl.callees)).x86_64Depth ≤ 2632 :=
    StreamTo.framed_xdepth (openCode_xdepth v.impl v.impl.blkB)
  simp only [openCodeF16, Impl.Gcm.X86_64.Flag.onFlag, Code.iteCold, Code.x86_64Depth, Nat.max_le, h₁, h₂,
    Nat.zero_le, and_self]

theorem openCodeF16_mx (v : GcmVariant) :
    (openCodeF16 v).allInstrs (fun i => !VG.X86_64.loadsMxcsr i) = true := by
  have h₁ : (Impl.StackScratch.X86_64.withStackArgScratch 2608 4
      (v.impl.openCodeP (v.impl.withBlk (blkR16 v)))).allInstrs (fun i => !VG.X86_64.loadsMxcsr i) = true :=
    StreamTo.framed_mx (openCodeP_mx v.impl (blkR16 v))
  have h₂ : (Impl.StackScratch.X86_64.withStackArgScratch 2608 4
      (v.impl.openCode v.impl.callees)).allInstrs (fun i => !VG.X86_64.loadsMxcsr i) = true :=
    StreamTo.framed_mx (openCode_mx v.impl v.impl.blkB)
  simp only [openCodeF16, Impl.Gcm.X86_64.Flag.onFlag, Code.iteCold, Code.allInstrs, h₁, h₂, Bool.and_true]
  rfl

/-- `vg_aes_gcm_open_prepared` of a variant whose loops read 16 powers, for
`open_to` to call on a context whose count is at least 16, as an internal
function of its own, `vg_aes_gcm_open_prepared<suffix>_core`, with the code
as it was: the function of that name returns without secret residue
(`openR16_scrubbed`). -/
def openFnF16 (v : GcmVariant) (r : R16 v) : OpenTo.OpenFn (Proof.Gcm.X86_64.Stitch.CtxMode.flaggedT 16) :=
  .ofFlagged ⟨Spec.Gcm.openPreparedApi.name ++ v.impl.suffix ++ "_core", openCodeF16 v⟩ (openCodeF16_verified v r)
    (openCodeF16_spAll v) (openCodeF16_xdepth v) (openCodeF16_mx v)

/-- `vg_aes_gcm_open_to_prepared`'s code on a context whose count is at least
16, of a variant whose loops read 16 powers. -/
def openToCodeF16 (v : GcmVariant) (r : R16 v) : Prog VG.X86_64.isa :=
  if v.stitchToDecR16.isSome then
    Impl.AesGcm.X86_64.OpenToSplit.openToSel Impl.AesGcm.X86_64.OpenToSplit.thr v.impl.copyW (openFnF16 v r).fn
      (openSplitFnF16 v).fn
  else Impl.AesGcm.X86_64.OpenTo.openTo v.impl.copyW (openFnF16 v r).fn

theorem openToCodeF16_verified (v : GcmVariant) (r : R16 v) :
    Verified X86_64.target (openToCodeF16 v r)
      (VG.Proof.AesGcm.Flag.openToFlaggedRoundsContract 16 X86_64.abi (openToStackR16 v)) := by
  unfold openToCodeF16 openToStackR16; split
  · exact OpenToSplit.openToSelFlagged_verified (by decide) _ v.impl.copyW (openFnF16 v r) (openSplitFnF16 v)
  · exact OpenTo.openToFlagged_verified (by decide) v.impl.copyW (openFnF16 v r)

theorem openToCodeF16_spAll (v : GcmVariant) (r : R16 v) :
    (openToCodeF16 v r).all (fun i => !X86_64.isa.writesSp i) = true := by
  unfold openToCodeF16; split
  · exact OpenToSplit.openToSel_spAll _ _ _ _ (openFnF16 v r).spAll (openSplitFnF16 v).spAll
  · exact OpenTo.openTo_spAll _ _ (openFnF16 v r).spAll

/-- The stack `openToCodeR16_onFlag` uses: the larger of its two branches'. -/
def openToStackF16 (v : GcmVariant) : Nat := max (openToStackR16 v) (openToStack v)

/-- `vg_aes_gcm_open_to_prepared` of a variant whose loops read 16 powers: by
the count, its code calling `vg_aes_gcm_open_prepared`, or `openToCode` on
the key context, which decrypts in one pass with the variant's
out-of-place counter mode. Both branches are proven at the larger of their
stacks. -/
theorem openToCodeR16_onFlag (v : GcmVariant) (r : R16 v) :
    Verified X86_64.target
      (Impl.Gcm.X86_64.Flag.onFlag 16 (openToCodeF16 v r) (openToCode v))
      (VG.Proof.AesGcm.Flag.openToRoundsContract X86_64.abi (openToStackF16 v)) := by
  have h := openToCodeF16_verified v r
  have hb := openToCode_verified v
  unfold openToStackF16 openToStackR16 openToStack at *
  cases hc : v.stitchToDecR16.isSome <;>
    simp only [hc, Bool.false_eq_true, ↓reduceIte] at h hb ⊢
  · exact Flag.openTo_onFlagF2776 (Or.inl rfl) (VG.X86_64.Verified.stack_mono (by decide) h
      (OpenToSplit.toSatF2776_pre (by decide))) hb
  · exact Flag.openTo_onFlagF2776 (Or.inl rfl) h hb

theorem openToCodeR16_onFlag_spAll (v : GcmVariant) (r : R16 v) :
    (Impl.Gcm.X86_64.Flag.onFlag 16 (openToCodeF16 v r) (openToCode v)).all
      (fun i => !X86_64.isa.writesSp i) = true :=
  VG.X86_64.onFlag_spSafe (openToCodeF16_spAll v r) (openToCode_spAll v)

/-- `vg_aes_gcm_seal_prepared` of a variant whose loops read 16 powers: by the
count, its code on them or its code on the key context. -/
def sealCodeF16 (v : GcmVariant) : Prog VG.X86_64.isa :=
  Impl.Gcm.X86_64.Flag.onFlag 16
    (Impl.StackScratch.X86_64.withStackArgScratch 2600 3 (v.impl.sealCodeP (v.impl.withBlk (blkR16 v))))
    (Impl.StackScratch.X86_64.withStackArgScratch 2600 3 (v.impl.sealCode v.impl.callees))

theorem sealCodeF16_verified (v : GcmVariant) (r : R16 v) :
    Verified X86_64.target (sealCodeF16 v) (VG.Proof.AesGcm.Flag.sealRoundsContractB 16 X86_64.abi 2624) :=
  Flag.seal_onFlag16B (sealSelPrepared16_framed v.impl (blkR16 v) Short.shortFacts r.short)
    (sealSel_framed v.impl Short.shortFacts)

theorem sealCodeF16_spAll (v : GcmVariant) : (sealCodeF16 v).all (fun i => !X86_64.isa.writesSp i) = true :=
  VG.X86_64.onFlag_spSafe (X86_64.withStackArgScratch_spSafe (sealCodeP_spSafe v.impl (blkR16 v)))
    (X86_64.withStackArgScratch_spSafe (sealCode_spSafe v.impl v.impl.blkB))

theorem sealCodeF16_xdepth (v : GcmVariant) : (sealCodeF16 v).x86_64Depth ≤ 2624 := by
  have h₁ : (Impl.StackScratch.X86_64.withStackArgScratch 2600 3
      (v.impl.sealCodeP (v.impl.withBlk (blkR16 v)))).x86_64Depth ≤ 2624 :=
    StreamTo.framed_xdepth (sealCodeP_xdepth v.impl (blkR16 v))
  have h₂ : (Impl.StackScratch.X86_64.withStackArgScratch 2600 3 (v.impl.sealCode v.impl.callees)).x86_64Depth ≤ 2624 :=
    StreamTo.framed_xdepth (sealCode_xdepth v.impl v.impl.blkB)
  simp only [sealCodeF16, Impl.Gcm.X86_64.Flag.onFlag, Code.iteCold, Code.x86_64Depth, Nat.max_le, h₁, h₂,
    Nat.zero_le, and_self]

theorem sealCodeF16_mx (v : GcmVariant) : (sealCodeF16 v).allInstrs (fun i => !VG.X86_64.loadsMxcsr i) = true := by
  have h₁ : (Impl.StackScratch.X86_64.withStackArgScratch 2600 3
      (v.impl.sealCodeP (v.impl.withBlk (blkR16 v)))).allInstrs (fun i => !VG.X86_64.loadsMxcsr i) = true :=
    StreamTo.framed_mx (sealCodeP_mx v.impl (blkR16 v))
  have h₂ : (Impl.StackScratch.X86_64.withStackArgScratch 2600 3
      (v.impl.sealCode v.impl.callees)).allInstrs (fun i => !VG.X86_64.loadsMxcsr i) = true :=
    StreamTo.framed_mx (sealCode_mx v.impl v.impl.blkB)
  simp only [sealCodeF16, Impl.Gcm.X86_64.Flag.onFlag, Code.iteCold, Code.allInstrs, h₁, h₂, Bool.and_true]
  rfl

/-- `vg_aes_gcm_stream_encrypt_prepared` of a variant whose loops read 16
powers: by the count, its code on them or its code on the key context. -/
def streamEncryptCodeF16 (v : GcmVariant) : Prog VG.X86_64.isa :=
  Impl.Gcm.X86_64.Flag.onFlag 16
    (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt (v.impl.withBlk (blkR16 v))))
    (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt v.impl.callees))

theorem streamEncryptCodeF16_verified (v : GcmVariant) :
    Verified X86_64.target (streamEncryptCodeF16 v)
      (VG.Proof.AesGcm.Flag.streamEncryptRoundsContractB 16 X86_64.abi 2608) :=
  Flag.streamEncrypt_onFlag16B (streamEncryptPrepared16_framed v.impl (blkR16 v)) (streamEncrypt_framed v.impl)

theorem streamEncryptCodeF16_spAll (v : GcmVariant) :
    (streamEncryptCodeF16 v).all (fun i => !X86_64.isa.writesSp i) = true :=
  VG.X86_64.onFlag_spSafe (X86_64.withStackArgScratch_spSafe (streamEncryptM_spSafe v.impl (blkR16 v)))
    (X86_64.withStackArgScratch_spSafe (streamEncrypt_spSafe v.impl))

theorem streamEncryptCodeF16_xdepth (v : GcmVariant) : (streamEncryptCodeF16 v).x86_64Depth ≤ 2608 := by
  have h₁ : (Impl.StackScratch.X86_64.withStackArgScratch 2584 1
      (Impl.AesGcm.X86_64.streamEncrypt (v.impl.withBlk (blkR16 v)))).x86_64Depth ≤ 2608 :=
    StreamTo.framed_xdepth (streamEncryptM_xdepth v.impl (blkR16 v))
  have h₂ : (Impl.StackScratch.X86_64.withStackArgScratch 2584 1
      (Impl.AesGcm.X86_64.streamEncrypt v.impl.callees)).x86_64Depth ≤ 2608 :=
    StreamTo.framed_xdepth (streamEncryptM_xdepth v.impl v.impl.blkB)
  simp only [streamEncryptCodeF16, Impl.Gcm.X86_64.Flag.onFlag, Code.iteCold, Code.x86_64Depth, Nat.max_le, h₁, h₂,
    Nat.zero_le, and_self]

theorem streamEncryptCodeF16_mx (v : GcmVariant) :
    (streamEncryptCodeF16 v).allInstrs (fun i => !VG.X86_64.loadsMxcsr i) = true := by
  have h₁ : (Impl.StackScratch.X86_64.withStackArgScratch 2584 1
      (Impl.AesGcm.X86_64.streamEncrypt (v.impl.withBlk (blkR16 v)))).allInstrs (fun i => !VG.X86_64.loadsMxcsr i) = true :=
    StreamTo.framed_mx (streamEncryptM_mx v.impl (blkR16 v))
  have h₂ : (Impl.StackScratch.X86_64.withStackArgScratch 2584 1
      (Impl.AesGcm.X86_64.streamEncrypt v.impl.callees)).allInstrs (fun i => !VG.X86_64.loadsMxcsr i) = true :=
    StreamTo.framed_mx (streamEncryptM_mx v.impl v.impl.blkB)
  simp only [streamEncryptCodeF16, Impl.Gcm.X86_64.Flag.onFlag, Code.iteCold, Code.allInstrs, h₁, h₂, Bool.and_true]
  rfl

/-- Whether `vg_aes_gcm_stream_encrypt_prepared` of a variant whose loops read
16 powers clears the registers only on the paths that call
(`streamEncryptClr`), as the variant on VAES and VPCLMULQDQ on 256-bit
registers does, whose callees never touch the stack. -/
def GcmVariant.streamF16Clr (v : GcmVariant) : Bool :=
  v.stitch.any fun p => match p.name with
    | .vaes => true
    | _ => false

/-- `streamEncryptCodeF16`, clearing the registers after each call
(`streamEncryptClr`, at the level of 256-bit registers). -/
def streamEncryptCodeF16C (v : GcmVariant) : Prog VG.X86_64.isa :=
  Impl.Gcm.X86_64.Flag.onFlag 16
    (Impl.StackScratch.X86_64.withStackArgScratch 2584 1
      (Impl.AesGcm.X86_64.streamEncryptClr (v.impl.withBlk (blkR16 v)) .avx))
    (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncryptClr v.impl.callees .avx))

/-- The code of `vg_aes_gcm_stream_encrypt_prepared` of a variant whose loops
read 16 powers: `streamEncryptCodeF16C` where `GcmVariant.streamF16Clr` says
so, else `streamEncryptCodeF16`. -/
def streamEncryptCodeF16S (v : GcmVariant) : Prog VG.X86_64.isa :=
  if v.streamF16Clr then streamEncryptCodeF16C v else streamEncryptCodeF16 v

theorem streamEncryptCodeF16S_verified (v : GcmVariant) :
    Verified X86_64.target (streamEncryptCodeF16S v)
      (VG.Proof.AesGcm.Flag.streamEncryptRoundsContractB 16 X86_64.abi 2608) := by
  unfold streamEncryptCodeF16S
  split
  · exact Flag.streamEncrypt_onFlag16B (streamEncryptClr16_framed .avx v.impl (blkR16 v))
      (streamEncryptClrB_framed .avx v.impl v.impl.blkB)
  · exact streamEncryptCodeF16_verified v

theorem streamEncryptCodeF16S_spAll (v : GcmVariant) :
    (streamEncryptCodeF16S v).all (fun i => !X86_64.isa.writesSp i) = true := by
  unfold streamEncryptCodeF16S
  split
  · exact VG.X86_64.onFlag_spSafe (streamEncryptClr_spSafe .avx v.impl (blkR16 v))
      (streamEncryptClr_spSafe .avx v.impl v.impl.blkB)
  · exact streamEncryptCodeF16_spAll v

theorem streamEncryptCodeF16S_xdepth (v : GcmVariant) : (streamEncryptCodeF16S v).x86_64Depth ≤ 2608 := by
  unfold streamEncryptCodeF16S
  split
  · have h₁ := streamEncryptClr_xdepth .avx v.impl (blkR16 v)
    have h₂ := streamEncryptClr_xdepth .avx v.impl v.impl.blkB
    simp only [streamEncryptCodeF16C, Impl.Gcm.X86_64.Flag.onFlag, Code.iteCold, Code.x86_64Depth, Nat.max_le]
    exact ⟨Nat.zero_le _, ⟨⟨⟨Nat.zero_le _, Nat.zero_le _⟩, h₁⟩, h₂⟩⟩
  · exact streamEncryptCodeF16_xdepth v

theorem streamEncryptCodeF16S_mx (v : GcmVariant) :
    (streamEncryptCodeF16S v).allInstrs (fun i => !VG.X86_64.loadsMxcsr i) = true := by
  unfold streamEncryptCodeF16S
  split
  · have h₁ := streamEncryptClr_mx .avx v.impl (blkR16 v)
    have h₂ : (Impl.StackScratch.X86_64.withStackArgScratch 2584 1
        (Impl.AesGcm.X86_64.streamEncryptClr v.impl.callees .avx)).allInstrs (fun i => !VG.X86_64.loadsMxcsr i) = true :=
      streamEncryptClr_mx .avx v.impl v.impl.blkB
    simp only [streamEncryptCodeF16C, Impl.Gcm.X86_64.Flag.onFlag, Code.iteCold, Code.allInstrs, h₁, h₂,
      Bool.and_true]
    rfl
  · exact streamEncryptCodeF16_mx v

/-- Whether `vg_aes_gcm_stream_encrypt_prepared` of a variant whose loops read
16 powers calls whole-blocks functions that zero their working space before
they return (`BlkFn.wipeW`), and clears only the scratch registers on return,
as the variant on AES-NI and PCLMULQDQ in `VEX.128` does, whose loops leave
the powers and the keystream there. -/
def GcmVariant.streamF16Wipe (v : GcmVariant) : Bool :=
  v.stitch.any fun p => match p.name with
    | .aesniAvx => true
    | _ => false

/-- The instance of `vg_aes_gcm_stream_encrypt_prepared` of a variant whose
loops read 16 powers; where that function is followed by the clearing of the
scratch registers (`GcmVariant.streamF16Clr`, `GcmVariant.streamF16Wipe`), as
an internal function of its own,
`vg_aes_gcm_stream_encrypt_prepared<suffix>_core`, with the code as it was. -/
def encFnF16 (v : GcmVariant) : StreamTo.EncFn (Proof.Gcm.X86_64.Stitch.CtxMode.flaggedT 16) :=
  .ofFlagged ⟨Spec.Gcm.streamEncryptPreparedApi.name ++ v.impl.suffix ++
        (if v.streamF16Clr || v.streamF16Wipe then "_core" else ""),
      streamEncryptCodeF16S v⟩
    (streamEncryptCodeF16S_verified v) (streamEncryptCodeF16S_spAll v) (streamEncryptCodeF16S_xdepth v)
    (streamEncryptCodeF16S_mx v)

def toFnF16 (v : GcmVariant) : Gather.ToFn (Proof.Gcm.X86_64.Stitch.CtxMode.flaggedT 16) :=
  .ofFlagged ⟨"vg_aes_gcm_stream_encrypt_to_prepared16" ++ v.impl.suffix,
      Impl.StackScratch.X86_64.withStackArgScratch 2232 3
        (Impl.AesGcm.X86_64.StreamTo.encrypt (blkToF16 v).fn (encFnF16 v).fn)⟩
    (StreamTo.streamEncryptToFlagged_framed (by decide) (blkToF16 v) (encFnF16 v))
    (X86_64.withStackArgScratch_spSafe (StreamTo.encrypt_spAll (blkToF16 v) (encFnF16 v)))
    (StreamTo.framed_xdepth (StreamTo.encrypt_xdepth (blkToF16 v) (encFnF16 v)))
    (StreamTo.framed_mx (StreamTo.encrypt_mx (blkToF16 v) (encFnF16 v)))

/-- The instance of `vg_aes_gcm_seal_prepared` of a variant whose loops read
16 powers, as an internal function of its own,
`vg_aes_gcm_seal_prepared<suffix>_core`, with the code as it was: the function
of that name returns without secret residue (`sealR16_scrubbed`). -/
def sealFnF16 (v : GcmVariant) (r : R16 v) : Gather.SealFn (Proof.Gcm.X86_64.Stitch.CtxMode.flaggedT 16) :=
  .ofFlagged ⟨Spec.Gcm.sealPreparedApi.name ++ v.impl.suffix ++ "_core",
      sealCodeF16 v⟩ (sealCodeF16_verified v r)
    (sealCodeF16_spAll v) (sealCodeF16_xdepth v) (sealCodeF16_mx v)

/-- `vg_aes_gcm_seal_split_prepared16` of a variant, on a context whose count is
at least 16: its proof on the first 16 prepared powers, of the context's
first 1024 bytes. -/
def splitFnF16 (v : GcmVariant) (r : R16 v) : Gather.SplitFn (Proof.Gcm.X86_64.Stitch.CtxMode.flaggedT 16) :=
  .ofFlagged ⟨"vg_aes_gcm_seal_split_prepared16" ++ v.impl.suffix,
      Impl.StackScratch.X86_64.withStackArgScratch 2616 5
        (Impl.AesGcm.X86_64.SealSplit.«seal» (v.impl.splitMidR (v.impl.withBlk (blkR16 v)) (blkToR16 v).fn))⟩
    (VG.X86_64.Verified.widenFirstArray (n := 128) (n' := 129) (by decide)
      (Split.sealSplitPrepared16_framed v.impl (blkR16 v) (blkToR16 v) Short.shortFacts r.onePass)
      (fun _ _ _ _ _ _ _ _ _ _ _ _ h => ⟨h.1, h.2.1, h.2.2.2.1 h.2.2.1⟩) (splitFrameSatF_pre (by decide)))
    (X86_64.withStackArgScratch_spSafe (Split.sealSplitR_spSafe v.impl (blkR16 v) (blkToR16 v)))
    (StreamTo.framed_xdepth (Split.sealSplitR_xdepth v.impl (blkR16 v) (blkToR16 v)))
    (StreamTo.framed_mx (Split.sealSplitR_mx v.impl (blkR16 v) (blkToR16 v)))

def shortFnF16 (v : GcmVariant) (r : R16 v) : Gather.ShortFn (Proof.Gcm.X86_64.Stitch.CtxMode.flaggedT 16) :=
  .ofBoth (sealFnF16 v r) (splitFnF16 v r) (copyBelow_lt v) (splitFrom_pos v) (splitFrom_le v)

/-- `vg_aes_gcm_seal_gather_prepared`'s code on a context whose count is at
least 16, of a variant whose loops read 16 powers. -/
def sealGatherCodeF16 (v : GcmVariant) (r : R16 v) : Prog VG.X86_64.isa :=
  Impl.StackScratch.X86_64.withStackArgScratch 240 5
    (Impl.AesGcm.X86_64.SealGather.withFront (tlsLong v) (splitFnF16 v r).fn
      (Impl.AesGcm.X86_64.SealGather.sealGather (shortFnF16 v r).quick (shortFnF16 v r).fast
        (shortFnF16 v r).test (shortFnF16 v r).code (initFn v.impl).fn (aadFn v.impl).fn (toFnF16 v).fn
        (finFn v.impl).fn true))

theorem sealGatherCodeF16_spAll (v : GcmVariant) (r : R16 v) :
    (sealGatherCodeF16 v r).all (fun i => !X86_64.isa.writesSp i) = true :=
  X86_64.withStackArgScratch_spSafe
    (Gather.withFront_spAll (shortFnF16 v r) (initFn v.impl) (aadFn v.impl) (toFnF16 v) (finFn v.impl)
      (splitFnF16 v r) (tlsLong v) true)

/-- `vg_aes_gcm_seal_gather_prepared` of a variant whose loops read 16 powers:
by the count, its code calling `vg_aes_gcm_seal_prepared` and
`vg_aes_gcm_stream_encrypt_prepared`, or its code on the key context. -/
theorem sealGatherR16_onFlag (v : GcmVariant) (r : R16 v) :
    Verified X86_64.target
      (Impl.Gcm.X86_64.Flag.onFlag 16 (sealGatherCodeF16 v r)
        (Impl.StackScratch.X86_64.withStackArgScratch 240 5
          (Impl.AesGcm.X86_64.SealGather.sealGather (shortFn v).quick (shortFn v).fast (shortFn v).test
            (shortFn v).code (initFn v.impl).fn (aadFn v.impl).fn (toFn v).fn (finFn v.impl).fn)))
      (VG.Proof.AesGcm.Flag.sealGatherRoundsContract X86_64.abi 5128) :=
  Flag.sealGather_onFlagF (Or.inl rfl)
    (Gather.sealGatherFlagged_framed (by decide) (shortFnF16 v r) (initFn v.impl) (aadFn v.impl) (toFnF16 v)
      (finFn v.impl) (splitFnF16 v r) (tlsLong v) true)
    (Gather.sealGather_framed (shortFn v) (initFn v.impl) (aadFn v.impl) (toFn v) (finFn v.impl))

end VG.Proof.AesGcm.X86_64
