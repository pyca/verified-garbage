module

public import VerifiedGarbage.Proof.Gcm.PreparedPowers
public import VerifiedGarbage.Impl.AesGcm.X86_64.OpenTo
public import VerifiedGarbage.Proof.AesGcm.Rounds
public import VerifiedGarbage.Proof.AesGcm.Flag
public import VerifiedGarbage.Proof.AesGcm.X86_64.Contract
public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Callee
public import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Context
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Copy
import VerifiedGarbage.Proof.ChaCha20Poly1305.Gathered
import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.Framework.X86_64.CallSp
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit

/-!
# AES-GCM decryption out of place, by a copy, x86-64: the function

Untrusted: everything here is checked by Lean. The contract the proof of
`vg_aes_gcm_open_to` is written against, for a key context of kind `M`
(`toK M`), which the shared ones imply (`OpenTo/Verified.lean`), and its
proof (`openTo_wp`). It calls an instance of `vg_aes_gcm_open` for its key
context (`CtxMode`: that of `vg_aes_gcm_init`, or a prepared one), an
artifact with its working space in a frame of its own, so what the proof
needs of it is its contract on the key context's contents
(`Proof/AesGcm/Rounds.lean`), in the terms of this target: a contract whose
precondition is the layout the call gives it (`openPreK`), which implies the
shared one's, whose postcondition is `Proof.AesGcm.openX86_64`'s, and whose
public data are the arguments and whether it succeeds (`openPubK`), as
`Gather/SealCallee.lean` does for `vg_aes_gcm_seal`. With `B` the base of the 2728 bytes of stack below the
stack pointer (`rsp = B + 2728`), the function pushes its frame of eleven
words at `P = B + 2640` (`pushed`), copies the ciphertext from `src` to
`dst` (`copied_wp`), puts the call's arguments in the registers and the
lowest four words of its frame (`ready_wp`), calls `vg_aes_gcm_open` on
`dst` in place (`called_wp`, by `openK`), which writes only `dst` and the
stack below `P`, and zeroes `dst` if it returned 0 (`after_wp`). Every write
is to `dst` or to the stack below `rsp` (`Frame [dR s, stkR s]`), so the
arguments, the other buffers and the return address stay as they were.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.OpenTo

open VG VG.X86_64 VG.X86_64.RegUpd VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm dstB Fn)
open VG.Impl.AesGcm.X86_64.OpenTo (frameRegs entry callRegs stArg callArgs wipeArgs wipeBody wipe after openTo)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Impl.ChaCha20Poly1305.X86_64.SealGather (Width)
open VG.Proof.AesGcm (arg args ret rounds)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxCiph ctxH openResult)
open VG.Impl.AesGcm.X86_64 (Fn)
open VG.Proof.AesGcm (arg args ret rounds onePub openLeak)
open VG.Proof.AesGcm.X86_64.Gather (CallFn)

/-! ## The function called -/
/-! ## `vg_aes_gcm_open(ctx = rdi, rounds = rsi, nonce = rdx, nonce_len = rcx, aad = r8,
aad_len = r9, data = [rsp + 8], len = [rsp + 16], tag = [rsp + 24], tag_len = [rsp + 32])` -/

/-- What a call of `vg_aes_gcm_open` needs, for a key context of kind `M`:
the layout of its shared contract with 2632 bytes of stack. -/
def openPreK (M : CtxMode) (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, M.len⟩
  let nonce : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  let aad : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  let data : Region := ⟨arg s 0, (arg s 1).toNat⟩
  let tag : Region := ⟨arg s 2, (arg s 3).toNat⟩
  let stk : Region := below (s.gpr .rsp) 2632
  s.rd = [ctx, nonce, aad, tag, args s 4] ∧ s.wr = [data] ∧
    ctx.Disjoint data ∧ nonce.Disjoint data ∧ aad.Disjoint data ∧ data.Disjoint tag ∧
    data.Disjoint (args s 4) ∧
    (ret s).Disjoint ctx ∧ (ret s).Disjoint nonce ∧ (ret s).Disjoint aad ∧ (ret s).Disjoint data ∧
    (ret s).Disjoint tag ∧ (ret s).Disjoint (args s 4) ∧
    stk.Disjoint ctx ∧ stk.Disjoint nonce ∧ stk.Disjoint aad ∧ stk.Disjoint data ∧ stk.Disjoint tag ∧
    stk.Disjoint (args s 4) ∧
    (s.gpr .rdi).toNat + M.len ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 64 ∧
    (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 64 ∧
    2632 ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 40 ≤ 2 ^ 64 ∧ rounds s ∧ M.ok s.mem (s.gpr .rdi)

/-- The public data of a call of `vg_aes_gcm_open`: its arguments, and
whether it succeeds. -/
def openPubK (s₁ s₂ : State) : Prop := onePub 4 s₁ s₂ ∧ openLeak s₁ = openLeak s₂

/-- A call of `vg_aes_gcm_open` for a key context of kind `M`. -/
def openK (M : CtxMode) : Contract isa where
  pre := openPreK M
  post := Proof.AesGcm.openX86_64.post
  pub := openPubK

theorem openSpec_pre {s : State} (h : openPreK CtxMode.base s) :
    (Proof.AesGcm.openRoundsContract X86_64.abi 2632).pre s := by
  sig_split h
  rename_i a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a₁₇ a₁₈ a₁₉ a₂₀ a₂₁ a₂₂ a₂₃ a₂₄ a₂₅ a₂₆ a₂₇
  clear h
  sig_pre [Proof.AesGcm.openRoundsContract, Spec.Gcm.openSig, Spec.Gcm.openPre, X86_64.abi, X86_64.argRegs]
  sig_reduce [Proof.AesGcm.openRoundsContract, Spec.Gcm.openSig, Spec.Gcm.openPre, X86_64.abi, X86_64.argRegs,
    Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, X86_64.stackArg, X86_64.stackArgAddr, List.getD,
    List.range, List.range.loop, VG.X86_64.below]
  sig_and_intros
  all_goals simp only [Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, X86_64.stackArg,
    X86_64.stackArgAddr, VG.X86_64.below, Nat.mul_one, Proof.AesGcm.rounds, CtxMode.base] at *
  all_goals first
    | with_reducible assumption
    | omega

theorem openSpecR_pre {s : State} (h : openPreK CtxMode.prepared s) :
    (Proof.AesGcm.openPreparedRoundsContract X86_64.abi 2632).pre s := by
  sig_split h
  rename_i a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a₁₇ a₁₈ a₁₉ a₂₀ a₂₁ a₂₂ a₂₃ a₂₄ a₂₅ a₂₆ a₂₇
  have a₂₈ := h
  clear h
  sig_pre [Proof.AesGcm.openPreparedRoundsContract, Spec.Gcm.openPrecomputedSig, Spec.Gcm.openPrecomputedSig,
    Proof.Gcm.openPowersPre, X86_64.abi, X86_64.argRegs]
  sig_reduce [Proof.AesGcm.openPreparedRoundsContract, Spec.Gcm.openPrecomputedSig, Spec.Gcm.openPrecomputedSig,
    Proof.Gcm.openPowersPre, X86_64.abi, X86_64.argRegs, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret,
    X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below]
  sig_and_intros
  all_goals simp only [Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, X86_64.stackArg,
    X86_64.stackArgAddr, VG.X86_64.below, Nat.mul_one, Proof.AesGcm.rounds, CtxMode.prepared, CtxMode.preparedN,
    VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowersRepr, Spec.Gcm.PreparedPowers16Repr] at *
  all_goals first
    | with_reducible assumption
    | omega

theorem openSpecR16_pre {s : State} (h : openPreK CtxMode.prepared16 s) :
    (Proof.AesGcm.openPrepared16RoundsContract X86_64.abi 2632).pre s := by
  sig_split h
  rename_i a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a₁₇ a₁₈ a₁₉ a₂₀ a₂₁ a₂₂ a₂₃ a₂₄ a₂₅ a₂₆ a₂₇
  have a₂₈ := h
  clear h
  sig_pre [Proof.AesGcm.openPrepared16RoundsContract, Spec.Gcm.openPrecomputedSig, Spec.Gcm.openPrecomputedSig,
    Proof.Gcm.openPrepared16Pre, X86_64.abi, X86_64.argRegs]
  sig_reduce [Proof.AesGcm.openPrepared16RoundsContract, Spec.Gcm.openPrecomputedSig, Spec.Gcm.openPrecomputedSig,
    Proof.Gcm.openPrepared16Pre, X86_64.abi, X86_64.argRegs, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret,
    X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below]
  sig_and_intros
  all_goals simp only [Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, X86_64.stackArg,
    X86_64.stackArgAddr, VG.X86_64.below, Nat.mul_one, Proof.AesGcm.rounds, CtxMode.prepared16, CtxMode.preparedN,
    VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr] at *
  all_goals first
    | with_reducible assumption
    | omega

theorem openSpec_post {s s' : State} (hR : rounds s)
    (h : (Proof.AesGcm.openRoundsContract X86_64.abi 2632).post s s') :
    Proof.AesGcm.openX86_64.post s s' := by
  sig_post [Proof.AesGcm.openRoundsContract, Spec.Gcm.openSig, Spec.Gcm.openPre, X86_64.abi, X86_64.argRegs,
    Proof.AesGcm.openRoundsPost] at h
  sig_reduce [Proof.AesGcm.openRoundsContract, Spec.Gcm.openSig, X86_64.abi, X86_64.argRegs, X86_64.stackArg,
    X86_64.stackArgAddr, List.range, List.range.loop] at h
  exact h hR

theorem openSpecR_post {s s' : State} (hR : rounds s)
    (h : (Proof.AesGcm.openPreparedRoundsContract X86_64.abi 2632).post s s') :
    Proof.AesGcm.openX86_64.post s s' := by
  sig_post [Proof.AesGcm.openPreparedRoundsContract, Spec.Gcm.openPrecomputedSig, Spec.Gcm.openPrecomputedSig,
    Proof.Gcm.openPowersPre, X86_64.abi, X86_64.argRegs, Proof.AesGcm.openRoundsPost] at h
  sig_reduce [Proof.AesGcm.openPreparedRoundsContract, Spec.Gcm.openPrecomputedSig, Spec.Gcm.openPrecomputedSig,
    X86_64.abi, X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop] at h
  exact h hR

theorem openSpecR16_post {s s' : State} (hR : rounds s)
    (h : (Proof.AesGcm.openPrepared16RoundsContract X86_64.abi 2632).post s s') :
    Proof.AesGcm.openX86_64.post s s' := by
  sig_post [Proof.AesGcm.openPrepared16RoundsContract, Spec.Gcm.openPrecomputedSig, Spec.Gcm.openPrecomputedSig,
    Proof.Gcm.openPrepared16Pre, X86_64.abi, X86_64.argRegs, Proof.AesGcm.openRoundsPost] at h
  sig_reduce [Proof.AesGcm.openPrepared16RoundsContract, Spec.Gcm.openPrecomputedSig, Spec.Gcm.openPrecomputedSig,
    X86_64.abi, X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop] at h
  exact h hR

theorem openSpec_pub {s₁ s₂ : State} (h : openPubK s₁ s₂) :
    (Proof.AesGcm.openRoundsContract X86_64.abi 2632).pub s₁ s₂ := by
  obtain ⟨⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈⟩, a₉⟩ := h
  have b₀ := a₈ 0 (by decide)
  have b₁ := a₈ 1 (by decide)
  have b₂ := a₈ 2 (by decide)
  have b₃ := a₈ 3 (by decide)
  sig_pub [Proof.AesGcm.openRoundsContract, Spec.Gcm.openSig, Spec.Gcm.openLeak, X86_64.abi, X86_64.argRegs]
  sig_reduce [Proof.AesGcm.openRoundsContract, Spec.Gcm.openSig, Spec.Gcm.openLeak, X86_64.abi, X86_64.argRegs,
    X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop, Proof.AesGcm.arg]
  simp only [Proof.AesGcm.arg, Proof.AesGcm.openLeak, Proof.AesGcm.rounds, X86_64.stackArg,
    X86_64.stackArgAddr] at b₀ b₁ b₂ b₃ a₉
  sig_and_intros
  all_goals first | with_reducible assumption | trivial | (intro r hr; simp at hr)

theorem openSpecR_pub {s₁ s₂ : State} (h : openPubK s₁ s₂) :
    (Proof.AesGcm.openPreparedRoundsContract X86_64.abi 2632).pub s₁ s₂ := by
  obtain ⟨⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈⟩, a₉⟩ := h
  have b₀ := a₈ 0 (by decide)
  have b₁ := a₈ 1 (by decide)
  have b₂ := a₈ 2 (by decide)
  have b₃ := a₈ 3 (by decide)
  sig_pub [Proof.AesGcm.openPreparedRoundsContract, Spec.Gcm.openPrecomputedSig, Spec.Gcm.openPrecomputedSig,
    Spec.Gcm.openLeak, X86_64.abi, X86_64.argRegs]
  sig_reduce [Proof.AesGcm.openPreparedRoundsContract, Spec.Gcm.openPrecomputedSig, Spec.Gcm.openPrecomputedSig,
    Spec.Gcm.openLeak, X86_64.abi, X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range,
    List.range.loop, Proof.AesGcm.arg]
  simp only [Proof.AesGcm.arg, Proof.AesGcm.openLeak, Proof.AesGcm.rounds, X86_64.stackArg,
    X86_64.stackArgAddr] at b₀ b₁ b₂ b₃ a₉
  sig_and_intros
  all_goals first | with_reducible assumption | trivial | (intro r hr; simp at hr)

theorem openSpecR16_pub {s₁ s₂ : State} (h : openPubK s₁ s₂) :
    (Proof.AesGcm.openPrepared16RoundsContract X86_64.abi 2632).pub s₁ s₂ := by
  obtain ⟨⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈⟩, a₉⟩ := h
  have b₀ := a₈ 0 (by decide)
  have b₁ := a₈ 1 (by decide)
  have b₂ := a₈ 2 (by decide)
  have b₃ := a₈ 3 (by decide)
  sig_pub [Proof.AesGcm.openPrepared16RoundsContract, Spec.Gcm.openPrecomputedSig, Spec.Gcm.openPrecomputedSig,
    Spec.Gcm.openLeak, X86_64.abi, X86_64.argRegs]
  sig_reduce [Proof.AesGcm.openPrepared16RoundsContract, Spec.Gcm.openPrecomputedSig, Spec.Gcm.openPrecomputedSig,
    Spec.Gcm.openLeak, X86_64.abi, X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range,
    List.range.loop, Proof.AesGcm.arg]
  simp only [Proof.AesGcm.arg, Proof.AesGcm.openLeak, Proof.AesGcm.rounds, X86_64.stackArg,
    X86_64.stackArgAddr] at b₀ b₁ b₂ b₃ a₉
  sig_and_intros
  all_goals first | with_reducible assumption | trivial | (intro r hr; simp at hr)

/-! ## Its instances -/

/-- An instance of `vg_aes_gcm_open` for a key context of kind `M`, by
`openK`, using at most 2632 bytes of stack. -/
abbrev OpenFn (M : CtxMode) := CallFn (openK M) 2632

/-- `vg_aes_gcm_open` from its contract on the key context. -/
def OpenFn.ofBase (f : Fn) (hv : Verified X86_64.target f.code (Proof.AesGcm.openRoundsContract X86_64.abi 2632))
    (sp : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (xd : f.code.x86_64Depth ≤ 2632)
    (mx : f.code.allInstrs (fun i => !loadsMxcsr i) = true) : OpenFn CtxMode.base :=
  CallFn.ofSpec f hv (fun _ h => openSpec_pre h)
    (fun _ _ h h' => openSpec_post h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h')
    (fun _ _ h => openSpec_pub h) sp xd mx

/-- `vg_aes_gcm_open_prepared` from its contract on the key context. -/
def OpenFn.ofPrepared (f : Fn)
    (hv : Verified X86_64.target f.code (Proof.AesGcm.openPreparedRoundsContract X86_64.abi 2632))
    (sp : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (xd : f.code.x86_64Depth ≤ 2632)
    (mx : f.code.allInstrs (fun i => !loadsMxcsr i) = true) : OpenFn CtxMode.prepared :=
  CallFn.ofSpec f hv (fun _ h => openSpecR_pre h)
    (fun _ _ h h' => openSpecR_post h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h')
    (fun _ _ h => openSpecR_pub h) sp xd mx

/-- `vg_aes_gcm_open_prepared16` from its contract on the key context. -/
def OpenFn.ofPrepared16 (f : Fn)
    (hv : Verified X86_64.target f.code (Proof.AesGcm.openPrepared16RoundsContract X86_64.abi 2632))
    (sp : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (xd : f.code.x86_64Depth ≤ 2632)
    (mx : f.code.allInstrs (fun i => !loadsMxcsr i) = true) : OpenFn CtxMode.prepared16 :=
  CallFn.ofSpec f hv (fun _ h => openSpecR16_pre h)
    (fun _ _ h h' => openSpecR16_post h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h')
    (fun _ _ h => openSpecR16_pub h) sp xd mx

theorem openSpecF_pre {t : Nat} {s : State} (h : openPreK (CtxMode.flaggedT t) s) :
    (Proof.AesGcm.Flag.openRoundsContractB t X86_64.abi 2632).pre s := by
  sig_split h
  sig_pre [Proof.AesGcm.Flag.openRoundsContractB, Spec.Gcm.openPreparedSig, Spec.Gcm.openPreparedSig,
    Spec.Gcm.openPreparedPre, X86_64.abi, X86_64.argRegs]
  sig_reduce [Proof.AesGcm.Flag.openRoundsContractB, Spec.Gcm.openPreparedSig, Spec.Gcm.openPreparedSig,
    Spec.Gcm.openPreparedPre, X86_64.abi, X86_64.argRegs, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret,
    X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below]
  sig_and_intros
  all_goals simp only [Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, X86_64.stackArg,
    X86_64.stackArgAddr, VG.X86_64.below, Nat.mul_one, Proof.AesGcm.rounds, CtxMode.flaggedT, Spec.Gcm.PreparedRepr,
    Spec.Gcm.powerCount, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowersRepr,
    Spec.Gcm.PreparedPowers16Repr] at *
  all_goals first
    | with_reducible assumption
    | omega
    | exact ⟨by assumption, by assumption⟩
theorem openSpecF_post {t : Nat} {s s' : State} (hR : rounds s)
    (h : (Proof.AesGcm.Flag.openRoundsContractB t X86_64.abi 2632).post s s') :
    Proof.AesGcm.openX86_64.post s s' := by
  sig_post [Proof.AesGcm.Flag.openRoundsContractB, Spec.Gcm.openPreparedSig, Spec.Gcm.openPreparedSig,
    Spec.Gcm.openPreparedPre, X86_64.abi, X86_64.argRegs, Proof.AesGcm.openRoundsPost] at h
  sig_reduce [Proof.AesGcm.Flag.openRoundsContractB, Spec.Gcm.openPreparedSig, Spec.Gcm.openPreparedSig,
    X86_64.abi, X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop] at h
  exact h hR
theorem openSpecF_pub {t : Nat} {s₁ s₂ : State} (h : openPubK s₁ s₂)
    (o₁ : (CtxMode.flaggedT t).ok s₁.mem (s₁.gpr .rdi)) (o₂ : (CtxMode.flaggedT t).ok s₂.mem (s₂.gpr .rdi)) :
    (Proof.AesGcm.Flag.openRoundsContractB t X86_64.abi 2632).pub s₁ s₂ := by
  have f₁ : Proof.AesGcm.Flag.flagBit t s₁.mem (s₁.gpr .rdi) = 1 := Proof.AesGcm.Flag.flagBit_of_le o₁.1
  have f₂ : Proof.AesGcm.Flag.flagBit t s₂.mem (s₂.gpr .rdi) = 1 := Proof.AesGcm.Flag.flagBit_of_le o₂.1
  obtain ⟨⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈⟩, a₉⟩ := h
  have b₀ := a₈ 0 (by decide)
  have b₁ := a₈ 1 (by decide)
  have b₂ := a₈ 2 (by decide)
  have b₃ := a₈ 3 (by decide)
  sig_pub [Proof.AesGcm.Flag.openRoundsContractB, Spec.Gcm.openPreparedSig, Spec.Gcm.openPreparedSig,
    Proof.AesGcm.Flag.openLeakB, Spec.Gcm.openLeak, X86_64.abi, X86_64.argRegs]
  sig_reduce [Proof.AesGcm.Flag.openRoundsContractB, Spec.Gcm.openPreparedSig, Spec.Gcm.openPreparedSig,
    Proof.AesGcm.Flag.openLeakB, Spec.Gcm.openLeak, X86_64.abi, X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr,
    List.range, List.range.loop, Proof.AesGcm.arg]
  simp only [Proof.AesGcm.arg, Proof.AesGcm.openLeak, Proof.AesGcm.rounds, X86_64.stackArg,
    X86_64.stackArgAddr] at b₀ b₁ b₂ b₃ a₉
  sig_and_intros
  all_goals try simp only [f₁, f₂]
  all_goals first | with_reducible assumption | trivial | exact congrArg (List.cons 1) a₉ |
    (intro r hr; simp at hr)

/-- `vg_aes_gcm_open_prepared` of an implementation reading `t` powers, from
its contract leaking only whether the count is at least `t`, for one whose
count is: what it leaks of the count is the same, 1, in every call. -/
def OpenFn.ofFlagged {t : Nat} (f : Fn)
    (hv : Verified X86_64.target f.code (Proof.AesGcm.Flag.openRoundsContractB t X86_64.abi 2632))
    (sp : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (xd : f.code.x86_64Depth ≤ 2632)
    (mx : f.code.allInstrs (fun i => !loadsMxcsr i) = true) : OpenFn (CtxMode.flaggedT t) where
  fn := f
  ok s h := by
    obtain ⟨t, s', he, ha, hp⟩ := hv.1 s (openSpecF_pre h)
    exact ⟨t, s', he, ha, openSpecF_post h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hp⟩
  ct s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂ :=
    hv.2.1 s₁ s₂ t₁ t₂ s₁' s₂' (openSpecF_pre h₁) (openSpecF_pre h₂)
      (openSpecF_pub hq h₁.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
        h₂.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2) e₁ e₂
  sp := SpSafe.of_all sp
  xd := xd
  mx := mx
  spAll := sp

/-! ## The contract -/

section
variable (s : State)

/-- The arguments: `(ctx = rdi, rounds = rsi, nonce = rdx, nonce_len = rcx,
aad = r8, aad_len = r9, src = [rsp + 8], len = [rsp + 16], dst = [rsp + 24],
dst_len = [rsp + 32], tag = [rsp + 40], tag_len = [rsp + 48])`. -/
abbrev K : Addr := s.gpr .rdi
abbrev R : Nat := (s.gpr .rsi).toNat
abbrev Nn : Addr := s.gpr .rdx
abbrev NL : Nat := (s.gpr .rcx).toNat
abbrev Ad : Addr := s.gpr .r8
abbrev AL : Nat := (s.gpr .r9).toNat
abbrev Src : Addr := arg s 0
abbrev L : Nat := (arg s 1).toNat
abbrev Dst : Addr := arg s 2
abbrev Tg : Addr := arg s 4
abbrev TL : Nat := (arg s 5).toNat

/-- The regions: the nonce, the additional data, the input, the output, the
received tag, the stack arguments, and the stack below the stack pointer. -/
abbrev nR : Region := ⟨Nn s, NL s⟩
abbrev aR : Region := ⟨Ad s, AL s⟩
abbrev sR : Region := ⟨Src s, L s⟩
abbrev dR : Region := ⟨Dst s, L s⟩
abbrev tR : Region := ⟨Tg s, TL s⟩
abbrev argR : Region := args s 6
abbrev stkR : Region := below (s.gpr .rsp) 2728

/-- What `vg_aes_gcm_open` computes on the arguments. -/
abbrev res : Option (List Byte) :=
  openResult (ctxCiph s.mem (K s) (R s)) (ctxH s.mem (K s)) (TL s) (bytesAt s.mem (Nn s) (NL s))
    (bytesAt s.mem (Src s) (L s)) (bytesAt s.mem (Ad s) (AL s)) (bytesAt s.mem (Tg s) (TL s))

end

/-- The key context. -/
abbrev kR (M : CtxMode) (s : State) : Region := ⟨K s, M.len⟩

/-- What `vg_aes_gcm_open_to` needs, for a key context of kind `M`. -/
structure ToPre (M : CtxMode) (s : State) : Prop where
  rd : s.rd = [kR M s, nR s, aR s, sR s, tR s, argR s]
  wr : s.wr = [dR s]
  kd : (kR M s).Disjoint (dR s)
  nd : (nR s).Disjoint (dR s)
  ad : (aR s).Disjoint (dR s)
  sd : (sR s).Disjoint (dR s)
  dt : (dR s).Disjoint (tR s)
  da : (dR s).Disjoint (argR s)
  rk : (ret s).Disjoint (kR M s)
  rn : (ret s).Disjoint (nR s)
  ra : (ret s).Disjoint (aR s)
  rs : (ret s).Disjoint (sR s)
  rdd : (ret s).Disjoint (dR s)
  rt : (ret s).Disjoint (tR s)
  rarg : (ret s).Disjoint (argR s)
  bk : (stkR s).Disjoint (kR M s)
  bn : (stkR s).Disjoint (nR s)
  ba : (stkR s).Disjoint (aR s)
  bs : (stkR s).Disjoint (sR s)
  bd : (stkR s).Disjoint (dR s)
  bt : (stkR s).Disjoint (tR s)
  barg : (stkR s).Disjoint (argR s)
  wk : (K s).toNat + M.len ≤ 2 ^ 64
  wn : (Nn s).toNat + NL s ≤ 2 ^ 64
  wa : (Ad s).toNat + AL s ≤ 2 ^ 64
  ws : (Src s).toNat + L s ≤ 2 ^ 64
  wd : (Dst s).toNat + L s ≤ 2 ^ 64
  wt : (Tg s).toNat + TL s ≤ 2 ^ 64
  w₁ : 2728 ≤ (s.gpr .rsp).toNat
  w₂ : (s.gpr .rsp).toNat + 56 ≤ 2 ^ 64
  rounds : rounds s
  dl : (arg s 3).toNat = L s
  ok : M.ok s.mem (K s)

/-- What `vg_aes_gcm_open_to` leaves: if the tag is right, the result 1 and
the plaintext at `dst`; otherwise the result 0 and zeros at `dst`. -/
def toPost (s s' : State) : Prop :=
  match res s with
  | some pt => (s'.gpr .rax).setWidth 32 = 1 ∧ bytesAt s'.mem (Dst s) (L s) = pt
  | none => (s'.gpr .rax).setWidth 32 = 0 ∧ bytesAt s'.mem (Dst s) (L s) = List.replicate (L s) 0

/-- What `vg_aes_gcm_open_to` may leak (`Spec.Gcm.openToLeak`): whether it
succeeds. -/
def toLeak (s : State) : List Nat := if ¬rounds s then [] else [if (res s).isSome then 1 else 0]

/-- What two runs agree on: the arguments, and whether the tag is right. -/
def toPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ (∀ i < 6, arg s₁ i = arg s₂ i) ∧ toLeak s₁ = toLeak s₂

/-- `vg_aes_gcm_open_to`, for a key context of kind `M`. -/
def toK (M : CtxMode) : Contract isa where
  pre := ToPre M
  post := toPost
  pub := toPub

/-! ## The layout -/

/-- Two disjoint regions, within the address space and not empty, are
apart. -/
theorem apart_of_disjoint {r₁ r₂ : Region} (h : r₁.Disjoint r₂) (h₁ : 0 < r₁.len) (h₂ : 0 < r₂.len) :
    r₁.base.toNat + r₁.len ≤ r₂.base.toNat ∨ r₂.base.toNat + r₂.len ≤ r₁.base.toNat := by
  rcases Nat.lt_or_ge (r₁.base.toNat + r₁.len) (r₂.base.toNat + 1) with c | c
  · exact .inl (by omega)
  rcases Nat.lt_or_ge (r₂.base.toNat + r₂.len) (r₁.base.toNat + 1) with d | d
  · exact .inr (by omega)
  exfalso
  rcases Nat.le_total r₁.base.toNat r₂.base.toNat with e | e
  · refine h r₂.base ?_ ?_
    · simp only [Region.Contains]
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact e)]; omega
    · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  · refine h r₁.base ?_ ?_
    · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
    · simp only [Region.Contains]
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact e)]; omega

section
variable (s : State)

/-- The base of the 2728 bytes of stack below the stack pointer. -/
abbrev Bs : Addr := s.gpr .rsp - BitVec.ofNat 64 2728

/-- Our frame, and the stack pointer in it. -/
abbrev P : Addr := Bs s + BitVec.ofNat 64 2640
abbrev FR : Region := ⟨P s, 88⟩

end

/-- What `ToPre` gives, with the stack below the stack pointer at `Bs s`. -/
structure Lay (M : CtxMode) (s : State) : Prop where
  pre : ToPre M s
  hB : s.gpr .rsp = Bs s + BitVec.ofNat 64 2728
  hBv : (Bs s).toNat = (s.gpr .rsp).toNat - 2728
  lt : L s < 2 ^ 63

theorem lay {M : CtxMode} {s : State} (hs : ToPre M s) : Lay M s := by
  have hBv : (Bs s).toNat = (s.gpr .rsp).toNat - 2728 := toNat_sub_ofNat hs.w₁
  refine ⟨hs, (BitVec.sub_add_cancel _ _).symm, hBv, ?_⟩
  rcases Nat.eq_zero_or_pos (L s) with h0 | hpos
  · rw [h0]; decide
  have a₁ := apart_of_disjoint hs.sd hpos hpos
  have a₂ := apart_of_disjoint hs.rs (show 0 < 8 by decide) hpos
  have a₃ := apart_of_disjoint hs.rdd (show 0 < 8 by decide) hpos
  have := hs.ws; have := hs.wd; have := hs.w₂
  simp only [ret, sR, dR] at a₁ a₂ a₃
  omega

/-- A region apart from `dst` and the stack, which nothing writes. -/
structure Kept (s : State) (r : Region) : Prop where
  d : r.Disjoint (dR s)
  k : r.Disjoint (stkR s)
  b : r.base.toNat + r.len ≤ 2 ^ 64

theorem Kept.all {s : State} {r : Region} (hk : Kept s r) : ∀ r' ∈ [dR s, stkR s], r.Disjoint r' := by
  intro r' hr'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl
  · exact hk.d
  · exact hk.k

/-- The memory outside `dst` and the stack, through a frame of them. -/
theorem Kept.bytes {s : State} {m : Mem} (hf : Frame [dR s, stkR s] s.mem m) {r : Region} (hk : Kept s r) :
    bytesAt m r.base r.len = bytesAt s.mem r.base r.len :=
  Proof.AesGcm.X86_64.bytesAt_frame hf hk.all (by have := hk.b; omega)

theorem Kept.readW {s : State} {m : Mem} (hf : Frame [dR s, stkR s] s.mem m) {r : Region} (hk : Kept s r)
    {a : Addr} (ha : r.Contains a 8) : m.readW a 64 = s.mem.readW a 64 :=
  hf.readW ha hk.all (by decide)

/-- Parts of the stack below the stack pointer. -/
theorem stk_sub (s : State) (d n : Nat) (h' : d + n ≤ 2728) :
    (⟨Bs s + BitVec.ofNat 64 d, n⟩ : Region).Sub (stkR s) :=
  Offset.sub_base _ h'

theorem fr_sub (s : State) : (FR s).Sub (stkR s) := stk_sub s 2640 88 (by decide)

namespace Lay

variable {M : CtxMode} {s : State} (h : Lay M s)
include h

theorem hBn : (Bs s).toNat + 2784 ≤ 2 ^ 64 := by have := h.pre.w₂; have := h.hBv; omega

/-- The stack arguments. -/
theorem argAddr (i : Nat) : stackArgAddr s i = Bs s + BitVec.ofNat 64 (2736 + 8 * i) := by
  show s.gpr .rsp + BitVec.ofNat 64 (8 * (i + 1)) = _
  rw [h.hB, Offset.add_ofNat_add_ofNat]; congr 2; omega

theorem hargR : argR s = ⟨Bs s + BitVec.ofNat 64 2736, 48⟩ := by
  show (⟨stackArgAddr s 0, 8 * 6⟩ : Region) = _
  rw [h.argAddr]

theorem k_kept : Kept s (kR M s) := ⟨h.pre.kd, h.pre.bk.symm, h.pre.wk⟩
theorem n_kept : Kept s (nR s) := ⟨h.pre.nd, h.pre.bn.symm, h.pre.wn⟩
theorem a_kept : Kept s (aR s) := ⟨h.pre.ad, h.pre.ba.symm, h.pre.wa⟩
theorem s_kept : Kept s (sR s) := ⟨h.pre.sd, h.pre.bs.symm, h.pre.ws⟩
theorem t_kept : Kept s (tR s) := ⟨h.pre.dt.symm, h.pre.bt.symm, h.pre.wt⟩
theorem arg_kept : Kept s (argR s) := by
  refine ⟨h.pre.da.symm, h.pre.barg.symm, ?_⟩
  rw [h.hargR]; have := h.hBn
  show (Bs s + BitVec.ofNat 64 2736).toNat + 48 ≤ 2 ^ 64
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2736) (by decide), Nat.mod_eq_of_lt (by omega)]
  omega
theorem ret_kept : Kept s (ret s) :=
  ⟨h.pre.rdd, Offset.base_disjoint_below _ (by have := h.pre.w₁; omega), by have := h.pre.w₂; simp only [ret]; omega⟩

/-- The stack arguments, through a frame of `dst` and the stack. -/
theorem argW {m : Mem} (hf : Frame [dR s, stkR s] s.mem m) (i : Nat) (hi : i < 6) :
    m.readW (Bs s + BitVec.ofNat 64 (2736 + 8 * i)) 64 = arg s i := by
  have hBn := h.hBn
  rw [h.arg_kept.readW hf (by rw [h.hargR]; exact Offset.contains _ (by omega) (by omega) (by omega)),
    ← h.argAddr]
  rfl

/-- The return address, through a frame of `dst` and the stack. -/
theorem retW {m : Mem} (hf : Frame [dR s, stkR s] s.mem m) : m.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 :=
  h.ret_kept.readW hf (Region.contains_self _ _)

/-- The key context's cipher and hash subkey, through a frame of `dst` and
the stack. -/
theorem ciph_eq {m : Mem} (hf : Frame [dR s, stkR s] s.mem m) : ctxCiph m (K s) (R s) = ctxCiph s.mem (K s) (R s) := by
  have hRb : 16 * (R s + 1) ≤ 256 := by
    rcases h.pre.rounds with e | e | e <;>
      simp only [R, e] <;> decide
  have hk := h.k_kept
  simp only [ctxCiph]
  rw [Proof.AesGcm.X86_64.bytesAt_frame hf (fun r hr => (hk.all r hr).sub_left (Region.sub_prefix (Nat.le_trans hRb M.ge)))
    (by have := hk.b; have := M.ge; omega)]

theorem hk_eq {m : Mem} (hf : Frame [dR s, stkR s] s.mem m) : ctxH m (K s) = ctxH s.mem (K s) := by
  have hk := h.k_kept
  simp only [ctxH]
  exact Proof.AesGcm.X86_64.blockAt_frame hf fun r hr => (hk.all r hr).sub_left (Offset.sub_base _ (by have := M.ge; omega))

end Lay

/-! ## The blocks -/

/-- `entry`: `src`, `dst` and `len` from our stack arguments. -/
theorem entry_ok (a : State) {Q : Addr} (hsp : a.gpr .rsp = Q)
    (r₉₆ : InRegions (a.rd ++ a.wr) (Q + BitVec.ofNat 64 96) 8)
    (r₁₀₄ : InRegions (a.rd ++ a.wr) (Q + BitVec.ofNat 64 104) 8)
    (r₁₁₂ : InRegions (a.rd ++ a.wr) (Q + BitVec.ofNat 64 112) 8) :
    WP isa (.block entry) a fun e => e.gpr .rsi = a.mem.readW (Q + BitVec.ofNat 64 96) 64 ∧
      e.gpr .rdi = a.mem.readW (Q + BitVec.ofNat 64 112) 64 ∧
      e.gpr .rcx = a.mem.readW (Q + BitVec.ofNat 64 104) 64 ∧
      (∀ r, r ≠ .rsi → r ≠ .rdi → r ≠ .rcx → e.gpr r = a.gpr r) ∧ e.mem = a.mem ∧ e.rd = a.rd ∧
      e.wr = a.wr := by
  apply WP.of_runBlock
  refine ⟨_, by xrun [entry, hsp, r₉₆, r₁₀₄, r₁₁₂], ?_⟩
  exact ⟨by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg],
    fun r h₁ h₂ h₃ => by simp [gpr_setReg, h₁, h₂, h₃], rfl, rfl, rfl⟩

/-- `callRegs`: the six argument registers from the frame. -/
theorem callRegs_ok (a : State) {Q : Addr} (hsp : a.gpr .rsp = Q)
    (r₄₀ : InRegions (a.rd ++ a.wr) (Q + BitVec.ofNat 64 40) 8)
    (r₄₈ : InRegions (a.rd ++ a.wr) (Q + BitVec.ofNat 64 48) 8)
    (r₅₆ : InRegions (a.rd ++ a.wr) (Q + BitVec.ofNat 64 56) 8)
    (r₆₄ : InRegions (a.rd ++ a.wr) (Q + BitVec.ofNat 64 64) 8)
    (r₇₂ : InRegions (a.rd ++ a.wr) (Q + BitVec.ofNat 64 72) 8)
    (r₈₀ : InRegions (a.rd ++ a.wr) (Q + BitVec.ofNat 64 80) 8) :
    WP isa (.block callRegs) a fun e => e.gpr .rdi = a.mem.readW (Q + BitVec.ofNat 64 80) 64 ∧
      e.gpr .rsi = a.mem.readW (Q + BitVec.ofNat 64 72) 64 ∧
      e.gpr .rdx = a.mem.readW (Q + BitVec.ofNat 64 64) 64 ∧
      e.gpr .rcx = a.mem.readW (Q + BitVec.ofNat 64 56) 64 ∧
      e.gpr .r8 = a.mem.readW (Q + BitVec.ofNat 64 48) 64 ∧
      e.gpr .r9 = a.mem.readW (Q + BitVec.ofNat 64 40) 64 ∧
      (∀ r ∈ calleeSaved, e.gpr r = a.gpr r) ∧ e.mem = a.mem ∧ e.rd = a.rd ∧ e.wr = a.wr := by
  apply WP.of_runBlock
  refine ⟨_, by xrun [callRegs, hsp, r₄₀, r₄₈, r₅₆, r₆₄, r₇₂, r₈₀], ?_⟩
  refine ⟨by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg],
    by simp [gpr_setReg], by simp [gpr_setReg], fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]

/-- `stArg d src`: the word at `rsp + src` stored at `rsp + d`. -/
theorem stArg_ok (a : State) {Q : Addr} (hsp : a.gpr .rsp = Q) (d src : Nat)
    (hr : InRegions (a.rd ++ a.wr) (Q + BitVec.ofNat 64 src) 8) (hw : InRegions a.wr (Q + BitVec.ofNat 64 d) 8) :
    WP isa (.block (stArg d src)) a fun e =>
      e.mem = a.mem.writeW (Q + BitVec.ofNat 64 d) (a.mem.readW (Q + BitVec.ofNat 64 src) 64) ∧
      (∀ r, r ≠ .rax → e.gpr r = a.gpr r) ∧ e.rd = a.rd ∧ e.wr = a.wr := by
  apply WP.of_runBlock
  refine ⟨_, by xrun [stArg, hsp, hr, hw], ?_⟩
  exact ⟨by simp [mem_setReg], fun r h₁ => by simp [gpr_setReg, h₁], rfl, rfl⟩

/-! ## The push -/

section
variable (s : State)

/-- The memory after the push of our frame. -/
abbrev eM : Mem := (pushed frameRegs s).mem

theorem hP : (pushed frameRegs s).gpr .rsp = P s := by
  rw [pushed_rsp, Offset.sub_ofNat_eq _ (show 8 * frameRegs.length ≤ 2728 by decide)]; rfl

theorem hPwr : (pushed frameRegs s).wr = FR s :: s.wr := by
  rw [pushed_wr, Offset.sub_ofNat_eq _ (show 8 * frameRegs.length ≤ 2728 by decide)]; rfl

end

namespace Lay

variable {M : CtxMode} {s : State} (h : Lay M s)
include h

theorem pushes : Frame [FR s] s.mem (eM s) ∧
    ∀ j (hj : j < frameRegs.length),
      (eM s).readW (s.gpr .rsp - BitVec.ofNat 64 (8 * (j + 1))) 64 = s.gpr frameRegs[j] := by
  have := pushRegs_mem s frameRegs (by decide) (by have := h.pre.w₁; simp only [List.length_cons, List.length_nil]; omega)
  rw [Offset.sub_ofNat_eq _ (show 8 * frameRegs.length ≤ 2728 by decide)] at this
  exact this

/-- The push writes only the stack. -/
theorem frame_eM : Frame [dR s, stkR s] s.mem (eM s) :=
  h.pushes.1.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨stkR s, by simp, fr_sub s⟩

/-- The words of our frame: the argument registers. -/
theorem pushedW (j : Nat) (hj : j < 11) (d : Nat) (hd : d + 8 * (j + 1) = 2728) :
    (eM s).readW (Bs s + BitVec.ofNat 64 d) 64 = s.gpr (frameRegs[j]'hj) := by
  have := h.pushes.2 j hj
  rw [Offset.sub_ofNat_eq _ (show 8 * (j + 1) ≤ 2728 by omega), show 2728 - 8 * (j + 1) = d by omega] at this
  exact this

end Lay

/-! ## The phases -/

/-- After the push and the entry. -/
structure Entered (s e : State) : Prop where
  mem : e.mem = eM s
  rsi : e.gpr .rsi = Src s
  rdi : e.gpr .rdi = Dst s
  rcx : e.gpr .rcx = arg s 1
  gpr : ∀ r, r ≠ .rsi → r ≠ .rdi → r ≠ .rcx → r ≠ .rsp → e.gpr r = s.gpr r
  rsp : e.gpr .rsp = P s
  rd : e.rd = s.rd
  wr : e.wr = FR s :: s.wr
  mx : e.mxcsr = s.mxcsr

/-- Our stack arguments are readable, from our frame's stack pointer. -/
theorem Lay.inArg {M : CtxMode} {s : State} (h : Lay M s) {rd wr : List Region} (hrd : rd = s.rd) (d : Nat)
    (h₁ : 96 ≤ d) (hd : d + 8 ≤ 144) : InRegions (rd ++ wr) (P s + BitVec.ofNat 64 d) 8 := by
  have hBn := h.hBn
  rw [hrd, Offset.add_ofNat_add_ofNat]
  refine ⟨argR s, List.mem_append_left _ (by rw [h.pre.rd]; simp), ?_⟩
  rw [h.hargR]; exact Offset.contains _ (by omega) (by omega) (by omega)

/-- Our stack argument at `P + d`, through a frame of `dst` and the stack. -/
theorem Lay.argAt {M : CtxMode} {s : State} (h : Lay M s) {m : Mem} (hf : Frame [dR s, stkR s] s.mem m) (i : Nat)
    (hi : i < 6) : m.readW (P s + BitVec.ofNat 64 (96 + 8 * i)) 64 = arg s i := by
  rw [Offset.add_ofNat_add_ofNat, show 2640 + (96 + 8 * i) = 2736 + 8 * i by omega]
  exact h.argW hf i hi

theorem entered_wp {M : CtxMode} {s : State} (h : Lay M s) :
    WP isa (.block entry) (pushed frameRegs s) (Entered s) := by
  have ia (d : Nat) (h₁ : 96 ≤ d) (hd : d + 8 ≤ 144) :=
    h.inArg (rd := (pushed frameRegs s).rd) (wr := (pushed frameRegs s).wr) (pushed_rd _ _) d h₁ hd
  refine WP.mono_mx (by decide +kernel) (entry_ok (pushed frameRegs s) (hP s) (ia 96 (by decide) (by decide))
    (ia 104 (by decide) (by decide)) (ia 112 (by decide) (by decide)))
    fun e ⟨rsie, rdie, rcxe, ge, me, rde, wre⟩ mxe => ?_
  have a₀ := h.argAt h.frame_eM 0 (by decide)
  have a₁ := h.argAt h.frame_eM 1 (by decide)
  have a₂ := h.argAt h.frame_eM 2 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at a₀ a₁ a₂
  exact ⟨me, rsie.trans a₀, rdie.trans a₂, rcxe.trans a₁,
    fun r h₁ h₂ h₃ h₄ => by rw [ge r h₁ h₂ h₃, pushed_gpr _ _ h₄], by rw [ge _ (by decide) (by decide) (by decide), hP],
    by rw [rde, pushed_rd], by rw [wre, hPwr], by rw [mxe, pushed_mxcsr]⟩

/-- The memory once the ciphertext is copied to `dst`. -/
abbrev cM (s : State) : Mem := writeBytes (eM s) (Dst s) (bytesAt s.mem (Src s) (L s))

/-- After the copy. -/
structure Copied (s c : State) : Prop where
  mem : c.mem = cM s
  gpr : ∀ r, r ≠ .rsi → r ≠ .rdi → r ≠ .rcx → r ≠ .rax → r ≠ .r8 → r ≠ .r10 → r ≠ .rsp → c.gpr r = s.gpr r
  rsp : c.gpr .rsp = P s
  rd : c.rd = s.rd
  wr : c.wr = FR s :: s.wr
  mx : c.mxcsr = s.mxcsr

theorem covers_of_mem {r : Region} {ts : List Region} (h : r ∈ ts) : Covers [r] ts := by
  intro a n ⟨x, hx, hc⟩
  simp only [List.mem_singleton] at hx; subst hx; exact ⟨x, h, hc⟩

theorem copied_wp (w : Width) {M : CtxMode} {s e : State} (h : Lay M s) (he : Entered s e) :
    WP isa (Impl.ChaCha20Poly1305.X86_64.SealGather.copyBytes w) e (Copied s) := by
  have hcp : Proof.AesGcm.X86_64.Short.CopyPre e (Src s) (Dst s) (L s) :=
    { rsi := he.rsi
      rdi := he.rdi
      rcx := by rw [he.rcx, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      lt := h.lt
      rd := covers_of_mem (List.mem_append_left _ (by rw [he.rd, h.pre.rd]; simp))
      wr := covers_of_mem (by rw [he.wr, h.pre.wr]; simp)
      disj := h.pre.sd }
  refine WP.mono_mx (by cases w <;> decide +kernel) (Proof.ChaCha20Poly1305.X86_64.Gather.copyBytes_ok hcp w)
    fun c ⟨mc, gc, rdc, wrc⟩ mxc => ?_
  have hs : bytesAt e.mem (Src s) (L s) = bytesAt s.mem (Src s) (L s) := by
    rw [he.mem]; exact h.s_kept.bytes h.frame_eM
  refine ⟨by rw [mc, hs, he.mem], fun r h₁ h₂ h₃ h₄ h₅ h₆ h₇ => by rw [gc r h₄ h₅ h₆, he.gpr r h₁ h₂ h₃ h₇],
    by rw [gc _ (by decide) (by decide) (by decide), he.rsp], rdc.trans he.rd, wrc.trans he.wr, mxc.trans he.mx⟩

namespace Lay

variable {M : CtxMode} {s : State} (h : Lay M s)
include h

/-- The copy writes only `dst`. -/
theorem frame_cM : Frame [dR s, stkR s] s.mem (cM s) := by
  refine h.frame_eM.trans ((writeBytes_frame (R := dR s) _ _ _ ?_).mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp)
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, Proof.AesGcm.X86_64.length_bytesAt,
    Nat.le_refl]

/-- A word of our frame, once the ciphertext is copied. -/
theorem cFrame (d : Nat) (hd : d + 8 ≤ 2728) :
    (cM s).readW (Bs s + BitVec.ofNat 64 d) 64 = (eM s).readW (Bs s + BitVec.ofNat 64 d) 64 := by
  refine Frame.readW (writeBytes_frame (R := dR s) _ _ _ ?_) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, Proof.AesGcm.X86_64.length_bytesAt,
      Nat.le_refl]
  · simp only [List.mem_singleton] at hr; subst hr
    exact h.pre.bd.sub_left (stk_sub s d 8 hd)

end Lay

/-! ## The call's arguments -/

section
variable (s : State)

/-- The memory once the call's stack arguments are stored in our frame. -/
abbrev rM : Mem :=
  ((((cM s).writeW (P s + BitVec.ofNat 64 0) (Dst s)).writeW (P s + BitVec.ofNat 64 8) (arg s 1)).writeW
    (P s + BitVec.ofNat 64 16) (Tg s)).writeW (P s + BitVec.ofNat 64 24) (arg s 5)

end

/-- Ready for the call. -/
structure Ready (s c : State) : Prop where
  mem : c.mem = rM s
  rdi : c.gpr .rdi = K s
  rsi : c.gpr .rsi = s.gpr .rsi
  rdx : c.gpr .rdx = Nn s
  rcx : c.gpr .rcx = s.gpr .rcx
  r8 : c.gpr .r8 = Ad s
  r9 : c.gpr .r9 = s.gpr .r9
  cs : ∀ r ∈ calleeSaved, r ≠ .rsp → c.gpr r = s.gpr r
  rsp : c.gpr .rsp = P s
  rd : c.rd = s.rd
  wr : c.wr = FR s :: s.wr
  mx : c.mxcsr = s.mxcsr

namespace Lay

variable {M : CtxMode} {s : State} (h : Lay M s)
include h

/-- A word of our frame is writable. -/
theorem inFr {wr : List Region} (hwr : wr = FR s :: s.wr) (d : Nat) (hd : d + 8 ≤ 88) :
    InRegions wr (P s + BitVec.ofNat 64 d) 8 := by
  have hBn := h.hBn
  rw [hwr]
  refine ⟨FR s, List.mem_cons_self .., ?_⟩
  simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]; omega

theorem inFr' {rd wr : List Region} (hwr : wr = FR s :: s.wr) (d : Nat) (hd : d + 8 ≤ 88) :
    InRegions (rd ++ wr) (P s + BitVec.ofNat 64 d) 8 :=
  let ⟨r, hr, hc⟩ := h.inFr hwr d hd; ⟨r, List.mem_append_right _ hr, hc⟩

omit h in
/-- A write of a word of our frame keeps the frame of `dst` and the stack. -/
theorem frame_wFr {m : Mem} (hf : Frame [dR s, stkR s] s.mem m) (d : Nat) (hd : d + 8 ≤ 88) (v : BitVec 64) :
    Frame [dR s, stkR s] s.mem (m.writeW (P s + BitVec.ofNat 64 d) v) := by
  refine hf.writeW (r := stkR s) (by simp) v ?_
  rw [Offset.add_ofNat_add_ofNat]
  exact Offset.contains_base _ (by omega) (by omega)

theorem frame_rM : Frame [dR s, stkR s] s.mem (rM s) :=
  frame_wFr (frame_wFr (frame_wFr (frame_wFr h.frame_cM 0 (by decide) (Dst s)) 8 (by decide) (arg s 1)) 16
    (by decide) (Tg s)) 24 (by decide) (arg s 5)

/-- A word of our frame, read through a write of another. -/
theorem rApart (m : Mem) (e k : Nat) (hek : e + 8 ≤ k ∨ k + 8 ≤ e) (he : e + 8 ≤ 88) (hk : k + 8 ≤ 88)
    (w : BitVec 64) :
    (m.writeW (P s + BitVec.ofNat 64 k) w).readW (P s + BitVec.ofNat 64 e) 64 =
      m.readW (P s + BitVec.ofNat 64 e) 64 := by
  have hBn := h.hBn
  refine Frame.readW ((Frame.refl _ _).writeW (List.mem_singleton_self ⟨P s + BitVec.ofNat 64 k, 8⟩) w
    (Region.contains_self _ _)) (r := ⟨P s + BitVec.ofNat 64 e, 8⟩) (Region.contains_self _ _) (fun r hr => ?_)
    (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  rw [Offset.add_ofNat_add_ofNat, Offset.add_ofNat_add_ofNat]
  exact Offset.disjoint _ (by omega) (by omega) (by omega)

theorem rArgs : (rM s).readW (P s + BitVec.ofNat 64 0) 64 = Dst s ∧ (rM s).readW (P s + BitVec.ofNat 64 8) 64 = arg s 1 ∧
    (rM s).readW (P s + BitVec.ofNat 64 16) 64 = Tg s ∧ (rM s).readW (P s + BitVec.ofNat 64 24) 64 = arg s 5 := by
  unfold rM
  refine ⟨?_, ?_, ?_, Mem.readW_writeW_self64 _ _ _⟩
  · rw [h.rApart _ 0 24 (by decide) (by decide) (by decide), h.rApart _ 0 16 (by decide) (by decide) (by decide),
      h.rApart _ 0 8 (by decide) (by decide) (by decide)]
    exact Mem.readW_writeW_self64 _ _ _
  · rw [h.rApart _ 8 24 (by decide) (by decide) (by decide), h.rApart _ 8 16 (by decide) (by decide) (by decide)]
    exact Mem.readW_writeW_self64 _ _ _
  · rw [h.rApart _ 16 24 (by decide) (by decide) (by decide)]
    exact Mem.readW_writeW_self64 _ _ _

end Lay

theorem ready_wp {M : CtxMode} {s c : State} (h : Lay M s) (hc : Copied s c) : WP isa callArgs c (Ready s) := by
  have hBn := h.hBn
  -- The frame's words, as pushed.
  have pw (j : Nat) (hj : j < 11) (d : Nat) (hd : d + 8 * (j + 1) = 88) :
      (cM s).readW (P s + BitVec.ofNat 64 d) 64 = s.gpr (frameRegs[j]'hj) := by
    rw [Offset.add_ofNat_add_ofNat, h.cFrame _ (by omega)]
    exact h.pushedW j hj _ (by omega)
  have ia {rd wr : List Region} (hrd : rd = s.rd) (d : Nat) (h₁ : 96 ≤ d) (hd : d + 8 ≤ 144) :=
    h.inArg (wr := wr) hrd d h₁ hd
  refine WP.seq (WP.mono_mx (by decide +kernel) (callRegs_ok c hc.rsp (h.inFr' hc.wr 40 (by decide))
    (h.inFr' hc.wr 48 (by decide)) (h.inFr' hc.wr 56 (by decide)) (h.inFr' hc.wr 64 (by decide))
    (h.inFr' hc.wr 72 (by decide)) (h.inFr' hc.wr 80 (by decide)))
    fun c₁ ⟨rdi₁, rsi₁, rdx₁, rcx₁, r8₁, r9₁, cs₁, m₁, rd₁, wr₁⟩ mx₁ => ?_)
  rw [hc.mem] at rdi₁ rsi₁ rdx₁ rcx₁ r8₁ r9₁
  rw [pw 0 (by decide) 80 rfl] at rdi₁
  rw [pw 1 (by decide) 72 rfl] at rsi₁
  rw [pw 2 (by decide) 64 rfl] at rdx₁
  rw [pw 3 (by decide) 56 rfl] at rcx₁
  rw [pw 4 (by decide) 48 rfl] at r8₁
  rw [pw 5 (by decide) 40 rfl] at r9₁
  have sp₁ : c₁.gpr .rsp = P s := (cs₁ _ (by decide)).trans hc.rsp
  -- The stack arguments.
  refine WP.seq (WP.mono_mx (by decide +kernel) (stArg_ok c₁ sp₁ 0 112 (ia (by rw [rd₁, hc.rd]) 112 (by decide) (by decide))
    (h.inFr (wr₁.trans hc.wr) 0 (by decide))) fun c₂ ⟨m₂, g₂, rd₂, wr₂⟩ mx₂ => ?_)
  have sp₂ : c₂.gpr .rsp = P s := (g₂ _ (by decide)).trans sp₁
  refine WP.seq (WP.mono_mx (by decide +kernel) (stArg_ok c₂ sp₂ 8 104 (ia (by rw [rd₂, rd₁, hc.rd]) 104 (by decide) (by decide))
    (h.inFr (wr₂.trans (wr₁.trans hc.wr)) 8 (by decide))) fun c₃ ⟨m₃, g₃, rd₃, wr₃⟩ mx₃ => ?_)
  have sp₃ : c₃.gpr .rsp = P s := (g₃ _ (by decide)).trans sp₂
  refine WP.seq (WP.mono_mx (by decide +kernel) (stArg_ok c₃ sp₃ 16 128
    (ia (by rw [rd₃, rd₂, rd₁, hc.rd]) 128 (by decide) (by decide))
    (h.inFr (wr₃.trans (wr₂.trans (wr₁.trans hc.wr))) 16 (by decide))) fun c₄ ⟨m₄, g₄, rd₄, wr₄⟩ mx₄ => ?_)
  have sp₄ : c₄.gpr .rsp = P s := (g₄ _ (by decide)).trans sp₃
  refine WP.mono_mx (by decide +kernel) (stArg_ok c₄ sp₄ 24 136
    (ia (by rw [rd₄, rd₃, rd₂, rd₁, hc.rd]) 136 (by decide) (by decide))
    (h.inFr (wr₄.trans (wr₃.trans (wr₂.trans (wr₁.trans hc.wr)))) 24 (by decide))) fun c₅ ⟨m₅, g₅, rd₅, wr₅⟩ mx₅ => ?_
  -- The values stored: our stack arguments, which no store reaches.
  have f₁ : Frame [dR s, stkR s] s.mem c₁.mem := by rw [m₁, hc.mem]; exact h.frame_cM
  have v₂ : c₁.mem.readW (P s + BitVec.ofNat 64 112) 64 = Dst s := h.argAt f₁ 2 (by decide)
  have f₂ : Frame [dR s, stkR s] s.mem c₂.mem := by rw [m₂]; exact Lay.frame_wFr f₁ 0 (by decide) _
  have v₃ : c₂.mem.readW (P s + BitVec.ofNat 64 104) 64 = arg s 1 := h.argAt f₂ 1 (by decide)
  have f₃ : Frame [dR s, stkR s] s.mem c₃.mem := by rw [m₃]; exact Lay.frame_wFr f₂ 8 (by decide) _
  have v₄ : c₃.mem.readW (P s + BitVec.ofNat 64 128) 64 = Tg s := h.argAt f₃ 4 (by decide)
  have f₄ : Frame [dR s, stkR s] s.mem c₄.mem := by rw [m₄]; exact Lay.frame_wFr f₃ 16 (by decide) _
  have v₅ : c₄.mem.readW (P s + BitVec.ofNat 64 136) 64 = arg s 5 := h.argAt f₄ 5 (by decide)
  have hg (r : Reg) (hr : r ≠ .rax) : c₅.gpr r = c₁.gpr r := by rw [g₅ r hr, g₄ r hr, g₃ r hr, g₂ r hr]
  refine ⟨by rw [m₅, v₅, m₄, v₄, m₃, v₃, m₂, v₂, m₁, hc.mem], by rw [hg _ (by decide), rdi₁]; rfl,
    by rw [hg _ (by decide), rsi₁]; rfl, by rw [hg _ (by decide), rdx₁]; rfl, by rw [hg _ (by decide), rcx₁]; rfl,
    by rw [hg _ (by decide), r8₁]; rfl, by rw [hg _ (by decide), r9₁]; rfl, fun r hr hsp => ?_,
    by rw [hg _ (by decide), sp₁], by rw [rd₅, rd₄, rd₃, rd₂, rd₁, hc.rd],
    by rw [wr₅, wr₄, wr₃, wr₂, wr₁, hc.wr], by rw [mx₅, mx₄, mx₃, mx₂, mx₁, hc.mx]⟩
  have hra : r ≠ .rax := fun e => by subst e; simp [calleeSaved] at hr
  rw [hg r hra, cs₁ r hr]
  refine hc.gpr r ?_ ?_ ?_ hra ?_ ?_ hsp <;> (intro e; subst e; simp [calleeSaved] at hr)

/-! ## The call -/

theorem add_ofNat_sub_ofNat (B : Addr) {a b : Nat} (h : b ≤ a) :
    B + BitVec.ofNat 64 a - BitVec.ofNat 64 b = B + BitVec.ofNat 64 (a - b) := by
  rw [← Offset.ofNat_sub_ofNat h, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]

section
variable (M : CtxMode) (s c : State)

/-- The regions the call of `vg_aes_gcm_open` reads (with its stack
arguments, the lowest four words of our frame) and writes. -/
abbrev rdC : List Region := [kR M s, nR s, aR s, tR s, ⟨P s, 32⟩]
abbrev wrC : List Region := [dR s]

/-- The state the callee starts in. -/
abbrev xS : State := c.callEntry.withRegions (rdC M s) (wrC s)

end

theorem xgpr_eq {M : CtxMode} {s c : State} {r : Reg} (hr : r ≠ .rsp) : (xS M s c).gpr r = c.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr]

section
variable {M : CtxMode} {s c : State} (h : Lay M s) (hc : Ready s c)
include h hc

omit h in
theorem Ready.xsp : (xS M s c).gpr .rsp = Bs s + BitVec.ofNat 64 2632 := by
  rw [State.withRegions_gpr, State.callEntry_rsp, hc.rsp, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl,
    add_ofNat_sub_ofNat _ (by decide)]

omit h in
/-- The return address of the call. -/
theorem Ready.xmem : Frame [⟨Bs s + BitVec.ofNat 64 2632, 8⟩] (rM s) (xS M s c).mem := by
  rw [State.withRegions_mem, State.callEntry_mem, hc.rsp, hc.mem, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl,
    add_ofNat_sub_ofNat _ (by decide)]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

theorem Ready.xframe : Frame [dR s, stkR s] s.mem (xS M s c).mem :=
  h.frame_rM.trans (hc.xmem.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨stkR s, by simp, stk_sub s 2632 8 (by decide)⟩)

/-- The callee's stack arguments: `dst`, `len`, `tag` and `tag_len`. -/
theorem Ready.xarg (i : Nat) (hi : i < 4) :
    arg (xS M s c) i = (rM s).readW (P s + BitVec.ofNat 64 (8 * i)) 64 := by
  have hBn := h.hBn
  show (xS M s c).mem.readW ((xS M s c).gpr .rsp + BitVec.ofNat 64 (8 * (i + 1))) 64 = _
  rw [hc.xsp, Offset.add_ofNat_add_ofNat, show 2632 + 8 * (i + 1) = 2640 + 8 * i by omega, ← Offset.add_ofNat_add_ofNat]
  refine Frame.readW hc.xmem (r := ⟨P s + BitVec.ofNat 64 (8 * i), 8⟩) (Region.contains_self _ _) (fun r hr => ?_)
    (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  rw [Offset.add_ofNat_add_ofNat]
  exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)

theorem Ready.xa : arg (xS M s c) 0 = Dst s ∧ arg (xS M s c) 1 = arg s 1 ∧ arg (xS M s c) 2 = Tg s ∧
    arg (xS M s c) 3 = arg s 5 := by
  obtain ⟨a₀, a₁, a₂, a₃⟩ := h.rArgs
  exact ⟨(hc.xarg h 0 (by decide)).trans a₀, (hc.xarg h 1 (by decide)).trans a₁, (hc.xarg h 2 (by decide)).trans a₂,
    (hc.xarg h 3 (by decide)).trans a₃⟩

/-- What the call needs. -/
theorem Ready.callPre : openPreK M (xS M s c) ∧ Covers (rdC M s ++ wrC s) (c.rd ++ c.wr) ∧
    Covers (wrC s) c.wr := by
  have hBn := h.hBn
  have hp := h.pre
  obtain ⟨xa₀, xa₁, xa₂, xa₃⟩ := hc.xa h
  have hx (r : Reg) (hr : r ≠ .rsp) : (xS M s c).gpr r = c.gpr r := xgpr_eq hr
  have hxa : args (xS M s c) 4 = ⟨P s, 32⟩ := by
    show (⟨(xS M s c).gpr .rsp + BitVec.ofNat 64 (8 * (0 + 1)), 8 * 4⟩ : Region) = _
    rw [hc.xsp, Offset.add_ofNat_add_ofNat]
  have hstk : below (Bs s + BitVec.ofNat 64 2632) 2632 = ⟨Bs s, 2632⟩ := by
    simp only [below, add_ofNat_sub_ofNat _ (show 2632 ≤ 2632 by decide), Nat.sub_self, BitVec.add_zero]
  have hxsp : (Bs s + BitVec.ofNat 64 2632).toNat = (Bs s).toNat + 2632 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2632) (by decide), Nat.mod_eq_of_lt (by omega)]
  have sb (d n : Nat) (hd : d + n ≤ 2728) {r : Region} (hr : (stkR s).Disjoint r) :
      (⟨Bs s + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := hr.sub_left (stk_sub s d n hd)
  have s0 {r : Region} (hr : (stkR s).Disjoint r) : (⟨Bs s, 2632⟩ : Region).Disjoint r :=
    hr.sub_left (Region.sub_prefix (by decide))
  have hargs : (⟨P s, 32⟩ : Region) = ⟨Bs s + BitVec.ofNat 64 2640, 32⟩ := rfl
  refine ⟨?_, ?_, ?_⟩
  · simp only [openPreK, State.withRegions_rd, State.withRegions_wr, hx .rdi (by decide), hx .rsi (by decide),
      hx .rdx (by decide), hx .rcx (by decide), hx .r8 (by decide), hx .r9 (by decide), hc.rdi, hc.rsi, hc.rdx,
      hc.rcx, hc.r8, hc.r9, xa₀, xa₁, xa₂, xa₃, hxa, Proof.AesGcm.ret, hc.xsp, hstk, Proof.AesGcm.rounds]
    refine ⟨trivial, trivial, hp.kd, hp.nd, hp.ad, hp.dt, (sb 2640 32 (by decide) hp.bd).symm,
      sb 2632 8 (by decide) hp.bk, sb 2632 8 (by decide) hp.bn, sb 2632 8 (by decide) hp.ba,
      sb 2632 8 (by decide) hp.bd, sb 2632 8 (by decide) hp.bt,
      Offset.disjoint _ (.inl (by omega)) (by omega) (by omega),
      s0 hp.bk, s0 hp.bn, s0 hp.ba, s0 hp.bd, s0 hp.bt, Offset.base_disjoint _ (by decide) (by omega),
      hp.wk, hp.wn, hp.wa, hp.wd, hp.wt, by omega, by omega, hp.rounds, ?_⟩
    exact M.frame (hc.xframe h) h.k_kept.all hp.wk hp.ok
  · rw [hc.rd, hc.wr, hp.rd, hp.wr]
    refine Covers.of_forall fun r hr => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl | rfl) | rfl
    · exact covers_of_mem (by simp)
    · exact covers_of_mem (by simp)
    · exact covers_of_mem (by simp)
    · exact covers_of_mem (by simp)
    · intro a n ⟨x, hx', hcn⟩
      simp only [List.mem_singleton] at hx'; subst hx'
      exact ⟨FR s, by simp, by simp only [Region.Contains] at hcn ⊢; omega⟩
    · exact covers_of_mem (by simp)
  · rw [hc.wr, hp.wr]; exact covers_of_mem (by simp)

end

/-- What the callee computes: `openResult` on the ciphertext copied to `dst`,
which is ours (`res`). -/
theorem Ready.xres {M : CtxMode} {s c : State} (h : Lay M s) (hc : Ready s c) :
    openResult (ctxCiph (xS M s c).mem ((xS M s c).gpr .rdi) ((xS M s c).gpr .rsi).toNat)
        (ctxH (xS M s c).mem ((xS M s c).gpr .rdi)) (stackArg (xS M s c) 3).toNat
        (bytesAt (xS M s c).mem ((xS M s c).gpr .rdx) ((xS M s c).gpr .rcx).toNat)
        (bytesAt (xS M s c).mem (stackArg (xS M s c) 0) (stackArg (xS M s c) 1).toNat)
        (bytesAt (xS M s c).mem ((xS M s c).gpr .r8) ((xS M s c).gpr .r9).toNat)
        (bytesAt (xS M s c).mem (stackArg (xS M s c) 2) (stackArg (xS M s c) 3).toNat) = res s := by
  have hBn := h.hBn
  have hp := h.pre
  have hx (r : Reg) (hr : r ≠ .rsp) : (xS M s c).gpr r = c.gpr r := xgpr_eq hr
  obtain ⟨xa₀, xa₁, xa₂, xa₃⟩ := hc.xa h
  have xa₀' : stackArg (xS M s c) 0 = Dst s := xa₀
  have xa₁' : stackArg (xS M s c) 1 = arg s 1 := xa₁
  have xa₂' : stackArg (xS M s c) 2 = Tg s := xa₂
  have xa₃' : stackArg (xS M s c) 3 = arg s 5 := xa₃
  have xf := hc.xframe h
  have hd' : bytesAt (xS M s c).mem (Dst s) (L s) = bytesAt s.mem (Src s) (L s) := by
    have st (d : Nat) (hd : d + 8 ≤ 88) : (stkR s).Contains (P s + BitVec.ofNat 64 d) 8 := by
      rw [Offset.add_ofNat_add_ofNat]; exact Offset.contains_base _ (by omega) (by omega)
    have f₀ : Frame [stkR s] (cM s) (rM s) :=
      (((Frame.refl [stkR s] _).writeW (List.mem_singleton_self _) _ (st 0 (by decide))).writeW
        (List.mem_singleton_self _) _ (st 8 (by decide))).writeW (List.mem_singleton_self _) _ (st 16 (by decide))
        |>.writeW (List.mem_singleton_self _) _ (st 24 (by decide))
    have f₁ : Frame [stkR s] (cM s) (xS M s c).mem :=
      f₀.trans (hc.xmem.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨stkR s, by simp, stk_sub s 2632 8 (by decide)⟩)
    rw [Proof.AesGcm.X86_64.bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.bd.symm) (by have := h.lt; omega)]
    have hl : (bytesAt s.mem (Src s) (L s)).length = L s := Proof.AesGcm.X86_64.length_bytesAt _ _ _
    conv => lhs; rw [← hl]
    exact Proof.ChaCha20Poly1305.bytesAt_writeBytes_self _ _ _ (by rw [hl]; have := h.lt; omega)
  have en := h.n_kept.bytes xf
  have ea := h.a_kept.bytes xf
  have et := h.t_kept.bytes xf
  simp only [nR, aR, tR] at en ea et
  rw [xa₀', xa₁', xa₂', xa₃', hx .rdi (by decide), hx .rsi (by decide), hx .rdx (by decide), hx .rcx (by decide),
    hx .r8 (by decide), hx .r9 (by decide), hc.rdi, hc.rsi, hc.rdx, hc.rcx, hc.r8, hc.r9, h.ciph_eq xf, h.hk_eq xf,
    hd', en, ea, et]

/-- What the callee may leak: what we may. -/
theorem Ready.leak {M : CtxMode} {s c : State} (h : Lay M s) (hc : Ready s c) :
    Proof.AesGcm.openLeak (xS M s c) = toLeak s := by
  have hx : (xS M s c).gpr .rsi = s.gpr .rsi := (xgpr_eq (by decide)).trans hc.rsi
  simp only [Proof.AesGcm.openLeak, toLeak, Proof.AesGcm.rounds, Proof.AesGcm.arg]
  rw [hc.xres h, hx]

/-- After the call: whether it succeeded, and if so the plaintext at `dst`. -/
structure Called (s z : State) : Prop where
  out : match res s with
    | some pt => (z.gpr .rax).setWidth 32 = 1 ∧ bytesAt z.mem (Dst s) (L s) = pt
    | none => (z.gpr .rax).setWidth 32 = 0
  frame : Frame [dR s, stkR s] s.mem z.mem
  cs : ∀ r ∈ calleeSaved, r ≠ .rsp → z.gpr r = s.gpr r
  rsp : z.gpr .rsp = P s
  rd : z.rd = s.rd
  wr : z.wr = FR s :: s.wr
  mx : z.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10

theorem called_wp {M : CtxMode} (F : OpenFn M) {s c : State} (h : Lay M s) (hc : Ready s c) :
    WP isa (.call F.fn.name F.fn.code) c (Called s) := by
  have hBn := h.hBn
  have hp := h.pre
  obtain ⟨hcp, hcov, hw⟩ := hc.callPre h
  have hd := F.xd
  have hx (r : Reg) (hr : r ≠ .rsp) : (xS M s c).gpr r = c.gpr r := xgpr_eq hr
  obtain ⟨xa₀, xa₁, xa₂, xa₃⟩ := hc.xa h
  refine WP.call_sp_mx F.ok F.sp (by omega) hcp hcov hw fun s' rd' wr' cs' fr' _ ⟨s₂, m₂, g₂, post'⟩ mx' => ?_
  have rsp' : s'.gpr .rsp = c.gpr .rsp := cs' .rsp (by decide)
  -- What the callee read: the arguments, and the ciphertext copied to `dst`.
  have hpost : Proof.AesGcm.openX86_64.post (xS M s c) s₂ := post'
  simp only [Proof.AesGcm.openX86_64, Proof.AesGcm.arg] at hpost
  have xa₀' : stackArg (xS M s c) 0 = Dst s := xa₀
  have xa₁' : stackArg (xS M s c) 1 = arg s 1 := xa₁
  rw [hc.xres h, xa₀', xa₁', m₂, g₂ .rax (by decide)] at hpost
  -- What the callee wrote: `dst` and the stack below our frame.
  have fz : Frame [dR s, stkR s] s.mem s'.mem := by
    have hPs : c.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 88 := by rw [hc.rsp, ← hP, pushed_rsp]; rfl
    refine (hc.mem ▸ h.frame_rM).trans (fr'.sub fun r hr => ?_)
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨dR s, by simp, fun _ h => h⟩
    · refine ⟨stkR s, by simp, ?_⟩
      rw [hPs]
      simp only [below]
      rw [BitVec.sub_sub, ← BitVec.ofNat_add]
      exact Offset.sub_below _ (by omega) (by omega)
  refine ⟨?_, fz, fun r hr hsp => ?_, rsp'.trans hc.rsp, rd'.trans hc.rd, wr'.trans hc.wr, mx'.trans (by rw [hc.mx])⟩
  · show match res s with
      | some pt => (s'.gpr .rax).setWidth 32 = 1 ∧ bytesAt s'.mem (Dst s) (L s) = pt
      | none => (s'.gpr .rax).setWidth 32 = 0
    revert hpost
    generalize res s = o
    cases o with
    | some pt => exact fun hp => hp
    | none => exact fun hp => hp.1
  · rw [cs' r hr, hc.cs r hr hsp]

/-! ## After the call -/

theorem zeroStep_ok (s : State) {D : Addr} {i n : Nat} (hd : s.gpr .rdi = D)
    (hi : s.gpr .r10 = BitVec.ofNat 64 i) (hn : s.gpr .rcx = BitVec.ofNat 64 n)
    (w : InRegions s.wr (D + BitVec.ofNat 64 i) 1) :
    ∃ s', runBlock isa wipeBody s = some s' ∧
      s'.mem = s.mem.writeW (D + BitVec.ofNat 64 i) ((s.gpr .rax).setWidth 8) ∧
      s'.gpr .r10 = BitVec.ofNat 64 i + 1 ∧
      s'.zf = some (BitVec.ofNat 64 i + 1 - BitVec.ofNat 64 n == 0) ∧
      (∀ r, r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e₂ := Proof.AesGcm.X86_64.ea_idx s .rdi hd hi
  have wr' : InRegions (s.rd ++ s.wr) (D + BitVec.ofNat 64 i) 1 := by
    obtain ⟨x, hx, hc⟩ := w; exact ⟨x, List.mem_append_right _ hx, hc⟩
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, ↓reduceDIte, Nat.reduceLT, Nat.reduceGT, Nat.reduceLeDiff,
      Nat.reduceEqDiff, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reducePow,
      BitVec.reduceEq, not_false_eq_true, not_true_eq_false, Bool.not_true, Bool.not_false, and_self, false_implies,
      implies_true, Nat.reduceBEq, Nat.reduceBNe, decide_true, decide_false, BitVec.reduceSignExtend, wipeBody, dstB,
      imm, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, State.load8, State.store8, State.ea,
      Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg,
      rd_arithFlags, wr_setReg, wr_arithFlags, ite_true, ite_false, e₂, w, wr']
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl⟩
  · simp only [mem_setReg, mem_arithFlags]
  · simp [gpr_setReg, hi]
  · simp [hi, hn]
  · intro r h₁; simp [gpr_setReg, h₁]

/-- `n` zero bytes. -/
abbrev zeros (n : Nat) : List Byte := List.replicate n 0

theorem zeros_succ (n : Nat) : zeros (n + 1) = zeros n ++ [0] := List.replicate_succ' ..

/-- The loop of `wipe`: the `n` (at least 1) bytes at `D` zeroed, with `al`
zero. -/
theorem zeroLoop_ok (s : State) {D : Addr} {n : Nat} (hd : s.gpr .rdi = D) (hn : s.gpr .rcx = BitVec.ofNat 64 n)
    (h10 : s.gpr .r10 = BitVec.ofNat 64 0) (hax : (s.gpr .rax).setWidth 8 = 0) (pos : 1 ≤ n) (lt : n < 2 ^ 63)
    (wr : Covers [⟨D, n⟩] s.wr) :
    WP isa (.loop (.block wipeBody) .ne) s fun s' => s'.mem = writeBytes s.mem D (zeros n) ∧
      (∀ r, r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.loop (M := isa) (body := .block wipeBody) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .r10 = BitVec.ofNat 64 i ∧
      t.mem = writeBytes s.mem D (zeros i) ∧ (∀ r, r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_
    (n - 0) _ ⟨0, rfl, pos, h10, by simp [writeBytes_nil], fun _ _ => rfl, rfl, rfl⟩
  rintro k t ⟨i, rfl, hi, r10, mem, g, rd, wr'⟩
  obtain ⟨t', run', mem', r10', zf', g', rd', wr''⟩ := zeroStep_ok t (by rw [g _ (by decide), hd]) r10
    (by rw [g _ (by decide), hn]) (by rw [wr']; exact Proof.AesGcm.X86_64.in_of_covers wr hi (by omega))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen : (zeros i).length = i := List.length_replicate ..
  have hmem : t'.mem = writeBytes s.mem D (zeros (i + 1)) := by
    rw [mem', mem, g _ (by decide), hax, zeros_succ, writeBytes_snoc s.mem D _ _ (by rw [hlen]; omega), hlen]
  have hz : t'.zf = some (decide (i + 1 = n)) := by
    rw [zf', Proof.AesGcm.X86_64.succ_ofNat, Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
  have gg : ∀ r, r ≠ .r10 → t'.gpr r = s.gpr r := fun r h₁ => by rw [g' r h₁, g r h₁]
  by_cases he : i + 1 = n
  · left
    exact ⟨by simp [eval, hz, he], by rw [hmem, he], gg, by rw [rd', rd], by rw [wr'', wr']⟩
  · right
    exact ⟨by simp [eval, hz, he], n - (i + 1), by omega, i + 1, rfl, by omega,
      by rw [r10', Proof.AesGcm.X86_64.succ_ofNat], hmem, gg, by rw [rd', rd], by rw [wr'', wr']⟩

/-- At the end of our frame's body. -/
structure Done (s d : State) : Prop where
  out : toPost s d
  frame : Frame [dR s, stkR s] s.mem d.mem
  cs : ∀ r ∈ calleeSaved, r ≠ .rsp → d.gpr r = s.gpr r
  rsp : d.gpr .rsp = P s
  wr : d.wr = FR s :: s.wr
  mx : d.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10

theorem bytesAt_zeros (m : Mem) (D : Addr) {n : Nat} (hn : n < 2 ^ 64) :
    bytesAt (writeBytes m D (zeros n)) D n = zeros n := by
  have := Proof.ChaCha20Poly1305.bytesAt_writeBytes_self m D (zeros n) (by rw [List.length_replicate]; exact hn)
  rwa [List.length_replicate] at this

/-- After `wipeArgs`. -/
structure Wiping (s z w : State) : Prop where
  rdi : w.gpr .rdi = Dst s
  rcx : w.gpr .rcx = BitVec.ofNat 64 (L s)
  rax : w.gpr .rax = BitVec.setWidth 64 (BitVec.ofNat 32 0)
  r10 : w.gpr .r10 = BitVec.ofNat 64 0
  zf : w.zf = some (decide (0 = L s))
  gpr : ∀ r, r ≠ .rdi → r ≠ .rcx → r ≠ .rax → r ≠ .r10 → w.gpr r = z.gpr r
  mem : w.mem = z.mem
  rd : w.rd = z.rd
  wr : w.wr = z.wr
  mx : w.mxcsr = z.mxcsr

theorem wipeArgs_wp {M : CtxMode} {s z : State} (h : Lay M s) (hz : Called s z) :
    WP isa (.block wipeArgs) z (Wiping s z) := by
  have hBn := h.hBn
  have ia (d : Nat) (h₁ : 96 ≤ d) (hd : d + 8 ≤ 144) := h.inArg (wr := z.wr) hz.rd d h₁ hd
  obtain ⟨w, run₁, rdi₁, rcx₁, rax₁, r10₁, zf₁, g₁, m₁, rd₁, wr₁, mx₁⟩ : ∃ w, runBlock isa wipeArgs z = some w ∧
      w.gpr .rdi = z.mem.readW (P s + BitVec.ofNat 64 112) 64 ∧
      w.gpr .rcx = z.mem.readW (P s + BitVec.ofNat 64 104) 64 ∧
      w.gpr .rax = BitVec.setWidth 64 (BitVec.ofNat 32 0) ∧ w.gpr .r10 = BitVec.setWidth 64 (BitVec.ofNat 32 0) ∧
      w.zf = some (BitVec.setWidth 64 (BitVec.ofNat 32 0) - z.mem.readW (P s + BitVec.ofNat 64 104) 64 == 0) ∧
      (∀ r, r ≠ .rdi → r ≠ .rcx → r ≠ .rax → r ≠ .r10 → w.gpr r = z.gpr r) ∧ w.mem = z.mem ∧ w.rd = z.rd ∧
      w.wr = z.wr ∧ w.mxcsr = z.mxcsr := by
    refine ⟨_, by xrun [wipeArgs, hz.rsp, ia 104 (by decide) (by decide), ia 112 (by decide) (by decide)], ?_⟩
    refine ⟨by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg],
      by simp [gpr_setReg, gpr_arithFlags, zf_arithFlags], fun r a b c d => by simp [gpr_setReg, a, b, c, d],
      rfl, rfl, rfl, rfl⟩
  have v₁ := h.argAt hz.frame 1 (by decide)
  have v₂ := h.argAt hz.frame 2 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at v₁ v₂
  rw [v₂] at rdi₁
  rw [v₁] at rcx₁ zf₁
  have hlt := h.lt
  refine WP.of_runBlock ⟨w, run₁, rdi₁, by rw [rcx₁, BitVec.ofNat_toNat, BitVec.setWidth_eq], rax₁, r10₁, ?_, g₁,
    m₁, rd₁, wr₁, mx₁⟩
  rw [zf₁, show BitVec.setWidth 64 (BitVec.ofNat 32 0) = BitVec.ofNat 64 0 from rfl,
    show arg s 1 = BitVec.ofNat 64 (L s) by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq],
    Offset.ofNat_sub_ofNat_beq (by decide) (by omega)]

/-- `wipe`, after a call that failed. -/
theorem wipe_wp {M : CtxMode} {s z : State} (h : Lay M s) (hz : Called s z) (hres : res s = none) :
    WP isa wipe z (Done s) := by
  have hp := h.pre
  have hlt := h.lt
  have hout (m : Mem) (hm : m = writeBytes z.mem (Dst s) (zeros (L s))) (d : State) (hdm : d.mem = m)
      (hdax : d.gpr .rax = BitVec.setWidth 64 (BitVec.ofNat 32 0)) : toPost s d := by
    simp only [toPost, hres]
    exact ⟨by rw [hdax]; rfl, by rw [hdm, hm]; exact bytesAt_zeros _ _ (by omega)⟩
  have hfr (m : Mem) (hm : m = writeBytes z.mem (Dst s) (zeros (L s))) : Frame [dR s, stkR s] s.mem m := by
    rw [hm]
    refine hz.frame.trans ((writeBytes_frame (R := dR s) _ _ _ ?_).mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp)
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, List.length_replicate, Nat.le_refl]
  have hcs (d : State) (hd : ∀ r, r ≠ .rdi → r ≠ .rcx → r ≠ .rax → r ≠ .r10 → d.gpr r = z.gpr r) :
      ∀ r ∈ calleeSaved, r ≠ .rsp → d.gpr r = s.gpr r := fun r hr hsp => by
    rw [hd r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)
      (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr), hz.cs r hr hsp]
  refine WP.seq (WP.mono (wipeArgs_wp h hz) fun w ⟨rdi₁, hrcx, rax₁, r10₁, hz0, g₁, m₁, rd₁, wr₁, mx₁⟩ => ?_)
  refine WP.ite (decide (0 = L s)) (by simp only [eval, hz0]) (fun he => ?_) (fun he => ?_)
  · -- No bytes.
    have h0 : L s = 0 := (of_decide_eq_true he).symm
    refine WP.block_nil ⟨hout z.mem (by rw [h0, zeros, List.replicate_zero, writeBytes_nil]) w (by rw [m₁])
      rax₁, hfr z.mem (by rw [h0, zeros, List.replicate_zero, writeBytes_nil]) |>.trans (by rw [m₁]; exact Frame.refl _ _),
      hcs w g₁, by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), hz.rsp], by rw [wr₁, hz.wr],
      by rw [mx₁, hz.mx]⟩
  · have hpos : 1 ≤ L s := by have := of_decide_eq_false he; omega
    refine WP.mono_mx (by decide +kernel) (zeroLoop_ok w rdi₁ hrcx r10₁ (by rw [rax₁]; rfl) hpos h.lt
      (covers_of_mem (by rw [wr₁, hz.wr, hp.wr]; simp)))
      fun d ⟨md, gd, rdd, wrd⟩ mxd => ?_
    have ed : ∀ r, r ≠ .rdi → r ≠ .rcx → r ≠ .rax → r ≠ .r10 → d.gpr r = z.gpr r :=
      fun r a b c e => by rw [gd r e, g₁ r a b c e]
    rw [m₁] at md
    exact ⟨hout _ rfl d md (by rw [gd _ (by decide), rax₁]), md ▸ hfr _ rfl, hcs d ed,
      by rw [ed _ (by decide) (by decide) (by decide) (by decide), hz.rsp], by rw [wrd, wr₁, hz.wr],
      by rw [mxd, mx₁, hz.mx]⟩

/-- `after`: `dst` wiped if the call failed. -/
theorem after_wp {M : CtxMode} {s z : State} (h : Lay M s) (hz : Called s z) : WP isa after z (Done s) := by
  obtain ⟨z₁, run₁, zf₁, g₁, m₁, rd₁, wr₁, mx₁⟩ : ∃ z₁, runBlock isa [.alu32 .test .rax (.reg .rax)] z = some z₁ ∧
      z₁.zf = some (((z.gpr .rax).setWidth 32 &&& (z.gpr .rax).setWidth 32) == 0) ∧ z₁.gpr = z.gpr ∧
      z₁.mem = z.mem ∧ z₁.rd = z.rd ∧ z₁.wr = z.wr ∧ z₁.mxcsr = z.mxcsr :=
    ⟨arithFlags z ((z.gpr .rax).setWidth 32 &&& (z.gpr .rax).setWidth 32) false false, by xrun [],
      by simp [zf_arithFlags], rfl, rfl, rfl, rfl, rfl⟩
  rw [BitVec.and_self] at zf₁
  have hz₁ : Called s z₁ :=
    ⟨by rw [g₁, m₁]; exact hz.out, m₁ ▸ hz.frame, fun r hr hsp => by rw [g₁]; exact hz.cs r hr hsp,
      by rw [g₁]; exact hz.rsp, rd₁.trans hz.rd, wr₁.trans hz.wr, by rw [mx₁]; exact hz.mx⟩
  refine WP.seq (WP.of_runBlock ⟨z₁, run₁, ?_⟩)
  refine WP.ite ((z.gpr .rax).setWidth 32 == 0) (by simp only [eval, zf₁]) (fun hb => ?_) (fun hb => ?_)
  · -- The call failed.
    have hres : res s = none := by
      have ho := hz.out
      revert ho
      generalize res s = o
      cases o with
      | none => exact fun _ => rfl
      | some pt => intro ho; rw [ho.1] at hb; exact absurd hb (by decide)
    exact wipe_wp h hz₁ hres
  · -- It succeeded.
    have ho := hz.out
    refine WP.block_nil ⟨?_, m₁ ▸ hz.frame, fun r hr hsp => by rw [g₁]; exact hz.cs r hr hsp,
      by rw [g₁]; exact hz.rsp, wr₁.trans hz.wr, by rw [mx₁]; exact hz.mx⟩
    simp only [toPost, g₁, m₁]
    revert ho
    generalize res s = o
    cases o with
    | none => intro ho; rw [ho] at hb; exact absurd hb (by decide)
    | some pt => exact fun ho => ho

/-! ## The function -/

/-- The body of our frame. -/
theorem body_wp (w : Width) {M : CtxMode} (F : OpenFn M) {s : State} (h : Lay M s) :
    WP isa (.seq (.block entry) (.seq (Impl.ChaCha20Poly1305.X86_64.SealGather.copyBytes w)
      (.seq callArgs (.seq (.call F.fn.name F.fn.code) after)))) (pushed frameRegs s) (Done s) := by
  refine WP.seq (WP.mono (entered_wp h) fun e he => ?_)
  refine WP.seq (WP.mono (copied_wp w h he) fun c hc => ?_)
  refine WP.seq (WP.mono (ready_wp h hc) fun r hr => ?_)
  exact WP.seq (WP.mono (called_wp F h hr) fun z hz => after_wp h hz)

theorem openTo_wp (w : Width) {M : CtxMode} (F : OpenFn M) {s : State} (hs : ToPre M s) :
    WP isa (openTo w F.fn) s fun z => abiPreserved s z ∧ toPost s z := by
  have h := lay hs
  have hn : 8 * frameRegs.length ≤ (s.gpr .rsp).toNat := by
    have := hs.w₁; simp only [List.length_cons, List.length_nil]; omega
  refine WP.frame (by simp) (by decide) (by decide) hn (WP.mono (body_wp w F h) fun d hd => ?_)
  refine ⟨by rw [hd.rsp, hP s], by rw [hd.wr, hPwr s], ⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · by_cases hsp : r = .rsp
    · subst hsp
      rw [popped_rsp, hd.rsp, Offset.add_ofNat_add_ofNat, h.hB]; rfl
    · have h11 : r ≠ .r11 := fun e => by subst e; simp [calleeSaved] at hr
      rw [popped_gpr _ _ _ hsp h11, hd.cs r hr hsp]
  · rw [popped_mem]; exact h.retW hd.frame
  · rw [popped_mxcsr]; exact hd.mx
  · have := hd.out
    simp only [toPost, popped_mem, popped_gpr _ _ _ (show Reg.rax ≠ .rsp by decide) (show Reg.rax ≠ .r11 by decide)]
      at this ⊢
    exact this

end VG.Proof.AesGcm.X86_64.OpenTo
