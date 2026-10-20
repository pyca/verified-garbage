module

public import VerifiedGarbage.Spec.Cmac.TripleDesContract
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Streaming TDEA-CMAC on ARMv7: the contracts the proofs are written against

The artifacts' contracts are the shared ones of
`Spec/Cmac/TripleDesContract.lean`, with the working space as an argument
(`Proof/CmacTripleDes/StreamScratch.lean`), which imply these
(`Verified.lean`). `stream_init` uses no stack; `absorb` and `finish` push
the working space's address, the stack argument of the code of `update` and
`finalize`, below the stack pointer: so the 4 bytes below it may not overlap
any buffer.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.Arm

open VG VG.Arm

/-- `vg_cmac_triple_des_stream_init(state = r0, key = r1, key_len = r2, scratch = r3)`. -/
def initArm : Contract isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 416⟩
    let key : Region := ⟨State.addr (s.gpr .r1), (s.gpr .r2).toNat⟩
    let scr : Region := ⟨State.addr (s.gpr .r3), 640⟩
    s.rd = [key] ∧ s.wr = [state, scr] ∧ state.Disjoint key ∧ state.Disjoint scr ∧ key.Disjoint scr ∧
      (s.gpr .r0).toNat + 416 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + (s.gpr .r2).toNat ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 640 ≤ 2 ^ 32 ∧ Spec.TripleDes.validKey (s.gpr .r2).toNat
  post s s' :=
    Spec.Cmac.tdesRepr s'.mem (State.addr (s.gpr .r0))
      (Spec.TripleDes.bytesAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat) []
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3

/-- `count`, in `r2:r3` (AAPCS: the low word in `r2`). -/
def countArm (s : State) : BitVec 64 := s.gpr .r3 ++ s.gpr .r2

/-- `vg_cmac_triple_des_absorb(state = r0, count = r2:r3, data = [sp], len = [sp, #4], scratch = [sp, #8])`. -/
def absorbArm : Contract isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 416⟩
    let data : Region := ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩
    let scr : Region := ⟨State.addr (stackArg s 2), 688⟩
    let args : Region := ⟨stackArgAddr s 0, 12⟩
    let blw : Region := ⟨State.addr s.sp - 4, 4⟩
    s.rd = [data, args] ∧ s.wr = [state, scr] ∧
      state.Disjoint data ∧ state.Disjoint scr ∧ data.Disjoint scr ∧
      args.Disjoint state ∧ args.Disjoint scr ∧
      blw.Disjoint state ∧ blw.Disjoint data ∧ blw.Disjoint scr ∧
      (s.gpr .r0).toNat + 416 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 32 ∧
      (stackArg s 2).toNat + 688 ≤ 2 ^ 32 ∧ 4 ≤ s.sp.toNat ∧ s.sp.toNat + 12 ≤ 2 ^ 32
  post s s' :=
    ∀ key msg, Spec.Cmac.tdesRepr s.mem (State.addr (s.gpr .r0)) key msg →
      countArm s = BitVec.ofNat 64 msg.length → msg.length + (stackArg s 1).toNat < 2 ^ 64 →
      Spec.Cmac.tdesRepr s'.mem (State.addr (s.gpr .r0)) key
        (msg ++ Spec.Aes.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
      stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2

/-- `vg_cmac_triple_des_finish(state = r0, count = r2:r3, out = [sp], scratch = [sp, #4])`. -/
def finishArm : Contract isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 416⟩
    let out : Region := ⟨State.addr (stackArg s 0), 8⟩
    let scr : Region := ⟨State.addr (stackArg s 1), 640⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    let blw : Region := ⟨State.addr s.sp - 4, 4⟩
    s.rd = [args] ∧ s.wr = [state, out, scr] ∧
      state.Disjoint out ∧ state.Disjoint scr ∧ out.Disjoint scr ∧
      args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scr ∧
      blw.Disjoint state ∧ blw.Disjoint out ∧ blw.Disjoint scr ∧
      (s.gpr .r0).toNat + 416 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + 8 ≤ 2 ^ 32 ∧
      (stackArg s 1).toNat + 640 ≤ 2 ^ 32 ∧ 4 ≤ s.sp.toNat ∧ s.sp.toNat + 8 ≤ 2 ^ 32
  post s s' :=
    ∀ key msg, Spec.Cmac.tdesRepr s.mem (State.addr (s.gpr .r0)) key msg →
      countArm s = BitVec.ofNat 64 msg.length → msg.length < 2 ^ 64 →
      Spec.Aes.bytesAt s'.mem (State.addr (stackArg s 0)) 8 = Spec.Cmac.tdesCmac key 8 msg
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
      stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

end VG.Proof.CmacTripleDes.Stream.Arm
