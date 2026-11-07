module

public import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.Verified
public import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.CT
public import VerifiedGarbage.Proof.Sha3.Instances
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
public import VerifiedGarbage.Impl.Sha3.PPC64LE.Instances
public import VerifiedGarbage.Spec.Sha3.Instances
import VerifiedGarbage.Proof.Framework.Prologue
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT

meta import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.Verified
meta import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.CT
meta import VerifiedGarbage.Proof.Sha3.Instances
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
meta import VerifiedGarbage.Impl.Sha3.PPC64LE.Instances
meta import VerifiedGarbage.Spec.Sha3.Instances
meta import VerifiedGarbage.Proof.Framework.Prologue
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Sha3.Stream
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Call
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT

/-!
# SHA-3 and SHAKE on PPC64LE: the functions of each instance

As on x86-64 (`Proof/Sha3/X86_64/Instances.lean`): each runs the sponge's
code after a block that moves its arguments into the registers that code
takes them in and sets the rate (and suffix) (`Verified.of_prologue`).
-/

@[expose] public section

namespace VG.Proof.Sha3.PPC64LE.Instances

open VG VG.PPC64LE VG.Impl.Sha3.PPC64LE.Instances
open VG.Spec.Sha3 (Repr bytesAt rates stateAt XofRepr Xof)
open VG.Proof.Sha3.Instances (xofSponge hashSponge xofRepr_pad xofRepr_squeeze digest_of_pad
  xofFinalizeScratchContract xofSqueezeScratchContract finScratchContract)

theorem rate_lt {rate : Nat} (hr : rate ∈ rates) : rate < 2 ^ 15 := by simp [rates] at hr; omega

theorem toNat_rate {rate : Nat} (hr : rate ∈ rates) : (BitVec.ofNat 64 rate).toNat = rate := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := rate_lt hr; omega)]

/-! ## `update` -/

/-- `update rate`'s contract on PPC64LE, with the arguments in registers
(`state = r3, pos = r4, data = r5, len = r6, scratch = r7`): that of
`absorb` (`Proof.Sha3.absorbPPC64LE`), with the rate `rate`. -/
def updatePPC64LE (rate : Nat) : Contract PPC64LE.isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, 200⟩
    let data : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
    let scratch : Region := ⟨s.gpr .r7, 640⟩
    let stack : Region := ⟨s.sp - 48, 48⟩
    s.rd = [data] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    48 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch ∧
    (s.gpr .r4).toNat < rate
  post s s' :=
    (∀ msg, Repr s.mem (s.gpr .r3) rate msg → (s.gpr .r4).toNat = msg.length % rate →
      Repr s'.mem (s.gpr .r3) rate (msg ++ bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)) ∧
    (s'.gpr .r3).toNat = ((s.gpr .r4).toNat + (s.gpr .r6).toNat) % rate
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.sp = s₂.sp

/-- The state after `updateArgs rate`. -/
def updateState (rate : Nat) (s : State) : State :=
  ((((s.write .r8 (s.gpr .r7)).write .r7 (s.gpr .r6)).write .r6 (s.gpr .r5)).write .r5
    (s.gpr .r4)).write .r4 (BitVec.ofNat 64 rate)

theorem updateArgs_run {rate : Nat} (hr : rate < 2 ^ 15) (s : State) :
    execBlock isa (updateArgs rate) s = some (updateState rate s, []) := by
  simp [updateArgs, updateState, execBlock, isa, exec, Impl.Sha3.PPC64LE.Stream.mov, addrs, hr,
    State.write]

theorem updateState_gpr (rate : Nat) (s : State) (r : Reg) :
    (updateState rate s).gpr r =
      if r = .r4 then BitVec.ofNat 64 rate else if r = .r5 then s.gpr .r4
      else if r = .r6 then s.gpr .r5 else if r = .r7 then s.gpr .r6
      else if r = .r8 then s.gpr .r7 else s.gpr r := by
  simp only [updateState, State.write]

@[simp] theorem updateState_mem (rate : Nat) (s : State) : (updateState rate s).mem = s.mem := rfl
@[simp] theorem updateState_rd (rate : Nat) (s : State) : (updateState rate s).rd = s.rd := rfl
@[simp] theorem updateState_wr (rate : Nat) (s : State) : (updateState rate s).wr = s.wr := rfl
@[simp] theorem updateState_sp (rate : Nat) (s : State) : (updateState rate s).sp = s.sp := rfl
@[simp] theorem updateState_lr (rate : Nat) (s : State) : (updateState rate s).lr = s.lr := rfl

theorem preserved_ne : ∀ r ∈ preserved, r ≠ .r4 ∧ r ≠ .r5 ∧ r ≠ .r6 ∧ r ≠ .r7 ∧ r ≠ .r8 := by decide

theorem updateState_preserved (rate : Nat) (s : State) {r : Reg} (hr : r ∈ preserved) :
    (updateState rate s).gpr r = s.gpr r := by
  obtain ⟨h4, h5, h6, h7, h8⟩ := preserved_ne r hr
  simp only [updateState_gpr, h4, h5, h6, h7, h8, ite_false]

theorem absorb_sat : ∃ s, Proof.Sha3.absorbPPC64LE.pre s := by
  implies_sat [Proof.Sha3.absorbPPC64LE, rates] [Stream.absorbSat] using Stream.absorbSat

/-- A state satisfying `updatePPC64LE`'s precondition (with no data). -/
def updateSat : State :=
  { Stream.absorbSat with
    gpr := fun r => match r with | .r3 => 0x1000 | .r5 => 0x2000 | .r7 => 0x3000 | _ => 0 }

theorem update_verified' {rate : Nat} (hr : rate ∈ rates) :
    Verified PPC64LE.target (update rate) (updatePPC64LE rate) := by
  have h0 : 0 < rate := by simp [rates] at hr; omega
  have hv : Verified PPC64LE.target Impl.Sha3.PPC64LE.Stream.absorb Proof.Sha3.absorbPPC64LE :=
    Verified.of_correct Stream.absorb_correct Stream.absorb_ct (Contract.Implies.refl absorb_sat)
  refine Verified.of_prologue hv (updateState rate) (fun s _ => updateArgs_run (rate_lt hr) s)
    (fun s hs => ?_) (fun s s' _ ha => ?_) (fun s s' _ hq => ?_) (fun s₁ s₂ _ _ hp => ?_)
    ⟨updateSat, rfl, rfl, Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
      Region.disjoint_of_sep (by decide), by decide, Region.disjoint_of_sep (by decide),
      Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), h0⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hs
    simp only [Proof.Sha3.absorbPPC64LE, updateState_gpr, updateState_rd, updateState_wr,
      updateState_sp, reduceCtorEq, ite_false, ite_true, toNat_rate hr]
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, hr, h10⟩
  · obtain ⟨h1, h2, h3⟩ := ha
    exact ⟨fun r hr => by rw [h1 r hr, updateState_preserved _ _ hr], h2, h3⟩
  · obtain ⟨h1, h2⟩ := hq
    simp only [updateState_gpr, updateState_mem, reduceCtorEq, ite_false, ite_true,
      toNat_rate hr] at h1 h2
    exact ⟨h1, h2⟩
  · obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hp
    simp only [Proof.Sha3.absorbPPC64LE, updateState_gpr, updateState_sp, reduceCtorEq, ite_false,
      ite_true]
    exact ⟨p1, trivial, p2, p3, p4, p5, p6⟩

theorem update_verified {rate : Nat} (hr : rate ∈ rates) :
    Verified PPC64LE.target (update rate) (Spec.Sha3.updateContract PPC64LE.abi rate 48) := by
  have h0 : 0 < rate := by simp [rates] at hr; omega
  refine (update_verified' hr).of_implies
    { pre := by sig_implies_pre [Spec.Sha3.updateContract, Spec.Sha3.updateSig, Spec.Sha3.updatePre,
          Spec.Sha3.updatePost, updatePPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      post := by sig_implies_post [Spec.Sha3.updateContract, Spec.Sha3.updateSig, Spec.Sha3.updatePre,
          Spec.Sha3.updatePost, updatePPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      pub := by sig_implies_pub [Spec.Sha3.updateContract, Spec.Sha3.updateSig, Spec.Sha3.updatePre,
          Spec.Sha3.updatePost, updatePPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      sat := ?_ }
  refine ⟨updateSat, ?_⟩
  sig_pre [Spec.Sha3.updateContract, Spec.Sha3.updateSig, Spec.Sha3.updatePre, Spec.Sha3.updatePost,
    PPC64LE.abi, PPC64LE.argRegs, updateSat, Stream.absorbSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact h0

/-! ## SHAKE's `finalize` -/

/-- SHAKE's `finalize`'s contract on PPC64LE for `X`, with its working space
passed in `r5` (`state = r3, pos = r4, scratch = r5`). -/
def xofPadPPC64LE (X : Xof) : Contract PPC64LE.isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, 200⟩
    let scratch : Region := ⟨s.gpr .r5, 640⟩
    let stack : Region := ⟨s.sp - 48, 48⟩
    s.rd = [] ∧ s.wr = [state, scratch] ∧ state.Disjoint scratch ∧
    48 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint scratch ∧
    (s.gpr .r4).toNat < X.rate
  post s s' := ∀ msg, Repr s.mem (s.gpr .r3) X.rate msg →
    (s.gpr .r4).toNat = msg.length % X.rate → XofRepr s'.mem (s.gpr .r3) X.rate 0 X.xof msg 0
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.sp = s₂.sp

/-- The state after `xofPadArgs rate`. -/
def xofPadState (rate : Nat) (s : State) : State :=
  (((s.write .r7 (s.gpr .r5)).write .r5 (s.gpr .r4)).write .r4 (BitVec.ofNat 64 rate)).write .r6
    (BitVec.ofNat 64 0x1f)

theorem xofPadArgs_run {rate : Nat} (hr : rate < 2 ^ 15) (s : State) :
    execBlock isa (xofPadArgs rate) s = some (xofPadState rate s, []) := by
  simp [xofPadArgs, xofPadState, execBlock, isa, exec, Impl.Sha3.PPC64LE.Stream.mov, addrs, hr,
    State.write]

theorem xofPadState_gpr (rate : Nat) (s : State) (r : Reg) :
    (xofPadState rate s).gpr r =
      if r = .r6 then BitVec.ofNat 64 0x1f else if r = .r4 then BitVec.ofNat 64 rate
      else if r = .r5 then s.gpr .r4 else if r = .r7 then s.gpr .r5 else s.gpr r := by
  simp only [xofPadState, State.write]

@[simp] theorem xofPadState_mem (rate : Nat) (s : State) : (xofPadState rate s).mem = s.mem := rfl
@[simp] theorem xofPadState_rd (rate : Nat) (s : State) : (xofPadState rate s).rd = s.rd := rfl
@[simp] theorem xofPadState_wr (rate : Nat) (s : State) : (xofPadState rate s).wr = s.wr := rfl
@[simp] theorem xofPadState_sp (rate : Nat) (s : State) : (xofPadState rate s).sp = s.sp := rfl
@[simp] theorem xofPadState_lr (rate : Nat) (s : State) : (xofPadState rate s).lr = s.lr := rfl

theorem pad_sat : ∃ s, Proof.Sha3.padPPC64LE.pre s := by
  implies_sat [Proof.Sha3.padPPC64LE, rates] [Stream.padSat] using Stream.padSat

/-- A state satisfying `xofPadPPC64LE`'s precondition. -/
def xofPadSat : State :=
  { Stream.padSat with gpr := fun r => match r with | .r3 => 0x1000 | .r5 => 0x3000 | _ => 0 }

theorem xofPad_verified' {X : Xof} (hX : xofSponge X) (hr : X.rate ∈ rates) :
    Verified PPC64LE.target (.seq (.block (xofPadArgs X.rate)) Impl.Sha3.PPC64LE.Stream.pad)
      (xofPadPPC64LE X) := by
  have h0 : 0 < X.rate := by simp [rates] at hr; omega
  have hv : Verified PPC64LE.target Impl.Sha3.PPC64LE.Stream.pad Proof.Sha3.padPPC64LE :=
    Verified.of_correct Stream.pad_correct Stream.pad_ct (Contract.Implies.refl pad_sat)
  have hsuf : (BitVec.ofNat 64 0x1f).setWidth 8 = Spec.Sha3.shakeSuffix := by decide
  refine Verified.of_prologue hv (xofPadState X.rate) (fun s _ => xofPadArgs_run (rate_lt hr) s)
    (fun s hs => ?_) (fun s s' _ ha => ?_) (fun s s' _ hq => ?_) (fun s₁ s₂ _ _ hp => ?_)
    ⟨xofPadSat, rfl, rfl, Region.disjoint_of_sep (by decide), by decide,
      Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), h0⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hs
    simp only [Proof.Sha3.padPPC64LE, xofPadState_gpr, xofPadState_rd, xofPadState_wr,
      xofPadState_sp, reduceCtorEq, ite_false, ite_true, toNat_rate hr]
    exact ⟨h1, h2, h3, h4, h5, h6, hr, h7⟩
  · obtain ⟨h1, h2, h3⟩ := ha
    refine ⟨fun r hr => ?_, h2, h3⟩
    obtain ⟨h4, h5, h6, h7, -⟩ := preserved_ne r hr
    rw [h1 r hr, xofPadState_gpr]
    simp only [h4, h5, h6, h7, ite_false]
  · intro msg hm hp
    simp only [Proof.Sha3.padPPC64LE, xofPadState_gpr, xofPadState_mem, reduceCtorEq, ite_false,
      ite_true, toNat_rate hr, hsuf] at hq
    exact xofRepr_pad hX (hq msg hm hp)
  · obtain ⟨p1, p2, p3, p4⟩ := hp
    simp only [Proof.Sha3.padPPC64LE, xofPadState_gpr, xofPadState_sp, reduceCtorEq, ite_false,
      ite_true]
    exact ⟨p1, trivial, p2, p3, p4⟩

theorem xofPad_verified {X : Xof} (hX : xofSponge X) (hr : X.rate ∈ rates) :
    Verified PPC64LE.target (.seq (.block (xofPadArgs X.rate)) Impl.Sha3.PPC64LE.Stream.pad)
      (xofFinalizeScratchContract PPC64LE.abi X 48) := by
  have h0 : 0 < X.rate := by simp [rates] at hr; omega
  refine (xofPad_verified' hX hr).of_implies
    { pre := by sig_implies_pre [VG.Proof.Sha3.Instances.xofFinalizeScratchContract,
          VG.Proof.Sha3.Instances.xofFinalizeScratchSig, Spec.Sha3.xofFinalizePre,
          Spec.Sha3.xofFinalizePost, xofPadPPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      post := by sig_implies_post [VG.Proof.Sha3.Instances.xofFinalizeScratchContract,
          VG.Proof.Sha3.Instances.xofFinalizeScratchSig, Spec.Sha3.xofFinalizePre,
          Spec.Sha3.xofFinalizePost, xofPadPPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      pub := by sig_implies_pub [VG.Proof.Sha3.Instances.xofFinalizeScratchContract,
          VG.Proof.Sha3.Instances.xofFinalizeScratchSig, Spec.Sha3.xofFinalizePre,
          Spec.Sha3.xofFinalizePost, xofPadPPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      sat := ?_ }
  refine ⟨xofPadSat, ?_⟩
  sig_pre [VG.Proof.Sha3.Instances.xofFinalizeScratchContract,
    VG.Proof.Sha3.Instances.xofFinalizeScratchSig, Spec.Sha3.xofFinalizePre,
    Spec.Sha3.xofFinalizePost, PPC64LE.abi, PPC64LE.argRegs, xofPadSat, Stream.padSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact h0

/-- A state satisfying SHAKE's `finalize`'s precondition, with no working space. -/
def xofFinalizeSat : State := { xofPadSat with wr := [⟨0x1000, 200⟩] }

theorem xofFinalize_verified {X : Xof} (hX : xofSponge X) (hr : X.rate ∈ rates) :
    Verified PPC64LE.target (xofFinalize X.rate) (Spec.Sha3.xofFinalizeContract PPC64LE.abi X (48 + 672)) := by
  have h0 : 0 < X.rate := by simp [rates] at hr; omega
  refine PPC64LE.Verified.stackScratch (sig := Spec.Sha3.xofFinalizeSig) (nm := "scratch") (e := .u64)
    (n := 80) (pre := Spec.Sha3.xofFinalizePre X PPC64LE.abi.ptrBits)
    (post := Spec.Sha3.xofFinalizePost X PPC64LE.abi.ptrBits) (wa := true) (stack := 48)
    (bytes := 672) (xofPad_verified hX hr) (by decide) (by decide)
    (VG.Proof.Sha3.Instances.xofFinalizePre_local _ X) (VG.Proof.Sha3.Instances.xofFinalizePost_local _ X)
    ⟨xofFinalizeSat, ?_⟩
  sig_pre [Spec.Sha3.xofFinalizeContract, Spec.Sha3.xofFinalizeSig, Spec.Sha3.xofFinalizePre,
    Spec.Sha3.xofFinalizePost, PPC64LE.abi, PPC64LE.argRegs, xofFinalizeSat, xofPadSat,
    Stream.padSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact h0

/-! ## SHAKE's `squeeze` -/

/-- SHAKE's `squeeze`'s contract on PPC64LE for `X`, with its working space
passed in `r7` (`state = r3, pos = r4, out = r5, outlen = r6, scratch = r7`). -/
def xofSqueezePPC64LE (X : Xof) : Contract PPC64LE.isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, 200⟩
    let out : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
    let scratch : Region := ⟨s.gpr .r7, 640⟩
    let stack : Region := ⟨s.sp - 48, 48⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    48 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    (s.gpr .r4).toNat ≤ X.rate
  post s s' :=
    (∀ msg n, XofRepr s.mem (s.gpr .r3) X.rate (s.gpr .r4).toNat X.xof msg n →
      bytesAt s'.mem (s.gpr .r5) (s.gpr .r6).toNat = (X.xof msg (n + (s.gpr .r6).toNat)).drop n ∧
      XofRepr s'.mem (s.gpr .r3) X.rate (s'.gpr .r3).toNat X.xof msg (n + (s.gpr .r6).toNat)) ∧
    (s'.gpr .r3).toNat ≤ X.rate
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.sp = s₂.sp

theorem squeeze_sat : ∃ s, Proof.Sha3.squeezePPC64LE.pre s := by
  implies_sat [Proof.Sha3.squeezePPC64LE, rates] [Stream.squeezeSat] using Stream.squeezeSat

/-- A state satisfying `xofSqueezePPC64LE`'s precondition (with no output). -/
def xofSqueezeSat : State :=
  { Stream.squeezeSat with
    gpr := fun r => match r with | .r3 => 0x1000 | .r5 => 0x2000 | .r7 => 0x3000 | _ => 0 }

theorem xofSqueeze_verified' {X : Xof} (hr : X.rate ∈ rates) :
    Verified PPC64LE.target (.seq (.block (updateArgs X.rate)) Impl.Sha3.PPC64LE.Stream.squeeze)
      (xofSqueezePPC64LE X) := by
  have hv : Verified PPC64LE.target Impl.Sha3.PPC64LE.Stream.squeeze Proof.Sha3.squeezePPC64LE :=
    Verified.of_correct Stream.squeeze_correct Stream.squeeze_ct (Contract.Implies.refl squeeze_sat)
  refine Verified.of_prologue hv (updateState X.rate) (fun s _ => updateArgs_run (rate_lt hr) s)
    (fun s hs => ?_) (fun s s' _ ha => ?_) (fun s s' _ hq => ?_) (fun s₁ s₂ _ _ hp => ?_)
    ⟨xofSqueezeSat, rfl, rfl, Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
      Region.disjoint_of_sep (by decide), by decide, Region.disjoint_of_sep (by decide),
      Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Nat.zero_le _⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hs
    simp only [Proof.Sha3.squeezePPC64LE, updateState_gpr, updateState_rd, updateState_wr,
      updateState_sp, reduceCtorEq, ite_false, ite_true, toNat_rate hr]
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, hr, h10⟩
  · obtain ⟨h1, h2, h3⟩ := ha
    exact ⟨fun r hr => by rw [h1 r hr, updateState_preserved _ _ hr], h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := hq
    simp only [updateState_gpr, updateState_mem, reduceCtorEq, ite_false, ite_true,
      toNat_rate hr] at h1 h2 h3
    exact ⟨fun msg n hR => xofRepr_squeeze hR h1 h3, h2⟩
  · obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hp
    simp only [Proof.Sha3.squeezePPC64LE, updateState_gpr, updateState_sp, reduceCtorEq, ite_false,
      ite_true]
    exact ⟨p1, trivial, p2, p3, p4, p5, p6⟩

theorem xofSqueezeS_verified {X : Xof} (hr : X.rate ∈ rates) :
    Verified PPC64LE.target (.seq (.block (updateArgs X.rate)) Impl.Sha3.PPC64LE.Stream.squeeze)
      (xofSqueezeScratchContract PPC64LE.abi X 48) := by
  refine (xofSqueeze_verified' hr).of_implies
    { pre := by sig_implies_pre [VG.Proof.Sha3.Instances.xofSqueezeScratchContract,
          VG.Proof.Sha3.Instances.xofSqueezeScratchSig, Spec.Sha3.xofSqueezePre,
          Spec.Sha3.xofSqueezePost, xofSqueezePPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      post := by sig_implies_post [VG.Proof.Sha3.Instances.xofSqueezeScratchContract,
          VG.Proof.Sha3.Instances.xofSqueezeScratchSig, Spec.Sha3.xofSqueezePre,
          Spec.Sha3.xofSqueezePost, xofSqueezePPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      pub := by sig_implies_pub [VG.Proof.Sha3.Instances.xofSqueezeScratchContract,
          VG.Proof.Sha3.Instances.xofSqueezeScratchSig, Spec.Sha3.xofSqueezePre,
          Spec.Sha3.xofSqueezePost, xofSqueezePPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      sat := ?_ }
  refine ⟨xofSqueezeSat, ?_⟩
  sig_pre [VG.Proof.Sha3.Instances.xofSqueezeScratchContract,
    VG.Proof.Sha3.Instances.xofSqueezeScratchSig, Spec.Sha3.xofSqueezePre,
    Spec.Sha3.xofSqueezePost, PPC64LE.abi, PPC64LE.argRegs, xofSqueezeSat, Stream.squeezeSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Nat.zero_le _

/-- A state satisfying SHAKE's `squeeze`'s precondition, with no working space. -/
def xofSqueezeTopSat : State := { xofSqueezeSat with wr := [⟨0x1000, 200⟩, ⟨0x2000, 0⟩] }

theorem xofSqueeze_verified {X : Xof} (hr : X.rate ∈ rates) :
    Verified PPC64LE.target (xofSqueeze X.rate) (Spec.Sha3.xofSqueezeContract PPC64LE.abi X (48 + 672)) := by
  refine PPC64LE.Verified.stackScratch (sig := Spec.Sha3.xofSqueezeSig) (nm := "scratch") (e := .u64)
    (n := 80) (pre := Spec.Sha3.xofSqueezePre X PPC64LE.abi.ptrBits)
    (post := Spec.Sha3.xofSqueezePost X PPC64LE.abi.ptrBits) (wa := true) (stack := 48)
    (bytes := 672) (xofSqueezeS_verified hr) (by decide) (by decide)
    (VG.Proof.Sha3.Instances.xofSqueezePre_local _ X) (VG.Proof.Sha3.Instances.xofSqueezePost_local _ X)
    ⟨xofSqueezeTopSat, ?_⟩
  sig_pre [Spec.Sha3.xofSqueezeContract, Spec.Sha3.xofSqueezeSig, Spec.Sha3.xofSqueezePre,
    Spec.Sha3.xofSqueezePost, PPC64LE.abi, PPC64LE.argRegs, xofSqueezeTopSat, xofSqueezeSat,
    Stream.squeezeSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Nat.zero_le _

/-! ## SHA-3's `finalize` -/

/-- SHA-3's `finalize`'s contract on PPC64LE for `H`, with its working space
(672 bytes) passed in `r6` (`state = r3, pos = r4, out = r5, scratch = r6`);
its calls use the 48 bytes below the stack pointer. -/
def finPPC64LE (H : Spec.Sha3.HashFn) : Contract PPC64LE.isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, 200⟩
    let out : Region := ⟨s.gpr .r5, H.len⟩
    let scratch : Region := ⟨s.gpr .r6, 672⟩
    let stack : Region := ⟨s.sp - 48, 48⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    48 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    (s.gpr .r4).toNat < H.rate
  post s s' := ∀ msg, Repr s.mem (s.gpr .r3) H.rate msg →
    (s.gpr .r4).toNat = msg.length % H.rate → bytesAt s'.mem (s.gpr .r5) H.len = H.digest msg
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp

/-- Where `finalize`'s buffers are, and the 48 bytes of stack below the
stack pointer at `K + 48`. -/
structure Lay (st op sc K : Addr) (len : Nat) : Prop where
  st_op : Region.Disjoint ⟨st, 200⟩ ⟨op, len⟩
  st_sc : Region.Disjoint ⟨st, 200⟩ ⟨sc, 672⟩
  op_sc : Region.Disjoint ⟨op, len⟩ ⟨sc, 672⟩
  stk_st : Region.Disjoint ⟨K, 48⟩ ⟨st, 200⟩
  stk_op : Region.Disjoint ⟨K, 48⟩ ⟨op, len⟩
  stk_sc : Region.Disjoint ⟨K, 48⟩ ⟨sc, 672⟩

theorem sub_prefix (p : Addr) {n k : Nat} (h : n ≤ k) : Region.Sub ⟨p, n⟩ ⟨p, k⟩ :=
  fun _ hx => by simp only [Region.Contains] at hx ⊢; omega

theorem stateAt_frame {rs : List Region} {m m' : Mem} {p : Addr} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 200⟩ r) : stateAt m' p = stateAt m p :=
  Proof.Sha3.stateAt_congr fun _ hi => hf.bytes (R := ⟨p, 200⟩) hd (by show 200 ≤ 2 ^ 64; decide) hi

theorem readW_frame {rs : List Region} {m m' : Mem} {a : Addr} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨a, 8⟩ r) : m'.readW a 64 = m.readW a 64 :=
  hf.readW (r := ⟨a, 8⟩) (Region.contains_self _ _) hd (by decide)

theorem in_scr {s : State} {sc : Addr} {d : Nat} (hd : d + 8 ≤ 672) (hw : ⟨sc, 672⟩ ∈ s.wr) :
    InRegions s.wr (sc + BitVec.ofNat 64 d) 8 :=
  ⟨⟨sc, 672⟩, hw, Offset.contains_base _ (by omega) (by omega)⟩

theorem in_scr' {s : State} {sc : Addr} {d : Nat} (hd : d + 8 ≤ 672) (hw : ⟨sc, 672⟩ ∈ s.wr) :
    InRegions (s.rd ++ s.wr) (sc + BitVec.ofNat 64 d) 8 :=
  let ⟨r, hr, hc⟩ := in_scr (s := s) hd hw
  ⟨r, List.mem_append_right _ hr, hc⟩

theorem wcons {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

theorem exec_mov {s : State} {d n : Reg} (hn : n ≠ .r0 := by decide) :
    exec (Impl.Sha3.PPC64LE.Stream.mov d n) s = some (s.write d (s.gpr n)) := by
  rw [Impl.Sha3.PPC64LE.Stream.mov, exec_addi' (by decide) hn, BitVec.add_zero]

/-- After `finPadArgs`. -/
theorem finPad_ok {rate : Nat} (hr : rate < 2 ^ 15) {s : State} (hw : ⟨s.gpr .r6, 672⟩ ∈ s.wr) :
    WP isa (.block (finPadArgs rate)) s fun t =>
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.lr = s.lr ∧
      t.mem = (((s.mem.writeW (s.gpr .r6 + BitVec.ofNat 64 664) s.lr).writeW
        (s.gpr .r6 + BitVec.ofNat 64 640) (s.gpr .r29)).writeW (s.gpr .r6 + BitVec.ofNat 64 648)
        (s.gpr .r30)).writeW (s.gpr .r6 + BitVec.ofNat 64 656) (s.gpr .r31) ∧
      t.gpr .r3 = s.gpr .r3 ∧ t.gpr .r29 = s.gpr .r3 ∧ t.gpr .r30 = s.gpr .r5 ∧
      t.gpr .r31 = s.gpr .r6 ∧ t.gpr .r5 = s.gpr .r4 ∧ t.gpr .r4 = BitVec.ofNat 64 rate ∧
      t.gpr .r6 = BitVec.ofNat 64 0x06 ∧ t.gpr .r7 = s.gpr .r6 ∧
      ∀ r ∈ preserved, r ≠ .r29 → r ≠ .r30 → r ≠ .r31 → t.gpr r = s.gpr r := by
  have h1 := in_scr (s := s) (d := 664) (by omega) hw
  have h2 := in_scr (s := s) (d := 640) (by omega) hw
  have h3 := in_scr (s := s) (d := 648) (by omega) hw
  have h4 := in_scr (s := s) (d := 656) (by omega) hw
  unfold finPadArgs
  refine wcons exec_mflr (wcons (exec_std (by decide) (by simpa [RegUpd.wr_write, RegUpd.gpr_write] using h1)) (wcons
    (exec_std (by decide) (by simpa [RegUpd.wr_write, RegUpd.gpr_write] using h2)) (wcons (exec_std (by decide) (by simpa [RegUpd.wr_write, RegUpd.gpr_write] using h3))
    (wcons (exec_std (by decide) (by simpa [RegUpd.wr_write, RegUpd.gpr_write] using h4)) (wcons exec_mov (wcons exec_mov (wcons exec_mov
    (wcons exec_mov (wcons (exec_li hr) (wcons (exec_li (by decide)) (wcons exec_mov
    (WP.block_nil ?_))))))))))))
  simp only [RegUpd.gpr_write, RegUpd.mem_write, RegUpd.wr_write, RegUpd.rd_write, RegUpd.sp_write,
    RegUpd.lr_write, reduceCtorEq, ite_true, ite_false]
  iterate 13 refine ⟨by first | trivial | rfl, ?_⟩
  intro r hr h29 h30 h31
  have hne : r ≠ .r0 ∧ r ≠ .r4 ∧ r ≠ .r5 ∧ r ≠ .r6 ∧ r ≠ .r7 := by revert r; decide
  simp only [h29, h30, h31, hne.1, hne.2.1, hne.2.2.1, hne.2.2.2.1, hne.2.2.2.2, ite_false]

theorem pad_fdepth : Impl.Sha3.PPC64LE.Stream.pad.fdepth = 1 := by decide +kernel
theorem squeeze_fdepth : Impl.Sha3.PPC64LE.Stream.squeeze.fdepth = 1 := by decide +kernel

theorem gpr_ce (t : State) (rd wr : List Region) {r : Reg} (h : r ∉ linkRegs := by decide) :
    (t.callEntry.withRegions rd wr).gpr r = t.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h]

/-- `pad`'s precondition at the call, narrowed to the state and the first
640 bytes of `scratch`. -/
theorem finPad_pre {st op sc K : Addr} {len rate : Nat} (hL : Lay st op sc K len) (hr : rate ∈ rates)
    {t : State} (hdi : t.gpr .r3 = st) (hsi : t.gpr .r4 = BitVec.ofNat 64 rate)
    (hdx : (t.gpr .r5).toNat < rate) (h7 : t.gpr .r7 = sc) (hsp : t.sp = K + 48)
    (h48 : 48 ≤ t.sp.toNat) :
    Proof.Sha3.padPPC64LE.pre (t.callEntry.withRegions [] [⟨st, 200⟩, ⟨sc, 640⟩]) := by
  have hK : t.sp - 48 = K := by rw [hsp]; exact BitVec.add_sub_cancel _ _
  simp (disch := decide) only [Proof.Sha3.padPPC64LE, gpr_ce, State.withRegions_sp, State.callEntry_sp,
    State.withRegions_rd, State.withRegions_wr, hdi, hsi, h7, hK, toNat_rate hr]
  exact ⟨trivial, trivial, hL.st_sc.sub_right (sub_prefix sc (by omega)), h48, hL.stk_st,
    hL.stk_sc.sub_right (sub_prefix sc (by omega)), hr, hdx⟩

theorem finPad_cov {st op sc : Addr} {len : Nat} {t : State}
    (hwr : t.wr = [⟨st, 200⟩, ⟨op, len⟩, ⟨sc, 672⟩]) :
    Covers ([] ++ [⟨st, 200⟩, ⟨sc, 640⟩]) (t.rd ++ t.wr) ∧ Covers [⟨st, 200⟩, ⟨sc, 640⟩] t.wr := by
  refine ⟨Covers.of_sub fun r hr' => ?_, Covers.of_sub fun r hr' => ?_⟩
  all_goals
    simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact ⟨⟨st, 200⟩, by simp [hwr], 0, by simp, by simp⟩
    · exact ⟨⟨sc, 672⟩, by simp [hwr], 0, by simp, by simp⟩

/-- The call of `pad`, with SHA-3's suffix. -/
theorem finPadCall {st op sc K : Addr} {len rate : Nat} (hL : Lay st op sc K len) (hr : rate ∈ rates)
    {t : State} (hwr : t.wr = [⟨st, 200⟩, ⟨op, len⟩, ⟨sc, 672⟩])
    (hdi : t.gpr .r3 = st) (hsi : t.gpr .r4 = BitVec.ofNat 64 rate) (hdx : (t.gpr .r5).toNat < rate)
    (h6 : t.gpr .r6 = BitVec.ofNat 64 0x06) (h7 : t.gpr .r7 = sc) (hsp : t.sp = K + 48)
    (h48 : 48 ≤ t.sp.toNat) :
    WP isa (.call "vg_keccak_pad_scratch" Impl.Sha3.PPC64LE.Stream.pad) t fun u =>
      u.rd = t.rd ∧ u.wr = t.wr ∧ u.sp = t.sp ∧ (∀ r ∈ preserved, u.gpr r = t.gpr r) ∧
      Frame [⟨st, 200⟩, ⟨sc, 640⟩, ⟨K, 48⟩] t.mem u.mem ∧
      ∀ msg, Repr t.mem st rate msg → (t.gpr .r5).toNat = msg.length % rate →
        stateAt u.mem st = Spec.Sha3.absorb rate (Spec.Sha3.pad rate Spec.Sha3.sha3Suffix msg) := by
  have hK : t.sp - BitVec.ofNat 64 48 = K := by rw [hsp]; exact BitVec.add_sub_cancel _ _
  refine WP.callF (k := Proof.Sha3.padPPC64LE) Stream.pad_correct (rd := []) (wr := [⟨st, 200⟩, ⟨sc, 640⟩])
    (finPad_pre hL hr hdi hsi hdx h7 hsp h48) (finPad_cov hwr).1 (finPad_cov hwr).2
    (fun u h1 h2 h3 h4 h5 hpost => ⟨h1, h2, h3, h5, by rw [pad_fdepth] at h4; simpa [below, hK] using h4,
      fun msg hm hp => ?_⟩)
  simp (disch := decide) only [Proof.Sha3.padPPC64LE, gpr_ce, State.withRegions_mem, State.callEntry_mem, hdi, hsi, h6,
    toNat_rate hr] at hpost
  rw [hpost msg hm hp]
  rfl

/-- `squeeze`'s precondition at the call. -/
theorem finSqz_pre {st op sc K : Addr} {len rate : Nat} (hL : Lay st op sc K len) (hr : rate ∈ rates)
    (hl : len < 2 ^ 15) {t : State} (hdi : t.gpr .r3 = st) (hsi : t.gpr .r4 = BitVec.ofNat 64 rate)
    (hdx : t.gpr .r5 = BitVec.ofNat 64 0) (h6 : t.gpr .r6 = op) (h7 : t.gpr .r7 = BitVec.ofNat 64 len)
    (h8 : t.gpr .r8 = sc) (hsp : t.sp = K + 48) (h48 : 48 ≤ t.sp.toNat) :
    Proof.Sha3.squeezePPC64LE.pre
      (t.callEntry.withRegions [] [⟨st, 200⟩, ⟨op, len⟩, ⟨sc, 640⟩]) := by
  have hK : t.sp - 48 = K := by rw [hsp]; exact BitVec.add_sub_cancel _ _
  have hl' : (BitVec.ofNat 64 len).toNat = len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp (disch := decide) only [Proof.Sha3.squeezePPC64LE, gpr_ce, State.withRegions_sp, State.callEntry_sp,
    State.withRegions_rd, State.withRegions_wr, hdi, hsi, hdx, h6, h7, h8, hK, toNat_rate hr, hl']
  exact ⟨trivial, trivial, hL.st_op, hL.st_sc.sub_right (sub_prefix sc (by omega)),
    hL.op_sc.sub_right (sub_prefix sc (by omega)), h48, hL.stk_st, hL.stk_op,
    hL.stk_sc.sub_right (sub_prefix sc (by omega)), hr, by simp⟩

theorem finSqz_cov {st op sc : Addr} {len : Nat} {t : State}
    (hwr : t.wr = [⟨st, 200⟩, ⟨op, len⟩, ⟨sc, 672⟩]) :
    Covers ([] ++ [⟨st, 200⟩, ⟨op, len⟩, ⟨sc, 640⟩]) (t.rd ++ t.wr) ∧
      Covers [⟨st, 200⟩, ⟨op, len⟩, ⟨sc, 640⟩] t.wr := by
  refine ⟨Covers.of_sub fun r hr' => ?_, Covers.of_sub fun r hr' => ?_⟩
  all_goals
    simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact ⟨⟨st, 200⟩, by simp [hwr], 0, by simp, by simp⟩
    · exact ⟨⟨op, len⟩, by simp [hwr], 0, by simp, by simp⟩
    · exact ⟨⟨sc, 672⟩, by simp [hwr], 0, by simp, by simp⟩

/-- The call of `squeeze`, from position 0, for `len` bytes into `out`. -/
theorem finSqzCall {st op sc K : Addr} {len rate : Nat} (hL : Lay st op sc K len) (hr : rate ∈ rates)
    (hl : len < 2 ^ 15) {t : State} (hwr : t.wr = [⟨st, 200⟩, ⟨op, len⟩, ⟨sc, 672⟩])
    (hdi : t.gpr .r3 = st) (hsi : t.gpr .r4 = BitVec.ofNat 64 rate) (hdx : t.gpr .r5 = BitVec.ofNat 64 0)
    (h6 : t.gpr .r6 = op) (h7 : t.gpr .r7 = BitVec.ofNat 64 len) (h8 : t.gpr .r8 = sc)
    (hsp : t.sp = K + 48) (h48 : 48 ≤ t.sp.toNat) :
    WP isa (.call "vg_keccak_squeeze_scratch" Impl.Sha3.PPC64LE.Stream.squeeze) t fun u =>
      u.rd = t.rd ∧ u.wr = t.wr ∧ u.sp = t.sp ∧ (∀ r ∈ preserved, u.gpr r = t.gpr r) ∧
      Frame [⟨st, 200⟩, ⟨op, len⟩, ⟨sc, 640⟩, ⟨K, 48⟩] t.mem u.mem ∧
      bytesAt u.mem op len = Spec.Sha3.squeezeFrom rate (stateAt t.mem st) 0 len := by
  have hK : t.sp - BitVec.ofNat 64 48 = K := by rw [hsp]; exact BitVec.add_sub_cancel _ _
  have hl' : (BitVec.ofNat 64 len).toNat = len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine WP.callF (k := Proof.Sha3.squeezePPC64LE) Stream.squeeze_correct (rd := [])
    (wr := [⟨st, 200⟩, ⟨op, len⟩, ⟨sc, 640⟩])
    (finSqz_pre hL hr hl hdi hsi hdx h6 h7 h8 hsp h48) (finSqz_cov hwr).1 (finSqz_cov hwr).2
    (fun u h1 h2 h3 h4 h5 hpost => ⟨h1, h2, h3, h5,
      by rw [squeeze_fdepth] at h4; simpa [below, hK] using h4, ?_⟩)
  obtain ⟨hp, -⟩ := hpost
  simp (disch := decide) only [gpr_ce, State.withRegions_mem, State.callEntry_mem, hdi, hsi, hdx, h6, h7,
    toNat_rate hr, hl'] at hp
  rw [hp]
  simp

/-- After `finSqzArgs`. -/
theorem finSqz_ok {rate len : Nat} (hr : rate < 2 ^ 15) (hl : len < 2 ^ 15) (s : State) :
    WP isa (.block (finSqzArgs rate len)) s fun t =>
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.lr = s.lr ∧ t.mem = s.mem ∧
      t.gpr .r3 = s.gpr .r29 ∧ t.gpr .r4 = BitVec.ofNat 64 rate ∧ t.gpr .r5 = BitVec.ofNat 64 0 ∧
      t.gpr .r6 = s.gpr .r30 ∧ t.gpr .r7 = BitVec.ofNat 64 len ∧ t.gpr .r8 = s.gpr .r31 ∧
      ∀ r ∈ preserved, t.gpr r = s.gpr r := by
  unfold finSqzArgs
  refine wcons exec_mov (wcons (exec_li hr) (wcons (exec_li (by decide)) (wcons exec_mov
    (wcons (exec_li hl) (wcons exec_mov (WP.block_nil ?_))))))
  simp only [RegUpd.gpr_write, RegUpd.mem_write, RegUpd.wr_write, RegUpd.rd_write, RegUpd.sp_write,
    RegUpd.lr_write, reduceCtorEq, ite_true, ite_false]
  iterate 11 refine ⟨by first | trivial | rfl, ?_⟩
  intro r hr
  obtain ⟨h4, h5, h6, h7, h8⟩ := preserved_ne r hr
  have h3 : r ≠ .r3 := by revert r; decide
  simp only [h3, h4, h5, h6, h7, h8, ite_false]

/-- After `finRestore`, from a state with `r31` = `sc`. -/
theorem finRestore_ok {sc : Addr} {s : State} (h31 : s.gpr .r31 = sc)
    (h1 : InRegions (s.rd ++ s.wr) (sc + BitVec.ofNat 64 664) 8)
    (h2 : InRegions (s.rd ++ s.wr) (sc + BitVec.ofNat 64 640) 8)
    (h3 : InRegions (s.rd ++ s.wr) (sc + BitVec.ofNat 64 648) 8)
    (h4 : InRegions (s.rd ++ s.wr) (sc + BitVec.ofNat 64 656) 8) :
    WP isa (.block finRestore) s fun t =>
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.mem = s.mem ∧
      t.lr = s.mem.readW (sc + BitVec.ofNat 64 664) 64 ∧
      t.gpr .r29 = s.mem.readW (sc + BitVec.ofNat 64 640) 64 ∧
      t.gpr .r30 = s.mem.readW (sc + BitVec.ofNat 64 648) 64 ∧
      t.gpr .r31 = s.mem.readW (sc + BitVec.ofNat 64 656) 64 ∧
      ∀ r ∈ preserved, r ≠ .r29 → r ≠ .r30 → r ≠ .r31 → t.gpr r = s.gpr r := by
  unfold finRestore
  refine wcons (exec_ld (by decide) (by rw [h31]; exact h1)) (wcons exec_mtlr
    (wcons (exec_ld (by decide) (by simpa [RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.mem_write, h31] using h2))
    (wcons (exec_ld (by decide) (by simpa [RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.mem_write, h31] using h3))
    (wcons (exec_ld (by decide) (by simpa [RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.mem_write, h31] using h4)) (WP.block_nil ?_)))))
  simp only [RegUpd.gpr_write, RegUpd.mem_write, RegUpd.wr_write, RegUpd.rd_write, RegUpd.sp_write,
    RegUpd.lr_write, reduceCtorEq, ite_true, ite_false, h31]
  iterate 8 refine ⟨by first | trivial | rfl, ?_⟩
  intro r hr h29 h30 h31'
  have h0 : r ≠ .r0 := by revert r; decide
  simp only [h0, h29, h30, h31', ite_false]

/-- The layout `finPPC64LE`'s precondition gives, with `K = sp - 48`. -/
theorem lay_of_pre {H : Spec.Sha3.HashFn} {s : State} (hp : (finPPC64LE H).pre s) :
    Lay (s.gpr .r3) (s.gpr .r5) (s.gpr .r6) (s.sp - 48) H.len ∧ s.sp = s.sp - 48 + 48 := by
  obtain ⟨-, -, p3, p4, p5, -, p7, p8, p9, -⟩ := hp
  exact ⟨⟨p3, p4, p5, p7, p8, p9⟩, (BitVec.sub_add_cancel _ _).symm⟩

/-- `finBody` meets `finPPC64LE` and the ABI. -/
theorem finBody_correct {H : Spec.Sha3.HashFn} (hH : hashSponge H) (hr : H.rate ∈ rates)
    (hl : H.len < 2 ^ 15) {s : State} (hp : (finPPC64LE H).pre s) :
    WP isa (finBody H.rate H.len) s fun s' => abiPreserved s s' ∧ (finPPC64LE H).post s s' := by
  obtain ⟨hL, hsp⟩ := lay_of_pre hp
  obtain ⟨p1, p2, -, -, -, p6, -, -, -, p10⟩ := hp
  generalize s.sp - 48 = K at hL hsp
  have hw : ⟨s.gpr .r6, 672⟩ ∈ s.wr := by rw [p2]; simp
  -- The four saved words, beyond what the calls use.
  have hslot : ∀ d, 640 ≤ d → d + 8 ≤ 672 →
      ∀ r ∈ [(⟨s.gpr .r3, 200⟩ : Region), ⟨s.gpr .r5, H.len⟩, ⟨s.gpr .r6, 640⟩, ⟨K, 48⟩],
        Region.Disjoint ⟨s.gpr .r6 + BitVec.ofNat 64 d, 8⟩ r := by
    intro d h1 h2 r hr
    have hsub : Region.Sub ⟨s.gpr .r6 + BitVec.ofNat 64 d, 8⟩ ⟨s.gpr .r6, 672⟩ :=
      Offset.sub_base _ (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (hL.st_sc.symm).sub_left hsub
    · exact (hL.op_sc.symm).sub_left hsub
    · exact Offset.disjoint_base _ (by omega) (by omega)
    · exact (hL.stk_sc.symm).sub_left hsub
  refine WP.seq (WP.mono (finPad_ok (rate_lt hr) hw) fun t ⟨trd, twr, tsp, tlr, tmem, t3, t29, t30,
    t31, t5, t4, t6, t7, toth⟩ => ?_)
  refine WP.seq (WP.mono (finPadCall hL hr (by rw [twr, p2]) t3 t4 (by rw [t5]; exact p10) t6 t7
    (by rw [tsp, hsp]) (by rw [tsp]; exact p6))
    fun u ⟨urd, uwr, usp, upr, uf, upad⟩ => ?_)
  refine WP.seq (WP.mono (finSqz_ok (rate_lt hr) hl u) fun v ⟨vrd, vwr, vsp, vlr, vmem, v3, v4, v5, v6,
    v7, v8, vpr⟩ => ?_)
  have u29 : u.gpr .r29 = s.gpr .r3 := by rw [upr .r29 (by decide), t29]
  have u30 : u.gpr .r30 = s.gpr .r5 := by rw [upr .r30 (by decide), t30]
  have u31 : u.gpr .r31 = s.gpr .r6 := by rw [upr .r31 (by decide), t31]
  refine WP.seq (WP.mono (finSqzCall hL hr hl (by rw [vwr, uwr, twr, p2]) (by rw [v3, u29]) v4 v5
    (by rw [v6, u30]) v7 (by rw [v8, u31]) (by rw [vsp, usp, tsp, hsp])
    (by rw [vsp, usp, tsp]; exact p6))
    fun w ⟨wrd, wwr, wsp, wpr, wf, wout⟩ => ?_)
  have w31 : w.gpr .r31 = s.gpr .r6 := by rw [wpr .r31 (by decide), vpr .r31 (by decide), u31]
  have hin : ∀ d, d + 8 ≤ 672 → InRegions (w.rd ++ w.wr) (s.gpr .r6 + BitVec.ofNat 64 d) 8 :=
    fun d hd => in_scr' hd (by rw [wwr, vwr, uwr, twr]; exact hw)
  refine WP.mono (finRestore_ok w31 (hin 664 (by omega)) (hin 640 (by omega)) (hin 648 (by omega))
    (hin 656 (by omega))) fun x ⟨xrd, xwr, xsp, xmem, xlr, x29, x30, x31, xoth⟩ => ?_
  have fw : Frame [⟨s.gpr .r3, 200⟩, ⟨s.gpr .r5, H.len⟩, ⟨s.gpr .r6, 640⟩, ⟨K, 48⟩] t.mem w.mem := by
    refine (uf.mono fun r hr => ?_).trans (vmem ▸ wf)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl <;> simp
  have slot : ∀ d, 640 ≤ d → d + 8 ≤ 672 →
      w.mem.readW (s.gpr .r6 + BitVec.ofNat 64 d) 64 = t.mem.readW (s.gpr .r6 + BitVec.ofNat 64 d) 64 :=
    fun d h1 h2 => readW_frame fw (hslot d h1 h2)
  have sep : ∀ a b, 640 ≤ a → a + 8 ≤ 672 → 640 ≤ b → b + 8 ≤ 672 → a ≠ b → a % 8 = 0 → b % 8 = 0 →
      Mem.Sep (s.gpr .r6 + BitVec.ofNat 64 a) (64 / 8) (s.gpr .r6 + BitVec.ofNat 64 b) (64 / 8) :=
    fun a b _ _ _ _ hab ha hb => Offset.sep _ (by omega) (by omega) (by omega)
  have t664 : t.mem.readW (s.gpr .r6 + BitVec.ofNat 64 664) 64 = s.lr := by
    rw [tmem, Mem.readW_writeW_sep (sep 664 656 (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 664 648 (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 664 640 (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)) (by decide), Mem.readW_writeW_self64]
  have t640 : t.mem.readW (s.gpr .r6 + BitVec.ofNat 64 640) 64 = s.gpr .r29 := by
    rw [tmem, Mem.readW_writeW_sep (sep 640 656 (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 640 648 (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)) (by decide), Mem.readW_writeW_self64]
  have t648 : t.mem.readW (s.gpr .r6 + BitVec.ofNat 64 648) 64 = s.gpr .r30 := by
    rw [tmem, Mem.readW_writeW_sep (sep 648 656 (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)) (by decide), Mem.readW_writeW_self64]
  have t656 : t.mem.readW (s.gpr .r6 + BitVec.ofNat 64 656) 64 = s.gpr .r31 := by
    rw [tmem, Mem.readW_writeW_self64]
  have ft : Frame [⟨s.gpr .r6, 672⟩] s.mem t.mem := by
    rw [tmem]
    refine Frame.writeW (Frame.writeW (Frame.writeW (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
      ?_) (List.mem_singleton_self _) _ ?_) (List.mem_singleton_self _) _ ?_) (List.mem_singleton_self _) _ ?_
    all_goals exact Offset.contains_base _ (by omega) (by omega)
  refine ⟨⟨fun r hr => ?_, by rw [xsp, wsp, vsp, usp, tsp], ?_⟩, fun msg hm hpos => ?_⟩
  · by_cases h29 : r = .r29
    · subst h29; rw [x29, slot 640 (by omega) (by omega), t640]
    by_cases h30 : r = .r30
    · subst h30; rw [x30, slot 648 (by omega) (by omega), t648]
    by_cases h31 : r = .r31
    · subst h31; rw [x31, slot 656 (by omega) (by omega), t656]
    rw [xoth r hr h29 h30 h31, wpr r hr, vpr r hr, upr r hr, toth r hr h29 h30 h31]
  · rw [xlr, slot 664 (by omega) (by omega), t664]
  · have hst : stateAt t.mem (s.gpr .r3) = stateAt s.mem (s.gpr .r3) :=
      stateAt_frame ft (by intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hL.st_sc)
    have hpad := upad msg (by unfold Spec.Sha3.Repr; rw [hst]; exact hm) (by rw [t5]; exact hpos)
    show bytesAt x.mem (s.gpr .r5) H.len = H.digest msg
    rw [xmem, wout, vmem, hpad]
    exact digest_of_pad hH rfl

/-! ### Constant time -/

def G1 (rate : Nat) (σ t : State) : Prop :=
  t.rd = σ.rd ∧ t.wr = σ.wr ∧ t.gpr .r3 = σ.gpr .r3 ∧ t.gpr .r4 = BitVec.ofNat 64 rate ∧
    t.gpr .r5 = σ.gpr .r4 ∧ t.gpr .r6 = BitVec.ofNat 64 0x06 ∧ t.gpr .r7 = σ.gpr .r6 ∧
    t.gpr .r29 = σ.gpr .r3 ∧ t.gpr .r30 = σ.gpr .r5 ∧ t.gpr .r31 = σ.gpr .r6 ∧ t.sp = σ.sp

def G2 (σ u : State) : Prop :=
  u.rd = σ.rd ∧ u.wr = σ.wr ∧ u.gpr .r29 = σ.gpr .r3 ∧ u.gpr .r30 = σ.gpr .r5 ∧
    u.gpr .r31 = σ.gpr .r6 ∧ u.sp = σ.sp

def G3 (rate len : Nat) (σ v : State) : Prop :=
  v.rd = σ.rd ∧ v.wr = σ.wr ∧ v.gpr .r3 = σ.gpr .r3 ∧ v.gpr .r4 = BitVec.ofNat 64 rate ∧
    v.gpr .r5 = BitVec.ofNat 64 0 ∧ v.gpr .r6 = σ.gpr .r5 ∧ v.gpr .r7 = BitVec.ofNat 64 len ∧
    v.gpr .r8 = σ.gpr .r6 ∧ v.gpr .r31 = σ.gpr .r6 ∧ v.sp = σ.sp

theorem g1_ok {H : Spec.Sha3.HashFn} (hr : H.rate < 2 ^ 15) {σ : State} (hp : (finPPC64LE H).pre σ) :
    WP isa (.block (finPadArgs H.rate)) σ (G1 H.rate σ) :=
  WP.mono (finPad_ok hr (by rw [hp.2.1]; simp)) fun _ ⟨h1, h2, h3, _, _, h6, h7, h8, h9, h10, h11, h12, h13, _⟩ =>
    ⟨h1, h2, h6, h11, h10, h12, h13, h7, h8, h9, h3⟩

theorem g2_ok {H : Spec.Sha3.HashFn} (hr : H.rate ∈ rates) {σ t : State} (hp : (finPPC64LE H).pre σ)
    (h : G1 H.rate σ t) :
    WP isa (.call "vg_keccak_pad_scratch" Impl.Sha3.PPC64LE.Stream.pad) t (G2 σ) := by
  obtain ⟨hL, hsp⟩ := lay_of_pre hp
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  refine WP.mono (finPadCall hL hr (by rw [h2, hp.2.1]) h3 h4 (by rw [h5]; exact hp.2.2.2.2.2.2.2.2.2)
    h6 h7 (by rw [h11, ← hsp]) (by rw [h11]; exact hp.2.2.2.2.2.1)) fun u ⟨u1, u2, u3, u4, _, _⟩ =>
      ⟨by rw [u1, h1], by rw [u2, h2], by rw [u4 .r29 (by decide), h8], by rw [u4 .r30 (by decide), h9],
        by rw [u4 .r31 (by decide), h10], by rw [u3, h11]⟩

theorem g3_ok {H : Spec.Sha3.HashFn} (hr : H.rate < 2 ^ 15) (hl : H.len < 2 ^ 15) {σ u : State}
    (h : G2 σ u) : WP isa (.block (finSqzArgs H.rate H.len)) u (G3 H.rate H.len σ) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine WP.mono (finSqz_ok hr hl u) fun v ⟨v1, v2, v3, _, _, v6, v7, v8, v9, v10, v11, v12⟩ =>
    ⟨by rw [v1, h1], by rw [v2, h2], by rw [v6, h3], v7, v8, by rw [v9, h4], v10, by rw [v11, h5],
      by rw [v12 .r31 (by decide), h5], by rw [v3, h6]⟩

theorem g4_ok {H : Spec.Sha3.HashFn} (hr : H.rate ∈ rates) (hl : H.len < 2 ^ 15) {σ v : State}
    (hp : (finPPC64LE H).pre σ) (h : G3 H.rate H.len σ v) :
    WP isa (.call "vg_keccak_squeeze_scratch" Impl.Sha3.PPC64LE.Stream.squeeze) v
      fun w => w.gpr .r31 = σ.gpr .r6 ∧ w.sp = σ.sp := by
  obtain ⟨hL, hsp⟩ := lay_of_pre hp
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact WP.mono (finSqzCall hL hr hl (by rw [h2, hp.2.1]) h3 h4 h5 h6 h7 h8 (by rw [h10, ← hsp])
    (by rw [h10]; exact hp.2.2.2.2.2.1)) fun w ⟨_, _, w3, w4, _⟩ =>
      ⟨by rw [w4 .r31 (by decide), h9], by rw [w3, h10]⟩

theorem finBody_ct {H : Spec.Sha3.HashFn} (hr : H.rate ∈ rates) (hl : H.len < 2 ^ 15)
    {h₁ h₂ h₃ : VG.Taint.Hint PPC64LE.Taint.T}
    (hb₁ : (PPC64LE.taint.check (PPC64LE.Taint.ofRegs [.r3, .r4, .r5, .r6]) (.block (finPadArgs H.rate))
      h₁).isSome = true)
    (hb₂ : (PPC64LE.taint.check (PPC64LE.Taint.ofRegs []) (.block (finSqzArgs H.rate H.len)) h₂).isSome = true)
    (hb₃ : (PPC64LE.taint.check (PPC64LE.Taint.ofRegs [.r31]) (.block finRestore) h₃).isSome = true) :
    ConstantTime isa (finPPC64LE H).pre (finPPC64LE H).pub (finBody H.rate H.len) := by
  intro σ₁ σ₂ t₁ t₂ σ₁' σ₂' p₁ p₂ hp e₁ e₂
  obtain ⟨q3, q4, q5, q6, qsp⟩ := hp
  have hP : RelCT isa (fun a b => a = σ₁ ∧ b = σ₂) (finBody H.rate H.len) fun _ _ => True := by
    unfold finBody
    refine RelCT.seq (RelCT.wp (F₁ := G1 H.rate σ₁) (F₂ := G1 H.rate σ₂)
      (RelCT.taint (A := PPC64LE.taint) (PPC64LE.Taint.ofRegs [.r3, .r4, .r5, .r6])
        (fun a b ⟨ea, eb⟩ => by
          subst ea eb
          refine ⟨qsp, fun r hr => ?_⟩
          simp only [PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption) hb₁)
      fun a b ⟨ea, eb⟩ => by subst ea eb; exact ⟨g1_ok (rate_lt hr) p₁, g1_ok (rate_lt hr) p₂⟩) ?_
    refine RelCT.seq (RelCT.wp (F₁ := G2 σ₁) (F₂ := G2 σ₂)
      (RelCT.call Stream.pad_correct Stream.pad_ct [] [⟨σ₁.gpr .r3, 200⟩, ⟨σ₁.gpr .r6, 640⟩]
        fun a b ⟨_, ha, hb⟩ => ?_) fun a b ⟨_, ha, hb⟩ => ⟨g2_ok hr p₁ ha, g2_ok hr p₂ hb⟩) ?_
    · obtain ⟨hL₁, hs₁⟩ := lay_of_pre p₁
      obtain ⟨hL₂, hs₂⟩ := lay_of_pre p₂
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := ha
      obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := hb
      have pb := finPad_pre hL₂ hr b3 b4 (by rw [b5]; exact p₂.2.2.2.2.2.2.2.2.2) b7 (by rw [b11, ← hs₂])
        (by rw [b11]; exact p₂.2.2.2.2.2.1)
      rw [← q3, ← q6] at pb
      refine ⟨finPad_pre hL₁ hr a3 a4 (by rw [a5]; exact p₁.2.2.2.2.2.2.2.2.2) a7 (by rw [a11, ← hs₁])
        (by rw [a11]; exact p₁.2.2.2.2.2.1), pb, ?_, (finPad_cov (by rw [a2, p₁.2.1])).1,
        (finPad_cov (by rw [a2, p₁.2.1])).2, (finPad_cov (by rw [b2, p₂.2.1, ← q3, ← q5, ← q6])).1,
        (finPad_cov (by rw [b2, p₂.2.1, ← q3, ← q5, ← q6])).2⟩
      simp (disch := decide) only [Proof.Sha3.padPPC64LE, gpr_ce, State.withRegions_sp,
        State.callEntry_sp]
      exact ⟨by rw [a3, b3, q3], by rw [a4, b4], by rw [a5, b5, q4], by rw [a7, b7, q6],
        by rw [a11, b11, qsp]⟩
    refine RelCT.seq (RelCT.wp (F₁ := G3 H.rate H.len σ₁) (F₂ := G3 H.rate H.len σ₂)
      (RelCT.taint (A := PPC64LE.taint) (PPC64LE.Taint.ofRegs []) (fun a b ⟨_, ha, hb⟩ =>
        ⟨by rw [ha.2.2.2.2.2, hb.2.2.2.2.2, qsp], fun r h => by simp [PPC64LE.Taint.mem_ofRegs] at h⟩) hb₂)
      fun a b ⟨_, ha, hb⟩ => ⟨g3_ok (rate_lt hr) hl ha, g3_ok (rate_lt hr) hl hb⟩) ?_
    refine RelCT.seq (RelCT.wp (F₁ := fun w : State => w.gpr .r31 = σ₁.gpr .r6 ∧ w.sp = σ₁.sp)
      (F₂ := fun w : State => w.gpr .r31 = σ₂.gpr .r6 ∧ w.sp = σ₂.sp)
      (RelCT.call Stream.squeeze_correct Stream.squeeze_ct []
        [⟨σ₁.gpr .r3, 200⟩, ⟨σ₁.gpr .r5, H.len⟩, ⟨σ₁.gpr .r6, 640⟩] fun a b ⟨_, ha, hb⟩ => ?_)
      fun a b ⟨_, ha, hb⟩ => ⟨g4_ok hr hl p₁ ha, g4_ok hr hl p₂ hb⟩) ?_
    · obtain ⟨hL₁, hs₁⟩ := lay_of_pre p₁
      obtain ⟨hL₂, hs₂⟩ := lay_of_pre p₂
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := ha
      obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := hb
      have pb := finSqz_pre hL₂ hr hl b3 b4 b5 b6 b7 b8 (by rw [b10, ← hs₂]) (by rw [b10]; exact p₂.2.2.2.2.2.1)
      rw [← q3, ← q5, ← q6] at pb
      refine ⟨finSqz_pre hL₁ hr hl a3 a4 a5 a6 a7 a8 (by rw [a10, ← hs₁]) (by rw [a10]; exact p₁.2.2.2.2.2.1),
        pb, ?_, (finSqz_cov (by rw [a2, p₁.2.1])).1, (finSqz_cov (by rw [a2, p₁.2.1])).2,
        (finSqz_cov (by rw [b2, p₂.2.1, ← q3, ← q5, ← q6])).1,
        (finSqz_cov (by rw [b2, p₂.2.1, ← q3, ← q5, ← q6])).2⟩
      simp (disch := decide) only [Proof.Sha3.squeezePPC64LE, gpr_ce, State.withRegions_sp,
        State.callEntry_sp]
      exact ⟨by rw [a3, b3, q3], by rw [a4, b4], by rw [a5, b5], by rw [a6, b6, q5], by rw [a7, b7],
        by rw [a8, b8, q6], by rw [a10, b10, qsp]⟩
    exact RelCT.taint (A := PPC64LE.taint) (PPC64LE.Taint.ofRegs [.r31]) (fun a b ⟨_, ha, hb⟩ => ⟨by rw [ha.2, hb.2, qsp],
      fun r h => by simp [PPC64LE.Taint.mem_ofRegs] at h; subst h; rw [ha.1, hb.1, q6]⟩) hb₃
  exact (hP _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ### `Verified` -/

theorem finBody_verified {H : Spec.Sha3.HashFn} (hH : hashSponge H) (hr : H.rate ∈ rates)
    (hl : H.len < 2 ^ 15)
    (hct : ConstantTime isa (finPPC64LE H).pre (finPPC64LE H).pub (finBody H.rate H.len))
    (hsat : ∃ s, (finPPC64LE H).pre s) (hsat' : ∃ s, (finScratchContract PPC64LE.abi H 84 48).pre s) :
    Verified PPC64LE.target (finBody H.rate H.len) (finScratchContract PPC64LE.abi H 84 48) :=
  (Verified.of_correct (fun s hs => (finBody_correct hH hr hl hs).elim fun t ⟨s', he, h⟩ =>
      ⟨t, s', he, h.1, h.2⟩) hct (Contract.Implies.refl hsat)).of_implies
    { pre := by sig_implies_pre [VG.Proof.Sha3.Instances.finScratchContract,
          VG.Proof.Sha3.Instances.finScratchSig, Spec.Sha3.finalizePre, Spec.Sha3.finalizePost,
          finPPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      post := by sig_implies_post [VG.Proof.Sha3.Instances.finScratchContract,
          VG.Proof.Sha3.Instances.finScratchSig, Spec.Sha3.finalizePre, Spec.Sha3.finalizePost,
          finPPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      pub := by sig_implies_pub [VG.Proof.Sha3.Instances.finScratchContract,
          VG.Proof.Sha3.Instances.finScratchSig, Spec.Sha3.finalizePre, Spec.Sha3.finalizePost,
          finPPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      sat := hsat' }

theorem finalize_verified {H : Spec.Sha3.HashFn} (hH : hashSponge H) (hr : H.rate ∈ rates)
    (hl : H.len < 2 ^ 15)
    (hct : ConstantTime isa (finPPC64LE H).pre (finPPC64LE H).pub (finBody H.rate H.len))
    (hsat : ∃ s, (finPPC64LE H).pre s) (hsat' : ∃ s, (finScratchContract PPC64LE.abi H 84 48).pre s)
    (hsat'' : ∃ s, (Spec.Sha3.finalizeContract PPC64LE.abi H (48 + 704)).pre s) :
    Verified PPC64LE.target (finalize H.rate H.len) (Spec.Sha3.finalizeContract PPC64LE.abi H (48 + 704)) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Sha3.finalizeSig H.len) (nm := "scratch") (e := .u64)
    (n := 84) (pre := Spec.Sha3.finalizePre H PPC64LE.abi.ptrBits)
    (post := Spec.Sha3.finalizePost H PPC64LE.abi.ptrBits) (wa := true) (stack := 48)
    (bytes := 704) (finBody_verified hH hr hl hct hsat hsat') (by exact (by decide : 3 < 8))
    (by decide) (VG.Proof.Sha3.Instances.finalizePre_local _ H)
    (VG.Proof.Sha3.Instances.finalizePost_local _ H) hsat'' rfl

/-- A state satisfying `finPPC64LE`'s precondition. -/
def finSat (len : Nat) : State :=
  { Stream.padSat with
    gpr := fun r => match r with | .r3 => 0x1000 | .r5 => 0x2000 | .r6 => 0x3000 | _ => 0
    wr := [⟨0x1000, 200⟩, ⟨0x2000, len⟩, ⟨0x3000, 672⟩] }

/-- `finalize`'s constant time for an instance, from the taint analysis of
its blocks. -/
macro "fin_ct" : term => `(finBody_ct (by decide) (by decide) (by taint_decide) (by taint_decide)
  (by taint_decide))

theorem update_sha3_224 :
    Verified PPC64LE.target (update Spec.Sha3.hashSha3_224.rate) (Spec.Sha3.updateContract PPC64LE.abi Spec.Sha3.hashSha3_224.rate 48) :=
  update_verified (by decide)

theorem finalize_sha3_224 :
    Verified PPC64LE.target (finalize Spec.Sha3.hashSha3_224.rate Spec.Sha3.hashSha3_224.len)
      (Spec.Sha3.finalizeContract PPC64LE.abi Spec.Sha3.hashSha3_224 (48 + 704)) :=
  finalize_verified VG.Proof.Sha3.Instances.sha3_224_sponge (by decide) (by decide) fin_ct
    (by implies_sat [finPPC64LE, Spec.Sha3.hashSha3_224] [finSat, Stream.padSat] using finSat 28)
    (by implies_sat [VG.Proof.Sha3.Instances.finScratchContract, VG.Proof.Sha3.Instances.finScratchSig,
      Spec.Sha3.finalizePre, Spec.Sha3.finalizePost, PPC64LE.abi, PPC64LE.argRegs, Spec.Sha3.hashSha3_224]
      [finSat, Stream.padSat] using finSat 28)
    (by implies_sat [Spec.Sha3.finalizeContract, Spec.Sha3.finalizeSig, Spec.Sha3.finalizePre,
      Spec.Sha3.finalizePost, PPC64LE.abi, PPC64LE.argRegs, Spec.Sha3.hashSha3_224] [finSat, Stream.padSat]
      using { finSat 28 with wr := [⟨0x1000, 200⟩, ⟨0x2000, 28⟩] })

theorem update_sha3_256 :
    Verified PPC64LE.target (update Spec.Sha3.hashSha3_256.rate) (Spec.Sha3.updateContract PPC64LE.abi Spec.Sha3.hashSha3_256.rate 48) :=
  update_verified (by decide)

theorem finalize_sha3_256 :
    Verified PPC64LE.target (finalize Spec.Sha3.hashSha3_256.rate Spec.Sha3.hashSha3_256.len)
      (Spec.Sha3.finalizeContract PPC64LE.abi Spec.Sha3.hashSha3_256 (48 + 704)) :=
  finalize_verified VG.Proof.Sha3.Instances.sha3_256_sponge (by decide) (by decide) fin_ct
    (by implies_sat [finPPC64LE, Spec.Sha3.hashSha3_256] [finSat, Stream.padSat] using finSat 32)
    (by implies_sat [VG.Proof.Sha3.Instances.finScratchContract, VG.Proof.Sha3.Instances.finScratchSig,
      Spec.Sha3.finalizePre, Spec.Sha3.finalizePost, PPC64LE.abi, PPC64LE.argRegs, Spec.Sha3.hashSha3_256]
      [finSat, Stream.padSat] using finSat 32)
    (by implies_sat [Spec.Sha3.finalizeContract, Spec.Sha3.finalizeSig, Spec.Sha3.finalizePre,
      Spec.Sha3.finalizePost, PPC64LE.abi, PPC64LE.argRegs, Spec.Sha3.hashSha3_256] [finSat, Stream.padSat]
      using { finSat 32 with wr := [⟨0x1000, 200⟩, ⟨0x2000, 32⟩] })

theorem update_sha3_384 :
    Verified PPC64LE.target (update Spec.Sha3.hashSha3_384.rate) (Spec.Sha3.updateContract PPC64LE.abi Spec.Sha3.hashSha3_384.rate 48) :=
  update_verified (by decide)

theorem finalize_sha3_384 :
    Verified PPC64LE.target (finalize Spec.Sha3.hashSha3_384.rate Spec.Sha3.hashSha3_384.len)
      (Spec.Sha3.finalizeContract PPC64LE.abi Spec.Sha3.hashSha3_384 (48 + 704)) :=
  finalize_verified VG.Proof.Sha3.Instances.sha3_384_sponge (by decide) (by decide) fin_ct
    (by implies_sat [finPPC64LE, Spec.Sha3.hashSha3_384] [finSat, Stream.padSat] using finSat 48)
    (by implies_sat [VG.Proof.Sha3.Instances.finScratchContract, VG.Proof.Sha3.Instances.finScratchSig,
      Spec.Sha3.finalizePre, Spec.Sha3.finalizePost, PPC64LE.abi, PPC64LE.argRegs, Spec.Sha3.hashSha3_384]
      [finSat, Stream.padSat] using finSat 48)
    (by implies_sat [Spec.Sha3.finalizeContract, Spec.Sha3.finalizeSig, Spec.Sha3.finalizePre,
      Spec.Sha3.finalizePost, PPC64LE.abi, PPC64LE.argRegs, Spec.Sha3.hashSha3_384] [finSat, Stream.padSat]
      using { finSat 48 with wr := [⟨0x1000, 200⟩, ⟨0x2000, 48⟩] })

theorem update_sha3_512 :
    Verified PPC64LE.target (update Spec.Sha3.hashSha3_512.rate) (Spec.Sha3.updateContract PPC64LE.abi Spec.Sha3.hashSha3_512.rate 48) :=
  update_verified (by decide)

theorem finalize_sha3_512 :
    Verified PPC64LE.target (finalize Spec.Sha3.hashSha3_512.rate Spec.Sha3.hashSha3_512.len)
      (Spec.Sha3.finalizeContract PPC64LE.abi Spec.Sha3.hashSha3_512 (48 + 704)) :=
  finalize_verified VG.Proof.Sha3.Instances.sha3_512_sponge (by decide) (by decide) fin_ct
    (by implies_sat [finPPC64LE, Spec.Sha3.hashSha3_512] [finSat, Stream.padSat] using finSat 64)
    (by implies_sat [VG.Proof.Sha3.Instances.finScratchContract, VG.Proof.Sha3.Instances.finScratchSig,
      Spec.Sha3.finalizePre, Spec.Sha3.finalizePost, PPC64LE.abi, PPC64LE.argRegs, Spec.Sha3.hashSha3_512]
      [finSat, Stream.padSat] using finSat 64)
    (by implies_sat [Spec.Sha3.finalizeContract, Spec.Sha3.finalizeSig, Spec.Sha3.finalizePre,
      Spec.Sha3.finalizePost, PPC64LE.abi, PPC64LE.argRegs, Spec.Sha3.hashSha3_512] [finSat, Stream.padSat]
      using { finSat 64 with wr := [⟨0x1000, 200⟩, ⟨0x2000, 64⟩] })

theorem update_shake128 :
    Verified PPC64LE.target (update Spec.Sha3.xofShake128.rate) (Spec.Sha3.updateContract PPC64LE.abi Spec.Sha3.xofShake128.rate 48) :=
  update_verified (by decide)

theorem finalize_shake128 :
    Verified PPC64LE.target (xofFinalize Spec.Sha3.xofShake128.rate) (Spec.Sha3.xofFinalizeContract PPC64LE.abi Spec.Sha3.xofShake128 (48 + 672)) :=
  xofFinalize_verified VG.Proof.Sha3.Instances.shake128_sponge (by decide)

theorem squeeze_shake128 :
    Verified PPC64LE.target (xofSqueeze Spec.Sha3.xofShake128.rate) (Spec.Sha3.xofSqueezeContract PPC64LE.abi Spec.Sha3.xofShake128 (48 + 672)) :=
  xofSqueeze_verified (by decide)

theorem finalize_shake256 :
    Verified PPC64LE.target (xofFinalize Spec.Sha3.xofShake256.rate) (Spec.Sha3.xofFinalizeContract PPC64LE.abi Spec.Sha3.xofShake256 (48 + 672)) :=
  xofFinalize_verified VG.Proof.Sha3.Instances.shake256_sponge (by decide)

theorem squeeze_shake256 :
    Verified PPC64LE.target (xofSqueeze Spec.Sha3.xofShake256.rate) (Spec.Sha3.xofSqueezeContract PPC64LE.abi Spec.Sha3.xofShake256 (48 + 672)) :=
  xofSqueeze_verified (by decide)

end VG.Proof.Sha3.PPC64LE.Instances
