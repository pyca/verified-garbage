module

public import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Verified
public import VerifiedGarbage.Proof.Sha3.Instances
public import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
public import VerifiedGarbage.Impl.Sha3.RISCV64.Instances
public import VerifiedGarbage.Spec.Sha3.Instances
import VerifiedGarbage.Proof.Framework.Prologue
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT

meta import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Verified
meta import VerifiedGarbage.Proof.Sha3.Instances
meta import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
meta import VerifiedGarbage.Impl.Sha3.RISCV64.Instances
meta import VerifiedGarbage.Spec.Sha3.Instances
meta import VerifiedGarbage.Proof.Framework.Prologue
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Sha3.Stream
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.Call
meta import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelCT

/-!
# SHA-3 and SHAKE on RISC-V: the functions of each instance

As on x86-64 (`Proof/Sha3/X86_64/Instances.lean`): each runs the sponge's
code after a block that moves its arguments into the registers that code
takes them in and sets the rate (and suffix) (`Verified.of_prologue`).
-/

@[expose] public section

namespace VG.Proof.Sha3.RISCV64.Instances

open VG VG.RISCV64 VG.Impl.Sha3.RISCV64.Instances
open VG.Spec.Sha3 (Repr bytesAt rates stateAt XofRepr Xof)
open VG.Proof.Sha3.Instances (xofSponge hashSponge xofRepr_pad xofRepr_squeeze digest_of_pad
  finScratchContract)

theorem rate_lt {rate : Nat} (hr : rate ∈ rates) : rate < 2048 := by simp [rates] at hr; omega

theorem toNat_rate {rate : Nat} (hr : rate ∈ rates) : (BitVec.ofNat 64 rate).toNat = rate := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := rate_lt hr; omega)]

theorem ofInt_nat (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := BitVec.ofInt_natCast _ _

theorem preserved_ne : ∀ r ∈ preserved, r ≠ .a1 ∧ r ≠ .a2 ∧ r ≠ .a3 ∧ r ≠ .a4 ∧ r ≠ .a5 ∧ r ≠ .ra :=
  by decide

/-! ## `update` -/

/-- `update rate`'s contract on RISC-V, with the arguments in registers
(`state = a0, pos = a1, data = a2, len = a3, scratch = a4`): that of
`absorbWs` (`Proof.Sha3.absorbWsRISCV64`), with the rate `rate`. -/
def updateRISCV64 (rate : Nat) : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 200⟩
    let data : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
    let scratch : Region := ⟨s.gpr .a4, 640⟩
    let stack : Region := ⟨s.sp - 608, 608⟩
    s.rd = [data] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    (s.gpr .a4).toNat % 8 = 0 ∧ (s.gpr .a4).toNat + 640 ≤ 2 ^ 64 ∧
    s.sp.toNat % 16 = 0 ∧ 608 ≤ s.sp.toNat ∧
    stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch ∧
    (s.gpr .a1).toNat < rate
  post s s' :=
    (∀ msg, Repr s.mem (s.gpr .a0) rate msg → (s.gpr .a1).toNat = msg.length % rate →
      Repr s'.mem (s.gpr .a0) rate (msg ++ bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)) ∧
    (s'.gpr .a0).toNat = ((s.gpr .a1).toNat + (s.gpr .a3).toNat) % rate
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.sp = s₂.sp

/-- The state after `updateArgs rate`. -/
def updateState (rate : Nat) (s : State) : State :=
  ((((s.write .a5 (s.gpr .a4)).write .a4 (s.gpr .a3)).write .a3 (s.gpr .a2)).write .a2
    (s.gpr .a1)).write .a1 (BitVec.ofNat 64 rate)

theorem updateArgs_run {rate : Nat} (hr : rate < 2048) (s : State) :
    execBlock isa (updateArgs rate) s = some (updateState rate s, []) := by
  simp [updateArgs, updateState, execBlock, isa, exec, Impl.Sha3.RISCV64.Stream.mov, addrs, imm12,
    show (rate : Int) < 2048 by omega, State.write]

theorem updateState_gpr (rate : Nat) (s : State) (r : Reg) :
    (updateState rate s).gpr r =
      if r = .a1 then BitVec.ofNat 64 rate else if r = .a2 then s.gpr .a1
      else if r = .a3 then s.gpr .a2 else if r = .a4 then s.gpr .a3
      else if r = .a5 then s.gpr .a4 else s.gpr r := by
  simp only [updateState, State.write]

@[simp] theorem updateState_mem (rate : Nat) (s : State) : (updateState rate s).mem = s.mem := rfl
@[simp] theorem updateState_rd (rate : Nat) (s : State) : (updateState rate s).rd = s.rd := rfl
@[simp] theorem updateState_wr (rate : Nat) (s : State) : (updateState rate s).wr = s.wr := rfl
@[simp] theorem updateState_sp (rate : Nat) (s : State) : (updateState rate s).sp = s.sp := rfl

theorem updateState_keep (rate : Nat) (s : State) {r : Reg} (hr : r ∈ preserved ∨ r = .ra) :
    (updateState rate s).gpr r = s.gpr r := by
  rcases hr with hr | rfl
  · obtain ⟨h1, h2, h3, h4, h5, -⟩ := preserved_ne r hr
    simp only [updateState_gpr, h1, h2, h3, h4, h5, ite_false]
  · simp only [updateState_gpr]; rfl

/-- A state satisfying `updateRISCV64`'s precondition (with no data). -/
def updateSat : State :=
  { Stream.absorbWsSat with
    gpr := fun r => match r with | .a0 => 0x1000 | .a2 => 0x2000 | .a4 => 0x3000 | _ => 0 }

theorem update_verified' {rate : Nat} (hr : rate ∈ rates) :
    Verified RISCV64.target (update rate) (updateRISCV64 rate) := by
  have h0 : 0 < rate := by simp [rates] at hr; omega
  refine Verified.of_prologue Stream.absorbWs_verified' (updateState rate)
    (fun s _ => updateArgs_run (rate_lt hr) s)
    (fun s hs => ?_) (fun s s' _ ha => ?_) (fun s s' _ hq => ?_) (fun s₁ s₂ _ _ hp => ?_)
    ⟨updateSat, rfl, rfl, Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
      Region.disjoint_of_sep (by decide), by decide, by decide, by decide, by decide,
      Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
      Region.disjoint_of_sep (by decide), h0⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hs
    simp only [Proof.Sha3.absorbWsRISCV64, updateState_gpr, updateState_rd, updateState_wr,
      updateState_sp, reduceCtorEq, ite_false, ite_true, toNat_rate hr]
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hr, h13⟩
  · obtain ⟨h1, h2, h3⟩ := ha
    exact ⟨fun r hr => by rw [h1 r hr, updateState_keep _ _ (.inl hr)], h2,
      by rw [h3, updateState_keep _ _ (.inr rfl)]⟩
  · obtain ⟨h1, h2⟩ := hq
    simp only [updateState_gpr, updateState_mem, reduceCtorEq, ite_false, ite_true,
      toNat_rate hr] at h1 h2
    exact ⟨h1, h2⟩
  · obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hp
    simp only [Proof.Sha3.absorbWsRISCV64, updateState_gpr, updateState_sp, reduceCtorEq, ite_false,
      ite_true]
    exact ⟨p1, trivial, p2, p3, p4, p5, p6⟩

theorem update_verified {rate : Nat} (hr : rate ∈ rates) :
    Verified RISCV64.target (update rate) (Spec.Sha3.updateContract RISCV64.abi rate 608) := by
  have h0 : 0 < rate := by simp [rates] at hr; omega
  refine (update_verified' hr).of_implies
    { pre := by sig_implies_pre [Spec.Sha3.updateContract, Spec.Sha3.updateSig, Spec.Sha3.updatePre,
          Spec.Sha3.updatePost, updateRISCV64, RISCV64.abi, RISCV64.argRegs]
      post := by sig_implies_post [Spec.Sha3.updateContract, Spec.Sha3.updateSig, Spec.Sha3.updatePre,
          Spec.Sha3.updatePost, updateRISCV64, RISCV64.abi, RISCV64.argRegs]
      pub := by sig_implies_pub [Spec.Sha3.updateContract, Spec.Sha3.updateSig, Spec.Sha3.updatePre,
          Spec.Sha3.updatePost, updateRISCV64, RISCV64.abi, RISCV64.argRegs]
      sat := ?_ }
  refine ⟨updateSat, ?_⟩
  sig_pre [Spec.Sha3.updateContract, Spec.Sha3.updateSig, Spec.Sha3.updatePre, Spec.Sha3.updatePost,
    RISCV64.abi, RISCV64.argRegs, updateSat, Stream.absorbWsSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact h0

/-! ## SHAKE's `finalize` -/

/-- SHAKE's `finalize`'s contract on RISC-V for `X` (`state = a0, pos = a1`). -/
def xofPadRISCV64 (X : Xof) : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 200⟩
    let stack : Region := ⟨s.sp - 1136, 1136⟩
    s.rd = [] ∧ s.wr = [state] ∧
    s.sp.toNat % 16 = 0 ∧ 1136 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ (s.gpr .a1).toNat < X.rate
  post s s' := ∀ msg, Repr s.mem (s.gpr .a0) X.rate msg →
    (s.gpr .a1).toNat = msg.length % X.rate → XofRepr s'.mem (s.gpr .a0) X.rate 0 X.xof msg 0
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.sp = s₂.sp

/-- The state after `xofPadArgs rate`. -/
def xofPadState (rate : Nat) (s : State) : State :=
  ((s.write .a2 (s.gpr .a1)).write .a1 (BitVec.ofNat 64 rate)).write .a3 (BitVec.ofNat 64 0x1f)

theorem xofPadArgs_run {rate : Nat} (hr : rate < 2048) (s : State) :
    execBlock isa (xofPadArgs rate) s = some (xofPadState rate s, []) := by
  simp [xofPadArgs, xofPadState, execBlock, isa, exec, Impl.Sha3.RISCV64.Stream.mov, addrs, imm12,
    show (rate : Int) < 2048 by omega, State.write]

theorem xofPadState_gpr (rate : Nat) (s : State) (r : Reg) :
    (xofPadState rate s).gpr r =
      if r = .a3 then BitVec.ofNat 64 0x1f else if r = .a1 then BitVec.ofNat 64 rate
      else if r = .a2 then s.gpr .a1 else s.gpr r := by
  simp only [xofPadState, State.write]

@[simp] theorem xofPadState_mem (rate : Nat) (s : State) : (xofPadState rate s).mem = s.mem := rfl
@[simp] theorem xofPadState_rd (rate : Nat) (s : State) : (xofPadState rate s).rd = s.rd := rfl
@[simp] theorem xofPadState_wr (rate : Nat) (s : State) : (xofPadState rate s).wr = s.wr := rfl
@[simp] theorem xofPadState_sp (rate : Nat) (s : State) : (xofPadState rate s).sp = s.sp := rfl

theorem xofPadState_keep (rate : Nat) (s : State) {r : Reg} (hr : r ∈ preserved ∨ r = .ra) :
    (xofPadState rate s).gpr r = s.gpr r := by
  rcases hr with hr | rfl
  · obtain ⟨h1, h2, h3, -⟩ := preserved_ne r hr
    simp only [xofPadState_gpr, h1, h2, h3, ite_false]
  · simp only [xofPadState_gpr]; rfl

def xofPadSat : State := { Stream.padSat with gpr := fun r => match r with | .a0 => 0x1000 | _ => 0 }

theorem xofFinalize_verified' {X : Xof} (hX : xofSponge X) (hr : X.rate ∈ rates) :
    Verified RISCV64.target (xofFinalize X.rate) (xofPadRISCV64 X) := by
  have h0 : 0 < X.rate := by simp [rates] at hr; omega
  have hsuf : (BitVec.ofNat 64 0x1f).setWidth 8 = Spec.Sha3.shakeSuffix := by decide
  refine Verified.of_prologue Stream.pad_verified' (xofPadState X.rate)
    (fun s _ => xofPadArgs_run (rate_lt hr) s)
    (fun s hs => ?_) (fun s s' _ ha => ?_) (fun s s' _ hq => ?_) (fun s₁ s₂ _ _ hp => ?_)
    ⟨xofPadSat, rfl, rfl, by decide, by decide, Region.disjoint_of_sep (by decide), h0⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hs
    simp only [Proof.Sha3.padRISCV64, xofPadState_gpr, xofPadState_rd, xofPadState_wr,
      xofPadState_sp, reduceCtorEq, ite_false, ite_true, toNat_rate hr]
    exact ⟨h1, h2, h3, h4, h5, hr, h6⟩
  · obtain ⟨h1, h2, h3⟩ := ha
    exact ⟨fun r hr => by rw [h1 r hr, xofPadState_keep _ _ (.inl hr)], h2,
      by rw [h3, xofPadState_keep _ _ (.inr rfl)]⟩
  · intro msg hm hp
    simp only [Proof.Sha3.padRISCV64, xofPadState_gpr, xofPadState_mem, reduceCtorEq, ite_false,
      ite_true, toNat_rate hr, hsuf] at hq
    exact xofRepr_pad hX (hq msg hm hp)
  · obtain ⟨p1, p2, p3⟩ := hp
    simp only [Proof.Sha3.padRISCV64, xofPadState_gpr, xofPadState_sp, reduceCtorEq, ite_false,
      ite_true]
    exact ⟨p1, trivial, p2, p3⟩

theorem xofFinalize_verified {X : Xof} (hX : xofSponge X) (hr : X.rate ∈ rates) :
    Verified RISCV64.target (xofFinalize X.rate) (Spec.Sha3.xofFinalizeContract RISCV64.abi X 1136) := by
  have h0 : 0 < X.rate := by simp [rates] at hr; omega
  refine (xofFinalize_verified' hX hr).of_implies
    { pre := by sig_implies_pre [Spec.Sha3.xofFinalizeContract, Spec.Sha3.xofFinalizeSig,
          Spec.Sha3.xofFinalizePre, Spec.Sha3.xofFinalizePost, xofPadRISCV64, RISCV64.abi,
          RISCV64.argRegs]
      post := by sig_implies_post [Spec.Sha3.xofFinalizeContract, Spec.Sha3.xofFinalizeSig,
          Spec.Sha3.xofFinalizePre, Spec.Sha3.xofFinalizePost, xofPadRISCV64, RISCV64.abi,
          RISCV64.argRegs]
      pub := by sig_implies_pub [Spec.Sha3.xofFinalizeContract, Spec.Sha3.xofFinalizeSig,
          Spec.Sha3.xofFinalizePre, Spec.Sha3.xofFinalizePost, xofPadRISCV64, RISCV64.abi,
          RISCV64.argRegs]
      sat := ?_ }
  refine ⟨xofPadSat, ?_⟩
  sig_pre [Spec.Sha3.xofFinalizeContract, Spec.Sha3.xofFinalizeSig, Spec.Sha3.xofFinalizePre,
    Spec.Sha3.xofFinalizePost, RISCV64.abi, RISCV64.argRegs, xofPadSat, Stream.padSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact h0

/-! ## SHAKE's `squeeze` -/

/-- SHAKE's `squeeze`'s contract on RISC-V for `X` (`state = a0, pos = a1,
out = a2, outlen = a3`). -/
def xofSqueezeRISCV64 (X : Xof) : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 200⟩
    let out : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
    let stack : Region := ⟨s.sp - 1168, 1168⟩
    s.rd = [] ∧ s.wr = [state, out] ∧ state.Disjoint out ∧
    s.sp.toNat % 16 = 0 ∧ 1168 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint out ∧
    (s.gpr .a1).toNat ≤ X.rate
  post s s' :=
    (∀ msg n, XofRepr s.mem (s.gpr .a0) X.rate (s.gpr .a1).toNat X.xof msg n →
      bytesAt s'.mem (s.gpr .a2) (s.gpr .a3).toNat = (X.xof msg (n + (s.gpr .a3).toNat)).drop n ∧
      XofRepr s'.mem (s.gpr .a0) X.rate (s'.gpr .a0).toNat X.xof msg (n + (s.gpr .a3).toNat)) ∧
    (s'.gpr .a0).toNat ≤ X.rate
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

/-- The state after `xofSqueezeArgs rate`. -/
def xofSqzState (rate : Nat) (s : State) : State :=
  (((s.write .a4 (s.gpr .a3)).write .a3 (s.gpr .a2)).write .a2 (s.gpr .a1)).write .a1
    (BitVec.ofNat 64 rate)

theorem xofSqueezeArgs_run {rate : Nat} (hr : rate < 2048) (s : State) :
    execBlock isa (xofSqueezeArgs rate) s = some (xofSqzState rate s, []) := by
  simp [xofSqueezeArgs, xofSqzState, execBlock, isa, exec, Impl.Sha3.RISCV64.Stream.mov, addrs, imm12,
    show (rate : Int) < 2048 by omega, State.write]

theorem xofSqzState_gpr (rate : Nat) (s : State) (r : Reg) :
    (xofSqzState rate s).gpr r =
      if r = .a1 then BitVec.ofNat 64 rate else if r = .a2 then s.gpr .a1
      else if r = .a3 then s.gpr .a2 else if r = .a4 then s.gpr .a3 else s.gpr r := by
  simp only [xofSqzState, State.write]

@[simp] theorem xofSqzState_mem (rate : Nat) (s : State) : (xofSqzState rate s).mem = s.mem := rfl
@[simp] theorem xofSqzState_rd (rate : Nat) (s : State) : (xofSqzState rate s).rd = s.rd := rfl
@[simp] theorem xofSqzState_wr (rate : Nat) (s : State) : (xofSqzState rate s).wr = s.wr := rfl
@[simp] theorem xofSqzState_sp (rate : Nat) (s : State) : (xofSqzState rate s).sp = s.sp := rfl

theorem xofSqzState_keep (rate : Nat) (s : State) {r : Reg} (hr : r ∈ preserved ∨ r = .ra) :
    (xofSqzState rate s).gpr r = s.gpr r := by
  rcases hr with hr | rfl
  · obtain ⟨h1, h2, h3, h4, -⟩ := preserved_ne r hr
    simp only [xofSqzState_gpr, h1, h2, h3, h4, ite_false]
  · simp only [xofSqzState_gpr]; rfl

def xofSqueezeSat : State :=
  { Stream.squeezeSat with gpr := fun r => match r with | .a0 => 0x1000 | .a2 => 0x2000 | _ => 0 }

theorem xofSqueeze_verified' {X : Xof} (hr : X.rate ∈ rates) :
    Verified RISCV64.target (xofSqueeze X.rate) (xofSqueezeRISCV64 X) := by
  refine Verified.of_prologue Stream.squeeze_verified' (xofSqzState X.rate)
    (fun s _ => xofSqueezeArgs_run (rate_lt hr) s)
    (fun s hs => ?_) (fun s s' _ ha => ?_) (fun s s' _ hq => ?_) (fun s₁ s₂ _ _ hp => ?_)
    ⟨xofSqueezeSat, rfl, rfl, Region.disjoint_of_sep (by decide), by decide, by decide,
      Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Nat.zero_le _⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hs
    simp only [Proof.Sha3.squeezeRISCV64, xofSqzState_gpr, xofSqzState_rd, xofSqzState_wr,
      xofSqzState_sp, reduceCtorEq, ite_false, ite_true, toNat_rate hr]
    exact ⟨h1, h2, h3, h4, h5, h6, h7, hr, h8⟩
  · obtain ⟨h1, h2, h3⟩ := ha
    exact ⟨fun r hr => by rw [h1 r hr, xofSqzState_keep _ _ (.inl hr)], h2,
      by rw [h3, xofSqzState_keep _ _ (.inr rfl)]⟩
  · obtain ⟨h1, h2, h3⟩ := hq
    simp only [xofSqzState_gpr, xofSqzState_mem, reduceCtorEq, ite_false, ite_true,
      toNat_rate hr] at h1 h2 h3
    exact ⟨fun msg n hR => xofRepr_squeeze hR h1 h3, h2⟩
  · obtain ⟨p1, p2, p3, p4, p5⟩ := hp
    simp only [Proof.Sha3.squeezeRISCV64, xofSqzState_gpr, xofSqzState_sp, reduceCtorEq, ite_false,
      ite_true]
    exact ⟨p1, trivial, p2, p3, p4, p5⟩

theorem xofSqueeze_verified {X : Xof} (hr : X.rate ∈ rates) :
    Verified RISCV64.target (xofSqueeze X.rate) (Spec.Sha3.xofSqueezeContract RISCV64.abi X 1168) := by
  refine (xofSqueeze_verified' hr).of_implies
    { pre := by sig_implies_pre [Spec.Sha3.xofSqueezeContract, Spec.Sha3.xofSqueezeSig,
          Spec.Sha3.xofSqueezePre, Spec.Sha3.xofSqueezePost, xofSqueezeRISCV64, RISCV64.abi,
          RISCV64.argRegs]
      post := by sig_implies_post [Spec.Sha3.xofSqueezeContract, Spec.Sha3.xofSqueezeSig,
          Spec.Sha3.xofSqueezePre, Spec.Sha3.xofSqueezePost, xofSqueezeRISCV64, RISCV64.abi,
          RISCV64.argRegs]
      pub := by sig_implies_pub [Spec.Sha3.xofSqueezeContract, Spec.Sha3.xofSqueezeSig,
          Spec.Sha3.xofSqueezePre, Spec.Sha3.xofSqueezePost, xofSqueezeRISCV64, RISCV64.abi,
          RISCV64.argRegs]
      sat := ?_ }
  refine ⟨xofSqueezeSat, ?_⟩
  sig_pre [Spec.Sha3.xofSqueezeContract, Spec.Sha3.xofSqueezeSig, Spec.Sha3.xofSqueezePre,
    Spec.Sha3.xofSqueezePost, RISCV64.abi, RISCV64.argRegs, xofSqueezeSat, Stream.squeezeSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Nat.zero_le _

/-! ## SHA-3's `finalize` -/

/-- SHA-3's `finalize`'s contract on RISC-V for `H`, with its frame (32
bytes) passed in `a3` (`state = a0, pos = a1, out = a2, scratch = a3`); its
calls use the 1168 bytes below the stack pointer. -/
def finRISCV64 (H : Spec.Sha3.HashFn) : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 200⟩
    let out : Region := ⟨s.gpr .a2, H.len⟩
    let scratch : Region := ⟨s.gpr .a3, 32⟩
    let stack : Region := ⟨s.sp - 1168, 1168⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    (s.gpr .a3).toNat % 8 = 0 ∧ (s.gpr .a3).toNat + 32 ≤ 2 ^ 64 ∧
    s.sp.toNat % 16 = 0 ∧ 1168 ≤ s.sp.toNat ∧
    stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    (s.gpr .a1).toNat < H.rate
  post s s' := ∀ msg, Repr s.mem (s.gpr .a0) H.rate msg →
    (s.gpr .a1).toNat = msg.length % H.rate → bytesAt s'.mem (s.gpr .a2) H.len = H.digest msg
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

/-- Where `finalize`'s buffers are, and the 1168 bytes of stack below the
stack pointer `sp`. -/
structure Lay (st op sc sp : Addr) (len : Nat) : Prop where
  st_op : Region.Disjoint ⟨st, 200⟩ ⟨op, len⟩
  st_sc : Region.Disjoint ⟨st, 200⟩ ⟨sc, 32⟩
  op_sc : Region.Disjoint ⟨op, len⟩ ⟨sc, 32⟩
  stk_st : Region.Disjoint ⟨sp - 1168, 1168⟩ ⟨st, 200⟩
  stk_op : Region.Disjoint ⟨sp - 1168, 1168⟩ ⟨op, len⟩
  stk_sc : Region.Disjoint ⟨sp - 1168, 1168⟩ ⟨sc, 32⟩
  al : sc.toNat % 8 = 0
  nw : sc.toNat + 32 ≤ 2 ^ 64
  sp16 : sp.toNat % 16 = 0
  sp1168 : 1168 ≤ sp.toNat

theorem stateAt_frame {rs : List Region} {m m' : Mem} {p : Addr} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 200⟩ r) : stateAt m' p = stateAt m p :=
  Proof.Sha3.stateAt_congr fun _ hi => hf.bytes (R := ⟨p, 200⟩) hd (by show 200 ≤ 2 ^ 64; decide) hi

theorem readW_frame {rs : List Region} {m m' : Mem} {a : Addr} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨a, 8⟩ r) : m'.readW a 64 = m.readW a 64 :=
  hf.readW (r := ⟨a, 8⟩) (Region.contains_self _ _) hd (by decide)

theorem wcons {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

theorem exec_mov {s : State} {d n : Reg} :
    exec (Impl.Sha3.RISCV64.Stream.mov d n) s = some (s.write d (s.gpr n)) := by
  rw [Impl.Sha3.RISCV64.Stream.mov, exec_addi (by decide)]; simp

theorem exec_liN {s : State} {d : Reg} {n : Nat} (h : n < 2048) :
    exec (.li d (n : Int)) s = some (s.write d (BitVec.ofNat 64 n)) := by
  rw [exec_li (by unfold imm12; omega), ofInt_nat]

theorem aligned {sc : Addr} (hal : sc.toNat % 8 = 0) (hnw : sc.toNat + 32 ≤ 2 ^ 64) {d : Nat}
    (hd : d < 32) (h8 : d % 8 = 0) : (sc + BitVec.ofNat 64 d).toNat % 8 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show d < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show sc.toNat + d < 2 ^ 64 by omega)]
  omega

theorem in_scr {rs : List Region} {sc : Addr} {d : Nat} (hd : d + 8 ≤ 32) (hw : ⟨sc, 32⟩ ∈ rs) :
    InRegions rs (sc + BitVec.ofNat 64 d) 8 :=
  ⟨⟨sc, 32⟩, hw, Offset.contains_base _ (by omega) (by omega)⟩

/-- After `finPadArgs`. -/
theorem finPad_ok {rate : Nat} (hr : rate < 2048) {s : State} (hw : ⟨s.gpr .a3, 32⟩ ∈ s.wr)
    (hal : (s.gpr .a3).toNat % 8 = 0) (hnw : (s.gpr .a3).toNat + 32 ≤ 2 ^ 64) :
    WP isa (.block (finPadArgs rate)) s fun t =>
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.gpr .ra = s.gpr .ra ∧
      t.mem = (((s.mem.writeW (s.gpr .a3 + BitVec.ofNat 64 0) (s.gpr .ra)).writeW
        (s.gpr .a3 + BitVec.ofNat 64 8) (s.gpr .s2)).writeW (s.gpr .a3 + BitVec.ofNat 64 16)
        (s.gpr .s3)).writeW (s.gpr .a3 + BitVec.ofNat 64 24) (s.gpr .s4) ∧
      t.gpr .a0 = s.gpr .a0 ∧ t.gpr .s2 = s.gpr .a0 ∧ t.gpr .s3 = s.gpr .a2 ∧
      t.gpr .s4 = s.gpr .a3 ∧ t.gpr .a2 = s.gpr .a1 ∧ t.gpr .a1 = BitVec.ofNat 64 rate ∧
      t.gpr .a3 = BitVec.ofNat 64 0x06 ∧
      ∀ r ∈ preserved, r ≠ .s2 → r ≠ .s3 → r ≠ .s4 → t.gpr r = s.gpr r := by
  have h1 := in_scr (rs := s.wr) (d := 0) (by omega) hw
  have h2 := in_scr (rs := s.wr) (d := 8) (by omega) hw
  have h3 := in_scr (rs := s.wr) (d := 16) (by omega) hw
  have h4 := in_scr (rs := s.wr) (d := 24) (by omega) hw
  unfold finPadArgs
  refine wcons (exec_store_d (by decide) (aligned hal hnw (by omega) (by omega)) h1)
    (wcons (exec_store_d (by decide) (aligned hal hnw (by omega) (by omega)) h2)
    (wcons (exec_store_d (by decide) (aligned hal hnw (by omega) (by omega)) h3)
    (wcons (exec_store_d (by decide) (aligned hal hnw (by omega) (by omega)) h4)
    (wcons exec_mov (wcons exec_mov (wcons exec_mov (wcons exec_mov (wcons (exec_liN hr)
    (wcons (exec_liN (by decide)) (WP.block_nil ?_))))))))))
  simp only [RegUpd.gpr_write, RegUpd.mem_write, RegUpd.wr_write, RegUpd.rd_write, RegUpd.sp_write,
    reduceCtorEq, ite_true, ite_false]
  iterate 12 refine ⟨by first | trivial | rfl, ?_⟩
  intro r hr h2' h3' h4'
  have hne : r ≠ .a1 ∧ r ≠ .a2 ∧ r ≠ .a3 := by revert r; decide
  simp only [h2', h3', h4', hne.1, hne.2.1, hne.2.2, ite_false]

theorem gpr_ce (t : State) (rd wr : List Region) {r : Reg} (h : r ∉ linkRegs := by decide) :
    (t.callEntry.withRegions rd wr).gpr r = t.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h]

theorem sub1136 (sp : Addr) : Region.Sub ⟨sp - BitVec.ofNat 64 1136, 1136⟩ ⟨sp - BitVec.ofNat 64 1168, 1168⟩ :=
  Offset.sub_below sp (by omega) (by omega)

theorem sp1136 (sp : Addr) : sp - 1136 = sp - BitVec.ofNat 64 1136 := rfl
theorem sp1168 (sp : Addr) : sp - 1168 = sp - BitVec.ofNat 64 1168 := rfl

theorem pad_sdepth : sdepth Impl.Sha3.RISCV64.Stream.pad = 1136 := by decide +kernel
theorem squeeze_sdepth : sdepth Impl.Sha3.RISCV64.Stream.squeeze = 1168 := by decide +kernel

/-- `pad`'s precondition at the call, narrowed to the state. -/
theorem finPad_pre {st op sc sp : Addr} {len rate : Nat} (hL : Lay st op sc sp len) (hr : rate ∈ rates)
    {t : State} (h0 : t.gpr .a0 = st) (h1 : t.gpr .a1 = BitVec.ofNat 64 rate)
    (h2 : (t.gpr .a2).toNat < rate) (hsp : t.sp = sp) :
    Proof.Sha3.padRISCV64.pre (t.callEntry.withRegions [] [⟨st, 200⟩]) := by
  simp (disch := decide) only [Proof.Sha3.padRISCV64, gpr_ce, State.withRegions_sp, State.callEntry_sp,
    State.withRegions_rd, State.withRegions_wr, h0, h1, hsp, toNat_rate hr]
  exact ⟨trivial, trivial, hL.sp16, by have := hL.sp1168; omega,
    (by rw [sp1136]; exact hL.stk_st.sub_left (sp1168 sp ▸ sub1136 sp)), hr, h2⟩

theorem finPad_cov {st op sc : Addr} {len : Nat} {t : State}
    (hwr : t.wr = [⟨st, 200⟩, ⟨op, len⟩, ⟨sc, 32⟩]) :
    Covers ([] ++ [⟨st, 200⟩]) (t.rd ++ t.wr) ∧ Covers [⟨st, 200⟩] t.wr :=
  ⟨Covers.right (Covers.of_mem fun r hr => by simp at hr; simp [hwr, hr]),
    Covers.of_mem fun r hr => by simp at hr; simp [hwr, hr]⟩

/-- The call of `pad`, with SHA-3's suffix. -/
theorem finPadCall {st op sc sp : Addr} {len rate : Nat} (hL : Lay st op sc sp len) (hr : rate ∈ rates)
    {t : State} (hwr : t.wr = [⟨st, 200⟩, ⟨op, len⟩, ⟨sc, 32⟩])
    (h0 : t.gpr .a0 = st) (h1 : t.gpr .a1 = BitVec.ofNat 64 rate) (h2 : (t.gpr .a2).toNat < rate)
    (h3 : t.gpr .a3 = BitVec.ofNat 64 0x06) (hsp : t.sp = sp) :
    WP isa (.call "vg_keccak_pad" Impl.Sha3.RISCV64.Stream.pad) t fun u =>
      u.rd = t.rd ∧ u.wr = t.wr ∧ u.sp = t.sp ∧ (∀ r ∈ preserved, u.gpr r = t.gpr r) ∧
      Frame [⟨st, 200⟩, ⟨sp - 1168, 1168⟩] t.mem u.mem ∧
      ∀ msg, Repr t.mem st rate msg → (t.gpr .a2).toNat = msg.length % rate →
        stateAt u.mem st = Spec.Sha3.absorb rate (Spec.Sha3.pad rate Spec.Sha3.sha3Suffix msg) := by
  refine WP.callAny (k := Proof.Sha3.padRISCV64) Stream.pad_verified'.1 (rd := []) (wr := [⟨st, 200⟩])
    (finPad_pre hL hr h0 h1 h2 hsp) (finPad_cov hwr).1 (finPad_cov hwr).2
    (fun u e1 e2 e3 e4 e5 hpost => ⟨e1, e2, e3, e5, ?_, fun msg hm hp => ?_⟩)
  · rw [pad_sdepth, hsp] at e4
    refine e4.sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, sp1168 sp ▸ sub1136 sp⟩
  · simp (disch := decide) only [Proof.Sha3.padRISCV64, gpr_ce, State.withRegions_mem,
      State.callEntry_mem, h0, h1, h3, toNat_rate hr] at hpost
    rw [hpost msg hm hp]
    rfl

/-- `squeeze`'s precondition at the call, narrowed to the state and `out`. -/
theorem finSqz_pre {st op sc sp : Addr} {len rate : Nat} (hL : Lay st op sc sp len) (hr : rate ∈ rates)
    (hl : len < 2048) {t : State} (h0 : t.gpr .a0 = st) (h1 : t.gpr .a1 = BitVec.ofNat 64 rate)
    (h2 : t.gpr .a2 = BitVec.ofNat 64 0) (h3 : t.gpr .a3 = op) (h4 : t.gpr .a4 = BitVec.ofNat 64 len)
    (hsp : t.sp = sp) :
    Proof.Sha3.squeezeRISCV64.pre (t.callEntry.withRegions [] [⟨st, 200⟩, ⟨op, len⟩]) := by
  have hl' : (BitVec.ofNat 64 len).toNat = len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp (disch := decide) only [Proof.Sha3.squeezeRISCV64, gpr_ce, State.withRegions_sp,
    State.callEntry_sp, State.withRegions_rd, State.withRegions_wr, h0, h1, h2, h3, h4, hsp,
    toNat_rate hr, hl']
  exact ⟨trivial, trivial, hL.st_op, hL.sp16, hL.sp1168, hL.stk_st, hL.stk_op, hr, by simp⟩

theorem finSqz_cov {st op sc : Addr} {len : Nat} {t : State}
    (hwr : t.wr = [⟨st, 200⟩, ⟨op, len⟩, ⟨sc, 32⟩]) :
    Covers ([] ++ [⟨st, 200⟩, ⟨op, len⟩]) (t.rd ++ t.wr) ∧ Covers [⟨st, 200⟩, ⟨op, len⟩] t.wr :=
  ⟨Covers.right (Covers.of_mem fun r hr => by
      simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [hwr]),
    Covers.of_mem fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [hwr]⟩

/-- The call of `squeeze`, from position 0, for `len` bytes into `out`. -/
theorem finSqzCall {st op sc sp : Addr} {len rate : Nat} (hL : Lay st op sc sp len) (hr : rate ∈ rates)
    (hl : len < 2048) {t : State} (hwr : t.wr = [⟨st, 200⟩, ⟨op, len⟩, ⟨sc, 32⟩])
    (h0 : t.gpr .a0 = st) (h1 : t.gpr .a1 = BitVec.ofNat 64 rate) (h2 : t.gpr .a2 = BitVec.ofNat 64 0)
    (h3 : t.gpr .a3 = op) (h4 : t.gpr .a4 = BitVec.ofNat 64 len) (hsp : t.sp = sp) :
    WP isa (.call "vg_keccak_squeeze" Impl.Sha3.RISCV64.Stream.squeeze) t fun u =>
      u.rd = t.rd ∧ u.wr = t.wr ∧ u.sp = t.sp ∧ (∀ r ∈ preserved, u.gpr r = t.gpr r) ∧
      Frame [⟨st, 200⟩, ⟨op, len⟩, ⟨sp - 1168, 1168⟩] t.mem u.mem ∧
      bytesAt u.mem op len = Spec.Sha3.squeezeFrom rate (stateAt t.mem st) 0 len := by
  have hl' : (BitVec.ofNat 64 len).toNat = len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine WP.callAny (k := Proof.Sha3.squeezeRISCV64) Stream.squeeze_verified'.1 (rd := [])
    (wr := [⟨st, 200⟩, ⟨op, len⟩])
    (finSqz_pre hL hr hl h0 h1 h2 h3 h4 hsp) (finSqz_cov hwr).1 (finSqz_cov hwr).2
    (fun u e1 e2 e3 e4 e5 hpost => ⟨e1, e2, e3, e5, by rw [squeeze_sdepth, hsp] at e4; exact e4, ?_⟩)
  obtain ⟨hp, -⟩ := hpost
  simp (disch := decide) only [gpr_ce, State.withRegions_mem, State.callEntry_mem, h0, h1, h2, h3, h4,
    toNat_rate hr, hl'] at hp
  rw [hp]
  simp

/-- After `finSqzArgs`. -/
theorem finSqz_ok {rate len : Nat} (hr : rate < 2048) (hl : len < 2048) (s : State) :
    WP isa (.block (finSqzArgs rate len)) s fun t =>
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.mem = s.mem ∧
      t.gpr .a0 = s.gpr .s2 ∧ t.gpr .a1 = BitVec.ofNat 64 rate ∧ t.gpr .a2 = BitVec.ofNat 64 0 ∧
      t.gpr .a3 = s.gpr .s3 ∧ t.gpr .a4 = BitVec.ofNat 64 len ∧
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.gpr .ra = s.gpr .ra := by
  unfold finSqzArgs
  refine wcons exec_mov (wcons (exec_liN hr) (wcons (exec_liN (by decide)) (wcons exec_mov
    (wcons (exec_liN hl) (WP.block_nil ?_)))))
  simp only [RegUpd.gpr_write, RegUpd.mem_write, RegUpd.wr_write, RegUpd.rd_write, RegUpd.sp_write,
    reduceCtorEq, ite_true, ite_false]
  iterate 9 refine ⟨by first | trivial | rfl, ?_⟩
  refine ⟨fun r hr => ?_, trivial⟩
  obtain ⟨h1, h2, h3, h4, -⟩ := preserved_ne r hr
  have h0 : r ≠ .a0 := by revert r; decide
  simp only [h0, h1, h2, h3, h4, ite_false]

/-- After `finRestore`, from a state with `s4` = `sc`. -/
theorem finRestore_ok {sc : Addr} {s : State} (h4 : s.gpr .s4 = sc) (hal : sc.toNat % 8 = 0)
    (hnw : sc.toNat + 32 ≤ 2 ^ 64) (hin : ∀ d, d + 8 ≤ 32 →
      InRegions (s.rd ++ s.wr) (sc + BitVec.ofNat 64 d) 8) :
    WP isa (.block finRestore) s fun t =>
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.mem = s.mem ∧
      t.gpr .ra = s.mem.readW (sc + BitVec.ofNat 64 0) 64 ∧
      t.gpr .s2 = s.mem.readW (sc + BitVec.ofNat 64 8) 64 ∧
      t.gpr .s3 = s.mem.readW (sc + BitVec.ofNat 64 16) 64 ∧
      t.gpr .s4 = s.mem.readW (sc + BitVec.ofNat 64 24) 64 ∧
      ∀ r ∈ preserved, r ≠ .s2 → r ≠ .s3 → r ≠ .s4 → t.gpr r = s.gpr r := by
  have a0 : (sc + BitVec.ofNat 64 0).toNat % 8 = 0 := aligned hal hnw (by omega) (by omega)
  have a8 : (sc + BitVec.ofNat 64 8).toNat % 8 = 0 := aligned hal hnw (by omega) (by omega)
  have a16 : (sc + BitVec.ofNat 64 16).toNat % 8 = 0 := aligned hal hnw (by omega) (by omega)
  have a24 : (sc + BitVec.ofNat 64 24).toNat % 8 = 0 := aligned hal hnw (by omega) (by omega)
  have i0 := hin 0 (by omega)
  have i8 := hin 8 (by omega)
  have i16 := hin 16 (by omega)
  have i24 := hin 24 (by omega)
  unfold finRestore
  refine wcons (exec_load_d (by decide) (by rw [h4]; exact a0) (by rw [h4]; exact i0)) ?_
  refine wcons (exec_load_d (by decide) (by simpa [RegUpd.gpr_write, h4] using a8)
    (by simpa [RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, h4] using i8)) ?_
  refine wcons (exec_load_d (by decide) (by simpa [RegUpd.gpr_write, h4] using a16)
    (by simpa [RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, h4] using i16)) ?_
  refine wcons (exec_load_d (by decide) (by simpa [RegUpd.gpr_write, h4] using a24)
    (by simpa [RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, h4] using i24)) (WP.block_nil ?_)
  simp only [RegUpd.gpr_write, RegUpd.mem_write, RegUpd.wr_write, RegUpd.rd_write, RegUpd.sp_write,
    reduceCtorEq, ite_true, ite_false, h4]
  iterate 8 refine ⟨by first | trivial | rfl, ?_⟩
  intro r hr h2' h3' h4'
  have hra : r ≠ .ra := by revert r; decide
  simp only [hra, h2', h3', h4', ite_false]

theorem lay_of_pre {H : Spec.Sha3.HashFn} {s : State} (hp : (finRISCV64 H).pre s) :
    Lay (s.gpr .a0) (s.gpr .a2) (s.gpr .a3) s.sp H.len := by
  obtain ⟨-, -, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, -⟩ := hp
  exact ⟨p3, p4, p5, p10, p11, p12, p6, p7, p8, p9⟩

/-- `finBody` meets `finRISCV64` and the ABI. -/
theorem finBody_correct {H : Spec.Sha3.HashFn} (hH : hashSponge H) (hr : H.rate ∈ rates)
    (hl : H.len < 2048) {s : State} (hp : (finRISCV64 H).pre s) :
    WP isa (finBody H.rate H.len) s fun s' => abiPreserved s s' ∧ (finRISCV64 H).post s s' := by
  have hL := lay_of_pre hp
  obtain ⟨p1, p2, -, -, -, -, -, -, -, -, -, -, p13⟩ := hp
  have hw : ⟨s.gpr .a3, 32⟩ ∈ s.wr := by rw [p2]; simp
  have hslot : ∀ d, d + 8 ≤ 32 →
      ∀ r ∈ [(⟨s.gpr .a0, 200⟩ : Region), ⟨s.gpr .a2, H.len⟩, ⟨s.sp - 1168, 1168⟩],
        Region.Disjoint ⟨s.gpr .a3 + BitVec.ofNat 64 d, 8⟩ r := by
    intro d h2 r hr
    have hsub : Region.Sub ⟨s.gpr .a3 + BitVec.ofNat 64 d, 8⟩ ⟨s.gpr .a3, 32⟩ :=
      Offset.sub_base _ (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hL.st_sc.symm).sub_left hsub
    · exact (hL.op_sc.symm).sub_left hsub
    · exact (hL.stk_sc.symm).sub_left hsub
  refine WP.seq (WP.mono (finPad_ok (rate_lt hr) hw hL.al hL.nw) fun t ⟨trd, twr, tsp, tra, tmem, t0,
    ts2, ts3, ts4, t2, t1, t3, toth⟩ => ?_)
  refine WP.seq (WP.mono (finPadCall hL hr (by rw [twr, p2]) t0 t1 (by rw [t2]; exact p13) t3 tsp)
    fun u ⟨urd, uwr, usp, upr, uf, upad⟩ => ?_)
  refine WP.seq (WP.mono (finSqz_ok (rate_lt hr) hl u) fun v ⟨vrd, vwr, vsp, vmem, v0, v1, v2, v3, v4,
    vpr, vra⟩ => ?_)
  have u2 : u.gpr .s2 = s.gpr .a0 := by rw [upr .s2 (by decide), ts2]
  have u3 : u.gpr .s3 = s.gpr .a2 := by rw [upr .s3 (by decide), ts3]
  have u4 : u.gpr .s4 = s.gpr .a3 := by rw [upr .s4 (by decide), ts4]
  refine WP.seq (WP.mono (finSqzCall hL hr hl (by rw [vwr, uwr, twr, p2]) (by rw [v0, u2]) v1 v2
    (by rw [v3, u3]) v4 (by rw [vsp, usp, tsp]))
    fun w ⟨wrd, wwr, wsp, wpr, wf, wout⟩ => ?_)
  have w4 : w.gpr .s4 = s.gpr .a3 := by rw [wpr .s4 (by decide), vpr .s4 (by decide), u4]
  have hin : ∀ d, d + 8 ≤ 32 → InRegions (w.rd ++ w.wr) (s.gpr .a3 + BitVec.ofNat 64 d) 8 :=
    fun d hd => let ⟨r, hr, hc⟩ := in_scr (rs := w.wr) hd (by rw [wwr, vwr, uwr, twr]; exact hw)
      ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (finRestore_ok w4 hL.al hL.nw hin) fun x ⟨xrd, xwr, xsp, xmem, xra, x2, x3, x4, xoth⟩ => ?_
  have fw : Frame [⟨s.gpr .a0, 200⟩, ⟨s.gpr .a2, H.len⟩, ⟨s.sp - 1168, 1168⟩] t.mem w.mem := by
    refine (uf.mono fun r hr => ?_).trans (vmem ▸ wf)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl <;> simp
  have slot : ∀ d, d + 8 ≤ 32 →
      w.mem.readW (s.gpr .a3 + BitVec.ofNat 64 d) 64 = t.mem.readW (s.gpr .a3 + BitVec.ofNat 64 d) 64 :=
    fun d h2 => readW_frame fw (hslot d h2)
  have sep : ∀ a b, a + 8 ≤ 32 → b + 8 ≤ 32 → a ≠ b → a % 8 = 0 → b % 8 = 0 →
      Mem.Sep (s.gpr .a3 + BitVec.ofNat 64 a) (64 / 8) (s.gpr .a3 + BitVec.ofNat 64 b) (64 / 8) :=
    fun a b _ _ hab ha hb => Offset.sep _ (by omega) (by omega) (by omega)
  have t0' : t.mem.readW (s.gpr .a3 + BitVec.ofNat 64 0) 64 = s.gpr .ra := by
    rw [tmem, Mem.readW_writeW_sep (sep 0 24 (by omega) (by omega) (by omega) (by omega) (by omega))
        (by decide),
      Mem.readW_writeW_sep (sep 0 16 (by omega) (by omega) (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 0 8 (by omega) (by omega) (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64]
  have t8 : t.mem.readW (s.gpr .a3 + BitVec.ofNat 64 8) 64 = s.gpr .s2 := by
    rw [tmem, Mem.readW_writeW_sep (sep 8 24 (by omega) (by omega) (by omega) (by omega) (by omega))
        (by decide),
      Mem.readW_writeW_sep (sep 8 16 (by omega) (by omega) (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64]
  have t16 : t.mem.readW (s.gpr .a3 + BitVec.ofNat 64 16) 64 = s.gpr .s3 := by
    rw [tmem, Mem.readW_writeW_sep (sep 16 24 (by omega) (by omega) (by omega) (by omega) (by omega))
        (by decide), Mem.readW_writeW_self64]
  have t24 : t.mem.readW (s.gpr .a3 + BitVec.ofNat 64 24) 64 = s.gpr .s4 := by
    rw [tmem, Mem.readW_writeW_self64]
  have ft : Frame [⟨s.gpr .a3, 32⟩] s.mem t.mem := by
    rw [tmem]
    refine Frame.writeW (Frame.writeW (Frame.writeW (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
      ?_) (List.mem_singleton_self _) _ ?_) (List.mem_singleton_self _) _ ?_) (List.mem_singleton_self _) _ ?_
    all_goals exact Offset.contains_base _ (by omega) (by omega)
  refine ⟨⟨fun r hr => ?_, by rw [xsp, wsp, vsp, usp, tsp], ?_⟩, fun msg hm hpos => ?_⟩
  · by_cases h2 : r = .s2
    · subst h2; rw [x2, slot 8 (by omega), t8]
    by_cases h3 : r = .s3
    · subst h3; rw [x3, slot 16 (by omega), t16]
    by_cases h4 : r = .s4
    · subst h4; rw [x4, slot 24 (by omega), t24]
    rw [xoth r hr h2 h3 h4, wpr r hr, vpr r hr, upr r hr, toth r hr h2 h3 h4]
  · rw [xra, slot 0 (by omega), t0']
  · have hst : stateAt t.mem (s.gpr .a0) = stateAt s.mem (s.gpr .a0) :=
      stateAt_frame ft (by intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hL.st_sc)
    have hpad := upad msg (by unfold Spec.Sha3.Repr; rw [hst]; exact hm) (by rw [t2]; exact hpos)
    show bytesAt x.mem (s.gpr .a2) H.len = H.digest msg
    rw [xmem, wout, vmem, hpad]
    exact digest_of_pad hH rfl

/-! ### Constant time -/

def G1 (rate : Nat) (σ t : State) : Prop :=
  t.rd = σ.rd ∧ t.wr = σ.wr ∧ t.gpr .a0 = σ.gpr .a0 ∧ t.gpr .a1 = BitVec.ofNat 64 rate ∧
    t.gpr .a2 = σ.gpr .a1 ∧ t.gpr .a3 = BitVec.ofNat 64 0x06 ∧
    t.gpr .s2 = σ.gpr .a0 ∧ t.gpr .s3 = σ.gpr .a2 ∧ t.gpr .s4 = σ.gpr .a3 ∧ t.sp = σ.sp

def G2 (σ u : State) : Prop :=
  u.rd = σ.rd ∧ u.wr = σ.wr ∧ u.gpr .s2 = σ.gpr .a0 ∧ u.gpr .s3 = σ.gpr .a2 ∧
    u.gpr .s4 = σ.gpr .a3 ∧ u.sp = σ.sp

def G3 (rate len : Nat) (σ v : State) : Prop :=
  v.rd = σ.rd ∧ v.wr = σ.wr ∧ v.gpr .a0 = σ.gpr .a0 ∧ v.gpr .a1 = BitVec.ofNat 64 rate ∧
    v.gpr .a2 = BitVec.ofNat 64 0 ∧ v.gpr .a3 = σ.gpr .a2 ∧ v.gpr .a4 = BitVec.ofNat 64 len ∧
    v.gpr .s4 = σ.gpr .a3 ∧ v.sp = σ.sp

theorem g1_ok {H : Spec.Sha3.HashFn} (hr : H.rate < 2048) {σ : State} (hp : (finRISCV64 H).pre σ) :
    WP isa (.block (finPadArgs H.rate)) σ (G1 H.rate σ) :=
  WP.mono (finPad_ok hr (by rw [hp.2.1]; simp) (lay_of_pre hp).al (lay_of_pre hp).nw)
    fun _ ⟨h1, h2, h3, _, _, h6, h7, h8, h9, h10, h11, h12, _⟩ =>
      ⟨h1, h2, h6, h11, h10, h12, h7, h8, h9, h3⟩

theorem g2_ok {H : Spec.Sha3.HashFn} (hr : H.rate ∈ rates) {σ t : State} (hp : (finRISCV64 H).pre σ)
    (h : G1 H.rate σ t) :
    WP isa (.call "vg_keccak_pad" Impl.Sha3.RISCV64.Stream.pad) t (G2 σ) := by
  have hL := lay_of_pre hp
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  refine WP.mono (finPadCall hL hr (by rw [h2, hp.2.1]) h3 h4 (by rw [h5]; exact hp.2.2.2.2.2.2.2.2.2.2.2.2)
    h6 h10) fun u ⟨u1, u2, u3, u4, _, _⟩ =>
      ⟨by rw [u1, h1], by rw [u2, h2], by rw [u4 .s2 (by decide), h7], by rw [u4 .s3 (by decide), h8],
        by rw [u4 .s4 (by decide), h9], by rw [u3, h10]⟩

theorem g3_ok {H : Spec.Sha3.HashFn} (hr : H.rate < 2048) (hl : H.len < 2048) {σ u : State}
    (h : G2 σ u) : WP isa (.block (finSqzArgs H.rate H.len)) u (G3 H.rate H.len σ) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine WP.mono (finSqz_ok hr hl u) fun v ⟨v1, v2, v3, _, v5, v6, v7, v8, v9, v10, _⟩ =>
    ⟨by rw [v1, h1], by rw [v2, h2], by rw [v5, h3], v6, v7, by rw [v8, h4], v9,
      by rw [v10 .s4 (by decide), h5], by rw [v3, h6]⟩

theorem g4_ok {H : Spec.Sha3.HashFn} (hr : H.rate ∈ rates) (hl : H.len < 2048) {σ v : State}
    (hp : (finRISCV64 H).pre σ) (h : G3 H.rate H.len σ v) :
    WP isa (.call "vg_keccak_squeeze" Impl.Sha3.RISCV64.Stream.squeeze) v
      fun w => w.gpr .s4 = σ.gpr .a3 ∧ w.sp = σ.sp := by
  have hL := lay_of_pre hp
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact WP.mono (finSqzCall hL hr hl (by rw [h2, hp.2.1]) h3 h4 h5 h6 h7 h9) fun w ⟨_, _, w3, w4, _⟩ =>
    ⟨by rw [w4 .s4 (by decide), h8], by rw [w3, h9]⟩

theorem finBody_ct {H : Spec.Sha3.HashFn} (hr : H.rate ∈ rates) (hl : H.len < 2048)
    {h₁ h₂ h₃ : VG.Taint.Hint RISCV64.Taint.T}
    (hb₁ : (RISCV64.taint.check (RISCV64.Taint.ofRegs [.a0, .a1, .a2, .a3]) (.block (finPadArgs H.rate))
      h₁).isSome = true)
    (hb₂ : (RISCV64.taint.check (RISCV64.Taint.ofRegs []) (.block (finSqzArgs H.rate H.len)) h₂).isSome = true)
    (hb₃ : (RISCV64.taint.check (RISCV64.Taint.ofRegs [.s4]) (.block finRestore) h₃).isSome = true) :
    ConstantTime isa (finRISCV64 H).pre (finRISCV64 H).pub (finBody H.rate H.len) := by
  intro σ₁ σ₂ t₁ t₂ σ₁' σ₂' p₁ p₂ hp e₁ e₂
  obtain ⟨q0, q1, q2, q3, qsp⟩ := hp
  have hP : RelCT isa (fun a b => a = σ₁ ∧ b = σ₂) (finBody H.rate H.len) fun _ _ => True := by
    unfold finBody
    refine RelCT.seq (RelCT.wp (F₁ := G1 H.rate σ₁) (F₂ := G1 H.rate σ₂)
      (RelCT.taint (A := RISCV64.taint) (RISCV64.Taint.ofRegs [.a0, .a1, .a2, .a3])
        (fun a b ⟨ea, eb⟩ => by
          subst ea eb
          refine ⟨qsp, fun r hr => ?_⟩
          simp only [RISCV64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption) hb₁)
      fun a b ⟨ea, eb⟩ => by subst ea eb; exact ⟨g1_ok (rate_lt hr) p₁, g1_ok (rate_lt hr) p₂⟩) ?_
    refine RelCT.seq (RelCT.wp (F₁ := G2 σ₁) (F₂ := G2 σ₂)
      (RelCT.call Stream.pad_verified'.1 Stream.pad_ct [] [⟨σ₁.gpr .a0, 200⟩]
        fun a b ⟨_, ha, hb⟩ => ?_) fun a b ⟨_, ha, hb⟩ => ⟨g2_ok hr p₁ ha, g2_ok hr p₂ hb⟩) ?_
    · have hL₁ := lay_of_pre p₁
      have hL₂ := lay_of_pre p₂
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := ha
      obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := hb
      have pb := finPad_pre hL₂ hr b3 b4 (by rw [b5]; exact p₂.2.2.2.2.2.2.2.2.2.2.2.2) b10
      rw [← q0] at pb
      refine ⟨finPad_pre hL₁ hr a3 a4 (by rw [a5]; exact p₁.2.2.2.2.2.2.2.2.2.2.2.2) a10, pb, ?_,
        (finPad_cov (by rw [a2, p₁.2.1])).1, (finPad_cov (by rw [a2, p₁.2.1])).2,
        (finPad_cov (by rw [b2, p₂.2.1, ← q0, ← q2, ← q3])).1,
        (finPad_cov (by rw [b2, p₂.2.1, ← q0, ← q2, ← q3])).2⟩
      simp (disch := decide) only [Proof.Sha3.padRISCV64, gpr_ce, State.withRegions_sp,
        State.callEntry_sp]
      exact ⟨by rw [a3, b3, q0], by rw [a4, b4], by rw [a5, b5, q1], by rw [a10, b10, qsp]⟩
    refine RelCT.seq (RelCT.wp (F₁ := G3 H.rate H.len σ₁) (F₂ := G3 H.rate H.len σ₂)
      (RelCT.taint (A := RISCV64.taint) (RISCV64.Taint.ofRegs []) (fun a b ⟨_, ha, hb⟩ =>
        ⟨by rw [ha.2.2.2.2.2, hb.2.2.2.2.2, qsp], fun r h => by simp [RISCV64.Taint.mem_ofRegs] at h⟩) hb₂)
      fun a b ⟨_, ha, hb⟩ => ⟨g3_ok (rate_lt hr) hl ha, g3_ok (rate_lt hr) hl hb⟩) ?_
    refine RelCT.seq (RelCT.wp (F₁ := fun w : State => w.gpr .s4 = σ₁.gpr .a3 ∧ w.sp = σ₁.sp)
      (F₂ := fun w : State => w.gpr .s4 = σ₂.gpr .a3 ∧ w.sp = σ₂.sp)
      (RelCT.call Stream.squeeze_verified'.1 Stream.squeeze_ct []
        [⟨σ₁.gpr .a0, 200⟩, ⟨σ₁.gpr .a2, H.len⟩] fun a b ⟨_, ha, hb⟩ => ?_)
      fun a b ⟨_, ha, hb⟩ => ⟨g4_ok hr hl p₁ ha, g4_ok hr hl p₂ hb⟩) ?_
    · have hL₁ := lay_of_pre p₁
      have hL₂ := lay_of_pre p₂
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := ha
      obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := hb
      have pb := finSqz_pre hL₂ hr hl b3 b4 b5 b6 b7 b9
      rw [← q0, ← q2] at pb
      refine ⟨finSqz_pre hL₁ hr hl a3 a4 a5 a6 a7 a9, pb, ?_, (finSqz_cov (by rw [a2, p₁.2.1])).1,
        (finSqz_cov (by rw [a2, p₁.2.1])).2, (finSqz_cov (by rw [b2, p₂.2.1, ← q0, ← q2, ← q3])).1,
        (finSqz_cov (by rw [b2, p₂.2.1, ← q0, ← q2, ← q3])).2⟩
      simp (disch := decide) only [Proof.Sha3.squeezeRISCV64, gpr_ce, State.withRegions_sp,
        State.callEntry_sp]
      exact ⟨by rw [a3, b3, q0], by rw [a4, b4], by rw [a5, b5], by rw [a6, b6, q2], by rw [a7, b7],
        by rw [a9, b9, qsp]⟩
    exact RelCT.taint (A := RISCV64.taint) (RISCV64.Taint.ofRegs [.s4]) (fun a b ⟨_, ha, hb⟩ =>
      ⟨by rw [ha.2, hb.2, qsp], fun r h => by
        simp [RISCV64.Taint.mem_ofRegs] at h; subst h; rw [ha.1, hb.1, q3]⟩) hb₃
  exact (hP _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ### `Verified` -/

theorem finBody_verified {H : Spec.Sha3.HashFn} (hH : hashSponge H) (hr : H.rate ∈ rates)
    (hl : H.len < 2048)
    (hct : ConstantTime isa (finRISCV64 H).pre (finRISCV64 H).pub (finBody H.rate H.len))
    (hsat : ∃ s, (finRISCV64 H).pre s) (hsat' : ∃ s, (finScratchContract RISCV64.abi H 4 1168).pre s) :
    Verified RISCV64.target (finBody H.rate H.len) (finScratchContract RISCV64.abi H 4 1168) :=
  (Verified.of_correct (fun s hs => (finBody_correct hH hr hl hs).elim fun t ⟨s', he, h⟩ =>
      ⟨t, s', he, h.1, h.2⟩) hct (Contract.Implies.refl hsat)).of_implies
    { pre := by sig_implies_pre [VG.Proof.Sha3.Instances.finScratchContract,
          VG.Proof.Sha3.Instances.finScratchSig, Spec.Sha3.finalizePre, Spec.Sha3.finalizePost,
          finRISCV64, RISCV64.abi, RISCV64.argRegs]
      post := by sig_implies_post [VG.Proof.Sha3.Instances.finScratchContract,
          VG.Proof.Sha3.Instances.finScratchSig, Spec.Sha3.finalizePre, Spec.Sha3.finalizePost,
          finRISCV64, RISCV64.abi, RISCV64.argRegs]
      pub := by sig_implies_pub [VG.Proof.Sha3.Instances.finScratchContract,
          VG.Proof.Sha3.Instances.finScratchSig, Spec.Sha3.finalizePre, Spec.Sha3.finalizePost,
          finRISCV64, RISCV64.abi, RISCV64.argRegs]
      sat := hsat' }

theorem finalize_verified {H : Spec.Sha3.HashFn} (hH : hashSponge H) (hr : H.rate ∈ rates)
    (hl : H.len < 2048)
    (hct : ConstantTime isa (finRISCV64 H).pre (finRISCV64 H).pub (finBody H.rate H.len))
    (hsat : ∃ s, (finRISCV64 H).pre s) (hsat' : ∃ s, (finScratchContract RISCV64.abi H 4 1168).pre s)
    (hsat'' : ∃ s, (Spec.Sha3.finalizeContract RISCV64.abi H (1168 + 32)).pre s) :
    Verified RISCV64.target (finalize H.rate H.len) (Spec.Sha3.finalizeContract RISCV64.abi H (1168 + 32)) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Sha3.finalizeSig H.len) (nm := "scratch") (e := .u64)
    (n := 4) (pre := Spec.Sha3.finalizePre H RISCV64.abi.ptrBits)
    (post := Spec.Sha3.finalizePost H RISCV64.abi.ptrBits) (wa := true) (stack := 1168)
    (bytes := 32) (finBody_verified hH hr hl hct hsat hsat') (by exact (by decide : 3 < 8))
    (by decide) hsat'' rfl

/-- A state satisfying `finRISCV64`'s precondition. -/
def finSat (len : Nat) : State :=
  { Stream.padSat with
    gpr := fun r => match r with | .a0 => 0x1000 | .a2 => 0x2000 | .a3 => 0x3000 | _ => 0
    wr := [⟨0x1000, 200⟩, ⟨0x2000, len⟩, ⟨0x3000, 32⟩] }

macro "fin_ct" : term => `(finBody_ct (by decide) (by decide) (by taint_decide) (by taint_decide)
  (by taint_decide))

theorem update_sha3_224 :
    Verified RISCV64.target (update Spec.Sha3.hashSha3_224.rate) (Spec.Sha3.updateContract RISCV64.abi Spec.Sha3.hashSha3_224.rate 608) :=
  update_verified (by decide)

theorem finalize_sha3_224 :
    Verified RISCV64.target (finalize Spec.Sha3.hashSha3_224.rate Spec.Sha3.hashSha3_224.len)
      (Spec.Sha3.finalizeContract RISCV64.abi Spec.Sha3.hashSha3_224 (1168 + 32)) :=
  finalize_verified VG.Proof.Sha3.Instances.sha3_224_sponge (by decide) (by decide) fin_ct
    (by implies_sat [finRISCV64, Spec.Sha3.hashSha3_224] [finSat, Stream.padSat] using finSat 28)
    (by implies_sat [VG.Proof.Sha3.Instances.finScratchContract, VG.Proof.Sha3.Instances.finScratchSig,
      Spec.Sha3.finalizePre, Spec.Sha3.finalizePost, RISCV64.abi, RISCV64.argRegs, Spec.Sha3.hashSha3_224]
      [finSat, Stream.padSat] using finSat 28)
    (by implies_sat [Spec.Sha3.finalizeContract, Spec.Sha3.finalizeSig, Spec.Sha3.finalizePre,
      Spec.Sha3.finalizePost, RISCV64.abi, RISCV64.argRegs, Spec.Sha3.hashSha3_224] [finSat, Stream.padSat]
      using { finSat 28 with wr := [⟨0x1000, 200⟩, ⟨0x2000, 28⟩] })

theorem update_sha3_256 :
    Verified RISCV64.target (update Spec.Sha3.hashSha3_256.rate) (Spec.Sha3.updateContract RISCV64.abi Spec.Sha3.hashSha3_256.rate 608) :=
  update_verified (by decide)

theorem finalize_sha3_256 :
    Verified RISCV64.target (finalize Spec.Sha3.hashSha3_256.rate Spec.Sha3.hashSha3_256.len)
      (Spec.Sha3.finalizeContract RISCV64.abi Spec.Sha3.hashSha3_256 (1168 + 32)) :=
  finalize_verified VG.Proof.Sha3.Instances.sha3_256_sponge (by decide) (by decide) fin_ct
    (by implies_sat [finRISCV64, Spec.Sha3.hashSha3_256] [finSat, Stream.padSat] using finSat 32)
    (by implies_sat [VG.Proof.Sha3.Instances.finScratchContract, VG.Proof.Sha3.Instances.finScratchSig,
      Spec.Sha3.finalizePre, Spec.Sha3.finalizePost, RISCV64.abi, RISCV64.argRegs, Spec.Sha3.hashSha3_256]
      [finSat, Stream.padSat] using finSat 32)
    (by implies_sat [Spec.Sha3.finalizeContract, Spec.Sha3.finalizeSig, Spec.Sha3.finalizePre,
      Spec.Sha3.finalizePost, RISCV64.abi, RISCV64.argRegs, Spec.Sha3.hashSha3_256] [finSat, Stream.padSat]
      using { finSat 32 with wr := [⟨0x1000, 200⟩, ⟨0x2000, 32⟩] })

theorem update_sha3_384 :
    Verified RISCV64.target (update Spec.Sha3.hashSha3_384.rate) (Spec.Sha3.updateContract RISCV64.abi Spec.Sha3.hashSha3_384.rate 608) :=
  update_verified (by decide)

theorem finalize_sha3_384 :
    Verified RISCV64.target (finalize Spec.Sha3.hashSha3_384.rate Spec.Sha3.hashSha3_384.len)
      (Spec.Sha3.finalizeContract RISCV64.abi Spec.Sha3.hashSha3_384 (1168 + 32)) :=
  finalize_verified VG.Proof.Sha3.Instances.sha3_384_sponge (by decide) (by decide) fin_ct
    (by implies_sat [finRISCV64, Spec.Sha3.hashSha3_384] [finSat, Stream.padSat] using finSat 48)
    (by implies_sat [VG.Proof.Sha3.Instances.finScratchContract, VG.Proof.Sha3.Instances.finScratchSig,
      Spec.Sha3.finalizePre, Spec.Sha3.finalizePost, RISCV64.abi, RISCV64.argRegs, Spec.Sha3.hashSha3_384]
      [finSat, Stream.padSat] using finSat 48)
    (by implies_sat [Spec.Sha3.finalizeContract, Spec.Sha3.finalizeSig, Spec.Sha3.finalizePre,
      Spec.Sha3.finalizePost, RISCV64.abi, RISCV64.argRegs, Spec.Sha3.hashSha3_384] [finSat, Stream.padSat]
      using { finSat 48 with wr := [⟨0x1000, 200⟩, ⟨0x2000, 48⟩] })

theorem update_sha3_512 :
    Verified RISCV64.target (update Spec.Sha3.hashSha3_512.rate) (Spec.Sha3.updateContract RISCV64.abi Spec.Sha3.hashSha3_512.rate 608) :=
  update_verified (by decide)

theorem finalize_sha3_512 :
    Verified RISCV64.target (finalize Spec.Sha3.hashSha3_512.rate Spec.Sha3.hashSha3_512.len)
      (Spec.Sha3.finalizeContract RISCV64.abi Spec.Sha3.hashSha3_512 (1168 + 32)) :=
  finalize_verified VG.Proof.Sha3.Instances.sha3_512_sponge (by decide) (by decide) fin_ct
    (by implies_sat [finRISCV64, Spec.Sha3.hashSha3_512] [finSat, Stream.padSat] using finSat 64)
    (by implies_sat [VG.Proof.Sha3.Instances.finScratchContract, VG.Proof.Sha3.Instances.finScratchSig,
      Spec.Sha3.finalizePre, Spec.Sha3.finalizePost, RISCV64.abi, RISCV64.argRegs, Spec.Sha3.hashSha3_512]
      [finSat, Stream.padSat] using finSat 64)
    (by implies_sat [Spec.Sha3.finalizeContract, Spec.Sha3.finalizeSig, Spec.Sha3.finalizePre,
      Spec.Sha3.finalizePost, RISCV64.abi, RISCV64.argRegs, Spec.Sha3.hashSha3_512] [finSat, Stream.padSat]
      using { finSat 64 with wr := [⟨0x1000, 200⟩, ⟨0x2000, 64⟩] })

theorem update_shake128 :
    Verified RISCV64.target (update Spec.Sha3.xofShake128.rate) (Spec.Sha3.updateContract RISCV64.abi Spec.Sha3.xofShake128.rate 608) :=
  update_verified (by decide)

theorem finalize_shake128 :
    Verified RISCV64.target (xofFinalize Spec.Sha3.xofShake128.rate) (Spec.Sha3.xofFinalizeContract RISCV64.abi Spec.Sha3.xofShake128 1136) :=
  xofFinalize_verified VG.Proof.Sha3.Instances.shake128_sponge (by decide)

theorem squeeze_shake128 :
    Verified RISCV64.target (xofSqueeze Spec.Sha3.xofShake128.rate) (Spec.Sha3.xofSqueezeContract RISCV64.abi Spec.Sha3.xofShake128 1168) :=
  xofSqueeze_verified (by decide)

theorem finalize_shake256 :
    Verified RISCV64.target (xofFinalize Spec.Sha3.xofShake256.rate) (Spec.Sha3.xofFinalizeContract RISCV64.abi Spec.Sha3.xofShake256 1136) :=
  xofFinalize_verified VG.Proof.Sha3.Instances.shake256_sponge (by decide)

theorem squeeze_shake256 :
    Verified RISCV64.target (xofSqueeze Spec.Sha3.xofShake256.rate) (Spec.Sha3.xofSqueezeContract RISCV64.abi Spec.Sha3.xofShake256 1168) :=
  xofSqueeze_verified (by decide)

end VG.Proof.Sha3.RISCV64.Instances
