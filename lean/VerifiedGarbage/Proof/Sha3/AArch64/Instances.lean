module

public import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Absorb
public import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
public import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Squeeze
public import VerifiedGarbage.Proof.Sha3.Instances
public import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
public import VerifiedGarbage.Impl.Sha3.AArch64.Instances
public import VerifiedGarbage.Spec.Sha3.Instances
import VerifiedGarbage.Proof.Framework.Prologue
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Taint

meta import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Absorb
meta import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
meta import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Squeeze
meta import VerifiedGarbage.Proof.Sha3.Instances
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
meta import VerifiedGarbage.Impl.Sha3.AArch64.Instances
meta import VerifiedGarbage.Spec.Sha3.Instances
meta import VerifiedGarbage.Proof.Framework.Prologue
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-!
# SHA-3 and SHAKE on AArch64: the functions of each instance

As on x86-64 (`Proof/Sha3/X86_64/Instances.lean`), for any implementation
of the permutation (`Permutation`): each runs the sponge's code after a
block that moves its arguments into the registers that code takes them in
and sets the rate (and suffix) (`Verified.of_prologue`).
-/

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Instances

open VG VG.AArch64 VG.Impl.Sha3.AArch64.Instances
open VG.Proof.Sha3.AArch64 (Permutation)
open VG.Spec.Sha3 (Repr bytesAt rates stateAt XofRepr Xof)
open VG.Proof.Sha3.Instances (xofSponge hashSponge xofRepr_pad xofRepr_squeeze digest_of_pad
  xofFinalizeScratchContract xofSqueezeScratchContract finScratchContract)

theorem rate_lt {rate : Nat} (hr : rate ∈ rates) : rate < 2 ^ 15 := by simp [rates] at hr; omega

theorem toNat_rate {rate : Nat} (hr : rate ∈ rates) : (BitVec.ofNat 64 rate).toNat = rate := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := rate_lt hr; omega)]

theorem exec_mov {s : State} {d n : Reg} :
    exec (Impl.Sha3.AArch64.mov d n) s = some (s.write .x d (s.gpr n)) := by
  rw [Impl.Sha3.AArch64.mov, exec_addImm_x (by decide)]
  simp [State.read]

theorem exec_li {s : State} {d : Reg} {n : Nat} (h : n < 2 ^ 16) :
    exec (li d n) s = some (s.write .x d (BitVec.ofNat 64 n)) := by
  simp only [li, exec, Size.bits, Nat.mul_zero, show (0 : Nat) < 64 from by decide, ite_true,
    BitVec.shiftLeft_zero]
  congr 2
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64)]

theorem wcons {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

/-! ## `update` -/

/-- `update rate`'s contract on AArch64, with the arguments in registers
(`state = x0, pos = x1, data = x2, len = x3, scratch = x4`): that of
`absorb` (`Proof.Sha3.absorbAArch64`), with the rate `rate`. -/
def updateAArch64 (rate : Nat) : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 200⟩
    let data : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let scratch : Region := ⟨s.gpr .x4, 640⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [data] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch ∧
    (s.gpr .x1).toNat < rate
  post s s' :=
    (∀ msg, Repr s.mem (s.gpr .x0) rate msg → (s.gpr .x1).toNat = msg.length % rate →
      Repr s'.mem (s.gpr .x0) rate (msg ++ bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)) ∧
    (s'.gpr .x0).toNat = ((s.gpr .x1).toNat + (s.gpr .x3).toNat) % rate
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

/-- The state after `updateArgs rate`. -/
def updateState (rate : Nat) (s : State) : State :=
  ((((s.write .x .x5 (s.gpr .x4)).write .x .x4 (s.gpr .x3)).write .x .x3 (s.gpr .x2)).write .x .x2
    (s.gpr .x1)).write .x .x1 (BitVec.ofNat 64 rate)

theorem updateArgs_run {rate : Nat} (hr : rate < 2 ^ 16) (s : State) :
    execBlock isa (updateArgs rate) s = some (updateState rate s, []) := by
  simp only [updateArgs, updateState, execBlock, isa, exec_mov, exec_li hr, RegUpd.gpr_write,
    reduceCtorEq, ite_false]
  rfl

theorem updateState_gpr (rate : Nat) (s : State) (r : Reg) :
    (updateState rate s).gpr r =
      if r = .x1 then BitVec.ofNat 64 rate else if r = .x2 then s.gpr .x1
      else if r = .x3 then s.gpr .x2 else if r = .x4 then s.gpr .x3
      else if r = .x5 then s.gpr .x4 else s.gpr r := by
  simp only [updateState, RegUpd.gpr_write, BitVec.setWidth_eq]

@[simp] theorem updateState_mem (rate : Nat) (s : State) : (updateState rate s).mem = s.mem := rfl
@[simp] theorem updateState_rd (rate : Nat) (s : State) : (updateState rate s).rd = s.rd := rfl
@[simp] theorem updateState_wr (rate : Nat) (s : State) : (updateState rate s).wr = s.wr := rfl
@[simp] theorem updateState_sp (rate : Nat) (s : State) : (updateState rate s).sp = s.sp := rfl
@[simp] theorem updateState_v (rate : Nat) (s : State) : (updateState rate s).v = s.v := rfl

theorem preserved_ne : ∀ r ∈ preserved, r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 ∧ r ≠ .x4 ∧ r ≠ .x5 := by decide

theorem updateState_preserved (rate : Nat) (s : State) {r : Reg} (hr : r ∈ preserved) :
    (updateState rate s).gpr r = s.gpr r := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := preserved_ne r hr
  simp only [updateState_gpr, h1, h2, h3, h4, h5, ite_false]

theorem absorb_sat : ∃ s, Proof.Sha3.absorbAArch64.pre s := by
  implies_sat [Proof.Sha3.absorbAArch64, rates] [Stream.Absorb.sat] using Stream.Absorb.sat

/-- A state satisfying `updateAArch64`'s precondition (with no data). -/
def updateSat : State :=
  { Stream.Absorb.sat with
    gpr := fun r => match r with | .x0 => 0x1000 | .x2 => 0x2000 | .x4 => 0x3000 | _ => 0 }

theorem update_verified' (v : Permutation) {rate : Nat} (hr : rate ∈ rates) :
    Verified AArch64.target (update v.callee rate) (updateAArch64 rate) := by
  have h0 : 0 < rate := by simp [rates] at hr; omega
  have hv : Verified AArch64.target (Impl.Sha3.AArch64.Stream.absorbWith v.callee)
      Proof.Sha3.absorbAArch64 :=
    Verified.of_correct (Stream.Absorb.absorb_correct v) (Stream.Absorb.absorb_ct v)
      (Contract.Implies.refl absorb_sat)
  refine Verified.of_prologue hv (updateState rate)
    (fun s _ => updateArgs_run (by have := rate_lt hr; omega) s)
    (fun s hs => ?_) (fun s s' _ ha => ?_) (fun s s' _ hq => ?_) (fun s₁ s₂ _ _ hp => ?_)
    ⟨updateSat, rfl, rfl, Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
      Region.disjoint_of_sep (by decide), by decide, Region.disjoint_of_sep (by decide),
      Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), h0⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hs
    simp only [Proof.Sha3.absorbAArch64, updateState_gpr, updateState_rd, updateState_wr,
      updateState_sp, reduceCtorEq, ite_false, ite_true, toNat_rate hr]
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, hr, h10⟩
  · obtain ⟨h1, h2, h3⟩ := ha
    exact ⟨fun r hr => by rw [h1 r hr, updateState_preserved _ _ hr], h2, h3⟩
  · obtain ⟨h1, h2⟩ := hq
    simp only [updateState_gpr, updateState_mem, reduceCtorEq, ite_false, ite_true,
      toNat_rate hr] at h1 h2
    exact ⟨h1, h2⟩
  · obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hp
    simp only [Proof.Sha3.absorbAArch64, updateState_gpr, updateState_sp, reduceCtorEq, ite_false,
      ite_true]
    exact ⟨p1, trivial, p2, p3, p4, p5, p6⟩

theorem update_verified (v : Permutation) {rate : Nat} (hr : rate ∈ rates) :
    Verified AArch64.target (update v.callee rate) (Spec.Sha3.updateContract AArch64.abi rate 16) := by
  have h0 : 0 < rate := by simp [rates] at hr; omega
  refine (update_verified' v hr).of_implies
    { pre := by sig_implies_pre [Spec.Sha3.updateContract, Spec.Sha3.updateSig, Spec.Sha3.updatePre,
          Spec.Sha3.updatePost, updateAArch64, AArch64.abi, AArch64.argRegs]
      post := by sig_implies_post [Spec.Sha3.updateContract, Spec.Sha3.updateSig,
          Spec.Sha3.updatePre, Spec.Sha3.updatePost, updateAArch64, AArch64.abi, AArch64.argRegs]
      pub := by sig_implies_pub [Spec.Sha3.updateContract, Spec.Sha3.updateSig, Spec.Sha3.updatePre,
          Spec.Sha3.updatePost, updateAArch64, AArch64.abi, AArch64.argRegs]
      sat := ?_ }
  refine ⟨updateSat, ?_⟩
  sig_pre [Spec.Sha3.updateContract, Spec.Sha3.updateSig, Spec.Sha3.updatePre, Spec.Sha3.updatePost,
    AArch64.abi, AArch64.argRegs, updateSat, Stream.Absorb.sat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact h0

/-! ## SHAKE's `finalize` -/

/-- SHAKE's `finalize`'s contract on AArch64 for `X`, with its working space
passed in `x2` (`state = x0, pos = x1, scratch = x2`). -/
def xofPadAArch64 (X : Xof) : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 200⟩
    let scratch : Region := ⟨s.gpr .x2, 640⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [] ∧ s.wr = [state, scratch] ∧ state.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint scratch ∧
    (s.gpr .x1).toNat < X.rate
  post s s' := ∀ msg, Repr s.mem (s.gpr .x0) X.rate msg →
    (s.gpr .x1).toNat = msg.length % X.rate → XofRepr s'.mem (s.gpr .x0) X.rate 0 X.xof msg 0
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.sp = s₂.sp

/-- The state after `xofPadArgs rate`. -/
def xofPadState (rate : Nat) (s : State) : State :=
  (((s.write .x .x4 (s.gpr .x2)).write .x .x2 (s.gpr .x1)).write .x .x1 (BitVec.ofNat 64 rate)).write
    .x .x3 (BitVec.ofNat 64 0x1f)

theorem xofPadArgs_run {rate : Nat} (hr : rate < 2 ^ 16) (s : State) :
    execBlock isa (xofPadArgs rate) s = some (xofPadState rate s, []) := by
  simp only [xofPadArgs, xofPadState, execBlock, isa, exec_mov, exec_li hr,
    exec_li (by decide : 0x1f < 2 ^ 16), RegUpd.gpr_write, reduceCtorEq, ite_false]
  rfl

theorem xofPadState_gpr (rate : Nat) (s : State) (r : Reg) :
    (xofPadState rate s).gpr r =
      if r = .x3 then BitVec.ofNat 64 0x1f else if r = .x1 then BitVec.ofNat 64 rate
      else if r = .x2 then s.gpr .x1 else if r = .x4 then s.gpr .x2 else s.gpr r := by
  simp only [xofPadState, RegUpd.gpr_write, BitVec.setWidth_eq]

@[simp] theorem xofPadState_mem (rate : Nat) (s : State) : (xofPadState rate s).mem = s.mem := rfl
@[simp] theorem xofPadState_rd (rate : Nat) (s : State) : (xofPadState rate s).rd = s.rd := rfl
@[simp] theorem xofPadState_wr (rate : Nat) (s : State) : (xofPadState rate s).wr = s.wr := rfl
@[simp] theorem xofPadState_sp (rate : Nat) (s : State) : (xofPadState rate s).sp = s.sp := rfl
@[simp] theorem xofPadState_v (rate : Nat) (s : State) : (xofPadState rate s).v = s.v := rfl

theorem pad_sat : ∃ s, Proof.Sha3.padAArch64.pre s := by
  implies_sat [Proof.Sha3.padAArch64, rates] [Stream.Pad.sat] using Stream.Pad.sat

/-- A state satisfying `xofPadAArch64`'s precondition. -/
def xofPadSat : State :=
  { Stream.Pad.sat with gpr := fun r => match r with | .x0 => 0x1000 | .x2 => 0x3000 | _ => 0 }

theorem xofPad_verified' (v : Permutation) {X : Xof} (hX : xofSponge X) (hr : X.rate ∈ rates) :
    Verified AArch64.target
      (.seq (.block (xofPadArgs X.rate)) (Impl.Sha3.AArch64.Stream.padWith v.callee))
      (xofPadAArch64 X) := by
  have h0 : 0 < X.rate := by simp [rates] at hr; omega
  have hv : Verified AArch64.target (Impl.Sha3.AArch64.Stream.padWith v.callee)
      Proof.Sha3.padAArch64 :=
    Verified.of_correct (Stream.Pad.pad_correct v) (Stream.Pad.pad_ct v)
      (Contract.Implies.refl pad_sat)
  have hsuf : (BitVec.ofNat 64 0x1f).setWidth 8 = Spec.Sha3.shakeSuffix := by decide
  refine Verified.of_prologue hv (xofPadState X.rate)
    (fun s _ => xofPadArgs_run (by have := rate_lt hr; omega) s)
    (fun s hs => ?_) (fun s s' _ ha => ?_) (fun s s' _ hq => ?_) (fun s₁ s₂ _ _ hp => ?_)
    ⟨xofPadSat, rfl, rfl, Region.disjoint_of_sep (by decide), by decide,
      Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), h0⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hs
    simp only [Proof.Sha3.padAArch64, xofPadState_gpr, xofPadState_rd, xofPadState_wr,
      xofPadState_sp, reduceCtorEq, ite_false, ite_true, toNat_rate hr]
    exact ⟨h1, h2, h3, h4, h5, h6, hr, h7⟩
  · obtain ⟨h1, h2, h3⟩ := ha
    refine ⟨fun r hr => ?_, h2, h3⟩
    obtain ⟨h4, h5, h6, h7, -⟩ := preserved_ne r hr
    rw [h1 r hr, xofPadState_gpr]
    simp only [h4, h5, h6, h7, ite_false]
  · intro msg hm hp
    simp only [Proof.Sha3.padAArch64, xofPadState_gpr, xofPadState_mem, reduceCtorEq, ite_false,
      ite_true, toNat_rate hr, hsuf] at hq
    exact xofRepr_pad hX (hq msg hm hp)
  · obtain ⟨p1, p2, p3, p4⟩ := hp
    simp only [Proof.Sha3.padAArch64, xofPadState_gpr, xofPadState_sp, reduceCtorEq, ite_false,
      ite_true]
    exact ⟨p1, trivial, p2, p3, p4⟩

theorem xofPad_verified (v : Permutation) {X : Xof} (hX : xofSponge X) (hr : X.rate ∈ rates) :
    Verified AArch64.target
      (.seq (.block (xofPadArgs X.rate)) (Impl.Sha3.AArch64.Stream.padWith v.callee))
      (xofFinalizeScratchContract AArch64.abi X 16) := by
  have h0 : 0 < X.rate := by simp [rates] at hr; omega
  refine (xofPad_verified' v hX hr).of_implies
    { pre := by sig_implies_pre [VG.Proof.Sha3.Instances.xofFinalizeScratchContract,
          VG.Proof.Sha3.Instances.xofFinalizeScratchSig, Spec.Sha3.xofFinalizePre,
          Spec.Sha3.xofFinalizePost, xofPadAArch64, AArch64.abi, AArch64.argRegs]
      post := by sig_implies_post [VG.Proof.Sha3.Instances.xofFinalizeScratchContract,
          VG.Proof.Sha3.Instances.xofFinalizeScratchSig, Spec.Sha3.xofFinalizePre,
          Spec.Sha3.xofFinalizePost, xofPadAArch64, AArch64.abi, AArch64.argRegs]
      pub := by sig_implies_pub [VG.Proof.Sha3.Instances.xofFinalizeScratchContract,
          VG.Proof.Sha3.Instances.xofFinalizeScratchSig, Spec.Sha3.xofFinalizePre,
          Spec.Sha3.xofFinalizePost, xofPadAArch64, AArch64.abi, AArch64.argRegs]
      sat := ?_ }
  refine ⟨xofPadSat, ?_⟩
  sig_pre [VG.Proof.Sha3.Instances.xofFinalizeScratchContract,
    VG.Proof.Sha3.Instances.xofFinalizeScratchSig, Spec.Sha3.xofFinalizePre,
    Spec.Sha3.xofFinalizePost, AArch64.abi, AArch64.argRegs, xofPadSat, Stream.Pad.sat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact h0

/-- A state satisfying SHAKE's `finalize`'s precondition, with no working space. -/
def xofFinalizeSat : State := { xofPadSat with wr := [⟨0x1000, 200⟩] }

theorem xofFinalize_verified (v : Permutation) {X : Xof} (hX : xofSponge X) (hr : X.rate ∈ rates) :
    Verified AArch64.target (xofFinalize v.callee X.rate)
      (Spec.Sha3.xofFinalizeContract AArch64.abi X (16 + 640)) := by
  have h0 : 0 < X.rate := by simp [rates] at hr; omega
  refine AArch64.Verified.stackScratch (sig := Spec.Sha3.xofFinalizeSig) (nm := "scratch")
    (e := .u64) (n := 80) (pre := Spec.Sha3.xofFinalizePre X AArch64.abi.ptrBits)
    (post := Spec.Sha3.xofFinalizePost X AArch64.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 640) (xofPad_verified v hX hr) (by decide) (by decide) ⟨xofFinalizeSat, ?_⟩
  sig_pre [Spec.Sha3.xofFinalizeContract, Spec.Sha3.xofFinalizeSig, Spec.Sha3.xofFinalizePre,
    Spec.Sha3.xofFinalizePost, AArch64.abi, AArch64.argRegs, xofFinalizeSat, xofPadSat,
    Stream.Pad.sat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact h0

/-! ## SHAKE's `squeeze` -/

/-- SHAKE's `squeeze`'s contract on AArch64 for `X`, with its working space
passed in `x4` (`state = x0, pos = x1, out = x2, outlen = x3, scratch = x4`). -/
def xofSqueezeAArch64 (X : Xof) : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 200⟩
    let out : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let scratch : Region := ⟨s.gpr .x4, 640⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    (s.gpr .x1).toNat ≤ X.rate
  post s s' :=
    (∀ msg n, XofRepr s.mem (s.gpr .x0) X.rate (s.gpr .x1).toNat X.xof msg n →
      bytesAt s'.mem (s.gpr .x2) (s.gpr .x3).toNat = (X.xof msg (n + (s.gpr .x3).toNat)).drop n ∧
      XofRepr s'.mem (s.gpr .x0) X.rate (s'.gpr .x0).toNat X.xof msg (n + (s.gpr .x3).toNat)) ∧
    (s'.gpr .x0).toNat ≤ X.rate
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

theorem squeeze_sat : ∃ s, Proof.Sha3.squeezeAArch64.pre s := by
  implies_sat [Proof.Sha3.squeezeAArch64, rates] [Stream.Squeeze.sat] using Stream.Squeeze.sat

/-- A state satisfying `xofSqueezeAArch64`'s precondition (with no output). -/
def xofSqueezeSat : State :=
  { Stream.Squeeze.sat with
    gpr := fun r => match r with | .x0 => 0x1000 | .x2 => 0x2000 | .x4 => 0x3000 | _ => 0
    wr := [⟨0x1000, 200⟩, ⟨0x2000, 0⟩, ⟨0x3000, 640⟩] }

theorem xofSqueeze_verified' (v : Permutation) {X : Xof} (hr : X.rate ∈ rates) :
    Verified AArch64.target
      (.seq (.block (updateArgs X.rate)) (Impl.Sha3.AArch64.Stream.squeezeWith v.callee))
      (xofSqueezeAArch64 X) := by
  have hv : Verified AArch64.target (Impl.Sha3.AArch64.Stream.squeezeWith v.callee)
      Proof.Sha3.squeezeAArch64 :=
    Verified.of_correct (Stream.Squeeze.squeeze_correct v) (Stream.Squeeze.squeeze_ct v)
      (Contract.Implies.refl squeeze_sat)
  refine Verified.of_prologue hv (updateState X.rate)
    (fun s _ => updateArgs_run (by have := rate_lt hr; omega) s)
    (fun s hs => ?_) (fun s s' _ ha => ?_) (fun s s' _ hq => ?_) (fun s₁ s₂ _ _ hp => ?_)
    ⟨xofSqueezeSat, rfl, rfl, Region.disjoint_of_sep (by decide),
      Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), by decide,
      Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
      Region.disjoint_of_sep (by decide), Nat.zero_le _⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hs
    simp only [Proof.Sha3.squeezeAArch64, updateState_gpr, updateState_rd, updateState_wr,
      updateState_sp, reduceCtorEq, ite_false, ite_true, toNat_rate hr]
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, hr, h10⟩
  · obtain ⟨h1, h2, h3⟩ := ha
    exact ⟨fun r hr => by rw [h1 r hr, updateState_preserved _ _ hr], h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := hq
    simp only [updateState_gpr, updateState_mem, reduceCtorEq, ite_false, ite_true,
      toNat_rate hr] at h1 h2 h3
    exact ⟨fun msg n hR => xofRepr_squeeze hR h1 h3, h2⟩
  · obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hp
    simp only [Proof.Sha3.squeezeAArch64, updateState_gpr, updateState_sp, reduceCtorEq, ite_false,
      ite_true]
    exact ⟨p1, trivial, p2, p3, p4, p5, p6⟩

theorem xofSqueezeS_verified (v : Permutation) {X : Xof} (hr : X.rate ∈ rates) :
    Verified AArch64.target
      (.seq (.block (updateArgs X.rate)) (Impl.Sha3.AArch64.Stream.squeezeWith v.callee))
      (xofSqueezeScratchContract AArch64.abi X 16) := by
  refine (xofSqueeze_verified' v hr).of_implies
    { pre := by sig_implies_pre [VG.Proof.Sha3.Instances.xofSqueezeScratchContract,
          VG.Proof.Sha3.Instances.xofSqueezeScratchSig, Spec.Sha3.xofSqueezePre,
          Spec.Sha3.xofSqueezePost, xofSqueezeAArch64, AArch64.abi, AArch64.argRegs]
      post := by sig_implies_post [VG.Proof.Sha3.Instances.xofSqueezeScratchContract,
          VG.Proof.Sha3.Instances.xofSqueezeScratchSig, Spec.Sha3.xofSqueezePre,
          Spec.Sha3.xofSqueezePost, xofSqueezeAArch64, AArch64.abi, AArch64.argRegs]
      pub := by sig_implies_pub [VG.Proof.Sha3.Instances.xofSqueezeScratchContract,
          VG.Proof.Sha3.Instances.xofSqueezeScratchSig, Spec.Sha3.xofSqueezePre,
          Spec.Sha3.xofSqueezePost, xofSqueezeAArch64, AArch64.abi, AArch64.argRegs]
      sat := ?_ }
  refine ⟨xofSqueezeSat, ?_⟩
  sig_pre [VG.Proof.Sha3.Instances.xofSqueezeScratchContract,
    VG.Proof.Sha3.Instances.xofSqueezeScratchSig, Spec.Sha3.xofSqueezePre,
    Spec.Sha3.xofSqueezePost, AArch64.abi, AArch64.argRegs, xofSqueezeSat, Stream.Squeeze.sat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Nat.zero_le _

/-- A state satisfying SHAKE's `squeeze`'s precondition, with no working space. -/
def xofSqueezeTopSat : State := { xofSqueezeSat with wr := [⟨0x1000, 200⟩, ⟨0x2000, 0⟩] }

theorem xofSqueeze_verified (v : Permutation) {X : Xof} (hr : X.rate ∈ rates) :
    Verified AArch64.target (xofSqueeze v.callee X.rate)
      (Spec.Sha3.xofSqueezeContract AArch64.abi X (16 + 640)) := by
  refine AArch64.Verified.stackScratch (sig := Spec.Sha3.xofSqueezeSig) (nm := "scratch")
    (e := .u64) (n := 80) (pre := Spec.Sha3.xofSqueezePre X AArch64.abi.ptrBits)
    (post := Spec.Sha3.xofSqueezePost X AArch64.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 640) (xofSqueezeS_verified v hr) (by decide) (by decide) ⟨xofSqueezeTopSat, ?_⟩
  sig_pre [Spec.Sha3.xofSqueezeContract, Spec.Sha3.xofSqueezeSig, Spec.Sha3.xofSqueezePre,
    Spec.Sha3.xofSqueezePost, AArch64.abi, AArch64.argRegs, xofSqueezeTopSat, xofSqueezeSat,
    Stream.Squeeze.sat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Nat.zero_le _

/-! ## SHA-3's `finalize` -/

/-- SHA-3's `finalize`'s contract on AArch64 for `H`, with its working space
(672 bytes) passed in `x3` (`state = x0, pos = x1, out = x2, scratch = x3`);
its calls use the 16 bytes below the stack pointer. -/
def finAArch64 (H : Spec.Sha3.HashFn) : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 200⟩
    let out : Region := ⟨s.gpr .x2, H.len⟩
    let scratch : Region := ⟨s.gpr .x3, 672⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    (s.gpr .x1).toNat < H.rate
  post s s' := ∀ msg, Repr s.mem (s.gpr .x0) H.rate msg →
    (s.gpr .x1).toNat = msg.length % H.rate → bytesAt s'.mem (s.gpr .x2) H.len = H.digest msg
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

/-- Where `finalize`'s buffers are, and the 16 bytes of stack below the
stack pointer at `K + 16`. -/
structure Lay (st op sc K : Addr) (len : Nat) : Prop where
  st_op : Region.Disjoint ⟨st, 200⟩ ⟨op, len⟩
  st_sc : Region.Disjoint ⟨st, 200⟩ ⟨sc, 672⟩
  op_sc : Region.Disjoint ⟨op, len⟩ ⟨sc, 672⟩
  stk_st : Region.Disjoint ⟨K, 16⟩ ⟨st, 200⟩
  stk_op : Region.Disjoint ⟨K, 16⟩ ⟨op, len⟩
  stk_sc : Region.Disjoint ⟨K, 16⟩ ⟨sc, 672⟩

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

/-- After `finPadArgs`. -/
theorem finPad_ok {rate : Nat} (hr : rate < 2 ^ 16) {s : State} (hw : ⟨s.gpr .x3, 672⟩ ∈ s.wr) :
    WP isa (.block (finPadArgs rate)) s fun t =>
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v ∧
      t.mem = (((s.mem.writeW (s.gpr .x3 + BitVec.ofNat 64 664) (s.gpr .x30)).writeW
        (s.gpr .x3 + BitVec.ofNat 64 640) (s.gpr .x19)).writeW (s.gpr .x3 + BitVec.ofNat 64 648)
        (s.gpr .x20)).writeW (s.gpr .x3 + BitVec.ofNat 64 656) (s.gpr .x21) ∧
      t.gpr .x0 = s.gpr .x0 ∧ t.gpr .x19 = s.gpr .x0 ∧ t.gpr .x20 = s.gpr .x2 ∧
      t.gpr .x21 = s.gpr .x3 ∧ t.gpr .x2 = s.gpr .x1 ∧ t.gpr .x1 = BitVec.ofNat 64 rate ∧
      t.gpr .x3 = BitVec.ofNat 64 0x06 ∧ t.gpr .x4 = s.gpr .x3 ∧
      ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → t.gpr r = s.gpr r := by
  have h1 := in_scr (s := s) (d := 664) (by omega) hw
  have h2 := in_scr (s := s) (d := 640) (by omega) hw
  have h3 := in_scr (s := s) (d := 648) (by omega) hw
  have h4 := in_scr (s := s) (d := 656) (by omega) hw
  unfold finPadArgs
  refine wcons (exec_str_x (by decide) h1) (wcons (exec_str_x (by decide) h2)
    (wcons (exec_str_x (by decide) h3) (wcons (exec_str_x (by decide) h4) (wcons exec_mov
    (wcons exec_mov (wcons exec_mov (wcons exec_mov (wcons (exec_li hr) (wcons (exec_li (by decide))
    (wcons exec_mov (WP.block_nil ?_)))))))))))
  simp only [RegUpd.gpr_write, RegUpd.mem_write, RegUpd.wr_write, RegUpd.rd_write, RegUpd.sp_write,
    RegUpd.v_write, BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false]
  iterate 13 refine ⟨by first | trivial | rfl, ?_⟩
  intro r hr h19 h20 h21
  have hne : r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 ∧ r ≠ .x4 := by revert r; decide
  simp only [h19, h20, h21, hne.1, hne.2.1, hne.2.2.1, hne.2.2.2, ite_false]

theorem gpr_ce (t : State) (rd wr : List Region) {r : Reg} (h : r ∉ linkRegs := by decide) :
    (t.callEntry.withRegions rd wr).gpr r = t.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h]

/-- `pad`'s precondition at the call, narrowed to the state and the first
640 bytes of `scratch`. -/
theorem finPad_pre {st op sc K : Addr} {len rate : Nat} (hL : Lay st op sc K len) (hr : rate ∈ rates)
    {t : State} (h0 : t.gpr .x0 = st) (h1 : t.gpr .x1 = BitVec.ofNat 64 rate)
    (h2 : (t.gpr .x2).toNat < rate) (h4 : t.gpr .x4 = sc) (hsp : t.sp = K + 16)
    (h16 : 16 ≤ t.sp.toNat) :
    Proof.Sha3.padAArch64.pre (t.callEntry.withRegions [] [⟨st, 200⟩, ⟨sc, 640⟩]) := by
  have hK : t.sp - 16 = K := by rw [hsp]; exact BitVec.add_sub_cancel _ _
  simp (disch := decide) only [Proof.Sha3.padAArch64, gpr_ce, State.withRegions_sp,
    State.callEntry_sp, State.withRegions_rd, State.withRegions_wr, h0, h1, h4, hK, toNat_rate hr]
  exact ⟨trivial, trivial, hL.st_sc.sub_right (sub_prefix sc (by omega)), h16, hL.stk_st,
    hL.stk_sc.sub_right (sub_prefix sc (by omega)), hr, h2⟩

theorem finPad_cov {st op sc : Addr} {len : Nat} {t : State}
    (hwr : t.wr = [⟨st, 200⟩, ⟨op, len⟩, ⟨sc, 672⟩]) :
    Covers ([] ++ [⟨st, 200⟩, ⟨sc, 640⟩]) (t.rd ++ t.wr) ∧ Covers [⟨st, 200⟩, ⟨sc, 640⟩] t.wr := by
  refine ⟨Covers.of_sub fun r hr' => ?_, Covers.of_sub fun r hr' => ?_⟩
  all_goals
    simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact ⟨⟨st, 200⟩, by simp [hwr], 0, by simp, by simp⟩
    · exact ⟨⟨sc, 672⟩, by simp [hwr], 0, by simp, by simp⟩

/-- What a call of `pad` or `squeeze` keeps. -/
structure Kept (t u : State) : Prop where
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  sp : u.sp = t.sp
  gpr : ∀ r ∈ preserved, r ≠ .x30 → u.gpr r = t.gpr r
  v : ∀ r ∈ VG.AArch64.preservedV, (u.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64

/-- The call of `pad`, with SHA-3's suffix. -/
theorem finPadCall (v : Permutation) {st op sc K : Addr} {len rate : Nat} (hL : Lay st op sc K len)
    (hr : rate ∈ rates) {t : State} (hwr : t.wr = [⟨st, 200⟩, ⟨op, len⟩, ⟨sc, 672⟩])
    (h0 : t.gpr .x0 = st) (h1 : t.gpr .x1 = BitVec.ofNat 64 rate) (h2 : (t.gpr .x2).toNat < rate)
    (h3 : t.gpr .x3 = BitVec.ofNat 64 0x06) (h4 : t.gpr .x4 = sc) (hsp : t.sp = K + 16)
    (h16 : 16 ≤ t.sp.toNat) :
    WP isa (.call ("vg_keccak_pad_scratch" ++ v.callee.suffix)
        (Impl.Sha3.AArch64.Stream.padWith v.callee)) t fun u =>
      Kept t u ∧ Frame [⟨st, 200⟩, ⟨sc, 640⟩, ⟨K, 16⟩] t.mem u.mem ∧
      ∀ msg, Repr t.mem st rate msg → (t.gpr .x2).toNat = msg.length % rate →
        stateAt u.mem st = Spec.Sha3.absorb rate (Spec.Sha3.pad rate Spec.Sha3.sha3Suffix msg) := by
  have hK : t.sp - BitVec.ofNat 64 16 = K := by rw [hsp]; exact BitVec.add_sub_cancel _ _
  refine WP.callFV (k := Proof.Sha3.padAArch64) (Stream.Pad.pad_correct v) (rd := [])
    (wr := [⟨st, 200⟩, ⟨sc, 640⟩]) (finPad_pre hL hr h0 h1 h2 h4 hsp h16) (finPad_cov hwr).1
    (finPad_cov hwr).2
    (fun u u1 u2 u3 u4 u5 u6 hpost => ⟨⟨u1, u2, u3, u5, u6⟩,
      by rw [v.pad_depth] at u4; simpa [below, hK] using u4, fun msg hm hp => ?_⟩)
    (by rw [v.pad_depth]; decide)
  simp (disch := decide) only [Proof.Sha3.padAArch64, gpr_ce, State.withRegions_mem,
    State.callEntry_mem, h0, h1, h3, toNat_rate hr] at hpost
  rw [hpost msg hm hp]
  rfl

/-- `squeeze`'s precondition at the call. -/
theorem finSqz_pre {st op sc K : Addr} {len rate : Nat} (hL : Lay st op sc K len) (hr : rate ∈ rates)
    (hl : len < 2 ^ 16) {t : State} (h0 : t.gpr .x0 = st) (h1 : t.gpr .x1 = BitVec.ofNat 64 rate)
    (h2 : t.gpr .x2 = BitVec.ofNat 64 0) (h3 : t.gpr .x3 = op) (h4 : t.gpr .x4 = BitVec.ofNat 64 len)
    (h5 : t.gpr .x5 = sc) (hsp : t.sp = K + 16) (h16 : 16 ≤ t.sp.toNat) :
    Proof.Sha3.squeezeAArch64.pre
      (t.callEntry.withRegions [] [⟨st, 200⟩, ⟨op, len⟩, ⟨sc, 640⟩]) := by
  have hK : t.sp - 16 = K := by rw [hsp]; exact BitVec.add_sub_cancel _ _
  have hl' : (BitVec.ofNat 64 len).toNat = len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp (disch := decide) only [Proof.Sha3.squeezeAArch64, gpr_ce, State.withRegions_sp,
    State.callEntry_sp, State.withRegions_rd, State.withRegions_wr, h0, h1, h2, h3, h4, h5, hK,
    toNat_rate hr, hl']
  exact ⟨trivial, trivial, hL.st_op, hL.st_sc.sub_right (sub_prefix sc (by omega)),
    hL.op_sc.sub_right (sub_prefix sc (by omega)), h16, hL.stk_st, hL.stk_op,
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
theorem finSqzCall (v : Permutation) {st op sc K : Addr} {len rate : Nat} (hL : Lay st op sc K len)
    (hr : rate ∈ rates) (hl : len < 2 ^ 16) {t : State}
    (hwr : t.wr = [⟨st, 200⟩, ⟨op, len⟩, ⟨sc, 672⟩])
    (h0 : t.gpr .x0 = st) (h1 : t.gpr .x1 = BitVec.ofNat 64 rate) (h2 : t.gpr .x2 = BitVec.ofNat 64 0)
    (h3 : t.gpr .x3 = op) (h4 : t.gpr .x4 = BitVec.ofNat 64 len) (h5 : t.gpr .x5 = sc)
    (hsp : t.sp = K + 16) (h16 : 16 ≤ t.sp.toNat) :
    WP isa (.call ("vg_keccak_squeeze_scratch" ++ v.callee.suffix)
        (Impl.Sha3.AArch64.Stream.squeezeWith v.callee)) t fun u =>
      Kept t u ∧ Frame [⟨st, 200⟩, ⟨op, len⟩, ⟨sc, 640⟩, ⟨K, 16⟩] t.mem u.mem ∧
      bytesAt u.mem op len = Spec.Sha3.squeezeFrom rate (stateAt t.mem st) 0 len := by
  have hK : t.sp - BitVec.ofNat 64 16 = K := by rw [hsp]; exact BitVec.add_sub_cancel _ _
  have hl' : (BitVec.ofNat 64 len).toNat = len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine WP.callFV (k := Proof.Sha3.squeezeAArch64) (Stream.Squeeze.squeeze_correct v) (rd := [])
    (wr := [⟨st, 200⟩, ⟨op, len⟩, ⟨sc, 640⟩])
    (finSqz_pre hL hr hl h0 h1 h2 h3 h4 h5 hsp h16) (finSqz_cov hwr).1 (finSqz_cov hwr).2
    (fun u u1 u2 u3 u4 u5 u6 hpost => ⟨⟨u1, u2, u3, u5, u6⟩,
      by rw [v.squeeze_depth] at u4; simpa [below, hK] using u4, ?_⟩)
    (by rw [v.squeeze_depth]; decide)
  obtain ⟨hp, -⟩ := hpost
  simp (disch := decide) only [gpr_ce, State.withRegions_mem, State.callEntry_mem, h0, h1, h2, h3,
    h4, toNat_rate hr, hl'] at hp
  rw [hp]
  simp

/-- After `finSqzArgs`. -/
theorem finSqz_ok {rate len : Nat} (hr : rate < 2 ^ 16) (hl : len < 2 ^ 16) (s : State) :
    WP isa (.block (finSqzArgs rate len)) s fun t =>
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v ∧ t.mem = s.mem ∧
      t.gpr .x0 = s.gpr .x19 ∧ t.gpr .x1 = BitVec.ofNat 64 rate ∧ t.gpr .x2 = BitVec.ofNat 64 0 ∧
      t.gpr .x3 = s.gpr .x20 ∧ t.gpr .x4 = BitVec.ofNat 64 len ∧ t.gpr .x5 = s.gpr .x21 ∧
      ∀ r ∈ preserved, t.gpr r = s.gpr r := by
  unfold finSqzArgs
  refine wcons exec_mov (wcons (exec_li hr) (wcons (exec_li (by decide)) (wcons exec_mov
    (wcons (exec_li hl) (wcons exec_mov (WP.block_nil ?_))))))
  simp only [RegUpd.gpr_write, RegUpd.mem_write, RegUpd.wr_write, RegUpd.rd_write, RegUpd.sp_write,
    RegUpd.v_write, BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false]
  iterate 11 refine ⟨by first | trivial | rfl, ?_⟩
  intro r hr
  obtain ⟨h1, h2, h3, h4, h5⟩ := preserved_ne r hr
  have h0 : r ≠ .x0 := by revert r; decide
  simp only [h0, h1, h2, h3, h4, h5, ite_false]

/-- After `finRestore`, from a state with `x21` = `sc`. -/
theorem finRestore_ok {sc : Addr} {s : State} (h21 : s.gpr .x21 = sc)
    (h1 : InRegions (s.rd ++ s.wr) (sc + BitVec.ofNat 64 664) 8)
    (h2 : InRegions (s.rd ++ s.wr) (sc + BitVec.ofNat 64 640) 8)
    (h3 : InRegions (s.rd ++ s.wr) (sc + BitVec.ofNat 64 648) 8)
    (h4 : InRegions (s.rd ++ s.wr) (sc + BitVec.ofNat 64 656) 8) :
    WP isa (.block finRestore) s fun t =>
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v ∧ t.mem = s.mem ∧
      t.gpr .x30 = s.mem.readW (sc + BitVec.ofNat 64 664) 64 ∧
      t.gpr .x19 = s.mem.readW (sc + BitVec.ofNat 64 640) 64 ∧
      t.gpr .x20 = s.mem.readW (sc + BitVec.ofNat 64 648) 64 ∧
      t.gpr .x21 = s.mem.readW (sc + BitVec.ofNat 64 656) 64 ∧
      ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x30 → t.gpr r = s.gpr r := by
  unfold finRestore
  refine wcons (exec_ldr_x (by decide) (by rw [h21]; exact h1)) (wcons
    (exec_ldr_x (by decide) (by simpa [RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, h21] using h2))
    (wcons (exec_ldr_x (by decide) (by simpa [RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, h21] using h3))
    (wcons (exec_ldr_x (by decide) (by simpa [RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, h21] using h4))
    (WP.block_nil ?_))))
  simp only [RegUpd.gpr_write, RegUpd.mem_write, RegUpd.wr_write, RegUpd.rd_write, RegUpd.sp_write,
    RegUpd.v_write, BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false, h21]
  iterate 9 refine ⟨by first | trivial | rfl, ?_⟩
  intro r hr h19 h20 h21' h30
  simp only [h19, h20, h21', h30, ite_false]

theorem bytesAt_frame {rs : List Region} {m m' : Mem} {p : Addr} {n : Nat} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [Spec.Sha3.bytesAt]
  exact List.map_congr_left fun i hi => hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

/-- The layout `finAArch64`'s precondition gives, with `K = sp - 16`. -/
theorem lay_of_pre {H : Spec.Sha3.HashFn} {s : State} (hp : (finAArch64 H).pre s) :
    Lay (s.gpr .x0) (s.gpr .x2) (s.gpr .x3) (s.sp - 16) H.len ∧ s.sp = s.sp - 16 + 16 := by
  obtain ⟨-, -, p3, p4, p5, -, p7, p8, p9, -⟩ := hp
  exact ⟨⟨p3, p4, p5, p7, p8, p9⟩, (BitVec.sub_add_cancel _ _).symm⟩

/-- `finBody` meets `finAArch64` and the ABI. -/
theorem finBody_correct (v : Permutation) {H : Spec.Sha3.HashFn} (hH : hashSponge H)
    (hr : H.rate ∈ rates) (hl : H.len < 2 ^ 16) {s : State} (hp : (finAArch64 H).pre s) :
    WP isa (finBody v.callee H.rate H.len) s fun s' =>
      abiPreserved s s' ∧ (finAArch64 H).post s s' := by
  obtain ⟨hL, hsp⟩ := lay_of_pre hp
  obtain ⟨p1, p2, -, -, -, p6, -, -, -, p10⟩ := hp
  generalize s.sp - 16 = K at hL hsp
  have hr16 : H.rate < 2 ^ 16 := by have := rate_lt hr; omega
  have hw : ⟨s.gpr .x3, 672⟩ ∈ s.wr := by rw [p2]; simp
  -- The four saved words, beyond what the calls use.
  have hslot : ∀ d, 640 ≤ d → d + 8 ≤ 672 →
      ∀ r ∈ [(⟨s.gpr .x0, 200⟩ : Region), ⟨s.gpr .x2, H.len⟩, ⟨s.gpr .x3, 640⟩, ⟨K, 16⟩],
        Region.Disjoint ⟨s.gpr .x3 + BitVec.ofNat 64 d, 8⟩ r := by
    intro d h1 h2 r hr
    have hsub : Region.Sub ⟨s.gpr .x3 + BitVec.ofNat 64 d, 8⟩ ⟨s.gpr .x3, 672⟩ :=
      Offset.sub_base _ (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (hL.st_sc.symm).sub_left hsub
    · exact (hL.op_sc.symm).sub_left hsub
    · exact Offset.disjoint_base _ (by omega) (by omega)
    · exact (hL.stk_sc.symm).sub_left hsub
  refine WP.seq (WP.mono (finPad_ok hr16 hw) fun t ⟨trd, twr, tsp, tv, tmem, t0, t19, t20,
    t21, t2, t1, t3, t4, toth⟩ => ?_)
  refine WP.seq (WP.mono (finPadCall v hL hr (by rw [twr, p2]) t0 t1 (by rw [t2]; exact p10) t3 t4
    (by rw [tsp, hsp]) (by rw [tsp]; exact p6))
    fun u ⟨uk, uf, upad⟩ => ?_)
  refine WP.seq (WP.mono (finSqz_ok hr16 hl u) fun w ⟨wrd, wwr, wsp, wv, wmem, w0, w1, w2, w3,
    w4, w5, wpr⟩ => ?_)
  have u19 : u.gpr .x19 = s.gpr .x0 := by rw [uk.gpr .x19 (by decide) (by decide), t19]
  have u20 : u.gpr .x20 = s.gpr .x2 := by rw [uk.gpr .x20 (by decide) (by decide), t20]
  have u21 : u.gpr .x21 = s.gpr .x3 := by rw [uk.gpr .x21 (by decide) (by decide), t21]
  refine WP.seq (WP.mono (finSqzCall v hL hr hl (by rw [wwr, uk.wr, twr, p2]) (by rw [w0, u19]) w1
    w2 (by rw [w3, u20]) w4 (by rw [w5, u21]) (by rw [wsp, uk.sp, tsp, hsp])
    (by rw [wsp, uk.sp, tsp]; exact p6))
    fun x ⟨xk, xf, xout⟩ => ?_)
  have x21 : x.gpr .x21 = s.gpr .x3 := by
    rw [xk.gpr .x21 (by decide) (by decide), wpr .x21 (by decide), u21]
  have hin : ∀ d, d + 8 ≤ 672 → InRegions (x.rd ++ x.wr) (s.gpr .x3 + BitVec.ofNat 64 d) 8 :=
    fun d hd => in_scr' hd (by rw [xk.wr, wwr, uk.wr, twr]; exact hw)
  refine WP.mono (finRestore_ok x21 (hin 664 (by omega)) (hin 640 (by omega)) (hin 648 (by omega))
    (hin 656 (by omega))) fun y ⟨yrd, ywr, ysp, yv, ymem, y30, y19, y20, y21, yoth⟩ => ?_
  have fx : Frame [⟨s.gpr .x0, 200⟩, ⟨s.gpr .x2, H.len⟩, ⟨s.gpr .x3, 640⟩, ⟨K, 16⟩] t.mem x.mem := by
    refine (uf.mono fun r hr => ?_).trans (wmem ▸ xf)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl <;> simp
  have slot : ∀ d, 640 ≤ d → d + 8 ≤ 672 →
      x.mem.readW (s.gpr .x3 + BitVec.ofNat 64 d) 64 = t.mem.readW (s.gpr .x3 + BitVec.ofNat 64 d) 64 :=
    fun d h1 h2 => readW_frame fx (hslot d h1 h2)
  have sep : ∀ a b, 640 ≤ a → a + 8 ≤ 672 → 640 ≤ b → b + 8 ≤ 672 → a ≠ b → a % 8 = 0 → b % 8 = 0 →
      Mem.Sep (s.gpr .x3 + BitVec.ofNat 64 a) (64 / 8) (s.gpr .x3 + BitVec.ofNat 64 b) (64 / 8) :=
    fun a b _ _ _ _ hab ha hb => Offset.sep _ (by omega) (by omega) (by omega)
  have t664 : t.mem.readW (s.gpr .x3 + BitVec.ofNat 64 664) 64 = s.gpr .x30 := by
    rw [tmem, Mem.readW_writeW_sep (sep 664 656 (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 664 648 (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 664 640 (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)) (by decide), Mem.readW_writeW_self64]
  have t640 : t.mem.readW (s.gpr .x3 + BitVec.ofNat 64 640) 64 = s.gpr .x19 := by
    rw [tmem, Mem.readW_writeW_sep (sep 640 656 (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 640 648 (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)) (by decide), Mem.readW_writeW_self64]
  have t648 : t.mem.readW (s.gpr .x3 + BitVec.ofNat 64 648) 64 = s.gpr .x20 := by
    rw [tmem, Mem.readW_writeW_sep (sep 648 656 (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)) (by decide), Mem.readW_writeW_self64]
  have t656 : t.mem.readW (s.gpr .x3 + BitVec.ofNat 64 656) 64 = s.gpr .x21 := by
    rw [tmem, Mem.readW_writeW_self64]
  have ft : Frame [⟨s.gpr .x3, 672⟩] s.mem t.mem := by
    rw [tmem]
    refine Frame.writeW (Frame.writeW (Frame.writeW (Frame.writeW (Frame.refl _ _)
      (List.mem_singleton_self _) _ ?_) (List.mem_singleton_self _) _ ?_)
      (List.mem_singleton_self _) _ ?_) (List.mem_singleton_self _) _ ?_
    all_goals exact Offset.contains_base _ (by omega) (by omega)
  refine ⟨⟨fun r hr => ?_, by rw [ysp, xk.sp, wsp, uk.sp, tsp], fun r hr => ?_⟩, fun msg hm hpos => ?_⟩
  · by_cases h19 : r = .x19
    · subst h19; rw [y19, slot 640 (by omega) (by omega), t640]
    by_cases h20 : r = .x20
    · subst h20; rw [y20, slot 648 (by omega) (by omega), t648]
    by_cases h21 : r = .x21
    · subst h21; rw [y21, slot 656 (by omega) (by omega), t656]
    by_cases h30 : r = .x30
    · subst h30; rw [y30, slot 664 (by omega) (by omega), t664]
    rw [yoth r hr h19 h20 h21 h30, xk.gpr r hr h30, wpr r hr, uk.gpr r hr h30, toth r hr h19 h20 h21]
  · rw [yv, xk.v r hr, wv, uk.v r hr, tv]
  · have hst : stateAt t.mem (s.gpr .x0) = stateAt s.mem (s.gpr .x0) :=
      stateAt_frame ft (by intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hL.st_sc)
    have hpad := upad msg (by unfold Spec.Sha3.Repr; rw [hst]; exact hm) (by rw [t2]; exact hpos)
    show bytesAt y.mem (s.gpr .x2) H.len = H.digest msg
    rw [ymem, xout, wmem, hpad]
    exact digest_of_pad hH rfl

/-! ### Constant time -/

def G1 (rate : Nat) (σ t : State) : Prop :=
  t.rd = σ.rd ∧ t.wr = σ.wr ∧ t.gpr .x0 = σ.gpr .x0 ∧ t.gpr .x1 = BitVec.ofNat 64 rate ∧
    t.gpr .x2 = σ.gpr .x1 ∧ t.gpr .x3 = BitVec.ofNat 64 0x06 ∧ t.gpr .x4 = σ.gpr .x3 ∧
    t.gpr .x19 = σ.gpr .x0 ∧ t.gpr .x20 = σ.gpr .x2 ∧ t.gpr .x21 = σ.gpr .x3 ∧ t.sp = σ.sp

def G2 (σ u : State) : Prop :=
  u.rd = σ.rd ∧ u.wr = σ.wr ∧ u.gpr .x19 = σ.gpr .x0 ∧ u.gpr .x20 = σ.gpr .x2 ∧
    u.gpr .x21 = σ.gpr .x3 ∧ u.sp = σ.sp

def G3 (rate len : Nat) (σ w : State) : Prop :=
  w.rd = σ.rd ∧ w.wr = σ.wr ∧ w.gpr .x0 = σ.gpr .x0 ∧ w.gpr .x1 = BitVec.ofNat 64 rate ∧
    w.gpr .x2 = BitVec.ofNat 64 0 ∧ w.gpr .x3 = σ.gpr .x2 ∧ w.gpr .x4 = BitVec.ofNat 64 len ∧
    w.gpr .x5 = σ.gpr .x3 ∧ w.gpr .x21 = σ.gpr .x3 ∧ w.sp = σ.sp

theorem g1_ok {H : Spec.Sha3.HashFn} (hr : H.rate < 2 ^ 16) {σ : State} (hp : (finAArch64 H).pre σ) :
    WP isa (.block (finPadArgs H.rate)) σ (G1 H.rate σ) :=
  WP.mono (finPad_ok hr (by rw [hp.2.1]; simp))
    fun _ ⟨h1, h2, h3, _, _, h6, h7, h8, h9, h10, h11, h12, h13, _⟩ =>
      ⟨h1, h2, h6, h11, h10, h12, h13, h7, h8, h9, h3⟩

theorem g2_ok (v : Permutation) {H : Spec.Sha3.HashFn} (hr : H.rate ∈ rates) {σ t : State}
    (hp : (finAArch64 H).pre σ) (h : G1 H.rate σ t) :
    WP isa (.call ("vg_keccak_pad_scratch" ++ v.callee.suffix)
      (Impl.Sha3.AArch64.Stream.padWith v.callee)) t (G2 σ) := by
  obtain ⟨hL, hsp⟩ := lay_of_pre hp
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  refine WP.mono (finPadCall v hL hr (by rw [h2, hp.2.1]) h3 h4
    (by rw [h5]; exact hp.2.2.2.2.2.2.2.2.2) h6 h7 (by rw [h11, ← hsp])
    (by rw [h11]; exact hp.2.2.2.2.2.1)) fun u ⟨uk, _, _⟩ =>
      ⟨by rw [uk.rd, h1], by rw [uk.wr, h2], by rw [uk.gpr .x19 (by decide) (by decide), h8],
        by rw [uk.gpr .x20 (by decide) (by decide), h9],
        by rw [uk.gpr .x21 (by decide) (by decide), h10], by rw [uk.sp, h11]⟩

theorem g3_ok {H : Spec.Sha3.HashFn} (hr : H.rate < 2 ^ 16) (hl : H.len < 2 ^ 16) {σ u : State}
    (h : G2 σ u) : WP isa (.block (finSqzArgs H.rate H.len)) u (G3 H.rate H.len σ) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine WP.mono (finSqz_ok hr hl u) fun w ⟨w1, w2, w3, _, _, w6, w7, w8, w9, w10, w11, w12⟩ =>
    ⟨by rw [w1, h1], by rw [w2, h2], by rw [w6, h3], w7, w8, by rw [w9, h4], w10, by rw [w11, h5],
      by rw [w12 .x21 (by decide), h5], by rw [w3, h6]⟩

theorem g4_ok (v : Permutation) {H : Spec.Sha3.HashFn} (hr : H.rate ∈ rates) (hl : H.len < 2 ^ 16)
    {σ w : State} (hp : (finAArch64 H).pre σ) (h : G3 H.rate H.len σ w) :
    WP isa (.call ("vg_keccak_squeeze_scratch" ++ v.callee.suffix)
      (Impl.Sha3.AArch64.Stream.squeezeWith v.callee)) w
      fun x => x.gpr .x21 = σ.gpr .x3 ∧ x.sp = σ.sp := by
  obtain ⟨hL, hsp⟩ := lay_of_pre hp
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact WP.mono (finSqzCall v hL hr hl (by rw [h2, hp.2.1]) h3 h4 h5 h6 h7 h8 (by rw [h10, ← hsp])
    (by rw [h10]; exact hp.2.2.2.2.2.1)) fun x ⟨xk, _⟩ =>
      ⟨by rw [xk.gpr .x21 (by decide) (by decide), h9], by rw [xk.sp, h10]⟩

theorem finBody_ct (v : Permutation) {H : Spec.Sha3.HashFn} (hr : H.rate ∈ rates)
    (hl : H.len < 2 ^ 16) {h₁ h₂ h₃ : VG.Taint.Hint VG.AArch64.Taint.T}
    (hb₁ : (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3]) (.block (finPadArgs H.rate))
      h₁).isSome = true)
    (hb₂ : (taint.check (Taint.ofRegs []) (.block (finSqzArgs H.rate H.len)) h₂).isSome = true)
    (hb₃ : (taint.check (Taint.ofRegs [.x21]) (.block finRestore) h₃).isSome = true) :
    ConstantTime isa (finAArch64 H).pre (finAArch64 H).pub (finBody v.callee H.rate H.len) := by
  intro σ₁ σ₂ t₁ t₂ σ₁' σ₂' p₁ p₂ hp e₁ e₂
  obtain ⟨q0, q1, q2, q3, qsp⟩ := hp
  have hr16 : H.rate < 2 ^ 16 := by have := rate_lt hr; omega
  have hP : RelCT isa (fun a b => a = σ₁ ∧ b = σ₂) (finBody v.callee H.rate H.len)
      fun _ _ => True := by
    unfold finBody
    refine RelCT.seq (RelCT.wp (F₁ := G1 H.rate σ₁) (F₂ := G1 H.rate σ₂)
      (RelCT.taint (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
        (fun a b ⟨ea, eb⟩ => by
          subst ea eb
          refine ⟨qsp, fun r hr => ?_⟩
          simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption) hb₁)
      fun a b ⟨ea, eb⟩ => by subst ea eb; exact ⟨g1_ok hr16 p₁, g1_ok hr16 p₂⟩) ?_
    refine RelCT.seq (RelCT.wp (F₁ := G2 σ₁) (F₂ := G2 σ₂)
      (RelCT.call (Stream.Pad.pad_correct v) (Stream.Pad.pad_ct v) []
        [⟨σ₁.gpr .x0, 200⟩, ⟨σ₁.gpr .x3, 640⟩] fun a b ⟨_, ha, hb⟩ => ?_)
      fun a b ⟨_, ha, hb⟩ => ⟨g2_ok v hr p₁ ha, g2_ok v hr p₂ hb⟩) ?_
    · obtain ⟨hL₁, hs₁⟩ := lay_of_pre p₁
      obtain ⟨hL₂, hs₂⟩ := lay_of_pre p₂
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := ha
      obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := hb
      have pb := finPad_pre hL₂ hr b3 b4 (by rw [b5]; exact p₂.2.2.2.2.2.2.2.2.2) b7
        (by rw [b11, ← hs₂]) (by rw [b11]; exact p₂.2.2.2.2.2.1)
      rw [← q0, ← q3] at pb
      refine ⟨finPad_pre hL₁ hr a3 a4 (by rw [a5]; exact p₁.2.2.2.2.2.2.2.2.2) a7
        (by rw [a11, ← hs₁]) (by rw [a11]; exact p₁.2.2.2.2.2.1), pb, ?_,
        (finPad_cov (by rw [a2, p₁.2.1])).1, (finPad_cov (by rw [a2, p₁.2.1])).2,
        (finPad_cov (by rw [b2, p₂.2.1, ← q0, ← q2, ← q3])).1,
        (finPad_cov (by rw [b2, p₂.2.1, ← q0, ← q2, ← q3])).2⟩
      simp (disch := decide) only [Proof.Sha3.padAArch64, gpr_ce, State.withRegions_sp,
        State.callEntry_sp]
      exact ⟨by rw [a3, b3, q0], by rw [a4, b4], by rw [a5, b5, q1], by rw [a7, b7, q3],
        by rw [a11, b11, qsp]⟩
    refine RelCT.seq (RelCT.wp (F₁ := G3 H.rate H.len σ₁) (F₂ := G3 H.rate H.len σ₂)
      (RelCT.taint (A := taint) (Taint.ofRegs []) (fun a b ⟨_, ha, hb⟩ =>
        ⟨by rw [ha.2.2.2.2.2, hb.2.2.2.2.2, qsp], fun r h => by simp [Taint.mem_ofRegs] at h⟩)
        hb₂)
      fun a b ⟨_, ha, hb⟩ => ⟨g3_ok hr16 hl ha, g3_ok hr16 hl hb⟩) ?_
    refine RelCT.seq (RelCT.wp (F₁ := fun x : State => x.gpr .x21 = σ₁.gpr .x3 ∧ x.sp = σ₁.sp)
      (F₂ := fun x : State => x.gpr .x21 = σ₂.gpr .x3 ∧ x.sp = σ₂.sp)
      (RelCT.call (Stream.Squeeze.squeeze_correct v) (Stream.Squeeze.squeeze_ct v) []
        [⟨σ₁.gpr .x0, 200⟩, ⟨σ₁.gpr .x2, H.len⟩, ⟨σ₁.gpr .x3, 640⟩] fun a b ⟨_, ha, hb⟩ => ?_)
      fun a b ⟨_, ha, hb⟩ => ⟨g4_ok v hr hl p₁ ha, g4_ok v hr hl p₂ hb⟩) ?_
    · obtain ⟨hL₁, hs₁⟩ := lay_of_pre p₁
      obtain ⟨hL₂, hs₂⟩ := lay_of_pre p₂
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := ha
      obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := hb
      have pb := finSqz_pre hL₂ hr hl b3 b4 b5 b6 b7 b8 (by rw [b10, ← hs₂])
        (by rw [b10]; exact p₂.2.2.2.2.2.1)
      rw [← q0, ← q2, ← q3] at pb
      refine ⟨finSqz_pre hL₁ hr hl a3 a4 a5 a6 a7 a8 (by rw [a10, ← hs₁])
        (by rw [a10]; exact p₁.2.2.2.2.2.1), pb, ?_, (finSqz_cov (by rw [a2, p₁.2.1])).1,
        (finSqz_cov (by rw [a2, p₁.2.1])).2,
        (finSqz_cov (by rw [b2, p₂.2.1, ← q0, ← q2, ← q3])).1,
        (finSqz_cov (by rw [b2, p₂.2.1, ← q0, ← q2, ← q3])).2⟩
      simp (disch := decide) only [Proof.Sha3.squeezeAArch64, gpr_ce, State.withRegions_sp,
        State.callEntry_sp]
      exact ⟨by rw [a3, b3, q0], by rw [a4, b4], by rw [a5, b5], by rw [a6, b6, q2], by rw [a7, b7],
        by rw [a8, b8, q3], by rw [a10, b10, qsp]⟩
    exact RelCT.taint (A := taint) (Taint.ofRegs [.x21]) (fun a b ⟨_, ha, hb⟩ =>
      ⟨by rw [ha.2, hb.2, qsp], fun r h => by
        simp [Taint.mem_ofRegs] at h; subst h; rw [ha.1, hb.1, q3]⟩) hb₃
  exact (hP _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ### `Verified` -/

theorem finBody_verified (v : Permutation) {H : Spec.Sha3.HashFn} (hH : hashSponge H)
    (hr : H.rate ∈ rates) (hl : H.len < 2 ^ 16)
    (hct : ConstantTime isa (finAArch64 H).pre (finAArch64 H).pub (finBody v.callee H.rate H.len))
    (hsat : ∃ s, (finAArch64 H).pre s)
    (hsat' : ∃ s, (finScratchContract AArch64.abi H 84 16).pre s) :
    Verified AArch64.target (finBody v.callee H.rate H.len)
      (finScratchContract AArch64.abi H 84 16) :=
  (Verified.of_correct (fun s hs => (finBody_correct v hH hr hl hs).elim fun t ⟨s', he, h⟩ =>
      ⟨t, s', he, h.1, h.2⟩) hct (Contract.Implies.refl hsat)).of_implies
    { pre := by sig_implies_pre [VG.Proof.Sha3.Instances.finScratchContract,
          VG.Proof.Sha3.Instances.finScratchSig, Spec.Sha3.finalizePre, Spec.Sha3.finalizePost,
          finAArch64, AArch64.abi, AArch64.argRegs]
      post := by sig_implies_post [VG.Proof.Sha3.Instances.finScratchContract,
          VG.Proof.Sha3.Instances.finScratchSig, Spec.Sha3.finalizePre, Spec.Sha3.finalizePost,
          finAArch64, AArch64.abi, AArch64.argRegs]
      pub := by sig_implies_pub [VG.Proof.Sha3.Instances.finScratchContract,
          VG.Proof.Sha3.Instances.finScratchSig, Spec.Sha3.finalizePre, Spec.Sha3.finalizePost,
          finAArch64, AArch64.abi, AArch64.argRegs]
      sat := hsat' }

theorem finalize_verified (v : Permutation) {H : Spec.Sha3.HashFn} (hH : hashSponge H)
    (hr : H.rate ∈ rates) (hl : H.len < 2 ^ 16)
    (hct : ConstantTime isa (finAArch64 H).pre (finAArch64 H).pub (finBody v.callee H.rate H.len))
    (hsat : ∃ s, (finAArch64 H).pre s)
    (hsat' : ∃ s, (finScratchContract AArch64.abi H 84 16).pre s)
    (hsat'' : ∃ s, (Spec.Sha3.finalizeContract AArch64.abi H (16 + 672)).pre s) :
    Verified AArch64.target (finalize v.callee H.rate H.len)
      (Spec.Sha3.finalizeContract AArch64.abi H (16 + 672)) :=
  AArch64.Verified.stackScratch (sig := Spec.Sha3.finalizeSig H.len) (nm := "scratch") (e := .u64)
    (n := 84) (pre := Spec.Sha3.finalizePre H AArch64.abi.ptrBits)
    (post := Spec.Sha3.finalizePost H AArch64.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 672) (finBody_verified v hH hr hl hct hsat hsat') (by exact (by decide : 3 < 8))
    (by decide) hsat''

/-- A state satisfying `finAArch64`'s precondition. -/
def finSat (len : Nat) : State :=
  { Stream.Pad.sat with
    gpr := fun r => match r with | .x0 => 0x1000 | .x2 => 0x2000 | .x3 => 0x3000 | _ => 0
    wr := [⟨0x1000, 200⟩, ⟨0x2000, len⟩, ⟨0x3000, 672⟩] }

/-- The constant-time hypotheses of `finBody_ct` for an instance, from the
taint analysis of its blocks, which do not depend on the permutation. -/
macro "fin_ct" v:term : term => `(finBody_ct $v (by decide) (by decide) (by taint_decide)
  (by taint_decide) (by taint_decide))

theorem update_sha3_224 (v : Permutation) :
    Verified AArch64.target (update v.callee Spec.Sha3.hashSha3_224.rate)
      (Spec.Sha3.updateContract AArch64.abi Spec.Sha3.hashSha3_224.rate 16) :=
  update_verified v (by decide)

theorem finalize_sha3_224 (v : Permutation) :
    Verified AArch64.target
      (finalize v.callee Spec.Sha3.hashSha3_224.rate Spec.Sha3.hashSha3_224.len)
      (Spec.Sha3.finalizeContract AArch64.abi Spec.Sha3.hashSha3_224 (16 + 672)) :=
  finalize_verified v VG.Proof.Sha3.Instances.sha3_224_sponge (by decide) (by decide) (fin_ct v)
    (by implies_sat [finAArch64, Spec.Sha3.hashSha3_224] [finSat, Stream.Pad.sat] using finSat 28)
    (by implies_sat [VG.Proof.Sha3.Instances.finScratchContract,
      VG.Proof.Sha3.Instances.finScratchSig, Spec.Sha3.finalizePre, Spec.Sha3.finalizePost,
      AArch64.abi, AArch64.argRegs, Spec.Sha3.hashSha3_224] [finSat, Stream.Pad.sat] using finSat 28)
    (by implies_sat [Spec.Sha3.finalizeContract, Spec.Sha3.finalizeSig, Spec.Sha3.finalizePre,
      Spec.Sha3.finalizePost, AArch64.abi, AArch64.argRegs, Spec.Sha3.hashSha3_224]
      [finSat, Stream.Pad.sat] using { finSat 28 with wr := [⟨0x1000, 200⟩, ⟨0x2000, 28⟩] })

theorem update_sha3_256 (v : Permutation) :
    Verified AArch64.target (update v.callee Spec.Sha3.hashSha3_256.rate)
      (Spec.Sha3.updateContract AArch64.abi Spec.Sha3.hashSha3_256.rate 16) :=
  update_verified v (by decide)

theorem finalize_sha3_256 (v : Permutation) :
    Verified AArch64.target
      (finalize v.callee Spec.Sha3.hashSha3_256.rate Spec.Sha3.hashSha3_256.len)
      (Spec.Sha3.finalizeContract AArch64.abi Spec.Sha3.hashSha3_256 (16 + 672)) :=
  finalize_verified v VG.Proof.Sha3.Instances.sha3_256_sponge (by decide) (by decide) (fin_ct v)
    (by implies_sat [finAArch64, Spec.Sha3.hashSha3_256] [finSat, Stream.Pad.sat] using finSat 32)
    (by implies_sat [VG.Proof.Sha3.Instances.finScratchContract,
      VG.Proof.Sha3.Instances.finScratchSig, Spec.Sha3.finalizePre, Spec.Sha3.finalizePost,
      AArch64.abi, AArch64.argRegs, Spec.Sha3.hashSha3_256] [finSat, Stream.Pad.sat] using finSat 32)
    (by implies_sat [Spec.Sha3.finalizeContract, Spec.Sha3.finalizeSig, Spec.Sha3.finalizePre,
      Spec.Sha3.finalizePost, AArch64.abi, AArch64.argRegs, Spec.Sha3.hashSha3_256]
      [finSat, Stream.Pad.sat] using { finSat 32 with wr := [⟨0x1000, 200⟩, ⟨0x2000, 32⟩] })

theorem update_sha3_384 (v : Permutation) :
    Verified AArch64.target (update v.callee Spec.Sha3.hashSha3_384.rate)
      (Spec.Sha3.updateContract AArch64.abi Spec.Sha3.hashSha3_384.rate 16) :=
  update_verified v (by decide)

theorem finalize_sha3_384 (v : Permutation) :
    Verified AArch64.target
      (finalize v.callee Spec.Sha3.hashSha3_384.rate Spec.Sha3.hashSha3_384.len)
      (Spec.Sha3.finalizeContract AArch64.abi Spec.Sha3.hashSha3_384 (16 + 672)) :=
  finalize_verified v VG.Proof.Sha3.Instances.sha3_384_sponge (by decide) (by decide) (fin_ct v)
    (by implies_sat [finAArch64, Spec.Sha3.hashSha3_384] [finSat, Stream.Pad.sat] using finSat 48)
    (by implies_sat [VG.Proof.Sha3.Instances.finScratchContract,
      VG.Proof.Sha3.Instances.finScratchSig, Spec.Sha3.finalizePre, Spec.Sha3.finalizePost,
      AArch64.abi, AArch64.argRegs, Spec.Sha3.hashSha3_384] [finSat, Stream.Pad.sat] using finSat 48)
    (by implies_sat [Spec.Sha3.finalizeContract, Spec.Sha3.finalizeSig, Spec.Sha3.finalizePre,
      Spec.Sha3.finalizePost, AArch64.abi, AArch64.argRegs, Spec.Sha3.hashSha3_384]
      [finSat, Stream.Pad.sat] using { finSat 48 with wr := [⟨0x1000, 200⟩, ⟨0x2000, 48⟩] })

theorem update_sha3_512 (v : Permutation) :
    Verified AArch64.target (update v.callee Spec.Sha3.hashSha3_512.rate)
      (Spec.Sha3.updateContract AArch64.abi Spec.Sha3.hashSha3_512.rate 16) :=
  update_verified v (by decide)

theorem finalize_sha3_512 (v : Permutation) :
    Verified AArch64.target
      (finalize v.callee Spec.Sha3.hashSha3_512.rate Spec.Sha3.hashSha3_512.len)
      (Spec.Sha3.finalizeContract AArch64.abi Spec.Sha3.hashSha3_512 (16 + 672)) :=
  finalize_verified v VG.Proof.Sha3.Instances.sha3_512_sponge (by decide) (by decide) (fin_ct v)
    (by implies_sat [finAArch64, Spec.Sha3.hashSha3_512] [finSat, Stream.Pad.sat] using finSat 64)
    (by implies_sat [VG.Proof.Sha3.Instances.finScratchContract,
      VG.Proof.Sha3.Instances.finScratchSig, Spec.Sha3.finalizePre, Spec.Sha3.finalizePost,
      AArch64.abi, AArch64.argRegs, Spec.Sha3.hashSha3_512] [finSat, Stream.Pad.sat] using finSat 64)
    (by implies_sat [Spec.Sha3.finalizeContract, Spec.Sha3.finalizeSig, Spec.Sha3.finalizePre,
      Spec.Sha3.finalizePost, AArch64.abi, AArch64.argRegs, Spec.Sha3.hashSha3_512]
      [finSat, Stream.Pad.sat] using { finSat 64 with wr := [⟨0x1000, 200⟩, ⟨0x2000, 64⟩] })

theorem update_shake128 (v : Permutation) :
    Verified AArch64.target (update v.callee Spec.Sha3.xofShake128.rate)
      (Spec.Sha3.updateContract AArch64.abi Spec.Sha3.xofShake128.rate 16) :=
  update_verified v (by decide)

theorem finalize_shake128 (v : Permutation) :
    Verified AArch64.target (xofFinalize v.callee Spec.Sha3.xofShake128.rate)
      (Spec.Sha3.xofFinalizeContract AArch64.abi Spec.Sha3.xofShake128 (16 + 640)) :=
  xofFinalize_verified v VG.Proof.Sha3.Instances.shake128_sponge (by decide)

theorem squeeze_shake128 (v : Permutation) :
    Verified AArch64.target (xofSqueeze v.callee Spec.Sha3.xofShake128.rate)
      (Spec.Sha3.xofSqueezeContract AArch64.abi Spec.Sha3.xofShake128 (16 + 640)) :=
  xofSqueeze_verified v (by decide)

theorem update_shake256 (v : Permutation) :
    Verified AArch64.target (update v.callee Spec.Sha3.xofShake256.rate)
      (Spec.Sha3.updateContract AArch64.abi Spec.Sha3.xofShake256.rate 16) :=
  update_verified v (by decide)

theorem finalize_shake256 (v : Permutation) :
    Verified AArch64.target (xofFinalize v.callee Spec.Sha3.xofShake256.rate)
      (Spec.Sha3.xofFinalizeContract AArch64.abi Spec.Sha3.xofShake256 (16 + 640)) :=
  xofFinalize_verified v VG.Proof.Sha3.Instances.shake256_sponge (by decide)

theorem squeeze_shake256 (v : Permutation) :
    Verified AArch64.target (xofSqueeze v.callee Spec.Sha3.xofShake256.rate)
      (Spec.Sha3.xofSqueezeContract AArch64.abi Spec.Sha3.xofShake256 (16 + 640)) :=
  xofSqueeze_verified v (by decide)

end VG.Proof.Sha3.AArch64.Instances
