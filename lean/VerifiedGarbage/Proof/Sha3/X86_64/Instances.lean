module

public import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Absorb
public import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Pad
public import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Squeeze
public import VerifiedGarbage.Proof.Sha3.Instances
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
public import VerifiedGarbage.Impl.Sha3.X86_64.Instances
public import VerifiedGarbage.Spec.Sha3.Instances
import VerifiedGarbage.Proof.Framework.Prologue
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.RelCT

meta import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Absorb
meta import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Pad
meta import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Squeeze
meta import VerifiedGarbage.Proof.Sha3.Instances
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
meta import VerifiedGarbage.Impl.Sha3.X86_64.Instances
meta import VerifiedGarbage.Spec.Sha3.Instances
meta import VerifiedGarbage.Proof.Framework.Prologue
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.RelCT

/-!
# SHA-3 and SHAKE on x86-64: the functions of each instance

Each runs the sponge's code after a block that moves its arguments into the
registers that code takes them in and sets the rate (and suffix)
(`Verified.of_prologue`), so its proof is the sponge's, on the state after
that block.
-/

@[expose] public section

namespace VG.Proof.Sha3.X86_64.Instances

open VG VG.X86_64 VG.Impl.Sha3.X86_64.Instances
open VG.Spec.Sha3 (Repr bytesAt rates stateAt XofRepr Xof)
open VG.Proof.Sha3.Instances (xofSponge hashSponge xofRepr_pad xofRepr_squeeze digest_of_pad
  xofFinalizeScratchContract xofSqueezeScratchContract finScratchContract)

/-! ## `update` -/

/-- `update rate`'s contract on x86-64, with the arguments in registers
(`state = rdi, pos = rsi, data = rdx, len = rcx, scratch = r8`): that of
`absorb` (`Proof.Sha3.absorbX86_64`), with the rate `rate`. -/
def updateX86_64 (rate : Nat) : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 200⟩
    let data : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, 640⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    s.rd = [data] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch ∧
    (s.gpr .rsi).toNat < rate
  post s s' :=
    (∀ msg, Repr s.mem (s.gpr .rdi) rate msg → (s.gpr .rsi).toNat = msg.length % rate →
      Repr s'.mem (s.gpr .rdi) rate (msg ++ bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)) ∧
    (s'.gpr .rax).toNat = ((s.gpr .rsi).toNat + (s.gpr .rcx).toNat) % rate
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- The state after `updateArgs rate`. -/
def updateState (rate : Nat) (s : State) : State :=
  ((((s.setReg .r9 (s.gpr .r8)).setReg .r8 (s.gpr .rcx)).setReg .rcx (s.gpr .rdx)).setReg .rdx
    (s.gpr .rsi)).setReg32 .rsi (BitVec.ofNat 32 rate)

theorem updateArgs_run (rate : Nat) (s : State) :
    execBlock isa (updateArgs rate) s = some (updateState rate s, []) := by
  simp [updateArgs, updateState, execBlock, isa, exec, readSrc, readSrc32, addrs, srcAddrs,
    State.setReg]

theorem setWidth_ofNat {rate : Nat} (hr : rate < 2 ^ 32) :
    (BitVec.ofNat 32 rate).setWidth 64 = BitVec.ofNat 64 rate := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt (by omega_arith)]

theorem updateState_gpr {rate : Nat} (hr : rate < 2 ^ 32) (s : State) (r : Reg) :
    (updateState rate s).gpr r =
      if r = .rsi then BitVec.ofNat 64 rate else if r = .rdx then s.gpr .rsi
      else if r = .rcx then s.gpr .rdx else if r = .r8 then s.gpr .rcx
      else if r = .r9 then s.gpr .r8 else s.gpr r := by
  simp only [updateState, State.setReg32, State.setReg, setWidth_ofNat hr]

@[simp] theorem updateState_mem (rate : Nat) (s : State) : (updateState rate s).mem = s.mem := rfl
@[simp] theorem updateState_rd (rate : Nat) (s : State) : (updateState rate s).rd = s.rd := rfl
@[simp] theorem updateState_wr (rate : Nat) (s : State) : (updateState rate s).wr = s.wr := rfl
@[simp] theorem updateState_mxcsr (rate : Nat) (s : State) :
    (updateState rate s).mxcsr = s.mxcsr := rfl

/-- A state satisfying `updateX86_64`'s precondition (with no data). -/
def updateSat : State :=
  { Stream.Absorb.sat with
    gpr := fun r => match r with
      | .rdi => 0x1000 | .rdx => 0x2000 | .r8 => 0x3000 | .rsp => 0x4000 | _ => 0 }

theorem absorb_sat : ∃ s, Proof.Sha3.absorbX86_64.pre s := by
  implies_sat [Proof.Sha3.absorbX86_64, rates] [Stream.Absorb.sat] using Stream.Absorb.sat

theorem update_sat {rate : Nat} (hr : rate ∈ rates) : ∃ s, (updateX86_64 rate).pre s := by
  have h0 : 0 < rate := by simp [rates] at hr; omega
  exact ⟨updateSat, rfl, rfl, Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), h0⟩

theorem update_verified' {rate : Nat} (hr : rate ∈ rates) :
    Verified X86_64.target (update rate) (updateX86_64 rate) := by
  have hr' : rate < 2 ^ 32 := by simp [rates] at hr; omega
  have hv : Verified X86_64.target Impl.Sha3.X86_64.Stream.absorb Proof.Sha3.absorbX86_64 :=
    Verified.of_correct Stream.Absorb.absorb_correct Stream.Absorb.absorb_ct
      (Contract.Implies.refl absorb_sat)
  refine Verified.of_prologue hv (updateState rate) (fun s _ => updateArgs_run rate s)
    (fun s hs => ?_) (fun s s' _ ha => ?_) (fun s s' _ hq => ?_) (fun s₁ s₂ _ _ hp => ?_) (update_sat hr)
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hs
    simp only [Proof.Sha3.absorbX86_64, updateState_gpr hr', updateState_rd, updateState_wr]
    simp only [reduceCtorEq, ite_false, ite_true, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_trans hr' (by decide : 2 ^ 32 < 2 ^ 64))]
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hr, h11⟩
  · obtain ⟨h1, h2, h3⟩ := ha
    refine ⟨fun r hr => ?_, ?_, h3⟩
    · rw [h1 r hr, updateState_gpr hr']
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · rw [updateState_gpr hr'] at h2; simpa using h2
  · obtain ⟨h1, h2⟩ := hq
    simp only [updateState_gpr hr', updateState_mem, reduceCtorEq, ite_false, ite_true,
      BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_trans hr' (by decide : 2 ^ 32 < 2 ^ 64))] at h1 h2
    exact ⟨h1, h2⟩
  · obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hp
    simp only [Proof.Sha3.absorbX86_64, updateState_gpr hr', reduceCtorEq, ite_false, ite_true]
    exact ⟨p1, trivial, p2, p3, p4, p5, p6⟩

theorem update_verified {rate : Nat} (hr : rate ∈ rates) :
    Verified X86_64.target (update rate) (Spec.Sha3.updateContract X86_64.abi rate 8) := by
  have h0 : 0 < rate := by simp [rates] at hr; omega
  refine (update_verified' hr).of_implies
    { pre := by sig_implies_pre [Spec.Sha3.updateContract, Spec.Sha3.updateSig, Spec.Sha3.updatePre,
          Spec.Sha3.updatePost, updateX86_64, X86_64.abi, X86_64.argRegs]
      post := by sig_implies_post [Spec.Sha3.updateContract, Spec.Sha3.updateSig, Spec.Sha3.updatePre,
          Spec.Sha3.updatePost, updateX86_64, X86_64.abi, X86_64.argRegs]
      pub := by sig_implies_pub [Spec.Sha3.updateContract, Spec.Sha3.updateSig, Spec.Sha3.updatePre,
          Spec.Sha3.updatePost, updateX86_64, X86_64.abi, X86_64.argRegs]
      sat := ?_ }
  refine ⟨updateSat, ?_⟩
  sig_pre [Spec.Sha3.updateContract, Spec.Sha3.updateSig, Spec.Sha3.updatePre, Spec.Sha3.updatePost,
    X86_64.abi, X86_64.argRegs, updateSat, Stream.Absorb.sat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact h0

/-! ## SHAKE's `finalize` -/

/-- SHAKE's `finalize`'s contract on x86-64 for `X`, with its working space
passed in `rdx` (`state = rdi, pos = rsi, scratch = rdx`). -/
def xofPadX86_64 (X : Xof) : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 200⟩
    let scratch : Region := ⟨s.gpr .rdx, 640⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    s.rd = [] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ ret.Disjoint state ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint scratch ∧
    (s.gpr .rsi).toNat < X.rate
  post s s' := ∀ msg, Repr s.mem (s.gpr .rdi) X.rate msg →
    (s.gpr .rsi).toNat = msg.length % X.rate → XofRepr s'.mem (s.gpr .rdi) X.rate 0 X.xof msg 0
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rsp = s₂.gpr .rsp

/-- The state after `xofPadArgs rate`. -/
def xofPadState (rate : Nat) (s : State) : State :=
  (((s.setReg .r8 (s.gpr .rdx)).setReg .rdx (s.gpr .rsi)).setReg32 .rsi
    (BitVec.ofNat 32 rate)).setReg32 .rcx 0x1f

theorem xofPadArgs_run (rate : Nat) (s : State) :
    execBlock isa (xofPadArgs rate) s = some (xofPadState rate s, []) := by
  simp [xofPadArgs, xofPadState, execBlock, isa, exec, readSrc, readSrc32, addrs, srcAddrs,
    State.setReg]

theorem xofPadState_gpr {rate : Nat} (hr : rate < 2 ^ 32) (s : State) (r : Reg) :
    (xofPadState rate s).gpr r =
      if r = .rcx then 0x1f else if r = .rsi then BitVec.ofNat 64 rate
      else if r = .rdx then s.gpr .rsi else if r = .r8 then s.gpr .rdx else s.gpr r := by
  simp only [xofPadState, State.setReg32, State.setReg, setWidth_ofNat hr]
  split
  · simp
  · rfl

@[simp] theorem xofPadState_mem (rate : Nat) (s : State) : (xofPadState rate s).mem = s.mem := rfl
@[simp] theorem xofPadState_rd (rate : Nat) (s : State) : (xofPadState rate s).rd = s.rd := rfl
@[simp] theorem xofPadState_wr (rate : Nat) (s : State) : (xofPadState rate s).wr = s.wr := rfl
@[simp] theorem xofPadState_mxcsr (rate : Nat) (s : State) :
    (xofPadState rate s).mxcsr = s.mxcsr := rfl

/-- A state satisfying `xofPadX86_64`'s precondition. -/
def xofPadSat : State :=
  { Stream.Absorb.sat with
    gpr := fun r => match r with | .rdi => 0x1000 | .rdx => 0x3000 | .rsp => 0x4000 | _ => 0
    rd := []
    wr := [⟨0x1000, 200⟩, ⟨0x3000, 640⟩] }

theorem pad_sat : ∃ s, Proof.Sha3.padX86_64.pre s := by
  implies_sat [Proof.Sha3.padX86_64, rates] [Stream.Pad.sat] using Stream.Pad.sat

theorem xofPad_verified' {X : Xof} (hX : xofSponge X) (hr : X.rate ∈ rates) :
    Verified X86_64.target (.seq (.block (xofPadArgs X.rate)) Impl.Sha3.X86_64.Stream.pad)
      (xofPadX86_64 X) := by
  have hr' : X.rate < 2 ^ 32 := by simp [rates] at hr; omega
  have h0 : 0 < X.rate := by simp [rates] at hr; omega
  have hv : Verified X86_64.target Impl.Sha3.X86_64.Stream.pad Proof.Sha3.padX86_64 :=
    Verified.of_correct Stream.Pad.pad_correct Stream.Pad.pad_ct (Contract.Implies.refl pad_sat)
  have hsuf : (0x1f : BitVec 64).setWidth 8 = Spec.Sha3.shakeSuffix := by decide
  refine Verified.of_prologue hv (xofPadState X.rate) (fun s _ => xofPadArgs_run X.rate s)
    (fun s hs => ?_) (fun s s' _ ha => ?_) (fun s s' _ hq => ?_) (fun s₁ s₂ _ _ hp => ?_)
    ⟨xofPadSat, rfl, rfl, Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
      Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
      Region.disjoint_of_sep (by decide), h0⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hs
    simp only [Proof.Sha3.padX86_64, xofPadState_gpr hr', xofPadState_rd, xofPadState_wr]
    simp only [reduceCtorEq, ite_false, ite_true, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_trans hr' (by decide : 2 ^ 32 < 2 ^ 64))]
    exact ⟨h1, h2, h3, h4, h5, h6, h7, hr, h8⟩
  · obtain ⟨h1, h2, h3⟩ := ha
    refine ⟨fun r hr => ?_, ?_, h3⟩
    · rw [h1 r hr, xofPadState_gpr hr']
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · rw [xofPadState_gpr hr'] at h2; simpa using h2
  · intro msg hm hp
    simp only [Proof.Sha3.padX86_64, xofPadState_gpr hr', xofPadState_mem, reduceCtorEq, ite_false,
      ite_true, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_trans hr' (by decide : 2 ^ 32 < 2 ^ 64)), hsuf] at hq
    exact xofRepr_pad hX (hq msg hm hp)
  · obtain ⟨p1, p2, p3, p4⟩ := hp
    simp only [Proof.Sha3.padX86_64, xofPadState_gpr hr', reduceCtorEq, ite_false, ite_true]
    exact ⟨p1, trivial, p2, p3, p4⟩

theorem xofPad_verified {X : Xof} (hX : xofSponge X) (hr : X.rate ∈ rates) :
    Verified X86_64.target (.seq (.block (xofPadArgs X.rate)) Impl.Sha3.X86_64.Stream.pad)
      (xofFinalizeScratchContract X86_64.abi X 8) := by
  have h0 : 0 < X.rate := by simp [rates] at hr; omega
  refine (xofPad_verified' hX hr).of_implies
    { pre := by sig_implies_pre [VG.Proof.Sha3.Instances.xofFinalizeScratchContract, VG.Proof.Sha3.Instances.xofFinalizeScratchSig,
          Spec.Sha3.xofFinalizePre, Spec.Sha3.xofFinalizePost, xofPadX86_64, X86_64.abi,
          X86_64.argRegs]
      post := by sig_implies_post [VG.Proof.Sha3.Instances.xofFinalizeScratchContract, VG.Proof.Sha3.Instances.xofFinalizeScratchSig,
          Spec.Sha3.xofFinalizePre, Spec.Sha3.xofFinalizePost, xofPadX86_64, X86_64.abi,
          X86_64.argRegs]
      pub := by sig_implies_pub [VG.Proof.Sha3.Instances.xofFinalizeScratchContract, VG.Proof.Sha3.Instances.xofFinalizeScratchSig,
          Spec.Sha3.xofFinalizePre, Spec.Sha3.xofFinalizePost, xofPadX86_64, X86_64.abi,
          X86_64.argRegs]
      sat := ?_ }
  refine ⟨xofPadSat, ?_⟩
  sig_pre [VG.Proof.Sha3.Instances.xofFinalizeScratchContract, VG.Proof.Sha3.Instances.xofFinalizeScratchSig, Spec.Sha3.xofFinalizePre,
    Spec.Sha3.xofFinalizePost, X86_64.abi, X86_64.argRegs, xofPadSat, Stream.Absorb.sat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact h0

/-- A state satisfying SHAKE's `finalize`'s precondition, with no working space. -/
def xofFinalizeSat : State := { xofPadSat with wr := [⟨0x1000, 200⟩] }

theorem xofFinalize_verified {X : Xof} (hX : xofSponge X) (hr : X.rate ∈ rates)
    (hsp : (Code.seq (.block (xofPadArgs X.rate)) Impl.Sha3.X86_64.Stream.pad).all
      (fun i => !isa.writesSp i) = true := by exact VG.Code.all_of_allInstrs (by lit_decide))
    (hd : (Code.seq (.block (xofPadArgs X.rate)) Impl.Sha3.X86_64.Stream.pad).x86_64Depth ≤ 8 := by
      lit_decide) :
    Verified X86_64.target (xofFinalize X.rate) (Spec.Sha3.xofFinalizeContract X86_64.abi X 656) := by
  have h0 : 0 < X.rate := by simp [rates] at hr; omega
  refine X86_64.Verified.stackScratch (sig := Spec.Sha3.xofFinalizeSig) (nm := "scratch") (e := .u64)
    (n := 80) (pre := Spec.Sha3.xofFinalizePre X X86_64.abi.ptrBits)
    (post := Spec.Sha3.xofFinalizePost X X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 648) (xofPad_verified hX hr) (by decide) (by decide) (by decide) hsp hd
    ⟨xofFinalizeSat, ?_⟩
  sig_pre [Spec.Sha3.xofFinalizeContract, Spec.Sha3.xofFinalizeSig, Spec.Sha3.xofFinalizePre,
    Spec.Sha3.xofFinalizePost, X86_64.abi, X86_64.argRegs, xofFinalizeSat, xofPadSat,
    Stream.Absorb.sat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact h0

/-! ## SHAKE's `squeeze` -/

/-- SHAKE's `squeeze`'s contract on x86-64 for `X`, with its working space
passed in `r8` (`state = rdi, pos = rsi, out = rdx, outlen = rcx,
scratch = r8`). -/
def xofSqueezeX86_64 (X : Xof) : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 200⟩
    let out : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, 640⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    (s.gpr .rsi).toNat ≤ X.rate
  post s s' :=
    (∀ msg n, XofRepr s.mem (s.gpr .rdi) X.rate (s.gpr .rsi).toNat X.xof msg n →
      bytesAt s'.mem (s.gpr .rdx) (s.gpr .rcx).toNat = (X.xof msg (n + (s.gpr .rcx).toNat)).drop n ∧
      XofRepr s'.mem (s.gpr .rdi) X.rate (s'.gpr .rax).toNat X.xof msg (n + (s.gpr .rcx).toNat)) ∧
    (s'.gpr .rax).toNat ≤ X.rate
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- A state satisfying `xofSqueezeX86_64`'s precondition (with no output). -/
def xofSqueezeSat : State :=
  { Stream.Absorb.sat with
    gpr := fun r => match r with
      | .rdi => 0x1000 | .rdx => 0x2000 | .r8 => 0x3000 | .rsp => 0x4000 | _ => 0
    rd := []
    wr := [⟨0x1000, 200⟩, ⟨0x2000, 0⟩, ⟨0x3000, 640⟩] }

theorem squeeze_sat : ∃ s, Proof.Sha3.squeezeX86_64.pre s := by
  implies_sat [Proof.Sha3.squeezeX86_64, rates] [Stream.Squeeze.sat] using Stream.Squeeze.sat

theorem xofSqueeze_verified' {X : Xof} (hr : X.rate ∈ rates) :
    Verified X86_64.target (.seq (.block (updateArgs X.rate)) Impl.Sha3.X86_64.Stream.squeeze)
      (xofSqueezeX86_64 X) := by
  have hr' : X.rate < 2 ^ 32 := by simp [rates] at hr; omega
  have hv : Verified X86_64.target Impl.Sha3.X86_64.Stream.squeeze Proof.Sha3.squeezeX86_64 :=
    Verified.of_correct Stream.Squeeze.squeeze_correct Stream.Squeeze.squeeze_ct
      (Contract.Implies.refl squeeze_sat)
  have e64 : (BitVec.ofNat 64 X.rate).toNat = X.rate :=
    by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hr' (by decide : 2 ^ 32 < 2 ^ 64))]
  refine Verified.of_prologue hv (updateState X.rate) (fun s _ => updateArgs_run X.rate s)
    (fun s hs => ?_) (fun s s' _ ha => ?_) (fun s s' _ hq => ?_) (fun s₁ s₂ _ _ hp => ?_)
    ⟨xofSqueezeSat, rfl, rfl, Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
      Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
      Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
      Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
      Region.disjoint_of_sep (by decide), Nat.zero_le _⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hs
    simp only [Proof.Sha3.squeezeX86_64, updateState_gpr hr', updateState_rd, updateState_wr]
    simp only [reduceCtorEq, ite_false, ite_true, e64]
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hr, h12⟩
  · obtain ⟨h1, h2, h3⟩ := ha
    refine ⟨fun r hr => ?_, ?_, h3⟩
    · rw [h1 r hr, updateState_gpr hr']
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · rw [updateState_gpr hr'] at h2; simpa using h2
  · obtain ⟨h1, h2, h3⟩ := hq
    simp only [updateState_gpr hr', updateState_mem, reduceCtorEq, ite_false, ite_true, e64] at h1 h2 h3
    exact ⟨fun msg n hR => xofRepr_squeeze hR h1 h3, h2⟩
  · obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hp
    simp only [Proof.Sha3.squeezeX86_64, updateState_gpr hr', reduceCtorEq, ite_false, ite_true]
    exact ⟨p1, trivial, p2, p3, p4, p5, p6⟩

theorem xofSqueezeS_verified {X : Xof} (hr : X.rate ∈ rates) :
    Verified X86_64.target (.seq (.block (updateArgs X.rate)) Impl.Sha3.X86_64.Stream.squeeze)
      (xofSqueezeScratchContract X86_64.abi X 8) := by
  refine (xofSqueeze_verified' hr).of_implies
    { pre := by sig_implies_pre [VG.Proof.Sha3.Instances.xofSqueezeScratchContract, VG.Proof.Sha3.Instances.xofSqueezeScratchSig,
          Spec.Sha3.xofSqueezePre, Spec.Sha3.xofSqueezePost, xofSqueezeX86_64, X86_64.abi,
          X86_64.argRegs]
      post := by sig_implies_post [VG.Proof.Sha3.Instances.xofSqueezeScratchContract, VG.Proof.Sha3.Instances.xofSqueezeScratchSig,
          Spec.Sha3.xofSqueezePre, Spec.Sha3.xofSqueezePost, xofSqueezeX86_64, X86_64.abi,
          X86_64.argRegs]
      pub := by sig_implies_pub [VG.Proof.Sha3.Instances.xofSqueezeScratchContract, VG.Proof.Sha3.Instances.xofSqueezeScratchSig,
          Spec.Sha3.xofSqueezePre, Spec.Sha3.xofSqueezePost, xofSqueezeX86_64, X86_64.abi,
          X86_64.argRegs]
      sat := ?_ }
  refine ⟨xofSqueezeSat, ?_⟩
  sig_pre [VG.Proof.Sha3.Instances.xofSqueezeScratchContract, VG.Proof.Sha3.Instances.xofSqueezeScratchSig, Spec.Sha3.xofSqueezePre,
    Spec.Sha3.xofSqueezePost, X86_64.abi, X86_64.argRegs, xofSqueezeSat, Stream.Absorb.sat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Nat.zero_le _

/-- A state satisfying SHAKE's `squeeze`'s precondition, with no working space. -/
def xofSqueezeTopSat : State := { xofSqueezeSat with wr := [⟨0x1000, 200⟩, ⟨0x2000, 0⟩] }

theorem xofSqueeze_verified {X : Xof} (hr : X.rate ∈ rates)
    (hsp : (Code.seq (.block (updateArgs X.rate)) Impl.Sha3.X86_64.Stream.squeeze).all
      (fun i => !isa.writesSp i) = true := by exact VG.Code.all_of_allInstrs (by lit_decide))
    (hd : (Code.seq (.block (updateArgs X.rate)) Impl.Sha3.X86_64.Stream.squeeze).x86_64Depth ≤ 8 :=
      by lit_decide) :
    Verified X86_64.target (xofSqueeze X.rate) (Spec.Sha3.xofSqueezeContract X86_64.abi X 656) := by
  refine X86_64.Verified.stackScratch (sig := Spec.Sha3.xofSqueezeSig) (nm := "scratch") (e := .u64)
    (n := 80) (pre := Spec.Sha3.xofSqueezePre X X86_64.abi.ptrBits)
    (post := Spec.Sha3.xofSqueezePost X X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 648) (xofSqueezeS_verified hr) (by decide) (by decide) (by decide) hsp hd
    ⟨xofSqueezeTopSat, ?_⟩
  sig_pre [Spec.Sha3.xofSqueezeContract, Spec.Sha3.xofSqueezeSig, Spec.Sha3.xofSqueezePre,
    Spec.Sha3.xofSqueezePost, X86_64.abi, X86_64.argRegs, xofSqueezeTopSat, xofSqueezeSat,
    Stream.Absorb.sat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Nat.zero_le _

/-! ## SHA-3's `finalize` -/

/-- SHA-3's `finalize`'s contract on x86-64 for `H`, with its working space
(656 bytes) passed in `rcx` (`state = rdi, pos = rsi, out = rdx,
scratch = rcx`); its calls use the 16 bytes below `rsp`. -/
def finX86_64 (H : Spec.Sha3.HashFn) : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 200⟩
    let out : Region := ⟨s.gpr .rdx, H.len⟩
    let scratch : Region := ⟨s.gpr .rcx, 656⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 16, 16⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    (s.gpr .rsi).toNat < H.rate
  post s s' := ∀ msg, Repr s.mem (s.gpr .rdi) H.rate msg →
    (s.gpr .rsi).toNat = msg.length % H.rate → bytesAt s'.mem (s.gpr .rdx) H.len = H.digest msg
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

theorem in_scr {s : State} {d n : Nat} (hd : d + 8 ≤ 656) (hw : s.wr = [⟨s.gpr .rdi, 200⟩, ⟨s.gpr .rdx, n⟩,
      ⟨s.gpr .rcx, 656⟩]) :
    InRegions s.wr (s.gpr .rcx + BitVec.ofNat 64 d) 8 :=
  ⟨⟨s.gpr .rcx, 656⟩, by rw [hw]; simp, Offset.contains_base _ (by omega) (by omega)⟩

/-- After `finPadArgs`. -/
theorem finPad_ok {rate n : Nat} (hr : rate < 2 ^ 32) {s : State}
    (hw : s.wr = [⟨s.gpr .rdi, 200⟩, ⟨s.gpr .rdx, n⟩, ⟨s.gpr .rcx, 656⟩]) :
    WP isa (.block (finPadArgs rate)) s fun t =>
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr ∧
      t.mem = (s.mem.writeW (s.gpr .rcx + BitVec.ofNat 64 640) (s.gpr .r12)).writeW
        (s.gpr .rcx + BitVec.ofNat 64 648) (s.gpr .rbp) ∧
      t.gpr .rdi = s.gpr .rdi ∧ t.gpr .r12 = s.gpr .rcx ∧ t.gpr .rbp = s.gpr .rdx ∧
      t.gpr .rdx = s.gpr .rsi ∧ t.gpr .rsi = BitVec.ofNat 64 rate ∧ t.gpr .rcx = 0x06 ∧
      t.gpr .r8 = s.gpr .rcx ∧
      ∀ r, r ≠ .r12 → r ≠ .rbp → r ≠ .rdx → r ≠ .rsi → r ≠ .rcx → r ≠ .r8 → t.gpr r = s.gpr r := by
  apply WP.of_runBlock
  have h1 := in_scr (d := 640) (by omega) hw
  have h2 := in_scr (d := 648) (by omega) hw
  simp only [finPadArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32,
    State.store64, State.setReg32, ea_at, h1, h2, ite_true, Option.map_some, RegUpd.gpr_setReg,
    RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mxcsr_setReg, reduceCtorEq,
    ite_false, Option.some.injEq, exists_eq_left', setWidth_ofNat hr]
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, by decide,
    trivial, fun r h1 h2 h3 h4 h5 h6 => ?_⟩
  simp only [h1, h2, h3, h4, h5, h6, ite_false]

/-- Where `finalize`'s buffers are, and the 16 bytes of stack below the
return address at `B + 16` (`B` = `rsp - 16`). -/
structure Lay (st op sc B : Addr) (len : Nat) : Prop where
  st_op : Region.Disjoint ⟨st, 200⟩ ⟨op, len⟩
  st_sc : Region.Disjoint ⟨st, 200⟩ ⟨sc, 656⟩
  op_sc : Region.Disjoint ⟨op, len⟩ ⟨sc, 656⟩
  stk_st : Region.Disjoint ⟨B, 16⟩ ⟨st, 200⟩
  stk_op : Region.Disjoint ⟨B, 16⟩ ⟨op, len⟩
  stk_sc : Region.Disjoint ⟨B, 16⟩ ⟨sc, 656⟩
  ret_st : Region.Disjoint ⟨B + BitVec.ofNat 64 16, 8⟩ ⟨st, 200⟩
  ret_op : Region.Disjoint ⟨B + BitVec.ofNat 64 16, 8⟩ ⟨op, len⟩
  ret_sc : Region.Disjoint ⟨B + BitVec.ofNat 64 16, 8⟩ ⟨sc, 656⟩

theorem stateAt_frame {rs : List Region} {m m' : Mem} {p : Addr} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 200⟩ r) : stateAt m' p = stateAt m p :=
  Proof.Sha3.stateAt_congr fun _ hi => hf.bytes (R := ⟨p, 200⟩) hd (by show 200 ≤ 2 ^ 64; decide) hi

theorem sub_prefix (p : Addr) {n k : Nat} (h : n ≤ k) : Region.Sub ⟨p, n⟩ ⟨p, k⟩ :=
  fun _ hx => by simp only [Region.Contains] at hx ⊢; omega

theorem gpr_ce (t : State) (rd wr : List Region) {r : Reg} (h : r ≠ .rsp) :
    (t.callEntry.withRegions rd wr).gpr r = t.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h]

theorem b16_8 (B : Addr) : B + BitVec.ofNat 64 16 - 8 = B + BitVec.ofNat 64 8 := by bv_omega
theorem b8_8 (B : Addr) : B + BitVec.ofNat 64 8 - 8 = B := by bv_omega

/-- The 8 bytes at `B + 8` and below them, which a call from `B + 16` uses,
are within the stack. -/
theorem call_disj {B : Addr} {R : Region}
    (h : Region.Disjoint ⟨B, 16⟩ R) :
    Region.Disjoint ⟨B + BitVec.ofNat 64 8, 8⟩ R ∧ Region.Disjoint ⟨B, 8⟩ R :=
  ⟨h.sub_left (Offset.sub_base B (by omega)), h.sub_left (sub_prefix B (by omega))⟩

theorem pad_nosp : NoSp Impl.Sha3.X86_64.Stream.pad := by
  have : ((instrs Impl.Sha3.X86_64.Stream.pad).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro i hi; simpa using List.all_eq_true.mp this i hi

theorem squeeze_nosp : NoSp Impl.Sha3.X86_64.Stream.squeeze := by
  have : ((instrs Impl.Sha3.X86_64.Stream.squeeze).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro i hi; simpa using List.all_eq_true.mp this i hi

theorem pad_depth : Impl.Sha3.X86_64.Stream.pad.depth = 1 := by decide +kernel
theorem squeeze_depth : Impl.Sha3.X86_64.Stream.squeeze.depth = 1 := by decide +kernel

theorem pad_rdi : ∀ i ∈ instrs Impl.Sha3.X86_64.Stream.pad, Taint.clobbers i .rdi = false := by
  have : ((instrs Impl.Sha3.X86_64.Stream.pad).all fun i => !Taint.clobbers i .rdi) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro i hi; simpa using List.all_eq_true.mp this i hi

/-- `pad`'s precondition at the call, with its permissions narrowed to the
state and the first 640 bytes of `scratch`. -/
theorem finPad_pre {st op sc B : Addr} {len rate : Nat} (hL : Lay st op sc B len) (hr : rate ∈ rates)
    {t : State} (hdi : t.gpr .rdi = st) (hsi : t.gpr .rsi = BitVec.ofNat 64 rate)
    (hdx : (t.gpr .rdx).toNat < rate) (h8 : t.gpr .r8 = sc) (hsp : t.gpr .rsp = B + BitVec.ofNat 64 16) :
    Proof.Sha3.padX86_64.pre (t.callEntry.withRegions [] [⟨st, 200⟩, ⟨sc, 640⟩]) := by
  have hr64 : rate < 2 ^ 64 := by simp [rates] at hr; omega
  have hsc := hL.st_sc.sub_right (sub_prefix sc (n := 640) (by omega))
  obtain ⟨r1, r2⟩ := call_disj hL.stk_st
  obtain ⟨r3, r4⟩ := call_disj (hL.stk_sc.sub_right (sub_prefix sc (n := 640) (by omega)))
  simp only [Proof.Sha3.padX86_64, gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
    gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp),
    gpr_ce _ _ _ (by decide : Reg.r8 ≠ .rsp), State.withRegions_gpr, State.callEntry_rsp,
    State.withRegions_rd, State.withRegions_wr, hdi, hsi, h8, hsp, b16_8, b8_8, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hr64]
  exact ⟨trivial, trivial, hsc, r1, r3, r2, r4, hr, hdx⟩

theorem finPad_cov {st op sc : Addr} {len : Nat} {t : State}
    (hwr : t.wr = [⟨st, 200⟩, ⟨op, len⟩, ⟨sc, 656⟩]) :
    Covers ([] ++ [⟨st, 200⟩, ⟨sc, 640⟩]) (t.rd ++ t.wr) ∧ Covers [⟨st, 200⟩, ⟨sc, 640⟩] t.wr := by
  refine ⟨Covers.of_sub fun r hr' => ?_, Covers.of_sub fun r hr' => ?_⟩
  all_goals
    simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact ⟨⟨st, 200⟩, by simp [hwr], 0, by simp, by simp⟩
    · exact ⟨⟨sc, 656⟩, by simp [hwr], 0, by simp, by simp⟩

/-- The call of `pad`, with SHA-3's suffix. -/
theorem finPadCall {st op sc B : Addr} {len rate : Nat} (hL : Lay st op sc B len) (hr : rate ∈ rates)
    {t : State} (hwr : t.wr = [⟨st, 200⟩, ⟨op, len⟩, ⟨sc, 656⟩])
    (hdi : t.gpr .rdi = st) (hsi : t.gpr .rsi = BitVec.ofNat 64 rate) (hdx : (t.gpr .rdx).toNat < rate)
    (hcx : t.gpr .rcx = 0x06) (h8 : t.gpr .r8 = sc) (hsp : t.gpr .rsp = B + BitVec.ofNat 64 16) :
    WP isa (.call "vg_keccak_pad_scratch" Impl.Sha3.X86_64.Stream.pad) t fun u =>
      u.rd = t.rd ∧ u.wr = t.wr ∧ (∀ r ∈ calleeSaved, u.gpr r = t.gpr r) ∧ u.gpr .rdi = st ∧
      Frame [⟨st, 200⟩, ⟨sc, 640⟩, below (B + BitVec.ofNat 64 16) 16] t.mem u.mem ∧
      ∀ msg, Repr t.mem st rate msg → (t.gpr .rdx).toNat = msg.length % rate →
        stateAt u.mem st = Spec.Sha3.absorb rate (Spec.Sha3.pad rate Spec.Sha3.sha3Suffix msg) := by
  have hr64 : rate < 2 ^ 64 := by simp [rates] at hr; omega
  obtain ⟨r1, -⟩ := call_disj hL.stk_st
  refine WP.call (k := Proof.Sha3.padX86_64) Stream.Pad.pad_correct pad_nosp
    (by rw [pad_depth]; decide) (rd := []) (wr := [⟨st, 200⟩, ⟨sc, 640⟩])
    (finPad_pre hL hr hdi hsi hdx h8 hsp) (finPad_cov hwr).1 (finPad_cov hwr).2
    fun u h1 h2 h3 h4 h5 ⟨s₂, hm, _, hpost⟩ => ⟨h1, h2, h3, (h5 .rdi pad_rdi).trans hdi,
      by rw [pad_depth, hsp] at h4; exact h4, fun msg hm' hp => ?_⟩
  simp only [Proof.Sha3.padX86_64, gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
    gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp),
    gpr_ce _ _ _ (by decide : Reg.rcx ≠ .rsp), State.withRegions_mem, hdi, hsi, hcx,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr64, hm] at hpost
  have hce : stateAt t.callEntry.mem st = stateAt t.mem st := by
    refine stateAt_frame (rs := [⟨B + BitVec.ofNat 64 8, 8⟩]) ?_ (by simpa using r1.symm)
    rw [State.callEntry_mem, hsp, b16_8]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  rw [hpost msg (by unfold Spec.Sha3.Repr; rw [hce]; exact hm') hp]
  rfl

/-- `squeeze`'s precondition at the call, narrowed to the state, `out` and
the first 640 bytes of `scratch`. -/
theorem finSqz_pre {st op sc B : Addr} {len rate : Nat} (hL : Lay st op sc B len) (hr : rate ∈ rates)
    (hl : len < 2 ^ 32) {t : State} (hdi : t.gpr .rdi = st) (hsi : t.gpr .rsi = BitVec.ofNat 64 rate)
    (hdx : t.gpr .rdx = 0) (hcx : t.gpr .rcx = op) (h8 : t.gpr .r8 = BitVec.ofNat 64 len)
    (h9 : t.gpr .r9 = sc) (hsp : t.gpr .rsp = B + BitVec.ofNat 64 16) :
    Proof.Sha3.squeezeX86_64.pre (t.callEntry.withRegions [] [⟨st, 200⟩, ⟨op, len⟩, ⟨sc, 640⟩]) := by
  have hr64 : rate < 2 ^ 64 := by simp [rates] at hr; omega
  have hl64 : len < 2 ^ 64 := by omega
  have hsc := hL.st_sc.sub_right (sub_prefix sc (n := 640) (by omega))
  have hosc := hL.op_sc.sub_right (sub_prefix sc (n := 640) (by omega))
  obtain ⟨r1, r2⟩ := call_disj hL.stk_st
  obtain ⟨r3, r4⟩ := call_disj hL.stk_op
  obtain ⟨r5, r6⟩ := call_disj (hL.stk_sc.sub_right (sub_prefix sc (n := 640) (by omega)))
  simp only [Proof.Sha3.squeezeX86_64, gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
    gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp),
    gpr_ce _ _ _ (by decide : Reg.rcx ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.r8 ≠ .rsp),
    gpr_ce _ _ _ (by decide : Reg.r9 ≠ .rsp), State.withRegions_gpr, State.callEntry_rsp,
    State.withRegions_rd, State.withRegions_wr, hdi, hsi, hdx, hcx, h8, h9, hsp, b16_8, b8_8,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr64, Nat.mod_eq_of_lt hl64]
  exact ⟨trivial, trivial, hL.st_op, hsc, hosc, r1, r3, r5, r2, r4, r6, hr, by simp⟩

theorem finSqz_cov {st op sc : Addr} {len : Nat} {t : State}
    (hwr : t.wr = [⟨st, 200⟩, ⟨op, len⟩, ⟨sc, 656⟩]) :
    Covers ([] ++ [⟨st, 200⟩, ⟨op, len⟩, ⟨sc, 640⟩]) (t.rd ++ t.wr) ∧
      Covers [⟨st, 200⟩, ⟨op, len⟩, ⟨sc, 640⟩] t.wr := by
  refine ⟨Covers.of_sub fun r hr' => ?_, Covers.of_sub fun r hr' => ?_⟩
  all_goals
    simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact ⟨⟨st, 200⟩, by simp [hwr], 0, by simp, by simp⟩
    · exact ⟨⟨op, len⟩, by simp [hwr], 0, by simp, by simp⟩
    · exact ⟨⟨sc, 656⟩, by simp [hwr], 0, by simp, by simp⟩

/-- The call of `squeeze`, from position 0, for `len` bytes into `out`. -/
theorem finSqzCall {st op sc B : Addr} {len rate : Nat} (hL : Lay st op sc B len) (hr : rate ∈ rates)
    (hl : len < 2 ^ 32) {t : State} (hwr : t.wr = [⟨st, 200⟩, ⟨op, len⟩, ⟨sc, 656⟩])
    (hdi : t.gpr .rdi = st) (hsi : t.gpr .rsi = BitVec.ofNat 64 rate) (hdx : t.gpr .rdx = 0)
    (hcx : t.gpr .rcx = op) (h8 : t.gpr .r8 = BitVec.ofNat 64 len) (h9 : t.gpr .r9 = sc)
    (hsp : t.gpr .rsp = B + BitVec.ofNat 64 16) :
    WP isa (.call "vg_keccak_squeeze_scratch" Impl.Sha3.X86_64.Stream.squeeze) t fun u =>
      u.rd = t.rd ∧ u.wr = t.wr ∧ (∀ r ∈ calleeSaved, u.gpr r = t.gpr r) ∧
      Frame [⟨st, 200⟩, ⟨op, len⟩, ⟨sc, 640⟩, below (B + BitVec.ofNat 64 16) 16] t.mem u.mem ∧
      bytesAt u.mem op len = Spec.Sha3.squeezeFrom rate (stateAt t.mem st) 0 len := by
  have hr64 : rate < 2 ^ 64 := by simp [rates] at hr; omega
  have hl64 : len < 2 ^ 64 := by omega
  obtain ⟨r1, -⟩ := call_disj hL.stk_st
  refine WP.call (k := Proof.Sha3.squeezeX86_64) Stream.Squeeze.squeeze_correct squeeze_nosp
    (by rw [squeeze_depth]; decide) (rd := []) (wr := [⟨st, 200⟩, ⟨op, len⟩, ⟨sc, 640⟩])
    (finSqz_pre hL hr hl hdi hsi hdx hcx h8 h9 hsp) (finSqz_cov hwr).1 (finSqz_cov hwr).2
    fun u h1 h2 h3 h4 _ ⟨s₂, hm, _, hpost, _⟩ => ⟨h1, h2, h3,
      by rw [squeeze_depth, hsp] at h4; exact h4, ?_⟩
  simp only [gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
    gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp),
    gpr_ce _ _ _ (by decide : Reg.rcx ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.r8 ≠ .rsp),
    State.withRegions_mem, hdi, hsi, hdx, hcx, h8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr64,
    Nat.mod_eq_of_lt hl64, hm] at hpost
  have hce : stateAt t.callEntry.mem st = stateAt t.mem st := by
    refine stateAt_frame (rs := [⟨B + BitVec.ofNat 64 8, 8⟩]) ?_ (by simpa using r1.symm)
    rw [State.callEntry_mem, hsp, b16_8]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  rw [hpost, hce]
  simp

/-- After `finSqzArgs`. -/
theorem finSqz_ok {rate len : Nat} (hr : rate < 2 ^ 32) (hl : len < 2 ^ 32) (s : State) :
    WP isa (.block (finSqzArgs rate len)) s fun t =>
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr ∧ t.mem = s.mem ∧
      t.gpr .rsi = BitVec.ofNat 64 rate ∧ t.gpr .rdx = 0 ∧ t.gpr .rcx = s.gpr .rbp ∧
      t.gpr .r8 = BitVec.ofNat 64 len ∧ t.gpr .r9 = s.gpr .r12 ∧
      ∀ r, r ≠ .rsi → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r9 → t.gpr r = s.gpr r := by
  apply WP.of_runBlock
  simp only [finSqzArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32,
    State.setReg32, Option.map_some, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, RegUpd.mxcsr_setReg, reduceCtorEq, ite_false, ite_true, Option.some.injEq,
    exists_eq_left', setWidth_ofNat hr, setWidth_ofNat hl]
  refine ⟨trivial, trivial, trivial, trivial, trivial, by decide, trivial, trivial, trivial,
    fun r h1 h2 h3 h4 h5 => ?_⟩
  simp only [h1, h2, h3, h4, h5, ite_false]

/-- After `finRestore`, from a state with `rbx` = `sc`. -/
theorem finRestore_ok {sc : Addr} {s : State} (hbx : s.gpr .r12 = sc)
    (h1 : InRegions (s.rd ++ s.wr) (sc + BitVec.ofNat 64 640) 8)
    (h2 : InRegions (s.rd ++ s.wr) (sc + BitVec.ofNat 64 648) 8) :
    WP isa (.block finRestore) s fun t =>
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr ∧ t.mem = s.mem ∧
      t.gpr .rbp = s.mem.readW (sc + BitVec.ofNat 64 648) 64 ∧
      t.gpr .r12 = s.mem.readW (sc + BitVec.ofNat 64 640) 64 ∧
      ∀ r, r ≠ .rbp → r ≠ .r12 → t.gpr r = s.gpr r := by
  apply WP.of_runBlock
  simp only [finRestore, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    ea_at, hbx, h1, h2, ite_true, Option.map_some, RegUpd.gpr_setReg, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mxcsr_setReg, RegUpd.rd_setReg, reduceCtorEq,
    ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, fun r h1 h2 => ?_⟩
  simp only [h1, h2, ite_false]

theorem readW_frame {rs : List Region} {m m' : Mem} {a : Addr} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨a, 8⟩ r) : m'.readW a 64 = m.readW a 64 :=
  hf.readW (r := ⟨a, 8⟩) (Region.contains_self _ _) hd (by decide)

theorem below16 (B : Addr) : below (B + BitVec.ofNat 64 16) 16 = ⟨B, 16⟩ := by
  simp only [below]; congr 1; bv_omega

/-- `finBody` meets `finX86_64`, and keeps the callee-saved registers and the
return address. -/
theorem finBody_correct {H : Spec.Sha3.HashFn} (hH : hashSponge H) (hr : H.rate ∈ rates)
    (hl : H.len < 2 ^ 32) {s : State} (hp : (finX86_64 H).pre s) :
    WP isa (finBody H.rate H.len) s fun s' => gprPreserved s s' ∧ (finX86_64 H).post s s' := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12⟩ := hp
  have hr' : H.rate < 2 ^ 32 := by simp [rates] at hr; omega
  -- The layout, with `B` the bottom of the stack the calls use.
  generalize hB : s.gpr .rsp - 16 = B at p9 p10 p11
  have hsp : s.gpr .rsp = B + BitVec.ofNat 64 16 := by rw [← hB]; bv_omega
  rw [hsp] at p6 p7 p8
  have hL : Lay (s.gpr .rdi) (s.gpr .rdx) (s.gpr .rcx) B H.len :=
    ⟨p3, p4, p5, p9, p10, p11, p6, p7, p8⟩
  -- The two saved words, within `scratch`, beyond what the calls use.
  have hslot : ∀ d, 640 ≤ d → d + 8 ≤ 656 →
      ∀ r ∈ [(⟨s.gpr .rdi, 200⟩ : Region), ⟨s.gpr .rdx, H.len⟩, ⟨s.gpr .rcx, 640⟩, ⟨B, 16⟩],
        Region.Disjoint ⟨s.gpr .rcx + BitVec.ofNat 64 d, 8⟩ r := by
    intro d h1 h2 r hr
    have hsub : Region.Sub ⟨s.gpr .rcx + BitVec.ofNat 64 d, 8⟩ ⟨s.gpr .rcx, 656⟩ :=
      Offset.sub_base _ (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (hL.st_sc.symm).sub_left hsub
    · exact (hL.op_sc.symm).sub_left hsub
    · exact Offset.disjoint_base _ (by omega) (by omega)
    · exact (hL.stk_sc.symm).sub_left hsub
  refine WP.seq (WP.mono (finPad_ok hr' p2) fun t ⟨trd, twr, tmx, tmem, tdi, t12, tbp, tdx, tsi, tcx,
    t8, toth⟩ => ?_)
  have tsp : t.gpr .rsp = B + BitVec.ofNat 64 16 := by rw [toth _ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide), hsp]
  refine WP.seq (WP.mono (finPadCall hL hr (by rw [twr, p2]) tdi tsi (by rw [tdx]; exact p12) tcx t8 tsp)
    fun u ⟨urd, uwr, ucs, udi, uf, upad⟩ => ?_)
  refine WP.seq (WP.mono (finSqz_ok hr' hl u) fun v ⟨vrd, vwr, vmx, vmem, vsi, vdx, vcx, v8, v9, voth⟩ => ?_)
  have u12 : u.gpr .r12 = s.gpr .rcx := by rw [ucs .r12 (by decide), t12]
  have ubp : u.gpr .rbp = s.gpr .rdx := by rw [ucs .rbp (by decide), tbp]
  have usp : u.gpr .rsp = B + BitVec.ofNat 64 16 := by rw [ucs .rsp (by decide), tsp]
  refine WP.seq (WP.mono (finSqzCall hL hr hl (by rw [vwr, uwr, twr, p2])
    (by rw [voth _ (by decide) (by decide) (by decide) (by decide) (by decide), udi]) vsi vdx
    (by rw [vcx, ubp]) v8 (by rw [v9, u12])
    (by rw [voth _ (by decide) (by decide) (by decide) (by decide) (by decide), usp]))
    fun w ⟨wrd, wwr, wcs, wf, wout⟩ => ?_)
  have w12 : w.gpr .r12 = s.gpr .rcx := by
    rw [wcs .r12 (by decide), voth _ (by decide) (by decide) (by decide) (by decide) (by decide), u12]
  have hin : ∀ d, d + 8 ≤ 656 → InRegions (w.rd ++ w.wr) (s.gpr .rcx + BitVec.ofNat 64 d) 8 :=
    fun d hd => ⟨⟨s.gpr .rcx, 656⟩, by rw [wwr, vwr, uwr, twr, p2]; simp,
      Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.mono (finRestore_ok w12 (hin 640 (by omega)) (hin 648 (by omega)))
    fun x ⟨xrd, xwr, xmx, xmem, xbp, x12, xoth⟩ => ?_
  -- Memory from `t` to `w`, outside the calls' regions.
  have fw : Frame [⟨s.gpr .rdi, 200⟩, ⟨s.gpr .rdx, H.len⟩, ⟨s.gpr .rcx, 640⟩, ⟨B, 16⟩] t.mem w.mem := by
    rw [below16] at uf wf
    refine (uf.mono fun r hr => ?_).trans (vmem ▸ wf)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl <;> simp
  have slot : ∀ d, 640 ≤ d → d + 8 ≤ 656 →
      w.mem.readW (s.gpr .rcx + BitVec.ofNat 64 d) 64 = t.mem.readW (s.gpr .rcx + BitVec.ofNat 64 d) 64 :=
    fun d h1 h2 => readW_frame fw (hslot d h1 h2)
  have ft : Frame [⟨s.gpr .rcx, 656⟩] s.mem t.mem := by
    rw [tmem]
    exact Frame.writeW (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega) (by omega))) (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega) (by omega))
  have t640 : t.mem.readW (s.gpr .rcx + BitVec.ofNat 64 640) 64 = s.gpr .r12 := by
    rw [tmem, Mem.readW_writeW_sep (Offset.sep _ (d := 640) (n := 8) (e := 648) (k := 8)
      (by omega) (by omega) (by omega)) (by decide), Mem.readW_writeW_self64]
  have t648 : t.mem.readW (s.gpr .rcx + BitVec.ofNat 64 648) 64 = s.gpr .rbp := by
    rw [tmem, Mem.readW_writeW_self64]
  refine ⟨⟨fun r hr => ?_, ?_⟩, fun msg hm hpos => ?_⟩
  · by_cases h1 : r = .rbp
    · subst h1; rw [xbp, slot 648 (by omega) (by omega), t648]
    by_cases h2 : r = .r12
    · subst h2; rw [x12, slot 640 (by omega) (by omega), t640]
    have hcs : r ≠ .rsi ∧ r ≠ .rdx ∧ r ≠ .rcx ∧ r ≠ .r8 ∧ r ≠ .r9 := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [xoth r h1 h2, wcs r hr, voth r hcs.1 hcs.2.1 hcs.2.2.1 hcs.2.2.2.1 hcs.2.2.2.2, ucs r hr,
      toth r h2 h1 hcs.2.1 hcs.1 hcs.2.2.1 hcs.2.2.2.1]
  · rw [xmem, hsp, readW_frame fw ?_, readW_frame ft ?_]
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact p8
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact p6
      · exact p7
      · exact p8.sub_right (sub_prefix _ (by omega))
      · exact Offset.disjoint_base _ (by omega) (by omega)
  · have hst : stateAt t.mem (s.gpr .rdi) = stateAt s.mem (s.gpr .rdi) :=
      stateAt_frame ft (by intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact p4)
    have hpad := upad msg (by unfold Spec.Sha3.Repr; rw [hst]; exact hm) (by rw [tdx]; exact hpos)
    show bytesAt x.mem (s.gpr .rdx) H.len = H.digest msg
    rw [xmem, wout, vmem, hpad]
    exact digest_of_pad hH rfl

/-! ### Constant time -/

/-- The initial taint: the arguments and `rsp` are public, and `rdi`, `rdx`
and `rcx` point at the writable regions. -/
def finTaint (len : Nat) : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .rsp], flags := false, lens := [200, len, 656],
    bases := [(.rdi, 0, 0), (.rdx, 1, 0), (.rcx, 2, 0)] }

theorem finAgree {H : Spec.Sha3.HashFn} (hl : H.len < 2 ^ 32) {s₁ s₂ : State} (h₁ : (finX86_64 H).pre s₁)
    (h₂ : (finX86_64 H).pre s₂) (hpub : (finX86_64 H).pub s₁ s₂) :
    X86_64.Taint.Agree (finTaint H.len) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := hpub
  have wf : ∀ s, (finX86_64 H).pre s → X86_64.Taint.Wf (finTaint H.len) s := by
    intro s hs
    obtain ⟨-, hw, d1, d2, d3, -⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, finTaint], by simp [hw, d1, d2, d3], by simp [hw]; omega⟩, fun p hp => ?_⟩
    simp only [finTaint, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_,
    X86_64.Taint.noLo, X86_64.Taint.noXr⟩
  · simp only [finTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption
  · rw [h₁.2.1, h₂.2.1, p1, p3, p4]
  · intro sl h; simp [finTaint] at h
  · intro sl h; simp [finTaint] at h

/-- The layout `finX86_64`'s precondition gives, with `B = rsp - 16`. -/
theorem lay_of_pre {H : Spec.Sha3.HashFn} {s : State} (hp : (finX86_64 H).pre s) :
    Lay (s.gpr .rdi) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .rsp - 16) H.len ∧
      s.gpr .rsp = s.gpr .rsp - 16 + BitVec.ofNat 64 16 := by
  obtain ⟨-, -, p3, p4, p5, p6, p7, p8, p9, p10, p11, -⟩ := hp
  have hsp : s.gpr .rsp = s.gpr .rsp - 16 + BitVec.ofNat 64 16 := by bv_omega
  rw [hsp] at p6 p7 p8
  exact ⟨⟨p3, p4, p5, p9, p10, p11, p6, p7, p8⟩, hsp⟩

/-- What the second piece needs of the state after the first. -/
def G1 (rate : Nat) (σ t : State) : Prop :=
  t.rd = σ.rd ∧ t.wr = σ.wr ∧ t.gpr .rdi = σ.gpr .rdi ∧ t.gpr .rsi = BitVec.ofNat 64 rate ∧
    t.gpr .rdx = σ.gpr .rsi ∧ t.gpr .rcx = 0x06 ∧ t.gpr .r8 = σ.gpr .rcx ∧ t.gpr .r12 = σ.gpr .rcx ∧
    t.gpr .rbp = σ.gpr .rdx ∧ t.gpr .rsp = σ.gpr .rsp

def G2 (σ u : State) : Prop :=
  u.rd = σ.rd ∧ u.wr = σ.wr ∧ u.gpr .rdi = σ.gpr .rdi ∧ u.gpr .r12 = σ.gpr .rcx ∧
    u.gpr .rbp = σ.gpr .rdx ∧ u.gpr .rsp = σ.gpr .rsp

def G3 (rate len : Nat) (σ v : State) : Prop :=
  v.rd = σ.rd ∧ v.wr = σ.wr ∧ v.gpr .rdi = σ.gpr .rdi ∧ v.gpr .rsi = BitVec.ofNat 64 rate ∧
    v.gpr .rdx = 0 ∧ v.gpr .rcx = σ.gpr .rdx ∧ v.gpr .r8 = BitVec.ofNat 64 len ∧
    v.gpr .r9 = σ.gpr .rcx ∧ v.gpr .r12 = σ.gpr .rcx ∧ v.gpr .rsp = σ.gpr .rsp

theorem g1_ok {H : Spec.Sha3.HashFn} (hr : H.rate < 2 ^ 32) {σ : State} (hp : (finX86_64 H).pre σ) :
    WP isa (.block (finPadArgs H.rate)) σ (G1 H.rate σ) :=
  WP.mono (finPad_ok hr hp.2.1) fun _ ⟨h1, h2, _, _, h5, h6, h7, h8, h9, h10, h11, h12⟩ =>
    ⟨h1, h2, h5, h9, h8, h10, h11, h6, h7, h12 _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)⟩

theorem g2_ok {H : Spec.Sha3.HashFn} (hr : H.rate ∈ rates) {σ t : State} (hp : (finX86_64 H).pre σ)
    (h : G1 H.rate σ t) :
    WP isa (.call "vg_keccak_pad_scratch" Impl.Sha3.X86_64.Stream.pad) t (G2 σ) := by
  obtain ⟨hL, hsp⟩ := lay_of_pre hp
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  refine WP.mono (finPadCall hL hr (by rw [h2, hp.2.1]) h3 h4 (by rw [h5]; exact hp.2.2.2.2.2.2.2.2.2.2.2)
    h6 h7 (by rw [h10, ← hsp])) fun u ⟨u1, u2, u3, u4, _, _⟩ => ⟨by rw [u1, h1], by rw [u2, h2], u4,
      by rw [u3 .r12 (by decide), h8], by rw [u3 .rbp (by decide), h9], by rw [u3 .rsp (by decide), h10]⟩

theorem g3_ok {H : Spec.Sha3.HashFn} (hr : H.rate < 2 ^ 32) (hl : H.len < 2 ^ 32) {σ u : State}
    (h : G2 σ u) : WP isa (.block (finSqzArgs H.rate H.len)) u (G3 H.rate H.len σ) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine WP.mono (finSqz_ok hr hl u) fun v ⟨v1, v2, _, _, v5, v6, v7, v8, v9, v10⟩ =>
    ⟨by rw [v1, h1], by rw [v2, h2], by rw [v10 _ (by decide) (by decide) (by decide) (by decide)
      (by decide), h3], v5, v6, by rw [v7, h5], v8, by rw [v9, h4],
      by rw [v10 _ (by decide) (by decide) (by decide) (by decide) (by decide), h4],
      by rw [v10 _ (by decide) (by decide) (by decide) (by decide) (by decide), h6]⟩

theorem g4_ok {H : Spec.Sha3.HashFn} (hr : H.rate ∈ rates) (hl : H.len < 2 ^ 32) {σ v : State}
    (hp : (finX86_64 H).pre σ) (h : G3 H.rate H.len σ v) :
    WP isa (.call "vg_keccak_squeeze_scratch" Impl.Sha3.X86_64.Stream.squeeze) v
      fun w => w.gpr .r12 = σ.gpr .rcx := by
  obtain ⟨hL, hsp⟩ := lay_of_pre hp
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact WP.mono (finSqzCall hL hr hl (by rw [h2, hp.2.1]) h3 h4 h5 h6 h7 h8 (by rw [h10, ← hsp]))
    fun w ⟨_, _, w3, _⟩ => by rw [w3 .r12 (by decide), h9]

/-- `finBody`'s constant time, from the taint analysis of its three blocks
(which the instances decide) and the constant time of the calls. -/
theorem finBody_ct {H : Spec.Sha3.HashFn} (hr : H.rate ∈ rates) (hl : H.len < 2 ^ 32)
    {h₁ h₂ h₃ : VG.Taint.Hint X86_64.Taint.T}
    (hb₁ : (X86_64.taint.check (finTaint H.len) (.block (finPadArgs H.rate)) h₁).isSome = true)
    (hb₂ : (X86_64.taint.check (X86_64.Taint.ofRegs []) (.block (finSqzArgs H.rate H.len)) h₂).isSome = true)
    (hb₃ : (X86_64.taint.check (X86_64.Taint.ofRegs [.r12]) (.block finRestore) h₃).isSome = true) :
    ConstantTime isa (finX86_64 H).pre (finX86_64 H).pub (finBody H.rate H.len) := by
  have hr' : H.rate < 2 ^ 32 := by simp [rates] at hr; omega
  intro σ₁ σ₂ t₁ t₂ σ₁' σ₂' p₁ p₂ hp e₁ e₂
  obtain ⟨q1, q2, q3, q4, q5⟩ := hp
  have hP : RelCT isa (fun a b => a = σ₁ ∧ b = σ₂) (finBody H.rate H.len) fun _ _ => True := by
    unfold finBody
    -- The first block.
    refine RelCT.seq (RelCT.wp (F₁ := G1 H.rate σ₁) (F₂ := G1 H.rate σ₂)
      (RelCT.taint (A := X86_64.taint) (finTaint H.len) (fun a b ⟨ea, eb⟩ => by
        subst ea eb; exact finAgree hl p₁ p₂ ⟨q1, q2, q3, q4, q5⟩) hb₁)
      fun a b ⟨ea, eb⟩ => by subst ea eb; exact ⟨g1_ok hr' p₁, g1_ok hr' p₂⟩) ?_
    -- The call of `pad`.
    refine RelCT.seq (RelCT.wp (F₁ := G2 σ₁) (F₂ := G2 σ₂)
      (RelCT.call Stream.Pad.pad_correct Stream.Pad.pad_ct [] [⟨σ₁.gpr .rdi, 200⟩, ⟨σ₁.gpr .rcx, 640⟩]
        fun a b ⟨_, ha, hb⟩ => ?_) fun a b ⟨_, ha, hb⟩ => ⟨g2_ok hr p₁ ha, g2_ok hr p₂ hb⟩) ?_
    · obtain ⟨hL₁, hs₁⟩ := lay_of_pre p₁
      obtain ⟨hL₂, hs₂⟩ := lay_of_pre p₂
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := ha
      obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := hb
      have pb := finPad_pre hL₂ hr b3 b4 (by rw [b5]; exact p₂.2.2.2.2.2.2.2.2.2.2.2) b7
        (by rw [b10, ← hs₂])
      rw [← q1, ← q4] at pb
      refine ⟨finPad_pre hL₁ hr a3 a4 (by rw [a5]; exact p₁.2.2.2.2.2.2.2.2.2.2.2) a7 (by rw [a10, ← hs₁]),
        pb, ?_, (finPad_cov (by rw [a2, p₁.2.1])).1, (finPad_cov (by rw [a2, p₁.2.1])).2,
        (finPad_cov (by rw [b2, p₂.2.1, ← q1, ← q3, ← q4])).1,
        (finPad_cov (by rw [b2, p₂.2.1, ← q1, ← q3, ← q4])).2, by rw [a10, b10, q5]⟩
      simp only [Proof.Sha3.padX86_64, gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
        gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp),
        gpr_ce _ _ _ (by decide : Reg.r8 ≠ .rsp), State.withRegions_gpr, State.callEntry_rsp]
      exact ⟨by rw [a3, b3, q1], by rw [a4, b4], by rw [a5, b5, q2], by rw [a7, b7, q4],
        by rw [a10, b10, q5]⟩
    -- The second block.
    refine RelCT.seq (RelCT.wp (F₁ := G3 H.rate H.len σ₁) (F₂ := G3 H.rate H.len σ₂)
      (RelCT.taint (A := X86_64.taint) (X86_64.Taint.ofRegs []) (fun _ _ _ => X86_64.Taint.agree_ofRegs fun _ h => by
        simp at h) hb₂)
      fun a b ⟨_, ha, hb⟩ => ⟨g3_ok hr' hl ha, g3_ok hr' hl hb⟩) ?_
    -- The call of `squeeze`.
    refine RelCT.seq (RelCT.wp (F₁ := fun w : State => w.gpr .r12 = σ₁.gpr .rcx)
      (F₂ := fun w : State => w.gpr .r12 = σ₂.gpr .rcx)
      (RelCT.call Stream.Squeeze.squeeze_correct Stream.Squeeze.squeeze_ct []
        [⟨σ₁.gpr .rdi, 200⟩, ⟨σ₁.gpr .rdx, H.len⟩, ⟨σ₁.gpr .rcx, 640⟩] fun a b ⟨_, ha, hb⟩ => ?_)
      fun a b ⟨_, ha, hb⟩ => ⟨g4_ok hr hl p₁ ha, g4_ok hr hl p₂ hb⟩) ?_
    · obtain ⟨hL₁, hs₁⟩ := lay_of_pre p₁
      obtain ⟨hL₂, hs₂⟩ := lay_of_pre p₂
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := ha
      obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := hb
      have pb := finSqz_pre hL₂ hr hl b3 b4 b5 b6 b7 b8 (by rw [b10, ← hs₂])
      rw [← q1, ← q3, ← q4] at pb
      refine ⟨finSqz_pre hL₁ hr hl a3 a4 a5 a6 a7 a8 (by rw [a10, ← hs₁]), pb, ?_,
        (finSqz_cov (by rw [a2, p₁.2.1])).1, (finSqz_cov (by rw [a2, p₁.2.1])).2,
        (finSqz_cov (by rw [b2, p₂.2.1, ← q1, ← q3, ← q4])).1,
        (finSqz_cov (by rw [b2, p₂.2.1, ← q1, ← q3, ← q4])).2, by rw [a10, b10, q5]⟩
      simp only [Proof.Sha3.squeezeX86_64, gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
        gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp),
        gpr_ce _ _ _ (by decide : Reg.rcx ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.r8 ≠ .rsp),
        gpr_ce _ _ _ (by decide : Reg.r9 ≠ .rsp), State.withRegions_gpr, State.callEntry_rsp]
      exact ⟨by rw [a3, b3, q1], by rw [a4, b4], by rw [a5, b5], by rw [a6, b6, q3], by rw [a7, b7],
        by rw [a8, b8, q4], by rw [a10, b10, q5]⟩
    -- The restore.
    exact RelCT.taint (A := X86_64.taint) (X86_64.Taint.ofRegs [.r12]) (fun a b ⟨_, ha, hb⟩ => X86_64.Taint.agree_ofRegs
      fun r h => by simp at h; subst h; rw [ha, hb, q4]) hb₃
  exact (hP _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ### `Verified` -/

theorem finBody_verified' {H : Spec.Sha3.HashFn} (hH : hashSponge H) (hr : H.rate ∈ rates)
    (hl : H.len < 2 ^ 32)
    (hmx : (finBody H.rate H.len).allInstrs (fun i => !loadsMxcsr i) = true)
    (hct : ConstantTime isa (finX86_64 H).pre (finX86_64 H).pub (finBody H.rate H.len))
    (hsat : ∃ s, (finX86_64 H).pre s) :
    Verified X86_64.target (finBody H.rate H.len) (finX86_64 H) := by
  refine Verified.of_correct (fun s hs => ?_) hct (Contract.Implies.refl hsat)
  obtain ⟨t, s', he, h⟩ := finBody_correct hH hr hl hs
  exact ⟨t, s', he, abiPreserved_of_exec hmx he h.1, h.2⟩

/-- A state satisfying `finX86_64`'s precondition. -/
def finSat (len : Nat) : State :=
  { Stream.Absorb.sat with
    gpr := fun r => match r with
      | .rdi => 0x1000 | .rdx => 0x2000 | .rcx => 0x3000 | .rsp => 0x4000 | _ => 0
    rd := []
    wr := [⟨0x1000, 200⟩, ⟨0x2000, len⟩, ⟨0x3000, 656⟩] }

theorem finBody_verified {H : Spec.Sha3.HashFn} (hH : hashSponge H) (hr : H.rate ∈ rates)
    (hl : H.len < 2 ^ 32)
    (hmx : (finBody H.rate H.len).allInstrs (fun i => !loadsMxcsr i) = true)
    (hct : ConstantTime isa (finX86_64 H).pre (finX86_64 H).pub (finBody H.rate H.len))
    (hsat : ∃ s, (finX86_64 H).pre s) (hsat' : ∃ s, (finScratchContract X86_64.abi H 82 16).pre s) :
    Verified X86_64.target (finBody H.rate H.len) (finScratchContract X86_64.abi H 82 16) :=
  (finBody_verified' hH hr hl hmx hct hsat).of_implies
    { pre := by sig_implies_pre [VG.Proof.Sha3.Instances.finScratchContract, VG.Proof.Sha3.Instances.finScratchSig, Spec.Sha3.finalizePre,
          Spec.Sha3.finalizePost, finX86_64, X86_64.abi, X86_64.argRegs]
      post := by sig_implies_post [VG.Proof.Sha3.Instances.finScratchContract, VG.Proof.Sha3.Instances.finScratchSig, Spec.Sha3.finalizePre,
          Spec.Sha3.finalizePost, finX86_64, X86_64.abi, X86_64.argRegs]
      pub := by sig_implies_pub [VG.Proof.Sha3.Instances.finScratchContract, VG.Proof.Sha3.Instances.finScratchSig, Spec.Sha3.finalizePre,
          Spec.Sha3.finalizePost, finX86_64, X86_64.abi, X86_64.argRegs]
      sat := hsat' }

theorem finalize_verified {H : Spec.Sha3.HashFn} (hH : hashSponge H) (hr : H.rate ∈ rates)
    (hl : H.len < 2 ^ 32)
    (hmx : (finBody H.rate H.len).allInstrs (fun i => !loadsMxcsr i) = true)
    (hct : ConstantTime isa (finX86_64 H).pre (finX86_64 H).pub (finBody H.rate H.len))
    (hsat : ∃ s, (finX86_64 H).pre s) (hsat' : ∃ s, (finScratchContract X86_64.abi H 82 16).pre s)
    (hsp : (finBody H.rate H.len).all (fun i => !isa.writesSp i) = true)
    (hd : (finBody H.rate H.len).x86_64Depth ≤ 16)
    (hsat'' : ∃ s, (Spec.Sha3.finalizeContract X86_64.abi H 680).pre s) :
    Verified X86_64.target (finalize H.rate H.len) (Spec.Sha3.finalizeContract X86_64.abi H 680) :=
  X86_64.Verified.stackScratch (sig := Spec.Sha3.finalizeSig H.len) (nm := "scratch") (e := .u64)
    (n := 82) (pre := Spec.Sha3.finalizePre H X86_64.abi.ptrBits)
    (post := Spec.Sha3.finalizePost H X86_64.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 664) (finBody_verified hH hr hl hmx hct hsat hsat') (by exact (by decide : 3 < 6))
    (by decide) (by decide) hsp hd hsat'' rfl

/-! ### The instances -/

/-- `finalize`'s constant time for an instance, from the taint analysis of
its blocks. -/
macro "fin_ct" : term => `(finBody_ct (by decide) (by decide)
  (by taint_decide_weak VG.Proof.Sha3.X86_64.dropRC) (by taint_decide_weak VG.Proof.Sha3.X86_64.dropRC)
  (by taint_decide_weak VG.Proof.Sha3.X86_64.dropRC))

theorem finalize_sha3_224 :
    Verified X86_64.target (finalize Spec.Sha3.hashSha3_224.rate Spec.Sha3.hashSha3_224.len)
      (Spec.Sha3.finalizeContract X86_64.abi Spec.Sha3.hashSha3_224 680) :=
  finalize_verified VG.Proof.Sha3.Instances.sha3_224_sponge (by decide) (by decide) (by decide +kernel) fin_ct
    (by implies_sat [finX86_64, Spec.Sha3.hashSha3_224] [finSat, Stream.Absorb.sat] using finSat 28)
    (by implies_sat [VG.Proof.Sha3.Instances.finScratchContract, VG.Proof.Sha3.Instances.finScratchSig, Spec.Sha3.finalizePre, Spec.Sha3.finalizePost,
      X86_64.abi, X86_64.argRegs, Spec.Sha3.hashSha3_224] [finSat, Stream.Absorb.sat] using finSat 28)
    (Code.all_of_allInstrs (by decide +kernel)) (by decide +kernel)
    (by implies_sat [Spec.Sha3.finalizeContract, Spec.Sha3.finalizeSig, Spec.Sha3.finalizePre,
      Spec.Sha3.finalizePost, X86_64.abi, X86_64.argRegs, Spec.Sha3.hashSha3_224] [finSat, Stream.Absorb.sat]
      using { finSat 28 with wr := [⟨0x1000, 200⟩, ⟨0x2000, 28⟩] })

theorem finalize_sha3_256 :
    Verified X86_64.target (finalize Spec.Sha3.hashSha3_256.rate Spec.Sha3.hashSha3_256.len)
      (Spec.Sha3.finalizeContract X86_64.abi Spec.Sha3.hashSha3_256 680) :=
  finalize_verified VG.Proof.Sha3.Instances.sha3_256_sponge (by decide) (by decide) (by decide +kernel) fin_ct
    (by implies_sat [finX86_64, Spec.Sha3.hashSha3_256] [finSat, Stream.Absorb.sat] using finSat 32)
    (by implies_sat [VG.Proof.Sha3.Instances.finScratchContract, VG.Proof.Sha3.Instances.finScratchSig, Spec.Sha3.finalizePre, Spec.Sha3.finalizePost,
      X86_64.abi, X86_64.argRegs, Spec.Sha3.hashSha3_256] [finSat, Stream.Absorb.sat] using finSat 32)
    (Code.all_of_allInstrs (by decide +kernel)) (by decide +kernel)
    (by implies_sat [Spec.Sha3.finalizeContract, Spec.Sha3.finalizeSig, Spec.Sha3.finalizePre,
      Spec.Sha3.finalizePost, X86_64.abi, X86_64.argRegs, Spec.Sha3.hashSha3_256] [finSat, Stream.Absorb.sat]
      using { finSat 32 with wr := [⟨0x1000, 200⟩, ⟨0x2000, 32⟩] })

theorem finalize_sha3_384 :
    Verified X86_64.target (finalize Spec.Sha3.hashSha3_384.rate Spec.Sha3.hashSha3_384.len)
      (Spec.Sha3.finalizeContract X86_64.abi Spec.Sha3.hashSha3_384 680) :=
  finalize_verified VG.Proof.Sha3.Instances.sha3_384_sponge (by decide) (by decide) (by decide +kernel) fin_ct
    (by implies_sat [finX86_64, Spec.Sha3.hashSha3_384] [finSat, Stream.Absorb.sat] using finSat 48)
    (by implies_sat [VG.Proof.Sha3.Instances.finScratchContract, VG.Proof.Sha3.Instances.finScratchSig, Spec.Sha3.finalizePre, Spec.Sha3.finalizePost,
      X86_64.abi, X86_64.argRegs, Spec.Sha3.hashSha3_384] [finSat, Stream.Absorb.sat] using finSat 48)
    (Code.all_of_allInstrs (by decide +kernel)) (by decide +kernel)
    (by implies_sat [Spec.Sha3.finalizeContract, Spec.Sha3.finalizeSig, Spec.Sha3.finalizePre,
      Spec.Sha3.finalizePost, X86_64.abi, X86_64.argRegs, Spec.Sha3.hashSha3_384] [finSat, Stream.Absorb.sat]
      using { finSat 48 with wr := [⟨0x1000, 200⟩, ⟨0x2000, 48⟩] })

theorem finalize_sha3_512 :
    Verified X86_64.target (finalize Spec.Sha3.hashSha3_512.rate Spec.Sha3.hashSha3_512.len)
      (Spec.Sha3.finalizeContract X86_64.abi Spec.Sha3.hashSha3_512 680) :=
  finalize_verified VG.Proof.Sha3.Instances.sha3_512_sponge (by decide) (by decide) (by decide +kernel) fin_ct
    (by implies_sat [finX86_64, Spec.Sha3.hashSha3_512] [finSat, Stream.Absorb.sat] using finSat 64)
    (by implies_sat [VG.Proof.Sha3.Instances.finScratchContract, VG.Proof.Sha3.Instances.finScratchSig, Spec.Sha3.finalizePre, Spec.Sha3.finalizePost,
      X86_64.abi, X86_64.argRegs, Spec.Sha3.hashSha3_512] [finSat, Stream.Absorb.sat] using finSat 64)
    (Code.all_of_allInstrs (by decide +kernel)) (by decide +kernel)
    (by implies_sat [Spec.Sha3.finalizeContract, Spec.Sha3.finalizeSig, Spec.Sha3.finalizePre,
      Spec.Sha3.finalizePost, X86_64.abi, X86_64.argRegs, Spec.Sha3.hashSha3_512] [finSat, Stream.Absorb.sat]
      using { finSat 64 with wr := [⟨0x1000, 200⟩, ⟨0x2000, 64⟩] })

theorem update_sha3_224 :
    Verified X86_64.target (update Spec.Sha3.hashSha3_224.rate) (Spec.Sha3.updateContract X86_64.abi Spec.Sha3.hashSha3_224.rate 8) :=
  update_verified (by decide)

theorem update_sha3_256 :
    Verified X86_64.target (update Spec.Sha3.hashSha3_256.rate) (Spec.Sha3.updateContract X86_64.abi Spec.Sha3.hashSha3_256.rate 8) :=
  update_verified (by decide)

theorem update_sha3_384 :
    Verified X86_64.target (update Spec.Sha3.hashSha3_384.rate) (Spec.Sha3.updateContract X86_64.abi Spec.Sha3.hashSha3_384.rate 8) :=
  update_verified (by decide)

theorem update_sha3_512 :
    Verified X86_64.target (update Spec.Sha3.hashSha3_512.rate) (Spec.Sha3.updateContract X86_64.abi Spec.Sha3.hashSha3_512.rate 8) :=
  update_verified (by decide)

theorem update_shake128 :
    Verified X86_64.target (update Spec.Sha3.xofShake128.rate) (Spec.Sha3.updateContract X86_64.abi Spec.Sha3.xofShake128.rate 8) :=
  update_verified (by decide)

theorem finalize_shake128 :
    Verified X86_64.target (xofFinalize Spec.Sha3.xofShake128.rate) (Spec.Sha3.xofFinalizeContract X86_64.abi Spec.Sha3.xofShake128 656) :=
  xofFinalize_verified VG.Proof.Sha3.Instances.shake128_sponge (by decide)

theorem squeeze_shake128 :
    Verified X86_64.target (xofSqueeze Spec.Sha3.xofShake128.rate) (Spec.Sha3.xofSqueezeContract X86_64.abi Spec.Sha3.xofShake128 656) :=
  xofSqueeze_verified (by decide)

theorem update_shake256 :
    Verified X86_64.target (update Spec.Sha3.xofShake256.rate) (Spec.Sha3.updateContract X86_64.abi Spec.Sha3.xofShake256.rate 8) :=
  update_verified (by decide)

theorem finalize_shake256 :
    Verified X86_64.target (xofFinalize Spec.Sha3.xofShake256.rate) (Spec.Sha3.xofFinalizeContract X86_64.abi Spec.Sha3.xofShake256 656) :=
  xofFinalize_verified VG.Proof.Sha3.Instances.shake256_sponge (by decide)

theorem squeeze_shake256 :
    Verified X86_64.target (xofSqueeze Spec.Sha3.xofShake256.rate) (Spec.Sha3.xofSqueezeContract X86_64.abi Spec.Sha3.xofShake256 656) :=
  xofSqueeze_verified (by decide)

end VG.Proof.Sha3.X86_64.Instances
