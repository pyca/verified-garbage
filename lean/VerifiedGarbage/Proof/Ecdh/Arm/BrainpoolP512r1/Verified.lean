module

public import VerifiedGarbage.Proof.Ecdh.Arm.Main
import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.Config
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP512r1.Arm
public import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
public import VerifiedGarbage.Spec.EcKey.BrainpoolP512r1
public import VerifiedGarbage.Spec.Ecdh.Generic
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Ecdh.Arm.BrainpoolP512r1.Lit
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ecdh.Arm.Main
meta import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.Config
meta import VerifiedGarbage.Impl.Ecdh.BrainpoolP512r1.Arm
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Spec.EcKey.BrainpoolP512r1
meta import VerifiedGarbage.Spec.Ecdh.Generic
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Ecdh.Arm.BrainpoolP512r1.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
public import VerifiedGarbage.Spec.BrainpoolP512r1
public import VerifiedGarbage.Spec.EcKey.Generic
public import VerifiedGarbage.Spec.Ecdh
public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.GetElem
meta import VerifiedGarbage.Spec.BrainpoolP512r1
meta import VerifiedGarbage.Spec.EcKey.Generic
meta import VerifiedGarbage.Spec.Ecdh
meta import VerifiedGarbage.TCB.Arm.Isa
meta import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.Framework.GetElem

/-! ### `Ecdh.Arm.BrainpoolP512r1.Contract`, which only this module used -/

section

/-!
# ECDH over brainpoolP512r1 on 32-bit ARM: the contract the proof is written against

The facts of `Spec.Ecdh.BrainpoolP512r1.inst.exchangeContract` for 32-bit ARM, by
name: `vg_ecdh_brainpoolp512r1(out, d, peer, scratch)`, with the arguments in `r0`–`r3`
(AAPCS), the result in `r0` (the low word of `r1:r0`).
-/

@[expose] public section

namespace VG.Proof.Ecdh.Arm.BrainpoolP512r1

open VG VG.Arm Spec.Weierstrass Spec.EcKey

/-- The shared secret of the private key at `d` and the public key at
`peer`, as the specification computes it. -/
abbrev ex (m : Mem) (d peer : Addr) : Option (List Byte) :=
  Spec.Ecdh.exchange Spec.BrainpoolP512r1.curve (ofBytes (bytesAt m d 64)) (bytesAt m peer 129)

def ecdhArm : Contract Arm.isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 64⟩
    let d : Region := ⟨State.addr (s.gpr .r1), 64⟩
    let peer : Region := ⟨State.addr (s.gpr .r2), 129⟩
    let scratch : Region := ⟨State.addr (s.gpr .r3), 8192⟩
    s.rd = [d, peer] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧ d.Disjoint scratch ∧
      peer.Disjoint scratch ∧ (s.gpr .r0).toNat + 64 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 64 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 129 ≤ 2 ^ 32 ∧ (s.gpr .r3).toNat + 8192 ≤ 2 ^ 32
  post s s' :=
    match ex s.mem (State.addr (s.gpr .r1)) (State.addr (s.gpr .r2)) with
    | some z => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 1 ∧
      bytesAt s'.mem (State.addr (s.gpr .r0)) 64 = z
    | none => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 0 ∧
      bytesAt s'.mem (State.addr (s.gpr .r0)) 64 = List.replicate 64 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3

end VG.Proof.Ecdh.Arm.BrainpoolP512r1

end

end

/-!
# ECDH over brainpoolP512r1 on 32-bit ARM: `Verified`

`exchange_ok` for brainpoolP512r1 (`brainpoolp512r1_ok`, and `Law` for its group law, which the
registration file supplies: `Proof.BrainpoolP512r1.law`) gives the contract's
postcondition; `r4`–`r11` and `lr` are restored and `sp` kept. Constant time
by taint tracking from the arguments' registers, as for the public key
(`Proof/EcKey/Arm/P256/Comb.lean`): the only branches are on loop counters,
and every address is `r12` (`scratch`), `lr` (`out`) or `r2` (`peer`) plus a
constant or a counter.
-/

@[expose] public section

namespace VG.Proof.Ecdh.Arm.BrainpoolP512r1

open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Ecdh.Arm VG.Proof.Ecdsa.Arm VG.Proof.Ecdsa.Arm.BrainpoolP512r1 Spec.Weierstrass

theorem pre_of {u : Bool} {s : State} (h : ecdhArm.pre s) : EPre (brainpoolp512r1With u) s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem post_of {u : Bool} {s s' : State} (h : EPost (brainpoolp512r1With u) s s') : ecdhArm.post s s' := by
  unfold EPost at h
  simp only [ecdhArm, BitVec.setWidth_append_eq_right]
  revert h
  generalize hq : ex s.mem (State.addr (s.gpr .r1)) (State.addr (s.gpr .r2)) = q
  rw [show Spec.Ecdh.exchange (brainpoolp512r1With u).C (dk (brainpoolp512r1With u) s)
      (Spec.Ecdsa.bytesAt s.mem (ptr s .r2) (1 + 2 * (brainpoolp512r1With u).C.len)) =
        ex s.mem (State.addr (s.gpr .r1)) (State.addr (s.gpr .r2)) from rfl, hq]
  rcases q with _ | z <;> exact id

theorem ecdh_arm (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) (u : Bool) (s : State) (hs : ecdhArm.pre s) :
    ∃ t s', Exec isa (exchangeBrainpoolP512r1With u) s t s' ∧ abiPreserved s s' ∧ ecdhArm.post s s' := by
  have hp := pre_of (u := u) hs
  obtain ⟨t, s', he, K, hpost⟩ := exchange_ok (brainpoolp512r1With_ok u) hL hp
  exact ⟨t, s', he, abi_of_saved K.saved K.sp, post_of hpost⟩

/-- The taint analysis starts with the arguments' registers public. -/
def τ₀ : VG.Arm.Taint.T := { regs := .ofList [.r0, .r1, .r2, .r3], flags := false }

/-- The taint analysis's start agrees in the two states. -/
theorem agree_τ₀ {s t : State} (_hs : ecdhArm.pre s) (_ht : ecdhArm.pre t) (h : ecdhArm.pub s t) :
    VG.Arm.Taint.Agree τ₀ s t := by
  obtain ⟨_, h0, h1, h2, h3⟩ := h
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h,
    ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim, fun h => absurd h (by decide),
      fun _ h => (List.not_mem_nil h).elim⟩,
    ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim, fun h => absurd h (by decide),
      fun _ h => (List.not_mem_nil h).elim⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun h => absurd h (Nat.lt_irrefl 0), fun _ h => absurd h (Nat.not_lt_zero _)⟩
  simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem ecdh_ct : ConstantTime isa ecdhArm.pre ecdhArm.pub exchangeBrainpoolP512r1 :=
  VG.Taint.constantTime (A := taint) τ₀ (fun _ _ hs ht h => agree_τ₀ hs ht h) (by native_taint_decide)

theorem ecdhU_ct : ConstantTime isa ecdhArm.pre ecdhArm.pub exchangeBrainpoolP512r1U :=
  VG.Taint.constantTime (A := taintU) τ₀ (fun _ _ hs ht h => agree_τ₀ hs ht h) (by taint_decide)

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 0x8000 | _ => 0
  sp := 0x20000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 129⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x8000, 8192⟩]

theorem ecdhWith_verified (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) (u : Bool)
    (hct : ConstantTime isa ecdhArm.pre ecdhArm.pub (exchangeBrainpoolP512r1With u)) :
    Verified Arm.target (exchangeBrainpoolP512r1With u) (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.BrainpoolP512r1.inst Arm.abi) :=
  Verified.of_correct (ecdh_arm hL u) hct
    { pre := by
        sig_implies_pre [Spec.EcKey.BrainpoolP512r1.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.BrainpoolP512r1.curve, Spec.EcKey.scratchWords, ecdhArm, ex, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by
        intro s s' _ h
        sig_post [Spec.EcKey.BrainpoolP512r1.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.BrainpoolP512r1.curve, Spec.EcKey.scratchWords, ecdhArm, ex, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
        simp only [ecdhArm, ex, Spec.BrainpoolP512r1.curve, Arm.State.addr] at h
        revert h
        generalize Spec.Ecdh.exchange _ _ _ = q
        rcases q with _ | z <;> exact id
      pub := by
        sig_implies_pub [Spec.EcKey.BrainpoolP512r1.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.BrainpoolP512r1.curve, Spec.EcKey.scratchWords, ecdhArm, ex, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := by
        sig_implies_sat [Spec.EcKey.BrainpoolP512r1.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.BrainpoolP512r1.curve, Spec.EcKey.scratchWords, ecdhArm, ex, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
          [satState, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using satState }

theorem ecdh_verified (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) :
    Verified Arm.target exchangeBrainpoolP512r1 (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.BrainpoolP512r1.inst Arm.abi) :=
  ecdhWith_verified hL false ecdh_ct

theorem ecdhU_verified (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) :
    Verified Arm.target exchangeBrainpoolP512r1U (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.BrainpoolP512r1.inst Arm.abi) :=
  ecdhWith_verified hL true ecdhU_ct

end VG.Proof.Ecdh.Arm.BrainpoolP512r1
