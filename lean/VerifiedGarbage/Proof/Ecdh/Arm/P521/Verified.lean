module

public import VerifiedGarbage.Proof.Ecdh.Arm.Main
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
import VerifiedGarbage.Proof.Framework.Arm.TaintSym
import VerifiedGarbage.Proof.Ecdsa.Arm.Setup
public import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
meta import VerifiedGarbage.Proof.Framework.Arm.TaintSym
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Setup
meta import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
import VerifiedGarbage.Proof.Ecdsa.Arm.P521.Verified
import VerifiedGarbage.Proof.Ecdsa.Arm.P521.Umaal
public import VerifiedGarbage.Impl.Ecdh.P521.Arm
public import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Spec.EcKey.P521
public import VerifiedGarbage.Spec.Ecdh.Generic
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Ecdh.Arm.P521.Lit
import VerifiedGarbage.Proof.Ecdsa.Arm.P521.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ecdh.Arm.Main
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P521.Verified
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Impl.Ecdh.P521.Arm
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Spec.EcKey.P521
meta import VerifiedGarbage.Spec.Ecdh.Generic
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Ecdh.Arm.P521.Lit
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P521.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
import VerifiedGarbage.Proof.Framework.Arm.TaintMono
meta import VerifiedGarbage.Proof.Framework.Arm.TaintMono
public import VerifiedGarbage.Spec.EcKey.Generic
public import VerifiedGarbage.Spec.Ecdh
public import VerifiedGarbage.Spec.P521
public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.GetElem
meta import VerifiedGarbage.Spec.EcKey.Generic
meta import VerifiedGarbage.Spec.Ecdh
meta import VerifiedGarbage.Spec.P521
meta import VerifiedGarbage.TCB.Arm.Isa
meta import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.Framework.GetElem

/-! ### `Ecdh.Arm.P521.Contract`, which only this module used -/

section

/-!
# ECDH over P-521 on 32-bit ARM: the contract the proof is written against

The facts of `Spec.Ecdh.P521.inst.exchangeContract` for 32-bit ARM, by
name: `vg_ecdh_p521(out, d, peer, scratch)`, with the arguments in `r0`–`r3`
(AAPCS), the result in `r0` (the low word of `r1:r0`).
-/

@[expose] public section

namespace VG.Proof.Ecdh.Arm.P521

open VG VG.Arm Spec.Weierstrass Spec.EcKey

/-- The shared secret of the private key at `d` and the public key at
`peer`, as the specification computes it. -/
abbrev ex (m : Mem) (d peer : Addr) : Option (List Byte) :=
  Spec.Ecdh.exchange Spec.P521.curve (ofBytes (bytesAt m d 66)) (bytesAt m peer 133)

def ecdhArm : Contract Arm.isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 66⟩
    let d : Region := ⟨State.addr (s.gpr .r1), 66⟩
    let peer : Region := ⟨State.addr (s.gpr .r2), 133⟩
    let scratch : Region := ⟨State.addr (s.gpr .r3), 8192⟩
    s.rd = [d, peer] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧ d.Disjoint scratch ∧
      peer.Disjoint scratch ∧ (s.gpr .r0).toNat + 66 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 66 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 133 ≤ 2 ^ 32 ∧ (s.gpr .r3).toNat + 8192 ≤ 2 ^ 32
  post s s' :=
    match ex s.mem (State.addr (s.gpr .r1)) (State.addr (s.gpr .r2)) with
    | some z => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 1 ∧
      bytesAt s'.mem (State.addr (s.gpr .r0)) 66 = z
    | none => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 0 ∧
      bytesAt s'.mem (State.addr (s.gpr .r0)) 66 = List.replicate 66 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3

end VG.Proof.Ecdh.Arm.P521

end

end

/-!
# ECDH over P-521 on 32-bit ARM: `Verified`

`exchange_ok` for P-521 (`p521_ok`, and `Law` for its group law, which the
registration file supplies: `Proof.P521.law`) gives the contract's
postcondition; `r4`–`r11` and `lr` are restored and `sp` kept. Constant time
by taint tracking from the arguments' registers, as for the public key
(`Proof/EcKey/Arm/P256/Comb.lean`): the only branches are on loop counters,
and every address is `r12` (`scratch`), `lr` (`out`) or `r2` (`peer`) plus a
constant or a counter.
-/

@[expose] public section

namespace VG.Proof.Ecdh.Arm.P521

open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Ecdh.Arm VG.Proof.Ecdsa.Arm VG.Proof.Ecdsa.Arm.P521 Spec.Weierstrass

/-- The contract with the table of constants (`Cfg.constsK`), as the proof states it. -/
abbrev ecdhAC (u : Bool) : Contract isa := ecdhArm.withTablesArm (p521With u).constsK

theorem pre_of {u : Bool} {s : State} (h : ecdhArm.pre (stripConsts (p521With u).constsK s))
    (hk : ConstsOk (p521With u).constsK 0 s) : EPre (p521With u) s (constRegs (p521With u).constsK s) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨hk.rd_strip h1, h2, h3, h4, h5, h6, h7, h8, h9, fun _ => tbl_of_consts hk (List.mem_singleton_self _)
    (show (⟨ptr s .r3, 8192⟩ : Region) ∈ (stripConsts (p521With u).constsK s).wr by
      rw [h2]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _))⟩

theorem post_of {u : Bool} {s s' : State} (h : EPost (p521With u) s s') : ecdhArm.post s s' := by
  unfold EPost at h
  simp only [ecdhArm, BitVec.setWidth_append_eq_right]
  revert h
  generalize hq : ex s.mem (State.addr (s.gpr .r1)) (State.addr (s.gpr .r2)) = q
  rw [show Spec.Ecdh.exchange (p521With u).C (dk (p521With u) s)
      (Spec.Ecdsa.bytesAt s.mem (ptr s .r2) (1 + 2 * (p521With u).C.len)) =
        ex s.mem (State.addr (s.gpr .r1)) (State.addr (s.gpr .r2)) from rfl, hq]
  rcases q with _ | z <;> exact id

theorem ecdh_arm (hL : Weierstrass.Law Spec.P521.curve) (u : Bool) (s : State) (hs : (ecdhAC u).pre s) :
    ∃ t s', Exec isa (exchangeP521With u) s t s' ∧ abiPreserved s s' ∧ (ecdhAC u).post s s' := by
  obtain ⟨hp, hk⟩ := hs
  obtain ⟨t, s', he, K, hpost⟩ := exchange_ok (p521With_ok u) hL (pre_of hp hk)
  exact ⟨t, s', he, abi_of_saved K.saved K.sp, post_of hpost⟩

/-- The taint analysis starts with the arguments' registers public. -/
def τ₀ : VG.Arm.Taint.T := { regs := .ofList [.r0, .r1, .r2, .r3], flags := false }

/-- The taint analysis's start agrees in the two states. -/
theorem agree_τ₀ {s t : State} (h : ecdhArm.pub s t) : VG.Arm.Taint.Agree τ₀ s t := by
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

/-- The taint analysis's start, and the table's address, agree in the two states. -/
theorem agreeC {u : Bool} {s t : State} (h : (ecdhAC u).pub s t) :
    VG.Arm.Taint.Agree τ₀ s t ∧ ∀ n ∈ (p521With u).constsK.map Prod.fst, s.syms n = t.syms n :=
  ⟨agree_τ₀ h.1, withTablesArm_syms h⟩

theorem ecdh_ct : ConstantTime isa (ecdhAC false).pre (ecdhAC false).pub exchangeP521 :=
  VG.Taint.constantTime_of_exists (A := taintC) τ₀ (fun _ _ _ _ h => agreeC h)
    (by taint_decide_sum [mulPSum, addPSum, subPSum, mulSum])

theorem ecdhU_ct : ConstantTime isa (ecdhAC true).pre (ecdhAC true).pub exchangeP521U :=
  VG.Taint.constantTime (A := taintSymU [(p521With true).constSym]) τ₀ (fun _ _ _ _ h => agreeC h)
    (by taint_decide)

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
  rd := [⟨0x2000, 66⟩, ⟨0x3000, 133⟩]
  wr := [⟨0x1000, 66⟩, ⟨0x8000, 8192⟩]

/-- The contract as the proof states it implies the exchange's (without the table). -/
theorem ecdhArm_implies :
    ecdhArm.Implies (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P521.inst Arm.abi) :=
    { pre := by
        sig_implies_pre [Spec.EcKey.P521.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P521.curve, Spec.EcKey.scratchWords, ecdhArm, ex, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by
        intro s s' _ h
        sig_post [Spec.EcKey.P521.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P521.curve, Spec.EcKey.scratchWords, ecdhArm, ex, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
        simp only [ecdhArm, ex, Spec.P521.curve, Arm.State.addr] at h
        revert h
        generalize Spec.Ecdh.exchange _ _ _ = q
        rcases q with _ | z <;> exact id
      pub := by
        sig_implies_pub [Spec.EcKey.P521.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P521.curve, Spec.EcKey.scratchWords, ecdhArm, ex, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := by
        sig_implies_sat [Spec.EcKey.P521.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P521.curve, Spec.EcKey.scratchWords, ecdhArm, ex, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
          [satState, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using satState }

/-- `satState`, holding the table at `0x100000`. -/
def satStateC (u : Bool) : State := { satState with
  mem := constMem ((0x100000 : BitVec 32).setWidth 64) (p521With u).constTbl
  syms := fun _ => 0x100000 }

theorem satC (u : Bool) :
    ∃ s, (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P521.inst (Arm.abi.withConsts (p521With u).constsK)).pre s :=
  sat_consts (s := satStateC u)
    (by cases u <;> sig_sat_check [Spec.EcKey.P521.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P521.curve, Spec.EcKey.scratchWords, ecdhArm, ex, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr])
    (constsOk_tbl _ (T := 0x100000) rfl rfl (by cases u <;> decide) (by decide) (by cases u <;> decide)
      (by cases u <;> decide))

theorem ecdhAC_implies (u : Bool) :
    (ecdhAC u).Implies
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P521.inst (Arm.abi.withConsts (p521With u).constsK)) :=
  withTables_implies ecdhArm_implies (satC u)

theorem ecdhWith_verified (hL : Weierstrass.Law Spec.P521.curve) (u : Bool)
    (hct : ConstantTime isa (ecdhAC u).pre (ecdhAC u).pub (exchangeP521With u)) :
    Verified Arm.target (exchangeP521With u)
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P521.inst (Arm.abi.withConsts (p521With u).constsK)) :=
  Verified.of_correct (ecdh_arm hL u) hct (ecdhAC_implies u)

theorem ecdh_verified (hL : Weierstrass.Law Spec.P521.curve) :
    Verified Arm.target exchangeP521
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P521.inst (Arm.abi.withConsts (p521With false).constsK)) :=
  ecdhWith_verified hL false ecdh_ct

theorem ecdhU_verified (hL : Weierstrass.Law Spec.P521.curve) :
    Verified Arm.target exchangeP521U
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P521.inst (Arm.abi.withConsts (p521With true).constsK)) :=
  ecdhWith_verified hL true ecdhU_ct

end VG.Proof.Ecdh.Arm.P521
