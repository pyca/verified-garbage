module

public import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Hash
public import VerifiedGarbage.Impl.Ecdsa.PPC64LE.VerifyHash
import VerifiedGarbage.Proof.Ecdsa.Verify.Curves
meta import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Hash
meta import VerifiedGarbage.Impl.Ecdsa.PPC64LE.VerifyHash
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Main
public import VerifiedGarbage.Impl.Ecdsa.Verify.P192.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Setup
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.P192.Lit
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P192
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Main
meta import VerifiedGarbage.Impl.Ecdsa.Verify.P192.PPC64LE
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
meta import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Setup
meta import VerifiedGarbage.Spec.Ecdsa.Verify.P192
meta import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.P192.Lit
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P192
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Ecdsa.P192
public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
public import VerifiedGarbage.Spec.Ecdsa.Generic
public import VerifiedGarbage.Spec.Ecdsa.Verify
public import VerifiedGarbage.Spec.P192
public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Spec.Ecdsa.Generic
meta import VerifiedGarbage.Spec.Ecdsa.Verify
meta import VerifiedGarbage.Spec.P192
meta import VerifiedGarbage.TCB.PPC64LE.Isa
meta import VerifiedGarbage.Proof.Framework.PowLit

/-! ### `Ecdsa.Verify.PPC64LE.P192.Contract`, which only this module used -/

section

/-!
# ECDSA verification over P-192 on PPC64LE: the contract the proof is written against

The facts of `Proof.Ecdsa.verifyContract Spec.Ecdsa.P192.inst` for PPC64LE, by name:
`vg_ecdsa_p192_verify(public, digest, sig, scratch)`, with the arguments in
`r3`–`r6` and the result in `r3` (ELFv2). Only the pointers are public here:
the proof shows that nothing else affects timing, although the contract
would let the contents of the three buffers.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.PPC64LE.P192

open VG VG.PPC64LE Spec.Weierstrass Spec.Ecdsa

/-- Whether the signature at `sig` of the hash at `digest` is valid for the
public key at `pk`, as the specification says. -/
abbrev vf (m : Mem) (pk digest sig : Addr) : Bool :=
  verify Spec.P192.curve (bytesAt m pk 49) (hashToInt Spec.P192.curve (bytesAt m digest 24)) (bytesAt m sig 48)

def verifyPPC : Contract PPC64LE.isa where
  pre s :=
    let pk : Region := ⟨s.gpr .r3, 49⟩
    let digest : Region := ⟨s.gpr .r4, 24⟩
    let sig : Region := ⟨s.gpr .r5, 48⟩
    let scratch : Region := ⟨s.gpr .r6, 8192⟩
    s.rd = [pk, digest, sig] ∧ s.wr = [scratch] ∧ pk.Disjoint scratch ∧ digest.Disjoint scratch ∧
      sig.Disjoint scratch ∧ (s.gpr .r3).toNat + 49 ≤ 2 ^ 64 ∧ (s.gpr .r4).toNat + 24 ≤ 2 ^ 64 ∧
      (s.gpr .r5).toNat + 48 ≤ 2 ^ 64 ∧ (s.gpr .r6).toNat + 8192 ≤ 2 ^ 64
  post s s' := s'.gpr .r3 = if vf s.mem (s.gpr .r3) (s.gpr .r4) (s.gpr .r5) then 1 else 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧
    s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.gpr .r6 = s₂.gpr .r6

end VG.Proof.Ecdsa.Verify.PPC64LE.P192

end

end

/-!
# ECDSA verification over P-192 on PPC64LE: `Verified`

`verify_ppc`: from `verify_ok`, for P-192's configuration; `verify_ct`: the
time depends only on the pointers (`taint_decide` on the code's literal).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.PPC64LE.P192

open VG VG.PPC64LE VG.Proof.Ecdsa.Verify.PPC64LE VG.Impl.Ecdsa.PPC64LE VG.Impl.Ecdsa.Verify.PPC64LE VG.Proof.Ecdsa.PPC64LE Spec.Weierstrass

/-- The contract with the table of constants (`Cfg.constsK`), as the proof states it. -/
abbrev vPC : Contract isa := verifyPPC.withTables p192.constsK

theorem pre_of {s : State} (h : verifyPPC.pre (stripConsts p192.constsK s)) (hk : ConstsOk p192.constsK 0 s) :
    VPre p192 s (constRegs p192.constsK s) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨hk.rd_strip h1, h2, h3, h4, h5, h6, h7, h8, h9, tbl_of_consts hk (List.mem_singleton_self _)
    (hk.disjoint_wr (List.mem_singleton_self _) (by
      show (⟨s.gpr .r6, size⟩ : Region) ∈ (stripConsts p192.constsK s).wr
      rw [h2]; exact List.mem_singleton_self _))⟩

theorem verify_ppc (hL : Weierstrass.Law Spec.P192.curve) (s : State) (hs : vPC.pre s) :
    ∃ t s', Exec isa verifyP192 s t s' ∧ abiPreserved s s' ∧ vPC.post s s' := by
  obtain ⟨hp, hk⟩ := hs
  obtain ⟨t, s', he, K, hpost⟩ := verify_ok p192_ok (by decide) hL (pre_of hp hk)
  exact ⟨t, s', he, ⟨K.saved, K.sp, K.lr⟩, hpost⟩

theorem verify_ct : ConstantTime isa vPC.pre vPC.pub verifyP192 :=
  VG.Taint.constantTime (A := taintSym [p192.constSym]) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ ⟨⟨hsp, h3, h4, h5, h6⟩, sy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h3
      · exact h4
      · exact h5
      · exact h6⟩, fun n hn => by
        simp only [List.mem_singleton] at hn; subst hn; exact sy _ (List.mem_singleton_self _)⟩)
    (by taint_decide)

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r6 => 0x8000 | _ => 0
  lr := 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x1000, 49⟩, ⟨0x2000, 24⟩, ⟨0x3000, 48⟩]
  wr := [⟨0x8000, 8192⟩]

/-- `verifyPPC` states `verifyContract`'s facts by name. -/
theorem verifyPPC_implies : verifyPPC.Implies (Proof.Ecdsa.verifyContract Spec.Ecdsa.P192.inst PPC64LE.abi) :=
    { pre := by
        sig_implies_pre [Spec.Ecdsa.P192.inst, Proof.Ecdsa.verifyContract,
          Proof.Ecdsa.verifySig, Spec.P192.curve, Spec.Ecdsa.scratchWords, verifyPPC, vf,
          PPC64LE.abi, PPC64LE.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.Ecdsa.P192.inst, Proof.Ecdsa.verifyContract,
          Proof.Ecdsa.verifySig, Spec.P192.curve, Spec.Ecdsa.scratchWords, verifyPPC, vf,
          PPC64LE.abi, PPC64LE.argRegs]
        simp only [verifyPPC, vf, Spec.P192.curve] at h
        revert h
        split <;> rename_i hv <;> simp only [hv, ite_true, ite_false, Bool.false_eq_true] <;>
          exact fun h => by rw [h]; rfl
      pub := by
        sig_implies_pub [Spec.Ecdsa.P192.inst, Proof.Ecdsa.verifyContract,
          Proof.Ecdsa.verifySig, Spec.P192.curve, Spec.Ecdsa.scratchWords, verifyPPC, vf,
          PPC64LE.abi, PPC64LE.argRegs]
      sat := by
        sig_implies_sat [Spec.Ecdsa.P192.inst, Proof.Ecdsa.verifyContract,
          Proof.Ecdsa.verifySig, Spec.P192.curve, Spec.Ecdsa.scratchWords, verifyPPC, vf,
          PPC64LE.abi, PPC64LE.argRegs]
          [satState] using satState }

/-- The memory of the witnesses with the table: the table at `0x100000`
(irreducible: unfolding it in a definitional check would evaluate the table). -/
@[irreducible] def tSatMem : Mem := constMem 0x100000 p192.constTbl

theorem tSatMem_held : ∀ i < p192.constTbl.length,
    tSatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = p192.constTbl.getD i 0 := by
  unfold tSatMem
  exact constMem_held _ _ (by rw [constTbl_length]; decide)

theorem constsK_eq : p192.constsK = [(p192.constSym, p192.constTbl)] := rfl

/-- A state satisfying the precondition with the table. -/
def vSatC : State :=
  { satState with mem := tSatMem, rd := satState.rd ++ [⟨0x100000, 8 * (17 * 3)⟩], syms := fun _ => 0x100000 }

theorem vSat : (Proof.Ecdsa.verifyContract Spec.Ecdsa.P192.inst (abi.withConsts p192.constsK)).pre vSatC := by
  have hl := constTbl_length p192
  have held := tSatMem_held
  rw [constsK_eq]
  obtain ⟨W, eW⟩ : ∃ W, p192.constTbl = W := ⟨_, rfl⟩
  rw [eW] at hl held ⊢
  generalize e : vSatC = s
  sig_pre [Spec.Ecdsa.P192.inst, Proof.Ecdsa.verifyContract, Proof.Ecdsa.verifySig, Spec.P192.curve,
    Spec.Ecdsa.scratchWords, abi, argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst e
  rw [hl]
  refine ⟨rfl, fun i hi => held i (by rw [hl]; exact hi), by decide, fun r hr => ?_, by decide, ?_⟩
  · change r ∈ [⟨0x8000, 8192⟩] at hr
    obtain rfl := List.mem_singleton.mp hr
    exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl

theorem vPC_implies :
    vPC.Implies (Proof.Ecdsa.verifyContract Spec.Ecdsa.P192.inst (abi.withConsts p192.constsK)) :=
  withTables_implies verifyPPC_implies ⟨vSatC, vSat⟩

theorem verify_verified (hL : Weierstrass.Law Spec.P192.curve) :
    Verified PPC64LE.target verifyP192
      (Proof.Ecdsa.verifyContract Spec.Ecdsa.P192.inst (PPC64LE.abi.withConsts p192.constsK)) :=
  Verified.of_correct (verify_ppc hL) verify_ct vPC_implies

/-- A state satisfying `verifyHashContract`'s precondition with the table, with an empty hash. -/
def hSatC : State :=
  let h := Proof.Ecdsa.Verify.PPC64LE.Hash.hashSatState 24
  { h with mem := tSatMem, rd := h.rd ++ [⟨0x100000, 8 * (17 * 3)⟩], syms := fun _ => 0x100000 }

theorem verifyHash_sat :
    ∃ s, (Spec.Ecdsa.P192.inst.verifyHashContract (PPC64LE.abi.withConsts p192.constsK) 112).pre s := by
  refine ⟨hSatC, ?_⟩
  have hl := constTbl_length p192
  have held := tSatMem_held
  rw [constsK_eq]
  obtain ⟨W, eW⟩ : ∃ W, p192.constTbl = W := ⟨_, rfl⟩
  rw [eW] at hl held ⊢
  generalize e : hSatC = s
  sig_pre [Spec.Ecdsa.Instance.verifyHashContract, Spec.Ecdsa.Instance.verifyHashSig, Spec.Ecdsa.P192.inst,
    Spec.P192.curve, Spec.Ecdsa.scratchWords, PPC64LE.abi, PPC64LE.argRegs, Abi.withConsts, Abi.constRegions,
    Abi.constsHeld, stackBelow]
  subst e
  rw [hl]
  refine ⟨by decide, rfl, fun i hi => held i (by rw [hl]; exact hi), by decide, fun r hr => ?_,
    Region.disjoint_of_sep (by decide), by decide, rfl, rfl, Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    by decide, by decide, by decide, by decide⟩
  change r ∈ [⟨0x8000, 8192⟩] at hr
  obtain rfl := List.mem_singleton.mp hr
  exact Region.disjoint_of_sep (by decide)

/-- `vg_ecdsa_p192_verify`, taking the hash function's output: the
verification above, run on the `len` bytes of the hash
(`Hash.verifyHash_verified_cons`). -/
theorem verifyHash_verified (hL : Weierstrass.Law Spec.P192.curve) :
    Verified PPC64LE.target
      (Impl.Ecdsa.PPC64LE.VerifyHash.verifyHash Spec.Ecdsa.P192.inst.curve.len false verifyP192)
      (Spec.Ecdsa.P192.inst.verifyHashContract (PPC64LE.abi.withConsts p192.constsK) 112) :=
  Proof.Ecdsa.Verify.PPC64LE.Hash.verifyHash_verified_cons Proof.Ecdsa.Verify.p192_len (by decide)
    (verify_verified hL) (by taint_decide) verifyHash_sat

end VG.Proof.Ecdsa.Verify.PPC64LE.P192
