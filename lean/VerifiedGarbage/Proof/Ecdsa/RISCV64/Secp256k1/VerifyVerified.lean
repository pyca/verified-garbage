module

public import VerifiedGarbage.Proof.Ecdsa.Verify.RISCV64.Hash
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyHash
import VerifiedGarbage.Proof.Ecdsa.Verify.Curves
meta import VerifiedGarbage.Proof.Ecdsa.Verify.RISCV64.Hash
meta import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyHash
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Secp256k1.Verify
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ecdsa.RISCV64.Secp256k1.CombVerified
public import VerifiedGarbage.Spec.Ecdsa.Verify.Secp256k1
import VerifiedGarbage.Proof.Ecdsa.RISCV64.Secp256k1.VerifyLit
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.Secp256k1.Verify
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.Secp256k1.CombVerified
meta import VerifiedGarbage.Spec.Ecdsa.Verify.Secp256k1
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.Secp256k1.VerifyLit
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# ECDSA verification over secp256k1 on RISC-V: `Verified`

`verify_rv` with the function's constant time, by taint tracking (only the
pointers, in `a0`–`a3`, and the comb's table's address public, although the
contract lets every input affect timing), under `abi.withConsts` of the
comb's table (`verifyRVC_implies`, from `verifyRV_implies` without it, as for
signatures).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.Secp256k1

open VG VG.RISCV64 VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdsa.RISCV64.Verify

theorem verify_ct : ConstantTime isa verifyRVC.pre verifyRVC.pub verifySecp256k1 :=
  VG.Taint.constantTime (A := taintSym [Impl.Ecdsa.RISCV64.Comb.secp256k1Sym]) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ ⟨⟨hsp, h0, h1, h2, h3⟩, hsy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2
      · exact h3⟩, fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩) (by taint_decide)

/-- A state satisfying the precondition without the table. -/
def verifySat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | .a3 => 0x8000 | _ => 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x1000, 65⟩, ⟨0x2000, 32⟩, ⟨0x3000, 64⟩]
  wr := [⟨0x8000, 8192⟩]

theorem verifyRV_implies :
    verifyRV.Implies (Spec.Ecdsa.Instance.verifyContract Spec.Ecdsa.Secp256k1.inst RISCV64.abi) :=
    { pre := by
        sig_implies_pre [Spec.Ecdsa.Secp256k1.inst, Spec.Ecdsa.Instance.verifyContract,
          Spec.Ecdsa.Instance.verifySig, Spec.Secp256k1.curve, Spec.Ecdsa.scratchWords, verifyRV, vf, RISCV64.abi,
          RISCV64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.Ecdsa.Secp256k1.inst, Spec.Ecdsa.Instance.verifyContract,
          Spec.Ecdsa.Instance.verifySig, Spec.Secp256k1.curve, Spec.Ecdsa.scratchWords, verifyRV, vf, RISCV64.abi,
          RISCV64.argRegs]
        have h' : s'.gpr .a0 = if vf s.mem (s.gpr .a0) (s.gpr .a1) (s.gpr .a2) then 1 else 0 := h
        rw [h']
        show BitVec.setWidth 32 (if vf s.mem (s.gpr .a0) (s.gpr .a1) (s.gpr .a2) then 1 else 0) =
          if vf s.mem (s.gpr .a0) (s.gpr .a1) (s.gpr .a2) then 1 else 0
        split <;> rfl
      pub := by
        sig_implies_pub [Spec.Ecdsa.Secp256k1.inst, Spec.Ecdsa.Instance.verifyContract,
          Spec.Ecdsa.Instance.verifySig, Spec.Secp256k1.curve, Spec.Ecdsa.scratchWords, verifyRV, vf, RISCV64.abi,
          RISCV64.argRegs]
      sat := by
        sig_implies_sat [Spec.Ecdsa.Secp256k1.inst, Spec.Ecdsa.Instance.verifyContract,
          Spec.Ecdsa.Instance.verifySig, Spec.Secp256k1.curve, Spec.Ecdsa.scratchWords, verifyRV, vf, RISCV64.abi,
          RISCV64.argRegs] [verifySat] using verifySat }

/-- A state satisfying the precondition with the table. -/
def verifySatC : State :=
  { verifySat with mem := Comb.combSatMem, rd := verifySat.rd ++ [⟨0x100000, 151552⟩], syms := fun _ => 0x100000 }

theorem verify_sat : (Spec.Ecdsa.Instance.verifyContract Spec.Ecdsa.Secp256k1.inst
    (RISCV64.abi.withConsts Impl.Ecdsa.RISCV64.Comb.secp256k1CombConsts)).pre verifySatC := by
  have hl := Comb.combWords_length
  have held := Comb.combSatMem_held
  rw [show Impl.Ecdsa.RISCV64.Comb.secp256k1CombConsts = [(Impl.Ecdsa.RISCV64.Comb.secp256k1Sym,
    Impl.Ecdsa.RISCV64.Comb.secp256k1CombWords)] from rfl]
  generalize Impl.Ecdsa.RISCV64.Comb.secp256k1CombWords = W' at hl held ⊢
  generalize e : verifySatC = s
  sig_pre [Spec.Ecdsa.Secp256k1.inst, Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig,
    Spec.Secp256k1.curve, Spec.Ecdsa.scratchWords, RISCV64.abi, RISCV64.argRegs, Abi.withConsts,
    Abi.constRegions, Abi.constsHeld, stackBelow]
  subst e
  rw [hl]
  refine ⟨by decide, rfl, fun i hi => held i (by rw [hl]; exact hi), by decide, fun r hr => ?_, by decide, rfl, rfl,
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    by decide, by decide, by decide, by decide, by decide⟩
  change r ∈ [⟨0x8000, 8192⟩] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  exact Region.disjoint_of_sep (by decide)

theorem verifyRVC_implies :
    verifyRVC.Implies (Spec.Ecdsa.Instance.verifyContract Spec.Ecdsa.Secp256k1.inst
      (RISCV64.abi.withConsts Impl.Ecdsa.RISCV64.Comb.secp256k1CombConsts)) :=
  { pre := fun _ hs => ⟨verifyRV_implies.pre _ (pre_consts.mp hs).1, (pre_consts.mp hs).2⟩
    post := fun s s' hs hp => post_consts.mpr (verifyRV_implies.post (stripConsts _ s) s'
      (pre_consts.mp hs).1 hp)
    pub := fun s₁ s₂ h₁ h₂ hp => ⟨verifyRV_implies.pub (stripConsts _ s₁) (stripConsts _ s₂)
        (pre_consts.mp h₁).1 (pre_consts.mp h₂).1 (pub_consts.mp hp).1,
      (pub_consts.mp hp).2 _ List.mem_cons_self⟩
    sat := ⟨verifySatC, verify_sat⟩ }

theorem verify_verified (hL : VG.Proof.Weierstrass.Law W) :
    Verified RISCV64.target verifySecp256k1 (Spec.Ecdsa.Instance.verifyContract Spec.Ecdsa.Secp256k1.inst
      (RISCV64.abi.withConsts Impl.Ecdsa.RISCV64.Comb.secp256k1CombConsts)) :=
  Verified.of_correct (verify_rv hL) verify_ct verifyRVC_implies


/-- `vg_ecdsa_secp256k1_verify`, taking the hash function's output: the
verification above, run on the `len` bytes of the hash (`verifyHash_verified_cons`). -/
theorem verifyHash_verified (hL : VG.Proof.Weierstrass.Law W) :
    Verified RISCV64.target
      (Impl.Ecdsa.RISCV64.VerifyHash.verifyHash Spec.Ecdsa.Secp256k1.inst.curve.len false Impl.Ecdsa.RISCV64.verifySecp256k1)
      (Spec.Ecdsa.Instance.verifyHashContract Spec.Ecdsa.Secp256k1.inst (RISCV64.abi.withConsts Impl.Ecdsa.RISCV64.Comb.secp256k1CombConsts) 80) :=
  Proof.Ecdsa.Verify.RISCV64.verifyHash_verified_cons Proof.Ecdsa.Verify.secp256k1_len (by decide) (verify_verified hL)
    (by taint_decide) (Proof.Ecdsa.Verify.RISCV64.hashSat_cons (by decide) verify_sat (by decide) fun r hr => by
      simp only [verifySatC, verifySat, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide))

end VG.Proof.Ecdsa.RISCV64.Secp256k1
