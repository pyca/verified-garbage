module

public import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
public import VerifiedGarbage.Proof.Ecdsa.Verify.RISCV64.Hash
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyHash
import VerifiedGarbage.Proof.Ecdsa.Verify.Curves
meta import VerifiedGarbage.Proof.Ecdsa.Verify.RISCV64.Hash
meta import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyHash
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.Verify
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
public meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.CombVerified
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.SignVerified
public import VerifiedGarbage.Spec.Ecdsa.Verify.P521
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.VerifyLit
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.Verify
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.CombVerified
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.SignVerified
meta import VerifiedGarbage.Impl.Ecdsa.RISCV64.CombU
meta import VerifiedGarbage.Impl.Weierstrass.Layout.Mont
meta import VerifiedGarbage.Spec.Ecdsa.Verify.P521
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.VerifyLit
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
public meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P521Field.Verified
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.P521Field.Verified
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P521Order.Verified
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.P521Order.Verified

/-!
# ECDSA verification over P-521 on RISC-V: `Verified`

`verify_rv` with the function's constant time, by taint tracking (only the
pointers, in `a0`–`a3`, and the comb's table's address public, although the
contract lets every input affect timing), under `abi.withConsts` of the
comb's table (`verifyRVC_implies`, from `verifyRV_implies` without it, as for
signatures).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.P521

open VG VG.RISCV64 VG.Impl.Ecdsa.RISCV64.P521

/-! The constant-time analyses, with the comb's table public, of the calls of the addition and
subtraction modulo `p`, of the subtraction modulo `n`, and of `vg_p521_mul` from their arguments,
each done once for the check below. -/
taint_summary pAddSymSum : (taintSym [Impl.Ecdsa.RISCV64.CombU.p521Sym]) (Taint.ofRegs [.a0, .a1, .a2, .a3])
  (.call (Impl.Weierstrass.Mont.p521p.fn "add") Impl.Weierstrass.RISCV64.P521Field.addFnA)
  keeping (Taint.ofRegs [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11])
taint_summary pSubSymSum : (taintSym [Impl.Ecdsa.RISCV64.CombU.p521Sym]) (Taint.ofRegs [.a0, .a1, .a2, .a3])
  (.call (Impl.Weierstrass.Mont.p521p.fn "sub") Impl.Weierstrass.RISCV64.P521Field.subFnA)
  keeping (Taint.ofRegs [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11])
taint_summary nSubSymSum : (taintSym [Impl.Ecdsa.RISCV64.CombU.p521Sym]) (Taint.ofRegs [.a0, .a1, .a2, .a3])
  (.call (Impl.Weierstrass.Mont.p521n.fn "sub") Impl.Weierstrass.RISCV64.P521Order.subFnA)
  keeping (Taint.ofRegs [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11])
taint_summary mulSymSum : (taintSym [Impl.Ecdsa.RISCV64.CombU.p521Sym]) (Taint.ofRegs [.a0])
  (.call "vg_p521_mul" Impl.Ecdsa.RISCV64.mulP521)
  keeping (Taint.ofRegs [.s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11])
  using Comb.uMulSymSum Comb.uAddSymSum Comb.uSubSymSum Comb.uPackSymSum Comb.uUnpackSymSum

theorem verify_ct : ConstantTime isa verifyRVC.pre verifyRVC.pub verifyP521 :=
  VG.Taint.constantTime_of_exists (A := taintSym [Impl.Ecdsa.RISCV64.CombU.p521Sym])
    (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ ⟨⟨hsp, h0, h1, h2, h3⟩, hsy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2
      · exact h3⟩, fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩)
    (by taint_decide_sum [Comb.mulGSum, mulSymSum, Comb.pMulSymSum, pAddSymSum, pSubSymSum, nMulSymSum,
      nAddSymSum, nSubSymSum])

/-- A state satisfying the precondition without the table. -/
def verifySat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | .a3 => 0x8000 | _ => 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x1000, 133⟩, ⟨0x2000, 66⟩, ⟨0x3000, 132⟩]
  wr := [⟨0x8000, 8192⟩]

theorem verifyRV_implies : verifyRV.Implies (Proof.Ecdsa.verifyContract Spec.Ecdsa.P521.inst RISCV64.abi) :=
    { pre := by
        sig_implies_pre [Spec.Ecdsa.P521.inst, Proof.Ecdsa.verifyContract,
          Proof.Ecdsa.verifySig, Spec.P521.curve, Spec.Ecdsa.scratchWords, verifyRV, vf, RISCV64.abi,
          RISCV64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.Ecdsa.P521.inst, Proof.Ecdsa.verifyContract,
          Proof.Ecdsa.verifySig, Spec.P521.curve, Spec.Ecdsa.scratchWords, verifyRV, vf, RISCV64.abi,
          RISCV64.argRegs]
        have h' : s'.gpr .a0 = if vf s.mem (s.gpr .a0) (s.gpr .a1) (s.gpr .a2) then 1 else 0 := h
        rw [h']
        show BitVec.setWidth 32 (if vf s.mem (s.gpr .a0) (s.gpr .a1) (s.gpr .a2) then 1 else 0) =
          if vf s.mem (s.gpr .a0) (s.gpr .a1) (s.gpr .a2) then 1 else 0
        split <;> rfl
      pub := by
        sig_implies_pub [Spec.Ecdsa.P521.inst, Proof.Ecdsa.verifyContract,
          Proof.Ecdsa.verifySig, Spec.P521.curve, Spec.Ecdsa.scratchWords, verifyRV, vf, RISCV64.abi,
          RISCV64.argRegs]
      sat := by
        sig_implies_sat [Spec.Ecdsa.P521.inst, Proof.Ecdsa.verifyContract,
          Proof.Ecdsa.verifySig, Spec.P521.curve, Spec.Ecdsa.scratchWords, verifyRV, vf, RISCV64.abi,
          RISCV64.argRegs] [verifySat] using verifySat }

/-- A state satisfying the precondition with the table. -/
def verifySatC : State :=
  { verifySat with mem := Comb.combSatMem, rd := verifySat.rd ++ [⟨0x100000, 764928⟩], syms := fun _ => 0x100000 }

theorem verify_sat : (Proof.Ecdsa.verifyContract Spec.Ecdsa.P521.inst
    (RISCV64.abi.withConsts Impl.Ecdsa.RISCV64.CombU.p521CombConsts)).pre verifySatC := by
  have hl := Comb.combWords_length
  have held := Comb.combSatMem_held
  rw [show Impl.Ecdsa.RISCV64.CombU.p521CombConsts = [(Impl.Ecdsa.RISCV64.CombU.p521Sym,
    Impl.Ecdsa.RISCV64.CombU.p521CombWords)] from rfl]
  obtain ⟨W', eW⟩ : ∃ W, Impl.Ecdsa.RISCV64.CombU.p521CombWords = W := ⟨_, rfl⟩
  rw [eW] at hl held ⊢
  generalize e : verifySatC = s
  sig_pre [Spec.Ecdsa.P521.inst, Proof.Ecdsa.verifyContract, Proof.Ecdsa.verifySig, Spec.P521.curve,
    Spec.Ecdsa.scratchWords, RISCV64.abi, RISCV64.argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
    stackBelow]
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
    verifyRVC.Implies (Proof.Ecdsa.verifyContract Spec.Ecdsa.P521.inst
      (RISCV64.abi.withConsts Impl.Ecdsa.RISCV64.CombU.p521CombConsts)) :=
  { pre := fun _ hs => ⟨verifyRV_implies.pre _ (pre_consts.mp hs).1, (pre_consts.mp hs).2⟩
    post := fun s s' hs hp => post_consts.mpr (verifyRV_implies.post (stripConsts _ s) s'
      (pre_consts.mp hs).1 hp)
    pub := fun s₁ s₂ h₁ h₂ hp => ⟨verifyRV_implies.pub (stripConsts _ s₁) (stripConsts _ s₂)
        (pre_consts.mp h₁).1 (pre_consts.mp h₂).1 (pub_consts.mp hp).1,
      (pub_consts.mp hp).2 _ List.mem_cons_self⟩
    sat := ⟨verifySatC, verify_sat⟩ }

theorem verify_verified (hL : VG.Proof.Weierstrass.Law W) :
    Verified RISCV64.target verifyP521 (Proof.Ecdsa.verifyContract Spec.Ecdsa.P521.inst
      (RISCV64.abi.withConsts Impl.Ecdsa.RISCV64.CombU.p521CombConsts)) :=
  Verified.of_correct (verify_rv hL) verify_ct verifyRVC_implies

/-- `vg_ecdsa_p521_verify`, taking the hash function's output: the
verification above, run on the `len` bytes of the hash (`verifyHash_verified_cons`). -/
theorem verifyHash_verified (hL : VG.Proof.Weierstrass.Law W) :
    Verified RISCV64.target
      (Impl.Ecdsa.RISCV64.VerifyHash.verifyHash Spec.Ecdsa.P521.inst.curve.len true Impl.Ecdsa.RISCV64.P521.verifyP521)
      (Spec.Ecdsa.Instance.verifyHashContract Spec.Ecdsa.P521.inst
        (RISCV64.abi.withConsts Impl.Ecdsa.RISCV64.CombU.p521CombConsts) 80) :=
  Proof.Ecdsa.Verify.RISCV64.verifyHash_verified_cons Proof.Ecdsa.Verify.p521_len (by decide) (verify_verified hL)
    (by taint_decide) (Proof.Ecdsa.Verify.RISCV64.hashSat_cons (by decide) verify_sat (by decide) fun r hr => by
      simp only [verifySatC, verifySat, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide))

end VG.Proof.Ecdsa.RISCV64.P521
