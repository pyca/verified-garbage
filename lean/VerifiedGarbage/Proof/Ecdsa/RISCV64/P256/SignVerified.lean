module

public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P256.Sign
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Spec.Ecdsa.P256
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P256.SignLit
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.Contract
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P256.Sign
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Spec.Ecdsa.P256
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P256.SignLit
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# ECDSA signatures over P-256 on RISC-V: `Verified`

`sign_rv` with the function's constant time, by taint tracking (only the
pointers, in `a0`–`a4`, and the comb's table's address public: every address
is a pointer or the table's address plus a constant, and the only branches
are the callees' loops, on their counters), under `abi.withConsts` of the
comb's table (`signRVC_implies`, from `signRV_implies` without it, as for
the other targets' tables).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.P256

open VG VG.RISCV64 VG.Impl.Ecdsa.RISCV64.Sign

theorem sign_ct : ConstantTime isa signRVC.pre signRVC.pub signP256 :=
  VG.Taint.constantTime (A := taintSym [Impl.Ecdsa.RISCV64.Comb.p256Sym]) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4])
    (fun _ _ _ _ ⟨⟨hsp, h0, h1, h2, h3, h4⟩, hsy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2
      · exact h3
      · exact h4⟩, fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩) (by taint_decide)

/-- A state satisfying the precondition without the table. -/
def signSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | .a3 => 0x4000 | .a4 => 0x8000 | _ => 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩, ⟨0x4000, 32⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x8000, 8192⟩]

theorem signRV_implies : signRV.Implies (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.P256.inst RISCV64.abi) :=
    { pre := by
        sig_implies_pre [Spec.Ecdsa.P256.inst, Proof.Ecdsa.Instance.signContract,
          Proof.Ecdsa.Instance.signSig, Spec.P256.curve, Spec.Ecdsa.scratchWords, signRV, sg, RISCV64.abi,
          RISCV64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.Ecdsa.P256.inst, Proof.Ecdsa.Instance.signContract,
          Proof.Ecdsa.Instance.signSig, Spec.P256.curve, Spec.Ecdsa.scratchWords, signRV, sg, RISCV64.abi,
          RISCV64.argRegs]
        show match sg s.mem (s.gpr .a1) (s.gpr .a2) (s.gpr .a3) with
          | some rs => BitVec.setWidth 32 (s'.gpr .a0) = 1 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) 64 =
              Spec.Ecdsa.encode W rs
          | none => BitVec.setWidth 32 (s'.gpr .a0) = 0 ∧
            Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) 64 = List.replicate 64 0
        have h' : match sg s.mem (s.gpr .a1) (s.gpr .a2) (s.gpr .a3) with
            | some rs => s'.gpr .a0 = 1 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) 64 = Spec.Ecdsa.encode W rs
            | none => s'.gpr .a0 = 0 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) 64 = List.replicate 64 0 := h
        revert h'
        generalize sg s.mem (s.gpr .a1) (s.gpr .a2) (s.gpr .a3) = q
        rcases q with _ | rs <;> exact fun h => ⟨by rw [h.1]; rfl, h.2⟩
      pub := by
        sig_implies_pub [Spec.Ecdsa.P256.inst, Proof.Ecdsa.Instance.signContract,
          Proof.Ecdsa.Instance.signSig, Spec.P256.curve, Spec.Ecdsa.scratchWords, signRV, sg, RISCV64.abi,
          RISCV64.argRegs]
      sat := by
        sig_implies_sat [Spec.Ecdsa.P256.inst, Proof.Ecdsa.Instance.signContract,
          Proof.Ecdsa.Instance.signSig, Spec.P256.curve, Spec.Ecdsa.scratchWords, signRV, sg, RISCV64.abi,
          RISCV64.argRegs] [signSat] using signSat }

/-- A state satisfying the precondition with the table. -/
def signSatC : State :=
  { signSat with mem := Comb.combSatMem, rd := signSat.rd ++ [⟨0x100000, 151552⟩], syms := fun _ => 0x100000 }

theorem sign_sat : (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.P256.inst
    (RISCV64.abi.withConsts Impl.Ecdsa.RISCV64.Comb.p256CombConsts)).pre signSatC := by
  have hl := Comb.combWords_length
  have held := Comb.combSatMem_held
  rw [show Impl.Ecdsa.RISCV64.Comb.p256CombConsts = [(Impl.Ecdsa.RISCV64.Comb.p256Sym,
    Impl.Ecdsa.RISCV64.Comb.p256CombWords)] from rfl]
  generalize Impl.Ecdsa.RISCV64.Comb.p256CombWords = W' at hl held ⊢
  generalize e : signSatC = s
  sig_pre [Spec.Ecdsa.P256.inst, Proof.Ecdsa.Instance.signContract, Proof.Ecdsa.Instance.signSig, Spec.P256.curve,
    Spec.Ecdsa.scratchWords, RISCV64.abi, RISCV64.argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
    stackBelow]
  subst e
  rw [hl]
  refine ⟨by decide, rfl, fun i hi => held i (by rw [hl]; exact hi), by decide, fun r hr => ?_, by decide, rfl, rfl,
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), by decide, by decide, by decide, by decide, by decide, by decide⟩
  change r ∈ [⟨0x1000, 64⟩, ⟨0x8000, 8192⟩] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)

theorem signRVC_implies :
    signRVC.Implies (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.P256.inst
      (RISCV64.abi.withConsts Impl.Ecdsa.RISCV64.Comb.p256CombConsts)) :=
  { pre := fun _ hs => ⟨signRV_implies.pre _ (pre_consts.mp hs).1, (pre_consts.mp hs).2⟩
    post := fun s s' hs hp => post_consts.mpr (signRV_implies.post (stripConsts _ s) s'
      (pre_consts.mp hs).1 hp)
    pub := fun s₁ s₂ h₁ h₂ hp => ⟨signRV_implies.pub (stripConsts _ s₁) (stripConsts _ s₂)
        (pre_consts.mp h₁).1 (pre_consts.mp h₂).1 (pub_consts.mp hp).1,
      (pub_consts.mp hp).2 _ List.mem_cons_self⟩
    sat := ⟨signSatC, sign_sat⟩ }

theorem sign_verified (hL : VG.Proof.Weierstrass.Law W) :
    Verified RISCV64.target signP256 (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.P256.inst
      (RISCV64.abi.withConsts Impl.Ecdsa.RISCV64.Comb.p256CombConsts)) :=
  Verified.of_correct (sign_rv hL) sign_ct signRVC_implies

end VG.Proof.Ecdsa.RISCV64.P256
