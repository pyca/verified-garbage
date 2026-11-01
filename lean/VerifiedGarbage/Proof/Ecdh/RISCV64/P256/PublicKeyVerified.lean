module

public import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.PublicKey
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
public import VerifiedGarbage.Spec.EcKey.P256
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.EcdhLit
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.PublicKey
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
meta import VerifiedGarbage.Spec.EcKey.P256
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.EcdhLit
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# P-256's public keys on RISC-V: `Verified`

`pk_rv` with the function's constant time, by taint tracking (only the
pointers, in `a0`–`a2`, and the comb's table's address public), under
`abi.withConsts` of the comb's table (`pkRVC_implies`, from `pkRV_implies`).
-/

@[expose] public section

namespace VG.Proof.Ecdh.RISCV64.P256

open VG VG.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Proof.Ecdsa.RISCV64.P256

theorem pk_ct : ConstantTime isa pkRVC.pre pkRVC.pub publicKeyP256 :=
  VG.Taint.constantTime (A := taintSym [Impl.Ecdsa.RISCV64.Comb.p256Sym]) (Taint.ofRegs [.a0, .a1, .a2])
    (fun _ _ _ _ ⟨⟨hsp, h0, h1, h2⟩, hsy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2⟩, fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩) (by taint_decide)

/-- A state satisfying the precondition. -/
def pkSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x8000 | _ => 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x2000, 32⟩]
  wr := [⟨0x1000, 65⟩, ⟨0x8000, 8192⟩]

theorem pkRV_implies : pkRV.Implies (Spec.EcKey.P256.inst.publicKeyContract RISCV64.abi) :=
    { pre := by
        sig_implies_pre [Spec.EcKey.P256.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.P256.curve, Spec.EcKey.scratchWords, pkRV, pk, RISCV64.abi,
          RISCV64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.EcKey.P256.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.P256.curve, Spec.EcKey.scratchWords, pkRV, pk, RISCV64.abi,
          RISCV64.argRegs]
        have h' : match pk s.mem (s.gpr .a1) with
            | some (.affine x y) => s'.gpr .a0 = 1 ∧
                Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) 65 = Spec.EcKey.encodePoint (.affine x y)
            | _ => s'.gpr .a0 = 0 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) 65 = List.replicate 65 0 := h
        generalize hq : Spec.EcKey.publicKey _ _ = q
        have hq' : pk s.mem (s.gpr .a1) = q := hq
        rw [hq'] at h'
        rcases q with _ | _ | ⟨x, y⟩
        · exact ⟨by rw [h'.1]; rfl, h'.2⟩
        · exact ⟨by rw [h'.1]; rfl, h'.2⟩
        · exact ⟨by rw [h'.1]; rfl, h'.2⟩
      pub := by
        sig_implies_pub [Spec.EcKey.P256.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.P256.curve, Spec.EcKey.scratchWords, pkRV, pk, RISCV64.abi,
          RISCV64.argRegs]
      sat := by
        sig_implies_sat [Spec.EcKey.P256.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.P256.curve, Spec.EcKey.scratchWords, pkRV, pk, RISCV64.abi,
          RISCV64.argRegs] [pkSat] using pkSat }

/-- A state satisfying the precondition with the table. -/
def pkSatC : State :=
  { pkSat with mem := VG.Proof.Ecdsa.RISCV64.Comb.combSatMem, rd := pkSat.rd ++ [⟨0x100000, 151552⟩], syms := fun _ => 0x100000 }

theorem pk_sat : (Spec.EcKey.P256.inst.publicKeyContract
    (RISCV64.abi.withConsts Impl.Ecdsa.RISCV64.Comb.p256CombConsts)).pre pkSatC := by
  have hl := VG.Proof.Ecdsa.RISCV64.Comb.combWords_length
  have held := VG.Proof.Ecdsa.RISCV64.Comb.combSatMem_held
  rw [show Impl.Ecdsa.RISCV64.Comb.p256CombConsts = [(Impl.Ecdsa.RISCV64.Comb.p256Sym,
    Impl.Ecdsa.RISCV64.Comb.p256CombWords)] from rfl]
  generalize Impl.Ecdsa.RISCV64.Comb.p256CombWords = W' at hl held ⊢
  generalize e : pkSatC = s
  sig_pre [Spec.EcKey.P256.inst, Spec.EcKey.Instance.publicKeyContract, Spec.EcKey.Instance.publicKeySig,
    Spec.P256.curve, Spec.EcKey.scratchWords, RISCV64.abi, RISCV64.argRegs, Abi.withConsts, Abi.constRegions,
    Abi.constsHeld, stackBelow]
  subst e
  rw [hl]
  refine ⟨by decide, rfl, fun i hi => held i (by rw [hl]; exact hi), by decide, fun r hr => ?_, by decide, rfl, rfl,
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    by decide, by decide, by decide, by decide⟩
  change r ∈ [⟨0x1000, 65⟩, ⟨0x8000, 8192⟩] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)

theorem pkRVC_implies :
    pkRVC.Implies (Spec.EcKey.P256.inst.publicKeyContract
      (RISCV64.abi.withConsts Impl.Ecdsa.RISCV64.Comb.p256CombConsts)) :=
  { pre := fun _ hs => ⟨pkRV_implies.pre _ (pre_consts.mp hs).1, (pre_consts.mp hs).2⟩
    post := fun s s' hs hp => post_consts.mpr (pkRV_implies.post (stripConsts _ s) s'
      (pre_consts.mp hs).1 hp)
    pub := fun s₁ s₂ h₁ h₂ hp => ⟨pkRV_implies.pub (stripConsts _ s₁) (stripConsts _ s₂)
        (pre_consts.mp h₁).1 (pre_consts.mp h₂).1 (pub_consts.mp hp).1,
      (pub_consts.mp hp).2 _ List.mem_cons_self⟩
    sat := ⟨pkSatC, pk_sat⟩ }

theorem pk_verified (hL : VG.Proof.Weierstrass.Law W) :
    Verified RISCV64.target publicKeyP256 (Spec.EcKey.P256.inst.publicKeyContract
      (RISCV64.abi.withConsts Impl.Ecdsa.RISCV64.Comb.p256CombConsts)) :=
  Verified.of_correct (pk_rv hL) pk_ct pkRVC_implies

end VG.Proof.Ecdh.RISCV64.P256
