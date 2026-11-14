module

public import VerifiedGarbage.Proof.Bignum.AArch64.PrivPreCT
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit

/-!
# `vg_rsa_private_precompute` on AArch64: verified against the shared contract

`ppA` states the shared contract on the registers and the stack
(`pp_implies`); with correctness (`ppCode_correct`) and constant time
(`ppCode_constantTime`), `PrivPre.code` is verified (`privPre_verified`).
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.PrivPre

open VG VG.AArch64

theorem stackArgs_two (s : State) : List.map (stackArg s) (List.range 2) = [stackArg s 0, stackArg s 1] := rfl

/-- A state meeting `ppA.pre`: a 64-byte modulus, one-byte primes, `pre`
at `0x1000`, the working space at `0x20000` and the stack arguments at
`0x10000`. -/
def ppSatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 20 | .x2 => 0x2000 | .x3 => 64 | .x4 => 0x3000 | .x5 => 1 | .x6 => 0x3100
    | .x7 => 1 | _ => 0
  sp := 0x10000
  mem a := if a = 0x10002 then 0x02 else if a = 0x10008 then 0x20 else if a = 0x10009 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x3100, 1⟩, ⟨0x10000, 16⟩]
  wr := [⟨0x1000, 160⟩, ⟨0x20000, 8448⟩]

theorem pp_implies : ppA.Implies (Spec.Rsa.privatePrecomputeContract abi) where
  pre := by
    intro s h
    sig_pre [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs, ppA, stackArgs_two,
      List.append_eq] at h
    sig_pre [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs, ppA, stackArgs_two,
      List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs, ppA, stackArgs_two,
      List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by
    sig_implies_post [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs, ppA,
      stackArgs_two, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs, ppA, stackArgs_two,
      List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1⟩ := h
    refine ⟨?_, hsp, a0, a1, (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hl⟩
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  sat := by
    sig_implies_sat [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs, ppA,
      stackArgs_two, List.append_eq] [ppSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using ppSatState

/-- `vg_rsa_private_precompute` with Montgomery multiplication `M`. -/
theorem privPre_verified (M : Mont) :
    Verified target (VG.Impl.Rsa.AArch64.PrivPre.code M.mm) (Spec.Rsa.privatePrecomputeContract abi) :=
  Verified.of_correct (ppCode_correct M) (ppCode_constantTime M) pp_implies

end VG.Proof.Bignum.AArch64.PrivPre
