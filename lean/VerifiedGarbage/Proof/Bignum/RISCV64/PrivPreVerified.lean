module

public import VerifiedGarbage.Proof.Bignum.RISCV64.PrivPreE
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Rsa.PrivatePrecompute
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Bignum.RISCV64.PrivPreCTB
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.Flat
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PrivPreCTB
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.Flat
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! ### `Bignum.RISCV64.PrivPreCT`, which only this module used -/

section

/-!
# An RSA private key's precomputed values on RISC-V: constant time

The code's list of programs (`privF`) is cut after each block that loads
values of the header (`PrivPreCTA.lean`, `PrivPreCTB.lean`): there the
registers the taint analysis needs public have values that the public data
fixes. `Precompute.core`, whose branches are on `n`, is
`vg_rsa_public_precompute`'s (`Pre.core_rel`), from `Pre.C1` for data the
public data fixes.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.PrivPre

open VG VG.RISCV64 VG.RISCV64.Taint VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Bignum.RISCV64.Crt
open VG.Proof.Bignum.RISCV64.Pre (Two two_post two_taint)
open VG.Proof.Bignum.RISCV64 (At seg chain_cons chain_start at_zero_inv)

/-- The first block, the registers saved and the arguments stored, by the
taint analysis from the stack's first argument once loaded. -/
theorem front_rel : RelCT isa (Two C0) (.block (PrivPre.save ++ PrivPre.args)) fun _ _ => True := by
  unfold PrivPre.save
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine RelCT.block_append (M := isa) (l₁ := ([.addSp .t0 0, .load .d .t0 .t0 0] : List Instr)) ?_
  exact RelCT.seq (two_post (two_taint _ pins_C0 (by taint_decide)) fun _ _ h => loadS_L1 h)
    (two_taint _ pins_L1 (by taint_decide))

theorem priv_run (d : PDat) (s : State) (h : C0 d s) : WP isa (Code.seqL privF) s fun _ => True :=
  let ⟨tr, t, e, _⟩ := fn_correct s h.1
  ⟨tr, t, exec_flat.mp e, trivial⟩

theorem relCT_to_flat {P Q : State → State → Prop} {c : Prog isa} (h : RelCT isa P c Q) :
    RelCT isa P (Code.seqL c.flat) Q :=
  fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ _ _ _ _ hp (exec_flat.mpr e₁) (exec_flat.mpr e₂)

/-- `Precompute.core`, as `vg_rsa_public_precompute`'s. -/
theorem core_seg : RelCT isa (Two (At C0 privF 97)) (seg privF 97 107) fun _ _ => True := by
  rw [show seg privF 97 107 = Code.seqL (Code.flat Precompute.core) from rfl]
  refine RelCT.mono (relCT_to_flat Pre.core_rel) (fun s₁ s₂ ⟨d, h₁, h₂, hsp⟩ => ?_) fun _ _ _ => trivial
  obtain ⟨s₀, c0, c1⟩ := at_C1 h₁
  obtain ⟨s₀', c0', c1'⟩ := at_C1 h₂
  exact ⟨pdOf s₀, c1, by rw [pdOf_eq c0 c0']; exact c1', hsp⟩

theorem fn_rel : RelCT isa (Two C0) PrivPre.code fun _ _ => True := by
  refine chain_start (chain_cons priv_run (m := 1) (by decide) ?_ ?_)
  · exact RelCT.mono (P := Two C0)
      (VG.Proof.Bignum.RISCV64.RelCT.seqL_single front_rel)
      (fun _ _ ⟨a, h₁, h₂, hsp⟩ => ⟨a, at_zero_inv h₁, at_zero_inv h₂, hsp⟩) fun _ _ h => h
  refine chain_cons priv_run (m := 5) (by decide) (two_taint _ pins1 (by taint_decide)) ?_
  refine chain_cons priv_run (m := 9) (by decide) (two_taint _ pins5 (by taint_decide)) ?_
  refine chain_cons priv_run (m := 17) (by decide) (two_taint _ pins9 (by taint_decide)) ?_
  refine chain_cons priv_run (m := 25) (by decide) (two_taint _ pins17 (by taint_decide)) ?_
  refine chain_cons priv_run (m := 33) (by decide) (two_taint _ pins25 (by taint_decide)) ?_
  refine chain_cons priv_run (m := 41) (by decide) (two_taint _ pins33 (by taint_decide)) ?_
  refine chain_cons priv_run (m := 50) (by decide) (two_taint _ pins41 (by taint_decide)) ?_
  refine chain_cons priv_run (m := 51) (by decide) (two_taint _ pins50 (by taint_decide)) ?_
  refine chain_cons priv_run (m := 97) (by decide) (two_taint _ pins51 (by taint_decide)) ?_
  refine chain_cons priv_run (m := 107) (by decide) core_seg ?_
  refine chain_cons priv_run (m := 114) (by decide) (two_taint _ pins107 (by taint_decide)) ?_
  refine chain_cons priv_run (m := 150) (by decide) (two_taint _ pins114 (by taint_decide)) ?_
  refine chain_cons priv_run (m := 153) (by decide) (two_taint _ pins150 (by taint_decide)) ?_
  refine chain_cons priv_run (m := 189) (by decide) (two_taint _ pins153 (by taint_decide)) ?_
  refine chain_cons priv_run (m := 192) (by decide) (two_taint _ pins189 (by taint_decide)) ?_
  exact two_taint _ pins192 (by taint_decide)

theorem fn_ct : ConstantTime isa fnContract.pre fnContract.pub PrivPre.code :=
  RelCT.constantTime (fn_rel.mono (fun s t ⟨hs, ht, ⟨hr, hsp, ha, hn⟩⟩ =>
    ⟨dataOf s, ⟨hs, rfl⟩, ⟨ht, by
      simp only [dataOf]
      rw [List.map_congr_left fun r h => (hr r h).symm, ha, hn]⟩, hsp⟩) fun _ _ h => h)

end VG.Proof.Bignum.RISCV64.PrivPre

end

end

/-!
# `vg_rsa_private_precompute` on RISC-V: verified against the shared contract

`fnContract` states the shared contract on the registers and the stack
(`pp_implies`); with correctness (`fn_correct`) and constant time (`fn_ct`),
the code is verified (`pp_verified`).
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.PrivPre

open VG VG.RISCV64

/-- A state meeting `fnContract.pre`: a 512-bit modulus, one-byte factors,
`pre` at `0x1000`, and the stack arguments at `sp = 0x6000`: the working
space at `0x8000`, of 1056 words. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 20 | .a2 => 0x2000 | .a3 => 64 | .a4 => 0x3000 | .a5 => 1 | .a6 => 0x3100
    | .a7 => 1 | _ => 0
  sp := 0x6000
  mem a := if a = 0x6001 then 0x80 else if a = 0x6008 then 0x20 else if a = 0x6009 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x3100, 1⟩, ⟨0x6000, 16⟩]
  wr := [⟨0x1000, 160⟩, ⟨0x8000, 8448⟩]

theorem stackArgs_two (s : State) : List.map (stackArg s) (List.range 2) = [stackArg s 0, stackArg s 1] := rfl

theorem pp_implies : fnContract.Implies (Spec.Rsa.privatePrecomputeContract abi) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs, fnContract,
      stackArgs_two, List.append_eq] at h
    sig_pre [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs, fnContract,
      stackArgs_two, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs, fnContract,
      stackArgs_two, List.append_eq]
    sig_and_intros
    sig_close
    all_goals first | with_reducible assumption | omega
  post := by
    sig_implies_post [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs,
      fnContract, stackArgs_two, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs, fnContract,
      stackArgs_two, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, r0, r1, r2, r3, r4, r5, r6, r7, a0, a1⟩ := h
    refine ⟨?_, hsp, by rw [stackArgs_two, stackArgs_two, a0, a1],
      (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hl⟩
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩
  sat := by
    sig_implies_sat [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs,
      fnContract, stackArgs_two, List.append_eq] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using satState

/-- `vg_rsa_private_precompute`. -/
theorem pp_verified :
    Verified target VG.Impl.Bignum.RISCV64.PrivPre.code (Spec.Rsa.privatePrecomputeContract abi) :=
  Verified.of_correct fn_correct fn_ct pp_implies

end VG.Proof.Bignum.RISCV64.PrivPre
