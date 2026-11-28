module

-- separate module: the kernel's evaluation of verify's code (no instruction loads MXCSR or writes rsp), which the cleanup's module may not hold

public import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyTopCTTop
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyPkForsV
import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyPkXmssV
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Sig

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.VerifyTop

open VG VG.X86_64
open VG.Spec.SlhDsa

/-- A property of every instruction of `verify`, from those of `thash4` and
of its own code. -/
theorem verify_all {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} {gv : Impl.SlhDsa.X86_64.Verify.VFns}
    (P : Instr → Bool) (hT : ∀ i ∈ instrs f.t4, P i = true)
    (hB : ∀ i ∈ instrs (Impl.SlhDsa.X86_64.Verify.verify p { f with t4 := .block [] } gv), P i = true) :
    ∀ i ∈ instrs (Impl.SlhDsa.X86_64.Verify.verify p f gv), P i = true := by
  rw [← List.all_eq_true] at hT hB ⊢
  simp only [Impl.SlhDsa.X86_64.Verify.verify, Impl.SlhDsa.X86_64.Verify.verifyBody,
    Impl.SlhDsa.X86_64.Verify.layerBody, Impl.SlhDsa.X86_64.Verify.forsPk, Impl.SlhDsa.X86_64.Verify.forsGroup,
    Impl.SlhDsa.X86_64.Verify.forsLeaves, Impl.SlhDsa.X86_64.Verify.forsUp, Impl.SlhDsa.X86_64.Verify.forsUpLane,
    Impl.SlhDsa.X86_64.Fors.pkFors, Impl.SlhDsa.X86_64.Verify.xmssPk, Impl.SlhDsa.X86_64.Verify.chainGroup,
    Impl.SlhDsa.X86_64.Verify.stepBody, Impl.SlhDsa.X86_64.Verify.wotsPk, Impl.SlhDsa.X86_64.Verify.pathBody,
    Impl.SlhDsa.X86_64.thashCall, instrs, List.all_append, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true] at hB ⊢
  simp only [hT, and_true]
  exact hB

/-- `Code.all` of `verify`, from `thash4`'s and its own code's. -/
theorem verify_codeAll {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} {gv : Impl.SlhDsa.X86_64.Verify.VFns}
    (P : Instr → Bool) (hT : f.t4.all P = true)
    (hB : (Impl.SlhDsa.X86_64.Verify.verify p { f with t4 := .block [] } gv).all P = true) :
    (Impl.SlhDsa.X86_64.Verify.verify p f gv).all P = true := by
  simp only [Impl.SlhDsa.X86_64.Verify.verify, Impl.SlhDsa.X86_64.Verify.verifyBody,
    Impl.SlhDsa.X86_64.Verify.layerBody, Impl.SlhDsa.X86_64.Verify.forsPk, Impl.SlhDsa.X86_64.Verify.forsGroup,
    Impl.SlhDsa.X86_64.Verify.forsLeaves, Impl.SlhDsa.X86_64.Verify.forsUp, Impl.SlhDsa.X86_64.Verify.forsUpLane,
    Impl.SlhDsa.X86_64.Fors.pkFors, Impl.SlhDsa.X86_64.Verify.xmssPk, Impl.SlhDsa.X86_64.Verify.chainGroup,
    Impl.SlhDsa.X86_64.Verify.stepBody, Impl.SlhDsa.X86_64.Verify.wotsPk, Impl.SlhDsa.X86_64.Verify.pathBody,
    Impl.SlhDsa.X86_64.thashCall, Code.all, List.all_nil, Bool.and_true, Bool.and_eq_true] at hB ⊢
  simp only [hT, and_true]
  exact hB

section
variable {p : Params} (hS : S6 p) {f : Impl.SlhDsa.X86_64.Shake.Fns} {gv : Impl.SlhDsa.X86_64.Verify.VFns}
include hS

theorem fors_own_nm :
    ∀ i ∈ instrs (Impl.SlhDsa.X86_64.Verify.forsPk p { f with t4 := .block [] }), (!loadsMxcsr i) = true := by
  apply List.all_eq_true.mp
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl <;> kernel_rfl

theorem fors_own_sp :
    ∀ i ∈ instrs (Impl.SlhDsa.X86_64.Verify.forsPk p { f with t4 := .block [] }), (!Taint.clobbers i .rsp) = true := by
  apply List.all_eq_true.mp
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl <;> kernel_rfl

theorem verify_own_nm :
    ∀ i ∈ instrs (Impl.SlhDsa.X86_64.Verify.verify p { f with t4 := .block [] } gv), (!loadsMxcsr i) = true := by
  apply List.all_eq_true.mp
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl <;> kernel_rfl

/-- No instruction of `verify`'s own code writes `rsp`, but as the push and pop of its frame. -/
theorem verify_own_wsp :
    (Impl.SlhDsa.X86_64.Verify.verify p { f with t4 := .block [] } gv).all (fun i => !isa.writesSp i) = true := by
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl <;> kernel_rfl

end

/-! ## The code's facts over any `thash4` -/

section
variable {p : Params} (hS : S6 p) {f : Impl.SlhDsa.X86_64.Shake.Fns} (T : Thash4Impl p.n) (ht : f.t4 = T.code)
include hS ht

theorem forsPk_nm_of : (Impl.SlhDsa.X86_64.Verify.forsPk p f).allInstrs (fun i => !loadsMxcsr i) = true :=
  forsPk_nm (by rw [ht]; exact T.nomx) (fors_own_nm hS)

theorem forsPk_sp_of : NoSp (Impl.SlhDsa.X86_64.Verify.forsPk p f) :=
  forsPk_nosp (by rw [ht]; exact T.nosp) (fors_own_sp hS)

theorem verify_nm (gv : Impl.SlhDsa.X86_64.Verify.VFns) :
    (Impl.SlhDsa.X86_64.Verify.verify p f gv).allInstrs (fun i => !loadsMxcsr i) = true := by
  have h := T.nomx
  rw [Code.allInstrs_eq, List.all_eq_true] at h ⊢
  exact verify_all _ (by rw [ht]; exact h) (verify_own_nm hS)

end

/-! ## The contract -/

/-- A state of `verifyContract`'s precondition. -/
def vSat (p : Params) : State where
  gpr r := match r with
    | .rdi => 0x10000 | .rsi => 0x20000 | .rcx => 0x30000 | .r9 => 0x40000
    | .rsp => BitVec.ofNat 64 (2 ^ 64 - 32)
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x10000, p.pkLen⟩, ⟨0x20000, 0⟩, ⟨0x30000, 0⟩, ⟨0x40000, 0⟩, ⟨BitVec.ofNat 64 (2 ^ 64 - 24), 16⟩]
  wr := [⟨0, scratchWords * 8⟩]

theorem vSat_pre {p : Params} (hS : S6 p) {st : Nat} (hst62 : st < 2 ^ 62) :
    (verifyContract p X86_64.abi (st + 80)).pre (vSat p) := by
  have hpk : p.pkLen ≤ 64 := by rcases hS with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have g1 : (vSat p).gpr .rdi = 0x10000 := rfl
  have g2 : (vSat p).gpr .rsi = 0x20000 := rfl
  have g3 : (vSat p).gpr .rdx = 0 := rfl
  have g4 : (vSat p).gpr .rcx = 0x30000 := rfl
  have g5 : (vSat p).gpr .r8 = 0 := rfl
  have g6 : (vSat p).gpr .r9 = 0x40000 := rfl
  have g7 : (vSat p).gpr .rsp = BitVec.ofNat 64 (2 ^ 64 - 32) := rfl
  have aa : stackArgAddr (vSat p) 0 = BitVec.ofNat 64 (2 ^ 64 - 24) := rfl
  have a0 : stackArg (vSat p) 0 = 0 := by
    rw [stackArg, aa]; exact (by decide : Mem.readW (fun _ => 0) (BitVec.ofNat 64 (2 ^ 64 - 24)) 64 = 0)
  have a1 : stackArg (vSat p) 1 = 0 := by
    rw [stackArg, show stackArgAddr (vSat p) 1 = BitVec.ofNat 64 (2 ^ 64 - 16) from rfl]
    exact (by decide : Mem.readW (fun _ => 0) (BitVec.ofNat 64 (2 ^ 64 - 16)) 64 = 0)
  have hr : (vSat p).rd = [⟨0x10000, p.pkLen⟩, ⟨0x20000, 0⟩, ⟨0x30000, 0⟩, ⟨0x40000, 0⟩,
      ⟨BitVec.ofNat 64 (2 ^ 64 - 24), 16⟩] := rfl
  have hw : (vSat p).wr = [⟨0, scratchWords * 8⟩] := rfl
  have e5 : (BitVec.ofNat 64 (2 ^ 64 - 32)).toNat = 2 ^ 64 - 32 := rfl
  have e6 : (BitVec.ofNat 64 (2 ^ 64 - 32) - BitVec.ofNat 64 (st + 80)).toNat = 2 ^ 64 - 32 - (st + 80) := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, e5, BitVec.toNat_ofNat]; omega), e5, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
  have hsw : scratchWords * 8 = 65536 := rfl
  have n0 : (0 : Addr).toNat = 0 := rfl
  have n1 : (0x10000 : Addr).toNat = 0x10000 := rfl
  have n2 : (0x20000 : Addr).toNat = 0x20000 := rfl
  have n3 : (0x30000 : Addr).toNat = 0x30000 := rfl
  have n4 : (0x40000 : Addr).toNat = 0x40000 := rfl
  have n5 : (BitVec.ofNat 64 (2 ^ 64 - 24)).toNat = 2 ^ 64 - 24 := rfl
  rw [show st + 80 = (st + 79) + 1 from rfl]
  sig_pre [verifyContract, verifySig, X86_64.abi, X86_64.argRegs, List.range, List.range.loop]
  simp only [a0, a1, aa, hsw, show st + 79 + 1 = st + 80 from rfl]
  simp only [n0, n1, n2, n3, n4, e5]
  sig_and_intros
  all_goals first
    | exact True.intro
    | omega
    | (apply Offset.disjoint_of_le <;> dsimp only <;> simp only [n0, n1, n2, n3, n4, n5, e5, e6] <;> omega)
    | (apply Region.Disjoint.symm; apply Offset.disjoint_of_le <;> dsimp only <;>
        simp only [n0, n1, n2, n3, n4, e5, e6] <;> omega)

/-! ## `Verified` -/

/-- `vg_slhdsa_shake_*_verify` for a SHAKE parameter set `p` and any
implementation `T` of `thash4`, whose calls take `st` bytes of stack, meets
`verifyContract` in constant time. -/
theorem verify_verified {p : Params} (hS : S6 p) {f : Impl.SlhDsa.X86_64.Shake.Fns} (T : Thash4Impl p.n)
    (ht : f.t4 = T.code) (gv : Impl.SlhDsa.X86_64.Verify.VFns) {st : Nat} (hst : T.stack + 16 ≤ st)
    (hst62 : st < 2 ^ 62) :
    Verified X86_64.target (Impl.SlhDsa.X86_64.Verify.verify p f gv) (verifyContract p X86_64.abi (st + 80)) := by
  have hp := hS.par
  have hmx := forsPk_nm_of hS T ht
  have hsp := forsPk_sp_of hS T ht
  refine ⟨fun s h => ?_, verify_ct hS T ht hmx hsp gv hst hst62, ⟨vSat p, vSat_pre hS hst62⟩⟩
  obtain ⟨t, s', e, gp, hr⟩ := verify_wp T ht hp hmx hsp gv hst hst62 (vPre_of h)
  refine ⟨t, s', e, abiPreserved_of_exec (verify_nm hS T ht gv) e gp, ?_⟩
  rw [show st + 80 = (st + 79) + 1 from rfl]
  sig_post [verifyContract, verifySig, X86_64.abi, X86_64.argRegs, List.range, List.range.loop]
  exact hr

end VG.Proof.SlhDsa.X86_64.VerifyTop
