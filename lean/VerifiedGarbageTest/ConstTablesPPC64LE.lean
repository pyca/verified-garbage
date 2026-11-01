module

import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
meta import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Sig

/-!
# Tables of constants on PPC64LE (`Artifact.consts`)

As `ConstTables.lean` for AArch64: a function `() -> u64` that returns word
1 of a table of constants: `mflr r0` (`adrSym` writes the link register,
which the function must preserve), `adrSym` of the table's `static`, `ld r3,
8(r3)`, then `mtlr r0`, proven against the contract of its signature under
`abi.withConsts`. The proof steps over `adrSym` with `exec_adrSym` and takes
what the contract says of the table from `pre_consts` and `ConstsOk`
(readable, its words). Its constant time is `taintSym`'s, which sees the
table's address as public.
-/

namespace VG.Test.ConstTablesPPC64LE
open VG VG.PPC64LE

def sig : Sig := { params := [], ret := some .u64 }
def tbl : List (BitVec 64) := [7, 42]
def consts : List (String × List (BitVec 64)) := [("VG_TEST_TABLE", tbl)]

def contract : Contract isa :=
  sig.contract (abi.withConsts consts) (post := fun m m' r => r = 42 ∧ m' = m)

def instrs : List Instr := [.mflr .r0, .adrSym .r3 "VG_TEST_TABLE", .load .d .r3 .r3 8, .mtlr .r0]

def code : Prog isa := .block instrs

theorem mem_consts : ("VG_TEST_TABLE", tbl) ∈ consts := List.mem_singleton_self _

/-- The state after the code. -/
def final (s : State) : State :=
  { (s.write .r0 s.lr).write .r3 42 with lr := s.lr, unknowns := fun n => s.unknowns (n + 1) }

theorem exec_code {s : State} (h : contract.pre s) :
    execBlock isa instrs s = some (final s, [Leak.addr (s.syms "VG_TEST_TABLE" + BitVec.ofNat 64 8)]) := by
  have hk : ConstsOk consts 0 s := (pre_consts.mp h).2
  have h42 : s.mem.readW (s.syms "VG_TEST_TABLE" + BitVec.ofNat 64 8) 64 = 42 :=
    hk.readW mem_consts (i := 1) (by decide)
  have hin : InRegions (s.rd ++ s.wr) (s.syms "VG_TEST_TABLE" + BitVec.ofNat 64 8) 8 :=
    hk.inRegions mem_consts (x := 8) (by decide) (by decide) _
  simp only [instrs, execBlock, isa, exec_mflr, exec_adrSym (show Reg.r3 ≠ .r0 by decide)]
  rw [exec_load_d (by decide) (by decide) (by simpa [State.write] using hin)]
  simp [State.write, h42, exec_mtlr, addrs, final]
  funext r; by_cases hr : r = .r3 <;> simp [hr]

/-- A state satisfying the precondition: the table at `0x1000`. -/
def sat : State where
  gpr _ := 0
  lr := 0
  sp := 0x10000
  mem a := if a = 0x1000 then 7 else if a = 0x1008 then 42 else 0
  rd := [⟨0x1000, 16⟩]
  wr := []
  unknowns _ := 0
  syms _ := 0x1000

theorem constantTime : ConstantTime isa contract.pre contract.pub code :=
  VG.Taint.constantTime (A := taintSym ["VG_TEST_TABLE"]) (Taint.ofRegs [])
    (fun s₁ s₂ _ _ hp => ⟨⟨(pub_consts.mp hp).1.1, fun r hr => absurd (Taint.mem_ofRegs.mp hr) (by simp)⟩,
      fun n hn => by
        simp only [List.mem_singleton] at hn; subst hn
        exact (pub_consts.mp hp).2 _ mem_consts⟩)
    (by taint_decide)

theorem verified : Verified target code contract := by
  refine ⟨fun s h => ⟨_, _, .block (exec_code h), ?_, ?_⟩, constantTime, ?_⟩
  · refine ⟨fun r hr => ?_, rfl, rfl⟩
    have h3 : r ≠ .r3 := fun e => by subst e; exact absurd hr (by decide)
    have h0 : r ≠ .r0 := fun e => by subst e; exact absurd hr (by decide)
    simp [final, State.write, h3, h0]
  · sig_post [contract, sig, consts, Abi.withConsts, abi, argRegs, final, State.write]
  · refine ⟨sat, ?_⟩
    sig_pre [contract, sig, consts, Abi.withConsts, Abi.constRegions, Abi.constsHeld, abi, argRegs,
      stackBelow, tbl, sat]
    exact ⟨by decide, by decide⟩

end VG.Test.ConstTablesPPC64LE
