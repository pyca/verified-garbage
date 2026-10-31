module

import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.ReadHalves
meta import VerifiedGarbage.Proof.Framework.ReadHalves
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Sig

/-!
# Tables of constants on ARMv7 (`Artifact.consts`)

As `ConstTables.lean` for AArch64: a function `() -> u32` that returns the
low word of word 1 of a table of constants, `adrSym` of the table's `static`
then `ldr r0, [r0, #8]`, proven against the contract of its signature under
`abi.withConsts`. The proof steps over `adrSym` with `exec_adrSym`, reads the
register through the write (`RegUpd`), and takes what the contract says of
the table from `pre_consts` and `ConstsOk` (readable, its words), in the
32-bit addresses the code forms.
-/

namespace VG.Test.ConstTablesArm
open VG VG.Arm

def sig : Sig := { params := [], ret := some .u32 }
def tbl : List (BitVec 64) := [7, 42]
def consts : List (String × List (BitVec 64)) := [("VG_TEST_TABLE", tbl)]

def contract : Contract isa :=
  sig.contract (abi.withConsts consts) (post := fun m m' r => r = 42 ∧ m' = m)

def code : Prog isa := .block [.adrSym .r0 "VG_TEST_TABLE", .ldr .r0 .r0 8]

theorem mem_consts : ("VG_TEST_TABLE", tbl) ∈ consts := List.mem_singleton_self _

/-- After `adrSym`, the register holds the static's address. -/
example (s : State) :
    ((exec (.adrSym .r4 "T") s).map fun s' => s'.gpr .r4) = some (s.syms "T") := by
  rw [exec_adrSym, Option.map_some, RegUpd.gpr_setReg_self]

theorem exec_code {s : State} (h : contract.pre s) :
    execBlock isa [.adrSym .r0 "VG_TEST_TABLE", .ldr .r0 .r0 8] s =
      some ((s.setReg .r0 (s.syms "VG_TEST_TABLE")).setReg .r0 42,
        [Leak.addr (State.addr (s.syms "VG_TEST_TABLE" + BitVec.ofNat 32 8))]) := by
  have hk : ConstsOk consts 0 s := (pre_consts.mp h).2
  have g : (s.setReg .r0 (s.syms "VG_TEST_TABLE")).gpr .r0 = s.syms "VG_TEST_TABLE" :=
    RegUpd.gpr_setReg_self s .r0 _
  have hin : InRegions ((s.setReg .r0 (s.syms "VG_TEST_TABLE")).rd ++
      (s.setReg .r0 (s.syms "VG_TEST_TABLE")).wr)
      (State.addr ((s.setReg .r0 (s.syms "VG_TEST_TABLE")).gpr .r0 + BitVec.ofNat 32 8)) 4 := by
    rw [RegUpd.rd_setReg, g]
    exact hk.inRegions mem_consts (by decide) (by decide) _
  have h64 := hk.readW mem_consts (i := 1) (by decide)
  have h42 : s.mem.readW (State.addr (s.syms "VG_TEST_TABLE" + BitVec.ofNat 32 8)) 32 = 42 :=
    (Mem.readW_lo32 h64).trans (by decide)
  have e₁ : exec (.adrSym .r0 "VG_TEST_TABLE") s = some (s.setReg .r0 (s.syms "VG_TEST_TABLE")) :=
    exec_adrSym
  have e₂ := exec_ldr (t := .r0) (by decide) hin
  rw [RegUpd.mem_setReg, g, h42] at e₂
  simp only [execBlock, isa, e₁, e₂, Option.map_some, addrs, List.map_cons, List.map_nil,
    List.nil_append, List.append_nil, g]

/-- A state satisfying the precondition: the table at `0x1000`. -/
def sat : State where
  gpr _ := 0
  sp := 0x10000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x1000 then 7 else if a = 0x1008 then 42 else 0
  rd := [⟨0x1000, 16⟩]
  wr := []
  syms _ := 0x1000

theorem verified : Verified target code contract := by
  refine ⟨fun s h => ⟨_, _, .block (exec_code h), ?_, ?_⟩,
    .of_leakage (fun s => [Leak.addr (State.addr (s.syms "VG_TEST_TABLE" + BitVec.ofNat 32 8))])
      (fun s t s' h e => by cases e with | block e => rw [exec_code h] at e; cases e; rfl)
      (fun s₁ s₂ _ _ hp => ?_), ?_⟩
  · exact ⟨fun r hr => by
      rw [RegUpd.gpr_setReg_of_ne _ _ (fun e => by subst e; exact absurd hr (by decide)),
        RegUpd.gpr_setReg_of_ne _ _ (fun e => by subst e; exact absurd hr (by decide))],
      rfl⟩
  · sig_post [contract, sig, consts, Abi.withConsts, abi, argRegs]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_append, decide_eq_true hi, Bool.true_and, ite_eq_left hi]
  · -- The table's address is public (`pub_consts`), in 32 bits (`symAddr_eq_iff`).
    have hsy := symAddr_eq_iff.mp ((pub_consts.mp hp).2 _ (List.mem_singleton_self ("VG_TEST_TABLE", tbl)))
    rw [hsy]
  · refine ⟨sat, ?_⟩
    sig_pre [contract, sig, consts, Abi.withConsts, Abi.constRegions, Abi.constsHeld, abi, argRegs,
      stackBelow, tbl, sat]
    exact ⟨by decide, by decide⟩

end VG.Test.ConstTablesArm
