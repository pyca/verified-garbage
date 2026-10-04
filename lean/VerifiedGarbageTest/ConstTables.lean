import VerifiedGarbage.TCB.Rust
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-!
# Tables of constants (`Artifact.consts`)

A function `() -> u64` that returns word 1 of a table of constants: its code,
`adrp`/`add` of the table's `static` (`adrSym`) then `ldr x0, [x0, #8]`, is
proven against the contract of its signature under `abi.withConsts`
(the table's address `State.syms "VG_TEST_TABLE"`, where the memory holds
it), and the emitter renders the code with the static's symbol, in the syntax
of the object format, and the table as the `static`.
-/

namespace VG.Test.ConstTables
open VG VG.AArch64

def sig : Sig := { params := [], ret := some .u64 }
def tbl : List (BitVec 64) := [7, 42]
def consts : List (String × List (BitVec 64)) := [("VG_TEST_TABLE", tbl)]

def contract : Contract isa :=
  sig.contract (abi.withConsts consts) (post := fun m m' r => r = 42 ∧ m' = m)

def code : Prog isa := .block [.adrSym .x0 "VG_TEST_TABLE", .ldr .x .x0 .x0 8]

/-- What the contract says of the entry state: the table is the only region,
at the static's address, holding `tbl`. -/
theorem pre_facts {s : State} (h : contract.pre s) :
    s.rd = [⟨s.syms "VG_TEST_TABLE", 16⟩] ∧ s.wr = [] ∧
      s.mem.readW (s.syms "VG_TEST_TABLE" + BitVec.ofNat 64 8) 64 = 42 := by
  sig_pre [contract, sig, consts, Abi.withConsts, Abi.constRegions, Abi.constsHeld, abi, argRegs,
    stackBelow, tbl] at h
  obtain ⟨hd, hheld, -, -, ht, hw⟩ := h
  refine ⟨?_, hw, hheld 1 (by decide)⟩
  rw [← List.take_append_drop (s.rd.length - 1) s.rd, hd, ht]; rfl

theorem exec_code {s : State} (h : contract.pre s) :
    execBlock isa [.adrSym .x0 "VG_TEST_TABLE", .ldr .x .x0 .x0 8] s =
      some ((s.write .x .x0 (s.syms "VG_TEST_TABLE")).write .x .x0 42,
        [Leak.addr (s.syms "VG_TEST_TABLE" + BitVec.ofNat 64 8)]) := by
  obtain ⟨hrd, -, h42⟩ := pre_facts h
  have g : (s.write .x .x0 (s.syms "VG_TEST_TABLE")).gpr .x0 = s.syms "VG_TEST_TABLE" :=
    RegUpd.gpr_write_self s .x .x0 _
  have hin : InRegions ((s.write .x .x0 (s.syms "VG_TEST_TABLE")).rd ++
      (s.write .x .x0 (s.syms "VG_TEST_TABLE")).wr)
      ((s.write .x .x0 (s.syms "VG_TEST_TABLE")).gpr .x0 + BitVec.ofNat 64 8) 8 :=
    ⟨_, by rw [RegUpd.rd_write, hrd]; exact List.mem_append_left _ (List.mem_singleton_self _), by
      rw [g]
      show ((s.syms "VG_TEST_TABLE" + BitVec.ofNat 64 8) - s.syms "VG_TEST_TABLE").toNat + 8 ≤ 16
      rw [BitVec.add_comm, BitVec.add_sub_cancel]; decide⟩
  have e₁ : AArch64.exec (.adrSym .x0 "VG_TEST_TABLE") s = some (s.write .x .x0 (s.syms "VG_TEST_TABLE")) :=
    exec_adrSym
  have e₂ := exec_ldr_x (t := .x0) (by decide) hin
  rw [RegUpd.mem_write, g, h42] at e₂
  simp only [execBlock, isa, e₁, e₂, Option.map_some, addrs, List.map_cons, List.map_nil,
    List.nil_append, List.append_nil, g]

/-- A state satisfying the precondition: the table at `0x1000`. -/
def sat : State where
  gpr _ := 0
  sp := 0x10000
  mem a := if a = 0x1000 then 7 else if a = 0x1008 then 42 else 0
  rd := [⟨0x1000, 16⟩]
  wr := []
  syms _ := 0x1000

theorem verified : Verified target code contract := by
  refine ⟨fun s h => ⟨_, _, .block (exec_code h), ?_, ?_⟩,
    .of_leakage (fun s => [Leak.addr (s.syms "VG_TEST_TABLE" + BitVec.ofNat 64 8)])
      (fun s t s' h e => by cases e with | block e => rw [exec_code h] at e; cases e; rfl)
      (fun s₁ s₂ _ _ hp => ?_), ?_⟩
  · exact ⟨fun r hr => by
      rw [RegUpd.gpr_write_of_ne _ _ _ (fun e => by subst e; exact absurd hr (by decide)),
        RegUpd.gpr_write_of_ne _ _ _ (fun e => by subst e; exact absurd hr (by decide))],
      rfl, fun _ _ => rfl⟩
  · sig_post [contract, sig, consts, Abi.withConsts, abi, argRegs]
  · sig_pub [contract, sig, consts, Abi.withConsts, abi, argRegs] at hp
    rw [hp.2]
  · refine ⟨sat, ?_⟩
    sig_pre [contract, sig, consts, Abi.withConsts, Abi.constRegions, Abi.constsHeld, abi, argRegs,
      stackBelow, tbl, sat]
    exact ⟨by decide, by decide⟩

def artifact : Artifact where
  target := target
  module := "test"
  name := "vg_test_consts"
  sig := sig
  doc := "Returns word 1 of its table."
  consts := consts
  code := code
  contract := contract
  verified := verified

/-- The rendering: the static's page and offset in the syntax of the object
format (`vg_sym_page!`, `vg_sym_pageoff!`), and its symbol. -/
def expected : String := "/// Returns word 1 of its table.
#[unsafe(naked)]
pub(crate) unsafe extern \"C\" fn vg_test_consts() -> u64 {
    core::arch::naked_asm!(
        concat!(\"adrp x0, \", vg_sym_page!(\"{VG_TEST_TABLE}\")),
        concat!(\"add x0, x0, \", vg_sym_pageoff!(\"{VG_TEST_TABLE}\")),
        \"ldr x0, [x0, #8]\",
        \"ret\",
        VG_TEST_TABLE = sym super::consts::VG_TEST_TABLE,
    )
}
"

#guard Rust.function artifact (fun _ => "") == expected

/-- The table, as `files` writes it in `src/asm/aarch64/consts.rs`. -/
def expectedTables : String := "// @generated by lean/Emit.lean. DO NOT EDIT.
//! The tables of constants of the verified functions for `aarch64` (`Artifact.consts`).
#![allow(dead_code)]

/// The table of constants `VG_TEST_TABLE` (`Artifact.consts`).
pub(crate) static VG_TEST_TABLE: [u64; 2] = [
    7,
    42,
];
"

#guard Rust.tablesFile "aarch64" (Rust.tables [artifact]) == expectedTables

#guard (Rust.checkConsts [artifact] artifact).isOk
#guard Rust.consistent consts [("VG_TEST_TABLE", [7, 42]), ("VG_OTHER", [1])]
#guard !Rust.consistent consts [("VG_OTHER", [1]), ("VG_TEST_TABLE", [7, 43])]
#guard Rust.tableName "VG_P256_COMB7" && !Rust.tableName "vg_table" && !Rust.tableName "_A" &&
  !Rust.tableName "" && !Rust.tableName "A-B"

end VG.Test.ConstTables
