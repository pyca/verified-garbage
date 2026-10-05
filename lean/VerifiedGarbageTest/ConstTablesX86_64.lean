import VerifiedGarbage.TCB.Rust
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Tables of constants (`Artifact.consts`) on x86-64

A function `() -> u64` that returns word 1 of a table of constants: its code,
`lea rax, [rip + VG_TEST_TABLE]` (`leaSym`) then `mov rax, [rax + 8]`, is
proven against the contract of its signature under `abi.withConsts` (the
table's address `State.syms "VG_TEST_TABLE"`, where the memory holds it),
and the emitter renders the code with the static's symbol in a RIP-relative
operand, and the table as the `static`.
-/

namespace VG.Test.ConstTablesX86_64
open VG VG.X86_64

def sig : Sig := { params := [], ret := some .u64 }
def tbl : List (BitVec 64) := [7, 42]
def consts : List (String × List (BitVec 64)) := [("VG_TEST_TABLE", tbl)]

def contract : Contract isa :=
  sig.contract (abi.withConsts consts) (post := fun m m' r => r = 42 ∧ m' = m)

def code : Prog isa :=
  .block [.leaSym .rax "VG_TEST_TABLE", .mov .rax (.mem { base := .rax, disp := 8 })]

/-- What the contract says of the entry state: the table is the only region,
at the static's address, holding `tbl`. -/
theorem pre_facts {s : State} (h : contract.pre s) :
    s.rd = [⟨s.syms "VG_TEST_TABLE", 16⟩] ∧ s.wr = [] ∧
      s.mem.readW (s.syms "VG_TEST_TABLE" + BitVec.ofNat 64 8) 64 = 42 := by
  sig_pre [contract, sig, consts, Abi.withConsts, Abi.constRegions, Abi.constsHeld, abi, argRegs,
    stackBelow, tbl] at h
  obtain ⟨hd, hheld, -, -, -, ht, hw⟩ := h
  refine ⟨?_, hw, hheld 1 (by decide)⟩
  rw [← List.take_append_drop (s.rd.length - 1) s.rd, hd, ht]; rfl

theorem exec_code {s : State} (h : contract.pre s) :
    execBlock isa [.leaSym .rax "VG_TEST_TABLE", .mov .rax (.mem { base := .rax, disp := 8 })] s =
      some ((s.setReg .rax (s.syms "VG_TEST_TABLE")).setReg .rax 42,
        [Leak.addr (s.syms "VG_TEST_TABLE" + BitVec.ofNat 64 8)]) := by
  obtain ⟨hrd, hwr, h42⟩ := pre_facts h
  have hea : (s.setReg .rax (s.syms "VG_TEST_TABLE")).ea { base := .rax, disp := 8 } =
      s.syms "VG_TEST_TABLE" + BitVec.ofNat 64 8 := rfl
  have hin : InRegions ((s.setReg .rax (s.syms "VG_TEST_TABLE")).rd ++
      (s.setReg .rax (s.syms "VG_TEST_TABLE")).wr) (s.syms "VG_TEST_TABLE" + BitVec.ofNat 64 8) 8 :=
    ⟨_, by
      show _ ∈ s.rd ++ s.wr
      rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _), by
      show ((s.syms "VG_TEST_TABLE" + BitVec.ofNat 64 8) - s.syms "VG_TEST_TABLE").toNat + 8 ≤ 16
      rw [BitVec.add_comm, BitVec.add_sub_cancel]; decide⟩
  have e₁ : X86_64.exec (.leaSym .rax "VG_TEST_TABLE") s =
      some (s.setReg .rax (s.syms "VG_TEST_TABLE")) := rfl
  have e₂ : X86_64.exec (.mov .rax (.mem { base := .rax, disp := 8 }))
      (s.setReg .rax (s.syms "VG_TEST_TABLE")) =
      some ((s.setReg .rax (s.syms "VG_TEST_TABLE")).setReg .rax 42) := by
    simp only [X86_64.exec, readSrc, State.load64, hea, hin, ite_true, Option.map_some]
    exact congrArg (fun v => some ((s.setReg .rax (s.syms "VG_TEST_TABLE")).setReg .rax v)) h42
  simp only [execBlock, isa, e₁, e₂, Option.map_some, addrs, srcAddrs, hea, List.map_cons,
    List.map_nil, List.nil_append, List.append_nil]

/-- A state satisfying the precondition: the table at `0x1000`, the stack
at `0x10000`. -/
def sat : State where
  gpr r := if r = .rsp then 0x10000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x1000 then 7 else if a = 0x1008 then 42 else 0
  rd := [⟨0x1000, 16⟩]
  wr := []
  syms _ := 0x1000

theorem verified : Verified target code contract := by
  refine ⟨fun s h => ⟨_, _, .block (exec_code h), ?_, ?_⟩,
    .of_leakage (fun s => [Leak.addr (s.syms "VG_TEST_TABLE" + BitVec.ofNat 64 8)])
      (fun s t s' h e => by cases e with | block e => rw [exec_code h] at e; cases e; rfl)
      (fun s₁ s₂ _ _ hp => ?_), ?_⟩
  · refine ⟨fun r hr => ?_, rfl, rfl⟩
    have : r ≠ .rax := fun e => by subst e; exact absurd hr (by decide)
    simp only [State.setReg, this, ite_false]
  · sig_post [contract, sig, consts, Abi.withConsts, abi, argRegs]
  · sig_pub [contract, sig, consts, Abi.withConsts, abi, argRegs] at hp
    rw [hp.2]
  · refine ⟨sat, ?_⟩
    sig_pre [contract, sig, consts, Abi.withConsts, Abi.constRegions, Abi.constsHeld, abi, argRegs,
      stackBelow, tbl, sat]
    exact ⟨by decide, by decide, Region.disjoint_of_sep (by decide)⟩

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

/-- The rendering: the static's symbol in a RIP-relative operand. -/
def expected : String := "/// Returns word 1 of its table.
#[unsafe(naked)]
pub(crate) unsafe extern \"sysv64\" fn vg_test_consts() -> u64 {
    core::arch::naked_asm!(
        \"lea rax, [rip + {VG_TEST_TABLE}]\",
        \"mov rax, QWORD PTR [rax+8]\",
        \"ret\",
        \".p2align 6\",
        VG_TEST_TABLE = sym super::consts::VG_TEST_TABLE,
    )
}
"

#guard Rust.function artifact (fun _ => "") == expected

#guard (Rust.checkConsts [artifact] artifact).isOk
#guard Instr.asm (.leaSym .rdx "VG_TEST_TABLE") == ["lea rdx, [rip + VG_TEST_TABLE]"]
#guard (Instr.leaSym .rdx "VG_TEST_TABLE").requires.isEmpty
#guard addrs (.leaSym .rdx "VG_TEST_TABLE") sat == []
#guard isa.writesSp (.leaSym .rdx "VG_TEST_TABLE") == false
#guard isa.writesSp (.leaSym .rsp "VG_TEST_TABLE") == true
#guard ((X86_64.exec (.leaSym .rdx "VG_TEST_TABLE") sat).map fun t =>
  (t.gpr .rdx, t.gpr .rax, t.cf, t.mem 0x1008, t.syms "VG_TEST_TABLE")) ==
    some (0x1000, 0, none, 42, 0x1000)

end VG.Test.ConstTablesX86_64
