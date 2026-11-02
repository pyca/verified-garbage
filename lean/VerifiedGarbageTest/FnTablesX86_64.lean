module

import VerifiedGarbage.TCB.Rust
meta import VerifiedGarbage.TCB.Rust
import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Call
meta import VerifiedGarbage.Proof.Framework.X86_64.Call

/-!
# Tables of functions (`Artifact.tables`) on x86-64

A function `(t: &[u64; 2]) -> u64` that takes a table of the interface
`TestFns` (`Abi.withTables`), of one function and one word of data, and calls
the function through it: its code, `mov r11, [rdi]` then `call r11`
(`Code.icall`, of `vg_test_fn_a` or else `vg_test_fn_b`), returns what the
function returns. The table `VG_TEST_FNS_A` holds `vg_test_fn_a`, which
returns 1, and the data 1, and `VG_TEST_FNS_B` holds `vg_test_fn_b`, which
returns 2, and the data 2: the function is proven to return the table's word
of data, which needs the model to run the function the table holds. The
emitter renders the indirect call as the instruction alone, and the tables as
statics of the interface's type.
-/

namespace VG.Test.FnTablesX86_64
open VG VG.X86_64

def sig : Sig := { params := [("t", .array false .u64 2)], ret := some .u64 }

def tA : FnTable := { name := "VG_TEST_FNS_A", iface := "TestFns", fns := ["vg_test_fn_a"], data := [1] }
def tB : FnTable := { name := "VG_TEST_FNS_B", iface := "TestFns", fns := ["vg_test_fn_b"], data := [2] }
def tables : List (String × List FnTable) := [("t", [tA, tB])]

/-- The function returns the table's word of data. Its call stores a return
address below the stack pointer: 8 bytes of stack. -/
def contract : Contract isa :=
  sig.contract (abi.withTables sig tables) (post := fun t m _ r => r = m.readW (t + 8) 64)
    (stack := 8)

def fnA : Prog isa := .block [.mov32 .rax (.imm 1)]
def fnB : Prog isa := .block [.mov32 .rax (.imm 2)]

/-- `call r11`, of `vg_test_fn_a` or else `vg_test_fn_b`. -/
def calls : Prog isa :=
  .icall (.callr .r11) "vg_test_fn_a" fnA (.icall (.callr .r11) "vg_test_fn_b" fnB (.block []))

def code : Prog isa := .seq (.block [.mov .r11 (.mem { base := .rdi })]) calls

/-- What the contract says of the entry state: the table is the only region,
holding the words of `VG_TEST_FNS_A` or of `VG_TEST_FNS_B`, whose functions
are at distinct addresses, and there is a quadword of stack. -/
theorem pre_facts {s : State} (h : contract.pre s) :
    s.rd = [⟨s.gpr .rdi, 16⟩] ∧ s.wr = [] ∧ 8 ≤ (s.gpr .rsp).toNat ∧
      s.syms "vg_test_fn_a" ≠ s.syms "vg_test_fn_b" ∧
      ((s.mem.readW (s.gpr .rdi) 64 = s.syms "vg_test_fn_a" ∧
          s.mem.readW (s.gpr .rdi + 8) 64 = 1) ∨
        (s.mem.readW (s.gpr .rdi) 64 = s.syms "vg_test_fn_b" ∧
          s.mem.readW (s.gpr .rdi + 8) 64 = 2)) := by
  sig_pre [contract, sig, tables, Abi.withTables, abi, argRegs, stackBelow, tA, tB, FnTable.words,
    Abi.tableHeld, Sig.wordIndex] at h
  obtain ⟨hsp, ⟨p, hp, T, hT, hh⟩, hd, hrd, hwr, -⟩ := h
  simp only [Option.map_some, List.getD_cons_zero, Option.some.injEq] at hp
  subst hp
  refine ⟨hrd, hwr, hsp, hd (by decide), ?_⟩
  rcases hT with rfl | rfl
  · refine .inl ⟨?_, ?_⟩
    · simpa using hh 0 (by simp)
    · simpa using hh 1 (by simp)
  · refine .inr ⟨?_, ?_⟩
    · simpa using hh 0 (by simp)
    · simpa using hh 1 (by simp)

/-- The state after `mov r11, [rdi]`. -/
def s₁ (s : State) : State := s.setReg .r11 (s.mem.readW (s.gpr .rdi) 64)

/-- The state the function returns in, after a call of the function that
returns `v`. -/
def fin (s : State) (v : BitVec 32) : State :=
  let s₃ := (s₁ s).callEntry.setReg32 .rax v
  s₃.setReg .rsp (s₃.gpr .rsp + 8)

/-- The leakage: the table's first word's address, then the address called,
then the return address's, stored and loaded. -/
def tr (s : State) : List Leak :=
  [.addr (s.gpr .rdi), .addr (s.mem.readW (s.gpr .rdi) 64), .addr (s.gpr .rsp - 8),
    .addr (s.gpr .rsp - 8)]

theorem exec_load {s : State} (h : contract.pre s) :
    Exec isa (.block [.mov .r11 (.mem { base := .rdi })]) s [.addr (s.gpr .rdi)] (s₁ s) := by
  obtain ⟨hrd, hwr, -⟩ := pre_facts h
  have hea : s.ea { base := .rdi } = s.gpr .rdi := by simp [State.ea]
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 8 :=
    ⟨_, by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _), by
      simp [Region.Contains]⟩
  refine .block ?_
  simp only [execBlock, isa, X86_64.exec, readSrc, State.load64, hea, hin, ite_true, Option.map_some,
    addrs, srcAddrs, List.map_cons, List.map_nil, List.append_nil, s₁]

/-- The function at the address `rdi` holds: `mov eax, v` and its return. -/
theorem exec_fn {s : State} (v : BitVec 32) :
    Exec isa (.block [.mov32 .rax (.imm v)]) (s₁ s).callEntry [] ((s₁ s).callEntry.setReg32 .rax v) := by
  refine .block ?_
  simp only [execBlock, isa, X86_64.exec, readSrc32, Option.map_some, addrs, srcAddrs, List.map_nil,
    List.append_nil]

theorem ret_fn {s : State} (v : BitVec 32) :
    isa.ret (s₁ s).callEntry ((s₁ s).callEntry.setReg32 .rax v) = some (fin s v) := by
  simp only [isa, ret, fin, State.setReg32, State.setReg, reduceCtorEq, ite_false, and_self, ite_true]

theorem run {s : State} (h : contract.pre s) :
    ∃ v : BitVec 32, Exec isa code s (tr s) (fin s v) ∧
      v.setWidth 64 = s.mem.readW (s.gpr .rdi + 8) 64 := by
  obtain ⟨-, -, -, hd, hA | hB⟩ := pre_facts h
  · refine ⟨1, ?_, by rw [hA.2]; rfl⟩
    have hi : isa.icall (.callr .r11) (s₁ s) = some (isa.fnAddr (s₁ s) "vg_test_fn_a") := by
      simp only [icall, s₁, State.setReg, ite_true, hA.1]
    have e := Exec.seq (exec_load h)
      (Exec.icall (next := .icall (Instr.callr .r11) "vg_test_fn_b" fnB (.block [])) hi
        (call_callEntry _) (exec_fn 1) (ret_fn 1))
    have ht : [Leak.addr (s.gpr .rdi)] ++ ((isa.addrs (.callr .r11) (s₁ s)).map .addr ++
        .addr (isa.fnAddr (s₁ s) "vg_test_fn_a") :: ((isa.callAddrs (s₁ s)).map .addr ++ [] ++
          (isa.retAddrs ((s₁ s).callEntry.setReg32 .rax 1)).map .addr)) = tr s := by
      simp [tr, addrs, s₁, hA.1, State.setReg32, State.setReg, State.callEntry]
    rw [ht] at e; exact e
  · refine ⟨2, ?_, by rw [hB.2]; rfl⟩
    have hi : isa.icall (.callr .r11) (s₁ s) = some (isa.fnAddr (s₁ s) "vg_test_fn_b") := by
      simp only [icall, s₁, State.setReg, ite_true, hB.1]
    have hne : isa.fnAddr (s₁ s) "vg_test_fn_b" ≠ isa.fnAddr (s₁ s) "vg_test_fn_a" := by
      simp only [s₁, State.setReg]; exact fun e => hd e.symm
    have e := Exec.seq (exec_load h) (Exec.icallNext (i := Instr.callr .r11) (name := "vg_test_fn_a")
        (body := fnA) hi hne
        (Exec.icall (next := .block []) hi (call_callEntry _) (exec_fn 2) (ret_fn 2)))
    have ht : [Leak.addr (s.gpr .rdi)] ++ ((isa.addrs (.callr .r11) (s₁ s)).map .addr ++
        .addr (isa.fnAddr (s₁ s) "vg_test_fn_b") :: ((isa.callAddrs (s₁ s)).map .addr ++ [] ++
          (isa.retAddrs ((s₁ s).callEntry.setReg32 .rax 2)).map .addr)) = tr s := by
      simp [tr, addrs, s₁, hB.1, State.setReg32, State.setReg, State.callEntry]
    rw [ht] at e; exact e

/-- The address called, from the public data. -/
theorem pub_tr {s₁ s₂ : State} (h₁ : contract.pre s₁) (_h₂ : contract.pre s₂) (hp : contract.pub s₁ s₂) :
    tr s₁ = tr s₂ := by
  sig_pub [contract, sig, tables, Abi.withTables, abi, argRegs, tA, tB, FnTable.words, Abi.tableHeld,
    Sig.wordIndex] at hp
  obtain ⟨hsp, ha, hb, ht, hdi⟩ := hp
  have ht := ht _ _ rfl rfl
  have w : s₁.mem.readW (s₁.gpr .rdi) 64 = s₂.mem.readW (s₂.gpr .rdi) 64 := by
    obtain ⟨-, -, -, -, hA | hB⟩ := pre_facts h₁
    · have := ht.1.mp (fun i hi => by
        rcases i with _ | _ | i
        · simpa using hA.1
        · simpa using hA.2
        · exact absurd hi (by simp)) 0 (by simp)
      simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, List.getD_cons_zero] at this
      rw [hA.1, ha, this]
    · have := ht.2.mp (fun i hi => by
        rcases i with _ | _ | i
        · simpa using hB.1
        · simpa using hB.2
        · exact absurd hi (by simp)) 0 (by simp)
      simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, List.getD_cons_zero] at this
      rw [hB.1, hb, this]
  simp only [tr]; rw [w, hsp, hdi]

/-- A state satisfying the precondition: `VG_TEST_FNS_A` at `0x1000`, its
function at `0x100` and the other at `0x200`, the stack at `0x10000`. -/
def sat : State where
  gpr r := if r = .rdi then 0x1000 else if r = .rsp then 0x10000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x1001 then 1 else if a = 0x1008 then 1 else 0
  rd := [⟨0x1000, 16⟩]
  wr := []
  syms n := if n = "vg_test_fn_a" then 0x100 else if n = "vg_test_fn_b" then 0x200 else 0

theorem verified : Verified target code contract := by
  refine ⟨fun s h => ?_, .of_leakage tr (fun s t s' h e => ?_) (fun s₁ s₂ h₁ h₂ hp => pub_tr h₁ h₂ hp), ?_⟩
  · obtain ⟨v, e, hv⟩ := run h
    obtain ⟨-, -, hsp, -⟩ := pre_facts h
    refine ⟨_, _, e, ⟨fun r hr => ?_, ?_, rfl⟩, ?_⟩
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [fin, s₁, State.setReg32, State.setReg, State.callEntry, BitVec.sub_add_cancel]
    · show (fin s v).mem.readW _ 64 = _
      simp only [fin, s₁, State.setReg32, State.setReg, State.callEntry, reduceCtorEq, ite_false]
      refine Mem.readW_writeW_sep (fun x hx hx' => ?_) (by decide)
      simp only [Nat.reduceDiv] at hx hx'
      bv_omega
    · sig_post [contract, sig, tables, Abi.withTables, abi, argRegs]
      exact hv
  · obtain ⟨v, e', -⟩ := run h
    exact (Exec.det e e').1
  · refine ⟨sat, ?_⟩
    sig_pre [contract, sig, tables, Abi.withTables, abi, argRegs, stackBelow, tA, tB, FnTable.words,
      Abi.tableHeld, Sig.wordIndex, sat]
    exact ⟨by decide, ⟨_, rfl, _, .inl rfl, by decide⟩, fun _ => by decide,
      Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), by decide⟩

def artifact : Artifact where
  target := target
  module := "test"
  name := "vg_test_fn_tables"
  sig := sig
  doc := "Returns the word of data of its table, which the table's function returns.\n\n# Safety\n\n"
  tables := tables
  code := code
  contract := contract
  verified := verified
  stack := 8

def prepared : Rust.Prepared := .of (.of artifact)
def internals : List Rust.Internal := Rust.internalsOf [prepared]

/-- The rendering: the indirect call is its instruction alone (`call r11`,
`41 FF D3`, after `mov r11, [rdi]`, `4C 8B 1F`), and the documentation says
what `t` must be. -/
def expected : String := "/// Returns the word of data of its table, which the table's function returns.
///
/// # Safety
///
/// * `t` must be valid for reads of 16 bytes.
/// * `t` must not overlap the return address on the stack or the 8 bytes of stack below it, \
or wrap around the end of the address space (no Rust object does).
/// * `t` must be the `words()` of one of the `TestFns` tables of functions of this crate \
(`fn_tables`), and the CPU must support the features its constant `<TABLE>_FEATURES` gives, \
if it has one.
#[unsafe(naked)]
pub unsafe extern \"sysv64\" fn vg_test_fn_tables(t: *const [u64; 2]) -> u64 {
    core::arch::naked_asm!(
        r#\".base64 \"TIsfQf/Tww==\"
.p2align 6\"#,
    )
}
"

#guard Rust.function artifact (fun n => s!"test::{n}") == expected

/-- Each table: the address of its function, as the internal function's
path, then its data. -/
def expectedA : String := "// @generated by lean/Emit.lean. DO NOT EDIT.
//! The table of functions `VG_TEST_FNS_A` of the verified functions for `x86_64` \
(`Artifact.tables`).
#![allow(dead_code)]

/// The table of functions `VG_TEST_FNS_A` of the interface `TestFns`: `vg_test_fn_a`, then the \
data 1.
pub static VG_TEST_FNS_A: super::TestFns = super::TestFns {
    fns: [crate::test::vg_test_fn_a::vg_test_fn_a as *const ()],
    data: [1],
};
"

#guard Rust.fnTableFile target tA [] (fun n => s!"test::{n}") == expectedA
#guard ((Rust.fnTablesMod "x86_64" (Rust.fnTables [artifact])).splitOn
  "pub struct TestFns {\n    fns: [*const (); 1],\n    data: [u64; 1],\n}").length == 2

-- Both functions the indirect call may reach are emitted, as internal functions.
#guard internals.map (·.name) == ["vg_test_fn_a", "vg_test_fn_b"]
#guard (Rust.checkCalls [prepared] internals prepared) matches .ok _
#guard (Rust.checkFnTables [prepared] internals prepared) matches .ok _
#guard (Rust.checkFeatures prepared) matches .ok _
-- A table naming a function that is not emitted is refused.
#guard (Rust.checkFnTables [prepared] [] prepared) matches .error _

/-! ## The instruction -/

#guard Instr.asm (.callr .r11) == ["call r11"]
#guard Instr.encode (.callr .r11) == some [[0x41, 0xFF, 0xD3]]
#guard Instr.encode (.callr .rax) == some [[0xFF, 0xD0]]
#guard (Instr.callr .rax).requires.isEmpty
#guard !isa.writesSp (.callr .rsp)
-- As a straight-line instruction it faults; as an indirect call's, it calls `r`.
#guard (X86_64.exec (.callr .rax) sat).isNone
#guard isa.icall (.callr .rdi) sat == some 0x1000
#guard isa.fnAddr sat "vg_test_fn_b" == 0x200

end VG.Test.FnTablesX86_64
