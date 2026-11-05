module

public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.Print

/-!
# Registering an implementation of an `Api`

**Trusted.** A registration file makes each function's `Artifact` from its
`Api` with `Api.artifact`, stating only what the implementation chooses: the
target, the code and its proof, the stack it uses, the constant tables it
reads, the tables of functions it takes, the CPU features it needs, how much
of its writable arrays it writes (`written`, with its proof), and the suffix
of its name. Everything else
comes from the `Api` (`Spec/`): the Rust module, name, signature and
documentation, `writeArgs`, and the contract on the target, which the proof
is of. So of a registration, a reviewer reads `suffix` and
`features` (which the emitter checks against the code); the kernel checks
the rest, `written` included. The code is printed with the printer of the
target's ISA, its one `HasPrinter` instance (`TCB/<ISA>/Print.lean`), which
`Api.artifact` pairs with the target (`EmitTarget`).

`Artifact` and `EmitTarget` are defined here rather than with `Target` and
`Verified` (`TCB/Artifact.lean`), which every proof imports, so that no
proof depends on a printer.
-/

@[expose] public section

namespace VG

/-- A target with the printer of its ISA's code (`HasPrinter`): the target
an artifact is emitted for. The printer is not a field of `Target`, which
every proof imports, so that a change to a printer rebuilds only the
registration files and the emitter, not the proofs. -/
structure EmitTarget extends Target where
  printer : Printer isa

/-- The target `T` with its ISA's printer (`HasPrinter`). -/
def EmitTarget.of (T : Target) [p : HasPrinter T.isa] : EmitTarget := ⟨T, p.printer⟩

/-- A verified function, ready to be emitted into the Rust crate. -/
structure Artifact where
  target : EmitTarget
  /-- The Rust module the function is emitted into, `src/asm/<target>/<module>.rs`
  (e.g. `sha256`). -/
  module : String
  /-- The Rust function name. Must be unique within the target. -/
  name : String
  /-- The Rust signature, rendered as the parameter list and return type
  (`Sig.rust`). -/
  sig : Sig
  /-- Documentation for the generated Rust function. With what the emitter
  adds to it (`Sig.layoutNote`, `Sig.validDoc` and `Sig.layoutDoc`, which
  need it to end with its `# Safety` section if they add anything, and not
  to state what they do), it must state every
  requirement of `contract.pre` that the caller is responsible for, and
  anything the contract declares the function may leak (`Sig.contract`'s
  `leak`). -/
  doc : String
  /-- Tables of 64-bit constants the code reads, by name: the emitter writes
  each as a `static` of that name, from which the code forms the table's
  address (`Abi.sym`; on AArch64, ARMv7 and PPC64LE, `adrSym`; on RISC-V,
  `lla`; on x86-64, `leaSym`), and checks that every artifact of the target with a table of that name gives
  the same words (`Rust.checkConsts`). So `contract` is one for the calling convention
  `target.abi.withConsts consts` (`Abi.withConsts`). A table an instruction
  carries (x86-64's `aluTbl`, `Printer.tables`) is written and checked the
  same way without being listed here: the model reads its words from the
  instruction, not from memory the contract describes. -/
  consts : List (String × List (BitVec 64)) := []
  /-- The tables of functions the function takes (`Abi.withTables`): for
  each of its parameters that is one, the parameter's name and every table
  it may point to. The emitter checks that each names a read-only array of
  `u64` of the tables' length, and that it lists every table of their
  interface on the target, of which the Rust caller may pass any
  (`Rust.checkFnTables`). So `contract` is one for the calling convention
  `(target.abi.withConsts consts).withTables sig tables`. -/
  tables : List (String × List FnTable) := []
  code : Prog target.isa
  contract : Contract target.isa
  verified : Verified target.toTarget code contract
  /-- `Sig.contract`'s `writeArgs` and `stack` for `contract` (see `ofSig`). -/
  writeArgs : Bool := false
  stack : Nat := 0
  /-- `contract` is one that `Sig.contract` derives from `sig` for the
  target's calling convention, `writeArgs` and `stack`: so it reads the
  arguments and writes the return value where the calling convention places
  them for `sig`, and requires what `Sig.layoutDoc` documents of where the
  buffers are. -/
  ofSig : ∃ pre post leak,
      contract = sig.contract ((target.abi.withConsts consts).withTables sig tables) pre post writeArgs
        stack leak := by
    exact ⟨_, _, _, rfl⟩
  /-- The contract of the function on every target, which an artifact made
  from an `Api` (`{ api with … }`) takes from it with its `name` and `sig`
  (`Api.contracts`). The emitter refuses an artifact without one
  (`Rust.checkApi`). -/
  contracts : Option Contracts := none
  /-- `contract` is `contracts` on the target, for `stack`: an artifact made
  from an `Api` is proven against the contract `Spec/` gives the function,
  not one chosen where the artifact is built. -/
  ofApi : contracts.elim True fun f =>
      contract = f ((target.abi.withConsts consts).withTables sig tables) stack := by
    first | exact True.intro | exact rfl
  /-- The code changes the stack pointer only by calls and returns and by
  the pushes and pops of frames, which are nested: no other instruction of
  it, or of the functions it calls, writes it. So a call instruction or a
  push only ever stores below the stack pointer on entry, where no Rust
  object lies. -/
  spSafe : code.all (fun i => !target.isa.writesSp i) = true := by decide +kernel
  /-- The CPU features beyond the target's baseline ISA that the code needs,
  by their Rust `target_feature` names: exactly those its instructions, and
  those of the functions it calls, require (`ISA.requires`). The emitter
  checks this (`Rust.checkFeatures`) and adds their presence to the
  function's `# Safety` section, which `doc` must end with when this is not
  empty. -/
  features : List String := []
  /-- How much of some writable array parameters the function writes, in
  bytes: for each `(name, n)`, it changes no byte of the buffer of the
  parameter `name` at offset `n` or beyond (`writtenOk`). The emitter checks
  that each names a writable array parameter, once, with `n` at most its size
  (`Rust.checkWritten`), exports `n` as the constant
  `<NAME>_<PARAM>_WRITTEN` (`Rust.writtenConsts`) and documents it, so that a
  caller that must destroy what the function wrote there need destroy only
  the first `n` bytes. -/
  written : List (String × Nat) := []
  /-- Every run from a state satisfying `contract.pre` changes no byte of
  those buffers beyond their bounds (`Sig.writtenWithin`). -/
  writtenOk : ∀ s t s', contract.pre s → Exec target.isa code s t s' →
      Sig.writtenWithin (target.abi.withConsts consts) sig written s s' := by
    exact fun _ _ _ _ _ => True.intro

/-- Proves `Registration.spSafe`, by default. `Proof/Framework/Registration.lean`
implements it, with the proofs the kernel checks fastest on each ISA; how it
is proven is not trusted. -/
syntax (name := spSafe) "sp_safe" : tactic

/-- Proves `Registration.ofSig`, by default. `Proof/Framework/Registration.lean`
implements it; how it is proven is not trusted. -/
syntax (name := ofSig) "of_sig" : tactic

/-- `api`'s contract under the calling convention `A`, for an implementation
whose calls and frames use `stack` bytes of stack (`Api.contracts`), or, if
`api` has none, one that no state satisfies, which `Verified` rejects. -/
def Api.contract {M : ISA} (api : Api) (A : Abi M) (stack : Nat) : Contract M :=
  match api.contracts with
  | some f => f A stack
  | none => ⟨fun _ => False, fun _ _ => False, fun _ _ => False⟩

/-- An implementation of `api` on `target`: what a registration file states
of a function made from `api` (see `Api.artifact`). -/
structure Registration (api : Api) (target : Target) where
  /-- What follows `api`'s name in the function's: that of the CPU features
  or other variant it is for (e.g. `_avx2`), or nothing. -/
  suffix : String := ""
  /-- `Artifact.consts`. -/
  consts : List (String × List (BitVec 64)) := []
  /-- `Artifact.tables`. -/
  tables : List (String × List FnTable) := []
  /-- `Artifact.stack`. -/
  stack : Nat := 0
  code : Prog target.isa
  /-- The contract `verified` proves, which is `api`'s on `target` for
  `consts`, `tables` and `stack` (`ofApi`); unification finds it in
  `verified`'s type. -/
  contract : Contract target.isa :=
    api.contract ((target.abi.withConsts consts).withTables api.sig tables) stack
  verified : Verified target code contract
  ofApi : contract = api.contract ((target.abi.withConsts consts).withTables api.sig tables) stack := by
    exact rfl
  /-- `Artifact.ofSig`. -/
  ofSig : ∃ pre post leak,
      contract = api.sig.contract ((target.abi.withConsts consts).withTables api.sig tables) pre post
        api.writeArgs stack leak := by
    of_sig
  /-- `Artifact.spSafe`. -/
  spSafe : code.all (fun i => !target.isa.writesSp i) = true := by sp_safe
  /-- `Artifact.features`. -/
  features : List String := []
  /-- `Artifact.written`. -/
  written : List (String × Nat) := []
  /-- `Artifact.writtenOk`. -/
  writtenOk : ∀ s t s', contract.pre s → Exec target.isa code s t s' →
      Sig.writtenWithin (target.abi.withConsts consts) api.sig written s s' := by
    exact fun _ _ _ _ _ => True.intro

/-- The artifact of the implementation `r` of `api` on `target`: its module,
signature and `writeArgs` are `api`'s, its name `api`'s followed by
`r.suffix`, its documentation `api`'s (`Api.doc`), and its
contract `api`'s on `target`, for `r.consts`, `r.tables` and `r.stack`
(`Api.contract`); its code is printed with the printer of `target`'s ISA
(`EmitTarget.of`). -/
def Api.artifact (api : Api) (target : Target) [HasPrinter target.isa] (r : Registration api target) :
    Artifact where
  target := .of target
  module := api.module
  name := api.name ++ r.suffix
  sig := api.sig
  doc := api.doc
  consts := r.consts
  tables := r.tables
  code := r.code
  contract := r.contract
  verified := r.verified
  writeArgs := api.writeArgs
  stack := r.stack
  ofSig := r.ofSig
  contracts := api.contracts
  ofApi := by
    rw [r.ofApi]
    unfold Api.contract
    cases api.contracts <;> exact (by trivial)
  spSafe := r.spSafe
  features := r.features
  written := r.written
  writtenOk := r.writtenOk

end VG
