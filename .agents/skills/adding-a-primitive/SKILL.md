---
name: adding-a-primitive
description: "Use before adding a new primitive or algorithm, a new target for one, a CPU-feature variant, or any file under lean/VerifiedGarbage/Artifacts/ or Proof/Variants/: the steps, what a registration states, and how generic callers and variants are registered."
---

# Adding a primitive

This takes at least two PRs (see "One kind of change per PR" in
`AGENTS.md`): step 1 alone, then steps 2–5 together. Any TCB additions the primitive needs (e.g. new
instructions in an ISA model) go in their own PR before either.

1. `Spec/<Alg>.lean`: the algorithm, transcribed from the standard, with no
   target-specific imports; and `Spec/<Alg>/Contract.lean`: for each function,
   its Rust signature (`Sig`) and its `Contract` on every target, built with
   `Sig.contract` from a postcondition and any precondition the signature does
   not imply, and its `Api`: its Rust module (the file under
   `crates/verified-garbage-asm-<target>/src/`) and name, its signature, its contract on every target
   (`contracts := some fun A stack => fooContract A stack`, or
   `fun A _ => fooContract A` for a contract without `stack`), its
   contract's `writeArgs`, and its documentation: what it does, and the `# Safety` items but for what
   the emitter generates (what memory each buffer must be valid for:
   `Sig.validDoc`; which buffers may not overlap each other, the stack or
   the arguments on it, and that none wraps around the address space:
   `Sig.layoutDoc`). Choose
   `pub` honestly: only lengths and pointers are public unless the algorithm
   says otherwise.
   Only functions the Rust code calls get an `Api`. A function only other
   verified functions call (a compression function, a field
   multiplication, a block function under a mode) needs no `Api`, contract
   or registration: the emitter emits it as an internal function
   (`Rust.Internal`, `internal/<name>.rs`) from the code its callers' proofs
   run, and the contract its proof uses, which their proofs compose, is in
   `Proof/`, untrusted. Name it as a Rust function starting with `vg_`.
2. `Impl/<Alg>/<Target>.lean`: the code.
3. `Proof/<Alg>/…`: the proof of `Verified`. A proof may be written against a
   simpler per-target contract of its own and moved to the shared one with
   `Verified.of_implies` (see `Proof/Framework/Contract.lean`).
4. An `Artifact` in the registration file `Artifacts/<Alg>/<Target>.lean`,
   which defines `VG.Artifacts.<Alg>.<Target>.artifacts` (a new file for a
   new algorithm or target; see `Artifacts/Selftest/X86_64.lean`). An
   algorithm has one file per target, holding the artifacts of all its
   functions, whatever variant lists they map over
   (`artifacts := [ … ] ++ Sign.artifacts`, with the artifacts of a function
   generic over a list in a namespace of their own): never a directory for
   one of its functions or interfaces. Each artifact is made
   from the function's `Api` by `Api.artifact` (`TCB/Registration.lean`),
   with the file importing
   `Proof/Framework/Registration.lean` for its default proofs, and its
   target's printer, `TCB/<Target>/Print.lean` (`public import
   VerifiedGarbage.TCB.X86_64.Print`), whose `Emitter` instance
   `Api.artifact` takes (no proof imports a printer, so a change to one
   rebuilds only registration files; a generic file imports it too):

   ```lean
     Spec.<Alg>.fooApi.artifact X86_64.target {
       code := Impl.<Alg>.X86_64.foo
       verified := Proof.<Alg>.X86_64.foo_verified },
   ```

   A registration states only what the implementation chooses: the Rust
   module, name, signature, `writeArgs`, documentation and contract come
   from the `Api`, so never restate them. Give a variant's name its
   `suffix` (`suffix := "_avx2"`), and, where a caller wipes a
   writable array the function uses as working space, how much of it the
   function writes in `written` (`written := [("scratch", 1024)]`, proven by
   `writtenOk`), which the emitter exports as `<NAME>_<PARAM>_WRITTEN` for
   the caller to wipe only that much. Its contract is found
   from `verified`'s type, and must be the `Api`'s on the target for
   its tables of constants and `stack` (`ofApi`, by `rfl`): give `contract` only when
   `verified`'s type does not determine it (its default is the `Api`'s for
   no tables and no stack), and where it is not yet known when the
   registration is elaborated, make it known: give the `v` of a
   `variants.map fun v =>` its type (`fun (v : Variant) =>`), for
   `v.verified`. The tables of constants the
   code reads are an implementation detail, never stated in a registration
   (`ci/check_registrations.py` refuses `consts :=`): the default of
   `consts`, `consts_of`, takes them from the contract `verified` proves,
   the first `Abi.withConsts A cs` in it or in the calling convention of the
   `Sig.contract` it unfolds to, so state the proof's contract on
   `T.abi.withConsts cs` (`fooContract (AArch64.abi.withConsts initConsts)`),
   and a proof that adds or changes a table changes no registration file.
   So is the stack the code's calls and frames use (it refuses `stack :=`
   too): the default of `stack`, `stack_of`, is the `stack` of that
   `Sig.contract` (`fooContract X86_64.abi 8`), and code that uses more or
   less stack changes its proof and no registration file. `of_sig` proves `ofSig`, and
   `sp_safe` proves `spSafe`: by `Code.all_of_forall` on ARMv7, AArch64 and
   PPC64LE,
   which evaluates nothing, and by `Code.all_of_spTest (by lit_decide)`
   on x86 and x86-64, which tests each instruction with the ISA's `keepsSp`
   (see "Code the kernel evaluates" and "Matching on an instruction" in the
   `proof-performance` skill), falling back
   to `decide +kernel` where `lit_decide` exceeds the recursion limit, and
   for code that depends on a `Bool` or an enumeration (`adx`, a field
   variant), by cases on it. Never set
   `contracts` outside `Spec/` (the emitter refuses an artifact without
   them). The CPU features the code needs beyond the target's baseline ISA
   are never stated: `Api.artifact` takes them from its instructions and
   those of the functions it calls (`Code.requiresDedup`, from the ISA
   model's `requires`).
   A function also proves that it returns without secret residue, as part
   of what its registration proves (`verified := .scrubbed h`): see
   "Returning without secret residue" below, which says how on every
   target.
   A function that calls another one with several implementations (e.g.
   scalar and SHA-NI compression) is proven once for any of them, and its
   registration file applies it to each: the implementations of the callee
   on a target are one list, `variants` in
   `Proof/Variants/<Iface>/<Target>.lean`, which the caller's registration
   maps over (`def artifacts : List Artifact :=
   Proof.Variants.<Iface>.<Target>.variants.flatMap artifactsFor`), and so
   is a function that calls such a caller (e.g. HMAC's `init`, calling
   SHA-256's `update`). A function that calls functions of several such
   interfaces maps over each of their lists, nested (e.g. Argon2's x86-64
   derivation, `Artifacts/Argon2/X86_64.lean`, calling BLAKE2b's streaming
   functions and Argon2's `G`); its instances are named by `qualifiedName`
   (`Proof/Framework/QualifiedName.lean`): the function's name, then a tag
   and the suffix of each interface whose variant is not the baseline
   (`vg_argon2_blake2b_avx2_g_avx512`; `vg_argon2` for the baseline), since
   variants of different interfaces may share a suffix; callers of one
   interface append the suffix alone. A function that takes every
   implementation at once, through a table of functions (`Abi.withTables`),
   takes the list itself. Never list the implementations in the caller: a
   new implementation is a new element of its interface's list, and its
   callers follow.
   The emitter writes each function's dispatcher, `<name>_auto` (in
   `crate::arch::dispatch::<module>`), which tries its implementations (the
   artifacts of its `Api`, all in one registration file) in the order that
   file lists them: so list them best first, and put a new variant in its
   interface's list where it ranks, which orders its callers' instances
   too (those of a caller of several interfaces by the first list, then the
   next). One the dispatcher would never choose (it needs every feature of
   one before it, or more) fails the emitter. Extra features or a `vendor`
   it is chosen only with go in its registration (`Registration.extra`,
   `Registration.vendor`).
   Registration files (`Artifacts/`) are reviewed by hand, so they only
   bind: no theorems, no tactic proofs beyond the defaults (not even a
   `(by decide)` argument), no definitions but those of its artifacts, and
   no module
   docstring but its title (`/-! # SHA-256 (FIPS 180-4) on x86-64 -/`):
   what the code does is in the code and its proofs. A lemma
   whose side conditions a registration would decide takes them as
   `autoParam`s (`(hd : stackUse c ≤ 48 := by lit_decide)`), or the
   algorithm's proofs state the instance as a theorem
   (`Proof/Rsa/X86_64/Instances.lean`); `ci/check_registrations.py` checks
   it. Build a variant with its proofs under `Proof/`
   (`Proof/Variants/<Iface>/<Target>/<Name>.lean`) and add it to its
   interface's list (`Proof/Variants/<Iface>/<Target>.lean`);
   put what a generic caller's artifacts are built from (instances of the
   functions it calls, lemmas about its code) in a module of the
   algorithm's proofs, as `Proof/AesGcm/X86_64/Instances.lean` does.
   The record itself (`{ suffix, code, verified, spSafe }`, and any choice
   between implementations, `match` or `if`) is written in the registration
   file, never built under `Proof/`: a `spSafe` the default does not prove
   is a theorem of the code there (`…_spSafeFn`, `Proof/AesGcm/X86_64/Leaves.lean`).
   The one exception is an interface whose functions carry their own contract
   and stack (`StreamFn.reg`, `StreamFnS.reg`, `Pbkdf2Impl.reg`,
   `FinImpl.reg`): their record must state `consts` and `stack`, which a
   registration file may not.
   A function whose proof takes a Weierstrass curve's group law (`Law`,
   `Proof/Weierstrass/Law.lean`) is registered as any other, passing the
   law: its registration file imports `Proof/<Curve>/<Target>/Law.lean`,
   which defines it (`hasLaw`) and is the only module that imports the
   Mathlib algebra of its proof, privately, exposing only its type. A law
   is not a variant: there is one per curve and target, with no suffix.
5. Regenerate the generated crates, build the public Rust API on top of the primitive
   (calling each function's dispatcher, `<name>_auto`, where it has variants;
   the Rust only checks arguments, lays out buffers and calls: see "The
   cryptography is in the verified code, never in Rust" in `AGENTS.md`, and
   if the API needs a step no verified function does, go back to step 1),
   and test it against the Wycheproof vectors in `tests/wycheproof/` (set
   `WYCHEPROOF_ROOT` to a checkout of C2SP/wycheproof). Benchmark the new
   API in `bench/benches/primitives/<alg>.rs`, next to the same operation in
   OpenSSL, at the sizes the others use.

## Returning without secret residue

### The method

Every artifact proves its ISA's `NoResidue` (`TCB/<ISA>/Residue.lean`) as
part of what its registration proves: `verified := .scrubbed h`, of an
`h : VerifiedScrubbed …` (`TCB/Registration.lean`). The cleanup is part of
the function's code. The function as emitted, its body and then the
instructions that clear the registers it wrote and zero the stack it used,
is a named definition in `Impl/` (`Fn`), which states those registers and
that stack as literals; one theorem in `Proof/` states `VerifiedScrubbed` of
that definition, from its target's theorem for its kind of cleanup; and the
registration file binds the two: `code := Impl.…`,
`verified := .scrubbed (Proof.… )`, with no call of a scrub wrapper or form,
no register list, no side condition and no tactic in it (`Fn` in
`Impl/Sha3/AArch64/Instances.lean`, `Proof/Sha3/AArch64/Scrub.lean`,
`Artifacts/Sha3/AArch64.lean`). With the registers and the stack stated,
nothing is worked out of the code when the emitter runs: it only prints,
and the kernel has checked what the cleanup needs of the code (its side
condition, by `lit_decide`) when the proof module was built.

There are three kinds of cleanup. Each target has the forms the table below
names, and no others:

* **Whole-frame:** zero all the stack the code's frames and calls use, then
  clear the registers. It needs nothing of where the code keeps its
  secrets, only facts about its shape (how deep its frames go, what it
  calls), so it serves any code, at a store per word or chunk of that stack
  on every call.
* **Selective:** zero only the parts of that stack that a residue analysis
  (a taint analysis of two runs, `TaintCT`) finds may differ between two
  runs, then clear the registers. Find them by running the analysis in
  compiled code (an `#eval`) and name them as a literal next to the
  function; the proof checks the analysis of the code with its cleanup
  (`⟨_, by taint_decide_ct⟩`, or `taint_decide`). It pays where the
  analysis leaves little of the stack secret, in code that wipes its own
  working space (`withRegScratchWiped`, `withStackScratchWiped`); where it
  leaves most of it secret, the whole-frame form is the shorter code.
* **Code wipes its own frame:** the code zeroes its frame before it
  releases it (`withStackScratchWiped`, its wipe covering all of the
  buffer), and the cleanup zeroes no stack: it only clears the registers.
  It needs more of the code than the others (its target's section says
  what): code that calls or pushes below that frame stays on the
  whole-frame form.

**Registers.** Every cleanup clears the registers the calling convention
lets a function change, but the result's `rb` bits. Which ones it names is
one of three ways, the table says which a target has: every caller-saved
register, whatever the code writes (a fixed tail); a list the `Fn`
definition states (a `Clear`); or, for a function generic over
implementations whose registers do not fit one list, a list worked out of
the code. Prefer stated registers for a function that is not generic: its
assembly's cleanup is then readable next to its definition.

**`PostOut`.** A cleanup that writes the stack after the body needs that
the postcondition reads the memory on return only within the buffers
(`<ISA>.Scrub.PostOut`, by `postOut_of_local`; on AArch64 the `post` field
of `ScrubAllOk`).

**Frame sizing.** The cleanup zeroes the stack the contract's `stack`
says the code uses, so prove the function with the frame its code uses,
not a contract sized for another target: ARMv7's SHA-2 `update` and
`finalize`, proven against the shared contracts' scratch (chosen for
x86-64's AVX2 compression functions), wiped 624 and 1392 bytes where their
code uses 176 and 288 (#5774; BLAKE2's, #5988). Prove such code against a
contract with the scratch it uses (`Proof.Sha256.updateScratchContractW`)
and move it to the shared one with `Verified.of_implies`. Where a form
takes frames of a given size (ARM's `FrameOk`, AArch64's multiple of 16),
code proven with another number is first proven with the next one
(`Arm.Scrub.Verified.stack_le`, as `Proof/Ct/Arm/Scrub.lean` does).

**Variants.** For code generic over a variant, each variant proves what the
cleanup needs of its own code where it is defined (a field of the variant
structure, by `lit_decide`), the function proves its own instructions once
for any variant (most targets: its code with a stub, `.block []`, in the
variant's place, evaluated once, and `fill_calls` proving `Fill` from it to
the code with any variant), and a lemma joins the two (each target's
section names it): never a proof over the list of variants, which
evaluates every variant's code again for every caller, and never
`variants.attach` in a registration file.

**Every target the same way.** Each target states its cleanup only as
theorems about named code, and has no form that builds a registration: a
registration file binds `code := Impl.…` and `verified := .scrubbed Proof.…`
(and, where the default does not prove it, `spSafe := Proof.…`), and nothing
else. On 64-bit RISC-V, `ci/check_registrations.py` checks that shape
exactly; the other targets keep it by review, as some of their generic
interfaces' records give code from a variant's fields (`v.code`).

**Without a proof.** Only functions `ci/residue_allowlist.txt` already
lists may go without (`verified := .unscrubbed h`, of an
`h : Verified …`): the list only shrinks (`ci/check_residue_allowlist.py`),
and the emitter refuses a listed function that has a proof, so converting
one removes its line.

### The files on each target, and a new target

Every target keeps its cleanup in the same files, and a new target (or one
that starts requiring `NoResidue`) adds them in this shape:

| File | Holds |
|---|---|
| `TCB/<ISA>/Residue.lean` | `NoResidue`, the property (a trust change, in a TCB PR of its own) |
| `Impl/Scrub/<Target>.lean` | The forms: `scrubAll` (whole-frame), and `scrub` (code without frames) or `scrubSel` (selective) where the target has them; a further form module is `Impl/Scrub/<Target>/<name>.lean` |
| `Proof/Framework/<Target>/ScrubProved.lean` | `verifiedScrubbedAll` (and `verifiedScrubbed`, `verifiedScrubbedWiped`): `VerifiedScrubbed` of the form applied to a function's code, from its code's own theorem (an `Unscrubbed` record, or on AArch64 its `Verified`), with what the cleanup needs of the code as one Boolean (`scrubSide`, by default `lit_decide`) and the stack and result's bits as the literals of the code (`hW`, `hb := by rfl`) |
| `Proof/Framework/<Target>/ScrubSel.lean` | Where there is a residue analysis: `verifiedScrubbedSel` and its side condition, importing `ScrubProved.lean` and never imported by it |
| `Impl/<Alg>/<Target>/Fn.lean`, `Proof/<Alg>/<Target>/Scrub.lean`, `Artifacts/<Alg>/<Target>.lean` | Per algorithm: the function as emitted (`def f := scrubAll …`), the one theorem about it (`f_scrubbed`), and the binding |

Start from the whole-frame form alone, which serves any code: a selective
form needs a residue analysis of the ISA first. Never add a form that builds
a `Registration`, a scrub wrapper a registration file calls, or a second
name for a form: the theorems prove themselves from the code's own
`Verified` and the side condition, as every target's do.

### The forms on each target

| Target | Whole-frame: form; theorem | Selective: form; theorem; analysis | Code wipes its own frame: form; theorem | Registers cleared | Template | Notable limits |
|---|---|---|---|---|---|---|
| x86-64 | `Impl.Scrub.X86_64.scrubAll v rb n`; `X86_64.Scrub.verifiedScrubbedAll` (`Proof/Framework/X86_64/ScrubProved.lean`). Both it and `scrubSel` are built from `scrubWith`, the clearing of given registers and granules, which no registration names | `Impl.Scrub.X86_64.scrubSel v rb n rs` (runs of 16-byte granules); `X86_64.Scrub.verifiedScrubbedSel` (`Proof/Framework/X86_64/ScrubSel.lean`); `X86_64.RTaint` (`Proof/Framework/X86_64/ResidueTaint.lean`) | none | Fixed: every vector register at the level `v` (at `evex`, `zmm16`–`zmm31` too) and every caller-saved register, but the result's `rb` bits | `Impl/Rc2/X86_64/Fn.lean`, `Proof/Rc2/X86_64/Scrub.lean`, `Artifacts/Rc2/X86_64.lean` | Neither form writes MXCSR: the code must leave it as two runs found it (`mxSameB`). The analysis does not follow code whose pointers and lengths are arguments on the stack. |
| x86 (32-bit) | `Impl.Scrub.X86.scrubAll rb W c`; `X86.Scrub.verifiedScrubbedAll`. Code that calls nothing and has no frame: `scrub rb c`, which zeroes no stack; `X86.Scrub.verifiedScrubbed` | none | `Impl.Scrub.X86.scrub rb c` of code ending in `withStackScratchWiped`; `X86.Scrub.verifiedScrubbedWiped` (`Proof/Framework/X86/ScrubWiped.lean`) | Fixed: the caller-saved registers (`ecx`, `xmm0`–`xmm7`, `edx`:`eax` above the result's `rb` bits) and the flags, to constants | `Impl.Sha3.X86.Fn` (`Impl/Sha3/X86/Instances.lean`), `Proof/Sha3/X86/Scrub.lean`, `Artifacts/Sha3/X86.lean`; wiped: `Impl.Seed.X86.Fn.expandKey` (`Impl/Seed/X86/Fn.lean`), `Proof/Seed/X86/Scrub.lean` | No residue analysis: a selective form would need one, as x86-64's. The wiped form only for code whose frame calls nothing and has no frame below it, whose arguments are of 32 bits and public, and whose contract does not write its arguments |
| AArch64 | `Impl.Scrub.AArch64.scrubAll W rb cl c` (`scrubAllL` for 4080 < `W` < 8176); `AArch64.Scrub.verifiedScrubbedAll` (`Proof/Framework/AArch64/ScrubProved.lean`). With every register cleared (`Clear.all`), stated of the code and its contract: `AArch64.Scrub.verifiedScrubbedClearAll` (`SideFill.lean`). With the registers read off the code: `scrubOf W rb body`; `AArch64.Scrub.verifiedScrubbedOf` | `Impl.Scrub.AArch64.scrubSel W ks c` (16-byte granules `ks`), after the clears (`withClears`); `AArch64.Scrub.verifiedScrubbedSel` (`Proof/Framework/AArch64/ScrubSel.lean`); `AArch64.RTaintG.rtaintG` (`Proof/Framework/AArch64/ResidueWin.lean`) | none: code that wipes its own frame still has its stack zeroed again by `scrubAll` (a port would be a theorem like x86's or PPC64LE's `verifiedScrubbedWiped`) | Stated: a `Clear` (`Clear.all`, every register the calling convention does not preserve) and the flags; or worked out of the code (`Clear.of`, `Impl/Scrub/AArch64/Writes.lean`); for `scrubSel`, the lists of `withClears` | `Impl/Sha3/AArch64/Instances.lean`, `Proof/Sha3/AArch64/Scrub.lean`, `Artifacts/Sha3/AArch64.lean`; selective: `Impl/Rc2/AArch64/Fn.lean`, `Proof/Rc2/AArch64/InitResidue.lean`, `Artifacts/Rc2/AArch64.lean` | `W` a multiple of 16 below 4096 (`scrubAllL` above). No instruction may write PSTATE.DIT, and nothing is called indirectly (`sideAll`). `rtaintG` has no indirect call, and forgets every granule it knew of at a secret store it cannot place |
| ARMv7 | `Impl.Scrub.Arm.scrubAll rb n c`; `Arm.Scrub.verifiedScrubbedAll`. Code without frames: `scrub rb c`, which zeroes no stack; `Arm.Scrub.verifiedScrubbed` (`Proof/Framework/Arm/ScrubProved.lean`) | `Impl.Scrub.Arm.scrubSel rb n ws c` (words `ws`, `Impl/Scrub/Arm/Sel.lean`); `Arm.Scrub.verifiedScrubbedSel` (`Proof/Framework/Arm/ScrubSel.lean`); `Arm.rtaint` (`Proof/Framework/Arm/ResidueTaint.lean`, `ResidueTaintSound.lean`) | none: such code uses `scrubSel`, which stores nothing where the analysis finds no word (`ws = []`) | Fixed: the registers a callee may change, but the result's `rb` bits, and the flags, to constants | `Impl/Sm3/Arm/Stream.lean`, `Proof/Sm3/Arm/Scrub.lean`, `Artifacts/Sm3/Arm.lean`; selective: `Impl/Camellia/Arm/Fn.lean`, `Proof/Camellia/Arm/Scrub.lean` | `n` a multiple of 8 (`FrameOk`). The analysis has no indirect call, and a secret it stores where it cannot place makes the open frames' bytes secret |
| RISC-V64 | `Impl.Scrub.RISCV64.scrubAll rb W c`; `RISCV64.Scrub.verifiedScrubbedAll` (`Proof/Framework/RISCV64/ScrubProved.lean`) | `Impl.Scrub.RISCV64.scrubSel rb fs c` (runs `fs` of each frame); `RISCV64.Scrub.verifiedScrubbedSel` (`Proof/Framework/RISCV64/ScrubSel.lean`); `RISCV64.rtaint` (`Proof/Framework/RISCV64/ResidueTaint.lean`, `ResidueTaintSound.lean`) | none | Fixed: the caller-saved registers, but the result's `rb` bits | `Impl/Sha3/RISCV64/Instances.lean`, `Proof/Sha3/RISCV64/Scrub.lean`, `Artifacts/Sha3/RISCV64.lean` | The analysis has no indirect call, and a secret it stores where it cannot place makes the frames' bytes secret. |
| PPC64LE | `Impl.Scrub.PPC64LE.scrubAll rb d cl c`; `PPC64LE.Scrub.verifiedScrubbedAll` (`Proof/Framework/PPC64LE/ScrubProved.lean`) | none | `Impl.Scrub.PPC64LE.scrubAll rb 0 cl c` of code ending in `withStackScratchWiped`; `PPC64LE.Scrub.verifiedScrubbedWiped` | Stated: a `Clear` (`r0`, the bits of `r3` above the result's `rb`, the scratch registers, `XER`'s carry and the vector registers the code writes; `Clear.all`) | `Impl/Sha3/PPC64LE/Instances.lean`, `Proof/Sha3/PPC64LE/Scrub.lean`, `Artifacts/Sha3/PPC64LE.lean` | No residue analysis, and little need of one: the whole-frame wipe zeroes a region of 512 bytes or more by 128-byte `dcbz`s, so it is cheap. |

### x86-64

**Side conditions.** `scrubSel` zeroes, of the `n` bytes of stack, in
chunks whose 16-byte stores are aligned (`chunksA`), only the runs of
granules `rs` the analysis finds may differ between two runs; `scrubAll`
zeroes all of them, for code the analysis does not follow. The runs are
literals in the function's `Fn` definition (`RScrub.keepRuns` computes
them, by `#eval`). `verifiedScrubbedSel` takes the analysis by
`taint_decide`, and both theorems take `PostOut`; the registration also
binds the code's `spSafe`, from the code's own (`Scrub.scrubKs_spSafe`)
(`Proof/Framework/X86_64/ScrubProved.lean`; `verifiedScrubbedSel` in
`ScrubSel.lean`). Code must leave MXCSR as two runs
found it (`scrubSideG`'s `mxSameB`).

**Variants.** Each variant proves `X86_64.Scrub.calleeSide` of its own
code at its level where it is defined (a field of the variant structure,
by `lit_decide`; `EcbImpl.side`), the function proves `Fill` from its code
with a stub to its code with any variant (`fill_calls`), and
`verifiedScrubbedAllFill` joins them with `stubSide` of the stub, which the
kernel evaluates once (`Proof/Framework/X86_64/ScrubCall.lean`;
`Proof/TripleDes/X86_64/Batch/Scrub.lean`,
`Artifacts/TripleDesCbc/X86_64.lean`). A hole in the stub is a call
`.call f (.block [])`, charged the stack `n f` of the kind of
implementation it stands for (`depthH`), so give the stub's calls names
that tell them apart; pass the stub (`a`), its own level (`ks`) and `n`
explicitly, and case-split on any variant data the stub keeps
(`rcases v.scrOk …`) so that `stubSide` is of a closed term. Variant
structures state `calleeSide` importing only
`Proof/Framework/X86_64/CalleeSide.lean`; a variant built over another
proves it from the other's by `calleeSide_of_fill` (`UpdateImpl.ctr32`,
`Proof/CmacAes/X86_64/Variant.lean`), and a function that is one
variant's code alone by `verifiedScrubbedAllSide`. Examples:
`Proof/Scrypt/X86_64/Whole/Scrub.lean`, `Proof/AesCbc/X86_64/Wiped.lean`,
`Proof/CmacAes/Stream/X86_64/Scrub.lean`. Where each variant's function is
evaluated anyway (a variant's own streaming functions), the variant instead
carries what `scrubSel` needs of that function's code,
`X86_64.Scrub.SelScrub` (its level, the runs, the analysis by
`taint_decide` and `scrubSideG` by `lit_decide`), and `SelScrub.scrubbed`
states the theorem (`Backend.updScrub`, `Proof/Blake2/X86_64/Backend.lean`;
`StreamFnS`, `FinImpl`, `Proof/Pbkdf2/Md/X86_64/`).

**Where the analysis fails.** Its trace says at which instruction (an
index it cannot bound, a value reloaded after a store it cannot place):
change the code so it can, as the Merkle–Damgård streaming code clamps its
indices, and ChaCha20's `apply` keeps the data and its length in `r14` and
`r15` and takes its state back from the buffer `vg_chacha20_xor` returns.

**Calls that load MXCSR.** `calleeSide` forbids `ldmxcsr` in a callee.
Code that calls `vg_mcdt_enter`, the one function that loads it, proves
that it leaves MXCSR as two runs found it by its structure (`mxCalls`,
`Proof/Framework/X86_64/MxCall.lean`), which evaluates the MXCSR analysis on
`vg_mcdt_enter` alone, and a generic caller of it uses
`verifiedScrubbedAllFillM` (ChaCha20-Poly1305 over Poly1305's vector code).

**Calls through a table.** Code of the baseline ISA that may run AVX
functions ending in `vzeroupper` through a table it takes cannot be cleared
at the level `avx`, whose clearing needs a feature the code does not: it is
cleared at the level `sse` (`verifiedScrubbedAllUp`,
`Proof/Framework/X86_64/ScrubUpFn.lean`), which needs that the upper halves
of the vector registers agree after its calls if they did before. Each
implementation in the table states that of its own code (`upCallee`), and
`verifiedScrubbedAllUpFill` joins them with the function's code with a stub
in their place (`TFill`, `tfill_calls`,
`Proof/Framework/X86_64/TableFill.lean`; ECDSA's `sign`). Code that is also
generic over an implementation it calls directly, at the level `sse` for
some implementations and higher for others, uses `verifiedScrubbedOrUp`
(`Proof/Framework/X86_64/ScrubUpFill.lean`; RSA-PSS and RSA-OAEP over the
RSA implementations).

### x86 (32-bit)

**Side conditions.** The result's bits and the stack are literals in the
function's `Fn` definition. `verifiedScrubbed` needs that the code calls
nothing and has no frame (`scrubSide`, by `lit_decide`);
`verifiedScrubbedAll`, for code with frames, direct calls and calls through
its tables, needs `scrubFSide` (by `lit_decide`) and `PostOut`
(`Proof/Framework/X86/ScrubProved.lean`).

**Variants.** The tail clears every register a callee may change, so a
variant states only `calleeOk` of each code it gives (no MMX, no indirect
call: `Ctr32Impl.scrub`, by `lit_decide`) besides its stack; the function's
code with a stub of the variant (code `.block []`) is evaluated once
(`scrubFSide … = true`, `lit_decide`), `fill_calls` proves `Fill` from it
to the code with any variant, and `X86.Scrub.scrubFSide_of_fill` joins
them (`Proof/Framework/X86/ScrubCall.lean`,
`Proof/CmacAes/Stream/X86/Scrub.lean`).

**Code that wipes its own frame.** `verifiedScrubbedWiped` needs more than
PPC64LE's: there the frame's region leaves out its header, but on x86 the
header (its first word, the copies of the arguments, the buffer's address)
is in the frame and is not wiped. So it takes the code's own theorem with
its scratch contract, which must not let it write its arguments
(`wa = false`), and needs that the code in the frame calls nothing and has
no frame (`wipedSide`, by `lit_decide`) and that every argument is of 32
bits and public (`argsPub`, by `decide`): code that calls or pushes below
its frame, or whose contract may write its arguments, stays on `scrubAll`.

### AArch64

**Side conditions.** `verifiedScrubbedAll` needs `scrubSide … = true` (by
`lit_decide`) and `ScrubAllOk` of the contract (the stack, `PostOut`, and
that two runs share a stack pointer).

**Variants.** For a function generic over a variant whose registers fit
one list, the registers are the function's own joined with those the
variant states it writes (`Clear.union`, `Callee.clear`); each variant
proves that of its own code where it is defined (`Permutation.scrub`, by
`lit_decide`), the function proves its own instructions once, and
`AArch64.Scrub.scrubSide_union` joins the two. Code that is the same
for every implementation but for the calls of it is built with a hole in
its place and filled (`Code.fillCalls`, `Code.fill2`), and
`verifiedScrubbedOfFill` (`Proof/Framework/AArch64/SideFill.lean`) gives
the theorem for every implementation of which the closed code's facts
hold. A function generic over implementations whose registers do not fit
one list each (HMAC and PBKDF2 over the hashes: what `finalize` writes is
not what `update` writes, and their own instructions differ by parameter
set) states no registers: it is `scrubOf W rb body`, whose cleanup clears
the registers `Clear.of` reads off `body`, the functions it calls included,
and `verifiedScrubbedOf` needs of the code only that no instruction writes
PSTATE.DIT and that it calls nothing indirectly (`sideAll`), and its
frames' depth: each implementation's record carries the fact about its own
code (`Compress.side`, by `lit_decide` where it is defined), and the
function proves it of its own instructions once, with empty code in the
place of the functions it calls (`Fn` in
`Impl/Pbkdf2/Md/AnyKey/AArch64.lean`, `hmacInit_scrubbed` in
`Proof/Pbkdf2/Md/AArch64/Variant.lean`,
`Artifacts/HmacSha256/AArch64.lean`). There the registers are worked out of
the code where the definition is evaluated, by the emitter too; that they
cover what the code writes is a theorem about every code
(`Clear.of_keeps`), not a check of each function.

**Selective.** The analysis's result is the granules `ks` (`doneG W r ks`),
checked by `⟨_, by taint_decide_ct⟩`; `verifiedScrubbedSel` pairs
`RTaintG.Verified.scrubSel` and `RTaintG.noResidue_scrubSel` into
`VerifiedScrubbed`, and needs the granules within the window (by
`decide`), `ScrubOk` of the contract, and the analysis (RC2's
initialization, SEED's and SM4's ECB, CAST5's modes and OFB, X25519's and
X448's exchange; `Proof/Framework/AArch64/ScrubSel.lean`). Code that zeroes
every granule of its frame but clears only the registers it states
(`withClears`) is `scrubSel W (List.range (W / 16))`, as CAST5's OFB is: the
same instructions as a whole-frame wipe, with the selective theorem.

### ARMv7

**Side conditions.** `scrub` is for code without frames (`Code.noFrames`:
it writes memory only in its buffers). `scrubAll` first zeroes the `n` bytes
of stack its contract reserves; `verifiedScrubbedAll` needs
`scrubSideF c n ts`, which `scrubSideF_of` gives from `CodeOk c n` and
`FrameOk n`, and `PostOut`. `scrubSel` zeroes, of those `n` bytes, only the
words `ws`, a store each; `verifiedScrubbedSel` needs `selSide n ws W` (by
`decide`) and the analysis of the code with its cleanup ending in `done`
(`⟨_, by taint_decide_ct⟩`). Find `ws` with `TaintCT.hint` in an `#eval`
(the bits of the final taint's `sec`, as words).

**When `scrubAll`, when `scrubSel`.** Code with frames that wipes its own
working space uses `scrubSel`. `scrubAll` stays the cleanup where the
analysis leaves most of the stack secret (code that does not wipe its own
frames: `scrubAll`'s loop of eight stores is then the shorter code), for code
that calls the functions of its tables (`TaintCT.check` has no indirect
call), and for code generic over a variant until each variant's analysis is
checked.

**Variants.** Each variant proves `CodeOk` of its own code where it is
defined (by `lit_decide`), the function proves its own shape once for any
variant (`CodeOk.call`, `CodeOk.seq`, `CodeOk.alloc`, …), and
`scrubSideF_of` joins them.

### RISC-V64

**Side conditions.** `verifiedScrubbedAll` needs `scrubSide c W rb ts` (by
`lit_decide`), `verifiedScrubbedSel` needs `selSide fs W rb` (by
`lit_decide`) and the analysis of the code with its cleanup
(`⟨_, by taint_decide_ct⟩`); both need `PostOut`.

**Variants.** Each variant states, as a field proven where it is defined,
the depth of its code's frames and that it calls nothing indirectly
(`HVar.scrub`, by `lit_decide`; `RoundImpl.stack` and `RoundImpl.icalls`);
the function's code with a stub in the variant's place (`holeStub k`, or
nothing where it calls through a table) is evaluated once
(`scrubSide … = true`, `lit_decide`), `fill_calls` proves `Fill` from it to
the code with any variant, and `RISCV64.Scrub.scrubSide_of_fill` joins them
(`Proof/Framework/RISCV64/ScrubCall.lean`; `Proof/RsaKeyGen/RISCV64/Fn.lean`,
and `sign_fill` in `Proof/Ecdsa/Rfc6979/RISCV64/Scrub.lean` for calls
through tables).

### PPC64LE

**Side conditions.** `verifiedScrubbedAll` needs `scrubSide c d rb cl ts` (by
`lit_decide`), `verifiedScrubbedWiped` needs `wipedSide` (by `lit_decide`);
both need `PostOut`. The wiped form's frame region leaves out the frame's
header, so it needs less than x86's.

**Variants.** Its one interface with variants, `MillerRabin`, has only a
baseline (`Proof/Variants/MillerRabin/PPC64LE.lean`), and its callers' code
is evaluated with it; `Proof/Framework/PPC64LE/` has no join lemma: a
second variant would need one, as RISC-V's `scrubSide_of_fill`.
