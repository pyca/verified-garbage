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
   A function also proves that it returns without secret residue
   (`TCB/<ISA>/Residue.lean`), as part of what its registration proves:
   `verified := .scrubbed h`, of an `h : VerifiedScrubbed …`
   (`TCB/Registration.lean`). Its cleanup is part of its code. The
   function as emitted, its body and then the instructions that clear the
   registers it wrote and zero the stack it used, is a named definition in
   `Impl/`, which states those registers and that stack as literals; one
   theorem in `Proof/` states `VerifiedScrubbed` of that definition; and
   the registration file binds the two: `code := Impl.…`,
   `verified := .scrubbed (Proof.… )`, with no call of a scrub wrapper or
   form, no register list, no side condition and no tactic in it
   (`Fn` in `Impl/Sha3/AArch64/Instances.lean`,
   `Proof/Sha3/AArch64/Scrub.lean`, `Artifacts/Sha3/AArch64.lean`).
   Nothing is worked out of the code when the emitter runs: it only
   prints, and the kernel has checked what the cleanup needs of the code
   (`scrubSide … = true`, by `lit_decide`) when the proof module was built.
   For code generic over a variant, the registers are the function's own
   joined with those the variant states it writes (`Clear.union`,
   `Callee.clear`); each variant proves that of its own code where it is
   defined, as a field of the variant structure (`Permutation.scrub`, by
   `lit_decide`), the function proves its own instructions once, and a
   lemma joins the two (`AArch64.ScrubAll.scrubSide_union`): never a proof
   over the list of variants, which evaluates every variant's code again
   for every caller, and never `variants.attach` in a registration file.
   On AArch64 the cleanup is `Impl.Residue.AArch64.scrubAll` and the
   theorem comes from `AArch64.ScrubAll.verifiedScrubbed`
   (`Proof/Framework/AArch64/ScrubProved.lean`).
   On a target whose `Proof/Framework/` does not yet state its scrub as a
   theorem about named code, build the registration in `Proof/` with that
   target's form and let the registration file bind it by name, never
   call the form there. On x86-64, build its
   registration in `Proof/` and scrub it with `X86_64.Scrub.scrubReg`,
   whose code clears what the residue analysis (`X86_64.RTaint`) finds may
   hold secrets and which gives that proof; the registration file binds the
   result. On ARM, a function without frames (`Code.noFrames`: it writes
   memory only in its buffers) is scrubbed with `Arm.Scrub.scrubReg`
   (`Proof/Framework/Arm/Scrub.lean`), which sets the registers a callee may
   change, but the result, and the flags to constants; one with frames
   with `Arm.Scrub.scrubRegF`, which first zeroes the stack its contract
   reserves, given that its postcondition reads the memory on return only
   within its buffers (`Arm.Scrub.PostOut`, by `postOut_of_local`); that stack
   is a frame of the model, a multiple of 8 bytes (`FrameOk`), so code proven
   with another number is registered with the next one
   (`Arm.Scrub.Verified.stack_le`, as `Proof/MlDsa/Arm/Scrub.lean` does).
   Only functions `ci/residue_allowlist.txt` already lists may go
   without (`verified := .unscrubbed h`, of an `h : Verified …`): the list
   only shrinks (`ci/check_residue_allowlist.py`), and the
   emitter refuses a listed function that has a proof, so converting one
   removes its line. Where the analysis fails, its trace says at which
   instruction (an index it cannot bound, a value reloaded after a store it
   cannot place): change the code so it can, as the Merkle–Damgård
   streaming code clamps its indices, and ChaCha20's `apply` keeps the data
   and its length in `r14` and `r15` and takes its state back from the
   buffer `vg_chacha20_xor` returns. Code the analysis does not follow at
   all (RSA's private-key functions, most of whose pointers and lengths
   are arguments on the stack) is scrubbed with
   `X86_64.Scrub.withScrubAll`, which wipes all the stack its frames and
   calls use and needs only that its postcondition reads the memory on
   return in its buffers alone (`PostOut`); its level `evex` also clears
   `zmm16`–`zmm31` and MXCSR's status flags, for code that writes those.
   Code with no VEX or EVEX instruction, no frame and no call is scrubbed
   with `X86_64.RScrub.withScrubXs`, which clears only the SSE registers
   its instructions may write and wipes no stack, and keeps what the
   registration states of `written`: keep such code's secrets in few
   registers (AES-CBC's AES-NI encryption loads each round key from the
   schedule as its round uses it).
   It leaves a function as it is when the clearing would need a CPU
   feature the function does not: one that needs no AVX and may run an AVX2
   hash function through a table it takes (`vg_rsa_pss_sign`,
   `vg_rsa_oaep_decrypt`).
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
