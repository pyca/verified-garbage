---
name: adding-a-primitive
description: "Use before adding a new primitive or algorithm, a new target for one, a CPU-feature variant, or any file under lean/VerifiedGarbage/Artifacts/, Generic/ or Variants/: the steps, what a registration states, and how generic callers and variants are registered."
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
   `crates/verified-garbage-asm-<target>/src/`, ARM's `asm/`) and name, its signature, its contract on every target
   (`contracts := some fun A stack => fooContract A stack`, or
   `fun A _ => fooContract A` for a contract without `stack`), its
   contract's `writeArgs`, and its documentation: what it does, and the `# Safety` items but for what
   the emitter generates (what memory each buffer must be valid for:
   `Sig.validDoc`; which buffers may not overlap each other, the stack or
   the arguments on it, and that none wraps around the address space:
   `Sig.layoutDoc`). Choose
   `pub` honestly: only lengths and pointers are public unless the algorithm
   says otherwise.
2. `Impl/<Alg>/<Target>.lean`: the code.
3. `Proof/<Alg>/…`: the proof of `Verified`. A proof may be written against a
   simpler per-target contract of its own and moved to the shared one with
   `Verified.of_implies` (see `Proof/Framework/Contract.lean`).
4. An `Artifact` in the registration file `Artifacts/<Alg>/<Target>.lean`,
   which defines `VG.Artifacts.<Alg>.<Target>.artifacts` (a new file for a
   new algorithm or target; see `Artifacts/Selftest/X86_64.lean`), made
   from the function's `Api` by `Api.artifact` (`TCB/Registration.lean`),
   with the file importing
   `Proof/Framework/Registration.lean` for its default proofs:

   ```lean
     Spec.<Alg>.fooApi.artifact X86_64.target {
       stack := 8
       code := Impl.<Alg>.X86_64.foo
       verified := Proof.<Alg>.X86_64.foo_verified },
   ```

   A registration states only what the implementation chooses: the Rust
   module, name, signature, `writeArgs`, documentation and contract come
   from the `Api`, so never restate them. Give a variant's name its
   `suffix` (`suffix := "_avx2"`), the stack its calls and frames use in
   `stack`, the tables of constants it reads in `consts`, and, where a caller wipes a
   writable array the function uses as working space, how much of it the
   function writes in `written` (`written := [("scratch", 1024)]`, proven by
   `writtenOk`), which the emitter exports as `<NAME>_<PARAM>_WRITTEN` for
   the caller to wipe only that much. Its contract is found
   from `verified`'s type, and must be the `Api`'s on the target for
   `consts` and `stack` (`ofApi`, by `rfl`): give `contract` only when
   `verified`'s type does not determine it. `of_sig` proves `ofSig`, and
   `sp_safe` proves `spSafe`: by `Code.all_of_forall` on ARMv7, AArch64 and
   PPC64LE,
   which evaluates nothing, and by `Code.all_of_allInstrs (by lit_decide)`
   on x86 and x86-64 (see "Code the kernel evaluates" in the
   `proof-performance` skill), falling back
   to `decide +kernel` where `lit_decide` exceeds the recursion limit, and
   for code that depends on a `Bool` or an enumeration (`adx`, a field
   variant), by cases on it. Never set
   `contracts` outside `Spec/` (the emitter refuses an artifact without
   them). If its code uses instructions outside
   the target's baseline ISA, list the CPU features they require in
   `features` (the emitter rejects anything but the exact set).
   A function that calls another one with several implementations (e.g.
   scalar and SHA-NI compression) is proven once for any of them and
   registered in `Generic/<Iface>/<Target>/<Alg>.lean`, which the emitter
   applies to every implementation in `Variants/<Iface>/<Target>/` (see
   `TCB/Emit.lean`), and so is a function that calls a generic caller
   (e.g. HMAC's `init`, calling SHA-256's `update`). A function that calls
   functions of several such interfaces is generic over all of them, in
   `Generic/<Iface₁>/…/<Ifaceₙ>/<Target>/<Alg>.lean`, whose `artifacts`
   takes a variant of each, in path order: the emitter applies it to every
   combination (e.g. Argon2's x86-64 derivation,
   `Generic/Blake2b/Argon2Compress/X86_64/Argon2.lean`, calling BLAKE2b's
   streaming functions and Argon2's `G`). Its instances are named by
   `Emit.qualifiedName`: the function's name, then a tag and the suffix of
   each interface whose variant is not the baseline, in path order
   (`vg_argon2_blake2b_avx2_g_avx512`; `vg_argon2` for the baseline),
   since variants of different interfaces may share a suffix; callers of one
   interface append the suffix alone. Never list the
   implementations in the caller: a new implementation is a new variant
   file, and its callers follow.
   Registration files (`Artifacts/`, `Generic/`) and variant files
   (`Variants/`) are reviewed by hand, so they only bind: no theorems, no
   tactic proofs beyond the defaults (not even a `(by decide)` argument),
   no definitions but the artifacts and the variant, and no module
   docstring but its title (`/-! # SHA-256 (FIPS 180-4) on x86-64 -/`):
   what the code does is in the code and its proofs. A lemma
   whose side conditions a registration would decide takes them as
   `autoParam`s (`(hd : stackUse c ≤ 48 := by lit_decide)`), or the
   algorithm's proofs state the instance as a theorem
   (`Proof/Rsa/X86_64/Instances.lean`); `ci/check_registrations.py` checks
   it. Build a variant with its proofs under `Proof/`
   (`Proof/Variants/<Iface>/<Target>/<Name>.lean`, as the variant file's
   path) and bind it in the variant file
   (`def variant : … := Proof.Variants.<Iface>.<Target>.<Name>.variant`);
   put what a generic caller's artifacts are built from (instances of the
   functions it calls, lemmas about its code) in a module of the
   algorithm's proofs, as `Proof/AesGcm/X86_64/Instances.lean` does.
   A function whose proof takes a Weierstrass curve's group law (`Law`,
   `Proof/Weierstrass/Law.lean`) is registered generic over it the same
   way: the law is the one variant of the interface `<Curve>` on each target
   (`Variants/<Curve>/<Target>/Law.lean`, the only files that import the
   Mathlib algebra of its proof), and the registration file is
   `Generic/<Curve>/<Target>/<Alg>.lean` (`Generic/<Iface>/<Curve>/<Target>/`
   when it is generic over an implementation too). The law has no suffix.
5. Regenerate the generated crates, build the public Rust API on top of the primitive,
   and test it against the Wycheproof vectors in `tests/wycheproof/` (set
   `WYCHEPROOF_ROOT` to a checkout of C2SP/wycheproof). Benchmark the new
   API in `bench/benches/primitives/<alg>.rs`, next to the same operation in
   OpenSSL, at the sizes the others use.

## What `ci/check_variants.py` checks

`ci/check_variants.py` checks the generated code: each caller of a
function with a variant has that variant, which calls it or does its work
itself but never calls the baseline (a helper needs none if its callers'
variants all do its work themselves), some implementation of each caller
calls every implementation of its callee whose features the caller has
but the one it calls lacks (a variant chosen by hand, such as a field
naming the callee, still follows the features), and each variant is used by the
Rust code outside its tests (never emit one only a test calls).
