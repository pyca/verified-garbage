# x86 DSA parameter generation: work-in-progress handoff

## Goal and completion criterion

Original request: **“x86 dsa implement parameter generation. Submit a PR once it is as fast or faster than OpenSSL. Keep duplication to a minimum so reuse existing optimized implementations where possible.”**

This is 32-bit x86 (i686), not x86-64. Finish the existing DSA parameter-generation specification without weakening its contract, reuse optimized hash/Montgomery/RSA arithmetic implementations, propagate all backend variants, prove correctness and required timing/ABI properties, emit assembly, wire Rust dispatch and tests, and measure native x86 parameter generation against OpenSSL. Only open the requested PR after performance parity and the required checks. This checkpoint is incomplete and makes no performance claim.

Branch: `x86-dsa-paramgen`. Starting commit: `fad6ec1d4` (Split slow DSA, secp256k1, and SM4 tests into independent batches (#3008)). The user explicitly requested committing/pushing the unfinished work so another session can take over. No PR has been opened.

## What is implemented and individually proved

- Complete optimized x86 Miller–Rabin round and streamed witness loop, with exact unchanged randomness-tape semantics. Reuses existing optimized runtime Montgomery multiplication and symmetric squaring; no duplicated arithmetic kernels. Generic and variant registration for the standalone round, emitted x86 assembly and raw Rust MR tests exist.
- Early packed-prime trial division (reuse RSA table and arithmetic), full probable-prime stage, preparation/encoding/sampling, and exact tape cursor threading.
- Complete subgroup q candidate hashing/shaping/primality pipeline, generic over the existing SHA backends.
- Complete p construction: wrapped seed hash contributions, shaping, shared runtime reduction, serialization of p and generator exponent (p-1)/q.
- Complete single p attempt: construct p, reject undersized candidates without consuming witnesses, otherwise probable-prime test. Exact specification and preserved p/exponent outputs proved.
- Native bounded p-search controller exists. The counter/offset increment block is proved (`PSearchAdvanceHead`); the full controller proof remains unfinished.
- Shared pure MR/word/hash math extracted from architecture-specific proofs with old wrapper lemmas retained. Core.store generalized to Core.storeAt; old Core.store remains an alias with the same instructions. No Spec/TCB changes, proof escapes, or proof-budget increases intended.

Main code: `lean/VerifiedGarbage/{Impl,Proof}/Dsa/X86/Generation/`, `.../{Impl,Proof}/MillerRabin/X86/`, `Generic/MillerRabin/X86/`, `Variants/MillerRabin/X86/`. Audit module: `lean/VerifiedGarbageTest/MillerRabinX86.lean`. Standalone MR emitted code: `src/asm/x86/miller_rabin.rs`; tests: `src/dsa/miller_rabin_tests.rs`. Whole parameter generation is not emitted or exposed yet.

## Immediate next step

Continue the bounded p-search proof, then generator search, outer seed loop, final validation/packing/output, ABI/timing proofs, full generic registrations, Rust architecture/backend dispatch, tests, emission, checks, and native benchmarks.

1. Prove `PSearchAdvance`: compose `p_search_advance_head` with status write. Increment index and offset; status is 3 if index+1 < limit, otherwise 2. Precise frame: index/offset/status words; clobbers EAX/ECX.
2. Prove `PSearchStatusCmp` (loads status and compares with 3), and `PSearchInit` (index=0, offset=1).
3. Prove full controller against shared `VG.Proof.Dsa.Generation.primeSearch`, its start/step/done lemmas. Limit=256*n=4*L, L=64*n, stride=(64*n-1)/(8*H.D)+1. Termination measure limit-index. Reject undersized p without consuming tape; preserve advanced witness tape across composite retries. Status 0=tape exhaustion, 1=accepted, 3=retry, 2=bounded search exhausted.
4. Keep encoded p and exponent from `PAttemptResult` on accepted exit. Preserve q and external seed tape throughout. The full generator/outer/output pipeline is still absent.

## Important current layout (supersedes historical notes)

`Impl/Dsa/Generation/Layout`: parent=0 (14720 bytes), hash=16384 (8192), wrappedSeed=24576 (32), hashes=24640 (384), shaped=25024 (384), q=25408 (32), p=25472 (384), exponent=25856 (384), g=26240 (384), witness=26624 (384), packed=27008 (800), control=27840 (512), arithmetic=28672 (12288), domainCheck=40960. Workspace usedBytes(pLen)=40960+128*pLen (maximum 90112).

**Newest metadata relocation:** seedPointer=packed+512=27520; candidateOffset=packed+528=27536; pIndex=packed+532=27540. They previously lived in control; historical journal entries naming control+48/+64/+68 are stale. Borrowing the final-output buffer keeps search metadata outside the MR SampleRoundFrame, avoiding stronger inner-loop contracts. Packing must happen after search. Eventual outer retry state must survive final packing, e.g. in the root stack frame.

Witness controls: roundIndex=control+8, uniformCount=control+12, primeStatus=control+20, witnessCursor=control+32, witnessRemaining=control+36, witnessUniform=control+256. MR uses status 4 internally for continuing rounds.

Compact MR: width=48, inverse=56, header=64+8*j; arrAt n j=256+j*8*(n+2), 28 arrays. RR is array7, not4 (array4 is borrowed scratch). round stack1172, caller room1184. Runtime RSA array slot=160+j*4*(words+2), with words=2*n: stride is 8*n+8, not 8*n+4.

`ConstructionFrame` excludes q/witness/control/packed/g. `AttemptFrame` combines parent, hashes/shaping, p/exponent, arithmetic, witness, control, and stack1184; excludes q and packed metadata. `attempt_metadata` and `p_hash_metadata` prove packed metadata preserved. `PrimalityResult` has a precise SampleRoundFrame; `PrimeObservation` is a coarser convenience, while `PAttemptResult` retains the precise AttemptFrame and exact encoded p/exponent.

## Verification status and honest limits

Previous completed targeted Lean builds included: full MR/primality/subgroup; PHashes/PShape; PConstruct; PTest/PAttempt; metadata relocation foundations; PSearchAdvanceHead. Last counter-block build completed successfully (`/workspace/scratch/dsa-psearchadvancehead.log`). Shared DSA X86 artifact/CoreStoreTiming regression built successfully after alias unfolding was fixed. Audit test last passed at PShape (2062 targets), including x64 PShapeValue regression; audit imports later include PConstruct, but newest PTest/PAttempt/PSearchAdvanceHead assertions still need adding and rerunning. Earlier shared ARM/RSA regression builds passed.

Full repository build, full emitter comparison, all public-import checks, full Rust coverage and integration testing have **not** been completed for this checkpoint. Some public-import checker fixes were reverted in ProbablePrime/LoadCandidate/CheckCandidate because explicit dependencies were missing; rerun and resolve. Newer modules have not all been checked. Generated whole-parameter APIs and benchmarks do not exist yet. No end-to-end parameter generation result or native OpenSSL performance comparison exists.

Read AGENTS.md and lean/README.md before continuing. All assembly must be emitted from Lean; no hand edits in src/asm, no sorry/admit/native_decide/bv_decide/new axioms, no Spec/TCB weakening or budget increases. Keep 100% Rust coverage and complete backend-variant propagation. Full validation remains required before a completion PR; this user-requested WIP snapshot is for transfer.

## Environment and commands

On the existing workspace:

```sh
export ELAN_HOME=/workspace/.vg-tools/elan
export CARGO_HOME=/workspace/.vg-tools/cargo
export RUSTUP_HOME=/workspace/.vg-tools/rustup
export PATH=/workspace/.vg-tools/cargo/bin:/workspace/.vg-tools/elan/bin:$PATH
cd /workspace/verified-garbage/lean
lake build --log-level=warning +VerifiedGarbage.Proof.Dsa.X86.Generation.PAttempt +VerifiedGarbage.Proof.Dsa.X86.Generation.PSearchAdvanceHead
```

Wait for build completion and inspect the log tail before claiming success. An early grep with no errors is not evidence that a running build passed. Use targeted builds while iterating; the full tree has thousands of modules.

The host is x86-64 Zen5. Native i686 execution was previously unavailable; raw MR correctness was tested using QEMU with local cross toolchain:

```sh
CARGO_TARGET_I686_UNKNOWN_LINUX_GNU_LINKER=/workspace/scratch/x86-toolchain/cc \
CARGO_TARGET_I686_UNKNOWN_LINUX_GNU_RUNNER=/workspace/scratch/x86-toolchain/qemu/usr/bin/qemu-i386 \
cargo test --release --target i686-unknown-linux-gnu --lib dsa::miller_rabin_tests -- --nocapture
```

QEMU is not acceptable performance evidence. Use narrowly scoped native Benchmarks workflow (arch=x86, modules=dsa_parameters, openssl=true), with all supported configurations and representative sizes, once the API is implemented. Consult current AGENTS/workflow inputs; avoid cherry-picked reruns. Apply available optimization-review skill at the performance stage.

A custom audited emission workaround existed for vm.max_map_count: `/workspace/scratch/EmitX86Driver.lean`, `lean/.lake/emit/DriverX86.lean`, `/workspace/scratch/x86.targets`, `/workspace/scratch/build-x86-artifacts.sh`. These scratch/cache files are not part of the portable checkout; use the supported emitter when possible. The older commands are in the historical journal.

`x86-dsa-paramgen-history.txt` preserves the development journal for deeper context. It is historical, contains stale intermediate statuses/offsets, and this document takes precedence. Scratch logs/toolchain caches survive only if this workspace survives; do not depend on them in a new environment.

Checkpoint revalidation: targeted PAttempt + PSearchAdvanceHead build completed successfully (1933 jobs); `ci/check_lean_imports.py`, `ci/check_lean_modules.py`, and `git diff --check` passed immediately before this snapshot. The full pre-push suite was not rerun for this explicitly requested unfinished handoff checkpoint.
