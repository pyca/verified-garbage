# RSA x86 implementation handoff

The requested scope is **i686/x86 support for every RSA table row, one PR per
row**. This branch is a work-in-progress handoff of the encryption row. The user
explicitly requested pushing unfinished work so another agent can take over.
Do not interpret this branch as a completed or fully verified decryption API.

## Branches and completed PRs

| Row | Status | Branch / PR |
| --- | --- | --- |
| RSA core | Ready, CI and scoped x86 benchmark passed | `codex/rsa-x86`, [PR #2757](https://github.com/pyca/verified-garbage/pull/2757) |
| PKCS #1 signatures | Ready, CI and scoped x86 benchmark passed | `codex/rsa-pkcs1-sig-x86`, [PR #2833](https://github.com/pyca/verified-garbage/pull/2833) |
| PKCS #1 encryption / implicit rejection | Encryption complete; decryption proofs in progress | **`codex/rsa-pkcs1-enc-x86`**, this branch; no row PR yet |
| OAEP | Pending | Separate row PR required |
| PSS | Pending | Separate row PR required |
| Key generation | Pending | Separate row PR required |

The encryption branch is stacked on signatures commit
`3b0eb2030e1d54ad08cb7ff554a363cb0e9dd5ea`, which includes core commit
`612b60b2a04d9ebbe2ac28f7f213367445afc2da`. PR #2833 targets `codex/rsa-x86`.
The eventual encryption PR should target `codex/rsa-pkcs1-sig-x86` while that
stack remains open. Check current upstream status before changing the stack.
PRs are squash merged: use the repository's `rebase --onto` instructions when a
base merges. **Do not work on the cancelled check-key detour / PR #2807.**

Completed PR validation:

- Core CI: https://github.com/pyca/verified-garbage/actions/runs/39170575157
- Core benchmark: https://github.com/pyca/verified-garbage/actions/runs/39170334539
- Signature CI: https://github.com/pyca/verified-garbage/actions/runs/39175930239
- Signature benchmark: https://github.com/pyca/verified-garbage/actions/runs/39175946075
- Signatures additionally passed all three i686 Wycheproof signature tests and
  4,958 independent QEMU differential cases, including signing at every byte
  width from 64 through 1,024.

## Commits on this row

- `f2dfcd64b`: complete verified encryption, artifact and generated x86 assembly.
- `f40631d88`: compiling decryption implementation and proofs through complete
  SHA-256, KDK derivation and both IRPRF loops, plus the separator scan.
- The handoff commit after those includes the latest alternative-length proof
  work and this document. Some of that final proof work does not compile yet;
  see the diagnostics below. There are no proof placeholders or trust changes.

## Encryption entry point: complete

`Proof/RsaPkcs1Enc/X86/EncryptStackSafety.lean`, namespace
`VG.Proof.RsaPkcs1Enc.X86.Enc`, proves `encrypt_verified` against the existing
`encryptPrecomputedContract`, including correctness, memory safety, ABI,
constant time and satisfiability. `Artifacts/RsaPkcs1Enc/X86.lean` registers this
entry point only, with the signature row's verified public RSA instance.

The complete x86 artifact audits and emitter passed. The generated
`src/asm/x86/rsa_pkcs1_enc.rs` contains **encryption only**. 519 independent
QEMU encryption differential cases passed: 21 Wycheproof keys, message length
boundaries, zero-padding rejection, rejected exponents and representative
non-limb-aligned widths through 1,024 bytes, guards and immutable inputs.

Rust module/test/benchmark architecture gates and the algorithm table have
**not** been enabled for the row. Finish decryption and the row's complete
verification before advertising support or opening its completed PR.

## Decryption implementation and proved stages

Implementation: `Impl/RsaPkcs1Enc/X86/Decrypt.lean`. Proof namespace:
`VG.Proof.RsaPkcs1Enc.X86.Dec`. Decryption is **not registered or emitted**.

The implementation uses the existing checked CRT private RSA and SHA-256/HMAC
scratch APIs. It is generic over `Proof.Sha256.X86.Variants.Backend`; do not bind
it to a baseline-only hash implementation. The eventual registry should be
`Generic/Sha256/RsaPrivateCrt/X86/RsaPkcs1Enc.lean`, following both interfaces.
Rust selection must exhaustively match the SHA-256 and private CRT backends.

Main proved components, all included in `f40631d88`:

- `DecryptPrivate{Args,Regions,Pre,Call}`, `DecryptCall{,Public}`: checked private
  RSA call, memory geometry and its public leakage.
- `DecryptD{Args,Clear,Copy}`: pad the full private exponent to modulus width.
- `DecryptHash{Init,Update,Finalize,...}`, `DecryptHashD`: full three-call proof
  that `DH = SHA256(D)`, where D is the padded exponent. Connect D to the shared
  `Steps.i2osp_os2ip_pad` lemma when composing the final body.
- `DecryptMac{Init,Update,Finalize,...}`, `DecryptKdk{,Update}`: full proof that
  `KDK = HMAC-SHA256(DH, ciphertext)`.
- `DecryptMessage*`: exact public PRF messages, counter/label/two-byte bit length.
- `DecryptPrf{Address,Pointer,FinalizeArgs,Mac,Body,Step,Loop,...}`: complete
  individual HMAC blocks and finite loops, preserving KDK and earlier output.
- `DecryptPrfComplete`: both `clLoop_ok` (8 blocks) and `amLoop_ok` (ceil(k/32)).
- `DecryptPrfOutput`: exact truncation matches the existing `Spec...irprf`.
- `DecryptRejectionFrame`: PRFs preserve encoded RSA output and saved status.
- `DecryptScan{Step,Loop}`: complete constant-time first-separator byte scan.
- `DecryptBlocksTiming`: standalone scan, alternative-length, selection and mask
  loop timing proofs; **not** the entire decryption constant-time certificate.

Useful layout details (existing spec requires at least 8,448 scratch bytes):

- Wrapper frame: 160 bytes; saved registers: 16; callee reserve: 3,372.
  Intended complete stack bound: 3,548 bytes.
- Outgoing cdecl arguments occupy bytes 0..79. Saved status `oR=80`, counter
  `oI=84`, block count `oNB=88`, AL=92, mask=96, valid mask=108, OK mask=112,
  cutoff=116. The 8-byte message-length output has its own disjoint region.
- Scratch: inner SHA state 0..95, outer state 96..191, PRF message at 192,
  DH at 208, KDK at 240, CL at 272 (256 bytes), AM at 528 (up to 1,024),
  padded d at 1,552 (up to 1,024), hash working area at 3,072 (832 bytes).
- SHA scratch contracts allow 608 bytes; HMAC allows 832. SHA update/finalize
  verified proofs are rebound via reviewed `Shared.*Wide_of` / `*Wide_implies`
  helpers to the public scratch contracts.
- `rejectionWrites` is deliberately precise: workspace, callee reserve,
  outgoing arguments, counter and block-count slots; it excludes saved status.
- The current x86 ISA model supports `shr` and `ror`, not `shl`. Left shifts
  use repeated additions. Do not change the TCB to avoid proving these.

## Latest alternative-length proof work

New files after `f40631d88`:

- `AltLength.lean`: architecture-independent candidate bounds and arithmetic
  selection helpers, kernel checked.
- `DecryptMask{Step,Loop}.lean`: mask-building loop proved to compute
  `2^bitLength(k-11)-1`; targeted build passed.
- `DecryptAlLoad.lean`: two-byte big-endian candidate loading by repeated
  doubling; targeted build passed.
- `DecryptAlStep.lean`: branchless candidate-selection step; targeted build passed.
- `DecryptAlLoop.lean`: WIP fold of all 128 candidates. **Currently fails with
  the standard 200,000 heartbeat limit around lines 44–45**, when elaborating
  the second readable-byte proof in the `alBody_ok` call. Split the argument
  proofs into explicitly typed local lemmas and normalize the second address
  `(base + ofNat(2*i)) + 1` to `base + ofNat(2*i+1)` before applying `read`.
  Do not increase any proof resource budget. Further goals may appear afterward.
- `DecryptAlArgs.lean`: mask and candidate-loop setup; targeted build passed
  in the final handoff validation (`/tmp/vg-rsa-enc-handoff-verified.log`).
- `Impl/.../Decrypt.lean` now factors `alLoad` out of `alBody`. This preserves
  the instruction sequence. No decryption assembly has been emitted.

Then complete alternative-length composition (`maskInit`, mask loop, `alInit`,
128-candidate fold, saved AL), `validCalc` and message-length writes, and the
masked output-selection loop. Compose the full decryption body, ABI, contract,
constant-time, satisfiability, stack safety and generic registration.

## Validation and working environment

Last compiling checkpoint: all then-current new modules built together in
**1,536 Lean jobs** (`/tmp/vg-rsa-enc-decrypt-checkpoint3.log`). Imports, module,
registration and proof-speed static checks passed. That checkpoint predates the
final alternative-length WIP. Its mask, byte-load, candidate-step and setup
proofs pass targeted builds; only `DecryptAlLoop` is currently known to fail. Full row
Rust checks, end-to-end decryption tests, complete artifact audits and scoped
benchmark are still required after finishing the API.

The current worktree is `/workspace/verified-garbage-rsa-pkcs1-enc`. Other local
worktrees: `/workspace/verified-garbage` (core) and
`/workspace/verified-garbage-rsa-pkcs1-sig` (signatures). They share a `.lake`
cache; do not duplicate it. Environment commands:

```sh
export ELAN_HOME=/workspace/.vg-tools/elan
export PATH=/workspace/.vg-tools/elan/bin:/workspace/.vg-tools/cargo/bin:$PATH
export LEAN_NUM_THREADS=6
# Run from this worktree's lean directory:
lake build --log-level=warning +VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptAlLoop
lake build --log-level=warning +VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptAlArgs
```

Local diagnostics: `/tmp/vg-rsa-enc-alloop2.log`,
`/tmp/vg-rsa-enc-alargs.log`, `/tmp/vg-rsa-enc-alload2.log`,
`/tmp/vg-rsa-enc-maskloop2.log`. The final handoff validation logs are named
`/tmp/vg-rsa-enc-handoff-*`.

Read `CLAUDE.md` and `lean/README.md`. No `sorry`, `admit`, `native_decide`,
`bv_decide`, new axioms, Spec/TCB edits, cross-architecture implementation/proof
imports, hand-edited assembly or increased proof budgets. Pure shared lemmas
and same-target proof reuse are allowed. Warnings are errors.

Before pushing a completed implementation follow all repository checks,
including full Lean, emitter audits, Rust/bench format and Clippy, host/i686
unit and Wycheproof tests, architecture/variant/coverage gates and table
regeneration. This handoff push is explicitly authorized unfinished work.

On this host the all-target emitter exceeds `vm.max_map_count`; the existing
`.lake/emit/EmitX86.lean` and `EmitArm.lean` wrappers run complete per-architecture
emission/audits. **Build changed artifact targets first**; the wrappers do not
build them. Check other architectures' assembly is unchanged. Regenerate the
wrapper/driver inputs if changing worktrees. Use existing i686 QEMU Docker image
`vg-rsa-qemu:local`; this host cannot directly execute 32-bit ELF. Raw harnesses
are outside the repository in `/workspace/.vg-tools/rsa-i686/`, including
`pkcs1_encrypt*.{rs,py,txt}` and signature equivalents. Preserve inherited proxy
and CA settings for any network or Docker use; read the cloud runtime skill.

Root Cargo target cache: `/workspace/verified-garbage/target`; set
`CARGO_INCREMENTAL=0` to conserve disk. Rust toolchains live under
`RUSTUP_HOME=/workspace/.vg-tools/rustup` and `CARGO_HOME=/workspace/.vg-tools/cargo`.

`gh pr edit` fails against classic Projects here; update PR bodies with
`gh api --method PATCH ... --input <json-file>`. `gh pr ready` works.
Do not fetch Actions logs through blocked signed Azure blob redirects; use
check-run annotations, workflow status and local reproduction instead.
