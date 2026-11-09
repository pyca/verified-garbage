# ppc64le bignum workstream notes (session_01TKUFHJXsbSLv5iKkv86b9U)

Coordinator: session_01TKUFHH1um6BHmQjMB1jTPh (send short messages via mcp__claude-code-remote__send_message).
P-521 session (owns vmsumudm TCB PR + POWER9 CPU-feature path): session_01TKUFHH4GefHP3pmPRSL4N4.

## State (2026-11-09 22:30)
- Merged: #4824 (montOp calls ONE shared kernel `vg_rsa_mont_kernel` = MontMul.kernel, via `bl`).
- Dropped after prototypes: unroll-by-8 (branch range), 4+2/1 remainder (~1%), two-row FIOS (~7%), dedicated squaring (7-21% slower).
- Gaps vs OpenSSL on POWER9 (run 42643922871): RSA sign 1.9-2.1x, verify 1.4-2.0x, recover 1.6-1.7x;
  DSA verify 2.1-2.3x; x86-64 is ~0.7-1.2x for the same. Gap = kernel. OpenSSL ppc64 uses FP/vector units.

## Round 3 task
SCOPE CHANGE (alex): POWER8 baseline (ISA 2.07) only, no CPU-feature work: (ii) vmsumudm DROPPED.
Missing ISA 2.07 vector adds (vaddudm, vadduqm, vaddcuq, vaddeuqm, vaddecuq) may go in a TCB PR,
coordinated with the P-521 session, which needs the same ones.
Prototype a vector-unit Montgomery kernel, 2 versions, each measured vs main with openssl=true in ONE job:
 (i) POWER8 vmuleuw/vmulouw (already in the ISA model), 32-bit limbs in 64-bit lanes, deferred carries;
 (ii) POWER9 vmsumudm (64x64 multiply-sum into 128 bits).
Proceed only if >= 15% on RSA sign. If (ii) wins: coordinate with P-521 session (they add vmsumudm to TCB).
If (i) wins: plain impl PR replacing MontMul.kernel.

## Kernel interface (internal function vg_rsa_mont_kernel, called by montOp with bl)
Entry: r3 = y = -m^-1 mod 2^32 (low 32 bits), r4 = 2w (w = words), r5 = o base, r6 = a base, r7 = b base,
r8 = T (accumulator, array 2, w+2 words), r9 = tmp (array 3, w+2 words, contiguous right after array 2),
r10 = m base, r14 = caller's saved LR value (must be preserved), LR = return address.
Exit: [o] = a*b*R^-1 mod m (fully reduced, < m), r11 = 2w, r12 = y, r14 unchanged.
Must preserve: r1, r2, r13, r10, r21, r23-r31, r29 (callers' live regs). May clobber r0, r3-r9, r11, r12, r14-r20, r22
(restore r11, r12, r14 as above). Vector regs: check which are volatile (v0-v19 volatile in ELFv2; v20-v31 nonvolatile).
o may equal a or b. a/b may be array 3 in principle (prototype ignores). w may be odd (2049-bit keys -> w=33).

## Prototype mechanics (worked before)
- Branch: `git checkout -b bench/ppc64le-<name> origin/main`; replace the naked_asm! body in
  crates/verified-garbage-asm-powerpc64le/src/internal/vg_rsa_mont_kernel.rs with hand-written text asm
  (keep the fn signature; header comment "PROTOTYPE, never merged"). Generator scripts in scratchpad/proto/gen*.py.
- PITFALLS: `addi rX, r0, imm` reads literal 0 (r0 as RA); write `cmpldi %cr0, %rN, 0` explicitly.
- Local test under qemu (installed): harness scratchpad/proto/harness.c (calls `kern` with the interface above,
  compares to a reference Montgomery for w=2..40, half squares). Build:
  convert .base64 lines to .byte (see python in history) ; `powerpc64le-linux-gnu-gcc -O1 -o h harness.c kernel.S`;
  `qemu-ppc64le-static -cpu power9 -L /usr/powerpc64le-linux-gnu ./h`.
- Crate tests under qemu:
  export CARGO_TARGET_POWERPC64LE_UNKNOWN_LINUX_GNU_LINKER=powerpc64le-linux-gnu-gcc
  CARGO_TARGET_POWERPC64LE_UNKNOWN_LINUX_GNU_RUNNER="qemu-ppc64le-static -cpu power9 -L /usr/powerpc64le-linux-gnu"
  WYCHEPROOF_ROOT=/tmp/wycheproof; cargo test --release --target powerpc64le-unknown-linux-gnu --test tests -- rsa ffdh dsa miller
- Benchmark (GitHub MCP actions_run_trigger, workflow bench.yml, ref = bench branch):
  inputs {base_commit: <origin/main sha>, arches: "powerpc64", cpu_features: "", modules: "rsa_pkcs1_sig ffdh dsa",
  groups: "rsa_pkcs1_sign rsa_pkcs1_verify ffdh_exchange dsa_verify_q[0-9]+", openssl: "true"}.
  Read results: actions_list list_workflow_jobs -> get_job_logs(job, tail_lines ~200) -> markdown table.
- Delete bench branch after: `git push origin --delete <branch>` hangs at the remote -> ask coordinator to delete.

## Data from the P-521 session (22:43)
Its vmsumudm P-521 field multiplication was 32.6% slower than scalar (run 42713735790; llvm-mca pwr9 IPC 1.3 vs 2.9 for
scalar rows as two independent mulld/mulhdu+adde chains). It judges the POWER8 vmuleuw route worse (4x products).
Killers: VR<->GPR moves, 128-bit carry handling. It is NOT opening a vector-instruction TCB PR.
Scalar idea worth trying if the vector route fails: rows as two independent mulld/mulhdu+adde chains (#4774/#4838 style).

## Round 3 results (vector kernel prototypes)
- (ii) vmsumudm: dropped by repo owner (scope change), not built/benchmarked.
- (i) POWER8 vmuleuw/vmulouw: proto/genv.py (`python3 genv.py p8 asm|rust`; p9 path in it is unfinished/untested).
  Design: product scanning (FIPS), 26-bit limbs (n = ceil(64w/26)), a pre-shifted by 2^(26n-64w) so R = 2^64w;
  P_j = (a_j,u_j), Q_q = (b_q,m_q) as 32-bit word pairs; per 4 pairs: 4 lxvd2x, 2 vmuleuw, 2 vmulouw, 4 vaddudm
  (64-bit lanes, column sums < 2^63, no carries in vectors); per column: 3 vaddudm+vsldoi+vaddudm+mfvsrd, then a
  64-bit scalar chain (u = t*m' mod 2^26, t += u*m0, carry = t>>26), u_j stored back with std.
  Only model instructions used (lxvd2x, vmuleuw/vmulouw, vaddudm, vsldoi, vxor, mfvsrd).
  Correct: harness w=2..40 (odd, squares) under qemu -cpu power8 and power9; crate tests (rsa ffdh dsa miller) 60/60 pass under qemu power9.
  NOT benchmarked: llvm-mca -mcpu=pwr9 inner loop = 6.9 cycles / 4 pairs (RThroughput 4.5) -> 6.06 w^2 pairs
  ~ 10.4 w^2 cycles (bound 6.8 w^2) vs scalar FIOS 7.4 w^2 per mca (RThroughput 4.5; ~5 measured).
  Bound: 26-bit limbs need 6.06 pairs = 12 vector ops (mul+add) per 64x64 word-step; at 2 vector ops/cycle = 6 cycles,
  above scalar's ~5 even with zero overhead. 32-bit limbs would need 128-bit carry handling (>=3 ops/product).
  Conclusion: no POWER8 vector Montgomery kernel can beat the scalar one; drop.
- 22:5x: reported NO-GO to coordinator; offered scalar two-chain rows as optional next. Tree clean, no bench branches.

## Round 4: scalar 4-chain blocked rows (coordinator: mca first, prototype if >=15%, prove only if measured >=15%)
- mca pwr9: current unrolled loop (cur4.s) 28 cyc/4 words; blocked 4-chain (blk4.s) 21 cyc/4 words (-25%).
- proto/gen4c.py (`asm|rust`): FIOS, words 1..w-1 in blocks of 4 (+ one 1..3 remainder block), chains lo ab / hi ab /
  lo um / hi um, each CA saved in a GPR (addze c,zero; restore addic c,c,-1). Harness ok w=2..40; crate tests 60/60.
- bench/ppc64le-mont-4chain (265468c02) pushed; run 42715437320 (base 79ff93e5f, powerpc64, cpu_features "-").
  DELETE branch after (ask coordinator).

## Round 5 (coordinator 22:56, from alex): "never be afraid of a full rewrite of impl and proof, dream big"
- Keep 4-chain going (run 42715437320).
- BIG BET: FPU Montgomery kernel (as OpenSSL ppc64-mont.pl: FP multiplies; scalar FP is POWER8 baseline).
  TCB addition of FPRs + POWER8 FP instrs (fmadd, fcfid/fctidz, lfd/stfd, mtvsrd/mfvsrd...) now allowed.
  1. prototype FPU (or FPU+integer interleaved) kernel on bench/ branch (hand asm or C -mcpu=pwr8 ok);
     measure rsa sign/verify, dsa_verify, ffdh_exchange vs main with openssl in one job.
  2. if >= 20% on RSA sign: send coordinator numbers + PR plan: TCB first (ISA 2.07 citations; constant-time argument:
     POWER9 Table A-1 latencies; operands never denormal and how the proof guarantees it), then kernel.
     Share ONE TCB PR with P-521 session (session_01TKUFHH4GefHP3pmPRSL4N4), which is trying FP for P-521.
- Delegated FPU prototype to a background subagent (see below for id).
- FPU subagent id abb1d7aa1b8b86675 (branch bench/ppc64le-mont-fpu)
- P-521 session FPU sizing (22:57): fmadd exact < 2^53; 23x23 fmadd mul ~2750 cyc (mca) vs integer two-chain 9-word ~274;
  ideal 2 FMA/cyc ~390; mulld/mulhdu fully pipelined on P8/9 (OpenSSL FP path is POWER5/6-era); FP+int split ~parity.
  Forwarded to FPU subagent with bar: <~22 cycles per 4 word-steps incl. conversion, else stop without benchmarking.

## Round 5 FPU results (subagent, 2026-11-09): NO-GO at the mca stage; no branch, no benchmark run
- Premise check: OpenSSL does NOT use the FPU on 64-bit POWER8/9. crypto/bn/bn_ppc.c (master): bn_mul_mont calls
  bn_mul4x_mont_int (integer, crypto/bn/asm/ppc-mont.pl) when num%4==0, else bn_mul_mont_int; comment: "There used
  to be [optional] call to bn_mul_mont_fpu64 here, but above subroutine is faster on contemporary processors".
  crypto/ppccap.c: "In 64-bit case PPC_FPU64 is fastest only on POWER6". So the 2x gap is an INTEGER kernel
  (4x-unrolled, ppc-mont.pl) -> compare against bn_mul4x_mont_int, not ppc64-mont.pl.
- mca pwr9 facts: fmadd lat 7, RThroughput 0.5 (2/cycle); mulld/mulhdu RThroughput 0.5, and they use the SAME
  DP pipes as fmadd (4 mul + 12 fmadd = exactly 8 cycles). fctidz/fcfid lat 7, mffprd/mtfprd lat 2.
- Cost on the shared pipe per word-step (a_i*b_j + u*m_j): integer 4 mul ops = 2 cycles; FP exact splits:
  16x32 digits (OpenSSL) 16 fmadd = 8 cycles; 22-bit limbs (2*(64/22)^2 = 16.9) = 8.5; 25-bit 13.1 = 6.5 (and
  accumulators overflow 2^53). Bar (>=20% vs cur4 28/4) = 5.5 cycles/word-step -> unreachable even at zero overhead.
- Ideal 4-row register-blocked 22-bit FP inner loop (scratchpad/fpu/fp4.s, fp4b.s; no conversion, no u chain):
  mca 39.4 / 35.1 cycles per 32 fmadd = ~20.9 / 18.6 cycles per word-step vs cur4 7.0, blk4 5.25.
- FP+integer interleave: pipes are shared, so moving work to FP costs 4x the pipe slots; plus radix conversion
  and per-row carry exchange. Cannot win.
- TCB: model has only mtvsrd/mfvsrd (Encode.lean); lacks FPRs and lfd/stfd, fmadd/fmul/fadd/fsub, fcfid(u),
  fctidz/fctiduz (and xs* forms). Not needed now.
- 23:0x FPU NO-GO reported to coordinator + P-521 (OpenSSL uses integer bn_mul4x_mont_int on P8/9; fmadd shares mul pipes). Next: 4-chain run result; if short, study ppc-mont.pl mul4x structure.
- RESULT run 42715437320 (4-chain vs main): sign 256/384/512 +10.8/+14.0/+15.7%; verify +17.1/+18.6/+18.1%;
  dsa_verify +7.0..+16.3%; ffdh +16.2/+18.3/+20.7%. Head vs OpenSSL sign 1.8/1.7/1.7x. Borderline -> reported; next:
  fold word 0 into first block, 8-word blocks; mca, then one more run (bench/ppc64le-mont-4chain still exists).
