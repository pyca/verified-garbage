# ppc64le RSA Montgomery kernel: 4-chain blocked rows (handoff)

This branch is a handoff, not a PR: it holds the design, generator and measurements for rewriting
`vg_rsa_mont_kernel` (`lean/VerifiedGarbage/Impl/Bignum/PPC64LE/MontMul.lean`, `MontMul.kernel`), and
proving it. Delete the `notes/` directory before opening any PR from it (or start a fresh branch).

## Decision (coordinator, 2026-11-09, with alex's go-ahead for bold rewrites)
Prove the 4-word-block version below; no further benchmark gate. 8-word blocks were checked with
llvm-mca and are slower (5.4 vs 5.26 cycles per word-step, false dependencies from register reuse),
so they were not benchmarked. Plan the PRs so each is reviewable (e.g. the new kernel and its proof,
then the switch of the callers), and put the benchmark run in the PR that changes speed.

## Measured (Benchmarks run 42715437320, prototype vs main 79ff93e5f, POWER9 runner)
| Benchmark | Change |
|---|---|
| rsa_pkcs1_sign 256 / 384 / 512 | +10.8 / +14.0 / +15.7% |
| rsa_pkcs1_verify 256 / 384 / 512 | +17.1 / +18.6 / +18.1% |
| dsa_verify_q160/1024 .. q256/3072 | +7.0 .. +16.3% |
| ffdh_exchange 256 / 384 / 512 | +16.2 / +18.3 / +20.7% |
The prototype was a hand-written crate file on `bench/ppc64le-mont-4chain` (throwaway; ask the
coordinator to delete it). Ruled out before: vector units (POWER8 and POWER9), FPU (OpenSSL itself
uses integer `bn_mul4x_mont_int` on POWER8/9; fmadd shares the multiply pipes), two-row FIOS with the
old carry style (+7%), dedicated squaring (slower), unroll by 8 (branch range).

## Algorithm (gen4c.py is the exact reference; `python3 gen4c.py asm|rust`)
Same interface as today's kernel (see history.md, "Kernel interface"): r3 = y, r4 = 2w, r5 o, r6 a,
r7 b, r8 T (array 2), r9 tmp (array 3), r10 m, r14 kept; returns r11 = 2w, r12 = y; fully reduced.

FIOS, one round per word a_i of a (w rounds), T has w+1 words (T_w is 0/1):
* Word 0 (head): s0 = T_0; s0 += lo(a_i b_0) [addc, CA saved as cA]; u = s0·m' mod 2^64;
  s0 += lo(u m_0) [addc, cC] (result is 0, discarded); hA = hi(a_i b_0), hC = hi(u m_0); cB = cD = 0.
* Words 1..w-1 in blocks of k words (one block of k = (w-1) mod 4 first, then (w-1)/4 blocks of 4):
  load b_j.., m_j.., T_j..; four carry chains in turn, each `addic c,c,-1` (CA := c≠0), k `adde`, `addze c,zero`:
  - A: s_j += lo(a_i b_j)        - B: s_j += hi(a_i b_{j-1}) (hA for the block's first word)
  - C: s_j += lo(u m_j)          - D: s_j += hi(u m_{j-1})   (hC for the first word)
  then hA, hC := the block's last high words; store s_j to T_{j-1}.
* Top: x = T_w + cA + hA + cC + hC (each chain restored and added with adde, carry outs summed by addze
  into y); T_{w-1} := x, T_w := y.
* After w rounds: the existing subtract-and-select (T - m into tmp, mask from the borrow, select into o).

Invariant per block (what the proof tracks): with chains' saved carries cA..cD ∈ {0,1} and pending
high words hA, hC, the value
  Σ_{j<J} T'_{j-1} 2^{64(j-1)} + (cA + cB + cC + cD + hA + hC)·2^{64(J-1)}
  + Σ_{j≥J} (T_j + a_i b_j + u m_j) 2^{64(j-1)}  (low words only for j ≥ J, i.e. the not-yet-done part)
equals (T + a_i b + u m)/2^64, where J is the next word. Each chain's adde sequence is an exact
multi-word addition (carry in c, carry out c'), so the block step is four applications of one lemma
"k-word add with carry" plus the product split lo/hi (the existing mulld/mulhdu lemmas).

## Proof plan (suggested)
1. Read the skills: proof-performance, lean-modules, adding-a-primitive (the kernel is an internal
   function, `.call kernelName kernel`; callers are PublicChecked.montOp and friends).
2. Existing proof to adapt: `Proof/Bignum/PPC64LE/` MontCore (tailW_ok, tailN_ok, kernel_ok,
   kernelRegs), PubMont (WP.callRaw, montOpN_ok), CrtPinsB/CrtCT (taint cut positions over Code.flat
   — recompute with #eval of Code.flat lengths after `lean_cache.py fill-private`), Dsa CT/Base rel_end.
   Keep `kernel_ok`'s statement unchanged if at all possible so the callers' proofs only need the
   positions remapped.
3. Write the block as `Prog` with a generic `k` (1..4) so one lemma covers all block sizes; the
   remainder dispatch is a chain of `if r = k` conditionals, as measured. A simpler-to-prove
   alternative is running k=1 blocks (w-1) mod 4 times; it is slightly slower, so measure it if used.
4. Register pressure: the prototype uses r0, r3-r12, r14-r31 and saves r14, r21, r23-r31 (and the
   argument registers) below r1 (red zone, offsets -8 .. -176). Check how the existing kernel saves
   nonvolatiles (MontMul `saved`) and reuse that scheme; the model may not allow red-zone stores —
   use the existing frame convention.
5. Constant time: no data-dependent branches (block counts depend only on w); taint_decide over the
   new code; carries live in GPRs, not flags across branches.
6. Regenerate with `lake env lean --run EmitOne.lean <Reg>` / full Emit, test under qemu
   (history.md has the commands), run the Static checks, then one scoped Benchmarks run (inputs in
   history.md, `cpu_features: "-"`, `arches: powerpc64`, openssl true) and link it in the PR.

## Files here
* gen4c.py — the prototype generator (asm for harness; rust for the crate file)
* harness.c — C reference test harness (w = 2..40, odd, squares) for qemu-ppc64le
* cur4.s / blk4.s — llvm-mca inputs: today's loop (28 cyc / 4 words) vs the 4-chain block (21)
* history.md — the whole workstream's notes (interface, mechanics, pitfalls, all prior results)
