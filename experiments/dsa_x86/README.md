# Unproven x86 DSA experiments

Experimental branch only; not a library implementation or a proof. The checked
implementation is preserved on dsa-x86-generation at 784473529.

Prototype.lean constructs programs using the existing ISA and printer, without
constructing an Artifact, Verified value, or a proof placeholder. Compressed
manifests are its generated output. install.py applies those bodies only to a
checkout explicitly marked disposable. Do not run the normal verified emitter
on these temporary results or claim its audits cover them.

Variants: baseline; d removes the redundant internal domain check; w uses RSA's
constant-time 4-bit window exponentiation in a private stack arena; dw combines
them; dwp adds direct selection for public powers (domain checks and prime
search); dwpr2/4/8/0 also hold the multiplier in ESI and process 2/4/8/all words
per row iteration. ESI is saved around each row. Public APIs still validate the
domain. The public-key import/derivation API retains its validation.

The native i686 workflow tests each variant, including identical published CAVP
parameter searches repeated three times, and runs three alternating-order
key-generation benchmark rounds beside OpenSSL. Report round medians and spread;
never use emulated runtime for performance claims. Private exponent table access
remains a full masked scan. None of the new programs has a constant-time proof.
Stack arenas require new stack bounds if an experiment is promoted.

Generate manifests from the checked tree's Lean environment:
`lake env lean --run /path/to/Prototype.lean MODE [CHUNK]`, then gzip the JSON.
No hand-written assembly or trusted-model changes are used.

Second sweep: `t` changes the private table scan to compute masks once and
accumulate each output word in a register; `s` uses triangular squaring with
full-product Montgomery reduction; `c` keeps the triangular outer loop compact.
The expanded square initially failed a signature vector because the existing
CIOS carry tail is insufficient for a full raw product. Both square layouts now
propagate carries through every remaining high word with public loop bounds.
Carry-heavy algebraic power identities supplement the existing CAVP tests.
`dwprt4`, `dwprst4`, and `dwprsct4` use four-word multiplication chunks.

The second sweep records native DSA symbol sizes and selects a parameter-search
candidate using the geometric mean of its fixed-search ratios to baseline. It
then measures complete random parameter generation for baseline, that candidate,
and OpenSSL. Random-search medians remain noisy; fixed tapes isolate arithmetic
changes but cannot replace the real API comparison.

Third sweep: `f` seeds setup from the public modulus's known high bit for the
common full-width and padded-q shapes, retaining the original setup as fallback.
It reaches the same 2^(65*n) residue before the same six Montgomery squares.
`v` replaces full-product reduction's high-word scans with a pending carry at
context header offset 24. Each following row consumes that carry at its high
word; the last row publishes it as the accumulator's top word. These experiments
are stacked with both four-word and fully expanded multiplication rows.
Power identities cover full-width, shorter-high-bit, and padded moduli.

ABI regression: the first pending-carry draft used offset 8, colliding with
Pow.save's EBX spill. Arithmetic tests passed but a new Lean-generated ABI
wrapper reproduced the register corruption. The carry now uses offset 24,
beyond all four saved-register words. Every power identity checks all four
callee-saved registers as well as the arithmetic result. The affected native
run (39514353796) was cancelled and its results must not be used.

Final stacking experiment: `z` uses a 6-bit fixed window only for the long public
1024/2048/3072-bit parameter-search exponents. It handles a partial leading window
explicitly and allocates 64 table entries. Private powers retain four-bit masked
selection. The final comparison times the selected prototype beside OpenSSL;
the earlier sweeps also measured the verified baseline's random searches.

Compact alternative: `h` replaces Montgomery products with calls to the existing
`vg_rsa_mont_mul_at`, sharing RSA's already-verified runtime-width helper. The
`dwptfzh` variant uses it for squares too, so it has no separate square kernel or
expanded multiplication rows. Large widths use slots one/two as scratch. Small
widths temporarily borrow 16 unused modulus-padding bytes and restore them;
the algebraic tests assert that padding's frame property explicitly. Compare
its native speed and symbol sizes against `dwprsctfvz4` before selecting a
production design. No new RSA implementation is introduced by this variant.

Focused follow-up: `q` also windows the padded 192-bit (3-word) exponent in the
160-bit subgroup-prime test. Workflow inputs can restrict the random API timing
to one parameter width and raise its sample count. The installer instruments
only the disposable benchmark copy; ordinary library behavior is unchanged.

Proof promotion constraint: the existing generic `Spec.Dsa.ModPow.powContract`
classifies the modulus as secret. The `f` fast path branches only on DSA's public
modulus, but therefore cannot certify that generic contract unchanged. A promoted
DSA helper must explicitly expose the already-public modulus in its timing
contract (or move setup into the public DSA layer); the existing secret-modulus
contract must not be weakened. The experiment does not construct either proof.
The shared-RSA scratch-padding save/restore is also required to establish
ModPow.Keeps, in addition to arithmetic and ABI preservation.

Square-loop follow-up: `u` processes four triangular products per inner-loop
iteration; `j` processes eight. A scalar prefix handles the public remainder
of each row length. The outer loop and prefix remain compact. The numeric
suffix still controls the Montgomery row chunk, so `...j8` stacks both choices.
