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
