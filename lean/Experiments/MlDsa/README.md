# Unproved ARM64 ML-DSA experiment

This branch exists only to measure the prototype on N2 CI. It is not a production change and must not be merged. The generated Rust bodies are replaced with the output of these standalone Lean instruction emitters. Their old generated contract comments do not establish proofs of the replacement bodies; in particular, products use Montgomery scaling and the inverse compensates for it.

Candidate: fused3 NTT, scaled products, vector rounding, adaptive five-block/four-candidate vector matrix sampler, adaptive bounded sampler, four-way ExpandMask, wide copies, vector keygen masks, and wide zeroize. The default and forced-SHA3 paths remain selectable through the existing test override. No specification or TCB changes.

Local known-answer/Wycheproof tests passed, including the forced-SHA3 path. Additional external differential tests compare arithmetic and sampler outputs against main and check buffer canaries. Proofs and production dispatch follow only after the performance target is met. Measurements remain outside the repository.
