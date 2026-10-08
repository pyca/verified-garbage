# Unproved ARM64 ML-DSA experiment

This branch exists only to measure the prototype on N2 CI. It is not a production change and must not be merged. The generated Rust bodies are replaced with the output of these standalone Lean instruction emitters. Their old generated contract comments do not establish proofs of the replacement bodies; in particular, products use Montgomery scaling and the inverse compensates for it.

Candidate: fused3 NTT, scaled products, vector rounding, adaptive five-block/four-candidate vector matrix sampler, adaptive bounded sampler, four-way ExpandMask, wide copies, vector keygen masks, and wide zeroize. The default and forced-SHA3 paths remain selectable through the existing test override. No specification or TCB changes.

Local known-answer/Wycheproof tests passed, including the forced-SHA3 path. Additional external differential tests compare arithmetic and sampler outputs against main and check buffer canaries. Proofs and production dispatch follow only after the performance target is met. Measurements remain outside the repository.

Second screen adds grouped bounded sampling, vector packing/unpacking and verification masks, strict-schedule hint reuse, and fused dot products. In benchmark builds, ML-DSA now selects SHA3 automatically after checking its generated requirements, allowing an unrestricted same-job AWS-LC comparison. Early-rejection experiments are excluded.

Third screen uses immutable forward/inverse twiddle tables, a positive-lazy forward NTT (coefficients below 3q), canonical compensated inverse output, faster masked bounded-sampler parsing, and batched final three ExpandMask polynomials in ML-DSA-87. The wider internal NTT range is experimental and requires separately reviewed contracts before production; existing generated contract comments do not describe these unproved bodies. The strict signing rejection schedule is unchanged.

Fourth screen adds expanded twiddle vectors and folded inverse scaling, out-of-place mask NTTs, fused signing checks with the original rejection schedule, fixed-length commitment hashing, paired matrix tails for ML-DSA-65, vector mask parsing, wider rejection parsing with exact failure tails, and register-resident paired SHAKE. Local differential tests and ACVP/Wycheproof tests cover the baseline and forced-SHA3 configurations. No measurements are committed. All implementations remain experimental and unproved.
