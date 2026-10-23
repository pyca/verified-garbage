module

public import VerifiedGarbage.Spec.Dsa.Generate

/-! # Parameter-generation helpers for one public modulus width

**Trusted.** These helpers have the same arguments and results as complete
parameter generation, with the additional precondition that `p_len` equals
the width in the helper's name. This permits callers to share one verified
body per hash backend and width without introducing function pointers.
The FIPS generation algorithm, random-tape policy and leakage are unchanged.
-/

@[expose] public section
namespace VG.Spec.Dsa.GenerationSized
open VG.Spec.Dsa
open VG.Spec.Rsa (bytesAt)

def contract {M : ISA} (pBytes : Nat) (A : Abi M) (stack : Nat := 0) : Contract M :=
  generateParametersSig.contract A
    (pre := fun _out outLen pLen qLen _seeds seedsLen _hs hsLen _witnesses _witnessesLen
        _scratch scratchLen _ =>
      pLen.toNat = pBytes ∧ generationLengthsValid pLen.toNat qLen.toNat ∧
        outLen.toNat = 2 * pLen.toNat + qLen.toNat ∧
        seedsLen.toNat % qLen.toNat = 0 ∧ hsLen.toNat % pLen.toNat = 0 ∧
        generationScratchWords pLen.toNat ≤ scratchLen.toNat)
    (post := fun out outLen pLen qLen seeds seedsLen hs hsLen witnesses witnessesLen
        _scratch _scratchLen m m' r =>
      let res := generateParametersBytes pLen.toNat qLen.toNat (bytesAt m seeds seedsLen.toNat)
        (bytesAt m hs hsLen.toNat) (bytesAt m witnesses witnessesLen.toNat)
      r.toNat = signStatus res ∧
        bytesAt m' out outLen.toNat = res.getD (List.replicate outLen.toNat 0))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen _pLen _qLen seeds seedsLen hs hsLen witnesses witnessesLen
        _scratch _scratchLen m =>
      (bytesAt m seeds seedsLen.toNat).map (·.toNat) ++
        (bytesAt m hs hsLen.toNat).map (·.toNat) ++
        (bytesAt m witnesses witnessesLen.toNat).map (·.toNat))


/-- The complete generation API restricted to one public modulus width.
Its q width is still constrained by `generationLengthsValid`. -/
def api (pBytes : Nat) : Api where
  module := "dsa"
  name := s!"vg_dsa_generate_parameters_{8 * pBytes}"
  sig := generateParametersSig
  writeArgs := true
  contracts := some fun A stack => contract pBytes A stack
  summary := s!"Generate DSA parameters with p_len = {pBytes}, using the same bounded \
    FIPS 186-4 parameter-generation algorithm and random-tape policy as \
    vg_dsa_generate_parameters. Returns 1 with p||q||g, or 0 with zero output \
    if no parameters are produced. All three tapes may affect timing. \
    Contract: VG.Spec.Dsa.GenerationSized.contract."
  safety := [s!"p_len must be {pBytes}; the (p_len, q_len) pair must be (128,20), (256,32), or (384,32).",
    "out_len must be 2*p_len + q_len; seeds_len must be a multiple of q_len; hs_len a multiple of p_len.",
    "scratch_len must be at least 64*p_len + 1024 words; destroy scratch after use.",
    "All tapes must contain fresh independent random bytes when parameter generation requires randomness."]

end VG.Spec.Dsa.GenerationSized
