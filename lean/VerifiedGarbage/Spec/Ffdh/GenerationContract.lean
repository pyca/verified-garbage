module

public import VerifiedGarbage.Spec.Ffdh.Generation
public import VerifiedGarbage.Spec.Rsa.Contract

/-! # Native FFDH generation controllers: initialization and entropy refills -/

@[expose] public section

namespace VG.Spec.Ffdh

open VG.Spec.Rsa (bytesAt wordsAt i2osp)

def parameterInitSig : Sig where
  params := [("state", .array true .u64 16), ("bits", .int .usize true),
    ("generator", .int .u32 true)]
  ret := some .u32

def parameterInitContract {M : ISA} (A : Abi M) : Contract M :=
  parameterInitSig.contract A
    (post := fun state bits generator _ m' r =>
      match parameterInit bits.toNat generator.toNat with
      | none => r.toNat = 0 ∧ wordsAt m' state 4 = List.replicate 4 0
      | some values => r.toNat = 1 ∧ wordsAt m' state 4 = values.map (BitVec.ofNat 64))

def parameterInitApi : Api where
  module := "ffdh"
  name := "vg_ffdh_parameter_generation_init"
  sig := parameterInitSig
  contracts := some fun A _ => parameterInitContract A
  summary := "Initialize native finite-field Diffie–Hellman parameter generation. Validates \
    512..=8192 bits and generator 2 or 5. Returns 1 and initializes the controller's \
    attempt limit, output width, entropy budget and first entropy request; returns 0 \
    and clears those four words on invalid parameters. The remaining state words \
    are private workspace. Contract: `VG.Spec.Ffdh.parameterInitContract`."
  safety := []

def parameterSearchSig : Sig where
  params := [("out", .slice true .u8 "out_len"), ("used", .array true .u64 1),
    ("bits", .int .usize true), ("generator", .int .u32 true),
    ("rand", .slice false .u8 "rand_len"), ("scratch", .slice true .u64 "scratch_len"),
    ("state", .array true .u64 16)]
  ret := some .u32

end VG.Spec.Ffdh
