module

public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Sample.Common
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Pack.Encode

/-!
# ML-DSA on PPC64LE: `vg_mldsa_expand_mask_poly`

`expandMask(seed = r3, gamma1 = r4, a = r5, scratch = r6)` (see
`Common.lean` for the layout), as on 32-bit ARM: it squeezes 640 bytes of
SHAKE256 of the 66 bytes of the seed (5 blocks, which also hold the 576
bytes that `γ₁ = 2¹⁷` needs), and unpacks the first `32c` of them, `c = 18`
or `20` (chosen by a branch on the public `γ₁`), as `BitUnpack` with
`(a, b) = (γ₁ - 1, γ₁)`, with the loop of `vg_mldsa_bit_unpack`
(`Impl/MlDsa/PPC64LE/Pack/Stream.lean`): coefficient `i` is `γ₁` minus the
`c`-bit field `i`, modulo `q`. There is no branch on the data, and the
addresses depend only on the pointers and `γ₁`: it is constant time.
-/

@[expose] public section

namespace VG.Impl.MlDsa.PPC64LE.Sample

open VG.PPC64LE
open VG.Impl.MlDsa.PPC64LE.Pack (unpackLoop buFin loadB)

/-- The fields, from the XOF output at `scratch + 840` to `a`, with `γ₁` in
`r4` and `q` in `r7`. -/
def emLoop (c : Nat) : Prog isa :=
  .seq (.block ([.addi .r10 .r31 840, VG.Impl.Sha3.PPC64LE.Stream.mov .r11 .r30] ++ Pack.loadQ ++
      loadB .r4 (if c = 18 then 131072 else 524288)))
    (if c = 18 then unpackLoop buFin 18 4 9 else unpackLoop buFin 20 2 5)

def expandMask : Prog isa :=
  .seq (.block (pro .r6 .r5 .r3 [.li .r28 66] (zext32 .r27 .r4)))
    (.seq (sponge 136 640)
      (.seq (.seq (.block [.lis .r12 2, .sub .r12 .r27 .r12]) (.ite (.zero .d .r12) (emLoop 18) (emLoop 20)))
        (.block epi)))

end VG.Impl.MlDsa.PPC64LE.Sample
