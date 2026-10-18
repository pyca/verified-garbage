module

public import VerifiedGarbage.Proof.Dsa.Generation.WitnessBytes
import VerifiedGarbage.Proof.Framework.Omega

/-! # The copied suffix is the witness of the whole consumed tape draw -/

@[expose] public section
namespace VG.Proof.Dsa.Generation
open VG

theorem draw_suffix (r : List Byte) (used drawBytes len : Nat) (hlen : len ≤ drawBytes) :
    ((r.drop used).take drawBytes).drop (drawBytes - len) =
      (r.drop (used + (drawBytes - len))).take len := by
  rw [List.drop_take, List.drop_drop, Nat.sub_sub_self hlen]

theorem witness_slice {r : List Byte} {used drawBytes len N : Nat}
    (hlen : len ≤ drawBytes) (hroom : used + drawBytes ≤ r.length)
    (hbits : Spec.RsaKeyGen.bitLength (N - 1) = 8 * len) :
    Spec.RsaKeyGen.witness (N - 1) (Spec.Rsa.os2ip ((r.drop used).take drawBytes)) =
      Spec.RsaKeyGen.witness (N - 1)
        (Spec.Rsa.os2ip ((r.drop (used + (drawBytes - len))).take len)) := by
  let draw := (r.drop used).take drawBytes
  have hdraw : draw.length = drawBytes := by
    simp only [draw, List.length_take, List.length_drop]; omega
  have htail : (draw.drop (drawBytes - len)).length = len := by
    rw [List.length_drop, hdraw]; omega
  have he := witness_drop_padding (draw.take (drawBytes - len)) (draw.drop (drawBytes - len))
    (w := N) (by rwa [htail])
  rw [List.take_append_drop] at he
  rw [← draw_suffix r used drawBytes len hlen]
  exact he

end VG.Proof.Dsa.Generation
