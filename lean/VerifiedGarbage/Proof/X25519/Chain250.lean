import VerifiedGarbage.Proof.X25519.Invert

/-!
# The addition chain to `z^(2^250 - 1)` and `z^11`

`chainF z`: the chain of ref10's `fe_invert`, as the field code of each
target that has it runs it, up to `z^(2^250 - 1)`, with `z^11` beside it
(`chainF_eq`), which inversion and decoding's square root each finish with a
few squarings and a product.
-/

namespace VG.Proof.X25519

open VG.Spec.X25519 (Fe)

/-- The chain on `z`: `z^(2^250 - 1)` and `z^11`. -/
def chainF (z : Fe) : Fe × Fe :=
  let t0 := z * z                 -- 2
  let t1 := t0 * t0
  let t1 := t1 * t1               -- 8
  let t1 := z * t1                -- 9
  let t0 := t0 * t1               -- 11
  let t2 := t0 * t0               -- 22
  let t1 := t1 * t2               -- 31 = 2^5 - 1
  let t2 := sqn t1 5
  let t1 := t2 * t1               -- 2^10 - 1
  let t2 := sqn t1 10
  let t2 := t2 * t1               -- 2^20 - 1
  let t3 := sqn t2 20
  let t2 := t3 * t2               -- 2^40 - 1
  let t2 := sqn t2 10
  let t1 := t2 * t1               -- 2^50 - 1
  let t2 := sqn t1 50
  let t2 := t2 * t1               -- 2^100 - 1
  let t3 := sqn t2 100
  let t2 := t3 * t2               -- 2^200 - 1
  let t2 := sqn t2 50
  (t2 * t1, t0)                   -- 2^250 - 1, 11

theorem chainF_eq (z : Fe) : chainF z = (pw z (2 ^ 250 - 1), pw z 11) := by
  rw [← congrArg chainF (pw_one z)]
  simp only [chainF, pw_mul, sqn_pw]

end VG.Proof.X25519
