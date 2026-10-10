import Lean.Elab.Command
import VerifiedGarbage.Spec.Ed25519.Point64

/-!
# RFC 8032's doubling formula (`Spec/Ed25519/Point64.lean`)

`pointDouble`, the doubling formula of RFC 8032 §5.1.4, gives the same point
as the complete addition formula `pointAdd p p`: their projective
coordinates are proportional, and the double's extended coordinates are
consistent (`T Z = X Y`). Checked for the identity and multiples of the base
point, each also with its coordinates scaled by a factor, so that `Z ≠ 1`.
-/

namespace VG.Test.Ed25519Point64

open Lean Elab Command Spec.Ed25519 Spec.Ed25519.Point64

/-- The point with its coordinates multiplied by `k`. -/
def scale (k : Spec.X25519.Fe) (p : Point) : Point := ⟨k * p.X, k * p.Y, k * p.Z, k * p.T⟩

/-- `pointDouble p` and `pointAdd p p` are the same point. -/
def checkDouble (p : Point) : Except String Unit := do
  let r := pointDouble p
  let s := pointAdd p p
  unless r.Z != 0 do throw "the double's Z is 0"
  unless r.X * s.Z == s.X * r.Z && r.Y * s.Z == s.Y * r.Z do
    throw "pointDouble and pointAdd differ"
  unless r.T * r.Z == r.X * r.Y do throw "the double's T is inconsistent"

run_cmd do
  let result := do
    for j in List.range 12 do
      let p := pointMul j basePoint
      checkDouble p
      checkDouble (scale (Fin.ofNat _ (3 * j + 7)) p)
  match result with
  | .ok () => pure ()
  | .error e => throwError "pointDouble: {e}"

end VG.Test.Ed25519Point64
