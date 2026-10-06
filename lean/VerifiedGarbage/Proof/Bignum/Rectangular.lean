import VerifiedGarbage.Proof.Bignum.Square

/-! Positional arithmetic for rows of rectangular multiplication tiles. -/
namespace VG.Proof.Bignum.Rectangular

/-- Append one tile to a row. The incoming carry belongs to the tile's high
half; the new carry remains just beyond the processed prefix. -/
theorem extend_row {P R L A C T U V B D H O C' : Nat}
    (h : L + P * (A + R*C) = T + U*V)
    (step : O + R*H + R*R*C' = A + R*D + U*B + R*C) :
    L + P*O + (P*R)*(H + R*C') = T + (P*R)*D + U*(V + P*B) := by
  grind

/-- Lift a local equation through an unchanged surrounding number. -/
theorem lift_value {L L' X X' P Q R U V C D : Nat}
    (frame : L'+P*X = L+P*X') (tile : X'+Q*D = X+U*V+R*C) :
    L'+P*Q*D = L+P*(U*V)+P*R*C := by
  grind

theorem surround {A P X X' Q Y : Nat} :
    (A+P*(X'+Q*Y))+P*X = (A+P*(X+Q*Y))+P*X' := by
  grind

theorem extend_full {L L' C D X P T U V B : Nat}
    (prev : L+C = X+P*U*V) (step : L'+D = L+(P*T)*(U*B)+C) :
    L'+D = X+P*U*(V+T*B) := by
  grind

end VG.Proof.Bignum.Rectangular
