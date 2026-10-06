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

end VG.Proof.Bignum.Rectangular
