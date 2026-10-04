/-!
# A modulus for Montgomery arithmetic, on any target

What the Montgomery arithmetic of each target (`Impl/Mont/<Target>.lean`)
needs of an odd multiword modulus `m`: its number of 64-bit words `n`, where
it is in the working space (`mo`, `n` words), the working space's temporary
area (`tmp`, `n` words), and `minv = -m⁻¹ mod 2⁶⁴`.
-/

namespace VG.Impl.Mont

/-- A modulus: its number of words `n`, where it is (`mo`, `n` words), the
working space's temporary area (`tmp`, `n` words), and
`minv = -m⁻¹ mod 2⁶⁴`. -/
structure Mod where
  n : Nat
  mo : Nat
  tmp : Nat
  minv : BitVec 64

end VG.Impl.Mont
