module

public import VerifiedGarbage.Proof.Mont.Words32

/-! # Updating a window in an unreduced integer product

The multiplication row changes only its window. Its contribution to the
whole integer is the row's increment times the public word position.
-/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Product
open VG VG.Proof.Mont

theorem parts_add {m m' : Mem} {base : Addr} {out total i len increment : Nat}
    (fits : i + len ≤ total)
    (low : val32 m' base out i = val32 m base out i)
    (high : val32 m' base (out + 4 * (i + len)) (total - (i + len)) =
      val32 m base (out + 4 * (i + len)) (total - (i + len)))
    (value : val32 m' base (out + 4 * i) len =
      val32 m base (out + 4 * i) len + increment) :
    val32 m' base out total = val32 m base out total + 2 ^ (32 * i) * increment := by
  have split (mem : Mem) : val32 mem base out total =
      val32 mem base out i + 2 ^ (32 * i) *
        (val32 mem base (out + 4 * i) len + 2 ^ (32 * len) *
          val32 mem base (out + 4 * (i + len)) (total - (i + len))) := by
    have e : total = i + (len + (total - (i + len))) := by omega
    calc
      val32 mem base out total = val32 mem base out (i + (len + (total - (i + len)))) :=
        congrArg (val32 mem base out) e
      _ = _ := by
        rw [val32_append, val32_append]
        rw [show out + 4 * i + 4 * len = out + 4 * (i + len) by omega]
  rw [split m', split m, low, high, value]
  simp only [Nat.mul_add]
  omega

theorem window_add {m m' : Mem} {base : Addr} {out total i len increment : Nat}
    (bound : out + 4 * total ≤ 2 ^ 64) (fits : i + len ≤ total)
    (changed : Outside base (out + 4 * i) (4 * len) m m')
    (value : val32 m' base (out + 4 * i) len =
      val32 m base (out + 4 * i) len + increment) :
    val32 m' base out total = val32 m base out total + 2 ^ (32 * i) * increment :=
  parts_add fits (changed.val32 (Or.inl (Nat.le_refl _)) (by omega))
    (changed.val32 (by omega) (by omega)) value

end VG.Proof.RsaKeyGen.X86.Product
