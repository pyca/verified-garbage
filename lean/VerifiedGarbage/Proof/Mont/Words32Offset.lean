module

public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-! Packed words at an offset workspace base. -/

@[expose] public section
namespace VG.Proof.Mont
open VG

theorem val32_off (m : Mem) (base : Addr) (d : Nat) : ∀ (e n : Nat),
    val32 m (off base d) e n = val32 m base (d + e) n
  | _, 0 => rfl
  | e, n + 1 => by
    rw [val32, val32, val32_off m base d (e + 4) n, show d + (e + 4) = d + e + 4 by omega]
    simp only [w32, off, Offset.add_add]

end VG.Proof.Mont
