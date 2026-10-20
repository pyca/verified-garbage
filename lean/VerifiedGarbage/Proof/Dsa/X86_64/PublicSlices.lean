module

public import VerifiedGarbage.TCB.Mem
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Equality of public domain slices does not equate private key material -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG

theorem prefix_component_eq {a b : List Byte} {n offset len : Nat}
    (h : a.take n = b.take n) (hbound : offset + len ≤ n) :
    (a.drop offset).take len = (b.drop offset).take len := by
  have hh := congrArg (fun bs : List Byte => (bs.drop offset).take len) h
  simp only [List.drop_take, List.take_take, Nat.min_eq_left (by omega : len ≤ n - offset)] at hh
  exact hh

end VG.Proof.Dsa.X86_64
