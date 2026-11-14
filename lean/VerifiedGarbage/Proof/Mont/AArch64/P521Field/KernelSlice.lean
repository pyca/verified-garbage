module

public import VerifiedGarbage.TCB.AArch64.Target

/-! Slice literal blocks without traversing thousands of preceding instructions. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field

theorem drop_flatten_prefix {α : Type} (xs : List (List α)) (n k d : Nat)
    (hk : (xs.take n).flatten.length=k) :
    xs.flatten.drop (k+d)=(xs.drop n).flatten.drop d := by
  have hs : xs.flatten=(xs.take n).flatten++(xs.drop n).flatten := by
    rw [←List.flatten_append,List.take_append_drop]
  rw [hs,←hk,List.drop_length_add_append]

end VG.Proof.Mont.AArch64.P521Field
