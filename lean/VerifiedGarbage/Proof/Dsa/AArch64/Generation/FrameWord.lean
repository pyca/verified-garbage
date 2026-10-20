module
public import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.PlainSimp


/-! Persistent frame words survive writes within a separate arithmetic workspace. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.Proof.Bignum

theorem frame_word_of_workspace {B F : Addr} {Z k : Nat} {rs : List (Nat × Nat)} {m m' : Mem}
    (hf : Frm B rs m m') (hr : ∀ r ∈ rs, r.1 + r.2 ≤ Z)
    (ho : ∀ i < 8, Z ≤ ofs B (off (off F (8 * k)) i)) :
    word m' F (8 * k) = word m F (8 * k) := by
  apply Mem.readW_congr
  intro i hi
  exact hf _ (fun r h => Or.inr (Nat.le_trans (hr r h) (ho i hi)))

end VG.Proof.Dsa.AArch64.Generation
