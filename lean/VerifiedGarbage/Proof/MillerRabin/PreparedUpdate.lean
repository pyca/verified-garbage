module

public import VerifiedGarbage.Proof.MillerRabin.Workspace
public import VerifiedGarbage.Proof.MillerRabin.Reusable

/-! Replace a prepared witness while retaining the candidate's reusable data. -/

@[expose] public section
namespace VG.Proof.MillerRabin.Workspace
open VG VG.Spec.Rsa.Mont

theorem prepared_witness_update {m m' : Mem} {ws : Addr}
    (prepared : Spec.MillerRabin.Prepared Spec.MillerRabin.compact m ws)
    (width : wOf m' ws = wOf m ws)
    (numbers : ∀ j, j = 0 ∨ j = 9 ∨ j = 10 ∨ j = 27 →
      numAt m' ws (wOf m ws) j = numAt m ws (wOf m ws) j)
    (low : m'.readW (ws + BitVec.ofNat 64 (arrAt (wOf m ws) 0)) 64 =
      m.readW (ws + BitVec.ofNat 64 (arrAt (wOf m ws) 0)) 64)
    (inverse : wordAt m' ws minvWord = wordAt m ws minvWord)
    (tail : m'.readW (ws + BitVec.ofNat 64 (arrAt (wOf m ws) 27 + 8 * wOf m ws)) 64 =
      m.readW (ws + BitVec.ofNat 64 (arrAt (wOf m ws) 27 + 8 * wOf m ws)) 64)
    (witness : numAt m' ws (wOf m ws) 5 < numAt m ws (wOf m ws) 0) :
    Spec.MillerRabin.Prepared Spec.MillerRabin.compact m' ws := by
  apply ((prepared_core prepared).congr width numbers low inverse tail).prepared
  rw [width, numbers 0 (.inl rfl)]
  exact witness

end VG.Proof.MillerRabin.Workspace
