module

public import VerifiedGarbage.Proof.Rsa.X86.RvPair
public import VerifiedGarbage.Proof.Bignum.X86.PublicLoadTiming

/-! # Recovery input imports depend only on the public call geometry -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum.X86 VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Recover VG.Impl.Rsa.X86.Keys

theorem load_relCT (g : CallGeometry) (i : Fin 3) (j : Nat) (hj : j < nArr) :
    RelCT isa (Pair g) (load g.n (4 + 2 * i.val) j) (Pair g) := by
  intro s t tr ur sf tf h es et
  have trace := (loadArgument_trace (4 + 2 * i.val) (4 + 2 * i.val + 1) (g.n + 2)
    (slot (VG.Impl.Rsa.X86.Recover.width g.n) j) (g.args (4 + 2 * i.val)) (g.args (4 + 2 * i.val + 1)) _ _ _ _ _ _
    ⟨h.agree, (h.left.arguments _ (by omega)).readSrc, (h.right.arguments _ (by omega)).readSrc,
      (h.left.arguments _ (by omega)).readSrc, (h.right.arguments _ (by omega)).readSrc⟩ es et).1
  obtain ⟨hs, _, _, ks⟩ := wp_result (load_ok h.left i hj) es
  obtain ⟨ht, _, _, kt⟩ := wp_result (load_ok h.right i hj) et
  exact ⟨trace, h.after hs ht ks kt (by decide)⟩

end VG.Proof.Rsa.X86.Recover
