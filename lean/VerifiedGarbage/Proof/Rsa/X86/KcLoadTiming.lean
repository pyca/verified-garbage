module

public import VerifiedGarbage.Proof.Rsa.X86.KcPair
public import VerifiedGarbage.Proof.Bignum.X86.PublicLoadTiming

/-! # CRT input imports depend only on the public call geometry -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum.X86 VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.KeyCheck VG.Impl.Rsa.X86.Keys
open VG.Impl.Rsa.X86.CrtValues (load)

theorem load_relCT (g : CallGeometry) (i : Nat) (hi : 2 * i < VG.Impl.Rsa.X86.KeyCheck.scratchArg g.full) (j : Nat) (hj : j < nArr) :
    RelCT isa (Pair g) (load g.n (2 * i) j) (Pair g) := by
  intro s t tr ur sf tf h es et
  have trace := (loadArgument_trace (2 * i) (2 * i + 1) g.n
    (slot (2 * g.n) j) (g.args (2 * i)) (g.args (2 * i + 1)) _ _ _ _ _ _
    ⟨h.agree, (h.left.arguments _ (by omega)).readSrc, (h.right.arguments _ (by omega)).readSrc,
      (h.left.arguments _ (by omega)).readSrc, (h.right.arguments _ (by omega)).readSrc⟩ es et).1
  obtain ⟨hs, _, _, ks⟩ := wp_result (load_ok h.left i hi hj) es
  obtain ⟨ht, _, _, kt⟩ := wp_result (load_ok h.right i hi hj) et
  exact ⟨trace, h.after hs ht ks kt (by decide)⟩

end VG.Proof.Rsa.X86.KeyCheck
