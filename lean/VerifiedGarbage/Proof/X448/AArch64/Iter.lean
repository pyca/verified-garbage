module

public import VerifiedGarbage.Proof.X448.Ladder
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.X448.AArch64.Swap
public import VerifiedGarbage.Proof.X448.AArch64.Env

/-!
# X448 on AArch64: lemmas of the Montgomery ladder

The first element of the specification's conditional swap (`cswap_fst`), and
the offset of an address in the working space (`ofs_off'`).
-/

@[expose] public section

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

theorem cswap_fst (sw : Nat) (a b : Spec.X448.Fe) :
    (Spec.X448.cswap sw a b).1 = if decide (sw = 1) = true then b else a := by
  simp only [Spec.X448.cswap, decide_eq_true_eq]; split <;> rfl

theorem ofs_off' (base : Addr) {d : Nat} (h : d < 2 ^ 64) : ofs base (off base d) = d :=
  Mem.sub_ofNat_toNat base h

end VG.Proof.X448.AArch64
