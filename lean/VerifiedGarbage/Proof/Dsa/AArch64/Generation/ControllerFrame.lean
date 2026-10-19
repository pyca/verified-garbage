module
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Bignum.Words

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # Preserve the counter and offset while a native candidate is evaluated -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.Proof.Bignum

theorem controller_word_of_frame {m m' : Mem} {C : Addr} {rs : List Region} {d : Nat}
    (hf : Frame rs m m') (hsep : ∀ r ∈ rs, (⟨C, 24⟩ : Region).Disjoint r) (hd : d + 8 ≤ 24) :
    VG.Proof.Bignum.word m' C d = VG.Proof.Bignum.word m C d := by
  have sub : Region.Sub ⟨VG.Proof.Bignum.off C d, 8⟩ ⟨C, 24⟩ := Offset.sub_base C hd
  exact hf.readW (Region.contains_self _ _) (fun r hr a ha hb => hsep r hr a (sub a ha) hb) (by decide)

end VG.Proof.Dsa.AArch64.Generation
