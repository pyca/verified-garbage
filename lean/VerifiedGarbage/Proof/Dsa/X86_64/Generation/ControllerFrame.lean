module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchControl
public import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.Omega

/-! # Preserve the counter and offset while a native candidate is evaluated -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.Proof.Bignum

theorem controller_word_of_frame {m m' : Mem} {C : Addr} {rs : List Region} {d : Nat}
    (hf : Frame rs m m') (hsep : ∀ r ∈ rs, (⟨C, 24⟩ : Region).Disjoint r) (hd : d + 8 ≤ 24) :
    word m' C d = word m C d := by
  have sub : Region.Sub ⟨off C d, 8⟩ ⟨C, 24⟩ := Offset.sub_base C hd
  exact hf.readW (Region.contains_self _ _) (fun r hr a ha hb => hsep r hr a (sub a ha) hb) (by decide)

end VG.Proof.Dsa.X86_64.Generation
