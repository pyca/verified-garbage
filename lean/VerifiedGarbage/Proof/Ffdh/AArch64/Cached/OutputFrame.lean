module

public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Omega

/-! Convert a precise output-byte frame to the API's region frame. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.Proof.Bignum

theorem outside_frame_member {rs : List Region} {ptr : Addr} {k : Nat} {m m' : Mem}
 (frame : Outside ptr 0 k m m') (member : (⟨ptr,k⟩ : Region)∈rs) : Frame rs m m' := by
 intro x hx
 apply frame x
 right
 have no := hx ⟨ptr,k⟩ member
 change ¬ofs ptr x+1≤k at no
 omega

end VG.Proof.Ffdh.AArch64.Cached
