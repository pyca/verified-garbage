module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.BuildFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! Public precomputation may write only its scratch buffer and output context. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.Proof.Bignum

def publicWrites (p : Parameters) : List Region := [⟨p.B,p.Z⟩,⟨p.ctx,8*(3+34*p.w)⟩]

abbrev PublicFrame (p : Parameters) := Frame (publicWrites p)

theorem PublicFrame.of_inscr {p : Parameters} {m m' : Mem} (h : InScr p.B p.Z m m') : PublicFrame p m m' := by
 intro x hx
 apply h
 have no := hx ⟨p.B,p.Z⟩ (by simp [publicWrites])
 change ¬ofs p.B x+1≤p.Z at no
 omega

theorem PublicFrame.of_build {p : Parameters} {m m' : Mem} (h : BuildFrame p m m') : PublicFrame p m m' := by
 apply h.sub
 intro r hr
 simp only [buildWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
 rcases hr with rfl | rfl
 · exact ⟨⟨p.B,p.Z⟩,by simp [publicWrites],fun _ h => h⟩
 · exact ⟨⟨p.ctx,8*(3+34*p.w)⟩,by simp [publicWrites],Offset.sub_base p.ctx (by unfold tableStart;omega)⟩

theorem PublicFrame.of_context {p : Parameters} {m m' : Mem} {d n : Nat}
 (h : Outside p.ctx d n m m') (fit : d+n≤8*(3+34*p.w)) : PublicFrame p m m' := by
 have limit : 8*(3+34*p.w)<2^64 := by have := p.width;omega
 have frame := outside_to_array (by omega) (by omega) h
 intro x hx
 apply frame x
 right
 have no := hx ⟨p.ctx,8*(3+34*p.w)⟩ (by simp [publicWrites])
 have sub := Offset.sub_base p.ctx (d:=d) (n:=n) fit
 have notInside : ¬(⟨off p.ctx d,n⟩ : Region).Contains x 1 := fun hi => no (sub x hi)
 change ¬ofs (off p.ctx d) x+1≤n at notInside
 omega

end VG.Proof.Ffdh.AArch64.Cached
