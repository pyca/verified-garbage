module
public import VerifiedGarbage.Impl.Rsa.X86.GcdBatch
public import VerifiedGarbage.Proof.Rsa.X86.InvLoop
public import VerifiedGarbage.Proof.Weierstrass.Unch
/-! # The batched GCD's existing inverse bank -/
@[expose] public section
namespace VG.Proof.Rsa.X86.GcdBatch
open VG VG.Impl.Rsa.X86.GcdBatch VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Rsa.X86.Keys
theorem offset_arr (n j : Nat) : offset n j=arr n j := by
  change 160+j*(4*n+8)=160+j*(4*(n+2))
  rw [show 4*(n+2)=4*n+8 by omega]

def ownRanges (n : Nat) : List (Nat × Nat) :=
 [(offset n 0,8*(4*n+8)),(offset n 11,4*(4*n+8)),(100,4)]

theorem own_keep {base : Addr} {n : Nat} {m m' : Mem} (h : Unch base (ownRanges n) m m') :
    Keep base n invArrs invSlots m m' := by
  intro x hx
  have each : ∀ j ∈ invArrs,ofs base x<arr n j ∨ arr n j+S n ≤ ofs base x := by
    intro j hj
    exact hx (arr n j,S n) (by
      simp only [ranges,List.mem_append,List.mem_map]
      exact .inl ⟨j,hj,rfl⟩)
  have h0 := each 0 (by decide)
  have h1 := each 1 (by decide)
  have h2 := each 2 (by decide)
  have h3 := each 3 (by decide)
  have h4 := each 4 (by decide)
  have h5 := each 5 (by decide)
  have h6 := each 6 (by decide)
  have h7 := each 7 (by decide)
  have h11 := each 11 (by decide)
  have h12 := each 12 (by decide)
  have h13 := each 13 (by decide)
  have h14 := each 14 (by decide)
  have h100 := hx (100,4) (by
    simp only [ranges,List.mem_append,List.mem_map]
    exact .inr ⟨100,by decide,rfl⟩)
  apply h x
  intro w hw
  simp only [ownRanges,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl
  all_goals
    dsimp only [arr,S,VG.Impl.Rsa.X86.Keys.hdr,offset] at *
    omega

end VG.Proof.Rsa.X86.GcdBatch
