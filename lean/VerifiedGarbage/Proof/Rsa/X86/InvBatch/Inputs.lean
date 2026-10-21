module
public import VerifiedGarbage.Proof.Mont.Words32

public import VerifiedGarbage.Impl.Rsa.X86.InvBatch
public import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.Matrix
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Weierstrass.Unch
public import VerifiedGarbage.Proof.Divstep.Alg32Def
import VerifiedGarbage.Proof.Weierstrass.X86.InvRead
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog

/-! # Inputs preserved while the four matrix rows use scratch arrays -/

@[expose] public section
namespace VG.Proof.Rsa.X86.InvBatch
open VG VG.X86 VG.Impl.Rsa.X86.InvBatch VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86.Inv

 def rowWrites (w : Nat) : List (Nat × Nat) :=
 [(offset w 0,2*(4*w+8)),(offset w 11,4*(4*w+8))]

 structure RowInput (w n : Nat) (base : Addr) (p iv : Nat) (T : VG.Proof.Divstep.MSt)
    (st : VG.Proof.Divstep.W32.IState) (s : State) : Prop where
  matrix : GcdBatch.MatrixAt w base T s
  modulus : val32 s.mem base (offset w 2) n=p
  inverse : w32 s.mem base (offset w 3+28)=iv
  f : (val32 s.mem base (offset w 4) (n+1) : Int)%2^(32*(n+1))=st.f%2^(32*(n+1))
  g : (val32 s.mem base (offset w 5) (n+1) : Int)%2^(32*(n+1))=st.g%2^(32*(n+1))
  a : (val32 s.mem base (offset w 6) n : Int)=st.a
  b : (val32 s.mem base (offset w 7) n : Int)=st.b

 theorem RowInput.keep {s t : State} {base : Addr} {size w n p iv : Nat} {T : VG.Proof.Divstep.MSt}
    {st : VG.Proof.Divstep.W32.IState} (h : RowInput w n base p iv T st s)
    (hs : Scr s base size) (_hn : 16≤n) (hw : w=2*n) (hz : offset w 15≤size)
    (O : Unch base (rowWrites w) s.mem t.mem) : RowInput w n base p iv T st t := by
  have nowrap := hs.nowrap
  obtain ⟨hD,hU,hV,hQ,hR⟩ := h.matrix
  have word (d : Nat) (lo : offset w 2≤d) (hi : d+4≤offset w 11) :
      t.mem.readW (off base d) 32=s.mem.readW (off base d) 32 :=
    read32_unch O (by
      intro r hr; simp only [rowWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl <;> dsimp only [offset,VG.Impl.Rsa.X86.GcdBatch.offset] at * <;> omega)
      (by dsimp only [offset,VG.Impl.Rsa.X86.GcdBatch.offset] at *; omega)
  have value (j k : Nat) (jl : 2≤j) (ju : j≤7) (kb : k≤n+1) :
      val32 t.mem base (offset w j) k=val32 s.mem base (offset w j) k := by
    have jl' : offset w 2≤offset w j := Nat.add_le_add_left (Nat.mul_le_mul_right (4*w+8) jl) _
    have ju' : offset w j≤offset w 7 := Nat.add_le_add_left (Nat.mul_le_mul_right (4*w+8) ju) _
    exact Outs.val32 O (by
      intro r hr; simp only [rowWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl <;> dsimp only [offset,VG.Impl.Rsa.X86.GcdBatch.offset] at * <;> omega)
      (by dsimp only [offset,VG.Impl.Rsa.X86.GcdBatch.offset] at *; omega)
  refine ⟨⟨?_,?_,?_,?_,?_⟩,?_,?_,?_,?_,?_,?_⟩
  · change t.mem.readW (off base (offset w 3+0)) 32=_
    rw [word _ (by dsimp only [offset]; omega) (by dsimp only [offset]; omega)]
    exact hD
  · change t.mem.readW (off base (offset w 3+12)) 32=_
    rw [word _ (by dsimp only [offset]; omega) (by dsimp only [offset]; omega)]
    exact hU
  · change t.mem.readW (off base (offset w 3+16)) 32=_
    rw [word _ (by dsimp only [offset]; omega) (by dsimp only [offset]; omega)]
    exact hV
  · change t.mem.readW (off base (offset w 3+20)) 32=_
    rw [word _ (by dsimp only [offset]; omega) (by dsimp only [offset]; omega)]
    exact hQ
  · change t.mem.readW (off base (offset w 3+24)) 32=_
    rw [word _ (by dsimp only [offset]; omega) (by dsimp only [offset]; omega)]
    exact hR
  · rw [value 2 n (by decide) (by decide) (by omega)]
    exact h.modulus
  · rw [w32,word _ (by dsimp only [offset]; omega) (by dsimp only [offset]; omega)]
    exact h.inverse
  · rw [value 4 (n+1) (by decide) (by decide) (by omega)]
    exact h.f
  · rw [value 5 (n+1) (by decide) (by decide) (by omega)]
    exact h.g
  · rw [value 6 n (by decide) (by decide) (by omega)]
    exact h.a
  · rw [value 7 n (by decide) (by decide) (by omega)]
    exact h.b

end VG.Proof.Rsa.X86.InvBatch
