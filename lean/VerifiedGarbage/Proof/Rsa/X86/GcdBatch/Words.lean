module

public import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.Start
public import VerifiedGarbage.Proof.Divstep.Word32
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog

/-! # Thirty low-word divsteps produce the full transition matrix -/

@[expose] public section
namespace VG.Proof.Rsa.X86.GcdBatch
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.GcdBatch
  VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86.Inv

structure MatrixAt (n : Nat) (base : Addr) (T : Divstep.MSt) (s : State) : Prop where
  d : s.mem.readW (VG.Proof.Mont.off base (offset n 3)) 32 = BitVec.ofInt 32 T.d
  u : s.mem.readW (VG.Proof.Mont.off base (offset n 3+12)) 32 = BitVec.ofInt 32 T.u
  v : s.mem.readW (VG.Proof.Mont.off base (offset n 3+16)) 32 = BitVec.ofInt 32 T.v
  q : s.mem.readW (VG.Proof.Mont.off base (offset n 3+20)) 32 = BitVec.ofInt 32 T.q
  r : s.mem.readW (VG.Proof.Mont.off base (offset n 3+24)) 32 = BitVec.ofInt 32 T.r

theorem low_cong {m : Mem} {base : Addr} {d n : Nat} {x : Int}
    (h : (val32 m base d (n+1) : Int)%2^(32*(n+1))=x%2^(32*(n+1))) :
    ((m.readW (VG.Proof.Mont.off base d) 32).toNat : Int)%2^32=x%2^32 := by
  have D : (2:Int)^32 ∣ 2^(32*(n+1)) := pow_dvd_pow 2 (by omega)
  have E : (w32 m base d : Int)%2^32=(val32 m base d (n+1) : Int)%2^32 := by
    rw [val32,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Int.add_mul_emod_self_left]
  rw [E,← Int.emod_emod_of_dvd _ D,h,Int.emod_emod_of_dvd _ D]

theorem words_ok {s : State} {base : Addr} {size n : Nat} {d f g : Int}
    (hs : Scr s base size) (hn : 16 ≤ n) (hz : offset n 15 ≤ size)
    (hd : s.mem.readW (VG.Proof.Mont.off base (offset n 3)) 32=BitVec.ofInt 32 d)
    (hf : (val32 s.mem base (offset n 4) (n+1) : Int)%2^(32*(n+1))=f%2^(32*(n+1)))
    (hg : (val32 s.mem base (offset n 5) (n+1) : Int)%2^(32*(n+1))=g%2^(32*(n+1)))
    (hdb : |d|+64<2^30) (hfo : f%2=1) :
    WP isa (.seq (.block (start n)) (VG.Impl.Weierstrass.X86.Inv.wordSteps (offset n 3) 30)) s fun z =>
      MatrixAt n base (Divstep.msteps 30 (Divstep.MSt.init d f g)) z ∧
      Keeps wordClob s z ∧ Outside base (offset n 3) 28 s.mem z.mem := by
  have nowrap := hs.nowrap
  refine WP.seq (WP.mono (start_ok hs hn hz) fun s₁ ⟨V₁,K₁,O₁⟩ => ?_)
  have rel : (wordState s₁.mem base (offset n 3)).rel (Divstep.MSt.init d f g) 32 := by
    rw [V₁]
    exact ⟨hd,rfl,rfl,rfl,rfl,low_cong hf,low_cong hg⟩
  have matrix := Divstep.W32.wsteps_rel (by decide) rel hdb hfo 30 (by decide)
  refine WP.mono (wordSteps_ok (hs.of_keeps K₁ (by decide)) (by dsimp only [offset] at *; omega)
    (by decide) (by decide)) fun z ⟨V₂,K₂,O₂⟩ => ⟨?_,(K₁.mono (by decide)).trans K₂,?_⟩
  · rw [← V₂] at matrix
    obtain ⟨D,U,V,Q,R,_,_⟩ := matrix
    exact ⟨D,U,V,Q,R⟩
  · intro x hx
    rw [O₂ x hx,O₁ x (by omega)]

end VG.Proof.Rsa.X86.GcdBatch
