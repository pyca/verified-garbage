module

public import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.Batch
import VerifiedGarbage.Proof.Weierstrass.X86.Loop
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
import VerifiedGarbage.Proof.Divstep.Steps

/-! # A fixed public number of GCD batches -/

@[expose] public section
namespace VG.Proof.Rsa.X86.GcdBatch
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.GcdBatch
  VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass
open VG.Proof.Weierstrass.X86.Inv (wordClob)
open VG.Proof.Weierstrass.X86 (countLoop_ok)

structure Facts (I : Int × Int × Int) (p : Nat) : Prop where
  delta : |I.1|+64<2^30
  odd : I.2.1%2=1
  f : |I.2.1| ≤ p
  g : |I.2.2| ≤ p

theorem loop_ok {s : State} {base : Addr} {size n p B : Nat} {m x : Int}
    (hs : Scr s base size) (hn : 16 ≤ n) (hz : offset n 15 ≤ size)
    (hB : 0<B) (hB32 : B<2^32) (hp : p<2^(32*n+1))
    (hI : StateAt n base (1,m,x) s) (hc : w32 s.mem base 100=B)
    (facts : ∀ i<B,Facts (Divstep.divsteps (30*i) (1,m,x)) p) :
    WP isa (.loop (batch n) .ne) s fun z =>
      StateAt n base (Divstep.divsteps (30*B) (1,m,x)) z ∧
      Keeps wordClob s z ∧ Unch base (batchWrites n) s.mem z.mem := by
  let J := fun j u => Scr u base size ∧
    StateAt n base (Divstep.divsteps (30*(B-j)) (1,m,x)) u ∧
    w32 u.mem base 100=j ∧ Keeps wordClob s u ∧ Unch base (batchWrites n) s.mem u.mem
  refine countLoop_ok (Inv:=J) (n:=B) ?_ ?_ hB ?_
  · intro j u hj hjB hJ
    obtain ⟨hu,Iu,Cu,Ku,Ou⟩ := hJ
    have F := facts (B-j) (by omega)
    refine WP.mono (batch_ok hu hn hz Iu F.delta F.odd F.f F.g hp hj (by omega) Cu)
      fun z ⟨Iz,Cz,Zz,Kz,Oz⟩ => ⟨?_,Zz⟩
    refine ⟨hu.of_keeps Kz (by decide),?_,Cz,Ku.trans Kz,(Ou.trans Oz).mono (by
      intro w hw
      simpa only [List.mem_append,or_self] using hw)⟩
    rw [show 30*(B-(j-1))=30*(B-j)+30 by omega,Divstep.divsteps_add]
    exact Iz
  · intro u hJ
    obtain ⟨_,Iu,_,Ku,Ou⟩ := hJ
    simpa only [Nat.sub_zero] using (show StateAt n base (Divstep.divsteps (30*(B-0)) (1,m,x)) u ∧
      Keeps wordClob s u ∧ Unch base (batchWrites n) s.mem u.mem from ⟨Iu,Ku,Ou⟩)
  · exact ⟨hs,by simpa only [Nat.sub_self,Nat.mul_zero,Divstep.divsteps] using hI,hc,
      Keeps.refl _ _,Unch.refl _ _ _⟩

end VG.Proof.Rsa.X86.GcdBatch
