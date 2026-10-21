module

import VerifiedGarbage.Proof.Rsa.X86.RvFusedInit
import VerifiedGarbage.Proof.Rsa.X86.RvFusedFinish
import VerifiedGarbage.Proof.Rsa.X86.RvCandidateNext
import VerifiedGarbage.Proof.Rsa.X86.RvWindowExp
public import VerifiedGarbage.Proof.Rsa.RecoverFused
public import VerifiedGarbage.Proof.Rsa.X86.RvSquareStep
public import VerifiedGarbage.Proof.Rsa.X86.RvCandidateExp
public import VerifiedGarbage.Proof.Rsa.X86.RvFusedWindow
import VerifiedGarbage.Proof.Rsa.X86.RvCandidateExp
import VerifiedGarbage.Proof.Rsa.X86.RvFusedWindow

/-! One complete fused recovery candidate. -/
@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

abbrev fusedModel (n e j : Nat) := VG.Proof.Rsa.Fused.eval n (j+2) e

def fusedCandStart : Prog isa := .seq (.seq (.seq VG.Impl.Rsa.X86.RecoverRt.alignStart
  (.loop VG.Impl.Rsa.X86.RecoverRt.alignBody .ne)) VG.Impl.Rsa.X86.RecoverRt.fusedInit) (.block windowCount)

theorem fusedCandStart_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {n eLen dLen : Nat}
    (h : KS g s0 A liveM AW [wR] V slotsExp s)
    (zero : A aZ=0) (positive : 0<n) (one : A aO=2^(64*g.n)%n) (candidate : V sCand<100)
    (ae : CallArgument s0 g.B g.Z 7 (BitVec.ofNat 32 eLen))
    (ad : CallArgument s0 g.B g.Z 9 (BitVec.ofNat 32 dLen))
    (rb : AW wR<2^(8*(dLen+eLen))) (limit : 8*(dLen+eLen)≤16384)
    (wide : 8*(dLen+eLen)<32*g.W) :
    WP isa fusedCandStart s (FWI g s0 A AW V n (alignedExp g (AW wR) eLen dLen) (2*(dLen+eLen)) 0) := by
  let E := alignedExp g (AW wR) eLen dLen
  let C := 2*(dLen+eLen)
  let P := 2^(32*g.W)
  have aligned : AW wR*16^alignShifts g eLen dLen%P=E := by
    have eq := aligned_value (L := 32*g.W) rb (by omega) (by omega)
    rwa [show (32*g.W-8*(dLen+eLen))/4=alignShifts g eLen dLen by unfold alignShifts; omega] at eq
  have ef : E<P := by
    change AW wR*2^(32*g.W-8*(dLen+eLen))<2^(32*g.W)
    calc
      _ < 2^(8*(dLen+eLen))*2^(32*g.W-8*(dLen+eLen)) :=
        Nat.mul_lt_mul_of_pos_right rb (Nat.two_pow_pos _)
      _ = _ := by rw [←Nat.pow_add]; congr 1; omega
  unfold fusedCandStart
  apply WP.assoc'
  apply WP.assoc'
  refine WP.seq (WP.mono (alignStart_ok h zero candidate ae ad wide rb) fun u1 h1 => ?_)
  refine WP.seq (WP.mono (alignLoop_ok h1 (by unfold alignShifts; omega)
    (by have := geo_wide g h.upper; unfold alignShifts; omega)) fun u2 h2 => ?_)
  unfold AI at h2
  rw [Nat.sub_self,aligned,upd_twice] at h2
  refine WP.seq (WP.mono (fusedInit_ok h2 positive (by exact zero) (by exact one)) fun u3 h3 => ?_)
  refine WP.mono (h3.windowCount ae ad (by omega)) fun u4 h4 => ?_
  have initial : FWI g s0 A AW V n E C 0 u4 := by
    refine ⟨0,?_⟩
    have initEval : VG.Proof.Rsa.Fused.eval n (V sCand+2) (E*16^0/P)=VG.Proof.Rsa.Fused.start n 1 := by
      rw [Nat.pow_zero,Nat.mul_one,Nat.div_eq_of_lt ef,VG.Proof.Rsa.Fused.eval_zero]
    rw [initEval]
    refine h4.mono ?_ ?_ ?_
    · intro j hj
      simp only [liveM,List.mem_cons,List.not_mem_nil,or_false] at hj
      rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
    · intro j hj
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
      rcases hj with rfl|rfl
      · change E=E*16^0%P
        rw [Nat.pow_zero,Nat.mul_one,Nat.mod_eq_of_lt ef]
      · rfl
    · intro d hd
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hd
      rcases hd with rfl|rfl|rfl|rfl|rfl <;> rfl
  exact initial

 theorem fusedCand_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {n eLen dLen : Nat}
    (h : KS g s0 A liveM AW [wR] V slotsExp s)
    (value : A mBase=n) (modulus : A aN=n) (zero : A aZ=0)
    (bound : n<2^(64*g.n)) (inverse : (n*V sInv+1)%2^32=0)
    (odd : n%2=1) (hn : 1<n) (one : A aO=2^(64*g.n)%n) (neg : A aNg=n-2^(64*g.n)%n)
    (candidate : V sCand<100)
    (ae : CallArgument s0 g.B g.Z 7 (BitVec.ofNat 32 eLen))
    (ad : CallArgument s0 g.B g.Z 9 (BitVec.ofNat 32 dLen))
    (rb : AW wR<2^(8*(dLen+eLen))) (lo : 0<8*(dLen+eLen)) (limit : 8*(dLen+eLen)≤16384)
    (wide : 8*(dLen+eLen)<32*g.W) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.fusedCand s fun t =>
      let st := fusedModel n (AW wR) (V sCand)
      ∃ z, z<n ∧ (∀ r, st.root=some r → z=r) ∧
        SI g s0 A AW (upd V sCand (V sCand+1)) n 0 0 (z,st.done,st.root.isSome) t ∧
        t.zf=some (!(decide (V sCand+1<100) && !st.root.isSome)) := by
  let E := alignedExp g (AW wR) eLen dLen
  let C := 2*(dLen+eLen)
  let P := 2^(32*g.W)
  have positive : 0<n := by omega
  have aligned : AW wR*16^alignShifts g eLen dLen%P=E := by
    have eq := aligned_value (L := 32*g.W) rb (by omega) (by omega)
    rwa [show (32*g.W-8*(dLen+eLen))/4=alignShifts g eLen dLen by unfold alignShifts; omega] at eq
  have ef : E<P := by
    change AW wR*2^(32*g.W-8*(dLen+eLen))<2^(32*g.W)
    calc
      _ < 2^(8*(dLen+eLen))*2^(32*g.W-8*(dLen+eLen)) :=
        Nat.mul_lt_mul_of_pos_right rb (Nat.two_pow_pos _)
      _ = _ := by rw [←Nat.pow_add]; congr 1; omega
  unfold VG.Impl.Rsa.X86.RecoverRt.fusedCand
  simp only [seqs]
  refine WP.seq (WP.mono (alignStart_ok h zero candidate ae ad wide rb) fun u1 h1 => ?_)
  refine WP.seq (WP.mono (alignLoop_ok h1 (by unfold alignShifts; omega)
    (by have := geo_wide g h.upper; unfold alignShifts; omega)) fun u2 h2 => ?_)
  unfold AI at h2
  rw [Nat.sub_self,aligned,upd_twice] at h2
  refine WP.seq (WP.mono (fusedInit_ok h2 positive (by exact zero) (by exact one)) fun u3 h3 => ?_)
  refine WP.seq (WP.mono (h3.windowCount ae ad (by omega)) fun u4 h4 => ?_)
  have initial : FWI g s0 A AW V n E C 0 u4 := by
    refine ⟨0,?_⟩
    have initEval : VG.Proof.Rsa.Fused.eval n (V sCand+2) (E*16^0/P)=VG.Proof.Rsa.Fused.start n 1 := by
      rw [Nat.pow_zero,Nat.mul_one,Nat.div_eq_of_lt ef,VG.Proof.Rsa.Fused.eval_zero]
    rw [initEval]
    refine h4.mono ?_ ?_ ?_
    · intro j hj
      simp only [liveM,List.mem_cons,List.not_mem_nil,or_false] at hj
      rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
    · intro j hj
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
      rcases hj with rfl|rfl
      · change E=E*16^0%P
        rw [Nat.pow_zero,Nat.mul_one,Nat.mod_eq_of_lt ef]
      · rfl
    · intro d hd
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hd
      rcases hd with rfl|rfl|rfl|rfl|rfl <;> rfl
  refine WP.seq (WP.mono (fusedWindowLoop_ok initial value modulus zero bound inverse odd hn one neg candidate
    (by dsimp only [C]; omega) (by dsimp only [C]; omega)) fun u5 h5 => ?_)
  obtain ⟨w,h5⟩ := h5
  have complete : E*16^C/P=AW wR := by
    have eq := windows_value (r := AW wR) (c := 8*(dLen+eLen)) (L := 32*g.W) (by omega) (by omega)
    have div : 8*(dLen+eLen)/4=C := by dsimp only [C]; omega
    simpa only [div] using eq
  rw [complete] at h5
  refine WP.seq (WP.mono (fusedFinish_ok h5 (by change C-C=0; omega)) fun u6 ⟨z,zl,root,h6⟩ => ?_)
  have h6' : SI g s0 A AW V n 0 0
      (z,(fusedModel n (AW wR) (V sCand)).done,(fusedModel n (AW wR) (V sCand)).root.isSome) u6 := by
    refine h6.mono (fun j hj => ⟨hj,rfl⟩) (fun j hj => ⟨hj,?_⟩) (fun d hd => ⟨hd,?_⟩)
    · simp only [List.mem_singleton] at hj
      subst j
      rfl
    · simp only [slotsSq,List.mem_cons,List.not_mem_nil,or_false] at hd
      rcases hd with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  refine WP.mono (candNext_ok h6' (by decide) (by decide) (by exact candidate) rfl) fun t ⟨ht,zt⟩ => ?_
  refine ⟨z,zl,root,ht.mono (fun j hj => ⟨hj,rfl⟩) (fun j hj => ⟨hj,rfl⟩)
    (fun d hd => ⟨List.mem_cons_of_mem _ hd,?_⟩),zt⟩
  simp only [slotsSq,List.mem_cons,List.not_mem_nil,or_false] at hd
  rcases hd with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

end VG.Proof.Rsa.X86.Recover
