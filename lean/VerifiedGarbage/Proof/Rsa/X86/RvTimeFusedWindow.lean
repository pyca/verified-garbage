module

import VerifiedGarbage.Proof.Rsa.X86.RvTimeFusedBit
public import VerifiedGarbage.Proof.Rsa.X86.RvFusedWindow
import VerifiedGarbage.Proof.Rsa.X86.RvTimeCheck
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.Rsa.X86.RvFusedState
public import VerifiedGarbage.Proof.Rsa.X86.RvTimeBase
import VerifiedGarbage.Proof.Rsa.X86.RvTimeFusedCheck

/-! Fused exponent windows have a fixed public count. -/
@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

theorem fusedBits_relCT {g : Geo} (pg : PubG g) {s0 t0 : State} {A B AW BW V W : Nat → Nat}
    {n : Nat} {st tt : VG.Proof.Rsa.Fused.State}
    (valueA : A mBase=n) (valueB : B mBase=n)
    (modA : A aN=n) (modB : B aN=n) (zeroA : A aZ=0) (zeroB : B aZ=0)
    (bound : n<2^(64*g.n)) (invA : (n*V sInv+1)%2^32=0) (invB : (n*W sInv+1)%2^32=0)
    (odd : n%2=1) (hn : 1<n)
    (oneA : A aO=2^(64*g.n)%n) (oneB : B aO=2^(64*g.n)%n)
    (negA : A aNg=n-2^(64*g.n)%n) (negB : B aNg=n-2^(64*g.n)%n) (cand : V sCand=W sCand) (limit : V sCand<100)
    (smallA : V sWin<16) (smallB : W sWin<16) (yl : st.value<n) (zl : tt.value<n) :
    RelCT isa (fun s t => FI g s0 A AW V n st s ∧ FI g t0 B BW W n tt t)
      VG.Impl.Rsa.X86.RecoverRt.fusedBits (fun _ _ => True) := by
  have stage (a b : VG.Proof.Rsa.Fused.State) (al : a.value<n) (bl : b.value<n)
      (k : Nat) (hk : k≤3) :
      RelCT isa (fun s t => FI g s0 A AW V n a s ∧ FI g t0 B BW W n b t)
        (VG.Impl.Rsa.X86.RecoverRt.fusedBit k) (fun s t =>
          FI g s0 A AW V n (VG.Proof.Rsa.Fused.step n (V sCand+2) (decide (V sWin/2^k%2=1)) a) s ∧
          FI g t0 B BW W n (VG.Proof.Rsa.Fused.step n (W sCand+2) (decide (W sWin/2^k%2=1)) b) t) :=
    stage_relCT (fusedBit_relCT pg valueA valueB modA modB zeroA zeroB bound invA invB
      (by omega) cand limit smallA smallB hk)
      (fun _ h => fusedBit_ok h valueA modA zeroA bound invA odd hn oneA negA limit al smallA hk)
      (fun _ h => fusedBit_ok h valueB modB zeroB bound invB odd hn oneB negB
        (by rw [←cand]; exact limit) bl smallB hk)
  unfold VG.Impl.Rsa.X86.RecoverRt.fusedBits
  simp only [seqs]
  refine VG.RelCT.seq (stage st tt yl zl 3 (by decide)) ?_
  refine VG.RelCT.seq (stage _ _ (VG.Proof.Rsa.Fused.step_lt _ _ _ _ (by omega))
    (VG.Proof.Rsa.Fused.step_lt _ _ _ _ (by omega)) 2 (by decide)) ?_
  refine VG.RelCT.seq (stage _ _ (VG.Proof.Rsa.Fused.step_lt _ _ _ _ (by omega))
    (VG.Proof.Rsa.Fused.step_lt _ _ _ _ (by omega)) 1 (by decide)) ?_
  exact (stage _ _ (VG.Proof.Rsa.Fused.step_lt _ _ _ _ (by omega))
    (VG.Proof.Rsa.Fused.step_lt _ _ _ _ (by omega)) 0 (by decide)).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)

theorem FI.stage {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {n : Nat}
    {st : VG.Proof.Rsa.Fused.State} (h : FI g s0 A AW V n st s) : MulPost g s := by
  obtain ⟨_,_,_,h⟩ := h
  exact KS.stage h

theorem FI.trace {g : Geo} (pg : PubG g) {c : Prog isa}
    (check : (VG.Taint.check taint τA c (VG.Taint.hintOf taint τA c)).isSome=true)
    {s0 t0 s t : State} {A B AW BW V W : Nat → Nat} {n : Nat}
    {st tt : VG.Proof.Rsa.Fused.State} (h : FI g s0 A AW V n st s) (j : FI g t0 B BW W n tt t)
    {tr ur : List Leak} {sf tf : State} (es : Exec isa c s tr sf) (et : Exec isa c t ur tf) : tr=ur := by
  obtain ⟨_,_,_,h⟩ := h
  obtain ⟨_,_,_,j⟩ := j
  exact pub_trace pg check h j es et

theorem fusedWindow_relCT {g : Geo} (pg : PubG g) {s0 t0 : State} {A B AW BW V W : Nat → Nat}
    {n E F C i : Nat}
    (valueA : A mBase=n) (valueB : B mBase=n)
    (modA : A aN=n) (modB : B aN=n) (zeroA : A aZ=0) (zeroB : B aZ=0)
    (bound : n<2^(64*g.n)) (invA : (n*V sInv+1)%2^32=0) (invB : (n*W sInv+1)%2^32=0)
    (odd : n%2=1) (hn : 1<n)
    (oneA : A aO=2^(64*g.n)%n) (oneB : B aO=2^(64*g.n)%n)
    (negA : A aNg=n-2^(64*g.n)%n) (negB : B aNg=n-2^(64*g.n)%n)
    (cand : V sCand=W sCand) (limit : V sCand<100) :
    RelCT isa (fun s t => FWI g s0 A AW V n E C i s ∧ FWI g t0 B BW W n F C i t)
      VG.Impl.Rsa.X86.RecoverRt.fusedWindow (fun _ _ => True) := by
  intro s t tr ur sf tf ⟨⟨w,hs⟩,⟨v,ht⟩⟩ es et
  cases es with
  | @seq _ _ _ u1 _ _ _ e1 er =>
  cases et with
  | @seq _ _ _ v1 _ _ _ f1 fr =>
  have eq1 := hs.trace pg fusedWindowTopCheck ht e1 f1
  have hu1 := wp_result hs.windowTop e1
  have hv1 := wp_result ht.windowTop f1
  cases er with
  | @seq _ _ _ u2 _ _ _ e2 er =>
  cases fr with
  | @seq _ _ _ v2 _ _ _ f2 fr =>
  have eq2 := hu1.trace pg fusedShiftUpCheck hv1 e2 f2
  have hu2 := wp_result hu1.shiftUp e2
  have hv2 := wp_result hv1.shiftUp f2
  have small (x : Nat) : (x%2^(32*g.W))*16/2^(32*g.W)<16 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    have := Nat.mod_lt x (Nat.two_pow_pos (32*g.W))
    omega
  have la : (VG.Proof.Rsa.Fused.eval n (V sCand+2) (E*16^i/2^(32*g.W))).value<n := by
    rw [VG.Proof.Rsa.Fused.eval_value n _ _ hn]
    exact Nat.mod_lt _ (by omega)
  have lb : (VG.Proof.Rsa.Fused.eval n (W sCand+2) (F*16^i/2^(32*g.W))).value<n := by
    rw [VG.Proof.Rsa.Fused.eval_value n _ _ hn]
    exact Nat.mod_lt _ (by omega)
  cases er with
  | @seq _ _ _ u3 _ _ _ e3 e4 =>
  cases fr with
  | @seq _ _ _ v3 _ _ _ f3 f4 =>
  have eq3 := (fusedBits_relCT pg valueA valueB modA modB zeroA zeroB bound
    (by exact invA) (by exact invB) odd hn oneA oneB negA negB
    (by exact cand) (by exact limit) (by exact small (E*16^i)) (by exact small (F*16^i)) la lb _ _ _ _ _ _ ⟨hu2,hv2⟩ e3 f3).1
  have hu3 := wp_result (fusedBits_ok hu2 valueA modA zeroA bound (by exact invA) odd hn
    oneA negA (by exact limit) la (by exact small (E*16^i))) e3
  have hv3 := wp_result (fusedBits_ok hv2 valueB modB zeroB bound (by exact invB) odd hn
    oneB negB (by change W sCand<100; rw [←cand]; exact limit) lb (by exact small (F*16^i))) f3
  have eq4 := hu3.trace pg cntNextCheck hv3 e4 f4
  exact ⟨by rw [eq1,eq2,eq3,eq4],trivial⟩

end VG.Proof.Rsa.X86.Recover
