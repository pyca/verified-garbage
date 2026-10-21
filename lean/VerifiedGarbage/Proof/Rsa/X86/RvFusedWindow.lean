module

import VerifiedGarbage.Proof.Rsa.X86.RvFusedBit
import VerifiedGarbage.Proof.Rsa.X86.RvWindowOps
import VerifiedGarbage.Proof.Rsa.X86.RvCount
import VerifiedGarbage.Proof.Rsa.X86.RvWrite
public import VerifiedGarbage.Proof.Rsa.X86.RvFusedState

/-! Four fused bits per public-width exponent window. -/
@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

 theorem FI.mono {g : Geo} {s0 s : State} {A AW V A' AW' V' : Nat → Nat} {n : Nat}
    {st : VG.Proof.Rsa.Fused.State} (h : FI g s0 A AW V n st s)
    (ha : ∀ j ∈ liveM, A j=A' j) (hw : ∀ j ∈ [wRc,wR], AW j=AW' j)
    (hv : ∀ d ∈ [sInv,sCnt,sTc,sCand,sWin], V d=V' d) :
    FI g s0 A' AW' V' n st s := by
  obtain ⟨z,zl,root,h⟩ := h
  refine ⟨z,zl,root,h.mono (fun j hj => ⟨hj,?_⟩) (fun j hj => ⟨hj,hw j hj⟩) (fun d hd => ⟨hd,?_⟩)⟩
  · rcases List.mem_append.mp hj with low | high
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at low
      rcases low with rfl | rfl <;> rfl
    · have ny : j≠mY := (show ∀ j ∈ liveM, j≠mY from by decide) j high
      have nz : j≠0 := (show ∀ j ∈ liveM, j≠0 from by decide) j high
      simp only [fusedA,upd_ne _ _ ny,upd_ne _ _ nz]
      exact ha j high
  · simp only [fusedKeepSlots,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | rfl | exact hv _ (by decide)

 theorem FI.windowTop {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {n : Nat}
    {st : VG.Proof.Rsa.Fused.State} (h : FI g s0 A AW V n st s) :
    WP isa (.block VG.Impl.Rsa.X86.RecoverRt.windowTop) s fun t =>
      FI g s0 A AW (upd V sWin (AW wRc*16/2^(32*g.W))) n st t := by
  obtain ⟨z,zl,root,h⟩ := h
  refine WP.mono (h.windowTop_ok (by decide)) fun t ⟨ht,_⟩ => ⟨z,zl,root,?_⟩
  refine ht.mono (fun j hj => ⟨hj,rfl⟩) (fun j hj => ⟨hj,rfl⟩) fun d hd => ⟨List.mem_cons_of_mem _ hd,?_⟩
  simp only [fusedKeepSlots,List.mem_cons,List.not_mem_nil,or_false] at hd
  rcases hd with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

 theorem FI.shiftUp {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {n : Nat}
    {st : VG.Proof.Rsa.Fused.State} (h : FI g s0 A AW V n st s) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.shiftUp s fun t =>
      FI g s0 A (upd AW wRc (AW wRc*16%2^(32*g.W))) V n st t := by
  obtain ⟨z,zl,root,h⟩ := h
  refine WP.mono (h.shiftUp_W (by decide) (by decide)) fun t ⟨ht,_⟩ => ⟨z,zl,root,?_⟩
  exact ht.mono (fun j hj => ⟨hj,rfl⟩)
    (fun j hj => ⟨List.mem_cons_of_mem _ hj,rfl⟩) (fun d hd => ⟨hd,rfl⟩)

 theorem FI.cntNext {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {n : Nat}
    {st : VG.Proof.Rsa.Fused.State} (h : FI g s0 A AW V n st s)
    (lo : 1≤V sCnt) (hi : V sCnt<2^32) :
    WP isa (.block cntNext) s fun t =>
      FI g s0 A AW (upd V sCnt (V sCnt-1)) n st t ∧ t.zf=some (decide (V sCnt-1=0)) := by
  obtain ⟨z,zl,root,h⟩ := h
  refine WP.mono (h.cntNext_ok (by decide) lo hi) fun t ⟨ht,zt⟩ => ⟨⟨z,zl,root,?_⟩,zt⟩
  refine ht.mono (fun j hj => ⟨hj,rfl⟩) (fun j hj => ⟨hj,rfl⟩) fun d hd => ⟨List.mem_cons_of_mem _ hd,?_⟩
  simp only [fusedKeepSlots,List.mem_cons,List.not_mem_nil,or_false] at hd
  rcases hd with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

 theorem fusedBits_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {n : Nat}
    {st : VG.Proof.Rsa.Fused.State} (h : FI g s0 A AW V n st s)
    (value : A mBase=n) (modulus : A aN=n) (zero : A aZ=0)
    (bound : n<2^(64*g.n)) (inverse : (n*V sInv+1)%2^32=0)
    (odd : n%2=1) (hn : 1<n) (one : A aO=2^(64*g.n)%n) (neg : A aNg=n-2^(64*g.n)%n)
    (candidate : V sCand<100) (yl : st.value<n) (small : V sWin<16) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.fusedBits s fun t =>
      FI g s0 A AW V n (VG.Proof.Rsa.Fused.bits n (V sCand+2) 4 (V sWin) st) t := by
  unfold VG.Impl.Rsa.X86.RecoverRt.fusedBits
  simp only [seqs,VG.Proof.Rsa.Fused.bits]
  refine WP.seq (WP.mono (fusedBit_ok h value modulus zero bound inverse odd hn one neg candidate yl small
    (by decide : 3≤3)) fun u1 h1 => ?_)
  refine WP.seq (WP.mono (fusedBit_ok h1 value modulus zero bound inverse odd hn one neg candidate
    (VG.Proof.Rsa.Fused.step_lt _ _ _ _ (by omega)) small (by decide : 2≤3)) fun u2 h2 => ?_)
  refine WP.seq (WP.mono (fusedBit_ok h2 value modulus zero bound inverse odd hn one neg candidate
    (VG.Proof.Rsa.Fused.step_lt _ _ _ _ (by omega)) small (by decide : 1≤3)) fun u3 h3 => ?_)
  exact fusedBit_ok h3 value modulus zero bound inverse odd hn one neg candidate
    (VG.Proof.Rsa.Fused.step_lt _ _ _ _ (by omega)) small (by decide : 0≤3)

def FWI (g : Geo) (s0 : State) (A AW V : Nat → Nat) (n E C i : Nat) (s : State) : Prop :=
  ∃ w, FI g s0 A (upd AW wRc (E*16^i%2^(32*g.W)))
    (upd (upd V sWin w) sCnt (C-i)) n
    (VG.Proof.Rsa.Fused.eval n (V sCand+2) (E*16^i/2^(32*g.W))) s

 theorem fusedWindow_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {n E C i : Nat}
    (h : FWI g s0 A AW V n E C i s)
    (value : A mBase=n) (modulus : A aN=n) (zero : A aZ=0)
    (bound : n<2^(64*g.n)) (inverse : (n*V sInv+1)%2^32=0)
    (odd : n%2=1) (hn : 1<n) (one : A aO=2^(64*g.n)%n) (neg : A aNg=n-2^(64*g.n)%n)
    (candidate : V sCand<100) (hi : i<C) (cb : C<2^32) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.fusedWindow s fun t =>
      FWI g s0 A AW V n E C (i+1) t ∧ t.zf=some (decide (C-(i+1)=0)) := by
  obtain ⟨w,h⟩ := h
  let P := 2^(32*g.W)
  let w' := (E*16^i%P)*16/P
  have ppos : 0<P := Nat.two_pow_pos _
  have wl : w'<16 := by
    dsimp only [w']
    rw [Nat.div_lt_iff_lt_mul ppos]
    have := Nat.mod_lt (E*16^i) ppos
    omega
  unfold VG.Impl.Rsa.X86.RecoverRt.fusedWindow
  simp only [seqs]
  refine WP.seq (WP.mono h.windowTop fun u1 h1 => ?_)
  refine WP.seq (WP.mono h1.shiftUp fun u2 h2 => ?_)
  refine WP.seq (WP.mono (fusedBits_ok h2 value modulus zero bound (by exact inverse) odd hn one neg
    (by exact candidate) (by rw [VG.Proof.Rsa.Fused.eval_value n _ _ hn]; exact Nat.mod_lt _ (by omega))
    (by exact wl)) fun u3 h3 => ?_)
  have next : VG.Proof.Rsa.Fused.bits n (V sCand+2) 4 w'
      (VG.Proof.Rsa.Fused.eval n (V sCand+2) (E*16^i/P)) =
      VG.Proof.Rsa.Fused.eval n (V sCand+2) (E*16^(i+1)/P) := by
    rw [VG.Proof.Rsa.Fused.four_eval _ _ _ _ hn wl]
    congr 1
    have eq := VG.Proof.Mont.X86.Dynamic.window_exponent (E*16^i) P ppos
    dsimp only [w']
    rw [Nat.mul_comm (E*16^i/P) 16]
    simpa only [Nat.pow_succ,←Nat.mul_assoc] using eq.symm
  change FI g s0 A _ _ n (VG.Proof.Rsa.Fused.bits n (V sCand+2) 4 w'
    (VG.Proof.Rsa.Fused.eval n (V sCand+2) (E*16^i/P))) u3 at h3
  rw [next] at h3
  refine WP.mono (h3.cntNext (by change 1≤C-i; omega) (by change C-i<2^32; omega)) fun t ⟨ht,zt⟩ => ?_
  refine ⟨⟨w',ht.mono (fun _ _ => rfl) ?_ ?_⟩, ?_⟩
  · intro j hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl|rfl
    · change (E*16^i%P)*16%P=E*16^(i+1)%P
      rw [Nat.mod_mul_mod,Nat.pow_succ,←Nat.mul_assoc]
    · rfl
  · intro d hd
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl|rfl|rfl|rfl|rfl
    all_goals rfl
  · change t.zf=some (decide (C-(i+1)=0))
    change t.zf=some (decide (C-i-1=0)) at zt
    simpa only [Nat.sub_sub] using zt

 theorem fusedWindowLoop_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {n E C : Nat}
    (h : FWI g s0 A AW V n E C 0 s)
    (value : A mBase=n) (modulus : A aN=n) (zero : A aZ=0)
    (bound : n<2^(64*g.n)) (inverse : (n*V sInv+1)%2^32=0)
    (odd : n%2=1) (hn : 1<n) (one : A aO=2^(64*g.n)%n) (neg : A aNg=n-2^(64*g.n)%n)
    (candidate : V sCand<100) (lo : 0<C) (cb : C<2^32) :
    WP isa (.loop VG.Impl.Rsa.X86.RecoverRt.fusedWindow .ne) s
      (FWI g s0 A AW V n E C C) := by
  refine WP.loop (M := isa)
    (fun left u => ∃ i, i+left=C ∧ 0<left ∧ FWI g s0 A AW V n E C i u)
    ?_ C s ⟨0,by omega,lo,h⟩
  intro left u ⟨i,total,pos,hu⟩
  refine WP.mono (fusedWindow_ok hu value modulus zero bound inverse odd hn one neg candidate
    (by omega) cb) fun t ⟨ht,zt⟩ => ?_
  by_cases last : i+1=C
  · left
    refine ⟨?_,last ▸ ht⟩
    change t.zf.map (!·)=some false
    simp [zt,last]
  · right
    refine ⟨?_,left-1,by omega,i+1,by omega,by omega,ht⟩
    change t.zf.map (!·)=some true
    simp [zt,show C-(i+1)≠0 by omega]

end VG.Proof.Rsa.X86.Recover
