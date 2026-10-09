import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MontDotReads

namespace VG.Proof.MlDsa.AArch64.Optimized.MontDot
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (pR)
open VG.Proof.MlDsa.AArch64.Arith.Neon

def result (s : State) (n k : Nat) : Nat :=
  mont (dotNat (fun j=>inputWord s .x1 j k) (fun j=>inputWord s .x2 j k) n)%q

theorem result_current {s₀ s : State} {v : Nat→Nat} {i n e : Nat}
    (hi : i<64) (hn : n≤7) (he : e<4) (hp : Pre n s₀) (h : Inv s₀ v i s) :
    mont (dotAccum s 0 n e).toNat%q=result s₀ n (4*i+e) := by
  have ha (j : Nat) (hj : j<n) :=  input_current hi hp h (r:=Reg.x1) (by simp) (j:=j) hj he
  have hb (j : Nat) (hj : j<n) :=  input_current hi hp h (r:=Reg.x2) (by simp) (j:=j) hj he
  have halt : ∀j<n,(dotInput s .x1 0 j e).toNat<3*q := by
    intro j hj;rw [ha j hj];exact hp.bound .x1 (by simp) j hj _ (by omega)
  have hblt : ∀j<n,(dotInput s .x2 0 j e).toNat<3*q := by
    intro j hj;rw [hb j hj];exact hp.bound .x2 (by simp) j hj _ (by omega)
  rw [dotAccum,dotWord_nat _ _ hn halt hblt,dotNat_congr _ _ _ _ n ha hb]
  rfl

theorem run_ok {n : Nat} (hn : 0<n) (hn7 : n≤7) (s₀ : State) (hp : Pre n s₀) :
    WP isa (Impl.MlDsa.AArch64.Optimized.MontDot.dot n) s₀ (Inv s₀ (result s₀ n) 64) := by
  unfold Impl.MlDsa.AArch64.Optimized.MontDot.dot
  refine WP.seq (WP.mono (pro_ok s₀ (result s₀ n)) fun s ⟨hs,hcnt⟩=>?_)
  refine VG.Proof.MlDsa.AArch64.Arith.wp_countdown (cnt:=.x12) (N:=64)
    (by decide) (by decide) (Inv s₀ _) (fun i hi s h _=>?_) hs hcnt
  have hr (j : Nat) (hj : j<n) :=  And.intro (reads hi hp h (r:=Reg.x1) (by simp) (j:=j) hj)
    (reads hi hp h (r:=Reg.x2) (by simp) (j:=j) hj)
  have ha : ∀j<n,∀e<4,(dotInput s .x1 0 j e).toNat<3*q := by
    intro j hj e he
    rw [input_current hi hp h (r:=Reg.x1) (by simp) (j:=j) hj he]
    exact hp.bound .x1 (by simp) j hj _ (by omega)
  have hb : ∀j<n,∀e<4,(dotInput s .x2 0 j e).toNat<3*q := by
    intro j hj e he
    rw [input_current hi hp h (r:=Reg.x2) (by simp) (j:=j) hj he]
    exact hp.bound .x2 (by simp) j hj _ (by omega)
  have hw : InRegions s.wr (s.gpr .x0) 16 := by
    rw [h.keep.wr,h.x0]
    exact ⟨_,hp.output,Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.mono (body_ok hn hn7 h.consts hr ha hb hw) fun t ⟨x,hm,hx,hc,h0,h1,h2,h12,hk⟩=>?_
  refine ⟨inv_step hi h hm ?_ hc h0 h1 h2 hk,h12⟩
  intro e he
  exact (hx e he).trans (result_current hi hn7 he hp h)

end VG.Proof.MlDsa.AArch64.Optimized.MontDot
