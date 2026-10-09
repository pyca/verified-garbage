import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedMasks
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedDot

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Optimized

structure PositiveICw (p : Params) (S : Nat) (σ : State) (t i : Nat) (s : State) : Prop where
  masks : PositiveICm p S σ t p.ℓ s
  w : Fam s (wBase p) i (Wv p σ (p.ℓ*t))

def positiveRowChk (p : Params) (i : Nat) : Bool :=
  optimizedDotChk p i && positiveIcmChk p (dotWrites p i) p.ℓ &&
    famChk (sgR p) (sgW p) (dotWrites p i) (wBase p) i

theorem positiveRowChk_ok {p : Params} (hp : Ok3 p) : ∀i<p.k,positiveRowChk p i=true := by
  rcases hp with rfl | rfl | rfl <;> decide

theorem positiveRowW_ok {p : Params} {S : Nat} {σ s : State} {t i : Nat}
    (hp : Ok3 p) (hi : i<p.k) (h : PositiveICw p S σ t i s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.rowW p i) s (PositiveICw p S σ t (i+1)) := by
  have hc := positiveRowChk_ok hp i hi
  simp only [positiveRowChk,Bool.and_eq_true] at hc
  obtain ⟨⟨hd,hm⟩,hw⟩ := hc
  have hA j (hj : j<p.ℓ) : PolyIs s.mem
      (pa s (aP p i 0)+BitVec.ofNat 64 (1024*j)) (Am p σ i j) := by
    have he : p.ℓ*i+j<p.k*p.ℓ := by
      have hl := Nat.mul_le_mul_left p.ℓ (show i+1≤p.k by omega)
      simp only [Nat.mul_add,Nat.mul_one] at hl
      rw [Nat.mul_comm p.k p.ℓ]; omega
    have hv := h.masks.l.k.d.im.A (p.ℓ*i+j) he
    rw [aVal_ij hj] at hv
    change PolyIs s.mem (pa s (pS (aBase p+(p.ℓ*i+j)))) _ at hv
    rw [← Nat.add_assoc,dot_pS_addr] at hv
    simpa only [aP,Nat.add_zero] using hv
  have hB j (hj : j<p.ℓ) : PosPolyIs s.mem
      (pa s (yhP p 0)+BitVec.ofNat 64 (1024*j)) (YHv p σ (p.ℓ*t) j) := by
    have hv := h.masks.yh j hj
    change PosPolyIs s.mem (pa s (pS (yhBase p+j))) _ at hv
    rw [dot_pS_addr] at hv
    simpa only [yhP,Nat.add_zero] using hv
  refine WP.mono_syms (optimizedDot_ok hp hd ⟨h.masks.l.st,h.masks.l.k.d.roots⟩
    (fun j hj => (PosPolyIs.of_canonical (hA j hj)).bound)
    (fun j hj => (hB j hj).bound)) fun u ⟨_,_,hP,hv⟩ hy => ?_
  refine ⟨h.masks.step hP hy hm,(h.w.keep h.masks.l.st.lay hP hw).snoc ?_⟩
  change PolyIs u.mem (pa u (wP p i)) _
  have he : dotNTT
      (fun j => polyAt s.mem (pa s (aP p i 0)+BitVec.ofNat 64 (1024*j)))
      (fun j => polyAt s.mem (pa s (yhP p 0)+BitVec.ofNat 64 (1024*j))) p.ℓ =
      dotNTT (Am p σ i) (YHv p σ (p.ℓ*t)) p.ℓ := by
    unfold dotNTT
    apply congrArg (fun xs : List Poly => xs.foldl add zero)
    apply List.map_congr_left
    intro j hj
    rw [List.mem_range] at hj
    dsimp only
    rw [(hA j hj).2,(hB j hj).value]
  rw [he] at hv
  exact hv

/-- All matrix rows use the fused dot/inverse kernel while preserving the
mask vectors and the secret transforms for the later response checks. -/
theorem positiveRows_ok {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (hp : Ok3 p) (h : PositiveICm p S σ t p.ℓ s) :
    WP isa (VG.Impl.MlDsa.AArch64.Call.seqR
      (Impl.MlDsa.AArch64.Sign.Optimized.rowW p) 0 p.k) s (PositiveICw p S σ t p.k) := by
  simpa only [Nat.zero_add] using seqR_ok (I := fun i s => PositiveICw p S σ t i s) p.k 0
    (fun i _ hi s hs => positiveRowW_ok hp (by omega) hs) s ⟨h,by simp [Fam]⟩

end VG.Proof.MlDsa.AArch64.Sign
