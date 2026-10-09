import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedHintField
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedHintState
import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedPairedHints

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc)
open VG.Proof.MlDsa.AArch64.Optimized

def pairedHintWrites (i : Nat) : List (Ptr × Nat) := [(hP i,2048),(t1P,2176)]

def pairedHintRowChk (p : Params) (i : Nat) : Bool :=
  inB (sgB p) cP 1024 && inB (sgB p) (t0P p i) 2048 && inB (sgB p) (hP i) 2048 &&
  inB (sgB p) (wP p i) 2048 && inB (sgB p) t1P 2176 &&
  inB (sgW p) (hP i) 2048 && inB (sgW p) t1P 2176 &&
  sepB (sgR p) (sgW p) cP 1024 (hP i) 2048 && sepB (sgR p) (sgW p) cP 1024 t1P 2176 &&
  sepB (sgR p) (sgW p) (t0P p i) 2048 (hP i) 2048 && sepB (sgR p) (sgW p) (t0P p i) 2048 t1P 2176 &&
  sepB (sgR p) (sgW p) (hP i) 2048 t1P 2176 &&
  sepB (sgR p) (sgW p) (hP i) 2048 (wP p i) 2048 && sepB (sgR p) (sgW p) (wP p i) 2048 t1P 2176 &&
  decide (p.γ₂∈gamma2s)

theorem pairedHintRowChk_ok {p : Params} (hp : Ok3 p) : ∀i<p.k,i+1<p.k → pairedHintRowChk p i=true := by
  rcases hp with rfl|rfl|rfl <;> decide

theorem pairedHint_inputs {p : Params} {S : Nat} {σ s : State} {t i : Nat}
    (hi : i+1<p.k) (h : PositiveIH p S σ t i s) :
    (∀j<2,PosPolyIs s.mem (pairPolyPtr (pa s (t0P p i)) j) (T0v p σ (i+j))) ∧
    (∀j<2,SignedPolyIs s.mem (pairPolyPtr (pa s (hP i)) j)
      ((W'v p σ (p.ℓ*t) (i+j)).map fun r=>ofInt (lowBits p.γ₂ r)) (-(p.γ₂:Int)) p.γ₂) ∧
    (∀j<2,NatPolyIs s.mem (pairPolyPtr (pa s (wP p i)) j)
      ((W'v p σ (p.ℓ*t) (i+j)).map fun r=>(highBits p.γ₂ r).toNat)) := by
  refine ⟨?_,?_,?_⟩
  · intro j hj
    rw [paired_pS_addr]
    simpa only [Nat.add_assoc] using h.1.b.l.k.d.t0 (i+j) (by omega)
  · intro j hj
    rw [paired_pS_addr]
    simpa only [Nat.add_assoc,R0v,W'v,VG.Proof.MlDsa.Sign.r0F] using h.1.low j (by omega)
  · intro j hj
    rw [paired_pS_addr]
    simpa only [Nat.add_assoc,WHighv] using h.1.high (i+j) (by omega)

theorem pairedHint_ready {p : Params} {S : Nat} {σ s : State} {t i : Nat}
    (hp : Ok3 p) (hi : i+1<p.k) (roots : PairedRoots S s) (h : PositiveIH p S σ t i s) :
    Paired.PairedHintReady cP (t0P p i) (hP i) (wP p i) t1P p.γ₂ s := by
  have checks := pairedHintRowChk_ok hp i (by omega) hi
  simp only [pairedHintRowChk,Bool.and_eq_true,decide_eq_true_eq] at checks
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hc,hs⟩,hl⟩,hh⟩,hw⟩,hwl⟩,hww⟩,hcl⟩,hcw⟩,hsl⟩,hsw⟩,hlw⟩,hlh⟩,hhw⟩,hg⟩ := checks
  obtain ⟨hsk,hlo,hhi⟩ := pairedHint_inputs hi h
  refine pairedHintReady_layout h.1.b.l.st.lay roots hc hs hh hl hw hwl hww hcl hcw hsl hsw hlw hlh hhw
    ⟨h.1.b.c.bound,fun j hj => (hsk j hj).bound⟩ (fun j hj=>?_) hg
  have hg' := VG.Proof.MlDsa.AArch64.Round.isG_of_mem hg
  exact Response.responseDecomposed_parts hg' _ (Response.hintLow_exact hg' (hlo j hj)) (Response.hintHigh_exact (hhi j hj))

theorem pairedHintRow_ok {p : Params} {S : Nat} {σ s : State} {t i : Nat}
    (hp : Ok3 p) (hi : i+1<p.k) (roots : PairedRoots S s) (h : PositiveIH p S σ t i s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.hintPairRow p i) s fun a =>
      PPostB S s a (pairedHintWrites i) ∧ a.gpr .x24=s.gpr .x24 ∧
      HintIs a.mem (pa s (hP i)) 2 ((List.range 2).map fun j=>Hv p σ (p.ℓ*t) (i+j)) ∧
      a.gpr .x0=BitVec.ofNat 64 (hintOnes ((List.range 2).map fun j=>Hv p σ (p.ℓ*t) (i+j))+
        if normRq ((List.range 2).map fun j=>CT0v p σ (p.ℓ*t) (i+j))<p.γ₂ then 4294967296 else 0) := by
  have checks := pairedHintRowChk_ok hp i (by omega) hi
  simp only [pairedHintRowChk,Bool.and_eq_true,decide_eq_true_eq] at checks
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hc,hs⟩,hl⟩,hh⟩,hw⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩ := checks
  obtain ⟨hsk,hlo,hhi⟩ := pairedHint_inputs hi h
  refine WP.mono (pairedHintAt_field_layout h.1.b.l.st.lay hc hs hl hh hw
    (pairedHint_ready hp hi roots h) h.1.b.c hsk hlo hhi) fun a ⟨ha,h24,hints,ret⟩ => ?_
  change HintIs a.mem _ 2 ((List.range 2).map fun j=>Vector.zipWith _ (CT0v p σ (p.ℓ*t) (i+j)) (W'v p σ (p.ℓ*t) (i+j))) at hints
  change a.gpr .x0=BitVec.ofNat 64 (hintOnes ((List.range 2).map fun j=>Vector.zipWith _
    (CT0v p σ (p.ℓ*t) (i+j)) (W'v p σ (p.ℓ*t) (i+j)))+_) at ret
  simp only [hintRow_value] at hints ret
  exact ⟨ha,h24,hints,ret⟩

end VG.Proof.MlDsa.AArch64.Sign
