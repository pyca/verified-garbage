import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallSecondChecks

namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.AArch64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.Sha3 (stateAt)

structure SecondReady (P : Sp) (σ : State) (c : Spec.MlDsa.IPoly) (i : Nat)
    (w : BitVec 64) (Y : List Byte) (s : State) : Prop where
  env : Env P σ s
  parser : Parser P.a c i w s
  pos : (s.gpr .x0).toNat≤136
  next : Spec.Sha3.squeezeFrom 136 (stateAt s.mem P.scr) (s.gpr .x0).toNat 136=Y

 theorem second_relCT (v : Proof.Sha3.AArch64.Permutation) (hc : PrefixTiming v.callee)
    {P : Sp} {σ₁ σ₂ : State} {τ i : Nat} {h : Array Bool} {c : Spec.MlDsa.IPoly}
    {w : BitVec 64} {Y : List Byte} (hp₁ : SpOk P σ₁) (hp₂ : SpOk P σ₂)
    (hi : i≤256) (hY : Y.length=136)
    (hsign : ∀j,i≤j → j<256 → (w >>> (j-i)).getLsbD 0=h.getD (j+τ-256) false) :
    RelCT isa (fun s t => SecondReady P σ₁ c i w Y s ∧ SecondReady P σ₂ c i w Y t ∧
      s.sp=t.sp ∧ s.gpr .x0=t.gpr .x0)
      (Impl.MlDsa.AArch64.Optimized.Ball.second v.callee) (fun _ _ => True) := by
  intro s t ts tt u z ⟨hs,ht,hsp,h0⟩ es et
  cases es with | seq eb es =>
   cases es with | seq ec es =>
    cases es with | seq er el =>
     cases et with | seq fb et =>
      cases et with | seq fc et =>
       cases et with | seq fr fl =>
        have ep := Exec.seq eb (Exec.seq ec er)
        have fp := Exec.seq fb (Exec.seq fc fr)
        have hp := hc _ _ _ _ _ _ (by
          refine ⟨agree_of hsp (fun r hr => ?_),fun r hr => by simp [VectorTaint.ofRegs,RegSet.mem_ofList] at hr⟩
          rcases mem2 hr with rfl|rfl
          · exact h0
          · exact hs.env.x25.trans ht.env.x25.symm) ep fp
        obtain ⟨_,_,eq₁,h₁⟩ := secondPrefix_ok v hp₁ hs.env hs.parser hY hs.pos hs.next
        obtain ⟨_,_,eq₂,h₂⟩ := secondPrefix_ok v hp₂ ht.env ht.parser hY ht.pos ht.next
        obtain ⟨_,rfl⟩ := Exec.det ep eq₁
        obtain ⟨_,rfl⟩ := Exec.det fp eq₂
        have he := chunk_relCT (τ := τ) (h := h) (by rw [hY]; decide) (by rw [hY]; decide) hi
          (by rw [hY]; exact (a_scr' hp₁ (by decide)).symm) hsign _ _ _ _ _ _
          ⟨h₁.ready,h₂.ready,by rw [h₁.env.sp,h₂.env.sp,← hs.env.sp,← ht.env.sp]; exact hsp⟩ el fl
        refine ⟨?_,trivial⟩
        have hh := congr (congrArg (fun xs ys : List Leak => xs ++ ys) hp.1) he.1
        simpa only [List.append_assoc] using hh
end VG.Proof.MlDsa.AArch64.Optimized.Ball
