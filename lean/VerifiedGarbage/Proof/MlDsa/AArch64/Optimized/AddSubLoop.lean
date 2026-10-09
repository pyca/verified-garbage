import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.AddSubMem
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Pro

namespace VG.Proof.MlDsa.AArch64.Optimized.AddSub
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep Lanes)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (accK pR)
open VG.Proof.MlDsa.AArch64.Arith.Neon
open VG.Spec.MlDsa (q Poly coeffAt polyAt)

structure Inv (s₀ : State) (v : Nat → Nat) (i : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = coeffAddr (s₀.gpr .x0) (4*i)
  x1 : s.gpr .x1 = coeffAddr (s₀.gpr .x1) (4*i)
  consts : VConsts s
  keep : Keep [.x0,.x1,.x9,.x10,.x12] s₀ s
  frame : Frame [pR (s₀.gpr .x0)] s₀.mem s.mem
  coeff : ∀ k < 256, (coeffAt s.mem (s₀.gpr .x0) k).toNat =
    if k < 4*i then v k else (coeffAt s₀.mem (s₀.gpr .x0) k).toNat

theorem inv_step {s₀ s t : State} {v : Nat → Nat} {i : Nat}
    (hi : i < 64) (h : Inv s₀ v i s) {x : BitVec 128}
    (hm : t.mem = s.mem.write (s.gpr .x0) 16 x)
    (hx : Lanes x (fun e => v (4*i+e)))
    (hc : VConsts t) (h0 : t.gpr .x0 = s.gpr .x0 + 16)
    (h1 : t.gpr .x1 = s.gpr .x1 + 16) (hk : Keep [.x0,.x1,.x12] s t) :
    Inv s₀ v (i+1) t where
  x0 := by
    rw [h0,h.x0]
    have he := coeffAddr_add (s₀.gpr .x0) (4*i) 4
    simpa only [Nat.mul_add,Nat.mul_one,BitVec.ofNat_eq_ofNat] using he
  x1 := by
    rw [h1,h.x1]
    have he := coeffAddr_add (s₀.gpr .x1) (4*i) 4
    simpa only [Nat.mul_add,Nat.mul_one,BitVec.ofNat_eq_ofNat] using he
  consts := hc
  keep := (h.keep.trans hk).mono
  frame := by
    rw [hm,h.x0]
    exact h.frame.write (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega) (by omega))
  coeff k hk := by
    rw [hm,h.x0,coeffAt_write16 _ _ (by omega) _ hk]
    by_cases he : 4*i ≤ k ∧ k < 4*i+4
    · rw [ite_eq_left he,hx (k-4*i) (by omega),ite_eq_left (by omega)]
      exact congrArg v (by omega)
    · rw [ite_eq_right he,h.coeff k hk]
      have hh : (k < 4*(i+1)) = (k < 4*i) := propext (by omega)
      simp only [hh]

/-- Current input vectors still contain the original, as-yet-unprocessed coefficients. -/
theorem reads {op : Poly → Poly → Poly} {s₀ s : State} (hp : (accK op).pre s₀)
    {v : Nat → Nat} {i : Nat} (hi : i < 64) (h : Inv s₀ v i s) :
    Lanes (s.mem.read (s.gpr .x0) 16)
      (fun e => (coeffAt s₀.mem (s₀.gpr .x0) (4*i+e)).toNat) ∧
    Lanes (s.mem.read (s.gpr .x1) 16)
      (fun e => (coeffAt s₀.mem (s₀.gpr .x1) (4*i+e)).toNat) ∧
    InRegions (s.rd++s.wr) (s.gpr .x0) 16 ∧
    InRegions (s.rd++s.wr) (s.gpr .x1) 16 ∧ InRegions s.wr (s.gpr .x0) 16 := by
  have hrd := h.keep.rd.trans hp.1
  have hwr := h.keep.wr.trans hp.2.1
  have contains (p : Addr) : (pR p).Contains (coeffAddr p (4*i)) 16 :=
    Offset.contains_base _ (by omega) (by omega)
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro e he
    rw [h.x0,VG.Proof.MlDsa.AArch64.Arith.Neon.vword_read16 _ _ he,coeffAddr_add,← coeffAt_eq,h.coeff _ (by omega),ite_eq_right (by omega)]
  · intro e he
    rw [h.x1,VG.Proof.MlDsa.AArch64.Arith.Neon.vword_read16 _ _ he,coeffAddr_add,← coeffAt_eq,
      coeffAt_frame h.frame (by simpa using hp.2.2.1.symm) (by change 4*i+e < 256; omega)]
  · rw [hrd,hwr,h.x0]; exact ⟨_,by simp,contains _⟩
  · rw [hrd,hwr,h.x1]; exact ⟨_,by simp,contains _⟩
  · rw [hwr,h.x0]; exact ⟨_,by simp,contains _⟩

theorem pro_ok (s₀ : State) (v : Nat → Nat) :
    WP isa (.block (VG.Impl.MlDsa.AArch64.Arith.Neon.consts ++ ([.movz .x .x12 64 0] : List Instr))) s₀
      fun s => Inv s₀ v 0 s ∧ s.gpr .x12 = BitVec.ofNat 64 64 := by
  rw [WP.block_append_iff]
  refine WP.mono (consts_ok s₀) fun t ⟨hc,hm,hk⟩ => ?_
  have scalar : WP isa (.block [.movz .x .x12 64 0]) t fun u =>
      u.gpr .x12=BitVec.ofNat 64 64 ∧ u.mem=t.mem ∧ u.v=t.v := by
    arun [State.write]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.WP.keep [.x12] scalar (by decide))
    fun u ⟨⟨h12,hum,huv⟩,ku⟩ => ⟨?_,h12⟩
  have keep := hk.trans ku
  refine ⟨?_,?_,?_,keep.mono,?_,?_⟩
  · rw [keep.get .x0]; simp [coeffAddr]
  · rw [keep.get .x1]; simp [coeffAddr]
  · exact ⟨by rw [huv]; exact hc.q,by rw [huv]; exact hc.qi⟩
  · rw [hum,hm]; exact Frame.refl _ _
  · intro k _; rw [hum,hm]; simp

/-- Complete 64-iteration execution, retaining the original memory and ABI frame. -/
theorem run_ok (sub : Bool) {op : Poly → Poly → Poly} (s₀ : State) (hp : (accK op).pre s₀) :
    WP isa (VG.Impl.MlDsa.AArch64.Optimized.AddSub.code sub) s₀
      (Inv s₀ (fun k => result sub (coeffAt s₀.mem (s₀.gpr .x0) k).toNat
        (coeffAt s₀.mem (s₀.gpr .x1) k).toNat) 64) := by
  unfold VG.Impl.MlDsa.AArch64.Optimized.AddSub.code
  refine WP.seq (WP.mono (pro_ok s₀ (fun k => result sub (coeffAt s₀.mem (s₀.gpr .x0) k).toNat (coeffAt s₀.mem (s₀.gpr .x1) k).toNat)) fun s ⟨hs,hcnt⟩ => ?_)
  refine VG.Proof.MlDsa.AArch64.Arith.wp_countdown (cnt := .x12) (N := 64)
    (by decide) (by decide) (Inv s₀ _) (fun i hi t ht _ => ?_) hs hcnt
  obtain ⟨ha,hb,hra,hrb,hw⟩ := reads hp hi ht
  refine WP.mono (body_ok sub ht.consts ha hb
    (fun e he => hp.2.2.2.1 _ (by change 4*i+e < 256; omega))
    (fun e he => hp.2.2.2.2 _ (by change 4*i+e < 256; omega)) hra hrb hw)
    fun u ⟨x,hm,hx,hc,h0,h1,h12,hk⟩ => ?_
  exact ⟨inv_step hi ht hm hx hc h0 h1 hk,h12⟩
end VG.Proof.MlDsa.AArch64.Optimized.AddSub
