module

public import VerifiedGarbage.Proof.MlDsa.MontProductContract
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.MontProduct
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Lanes
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFrame
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Vec
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Word
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.MlDsa.Arith.Mem
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Pro
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem

/-! ### `MlDsa.AArch64.Optimized.MontProductMem`, which only this module used -/

section

/-! ## From `MontProductVec.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.MontProduct
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg Lanes)
open VG.Proof.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlDsa.Arith
open VG.Spec.MlDsa (q)

def result (a b : Nat) : Nat := mont (a*b) % q

/-- The selected seven-instruction REDC and two-instruction canonical correction. -/
theorem arithmetic_ok {s : State} (hc : VConsts s) {A B : Nat → Nat}
    (ha : Lanes (s.v .v0) A) (hb : Lanes (s.v .v1) B)
    (halt : ∀ e < 4, A e < 3*q) (hblt : ∀ e < 4, B e < 3*q)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, VChg [.v2,.v3,.v4,.v0] s t →
      Lanes (t.v .v0) (fun e => result (A e) (B e)) → WP isa (.block rest) t Q) :
    WP isa (.block (VG.Impl.MlDsa.AArch64.Optimized.MontProduct.arithmetic ++ rest)) s Q := by
  change WP isa (.block (VG.Impl.MlDsa.AArch64.Arith.Neon.mont .v0 .v1 ++
    (VG.Impl.MlDsa.AArch64.Arith.Neon.csub .v0 .v4 ++ rest))) s Q
  refine mont_ok (by decide) (by decide) hc.q hc.qi fun t ht hv => ?_
  have hl : Lanes (t.v .v0) (fun e => mont (A e * B e)) := by
    intro e he
    rw [hv, VG.Proof.MlKem.AArch64.vword_ofVWords _ _ _ _ he]
    have hm (i : Nat) (hi : i<4) :
        (redc (product (vword (s.v .v0) i) (vword (s.v .v1) i))).toNat = mont (A i*B i) := by
      rw [lazy_mont_word_nat _ _ (by rw [ha i hi]; exact halt i hi)
        (by rw [hb i hi]; exact hblt i hi),ha i hi,hb i hi]
    rcases (show e=0 ∨ e=1 ∨ e=2 ∨ e=3 by omega_using [he]) with rfl | rfl | rfl | rfl <;>
      exact hm _ (by decide)
  refine csub_ok (by decide) (hc.chg ht).lanes_q hl
    (fun e he => mont_lt (product_lt_qR (halt e he) (hblt e he))) fun u hu hlu =>
      k u (ht.trans hu).mono hlu
end VG.Proof.MlDsa.AArch64.Optimized.MontProduct

end

/-! ## From `MontProductMem.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.MontProduct
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg Lanes wp_ldrq wp_strq)
open VG.Proof.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlDsa.AArch64.Optimized.Response (StepKeep)
open VG.Spec.MlDsa (q)
/-- Two vector loads, the canonical arithmetic, and one vector store. -/
theorem group_ok {s : State} (hc : VConsts s) {A B : Nat → Nat}
    (ha : Lanes (s.mem.read (s.gpr .x1) 16) A)
    (hb : Lanes (s.mem.read (s.gpr .x2) 16) B)
    (halt : ∀ e < 4, A e < 3*q) (hblt : ∀ e < 4, B e < 3*q)
    (hra : InRegions (s.rd++s.wr) (s.gpr .x1) 16)
    (hrb : InRegions (s.rd++s.wr) (s.gpr .x2) 16)
    (hw : InRegions s.wr (s.gpr .x0) 16)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t v, StepKeep [.v0,.v1,.v2,.v3,.v4] s t →
      t.mem = s.mem.write (s.gpr .x0) 16 v →
      Lanes v (fun e => result (A e) (B e)) → WP isa (.block rest) t Q) :
    WP isa (.block (([.ldrq .v0 .x1 0,.ldrq .v1 .x2 0] : List Instr) ++
      VG.Impl.MlDsa.AArch64.Optimized.MontProduct.arithmetic ++ ([.strq .v0 .x0 0] : List Instr) ++ rest)) s Q := by
  simp only [List.append_assoc,List.cons_append,List.nil_append]
  refine wp_ldrq (by decide) rfl (by simpa using hra) fun a h1 => ?_
  refine wp_ldrq (by decide) rfl (by simpa only [h1.chg.rd,h1.chg.wr,h1.chg.gpr,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using hrb) fun b h2 => ?_
  have hk : VChg [.v0,.v1] s b := (h1.chg.trans h2.chg).mono (by decide)
  have hA : Lanes (b.v .v0) A := by
    rw [h2.get .v0,h1.v]; simpa using ha
  have hB : Lanes (b.v .v1) B := by
    rw [h2.v,h1.chg.mem,h1.chg.gpr]; simpa using hb
  refine arithmetic_ok (hc.chg hk) hA hB halt hblt fun c h3 hval => ?_
  have hk' : VChg [.v0,.v1,.v2,.v3,.v4] s c := (hk.trans h3).mono (by decide)
  refine wp_strq (by decide) rfl (by simpa only [hk'.wr,hk'.gpr,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using hw) fun d h4 => ?_
  refine k d (c.v .v0) ?_ ?_ hval
  · exact ((StepKeep.ofChg hk' (by decide)).trans (StepKeep.ofMem h4)).mono (by decide)
  · simp only [h4.mem,hk'.mem,hk'.gpr,BitVec.add_zero]

theorem body_ok {s : State} (hc : VConsts s) {A B : Nat → Nat}
    (ha : Lanes (s.mem.read (s.gpr .x1) 16) A)
    (hb : Lanes (s.mem.read (s.gpr .x2) 16) B)
    (halt : ∀ e < 4, A e < 3*q) (hblt : ∀ e < 4, B e < 3*q)
    (hra : InRegions (s.rd++s.wr) (s.gpr .x1) 16)
    (hrb : InRegions (s.rd++s.wr) (s.gpr .x2) 16)
    (hw : InRegions s.wr (s.gpr .x0) 16) :
    WP isa (.block (VG.Impl.MlDsa.AArch64.Optimized.MontProduct.body)) s fun t =>
      ∃ v, t.mem = s.mem.write (s.gpr .x0) 16 v ∧
        Lanes v (fun e => result (A e) (B e)) ∧ VConsts t ∧
        t.gpr .x0 = s.gpr .x0 + 16 ∧ t.gpr .x1 = s.gpr .x1 + 16 ∧ t.gpr .x2 = s.gpr .x2 + 16 ∧
        t.gpr .x12 = s.gpr .x12 - 1 ∧ VG.Proof.MlKem.AArch64.Keep [.x0,.x1,.x2,.x12] s t := by
  unfold VG.Impl.MlDsa.AArch64.Optimized.MontProduct.body
  have he : ([Instr.strq .v0 .x0 0, .addImm .x .x0 .x0 16,
      .addImm .x .x1 .x1 16,.addImm .x .x2 .x2 16,.subImm .x .x12 .x12 1] : List Instr) =
      [.strq .v0 .x0 0] ++ [.addImm .x .x0 .x0 16,.addImm .x .x1 .x1 16,.addImm .x .x2 .x2 16,.subImm .x .x12 .x12 1] := rfl
  rw [he, ← List.append_assoc]
  refine group_ok hc ha hb halt hblt hra hrb hw fun t v hk hm hl => ?_
  have ct : VConsts t := ⟨by rw [hk.vec .v16 (by decide)]; exact hc.q,
    by rw [hk.vec .v17 (by decide)]; exact hc.qi⟩
  have scalar : WP isa (.block [.addImm .x .x0 .x0 16,.addImm .x .x1 .x1 16,.addImm .x .x2 .x2 16,
      .subImm .x .x12 .x12 1]) t fun u =>
      u.mem=t.mem ∧ u.v=t.v ∧ u.gpr .x0=t.gpr .x0+16 ∧
      u.gpr .x1=t.gpr .x1+16 ∧ u.gpr .x2=t.gpr .x2+16 ∧ u.gpr .x12=t.gpr .x12-1 := by
    arun [State.write, BitVec.ofNat_eq_ofNat]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.WP.keep [.x0,.x1,.x2,.x12] scalar (by decide))
    fun u ⟨⟨hum,huv,h0,h1,h2,h12⟩,ku⟩ => ?_
  refine ⟨v, hum.trans hm, hl, ?_, ?_, ?_, ?_, ?_, (hk.keep.trans ku).mono⟩
  · exact ⟨by rw [huv]; exact ct.q, by rw [huv]; exact ct.qi⟩
  · simpa only [hk.keep.get .x0] using h0
  · simpa only [hk.keep.get .x1] using h1
  · simpa only [hk.keep.get .x2] using h2
  · simpa only [hk.keep.get .x12] using h12
end VG.Proof.MlDsa.AArch64.Optimized.MontProduct

end

end

end


/-! ## From `MontProductPre.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.MontProduct
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Arith (pR)

structure Pre (s : State) : Prop where
  a : pR (s.gpr .x1) ∈ s.rd++s.wr
  b : pR (s.gpr .x2) ∈ s.rd++s.wr
  out : pR (s.gpr .x0) ∈ s.wr
  oa : (pR (s.gpr .x0)).Disjoint (pR (s.gpr .x1))
  ob : (pR (s.gpr .x0)).Disjoint (pR (s.gpr .x2))
  pa : PositiveReduced s.mem (s.gpr .x1)
  pb : PositiveReduced s.mem (s.gpr .x2)

def contract : Contract isa where
  pre := Pre
  post s t := PolyIs t.mem (s.gpr .x0)
    (montgomeryMultiplyNTT (polyAt s.mem (s.gpr .x1)) (polyAt s.mem (s.gpr .x2)))
  pub s t := (∀r∈[Reg.x0,.x1,.x2],s.gpr r=t.gpr r) ∧ s.sp=t.sp

theorem pre {s : State} (h : (montProductContract abi).pre s) : Pre s := by
  sig_pre [montProductContract,montProductSig,abi,argRegs,stackBelow] at h
  obtain ⟨hr,hw,ha,hb,_,_,_,hpa,hpb⟩ := h
  exact ⟨by rw [hr]; simp [pR],by rw [hr]; simp [pR],by rw [hw]; simp [pR],ha,hb,hpa,hpb⟩
end VG.Proof.MlDsa.AArch64.Optimized.MontProduct

end

/-! ## From `MontProductLoop.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.MontProduct
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep Lanes)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (accK pR)
open VG.Proof.MlDsa.AArch64.Arith.Neon
open VG.Spec.MlDsa (q Poly)
open VG.Proof.MlDsa (coeffAt polyAt)

structure Inv (s₀ : State) (v : Nat → Nat) (i : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = coeffAddr (s₀.gpr .x0) (4*i)
  x1 : s.gpr .x1 = coeffAddr (s₀.gpr .x1) (4*i)
  x2 : s.gpr .x2 = coeffAddr (s₀.gpr .x2) (4*i)
  consts : VConsts s
  keep : Keep [.x0,.x1,.x2,.x9,.x10,.x12] s₀ s
  frame : Frame [pR (s₀.gpr .x0)] s₀.mem s.mem
  coeff : ∀ k < 256, (coeffAt s.mem (s₀.gpr .x0) k).toNat =
    if k < 4*i then v k else (coeffAt s₀.mem (s₀.gpr .x0) k).toNat

theorem inv_step {s₀ s t : State} {v : Nat → Nat} {i : Nat}
    (hi : i < 64) (h : Inv s₀ v i s) {x : BitVec 128}
    (hm : t.mem = s.mem.write (s.gpr .x0) 16 x)
    (hx : Lanes x (fun e => v (4*i+e)))
    (hc : VConsts t) (h0 : t.gpr .x0 = s.gpr .x0 + 16)
    (h1 : t.gpr .x1 = s.gpr .x1 + 16) (h2 : t.gpr .x2 = s.gpr .x2 + 16) (hk : Keep [.x0,.x1,.x2,.x12] s t) :
    Inv s₀ v (i+1) t where
  x0 := by
    rw [h0,h.x0]
    have he := coeffAddr_add (s₀.gpr .x0) (4*i) 4
    simpa only [Nat.mul_add,Nat.mul_one,BitVec.ofNat_eq_ofNat] using he
  x1 := by
    rw [h1,h.x1]
    have he := coeffAddr_add (s₀.gpr .x1) (4*i) 4
    simpa only [Nat.mul_add,Nat.mul_one,BitVec.ofNat_eq_ofNat] using he
  x2 := by
    rw [h2,h.x2]
    have he := coeffAddr_add (s₀.gpr .x2) (4*i) 4
    simpa only [Nat.mul_add,Nat.mul_one,BitVec.ofNat_eq_ofNat] using he
  consts := hc
  keep := (h.keep.trans hk).mono
  frame := by
    rw [hm,h.x0]
    exact h.frame.write (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi]))
  coeff k hk := by
    rw [hm,h.x0,coeffAt_write16 _ _ (by omega_using [hi]) _ hk]
    by_cases he : 4*i ≤ k ∧ k < 4*i+4
    · rw [ite_eq_left he,hx (k-4*i) (by omega_using [he]),ite_eq_left (by omega_using [he])]
      exact congrArg v (by omega_using [he])
    · rw [ite_eq_right he,h.coeff k hk]
      have hh : (k < 4*(i+1)) = (k < 4*i) := propext (by omega_using [he])
      simp only [hh]

/-- Both read-only inputs retain their original coefficients throughout the loop. -/
theorem reads {s₀ s : State} (hp : Pre s₀)
    {v : Nat → Nat} {i : Nat} (hi : i < 64) (h : Inv s₀ v i s) :
    Lanes (s.mem.read (s.gpr .x1) 16)
      (fun e => (coeffAt s₀.mem (s₀.gpr .x1) (4*i+e)).toNat) ∧
    Lanes (s.mem.read (s.gpr .x2) 16)
      (fun e => (coeffAt s₀.mem (s₀.gpr .x2) (4*i+e)).toNat) ∧
    InRegions (s.rd++s.wr) (s.gpr .x1) 16 ∧
    InRegions (s.rd++s.wr) (s.gpr .x2) 16 ∧ InRegions s.wr (s.gpr .x0) 16 := by
  have contains (p : Addr) : (pR p).Contains (coeffAddr p (4*i)) 16 :=
    Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro e he
    rw [h.x1,VG.Proof.MlDsa.AArch64.Arith.Neon.vword_read16 _ _ he,coeffAddr_add,← coeffAt_eq,
      coeffAt_frame h.frame (by simpa using hp.oa.symm) (by change 4*i+e<256; omega_using [hi, he])]
  · intro e he
    rw [h.x2,VG.Proof.MlDsa.AArch64.Arith.Neon.vword_read16 _ _ he,coeffAddr_add,← coeffAt_eq,
      coeffAt_frame h.frame (by simpa using hp.ob.symm) (by change 4*i+e<256; omega_using [hi, he])]
  · rw [h.keep.rd,h.keep.wr,h.x1]; exact ⟨_,hp.a,contains _⟩
  · rw [h.keep.rd,h.keep.wr,h.x2]; exact ⟨_,hp.b,contains _⟩
  · rw [h.keep.wr,h.x0]; exact ⟨_,hp.out,contains _⟩

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
  refine ⟨?_,?_,?_,?_,keep.mono,?_,?_⟩
  · rw [keep.get .x0]; simp [coeffAddr]
  · rw [keep.get .x1]; simp [coeffAddr]
  · rw [keep.get .x2]; simp [coeffAddr]
  · exact ⟨by rw [huv]; exact hc.q,by rw [huv]; exact hc.qi⟩
  · rw [hum,hm]; exact Frame.refl _ _
  · intro k _; rw [hum,hm]; simp

/-- Complete 64-iteration execution, retaining the original memory and ABI frame. -/
theorem run_ok (s₀ : State) (hp : Pre s₀) :
    WP isa (VG.Impl.MlDsa.AArch64.Optimized.MontProduct.code) s₀
      (Inv s₀ (fun k => result (coeffAt s₀.mem (s₀.gpr .x1) k).toNat
        (coeffAt s₀.mem (s₀.gpr .x2) k).toNat) 64) := by
  unfold VG.Impl.MlDsa.AArch64.Optimized.MontProduct.code
  refine WP.seq (WP.mono (pro_ok s₀ (fun k => result (coeffAt s₀.mem (s₀.gpr .x1) k).toNat (coeffAt s₀.mem (s₀.gpr .x2) k).toNat)) fun s ⟨hs,hcnt⟩ => ?_)
  refine VG.Proof.MlDsa.AArch64.Arith.wp_countdown (cnt := .x12) (N := 64)
    (by decide) (by decide) (Inv s₀ _) (fun i hi t ht _ => ?_) hs hcnt
  obtain ⟨ha,hb,hra,hrb,hw⟩ := reads hp hi ht
  refine WP.mono (body_ok ht.consts ha hb
    (fun e he => hp.pa _ (by change 4*i+e < 256; omega_using [hi, he]))
    (fun e he => hp.pb _ (by change 4*i+e < 256; omega_using [hi, he])) hra hrb hw)
    fun u ⟨x,hm,hx,hc,h0,h1,h2,h12,hk⟩ => ?_
  exact ⟨inv_step hi ht hm hx hc h0 h1 h2 hk,h12⟩
end VG.Proof.MlDsa.AArch64.Optimized.MontProduct

end
