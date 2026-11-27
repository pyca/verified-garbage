module

import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.Round.Mem
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.AddSub
meta import VerifiedGarbage.Proof.MlDsa.Round.Mem
meta import VerifiedGarbage.Proof.MlKem.AArch64.Common
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.AddSub
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Lanes
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFrame
public import VerifiedGarbage.Proof.MlDsa.Arith.Mem
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Pro
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Vec
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.AddSub
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Lanes
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFrame
meta import VerifiedGarbage.Proof.MlDsa.Arith.Mem
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Pro
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Vec
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! ### `MlDsa.AArch64.Optimized.AddSubLoop`, which only this module used -/

section

/-! ## From `AddSubVec.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.AddSub
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg Lanes wp_vop lanes_add lanes_sub)
open VG.Proof.MlDsa.AArch64.Arith.Neon
open VG.Spec.MlDsa (q)

/-- Exact measured vector addition, including unsigned conditional reduction. -/
theorem add_ok {s : State} (hc : VConsts s) {A B : Nat → Nat}
    (ha : Lanes (s.v .v0) A) (hb : Lanes (s.v .v1) B)
    (halt : ∀ e < 4, A e < q) (hblt : ∀ e < 4, B e < q)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, VChg [.v0,.v4] s t →
      Lanes (t.v .v0) (fun e => (A e + B e) % q) → WP isa (.block rest) t Q) :
    WP isa (.block (VG.Impl.MlDsa.AArch64.Optimized.AddSub.arithmetic false ++ rest)) s Q := by
  simp only [VG.Impl.MlDsa.AArch64.Optimized.AddSub.arithmetic, Bool.false_eq_true,
    ↓reduceIte, List.cons_append, List.nil_append]
  refine wp_vop (d := .v0) rfl fun t ht => ?_
  have hsum : Lanes (t.v .v0) (fun e => A e + B e) := by
    rw [ht.v]
    exact (lanes_add ha hb).congr fun e he => Nat.mod_eq_of_lt (by
      have := halt e he; have := hblt e he; simp only [VG.Spec.MlDsa.q] at *; omega_arith)
  refine csub_ok (by decide) (hc.chg ht.chg).lanes_q hsum
    (fun e he => by have := halt e he; have := hblt e he; omega_arith) fun u hu hv =>
      k u (ht.chg.trans hu).mono hv

/-- Exact measured vector subtraction, with q added before the subtraction. -/
theorem sub_ok {s : State} (hc : VConsts s) {A B : Nat → Nat}
    (ha : Lanes (s.v .v0) A) (hb : Lanes (s.v .v1) B)
    (halt : ∀ e < 4, A e < q) (hblt : ∀ e < 4, B e < q)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, VChg [.v0,.v4] s t →
      Lanes (t.v .v0) (fun e => (A e + q - B e) % q) → WP isa (.block rest) t Q) :
    WP isa (.block (VG.Impl.MlDsa.AArch64.Optimized.AddSub.arithmetic true ++ rest)) s Q := by
  simp only [VG.Impl.MlDsa.AArch64.Optimized.AddSub.arithmetic, ↓reduceIte,
    List.cons_append, List.nil_append]
  refine wp_vop (d := .v0) rfl fun t ht => wp_vop (d := .v0) rfl fun u hu => ?_
  have hsum : Lanes (t.v .v0) (fun e => A e + q) := by
    rw [ht.v]
    exact (lanes_add ha hc.lanes_q).congr fun e he => Nat.mod_eq_of_lt (by
      have := halt e he; change A e < 8380417 at this
      change A e + 8380417 < 2^32; omega_arith)
  have hb' : Lanes (t.v .v1) B := by rw [ht.get .v1]; exact hb
  have hdiff : Lanes (u.v .v0) (fun e => A e + q - B e) := by
    rw [hu.v]
    exact (lanes_sub hsum hb').congr fun e he => by
      have := halt e he; have := hblt e he
      simp only [VG.Spec.MlDsa.q] at *
      omega_arith
  refine csub_ok (by decide) (hc.chg (ht.chg.trans hu.chg)).lanes_q hdiff
    (fun e he => by have := halt e he; have := hblt e he; omega_arith) fun v hv hl =>
      k v ((ht.chg.trans hu.chg).trans hv).mono hl
end VG.Proof.MlDsa.AArch64.Optimized.AddSub

end

/-! ## From `AddSubMem.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.AddSub
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg Lanes wp_ldrq wp_strq)
open VG.Proof.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlDsa.AArch64.Optimized.Response (StepKeep)
open VG.Spec.MlDsa (q)

def result (sub : Bool) (a b : Nat) : Nat :=
  (if sub then a + q - b else a + b) % q

theorem arithmetic_ok (sub : Bool) {s : State} (hc : VConsts s) {A B : Nat → Nat}
    (ha : Lanes (s.v .v0) A) (hb : Lanes (s.v .v1) B)
    (halt : ∀ e < 4, A e < q) (hblt : ∀ e < 4, B e < q)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, VChg [.v0,.v4] s t →
      Lanes (t.v .v0) (fun e => result sub (A e) (B e)) → WP isa (.block rest) t Q) :
    WP isa (.block (VG.Impl.MlDsa.AArch64.Optimized.AddSub.arithmetic sub ++ rest)) s Q := by
  cases sub
  · exact add_ok hc ha hb halt hblt k
  · exact sub_ok hc ha hb halt hblt k

/-- Two vector loads, the canonical arithmetic, and one vector store. -/
theorem group_ok (sub : Bool) {s : State} (hc : VConsts s) {A B : Nat → Nat}
    (ha : Lanes (s.mem.read (s.gpr .x0) 16) A)
    (hb : Lanes (s.mem.read (s.gpr .x1) 16) B)
    (halt : ∀ e < 4, A e < q) (hblt : ∀ e < 4, B e < q)
    (hra : InRegions (s.rd++s.wr) (s.gpr .x0) 16)
    (hrb : InRegions (s.rd++s.wr) (s.gpr .x1) 16)
    (hw : InRegions s.wr (s.gpr .x0) 16)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t v, StepKeep [.v0,.v1,.v4] s t →
      t.mem = s.mem.write (s.gpr .x0) 16 v →
      Lanes v (fun e => result sub (A e) (B e)) → WP isa (.block rest) t Q) :
    WP isa (.block (([.ldrq .v0 .x0 0,.ldrq .v1 .x1 0] : List Instr) ++
      VG.Impl.MlDsa.AArch64.Optimized.AddSub.arithmetic sub ++ ([.strq .v0 .x0 0] : List Instr) ++ rest)) s Q := by
  simp only [List.append_assoc,List.cons_append,List.nil_append]
  refine wp_ldrq (by decide) rfl (by simpa using hra) fun a h1 => ?_
  refine wp_ldrq (by decide) rfl (by simpa only [h1.chg.rd,h1.chg.wr,h1.chg.gpr,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using hrb) fun b h2 => ?_
  have hk : VChg [.v0,.v1] s b := (h1.chg.trans h2.chg).mono (by decide)
  have hA : Lanes (b.v .v0) A := by
    rw [h2.get .v0,h1.v]; simpa using ha
  have hB : Lanes (b.v .v1) B := by
    rw [h2.v,h1.chg.mem,h1.chg.gpr]; simpa using hb
  refine arithmetic_ok sub (hc.chg hk) hA hB halt hblt fun c h3 hval => ?_
  have hk' : VChg [.v0,.v1,.v4] s c := (hk.trans h3).mono (by decide)
  refine wp_strq (by decide) rfl (by simpa only [hk'.wr,hk'.gpr,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using hw) fun d h4 => ?_
  refine k d (c.v .v0) ?_ ?_ hval
  · exact ((StepKeep.ofChg hk' (by decide)).trans (StepKeep.ofMem h4)).mono (by decide)
  · simp only [h4.mem,hk'.mem,hk'.gpr,BitVec.add_zero]

theorem body_ok (sub : Bool) {s : State} (hc : VConsts s) {A B : Nat → Nat}
    (ha : Lanes (s.mem.read (s.gpr .x0) 16) A)
    (hb : Lanes (s.mem.read (s.gpr .x1) 16) B)
    (halt : ∀ e < 4, A e < q) (hblt : ∀ e < 4, B e < q)
    (hra : InRegions (s.rd++s.wr) (s.gpr .x0) 16)
    (hrb : InRegions (s.rd++s.wr) (s.gpr .x1) 16)
    (hw : InRegions s.wr (s.gpr .x0) 16) :
    WP isa (.block (VG.Impl.MlDsa.AArch64.Optimized.AddSub.body sub)) s fun t =>
      ∃ v, t.mem = s.mem.write (s.gpr .x0) 16 v ∧
        Lanes v (fun e => result sub (A e) (B e)) ∧ VConsts t ∧
        t.gpr .x0 = s.gpr .x0 + 16 ∧ t.gpr .x1 = s.gpr .x1 + 16 ∧
        t.gpr .x12 = s.gpr .x12 - 1 ∧ VG.Proof.MlKem.AArch64.Keep [.x0,.x1,.x12] s t := by
  unfold VG.Impl.MlDsa.AArch64.Optimized.AddSub.body
  have he : ([Instr.strq .v0 .x0 0, .addImm .x .x0 .x0 16,
      .addImm .x .x1 .x1 16,.subImm .x .x12 .x12 1] : List Instr) =
      [.strq .v0 .x0 0] ++ [.addImm .x .x0 .x0 16,.addImm .x .x1 .x1 16,.subImm .x .x12 .x12 1] := rfl
  rw [he, ← List.append_assoc]
  refine group_ok sub hc ha hb halt hblt hra hrb hw fun t v hk hm hl => ?_
  have ct : VConsts t := ⟨by rw [hk.vec .v16 (by decide)]; exact hc.q,
    by rw [hk.vec .v17 (by decide)]; exact hc.qi⟩
  have scalar : WP isa (.block [.addImm .x .x0 .x0 16,.addImm .x .x1 .x1 16,
      .subImm .x .x12 .x12 1]) t fun u =>
      u.mem=t.mem ∧ u.v=t.v ∧ u.gpr .x0=t.gpr .x0+16 ∧
      u.gpr .x1=t.gpr .x1+16 ∧ u.gpr .x12=t.gpr .x12-1 := by
    arun [State.write, BitVec.ofNat_eq_ofNat]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.WP.keep [.x0,.x1,.x12] scalar (by decide))
    fun u ⟨⟨hum,huv,h0,h1,h12⟩,ku⟩ => ?_
  refine ⟨v, hum.trans hm, hl, ?_, ?_, ?_, ?_, (hk.keep.trans ku).mono⟩
  · exact ⟨by rw [huv]; exact ct.q, by rw [huv]; exact ct.qi⟩
  · simpa only [hk.keep.get .x0] using h0
  · simpa only [hk.keep.get .x1] using h1
  · simpa only [hk.keep.get .x12] using h12
end VG.Proof.MlDsa.AArch64.Optimized.AddSub

end

/-! ## From `AddSubLoop.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.AddSub
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
      (Offset.contains_base _ (by omega_arith) (by omega_arith))
  coeff k hk := by
    rw [hm,h.x0,coeffAt_write16 _ _ (by omega_arith) _ hk]
    by_cases he : 4*i ≤ k ∧ k < 4*i+4
    · rw [ite_eq_left he,hx (k-4*i) (by omega_arith),ite_eq_left (by omega_arith)]
      exact congrArg v (by omega_arith)
    · rw [ite_eq_right he,h.coeff k hk]
      have hh : (k < 4*(i+1)) = (k < 4*i) := propext (by omega_arith)
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
    Offset.contains_base _ (by omega_arith) (by omega_arith)
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro e he
    rw [h.x0,VG.Proof.MlDsa.AArch64.Arith.Neon.vword_read16 _ _ he,coeffAddr_add,← coeffAt_eq,h.coeff _ (by omega_arith),ite_eq_right (by omega_arith)]
  · intro e he
    rw [h.x1,VG.Proof.MlDsa.AArch64.Arith.Neon.vword_read16 _ _ he,coeffAddr_add,← coeffAt_eq,
      coeffAt_frame h.frame (by simpa using hp.2.2.1.symm) (by change 4*i+e < 256; omega_arith)]
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
    (fun e he => hp.2.2.2.1 _ (by change 4*i+e < 256; omega_arith))
    (fun e he => hp.2.2.2.2 _ (by change 4*i+e < 256; omega_arith)) hra hrb hw)
    fun u ⟨x,hm,hx,hc,h0,h1,h12,hk⟩ => ?_
  exact ⟨inv_step hi ht hm hx hc h0 h1 hk,h12⟩
end VG.Proof.MlDsa.AArch64.Optimized.AddSub

end

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.AddSub
open VG VG.AArch64
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (accK acc_agree accSat)
open VG.Proof.MlDsa (polyAt)

private theorem correct (sub : Bool) (op : Spec.MlDsa.Poly → Spec.MlDsa.Poly → Spec.MlDsa.Poly)
    (hval : ∀ s, (accK op).pre s → ∀ i < 256,
      result sub (Proof.MlDsa.coeffAt s.mem (s.gpr .x0) i).toNat
        (Proof.MlDsa.coeffAt s.mem (s.gpr .x1) i).toNat =
        ((op (polyAt s.mem (s.gpr .x0)) (polyAt s.mem (s.gpr .x1)))[i]!).val)
    (s : State) (hp : (accK op).pre s) :
    ∃ tr t, Exec isa (VG.Impl.MlDsa.AArch64.Optimized.AddSub.code sub) s tr t ∧
      abiPreserved s t ∧ (accK op).post s t := by
  obtain ⟨tr,t,he,hi⟩ := run_ok sub s hp
  refine ⟨tr,t,he,VG.Proof.MlKem.AArch64.abi_of rfl ?_ he ?_,
    polyIs_of_toNat fun i hit => ?_⟩
  · cases sub <;> decide +kernel
  · cases sub <;> decide +kernel
  · have hlt : i < 256 := hit
    rw [hi.coeff i hlt,ite_eq_left (by omega_using [hlt])]
    exact hval s hp i hlt

theorem add_correct (s : State) (hp : (accK Spec.MlDsa.add).pre s) :
    ∃ tr t, Exec isa (VG.Impl.MlDsa.AArch64.Optimized.AddSub.code false) s tr t ∧
      abiPreserved s t ∧ (accK Spec.MlDsa.add).post s t := by
  apply correct false Spec.MlDsa.add ?_ s hp
  intro a ha i hi
  rw [add_get _ _ hi, val_add']
  simp only [result, Bool.false_eq_true, ↓reduceIte,polyAt_val ha.2.2.2.1 hi,
    polyAt_val ha.2.2.2.2 hi]

theorem sub_correct (s : State) (hp : (accK Spec.MlDsa.sub).pre s) :
    ∃ tr t, Exec isa (VG.Impl.MlDsa.AArch64.Optimized.AddSub.code true) s tr t ∧
      abiPreserved s t ∧ (accK Spec.MlDsa.sub).post s t := by
  apply correct true Spec.MlDsa.sub ?_ s hp
  intro a ha i hi
  rw [sub_get _ _ hi, val_sub,condSub_eq]
  · simp only [result, ↓reduceIte,polyAt_val ha.2.2.2.1 hi,polyAt_val ha.2.2.2.2 hi]
  · have := (polyAt a.mem (a.gpr .x0))[i]!.isLt
    have := (polyAt a.mem (a.gpr .x1))[i]!.isLt
    omega_using []

theorem add_verified : Verified target (VG.Impl.MlDsa.AArch64.Optimized.AddSub.code false)
    (Proof.MlDsa.addContract abi) :=
  Verified.of_correct add_correct
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0,.x1]) acc_agree (by taint_decide))
    (by mldsa_implies [Proof.MlDsa.addContract,Proof.MlDsa.accSig,accK,abi,argRegs] [accSat] using accSat)

theorem sub_verified : Verified target (VG.Impl.MlDsa.AArch64.Optimized.AddSub.code true)
    (Proof.MlDsa.subContract abi) :=
  Verified.of_correct sub_correct
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0,.x1]) acc_agree (by taint_decide))
    (by mldsa_implies [Proof.MlDsa.subContract,Proof.MlDsa.accSig,accK,abi,argRegs] [accSat] using accSat)
end VG.Proof.MlDsa.AArch64.Optimized.AddSub
