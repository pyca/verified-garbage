import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MontDotLoad
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Vec
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Pro
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFrame
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic

/-! ## From `MontDotTerms.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.MontDot
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)

theorem dotTerms_ok (n : Nat) {s : State} {off : Nat}
    (ho : ∀k<n,(1024*k+off)%16=0 ∧ 1024*k+off<4096*16)
    (hr : ∀k<n,InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 (1024*k+off)) 16 ∧
      InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 (1024*k+off)) 16)
    {rest : List Instr} {Q : State → Prop}
    (next : ∀t,VChg [.v0,.v1,.v2,.v3] s t →
      (n≠0 → t.v .v2=ofVDwords (dotAccum s off n 0) (dotAccum s off n 1)) →
      (n≠0 → t.v .v3=ofVDwords (dotAccum s off n 2) (dotAccum s off n 3)) →
      WP isa (.block rest) t Q) :
    WP isa (.block ((List.range n).flatMap (dotTerm off)++rest)) s Q := by
  induction n generalizing s rest with
  | zero => exact next s (VChg.refl _ _) (by simp) (by simp)
  | succ n ih =>
    rw [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]
    refine ih (fun k hk => ho k (by omega)) (fun k hk => hr k (by omega)) fun a ha e18 e19 => ?_
    have hr' : InRegions (a.rd++a.wr) (a.gpr .x1+BitVec.ofNat 64 (1024*n+off)) 16 ∧
        InRegions (a.rd++a.wr) (a.gpr .x2+BitVec.ofNat 64 (1024*n+off)) 16 := by
      rw [ha.rd,ha.wr,ha.gpr]; exact hr n (by omega)
    refine dotTerm_ok (ho n (by omega)) hr'.1 hr'.2 ?_ ?_ fun t ht a18 a19 => ?_
    · rw [dotAccum_chg ha]; exact e18
    · rw [dotAccum_chg ha]; exact e19
    · refine next t ((ha.trans ht).mono (by simp)) (fun _ => ?_) (fun _ => ?_)
      · simpa only [dotAccum_chg ha] using a18
      · simpa only [dotAccum_chg ha] using a19

end VG.Proof.MlDsa.AArch64.Optimized.MontDot

end

/-! ## From `MontDotReduce.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.MontDot
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64 (VChg Lanes)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith.Neon

/-- The selected five-instruction REDC and two-instruction correction produce
canonical Montgomery residues, including zero and values just above q. -/
theorem canonicalReduce_ok (p : Nat→BitVec 64) {s : State}
    (a₁ : s.v .v2=ofVDwords (p 0) (p 1)) (a₂ : s.v .v3=ofVDwords (p 2) (p 3))
    (hq : s.v .v16=ofVWords (BitVec.ofNat 32 q) (BitVec.ofNat 32 q)
      (BitVec.ofNat 32 q) (BitVec.ofNat 32 q))
    (hqi : s.v .v17=ofVWords (BitVec.ofNat 32 montQInv) (BitVec.ofNat 32 montQInv)
      (BitVec.ofNat 32 montQInv) (BitVec.ofNat 32 montQInv))
    (hp : ∀e<4,(p e).toNat<q*2^32)
    {rest : List Instr} {Q : State→Prop}
    (next : ∀t,VChg [.v0,.v2,.v3,.v4] s t →
      Lanes (t.v .v0) (fun e=>mont (p e).toNat%q) → WP isa (.block rest) t Q) :
    WP isa (.block (reduce .v0++Impl.MlDsa.AArch64.Arith.Neon.csub .v0 .v4++rest)) s Q := by
  rw [List.append_assoc]
  refine reduce_ok p a₁ a₂ hq hqi fun a ha hv=>?_
  have hqa : Lanes (a.v .v16) (fun _=>q) := by
    rw [ha.get .v16 (by decide),hq]
    intro e he
    rcases (show e=0∨e=1∨e=2∨e=3 by omega) with rfl|rfl|rfl|rfl <;> rfl
  have hl : Lanes (a.v .v0) (fun e=>mont (p e).toNat) := by
    rw [hv]
    intro e he
    have hr := redc_nat (p e) (hp e he)
    rcases (show e=0∨e=1∨e=2∨e=3 by omega) with rfl|rfl|rfl|rfl <;>
      simpa only [vword_ofVWords_0,vword_ofVWords_1,vword_ofVWords_2,vword_ofVWords_3] using hr
  refine csub_ok (by decide) hqa hl (fun e he=>mont_lt (hp e he)) fun t ht hval=>?_
  exact next t ((ha.trans ht).mono (by simp)) hval

end VG.Proof.MlDsa.AArch64.Optimized.MontDot

end

/-! ## From `MontDotBlock.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.MontDot
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64 (VChg Lanes)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith.Neon

 theorem product_eq (k : Nat) : Impl.MlDsa.AArch64.Optimized.MontDot.product k=dotTerm 0 k := by
  simp only [Impl.MlDsa.AArch64.Optimized.MontDot.product,dotTerm,Nat.add_zero,dotAcc]
  by_cases hk : k=0 <;> simp only [hk,decide_true,decide_false,ite_true,ite_false,Bool.false_eq_true]

theorem block_ok {n : Nat} (hn : 0<n) (hn7 : n≤7) {s : State}
    (hr : ∀k<n,InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 (1024*k)) 16 ∧
      InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 (1024*k)) 16)
    (ha : ∀k<n,∀e<4,(dotInput s .x1 0 k e).toNat<3*q)
    (hb : ∀k<n,∀e<4,(dotInput s .x2 0 k e).toNat<3*q)
    (hq : s.v .v16=ofVWords (BitVec.ofNat 32 q) (BitVec.ofNat 32 q)
      (BitVec.ofNat 32 q) (BitVec.ofNat 32 q))
    (hqi : s.v .v17=ofVWords (BitVec.ofNat 32 montQInv) (BitVec.ofNat 32 montQInv)
      (BitVec.ofNat 32 montQInv) (BitVec.ofNat 32 montQInv))
    {rest : List Instr} {Q : State→Prop}
    (next : ∀t,VChg [.v0,.v1,.v2,.v3,.v4] s t →
      Lanes (t.v .v0) (fun e=>mont (dotAccum s 0 n e).toNat%q) → WP isa (.block rest) t Q) :
    WP isa (.block ((List.range n).flatMap Impl.MlDsa.AArch64.Optimized.MontDot.product++
      Impl.MlDsa.AArch64.Optimized.MontDot.reduce++Impl.MlDsa.AArch64.Arith.Neon.csub .v0 .v4++rest)) s Q := by
  rw [show Impl.MlDsa.AArch64.Optimized.MontDot.product=dotTerm 0 from funext product_eq]
  simp only [List.append_assoc]
  refine dotTerms_ok n (off:=0) ?_ ?_ fun a hA e2 e3=>?_
  · intro k hk
    constructor
    · omega
    · omega
  · intro k hk
    simpa only [Nat.add_zero] using hr k hk
  · change WP isa (.block (reduce .v0++Impl.MlDsa.AArch64.Arith.Neon.csub .v0 .v4++rest)) a Q
    refine canonicalReduce_ok (dotAccum s 0 n) (e2 (by omega)) (e3 (by omega)) ?_ ?_ ?_ fun t ht hv=>?_
    · rw [hA.get .v16 (by decide)];exact hq
    · rw [hA.get .v17 (by decide)];exact hqi
    · intro e he
      have hw := dotWord_nat (fun k=>dotInput s .x1 0 k e) (fun k=>dotInput s .x2 0 k e) hn7
        (fun k hk=>ha k hk e he) (fun k hk=>hb k hk e he)
      unfold dotAccum
      rw [hw]
      exact dotNat_lt_qR _ _ hn7 (fun k hk=>ha k hk e he) (fun k hk=>hb k hk e he)
    · exact next t ((hA.trans ht).mono (by simp)) hv

end VG.Proof.MlDsa.AArch64.Optimized.MontDot

end

/-! ## From `MontDotMem.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.MontDot
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64 (VChg Lanes wp_strq wp_nil Keep)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlDsa.AArch64.Optimized.Response (StepKeep)

theorem body_ok {n : Nat} (hn : 0<n) (hn7 : n≤7) {s : State} (hc : VConsts s)
    (hr : ∀k<n,InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 (1024*k)) 16 ∧
      InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 (1024*k)) 16)
    (ha : ∀k<n,∀e<4,(dotInput s .x1 0 k e).toNat<3*q)
    (hb : ∀k<n,∀e<4,(dotInput s .x2 0 k e).toNat<3*q)
    (hw : InRegions s.wr (s.gpr .x0) 16) :
    WP isa (.block (Impl.MlDsa.AArch64.Optimized.MontDot.body n)) s fun t=>
      ∃v,t.mem=s.mem.write (s.gpr .x0) 16 v ∧
      Lanes v (fun e=>mont (dotAccum s 0 n e).toNat%q) ∧ VConsts t ∧
      t.gpr .x0=s.gpr .x0+16 ∧ t.gpr .x1=s.gpr .x1+16 ∧ t.gpr .x2=s.gpr .x2+16 ∧
      t.gpr .x12=s.gpr .x12-1 ∧ Keep [.x0,.x1,.x2,.x12] s t := by
  unfold Impl.MlDsa.AArch64.Optimized.MontDot.body
  refine block_ok hn hn7 hr ha hb hc.q hc.qi fun a hA hv=>?_
  refine wp_strq (by decide) rfl (by simpa only [hA.wr,hA.gpr,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using hw) fun b hB=>?_
  have hk : StepKeep [.v0,.v1,.v2,.v3,.v4] s b :=
    (StepKeep.ofChg hA (by decide)).trans (StepKeep.ofMem hB)
  have hm : b.mem=s.mem.write (s.gpr .x0) 16 (a.v .v0) := by
    simp only [hB.mem,hA.mem,hA.gpr,BitVec.add_zero]
  have cb : VConsts b := ⟨by rw [hk.vec .v16 (by decide)];exact hc.q,
    by rw [hk.vec .v17 (by decide)];exact hc.qi⟩
  have scalar : WP isa (.block [.addImm .x .x0 .x0 16,.addImm .x .x1 .x1 16,
      .addImm .x .x2 .x2 16,.subImm .x .x12 .x12 1]) b fun u=>
      u.mem=b.mem ∧ u.v=b.v ∧ u.gpr .x0=b.gpr .x0+16 ∧ u.gpr .x1=b.gpr .x1+16 ∧
      u.gpr .x2=b.gpr .x2+16 ∧ u.gpr .x12=b.gpr .x12-1 := by
    arun [State.write,BitVec.ofNat_eq_ofNat]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.WP.keep [.x0,.x1,.x2,.x12] scalar (by decide))
    fun u ⟨⟨hum,huv,h0,h1,h2,h12⟩,ku⟩=>?_
  refine ⟨a.v .v0,hum.trans hm,hv,?_,?_,?_,?_,?_,(hk.keep.trans ku).mono⟩
  · exact ⟨by rw [huv];exact cb.q,by rw [huv];exact cb.qi⟩
  · simpa only [hk.keep.get .x0] using h0
  · simpa only [hk.keep.get .x1] using h1
  · simpa only [hk.keep.get .x2] using h2
  · simpa only [hk.keep.get .x12] using h12

end VG.Proof.MlDsa.AArch64.Optimized.MontDot

end
