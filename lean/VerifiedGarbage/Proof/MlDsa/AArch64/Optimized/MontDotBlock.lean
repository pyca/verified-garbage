import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MontDotReduce

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
