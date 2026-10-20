module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.SqueezeBlock
import VerifiedGarbage.Proof.Framework.Block

/-! # One matrix-squeeze iteration and its public counter -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon

def squeezeRegs : List Reg := blockRegs++[.x20,.x21,.x22]
def squeezeBody : Prog isa :=
 .seq (Impl.Sha3.AArch64.Neon.X2.call true .x19 .x19 1536)
  (.block (Impl.Sha3.AArch64.Neon.X2.squeeze 21 .x19 .x20 .x21 ++
   [.addImm .x .x20 .x20 168,.addImm .x .x21 .x21 168,.subImm .x .x22 .x22 1]))

theorem squeezeStep_ok {s : State} {p a b : Addr} {A B : Spec.Sha3.State}
    (hp : s.gpr .x19=p) (ha : s.gpr .x20=a) (hb : s.gpr .x21=b)
    (pair : PairAt s.mem p A B)
    (hin : ∀i<25,InRegions (s.rd++s.wr) (wordAddr p i) 16)
    (hwa : ∀i<21,InRegions s.wr (outAddr a i) 8)
    (hwb : ∀i<21,InRegions s.wr (outAddr b i) 8)
    (hd : (rateR21 a).Disjoint (rateR21 b))
    (hpa : (pairR p).Disjoint (rateR21 a)) (hpb : (pairR p).Disjoint (rateR21 b))
    (hpw : (pairR p).Disjoint (X2.callR (p+1536)))
    (hcov : Covers [pairR p,X2.callR (p+1536)] s.wr) :
    WP isa squeezeBody s fun t =>
      Keep squeezeRegs s t ∧ PairAt t.mem p (Spec.Sha3.keccakF A) (Spec.Sha3.keccakF B) ∧
      Rate21 t.mem a (Spec.Sha3.keccakF A) ∧ Rate21 t.mem b (Spec.Sha3.keccakF B) ∧
      Frame [pairR p,rateR21 a,rateR21 b,X2.callR (p+1536)] s.mem t.mem ∧
      t.gpr .x20=a+168 ∧ t.gpr .x21=b+168 ∧ t.gpr .x22=s.gpr .x22-1 := by
  have hc := squeezeBlock_ok hp ha hb (by rw [hp]; rfl)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) pair hin hwa hwb hd hpa hpb hpw hcov
  apply WP.seq
  refine WP.mono (WP.seq_iff.mp hc) fun u hu => ?_
  rw [WP.block_append_iff]
  refine WP.mono hu fun v ⟨kv,pv,av,bv,fv,vv⟩ => ?_
  refine wp_addImm (by decide) fun v1 h1 e1 => wp_addImm (by decide) fun v2 h2 e2 =>
    wp_subImm (by decide) fun t h3 e3 => wp_nil ?_
  have hv : Keep blockRegs s v := ⟨kv.gpr,kv.rd,kv.wr,kv.sp,vv⟩
  have ot : Only [.x20,.x21,.x22] v t := ((h1.trans h2).trans h3).mono (by simp)
  have hm : t.mem=v.mem := ot.mem
  refine ⟨(hv.trans ot.keep).mono (by simp [squeezeRegs]),?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hm]; exact pv
  · rw [hm]; exact av
  · rw [hm]; exact bv
  · rw [hm]; exact fv
  · rw [h3.get .x20 (by decide),h2.get .x20 (by decide),e1,kv.gpr .x20 (by decide),ha]; rfl
  · rw [h3.get .x21 (by decide),e2,h1.get .x21 (by decide),kv.gpr .x21 (by decide),hb]; rfl
  · rw [e3,h2.get .x22 (by decide),h1.get .x22 (by decide),kv.gpr .x22 (by decide)]; rfl

end VG.Proof.MlKem.AArch64.Paired
