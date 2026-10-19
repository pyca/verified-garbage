module

public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Call
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Keep

/-! # Paired noise PRF permutation and serialization -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon

def rateR21 (p : Addr) : Region := ⟨p,168⟩
def Rate21 (m : Mem) (p : Addr) (A : Spec.Sha3.State) : Prop :=
 ∀i<21,m.readW (outAddr p i) 64=A[i]!

/-- The registers a pair's block changes. -/
def blockRegs : List Reg := [.x0,.x1,.x16,.x17,.x6,.x7]

theorem squeezeBlock_ok {s : State} {p a b w : Addr} {rp ra rb : Reg} {A B : Spec.Sha3.State}
    (hp : s.gpr rp = p) (ha : s.gpr ra = a) (hb : s.gpr rb = b)
    (hw : s.gpr .x19 + BitVec.ofNat 64 1536 = w)
    (hp1 : rp ≠ .x1) (hp6 : rp ≠ .x6) (hp7 : rp ≠ .x7)
    (ha6 : ra ≠ .x6) (ha7 : ra ≠ .x7) (hb6 : rb ≠ .x6) (hb7 : rb ≠ .x7)
    (hpc : rp ∉ X2.clobbered) (hac : ra ∉ X2.clobbered) (hbc : rb ∉ X2.clobbered)
    (hpair : PairAt s.mem p A B)
    (hin : ∀ i < 25, InRegions (s.rd++s.wr) (wordAddr p i) 16)
    (hwa : ∀ i < 21, InRegions s.wr (outAddr a i) 8)
    (hwb : ∀ i < 21, InRegions s.wr (outAddr b i) 8)
    (hd : (rateR21 a).Disjoint (rateR21 b))
    (hpa : (pairR p).Disjoint (rateR21 a)) (hpb : (pairR p).Disjoint (rateR21 b))
    (hpw : (pairR p).Disjoint (X2.callR w)) (hcov : Covers [pairR p, X2.callR w] s.wr) :
    WP isa ((.seq (Impl.Sha3.AArch64.Neon.X2.call true rp .x19 1536) (.block (Impl.Sha3.AArch64.Neon.X2.squeeze 21 rp ra rb)))) s fun t =>
      RegKeep blockRegs s t ∧ PairAt t.mem p (Spec.Sha3.keccakF A) (Spec.Sha3.keccakF B) ∧
      Rate21 t.mem a (Spec.Sha3.keccakF A) ∧ Rate21 t.mem b (Spec.Sha3.keccakF B) ∧
      Frame [pairR p,rateR21 a,rateR21 b,X2.callR w] s.mem t.mem ∧
      (∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) := by
  refine WP.seq (WP.mono (X2.call_ok true (by decide) hp1 hp hw hpw hpair hcov) fun t ⟨hk,hf,hpt⟩ => ?_)
  have hkt : RegKeep X2.clobbered s t := ⟨hk.gpr,hk.rd,hk.wr,hk.sp⟩
  refine WP.mono (X2.squeeze_ok (n := 21) (by decide) ((hkt.gpr _ hpc).trans hp)
    ((hkt.gpr _ hac).trans ha) ((hkt.gpr _ hbc).trans hb) hp6 hp7 ha6 ha7 hb6 hb7 hpt hd hpa hpb
    (fun i hi => by rw [hk.rd,hk.wr]; exact hin i hi)
    (fun i hi => by rw [hk.wr]; exact hwa i hi) (fun i hi => by rw [hk.wr]; exact hwb i hi))
    fun u ⟨hu,hfu,hau,hbu⟩ => ?_
  have hku : RegKeep [.x6,.x7] t u := ⟨fun r hr => by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr; exact hu.gpr r hr.1 hr.2,
    hu.rd,hu.wr,hu.sp⟩
  have hfu' : Frame [rateR21 a,rateR21 b] t.mem u.mem := hfu
  refine ⟨(hkt.trans hku).mono (by decide),fun i hi => ?_,hau,hbu,?_,?_⟩
  · rw [hfu'.read (pair_contains p hi) (by
      intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl; exact hpa; exact hpb) (by decide)]
    exact hpt i hi
  · exact (hf.mono fun r hr => by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; rcases hr with h | h <;> simp [h]).trans
      (hfu'.mono fun r hr => by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; rcases hr with h | h <;> simp [h])

  · intro r hr; rw [hu.vec]; exact hk.vcs r hr

end VG.Proof.MlKem.AArch64.Paired
