import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Call
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.BoundedFour
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Keep
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic

/-! ## From `BoundedFourSqueeze.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon

def rateR (p : Addr) : Region := ⟨p,136⟩
def Rate136 (m : Mem) (p : Addr) (A : Spec.Sha3.State) : Prop :=
 ∀i<17,m.readW (outAddr p i) 64=A[i]!
theorem rate_contains (p : Addr) {i : Nat} (hi : i<17) :
 (rateR p).Contains (outAddr p i) 8 := Offset.contains_base p (by omega) (by omega)

theorem Rate136.byte {m : Mem} {p : Addr} {A : Spec.Sha3.State} (h : Rate136 m p A)
    {j : Nat} (hj : j < 136) : m (p+BitVec.ofNat 64 j) = Proof.Sha3.byteOf A j := by
  have hw := h (j/8) (by omega)
  have he := congrArg (fun v : BitVec 64 => v.extractLsb' (8*(j%8)) 8) hw
  change (m.read (outAddr p (j/8)) 8).extractLsb' (8*(j%8)) 8 = _ at he
  rw [Mem.extractLsb'_read m _ (by omega)] at he
  rw [outAddr,BitVec.add_assoc,← BitVec.ofNat_add,
    show 8*(j/8)+j%8 = j by omega] at he
  exact he
end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourPair.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon

/-- The registers a pair's block changes. -/
def blockRegs : List Reg := [.x0,.x1,.x16,.x17,.x6,.x7]

theorem pair_ok (sha3 : Bool) {s : State} {p a b w : Addr} {rp ra rb : Reg} {A B : Spec.Sha3.State}
    (hp : s.gpr rp = p) (ha : s.gpr ra = a) (hb : s.gpr rb = b)
    (hw : s.gpr .x19 + BitVec.ofNat 64 Impl.MlDsa.AArch64.Optimized.BoundedFour.oX2 = w)
    (hp1 : rp ≠ .x1) (hp6 : rp ≠ .x6) (hp7 : rp ≠ .x7)
    (ha6 : ra ≠ .x6) (ha7 : ra ≠ .x7) (hb6 : rb ≠ .x6) (hb7 : rb ≠ .x7)
    (hpc : rp ∉ X2.clobbered) (hac : ra ∉ X2.clobbered) (hbc : rb ∉ X2.clobbered)
    (hpair : PairAt s.mem p A B)
    (hin : ∀ i < 25, InRegions (s.rd++s.wr) (wordAddr p i) 16)
    (hwa : ∀ i < 17, InRegions s.wr (outAddr a i) 8)
    (hwb : ∀ i < 17, InRegions s.wr (outAddr b i) 8)
    (hd : (rateR a).Disjoint (rateR b))
    (hpa : (pairR p).Disjoint (rateR a)) (hpb : (pairR p).Disjoint (rateR b))
    (hpw : (pairR p).Disjoint (X2.callR w)) (hcov : Covers [pairR p, X2.callR w] s.wr) :
    WP isa (Impl.MlDsa.AArch64.Optimized.BoundedFour.pair sha3 rp ra rb) s fun t =>
      RegKeep blockRegs s t ∧ PairAt t.mem p (Spec.Sha3.keccakF A) (Spec.Sha3.keccakF B) ∧
      Rate136 t.mem a (Spec.Sha3.keccakF A) ∧ Rate136 t.mem b (Spec.Sha3.keccakF B) ∧
      Frame [pairR p,rateR a,rateR b,X2.callR w] s.mem t.mem := by
  unfold Impl.MlDsa.AArch64.Optimized.BoundedFour.pair
  refine WP.seq (WP.mono (X2.call_ok sha3 (by decide) hp1 hp hw hpw hpair hcov) fun t ⟨hk,hf,hpt⟩ => ?_)
  have hkt : RegKeep X2.clobbered s t := ⟨hk.gpr,hk.rd,hk.wr,hk.sp⟩
  refine WP.mono (X2.squeeze_ok (n := 17) (by decide) ((hkt.gpr _ hpc).trans hp)
    ((hkt.gpr _ hac).trans ha) ((hkt.gpr _ hbc).trans hb) hp6 hp7 ha6 ha7 hb6 hb7 hpt hd hpa hpb
    (fun i hi => by rw [hk.rd,hk.wr]; exact hin i hi)
    (fun i hi => by rw [hk.wr]; exact hwa i hi) (fun i hi => by rw [hk.wr]; exact hwb i hi))
    fun u ⟨hu,hfu,hau,hbu⟩ => ?_
  have hku : RegKeep [.x6,.x7] t u := ⟨fun r hr => by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr; exact hu.gpr r hr.1 hr.2,
    hu.rd,hu.wr,hu.sp⟩
  have hfu' : Frame [rateR a,rateR b] t.mem u.mem := hfu
  refine ⟨(hkt.trans hku).mono (by decide),fun i hi => ?_,hau,hbu,?_⟩
  · rw [hfu'.read (pair_contains p hi) (by
      intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl; exact hpa; exact hpb) (by decide)]
    exact hpt i hi
  · exact (hf.mono fun r hr => by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; rcases hr with h | h <;> simp [h]).trans
      (hfu'.mono fun r hr => by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; rcases hr with h | h <;> simp [h])
end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourStream.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon

theorem Rate136.keep {m m' : Mem} {p : Addr} {A : Spec.Sha3.State} {rs : List Region}
    (h : Rate136 m p A) (hf : Frame rs m m') (hd : ∀r∈rs,(rateR p).Disjoint r) :
    Rate136 m' p A := by
  intro i hi
  rw [hf.readW (rate_contains p hi) hd (by decide)]
  exact h i hi

theorem pairAt_keep {m m' : Mem} {p : Addr} {A B : Spec.Sha3.State} {rs : List Region}
    (h : PairAt m p A B) (hf : Frame rs m m') (hd : ∀r∈rs,(pairR p).Disjoint r) :
    PairAt m' p A B := by
  intro i hi
  rw [hf.read (pair_contains p hi) hd (by decide)]
  exact h i hi

def Stream136 (m : Mem) (p : Addr) (j : Nat) (A : Spec.Sha3.State) : Prop :=
 ∀i<j,Rate136 m (p+BitVec.ofNat 64 (136*i)) (Resident.permuted A (i+1))

theorem stream136_zero (m : Mem) (p : Addr) (A : Spec.Sha3.State) : Stream136 m p 0 A := by
  intro i hi; omega

theorem Stream136.keep {m m' : Mem} {p : Addr} {j : Nat} {A : Spec.Sha3.State} {rs : List Region}
    (h : Stream136 m p j A) (hf : Frame rs m m')
    (hd : ∀i<j,∀r∈rs,(rateR (p+BitVec.ofNat 64 (136*i))).Disjoint r) :
    Stream136 m' p j A := fun i hi=>(h i hi).keep hf (hd i hi)

theorem Stream136.succ {m : Mem} {p : Addr} {j : Nat} {A : Spec.Sha3.State}
    (h : Stream136 m p j A)
    (hl : Rate136 m (p+BitVec.ofNat 64 (136*j)) (Spec.Sha3.keccakF (Resident.permuted A j))) :
    Stream136 m p (j+1) A := by
  intro i hi
  by_cases he : i=j
  · subst i; exact hl
  · exact h i (by omega)

theorem stream136_byte {m : Mem} {p : Addr} {j : Nat} {A : Spec.Sha3.State}
    (h : Stream136 m p j A) {i : Nat} (hi : i<136*j) :
    m (p+BitVec.ofNat 64 i)=Proof.Sha3.byteOf (Resident.permuted A (i/136+1)) (i%136) := by
  have he:=(h (i/136) (by omega)).byte (j := i%136) (by omega)
  rw [BitVec.add_assoc,←BitVec.ofNat_add,show 136*(i/136)+i%136=i by omega] at he
  exact he

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourSqueezeArgs.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64

def squeezeArgs (off : Nat) : List Instr :=
 [Impl.MlKem.AArch64.mov .x22 .x19,.addImm .x .x23 .x19 400,
 .addImm .x .x24 .x19 (840+off),.addImm .x .x25 .x19 (1384+off),
 .addImm .x .x26 .x19 (1928+off),.addImm .x .x27 .x19 (2472+off),.movz .x .x28 2 0]

theorem squeezeArgs_ok (s : State) {off : Nat} (ho : off≤272) :
    WP isa (.block (squeezeArgs off)) s fun t=>
      ((t.gpr .x22=s.gpr .x19 ∧ t.gpr .x23=s.gpr .x19+400 ∧
        t.gpr .x24=s.gpr .x19+BitVec.ofNat 64 (840+off) ∧
        t.gpr .x25=s.gpr .x19+BitVec.ofNat 64 (1384+off) ∧
        t.gpr .x26=s.gpr .x19+BitVec.ofNat 64 (1928+off) ∧
        t.gpr .x27=s.gpr .x19+BitVec.ofNat 64 (2472+off) ∧ t.gpr .x28=2 ∧t.mem=s.mem) ∧
        Keep [.x22,.x23,.x24,.x25,.x26,.x27,.x28] s t) ∧t.v=s.v := by
  apply WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  unfold squeezeArgs Impl.MlKem.AArch64.mov
  have h0 : 840+off<4096 := by omega
  have h1 : 1384+off<4096 := by omega
  have h2 : 1928+off<4096 := by omega
  have h3 : 2472+off<4096 := by omega
  arun [h0,h1,h2,h3]
  rfl

def squeezeAdvance : List Instr :=
 [.addImm .x .x24 .x24 136,.addImm .x .x25 .x25 136,
 .addImm .x .x26 .x26 136,.addImm .x .x27 .x27 136,.subImm .x .x28 .x28 1]

theorem squeezeAdvance_ok (s : State) :
    WP isa (.block squeezeAdvance) s fun t=>
      ((t.gpr .x24=s.gpr .x24+136 ∧ t.gpr .x25=s.gpr .x25+136 ∧
        t.gpr .x26=s.gpr .x26+136 ∧ t.gpr .x27=s.gpr .x27+136 ∧
        t.gpr .x28=s.gpr .x28-1 ∧t.mem=s.mem) ∧
        Keep [.x24,.x25,.x26,.x27,.x28] s t) ∧t.v=s.v := by
  apply WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  unfold squeezeAdvance
  arun
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end
