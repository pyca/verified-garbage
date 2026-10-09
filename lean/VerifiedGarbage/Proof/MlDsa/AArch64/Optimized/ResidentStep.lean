import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentBlock

namespace VG.Proof.MlDsa.AArch64.Optimized.Resident
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon (Pairs)

/-- The resident permutation and serialization clobber only these scalar
registers; the two Keccak states themselves remain in vector registers. -/
structure StepKeep (s t : State) : Prop where
  gpr : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x16 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem StepKeep.refl (s : State) : StepKeep s s :=
  ⟨fun _ _ _ _ => rfl,rfl,rfl,rfl⟩

theorem StepKeep.trans {s t u : State} (h : StepKeep s t) (k : StepKeep t u) :
    StepKeep s u :=
  ⟨fun r h6 h7 h16 => (k.gpr r h6 h7 h16).trans (h.gpr r h6 h7 h16),
    k.rd.trans h.rd,k.wr.trans h.wr,k.sp.trans h.sp⟩

/-- One complete resident SHAKE block, for either supported rate. Both input
states are arbitrary and both serialized outputs are exact. -/
theorem block_ok {s : State} {a b : Addr} {ra rb : Reg} {n : Nat}
    {A B : Spec.Sha3.State} (hn : n ≤ 10) (hp : Pairs s A B)
    (ha : s.gpr ra = a) (hb : s.gpr rb = b)
    (ha6 : ra ≠ .x6) (ha7 : ra ≠ .x7) (ha16 : ra ≠ .x16)
    (hb6 : rb ≠ .x6) (hb7 : rb ≠ .x7) (hb16 : rb ≠ .x16)
    (hd : (Region.mk a (16*n+8)).Disjoint ⟨b,16*n+8⟩)
    (hwa : ∀ i < n, InRegions s.wr (a+BitVec.ofNat 64 (16*i)) 16)
    (hwb : ∀ i < n, InRegions s.wr (b+BitVec.ofNat 64 (16*i)) 16)
    (hwal : InRegions s.wr (a+BitVec.ofNat 64 (16*n)) 8)
    (hwbl : InRegions s.wr (b+BitVec.ofNat 64 (16*n)) 8) :
    WP isa (.seq Impl.MlDsa.AArch64.Optimized.Resident.permute
      (.block (Impl.MlDsa.AArch64.Optimized.Resident.squeeze (2*n+1) ra rb))) s fun t =>
      StepKeep s t ∧ Pairs t (Spec.Sha3.keccakF A) (Spec.Sha3.keccakF B) ∧
      RateBlock t.mem a n (Spec.Sha3.keccakF A) ∧
      RateBlock t.mem b n (Spec.Sha3.keccakF B) ∧
      Frame [⟨a,16*n+8⟩,⟨b,16*n+8⟩] s.mem t.mem := by
  apply WP.seq
  refine WP.mono (permute_ok hp) ?_
  intro u hu
  refine WP.mono (squeeze_ok hn hu.2
    ((hu.1.gpr ra ha16).trans ha) ((hu.1.gpr rb hb16).trans hb)
    ha6 ha7 hb6 hb7 hd
    (by simpa only [hu.1.wr] using hwa) (by simpa only [hu.1.wr] using hwb)
    (by simpa only [hu.1.wr] using hwal) (by simpa only [hu.1.wr] using hwbl)) ?_
  intro t ht
  refine ⟨⟨fun r h6 h7 h16 => (ht.1.gpr r h6 h7).trans (hu.1.gpr r h16),
    ht.1.rd.trans hu.1.rd,ht.1.wr.trans hu.1.wr,ht.1.sp.trans hu.1.sp⟩,
    ht.2.1,ht.2.2.1,ht.2.2.2.1,?_⟩
  simpa only [hu.1.mem] using ht.2.2.2.2
end VG.Proof.MlDsa.AArch64.Optimized.Resident
