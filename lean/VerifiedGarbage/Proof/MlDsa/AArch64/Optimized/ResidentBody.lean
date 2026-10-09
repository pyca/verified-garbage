import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMemory

namespace VG.Proof.MlDsa.AArch64.Optimized.Resident
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon (Pairs)

/-- The inline body including public address and counter advancement. -/
theorem bodyWith_ok (core : Core) {s : State} {a b : Addr} {ra rb : Reg} {n : Nat}
    {A B : Spec.Sha3.State} (hn : n ≤ 10) (hp : Pairs s A B)
    (ha : s.gpr ra = a) (hb : s.gpr rb = b)
    (ha6 : ra ≠ .x6) (ha7 : ra ≠ .x7) (ha16 : ra ≠ .x16) (ha28 : ra ≠ .x28)
    (hb6 : rb ≠ .x6) (hb7 : rb ≠ .x7) (hb16 : rb ≠ .x16) (hb28 : rb ≠ .x28)
    (hab : ra ≠ rb)
    (hd : (Region.mk a (16*n+8)).Disjoint ⟨b,16*n+8⟩)
    (hwa : ∀ i < n, InRegions s.wr (a+BitVec.ofNat 64 (16*i)) 16)
    (hwb : ∀ i < n, InRegions s.wr (b+BitVec.ofNat 64 (16*i)) 16)
    (hwal : InRegions s.wr (a+BitVec.ofNat 64 (16*n)) 8)
    (hwbl : InRegions s.wr (b+BitVec.ofNat 64 (16*n)) 8) :
    WP isa (.seq core.code
      (.block (Impl.MlDsa.AArch64.Optimized.Resident.squeeze (2*n+1) ra rb ++
        ([.addImm .x ra ra (8*(2*n+1)),.addImm .x rb rb (8*(2*n+1)),
          .subImm .x .x28 .x28 1] : List Instr)))) s fun t =>
      Pairs t (Spec.Sha3.keccakF A) (Spec.Sha3.keccakF B) ∧
      RateBlock t.mem a n (Spec.Sha3.keccakF A) ∧
      RateBlock t.mem b n (Spec.Sha3.keccakF B) ∧
      Frame [⟨a,16*n+8⟩,⟨b,16*n+8⟩] s.mem t.mem ∧
      t.gpr ra = a+BitVec.ofNat 64 (16*n+8) ∧
      t.gpr rb = b+BitVec.ofNat 64 (16*n+8) ∧
      t.gpr .x28 = s.gpr .x28-1 ∧
      (∀ r, r ≠ ra → r ≠ rb → r ≠ .x28 → r ≠ .x6 → r ≠ .x7 → r ≠ .x16 →
        t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  rw [show 8*(2*n+1)=16*n+8 by omega]
  apply WP.seq
  refine WP.mono (core.correct hp) ?_
  intro u hu
  rw [WP.block_append_iff]
  refine WP.mono (squeeze_ok hn hu.2
    ((hu.1.gpr ra ha16).trans ha) ((hu.1.gpr rb hb16).trans hb)
    ha6 ha7 hb6 hb7 hd
    (by simpa only [hu.1.wr] using hwa) (by simpa only [hu.1.wr] using hwb)
    (by simpa only [hu.1.wr] using hwal) (by simpa only [hu.1.wr] using hwbl)) ?_
  intro v hv
  refine WP.mono (advance_ok (rate := 16*n+8) (by omega) hab ha28 hb28) ?_
  intro t ht
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i hi
    rw [ht.2.2.2.2.1]
    exact hv.2.1 i hi
  · simpa only [ht.2.2.2.2.2.1] using hv.2.2.1
  · simpa only [ht.2.2.2.2.2.1] using hv.2.2.2.1
  · simpa only [ht.2.2.2.2.2.1,hu.1.mem] using hv.2.2.2.2
  · rw [ht.1,hv.1.gpr ra ha6 ha7,hu.1.gpr ra ha16,ha]
  · rw [ht.2.1,hv.1.gpr rb hb6 hb7,hu.1.gpr rb hb16,hb]
  · rw [ht.2.2.1,hv.1.gpr .x28 (by decide) (by decide),hu.1.gpr .x28 (by decide)]
  · intro r hra hrb hr28 hr6 hr7 hr16
    exact (ht.2.2.2.1 r hra hrb hr28).trans ((hv.1.gpr r hr6 hr7).trans (hu.1.gpr r hr16))
  · exact ht.2.2.2.2.2.2.1.trans (hv.1.rd.trans hu.1.rd)
  · exact ht.2.2.2.2.2.2.2.1.trans (hv.1.wr.trans hu.1.wr)
  · exact ht.2.2.2.2.2.2.2.2.trans (hv.1.sp.trans hu.1.sp)

theorem body_ok {s : State} {a b : Addr} {ra rb : Reg} {n : Nat}
    {A B : Spec.Sha3.State} (hn : n ≤ 10) (hp : Pairs s A B)
    (ha : s.gpr ra = a) (hb : s.gpr rb = b)
    (ha6 : ra ≠ .x6) (ha7 : ra ≠ .x7) (ha16 : ra ≠ .x16) (ha28 : ra ≠ .x28)
    (hb6 : rb ≠ .x6) (hb7 : rb ≠ .x7) (hb16 : rb ≠ .x16) (hb28 : rb ≠ .x28)
    (hab : ra ≠ rb)
    (hd : (Region.mk a (16*n+8)).Disjoint ⟨b,16*n+8⟩)
    (hwa : ∀ i < n, InRegions s.wr (a+BitVec.ofNat 64 (16*i)) 16)
    (hwb : ∀ i < n, InRegions s.wr (b+BitVec.ofNat 64 (16*i)) 16)
    (hwal : InRegions s.wr (a+BitVec.ofNat 64 (16*n)) 8)
    (hwbl : InRegions s.wr (b+BitVec.ofNat 64 (16*n)) 8) :
    WP isa (.seq Impl.MlDsa.AArch64.Optimized.Resident.permute
      (.block (Impl.MlDsa.AArch64.Optimized.Resident.squeeze (2*n+1) ra rb ++
        ([.addImm .x ra ra (8*(2*n+1)),.addImm .x rb rb (8*(2*n+1)),
          .subImm .x .x28 .x28 1] : List Instr)))) s fun t =>
      Pairs t (Spec.Sha3.keccakF A) (Spec.Sha3.keccakF B) ∧
      RateBlock t.mem a n (Spec.Sha3.keccakF A) ∧
      RateBlock t.mem b n (Spec.Sha3.keccakF B) ∧
      Frame [⟨a,16*n+8⟩,⟨b,16*n+8⟩] s.mem t.mem ∧
      t.gpr ra = a+BitVec.ofNat 64 (16*n+8) ∧
      t.gpr rb = b+BitVec.ofNat 64 (16*n+8) ∧
      t.gpr .x28 = s.gpr .x28-1 ∧
      (∀ r, r ≠ ra → r ≠ rb → r ≠ .x28 → r ≠ .x6 → r ≠ .x7 → r ≠ .x16 →
        t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp :=
  bodyWith_ok originalCore hn hp ha hb ha6 ha7 ha16 ha28 hb6 hb7 hb16 hb28 hab hd hwa hwb hwal hwbl

end VG.Proof.MlDsa.AArch64.Optimized.Resident
