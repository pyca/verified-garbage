import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentBody

namespace VG.Proof.MlDsa.AArch64.Optimized.Resident
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon (Pairs)

structure StreamState (s₀ : State) (a b : Addr) (n blocks : Nat) (ra rb : Reg)
    (A B : Spec.Sha3.State) (j : Nat) (s : State) : Prop where
  bound : j ≤ blocks
  pairs : Pairs s (permuted A j) (permuted B j)
  outA : StreamOutput s.mem a n j A
  outB : StreamOutput s.mem b n j B
  frame : Frame [⟨a,(16*n+8)*blocks⟩,⟨b,(16*n+8)*blocks⟩] s₀.mem s.mem
  ptrA : s.gpr ra = a+BitVec.ofNat 64 ((16*n+8)*j)
  ptrB : s.gpr rb = b+BitVec.ofNat 64 ((16*n+8)*j)
  count : s.gpr .x28 = BitVec.ofNat 64 (blocks-j)
  gpr : ∀ r, r ≠ ra → r ≠ rb → r ≠ .x28 → r ≠ .x6 → r ≠ .x7 → r ≠ .x16 → s.gpr r=s₀.gpr r
  rd : s.rd=s₀.rd
  wr : s.wr=s₀.wr
  sp : s.sp=s₀.sp

/-- One iteration extends both exact output streams and decreases the public
remaining-block count. -/
theorem streamStepWith_ok (core : Core) {s₀ s : State} {a b : Addr} {n blocks j : Nat} {ra rb : Reg}
    {A B : Spec.Sha3.State} (hn : n ≤ 10) (hblocks : blocks < 65536)
    (hj : j < blocks) (h : StreamState s₀ a b n blocks ra rb A B j s)
    (ha6 : ra ≠ .x6) (ha7 : ra ≠ .x7) (ha16 : ra ≠ .x16) (ha28 : ra ≠ .x28)
    (hb6 : rb ≠ .x6) (hb7 : rb ≠ .x7) (hb16 : rb ≠ .x16) (hb28 : rb ≠ .x28)
    (hab : ra ≠ rb)
    (hd : (Region.mk a ((16*n+8)*blocks)).Disjoint ⟨b,(16*n+8)*blocks⟩)
    (hwa : ∀ j < blocks, ∀ i < n,
      InRegions s₀.wr ((a+BitVec.ofNat 64 ((16*n+8)*j))+BitVec.ofNat 64 (16*i)) 16)
    (hwb : ∀ j < blocks, ∀ i < n,
      InRegions s₀.wr ((b+BitVec.ofNat 64 ((16*n+8)*j))+BitVec.ofNat 64 (16*i)) 16)
    (hwal : ∀ j < blocks,
      InRegions s₀.wr ((a+BitVec.ofNat 64 ((16*n+8)*j))+BitVec.ofNat 64 (16*n)) 8)
    (hwbl : ∀ j < blocks,
      InRegions s₀.wr ((b+BitVec.ofNat 64 ((16*n+8)*j))+BitVec.ofNat 64 (16*n)) 8) :
    WP isa (.seq core.code
      (.block (Impl.MlDsa.AArch64.Optimized.Resident.squeeze (2*n+1) ra rb ++
        ([.addImm .x ra ra (8*(2*n+1)),.addImm .x rb rb (8*(2*n+1)),
          .subImm .x .x28 .x28 1] : List Instr)))) s
      (StreamState s₀ a b n blocks ra rb A B (j+1)) := by
  have sub (p : Addr) :
      (Region.mk (p+BitVec.ofNat 64 ((16*n+8)*j)) (16*n+8)).Sub
        ⟨p,(16*n+8)*blocks⟩ := by
    apply Offset.sub_base
    simpa only [Nat.mul_succ] using Nat.mul_le_mul_left (16*n+8) hj
  refine WP.mono (bodyWith_ok core hn h.pairs h.ptrA h.ptrB ha6 ha7 ha16 ha28 hb6 hb7 hb16 hb28 hab
    ((hd.sub_left (sub a)).sub_right (sub b))
    (by simpa only [h.wr] using hwa j hj) (by simpa only [h.wr] using hwb j hj)
    (by simpa only [h.wr] using hwal j hj) (by simpa only [h.wr] using hwbl j hj)) ?_
  intro t ht
  have hout := StreamOutput.append hn hj (by omega) hd h.outA h.outB ht.2.1 ht.2.2.1 ht.2.2.2.1
  refine ⟨by omega,ht.1,hout.1,hout.2,?_,?_,?_,?_,?_,ht.2.2.2.2.2.2.2.2.1.trans h.rd,
    ht.2.2.2.2.2.2.2.2.2.1.trans h.wr,ht.2.2.2.2.2.2.2.2.2.2.trans h.sp⟩
  · apply h.frame.trans
    apply ht.2.2.2.1.sub
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_,by simp,sub a⟩
    · exact ⟨_,by simp,sub b⟩
  · simpa only [BitVec.add_assoc,BitVec.ofNat_add_ofNat,Nat.mul_add,Nat.mul_one] using ht.2.2.2.2.1
  · simpa only [BitVec.add_assoc,BitVec.ofNat_add_ofNat,Nat.mul_add,Nat.mul_one] using ht.2.2.2.2.2.1
  · rw [ht.2.2.2.2.2.2.1,h.count]
    have he : blocks-j = blocks-(j+1)+1 := by omega
    rw [he,BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ (1 : BitVec 64)
  · intro r hra hrb hr28 hr6 hr7 hr16
    exact (ht.2.2.2.2.2.2.2.1 r hra hrb hr28 hr6 hr7 hr16).trans
      (h.gpr r hra hrb hr28 hr6 hr7 hr16)

/-- The resident loop terminates after the public number of blocks and writes
both complete streams, without reloading or spilling either Keccak state. -/
theorem streamLoopWith_ok (core : Core) {s₀ s : State} {a b : Addr} {n blocks start : Nat} {ra rb : Reg}
    {A B : Spec.Sha3.State} (hn : n ≤ 10) (hblocks : blocks < 65536)
    (hstart : start < blocks) (h : StreamState s₀ a b n blocks ra rb A B start s)
    (ha6 : ra ≠ .x6) (ha7 : ra ≠ .x7) (ha16 : ra ≠ .x16) (ha28 : ra ≠ .x28)
    (hb6 : rb ≠ .x6) (hb7 : rb ≠ .x7) (hb16 : rb ≠ .x16) (hb28 : rb ≠ .x28)
    (hab : ra ≠ rb)
    (hd : (Region.mk a ((16*n+8)*blocks)).Disjoint ⟨b,(16*n+8)*blocks⟩)
    (hwa : ∀ j < blocks, ∀ i < n,
      InRegions s₀.wr ((a+BitVec.ofNat 64 ((16*n+8)*j))+BitVec.ofNat 64 (16*i)) 16)
    (hwb : ∀ j < blocks, ∀ i < n,
      InRegions s₀.wr ((b+BitVec.ofNat 64 ((16*n+8)*j))+BitVec.ofNat 64 (16*i)) 16)
    (hwal : ∀ j < blocks,
      InRegions s₀.wr ((a+BitVec.ofNat 64 ((16*n+8)*j))+BitVec.ofNat 64 (16*n)) 8)
    (hwbl : ∀ j < blocks,
      InRegions s₀.wr ((b+BitVec.ofNat 64 ((16*n+8)*j))+BitVec.ofNat 64 (16*n)) 8) :
    WP isa (.loop (.seq core.code
      (.block (Impl.MlDsa.AArch64.Optimized.Resident.squeeze (2*n+1) ra rb ++
        ([.addImm .x ra ra (8*(2*n+1)),.addImm .x rb rb (8*(2*n+1)),
          .subImm .x .x28 .x28 1] : List Instr)))) (.nonzero .x .x28)) s
      (StreamState s₀ a b n blocks ra rb A B blocks) := by
  let Inv : Nat → State → Prop := fun left t => ∃ j, j < blocks ∧ left=blocks-j ∧
    StreamState s₀ a b n blocks ra rb A B j t
  refine WP.loop (M := isa) Inv (fun left t ⟨j,hj,hl,ht⟩ => ?_) (blocks-start) s ⟨start,hstart,rfl,h⟩
  refine WP.mono (streamStepWith_ok core hn hblocks hj ht ha6 ha7 ha16 ha28 hb6 hb7 hb16 hb28 hab
    hd hwa hwb hwal hwbl) ?_
  intro u hu
  by_cases hend : j+1=blocks
  · left
    refine ⟨?_,hend ▸ hu⟩
    simp only [eval,State.read,Size.bits,BitVec.setWidth_eq,hu.count,hend,Nat.sub_self]
    rfl
  · right
    refine ⟨?_,blocks-(j+1),by omega,j+1,by omega,rfl,hu⟩
    have hv : BitVec.ofNat 64 (blocks-(j+1)) ≠ 0 := by
      intro he
      have he' := congrArg BitVec.toNat he
      change (blocks-(j+1)) % 2^64 = 0 at he'
      have hb : blocks-(j+1) < 2^64 := by omega
      rw [Nat.mod_eq_of_lt hb] at he'
      omega
    simp only [eval,State.read,Size.bits,BitVec.setWidth_eq,hu.count]
    simp only [Option.some.injEq,bne_iff_ne]
    exact hv


/-- Complete resident stream, including initialization of its public counter. -/
theorem streamWith_ok (core : Core) {s : State} {a b : Addr} {n blocks : Nat} {ra rb : Reg}
    {A B : Spec.Sha3.State} (hn : n ≤ 10) (hblocks : blocks < 65536) (hpos : 0 < blocks)
    (hp : Pairs s A B) (ha : s.gpr ra=a) (hb : s.gpr rb=b)
    (ha6 : ra ≠ .x6) (ha7 : ra ≠ .x7) (ha16 : ra ≠ .x16) (ha28 : ra ≠ .x28)
    (hb6 : rb ≠ .x6) (hb7 : rb ≠ .x7) (hb16 : rb ≠ .x16) (hb28 : rb ≠ .x28)
    (hab : ra ≠ rb)
    (hd : (Region.mk a ((16*n+8)*blocks)).Disjoint ⟨b,(16*n+8)*blocks⟩)
    (hwa : ∀ j < blocks, ∀ i < n,
      InRegions s.wr ((a+BitVec.ofNat 64 ((16*n+8)*j))+BitVec.ofNat 64 (16*i)) 16)
    (hwb : ∀ j < blocks, ∀ i < n,
      InRegions s.wr ((b+BitVec.ofNat 64 ((16*n+8)*j))+BitVec.ofNat 64 (16*i)) 16)
    (hwal : ∀ j < blocks,
      InRegions s.wr ((a+BitVec.ofNat 64 ((16*n+8)*j))+BitVec.ofNat 64 (16*n)) 8)
    (hwbl : ∀ j < blocks,
      InRegions s.wr ((b+BitVec.ofNat 64 ((16*n+8)*j))+BitVec.ofNat 64 (16*n)) 8) :
    WP isa (Impl.MlDsa.AArch64.Optimized.Resident.streamWith core.code (2*n+1) blocks ra rb) s
      (StreamState s a b n blocks ra rb A B blocks) := by
  unfold Impl.MlDsa.AArch64.Optimized.Resident.streamWith
  rw [ite_eq_right (by omega)]
  apply WP.seq
  let t := s.write .x .x28 (BitVec.ofNat 64 blocks)
  have he : isa.exec (.movz .x .x28 (BitVec.ofNat 16 blocks) 0) s = some t := by
    simp only [isa,exec,Size.bits,Nat.mul_zero,show (0 : Nat)<64 by decide,ite_true,
      BitVec.shiftLeft_zero]
    congr 2
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt hblocks]
  refine WP.block_cons_iff.mpr ⟨t,he,WP.block_nil_iff.mpr ?_⟩
  apply streamLoopWith_ok core hn hblocks hpos ?_ ha6 ha7 ha16 ha28 hb6 hb7 hb16 hb28 hab hd hwa hwb hwal hwbl
  refine ⟨Nat.zero_le _,hp,?_,?_,Frame.refl _ _,?_,?_,?_,?_,rfl,rfl,rfl⟩
  · intro i hi; omega
  · intro i hi; omega
  · simpa only [t,RegUpd.gpr_write,ha28,ite_false,Nat.mul_zero,BitVec.add_zero] using ha
  · simpa only [t,RegUpd.gpr_write,hb28,ite_false,Nat.mul_zero,BitVec.add_zero] using hb
  · simp only [t,RegUpd.gpr_write_self,Nat.sub_zero,Size.bits,BitVec.setWidth_eq]
  · intro r _ _ hr28 _ _ _
    simp only [t,RegUpd.gpr_write,hr28,ite_false]

theorem stream_ok {s : State} {a b : Addr} {n blocks : Nat} {ra rb : Reg}
    {A B : Spec.Sha3.State} (hn : n ≤ 10) (hblocks : blocks < 65536) (hpos : 0 < blocks)
    (hp : Pairs s A B) (ha : s.gpr ra=a) (hb : s.gpr rb=b)
    (ha6 : ra ≠ .x6) (ha7 : ra ≠ .x7) (ha16 : ra ≠ .x16) (ha28 : ra ≠ .x28)
    (hb6 : rb ≠ .x6) (hb7 : rb ≠ .x7) (hb16 : rb ≠ .x16) (hb28 : rb ≠ .x28)
    (hab : ra ≠ rb)
    (hd : (Region.mk a ((16*n+8)*blocks)).Disjoint ⟨b,(16*n+8)*blocks⟩)
    (hwa : ∀ j < blocks, ∀ i < n,
      InRegions s.wr ((a+BitVec.ofNat 64 ((16*n+8)*j))+BitVec.ofNat 64 (16*i)) 16)
    (hwb : ∀ j < blocks, ∀ i < n,
      InRegions s.wr ((b+BitVec.ofNat 64 ((16*n+8)*j))+BitVec.ofNat 64 (16*i)) 16)
    (hwal : ∀ j < blocks,
      InRegions s.wr ((a+BitVec.ofNat 64 ((16*n+8)*j))+BitVec.ofNat 64 (16*n)) 8)
    (hwbl : ∀ j < blocks,
      InRegions s.wr ((b+BitVec.ofNat 64 ((16*n+8)*j))+BitVec.ofNat 64 (16*n)) 8) :
    WP isa (Impl.MlDsa.AArch64.Optimized.Resident.stream (2*n+1) blocks ra rb) s
      (StreamState s a b n blocks ra rb A B blocks) :=
  streamWith_ok originalCore hn hblocks hpos hp ha hb ha6 ha7 ha16 ha28 hb6 hb7 hb16 hb28 hab hd hwa hwb hwal hwbl

end VG.Proof.MlDsa.AArch64.Optimized.Resident
