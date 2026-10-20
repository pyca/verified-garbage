module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMemory
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract

/-! ## From `ResidentBody.lean` -/

@[expose] public section

section

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
    (hwbl : InRegions s.wr (b+BitVec.ofNat 64 (16*n)) 8)
    (htab : VG.Proof.Sha3.AArch64.Neon.Hw.RcTable s (s.gpr .x15)) :
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
  refine WP.mono (core.correct hp htab) ?_
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

end VG.Proof.MlDsa.AArch64.Optimized.Resident

end

/-! ## From `ResidentStream.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Resident
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon (Pairs)

structure StreamState (s₀ : State) (T a b : Addr) (n blocks : Nat) (ra rb : Reg)
    (A B : Spec.Sha3.State) (j : Nat) (s : State) : Prop where
  bound : j ≤ blocks
  pairs : Pairs s (permuted A j) (permuted B j)
  outA : StreamOutput s.mem a n j A
  outB : StreamOutput s.mem b n j B
  frame : Frame [⟨a,(16*n+8)*blocks⟩,⟨b,(16*n+8)*blocks⟩,⟨T,384⟩] s₀.mem s.mem
  ptrA : s.gpr ra = a+BitVec.ofNat 64 ((16*n+8)*j)
  ptrB : s.gpr rb = b+BitVec.ofNat 64 ((16*n+8)*j)
  count : s.gpr .x28 = BitVec.ofNat 64 (blocks-j)
  gpr : ∀ r, r ≠ ra → r ≠ rb → r ≠ .x28 → r ≠ .x6 → r ≠ .x7 → r ≠ .x16 → r ≠ .x15 → s.gpr r=s₀.gpr r
  rd : s.rd=s₀.rd
  wr : s.wr=s₀.wr
  sp : s.sp=s₀.sp
  ptrT : s.gpr .x15=T
  tbl : VG.Proof.Sha3.AArch64.Neon.Hw.RcTable s T

/-- One iteration extends both exact output streams and decreases the public
remaining-block count. -/
theorem streamStepWith_ok (core : Core) {s₀ s : State} {T a b : Addr} {n blocks j : Nat} {ra rb : Reg}
    {A B : Spec.Sha3.State} (hn : n ≤ 10) (hblocks : blocks < 65536)
    (hj : j < blocks) (h : StreamState s₀ T a b n blocks ra rb A B j s)
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
      InRegions s₀.wr ((b+BitVec.ofNat 64 ((16*n+8)*j))+BitVec.ofNat 64 (16*n)) 8)
    (ha15 : ra ≠ .x15) (hb15 : rb ≠ .x15)
    (hTa : (Region.mk T 384).Disjoint ⟨a,(16*n+8)*blocks⟩)
    (hTb : (Region.mk T 384).Disjoint ⟨b,(16*n+8)*blocks⟩) :
    WP isa (.seq core.code
      (.block (Impl.MlDsa.AArch64.Optimized.Resident.squeeze (2*n+1) ra rb ++
        ([.addImm .x ra ra (8*(2*n+1)),.addImm .x rb rb (8*(2*n+1)),
          .subImm .x .x28 .x28 1] : List Instr)))) s
      (StreamState s₀ T a b n blocks ra rb A B (j+1)) := by
  have sub (p : Addr) :
      (Region.mk (p+BitVec.ofNat 64 ((16*n+8)*j)) (16*n+8)).Sub
        ⟨p,(16*n+8)*blocks⟩ := by
    apply Offset.sub_base
    simpa only [Nat.mul_succ] using Nat.mul_le_mul_left (16*n+8) hj
  refine WP.mono (bodyWith_ok core hn h.pairs h.ptrA h.ptrB ha6 ha7 ha16 ha28 hb6 hb7 hb16 hb28 hab
    ((hd.sub_left (sub a)).sub_right (sub b))
    (by simpa only [h.wr] using hwa j hj) (by simpa only [h.wr] using hwb j hj)
    (by simpa only [h.wr] using hwal j hj) (by simpa only [h.wr] using hwbl j hj)
    (by rw [h.ptrT]; exact h.tbl)) ?_
  intro t ht
  have hout := StreamOutput.append hn hj (by omega) hd h.outA h.outB ht.2.1 ht.2.2.1 ht.2.2.2.1
  have h15 : t.gpr .x15 = s.gpr .x15 :=
    ht.2.2.2.2.2.2.2.1 .x15 ha15.symm hb15.symm (by decide) (by decide) (by decide) (by decide)
  refine ⟨by omega,ht.1,hout.1,hout.2,?_,?_,?_,?_,?_,ht.2.2.2.2.2.2.2.2.1.trans h.rd,
    ht.2.2.2.2.2.2.2.2.2.1.trans h.wr,ht.2.2.2.2.2.2.2.2.2.2.trans h.sp,h15.trans h.ptrT,
    h.tbl.frame ht.2.2.2.1 (fun r hr => by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      exacts [hTa.sub_right (sub a), hTb.sub_right (sub b)])
      ht.2.2.2.2.2.2.2.2.1 ht.2.2.2.2.2.2.2.2.2.1⟩
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
  · intro r hra hrb hr28 hr6 hr7 hr16 hr15
    exact (ht.2.2.2.2.2.2.2.1 r hra hrb hr28 hr6 hr7 hr16).trans
      (h.gpr r hra hrb hr28 hr6 hr7 hr16 hr15)

/-- The resident loop terminates after the public number of blocks and writes
both complete streams, without reloading or spilling either Keccak state. -/
theorem streamLoopWith_ok (core : Core) {s₀ s : State} {T a b : Addr} {n blocks start : Nat} {ra rb : Reg}
    {A B : Spec.Sha3.State} (hn : n ≤ 10) (hblocks : blocks < 65536)
    (hstart : start < blocks) (h : StreamState s₀ T a b n blocks ra rb A B start s)
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
      InRegions s₀.wr ((b+BitVec.ofNat 64 ((16*n+8)*j))+BitVec.ofNat 64 (16*n)) 8)
    (ha15 : ra ≠ .x15) (hb15 : rb ≠ .x15)
    (hTa : (Region.mk T 384).Disjoint ⟨a,(16*n+8)*blocks⟩)
    (hTb : (Region.mk T 384).Disjoint ⟨b,(16*n+8)*blocks⟩) :
    WP isa (.loop (.seq core.code
      (.block (Impl.MlDsa.AArch64.Optimized.Resident.squeeze (2*n+1) ra rb ++
        ([.addImm .x ra ra (8*(2*n+1)),.addImm .x rb rb (8*(2*n+1)),
          .subImm .x .x28 .x28 1] : List Instr)))) (.nonzero .x .x28)) s
      (StreamState s₀ T a b n blocks ra rb A B blocks) := by
  let Inv : Nat → State → Prop := fun left t => ∃ j, j < blocks ∧ left=blocks-j ∧
    StreamState s₀ T a b n blocks ra rb A B j t
  refine WP.loop (M := isa) Inv (fun left t ⟨j,hj,hl,ht⟩ => ?_) (blocks-start) s ⟨start,hstart,rfl,h⟩
  refine WP.mono (streamStepWith_ok core hn hblocks hj ht ha6 ha7 ha16 ha28 hb6 hb7 hb16 hb28 hab
    hd hwa hwb hwal hwbl ha15 hb15 hTa hTb) ?_
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


/-- Complete resident stream, including initialization of its public counter
and of the table of the round constants, at `T`. -/
theorem streamWith_ok (core : Core) {s : State} {T a b : Addr} {n blocks : Nat} {ra rb base : Reg}
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
      InRegions s.wr ((b+BitVec.ofNat 64 ((16*n+8)*j))+BitVec.ofNat 64 (16*n)) 8)
    (ha15 : ra ≠ .x15) (hb15 : rb ≠ .x15)
    (hTa : (Region.mk T 384).Disjoint ⟨a,(16*n+8)*blocks⟩)
    (hTb : (Region.mk T 384).Disjoint ⟨b,(16*n+8)*blocks⟩)
    (hbase : base ≠ .x28) (hT : s.gpr base + BitVec.ofNat 64 7296 = T)
    (hwT : ∀ i < 48, InRegions s.wr (T + BitVec.ofNat 64 (8 * i)) 8)
    (hwT16 : ∀ r < 24, InRegions s.wr (T + BitVec.ofNat 64 (16 * r)) 16) :
    WP isa (Impl.MlDsa.AArch64.Optimized.Resident.streamWith core.code (2*n+1) blocks ra rb base) s
      (StreamState s T a b n blocks ra rb A B blocks) := by
  unfold Impl.MlDsa.AArch64.Optimized.Resident.streamWith
  rw [ite_eq_right (by omega)]
  apply WP.seq
  let t := s.write .x .x28 (BitVec.ofNat 64 blocks)
  have he : isa.exec (.movz .x .x28 (BitVec.ofNat 16 blocks) 0) s = some t := by
    simp only [isa,exec,Size.bits,Nat.mul_zero,show (0 : Nat)<64 by decide,ite_true,
      BitVec.shiftLeft_zero]
    have hv : BitVec.setWidth 64 (BitVec.ofNat 16 blocks) = BitVec.ofNat 64 blocks := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt hblocks]
    rw [hv]
  have h28 : t.gpr .x28 = BitVec.ofNat 64 blocks := by
    simp only [t,RegUpd.gpr_write_self,Size.bits,BitVec.setWidth_eq]
  have ht : ∀ r, r ≠ .x28 → t.gpr r = s.gpr r := fun r hr => by
    simp only [t,RegUpd.gpr_write,hr,ite_false]
  simp only [List.cons_append, List.nil_append]
  refine WP.block_cons_iff.mpr ⟨t,he,?_⟩
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (VG.Proof.Sha3.AArch64.Neon.Hw.addImm_ok (s := t) (p := .x15) (n := base) (by decide))
    fun t₁ ⟨v₁,m₁,rd₁,wr₁,sp₁,p₁,g₁⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (VG.Proof.Sha3.AArch64.Neon.Hw.addImm_ok (s := t₁) (p := .x15) (n := .x15) (by decide))
    fun t₂ ⟨v₂',m₂',rd₂',wr₂',sp₂',p₂,g₂'⟩ => ?_
  have v₂ : t₂.v = t.v := v₂'.trans v₁
  have m₂ : t₂.mem = t.mem := m₂'.trans m₁
  have rd₂ : t₂.rd = t.rd := rd₂'.trans rd₁
  have wr₂ : t₂.wr = t.wr := wr₂'.trans wr₁
  have sp₂ : t₂.sp = t.sp := sp₂'.trans sp₁
  have g₂ : ∀ g, g ≠ .x15 → t₂.gpr g = t.gpr g := fun g hg => (g₂' g hg).trans (g₁ g hg)
  have hT₂ : t₂.gpr .x15 = T := by
    rw [p₂, p₁, ht base hbase, Offset.add_add, ← hT]; rfl
  refine WP.mono (VG.Proof.Sha3.AArch64.Neon.Hw.rcStore_ok (by decide) hT₂
    (by rw [wr₂]; exact hwT) (by rw [wr₂]; exact hwT16)) fun u ⟨gu,vu,rdu,wru,spu,fu,tu⟩ => ?_
  have hu : ∀ r, r ≠ .x16 → r ≠ .x15 → r ≠ .x28 → u.gpr r = s.gpr r := fun r h16 h15 h28 => by
    rw [gu r h16, g₂ r h15, ht r h28]
  apply streamLoopWith_ok core hn hblocks hpos ?_ ha6 ha7 ha16 ha28 hb6 hb7 hb16 hb28 hab hd hwa hwb hwal hwbl
    ha15 hb15 hTa hTb
  refine ⟨Nat.zero_le _,?_,?_,?_,?_,?_,?_,?_,?_,by rw [rdu,rd₂]; rfl,by rw [wru,wr₂]; rfl,
    by rw [spu,sp₂]; rfl,by rw [gu .x15 (by decide), hT₂],tu⟩
  · intro i hi; rw [vu, v₂]; exact hp i hi
  · intro i hi; omega
  · intro i hi; omega
  · have : t₂.mem = s.mem := m₂
    rw [← this]
    exact fu.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; simp)
  · rw [hu ra ha16 ha15 ha28, ha, Nat.mul_zero, BitVec.add_zero]
  · rw [hu rb hb16 hb15 hb28, hb, Nat.mul_zero, BitVec.add_zero]
  · rw [gu .x28 (by decide), g₂ .x28 (by decide), h28, Nat.sub_zero]
  · intro r _ _ hr28 _ _ hr16 hr15
    exact hu r hr16 hr15 hr28

end VG.Proof.MlDsa.AArch64.Optimized.Resident

end
