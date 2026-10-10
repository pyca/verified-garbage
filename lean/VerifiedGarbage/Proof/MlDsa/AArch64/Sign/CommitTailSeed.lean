import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailCoreState
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentSeed66
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentSeed

/-! ## From `CommitTailCoreRound.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.Sha3.AArch64.Sha3.Vector (rounds)

/-- Each inline permutation advances both unrelated sponge states. -/
theorem coreRound_ok {σ s : State} {wlen i : Nat} {w1 work : Addr}
    {A B : Spec.Sha3.State} (h : CoreState σ wlen w1 work A B i s) :
    WP isa (.block rounds) s (RoundState σ wlen w1 work A B i i) := by
  refine WP.mono (VG.Proof.MlDsa.AArch64.Optimized.Resident.permute_ok h.pairs)
    fun t ⟨hk,hp⟩ => ?_
  refine ⟨⟨?_,?_,?_,?_⟩,hp⟩
  · refine ⟨fun r hr=>?_,hk.rd.trans h.keep.rd,hk.wr.trans h.keep.wr,hk.sp.trans h.keep.sp⟩
    exact (hk.gpr r (fun he=>hr (by simp [coreRegs,he]))).trans (h.keep.gpr r hr)
  · rw [hk.mem]; exact h.frame
  · rw [hk.gpr .x5 (by decide)]; exact h.ptr
  · rw [hk.mem]; exact h.output

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailCoreEmit.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Sign.CommitTail

/-- Only the first five permutations serialize the independent mask stream. -/
theorem coreEmit_ok {σ s : State} {wlen i : Nat} {w1 work : Addr}
    {A B : Spec.Sha3.State} (hc : CoreConfig σ wlen w1 work)
    (h : RoundState σ wlen w1 work A B i i s) :
    WP isa (.block (if i<5 then squeeze i else [])) s
      (RoundState σ wlen w1 work A B i (i+1)) := by
  by_cases hi : i<5
  · rw [ite_eq_left hi]
    have hw : s.gpr .x19=work := (h.keep.gpr .x19 (by decide)).trans hc.workPtr
    refine WP.mono (squeeze_ok i hi h.pairs ?_ ?_) fun t ⟨hk,hp,ho,hf⟩ => ?_
    · intro j hj
      rw [h.keep.wr,hw,Offset.add_add]
      exact hc.writable _ _ (by omega)
    · rw [h.keep.wr,hw]
      change InRegions σ.wr ((work+BitVec.ofNat 64 (256+136*i))+BitVec.ofNat 64 128) 8
      rw [Offset.add_add]
      exact hc.writable _ _ (by omega)
    · rw [hw,buffer_addr] at ho hf
      refine ⟨⟨(h.keep.trans hk).mono (by simp [coreRegs]),?_,?_,?_⟩,hp⟩
      · apply h.frame.trans
        exact hf.sub (by
          intro r hr
          rcases List.mem_singleton.mp hr with rfl
          exact ⟨bufferRegion work,by simp,Offset.sub_base (bufferBase work)
            (d:=136*i) (n:=136) (k:=680) (by omega)⟩)
      · rw [hk.gpr .x5 (by decide)]; exact h.ptr
      · rw [Nat.min_eq_left (by omega)]
        have hold := h.output
        rw [Nat.min_eq_left (by omega)] at hold
        exact streamOutput_append hi hold ho hf
  · rw [ite_eq_right hi]
    refine WP.block_nil_iff.mpr ⟨⟨h.keep,h.frame,h.ptr,?_⟩,h.pairs⟩
    have ho := h.output
    rw [Nat.min_eq_right (by omega)] at ho
    rw [Nat.min_eq_right (by omega)]
    exact ho

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailCoreFull.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64.Sha3.Vector (xorWords)
open VG.Impl.MlDsa.AArch64.Sign.CommitTail

private theorem full_bound {σ : State} {wlen i j : Nat} {w1 work : Addr}
    (hc : CoreConfig σ wlen w1 work) (hi : i<(64+wlen)/136-1) (hj : j<17) :
    72+136*i+8*j+8≤wlen := by
  rcases hc.length with he|he
  · rw [he] at hi ⊢
    simp only [Nat.reduceAdd,Nat.reduceDiv,Nat.reduceSub] at hi
    omega
  · rw [he] at hi ⊢
    simp only [Nat.reduceAdd,Nat.reduceDiv,Nat.reduceSub] at hi
    omega

/-- The next full commitment block is read from the immutable packed input. -/
theorem coreFull_ok {σ s : State} {wlen i : Nat} {w1 work : Addr}
    {A B : Spec.Sha3.State} (hc : CoreConfig σ wlen w1 work)
    (hi : i<(64+wlen)/136-1) (h : RoundState σ wlen w1 work A B i (i+1) s) :
    WP isa (.block full) s (CoreState σ wlen w1 work A B (i+1)) := by
  have hptr : s.gpr .x5=w1+BitVec.ofNat 64 (72+136*i) := by
    rw [h.ptr,inputPtr,fullCount,Nat.min_eq_left (by omega)]
  refine WP.mono (full_ok h.pairs (fun j hj=>?_)) fun t ⟨hk,hm,hp5,hp⟩ => ?_
  · rw [hptr,Offset.add_add]
    exact h.toCoreEnv.readable hc (full_bound hc hi hj)
  · have he : xorWords (Spec.Sha3.keccakF (lowRun wlen σ.mem w1 A i)) s.mem
        (w1+BitVec.ofNat 64 (72+136*i)) 17 =
      xorWords (Spec.Sha3.keccakF (lowRun wlen σ.mem w1 A i)) σ.mem
        (w1+BitVec.ofNat 64 (72+136*i)) 17 := by
      apply xorWords_congr
      intro j hj
      rw [Offset.add_add]
      exact h.toCoreEnv.word hc (full_bound hc hi hj)
    rw [hptr,he] at hp
    refine ⟨⟨(h.keep.trans hk).mono (by simp [coreRegs]),?_,?_,?_⟩,?_⟩
    · rw [hm]; exact h.frame
    · rw [hp5,hptr]
      change (w1+BitVec.ofNat 64 (72+136*i))+BitVec.ofNat 64 136=inputPtr wlen w1 (i+1)
      rw [Offset.add_add,inputPtr,fullCount,Nat.min_eq_left (by omega)]
      congr 1
    · rw [hm]; exact h.output
    · change Pairs t (absorbAfter wlen σ.mem w1 i (Spec.Sha3.keccakF (lowRun wlen σ.mem w1 A i))) _
      rw [absorbAfter,ite_eq_left hi]
      exact hp

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailCoreTail.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64.Sha3.Vector (xorWords)
open VG.Impl.MlDsa.AArch64.Sign.CommitTail

theorem coreTail65_ok {σ s : State} {w1 work : Addr} {A B : Spec.Sha3.State}
    (hc : CoreConfig σ 768 w1 work) (h : RoundState σ 768 w1 work A B 5 6 s) :
    WP isa (.block tail) s (CoreState σ 768 w1 work A B 6) := by
  have hptr : s.gpr .x5=w1+BitVec.ofNat 64 752 := h.ptr
  refine WP.mono (tail_ok h.pairs (fun j hj=>?_)) fun t ⟨hk,hm,hp⟩ => ?_
  · rw [hptr,Offset.add_add]
    exact h.toCoreEnv.readable hc (by omega)
  · have he : xorWords (Spec.Sha3.keccakF (lowRun 768 σ.mem w1 A 5)) s.mem
        (w1+BitVec.ofNat 64 752) 2 =
      xorWords (Spec.Sha3.keccakF (lowRun 768 σ.mem w1 A 5)) σ.mem
        (w1+BitVec.ofNat 64 752) 2 := by
      apply xorWords_congr
      intro j hj
      rw [Offset.add_add]
      exact h.toCoreEnv.word hc (by omega)
    rw [hptr,he] at hp
    refine ⟨⟨(h.keep.trans hk).mono (by simp [coreRegs]),?_,?_,?_⟩,?_⟩
    · rw [hm]; exact h.frame
    · rw [hk.gpr .x5 (by decide)]
      exact h.ptr
    · rw [hm]; exact h.output
    · change Pairs t (absorbAfter 768 σ.mem w1 5 (Spec.Sha3.keccakF (lowRun 768 σ.mem w1 A 5))) _
      simpa only [absorbAfter,Nat.reduceAdd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceLT,
        Nat.reduceMul,ite_false,ite_true] using hp

theorem coreTail87_ok {σ s : State} {w1 work : Addr} {A B : Spec.Sha3.State}
    (h : RoundState σ 1024 w1 work A B 7 8 s) :
    WP isa (.block (paddingWord 0 31 0 ++ paddingWord 16 0x8000 3)) s
      (CoreState σ 1024 w1 work A B 8) := by
  refine WP.mono (padding_ok (by decide) h.pairs) fun t ⟨hk,hm,hp⟩ => ?_
  refine ⟨⟨(h.keep.trans hk).mono (by simp [coreRegs]),?_,?_,?_⟩,?_⟩
  · rw [hm]; exact h.frame
  · rw [hk.gpr .x5 (by decide)]
    exact h.ptr
  · rw [hm]; exact h.output
  · change Pairs t (absorbAfter 1024 σ.mem w1 7 (Spec.Sha3.keccakF (lowRun 1024 σ.mem w1 A 7))) _
    simpa only [absorbAfter,Nat.reduceAdd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceLT,
      ite_false,ite_true,ite_eq_right (by decide : ¬ (1024:Nat)=768)] using hp

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailCoreStep.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Sign.CommitTail
open VG.Impl.Sha3.AArch64.Sha3.Vector (rounds)

def absorbCode (wlen i : Nat) : List Instr :=
  let n := (64+wlen)/136
  if i<n-1 then full else if i==n-1 then
    if wlen=768 then tail else paddingWord 0 31 0 ++ paddingWord 16 0x8000 3
  else []

theorem coreAbsorb_ok {σ s : State} {wlen i : Nat} {w1 work : Addr}
    {A B : Spec.Sha3.State} (hc : CoreConfig σ wlen w1 work)
    (h : RoundState σ wlen w1 work A B i (i+1) s) :
    WP isa (.block (absorbCode wlen i)) s (CoreState σ wlen w1 work A B (i+1)) := by
  by_cases hi : i<(64+wlen)/136-1
  · rw [absorbCode,ite_eq_left hi]
    exact coreFull_ok hc hi h
  · by_cases he : i=(64+wlen)/136-1
    · rcases hc.length with hw|hw
      · subst wlen
        have hi5 : i=5 := he
        subst i
        exact coreTail65_ok hc h
      · subst wlen
        have hi7 : i=7 := he
        subst i
        exact coreTail87_ok h
    · have hb : (i==((64+wlen)/136-1))=false := by simp [he]
      rw [absorbCode,ite_eq_right hi,hb]
      refine WP.block_nil_iff.mpr ⟨⟨h.keep,h.frame,?_,h.output⟩,?_⟩
      · rw [h.ptr,inputPtr,inputPtr,fullCount,fullCount,
          Nat.min_eq_right (by omega),Nat.min_eq_right (by omega)]
      · change Pairs s (absorbAfter wlen σ.mem w1 i
          (Spec.Sha3.keccakF (lowRun wlen σ.mem w1 A i))) _
        rw [absorbAfter,ite_eq_right hi,ite_eq_right he]
        exact h.pairs

/-- One exact unrolled core step: shared permutation, optional mask squeeze,
and the next commitment absorb. -/
theorem coreStep_ok {σ s : State} {wlen i : Nat} {w1 work : Addr}
    {A B : Spec.Sha3.State} (hc : CoreConfig σ wlen w1 work)
    (h : CoreState σ wlen w1 work A B i s) :
    WP isa (.seq (.block rounds)
      (.block ((if i<5 then squeeze i else []) ++ absorbCode wlen i))) s
      (CoreState σ wlen w1 work A B (i+1)) := by
  rw [WP.seq_iff]
  refine WP.mono (coreRound_ok h) fun a ha=>?_
  rw [WP.block_append_iff]
  exact WP.mono (coreEmit_ok hc ha) fun b hb=>coreAbsorb_ok hc hb

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailCore.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Sign.CommitTail
open VG.Impl.Sha3.AArch64.Sha3.Vector (rounds)

def coreSequence (wlen : Nat) (is : List Nat) : Prog isa :=
  is.foldr (fun i rest=>.seq (.block rounds)
    (.seq (.block ((if i<5 then squeeze i else []) ++ absorbCode wlen i)) rest)) (.block [])

private theorem sequence_ok {σ : State} {wlen : Nat} {w1 work : Addr}
    {A B : Spec.Sha3.State} (hc : CoreConfig σ wlen w1 work) (count start : Nat)
    {s : State} (h : CoreState σ wlen w1 work A B start s) :
    WP isa (coreSequence wlen (List.range' start count)) s
      (CoreState σ wlen w1 work A B (start+count)) := by
  induction count generalizing start s with
  | zero =>
    change WP isa (.block []) s (CoreState σ wlen w1 work A B start)
    exact WP.block_nil h
  | succ count ih =>
    simp only [List.range'_succ,coreSequence,List.foldr_cons]
    rw [WP.seq_iff]
    have hs := coreStep_ok hc h
    rw [WP.seq_iff] at hs
    refine WP.mono hs fun a ha=>?_
    rw [WP.seq_iff]
    refine WP.mono ha fun b hb=>?_
    have hh := ih (start+1) hb
    rw [show start+1+count=start+(count+1) by omega] at hh
    exact hh

/-- Exact selected unrolled schedule: seven permutations for ML-DSA-65,
nine for ML-DSA-87, with only five cached-mask squeeze blocks. -/
theorem core_ok {σ s : State} {wlen : Nat} {w1 work : Addr} {A B : Spec.Sha3.State}
    (hc : CoreConfig σ wlen w1 work) (h : CoreState σ wlen w1 work A B 0 s) :
    WP isa (coreFor wlen) s (CoreState σ wlen w1 work A B ((64+wlen)/136+1)) := by
  have he : coreFor wlen=coreSequence wlen (List.range ((64+wlen)/136+1)) := rfl
  rw [he,List.range_eq_range']
  simpa only [Nat.zero_add] using sequence_ok hc ((64+wlen)/136+1) 0 h

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailNonceValue.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG

theorem nonceWord_value (k : BitVec 64) :
    (nonceWord k).toNat=k.toNat%65536+2031616 := by
  have hx : ((k <<< 48) >>> 48).toNat=k.toNat%65536 := by
    rw [BitVec.toNat_ushiftRight,BitVec.toNat_shiftLeft,Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow]
    change (k.toNat*281474976710656 % (65536*281474976710656))/281474976710656=_
    rw [Nat.mul_mod_mul_right,Nat.mul_div_cancel _ (by decide)]
  rw [nonceWord,BitVec.toNat_add,hx]
  change (k.toNat%65536+2031616)%18446744073709551616=_
  exact Nat.mod_eq_of_lt (by omega)

theorem nonceValue_byte (a k : BitVec 64) (hk : a.toNat=k.toNat%65536+2031616) {i : Nat} (hi : i<8) :
    a.extractLsb' (8*i) 8 =
      if i=0 then k.extractLsb' 0 8 else if i=1 then k.extractLsb' 8 8
      else if i=2 then 0x1f else 0 := by
  rcases (show i=0 ∨ i=1 ∨ i=2 ∨ 3≤i by omega) with h|h|h|h
  · subst i
    simp only [ite_true,Nat.mul_zero]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,Nat.reducePow]
    rw [hk, Nat.div_one, Nat.add_mod]
    simp only [show 2031616 % 256 = 0 from rfl, Nat.add_zero, Nat.mod_mod]
    simpa only [Nat.div_one] using Nat.mod_mul_right_mod k.toNat 256 256
  · subst i
    simp only [ite_eq_right (by decide : ¬ (1:Nat)=0),ite_true,Nat.mul_one]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,Nat.reducePow]
    rw [hk]
    change ((k.toNat % (256*256) + 7936*256)/256)%256 = _
    rw [Nat.add_mul_div_right _ _ (by decide), Nat.add_mod]
    simp only [show 7936 % 256 = 0 from rfl, Nat.add_zero, Nat.mod_mod]
    rw [Nat.mod_mul_right_div_self, Nat.mod_mod]
  · subst i
    simp only [ite_eq_right (by decide : ¬ (2:Nat)=0),ite_eq_right (by decide : ¬ (2:Nat)=1),ite_true]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,Nat.reducePow,Nat.reduceMul]
    rw [hk]
    change ((k.toNat % 65536 + 31*65536)/65536)%256 = 31
    rw [Nat.add_mul_div_right _ _ (by decide), Nat.mod_div_self]
  · simp only [ite_eq_right (by omega : ¬ i=0),ite_eq_right (by omega : ¬ i=1),
      ite_eq_right (by omega : ¬ i=2)]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.extractLsb'_toNat]
    have hb : 8*i≥24 := by omega
    have he : a.toNat<2^24 := by omega
    have hdiv : a.toNat/2^(8*i)=0 := Nat.div_eq_of_lt (Nat.lt_of_lt_of_le he (Nat.pow_le_pow_right (by decide) hb))
    rw [Nat.shiftRight_eq_div_pow,hdiv]
    rfl

theorem nonceWord_byte (k : BitVec 64) {i : Nat} (hi : i<8) :
    (nonceWord k).extractLsb' (8*i) 8 =
      if i=0 then k.extractLsb' 0 8 else if i=1 then k.extractLsb' 8 8
      else if i=2 then 0x1f else 0 :=
  nonceValue_byte (nonceWord k) k (nonceWord_value k) hi

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailSeed.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG

def seedBytes (m : Mem) (p : Addr) (k : BitVec 64) : List Byte :=
  Spec.Sha3.bytesAt m p 64 ++ [k.extractLsb' 0 8,k.extractLsb' 8 8]

theorem seedBytes_length (m : Mem) (p : Addr) (k : BitVec 64) :
    (seedBytes m p k).length=66 := by
  simp only [seedBytes,List.length_append,Proof.Sha3.bytesAt_length,List.length_cons,List.length_nil]

theorem seedBytes_get (m : Mem) (p : Addr) (k : BitVec 64) {j : Nat} (hj : j<66) :
    (seedBytes m p k).getD j 0 = if j<64 then m (p+BitVec.ofNat 64 j)
      else if j=64 then k.extractLsb' 0 8 else k.extractLsb' 8 8 := by
  unfold seedBytes
  by_cases h : j<64
  · rw [ite_eq_left h]
    rw [List.getD,List.getElem?_append_left (by rw [Proof.Sha3.bytesAt_length]; exact h)]
    exact Proof.MlKem.bytesAt_getD m p h
  · rw [ite_eq_right h,List.getD,List.getElem?_append_right (by rw [Proof.Sha3.bytesAt_length]; omega),Proof.Sha3.bytesAt_length]
    rcases (show j=64 ∨ j=65 by omega) with rfl|rfl <;> rfl

theorem seedNonceState_get (m : Mem) (p : Addr) (k : BitVec 64) {i : Nat} (hi : i<25) :
    (seedNonceState m p k)[i]! = if i<8 then m.readW (p+BitVec.ofNat 64 (8*i)) 64
      else if i=8 then nonceWord k else if i=16 then 0x8000000000000000 else 0 := by
  rw [Proof.Sha3.getElem!_eq _ hi]
  unfold seedNonceState
  rw [Vector.getElem_ofFn]

theorem seedNonceState_A0 (m : Mem) (p : Addr) (k : BitVec 64) :
    seedNonceState m p k = Optimized.ResidentSeed66.A0 (seedBytes m p k) := by
  apply Proof.Sha3.ext_bytes
  intro j hj
  rw [Optimized.ResidentSeed66.byteOf_A0 (seedBytes_length m p k) hj]
  unfold Proof.Sha3.byteOf
  rw [seedNonceState_get m p k (by omega)]
  by_cases h32 : j<64
  · rw [ite_eq_left (by omega : j/8<8),ite_eq_left (by omega : j<66),
      seedBytes_get m p k (by omega),ite_eq_left h32]
    change (m.read (p+BitVec.ofNat 64 (8*(j/8))) 8).extractLsb' (8*(j%8)) 8 = _
    rw [Mem.extractLsb'_read m _ (by omega),BitVec.add_assoc,← BitVec.ofNat_add,
      show 8*(j/8)+j%8=j by omega]
  · rw [ite_eq_right (by omega : ¬ j/8<8)]
    by_cases h40 : j<72
    · rw [ite_eq_left (by omega : j/8=8),nonceWord_byte k (by omega)]
      rcases (show j=64 ∨ j=65 ∨ j=66 ∨ 67≤j by omega) with h|h|h|h
      · subst j
        rw [ite_eq_left (by decide : 64<66),seedBytes_get m p k (by decide)]
        rfl
      · subst j
        rw [ite_eq_left (by decide : 65<66),seedBytes_get m p k (by decide)]
        rfl
      · subst j; simp
      · simp (disch := omega) only [ite_eq_right]
    · rw [ite_eq_right (by omega : ¬ j/8=8)]
      by_cases h20 : j/8=16
      · rw [ite_eq_left h20,Optimized.ResidentMask.pad_byte (j%8) (by omega)]
        by_cases he : j=135 <;> simp (disch := omega) only [ite_eq_left,ite_eq_right]
      · rw [ite_eq_right h20]
        simp (disch := omega) only [ite_eq_right]
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        simp

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end
