module

public import VerifiedGarbage.Impl.Weierstrass.AArch64.FastNaf
public import VerifiedGarbage.Proof.Mont.AArch64.Words
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafPrep
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafSubtract
public import VerifiedGarbage.Proof.Weierstrass.FastNaf
public import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafStep
import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafArith
import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafExec
import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafInit
import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafLoop
import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafState
import VerifiedGarbage.Proof.Weierstrass.AArch64.BytesLen
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvWords
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Mem

/-! The width-nine recoder: its digits as sixteen-bit words, little-endian, stored a byte at a
time, `2 j` bytes past `bits` for digit `j`. -/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64 VG.Proof.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

/-- The recoder's registers and the digits so far, the rest of the 514 bytes zero. -/
structure FastPrep9State (base : Addr) (size bits k j : Nat) (s : State) : Prop where
  scr : Scr s base size
  value : nafVal5 (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) (s.gpr .x8) (s.gpr .x9)=FastNaf.residual 9 k j
  mask : s.gpr .x10=BitVec.ofNat 64 511
  sign : s.gpr .x11=BitVec.ofNat 64 256
  zero : s.gpr .x12=0
  one : s.gpr .x13=1
  ptr : s.gpr .x20=off base (bits+2*j)
  digits : ∀ i<514,s.mem (off base (bits+i))=if i/2<j then FastNaf.wbyte k i else 0

theorem fastWord9_toNat (k j : Nat) : (FastNaf.word k j).toNat=
    if FastNaf.negative 9 k j then 65536-FastNaf.magnitude 9 k j else FastNaf.magnitude 9 k j := by
  have hm : FastNaf.magnitude 9 k j=FastNaf9.magnitude k j := by
    simp only [FastNaf.magnitude,FastNaf.ne_9_7,ite_true,ite_false]
  have hn : FastNaf.negative 9 k j=FastNaf9.negative k j := by
    simp only [FastNaf.negative,FastNaf.ne_9_7,ite_true,ite_false]
  rw [FastNaf.word,FastNaf9.word_toNat,hm,hn]

theorem fastWbyte_toNat (k i : Nat) :
    (FastNaf.wbyte k i).toNat=(FastNaf.word k (i/2)).toNat/2^(8*(i%2))%256 := by
  simp only [FastNaf.wbyte,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow]

/-- The low byte of the digit's register is its word's. -/
theorem fastLow9 (k j : Nat) :
    BitVec.ofNat 8 (BitVec.ofInt 64 (FastNaf.digit 9 k j)).toNat=FastNaf.wbyte k (2*j) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat,fastWord_toNat,fastWbyte_toNat,fastWord9_toNat,
    show 2*j/2=j by omega,show 2*j%2=0 by omega]
  have hb := fastMagnitude_bound 9 k j
  cases hn : FastNaf.negative 9 k j
  · simp only [Bool.false_eq_true,ite_false] <;> omega
  · have hp := FastNaf.negative_magnitude_pos 9 k j hn
    simp only [ite_true] <;> omega

/-- The low byte of the digit's register shifted right by eight is its word's high byte. -/
theorem fastHigh9 (k j : Nat) :
    BitVec.ofNat 8 (BitVec.ofInt 64 (FastNaf.digit 9 k j)>>>8).toNat=FastNaf.wbyte k (2*j+1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,fastWord_toNat,
    fastWbyte_toNat,fastWord9_toNat,show (2*j+1)/2=j by omega,show (2*j+1)%2=1 by omega]
  have hb := fastMagnitude_bound 9 k j
  cases hn : FastNaf.negative 9 k j
  · simp only [Bool.false_eq_true,ite_false] <;> omega
  · have hp := FastNaf.negative_magnitude_pos 9 k j hn
    simp only [ite_true] <;> omega

theorem off_add_one (base : Addr) (d : Nat) : off base d+BitVec.ofNat 64 1=off base (d+1) := by
  unfold off
  rw [Offset.add_add]

/-- The digit in `x2` as two bytes at `x20`. -/
theorem fastStore9_ok {s : State} {base : Addr} {size bits k j : Nat}
    (hs : Scr s base size) (hb : bits+2*j+2≤size)
    (hp : s.gpr .x20=off base (bits+2*j))
    (hd : s.gpr .x2=BitVec.ofInt 64 (FastNaf.digit 9 k j)) :
    WP isa (.block Impl.Weierstrass.AArch64.FastNaf.store16) s fun t =>
      t.mem=(s.mem.writeW (off base (bits+2*j)) (FastNaf.wbyte k (2*j))).writeW
        (off base (bits+2*j+1)) (FastNaf.wbyte k (2*j+1)) ∧ KeepRegs [.x3] s t := by
  have hw0 : InRegions s.wr (s.gpr .x20+BitVec.ofNat 64 0) 1 := by
    rw [hp]; simp only [BitVec.add_zero]
    exact ⟨_,hs.wr,hs.contains (by omega) (by decide)⟩
  rw [Impl.Weierstrass.AArch64.FastNaf.store16,
    show ([.strb .x2 .x20 0,.lsr .x .x3 .x2 8,.strb .x3 .x20 1] : List Instr)=
      [.strb .x2 .x20 0]++([.lsr .x .x3 .x2 8]++[.strb .x3 .x20 1]) from rfl,WP.block_append_iff]
  refine WP.mono (strb_ok s (by decide) hw0) fun a ha => ?_
  subst a
  rw [WP.block_append_iff]
  refine WP.mono (lsr_ok _ (by decide)) fun b ⟨vb,kb⟩ => ?_
  have pb : b.gpr .x20=off base (bits+2*j) := (kb.gpr .x20 (by decide)).trans hp
  have hw1 : InRegions b.wr (b.gpr .x20+BitVec.ofNat 64 1) 1 := by
    rw [pb,off_add_one,kb.wr]
    exact ⟨_,hs.wr,hs.contains (by omega) (by decide)⟩
  refine WP.mono (strb_ok b (by decide) hw1) fun t ht => ?_
  subst t
  refine ⟨?_,⟨fun r hr => kb.gpr r hr,kb.rd,kb.wr,kb.sp⟩⟩
  simp only [pb,off_add_one,vb,kb.mem,hp,BitVec.add_zero,hd,fastLow9,fastHigh9]

theorem FastPrep9State.of_keeps {s t : State} {base : Addr} {size bits k j : Nat}
    (hI : FastPrep9State base size bits k j s) {rs : List Reg}
    (ht : Keeps rs s t) (hr : ∀ r∈rs,r∈[Reg.x1,.x2,.x3,.x19]) :
    FastPrep9State base size bits k j t := by
  have kt := ht.mono hr
  refine ⟨hI.scr.of_keeps kt (by decide),?_,(kt.gpr _ (by decide)).trans hI.mask,
    (kt.gpr _ (by decide)).trans hI.sign,(kt.gpr _ (by decide)).trans hI.zero,
    (kt.gpr _ (by decide)).trans hI.one,(kt.gpr _ (by decide)).trans hI.ptr,?_⟩
  · simp only [kt.gpr .x5 (by decide),kt.gpr .x6 (by decide),kt.gpr .x7 (by decide),
      kt.gpr .x8 (by decide),kt.gpr .x9 (by decide),hI.value]
  · rw [kt.mem]; exact hI.digits

theorem fastOdd9_ok {s : State} {base : Addr} {size bits k j : Nat}
    (hI : FastPrep9State base size bits k j s)
    (hb : bits+520≤size) (hj : j<257) (hv : FastNaf.residual 9 k j≤2^256)
    (ho : FastNaf.residual 9 k j%2≠0) :
    WP isa (.block Impl.Weierstrass.AArch64.FastNaf.odd9) s fun t =>
      FastPrep9State base size bits k (j+9) t ∧ KeepRegs fastStepClob s t ∧
      Outside base bits 520 s.mem t.mem := by
  rw [Impl.Weierstrass.AArch64.FastNaf.odd9]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (fastChoose9_ok s k j hI.mask hI.sign hI.value ho) fun a ⟨da,ka⟩ => ?_
  have sa := hI.scr.of_keeps ka (by decide)
  have pa := (ka.gpr .x20 (by decide)).trans hI.ptr
  rw [WP.block_append_iff]
  refine WP.mono (fastStore9_ok sa (by omega) pa da) fun b ⟨mb,kb⟩ => ?_
  have vb : nafVal5 (b.gpr .x5) (b.gpr .x6) (b.gpr .x7) (b.gpr .x8) (b.gpr .x9)=FastNaf.residual 9 k j := by
    simp only [kb.gpr .x5 (by decide),kb.gpr .x6 (by decide),kb.gpr .x7 (by decide),
      kb.gpr .x8 (by decide),kb.gpr .x9 (by decide),
      ka.gpr .x5 (by decide),ka.gpr .x6 (by decide),
      ka.gpr .x7 (by decide),ka.gpr .x8 (by decide),ka.gpr .x9 (by decide),hI.value]
  rw [WP.block_append_iff]
  refine WP.mono (fastSubtract_ok b 9 k j
    (by rw [kb.gpr _ (by decide),ka.gpr _ (by decide),hI.zero])
    (by rw [kb.gpr _ (by decide)]; exact da) vb hv) fun c ⟨vc,kc⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (fastShift_ok c 9 (Or.inr (Or.inr (Or.inr rfl)))) fun d ⟨vd,kd⟩ => ?_
  have pd : d.gpr .x20=off base (bits+2*j) := by
    rw [kd.gpr _ (by decide),kc.gpr _ (by decide),kb.gpr _ (by decide),pa]
  refine WP.mono (fastAdvance_ok d (j:=2*j) (d:=18) (by decide) pd) fun t ⟨pt,kt⟩ => ?_
  have keep := (fastKept ka (by decide)).trans ((kb.mono (by decide)).trans
    ((fastKept kc (by decide)).trans ((fastKept kd (by decide)).trans (fastKept kt (by decide)))))
  have mt : t.mem=(s.mem.writeW (off base (bits+2*j)) (FastNaf.wbyte k (2*j))).writeW
      (off base (bits+2*j+1)) (FastNaf.wbyte k (2*j+1)) := by
    rw [kt.mem,kd.mem,kc.mem,mb,ka.mem]
  have hnw := hI.scr.nowrap
  have O0 := writeW8_outside s.mem base (FastNaf.wbyte k (2*j)) (d:=bits+2*j) (by omega)
  have O1 := writeW8_outside (s.mem.writeW (off base (bits+2*j)) (FastNaf.wbyte k (2*j))) base
    (FastNaf.wbyte k (2*j+1)) (d:=bits+2*j+1) (by omega)
  have hoff : ∀ i, i<520 → ofs base (off base (bits+i))=bits+i := fun i hi => ofs_off0 base (by omega)
  refine ⟨⟨hI.scr.of_keepRegs keep (by decide),?_,(keep.gpr _ (by decide)).trans hI.mask,
    (keep.gpr _ (by decide)).trans hI.sign,(keep.gpr _ (by decide)).trans hI.zero,
    (keep.gpr _ (by decide)).trans hI.one,?_,?_⟩,keep,?_⟩
  · simp only [kt.gpr .x5 (by decide),kt.gpr .x6 (by decide),kt.gpr .x7 (by decide),
      kt.gpr .x8 (by decide),kt.gpr .x9 (by decide),vd,vc]
    rw [FastNaf.residual_succ,FastNaf.next_odd9 _ ho,FastNaf.residual_skip9 k j ho]
    omega
  · rw [pt]; congr 2 <;> omega
  · intro i hi
    rw [mt]
    by_cases h1 : i=2*j+1
    · subst i
      rw [show bits+(2*j+1)=bits+2*j+1 by omega,writeW8_self,ite_eq_left (by omega)]
    · rw [O1 _ (by rw [hoff i (by omega)]; omega)]
      by_cases h0 : i=2*j
      · subst i
        rw [writeW8_self,ite_eq_left (by omega)]
      · rw [O0 _ (by rw [hoff i (by omega)]; omega),hI.digits i hi]
        by_cases hlt : i/2<j
        · simp only [hlt,ite_true,show i/2<j+9 from by omega]
        · by_cases hil : i/2<j+9
          · simp only [hlt,hil,ite_false,ite_true]
            exact (FastNaf.wbyte_of_zero (by
              have h := FastNaf.magnitude_skip_zero9 k j (i/2-j) ho (by omega) (by omega)
              rwa [Nat.add_sub_of_le (by omega)] at h)).symm
          · simp only [hlt,hil,ite_false]
  · rw [mt]
    exact (O0.mono (by omega) (by omega)).trans (O1.mono (by omega) (by omega))

theorem fastEven9_ok {s : State} {base : Addr} {size bits k j : Nat}
    (hI : FastPrep9State base size bits k j s) (he : FastNaf.residual 9 k j%2=0) :
    WP isa (.block Impl.Weierstrass.AArch64.FastNaf.even9) s fun t =>
      FastPrep9State base size bits k (j+1) t ∧ KeepRegs fastStepClob s t ∧
      Outside base bits 520 s.mem t.mem := by
  rw [Impl.Weierstrass.AArch64.FastNaf.even9,WP.block_append_iff]
  refine WP.mono (fastShift_ok s 1 (Or.inl rfl)) fun a ⟨va,ka⟩ => ?_
  have pa := (ka.gpr .x20 (by decide)).trans hI.ptr
  refine WP.mono (fastAdvance_ok a (j:=2*j) (d:=2) (by decide) pa) fun t ⟨pt,kt⟩ => ?_
  have keep := (fastKept ka (by decide)).trans (fastKept kt (by decide))
  have mt : t.mem=s.mem := kt.mem.trans ka.mem
  refine ⟨⟨hI.scr.of_keepRegs keep (by decide),?_,(keep.gpr _ (by decide)).trans hI.mask,
    (keep.gpr _ (by decide)).trans hI.sign,(keep.gpr _ (by decide)).trans hI.zero,
    (keep.gpr _ (by decide)).trans hI.one,?_,?_⟩,keep,?_⟩
  · simp only [kt.gpr .x5 (by decide),kt.gpr .x6 (by decide),kt.gpr .x7 (by decide),
      kt.gpr .x8 (by decide),kt.gpr .x9 (by decide),va,hI.value]
    rw [FastNaf.residual_succ,FastNaf.next_even _ _ he]
  · rw [pt]; congr 2 <;> omega
  · intro i hi
    rw [mt,hI.digits i hi]
    by_cases hij : i/2=j
    · simp only [hij,Nat.lt_irrefl,ite_false,Nat.lt_add_one,ite_true]
      exact (FastNaf.wbyte_of_zero (by rw [hij]; exact (FastNaf.magnitude_zero_iff 9 k j).mpr he)).symm
    · have hh : (i/2<j)=(i/2<j+1) := propext (by omega)
      simp only [hh]
  · rw [mt]; exact Outside.refl _ _ _ _

def fastNext9 (k j : Nat) : Nat := j+if FastNaf.residual 9 k j%2=0 then 1 else 9

theorem fastStep9_ok {s : State} {base : Addr} {size bits k j : Nat}
    (hI : FastPrep9State base size bits k j s)
    (hb : bits+520≤size) (hj : j<257) (hv : FastNaf.residual 9 k j≤2^256) :
    WP isa Impl.Weierstrass.AArch64.FastNaf.step9 s fun t =>
      FastPrep9State base size bits k (fastNext9 k j) t ∧
      KeepRegs fastStepClob s t ∧ Outside base bits 520 s.mem t.mem ∧
      (t.gpr .x19=0 ↔ FastNaf.residual 9 k (fastNext9 k j)=0) := by
  rw [Impl.Weierstrass.AArch64.FastNaf.step9]
  refine WP.seq (WP.mono (fastTest_ok s hI.one) fun a ⟨ea,ka⟩ => ?_)
  have ia := hI.of_keeps ka (by decide)
  have eb : a.gpr .x1=0 ↔ FastNaf.residual 9 k j%2=0 := by rw [ea]; exact fastLow_even hI.value
  have branches : WP isa (.ite (.nonzero .x .x1) (.block Impl.Weierstrass.AArch64.FastNaf.odd9)
      (.block Impl.Weierstrass.AArch64.FastNaf.even9)) a fun b =>
      FastPrep9State base size bits k (fastNext9 k j) b ∧ KeepRegs fastStepClob a b ∧
      Outside base bits 520 a.mem b.mem := by
    by_cases he : FastNaf.residual 9 k j%2=0
    · refine WP.ite false ?_ (by intro h; cases h) (fun _ => ?_)
      · simp only [eval,read_x,Size.bits,show a.gpr .x1=0 from eb.mpr he]
        rfl
      · simpa only [fastNext9,he,ite_true] using fastEven9_ok ia he
    · refine WP.ite true ?_ (fun _ => ?_) (by intro h; cases h)
      · simp only [eval,read_x,Size.bits,Option.some.injEq,bne_iff_ne]
        exact fun h => he (eb.mp h)
      · simpa only [fastNext9,he,ite_false] using fastOdd9_ok ia hb hj hv he
  refine WP.seq (WP.mono branches fun b ⟨ib,kb,ob⟩ => ?_)
  refine WP.mono (fastRemain_ok b) fun t ⟨et,kt⟩ => ?_
  refine ⟨ib.of_keeps kt (by decide),
    (fastKept ka (by decide)).trans (kb.trans (fastKept kt (by decide))),?_,?_⟩
  · rw [kt.mem,←ka.mem]; exact ob
  · rw [et,ib.value]

/-- After the recoder: every digit's two bytes. -/
structure FastPrep9Post (base : Addr) (size bits k : Nat) (s : State) : Prop where
  scr : Scr s base size
  digits : ∀ i<514,s.mem (off base (bits+i))=FastNaf.wbyte k i

theorem fastPrep9Post_of_zero {s : State} {base : Addr} {size bits k j : Nat}
    (hI : FastPrep9State base size bits k j s) (hz : FastNaf.residual 9 k j=0) :
    FastPrep9Post base size bits k s := by
  refine ⟨hI.scr,?_⟩
  intro i hi
  rw [hI.digits i hi]
  split
  · rfl
  · have hv := FastNaf.residual_of_zero 9 k j hz (i/2-j)
    rw [show j+(i/2-j)=i/2 from by omega] at hv
    exact (FastNaf.wbyte_of_zero ((FastNaf.magnitude_zero_iff 9 k (i/2)).mpr (by rw [hv]))).symm

theorem fastLoop9_ok {s : State} {base : Addr} {size bits k j : Nat}
    (hI : FastPrep9State base size bits k j s)
    (hk : k<2^256) (hb : bits+520≤size) (hj : j<257) :
    WP isa (.loop Impl.Weierstrass.AArch64.FastNaf.step9 (.nonzero .x .x19)) s fun t =>
      FastPrep9Post base size bits k t ∧ KeepRegs fastStepClob s t ∧ Outside base bits 520 s.mem t.mem := by
  let I (n : Nat) (t : State) := ∃ i, i<257 ∧ n=257-i ∧ FastPrep9State base size bits k i t ∧
    KeepRegs fastStepClob s t ∧ Outside base bits 520 s.mem t.mem
  apply WP.loop I (n:=257-j)
  · intro n a ⟨i,hi,hn,ia,ka,oa⟩
    have hv : FastNaf.residual 9 k i≤2^256 :=
      Nat.le_trans (FastNaf.residual_boundB 9 (Nat.le_of_lt hk) (j:=i) (by omega))
        (Nat.pow_le_pow_right (by decide) (by omega))
    refine WP.mono (fastStep9_ok ia hb hi hv) fun t ⟨it,kt,ot,et⟩ => ?_
    by_cases hz : FastNaf.residual 9 k (fastNext9 k i)=0
    · refine Or.inl ⟨?_,fastPrep9Post_of_zero it hz,ka.trans kt,oa.trans ot⟩
      simp only [eval,read_x,Size.bits,et.mpr hz]
      rfl
    · have hj' : fastNext9 k i<257 := by
        by_contra h
        exact hz (FastNaf.residual_zero_ge hk (by omega))
      refine Or.inr ⟨?_,257-fastNext9 k i,?_,fastNext9 k i,hj',rfl,it,ka.trans kt,oa.trans ot⟩
      · simp only [eval,read_x,Size.bits,Option.some.injEq,bne_iff_ne]
        exact fun h => hz (et.mp h)
      · have : i<fastNext9 k i := by unfold fastNext9; split <;> omega
        omega
  · exact ⟨j,hj,rfl,hI,⟨fun _ _ => rfl,rfl,rfl,rfl⟩,Outside.refl _ _ _ _⟩

theorem fastClear9_ok (K : WinCfg) {s : State} {base : Addr} {size : Nat}
    (hs : Scr s base size) (hz : s.gpr .x12=0) (ha : K.bits%8=0) (hb : K.bits+520≤size) :
    WP isa (.block (Impl.Weierstrass.AArch64.FastNaf.clear9 K)) s fun t =>
      (∀ i<520,t.mem (off base (K.bits+i))=0) ∧ KeepRegs [] s t ∧ Outside base K.bits 520 s.mem t.mem := by
  refine WP.mono (zerosW_ok hs hz ha 65 hb) fun t ⟨ht,kt,ot⟩ => ⟨?_,kt,ot⟩
  intro i hi
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  rw [testBit_byte t.mem base (n:=65) (by omega) hb,ht]
  simp only [BitVec.ofNat_eq_ofNat,Nat.zero_testBit,BitVec.getLsbD_zero]

theorem fastSetup9_ok (K : WinCfg) {s : State} {base : Addr} {size src : Nat}
    (hs : Scr s base size) (hsrc : src+32≤size) (hsrc8 : src%8=0)
    (hbits : K.bits<4096) (hbits8 : K.bits%8=0) (hb : K.bits+520≤size) :
    WP isa (.block (Impl.Weierstrass.AArch64.FastNaf.init K src 9 ++
      Impl.Weierstrass.AArch64.FastNaf.clear9 K)) s fun t =>
      FastPrep9State base size K.bits (wordsVal s.mem base src 4) 0 t ∧
      KeepRegs nafPrepClob s t ∧ Outside base K.bits 520 s.mem t.mem := by
  rw [WP.block_append_iff]
  refine WP.mono (fastInit_ok K (w:=9) (Or.inr (Or.inr rfl)) hs hsrc hsrc8 hbits) fun a ⟨ia,ka,ma⟩ => ?_
  refine WP.mono (fastClear9_ok K ia.scr ia.zero hbits8 hb) fun t ⟨zt,kt,ot⟩ => ?_
  refine ⟨⟨ia.scr.of_keepRegs kt (by decide),?_,(kt.gpr _ List.not_mem_nil).trans ia.mask,
    (kt.gpr _ List.not_mem_nil).trans ia.sign,(kt.gpr _ List.not_mem_nil).trans ia.zero,
    (kt.gpr _ List.not_mem_nil).trans ia.one,?_,?_⟩,ka.trans (kt.mono (by simp)),?_⟩
  · simp only [kt.gpr _ List.not_mem_nil,ia.value]
  · simpa only [Nat.mul_zero,Nat.add_zero] using (kt.gpr _ List.not_mem_nil).trans ia.ptr
  · intro i hi
    simpa only [Nat.not_lt_zero,ite_false] using zt i (by omega)
  · rw [←ma]; exact ot

/-- The width-nine digits of the scalar at `src`, two bytes each at `K.bits`, touching only
their 520-byte buffer. -/
theorem fastPrep9_ok (K : WinCfg) {s : State} {base : Addr} {size src : Nat}
    (hs : Scr s base size) (hsrc : src+32≤size) (hsrc8 : src%8=0)
    (hbits : K.bits<4096) (hbits8 : K.bits%8=0) (hb : K.bits+520≤size) :
    WP isa (Impl.Weierstrass.AArch64.FastNaf.prep9 K src) s fun t =>
      FastPrep9Post base size K.bits (wordsVal s.mem base src 4) t ∧
      KeepRegs nafPrepClob s t ∧ Outside base K.bits 520 s.mem t.mem := by
  rw [Impl.Weierstrass.AArch64.FastNaf.prep9]
  refine WP.seq (WP.mono (fastSetup9_ok K hs hsrc hsrc8 hbits hbits8 hb) fun a ⟨ia,ka,oa⟩ => ?_)
  refine WP.mono (fastLoop9_ok ia (wordsVal_lt ..) hb (by decide)) fun t ⟨it,kt,ot⟩ => ?_
  exact ⟨it,ka.trans (kt.mono (by decide)),oa.trans ot⟩

end VG.Proof.Weierstrass.AArch64
