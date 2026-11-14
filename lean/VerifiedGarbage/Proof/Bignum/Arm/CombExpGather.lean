module

public import VerifiedGarbage.Proof.Bignum.Arm.CombExpState
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomery
public import VerifiedGarbage.Proof.Rsa.FixedBaseComb
public import VerifiedGarbage.Impl.Bignum.Arm.CombExp
public import VerifiedGarbage.Proof.Bignum.Arm.CombDigitLoad
import VerifiedGarbage.Proof.Bignum.Arm.CombExpArgs
import VerifiedGarbage.Proof.Bignum.Arm.CombExpKernel
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Impl.Bignum.Arm.CombDigit
import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.TCB.Arm.Isa
import VerifiedGarbage.Proof.Ffdh.CombBitBytes

/-! ### `Bignum.Arm.CombDigitBit`, which only this module used -/

section

/-! A guarded public-position read returns exactly one exponent bit. -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CombDigitGuard.lean`, which only this module imported.
section

/-! The bounded public index comparison needs only the existing Z condition. -/

section
namespace VG.Proof.Bignum.Arm.CombDigit
open VG VG.Arm VG.Proof.X25519.Arm

theorem guard_value {k N : Nat} (hk : k < 2^31) (hn : N < 2^31) :
    (BitVec.ofNat 32 k - BitVec.ofNat 32 N) >>> 31 = if k<N then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : k < 2^32), Nat.mod_eq_of_lt (by omega : N < 2^32)]
  simp only [Nat.shiftRight_eq_div_pow]
  split
  · rw [show (1 : BitVec 32).toNat = 1 by decide]
    omega
  · rw [show (0 : BitVec 32).toNat = 0 by decide]
    omega

theorem guard_ok (s : State) {k N : Nat} (hk : k < 2^31) (hn : N < 2^31)
    (index : s.gpr .r9 = BitVec.ofNat 32 k) (width : s.gpr .r8 = BitVec.ofNat 32 N) :
    WP isa (.block [.dp .sub .r12 .r9 (.reg .r8), .mov .r12 (.shifted .r12 .lsr 31),
      .cmp .r12 (.imm 0)]) s fun t =>
      t.z = !decide (k<N) ∧ t.mem = s.mem ∧ Rest [.r12] s t := by
  refine wp_dp (op2_reg _ _) fun u one => ?_
  refine wp_mov (by rfl) fun v two => ?_
  refine wp_cmp (op2_imm (by decide)) fun t three zero => WP.block_nil ?_
  have value : v.gpr .r12 = if k<N then 1 else 0 := by
    rw [two.gpr,one.gpr]
    change (s.gpr .r9 - s.gpr .r8) >>> 31 = _
    rw [index,width,guard_value hk hn]
  refine ⟨?_,three.mem.trans (two.mem.trans one.mem),
    ((one.rest (by simp)).trans (two.rest (by simp))).trans (three.rest _)⟩
  rw [zero,value]
  by_cases h : k<N
  · simp only [ite_eq_left h,decide_eq_true h]
    rfl
  · simp only [ite_eq_right h,decide_eq_false h]
    rfl

end VG.Proof.Bignum.Arm.CombDigit
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CombDigitShift.lean`, which only this module imported.
section

/-! Public-count shifts use only modeled immediate shift instructions. -/

section
namespace VG.Proof.Bignum.Arm.CombDigit
open VG VG.Arm VG.Proof.X25519.Arm

private theorem step_ok (s : State) {k : Nat} (positive : 0 < k) (fit : k < 2^32)
    (count : s.gpr .r2 = BitVec.ofNat 32 k) :
    WP isa (.block [.mov .r11 (.shifted .r11 .lsr 1), .subs .r2 .r2 (.imm 1)]) s fun t =>
      t.gpr .r11 = s.gpr .r11 >>> 1 ∧ t.gpr .r2 = BitVec.ofNat 32 (k-1) ∧
      t.z = decide (k=1) ∧ t.mem = s.mem ∧ Rest [.r2,.r11] s t := by
  refine wp_mov (by rfl) fun u one => ?_
  refine wp_subs (op2_imm (by decide)) fun t two zero => WP.block_nil ?_
  have mid : u.gpr .r2 = BitVec.ofNat 32 k := (one.other .r2 (by decide)).trans count
  have sub : u.gpr .r2 - 1 = BitVec.ofNat 32 (k-1) := by
    rw [mid]
    change BitVec.ofNat 32 k - BitVec.ofNat 32 1 = BitVec.ofNat 32 (k-1)
    exact BitVec.ofNat_sub_ofNat_of_le k 1 (by decide) (by omega)
  refine ⟨(two.other .r11 (by decide)).trans one.gpr, two.gpr.trans sub, ?_,
    two.mem.trans one.mem, (one.rest (by simp)).trans (two.rest (by simp))⟩
  rw [zero,sub,ofNat_beq_zero (by omega)]
  exact decide_eq_decide.mpr (by omega)

theorem shift_ok (s : State) {n : Nat} (positive : 0 < n) (fit : n < 2^32)
    (count : s.gpr .r2 = BitVec.ofNat 32 n) :
    WP isa VG.Impl.Bignum.Arm.CombDigit.shift s fun t =>
      t.gpr .r11 = s.gpr .r11 >>> n ∧ t.gpr .r2 = 0 ∧ t.mem = s.mem ∧ Rest [.r2,.r11] s t := by
  let I := fun k t => 0 < k ∧ k ≤ n ∧ t.gpr .r2 = BitVec.ofNat 32 k ∧
    t.gpr .r11 = s.gpr .r11 >>> (n-k) ∧ t.mem = s.mem ∧ Rest [.r2,.r11] s t
  unfold VG.Impl.Bignum.Arm.CombDigit.shift
  refine WP.loop (M := isa) I ?_ n s ⟨positive,by omega,count,by simp,rfl,Rest.refl _ _⟩
  intro k t h
  obtain ⟨positiveK,leK,countK,word,mem,rest⟩ := h
  refine WP.mono (step_ok t positiveK (by omega) countK) ?_
  rintro u ⟨wordU,countU,zeroU,memU,restU⟩
  have next : u.gpr .r11 = s.gpr .r11 >>> (n-(k-1)) := by
    rw [wordU,word,←BitVec.shiftRight_add]
    congr 1
    omega
  by_cases last : k=1
  · left
    refine ⟨?_, ?_, ?_, memU.trans mem, rest.trans restU⟩
    · change some (!u.z) = some false
      simp only [zeroU,last,decide_true,Bool.not_true]
    · simpa only [last,Nat.sub_self,Nat.sub_zero] using next
    · change u.gpr .r2 = BitVec.ofNat 32 0
      simpa only [last,Nat.sub_self] using countU
  · right
    refine ⟨?_, k-1,by omega,by omega,by omega,countU,next,memU.trans mem,rest.trans restU⟩
    change some (!u.z) = some true
    simp only [zeroU,decide_eq_false last,Bool.not_false]

end VG.Proof.Bignum.Arm.CombDigit
end

end

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombDigit
open VG VG.Arm VG.Proof.X25519.Arm

abbrev bitClobbers : List Reg := [.r2,.r11,.r12]

theorem Source.of_mem {src : BitVec 32} {bs : List Byte} {s t : State} {rs : List Reg}
    (h : Source src bs s) (mem : t.mem=s.mem) (rest : Rest rs s t) : Source src bs t := by
  refine ⟨h.fits,?_,?_⟩
  · rw [rest.rd,rest.wr]; exact h.readable
  · intro j hj; rw [mem]; exact h.bytes j hj

private theorem shiftedBit (b : Byte) (r : Nat) :
    (b.setWidth 32 >>> r) &&& 1 = BitVec.ofNat 32 (b.toNat / 2^r % 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and,BitVec.toNat_ushiftRight,BitVec.toNat_setWidth,BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by have := b.isLt; omega_using [] : b.toNat < 2^32)]
  change (b.toNat >>> r) &&& 1 = (b.toNat / 2^r % 2)%2^32
  rw [Nat.and_one_is_mod,Nat.shiftRight_eq_div_pow]
  exact (Nat.mod_eq_of_lt (by omega_using [] : b.toNat / 2^r % 2 < 2^32)).symm

private theorem optionalShift_ok (s : State) {r : Nat} (bound : r<8)
    (count : s.gpr .r2=BitVec.ofNat 32 r) (zero : s.z=decide (r=0)) :
    WP isa (.ite .ne VG.Impl.Bignum.Arm.CombDigit.shift (.block [])) s fun t =>
      t.gpr .r11=s.gpr .r11>>>r ∧ t.mem=s.mem ∧ Rest [.r2,.r11] s t := by
  by_cases h : r=0
  · subst r
    have run : Exec isa (.ite .ne VG.Impl.Bignum.Arm.CombDigit.shift (.block [])) s
        [.branch false] s := .iteF (by change some (!s.z)=_; simp [zero]) (.block rfl)
    exact ⟨_,s,run,by simp,rfl,Rest.refl _ _⟩
  · obtain ⟨tr,t,run,word,_,mem,rest⟩ := shift_ok s (by omega_using [h]) (by omega_using [bound]) count
    exact ⟨_,t,.iteT (by change some (!s.z)=_; simp [zero,h]) run,word,mem,rest⟩

/-- The bit is zero when its public index is outside the declared width. -/
theorem bit_ok (s : State) {src : BitVec 32} {bs : List Byte} {k N : Nat}
    (source : Source src bs s) (widthBound : N≤8*bs.length) (size : bs.length<2^32)
    (indexFit : k<2^31) (widthFit : N<2^31)
    (ptr : s.gpr .r4=src) (length : s.gpr .r5=BitVec.ofNat 32 bs.length)
    (index : s.gpr .r9=BitVec.ofNat 32 k) (width : s.gpr .r8=BitVec.ofNat 32 N) :
    WP isa VG.Impl.Bignum.Arm.CombDigit.bit s fun t =>
      t.gpr .r11=BitVec.ofNat 32 (if h:k<N then
        (bs[bs.length-1-k/8]'(by omega_using [widthBound, h])).toNat / 2^(k%8) % 2 else 0) ∧
      t.mem=s.mem ∧ Rest bitClobbers s t := by
  unfold VG.Impl.Bignum.Arm.CombDigit.bit
  rw [WP.seq_iff]
  refine WP.mono (guard_ok s indexFit widthFit index width) ?_
  rintro u ⟨zero,memU,restU⟩
  by_cases inside : k<N
  · have condition : isa.eval .ne u=some true := by change some (!u.z)=_; simp [zero,inside]
    apply WP.ite true condition
    · intro _
      rw [WP.seq_iff]
      refine WP.mono (load_ok u (source.of_mem memU restU) (by omega_using [widthBound, inside]) size
        ((restU.gpr .r4 (by decide)).trans ptr) ((restU.gpr .r5 (by decide)).trans length)
        ((restU.gpr .r9 (by decide)).trans index) (by omega_using [indexFit])) ?_
      rintro v ⟨byte,count,zeroV,memV,restV⟩
      rw [WP.seq_iff]
      refine WP.mono (optionalShift_ok v (by omega_using []) count zeroV) ?_
      rintro z ⟨shifted,memZ,restZ⟩
      refine wp_dp (op2_imm (by decide)) fun t last => WP.block_nil ?_
      refine ⟨?_,last.mem.trans (memZ.trans (memV.trans memU)),?_⟩
      · rw [last.gpr]
        change z.gpr .r11 &&& 1 = _
        rw [shifted,byte,shiftedBit]
        simp only [dite_eq_left inside]
      · exact (((restU.mono (by decide)).trans restV).trans
          (restZ.mono (by decide))).trans (last.rest (by decide))
    · intro impossible; cases impossible
  · have condition : isa.eval .ne u=some false := by change some (!u.z)=_; simp [zero,inside]
    apply WP.ite false condition
    · intro impossible; cases impossible
    · intro _
      refine wp_mov (op2_imm (by decide)) fun t last => WP.block_nil ?_
      refine ⟨?_,last.mem.trans memU,(restU.mono (by decide)).trans (last.rest (by decide))⟩
      rw [last.gpr]
      simp only [dite_eq_right inside]
      rfl

end VG.Proof.Bignum.Arm.CombDigit

end

end

/-! The evaluator's public header produces exactly the mathematical comb digit. -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CombDigitTooth.lean`, which only this module imported.
section

/-! One tooth appends one bit at its fixed place in the comb digit. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombDigit
open VG VG.Arm VG.Proof.X25519.Arm

abbrev clobbers : List Reg := [.r2,.r9,.r10,.r11,.r12]

def value (bs : List Byte) (N k : Nat) : Nat :=
  if k<N then ((bs.getD (bs.length-1-k/8) 0).toNat / 2^(k%8)) % 2 else 0

theorem value_lt (bs : List Byte) (N k : Nat) : value bs N k < 2 := by
  unfold value
  split
  · exact Nat.mod_lt _ (by decide)
  · omega_using []

private theorem appendBit {a b j : Nat} (ha : a<2^j) (hb : b<2) (hj : j<5) :
    BitVec.ofNat 32 a ||| (BitVec.ofNat 32 b <<< j) = BitVec.ofNat 32 (a+2^j*b) := by
  have pow : 2^j≤16 := Nat.pow_le_pow_right (by decide) (by omega_using [hj] : j≤4)
  have product : 2^j*b≤16 := calc
    2^j*b ≤ 2^j*1 := Nat.mul_le_mul_left _ (by omega_using [hb])
    _ ≤ 16 := by simpa only [Nat.mul_one] using pow
  have aa : a<2^32 := by omega_using [ha, pow]
  have sum : a+2^j*b<2^32 := by omega_using [ha, pow, product]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or,BitVec.toNat_shiftLeft,BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt aa,Nat.mod_eq_of_lt (by omega_using [hb] : b<2^32)]
  have shift : b<<<j<2^32 := by rw [Nat.shiftLeft_eq,Nat.mul_comm]; omega_using [product]
  rw [Nat.mod_eq_of_lt shift,Nat.mod_eq_of_lt sum]
  rw [Nat.or_comm,←Nat.shiftLeft_add_eq_or_of_lt ha,Nat.shiftLeft_eq]
  rw [Nat.mul_comm b (2^j),Nat.add_comm]

theorem tooth_ok (s : State) {src : BitVec 32} {bs : List Byte} {k N d a j : Nat}
    (source : Source src bs s) (widthBound : N≤8*bs.length) (size : bs.length<2^32)
    (indexFit : k<2^31) (widthFit : N<2^31) (_nextFit : k+d<2^32)
    (digitBound : a<2^j) (tooth : j<5)
    (ptr : s.gpr .r4=src) (length : s.gpr .r5=BitVec.ofNat 32 bs.length)
    (index : s.gpr .r9=BitVec.ofNat 32 k) (width : s.gpr .r8=BitVec.ofNat 32 N)
    (stride : s.gpr .r7=BitVec.ofNat 32 d) (digit : s.gpr .r10=BitVec.ofNat 32 a) :
    WP isa (VG.Impl.Bignum.Arm.CombDigit.tooth j) s fun t =>
      t.gpr .r9=BitVec.ofNat 32 (k+d) ∧
      t.gpr .r10=BitVec.ofNat 32 (a+2^j*value bs N k) ∧
      t.mem=s.mem ∧ Rest clobbers s t := by
  unfold VG.Impl.Bignum.Arm.CombDigit.tooth
  rw [WP.seq_iff]
  refine WP.mono (bit_ok s source widthBound size indexFit widthFit ptr length index width) ?_
  rintro u ⟨bit,memU,restU⟩
  have result : u.gpr .r11=BitVec.ofNat 32 (value bs N k) := by
    rw [bit]
    congr 1
    unfold value
    split
    · rw [←List.getElem_eq_getD 0]
    · rfl
  have old : u.gpr .r10=BitVec.ofNat 32 a := (restU.gpr .r10 (by decide)).trans digit
  have operand : (if j=0 then Op2.reg .r11 else .shifted .r11 .lsl j).eval u =
      some (u.gpr .r11<<<j) := by
    by_cases h : j=0
    · subst j; simp [Op2.eval]
    · simp only [ite_eq_right h,Op2.eval]
      rw [ite_eq_left (by omega_using [tooth, h] : 1≤j ∧ j≤31)]
  refine wp_dp operand fun v one => ?_
  refine wp_dp (op2_reg _ _) fun t two => WP.block_nil ?_
  refine ⟨?_,?_,two.mem.trans (one.mem.trans memU),?_⟩
  · rw [two.gpr]
    change v.gpr .r9+v.gpr .r7=_
    rw [one.other .r9 (by decide),one.other .r7 (by decide),restU.gpr .r9 (by decide),
      restU.gpr .r7 (by decide),index,stride,←BitVec.ofNat_add]
  · rw [two.other .r10 (by decide),one.gpr]
    change u.gpr .r10 ||| (u.gpr .r11<<<j)=_
    rw [old,result,appendBit digitBound (value_lt _ _ _) tooth]
  · exact ((restU.mono (by decide)).trans (one.rest (by decide))).trans
      (two.rest (by decide))

end VG.Proof.Bignum.Arm.CombDigit
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CombDigit.lean`, which only this module imported.
section

/-! Five statically fixed teeth produce the complete secret digit. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombDigit
open VG VG.Arm VG.Proof.X25519.Arm

def prefixValue (bs : List Byte) (N i d : Nat) : Nat → Nat
  | 0 => 0
  | j+1 => prefixValue bs N i d j + 2^j*value bs N (i+j*d)

theorem prefixValue_lt (bs : List Byte) (N i d j : Nat) : prefixValue bs N i d j<2^j := by
  induction j with
  | zero => simp [prefixValue]
  | succ j ih =>
    have bit := value_lt bs N (i+j*d)
    have product : 2^j*value bs N (i+j*d) ≤ 2^j := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2^j) (show value bs N (i+j*d)≤1 by omega_using [bit])
    simp only [prefixValue,Nat.pow_succ]
    omega_using [ih, product]

private structure GatherInv (s0 : State) (bs : List Byte) (N i d j : Nat) (s : State) : Prop where
  index : s.gpr .r9=BitVec.ofNat 32 (i+j*d)
  digit : s.gpr .r10=BitVec.ofNat 32 (prefixValue bs N i d j)
  mem : s.mem=s0.mem
  rest : Rest clobbers s0 s

/-- Raw byte semantics; the public-width bridge identifies this with the comb digit. -/
theorem code_ok (s : State) {src : BitVec 32} {bs : List Byte} {N i d : Nat}
    (source : Source src bs s) (widthBound : N≤8*bs.length) (size : bs.length<2^32)
    (positions : i+5*d<2^31) (widthFit : N<2^31)
    (ptr : s.gpr .r4=src) (length : s.gpr .r5=BitVec.ofNat 32 bs.length)
    (row : s.gpr .r6=BitVec.ofNat 32 i) (stride : s.gpr .r7=BitVec.ofNat 32 d)
    (width : s.gpr .r8=BitVec.ofNat 32 N) :
    WP isa VG.Impl.Bignum.Arm.CombDigit.code s fun t =>
      t.gpr .r11=BitVec.ofNat 32 (prefixValue bs N i d 5) ∧
      (t.gpr .r11).toNat<32 ∧ t.mem=s.mem ∧ Rest clobbers s t := by
  have step (j : Nat) (hj : j<5) (t : State) (h : GatherInv s bs N i d j t) :
      WP isa (VG.Impl.Bignum.Arm.CombDigit.tooth j) t (GatherInv s bs N i d (j+1)) := by
    have posBound : j*d≤5*d := Nat.mul_le_mul_right d (by omega_using [hj])
    have nextBound : (j+1)*d≤5*d := Nat.mul_le_mul_right d (by omega_using [hj])
    refine WP.mono (tooth_ok t (source.of_mem h.mem h.rest) widthBound size
      (by omega_using [positions, posBound]) widthFit (by omega_using [positions, posBound]) (prefixValue_lt bs N i d j) hj
      ((h.rest.gpr .r4 (by decide)).trans ptr)
      ((h.rest.gpr .r5 (by decide)).trans length)
      h.index ((h.rest.gpr .r8 (by decide)).trans width)
      ((h.rest.gpr .r7 (by decide)).trans stride) h.digit) ?_
    rintro u ⟨index,digit,mem,rest⟩
    refine ⟨?_,digit,mem.trans h.mem,h.rest.trans rest⟩
    simpa only [Nat.add_mul,Nat.one_mul,Nat.add_assoc] using index
  unfold VG.Impl.Bignum.Arm.CombDigit.code
  rw [WP.seq_iff]
  refine wp_mov (op2_reg _ _) fun a one => ?_
  refine wp_mov (op2_imm (by decide)) fun b two => WP.block_nil ?_
  have init : GatherInv s bs N i d 0 b := by
    refine ⟨?_,?_,two.mem.trans one.mem,(one.rest (by decide)).trans (two.rest (by decide))⟩
    · simpa only [Nat.zero_mul,Nat.add_zero] using (two.other .r9 (by decide)).trans (one.gpr.trans row)
    · exact two.gpr
  rw [WP.seq_iff]
  refine WP.mono (step 0 (by decide) b init) ?_
  intro s1 h1
  rw [WP.seq_iff]
  refine WP.mono (step 1 (by decide) s1 h1) ?_
  intro s2 h2
  rw [WP.seq_iff]
  refine WP.mono (step 2 (by decide) s2 h2) ?_
  intro s3 h3
  rw [WP.seq_iff]
  refine WP.mono (step 3 (by decide) s3 h3) ?_
  intro s4 h4
  rw [WP.seq_iff]
  refine WP.mono (step 4 (by decide) s4 h4) ?_
  intro s5 h5
  refine wp_mov (op2_reg _ _) fun t last => WP.block_nil ?_
  have result : t.gpr .r11=BitVec.ofNat 32 (prefixValue bs N i d 5) := last.gpr.trans h5.digit
  have bounded : prefixValue bs N i d 5<32 := prefixValue_lt bs N i d 5
  refine ⟨result,?_,last.mem.trans h5.mem,h5.rest.trans (last.rest (by decide))⟩
  rw [result,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega_using [bounded])]
  exact bounded

end VG.Proof.Bignum.Arm.CombDigit
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CombDigitValue.lean`, which only this module imported.
section

/-! The gathered five-byte bits are the reviewed comb's exponent columns. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombDigit
open VG VG.Arm

theorem value_eq_bit (bs : List Byte) (N k : Nat) (size : N≤8*bs.length)
    (bound : Spec.Rsa.os2ip bs<2^N) :
    value bs N k=VG.Proof.Rsa.FixedBaseComb.bit (Spec.Rsa.os2ip bs) k := by
  unfold value VG.Proof.Rsa.FixedBaseComb.bit
  by_cases inside : k<N
  · rw [ite_eq_left inside]
    rw [←List.getElem_eq_getD 0]
    exact (VG.Proof.Ffdh.CombBitBytes.os2ip_bit bs k (by omega_using [size, inside])).symm
  · rw [ite_eq_right inside]
    have limit : Spec.Rsa.os2ip bs<2^k :=
      Nat.lt_of_lt_of_le bound (Nat.pow_le_pow_right (by decide) (by omega_using [inside]))
    rw [Nat.div_eq_of_lt limit]

theorem prefixValue_eq_digit (bs : List Byte) (N i : Nat) (size : N≤8*bs.length)
    (bound : Spec.Rsa.os2ip bs<2^N) :
    prefixValue bs N i (Spec.Rsa.FixedBaseComb.rows N) 5=
      VG.Proof.Rsa.FixedBaseComb.digit N (Spec.Rsa.os2ip bs) i := by
  simp only [prefixValue,value_eq_bit bs N _ size bound,VG.Proof.Rsa.FixedBaseComb.digit,
    Nat.pow_zero,Nat.pow_one,show 2^2=4 from rfl,show 2^3=8 from rfl,show 2^4=16 from rfl,
    Nat.zero_mul,Nat.add_zero,Nat.one_mul,Nat.zero_add]

theorem code_digit_ok (s : State) {src : BitVec 32} {bs : List Byte} {N i : Nat}
    (source : Source src bs s) (widthBound : N≤8*bs.length) (size : bs.length<2^32)
    (positions : i+5*Spec.Rsa.FixedBaseComb.rows N<2^31) (widthFit : N<2^31)
    (bound : Spec.Rsa.os2ip bs<2^N)
    (ptr : s.gpr .r4=src) (length : s.gpr .r5=BitVec.ofNat 32 bs.length)
    (row : s.gpr .r6=BitVec.ofNat 32 i)
    (stride : s.gpr .r7=BitVec.ofNat 32 (Spec.Rsa.FixedBaseComb.rows N))
    (width : s.gpr .r8=BitVec.ofNat 32 N) :
    WP isa VG.Impl.Bignum.Arm.CombDigit.code s fun t =>
      t.gpr .r11=BitVec.ofNat 32 (VG.Proof.Rsa.FixedBaseComb.digit N (Spec.Rsa.os2ip bs) i) ∧
      (t.gpr .r11).toNat<32 ∧ t.mem=s.mem ∧ VG.Proof.X25519.Arm.Rest clobbers s t := by
  simpa only [prefixValue_eq_digit bs N i widthBound bound] using
    code_ok s source widthBound size positions widthFit ptr length row stride width

end VG.Proof.Bignum.Arm.CombDigit
end

end

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombExp
open VG VG.Arm
open VG.Proof.X25519.Arm (Rest)

theorem gather_ok {base source table : BitVec 32} {len w N M g E i : Nat} {bs : List Byte}
    {P : State→Prop} {regions : List Region}
    (A : TwoExp.Montgomery base len w P regions) (s : State)
    (h : Power base len w M g E s) (hp : P s) (controls : Controls base source table bs.length N s)
    (counter : Counter base (i+1) s) (fits : i+1<2^32)
    (bytes : CombDigit.Source source bs s) (widthBound : N≤8*bs.length) (size : bs.length<2^32)
    (positions : i+5*Spec.Rsa.FixedBaseComb.rows N<2^31) (widthFit : N<2^31)
    (bound : Spec.Rsa.os2ip bs<2^N) :
    WP isa (.seq (.block VG.Impl.Bignum.Arm.CombExp.digitArgs) VG.Impl.Bignum.Arm.CombDigit.code) s fun t =>
      Power base len w M g E t ∧ P t ∧ Controls base source table bs.length N t ∧ Counter base (i+1) t ∧
      t.gpr .r11=BitVec.ofNat 32 (VG.Proof.Rsa.FixedBaseComb.digit N (Spec.Rsa.os2ip bs) i) ∧
      (t.gpr .r11).toNat<32 ∧ t.mem=s.mem ∧ Rest roundClobbers s t := by
  rw [WP.seq_iff]
  refine WP.mono (digitArgs_ok s h.ready controls counter fits) ?_
  rintro u ⟨src,byteLen,row,stride,width,memU,restU⟩
  have ru : Rest roundClobbers s u := restU.mono (by decide)
  have frameU : Frame [⟨State.addr base,8*len⟩] s.mem u.mem := by rw [memU]; exact Frame.refl _ _
  have pu := A.stable frameU ru hp
  have powerU := h.of_mem memU restU ((restU.gpr .r0 (by decide)).trans h.ready.ptr)
  refine WP.mono (CombDigit.code_digit_ok u (bytes.of_mem memU restU) widthBound size positions widthFit
    bound src byteLen row stride width) ?_
  rintro t ⟨digit,digitBound,memT,restT⟩
  have rt : Rest roundClobbers u t := restT.mono (by decide)
  have frameT : Frame [⟨State.addr base,8*len⟩] u.mem t.mem := by rw [memT]; exact Frame.refl _ _
  have mem : t.mem=s.mem := memT.trans memU
  have rest := ru.trans rt
  refine ⟨powerU.of_mem memT restT ((restT.gpr .r0 (by decide)).trans powerU.ready.ptr),
    A.stable frameT rt pu,?_,?_,digit,digitBound,mem,rest⟩
  · exact controls.after_header (by intro d hd; rw [mem])
  · change t.mem.readW _ _=_
    rw [mem]
    exact counter

end VG.Proof.Bignum.Arm.CombExp
