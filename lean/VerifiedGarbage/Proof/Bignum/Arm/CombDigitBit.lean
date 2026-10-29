module

public import VerifiedGarbage.Proof.Bignum.Arm.CombDigitLoad

import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Impl.Bignum.Arm.CombDigit
import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.TCB.Arm.Isa
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
  rw [Nat.mod_eq_of_lt (by have := b.isLt; omega : b.toNat < 2^32)]
  change (b.toNat >>> r) &&& 1 = (b.toNat / 2^r % 2)%2^32
  rw [Nat.and_one_is_mod,Nat.shiftRight_eq_div_pow]
  exact (Nat.mod_eq_of_lt (by omega : b.toNat / 2^r % 2 < 2^32)).symm

private theorem optionalShift_ok (s : State) {r : Nat} (bound : r<8)
    (count : s.gpr .r2=BitVec.ofNat 32 r) (zero : s.z=decide (r=0)) :
    WP isa (.ite .ne VG.Impl.Bignum.Arm.CombDigit.shift (.block [])) s fun t =>
      t.gpr .r11=s.gpr .r11>>>r ∧ t.mem=s.mem ∧ Rest [.r2,.r11] s t := by
  by_cases h : r=0
  · subst r
    have run : Exec isa (.ite .ne VG.Impl.Bignum.Arm.CombDigit.shift (.block [])) s
        [.branch false] s := .iteF (by change some (!s.z)=_; simp [zero]) (.block rfl)
    exact ⟨_,s,run,by simp,rfl,Rest.refl _ _⟩
  · obtain ⟨tr,t,run,word,_,mem,rest⟩ := shift_ok s (by omega) (by omega) count
    exact ⟨_,t,.iteT (by change some (!s.z)=_; simp [zero,h]) run,word,mem,rest⟩

/-- The bit is zero when its public index is outside the declared width. -/
theorem bit_ok (s : State) {src : BitVec 32} {bs : List Byte} {k N : Nat}
    (source : Source src bs s) (widthBound : N≤8*bs.length) (size : bs.length<2^32)
    (indexFit : k<2^31) (widthFit : N<2^31)
    (ptr : s.gpr .r4=src) (length : s.gpr .r5=BitVec.ofNat 32 bs.length)
    (index : s.gpr .r9=BitVec.ofNat 32 k) (width : s.gpr .r8=BitVec.ofNat 32 N) :
    WP isa VG.Impl.Bignum.Arm.CombDigit.bit s fun t =>
      t.gpr .r11=BitVec.ofNat 32 (if h:k<N then
        (bs[bs.length-1-k/8]'(by omega)).toNat / 2^(k%8) % 2 else 0) ∧
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
      refine WP.mono (load_ok u (source.of_mem memU restU) (by omega) size
        ((restU.gpr .r4 (by decide)).trans ptr) ((restU.gpr .r5 (by decide)).trans length)
        ((restU.gpr .r9 (by decide)).trans index) (by omega)) ?_
      rintro v ⟨byte,count,zeroV,memV,restV⟩
      rw [WP.seq_iff]
      refine WP.mono (optionalShift_ok v (by omega) count zeroV) ?_
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
