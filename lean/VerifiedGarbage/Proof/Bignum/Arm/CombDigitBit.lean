module

public import VerifiedGarbage.Proof.Bignum.Arm.CombDigitLoad
import VerifiedGarbage.Proof.Bignum.Arm.CombDigitGuard
import VerifiedGarbage.Proof.Bignum.Arm.CombDigitShift
import VerifiedGarbage.Proof.Framework.Block

/-! A guarded public-position read returns exactly one exponent bit. -/

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
