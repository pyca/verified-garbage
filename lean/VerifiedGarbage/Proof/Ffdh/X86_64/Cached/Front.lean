module

public import VerifiedGarbage.Impl.Ffdh.X86_64.Cached
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Spec.RsaKeyGen
public import VerifiedGarbage.Spec.Rsa.FixedBaseComb
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
import VerifiedGarbage.Proof.Ffdh.KeyScalar
public import VerifiedGarbage.Impl.Ffdh.VettedGroups
public import VerifiedGarbage.Spec.Ffdh.VettedKeyGeneration
import VerifiedGarbage.Proof.Ffdh.VettedGroupFacts
import VerifiedGarbage.Proof.Framework.Omega

/-! # FFDH's context on x86-64: the public scalar width -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Cached

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Ffdh.X86_64.Cached
open VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Spec.RsaKeyGen (bitLength)

theorem shr_one_div (x j : Nat) (hx : x < 2 ^ 64) :
    BitVec.ofNat 64 (x / 2 ^ j) >>> 1 = BitVec.ofNat 64 (x / 2 ^ (j + 1)) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : x / 2 ^ j < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx
  have h2 : x / 2 ^ (j + 1) < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2,
    Nat.shiftRight_eq_div_pow, Nat.pow_one, Nat.div_div_eq_div_mul, ← Nat.pow_succ]

/-- `rcx := ` the bit length of the nonzero byte in `rax`. -/
theorem byteBits_ok {s : State} {b : Byte} (hb : b ≠ 0) (hax : s.gpr .rax = b.setWidth 64) :
    WP isa Precompute.byteBits s fun t => t.gpr .rcx = BitVec.ofNat 64 (bitLength b.toNat) ∧
      t.mem = s.mem ∧ Keep [.rax, .rcx] s t := by
  have hb0 : b.toNat ≠ 0 := fun h => hb (BitVec.eq_of_toNat_eq h)
  have hbl := KeyScalar.bitLength_bounds hb0
  have hlt : b.toNat < 256 := b.isLt
  have hpos : 1 ≤ bitLength b.toNat := by
    by_contra h; have : bitLength b.toNat = 0 := by omega
    rw [this] at hbl; omega
  unfold Precompute.byteBits
  refine WP.seq (WP.mono (WP.keep [.rcx] (Q := fun t => t.gpr .rcx = BitVec.ofNat 64 0 ∧ t.mem = s.mem)
    (by xrun) rfl) fun s₁ ⟨⟨hcx₁, hm₁⟩, k₁⟩ => ?_)
  let Inv : Nat → State → Prop := fun j t => t.gpr .rax = BitVec.ofNat 64 (b.toNat / 2 ^ j) ∧
    t.gpr .rcx = BitVec.ofNat 64 j ∧ t.mem = s.mem ∧ Keep [.rax, .rcx] s t
  refine wp_upto (a := 0) (N := bitLength b.toNat) hpos Inv (fun j _ hj t ⟨hat, hct, hmt, kt⟩ => ?_)
    (fun t h => ⟨h.2.1, h.2.2.1, h.2.2.2⟩)
    ⟨by rw [(k₁.gpr (by decide)).trans hax]; apply BitVec.eq_of_toNat_eq; simp,
      hcx₁, hm₁, k₁.mono (by decide)⟩
  have hz : (BitVec.ofNat 64 (b.toNat / 2 ^ (j + 1)) == 0) = decide (j + 1 = bitLength b.toNat) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_iff]
    constructor
    · intro h
      have h' : b.toNat / 2 ^ (j + 1) = 0 := by
        have := congrArg BitVec.toNat h
        rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))] at this
      rw [Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)] at h'
      by_contra hne
      have : 2 ^ (bitLength b.toNat - 1) ≥ 2 ^ (j + 1) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    · intro h
      rw [h, Nat.div_eq_of_lt hbl.2]; rfl
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t' => t'.gpr .rax = BitVec.ofNat 64 (b.toNat / 2 ^ (j + 1)) ∧
      t'.gpr .rcx = BitVec.ofNat 64 (j + 1) ∧ t'.mem = t.mem ∧ t'.zf = some (decide (j + 1 = bitLength b.toNat)))
    (by xrun [hat, hct, shr_one_div _ _ (by omega : b.toNat < 2 ^ 64), ofNat_add_one, BitVec.and_self, hz]) rfl)
    fun t' ⟨⟨ha', hc', hm', hz'⟩, k'⟩ => ⟨hz', ha', hc', hm'.trans hmt, (kt.trans k').mono (by decide)⟩

open VG.Impl.Bignum.X86_64.Public (sK)
open VG.Impl.Ffdh.X86_64.Domain (sEl)
open VG.Proof.Bignum

/-- The policy's width: the bound's, or the recognized one if smaller. -/
def pick (r bb : Nat) : Nat := if r = 0 then bb else min r bb

theorem imul3_low (a : BitVec 64) (b : BitVec 32) :
    BitVec.ofInt 64 (a.toInt * (b.signExtend 64).toInt) = a * b.signExtend 64 := by
  simp only [BitVec.ofInt_mul, BitVec.ofInt_toInt]

/-- `⌈x / 5⌉` by a multiplication: exact for `x < 2^18`. -/
theorem rows_mul {x : Nat} (hx : x ≤ 8192) :
    (BitVec.ofNat 64 (x + 4) * BitVec.signExtend 64 (52429 : BitVec 32)) >>> 18 =
      BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows x) := by
  have e : BitVec.signExtend 64 (52429 : BitVec 32) = BitVec.ofNat 64 52429 := by decide
  rw [e]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Spec.Rsa.FixedBaseComb.rows, Spec.Rsa.FixedBaseComb.teeth]
  rw [Nat.mod_eq_of_lt (show x + 4 < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show (52429 : Nat) < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show (x + 4) * 52429 < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show (x + 5 - 1) / 5 < 2 ^ 64 by omega)]
  omega

theorem bb_eq {e c : Nat} (he1 : 1 ≤ e) (he2 : e ≤ 1024) :
    BitVec.ofNat 64 e <<< 3 - 8 + BitVec.ofNat 64 c = BitVec.ofNat 64 (8 * e - 8 + c) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    show (8 : BitVec 64).toNat = 8 from rfl, Nat.shiftLeft_eq]
  omega

/-- The bound's width, or the recognized one if it is smaller and not zero, in `rax`. -/
theorem width_only {s : State} {B cp : Addr} {Z c e r : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : 256 ≤ Z)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 c) (hc : c ≤ 8) (hEl : word s.mem B (8 * sEl) = BitVec.ofNat 64 e)
    (he1 : 1 ≤ e) (he2 : e ≤ 1024)
    (hRec : word s.mem B (8 * sRec) = BitVec.ofNat 64 r) (hr : r < 2 ^ 32)
    (hCtx : word s.mem B (8 * sCtx) = cp) :
    WP isa (.block Precompute.width) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 (pick r (8 * e - 8 + c)) ∧ t.gpr .rsi = cp ∧ t.mem = s.mem ∧
        Keep [.rax, .rdx, .rsi] s t := by
  have hC8 : InRegions (s.rd ++ s.wr) (off B (8 * sCtx)) 8 :=
    hs.ld (by unfold sCtx VG.Impl.Ffdh.X86_64.Domain.sXe sFn; omega)
  have hR8 : InRegions (s.rd ++ s.wr) (off B (8 * sRec)) 8 := hs.ld (by unfold sRec VG.Impl.Ffdh.X86_64.Domain.sY sFn; omega)
  have hE8 : InRegions (s.rd ++ s.wr) (off B (8 * sEl)) 8 := hs.ld (by unfold sEl sFn; omega)
  have hz : (BitVec.ofNat 64 r &&& BitVec.ofNat 64 r == 0) = decide (r = 0) := by
    rw [BitVec.and_self]; apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq, decide_eq_true_iff]
    constructor
    · intro h; have := congrArg BitVec.toNat h; simpa [Nat.mod_eq_of_lt (show r < 2 ^ 64 by omega)] using this
    · rintro rfl; rfl
  have hlt : decide ((BitVec.ofNat 64 r).toNat < (BitVec.ofNat 64 (8 * e - 8 + c)).toNat) =
      decide (r < 8 * e - 8 + c) := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show r < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show 8 * e - 8 + c < 2 ^ 64 by omega)]
  by_cases h0 : r = 0
  · subst h0
    refine WP.mono (WP.keep [.rax, .rdx, .rsi] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 (pick 0 (8 * e - 8 + c)) ∧
        t.gpr .rsi = cp ∧ t.mem = s.mem) (by
      unfold Precompute.width
      xrun [State.ea, hdr, hdi, hdrOff, hC8, hCtx, hE8, hR8, hEl, hRec, hcx, bb_eq he1 he2, hz, execCmov, readSrc, eval,
        pick, Nat.lt_irrefl, decide_false]) rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  · by_cases hl : r < 8 * e - 8 + c
    · refine WP.mono (WP.keep [.rax, .rdx, .rsi] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 (pick r (8 * e - 8 + c)) ∧
          t.gpr .rsi = cp ∧ t.mem = s.mem) (by
        unfold Precompute.width
        xrun [State.ea, hdr, hdi, hdrOff, hC8, hCtx, hE8, hR8, hEl, hRec, hcx, bb_eq he1 he2, hz, h0, execCmov, readSrc,
          eval, hlt, hl, pick, Nat.min_eq_left (Nat.le_of_lt hl)]) rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
    · refine WP.mono (WP.keep [.rax, .rdx, .rsi] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 (pick r (8 * e - 8 + c)) ∧
          t.gpr .rsi = cp ∧ t.mem = s.mem) (by
        unfold Precompute.width
        xrun [State.ea, hdr, hdi, hdrOff, hC8, hCtx, hE8, hR8, hEl, hRec, hcx, bb_eq he1 he2, hz, h0, execCmov, readSrc,
          eval, hlt, hl, pick, Nat.min_eq_right (Nat.le_of_not_lt hl)]) rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩

theorem atOff (b : Addr) (d : Nat) : b + BitVec.ofInt 64 (d : Int) = off b d := by
  rw [BitVec.ofInt_natCast]

/-- The three public words to the context, the width and the rows to the header. -/
theorem metadata_ok {s : State} {B cp : Addr} {Z F : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : 256 ≤ Z)
    (hax : s.gpr .rax = BitVec.ofNat 64 F) (hF : F ≤ 8192)
    (hrsi : s.gpr .rsi = cp) (hcw : ∀ i < 3, InRegions s.wr (off cp (8 * i)) 8) :
    WP isa (.block Precompute.metadata) s fun t =>
      t.mem = ((((s.mem.writeW (off B (8 * sBits)) (BitVec.ofNat 64 F)).writeW (off B (8 * sRows))
        (BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows F))).writeW (off cp 0) (BitVec.ofNat 64 F)).writeW
          (off cp 8) (BitVec.ofNat 64 ((F + 7) / 8))).writeW (off cp 16)
            (BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows F)) ∧
      Keep [.rcx, .rdx] s t := by
  have hw0 : InRegions s.wr cp 8 := by simpa [off] using hcw 0 (by decide)
  have hw1 := hcw 1 (by decide)
  have hw2 := hcw 2 (by decide)
  simp only [Nat.mul_one, Nat.reduceMul] at hw1 hw2
  have sx7 : BitVec.signExtend 64 (7 : BitVec 32) = 7 := by decide
  have sx4 : BitVec.signExtend 64 (4 : BitVec 32) = 4 := by decide
  have hB8 : InRegions s.wr (off B (8 * sBits)) 8 := hs.st (by unfold sBits VG.Impl.Ffdh.X86_64.Domain.sXl sFn; omega)
  have hS8 : InRegions s.wr (off B (8 * sRows)) 8 := hs.st (by unfold sRows VG.Impl.Ffdh.X86_64.Domain.sOut sFn; omega)
  have hrows : ((BitVec.ofNat 64 F + 4) * BitVec.signExtend 64 (52429 : BitVec 32)) >>> 18 =
      BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows F) := by
    rw [← rows_mul hF, BitVec.ofNat_add]; rfl
  have e7 : (BitVec.ofNat 64 F + 7) >>> 3 = BitVec.ofNat 64 ((F + 7) / 8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      show (7 : BitVec 64).toNat = 7 from rfl]
    rw [Nat.mod_eq_of_lt (show F < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show F + 7 < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show (F + 7) / 8 < 2 ^ 64 by omega)]
  refine WP.mono (WP.keep [.rcx, .rdx] (Q := fun t => t.mem = _) (by
    unfold Precompute.metadata
    xrun [State.ea, hdr, hdi, hdrOff, hB8, hS8, hrsi, hax,
      execImul3, imul3_low, sx7, sx4, hrows, e7, at_, atOff, hw0, hw1, hw2]
    done) rfl) fun t ⟨h, k⟩ => ⟨h, k⟩

theorem recognized_nonzero {a : Spec.Ffdh.Parameters} {bits : Nat}
    (h : Spec.Ffdh.vettedExponentBits a = some bits) : bits ≠ 0 := by
  unfold Spec.Ffdh.vettedExponentBits at h
  repeat' split at h
  all_goals cases h
  all_goals decide

/-- The width the code computes is `generationScalarBits`'s. -/
theorem pick_spec {k : Nat} {dom : List Byte} (positive : 0 < k)
    (size : dom.length = 2 * k ∨ dom.length = 3 * k)
    (normalized : 2 ^ (64 * ((k + 7) / 8 - 1)) ≤ Spec.Rsa.os2ip (dom.take k)) :
    pick (VG.Impl.Ffdh.VettedGroups.recognizeList VG.Impl.Ffdh.VettedGroups.groups k dom)
      (bitLength (Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom))) =
      Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf k dom) := by
  rw [VG.Proof.Ffdh.VettedGroupFacts.recognize_spec positive size normalized]
  cases h : Spec.Ffdh.vettedExponentBits (Spec.Ffdh.domainOf k dom) with
  | none => simp only [Option.getD_none, pick, ite_true, Spec.Ffdh.generationScalarBits, h]
  | some bits => simp only [Option.getD_some, pick, ite_eq_right (recognized_nonzero h), Spec.Ffdh.generationScalarBits, h]

end VG.Proof.Ffdh.X86_64.Cached
