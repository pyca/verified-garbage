module

public import VerifiedGarbage.Proof.Dsa.AArch64.RandomMask
public import VerifiedGarbage.Proof.Dsa.DomainShape
public import VerifiedGarbage.Spec.Dsa.Random
public import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup
public import VerifiedGarbage.Impl.Dsa.AArch64.Random
import VerifiedGarbage.Proof.Dsa.AArch64.RandomCopyInit
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Dsa.AArch64.RandomCopy
public import Aesop.BuiltinRules
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Dsa.RandomEncoding
import VerifiedGarbage.Proof.Dsa.AArch64.RandomMemory
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Dsa.RandomRange
import VerifiedGarbage.Proof.Dsa.AArch64.ZeroMask
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.Dsa.AArch64.RandomFrame

/-! ### `Dsa.AArch64.RandomDrawRange`, which the modules that import this one used -/

section

/-! ### `Dsa.AArch64.RandomInRange`, which only this module used -/

section

/-! ### `Dsa.AArch64.RandomRange`, which only this module used -/

section

/-! ### `Dsa.AArch64.RandomBorrow`, which only this module used -/

section

/-! Byte-subtraction lemma used by the scalar range check. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64

/-- For byte-sized operands (including an incoming borrow), the high bit of
64-bit subtraction is precisely the unsigned borrow. -/
theorem random_byte_borrow (a b : BitVec 64) (ha : a.toNat ≤ 255) (hb : b.toNat ≤ 256) :
    ((a - b) >>> 63).toNat = if a.toNat < b.toNat then 1 else 0 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub]
  split <;> omega_arith

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.Bignum.AArch64

end VG.Proof.Dsa.AArch64

end

end


/-! Correctness of the sampler's right-to-left range check. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64

/-- A byte comparison advances both pointers, preserves memory, and computes
both the subtraction borrow and the nonzero accumulator. -/
theorem random_rangeByte_ok {s : State} {p q : Addr} {a b : Byte} {n c : Nat}
    (hp : s.gpr .x2 = p + 1#64) (hq : s.gpr .x12 = q + 1#64)
    (hn : s.gpr .x9 = BitVec.ofNat 64 n) (h8 : s.gpr .x8 = BitVec.ofNat 64 c)
    (hc : c ≤ 1) (hnpos : 0 < n) (hnb : n < 2 ^ 64)
    (hrp : InRegions (s.rd ++ s.wr) p 1) (hrq : InRegions (s.rd ++ s.wr) q 1)
    (ha : s.mem p = a) (hb : s.mem q = b) :
    WP isa (.block Random.rangeByte) s fun t =>
      t.gpr .x2 = p ∧ t.gpr .x12 = q ∧ t.gpr .x9 = BitVec.ofNat 64 (n - 1) ∧
      (t.gpr .x8).toNat = (if a.toNat < b.toNat + c then 1 else 0) ∧
      t.gpr .x10 = s.gpr .x10 ||| a.setWidth 64 ∧
      t.mem = s.mem ∧
      Keep [.x0, .x4, .x2, .x8, .x10, .x12, .x9] s t := by
  have hac : (a.setWidth 64).toNat = a.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := a.isLt; omega)]
  have hbc : (b.setWidth 64).toNat = b.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega)]
  have hcc : (BitVec.ofNat 64 c).toNat = c := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hadd : (b.setWidth 64 + BitVec.ofNat 64 c).toNat = b.toNat + c := by
    rw [BitVec.toNat_add, hbc, hcc, Nat.mod_eq_of_lt (by have := b.isLt; omega)]
  have hborrow := random_byte_borrow (a.setWidth 64) (b.setWidth 64 + BitVec.ofNat 64 c)
    (by rw [hac]; have := a.isLt; omega) (by rw [hadd]; have := b.isLt; omega)
  rw [hac, hadd] at hborrow
  refine WP.mono (WP.keep [.x0, .x4, .x2, .x8, .x10, .x12, .x9] (Q := fun t =>
      t.gpr .x2 = p ∧ t.gpr .x12 = q ∧ t.gpr .x9 = BitVec.ofNat 64 (n - 1) ∧
      (t.gpr .x8).toNat = (if a.toNat < b.toNat + c then 1 else 0) ∧
      t.gpr .x10 = s.gpr .x10 ||| a.setWidth 64 ∧
      t.mem = s.mem) ?_ rfl rfl rfl)
    fun t ⟨⟨htp, htq, htn, htc, hta, htm⟩, hkt⟩ =>
      ⟨htp, htq, htn, htc, hta, htm, hkt⟩
  unfold Random.rangeByte Random.borrow
  have hpred : BitVec.ofNat 64 n - 1#64 = BitVec.ofNat 64 (n - 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have hbyte (x : Byte) : (x.setWidth 32).setWidth 64 = x.setWidth 64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth]
    have := x.isLt
    omega
  brun [hp, hq, hn, h8, BitVec.add_sub_cancel, hrp, hrq, read_one, ha, hb,
    hbyte, hborrow, hpred]

structure RandomRangeInv (s : State) (p q : Addr) (as bs : List Byte) (j : Nat) (t : State) : Prop where
  keep : Keep [.x0, .x4, .x2, .x8, .x10, .x12, .x9] s t
  ptrA : t.gpr .x2 = p + BitVec.ofNat 64 (as.length - j)
  ptrB : t.gpr .x12 = q + BitVec.ofNat 64 (as.length - j)
  count : t.gpr .x9 = BitVec.ofNat 64 (as.length - j)
  borrow : (t.gpr .x8).toNat = VG.Proof.Dsa.randomBorrow (as.drop (as.length - j)) (bs.drop (as.length - j))
  accum : t.gpr .x10 = VG.Proof.Dsa.randomOr (as.drop (as.length - j))
  mem : t.mem = s.mem

/-- The entire right-to-left loop computes the borrow and OR accumulator. -/
theorem random_rangeLoop_ok {s : State} {p q : Addr} {as bs : List Byte}
    (hlen : as.length = bs.length) (hpos : 0 < as.length) (hbound : as.length < 2 ^ 64)
    (hp : s.gpr .x2 = p + BitVec.ofNat 64 as.length)
    (hq : s.gpr .x12 = q + BitVec.ofNat 64 as.length)
    (hn : s.gpr .x9 = BitVec.ofNat 64 as.length)
    (h8 : s.gpr .x8 = 0) (h9 : s.gpr .x10 = 0)
    (hra : ∀ i < as.length, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 i) 1)
    (hrb : ∀ i < as.length, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 i) 1)
    (hva : ∀ i (h : i < as.length), s.mem (p + BitVec.ofNat 64 i) = as[i])
    (hvb : ∀ i (h : i < bs.length), s.mem (q + BitVec.ofNat 64 i) = bs[i]) :
    WP isa (.loop (.block Random.rangeByte) (.nonzero .x .x9)) s fun t =>
      (t.gpr .x8).toNat = VG.Proof.Dsa.randomBorrow as bs ∧
      t.gpr .x10 = VG.Proof.Dsa.randomOr as ∧ t.mem = s.mem ∧
      Keep [.x0, .x4, .x2, .x8, .x10, .x12, .x9] s t := by
  refine WP.mono (wp_countdown (N := as.length) hbound hpos (RandomRangeInv s p q as bs) ?_ ?_ hn) fun t ht => ?_
  · intro j hj t ht hcount
    let i := as.length - (j + 1)
    have hi : i < as.length := by dsimp only [i]; omega_using [hpos]
    have hib : i < bs.length := by omega_using [hlen, hpos]
    have hij : i + 1 = as.length - j := by dsimp only [i]; omega_using [hj]
    have hpa : t.gpr .x2 = (p + BitVec.ofNat 64 i) + 1#64 := by
      change _ = _ + BitVec.ofNat 64 1
      rw [ht.ptrA, BitVec.add_assoc, BitVec.ofNat_add_ofNat, hij]
    have hpb : t.gpr .x12 = (q + BitVec.ofNat 64 i) + 1#64 := by
      change _ = _ + BitVec.ofNat 64 1
      rw [ht.ptrB, BitVec.add_assoc, BitVec.ofNat_add_ofNat, hij]
    have ht8 : t.gpr .x8 = BitVec.ofNat 64
        (VG.Proof.Dsa.randomBorrow (as.drop (as.length - j)) (bs.drop (as.length - j))) := by
      rw [← ht.borrow, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    refine WP.mono (random_rangeByte_ok (a := as[i]) (b := bs[i]) hpa hpb ht.count ht8 (VG.Proof.Dsa.randomBorrow_le _ _)
      (by omega_using [hj]) (by omega_using [hbound])
      (by rw [ht.keep.rd, ht.keep.wr]; exact hra i hi)
      (by rw [ht.keep.rd, ht.keep.wr]; exact hrb i hi)
      (by rw [ht.mem]; exact hva i hi) (by rw [ht.mem]; exact hvb i hib))
      fun u ⟨hup, huq, hun, hub, hua, hum, hku⟩ => ?_
    refine ⟨⟨(ht.keep.trans hku).mono (by decide), hup, huq, ?_, ?_, ?_, hum.trans ht.mem⟩, ?_⟩
    · rw [hun, show as.length - j - 1 = as.length - (j + 1) by omega_using []]
    · change (u.gpr .x8).toNat = VG.Proof.Dsa.randomBorrow (as.drop i) (bs.drop i)
      rw [List.drop_eq_getElem_cons hi, List.drop_eq_getElem_cons hib, VG.Proof.Dsa.randomBorrow, hij]
      exact hub
    · change u.gpr .x10 = VG.Proof.Dsa.randomOr (as.drop i)
      rw [List.drop_eq_getElem_cons hi, VG.Proof.Dsa.randomOr, hij, hua, ht.accum]
    · rw [hun, hcount]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega_using [hj]
  · refine ⟨Keep.refl _ _, by simpa using hp, by simpa using hq, by simpa using hn, ?_, ?_, rfl⟩
    · rw [Nat.sub_zero, List.drop_length, hlen, List.drop_length, h8]
      rfl
    · simp only [Nat.sub_zero, List.drop_length, VG.Proof.Dsa.randomOr, h9]
  · refine ⟨?_, ?_, ht.mem, ht.keep⟩
    · simpa only [Nat.sub_self, List.drop_zero] using ht.borrow
    · simpa only [Nat.sub_self, List.drop_zero] using ht.accum

/-- Only the combined accept bit is exposed to the following branch. -/
theorem random_rangeFinish_ok {s : State} {a b : Nat}
    (h8 : s.gpr .x8 = BitVec.ofNat 64 (if a < b then 1 else 0))
    (h9 : (s.gpr .x10 == 0) = decide (a = 0)) :
    WP isa (.block Random.rangeFinish) s fun t =>
      t.gpr .x8 = BitVec.ofNat 64 (if 0 < a ∧ a < b then 1 else 0) ∧ t.mem = s.mem ∧
      Keep [.x0, .x8] s t := by
  refine WP.mono (WP.keep [.x0, .x8] (Q := fun t =>
      t.gpr .x8 = BitVec.ofNat 64 (if 0 < a ∧ a < b then 1 else 0) ∧ t.mem = s.mem) ?_ rfl rfl rfl)
    fun _ ⟨h, hk⟩ => ⟨h.1, h.2, hk⟩
  unfold Random.rangeFinish
  brun [exec_tst_x, exec_cselc_x, CondCode.holds, State.write, h9, h8]
  by_cases hz : a = 0 <;> by_cases hl : a < b <;> simp [hz, hl]
  rw [ite_eq_left (show 0 < a by omega_using [hz])]

end VG.Proof.Dsa.AArch64

end

end


/-! Whole range-check correctness, including reads of the sampler's frame. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem random_inRange_ok {s : State} {B p q : Addr} {l : Nat} {as bs : List Byte}
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B)
    (hl : word s.mem B Random.oQLen = BitVec.ofNat 64 l)
    (hn : word s.mem B Random.oWidth = BitVec.ofNat 64 as.length)
    (hq : word s.mem B Random.oQ = q)
    (hp : p + BitVec.ofNat 64 as.length = off B (Random.oNonce + l))
    (hlen : as.length = bs.length) (hpos : 0 < as.length) (hbound : as.length < 2 ^ 64)
    (hra : ∀ i < as.length, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 i) 1)
    (hrb : ∀ i < as.length, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 i) 1)
    (hva : ∀ i (h : i < as.length), s.mem (p + BitVec.ofNat 64 i) = as[i])
    (hvb : ∀ i (h : i < bs.length), s.mem (q + BitVec.ofNat 64 i) = bs[i]) :
    WP isa Random.inRange s fun t =>
      t.gpr .x8 = BitVec.ofNat 64 (if 0 < Spec.Dsa.decodeBE as ∧ Spec.Dsa.decodeBE as < Spec.Dsa.decodeBE bs then 1 else 0) ∧
      t.mem = s.mem ∧ Keep [.x0, .x4, .x2, .x8, .x10, .x12, .x9] s t := by
  unfold Random.inRange
  refine WP.seq (WP.mono (random_rangeInit_ok hs hsp hl hn hq)
    fun u ⟨hup, huq, hun, hu8, hu9, hum, hku⟩ => ?_)
  refine WP.seq (WP.mono (random_rangeLoop_ok (as := as) (bs := bs) hlen hpos hbound
    (hup.trans hp.symm) huq hun hu8 hu9
    (fun i hi => by rw [hku.rd, hku.wr]; exact hra i hi)
    (fun i hi => by rw [hku.rd, hku.wr]; exact hrb i hi)
    (fun i hi => by rw [hum]; exact hva i hi)
    (fun i hi => by rw [hum]; exact hvb i hi))
    fun v ⟨hv8, hv9, hvm, hkv⟩ => ?_)
  have hb : v.gpr .x8 = BitVec.ofNat 64
      (if Spec.Dsa.decodeBE as < Spec.Dsa.decodeBE bs then 1 else 0) := by
    rw [← VG.Proof.Dsa.randomBorrow_eq as bs hlen, ← hv8, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hz : (v.gpr .x10 == 0) = decide (Spec.Dsa.decodeBE as = 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq, hv9]
    exact VG.Proof.Dsa.randomOr_zero as
  refine WP.mono (random_rangeFinish_ok hb hz) fun t ⟨htz, htm, hkt⟩ =>
    ⟨htz, (htm.trans hvm).trans hum, ((hku.trans hkv).trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64

end

end


/-! Range-check a copied candidate against a possibly zero-padded modulus. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem random_check_candidate_ok {s : State} {B Q : Addr} {qBytes copied : List Byte} {k : Nat}
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B)
    (hl : word s.mem B Random.oQLen = BitVec.ofNat 64 qBytes.length)
    (hn : word s.mem B Random.oWidth = BitVec.ofNat 64 (VG.Proof.Dsa.significant qBytes).1)
    (hq : word s.mem B Random.oQ = Q + BitVec.ofNat 64
      (qBytes.length - (VG.Proof.Dsa.significant qBytes).1))
    (hsrc : Src s B Random.frameBytes Q qBytes)
    (hqlen : qBytes.length ≤ 32) (hpos : 0 < (VG.Proof.Dsa.significant qBytes).1)
    (hclen : copied.length = (VG.Proof.Dsa.significant qBytes).1)
    (hcdec : Spec.Dsa.decodeBE copied = k)
    (hcv : ∀ i (hi : i < copied.length), s.mem
      (off B (200 + qBytes.length - (VG.Proof.Dsa.significant qBytes).1) + BitVec.ofNat 64 i) = copied[i]) :
    WP isa Random.inRange s fun t =>
      t.gpr .x8 = BitVec.ofNat 64 (if 0 < k ∧ k < Spec.Dsa.decodeBE qBytes then 1 else 0) ∧ t.mem = s.mem ∧
      Keep [.x0, .x4, .x2, .x8, .x10, .x12, .x9] s t := by
  let n := (VG.Proof.Dsa.significant qBytes).1
  have hnfit : n ≤ qBytes.length := VG.Proof.Dsa.significant_fits qBytes
  have hslice := random_src_drop hsrc (qBytes.length - n)
  have hlen : copied.length = (qBytes.drop (qBytes.length - n)).length := by
    rw [VG.Proof.Dsa.random_significant_drop_length, hclen]
  have hp : off B (200 + qBytes.length - n) + BitVec.ofNat 64 copied.length =
      off B (Random.oNonce + qBytes.length) := by
    rw [hclen]
    change B + BitVec.ofNat 64 (200 + qBytes.length - n) + BitVec.ofNat 64 n = _
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.sub_add_cancel (by omega_using [hnfit])]
    rfl
  have hra : ∀ i < copied.length, InRegions (s.rd ++ s.wr)
      (off B (200 + qBytes.length - n) + BitVec.ofNat 64 i) 1 := by
    intro i hi
    have headdr : off B (200 + qBytes.length - n) + BitVec.ofNat 64 i =
        off B (200 + qBytes.length - n + i) := by simp only [off, BitVec.ofNat_add, BitVec.add_assoc]
    rw [headdr]
    obtain ⟨r, hr, hc⟩ := hs.st1 (d := 200 + qBytes.length - n + i) (by
      unfold Random.frameBytes; omega_using [hqlen, hclen, hnfit, hi])
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (random_inRange_ok hs hsp hl (by rw [hclen]; exact hn) hq hp hlen
    (by omega_using [hpos, hclen]) (by omega) hra (fun i hi => hslice.rd i (by omega_using [hlen, hi])) hcv hslice.val)
    fun t ⟨htz, htm, htk⟩ => ⟨?_, htm, htk⟩
  rw [htz, hcdec, VG.Proof.Dsa.random_significant_drop]

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.RandomCopyCandidate`, which only this module used -/

section

/-! ### `Dsa.AArch64.RandomCopyWhole`, which only this module used -/

section

/-! Compose the masked first byte and unmasked suffix of a random draw. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64
open VG.WriteBytes (writeW8_apply)

private theorem zero_addr (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

private theorem shift_addr (p : Addr) (i : Nat) : p + 1#64 + BitVec.ofNat 64 i = p + BitVec.ofNat 64 (i + 1) := by
  change p + BitVec.ofNat 64 1 + BitVec.ofNat 64 i = _
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_comm 1]

/-- Composition rule used with `random_copyInit_ok`. Every write is confined
to the draw's destination; the only altered byte value is the masked head. -/
theorem random_copy_of_init {s : State} {src dst : Addr} {n : Nat} {head : Byte}
    (hpos : 0 < n) (hbound : n < 2 ^ 64)
    (hr : ∀ i < n, InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < n, InRegions s.wr (dst + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < n, ∀ j < n, src + BitVec.ofNat 64 i ≠ dst + BitVec.ofNat 64 j)
    (hinit : WP isa (.block Random.copyInit) s fun u =>
      u.gpr .x12 = src + 1#64 ∧ u.gpr .x2 = dst + 1#64 ∧ u.gpr .x9 = BitVec.ofNat 64 (n - 1) ∧
      u.mem = s.mem.writeW dst head ∧
      Keep [.x0, .x4, .x12, .x2, .x9] s u) :
    WP isa Random.copy s fun t =>
      (∀ i < n, t.mem (dst + BitVec.ofNat 64 i) = if i = 0 then head else s.mem (src + BitVec.ofNat 64 i)) ∧
      (∀ x, (∀ i < n, x ≠ dst + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧
      Keep [.x0, .x4, .x12, .x2, .x9] s t := by
  unfold Random.copy
  refine WP.seq (WP.mono hinit fun u ⟨hup, hud, hun, hum, hku⟩ => ?_)
  refine WP.mono (random_copyRest_ok hup hud hun (by omega_using [hbound])
    (fun i hi => by rw [hku.rd, hku.wr, shift_addr]; exact hr (i + 1) (by omega_using [hi]))
    (fun i hi => by rw [hku.wr, shift_addr]; exact hw (i + 1) (by omega_using [hi]))
    (fun i hi j hj => by rw [shift_addr, shift_addr]; exact hsep (i + 1) (by omega_using [hi]) (j + 1) (by omega_using [hj])))
    fun t ⟨htb, htf, hkt⟩ => ?_
  refine ⟨?_, ?_, (hku.trans hkt).mono (by decide)⟩
  · intro i hi
    by_cases hi0 : i = 0
    · subst i
      simp only [zero_addr, ite_true]
      have hstay : t.mem dst = u.mem dst := htf dst fun j hj => by
        rw [shift_addr]
        have hn := out_ne (out := dst) (i := 0) (j := j + 1) (by decide) (by omega_using [hbound, hj]) (by omega_using [])
        simpa only [zero_addr] using hn
      rw [hstay, hum, writeW8_apply, ite_eq_left rfl]
    · have hj : i - 1 < n - 1 := by omega_using [hi, hi0]
      have hb := htb (i - 1) hj
      rw [shift_addr, shift_addr, Nat.sub_add_cancel (by omega_using [hi0])] at hb
      rw [hb, ite_eq_right hi0, hum, writeW8_apply]
      have hne : src + BitVec.ofNat 64 i ≠ dst := by
        have h := hsep i hi 0 hpos
        simpa only [zero_addr] using h
      exact ite_eq_right hne
  · intro x hx
    have hstay := htf x fun j hj => by rw [shift_addr]; exact hx (j + 1) (by omega_using [hj])
    rw [hstay, hum, writeW8_apply]
    have hne : x ≠ dst := by simpa only [zero_addr] using hx 0 hpos
    exact ite_eq_right hne

/-- A complete draw copy, from the caller-owned frame to the nonce buffer. -/
theorem random_copy_ok {s : State} {B R src dst : Addr} {l n used : Nat} {mask : BitVec 64}
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B)
    (hR : word s.mem B Random.oRand = R) (hu : word s.mem B Random.oUsed = BitVec.ofNat 64 used)
    (hn : word s.mem B Random.oWidth = BitVec.ofNat 64 n)
    (hl : word s.mem B Random.oQLen = BitVec.ofNat 64 l)
    (hm : word s.mem B Random.oMask = mask)
    (hsrc : R + BitVec.ofNat 64 used = src)
    (hdst : off B Random.oNonce + BitVec.ofNat 64 l - BitVec.ofNat 64 n = dst)
    (hpos : 0 < n) (hbound : n < 2 ^ 64)
    (hr : ∀ i < n, InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < n, InRegions s.wr (dst + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < n, ∀ j < n, src + BitVec.ofNat 64 i ≠ dst + BitVec.ofNat 64 j) :
    WP isa Random.copy s fun t =>
      (∀ i < n, t.mem (dst + BitVec.ofNat 64 i) =
        if i = 0 then (((s.mem src).setWidth 64 &&& mask).setWidth 8)
        else s.mem (src + BitVec.ofNat 64 i)) ∧
      (∀ x, (∀ i < n, x ≠ dst + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧
      Keep [.x0, .x4, .x12, .x2, .x9] s t := by
  exact random_copy_of_init hpos hbound hr hw hsep
    (random_copyInit_ok hs hsp hR hu hn hl hm hsrc hdst hpos hbound
      (by simpa only [zero_addr] using hr 0 hpos)
      (by simpa only [zero_addr] using hw 0 hpos))

end VG.Proof.Dsa.AArch64

end

end


/-! The copied ISA bytes encode precisely the specification's candidate. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

private theorem masked_head (qBytes : List Byte) (b : Byte)
    (hpos : 0 < (VG.Proof.Dsa.significant qBytes).1) :
    ((b.setWidth 64 &&& randomMaskValue (VG.Proof.Dsa.significant qBytes).2.toNat).setWidth 8) =
      b &&& BitVec.ofNat 8 (2 ^ ((VG.Proof.Dsa.significant qBytes).2.toNat.log2 + 1) - 1) := by
  have hb : 0 < (VG.Proof.Dsa.significant qBytes).2.toNat := by
    have hn := VG.Proof.Dsa.significant_nonzero qBytes
    have hz : (VG.Proof.Dsa.significant qBytes).2.toNat ≠ 0 := by
      intro he
      have := hn.mpr (BitVec.eq_of_toNat_eq he)
      omega_using [hpos, this]
    omega_using [hz]
  rw [randomMaskValue_eq _ hb (VG.Proof.Dsa.significant qBytes).2.isLt, BitVec.setWidth_and,
    BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
  rw [BitVec.setWidth_ofNat_of_le (by decide)]

theorem random_copy_candidate_ok {s : State} {B R src dst : Addr} {l used : Nat}
    {qBytes tail : List Byte} {b : Byte}
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B)
    (hR : word s.mem B Random.oRand = R) (hu : word s.mem B Random.oUsed = BitVec.ofNat 64 used)
    (hn : word s.mem B Random.oWidth = BitVec.ofNat 64 (tail.length + 1))
    (hl : word s.mem B Random.oQLen = BitVec.ofNat 64 l)
    (hm : word s.mem B Random.oMask = randomMaskValue (VG.Proof.Dsa.significant qBytes).2.toNat)
    (hsrc : R + BitVec.ofNat 64 used = src)
    (hdst : off B Random.oNonce + BitVec.ofNat 64 l - BitVec.ofNat 64 (tail.length + 1) = dst)
    (hwidth : tail.length + 1 = (VG.Proof.Dsa.significant qBytes).1)
    (hbound : tail.length + 1 < 2 ^ 64)
    (hr : ∀ i < tail.length + 1, InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < tail.length + 1, InRegions s.wr (dst + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < tail.length + 1, ∀ j < tail.length + 1,
      src + BitVec.ofNat 64 i ≠ dst + BitVec.ofNat 64 j)
    (hv : ∀ i (hi : i < (b :: tail).length), s.mem (src + BitVec.ofNat 64 i) = (b :: tail)[i]) :
    WP isa Random.copy s fun t => ∃ copied : List Byte,
      copied.length = tail.length + 1 ∧
      (∀ i (hi : i < copied.length), t.mem (dst + BitVec.ofNat 64 i) = copied[i]) ∧
      Spec.Dsa.decodeBE copied = Spec.Dsa.Random.candidate (Spec.Dsa.decodeBE qBytes) (b :: tail) ∧
      (∀ x, (∀ i < tail.length + 1, x ≠ dst + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧
      Keep [.x0, .x4, .x12, .x2, .x9] s t := by
  refine WP.mono (random_copy_ok hs hsp hR hu hn hl hm hsrc hdst (by omega_using []) hbound hr hw hsep)
    fun t ⟨htv, htf, htk⟩ => ?_
  let head := b &&& BitVec.ofNat 8 (2 ^ ((VG.Proof.Dsa.significant qBytes).2.toNat.log2 + 1) - 1)
  refine ⟨head :: tail, rfl, ?_, (VG.Proof.Dsa.random_candidate_mask qBytes b tail hwidth).symm,
    htf, htk⟩
  intro i hi
  rw [htv i hi]
  cases i with
  | zero =>
    have hb : s.mem src = b := by
      have h := hv 0 (by simp)
      change s.mem (src + 0#64) = b at h
      simpa only [BitVec.add_zero] using h
    simp only [ite_true, hb, List.getElem_cons_zero]
    exact masked_head qBytes b (by omega_using [hwidth])
  | succ i =>
    rw [ite_eq_right (Nat.succ_ne_zero i), hv (i + 1) hi]
    rfl

end VG.Proof.Dsa.AArch64

end

end


/-! A complete draw from the random tape, with derived memory permissions. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem random_copy_draw_ok {s : State} {B R : Addr} {used : Nat} {qBytes rand : List Byte}
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B)
    (hR : word s.mem B Random.oRand = R) (hu : word s.mem B Random.oUsed = BitVec.ofNat 64 used)
    (hn : word s.mem B Random.oWidth = BitVec.ofNat 64 (VG.Proof.Dsa.significant qBytes).1)
    (hl : word s.mem B Random.oQLen = BitVec.ofNat 64 qBytes.length)
    (hm : word s.mem B Random.oMask = randomMaskValue (VG.Proof.Dsa.significant qBytes).2.toNat)
    (hrand : Src s B Random.frameBytes R rand)
    (hqlen : qBytes.length ≤ 32)
    (hpos : 0 < (VG.Proof.Dsa.significant qBytes).1)
    (hfull : used + (VG.Proof.Dsa.significant qBytes).1 ≤ rand.length) :
    WP isa Random.copy s fun t => ∃ copied : List Byte,
      copied.length = (VG.Proof.Dsa.significant qBytes).1 ∧
      (∀ i (hi : i < copied.length), t.mem
        (off B (200 + qBytes.length - (VG.Proof.Dsa.significant qBytes).1) + BitVec.ofNat 64 i) = copied[i]) ∧
      Spec.Dsa.decodeBE copied = Spec.Dsa.Random.candidate (Spec.Dsa.decodeBE qBytes)
        ((rand.drop used).take (VG.Proof.Dsa.significant qBytes).1) ∧
      Outside B (200 + qBytes.length - (VG.Proof.Dsa.significant qBytes).1)
        (VG.Proof.Dsa.significant qBytes).1 s.mem t.mem ∧ Keep [.x0, .x4, .x12, .x2, .x9] s t := by
  let n := (VG.Proof.Dsa.significant qBytes).1
  have hnfit : n ≤ qBytes.length := VG.Proof.Dsa.significant_fits qBytes
  have hlen : ((rand.drop used).take n).length = n := by
    rw [List.length_take, List.length_drop]
    omega_using [hfull]
  have hslice := random_src_take (random_src_drop hrand used) n
  have hne : (rand.drop used).take n ≠ [] := by
    intro he
    rw [he, List.length_nil] at hlen
    omega_using [hpos, hlen]
  obtain ⟨b, tail, he⟩ := List.exists_cons_of_ne_nil hne
  rw [he] at hlen hslice
  have htlen : tail.length + 1 = n := hlen
  have hbound : tail.length + 1 < 2 ^ 64 := by omega_using [hqlen, hnfit, htlen]
  have hdst : off B Random.oNonce + BitVec.ofNat 64 qBytes.length - BitVec.ofNat 64 (tail.length + 1) =
      off B (200 + qBytes.length - n) := by rw [htlen]; exact random_nonce_addr B hnfit
  have hwrite : ∀ i < tail.length + 1,
      InRegions s.wr (off B (200 + qBytes.length - n) + BitVec.ofNat 64 i) 1 := by
    intro i hi
    have headdr : off B (200 + qBytes.length - n) + BitVec.ofNat 64 i =
        off B (200 + qBytes.length - n + i) := by simp only [off, BitVec.ofNat_add, BitVec.add_assoc]
    rw [headdr]
    exact hs.st1 (by unfold Random.frameBytes; omega_using [hqlen, hnfit, htlen, hi])
  have hsep : ∀ i < tail.length + 1, ∀ j < tail.length + 1,
      R + BitVec.ofNat 64 used + BitVec.ofNat 64 i ≠
        off B (200 + qBytes.length - n) + BitVec.ofNat 64 j := by
    intro i hi j hj headdr
    have ho := hslice.out i hi
    rw [headdr, random_nonce_offset B hnfit hqlen (by omega_using [htlen, hj])] at ho
    unfold Random.frameBytes at ho
    omega_using [hsp, hR, hu, hn, hl, hm, hqlen, hpos, hfull, hnfit, hlen, htlen, hbound, hi, hj, ho]
  refine WP.mono (random_copy_candidate_ok hs hsp hR hu
    (by rw [htlen]; exact hn) hl hm rfl hdst htlen hbound hslice.rd hwrite hsep hslice.val)
    fun t ⟨copied, hclen, hcv, hcdec, hcf, hck⟩ => ?_
  refine ⟨copied, hclen.trans htlen, hcv, ?_, ?_, hck⟩
  · rw [he]; exact hcdec
  · exact random_copy_outside hnfit hqlen (by simpa only [htlen] using hcf)

end VG.Proof.Dsa.AArch64
