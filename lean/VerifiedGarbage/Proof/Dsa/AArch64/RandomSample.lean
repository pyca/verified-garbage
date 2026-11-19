module

public import VerifiedGarbage.Proof.Dsa.RandomResult
import VerifiedGarbage.Proof.Dsa.RandomEncoding
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Dsa.Encoding
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomState
public import VerifiedGarbage.Spec.Dsa.Random
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomDrawControl
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomMask
public import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup
public import VerifiedGarbage.Proof.Dsa.DomainShape
import VerifiedGarbage.Proof.Dsa.AArch64.RandomMemory
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Impl.Dsa.AArch64.Random
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Dsa.AArch64.RandomCopy
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Dsa.RandomRange
import VerifiedGarbage.Proof.Dsa.AArch64.ZeroMask
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Push
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp

/-! ### `Dsa.AArch64.RandomSampleLoop`, which this module and modules that import it used -/

section

/-! Termination rule for the sampler's status-controlled loop. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem random_statusTest_ok {s : State} {B : Addr} {status : BitVec 64}
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B)
    (hv : word s.mem B Random.oStatus = status) :
    WP isa (.block (Random.statusTest 4)) s fun t =>
      (t.gpr .x4 == 0#64) = (status == 4) ∧ t.mem = s.mem ∧ Keep [.x0, .x4] s t := by
  refine WP.mono (WP.keep [.x0, .x4] (Q := fun t =>
      (t.gpr .x4 == 0#64) = (status == 4) ∧ t.mem = s.mem) ?_ rfl rfl rfl)
    fun _ ⟨⟨hz, hm⟩, hk⟩ => ⟨hz, hm, hk⟩
  unfold Random.statusTest
  brun [exec_ldrSp (show Random.oStatus % 8 = 0 ∧ Random.oStatus < 32768 by decide),
    hsp, hs.ld (d := Random.oStatus) (by decide), hv]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, BitVec.sub_eq_iff_eq_add, BitVec.zero_add]
  rfl

/-- A draw either produces a terminal result or strictly decreases fuel.
The actual status test is verified here; callers supply the draw invariant. -/
theorem random_statusLoop_rule (body : Prog isa) (B : Addr) (Inv : Nat → State → Prop) (Q : State → Prop)
    (hstable : ∀ n s t, Inv n s → t.mem = s.mem → Keep [.x0, .x4] s t → Inv n t)
    (hqstable : ∀ s t, Q s → t.mem = s.mem → Keep [.x0, .x4] s t → Q t)
    (hdraw : ∀ n s, Inv n s → WP isa body s fun t =>
      Scr t B Random.frameBytes ∧ t.sp = B ∧
      ((word t.mem B Random.oStatus ≠ 4 ∧ Q t) ∨
       (word t.mem B Random.oStatus = 4 ∧ ∃ k < n, Inv k t)))
    {n : Nat} {s : State} (hi : Inv n s) :
    WP isa (.loop (.seq body (.block (Random.statusTest 4))) (.zero .x .x4)) s Q := by
  refine WP.loop (M := isa) Inv ?_ n s hi
  intro n u hu
  refine WP.seq (WP.mono (hdraw n u hu) fun v ⟨hvs, hvsp, hv⟩ => ?_)
  refine WP.mono (random_statusTest_ok hvs hvsp rfl) fun t ⟨htz, htm, hkt⟩ => ?_
  rcases hv with ⟨hne, hq⟩ | ⟨he, k, hkn, hk⟩
  · exact Or.inl ⟨by
      change some (t.gpr .x4 == 0#64) = some false
      rw [htz, beq_eq_false_iff_ne.mpr hne],
      hqstable v t hq htm hkt⟩
  · exact Or.inr ⟨by
      change some (t.gpr .x4 == 0#64) = some true
      rw [htz, he, beq_self_eq_true], k, hkn,
      hstable k v t hk htm hkt⟩


theorem random_sampleLoop_rule (B : Addr) (Inv : Nat → State → Prop) (Q : State → Prop)
    (hstable : ∀ n s t, Inv n s → t.mem = s.mem → Keep [.x0, .x4] s t → Inv n t)
    (hqstable : ∀ s t, Q s → t.mem = s.mem → Keep [.x0, .x4] s t → Q t)
    (hdraw : ∀ n s, Inv n s → WP isa Random.draw s fun t =>
      Scr t B Random.frameBytes ∧ t.sp = B ∧
      ((word t.mem B Random.oStatus ≠ 4 ∧ Q t) ∨
       (word t.mem B Random.oStatus = 4 ∧ ∃ k < n, Inv k t)))
    {n : Nat} {s : State} (hi : Inv n s) :
    WP isa (.loop (.seq Random.draw (.block (Random.statusTest 4))) (.zero .x .x4)) s Q :=
  random_statusLoop_rule Random.draw B Inv Q hstable hqstable hdraw hi

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.RandomDrawResult`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.RandomDrawCopy`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.RandomCopyInit`, which this module and modules that import it used -/

section

/-! Read a complete draw's first byte and apply its public bit mask. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem random_copyInit_ok {s : State} {B R src dst : Addr} {l n used : Nat} {mask : BitVec 64}
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B)
    (hR : word s.mem B Random.oRand = R) (hu : word s.mem B Random.oUsed = BitVec.ofNat 64 used)
    (hn : word s.mem B Random.oWidth = BitVec.ofNat 64 n)
    (hl : word s.mem B Random.oQLen = BitVec.ofNat 64 l)
    (hm : word s.mem B Random.oMask = mask)
    (hsrc : R + BitVec.ofNat 64 used = src)
    (hdst : off B Random.oNonce + BitVec.ofNat 64 l - BitVec.ofNat 64 n = dst)
    (hpos : 0 < n) (hbound : n < 2 ^ 64)
    (hr : InRegions (s.rd ++ s.wr) src 1) (hw : InRegions s.wr dst 1) :
    WP isa (.block Random.copyInit) s fun t =>
      t.gpr .x12 = src + 1#64 ∧ t.gpr .x2 = dst + 1#64 ∧ t.gpr .x9 = BitVec.ofNat 64 (n - 1) ∧
      t.mem = s.mem.writeW dst (((s.mem src).setWidth 64 &&& mask).setWidth 8) ∧
      Keep [.x0, .x4, .x12, .x2, .x9] s t := by
  refine WP.mono (WP.keep [.x0, .x4, .x12, .x2, .x9] (Q := fun t =>
      t.gpr .x12 = src + 1#64 ∧ t.gpr .x2 = dst + 1#64 ∧ t.gpr .x9 = BitVec.ofNat 64 (n - 1) ∧
      t.mem = s.mem.writeW dst (((s.mem src).setWidth 64 &&& mask).setWidth 8)) ?_ rfl rfl rfl)
    fun _ ⟨⟨ha, hb, hc, hm⟩, hk⟩ => ⟨ha, hb, hc, hm, hk⟩
  unfold Random.copyInit Random.copyHeader Random.copyFirst
  have hbyte (x : Byte) : (x.setWidth 32).setWidth 64 = x.setWidth 64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth]
    have := x.isLt
    omega
  have hpred : BitVec.ofNat 64 n - 1#64 = BitVec.ofNat 64 (n - 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have haddr : off B (Random.oNonce + l) - BitVec.ofNat 64 n = dst := by
    simpa only [off, BitVec.ofNat_add_ofNat, BitVec.add_assoc] using hdst
  brun [List.append_assoc, List.cons_append, List.nil_append,
    exec_addSp (show Random.oNonce < 4096 by decide),
    exec_ldrSp (show Random.oRand % 8 = 0 ∧ Random.oRand < 32768 by decide),
    exec_ldrSp (show Random.oUsed % 8 = 0 ∧ Random.oUsed < 32768 by decide),
    exec_ldrSp (show Random.oWidth % 8 = 0 ∧ Random.oWidth < 32768 by decide),
    exec_ldrSp (show Random.oQLen % 8 = 0 ∧ Random.oQLen < 32768 by decide),
    exec_ldrSp (show Random.oMask % 8 = 0 ∧ Random.oMask < 32768 by decide),
    hsp, hs.ld (d := Random.oRand) (by decide), hs.ld (d := Random.oUsed) (by decide),
    hs.ld (d := Random.oWidth) (by decide), hs.ld (d := Random.oQLen) (by decide),
    hs.ld (d := Random.oMask) (by decide), hR, hu, hn, hl, hm, hsrc, haddr,
    hr, hw, hpred, read_one, hbyte]
  rfl

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.RandomFrame`, which this module and modules that import it used -/

section

/-! Accesses to the randomized-signing frame. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem random_rangeInit_ok {s : State} {B q : Addr} {l n : Nat}
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B)
    (hl : word s.mem B Random.oQLen = BitVec.ofNat 64 l)
    (hn : word s.mem B Random.oWidth = BitVec.ofNat 64 n)
    (hq : word s.mem B Random.oQ = q) :
    WP isa (.block Random.rangeInit) s fun t =>
      t.gpr .x2 = off B (Random.oNonce + l) ∧
      t.gpr .x12 = q + BitVec.ofNat 64 n ∧ t.gpr .x9 = BitVec.ofNat 64 n ∧
      t.gpr .x8 = 0 ∧ t.gpr .x10 = 0 ∧ t.mem = s.mem ∧
      Keep [.x2, .x4, .x8, .x9, .x10, .x12] s t := by
  refine WP.mono (WP.keep [.x2, .x4, .x8, .x9, .x10, .x12] (Q := fun t =>
      t.gpr .x2 = off B (Random.oNonce + l) ∧
      t.gpr .x12 = q + BitVec.ofNat 64 n ∧ t.gpr .x9 = BitVec.ofNat 64 n ∧
      t.gpr .x8 = 0 ∧ t.gpr .x10 = 0 ∧ t.mem = s.mem) ?_ rfl rfl rfl)
    fun _ ⟨⟨hd, hq, hn, h8, h9, hm⟩, hk⟩ => ⟨hd, hq, hn, h8, h9, hm, hk⟩
  unfold Random.rangeInit
  brun [exec_addSp (show Random.oNonce < 4096 by decide), hsp,
    exec_ldrSp (show Random.oQLen % 8 = 0 ∧ Random.oQLen < 32768 by decide),
    exec_ldrSp (show Random.oWidth % 8 = 0 ∧ Random.oWidth < 32768 by decide),
    exec_ldrSp (show Random.oQ % 8 = 0 ∧ Random.oQ < 32768 by decide),
    hs.ld (d := Random.oQLen) (by decide), hs.ld (d := Random.oWidth) (by decide),
    hs.ld (d := Random.oQ) (by decide), hl, hn, hq]

end VG.Proof.Dsa.AArch64

end

end

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

end

end

/-! ### `Dsa.AArch64.RandomDraw`, which only this module used -/

section

/-! A full scalar draw: copy, account for bytes, compare and update fuel. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem random_draw_full_ok {s : State} {B R Q : Addr} {used draws : Nat} {qBytes rand : List Byte}
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B)
    (hR : word s.mem B Random.oRand = R)
    (hrlen : word s.mem B Random.oRandLen = BitVec.ofNat 64 rand.length)
    (hu : word s.mem B Random.oUsed = BitVec.ofNat 64 used)
    (hn : word s.mem B Random.oWidth = BitVec.ofNat 64 (VG.Proof.Dsa.significant qBytes).1)
    (hl : word s.mem B Random.oQLen = BitVec.ofNat 64 qBytes.length)
    (hm : word s.mem B Random.oMask = randomMaskValue (VG.Proof.Dsa.significant qBytes).2.toNat)
    (hq : word s.mem B Random.oQ = Q + BitVec.ofNat 64
      (qBytes.length - (VG.Proof.Dsa.significant qBytes).1))
    (hd : word s.mem B Random.oDraws = BitVec.ofNat 64 draws)
    (hrand : Src s B Random.frameBytes R rand) (hqs : Src s B Random.frameBytes Q qBytes)
    (hqlen : qBytes.length ≤ 32) (hrbound : rand.length < 2 ^ 64)
    (hpos : 0 < (VG.Proof.Dsa.significant qBytes).1)
    (hfull : used + (VG.Proof.Dsa.significant qBytes).1 ≤ rand.length)
    (hdpos : 0 < draws) (hdbound : draws < 2 ^ 64) :
    WP isa Random.draw s fun t => ∃ m : Mem, ∃ copied : List Byte,
      copied.length = (VG.Proof.Dsa.significant qBytes).1 ∧
      (∀ i (hi : i < copied.length), m
        (off B (200 + qBytes.length - (VG.Proof.Dsa.significant qBytes).1) + BitVec.ofNat 64 i) = copied[i]) ∧
      Spec.Dsa.decodeBE copied = Spec.Dsa.Random.candidate (Spec.Dsa.decodeBE qBytes)
        ((rand.drop used).take (VG.Proof.Dsa.significant qBytes).1) ∧
      Outside B (200 + qBytes.length - (VG.Proof.Dsa.significant qBytes).1)
        (VG.Proof.Dsa.significant qBytes).1 s.mem m ∧
      t.mem = randomDrawFinishMem
        (m.writeW (off B Random.oUsed) (BitVec.ofNat 64 (used + copied.length))) B
        (decide (0 < Spec.Dsa.decodeBE copied ∧ Spec.Dsa.decodeBE copied < Spec.Dsa.decodeBE qBytes)) draws ∧
      Keep [.x0, .x3, .x4, .x2, .x8, .x10, .x12, .x9, .x15] s t := by
  let n := (VG.Proof.Dsa.significant qBytes).1
  have hnfit : n ≤ qBytes.length := VG.Proof.Dsa.significant_fits qBytes
  unfold Random.draw
  refine WP.seq (WP.mono (random_drawHead_ok hs hsp hrlen hu hn (by omega_using [hfull]) hrbound (by omega_using [hrbound, hfull]))
    fun a ⟨hac, ham, hka⟩ => ?_)
  change a.gpr .x3 = BitVec.ofNat 64 (if rand.length - used < n then 1 else 0) at hac
  have hshort : ¬ rand.length - used < n := by omega_using [hfull]
  refine WP.ite false (by simp [eval, State.read, hac, hshort])
    (fun h => Bool.noConfusion h) (fun _ => ?_)
  have has := hs.congr hka.wr
  have hasp := hka.sp.trans hsp
  have harand := hrand.congrK (show InScr B Random.frameBytes s.mem a.mem from by
    rw [ham]; exact InScr.refl _ _ _) hka
  refine WP.seq (WP.mono (random_copy_draw_ok has hasp
    (by rw [ham]; exact hR) (by rw [ham]; exact hu) (by rw [ham]; exact hn)
    (by rw [ham]; exact hl) (by rw [ham]; exact hm) harand hqlen hpos hfull)
    fun b ⟨copied, hclen, hcv, hcdec, hbf, hkb⟩ => ?_)
  have hbk := hka.trans hkb
  have hbs := hs.congr hbk.wr
  have hbsp := hbk.sp.trans hsp
  have hbf' : Outside B 200 32 s.mem b.mem := by
    rw [← ham]
    exact hbf.mono (by omega_using [hnfit]) (by omega_using [hqlen, hnfit])
  have hbu : word b.mem B Random.oUsed = BitVec.ofNat 64 used := by
    rw [hbf'.word (by decide) (by decide)]; exact hu
  have hbn : word b.mem B Random.oWidth = BitVec.ofNat 64 n := by
    rw [hbf'.word (by decide) (by decide)]; exact hn
  refine WP.seq (WP.mono (random_used_ok hbs hbsp hbu hbn)
    fun c ⟨hcm, hkc⟩ => ?_)
  have hck := hbk.trans hkc
  have hcs := hs.congr hck.wr
  have hcsp := hck.sp.trans hsp
  have hcf : Outside B Random.oUsed 8 b.mem c.mem := by
    rw [hcm]; exact writeW_outside _ _ _ (by decide)
  have hcqsrc := hqs.congrK
    ((InScr.of_outside hbf' (by decide)).trans (InScr.of_outside hcf (by decide))) hck
  have hcl : word c.mem B Random.oQLen = BitVec.ofNat 64 qBytes.length := by
    rw [hcf.word (by decide) (by decide), hbf'.word (by decide) (by decide)]; exact hl
  have hcn : word c.mem B Random.oWidth = BitVec.ofNat 64 n := by
    rw [hcf.word (by decide) (by decide)]; exact hbn
  have hcq : word c.mem B Random.oQ = Q + BitVec.ofNat 64 (qBytes.length - n) := by
    rw [hcf.word (by decide) (by decide), hbf'.word (by decide) (by decide)]; exact hq
  have hccv : ∀ i (hi : i < copied.length), c.mem
      (off B (200 + qBytes.length - n) + BitVec.ofNat 64 i) = copied[i] := by
    intro i hi
    rw [hcf _ (by
      rw [random_nonce_offset B hnfit hqlen (by omega_using [hclen, hi])]
      right
      unfold Random.oUsed
      omega_using [hnfit])]
    exact hcv i hi
  refine WP.seq (WP.mono (random_check_candidate_ok hcs hcsp hcl hcn hcq hcqsrc
      hqlen hpos hclen rfl hccv)
    fun d ⟨hdz, hdm, hkd⟩ => ?_)
  have hdk := hck.trans hkd
  have hdd : word d.mem B Random.oDraws = BitVec.ofNat 64 draws := by
    rw [hdm, hcf.word (by decide) (by decide), hbf'.word (by decide) (by decide)]; exact hd
  refine WP.mono (random_drawFinish_ok (accept := decide (0 < Spec.Dsa.decodeBE copied ∧
      Spec.Dsa.decodeBE copied < Spec.Dsa.decodeBE qBytes)) (hs.congr hdk.wr)
    (hdk.sp.trans hsp) hdd (by simpa only [decide_eq_true_eq] using hdz) hdpos hdbound)
    fun t ⟨htm, hkt⟩ => ?_
  refine ⟨b.mem, copied, hclen, hcv, hcdec, (by rw [← ham]; exact hbf), ?_, (hdk.trans hkt).mono (by decide)⟩
  rw [htm, hdm, hcm, hclen]

end VG.Proof.Dsa.AArch64

end

end


/-! Value and status observations after one complete draw. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

def RandomNonceValue (C : RandomContext) (k : Nat) (s : State) : Prop :=
  ∃ copied : List Byte, copied.length = (VG.Proof.Dsa.significant C.qBytes).1 ∧
    (∀ i (hi : i < copied.length), s.mem
      (off C.B (200 + C.qBytes.length - (VG.Proof.Dsa.significant C.qBytes).1) + BitVec.ofNat 64 i) = copied[i]) ∧
    Spec.Dsa.decodeBE copied = k

theorem RandomNonceValue.congr {C : RandomContext} {k : Nat} {s t : State}
    (h : RandomNonceValue C k s) (hm : t.mem = s.mem) : RandomNonceValue C k t := by
  obtain ⟨bs, hl, hv, hd⟩ := h
  exact ⟨bs, hl, by rw [hm]; exact hv, hd⟩

def randomNextCandidate (C : RandomContext) (used : Nat) : Nat :=
  Spec.Dsa.Random.candidate (Spec.Dsa.decodeBE C.qBytes)
    ((C.rand.drop used).take (VG.Proof.Dsa.significant C.qBytes).1)

theorem random_draw_full_result {C : RandomContext} {used draws : Nat} {s : State}
    (hr : RandomReady C used draws s) (hstatus : word s.mem C.B Random.oStatus = 4)
    (hfull : used + (VG.Proof.Dsa.significant C.qBytes).1 ≤ C.rand.length)
    (hdpos : 0 < draws) (hdbound : draws < 2 ^ 64) :
    WP isa Random.draw s fun t =>
      let accepted := decide (0 < randomNextCandidate C used ∧ randomNextCandidate C used < Spec.Dsa.decodeBE C.qBytes)
      RandomReady C (used + (VG.Proof.Dsa.significant C.qBytes).1)
        (if accepted then draws else draws - 1) t ∧
      word t.mem C.B Random.oStatus = (if accepted then 1 else if draws = 1 then 0 else 4) ∧
      RandomNonceValue C (randomNextCandidate C used) t := by
  refine WP.mono (random_draw_full_ok hr.scr hr.sp hr.rand hr.randLen hr.usedWord hr.width
    hr.qLen hr.mask hr.q hr.draws hr.randSrc hr.qSrc C.qlen C.randBound C.positive hfull hdpos hdbound)
    fun t ⟨m, copied, hclen, hcv, hcdec, hcopy, htm, hkt⟩ => ?_
  let n := (VG.Proof.Dsa.significant C.qBytes).1
  let accepted := decide (0 < randomNextCandidate C used ∧ randomNextCandidate C used < Spec.Dsa.decodeBE C.qBytes)
  have htm' : t.mem = randomDrawFinishMem
      (m.writeW (off C.B Random.oUsed) (BitVec.ofNat 64 (used + n))) C.B accepted draws := by
    rw [htm, hclen, hcdec]; rfl
  refine ⟨hr.after_draw accepted hfull hcopy htm' hkt, ?_, copied, hclen, ?_, hcdec⟩
  · rw [htm', random_drawFinish_status]
    have he : word (m.writeW (off C.B Random.oUsed) (BitVec.ofNat 64 (used + n))) C.B Random.oStatus = 4 := by
      rw [(writeW_outside _ C.B _ (by decide)).word (by decide) (by decide), (hcopy.mono (o' := 200) (n' := 32) (by have := VG.Proof.Dsa.significant_fits C.qBytes; omega_using [this]) (by have := C.qlen; have := VG.Proof.Dsa.significant_fits C.qBytes; omega_arith)).word (by decide) (by decide)]
      exact hstatus
    rw [he]
  · intro i hi
    have hnfit : n ≤ C.qBytes.length := VG.Proof.Dsa.significant_fits C.qBytes
    have ho : ofs C.B (off C.B (200 + C.qBytes.length - n) + BitVec.ofNat 64 i) =
        200 + C.qBytes.length - n + i := random_nonce_offset C.B hnfit C.qlen (by omega_using [hclen, hi])
    rw [htm', random_drawFinish_outside _ C.B accepted draws _ (by rw [ho]; right; omega_using [hnfit]),
      (writeW_outside _ C.B _ (by decide)) _ (by rw [ho]; right; unfold Random.oUsed; omega_using [hnfit])]
    exact hcv i hi

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.RandomRemaining`, which only this module used -/

section

/-! Relating a tape offset to the recursive sampling specification. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64 VG.Proof.Dsa.Random

def randomRemaining (C : RandomContext) (used fuel : Nat) : Spec.Dsa.Random.Sample :=
  Spec.Dsa.Random.sample (Spec.Dsa.decodeBE C.qBytes) fuel (C.rand.drop used)

structure RandomResultRel (C : RandomContext) (start : Nat) (result : Spec.Dsa.Random.Sample)
    (used fuel : Nat) : Prop where
  scalar : result.scalar = (randomRemaining C used fuel).scalar
  consumption : start + result.used = used + (randomRemaining C used fuel).used
  status : sampleStatus result = sampleStatus (randomRemaining C used fuel)

def RandomSamplePost (C : RandomContext) (start : Nat) (result : Spec.Dsa.Random.Sample) (s : State) : Prop :=
  (∃ draws, RandomReady C (start + result.used) draws s) ∧
  word s.mem C.B Random.oStatus = BitVec.ofNat 64 (sampleStatus result) ∧
  ∀ k, result.scalar = some k → RandomNonceValue C k s

theorem random_remaining_short {C : RandomContext} {used fuel : Nat}
    (hq : 1 < Spec.Dsa.decodeBE C.qBytes)
    (hshort : C.rand.length - used < (VG.Proof.Dsa.significant C.qBytes).1) :
    randomRemaining C used (fuel + 1) = ⟨none, 0, [2]⟩ := by
  apply sample_short _ _ _ hq
  rwa [List.length_drop, VG.Proof.Dsa.random_drawBytes_scan]

theorem random_remaining_accept {C : RandomContext} {used fuel : Nat}
    (hq : 1 < Spec.Dsa.decodeBE C.qBytes)
    (hfull : used + (VG.Proof.Dsa.significant C.qBytes).1 ≤ C.rand.length)
    (hk : 0 < randomNextCandidate C used ∧ randomNextCandidate C used < Spec.Dsa.decodeBE C.qBytes) :
    randomRemaining C used (fuel + 1) =
      ⟨some (randomNextCandidate C used), (VG.Proof.Dsa.significant C.qBytes).1, [1]⟩ := by
  have hs : Spec.Dsa.Random.drawBytes (Spec.Dsa.decodeBE C.qBytes) ≤ (C.rand.drop used).length := by
    rw [VG.Proof.Dsa.random_drawBytes_scan, List.length_drop]; omega_using [hfull]
  have hk' : 0 < Spec.Dsa.Random.candidate (Spec.Dsa.decodeBE C.qBytes)
      ((C.rand.drop used).take (Spec.Dsa.Random.drawBytes (Spec.Dsa.decodeBE C.qBytes))) ∧
      Spec.Dsa.Random.candidate (Spec.Dsa.decodeBE C.qBytes)
      ((C.rand.drop used).take (Spec.Dsa.Random.drawBytes (Spec.Dsa.decodeBE C.qBytes))) < Spec.Dsa.decodeBE C.qBytes := by
    rw [VG.Proof.Dsa.random_drawBytes_scan]; exact hk
  simpa only [randomRemaining, randomNextCandidate, VG.Proof.Dsa.random_drawBytes_scan] using
    sample_accept _ fuel _ hq hs hk'

theorem random_remaining_reject {C : RandomContext} {used fuel : Nat}
    (hq : 1 < Spec.Dsa.decodeBE C.qBytes)
    (hfull : used + (VG.Proof.Dsa.significant C.qBytes).1 ≤ C.rand.length)
    (hk : ¬ (0 < randomNextCandidate C used ∧ randomNextCandidate C used < Spec.Dsa.decodeBE C.qBytes)) :
    randomRemaining C used (fuel + 1) =
      let next := randomRemaining C (used + (VG.Proof.Dsa.significant C.qBytes).1) fuel
      ⟨next.scalar, (VG.Proof.Dsa.significant C.qBytes).1 + next.used, 0 :: next.trace⟩ := by
  have hs : Spec.Dsa.Random.drawBytes (Spec.Dsa.decodeBE C.qBytes) ≤ (C.rand.drop used).length := by
    rw [VG.Proof.Dsa.random_drawBytes_scan, List.length_drop]; omega_using [hfull]
  have hk' : ¬ (0 < Spec.Dsa.Random.candidate (Spec.Dsa.decodeBE C.qBytes)
      ((C.rand.drop used).take (Spec.Dsa.Random.drawBytes (Spec.Dsa.decodeBE C.qBytes))) ∧
      Spec.Dsa.Random.candidate (Spec.Dsa.decodeBE C.qBytes)
      ((C.rand.drop used).take (Spec.Dsa.Random.drawBytes (Spec.Dsa.decodeBE C.qBytes))) < Spec.Dsa.decodeBE C.qBytes) := by
    rw [VG.Proof.Dsa.random_drawBytes_scan]; exact hk
  simpa only [randomRemaining, VG.Proof.Dsa.random_drawBytes_scan, List.drop_drop] using
    sample_reject _ fuel _ hq hs hk'

theorem RandomResultRel.reject {C : RandomContext} {start used fuel : Nat} {result : Spec.Dsa.Random.Sample}
    (hr : RandomResultRel C start result used (fuel + 1))
    (hq : 1 < Spec.Dsa.decodeBE C.qBytes)
    (hfull : used + (VG.Proof.Dsa.significant C.qBytes).1 ≤ C.rand.length)
    (hk : ¬ (0 < randomNextCandidate C used ∧ randomNextCandidate C used < Spec.Dsa.decodeBE C.qBytes)) :
    RandomResultRel C start result (used + (VG.Proof.Dsa.significant C.qBytes).1) fuel := by
  have he := random_remaining_reject hq hfull hk (fuel := fuel)
  refine ⟨?_, ?_, ?_⟩
  · rw [hr.scalar, he]
  · have hu := hr.consumption
    rw [he] at hu
    simp only at hu
    omega_using [hu]
  · rw [hr.status, he]
    exact sampleStatus_reject _ _ _ _

end VG.Proof.Dsa.AArch64

end

end

/-! Entry and exit of the complete 128-draw sampler. -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/RandomFunctional.lean`, which only this module imported.
section

/-! Functional equivalence of the bounded sampling loop. -/
section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64 VG.Proof.Dsa.Random

def RandomFunctionalInv (C : RandomContext) (start : Nat) (result : Spec.Dsa.Random.Sample)
    (fuel : Nat) (s : State) : Prop :=
  0 < fuel ∧ fuel ≤ 128 ∧ ∃ used, RandomReady C used fuel s ∧
    word s.mem C.B Random.oStatus = 4 ∧ RandomResultRel C start result used fuel

private theorem functional_draw (C : RandomContext) (start : Nat) (result : Spec.Dsa.Random.Sample)
    (hq : 1 < Spec.Dsa.decodeBE C.qBytes) (draws : Nat) (s : State)
    (hi : RandomFunctionalInv C start result draws s) :
    WP isa Random.draw s fun t => Scr t C.B Random.frameBytes ∧ t.sp = C.B ∧
      ((word t.mem C.B Random.oStatus ≠ 4 ∧ RandomSamplePost C start result t) ∨
       (word t.mem C.B Random.oStatus = 4 ∧ ∃ k < draws, RandomFunctionalInv C start result k t)) := by
  obtain ⟨hdpos, hdbound, used, hr, hstatus, hrel⟩ := hi
  cases draws with
  | zero => omega
  | succ fuel =>
    let n := (VG.Proof.Dsa.significant C.qBytes).1
    have hnfit : n ≤ C.qBytes.length := VG.Proof.Dsa.significant_fits C.qBytes
    by_cases hfull : used + n ≤ C.rand.length
    · refine WP.mono (random_draw_full_result hr hstatus hfull (by omega) (by omega))
        fun t ⟨htr, hts, htv⟩ => ?_
      refine ⟨htr.scr, htr.sp, ?_⟩
      by_cases ha : 0 < randomNextCandidate C used ∧ randomNextCandidate C used < Spec.Dsa.decodeBE C.qBytes
      · rw [decide_eq_true ha, ite_eq_left rfl] at htr hts
        have he := random_remaining_accept hq hfull ha (fuel := fuel)
        have hscalar : result.scalar = some (randomNextCandidate C used) := by rw [hrel.scalar, he]
        have hused : start + result.used = used + n := by
          have h := hrel.consumption
          rw [he] at h
          exact h
        have hst : sampleStatus result = 1 := by rw [hrel.status, he]; rfl
        refine Or.inl ⟨by rw [hts]; decide, ⟨fuel + 1, ?_⟩, ?_, ?_⟩
        · rw [hused]; exact htr
        · rw [hst]; exact hts
        · intro k hk
          rw [hscalar] at hk
          cases hk
          exact htv
      · simp only [ha, decide_false, Bool.false_eq_true, ite_false] at htr hts
        have hnext := hrel.reject hq hfull ha
        cases fuel with
        | zero =>
          have hscalar : result.scalar = none := hnext.scalar
          have hused : start + result.used = used + n := by
            have h := hnext.consumption
            simpa only [randomRemaining, Spec.Dsa.Random.sample, Nat.add_zero] using h
          have hst : sampleStatus result = 0 := hnext.status
          have hzero : word t.mem C.B Random.oStatus = 0 := by simpa only [ite_true] using hts
          refine Or.inl ⟨by rw [hzero]; decide, ⟨0, ?_⟩, ?_, ?_⟩
          · rw [hused]; exact htr
          · rw [hst]; exact hzero
          · intro k hk
            rw [hscalar] at hk
            cases hk
        | succ f =>
          have hfour : word t.mem C.B Random.oStatus = 4 := by
            rw [hts, ite_eq_right (by omega)]
          exact Or.inr ⟨hfour, f + 1, by omega, by omega, by omega,
            used + n, htr, hfour, hnext⟩
    · have hshort : C.rand.length - used < n := by have := hr.usedBound; omega
      refine WP.mono (random_draw_short_ok hr.scr hr.sp hr.randLen hr.usedWord hr.width hr.usedBound
        C.randBound (by have := C.qlen; omega) hshort) fun t ⟨_, htm, hkt⟩ => ?_
      have htr := hr.after_status htm hkt
      have he := random_remaining_short hq hshort (fuel := fuel)
      have hscalar : result.scalar = none := by rw [hrel.scalar, he]
      have hused : start + result.used = used := by
        have h := hrel.consumption
        rw [he] at h
        simpa only [Nat.add_zero] using h
      have hst : sampleStatus result = 2 := by rw [hrel.status, he]; rfl
      have htwo : word t.mem C.B Random.oStatus = 2 := by rw [htm, word_writeW_self]
      refine ⟨htr.scr, htr.sp, Or.inl ⟨by rw [htwo]; decide, ⟨fuel + 1, ?_⟩, ?_, ?_⟩⟩
      · rw [hused]; exact htr
      · rw [hst]; exact htwo
      · intro k hk
        rw [hscalar] at hk
        cases hk

theorem random_sampleLoop_correct {C : RandomContext} {used draws : Nat} {s : State}
    (hq : 1 < Spec.Dsa.decodeBE C.qBytes) (hr : RandomReady C used draws s)
    (hstatus : word s.mem C.B Random.oStatus = 4) (hdpos : 0 < draws) (hdbound : draws ≤ 128) :
    WP isa (.loop (.seq Random.draw (.block (Random.statusTest 4))) (.zero .x .x4)) s (RandomSamplePost C used (randomRemaining C used draws)) := by
  refine random_sampleLoop_rule C.B (RandomFunctionalInv C used (randomRemaining C used draws))
    (RandomSamplePost C used (randomRemaining C used draws)) ?_ ?_
    (functional_draw C used (randomRemaining C used draws) hq)
    (n := draws) ⟨hdpos, hdbound, used, hr, hstatus, rfl, rfl, rfl⟩
  · intro n a b hi hm hk
    obtain ⟨hp, hb, used', hr', hs', hrel⟩ := hi
    exact ⟨hp, hb, used', hr'.congr hm hk, by rw [hm]; exact hs', hrel⟩
  · intro a b hi hm hk
    obtain ⟨⟨draws', hr'⟩, hs', hv⟩ := hi
    exact ⟨⟨draws', hr'.congr hm hk⟩, by rw [hm]; exact hs', fun k he => (hv k he).congr hm⟩

end VG.Proof.Dsa.AArch64
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/RandomNonceEncoding.lean`, which only this module imported.
section

/-! Convert the right-aligned sampled scalar to the signer's nonce encoding. -/
section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64

private theorem decode_padding (bs : List Byte) (n : Nat) :
    Spec.Dsa.decodeBE (List.replicate n 0 ++ bs) = Spec.Dsa.decodeBE bs := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, VG.Proof.Dsa.decodeBE_zero_cons]
    exact ih

theorem random_nonce_encoding {C : RandomContext} {used draws k : Nat} {s : State}
    (hr : RandomReady C used draws s) (hv : RandomNonceValue C k s) :
    Spec.Rsa.bytesAt s.mem (off C.B 200) C.qBytes.length = Spec.Dsa.encodeBE C.qBytes.length k := by
  obtain ⟨copied, hlen, hbytes, hdecode⟩ := hv
  let pad := C.qBytes.length - (VG.Proof.Dsa.significant C.qBytes).1
  let padded := List.replicate pad (0 : Byte) ++ copied
  have hnfit := VG.Proof.Dsa.significant_fits C.qBytes
  have hpLen : padded.length = C.qBytes.length := by
    simp only [padded, List.length_append, List.length_replicate, hlen]
    exact Nat.sub_add_cancel hnfit
  have hpDec : Spec.Dsa.decodeBE padded = k := (decode_padding copied pad).trans hdecode
  have hpBytes : Spec.Rsa.bytesAt s.mem (off C.B 200) C.qBytes.length = padded := by
    apply List.ext_getElem
    · simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range, hpLen]
    · intro i hi hj
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
      have hil : i < C.qBytes.length := by simpa only [hpLen] using hj
      by_cases hip : i < pad
      · have he : off C.B 200 + BitVec.ofNat 64 i = off C.B (200 + i) := by
          simp only [off, BitVec.ofNat_add, BitVec.add_assoc]
        rw [he, hr.padding i hip]
        simp only [padded, List.getElem_append_left (as := List.replicate pad (0 : Byte)) (bs := copied) (i := i) (by simpa only [List.length_replicate] using hip),
          List.getElem_replicate]
      · have htail : i - pad < copied.length := by rw [hlen]; omega
        have he : off C.B 200 + BitVec.ofNat 64 i =
            off C.B (200 + C.qBytes.length - (VG.Proof.Dsa.significant C.qBytes).1) +
              BitVec.ofNat 64 (i - pad) := by
          simp only [off, BitVec.add_assoc, ← BitVec.ofNat_add]
          congr 2
          dsimp only [pad]
          omega
        rw [he, hbytes (i - pad) htail]
        simp only [padded, List.getElem_append_right (as := List.replicate pad (0 : Byte)) (bs := copied) (i := i) (by simpa only [List.length_replicate] using Nat.le_of_not_lt hip),
          List.length_replicate]
  rw [hpBytes, ← hpLen, ← hpDec, VG.Proof.Dsa.encodeBE_decodeBE]

end VG.Proof.Dsa.AArch64
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64 VG.Proof.Dsa.Random

theorem random_sample_init_ready {C : RandomContext} {used draws : Nat} {s t : State}
    (h : RandomReady C used draws s)
    (hm : t.mem = (s.mem.writeW (off C.B Random.oDraws) (128 : BitVec 64)).writeW
      (off C.B Random.oStatus) (4 : BitVec 64)) (hk : Keep [.x0, .x15] s t) :
    RandomReady C used 128 t ∧ word t.mem C.B Random.oStatus = 4 := by
  have hd := writeW_outside s.mem C.B (d := Random.oDraws) (128 : BitVec 64) (by decide)
  have hs := writeW_outside (s.mem.writeW (off C.B Random.oDraws) (128 : BitVec 64)) C.B
    (d := Random.oStatus) (4 : BitVec 64) (by decide)
  have hf : InScr C.B Random.frameBytes s.mem t.mem := by
    rw [hm]
    exact (InScr.of_outside hd (by decide)).trans (InScr.of_outside hs (by decide))
  have hw (d : Nat) (hd' : d + 8 ≤ 160 ∨ 168 ≤ d) (hs' : d + 8 ≤ 192) :
      word t.mem C.B d = word s.mem C.B d := by
    rw [hm, hs.word (Or.inl hs') (by omega_using [hs']), hd.word hd' (by omega_using [hs'])]
  refine ⟨⟨h.scr.congr hk.wr, hk.sp.trans h.sp,
    (hw _ (by decide) (by decide)).trans h.rand, (hw _ (by decide) (by decide)).trans h.randLen,
    (hw _ (by decide) (by decide)).trans h.usedWord, (hw _ (by decide) (by decide)).trans h.width,
    (hw _ (by decide) (by decide)).trans h.qLen, (hw _ (by decide) (by decide)).trans h.mask,
    (hw _ (by decide) (by decide)).trans h.q, ?_, h.randSrc.congrK hf hk, h.qSrc.congrK hf hk,
    h.usedBound, ?_, ?_⟩, ?_⟩
  · rw [hm, hs.word (by decide) (by decide), word_writeW_self]
    rfl
  · rw [hm]
    exact (h.frame.trans (Frm.of_outside (hd.mono (by decide) (by decide))
      (show (160, 72) ∈ randomWriteRanges by decide))).trans
      (Frm.of_outside (hs.mono (by decide) (by decide)) (show (160, 72) ∈ randomWriteRanges by decide))
  · intro i hi
    have ho : ofs C.B (off C.B (200 + i)) = 200 + i := by
      have he : off C.B (200 + i) + BitVec.ofNat 64 0 = off C.B (200 + i) := BitVec.add_zero _
      simpa only [he, Nat.add_zero] using ofs_off C.B (d := 200 + i) (i := 0) (by have := C.qlen; omega_using [hi, this])
    rw [hm, hs _ (by rw [ho]; right; unfold Random.oStatus; omega_using []),
      hd _ (by rw [ho]; right; unfold Random.oDraws; omega_using [])]
    exact h.padding i hi
  · rw [hm, word_writeW_self]

theorem random_sample_correct {C : RandomContext} {used draws : Nat} {s : State}
    (hq : 1 < Spec.Dsa.decodeBE C.qBytes) (hr : RandomReady C used draws s) :
    WP isa Random.sample s fun t =>
      t.gpr .x0 = BitVec.ofNat 64 (sampleStatus (randomRemaining C used 128)) ∧
      RandomSamplePost C used (randomRemaining C used 128) t := by
  unfold Random.sample
  refine WP.seq (WP.mono (WP.keep [.x0, .x15] (Q := fun t =>
      t.mem = (s.mem.writeW (off C.B Random.oDraws) (128 : BitVec 64)).writeW
        (off C.B Random.oStatus) (4 : BitVec 64))
      (by unfold Random.store; brun [exec_addSp (show Random.oDraws < 4096 by decide),
        exec_addSp (show Random.oStatus < 4096 by decide), hr.sp, hr.scr.st (d := Random.oDraws) (by decide),
        hr.scr.st (d := Random.oStatus) (by decide)]
          rfl) rfl rfl rfl)
    fun a ⟨ham, hka⟩ => ?_)
  obtain ⟨har, has⟩ := random_sample_init_ready hr ham hka
  refine WP.seq (WP.mono (random_sampleLoop_correct hq har has (by decide) (by decide))
    fun b hb => ?_)
  obtain ⟨⟨draws', hbr⟩, hbs, hbv⟩ := hb
  refine WP.mono (WP.keep [.x0] (Q := fun t =>
      t.gpr .x0 = BitVec.ofNat 64 (sampleStatus (randomRemaining C used 128)) ∧ t.mem = b.mem)
      (by brun [exec_ldrSp (show Random.oStatus % 8 = 0 ∧ Random.oStatus < 32768 by decide), hbr.sp, hbr.scr.ld (d := Random.oStatus) (by decide), hbs]) rfl rfl rfl)
    fun t ⟨⟨hta, htm⟩, hkt⟩ => ?_
  exact ⟨hta, ⟨draws', hbr.congr htm hkt⟩, by rw [htm]; exact hbs,
    fun k he => (hbv k he).congr htm⟩

/-- The complete sampler returns the specified status and byte consumption,
and a padded nonce suitable for the existing verified signer. -/
theorem random_sample_encoded {C : RandomContext} {used draws : Nat} {s : State}
    (hq : 1 < Spec.Dsa.decodeBE C.qBytes) (hr : RandomReady C used draws s) :
    WP isa Random.sample s fun t =>
      let result := randomRemaining C used 128
      t.gpr .x0 = BitVec.ofNat 64 (sampleStatus result) ∧
      word t.mem C.B Random.oStatus = BitVec.ofNat 64 (sampleStatus result) ∧
      word t.mem C.B Random.oUsed = BitVec.ofNat 64 (used + result.used) ∧
      (∀ k, result.scalar = some k →
        Spec.Rsa.bytesAt t.mem (off C.B 200) C.qBytes.length = Spec.Dsa.encodeBE C.qBytes.length k) ∧
      Frm C.B randomWriteRanges C.initialMem t.mem ∧
      (∃ draws', RandomReady C (used + result.used) draws' t) ∧
      Keep [.x0, .x1, .x2, .x3, .x4, .x8, .x9, .x10, .x12, .x15] s t := by
  refine WP.mono (WP.keep [.x0, .x1, .x2, .x3, .x4, .x8, .x9, .x10, .x12, .x15]
    (random_sample_correct hq hr) (by rfl) rfl rfl) fun t ⟨⟨hta, ⟨draws', htr⟩, hstatus, htv⟩, hkt⟩ => ?_
  exact ⟨hta, hstatus, htr.usedWord, fun k hk => random_nonce_encoding htr (htv k hk), htr.frame,
    ⟨draws', htr⟩, hkt⟩

end VG.Proof.Dsa.AArch64
