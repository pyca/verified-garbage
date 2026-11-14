module

public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import VerifiedGarbage.Impl.Dsa.X86_64.Random
public import VerifiedGarbage.Proof.Dsa.DomainShape
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Dsa.X86_64.RandomMemory
import VerifiedGarbage.Proof.Dsa.RandomEncoding
import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.Dsa.RandomRange
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Framework.Semantics
import Batteries.Tactic.Init
import Batteries.Tactic.PermuteGoals
import Batteries.Tactic.SeqFocus
import VerifiedGarbage.Impl.Dsa.Layout
import VerifiedGarbage.Impl.Rsa.X86_64.Crt
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame

/-! ### `Dsa.X86_64.RandomRange`, which only this module used -/

section

/-! Correctness of the sampler's right-to-left range check. -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/RandomBorrow.lean`, which only this module imported.
section

/-! Byte-subtraction lemma used by the scalar range check. -/
section
namespace VG.Proof.Dsa.X86_64

/-- For byte-sized operands (including an incoming borrow), the high bit of
64-bit subtraction is precisely the unsigned borrow. -/
theorem random_byte_borrow (a b : BitVec 64) (ha : a.toNat ≤ 255) (hb : b.toNat ≤ 256) :
    ((a - b) >>> 63).toNat = if a.toNat < b.toNat then 1 else 0 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub]
  split <;> omega

open VG VG.X86_64 VG.Proof.MlKem.X86_64

end VG.Proof.Dsa.X86_64
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64

/-- A byte comparison advances both pointers, preserves memory, and computes
both the subtraction borrow and the nonzero accumulator. -/
theorem random_rangeByte_ok {s : State} {p q : Addr} {a b : Byte} {n c : Nat}
    (hp : s.gpr .rdx = p + 1) (hq : s.gpr .r10 = q + 1)
    (hn : s.gpr .r11 = BitVec.ofNat 64 n) (h8 : s.gpr .r8 = BitVec.ofNat 64 c)
    (hc : c ≤ 1) (hnpos : 0 < n) (hnb : n < 2 ^ 64)
    (hrp : InRegions (s.rd ++ s.wr) p 1) (hrq : InRegions (s.rd ++ s.wr) q 1)
    (ha : s.mem p = a) (hb : s.mem q = b) :
    WP isa (.block Random.rangeByte) s fun t =>
      t.gpr .rdx = p ∧ t.gpr .r10 = q ∧ t.gpr .r11 = BitVec.ofNat 64 (n - 1) ∧
      (t.gpr .r8).toNat = (if a.toNat < b.toNat + c then 1 else 0) ∧
      t.gpr .r9 = s.gpr .r9 ||| a.setWidth 64 ∧
      t.zf = some (decide (n = 1)) ∧ t.mem = s.mem ∧
      Keep [.rax, .rcx, .rdx, .r8, .r9, .r10, .r11] s t := by
  have hac : (a.setWidth 64).toNat = a.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := a.isLt; omega_arith)]
  have hbc : (b.setWidth 64).toNat = b.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega_arith)]
  have hcc : (BitVec.ofNat 64 c).toNat = c := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  have hadd : (b.setWidth 64 + BitVec.ofNat 64 c).toNat = b.toNat + c := by
    rw [BitVec.toNat_add, hbc, hcc, Nat.mod_eq_of_lt (by have := b.isLt; omega_arith)]
  have hborrow := random_byte_borrow (a.setWidth 64) (b.setWidth 64 + BitVec.ofNat 64 c)
    (by rw [hac]; have := a.isLt; omega_arith) (by rw [hadd]; have := b.isLt; omega_arith)
  rw [hac, hadd] at hborrow
  have he : (BitVec.ofNat 64 (n - 1) == 0) = decide (n = 1) := by
    rw [ofNat64_beq_zero (by omega_arith)]
    exact decide_eq_decide.mpr (by omega_arith)
  refine WP.mono (WP.keep [.rax, .rcx, .rdx, .r8, .r9, .r10, .r11] (Q := fun t =>
      t.gpr .rdx = p ∧ t.gpr .r10 = q ∧ t.gpr .r11 = BitVec.ofNat 64 (n - 1) ∧
      (t.gpr .r8).toNat = (if a.toNat < b.toNat + c then 1 else 0) ∧
      t.gpr .r9 = s.gpr .r9 ||| a.setWidth 64 ∧
      t.zf = some (decide (n = 1)) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨htp, htq, htn, htc, hta, htz, htm⟩, hkt⟩ =>
      ⟨htp, htq, htn, htc, hta, htz, htm, hkt⟩
  unfold Random.rangeByte Random.borrow
  xrun [List.append_assoc, List.cons_append, List.nil_append, State.ea,
    hp, hq, hn, h8, BitVec.add_sub_cancel, show BitVec.ofInt 64 0 = 0#64 from rfl,
    BitVec.add_zero, hrp, hrq, ha, hb, hborrow, ofNat64_pred hnpos hnb, he]

structure RandomRangeInv (s : State) (p q : Addr) (as bs : List Byte) (j : Nat) (t : State) : Prop where
  keep : Keep [.rax, .rcx, .rdx, .r8, .r9, .r10, .r11] s t
  ptrA : t.gpr .rdx = p + BitVec.ofNat 64 (as.length - j)
  ptrB : t.gpr .r10 = q + BitVec.ofNat 64 (as.length - j)
  count : t.gpr .r11 = BitVec.ofNat 64 (as.length - j)
  borrow : (t.gpr .r8).toNat = VG.Proof.Dsa.randomBorrow (as.drop (as.length - j)) (bs.drop (as.length - j))
  accum : t.gpr .r9 = VG.Proof.Dsa.randomOr (as.drop (as.length - j))
  mem : t.mem = s.mem

/-- The entire right-to-left loop computes the borrow and OR accumulator. -/
theorem random_rangeLoop_ok {s : State} {p q : Addr} {as bs : List Byte}
    (hlen : as.length = bs.length) (hpos : 0 < as.length) (hbound : as.length < 2 ^ 64)
    (hp : s.gpr .rdx = p + BitVec.ofNat 64 as.length)
    (hq : s.gpr .r10 = q + BitVec.ofNat 64 as.length)
    (hn : s.gpr .r11 = BitVec.ofNat 64 as.length)
    (h8 : s.gpr .r8 = 0) (h9 : s.gpr .r9 = 0)
    (hra : ∀ i < as.length, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 i) 1)
    (hrb : ∀ i < as.length, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 i) 1)
    (hva : ∀ i (h : i < as.length), s.mem (p + BitVec.ofNat 64 i) = as[i])
    (hvb : ∀ i (h : i < bs.length), s.mem (q + BitVec.ofNat 64 i) = bs[i]) :
    WP isa (.loop (.block Random.rangeByte) .ne) s fun t =>
      (t.gpr .r8).toNat = VG.Proof.Dsa.randomBorrow as bs ∧
      t.gpr .r9 = VG.Proof.Dsa.randomOr as ∧ t.mem = s.mem ∧
      Keep [.rax, .rcx, .rdx, .r8, .r9, .r10, .r11] s t := by
  refine WP.mono (wp_upto (a := 0) (N := as.length) hpos (RandomRangeInv s p q as bs) ?_
      (fun _ h => h) ?_) fun t ht => ?_
  · intro j _ hj t ht
    let i := as.length - (j + 1)
    have hi : i < as.length := by dsimp only [i]; omega_arith
    have hib : i < bs.length := by omega_arith
    have hij : i + 1 = as.length - j := by dsimp only [i]; omega_arith
    have hpa : t.gpr .rdx = (p + BitVec.ofNat 64 i) + 1 := by
      rw [ht.ptrA, BitVec.add_assoc, ofNat_add_one, hij]
    have hpb : t.gpr .r10 = (q + BitVec.ofNat 64 i) + 1 := by
      rw [ht.ptrB, BitVec.add_assoc, ofNat_add_one, hij]
    have ht8 : t.gpr .r8 = BitVec.ofNat 64
        (VG.Proof.Dsa.randomBorrow (as.drop (as.length - j)) (bs.drop (as.length - j))) := by
      rw [← ht.borrow, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    refine WP.mono (random_rangeByte_ok (a := as[i]) (b := bs[i]) hpa hpb ht.count ht8 (VG.Proof.Dsa.randomBorrow_le _ _)
      (by omega_arith) (by omega_arith)
      (by rw [ht.keep.2.1, ht.keep.2.2]; exact hra i hi)
      (by rw [ht.keep.2.1, ht.keep.2.2]; exact hrb i hi)
      (by rw [ht.mem]; exact hva i hi) (by rw [ht.mem]; exact hvb i hib))
      fun u ⟨hup, huq, hun, hub, hua, huz, hum, hku⟩ => ?_
    refine ⟨?_, (ht.keep.trans hku).mono (by decide), hup, huq, ?_, ?_, ?_, hum.trans ht.mem⟩
    · rw [huz]
      congr 1
      exact decide_eq_decide.mpr (by omega_arith)
    · rw [hun, show as.length - j - 1 = as.length - (j + 1) by omega_arith]
    · change (u.gpr .r8).toNat = VG.Proof.Dsa.randomBorrow (as.drop i) (bs.drop i)
      rw [List.drop_eq_getElem_cons hi, List.drop_eq_getElem_cons hib, VG.Proof.Dsa.randomBorrow, hij]
      exact hub
    · change u.gpr .r9 = VG.Proof.Dsa.randomOr (as.drop i)
      rw [List.drop_eq_getElem_cons hi, VG.Proof.Dsa.randomOr, hij, hua, ht.accum]
  · refine ⟨Keep.refl _ _, by simpa using hp, by simpa using hq, by simpa using hn, ?_, ?_, rfl⟩
    · rw [Nat.sub_zero, List.drop_length, hlen, List.drop_length, h8]
      rfl
    · simp only [Nat.sub_zero, List.drop_length, VG.Proof.Dsa.randomOr, h9]
  · refine ⟨?_, ?_, ht.mem, ht.keep⟩
    · simpa only [Nat.sub_self, List.drop_zero] using ht.borrow
    · simpa only [Nat.sub_self, List.drop_zero] using ht.accum

/-- The branch after range checking reveals only the combined accept bit. -/
theorem random_rangeFinish_ok {s : State} {a b : Nat}
    (h8 : s.gpr .r8 = BitVec.ofNat 64 (if a < b then 1 else 0))
    (h9 : (s.gpr .r9 == 0) = decide (a = 0)) :
    WP isa (.block Random.rangeFinish) s fun t =>
      t.zf = some (!(decide (0 < a ∧ a < b))) ∧ t.mem = s.mem ∧
      Keep [.rax, .r8, .r9] s t := by
  refine WP.mono (WP.keep [.rax, .r8, .r9] (Q := fun t =>
      t.zf = some (!(decide (0 < a ∧ a < b))) ∧ t.mem = s.mem) ?_ rfl)
    fun _ ⟨h, hk⟩ => ⟨h.1, h.2, hk⟩
  unfold Random.rangeFinish
  by_cases hz : a = 0
  · have he : ¬ 0 < a := by omega_arith
    by_cases hl : a < b <;> xrun [execCmov, eval, show BitVec.signExtend 64 (0 : BitVec 32) = 0 from rfl,
      BitVec.and_self, h8, h9, hz, he, hl] <;> simp
  · have he : 0 < a := by omega_arith
    by_cases hl : a < b <;> xrun [execCmov, eval, show BitVec.signExtend 64 (0 : BitVec 32) = 0 from rfl,
      BitVec.and_self, h8, h9, hz, he, hl] <;> simp

end VG.Proof.Dsa.X86_64

end

end

/-! Range-check a copied candidate against a possibly zero-padded modulus. -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/RandomInRange.lean`, which only this module imported.
section

/-! Whole range-check correctness, including reads of the sampler's frame. -/
section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

theorem random_inRange_ok {s : State} {B p q : Addr} {l : Nat} {as bs : List Byte}
    (hs : Scr s B Random.frameBytes) (hsp : s.gpr .rsp = B)
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
      t.zf = some (!(decide (0 < Spec.Dsa.decodeBE as ∧ Spec.Dsa.decodeBE as < Spec.Dsa.decodeBE bs))) ∧
      t.mem = s.mem ∧ Keep [.rax, .rcx, .rdx, .r8, .r9, .r10, .r11] s t := by
  unfold Random.inRange
  refine WP.seq (WP.mono (random_rangeInit_ok hs hsp hl hn hq)
    fun u ⟨hup, huq, hun, hu8, hu9, hum, hku⟩ => ?_)
  refine WP.seq (WP.mono (random_rangeLoop_ok (as := as) (bs := bs) hlen hpos hbound
    (hup.trans hp.symm) huq hun hu8 hu9
    (fun i hi => by rw [hku.2.1, hku.2.2]; exact hra i hi)
    (fun i hi => by rw [hku.2.1, hku.2.2]; exact hrb i hi)
    (fun i hi => by rw [hum]; exact hva i hi)
    (fun i hi => by rw [hum]; exact hvb i hi))
    fun v ⟨hv8, hv9, hvm, hkv⟩ => ?_)
  have hb : v.gpr .r8 = BitVec.ofNat 64
      (if Spec.Dsa.decodeBE as < Spec.Dsa.decodeBE bs then 1 else 0) := by
    rw [← VG.Proof.Dsa.randomBorrow_eq as bs hlen, ← hv8, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hz : (v.gpr .r9 == 0) = decide (Spec.Dsa.decodeBE as = 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq, hv9]
    exact VG.Proof.Dsa.randomOr_zero as
  refine WP.mono (random_rangeFinish_ok hb hz) fun t ⟨htz, htm, hkt⟩ =>
    ⟨htz, (htm.trans hvm).trans hum, ((hku.trans hkv).trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

theorem random_check_candidate_ok {s : State} {B Q : Addr} {qBytes copied : List Byte} {k : Nat}
    (hs : Scr s B Random.frameBytes) (hsp : s.gpr .rsp = B)
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
      t.zf = some (!decide (0 < k ∧ k < Spec.Dsa.decodeBE qBytes)) ∧ t.mem = s.mem ∧
      Keep [.rax, .rcx, .rdx, .r8, .r9, .r10, .r11] s t := by
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
    obtain ⟨r, hr, hc⟩ := hs.st8 (d := 200 + qBytes.length - n + i) (by
      unfold Random.frameBytes; omega_using [hqlen, hclen, hnfit, hi])
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (random_inRange_ok hs hsp hl (by rw [hclen]; exact hn) hq hp hlen
    (by omega_using [hpos, hclen]) (by omega) hra (fun i hi => hslice.rd i (by omega_using [hlen, hi])) hcv hslice.val)
    fun t ⟨htz, htm, htk⟩ => ⟨?_, htm, htk⟩
  rw [htz, hcdec, VG.Proof.Dsa.random_significant_drop]

end VG.Proof.Dsa.X86_64
