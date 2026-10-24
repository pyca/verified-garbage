module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Cut
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Sel
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.Body
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicFn
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# `vg_ffdh_generate_key` on PPC64LE: x from `rand`

`scalar_ok`: the bound's octets (q's at `D + 2 k`, or p's at `D`: `bptr`)
scanned for the first nonzero one, its bits smeared, and `rand`'s `k` octets
(the header's word 11) cut there into x (the header's word 8).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.GenerateKey

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain
open VG.Impl.Ffdh.PPC64LE.GenerateKey
open VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE VG.Proof.Ffdh.KeyScalar
open VG.Proof.Bignum (slot)

/-- The bound's octets: q's, or p's without q. -/
def bptr (D : Addr) (k L : Nat) : Addr := if L = 3 * k then off D (2 * k) else D

/-- The octet x's cut ands at the bound's first nonzero one. -/
def smeared (bd : List Byte) : Byte := BitVec.ofNat 8 (smearN (bd.getD (lead bd) 0).toNat)

/-- The registers `scalar` writes. -/
def scalarRegs : List Reg :=
  [.r0, .r4, .r6, .r9, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r24, .r25]

/-- `boundPtr`: `r12 :=` the bound's octets. -/
theorem boundPtr_ok {s : State} {D : Addr} {k L : Nat} (h21 : s.gpr .r21 = D)
    (h27 : s.gpr .r27 = BitVec.ofNat 64 L) (h28 : s.gpr .r28 = BitVec.ofNat 64 k) (hL : L < 2 ^ 63)
    (hk32 : k < 2 ^ 32) :
    WP isa boundPtr s fun t => (t.gpr .r12 = off (bptr D k L) 0 ∧ t.mem = s.mem) ∧ Keep [.r0, .r12] s t := by
  unfold boundPtr
  refine WP.seq (WP.mono (WP.keep [.r0] (Q := fun t => (t.gpr .r0 == 0) = decide (L = 3 * k) ∧
    t.mem = s.mem) (by
      unfold hasQ
      prun [h27, h28]
      exact Domain.sub_3k_zero hL hk32) (by decide)) fun s₁ ⟨⟨a0, m1⟩, k1⟩ => ?_)
  refine WP.ite (s₁.gpr .r0 == 0) (eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · rw [a0, decide_eq_true_eq] at hb
    refine WP.mono (WP.keep [.r12] (Q := fun t => t.gpr .r12 = off (bptr D k L) 0 ∧ t.mem = s₁.mem) (by
        prun [(k1.gpr .r21 (by decide)).trans h21, (k1.gpr .r28 (by decide)).trans h28, shl1_ofNat,
          BitVec.add_zero, bptr, hb]
        exact BitVec.add_comm _ _) (by decide)) fun t ⟨⟨a12, mt⟩, kt⟩ =>
      ⟨⟨a12, mt.trans m1⟩, (k1.trans kt).mono (by decide)⟩
  · rw [a0, decide_eq_false_iff_not] at hb
    refine WP.mono (WP.keep [.r12] (Q := fun t => t.gpr .r12 = off (bptr D k L) 0 ∧ t.mem = s₁.mem) (by
        prun [(k1.gpr .r21 (by decide)).trans h21, BitVec.add_zero, bptr, hb]) (by decide)) fun t ⟨⟨a12, mt⟩, kt⟩ =>
      ⟨⟨a12, mt.trans m1⟩, (k1.trans kt).mono (by decide)⟩

/-- `scalar`: x's `k` octets at `X` are `rand`'s at `R` cut at the bound's
first nonzero octet. -/
theorem scalar_ok {s : State} {B D X R : Addr} {Z w k L : Nat} (h : Env s B Z w) (h23 : s.gpr .r23 = B)
    (h21 : s.gpr .r21 = D) (h27 : s.gpr .r27 = BitVec.ofNat 64 L) (h28 : s.gpr .r28 = BitVec.ofNat 64 k)
    (hk : 64 ≤ k) (hk' : k ≤ 1024) (hL : L = 2 * k ∨ L = 3 * k)
    (hX : s.mem.readW (off B 64) 64 = off X 0) (hR : s.mem.readW (off B 88) 64 = off R 0)
    (hrdD : ∀ i < L, InRegions (s.rd ++ s.wr) (off D i) 1) (hrdR : ∀ i < k, InRegions (s.rd ++ s.wr) (off R i) 1)
    (hx : Scr s X k) (hsepR : ∀ i < k, ∀ y, ofs X y < k → off R i ≠ y) :
    WP isa scalar s fun t =>
      (Spec.Rsa.bytesAt t.mem X k = cut (Spec.Rsa.bytesAt s.mem R k)
          (lead (Spec.Rsa.bytesAt s.mem (bptr D k L) k)) (smeared (Spec.Rsa.bytesAt s.mem (bptr D k L) k)) ∧
        Outside X 0 k s.mem t.mem) ∧ Keep scalarRegs s t := by
  have hZ := h.hZ
  have e28 := Domain.slot_eq w 28
  have hrdP : ∀ i < k, InRegions (s.rd ++ s.wr) (off (bptr D k L) i) 1 := fun i hi => by
    unfold bptr
    split
    · rw [Domain.off_off']; exact hrdD _ (by omega)
    · exact hrdD _ (by omega)
  unfold scalar
  refine WP.seq (WP.mono (boundPtr_ok h21 h27 h28 (by omega) (by omega)) fun s₁ ⟨⟨a12, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (scan_ok (k := k) (by omega) (by omega) (by rw [k1.rd, k1.wr]; exact hrdP) a12
    ((k1.gpr .r28 (by decide)).trans h28)) fun s₁' hl => WP.seq (WP.mono hl fun s₂ ⟨⟨a9, a14, m2⟩, k2⟩ => ?_))
  rw [m1] at a9 a14
  have k12 := k1.trans k2
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (smear_ok s₂ a14) fun s₃ ⟨⟨b14, m3⟩, k3⟩ => ?_
  have k13 := k12.trans k3
  have hs3 := h.hs.congr k13.wr
  refine WP.mono (WP.keep [.r4, .r6, .r24, .r25] (Q := fun t => t.gpr .r24 = off R 0 ∧ t.gpr .r25 = off X 0 ∧
      t.gpr .r6 = BitVec.ofNat 64 k ∧ t.gpr .r4 = BitVec.ofNat 64 0 ∧ t.mem = s₃.mem) (by
    unfold cutSetup
    prun [(k13.gpr .r23 (by decide)).trans h23, (k13.gpr .r28 (by decide)).trans h28,
      hs3.ld (d := 88) (n := 8) (by omega), hs3.ld (d := 64) (n := 8) (by omega), BitVec.add_zero,
      show s₃.mem.readW (off B 88) 64 = off R 0 by rw [m3, m2, m1]; exact hR,
      show s₃.mem.readW (off B 64) 64 = off X 0 by rw [m3, m2, m1]; exact hX]) (by decide))
    fun s₄ ⟨⟨c24, c25, c6, c4, m4⟩, k4⟩ => ?_
  have k14 := k13.trans k4
  have hm4 : s₄.mem = s.mem := by rw [m4, m3, m2, m1]
  refine WP.mono (cut_ok (R := R) (X := X) (k := k) (ld := lead (Spec.Rsa.bytesAt s.mem (bptr D k L) k))
    (tb := smeared (Spec.Rsa.bytesAt s.mem (bptr D k L) k)) (by omega) (by omega) ?_ (hx.congr k14.wr)
    (by rw [k14.rd, k14.wr]; exact hrdR) hsepR c24 c25 c4 ?_ ?_ c6) fun t ⟨⟨tb, tout⟩, kt⟩ => ?_
  · have hl : (Spec.Rsa.bytesAt s.mem (bptr D k L) k).length = k := by simp [Spec.Rsa.bytesAt]
    have hne : Spec.Rsa.bytesAt s.mem (bptr D k L) k ≠ [] := fun he => by rw [he] at hl; simp at hl; omega
    have := Proof.Ffdh.lead_lt hne
    omega
  · rw [k4.gpr .r9 (by decide), k3.gpr .r9 (by decide), a9]
  · rw [k4.gpr .r14 (by decide), b14]; rfl
  · rw [hm4] at tb tout
    exact ⟨⟨tb, tout⟩, (k14.trans kt).mono (by decide)⟩

theorem status_mask : ∀ n < 4, 1 ≤ n →
    (0#64 - (BitVec.ofNat 64 n - 1#64) ||| BitVec.ofNat 64 n - 1#64) >>> 63 - 1#64 = mask (decide (n = 1)) := by
  decide

/-- `maskX`: x's `k` octets (the header's word 8) kept for the status 1 in
`r3`, zeros for 2 and 3. -/
theorem maskX_ok {s : State} {B X : Addr} {Z k st : Nat} (hs : Scr s B Z) (hZ : 72 ≤ Z) (h23 : s.gpr .r23 = B)
    (h28 : s.gpr .r28 = BitVec.ofNat 64 k) (hX : s.mem.readW (off B 64) 64 = off X 0) (hk1 : 1 ≤ k)
    (hk : k < 2 ^ 32) (hx : Scr s X k) (h3 : s.gpr .r3 = BitVec.ofNat 64 st) (hst1 : 1 ≤ st) (hst : st < 4) :
    WP isa maskX s fun t =>
      (Spec.Rsa.bytesAt t.mem X k = (if st = 1 then Spec.Rsa.bytesAt s.mem X k else List.replicate k 0) ∧
        Outside X 0 k s.mem t.mem) ∧ Keep [.r0, .r6, .r12, .r16, .r17, .r25] s t := by
  unfold maskX
  refine WP.seq (WP.mono (WP.keep [.r0, .r6, .r12, .r17, .r25] (Q := fun t => t.gpr .r25 = off X 0 ∧
      t.gpr .r17 = mask (decide (st = 1)) ∧ t.gpr .r6 = BitVec.ofNat 64 k ∧ t.mem = s.mem) (by
    unfold statusMask
    prun [h3, h23, h28, hs.ld (d := 64) (n := 8) (by omega), hX, BitVec.add_zero, status_mask st hst hst1])
    (by decide)) fun u ⟨⟨u25, u17, u6, um⟩, ku⟩ => ?_)
  refine WP.mono (masked_ok hk1 hk (hx.congr ku.wr) u25 u17 u6) fun t ⟨⟨tb, tout⟩, kt⟩ => ?_
  rw [um] at tout tb
  refine ⟨⟨?_, tout⟩, (ku.trans kt).mono (by decide)⟩
  rw [tb]
  by_cases h : st = 1 <;> simp [h]

end VG.Proof.Ffdh.PPC64LE.GenerateKey
