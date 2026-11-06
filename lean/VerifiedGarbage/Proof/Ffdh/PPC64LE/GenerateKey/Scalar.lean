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

The bound's octets (q's at `D + 2 k`, or p's at `D`: `bptr`, `boundPtr_ok`),
the pointers from the header (`ptrs_ok`), and x masked by the status being 1
(`maskX_ok`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.GenerateKey

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain
open VG.Impl.Ffdh.PPC64LE.GenerateKey
open VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE VG.Proof.Ffdh.KeyScalar
open VG.Proof.Bignum (slot)

/-- The bound's octets: q's, or p's without q. -/
def bptr (D : Addr) (k L : Nat) : Addr := if L = 3 * k then off D (2 * k) else D

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

/-- `ptrs`: `rand`'s and x's addresses from the header's words 11 and 8. -/
theorem ptrs_ok {s : State} {B X R : Addr} {Z : Nat} (hs : Scr s B Z) (hZ : 96 ≤ Z) (h23 : s.gpr .r23 = B)
    (hX : s.mem.readW (off B 64) 64 = off X 0) (hR : s.mem.readW (off B 88) 64 = off R 0) :
    WP isa (.block ptrs) s fun t =>
      (t.gpr .r24 = off R 0 ∧ t.gpr .r25 = off X 0 ∧ t.mem = s.mem) ∧ Keep [.r24, .r25] s t := by
  refine WP.keep _ ?_ (by decide)
  unfold ptrs
  prun [h23, hs.ld (d := 88) (n := 8) (by omega), hs.ld (d := 64) (n := 8) (by omega), BitVec.add_zero, hX, hR]

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
