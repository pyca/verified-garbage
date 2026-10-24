module

import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Label
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Written
public import VerifiedGarbage.Proof.RsaOaep.Scan
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Loops
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mgf1.Bytes
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Hash
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Base
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.PrivCall

/-!
# RSAES-OAEP decryption on PPC64LE: the outputs

Untrusted: everything here is checked by Lean. `okMask_ok`: `ok`, all ones
iff the private operation's result is 1 and the accumulator zero (`x ≠ 0`
from the top bit of `x ∨ -x`); `outLoop_ok`: the buffer's first `k` bytes
ANDed with it to `out`; `decRet_ok`: the length and the result;
`decFail_ok`: zeros, and the result `r = 2 ? 2 : 0`. From `out` on, `Base`
does not hold (`out` is not ours): the caller's registers in their slots
(`Saves`) do.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec VG.WriteBytes
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_li wp_mov wp_addi wp_subi wp_add wp_sub wp_and wp_or wp_xor
  wp_lsr wp_lbz wp_stb wp_std wp_nil wp_countdown byte_setWidth64 ofNat_succ')
open VG.Proof.RsaPkcs1Sig (bytesAt_length writeBytes_out)
open VG.Proof.RsaOaep (mk)
open VG.Proof.Mgf1 (ifp ifn)

/-! ## Bits -/

/-- `(x ∨ -x) >>> 63`: 0 if `x = 0`, 1 if not. -/
theorem nzbit (x : BitVec 64) : ((BitVec.ofNat 64 0 - x) ||| x) >>> 63 = if x = 0 then 0#64 else 1#64 := by
  by_cases hx : x = 0
  · subst hx; decide
  · rw [ifn hx]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_or, Nat.shiftRight_eq_div_pow]
    have h0 : x.toNat ≠ 0 := fun h => hx (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
    have hl := x.isLt
    have hs : (BitVec.ofNat 64 0 - x).toNat = 2 ^ 64 - x.toNat := by
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    have h1 : 2 ^ 63 ≤ ((BitVec.ofNat 64 0 - x).toNat ||| x.toNat) := by
      rcases Nat.lt_or_ge x.toNat (2 ^ 63) with h | h
      · exact Nat.le_trans (by rw [hs]; omega) Nat.left_le_or
      · exact Nat.le_trans h Nat.right_le_or
    have h2 : ((BitVec.ofNat 64 0 - x).toNat ||| x.toNat) < 2 ^ 64 := Nat.or_lt_two_pow (BitVec.isLt _) hl
    rw [Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]; rfl

/-- `ok` from the result `rc` and the accumulator `x`. -/
theorem okbits {rc : Nat} (hrc : rc ≤ 2) (x : BitVec 64) :
    BitVec.ofNat 64 0 - ((((BitVec.ofNat 64 rc ^^^ BitVec.ofNat 64 1) - BitVec.ofNat 64 1) >>> 63) &&&
      ((((BitVec.ofNat 64 0 - x) ||| x) >>> 63) ^^^ BitVec.ofNat 64 1)) = mk (rc = 1 ∧ x = 0) := by
  rw [nzbit]
  by_cases hx : x = 0
  · rw [ifp hx, mk]
    rcases (by omega : rc = 0 ∨ rc = 1 ∨ rc = 2) with rfl | rfl | rfl <;> simp only [hx] <;> decide
  · rw [ifn hx, mk, ifn (fun h => hx h.2)]
    rcases (by omega : rc = 0 ∨ rc = 1 ∨ rc = 2) with rfl | rfl | rfl <;> decide

/-- The result's fault bit: 2 if `rc = 2`, 0 if not. -/
theorem faultbits {rc : Nat} (hrc : rc ≤ 2) :
    let f := ((BitVec.ofNat 64 rc ^^^ BitVec.ofNat 64 2) - BitVec.ofNat 64 1) >>> 63
    f + f = if rc = 2 then 2#64 else 0#64 := by
  rcases (by omega : rc = 0 ∨ rc = 1 ∨ rc = 2) with rfl | rfl | rfl <;> decide

/-- `Saves` of the entry state with other memory is `Saves` of the entry state. -/
theorem Saves.ofMem {s t : State} {m : Mem} (h : Saves (withMem s m) t) : Saves s t := ⟨h.sp, h.wr, h.hi, h.sv, h.ls⟩

/-- `r6` bytes from `r4` to `r5`, each ANDed with `r26`, for `r6 > 0`. -/
theorem andCopy_ok {u : State} {p q : Addr} {n : Nat} {msk : BitVec 64} (hn : 0 < n) (hn' : n < 2 ^ 64)
    (h4 : u.gpr .r4 = q) (h5 : u.gpr .r5 = p) (h6 : u.gpr .r6 = BitVec.ofNat 64 n) (h26 : u.gpr .r26 = msk)
    (hr : ∀ j < n, InRegions (u.rd ++ u.wr) (q + BitVec.ofNat 64 j) 1)
    (hw : ∀ i < n, InRegions u.wr (p + BitVec.ofNat 64 i) 1)
    (hd : ∀ j < n, ∀ i < n, q + BitVec.ofNat 64 j ≠ p + BitVec.ofNat 64 i) :
    WP isa (.loop (.block [.lbz .r7 .r4 0, .logic .and .r7 .r7 .r26, .stb .r7 .r5 0, .addi .r4 .r4 1,
      .addi .r5 .r5 1, .subi .r6 .r6 1]) (.nonzero .d .r6)) u fun t => Keep [.r7, .r4, .r5, .r6] u t ∧
      t.mem = writeBytes u.mem p ((Spec.Rsa.bytesAt u.mem q n).map fun b => andB b msk) := by
  refine WP.mono (wp_countdown (cnt := .r6) hn' hn
    (fun i t => Keep [.r7, .r4, .r5, .r6] u t ∧
      t.mem = writeBytes u.mem p (((Spec.Rsa.bytesAt u.mem q n).map fun b => andB b msk).take i) ∧
      t.gpr .r5 = p + BitVec.ofNat 64 i ∧ t.gpr .r4 = q + BitVec.ofNat 64 i) ?_
    ⟨Keep.refl _ _, by simp [writeBytes_nil], by simp [h5], by simp [h4]⟩ h6) fun t h => ⟨h.1, ?_⟩
  · intro i hi t ⟨hK, hm, h5', h4'⟩ _
    have hR : InRegions (t.rd ++ t.wr) (t.gpr .r4 + BitVec.ofNat 64 0) 1 := by
      rw [h4', hK.rd, hK.wr, BitVec.add_zero]; exact hr _ hi
    have hv : t.mem (q + BitVec.ofNat 64 i) = u.mem (q + BitVec.ofNat 64 i) := by
      rw [hm, writeBytes_out _ _ _ _ n (fun i' hi' => hd i hi i' hi')
        (by simp only [List.length_take, List.length_map, bytesAt_length]; omega)]
    refine wp_lbz rfl hR fun s₁ o₁ e₁ => wp_and fun s₂ o₂ e₂ => ?_
    have hA : InRegions s₂.wr (s₂.gpr .r5 + BitVec.ofNat 64 0) 1 := by
      rw [o₂.wr, o₁.wr, o₂.get .r5, o₁.get .r5, h5', hK.wr, BitVec.add_zero]; exact hw _ hi
    refine wp_stb rfl hA fun s₃ m₃ => ?_
    refine wp_addi fun s₄ o₄ e₄ => ?_
    refine wp_addi fun s₅ o₅ e₅ => ?_
    refine wp_subi fun s₆ o₆ e₆ => wp_nil ?_
    have hK' : Keep [.r7, .r4, .r5, .r6] t s₆ :=
      (o₁.keep.trans (o₂.keep.trans (m₃.keep.trans (o₄.keep.trans (o₅.keep.trans o₆.keep))))).mono
    have hlt : (((Spec.Rsa.bytesAt u.mem q n).map fun b => andB b msk).take i).length = i := by
      simp [bytesAt_length]; omega
    have hget : ((Spec.Rsa.bytesAt u.mem q n).map fun b => andB b msk)[i]'(by simp [bytesAt_length]; omega) =
        andB (u.mem (q + BitVec.ofNat 64 i)) msk := by
      simp [Spec.Rsa.bytesAt]
    refine ⟨⟨(hK.trans hK').mono, ?_, ?_, ?_⟩, ?_⟩
    · rw [o₆.mem, o₅.mem, o₄.mem, m₃.mem, o₂.mem, o₁.mem, hm, List.take_succ_eq_append_getElem
        (by simp [bytesAt_length]; omega), writeBytes_snoc _ _ _ _ (by omega), hlt, hget]
      congr 1
      · rw [o₂.get .r5, o₁.get .r5, h5', BitVec.add_zero]
      · rw [e₂, e₁, o₁.get .r26, hK.get .r26, h26, h4', BitVec.add_zero, hv]; rfl
    · rw [o₆.get .r5, e₅, o₄.get .r5, m₃.gpr, o₂.get .r5, o₁.get .r5, h5', ofNat_succ']
    · rw [o₆.get .r4, o₅.get .r4, e₄, m₃.gpr, o₂.get .r4, o₁.get .r4, h4', ofNat_succ']
    · rw [e₆, o₅.get .r6, o₄.get .r6, m₃.gpr, o₂.get .r6, o₁.get .r6]
  · rw [List.take_of_length_le (by simp [bytesAt_length])] at h
    exact h.2.1

section
variable {s : State} (P : PreD s) {m : Mem} {rc : Nat}
include P

/-- `ok` (`r26`). -/
theorem okMask_ok {t : State} (h : Base (SD s) (VD s rc) (withMem s m) t) (hrc : rc ≤ 2) :
    WP isa (.block okMask) t fun t' => Base (SD s) (VD s rc) (withMem s m) t' ∧ t'.mem = t.mem ∧
      (∀ r ∉ [Reg.r4, .r5, .r6, .r26], t'.gpr r = t.gpr r) ∧ t'.gpr .r26 = mk (rc = 1 ∧ t.gpr .r24 = 0) := by
  have PF := fitsM (m := m) P
  refine wp_li (by decide) fun t₁ o₁ e₁ => wp_xor fun t₂ o₂ e₂ => wp_subi fun t₃ o₃ e₃ =>
    wp_lsr fun t₄ o₄ e₄ => wp_li (by decide) fun t₅ o₅ e₅ => wp_sub fun t₆ o₆ e₆ => wp_or fun t₇ o₇ e₇ =>
    wp_lsr fun t₈ o₈ e₈ => wp_li (by decide) fun t₉ o₉ e₉ => wp_xor fun t₁₀ o₁₀ e₁₀ =>
    wp_and fun t₁₁ o₁₁ e₁₁ => wp_li (by decide) fun t₁₂ o₁₂ e₁₂ => wp_sub fun t₁₃ o₁₃ e₁₃ => wp_nil ?_
  have k : Only [.r4, .r5, .r6, .r26] t t₁₃ :=
    (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans (o₇.trans (o₈.trans (o₉.trans (o₁₀.trans
      (o₁₁.trans (o₁₂.trans o₁₃)))))))))))).mono
  refine ⟨h.only PF k, k.mem, fun r hr => k.gpr r hr, ?_⟩
  rw [e₁₃, e₁₂, o₁₂.get .r4, e₁₁, o₁₀.get .r4, e₁₀, e₉, o₉.get .r5, o₉.get .r4, e₈, o₈.get .r4, e₇, o₇.get .r4,
    e₆, o₆.get .r24, o₆.get .r4, e₅, o₅.get .r24, o₅.get .r4, e₄, o₄.get .r24, e₃, o₃.get .r24, e₂, o₂.get .r24,
    e₁, o₁.get .r20, o₁.get .r24, Base.r20 h]
  exact okbits hrc _

/-- `out` is writable. -/
theorem out_w : ∀ i < kk s, InRegions (fr s :: s.wr) (s.gpr .r3 + BitVec.ofNat 64 i) 1 :=
  fun i hi => by
    rw [P.hwr]
    exact ⟨oR s, by simp, Offset.contains_base _ (by have := P.ok; unfold kk at hi; omega)
      (by have := P.k2; unfold kk at hi; omega)⟩

/-- `*msg_len` is writable. -/
theorem ml_w : InRegions (fr s :: s.wr) (s.gpr .r5 + BitVec.ofNat 64 0) 8 := by
  rw [P.hwr, BitVec.add_zero]
  exact ⟨mlR s, by simp, Region.contains_self _ _⟩

omit P in
/-- The slots and a buffer apart from the stack. -/
theorem slR_dis {R : Region} (h : (kD s).Disjoint R) : (slR s).Disjoint R := h.sub_left fun a ha => kR_sub a (slR_sub s a ha)

/-- The buffer's first `k` bytes ANDed with `ok` to `out`. -/
theorem outLoop_ok {t : State} (h : Base (SD s) (VD s rc) (withMem s m) t) :
    WP isa outLoop t fun t' => Saves s t' ∧ t'.rd = s.rd ∧ (∀ r ∉ [Reg.r4, .r5, .r6, .r7], t'.gpr r = t.gpr r) ∧
      t'.mem = writeBytes t.mem (s.gpr .r3)
        ((Spec.Rsa.bytesAt t.mem (off (Sd s) oBuf) (kk s)).map fun b => andB b (t.gpr .r26)) := by
  have PF := fitsM (m := m) P
  have hk1 := P.k1
  have hk2 := P.k2
  have ek : kk s = (s.gpr .r7).toNat := rfl
  have hB : oBuf = 2560 := rfl
  have hR : oRsa = 8192 := rfl
  have hw : t.wr = fr s :: s.wr := h.wr
  refine WP.seq (wp_addi fun t₁ o₁ e₁ => wp_mov fun t₂ o₂ e₂ => wp_mov fun t₃ o₃ e₃ => wp_nil ?_)
  have k₃ : Only [.r4, .r5, .r6] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  have hsep : ∀ j < kk s, ∀ i < kk s, off (Sd s) oBuf + BitVec.ofNat 64 j ≠ s.gpr .r3 + BitVec.ofNat 64 i :=
    fun j hj i hi => ne_of_dis (A := scR s) (B := oR s) P.os.symm (by
      show (scR s).Contains (off (off (Sd s) oBuf) j) 1
      rw [off_off]; exact (sc_sub P) _ (sc_in (n := 1) (by omega) _ (Region.contains_self _ _)))
      (Offset.contains_base _ (by have := P.ok; omega) (by omega))
  refine WP.mono (andCopy_ok (q := off (Sd s) oBuf) (p := s.gpr .r3) (n := kk s) (msk := t.gpr .r26) (by omega)
    (by omega) (by rw [o₃.get .r4, o₂.get .r4, e₁, h.r14])
    (by rw [o₃.get .r5, e₂, o₁.get .r16, Base.r16 h])
    (by rw [e₃, o₂.get .r15, o₁.get .r15, Base.r15 h]; exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _) |>.symm)
    (by rw [k₃.get .r26])
    (fun j hj => by
      rw [k₃.rd, k₃.wr, hw]
      show InRegions _ (off (off (Sd s) oBuf) j) 1
      rw [off_off]; exact sc_inR PF (by omega) _)
    (by rw [k₃.wr, hw]; exact out_w P) hsep) fun t' ⟨hK, hm⟩ => ?_
  have K : Keep [.r4, .r5, .r6, .r7] t t' := (k₃.keep.trans hK).mono
  have hm' : t'.mem = writeBytes t.mem (s.gpr .r3)
      ((Spec.Rsa.bytesAt t.mem (off (Sd s) oBuf) (kk s)).map fun b => andB b (t.gpr .r26)) := by
    rw [hm, k₃.mem]
  have fr : Frame [oR s] t.mem t'.mem := by
    rw [hm']
    refine writeBytes_frame _ _ _ ?_
    simp only [Region.Contains, BitVec.sub_self, List.length_map, bytesAt_length]
    have := P.ok; unfold kk; simp; omega
  refine ⟨Saves.ofMem (h.sv.keep K fr fun r hr => by rw [List.mem_singleton.mp hr]; exact slR_dis P.ko),
    K.rd.trans h.rd, fun r hr => K.gpr r hr, hm'⟩

/-- The length and the result. -/
theorem decRet_ok {H : Hash} {D : Nat} (hD : H.D = D) (hD64 : D ≤ 64) {u : State} (sv : Saves s u)
    (h15 : u.gpr .r15 = s.gpr .r7) (h17 : u.gpr .r17 = s.gpr .r5) (h20 : u.gpr .r20 = BitVec.ofNat 64 rc)
    (hrc : rc ≤ 2) {idx : Nat} (h25 : u.gpr .r25 = BitVec.ofNat 64 idx) :
    WP isa (.block (decRet H)) u fun u' => Saves s u' ∧ u'.rd = u.rd ∧
      u'.mem = u.mem.writeW (s.gpr .r5)
        ((s.gpr .r7 - BitVec.ofNat 64 (2 * D + 2) - BitVec.ofNat 64 idx) &&& u.gpr .r26) ∧
      u'.gpr .r3 = (if rc = 2 then 2#64 else 0#64) ||| (u.gpr .r26 &&& 1#64) := by
  subst hD
  refine wp_subi (h := by omega) fun u₁ o₁ e₁ => wp_sub fun u₂ o₂ e₂ => wp_and fun u₃ o₃ e₃ => ?_
  have k₃ : Only [.r4] u u₃ := (o₁.trans (o₂.trans o₃)).mono
  refine wp_std (a := s.gpr .r5 + BitVec.ofNat 64 0) (by rw [k₃.get .r17, h17]) (by rw [k₃.wr, sv.wr]; exact ml_w P)
    fun u₄ m₄ => ?_
  refine wp_li (by decide) fun u₅ o₅ e₅ => wp_xor fun u₆ o₆ e₆ => wp_subi fun u₇ o₇ e₇ => wp_lsr fun u₈ o₈ e₈ =>
    wp_add fun u₉ o₉ e₉ => wp_li (by decide) fun u₁₀ o₁₀ e₁₀ => wp_and fun u₁₁ o₁₁ e₁₁ =>
    wp_or fun u₁₂ o₁₂ e₁₂ => wp_nil ?_
  have k₁₂ : Only [.r4, .r3] u₄ u₁₂ :=
    (o₅.trans (o₆.trans (o₇.trans (o₈.trans (o₉.trans (o₁₀.trans (o₁₁.trans o₁₂))))))).mono
  have K : Keep [.r4, .r3] u u₁₂ := (k₃.keep.trans (m₄.keep.trans k₁₂.keep)).mono
  have fm : Frame [mlR s] u.mem u₁₂.mem := by
    rw [k₁₂.mem, m₄.mem, k₃.mem, BitVec.add_zero]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨sv.keep K fm fun r hr => by rw [List.mem_singleton.mp hr]; exact slR_dis P.kml, K.rd, ?_, ?_⟩
  · rw [k₁₂.mem, m₄.mem, k₃.mem, BitVec.add_zero, e₃, e₂, e₁, o₁.get .r25, o₂.get .r26, o₁.get .r26, h25, h15]
  · rw [e₁₂, e₁₁, e₁₀, o₁₀.get .r26, o₉.get .r26, o₈.get .r26, o₇.get .r26, o₆.get .r26, o₅.get .r26, m₄.gpr,
      k₃.get .r26, o₁₁.get .r3, o₁₀.get .r3, e₉, e₈, e₇, e₆, e₅, o₅.get .r20, m₄.gpr, k₃.get .r20, h20]
    rw [faultbits hrc]

/-- Zeros to `out` and `*msg_len`, and the result `r = 2 ? 2 : 0`. -/
theorem decFail_ok {t : State} (h : Base (SD s) (VD s rc) (withMem s m) t) (hrc : rc ≤ 2) :
    WP isa decFail t fun u' => Saves s u' ∧ u'.rd = s.rd ∧
      u'.mem = (writeBytes t.mem (s.gpr .r3) (List.replicate (kk s) 0)).writeW (s.gpr .r5) (0#64) ∧
      u'.gpr .r3 = if rc = 2 then 2#64 else 0#64 := by
  have hk1 := P.k1
  have hk2 := P.k2
  have ek : kk s = (s.gpr .r7).toNat := rfl
  have hw : t.wr = fr s :: s.wr := h.wr
  refine WP.seq (WP.seq (wp_mov fun t₁ o₁ e₁ => wp_mov fun t₂ o₂ e₂ => wp_li (by decide) fun t₃ o₃ e₃ =>
    wp_nil ?_))
  have k₃ : Only [.r4, .r5, .r6] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  refine WP.mono (zero_ok (p := s.gpr .r3) (n := kk s) (b := 0) (by omega) (by omega)
    (by rw [o₃.get .r4, o₂.get .r4, e₁, Base.r16 h])
    (by rw [o₃.get .r5, e₂, o₁.get .r15, Base.r15 h]; exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _) |>.symm)
    (by rw [e₃]; rfl)
    (by rw [k₃.wr, hw]; exact out_w P)) fun t₄ ⟨hk, hm⟩ => ?_
  have K₄ : Keep [.r4, .r5, .r6] t t₄ := (k₃.keep.trans hk).mono
  have g6 : t₄.gpr .r6 = 0#64 := by rw [hk.get .r6, e₃]
  refine wp_std (a := s.gpr .r5 + BitVec.ofNat 64 0) (by rw [K₄.get .r17, Base.r17 h]) (by rw [K₄.wr, hw]; exact ml_w P)
    fun t₅ m₅ => ?_
  refine wp_li (by decide) fun u₅ o₅ e₅ => wp_xor fun u₆ o₆ e₆ => wp_subi fun u₇ o₇ e₇ => wp_lsr fun u₈ o₈ e₈ =>
    wp_add fun u₉ o₉ e₉ => wp_nil ?_
  have k₉ : Only [.r4, .r3] t₅ u₉ := (o₅.trans (o₆.trans (o₇.trans (o₈.trans o₉)))).mono
  have K : Keep [.r4, .r5, .r6, .r3] t u₉ := (K₄.trans (m₅.keep.trans k₉.keep)).mono
  have hm' : u₉.mem = (writeBytes t.mem (s.gpr .r3) (List.replicate (kk s) 0)).writeW (s.gpr .r5) (0#64) := by
    rw [k₉.mem, m₅.mem, hm, k₃.mem, BitVec.add_zero, g6]
  have fm : Frame [oR s, mlR s] t.mem u₉.mem := by
    rw [hm']
    refine ((writeBytes_frame _ _ _ ?_).mono fun r hr => by simp at hr ⊢; exact .inl hr).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (Region.contains_self _ _)
    simp only [Region.Contains, BitVec.sub_self, List.length_replicate]
    have := P.ok; unfold kk; simp; omega
  refine ⟨Saves.ofMem (h.sv.keep K fm fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact slR_dis P.ko
      · exact slR_dis P.kml), K.rd.trans h.rd, hm', ?_⟩
  rw [e₉, e₈, e₇, e₆, e₅, o₅.get .r20, m₅.gpr, K₄.get .r20, Base.r20 h, faultbits hrc]

end

end VG.Proof.RsaOaep.PPC64LE.Dec
