module

public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Written
public import VerifiedGarbage.Proof.RsaOaep.Scan
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Buf
import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Encode
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mgf1.Bytes

/-!
# RSAES-OAEP decryption on RISC-V: the outputs

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/Dc/Out.lean`): `okMask_ok`, `ok`, all ones iff
the private operation's result is 1 and the accumulator zero (`x ≠ 0` from
the top bit of `x ∨ -x`); `outLoop_ok`, the buffer's first `k` bytes ANDed
with it to `out`; `decRet_ok`, the length and the result; `decFail_ok`,
zeros, and the result `r = 2 ? 2 : 0`. From `out` on, `Base` does not hold
(`out` is not ours): the caller's registers in their slots (`Saves`) do.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.RISCV64.Dec

open VG VG.RISCV64 VG.Impl.RsaOaep.RISCV64 VG.Impl.RsaOaep.RISCV64.Dec VG.WriteBytes
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Impl.Bignum.RISCV64 (countLoop)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Kept MemTo wp_li wp_mov wp_addi wp_subi wp_add wp_sub wp_and wp_or wp_xor
  wp_srl wp_lbu wp_sb wp_sd wp_nil fill_ok ofNat_succ')
open VG.Proof.RsaPkcs1Sig (bytesAt_length writeBytes_out)
open VG.Proof.RsaOaep.RISCV64 (Base Fits Saves view off off_off sc_in sc_inR fr slR slR_sub ne_of_dis)
open VG.Proof.Bignum.RISCV64 (wp_countdown)
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
theorem Saves.ofMem {s t : State} {m : Mem} (h : Saves (withMem s m) t) : Saves s t := ⟨h.sp, h.wr, h.sv⟩

/-- `a6` bytes from `a4` to `a5`, each ANDed with `s7`, for `a6 > 0`. -/
theorem andCopy_ok {u : State} {p q : Addr} {n : Nat} {msk : BitVec 64} (hn : 0 < n) (hn' : n < 2 ^ 64)
    (h4 : u.gpr .a4 = q) (h5 : u.gpr .a5 = p) (h6 : u.gpr .a6 = BitVec.ofNat 64 n) (h7 : u.gpr .s7 = msk)
    (hr : ∀ j < n, InRegions (u.rd ++ u.wr) (q + BitVec.ofNat 64 j) 1)
    (hw : ∀ i < n, InRegions u.wr (p + BitVec.ofNat 64 i) 1)
    (hd : ∀ j < n, ∀ i < n, q + BitVec.ofNat 64 j ≠ p + BitVec.ofNat 64 i) :
    WP isa (countLoop .a6 outBody) u fun t => Kept [.t1, .a4, .a5, .a6] u t ∧
      t.mem = writeBytes u.mem p ((Spec.Rsa.bytesAt u.mem q n).map fun b => andB b msk) := by
  refine WP.mono (wp_countdown (cnt := .a6) hn' hn
    (fun i t => Kept [.t1, .a4, .a5, .a6] u t ∧
      t.mem = writeBytes u.mem p (((Spec.Rsa.bytesAt u.mem q n).map fun b => andB b msk).take i) ∧
      t.gpr .a5 = p + BitVec.ofNat 64 i ∧ t.gpr .a4 = q + BitVec.ofNat 64 i) ?_
    ⟨Kept.refl _ _, by simp [writeBytes_nil], by simp [h5], by simp [h4]⟩ h6) fun t h => ⟨h.1, ?_⟩
  · intro i hi t ⟨hK, hm, h5', h4'⟩ _
    simp only [outBody, List.cons_append, List.nil_append]
    have hR : InRegions (t.rd ++ t.wr) (q + BitVec.ofNat 64 i) 1 := by
      rw [hK.rd, hK.wr]; exact hr _ hi
    have hv : t.mem (q + BitVec.ofNat 64 i) = u.mem (q + BitVec.ofNat 64 i) := by
      rw [hm, writeBytes_out _ _ _ _ n (fun i' hi' => hd i hi i' hi')
        (by simp only [List.length_take, List.length_map, bytesAt_length]; omega)]
    refine wp_lbu (a := q + BitVec.ofNat 64 i) (by rw [h4', BitVec.add_zero]) hR fun s₁ o₁ e₁ =>
      wp_and fun s₂ o₂ e₂ => ?_
    have hA : InRegions s₂.wr (p + BitVec.ofNat 64 i) 1 := by
      rw [o₂.wr, o₁.wr, hK.wr]; exact hw _ hi
    refine wp_sb (a := p + BitVec.ofNat 64 i) (by rw [o₂.get .a5, o₁.get .a5, h5', BitVec.add_zero]) hA
      fun s₃ m₃ => ?_
    refine wp_addi (imm := 1) fun s₄ o₄ e₄ => wp_addi (imm := 1) fun s₅ o₅ e₅ =>
      wp_subi (imm := 1) fun s₆ o₆ e₆ => wp_nil ?_
    have hK' : Kept [.t1, .a4, .a5, .a6] t s₆ :=
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
      rw [e₂, e₁, o₁.get .s7, hK.get .s7, h7, hv]; rfl
    · rw [o₆.get .a5, e₅, o₄.get .a5, m₃.gpr, o₂.get .a5, o₁.get .a5, h5', ofNat_succ']
    · rw [o₆.get .a4, o₅.get .a4, e₄, m₃.gpr, o₂.get .a4, o₁.get .a4, h4', ofNat_succ']
    · rw [e₆, o₅.get .a6, o₄.get .a6, m₃.gpr, o₂.get .a6, o₁.get .a6]
  · rw [List.take_of_length_le (by simp [bytesAt_length])] at h
    exact h.2.1

section
variable {s : State} (P : PreD s) {m : Mem} {rc : Nat}
include P

/-- `ok` (`s7`). -/
theorem okMask_ok {t : State} (h : Base (SD s) (VD s rc) (withMem s m) t) (hrc : rc ≤ 2) :
    WP isa (.block okMask) t fun t' => Base (SD s) (VD s rc) (withMem s m) t' ∧ t'.mem = t.mem ∧
      Only [.a1, .a2, .a3, .s7] t t' ∧ t'.gpr .s7 = mk (rc = 1 ∧ t.gpr .s5 = 0) := by
  have PF : Fits (SD s) (withMem s m) := fits P rfl rfl
  unfold okMask
  refine wp_li (imm := 1) (by decide) fun t₁ o₁ e₁ => wp_xor fun t₂ o₂ e₂ => wp_subi (imm := 1) fun t₃ o₃ e₃ =>
    wp_srl fun t₄ o₄ e₄ => wp_li (imm := 0) (by decide) fun t₅ o₅ e₅ => wp_sub fun t₆ o₆ e₆ =>
    wp_or fun t₇ o₇ e₇ => wp_srl fun t₈ o₈ e₈ => wp_li (imm := 1) (by decide) fun t₉ o₉ e₉ =>
    wp_xor fun t₁₀ o₁₀ e₁₀ => wp_and fun t₁₁ o₁₁ e₁₁ => wp_li (imm := 0) (by decide) fun t₁₂ o₁₂ e₁₂ =>
    wp_sub fun t₁₃ o₁₃ e₁₃ => wp_nil ?_
  have k : Only [.a1, .a2, .a3, .s7] t t₁₃ :=
    (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans (o₇.trans (o₈.trans (o₉.trans (o₁₀.trans
      (o₁₁.trans (o₁₂.trans o₁₃)))))))))))).mono
  refine ⟨h.only PF k, k.mem, k, ?_⟩
  rw [e₁₃, e₁₂, o₁₂.get .a1, e₁₁, o₁₀.get .a1, e₁₀, e₉, o₉.get .a2, o₉.get .a1, e₈, o₈.get .a1, e₇, o₇.get .a1,
    e₆, o₆.get .s5, o₆.get .a1, e₅, o₅.get .s5, o₅.get .a1, e₄, o₄.get .s5, e₃, o₃.get .s5, e₂, o₂.get .s5,
    e₁, o₁.get .s4, o₁.get .s5, Base.drc h]
  exact okbits hrc _

/-- `out` is writable. -/
theorem out_w : ∀ i < kk s, InRegions (fr s :: s.wr) (s.gpr .a0 + BitVec.ofNat 64 i) 1 :=
  fun i hi => by
    rw [P.hwr]
    exact ⟨oR s, by simp, Offset.contains_base _ (by have := P.ok; unfold kk at hi; omega)
      (by have := P.k2; unfold kk at hi; omega)⟩

/-- `*msg_len` is writable. -/
theorem ml_w : InRegions (fr s :: s.wr) (s.gpr .a2 + BitVec.ofNat 64 0) 8 := by
  rw [P.hwr, BitVec.add_zero]
  exact ⟨mlR s, by simp, Region.contains_self _ _⟩

omit P in
/-- The slots and a buffer apart from the stack. -/
theorem slR_dis {R : Region} (h : (kD s).Disjoint R) : (slR s).Disjoint R :=
  h.sub_left fun a ha => kR_sub a (slR_sub s a ha)

/-- The buffer's first `k` bytes ANDed with `ok` to `out`. -/
theorem outLoop_ok {t : State} (h : Base (SD s) (VD s rc) (withMem s m) t) :
    WP isa outLoop t fun t' => Saves s t' ∧ t'.rd = s.rd ∧ Kept [.a4, .a5, .a6, .t1] t t' ∧
      t'.mem = writeBytes t.mem (s.gpr .a0)
        ((Spec.Rsa.bytesAt t.mem (off (Sd s) oBuf) (kk s)).map fun b => andB b (t.gpr .s7)) := by
  have PF : Fits (SD s) (withMem s m) := fits P rfl rfl
  have hk1 := P.k1
  have hk2 := P.k2
  have ek : kk s = (s.gpr .a4).toNat := rfl
  have hB : oBuf = 2560 := rfl
  have hR : oRsa = 8192 := rfl
  have hw : t.wr = fr s :: s.wr := h.wr
  unfold outLoop bufBase
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_addi (imm := 2047) fun t₀ o₀ e₀ => wp_addi (imm := 513) fun t₁ o₁ e₁ =>
    wp_mov fun t₂ o₂ e₂ => wp_mov fun t₃ o₃ e₃ => wp_nil ?_)
  have k₃ : Only [.a4, .a5, .a6] t t₃ := (o₀.trans (o₁.trans (o₂.trans o₃))).mono
  have hsep : ∀ j < kk s, ∀ i < kk s, off (Sd s) oBuf + BitVec.ofNat 64 j ≠ s.gpr .a0 + BitVec.ofNat 64 i :=
    fun j hj i hi => ne_of_dis (A := scR s) (B := oR s) P.os.symm (by
      show (scR s).Contains (off (off (Sd s) oBuf) j) 1
      rw [off_off]; exact (sc_sub P) _ (sc_in (n := 1) (by omega) _ (Region.contains_self _ _)))
      (Offset.contains_base _ (by have := P.ok; omega) (by omega))
  refine WP.mono (andCopy_ok (q := off (Sd s) oBuf) (p := s.gpr .a0) (n := kk s) (msk := t.gpr .s7) (by omega)
    (by omega) (by rw [o₃.get .a4, o₂.get .a4, e₁, e₀, h.s0]; exact bufBase_eq _)
    (by rw [o₃.get .a5, e₂, o₁.get .s2, o₀.get .s2, Base.dout h])
    (by rw [e₃, o₂.get .s1, o₁.get .s1, o₀.get .s1, Base.dk h]
        exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _) |>.symm)
    (by rw [k₃.get .s7])
    (fun j hj => by
      rw [k₃.rd, k₃.wr, hw]
      show InRegions _ (off (off (Sd s) oBuf) j) 1
      rw [off_off]; exact sc_inR PF (by omega) _)
    (by rw [k₃.wr, hw]; exact out_w P) hsep) fun t' ⟨hK, hm⟩ => ?_
  have K : Kept [.a4, .a5, .a6, .t1] t t' := (k₃.keep.trans hK).mono
  have hm' : t'.mem = writeBytes t.mem (s.gpr .a0)
      ((Spec.Rsa.bytesAt t.mem (off (Sd s) oBuf) (kk s)).map fun b => andB b (t.gpr .s7)) := by
    rw [hm, k₃.mem]
  have fr : Frame [oR s] t.mem t'.mem := by
    rw [hm']
    refine writeBytes_frame _ _ _ ?_
    simp only [Region.Contains, BitVec.sub_self, List.length_map, bytesAt_length]
    have := P.ok; unfold kk; simp; omega
  exact ⟨Saves.ofMem (h.sv.keep K fr fun r hr => by rw [List.mem_singleton.mp hr]; exact slR_dis P.ko),
    K.rd.trans h.rd, K, hm'⟩

/-- The length and the result. -/
theorem decRet_ok {H : Hash} {D : Nat} (hD : H.D = D) (hD64 : D ≤ 64) {u : State} (sv : Saves s u)
    (h1 : u.gpr .s1 = s.gpr .a4) (h3 : u.gpr .s3 = s.gpr .a2) (h4 : u.gpr .s4 = BitVec.ofNat 64 rc)
    (hrc : rc ≤ 2) {idx : Nat} (h6 : u.gpr .s6 = BitVec.ofNat 64 idx) :
    WP isa (.block (decRet H)) u fun u' => Saves s u' ∧ u'.rd = u.rd ∧
      u'.mem = u.mem.writeW (s.gpr .a2)
        ((s.gpr .a4 - BitVec.ofNat 64 (2 * D + 2) - BitVec.ofNat 64 idx) &&& u.gpr .s7) ∧
      u'.gpr .a0 = (if rc = 2 then 2#64 else 0#64) ||| (u.gpr .s7 &&& 1#64) := by
  subst hD
  unfold decRet faultBit
  simp only [List.cons_append, List.nil_append]
  refine wp_subi (imm := 2 * H.D + 2) (h := by omega) fun u₁ o₁ e₁ => wp_sub fun u₂ o₂ e₂ =>
    wp_and fun u₃ o₃ e₃ => ?_
  have k₃ : Only [.a1] u u₃ := (o₁.trans (o₂.trans o₃)).mono
  refine wp_sd (a := s.gpr .a2 + BitVec.ofNat 64 0) (by rw [k₃.get .s3, h3])
    (by have := P.alm; rw [BitVec.add_zero]; exact this) (by rw [k₃.wr, sv.wr]; exact ml_w P)
    fun u₄ m₄ => ?_
  refine wp_li (imm := 2) (by decide) fun u₅ o₅ e₅ => wp_xor fun u₆ o₆ e₆ => wp_subi (imm := 1) fun u₇ o₇ e₇ =>
    wp_srl fun u₈ o₈ e₈ => wp_add fun u₉ o₉ e₉ => wp_li (imm := 1) (by decide) fun u₁₀ o₁₀ e₁₀ =>
    wp_and fun u₁₁ o₁₁ e₁₁ => wp_or fun u₁₂ o₁₂ e₁₂ => wp_nil ?_
  have k₁₂ : Only [.a1, .a0] u₄ u₁₂ :=
    (o₅.trans (o₆.trans (o₇.trans (o₈.trans (o₉.trans (o₁₀.trans (o₁₁.trans o₁₂))))))).mono
  have K : Kept [.a1, .a0] u u₁₂ := (k₃.keep.trans (m₄.keep.trans k₁₂.keep)).mono
  have fm : Frame [mlR s] u.mem u₁₂.mem := by
    rw [k₁₂.mem, m₄.mem, k₃.mem, BitVec.add_zero]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨sv.keep K fm fun r hr => by rw [List.mem_singleton.mp hr]; exact slR_dis P.kml, K.rd, ?_, ?_⟩
  · rw [k₁₂.mem, m₄.mem, k₃.mem, BitVec.add_zero, e₃, e₂, e₁, o₁.get .s6, o₂.get .s7, o₁.get .s7, h6, h1]
  · rw [e₁₂, e₁₁, e₁₀, o₁₀.get .s7, o₉.get .s7, o₈.get .s7, o₇.get .s7, o₆.get .s7, o₅.get .s7, m₄.gpr,
      k₃.get .s7, o₁₁.get .a0, o₁₀.get .a0, e₉, e₈, e₇, e₆, e₅, o₅.get .s4, m₄.gpr, k₃.get .s4, h4]
    rw [faultbits hrc]

/-- Zeros to `out` and `*msg_len`, and the result `r = 2 ? 2 : 0`. -/
theorem decFail_ok {t : State} (h : Base (SD s) (VD s rc) (withMem s m) t) (hrc : rc ≤ 2) :
    WP isa decFail t fun u' => Saves s u' ∧ u'.rd = s.rd ∧
      u'.mem = (writeBytes t.mem (s.gpr .a0) (List.replicate (kk s) 0)).writeW (s.gpr .a2) (0#64) ∧
      u'.gpr .a0 = if rc = 2 then 2#64 else 0#64 := by
  have hk1 := P.k1
  have hk2 := P.k2
  have ek : kk s = (s.gpr .a4).toNat := rfl
  have hw : t.wr = fr s :: s.wr := h.wr
  unfold decFail zeroOut faultBit
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (WP.seq (wp_mov fun t₁ o₁ e₁ => wp_mov fun t₂ o₂ e₂ => wp_li (imm := 0) (by decide)
    fun t₃ o₃ e₃ => wp_nil ?_))
  have k₃ : Only [.a1, .t5, .t0] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  refine WP.mono (fill_ok (p := s.gpr .a0) (n := kk s) (b := 0) (by omega) (by omega)
    (by rw [o₃.get .a1, o₂.get .a1, e₁, Base.dout h])
    (by rw [o₃.get .t5, e₂, o₁.get .s1, Base.dk h]
        exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _) |>.symm)
    (by rw [e₃]; rfl)
    (by rw [k₃.wr, hw]; exact out_w P)) fun t₄ ⟨hk, hm⟩ => ?_
  have K₄ : Kept [.a1, .t5, .t0] t t₄ := (k₃.keep.trans hk).mono
  refine wp_li (imm := 0) (by decide) fun t₅ o₅ e₅ => ?_
  refine wp_sd (a := s.gpr .a2 + BitVec.ofNat 64 0) (by rw [o₅.get .s3, K₄.get .s3, Base.dml h])
    (by have := P.alm; rw [BitVec.add_zero]; exact this) (by rw [o₅.wr, K₄.wr, hw]; exact ml_w P)
    fun t₆ m₆ => ?_
  refine wp_li (imm := 2) (by decide) fun u₅ o₅' e₅' => wp_xor fun u₆ o₆ e₆ => wp_subi (imm := 1) fun u₇ o₇ e₇ =>
    wp_srl fun u₈ o₈ e₈ => wp_add fun u₉ o₉ e₉ => wp_nil ?_
  have k₉ : Only [.a1, .a0] t₆ u₉ := (o₅'.trans (o₆.trans (o₇.trans (o₈.trans o₉)))).mono
  have K : Kept [.a1, .t5, .t0, .t1, .a0] t u₉ := (K₄.trans (o₅.keep.trans (m₆.keep.trans k₉.keep))).mono
  have hm' : u₉.mem = (writeBytes t.mem (s.gpr .a0) (List.replicate (kk s) 0)).writeW (s.gpr .a2) (0#64) := by
    rw [k₉.mem, m₆.mem, o₅.mem, hm, k₃.mem, BitVec.add_zero, e₅]
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
  rw [e₉, e₈, e₇, e₆, e₅', o₅'.get .s4, m₆.gpr, o₅.get .s4, K₄.get .s4, Base.drc h, faultbits hrc]

end

end VG.Proof.RsaOaep.RISCV64.Dec
