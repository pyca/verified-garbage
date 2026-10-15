module

import VerifiedGarbage.Proof.Rsa.AArch64.CvHead
public import VerifiedGarbage.Proof.Rsa.AArch64.CkMain
public import VerifiedGarbage.Impl.Rsa.AArch64.CheckCrtKey
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs

/-!
# Compact CRT-key validation workspace

The public lengths choose `cap = max (ceil(k / 2)) (max p_len q_len)`.
The layout uses `W = 2 * ceil(cap / 8) + 2` words, enough for the full
modulus and every product, including malformed and unbalanced inputs.
`ckcHeadS_ok` connects this layout to the shared key-validation proofs.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.CheckKey
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- The factor-dependent capacity, rounded to limbs. -/
theorem crt_capacity_words (k pl ql : Nat) :
    wk (VG.Impl.Rsa.AArch64.CheckCrtKey.capacity k pl ql) =
      max ((k + 15) / 16) (max ((pl + 7) / 8) ((ql + 7) / 8)) := by
  unfold VG.Impl.Rsa.AArch64.CheckCrtKey.capacity wk
  omega

private theorem select_max (a b : BitVec 64) :
    (if decide (2 ^ 64 ≤ a.toNat + (~~~b).toNat + true.toNat) = true then a else b) =
      BitVec.ofNat 64 (max a.toNat b.toNat) := by
  simp only [decide_eq_true_eq, BitVec.toNat_not, Bool.toNat_true]
  have ha := a.isLt
  have hb := b.isLt
  split
  · rw [Nat.max_eq_left (by omega), BitVec.ofNat_toNat]; rfl
  · rw [Nat.max_eq_right (by omega), BitVec.ofNat_toNat]; rfl

theorem ckcWide_ok {s : State} {B : Addr} {Z k pl ql : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (hk2 : k ≤ 1024) (hp : pl ≤ k) (hq : ql ≤ k) (hZ : 8 * 32 ≤ Z)
    (hK : word s.mem B (8 * Public.sK) = BitVec.ofNat 64 k)
    (hP : word s.mem B (8 * sPlen) = BitVec.ofNat 64 pl)
    (hQ : word s.mem B (8 * sQlen) = BitVec.ofNat 64 ql) :
    WP isa (.block VG.Impl.Rsa.AArch64.CheckCrtKey.wide) s fun t =>
      (t.gpr .x12 = BitVec.ofNat 64 (wW (VG.Impl.Rsa.AArch64.CheckCrtKey.capacity k pl ql)) ∧
        t.mem = s.mem.writeW (off B (8 * sW)) (BitVec.ofNat 64 (wW (VG.Impl.Rsa.AArch64.CheckCrtKey.capacity k pl ql)))) ∧
      Keep [.x3, .x4, .x12] s t := by
  have nk : (BitVec.ofNat 64 k + 15#64) >>> 4 = BitVec.ofNat 64 ((k + 15) / 16) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  have round8 (v : Nat) (hv : v ≤ 1024) :
      (BitVec.ofNat 64 v + 7#64) >>> 3 = BitVec.ofNat 64 ((v + 7) / 8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  have np := round8 pl (by omega)
  have nq := round8 ql (by omega)
  have arith :
      (BitVec.ofNat 64 (max (max ((k + 15) / 16) ((pl + 7) / 8)) ((ql + 7) / 8))) +
      (BitVec.ofNat 64 (max (max ((k + 15) / 16) ((pl + 7) / 8)) ((ql + 7) / 8))) + 2#64 =
      BitVec.ofNat 64 (wW (VG.Impl.Rsa.AArch64.CheckCrtKey.capacity k pl ql)) := by
    simp only [wW, crt_capacity_words]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hn := hs.nowrap
  refine WP.keep [.x3, .x4, .x12] ?_ (by decide) (by decide) (by decide +kernel)
  brun [VG.Impl.Rsa.AArch64.CheckCrtKey.wide, h0,
    hdr_enc (show Public.sK < 32 by decide), hdr_enc (show sPlen < 32 by decide),
    hdr_enc (show sQlen < 32 by decide), hdr_enc (show sW < 32 by decide),
    hs.ld (d := 8 * Public.sK) (by unfold Public.sK sFn; omega),
    hs.ld (d := 8 * sPlen) (by unfold sPlen sFn; omega),
    hs.ld (d := 8 * sQlen) (by unfold sQlen sFn; omega),
    hs.st (d := 8 * sW) (by unfold sW; omega), hK, hP, hQ, nk, np, nq, select_max]
  have hpw : (pl + 7) / 8 < 2 ^ 64 := by omega
  have hqw : (ql + 7) / 8 < 2 ^ 64 := by omega
  have hkw : (k + 15) / 16 < 2 ^ 64 := by omega
  have hmw : max ((k + 15) / 16) ((pl + 7) / 8) < 2 ^ 64 := by omega
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpw, Nat.mod_eq_of_lt hqw,
    Nat.mod_eq_of_lt hkw, Nat.mod_eq_of_lt hmw]
  simp only [off, BitVec.ofNat_add, ← BitVec.add_assoc, arith, and_self]

/-- `head`: `W`, the arrays' bases, the stride, and the mask all ones. -/
theorem ckcHead_ok {s : State} {B : Addr} {Z k pl ql : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hk1 : 64 ≤ k)
    (hk2 : k ≤ 1024) (hZ : 128 * k ≤ Z) (hp : pl ≤ k) (hq : ql ≤ k) (hP : word s.mem B (8 * sPlen) = BitVec.ofNat 64 pl)
    (hQ : word s.mem B (8 * sQlen) = BitVec.ofNat 64 ql) (hK : word s.mem B (8 * Public.sK) = BitVec.ofNat 64 k) :
    WP isa (.block VG.Impl.Rsa.AArch64.CheckCrtKey.head) s fun t =>
      Ws t B Z (wW (VG.Impl.Rsa.AArch64.CheckCrtKey.capacity k pl ql)) ∧ word t.mem B (8 * Public.sMask) = mask true ∧
      Frm B [(8 * sW, 8), (8 * sArr 0, 64), (8 * sStride, 8), (8 * Public.sMask, 8)] s.mem t.mem ∧
      Keep [.x3, .x4, .x7, .x12] s t := by
  have hcap : VG.Impl.Rsa.AArch64.CheckCrtKey.capacity k pl ql ≤ k := by
    unfold VG.Impl.Rsa.AArch64.CheckCrtKey.capacity; omega
  have hn := hs.nowrap
  have hZ16 : slot (wW (VG.Impl.Rsa.AArch64.CheckCrtKey.capacity k pl ql)) 16 ≤ Z := by unfold slot hdrBytes wW wk; omega
  have h8 := hdr_lt_slot (wW (VG.Impl.Rsa.AArch64.CheckCrtKey.capacity k pl ql)) 8 (show 31 < 32 by decide)
  have eW : sW = 6 := rfl
  have eA : sArr 0 = 8 := rfl
  have eS : sStride = 28 := rfl
  have eM : Public.sMask = 22 := rfl
  have hl8 : slot (wW (VG.Impl.Rsa.AArch64.CheckCrtKey.capacity k pl ql)) 8 ≤ slot (wW (VG.Impl.Rsa.AArch64.CheckCrtKey.capacity k pl ql)) 16 := Nat.add_le_add_left (Nat.mul_le_mul_right _ (by decide)) _
  unfold VG.Impl.Rsa.AArch64.CheckCrtKey.head
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (ckcWide_ok hs h0 hk2 hp hq (by omega) hK hP hQ) fun t₀ ⟨⟨h12₀, hm₀⟩, k₀⟩ => ?_
  have hs₀ := hs.congr k₀.wr
  have h0₀ : t₀.gpr .x0 = B := (k₀.gpr .x0 (by decide)).trans h0
  rw [WP.block_append_iff]
  refine WP.mono (setBases_ok hs₀ h0₀ h12₀ (by unfold sArr; omega)) fun t₁ ⟨hb₁, ho₁, k₁⟩ => ?_
  have k01 := k₀.trans k₁
  have h12 : t₁.gpr .x12 = BitVec.ofNat 64 (wW (VG.Impl.Rsa.AArch64.CheckCrtKey.capacity k pl ql)) := (k₁.gpr .x12 (by decide)).trans h12₀
  have hs₁ := hs.congr k01.wr
  have h0₁ : t₁.gpr .x0 = B := (k01.gpr .x0 (by decide)).trans h0
  refine WP.mono (WP.keep [.x3, .x4, .x7] (Q := fun t => t.gpr .x7 = 0 ∧ t.mem = (t₁.mem.writeW (off B (8 * sStride))
      (BitVec.ofNat 64 (8 * (wW (VG.Impl.Rsa.AArch64.CheckCrtKey.capacity k pl ql) + 2)))).writeW (off B (8 * Public.sMask)) (mask true)) (by
    brun [h0₁, h12, hdr_enc (show sStride < 32 by decide), hdr_enc (show Public.sMask < 32 by decide),
      hs₁.st (d := 8 * sStride) (by omega), hs₁.st (d := 8 * Public.sMask) (by omega),
      ofNat_add_ofNat, shl_ofNat (show (wW (VG.Impl.Rsa.AArch64.CheckCrtKey.capacity k pl ql) + 2) * 2 ^ 3 < 2 ^ 64 by simp only [wW, wk]; omega)]
    rw [show (wW (VG.Impl.Rsa.AArch64.CheckCrtKey.capacity k pl ql) + 2) * 2 ^ 3 = 8 * (wW (VG.Impl.Rsa.AArch64.CheckCrtKey.capacity k pl ql) + 2) by omega]
    rfl) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨_, hm⟩, k₂⟩ => ?_
  have o1 := writeW_outside t₁.mem B (BitVec.ofNat 64 (8 * (wW (VG.Impl.Rsa.AArch64.CheckCrtKey.capacity k pl ql) + 2))) (d := 8 * sStride) (by omega)
  have o2 := writeW_outside (t₁.mem.writeW (off B (8 * sStride)) (BitVec.ofNat 64 (8 * (wW (VG.Impl.Rsa.AArch64.CheckCrtKey.capacity k pl ql) + 2)))) B (mask true)
    (d := 8 * Public.sMask) (by omega)
  have o0 := writeW_outside s.mem B (BitVec.ofNat 64 (wW (VG.Impl.Rsa.AArch64.CheckCrtKey.capacity k pl ql))) (d := 8 * sW) (by omega)
  rw [← hm₀] at o0
  have hw : ∀ i < 32, i ≠ sStride → i ≠ Public.sMask → word t.mem B (8 * i) = word t₁.mem B (8 * i) :=
    fun i hi h1 h2 => by rw [hm, o2.word (by omega) (by omega), o1.word (by omega) (by omega)]
  have hW₁ : word t₁.mem B (8 * sW) = BitVec.ofNat 64 (wW (VG.Impl.Rsa.AArch64.CheckCrtKey.capacity k pl ql)) := by
    rw [ho₁.word (by unfold sW sArr; omega) (by omega), hm₀, word_writeW_self]
  refine ⟨⟨hs₁.congr k₂.wr, (k₂.gpr .x0 (by decide)).trans h0₁, ?_, ?_, fun j hj => ?_, hZ16,
    show 2 ≤ wW (VG.Impl.Rsa.AArch64.CheckCrtKey.capacity k pl ql) by simp only [wW]; omega, show wW (VG.Impl.Rsa.AArch64.CheckCrtKey.capacity k pl ql) < 2 ^ 24 by simp only [wW, wk]; omega⟩,
    by rw [hm, word_writeW_self], ?_, (k01.trans k₂).mono (by decide)⟩
  · rw [hw sW (by decide) (by decide) (by decide)]; exact hW₁
  · rw [hm, o2.word (by omega) (by omega), word_writeW_self]
  · rw [hw (sArr j) (by unfold sArr; omega) (by unfold sArr sStride sFn; omega)
      (by unfold sArr Public.sMask sFn; omega)]
    exact hb₁ j hj
  · intro x hx
    have a := hx (8 * sW, 8) (by simp)
    have b := hx (8 * sArr 0, 64) (by simp)
    have c := hx (8 * sStride, 8) (by simp)
    have d := hx (8 * Public.sMask, 8) (by simp)
    dsimp only at a b c d
    rw [hm, o2 x d, o1 x c, ho₁ x b, o0 x a]

/-- `head`: the layout, the mask all ones, and `CkS` from the memory on
entry to `main`. -/
theorem ckcHeadS_ok {I : CkIn} {s : State} (h : CkPre I s) (hc : I.cap = VG.Impl.Rsa.AArch64.CheckCrtKey.capacity I.k I.pl I.ql) :
    WP isa (.block VG.Impl.Rsa.AArch64.CheckCrtKey.head) s fun t => CkS I s.mem t ∧ mword t.mem I.B = mask true := by
  have L := h.L
  have hZ := L.z
  refine WP.mono (ckcHead_ok h.scr h.x0 L.k1 L.k2 hZ (Nat.le_of_lt L.pl2) (Nat.le_of_lt L.ql2) h.args.pl h.args.ql h.args.k) fun s₁ ⟨hw₁, hm₁, f₁, k₁⟩ => ⟨?_, hm₁⟩
  have eW : sW = 6 := rfl
  have eA : sArr 0 = 8 := rfl
  have eS : sStride = 28 := rfl
  have eM : Public.sMask = 22 := rfl
  have k1 := L.k1
  have hi₁ : InScr I.B I.Z s.mem s₁.mem := InScr.of_frm f₁ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> dsimp only <;> omega)
  exact ⟨L.fit, hc ▸ hw₁, h.args.congr fun i hi => f₁.word_eq (fun r hr => by
      unfold ckSlot at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> dsimp only <;> omega) (by unfold ckSlot at hi; omega),
    h.n.congrK hi₁ k₁, h.e.congrK hi₁ k₁, h.d.congrK hi₁ k₁, h.p.congrK hi₁ k₁, h.q.congrK hi₁ k₁,
    h.dp.congrK hi₁ k₁, h.dq.congrK hi₁ k₁, h.qi.congrK hi₁ k₁, hi₁, k₁.wr.trans h.wr⟩

end VG.Proof.Rsa.AArch64
