module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyBits
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontStep
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.PPC64LE.Shifts

/-!
# The halving and the comparison of arrays, and the zeroing of the arrays

As on ARMv7: `half_ok` (`[j] := ([j] + c 2^(32 w)) / 2`), `eqS_ok` (the slot
`d` := whether `[a] = [b]`), and `zeroArrays_ok` (the first `n` digits of
the arrays := 0).
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Keys

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Loops
open VG.Impl.Rsa.PPC64LE.Keys (ptr half eqS zeroArrays halfBody eqBody countLoop)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

theorem shl2_ofNat (w : Nat) : BitVec.ofNat 64 w <<< 2 = BitVec.ofNat 64 (4 * w) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

/-- `half j`: `[j] := ([j] + c 2^(32 w)) / 2`, for `c` 0 or 1 in `r9`. -/
theorem half_ok {s : State} {B : Addr} {Z w N j : Nat} (h : Ws s B Z w N)
    (hj : j < N) (hN : N ≤ 256) (bit : (s.gpr .r9).toNat ≤ 1) :
    WP isa (half j) s fun t => Ws t B Z w N ∧ KeyWorkspace.Keep B w [j] [] s.mem t.mem ∧
      num t.mem B w j = (num s.mem B w j + 2 ^ (32 * w) * (s.gpr .r9).toNat) / 2 ∧
      Keep opRegs s t := by
  have fit := h.arr_fit hj
  have nw := h.nowrap
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wpos
  have := h.wle
  rw [half, WP.seq_iff]
  refine ptr_ok h (by decide) (by decide) (by decide) (show j < 2 ^ 15 by omega) ?_
  have k₀ : Keep opRegs s (s.write .r5 (off B (arr w j))) := (Keep.write _ _ _).mono
  have hb : WP isa (.block [.lsl .r6 .r29 2, .add .r6 .r5 .r6, .store .w .r9 .r6 0, .addi .r8 .r29 0])
      (s.write .r5 (off B (arr w j))) fun u =>
        (u.gpr .r5 = off B (arr w j) ∧ u.gpr .r8 = BitVec.ofNat 64 w ∧
          u.mem = s.mem.writeW (off B (arr w j + 4 * w)) ((s.gpr .r9).setWidth 32)) ∧
        Keep [.r6, .r8] (s.write .r5 (off B (arr w j))) u := by
    refine WP.keep _ ?_ (by decide)
    prun [h.r29, shl2_ofNat, BitVec.add_zero,
      h.scr.st (show arr w j + 4 * w + 4 ≤ Z by omega)]
  refine WP.mono hb fun u ⟨⟨u5, u8, mu⟩, ku⟩ => ?_
  have k₁ : Keep opRegs s u := k₀.trans' ku.mono
  have hu : Ws u B Z w N := h.of_keep k₁
  refine WP.mono (halfLoop_ok hu.scr u5 u8 (by omega) (by omega) (by omega)) ?_
  intro t ⟨v, out, kt⟩
  have o := writeW32_outside s.mem B (d := arr w j + 4 * w) ((s.gpr .r9).setWidth 32) (by omega)
  have lo : val32 u.mem B (arr w j) w = num s.mem B w j := by
    rw [mu]; exact o.val32 (by omega) (by omega)
  have top : w32 u.mem B (arr w j + 4 * w) = (s.gpr .r9).toNat := by
    rw [mu, w32_write_self, BitVec.toNat_setWidth]; omega
  have b0 : w32 u.mem B (arr w j) % 2 < 2 := Nat.mod_lt _ (by decide)
  rw [lo, top, Nat.mod_eq_of_lt (show (s.gpr .r9).toNat < 2 by omega)] at v
  refine ⟨hu.of_keep kt, ?_, ?_, k₁.trans' kt⟩
  · have k1 : KeyWorkspace.Keep B w [j] [] s.mem u.mem := by
      rw [mu]; exact KeyWorkspace.Keep.of_arr (d := 4 * w) o (by omega) (by simp)
    have k2 : KeyWorkspace.Keep B w [j] [] u.mem t.mem :=
      KeyWorkspace.Keep.of_arr (d := 0) (by simpa using out) (by omega) (by simp)
    exact k1.trans k2
  · change val32 _ _ _ _ = _
    generalize 2 ^ (32 * w) * (s.gpr .r9).toNat = P at v ⊢
    omega

/-- The normalization of the comparison's accumulator to a bit. -/
theorem eq_norm (r : BitVec 64) (hr : r.toNat < 2 ^ 32) :
    ((((BitVec.ofNat 64 0 - r) >>> 63) ^^^ BitVec.ofNat 64 1).setWidth 32).toNat =
      if r = 0 then 1 else 0 := by
  by_cases e : r = 0
  · subst e; rfl
  · have hp : 0 < r.toNat := by
      rcases Nat.eq_zero_or_pos r.toNat with z | z
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using z)) e
      · exact z
    have hs : ((BitVec.ofNat 64 0 - r) >>> 63) = BitVec.ofNat 64 1 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.shiftRight_eq_div_pow]
      omega
    rw [hs]
    simp only [e, ↓reduceIte]
    rfl

/-- `eqS d a b`: the slot `d` := 1 if `[a] = [b]`, else 0. -/
theorem eqS_ok {s : State} {B : Addr} {Z w N d a b : Nat} (h : Ws s B Z w N)
    (ha : a < N) (hb : b < N) (hN : N ≤ 256) (hd : d + 4 ≤ 160) :
    WP isa (eqS d a b) s fun u => Ws u B Z w N ∧ KeyWorkspace.Keep B w [] [d] s.mem u.mem ∧
      slot u.mem B d = (if num s.mem B w a = num s.mem B w b then 1 else 0) ∧ Keep opRegs s u := by
  have fa := h.arr_fit ha
  have fb := h.arr_fit hb
  have nw := h.nowrap
  have hS : S w = 4 * (w + 2) := rfl
  have hz : 160 ≤ Z := h.hdr_le
  have := h.wpos
  have := h.wle
  rw [eqS, WP.seq_iff, List.append_assoc]
  refine ptr_ok h (by decide) (by decide) (by decide) (show a < 2 ^ 15 by omega) ?_
  refine ptr_ok (h.of_keep (Keep.write _ _ _)) (by decide) (by decide) (by decide)
    (show b < 2 ^ 15 by omega) ?_
  let t := (s.write .r6 (off B (arr w a))).write .r7 (off B (arr w b))
  have kt : Keep opRegs s t := ((Keep.write _ _ _).trans (Keep.write _ _ _)).mono
  have hb : WP isa (.block [.addi .r8 .r29 0, .li .r9 0]) t fun u =>
      (u.gpr .r6 = off B (arr w a) ∧ u.gpr .r7 = off B (arr w b) ∧ u.gpr .r8 = BitVec.ofNat 64 w ∧
        u.gpr .r9 = 0 ∧ u.mem = s.mem) ∧ Keep [.r8, .r9] t u := by
    refine WP.keep _ ?_ (by decide)
    prun [t, h.r29, BitVec.add_zero]
    rfl
  refine WP.mono hb fun u ⟨⟨u6, u7, u8, u9, mu⟩, ku⟩ => ?_
  have k₁ : Keep opRegs s u := kt.trans' ku.mono
  have hu : Ws u B Z w N := h.of_keep k₁
  rw [WP.seq_iff]
  refine WP.mono (eqLoop_ok hu.scr u6 u7 u8 u9 (by omega) (by omega) (by omega) (by omega)) ?_
  intro v ⟨veq, v9, vm, kv⟩
  have hv : Ws v B Z w N := hu.of_keep kv
  have k₂ : Keep opRegs s v := k₁.trans' kv
  have hf : WP isa (.block [.li .r0 0, .sub .r0 .r0 .r9, .lsr .d .r0 .r0 63, .li .r3 1,
      .logic .xor .r0 .r0 .r3, .store .w .r0 .r31 d]) v fun x =>
        x.mem = v.mem.writeW (off B d) (((((BitVec.ofNat 64 0 - v.gpr .r9) >>> 63) ^^^
          BitVec.ofNat 64 1)).setWidth 32) ∧ Keep opRegs v x := by
    refine WP.mono (WP.keep [.r0, .r3] ?_ (by rfl)) fun x ⟨m, k⟩ => ⟨m, k.mono⟩
    prun [hv.r31, hv.scr.st (show d + 4 ≤ Z by omega),
      exec_store_w (show Reg.r31 ≠ .r0 by decide) (show d < 2 ^ 15 by omega)]
  refine WP.mono hf fun x ⟨xm, kx⟩ => ⟨hv.of_keep kx, ?_, ?_, k₂.trans' kx⟩
  · rw [xm, vm, mu]; exact keep_slot _ _ (by simp) (by omega)
  · have veq' : v.gpr .r9 = 0 ↔ num s.mem B w a = num s.mem B w b := by rw [← mu]; exact veq
    rw [xm, slot_write_self, eq_norm _ v9]
    by_cases e : num s.mem B w a = num s.mem B w b
    · simp only [veq'.mpr e, e, ↓reduceIte]
    · simp only [show ¬ v.gpr .r9 = 0 from fun h => e (veq'.mp h), e, ↓reduceIte]

/-- `zeroArrays .r8`: the `n` digits from array 0 on (`r8 = n`) := 0. -/
theorem zeroArrays_ok {s : State} {B : Addr} {Z w N n : Nat} (h : Ws s B Z w N)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 n) (hn : 1 ≤ n) (hn' : n < 2 ^ 32) (hZ : 160 + 4 * n ≤ Z) :
    WP isa (zeroArrays .r8) s fun t => Ws t B Z w N ∧ (∀ k < n, w32 t.mem B (160 + 4 * k) = 0) ∧
      Outside B 160 (4 * n) s.mem t.mem ∧ Keep opRegs s t := by
  rw [zeroArrays, WP.seq_iff]
  have hb : WP isa (.block [.addi .r5 .r31 VG.Impl.Rsa.PPC64LE.Keys.hdr, .li .r0 0]) s fun u =>
      (u.gpr .r5 = off B 160 ∧ u.gpr .r8 = BitVec.ofNat 64 n ∧ u.gpr .r0 = 0 ∧ u.mem = s.mem) ∧
        Keep [.r0, .r5] s u := by
    refine WP.keep _ ?_ (by decide)
    prun [h.r31, h8, VG.Impl.Rsa.PPC64LE.Keys.hdr]
    rfl
  refine WP.mono hb fun u ⟨⟨u5, u8, u0, mu⟩, ku⟩ => ?_
  have hu : Ws u B Z w N := h.of_keep ku
  refine WP.mono (zeroLoop_ok hu.scr u5 u8 u0 hn hn' hZ) fun t ⟨z, out, kt⟩ =>
    ⟨hu.of_keep kt, z, by rw [← mu]; exact out, (ku.trans kt).mono⟩

end VG.Proof.Rsa.PPC64LE.Keys
