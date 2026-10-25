module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyBits
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontStep
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.PPC64LE.Shifts
import VerifiedGarbage.Proof.Rsa.PPC64LE.EvenW
import VerifiedGarbage.Proof.Rsa.PPC64LE.WordLoops

/-!
# The halving and the comparison of arrays, and the zeroing of the arrays

As on ARMv7: `half_ok` (`[j] := ([j] + c 2^(32 w)) / 2`), `eqS_ok` (the slot
`d` := whether `[a] = [b]`), and `zeroArrays_ok` (the first `n` digits of
the arrays := 0). The halving and the comparison run over words for an even
`w`, over digits for an odd one.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Keys

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Loops
open VG.Impl.Rsa.PPC64LE.Keys (ptr half eqS zeroArrays halfBody eqBody halfWBody eqWBody countLoop)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

theorem shl2_ofNat (w : Nat) : BitVec.ofNat 64 w <<< 2 = BitVec.ofNat 64 (4 * w) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_arith

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
  refine ptr_ok h (by decide) (by decide) (by decide) (show j < 2 ^ 15 by omega_arith) ?_
  have k₀ : Keep opRegs s (s.write .r5 (off B (arr w j))) := (Keep.write _ _ _).mono
  have hb : WP isa (.block [.lsl .r6 .r29 2, .add .r6 .r5 .r6, .store .w .r9 .r6 0])
      (s.write .r5 (off B (arr w j))) fun u =>
        (u.gpr .r5 = off B (arr w j) ∧
          u.mem = s.mem.writeW (off B (arr w j + 4 * w)) ((s.gpr .r9).setWidth 32)) ∧
        Keep [.r6] (s.write .r5 (off B (arr w j))) u := by
    refine WP.keep _ ?_ (by decide)
    prun [h.r29, shl2_ofNat, BitVec.add_zero,
      h.scr.st (show arr w j + 4 * w + 4 ≤ Z by omega_arith)]
  refine WP.mono hb fun u ⟨⟨u5, mu⟩, ku⟩ => ?_
  have k₁ : Keep opRegs s u := k₀.trans' ku.mono
  have hu : Ws u B Z w N := h.of_keep k₁
  have o := writeW32_outside s.mem B (d := arr w j + 4 * w) ((s.gpr .r9).setWidth 32) (by omega_arith)
  have lo : val32 u.mem B (arr w j) w = num s.mem B w j := by
    rw [mu]; exact o.val32 (by omega_arith) (by omega_arith)
  have top : w32 u.mem B (arr w j + 4 * w) = (s.gpr .r9).toNat := by
    rw [mu, w32_write_self, BitVec.toNat_setWidth]; omega_arith
  have k1 : KeyWorkspace.Keep B w [j] [] s.mem u.mem := by
    rw [mu]; exact KeyWorkspace.Keep.of_arr (d := 4 * w) o (by omega_arith) (by simp)
  have b0 : w32 u.mem B (arr w j) % 2 < 2 := Nat.mod_lt _ (by decide)
  have post : ∀ t : State, Outside B (arr w j) (4 * w) u.mem t.mem → Ws t B Z w N → Keep opRegs u t →
      2 * num t.mem B w j + w32 u.mem B (arr w j) % 2 =
        num s.mem B w j + 2 ^ (32 * w) * (s.gpr .r9).toNat →
      Ws t B Z w N ∧ KeyWorkspace.Keep B w [j] [] s.mem t.mem ∧
        num t.mem B w j = (num s.mem B w j + 2 ^ (32 * w) * (s.gpr .r9).toNat) / 2 ∧ Keep opRegs s t :=
    fun t out ht kt v => by
      refine ⟨ht, k1.trans (KeyWorkspace.Keep.of_arr (d := 0) (by simpa using out) (by omega_arith) (by simp)), ?_,
        k₁.trans' kt⟩
      generalize 2 ^ (32 * w) * (s.gpr .r9).toNat = P at v ⊢
      omega_arith
  refine evenW_ok hu (fun hev v mv kv => ?_) (fun hodd v mv kv => ?_)
  · have hv := hu.of_keep kv
    rw [WP.seq_iff]
    refine WP.mono (WP.keep [.r8] (Q := fun x => x.gpr .r5 = off B (arr w j) ∧ x.gpr .r8 = BitVec.ofNat 64 (w / 2) ∧
      x.mem = v.mem) (by prun [kv.gpr (r := .r5) (by decide), u5, hv.r29, lsr1_ofNat (show w < 2 ^ 64 by omega_arith)])
      (by decide)) fun x ⟨⟨x5, x8, xm⟩, kx⟩ => ?_
    have hx := hv.of_keep kx
    refine WP.mono (halfWLoop_ok hx.scr x5 x8 (by omega_arith) (by omega_arith) (by omega_arith)) fun t ⟨eq, out, kt⟩ => ?_
    rw [xm, mv] at eq out
    have e1 : wordsVal u.mem B (arr w j) (w / 2) = num s.mem B w j := by
      rw [wordsVal_eq_val32, show 2 * (w / 2) = w by omega_arith]; exact lo
    rw [e1, show 8 * (w / 2) = 4 * w by omega_arith, show 64 * (w / 2) = 32 * w by omega_arith, top,
      Nat.mod_eq_of_lt (show (s.gpr .r9).toNat < 2 by omega_arith)] at eq
    refine post t (by simpa only [show 8 * (w / 2) = 4 * w by omega_arith] using out) (hx.of_keep kt)
      (Keep.mono (rs' := opRegs) ((kv.trans kx).trans kt) (by decide)) ?_
    rw [num_words _ _ hev]; exact eq
  · have hv := hu.of_keep kv
    rw [WP.seq_iff]
    refine WP.mono (WP.keep [.r8] (Q := fun x => x.gpr .r5 = off B (arr w j) ∧ x.gpr .r8 = BitVec.ofNat 64 w ∧
      x.mem = v.mem) (by prun [kv.gpr (r := .r5) (by decide), u5, hv.r29, BitVec.add_zero])
      (by decide)) fun x ⟨⟨x5, x8, xm⟩, kx⟩ => ?_
    have hx := hv.of_keep kx
    refine WP.mono (halfLoop_ok hx.scr x5 x8 (by omega_arith) (by omega_arith) (by omega_arith)) fun t ⟨eq, out, kt⟩ => ?_
    rw [xm, mv] at eq out
    rw [lo, top, Nat.mod_eq_of_lt (show (s.gpr .r9).toNat < 2 by omega_arith)] at eq
    exact post t out (hx.of_keep kt) (Keep.mono (rs' := opRegs) ((kv.trans kx).trans kt) (by decide)) eq

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
      omega_arith
    rw [hs]
    simp only [e, ↓reduceIte]
    rfl

/-- The normalization of the words' accumulator to a bit: `r | -r` has its
sign bit set exactly when `r` is not zero. -/
theorem eq_normW (r : BitVec 64) :
    (((((BitVec.ofNat 64 0 - r) ||| r) >>> 63) ^^^ BitVec.ofNat 64 1).setWidth 32).toNat =
      if r = 0 then 1 else 0 := by
  by_cases e : r = 0
  · subst e; rfl
  · have hp : 0 < r.toNat := by
      rcases Nat.eq_zero_or_pos r.toNat with z | z
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using z)) e
      · exact z
    have hneg : (BitVec.ofNat 64 0 - r).toNat = 2 ^ 64 - r.toNat := by
      have := r.isLt
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega_arith
    have big : 2 ^ 63 ≤ ((BitVec.ofNat 64 0 - r) ||| r).toNat := by
      rw [BitVec.toNat_or]
      have := r.isLt
      by_cases hr : r.toNat < 2 ^ 63
      · have := Nat.left_le_or (n := (BitVec.ofNat 64 0 - r).toNat) (m := r.toNat); omega_arith
      · have := Nat.right_le_or (n := (BitVec.ofNat 64 0 - r).toNat) (m := r.toNat); omega_arith
    have hs : (((BitVec.ofNat 64 0 - r) ||| r) >>> 63) = BitVec.ofNat 64 1 := by
      apply BitVec.eq_of_toNat_eq
      have := ((BitVec.ofNat 64 0 - r) ||| r).isLt
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
      omega_arith
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
  refine ptr_ok h (by decide) (by decide) (by decide) (show a < 2 ^ 15 by omega_arith) ?_
  refine ptr_ok (h.of_keep (Keep.write _ _ _)) (by decide) (by decide) (by decide)
    (show b < 2 ^ 15 by omega_arith) ?_
  let t := (s.write .r6 (off B (arr w a))).write .r7 (off B (arr w b))
  have kt : Keep opRegs s t := ((Keep.write _ _ _).trans (Keep.write _ _ _)).mono
  have hb : WP isa (.block [.li .r9 0]) t fun u =>
      (u.gpr .r6 = off B (arr w a) ∧ u.gpr .r7 = off B (arr w b) ∧ u.gpr .r9 = 0 ∧ u.mem = s.mem) ∧
        Keep [.r9] t u := by
    refine WP.keep _ ?_ (by decide)
    prun [t]
    rfl
  refine WP.mono hb fun u ⟨⟨u6, u7, u9, mu⟩, ku⟩ => ?_
  have k₁ : Keep opRegs s u := kt.trans' ku.mono
  have hu : Ws u B Z w N := h.of_keep k₁
  -- The slot from the accumulator, whatever the loop.
  have fin : ∀ (v : State) (nz : BitVec 64), Ws v B Z w N → Keep opRegs s v → v.mem = s.mem →
      (nz = 0 ↔ num s.mem B w a = num s.mem B w b) →
      ∀ ops : List Instr, WP isa (.block ops) v (fun x => x.mem = v.mem.writeW (off B d)
          (if nz = 0 then BitVec.ofNat 32 1 else BitVec.ofNat 32 0) ∧
          Keep opRegs v x) →
      WP isa (.block ops) v fun x => Ws x B Z w N ∧ KeyWorkspace.Keep B w [] [d] s.mem x.mem ∧
        slot x.mem B d = (if num s.mem B w a = num s.mem B w b then 1 else 0) ∧ Keep opRegs s x :=
    fun v nz hv kv vm hnz ops hw => WP.mono hw fun x ⟨xm, kx⟩ => by
      refine ⟨hv.of_keep kx, by rw [xm, vm]; exact keep_slot _ _ (by simp) (by omega_arith), ?_, kv.trans' kx⟩
      rw [xm, slot_write_self]
      by_cases e : num s.mem B w a = num s.mem B w b
      · simp only [hnz.mpr e, e, ↓reduceIte]; rfl
      · simp only [show ¬ nz = 0 from fun h => e (hnz.mp h), e, ↓reduceIte]; rfl
  refine evenW_ok hu (fun hev v mv kv => ?_) (fun hodd v mv kv => ?_)
  · have hv := hu.of_keep kv
    rw [WP.seq_iff]
    refine WP.mono (WP.keep [.r8] (Q := fun x => x.gpr .r6 = off B (arr w a) ∧ x.gpr .r7 = off B (arr w b) ∧
      x.gpr .r8 = BitVec.ofNat 64 (w / 2) ∧ x.gpr .r9 = 0 ∧ x.mem = v.mem)
      (by prun [kv.gpr (r := .r6) (by decide), kv.gpr (r := .r7) (by decide), kv.gpr (r := .r9) (by decide),
        u6, u7, u9, hv.r29, lsr1_ofNat (show w < 2 ^ 64 by omega_arith)]) (by decide))
      fun x ⟨⟨x6, x7, x8, x9, xm⟩, kx⟩ => ?_
    have hx := hv.of_keep kx
    rw [WP.seq_iff]
    refine WP.mono (eqWLoop_ok hx.scr x6 x7 x8 x9 (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith))
      fun y ⟨yeq, ym, ky⟩ => ?_
    have hy := hx.of_keep ky
    rw [xm, mv, mu, ← num_words _ _ hev, ← num_words _ _ hev] at yeq
    refine fin y (y.gpr .r9) hy (Keep.mono (rs' := opRegs) (((k₁.trans kv).trans kx).trans ky) (by decide))
      (by rw [ym, xm, mv, mu]) yeq _ ?_
    refine WP.mono (WP.keep [.r0, .r3] (Q := fun z => z.mem = y.mem.writeW (off B d)
      ((((((BitVec.ofNat 64 0 - y.gpr .r9) ||| y.gpr .r9) >>> 63) ^^^ BitVec.ofNat 64 1)).setWidth 32)) ?_ (by rfl))
      fun z ⟨m, k⟩ => ⟨?_, k.mono (by decide)⟩
    · prun [hy.r31, hy.scr.st (show d + 4 ≤ Z by omega_arith),
        exec_store_w (show Reg.r31 ≠ .r0 by decide) (show d < 2 ^ 15 by omega_arith)]
    · rw [m]; congr 1
      apply BitVec.eq_of_toNat_eq
      rw [eq_normW]; split <;> rfl
  · have hv := hu.of_keep kv
    rw [WP.seq_iff]
    refine WP.mono (WP.keep [.r8] (Q := fun x => x.gpr .r6 = off B (arr w a) ∧ x.gpr .r7 = off B (arr w b) ∧
      x.gpr .r8 = BitVec.ofNat 64 w ∧ x.gpr .r9 = 0 ∧ x.mem = v.mem)
      (by prun [kv.gpr (r := .r6) (by decide), kv.gpr (r := .r7) (by decide), kv.gpr (r := .r9) (by decide),
        u6, u7, u9, hv.r29, BitVec.add_zero]) (by decide))
      fun x ⟨⟨x6, x7, x8, x9, xm⟩, kx⟩ => ?_
    have hx := hv.of_keep kx
    rw [WP.seq_iff]
    refine WP.mono (eqLoop_ok hx.scr x6 x7 x8 x9 (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith))
      fun y ⟨yeq, y9, ym, ky⟩ => ?_
    have hy := hx.of_keep ky
    rw [xm, mv, mu] at yeq
    refine fin y (y.gpr .r9) hy (Keep.mono (rs' := opRegs) (((k₁.trans kv).trans kx).trans ky) (by decide))
      (by rw [ym, xm, mv, mu]) yeq _ ?_
    refine WP.mono (WP.keep [.r0, .r3] (Q := fun z => z.mem = y.mem.writeW (off B d)
      (((((BitVec.ofNat 64 0 - y.gpr .r9) >>> 63) ^^^ BitVec.ofNat 64 1)).setWidth 32)) ?_ (by rfl))
      fun z ⟨m, k⟩ => ⟨?_, k.mono (by decide)⟩
    · prun [hy.r31, hy.scr.st (show d + 4 ≤ Z by omega_arith),
        exec_store_w (show Reg.r31 ≠ .r0 by decide) (show d < 2 ^ 15 by omega_arith)]
    · rw [m]; congr 1
      apply BitVec.eq_of_toNat_eq
      rw [eq_norm _ y9]; split <;> rfl

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
