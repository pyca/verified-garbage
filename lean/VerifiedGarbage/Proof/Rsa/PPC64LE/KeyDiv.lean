module

public import VerifiedGarbage.Impl.Rsa.PPC64LE.KeyDiv
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyOps
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreR2Words
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Bignum.WordDiv
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Block

/-!
# Division by words for the RSA key checks on PPC64LE: correct

`divW_ok`: `divW a r m t sv` leaves `[r] = [a] mod forced [m]` for a divisor
of `wd = w / 4` words of 64 bits, `forced` its top bit set: the word steps
of `Proof/Bignum/PPC64LE/PreR2Words.lean` (`wordStepU_ok`) over `[a]`'s
words, most significant first (`WordStep.wordDiv_step'`), from `[r] = 0`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.KeyDiv

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (ptr seqs)
open VG.Impl.Rsa.PPC64LE.KeyDiv
open VG.Proof.Rsa.KeyWorkspace (arr S num arr_disj)

/-- The registers `save` keeps, by their words in the save area. -/
def svReg : Nat → Reg
  | 0 => .r14 | 1 => .r15 | 2 => .r16 | 3 => .r17 | 4 => .r18 | 5 => .r20 | _ => .r22

/-- A word read through a write of another. -/
theorem word_write_ne {m : Mem} {B : Addr} {d d' : Nat} (v : BitVec 64) (h : d' + 8 ≤ d ∨ d + 8 ≤ d')
    (hd : d + 8 ≤ 2 ^ 64) (hd' : d' + 8 ≤ 2 ^ 64) : word (m.writeW (off B d) v) B d' = word m B d' :=
  (writeW_outside m B v hd).word (by omega) hd'

/-- `save sv`: `r14`–`r18`, `r20` and `r22` into words 0–6 of the array `sv`. -/
theorem save_ok {s : State} {B : Addr} {Z w N sv : Nat} (h : Ws s B Z w N) (hsv : sv < N) (hN : N ≤ 256) (hw : 12 ≤ w) :
    WP isa (.block (save sv)) s fun t => (∀ i < 7, word t.mem B (arr w sv + 8 * i) = s.gpr (svReg i)) ∧
      Outside B (arr w sv) 56 s.mem t.mem ∧ Keep [.r5] s t := by
  have := h.wle
  have hnw := h.nowrap
  have fs := h.arr_fit hsv
  simp only [S] at fs
  refine ptr_ok h (r := .r5) (by decide) (by decide) (by decide) (show sv < 2 ^ 15 by omega) ?_
  refine WP.mono (WP.keep [] (Q := fun t => t.mem =
      (((((((s.mem.writeW (off B (arr w sv)) (s.gpr .r14)).writeW (off B (arr w sv + 8)) (s.gpr .r15)).writeW
        (off B (arr w sv + 16)) (s.gpr .r16)).writeW (off B (arr w sv + 24)) (s.gpr .r17)).writeW
        (off B (arr w sv + 32)) (s.gpr .r18)).writeW (off B (arr w sv + 40)) (s.gpr .r20)).writeW
        (off B (arr w sv + 48)) (s.gpr .r22))) (by
      prun [gpr_write, mem_write, off_add, h.scr.st (show arr w sv + 8 ≤ Z by omega),
        h.scr.st (show arr w sv + 8 + 8 ≤ Z by omega), h.scr.st (show arr w sv + 16 + 8 ≤ Z by omega),
        h.scr.st (show arr w sv + 24 + 8 ≤ Z by omega), h.scr.st (show arr w sv + 32 + 8 ≤ Z by omega),
        h.scr.st (show arr w sv + 40 + 8 ≤ Z by omega), h.scr.st (show arr w sv + 48 + 8 ≤ Z by omega)]) (by decide))
    fun t ⟨tm, tk⟩ => ⟨fun i hi => ?_, ?_, ((Keep.write _ .r5 _).trans tk).mono (by decide)⟩
  · rw [tm]
    have b : ∀ j, j < 7 → arr w sv + 8 * j + 8 ≤ 2 ^ 64 := fun j hj => by omega
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := omega) only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, show 8 * 2 = 16 from rfl,
      show 8 * 3 = 24 from rfl, show 8 * 4 = 32 from rfl, show 8 * 5 = 40 from rfl, show 8 * 6 = 48 from rfl,
      word_write_ne, word_writeW_self, svReg]
  · rw [tm]
    have o : ∀ (m : Mem) (j : Nat) (v : BitVec 64), j + 8 ≤ 56 →
        Outside B (arr w sv) 56 m (m.writeW (off B (arr w sv + j)) v) := fun m j v hj =>
      (writeW_outside m B v (by omega)).mono (by omega) (by omega)
    exact (((((((o _ 0 _ (by omega)).trans (o _ 8 _ (by omega))).trans (o _ 16 _ (by omega))).trans
      (o _ 24 _ (by omega))).trans (o _ 32 _ (by omega))).trans (o _ 40 _ (by omega))).trans (o _ 48 _ (by omega)))

/-- `restore sv`: words 0–6 of the array `sv` back into `r14`–`r18`, `r20`
and `r22`. -/
theorem restore_ok {s : State} {B : Addr} {Z w N sv : Nat} (h : Ws s B Z w N) (hsv : sv < N) (hN : N ≤ 256) (hw : 12 ≤ w) :
    WP isa (.block (restore sv)) s fun t => (∀ i < 7, t.gpr (svReg i) = word s.mem B (arr w sv + 8 * i)) ∧
      t.mem = s.mem ∧ Keep [.r5, .r14, .r15, .r16, .r17, .r18, .r20, .r22] s t := by
  have := h.wle
  have hnw := h.nowrap
  have fs := h.arr_fit hsv
  simp only [S] at fs
  refine ptr_ok h (r := .r5) (by decide) (by decide) (by decide) (show sv < 2 ^ 15 by omega) ?_
  have r : ∀ j, j < 7 → (s.write .r5 (off B (arr w sv))).mem.readW (off B (arr w sv) + BitVec.ofNat 64 (8 * j)) 64 =
      word s.mem B (arr w sv + 8 * j) := fun j hj => by rw [mem_write, off_add]
  refine WP.mono (WP.keep [.r14, .r15, .r16, .r17, .r18, .r20, .r22] (Q := fun t =>
      (∀ i < 7, t.gpr (svReg i) = word s.mem B (arr w sv + 8 * i)) ∧ t.mem = s.mem) (by
      prun [gpr_write, mem_write, h.scr.ld (show arr w sv + 8 ≤ Z by omega),
        h.scr.ld (show arr w sv + 8 + 8 ≤ Z by omega), h.scr.ld (show arr w sv + 16 + 8 ≤ Z by omega),
        h.scr.ld (show arr w sv + 24 + 8 ≤ Z by omega), h.scr.ld (show arr w sv + 32 + 8 ≤ Z by omega),
        h.scr.ld (show arr w sv + 40 + 8 ≤ Z by omega), h.scr.ld (show arr w sv + 48 + 8 ≤ Z by omega),
        off_add]
      intro i hi
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 by omega) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) (by decide))
    fun t ⟨⟨tg, tm⟩, tk⟩ => ⟨tg, by rw [tm], ((Keep.write _ .r5 _).trans tk).mono (by decide)⟩

/-- A word with its top bit set. -/
theorem or_top_toNat (x : BitVec 64) : (x ||| BitVec.ofNat 64 1 <<< 63).toNat = x.toNat % 2 ^ 63 + 2 ^ 63 := by
  have e : BitVec.ofNat 64 1 <<< 63 = BitVec.ofNat 64 (2 ^ 63) := by decide
  rw [e, BitVec.toNat_or, BitVec.toNat_ofNat, show 2 ^ 63 % 2 ^ 64 = 2 ^ 63 from rfl]
  have hx := x.isLt
  have hl := Nat.or_two_pow_eq_add_of_lt (Nat.mod_lt x.toNat (show 0 < 2 ^ 63 by decide))
  rcases (show x.toNat < 2 ^ 63 ∨ 2 ^ 63 ≤ x.toNat by omega) with h | h
  · rw [Nat.mod_eq_of_lt h] at hl ⊢; exact hl
  · have ex : x.toNat = x.toNat % 2 ^ 63 ||| 2 ^ 63 := by rw [hl]; omega
    rw [ex, Nat.or_assoc, Nat.or_self, ← ex]
    omega

/-- `force m t` for `w = 4 wd`: `[m]`'s word `wd - 1` with its top bit set (`F`),
and the temporary's words 0, 1 and 3 := `1`, `F` and `[m]`'s word `wd - 2`. -/
theorem force_ok {s : State} {B : Addr} {Z w N m t wd : Nat} (h : Ws s B Z w N) (hm : m < N) (ht : t < N)
    (hmt : m ≠ t) (hN : N ≤ 256) (hw : w = 4 * wd) (hwd : 4 ≤ wd) :
    WP isa (.block (force m t)) s fun u => ∃ F : BitVec 64,
      F.toNat = (word s.mem B (arr w m + 8 * (wd - 1))).toNat % 2 ^ 63 + 2 ^ 63 ∧
      u.mem = (((s.mem.writeW (off B (arr w m + 8 * (wd - 1))) F).writeW (off B (arr w t)) (BitVec.ofNat 64 1)).writeW
        (off B (arr w t + 8)) F).writeW (off B (arr w t + 24)) (word s.mem B (arr w m + 8 * (wd - 2))) ∧
      u.gpr .r9 = off B (arr w t) ∧ u.gpr .r10 = off B (arr w m) ∧ u.gpr .r11 = BitVec.ofNat 64 (2 * wd) ∧
      Keep [.r0, .r3, .r9, .r10, .r11, .r14] s u := by
  have := h.wle
  have hnw := h.nowrap
  have fm := h.arr_fit hm
  have ft := h.arr_fit ht
  have dmt := arr_disj (w := w) hmt
  simp only [S] at fm ft dmt
  have e11 : BitVec.ofNat 64 w >>> 1 = BitVec.ofNat 64 (2 * wd) := by
    rw [hw, show 4 * wd = 2 * (2 * wd) by omega]; exact mont_ofNat_shr1 (by omega)
  have ea := ea_top B (d := arr w m) (w := wd) (c := 8) (by omega)
  have ea2 : off B (arr w m + 8 * wd - 8) - BitVec.ofNat 64 8 = off B (arr w m + 8 * (wd - 2)) := by
    rw [BitVec.sub_eq_iff_eq_add, off_add, show arr w m + 8 * (wd - 2) + 8 = arr w m + 8 * wd - 8 by omega]
  rw [show arr w m + 8 * wd - 8 = arr w m + 8 * (wd - 1) by omega] at ea ea2
  simp only [force, List.append_assoc]
  refine ptr_ok h (r := .r10) (by decide) (by decide) (by decide) (show m < 2 ^ 15 by omega) ?_
  refine ptr_ok (h.of_keep (Keep.write _ .r10 _)) (r := .r9) (by decide) (by decide) (by decide)
    (show t < 2 ^ 15 by omega) ?_
  have rT : ((s.write .r10 (off B (arr w m))).write .r9 (off B (arr w t))).mem.readW
      (off B (arr w m + 8 * (wd - 1))) 64 = word s.mem B (arr w m + 8 * (wd - 1)) := rfl
  refine WP.mono (WP.keep [.r0, .r3, .r11, .r14] (Q := fun u => ∃ F : BitVec 64,
      F = word s.mem B (arr w m + 8 * (wd - 1)) ||| BitVec.ofNat 64 1 <<< 63 ∧
      u.mem = (((s.mem.writeW (off B (arr w m + 8 * (wd - 1))) F).writeW (off B (arr w t)) (BitVec.ofNat 64 1)).writeW
        (off B (arr w t + 8)) F).writeW (off B (arr w t + 24)) (word s.mem B (arr w m + 8 * (wd - 2))) ∧
      u.gpr .r11 = BitVec.ofNat 64 (2 * wd)) (by
      prun [gpr_write, mem_write, h.r29, e11, ea, ea2, off_add, rT,
        h.scr.ld (show arr w m + 8 * (wd - 1) + 8 ≤ Z by omega), h.scr.st (show arr w m + 8 * (wd - 1) + 8 ≤ Z by omega),
        h.scr.st (show arr w t + 8 ≤ Z by omega), h.scr.st (show arr w t + 8 + 8 ≤ Z by omega),
        h.scr.ld (show arr w m + 8 * (wd - 2) + 8 ≤ Z by omega), h.scr.st (show arr w t + 24 + 8 ≤ Z by omega)]
      refine ⟨_, rfl, ?_⟩
      have r2 := word_write_ne (m := ((s.mem.writeW (off B (arr w m + 8 * (wd - 1)))
        (word s.mem B (arr w m + 8 * (wd - 1)) ||| 1#64 <<< 63)).writeW (off B (arr w t)) 1#64))
        (B := B) (d := arr w t + 8) (d' := arr w m + 8 * (wd - 2))
        (word s.mem B (arr w m + 8 * (wd - 1)) ||| 1#64 <<< 63) (by omega) (by omega) (by omega)
      rw [word_write_ne (B := B) (d := arr w t) (d' := arr w m + 8 * (wd - 2)) _ (by omega) (by omega) (by omega),
        word_write_ne (B := B) (d := arr w m + 8 * (wd - 1)) (d' := arr w m + 8 * (wd - 2)) _ (by omega) (by omega)
          (by omega)] at r2
      exact congrArg _ r2) (by decide))
    fun u ⟨⟨F, hF, um, u11⟩, uk⟩ => ⟨F, by rw [hF]; exact or_top_toNat _, um, ?_, ?_, u11, ?_⟩
  · rw [uk.gpr .r9 (by decide), gpr_write]; rfl
  · rw [uk.gpr .r10 (by decide), gpr_write, gpr_write]; rfl
  · exact ((Keep.write _ .r10 _).trans ((Keep.write _ .r9 _).trans uk)).mono (by decide)

end VG.Proof.Rsa.PPC64LE.KeyDiv
