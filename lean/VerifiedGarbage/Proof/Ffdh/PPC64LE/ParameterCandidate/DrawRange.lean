module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Draw
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.Copy
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.KeyBits32
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.MontPrep
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Prep

/-!
# An FFDH parameter candidate on PPC64LE: a witness's upper bound

`dRange_ok`: with the witness `x` in array 4 and the odd modulus `N` in
array 0, `x | 1` into array 3 (its word `w` zeroed) and `x | 1 − N` into
array 6: `r20`, the borrow, is nonzero exactly when `x < N − 1`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search
open VG.Impl.Bignum.PPC64LE.PublicChecked (base)
open VG.Impl.Bignum.PPC64LE.Precompute (copyWords)
open VG.Proof.Mont (val32 w32)

/-- The number with its low word or'ed with 1. -/
theorem wv_or1 {m m' : Mem} {B : Addr} {d w : Nat} (hw : 1 ≤ w)
    (h0 : word m' B d = word m B d ||| 1#64) (hr : ∀ j, 1 ≤ j → j < w → word m' B (d + 8 * j) = word m B (d + 8 * j)) :
    wv m' B d w = wv m B d w + (1 - wv m B d w % 2) := by
  have e := fun mm => wv_add mm B d 1 (w - 1)
  rw [show 1 + (w - 1) = w by omega] at e
  rw [e m, e m']
  simp only [wv, Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.pow_zero, Nat.one_mul, Nat.mul_one]
  have hrest : wv m' B (d + 8) (w - 1) = wv m B (d + 8) (w - 1) := wv_congr fun i hi => by
    rw [show d + 8 + 8 * i = d + 8 * (i + 1) by omega]; exact hr _ (by omega) (by omega)
  rw [hrest, h0]
  have hor : (word m B d ||| 1#64).toNat = (word m B d).toNat + (1 - (word m B d).toNat % 2) := by
    rw [BitVec.toNat_or, show (1#64).toNat = 1 from rfl, VG.Proof.Rsa.KeyBits32.or_one]
    omega
  rw [hor]
  have : (2 ^ 64 * wv m B (d + 8) (w - 1)) % 2 = 0 := by
    rw [Nat.mul_mod, show 2 ^ 64 % 2 = 0 from rfl, Nat.zero_mul, Nat.zero_mod]
  omega

/-- The registers `dRange` writes. -/
def drRegs : List Reg := [.r14, .r15, .r0, .r17, .r5, .r3, .r4, .r6, .r8, .r9, .r16, .r20]

theorem dRange_ok {s : State} {B : Addr} {Z w N x : Nat} (hs : Scr s B Z) (h10 : s.gpr .r10 = off B (slot w 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (hw : 2 ≤ w) (hw' : w ≤ 128) (hZ : slot w 7 ≤ Z) (hN : wv s.mem B (slot w 0) w = N) (hodd : N % 2 = 1)
    (hx : wv s.mem B (slot w 4) w = x) :
    WP isa (.seq (.block (base .r14 3 ++ base .r15 4)) (.seq copyWords (.seq (.block (base .r5 3 ++
        ([.load .d .r3 .r5 0, .li .r4 1, .logic .or .r3 .r3 .r4, .store .d .r3 .r5 0, .lsl .r6 .r11 2,
          .add .r5 .r5 .r6, .li .r0 0, .store .d .r0 .r5 0] : List Instr) ++ base .r8 3 ++ base .r9 6)) subMod)))
      s fun t =>
      ((t.gpr .r20 = 0#64 ↔ ¬ x < N - 1) ∧
        Frm B [(slot w 3, 8 * (w + 2)), (slot w 6, 8 * (w + 2))] s.mem t.mem) ∧ Keep drRegs s t := by
  have hnw := hs.nowrap
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have hZ' : 256 + 7 * (8 * (w + 2)) ≤ Z := by rw [← es]; exact hZ
  -- Array 4 copied to array 3.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r14) (by decide) (by decide) h10 h29 3) fun s₁ ⟨⟨a14, m₁⟩, k₁⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .r15) (by decide) (by decide) ((k₁.gpr .r10 (by decide)).trans h10)
    ((k₁.gpr .r29 (by decide)).trans h29) 4) fun s₂ ⟨⟨a15, m₂⟩, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  refine WP.seq (WP.mono (copyWithin_ok (hs.congr k12.wr) a15 ((k₂.gpr .r14 (by decide)).trans a14)
    ((k12.gpr .r11 (by decide)).trans h11) (by omega) (by omega) (by simp only [es]; omega)
    (by simp only [es]; omega) (by simp only [es]; omega)) fun s₃ ⟨⟨_, cp, o₃⟩, k₃⟩ => ?_)
  have k13 := k12.trans k₃
  rw [m₂, m₁] at cp o₃
  -- Its low bit set and its word `w` zeroed.
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  have h10₃ : s₃.gpr .r10 = off B (slot w 0) := (k13.gpr .r10 (by decide)).trans h10
  have h29₃ : s₃.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2)) := (k13.gpr .r29 (by decide)).trans h29
  refine WP.mono (Pub.base_ok (rd := .r5) (by decide) (by decide) h10₃ h29₃ 3) fun s₄ ⟨⟨a5, m₄⟩, k₄⟩ => ?_
  have k14 := k13.trans k₄
  have hs₄ : Scr s₄ B Z := hs.congr k14.wr
  have l3 : InRegions (s₄.rd ++ s₄.wr) (off B (slot w 3)) 8 := hs₄.ld (by simp only [es]; omega)
  have st3 : InRegions s₄.wr (off B (slot w 3)) 8 := hs₄.st (by simp only [es]; omega)
  have st3w : InRegions s₄.wr (off B (slot w 3 + 8 * w)) 8 := hs₄.st (by simp only [es]; omega)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r3, .r4, .r6, .r5, .r0] (Q := fun u => u.mem =
      (s₄.mem.writeW (off B (slot w 3)) (s₄.mem.readW (off B (slot w 3)) 64 ||| 1#64)).writeW
        (off B (slot w 3 + 8 * w)) 0#64) ?_ (by decide)) fun s₅ ⟨m₅, k₅⟩ => ?_
  · prun [a5, BitVec.add_zero, l3, st3, st3w, (k14.gpr .r11 (by decide)).trans h11,
      Proof.MillerRabin.PPC64LE.shl2_ofNat]
  have k15 := k14.trans k₅
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r8) (by decide) (by decide) ((k₅.gpr .r10 (by decide)).trans
    ((k₄.gpr .r10 (by decide)).trans h10₃)) ((k15.gpr .r29 (by decide)).trans h29) 3) fun s₆ ⟨⟨a8, m₆⟩, k₆⟩ => ?_
  have k16 := k15.trans k₆
  refine WP.mono (Pub.base_ok (rd := .r9) (by decide) (by decide) ((k16.gpr .r10 (by decide)).trans h10)
    ((k16.gpr .r29 (by decide)).trans h29) 6) fun s₇ ⟨⟨a9, m₇⟩, k₇⟩ => ?_
  have k17 := k16.trans k₇
  -- `x | 1 − N`.
  refine WP.mono (subMod_ok (hs.congr k17.wr) ((k₇.gpr .r8 (by decide)).trans a8) a9
    ((k17.gpr .r10 (by decide)).trans h10) ((k17.gpr .r11 (by decide)).trans h11) (by omega) (by omega)
    (by simp only [es]; omega) (by simp only [es]; omega) (by simp only [es]; omega) (by simp only [es]; omega)
    (by simp only [es]; omega)) fun t ⟨⟨c, hc, hsub, h20⟩, o₈, k₈⟩ => ?_
  have m37 : s₇.mem = (s₃.mem.writeW (off B (slot w 3)) (s₃.mem.readW (off B (slot w 3)) 64 ||| 1#64)).writeW
      (off B (slot w 3 + 8 * w)) 0#64 := by rw [m₇, m₆, m₅, m₄]
  -- What changed before `subMod`: array 3.
  have f₇ : Frm B [(slot w 3, 8 * (w + 2))] s.mem s₇.mem := by
    rw [m37]
    refine frm_writeW (a := slot w 3 + 8 * w) (frm_writeW (a := slot w 3) (Frm.of_outside (o₃.mono (o' := slot w 3) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega))
      (List.mem_singleton_self _)) _ ⟨_, List.mem_singleton_self _, by dsimp only; omega,
        by dsimp only; omega⟩ (by simp only [es]; omega)) _
      ⟨_, List.mem_singleton_self _, by dsimp only; omega, by dsimp only; omega⟩ (by simp only [es]; omega)
  have n₇ : val32 s₇.mem B (slot w 0) (2 * w) = N := by
    rw [Pre.val32_eq_wv, f₇.wv_eq (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; dsimp only; simp only [es]; omega) (by simp only [es]; omega), hN]
  have x₃ : wv s₃.mem B (slot w 3) w = x := by
    rw [← hx]; exact wv_shift fun i hi => cp i hi
  have a₇ : val32 s₇.mem B (slot w 3) (2 * w) = x + (1 - x % 2) := by
    rw [Pre.val32_eq_wv, ← x₃]
    refine wv_or1 (by omega) ?_ fun j h1 h2 => ?_
    · simp only [word, off] at m37 ⊢
      rw [m37, rw_off _ _ _ (by omega) (by simp only [es]; omega) (by simp only [es]; omega), rw_self]
    · simp only [word, off] at m37 ⊢
      rw [m37, rw_off _ _ _ (by omega) (by simp only [es]; omega) (by simp only [es]; omega),
        rw_off _ _ _ (by omega) (by simp only [es]; omega) (by simp only [es]; omega)]
  have z₇ : w32 s₇.mem B (slot w 3 + 4 * (2 * w)) = 0 := by
    have e := VG.Proof.Mont.word_eq_w32 s₇.mem B (slot w 3 + 8 * w)
    have e0 : (VG.Proof.Mont.word s₇.mem B (slot w 3 + 8 * w)).toNat = 0 := by
      simp only [VG.Proof.Mont.word, VG.Proof.Mont.off] at m37 ⊢; rw [m37, rw_self]; rfl
    rw [show slot w 3 + 4 * (2 * w) = slot w 3 + 8 * w by omega]; omega
  rw [n₇, a₇, show 32 * (2 * w) = 64 * w by omega] at hsub
  rw [z₇] at h20
  have hT : val32 t.mem B (slot w 6) (2 * w) < 2 ^ (64 * w) := by rw [Pre.val32_eq_wv]; exact wv_lt _ _ _ _
  have hX : x < 2 ^ (64 * w) := by rw [← hx]; exact wv_lt _ _ _ _
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [h20]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with rfl | rfl
    · simp only [Nat.lt_irrefl, ↓reduceIte]
      constructor
      · intro _ hlt; omega
      · intro _; rfl
    · simp only [Nat.zero_lt_one, ↓reduceIte]
      constructor
      · intro h; exact absurd h (by decide)
      · intro hn; exfalso; apply hn; omega
  · exact (f₇.mono fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self).trans
      (Frm.of_outside (o₈.mono (o' := slot w 6) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega)) (List.mem_cons_of_mem _ List.mem_cons_self))
  · exact ((k17.trans k₈).mono (by decide))

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
