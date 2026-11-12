module

import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega
-- separate module: the inverse's proof is split in a chain of modules, so that a change rebuilds only the modules after it

public import VerifiedGarbage.Proof.Rsa.X86_64.InvB.Rows
public import VerifiedGarbage.Proof.Divstep.TcS
import VerifiedGarbage.Proof.Rsa.X86_64.InvB.Words
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Divstep.Tc
import VerifiedGarbage.Proof.Divstep.Packed
import VerifiedGarbage.Proof.Bignum.CrtFrame
public import VerifiedGarbage.Proof.Mont.Words
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# RSA's inverse by divsteps on x86-64: a batch

A batch (`batch_ok`) is `Divstep.batchS 59` on the window and arrays (`BS`):
the divsteps on the low words (`bWords_ok`) and the coefficients' magnitudes
and masks (`first_ok`), then `(f, g)` by `fgRow` (`fgPart_ok`, through
`Divstep.shr_nat`) and `(a, b)` by `abRow` (`abPart_ok`, through
`Divstep.mredRaw_nat`). A batch of the GCD alone (`batchG_ok`) is the same
without `(a, b)`, on `BSg`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.InvB

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Inv
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

theorem slot_eq (w j : Nat) : slot w j = 256 + j * (8 * (w + 2)) := by unfold slot hdrBytes; rfl

theorem xor_m1' (x : BitVec 64) : x ^^^ (-1 : BitVec 32).signExtend 64 = ~~~x := by
  rw [show (-1 : BitVec 32).signExtend 64 = BitVec.allOnes 64 by decide, BitVec.xor_allOnes]

/-- `bStart`: the low words of `f` and `g` into the window, `~d` into `rbx`, the stride into `r14`. -/
theorem bStart_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = off B (slot w 16)) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)))
    (hw1 : 2 ≤ w) (hZ : slot w 26 ≤ Z) :
    WP isa (.block bStart) s fun t =>
      t.mem = (s.mem.writeW (off B (slot w 16)) (word s.mem B (slot w 19))).writeW (off B (slot w 16 + 8))
        (word s.mem B (slot w 20)) ∧
      t.gpr .rbx = ~~~word s.mem B (slot w 16 + oD) ∧ t.gpr .r14 = BitVec.ofNat 64 (8 * (w + 2)) ∧
      Keep [.rax, .rbx, .r14] s t := by
  have hN := hs.nowrap
  have e16 := slot_eq w 16; have e19 := slot_eq w 19; have e20 := slot_eq w 20; have e26 := slot_eq w 26
  have e0 : ∀ x : Addr, x + BitVec.ofInt 64 0 = x := fun x => by
    rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
  unfold bStart
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (wa_ok 3 (r := .rax) (by decide) hdi h9) fun s₁ ⟨a₁, m₁, k₁⟩ => ?_
  rw [show 16 + 3 = 19 from rfl] at a₁
  rw [show ∀ l : List Instr, ([Instr.mov .rax (.mem (at0 .rax)), .store (wm 0) .rax] ++ l) =
    [Instr.mov .rax (.mem (at0 .rax)), .store (wm 0) .rax] ++ l from fun _ => rfl, WP.block_append_iff]
  have hdi₁ : s₁.gpr .rdi = off B (slot w 16) := (k₁.gpr (by decide)).trans hdi
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s₁.mem.writeW (off B (slot w 16)) (word s₁.mem B (slot w 19)))
    (by
      unfold wm
      have hs₁ := hs.congr k₁.2.2
      xrun [State.ea, at0, a₁, hdi₁, e0, offD, Nat.add_zero, hs₁.ld (show slot w 19 + 8 ≤ Z by omega_arith),
        hs₁.st (show slot w 16 + 8 ≤ Z by omega_arith)]) rfl) fun s₂ ⟨m₂, k₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (wa_ok 4 (r := .rax) (by decide) ((k₂.gpr (by decide)).trans hdi₁)
    ((k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans h9))) fun s₃ ⟨a₃, m₃, k₃⟩ => ?_
  rw [show 16 + 4 = 20 from rfl] at a₃
  have hdi₃ : s₃.gpr .rdi = off B (slot w 16) := ((k₂.trans k₃).gpr (by decide)).trans hdi₁
  have h9₃ : s₃.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) := (((k₁.trans k₂).trans k₃).gpr (by decide)).trans h9
  have o₂ : Outside B (slot w 16) 8 s.mem s₂.mem := by
    rw [m₂, m₁]; exact writeW_outside _ _ _ (by omega_arith)
  refine WP.mono (WP.keep [.rax, .rbx, .r14] (Q := fun t =>
      t.mem = s₃.mem.writeW (off B (slot w 16 + 8)) (word s₃.mem B (slot w 20)) ∧
      t.gpr .rbx = ~~~word s₃.mem B (slot w 16 + oD) ∧ t.gpr .r14 = BitVec.ofNat 64 (8 * (w + 2)))
    (by
      unfold wm
      have hs₃ := (hs.congr k₁.2.2).congr (k₂.trans k₃).2.2
      have hrd : ∀ v : BitVec 64, (s₃.mem.writeW (off B (slot w 16 + 8)) v).readW (off B (slot w 16 + oD)) 64 =
          s₃.mem.readW (off B (slot w 16 + oD)) 64 := fun v =>
        (writeW_outside s₃.mem B v (d := slot w 16 + 8) (by omega_arith)).word (by unfold oD; omega_arith) (by unfold oD; omega_arith)
      xrun [State.ea, at0, a₃, hdi₃, h9₃, e0, offD, xor_m1', hs₃.ld (show slot w 20 + 8 ≤ Z by omega_arith),
        hs₃.st (show slot w 16 + 8 + 8 ≤ Z by omega_arith), hs₃.ld (show slot w 16 + oD + 8 ≤ Z by unfold oD; omega_arith), hrd]
      done) rfl) fun t ⟨⟨mt, bx, r14⟩, kt⟩ => ?_
  refine ⟨?_, ?_, r14, (((k₁.trans k₂).trans k₃).trans kt).mono (by decide)⟩
  · rw [mt, m₃, o₂.word (d := slot w 20) (by omega_arith) (by omega_arith), m₂, m₁]
  · rw [bx, m₃, o₂.word (by unfold oD; omega_arith) (by unfold oD; omega_arith)]

/-- `bSave`: `d` and the matrix into the window, the stride back to `r9`, `r12 := n + 1`. -/
theorem bSave_ok {s : State} {B : Addr} {Z w n : Nat} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = off B (slot w 16)) (h14 : s.gpr .r14 = BitVec.ofNat 64 (8 * (w + 2)))
    (h15 : s.gpr .r15 = BitVec.ofNat 64 n) (hZ : slot w 16 + 64 ≤ Z) :
    WP isa (.block bSave) s fun t =>
      t.mem = ((((s.mem.writeW (off B (slot w 16 + oD)) (s.gpr .rbx)).writeW (off B (slot w 16 + oU)) (s.gpr .r9)).writeW
        (off B (slot w 16 + oV)) (s.gpr .r10)).writeW (off B (slot w 16 + oQ)) (s.gpr .r11)).writeW
        (off B (slot w 16 + oR)) (s.gpr .r12) ∧
      t.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.gpr .r12 = BitVec.ofNat 64 (n + 1) ∧
      Keep [.r9, .r12] s t := by
  refine WP.mono (WP.keep [.r9, .r12] (Q := fun t =>
      t.mem = ((((s.mem.writeW (off B (slot w 16 + oD)) (s.gpr .rbx)).writeW (off B (slot w 16 + oU)) (s.gpr .r9)).writeW
        (off B (slot w 16 + oV)) (s.gpr .r10)).writeW (off B (slot w 16 + oQ)) (s.gpr .r11)).writeW
        (off B (slot w 16 + oR)) (s.gpr .r12) ∧
      t.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.gpr .r12 = BitVec.ofNat 64 (n + 1)) ?_ rfl)
    fun t ⟨⟨a, b, c⟩, k⟩ => ⟨a, b, c, k⟩
  unfold bSave wm
  xrun [State.ea, hdi, offD, h14, h15, hs.st (show slot w 16 + oD + 8 ≤ Z by unfold oD; omega_arith),
    hs.st (show slot w 16 + oU + 8 ≤ Z by unfold oU; omega_arith), hs.st (show slot w 16 + oV + 8 ≤ Z by unfold oV; omega_arith),
    hs.st (show slot w 16 + oQ + 8 ≤ Z by unfold oQ; omega_arith), hs.st (show slot w 16 + oR + 8 ≤ Z by unfold oR; omega_arith)]
  rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat]

/-! ## The arithmetic of the updates -/

/-- The sign word of the top word, as the top half of the number. -/
theorem signW_half (m : Mem) (p : Addr) (e n : Nat) :
    signW (word m p (e + 8 * n)) = if 2 ^ (64 * n) * 2 ^ 63 ≤ wv m p e (n + 1) then 2 ^ 64 - 1 else 0 := by
  unfold signW
  have hl := wv_lt m p e n
  have hx := (word m p (e + 8 * n)).isLt
  rw [wv]
  by_cases h : 2 ^ 63 ≤ (word m p (e + 8 * n)).toNat
  · have : 2 ^ (64 * n) * 2 ^ 63 ≤ 2 ^ (64 * n) * (word m p (e + 8 * n)).toNat := Nat.mul_le_mul_left _ h
    simp only [h, ↓reduceIte, show 2 ^ (64 * n) * 2 ^ 63 ≤ wv m p e n + 2 ^ (64 * n) * (word m p (e + 8 * n)).toNat by omega_arith]
  · have : 2 ^ (64 * n) * ((word m p (e + 8 * n)).toNat + 1) ≤ 2 ^ (64 * n) * 2 ^ 63 :=
      Nat.mul_le_mul_left _ (by omega_arith)
    rw [Nat.mul_add_one] at this
    simp only [h, ↓reduceIte, show ¬ 2 ^ (64 * n) * 2 ^ 63 ≤ wv m p e n + 2 ^ (64 * n) * (word m p (e + 8 * n)).toNat by omega_arith]

/-- The low word of numbers congruent modulo `2^(64 (n + 1))`. -/
theorem low_cong' {m : Mem} {p : Addr} {e n : Nat} {x : Int}
    (h : (wv m p e (n + 1) : Int) % 2 ^ (64 * (n + 1)) = x % 2 ^ (64 * (n + 1))) :
    ((word m p e).toNat : Int) % 2 ^ 64 = x % 2 ^ 64 := by
  have hdvd : ((2 : Int) ^ 64) ∣ 2 ^ (64 * (n + 1)) := pow_dvd_pow 2 (by omega_arith)
  have low : ((word m p e).toNat : Int) % 2 ^ 64 = (wv m p e (n + 1) : Int) % 2 ^ 64 := by
    rw [wv_succ_low]; push_cast; rw [Int.add_mul_emod_self_left]
  rw [low, ← Int.emod_emod_of_dvd _ hdvd, h, Int.emod_emod_of_dvd _ hdvd]

/-- `absS c m`: `[c] := |[c]|` (the word as a signed number), the mask of its sign into `[m]`. -/
theorem absS_ok {s : State} {B : Addr} {Z eW c m : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = off B eW)
    (hc : eW + c + 8 ≤ Z) (hm : eW + m + 8 ≤ Z) :
    WP isa (.block (absS c m)) s fun t =>
      t.mem = (s.mem.writeW (off B (eW + m)) (mask (decide ((word s.mem B (eW + c)).toInt < 0)))).writeW
        (off B (eW + c)) (BitVec.ofNat 64 (word s.mem B (eW + c)).toInt.natAbs) ∧
      Keep [.rax, .rcx, .rdx] s t := by
  obtain ⟨e1, e2⟩ := abs_word (word s.mem B (eW + c))
  refine WP.mono (WP.keep [.rax, .rcx, .rdx] (Q := fun t =>
      t.mem = (s.mem.writeW (off B (eW + m)) (mask (decide ((word s.mem B (eW + c)).toInt < 0)))).writeW
        (off B (eW + c)) (BitVec.ofNat 64 (word s.mem B (eW + c)).toInt.natAbs)) ?_ rfl) fun t ⟨a, k⟩ => ⟨a, k⟩
  unfold absS wm
  xrun [State.ea, hdi, offD, hs.ld hc, hs.st hm, hs.st hc, e1, e2]
  rw [← e2, e1]

/-- `V ∈ [0, 2M)` congruent to `t ∈ [-M, M)` modulo `2M`, its sign word above it (`B - 1` where
`M ≤ V`): congruent to `t` modulo `2M B`. -/
theorem sext_cong {M V B : Nat} {t : Int} (hM : 0 < M) (hV : V < 2 * M)
    (hVt : (V : Int) % (2 * (M : Int)) = t % (2 * (M : Int)))
    (ht1 : -(M : Int) ≤ t) (ht2 : t < M) (hB : 1 ≤ B) :
    ((V + 2 * M * (if M ≤ V then B - 1 else 0) : Nat) : Int) % (2 * (M : Int) * B) = t % (2 * (M : Int) * B) := by
  have e := Divstep.tc_eq (H := (M : Int)) (x := t) (W := V) (by omega) ht1 ht2 (by omega) (by omega) hVt
  have sg := Divstep.tc_neg ht1 ht2 e
  by_cases h : t < 0
  · have hc : M ≤ V := by exact_mod_cast sg.mpr h
    simp only [hc, ↓reduceIte]
    simp only [h, ↓reduceIte] at e
    push_cast [Nat.cast_sub hB]
    rw [e, show t + 2 * (M : Int) + 2 * M * (B - 1) = t + 2 * M * B * 1 by grind, Int.add_mul_emod_self_left]
  · have hc : ¬ M ≤ V := fun h' => h (sg.mp (by exact_mod_cast h'))
    simp only [hc, ↓reduceIte, Nat.mul_zero, Nat.add_zero]
    simp only [h, ↓reduceIte, Int.add_zero] at e
    rw [e]

/-- `lin_term` over `N` words of memory and a word `S` above them. -/
theorem lin_term_ext (m : Mem) (p : Addr) (d N : Nat) (hd : d + 8 * N + 8 ≤ 2 ^ 64) (u : Int) (S : BitVec 64) :
    ((u.natAbs * (wvM m p d (mask (decide (u < 0))) N + 2 ^ (64 * N) * (S ^^^ mask (decide (u < 0))).toNat) +
        (if u < 0 then u.natAbs else 0) : Nat) : Int) % 2 ^ (64 * (N + 1)) =
      (u * (wv m p d N + 2 ^ (64 * N) * S.toNat : Nat)) % 2 ^ (64 * (N + 1)) := by
  have o := writeW_outside m p S (d := d + 8 * N) (by omega)
  have e1 : wvM (m.writeW (off p (d + 8 * N)) S) p d (mask (decide (u < 0))) (N + 1) =
      wvM m p d (mask (decide (u < 0))) N + 2 ^ (64 * N) * (S ^^^ mask (decide (u < 0))).toNat := by
    simp only [wvM]
    rw [word_writeW_self, wvM_congr fun i hi => o.word (by omega) (by omega)]
  have e2 : wv (m.writeW (off p (d + 8 * N)) S) p d (N + 1) = wv m p d N + 2 ^ (64 * N) * S.toNat :=
    wv_writeW_top _ _ _ _ _ (by omega)
  rw [← e1, ← e2]
  exact lin_term _ _ _ _ _

/-- The ones of the complements: `(|c| & mask(c < 0)).toNat`. -/
theorem ones_toNat {u v : Int} (hu : u.natAbs < 2 ^ 63) (hv : v.natAbs < 2 ^ 63) :
    ((BitVec.ofNat 64 u.natAbs &&& mask (decide (u < 0))) + (BitVec.ofNat 64 v.natAbs &&& mask (decide (v < 0)))).toNat =
      (if u < 0 then u.natAbs else 0) + (if v < 0 then v.natAbs else 0) := by
  rw [BitVec.toNat_add, and_mask_toNat, and_mask_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show u.natAbs < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show v.natAbs < 2 ^ 64 by omega)]
  simp only [decide_eq_true_eq]
  split <;> split <;> omega

/-- A row's sum, for the window holding `|u|`, `|v|` and their signs' masks: `u X + v Y` modulo
`2^(64 N)`. -/
theorem sum_cong {R : Rw} {c₁ m₁ c₂ m₂ : Nat} {u v : Int} (h₁ : R.c c₁ = BitVec.ofNat 64 u.natAbs)
    (h₂ : R.c c₂ = BitVec.ofNat 64 v.natAbs) (hm₁ : R.c m₁ = mask (decide (u < 0)))
    (hm₂ : R.c m₂ = mask (decide (v < 0))) (hu : u.natAbs < 2 ^ 63) (hv : v.natAbs < 2 ^ 63) (N : Nat) :
    (R.sum c₁ m₁ c₂ m₂ N : Int) % 2 ^ (64 * N) =
      (u * wv R.m R.B R.eA N + v * wv R.m R.B (R.eA + R.S) N) % 2 ^ (64 * N) := by
  unfold Rw.sum
  rw [h₁, h₂, hm₁, hm₂, ones_toNat hu hv, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show u.natAbs < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show v.natAbs < 2 ^ 64 by omega)]
  have e1 := lin_term R.m R.B R.eA N u
  have e2 := lin_term R.m R.B (R.eA + R.S) N v
  have key : ((u.natAbs * wvM R.m R.B R.eA (mask (decide (u < 0))) N +
      v.natAbs * wvM R.m R.B (R.eA + R.S) (mask (decide (v < 0))) N +
      ((if u < 0 then u.natAbs else 0) + (if v < 0 then v.natAbs else 0)) : Nat) : Int) =
      ((u.natAbs * wvM R.m R.B R.eA (mask (decide (u < 0))) N + (if u < 0 then u.natAbs else 0) : Nat) : Int) +
      ((v.natAbs * wvM R.m R.B (R.eA + R.S) (mask (decide (v < 0))) N + (if v < 0 then v.natAbs else 0) : Nat) : Int) := by
    rw [Nat.add_add_add_comm, Nat.cast_add]
  rw [key, Int.add_emod, e1, e2, ← Int.add_emod]

theorem two_H (n : Nat) : 2 * (2 ^ (64 * n) * 2 ^ 63) = 2 ^ (64 * (n + 1)) := by
  rw [pow64_succ, show (2 : Nat) ^ 64 = 2 * 2 ^ 63 by norm_num]; ring

/-- `fgRow`'s result as `Divstep.shr_nat` reads it: the shift of `y = 2^59 z`. -/
theorem fg_val {R : Rw} {c₁ m₁ c₂ m₂ n D : Nat} {u v f g z : Int}
    (hD : D = shrS n (R.sum c₁ m₁ c₂ m₂ (n + 1) % 2 ^ (64 * (n + 1))))
    (h₁ : R.c c₁ = BitVec.ofNat 64 u.natAbs) (h₂ : R.c c₂ = BitVec.ofNat 64 v.natAbs)
    (hm₁ : R.c m₁ = mask (decide (u < 0))) (hm₂ : R.c m₂ = mask (decide (v < 0)))
    (hu : u.natAbs < 2 ^ 63) (hv : v.natAbs < 2 ^ 63)
    (hf : (wv R.m R.B R.eA (n + 1) : Int) % 2 ^ (64 * (n + 1)) = f % 2 ^ (64 * (n + 1)))
    (hg : (wv R.m R.B (R.eA + R.S) (n + 1) : Int) % 2 ^ (64 * (n + 1)) = g % 2 ^ (64 * (n + 1)))
    (hz : u * f + v * g = 2 ^ 59 * z)
    (hb : -((2 ^ (64 * n) * 2 ^ 63 : Nat) : Int) ≤ u * f + v * g ∧ u * f + v * g < ((2 ^ (64 * n) * 2 ^ 63 : Nat) : Int)) :
    (D : Int) % 2 ^ (64 * (n + 1)) = z % 2 ^ (64 * (n + 1)) := by
  have e2 := two_H n
  have hc := Divstep.shr_nat (H := 2 ^ (64 * n) * 2 ^ 63) (V := R.sum c₁ m₁ c₂ m₂ (n + 1) % 2 ^ (64 * (n + 1)))
    (D := D) (c := 2 ^ 59) (B := 2 ^ 64) (y := u * f + v * g) (z := z) rfl rfl
    (Nat.mul_pos (Nat.two_pow_pos _) (by decide)) (by rw [e2]; exact Nat.mod_lt _ (Nat.two_pow_pos _))
    (by
      rw [e2]; push_cast
      rw [Int.emod_emod_of_dvd _ (dvd_refl _), sum_cong h₁ h₂ hm₁ hm₂ hu hv]
      exact Divstep.cong_comb hf hg)
    hb.1 hb.2 hz (by rw [hD, shrS, e2])
  rw [e2] at hc; exact_mod_cast hc

/-- `sum_mod64`: a row's sums over `j ≥ 1` words agree modulo `2^64`. -/
theorem sum_mod64 (R : Rw) (c₁ m₁ c₂ m₂ : Nat) : ∀ j, 1 ≤ j →
    R.sum c₁ m₁ c₂ m₂ j % 2 ^ 64 = R.sum c₁ m₁ c₂ m₂ 1 % 2 ^ 64
  | 0, h => absurd h (by decide)
  | 1, _ => rfl
  | j + 2, _ => by
    rw [Rw.sum_succ, ← sum_mod64 R c₁ m₁ c₂ m₂ (j + 1) (by omega), pow64_succ, Nat.mul_assoc,
      Nat.mul_left_comm, Nat.add_mul_mod_self_left]

/-- A number of `n + 1` words with its sign word above it: congruent to `x` modulo `2^(64 (n + 2))`
when it is `x` modulo `2^(64 (n + 1))` and `|x| < 2^(64 n + 63)`. -/
theorem ext_cong {m : Mem} {p : Addr} {e n : Nat} {x : Int}
    (hx : (wv m p e (n + 1) : Int) % 2 ^ (64 * (n + 1)) = x % 2 ^ (64 * (n + 1)))
    (h1 : -((2 ^ (64 * n) * 2 ^ 63 : Nat) : Int) ≤ x) (h2 : x < ((2 ^ (64 * n) * 2 ^ 63 : Nat) : Int)) :
    ((wv m p e (n + 1) + 2 ^ (64 * (n + 1)) *
      (BitVec.setWidth 64 (0 : BitVec 32) - word m p (e + 8 * n) >>> 63).toNat : Nat) : Int) %
      2 ^ (64 * (n + 1 + 1)) = x % 2 ^ (64 * (n + 1 + 1)) := by
  have e2 := two_H n
  rw [maskOf_toNat, signW_half, ← e2]
  have hc := sext_cong (M := 2 ^ (64 * n) * 2 ^ 63) (V := wv m p e (n + 1)) (B := 2 ^ 64) (t := x)
    (Nat.mul_pos (Nat.two_pow_pos _) (by decide)) (by rw [e2]; exact wv_lt _ _ _ _)
    (by rw [show (2 : Int) * ((2 ^ (64 * n) * 2 ^ 63 : Nat) : Int) = 2 ^ (64 * (n + 1)) by exact_mod_cast e2]
        exact hx) (by exact_mod_cast h1) (by exact_mod_cast h2) Nat.one_le_two_pow
  have e3 : 2 ^ (64 * (n + 1 + 1)) = 2 * (2 ^ (64 * n) * 2 ^ 63) * 2 ^ 64 := by rw [pow64_succ (n + 1), e2]
  rw [show (2 : Int) ^ (64 * (n + 1 + 1)) = 2 * ((2 ^ (64 * n) * 2 ^ 63 : Nat) : Int) * ((2 ^ 64 : Nat) : Int) by
    exact_mod_cast e3]
  exact hc

/-- `abRow`'s sum and sign words: `u A + v B` modulo `2^(64 (n + 2))` for the arrays `A`, `B`
sign-extended by a word. -/
theorem sg_cong {R : Rw} {c₁ m₁ c₂ m₂ : Nat} {u v : Int} (h₁ : R.c c₁ = BitVec.ofNat 64 u.natAbs)
    (h₂ : R.c c₂ = BitVec.ofNat 64 v.natAbs) (hm₁ : R.c m₁ = mask (decide (u < 0)))
    (hm₂ : R.c m₂ = mask (decide (v < 0))) (hu : u.natAbs < 2 ^ 63) (hv : v.natAbs < 2 ^ 63)
    (hz : R.eA + R.S + 8 * (R.n + 1) + 8 ≤ 2 ^ 64) :
    ((R.sum c₁ m₁ c₂ m₂ (R.n + 1) + 2 ^ (64 * (R.n + 1)) * R.sg c₁ m₁ c₂ m₂ : Nat) : Int) % 2 ^ (64 * (R.n + 1 + 1)) =
      (u * (wv R.m R.B R.eA (R.n + 1) + 2 ^ (64 * (R.n + 1)) *
          (BitVec.setWidth 64 (0 : BitVec 32) - word R.m R.B (R.eA + 8 * R.n) >>> 63).toNat : Nat) +
        v * (wv R.m R.B (R.eA + R.S) (R.n + 1) + 2 ^ (64 * (R.n + 1)) *
          (BitVec.setWidth 64 (0 : BitVec 32) - word R.m R.B (R.eA + R.S + 8 * R.n) >>> 63).toNat : Nat)) %
        2 ^ (64 * (R.n + 1 + 1)) := by
  unfold Rw.sum Rw.sg
  rw [h₁, h₂, hm₁, hm₂, ones_toNat hu hv, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show u.natAbs < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show v.natAbs < 2 ^ 64 by omega)]
  have e1 := lin_term_ext R.m R.B R.eA (R.n + 1) (by omega) u
    (BitVec.setWidth 64 (0 : BitVec 32) - word R.m R.B (R.eA + 8 * R.n) >>> 63)
  have e2 := lin_term_ext R.m R.B (R.eA + R.S) (R.n + 1) (by omega) v
    (BitVec.setWidth 64 (0 : BitVec 32) - word R.m R.B (R.eA + R.S + 8 * R.n) >>> 63)
  have key : ((u.natAbs * wvM R.m R.B R.eA (mask (decide (u < 0))) (R.n + 1) +
      v.natAbs * wvM R.m R.B (R.eA + R.S) (mask (decide (v < 0))) (R.n + 1) +
      ((if u < 0 then u.natAbs else 0) + (if v < 0 then v.natAbs else 0)) + 2 ^ (64 * (R.n + 1)) *
      (u.natAbs * ((BitVec.setWidth 64 (0 : BitVec 32) - word R.m R.B (R.eA + 8 * R.n) >>> 63) ^^^
        mask (decide (u < 0))).toNat +
       v.natAbs * ((BitVec.setWidth 64 (0 : BitVec 32) - word R.m R.B (R.eA + R.S + 8 * R.n) >>> 63) ^^^
        mask (decide (v < 0))).toNat) : Nat) : Int) =
      ((u.natAbs * (wvM R.m R.B R.eA (mask (decide (u < 0))) (R.n + 1) + 2 ^ (64 * (R.n + 1)) *
        ((BitVec.setWidth 64 (0 : BitVec 32) - word R.m R.B (R.eA + 8 * R.n) >>> 63) ^^^ mask (decide (u < 0))).toNat) +
        (if u < 0 then u.natAbs else 0) : Nat) : Int) +
      ((v.natAbs * (wvM R.m R.B (R.eA + R.S) (mask (decide (v < 0))) (R.n + 1) + 2 ^ (64 * (R.n + 1)) *
        ((BitVec.setWidth 64 (0 : BitVec 32) - word R.m R.B (R.eA + R.S + 8 * R.n) >>> 63) ^^^
          mask (decide (v < 0))).toNat) + (if v < 0 then v.natAbs else 0) : Nat) : Int) := by
    push_cast; ring
  rw [key]
  have e4 : ((2 : Nat) : Int) = 2 := rfl
  rw [Int.add_emod]
  simp only [e4] at *
  rw [e1, e2, ← Int.add_emod]

/-- `abRow`'s result as `Divstep.mredRaw_nat` reads it. -/
theorem ab_val {R : Rw} {c₁ m₁ c₂ m₂ D p mi : Nat} {u v a b : Int}
    (hD : D = (R.dsum c₁ m₁ c₂ m₂ (R.n + 1) + 2 ^ (64 * (R.n + 1)) * R.sg c₁ m₁ c₂ m₂) / 2 ^ 64 % 2 ^ (64 * (R.n + 1)))
    (h₁ : R.c c₁ = BitVec.ofNat 64 u.natAbs) (h₂ : R.c c₂ = BitVec.ofNat 64 v.natAbs)
    (hm₁ : R.c m₁ = mask (decide (u < 0))) (hm₂ : R.c m₂ = mask (decide (v < 0)))
    (hu : u.natAbs < 2 ^ 63) (hv : v.natAbs < 2 ^ 63) (hmi : (R.c oMi).toNat = mi)
    (hP : wv R.m R.B (R.eA + 4 * R.S) (R.n + 1) = p)
    (ha : (wv R.m R.B R.eA (R.n + 1) : Int) % 2 ^ (64 * (R.n + 1)) = a % 2 ^ (64 * (R.n + 1)))
    (hb : (wv R.m R.B (R.eA + R.S) (R.n + 1) : Int) % 2 ^ (64 * (R.n + 1)) = b % 2 ^ (64 * (R.n + 1)))
    (ha' : -((2 ^ (64 * R.n) * 2 ^ 63 : Nat) : Int) ≤ a ∧ a < ((2 ^ (64 * R.n) * 2 ^ 63 : Nat) : Int))
    (hb' : -((2 ^ (64 * R.n) * 2 ^ 63 : Nat) : Int) ≤ b ∧ b < ((2 ^ (64 * R.n) * 2 ^ 63 : Nat) : Int))
    (hp : 0 < p) (hpA : p < 2 ^ (64 * R.n)) (hm : (p * mi + 1) % 2 ^ 64 = 0) (ht : |u * a + v * b| ≤ 2 ^ 63 * p)
    (hz : R.eA + R.S + 8 * (R.n + 1) + 8 ≤ 2 ^ 64) :
    (D : Int) % 2 ^ (64 * (R.n + 1)) = Divstep.mredRaw p mi (u * a + v * b) % 2 ^ (64 * (R.n + 1)) := by
  have e2 := two_H R.n
  have eAB : 2 ^ (64 * (R.n + 1)) = 2 ^ (64 * R.n) * 2 ^ 64 := pow64_succ _
  have eABB : 2 ^ (64 * R.n) * 2 ^ 64 * 2 ^ 64 = 2 * (2 ^ (64 * R.n) * 2 ^ 63) * 2 ^ 64 := by rw [← eAB, e2]
  set S := R.sum c₁ m₁ c₂ m₂ (R.n + 1) with hS
  set W := S % 2 ^ (64 * (R.n + 1)) with hW
  -- `W ≡ t` modulo `2^(64 (n + 1))`
  have hWt : (W : Int) % 2 ^ (64 * (R.n + 1)) = (u * a + v * b) % 2 ^ (64 * (R.n + 1)) := by
    rw [hW]; push_cast
    rw [Int.emod_emod_of_dvd _ (dvd_refl _), hS, sum_cong h₁ h₂ hm₁ hm₂ hu hv]
    exact Divstep.cong_comb ha hb
  have hk : R.kv c₁ m₁ c₂ m₂ = W % 2 ^ 64 * mi % 2 ^ 64 := by
    rw [Rw.kv, hmi, hW, Nat.mod_mod_of_dvd _ (by rw [eAB]; exact Nat.dvd_mul_left _ _), hS,
      sum_mod64 _ _ _ _ _ (R.n + 1) (by omega)]
  -- `D = E / 2^64`
  have hDE : D = (W + 2 ^ (64 * R.n) * 2 ^ 64 * (if 2 ^ (64 * R.n) * 2 ^ 63 ≤ W then 2 ^ 64 - 1 else 0) +
      R.kv c₁ m₁ c₂ m₂ * p) % (2 ^ (64 * R.n) * 2 ^ 64 * 2 ^ 64) / 2 ^ 64 := by
    -- both sums are `t` modulo `2^(64 (n + 2))`
    have hL := sg_cong (c₁ := c₁) (m₁ := m₁) (c₂ := c₂) (m₂ := m₂) h₁ h₂ hm₁ hm₂ hu hv hz
    simp only [Nat.cast_ofNat] at hL
    have hA := ext_cong (m := R.m) (p := R.B) (e := R.eA) ha ha'.1 ha'.2
    have hB := ext_cong (m := R.m) (p := R.B) (e := R.eA + R.S) hb hb'.1 hb'.2
    have hL' : ((S + 2 ^ (64 * (R.n + 1)) * R.sg c₁ m₁ c₂ m₂ : Nat) : Int) % 2 ^ (64 * (R.n + 1 + 1)) =
        (u * a + v * b) % 2 ^ (64 * (R.n + 1 + 1)) := by
      rw [hS, hL]; exact Divstep.cong_comb hA hB
    have tb : (2 : Int) ^ 63 * p < ((2 ^ (64 * R.n) * 2 ^ 63 : Nat) : Int) := by
      push_cast; have : (p : Int) < 2 ^ (64 * R.n) := by exact_mod_cast hpA
      nlinarith [show (0 : Int) < 2 ^ 63 by norm_num]
    have ht' := abs_le.mp ht
    have hR' := sext_cong (M := 2 ^ (64 * R.n) * 2 ^ 63) (V := W) (B := 2 ^ 64) (t := u * a + v * b)
      (Nat.mul_pos (Nat.two_pow_pos _) (by decide)) (by rw [e2]; exact Nat.mod_lt _ (Nat.two_pow_pos _))
      (by rw [show (2 : Int) * ((2 ^ (64 * R.n) * 2 ^ 63 : Nat) : Int) = 2 ^ (64 * (R.n + 1)) by exact_mod_cast e2]
          exact hWt)
      (by linarith) (by linarith) Nat.one_le_two_pow
    have e5 : (2 : Int) * ((2 ^ (64 * R.n) * 2 ^ 63 : Nat) : Int) * ((2 ^ 64 : Nat) : Int) =
        2 ^ (64 * (R.n + 1 + 1)) := by
      have : 2 * (2 ^ (64 * R.n) * 2 ^ 63) * 2 ^ 64 = 2 ^ (64 * (R.n + 1 + 1)) := by rw [pow64_succ (R.n + 1), e2]
      exact_mod_cast this
    rw [e5, e2] at hR'
    have hc := hL'.trans hR'.symm
    have hNat : (S + 2 ^ (64 * (R.n + 1)) * R.sg c₁ m₁ c₂ m₂) % 2 ^ (64 * (R.n + 1 + 1)) =
        (W + 2 ^ (64 * (R.n + 1)) * (if 2 ^ (64 * R.n) * 2 ^ 63 ≤ W then 2 ^ 64 - 1 else 0)) %
          2 ^ (64 * (R.n + 1 + 1)) := by exact_mod_cast hc
    have e6 : 2 ^ (64 * (R.n + 1 + 1)) = 2 ^ (64 * R.n) * 2 ^ 64 * 2 ^ 64 := by rw [pow64_succ (R.n + 1), eAB]
    rw [e6, eAB] at hNat
    rw [hD, Rw.dsum, hP, ← hS, eAB, ← Nat.mod_mul_right_div_self,
      show 2 ^ 64 * (2 ^ (64 * R.n) * 2 ^ 64) = 2 ^ (64 * R.n) * 2 ^ 64 * 2 ^ 64 by ring]
    refine congrArg (· / 2 ^ 64) ?_
    rw [show S + R.kv c₁ m₁ c₂ m₂ * p + 2 ^ (64 * R.n) * 2 ^ 64 * R.sg c₁ m₁ c₂ m₂ =
      (S + 2 ^ (64 * R.n) * 2 ^ 64 * R.sg c₁ m₁ c₂ m₂) + R.kv c₁ m₁ c₂ m₂ * p by ring,
      Nat.add_mod, hNat, ← Nat.add_mod]
  have hmr := Divstep.mredRaw_nat (A := 2 ^ (64 * R.n)) (B := 2 ^ 64) (H := 2 ^ 63) (p := p) (m := mi) (W := W)
    (k := R.kv c₁ m₁ c₂ m₂) (t := u * a + v * b) (R := D) rfl rfl (Nat.two_pow_pos _) hp hpA hm ht
    (by rw [← eAB]; exact Nat.mod_lt _ (Nat.two_pow_pos _))
    (by rw [← eAB]; push_cast; exact hWt) hk rfl hDE
  have e7 : ((2 ^ (64 * R.n) * 2 ^ 64 : Nat) : Int) = 2 ^ (64 * (R.n + 1)) := by rw [← eAB]; push_cast; rfl
  rw [e7] at hmr
  exact hmr

/-- The facts of the working space a batch's updates need. -/
structure Lay (B : Addr) (Z w n : Nat) : Prop where
  n1 : 1 ≤ n
  nw : n ≤ w
  w2 : 2 ≤ w
  w24 : w < 2 ^ 24
  z : slot w 26 ≤ Z
  nowrap : B.toNat + Z ≤ 2 ^ 64

/-! ## A batch -/

/-- The count of batches less one, its zero flag whether it is now zero. -/
theorem decRsi_ok (s : State) {j : Nat} (hj : 1 ≤ j) (hj' : j < 2 ^ 64)
    (hb : s.gpr .rsi = BitVec.ofNat 64 j) :
    WP isa (.block [.alu .sub .rsi (.imm 1)]) s fun s' =>
      s'.gpr .rsi = BitVec.ofNat 64 (j - 1) ∧ s'.zf = some (decide (j - 1 = 0)) ∧ s'.mem = s.mem ∧
        Keep [.rsi] s s' := by
  have e : BitVec.ofNat 64 j - BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 (j - 1) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (BitVec.signExtend 64 (1 : BitVec 32)).toNat = 1 from rfl]
    rw [Nat.mod_eq_of_lt hj', Nat.mod_eq_of_lt (by omega_arith : j - 1 < 2 ^ 64)]
    omega_arith
  have ez : (BitVec.ofNat 64 (j - 1) == 0) = decide (j - 1 = 0) := by
    by_cases h : j - 1 = 0
    · rw [h]; simp
    · rw [decide_eq_false h]
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro he
      have := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at this
      exact h this
  refine WP.mono (WP.keep [.rsi] (Q := fun t => t.gpr .rsi = BitVec.ofNat 64 (j - 1) ∧
    t.zf = some (decide (j - 1 = 0)) ∧ t.mem = s.mem) ?_ rfl) fun t ⟨⟨a, b, c⟩, k⟩ => ⟨a, b, c, k⟩
  have e' : BitVec.ofNat 64 j - 1 = BitVec.ofNat 64 (j - 1) := e
  xrun [hb]
  rw [e']; exact ⟨rfl, ez⟩

theorem mw (m : Mem) (B : Addr) (o d : Nat) : VG.Proof.Mont.word m (off B o) d = word m B (o + d) := by
  simp only [VG.Proof.Mont.word, VG.Proof.Mont.off, Bignum.word, off, BitVec.add_assoc, BitVec.ofNat_add]

/-- The state between batches: `rdi` the window, the stride, `n`, and `d`,
`-m⁻¹`, `m`, `f`, `g`, `a`, `b` in the window and arrays (modulo `2^(64 (n + 1))`). -/
structure BS (B : Addr) (Z w n p mi : Nat) (I : Divstep.IState) (s : State) : Prop where
  scr : Scr s B Z
  rdi : s.gpr .rdi = off B (slot w 16)
  r9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2))
  r15 : s.gpr .r15 = BitVec.ofNat 64 n
  d : word s.mem B (slot w 16 + oD) = BitVec.ofInt 64 I.d
  mi : (word s.mem B (slot w 16 + oMi)).toNat = mi
  P : wv s.mem B (slot w 25) n = p
  Pz : word s.mem B (slot w 25 + 8 * n) = 0
  f : (wv s.mem B (slot w 19) (n + 1) : Int) % 2 ^ (64 * (n + 1)) = I.f % 2 ^ (64 * (n + 1))
  g : (wv s.mem B (slot w 20) (n + 1) : Int) % 2 ^ (64 * (n + 1)) = I.g % 2 ^ (64 * (n + 1))
  a : (wv s.mem B (slot w 21) (n + 1) : Int) % 2 ^ (64 * (n + 1)) = I.a % 2 ^ (64 * (n + 1))
  b : (wv s.mem B (slot w 22) (n + 1) : Int) % 2 ^ (64 * (n + 1)) = I.b % 2 ^ (64 * (n + 1))

/-- `BS` without `a` and `b`: the state between the batches of the GCD alone. -/
structure BSg (B : Addr) (Z w n p mi : Nat) (I : Divstep.IState) (s : State) : Prop where
  scr : Scr s B Z
  rdi : s.gpr .rdi = off B (slot w 16)
  r9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2))
  r15 : s.gpr .r15 = BitVec.ofNat 64 n
  d : word s.mem B (slot w 16 + oD) = BitVec.ofInt 64 I.d
  mi : (word s.mem B (slot w 16 + oMi)).toNat = mi
  P : wv s.mem B (slot w 25) n = p
  Pz : word s.mem B (slot w 25 + 8 * n) = 0
  f : (wv s.mem B (slot w 19) (n + 1) : Int) % 2 ^ (64 * (n + 1)) = I.f % 2 ^ (64 * (n + 1))
  g : (wv s.mem B (slot w 20) (n + 1) : Int) % 2 ^ (64 * (n + 1)) = I.g % 2 ^ (64 * (n + 1))

theorem BS.toG {B : Addr} {Z w n p mi : Nat} {I : Divstep.IState} {s : State} (h : BS B Z w n p mi I s) :
    BSg B Z w n p mi I s :=
  ⟨h.scr, h.rdi, h.r9, h.r15, h.d, h.mi, h.P, h.Pz, h.f, h.g⟩

theorem dsteps_ok {s : State} {B : Addr} {Z w n p mi : Nat} (L : Lay B Z w n) {I : Divstep.IState}
    (h : BSg B Z w n p mi I s) (hd : |I.d| ≤ 2 ^ 30) (hodd : I.f % 2 = 1) :
    WP isa (.block (bStart ++ bWords ++ bSave)) s fun t =>
      word t.mem B (slot w 16 + oD) = BitVec.ofInt 64 (Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).d ∧
      word t.mem B (slot w 16 + oU) = BitVec.ofInt 64 (Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).u ∧
      word t.mem B (slot w 16 + oV) = BitVec.ofInt 64 (Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).v ∧
      word t.mem B (slot w 16 + oQ) = BitVec.ofInt 64 (Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).q ∧
      word t.mem B (slot w 16 + oR) = BitVec.ofInt 64 (Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).r ∧
      Frm B [(slot w 16, 64)] s.mem t.mem ∧ t.gpr .rdi = off B (slot w 16) ∧
      t.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.gpr .r12 = BitVec.ofNat 64 (n + 1) ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14] s t := by
  have hN := L.nowrap
  have hn1 := L.n1; have hnw := L.nw; have hw2' := L.w2; have hZ := L.z
  have e16 := slot_eq w 16; have e19 := slot_eq w 19; have e20 := slot_eq w 20; have e26 := slot_eq w 26
  set T0 := Divstep.MSt.init I.d I.f I.g with hT0
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (bStart_ok h.scr h.rdi h.r9 hw2' hZ) fun s₁ ⟨m₁, bx₁, r14₁, k₁⟩ => ?_
  have hs₁ := h.scr.congr k₁.2.2
  have di₁ : s₁.gpr .rdi = off B (slot w 16) := (k₁.gpr (by decide)).trans h.rdi
  have oS0 := writeW_outside s.mem B (word s.mem B (slot w 19)) (d := slot w 16) (by omega_arith)
  have oS8 := writeW_outside (s.mem.writeW (off B (slot w 16)) (word s.mem B (slot w 19))) B
    (word s.mem B (slot w 20)) (d := slot w 16 + 8) (by omega_arith)
  have w0' : word s₁.mem B (slot w 16) = word s.mem B (slot w 19) := by
    rw [m₁, oS8.word (by omega_arith) (by omega_arith)]; exact word_writeW_self _ _ _ _
  have w8' : word s₁.mem B (slot w 16 + 8) = word s.mem B (slot w 20) := by
    rw [m₁]; exact word_writeW_self _ _ _ _
  have c₁ : VG.Proof.Rsa.X86_64.Chunk.CScr s₁ (off B (slot w 16)) 96 :=
    ⟨hs₁.sub (by omega_arith) (by decide), di₁⟩
  have ch : VG.Proof.Weierstrass.X86_64.ChunkAt (off B (slot w 16)) 0 64 true T0 s₁ :=
    ⟨by rw [bx₁, h.d]; rfl, by rw [mw, Nat.add_zero, w0']; exact low_cong' h.f,
      by rw [mw, Nat.zero_add, w8']; exact low_cong' h.g, fun _ => ⟨rfl, rfl, rfl, rfl⟩,
      fun h => absurd h (by decide)⟩
  refine WP.mono (bWords_ok c₁ (by decide) hodd hd ch) fun s₂ ⟨d₂, u₂, v₂, q₂, r₂, o₂, k₂⟩ => ?_
  have hs₂ := hs₁.congr k₂.wr
  have di₂ : s₂.gpr .rdi = off B (slot w 16) := (k₂.gpr _ (by decide)).trans di₁
  refine WP.mono (bSave_ok hs₂ di₂ ((k₂.gpr _ (by decide)).trans r14₁)
    ((k₂.gpr _ (by decide)).trans ((k₁.gpr (by decide)).trans h.r15)) (by omega_arith))
    fun t ⟨mt, r9t, r12t, kt⟩ => ?_
  have ap : ∀ (m : Mem) (e d : Nat) (v : BitVec 64), d + 8 ≤ e ∨ e + 8 ≤ d → e + 8 ≤ Z → d + 8 ≤ Z →
      word (m.writeW (off B e) v) B d = word m B d := fun m e d v h1 h2 h3 =>
    (writeW_outside m B v (by omega_arith)).word h1 (by omega_arith)
  have hk2 : Keep [.rax, .rbx, .rcx, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12, .r13] s₁ s₂ := ⟨k₂.gpr, k₂.rd, k₂.wr⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, (kt.gpr (by decide)).trans di₂, r9t, r12t,
    ((k₁.trans hk2).trans kt).mono (by decide)⟩
  · rw [mt, ap _ _ _ _ (by unfold oD oR; omega_arith) (by unfold oR; omega_arith) (by unfold oD; omega_arith),
      ap _ _ _ _ (by unfold oD oQ; omega_arith) (by unfold oQ; omega_arith) (by unfold oD; omega_arith),
      ap _ _ _ _ (by unfold oD oV; omega_arith) (by unfold oV; omega_arith) (by unfold oD; omega_arith),
      ap _ _ _ _ (by unfold oD oU; omega_arith) (by unfold oU; omega_arith) (by unfold oD; omega_arith), word_writeW_self, d₂]
  · rw [mt, ap _ _ _ _ (by unfold oU oR; omega_arith) (by unfold oR; omega_arith) (by unfold oU; omega_arith),
      ap _ _ _ _ (by unfold oU oQ; omega_arith) (by unfold oQ; omega_arith) (by unfold oU; omega_arith),
      ap _ _ _ _ (by unfold oU oV; omega_arith) (by unfold oV; omega_arith) (by unfold oU; omega_arith), word_writeW_self, u₂]
  · rw [mt, ap _ _ _ _ (by unfold oV oR; omega_arith) (by unfold oR; omega_arith) (by unfold oV; omega_arith),
      ap _ _ _ _ (by unfold oV oQ; omega_arith) (by unfold oQ; omega_arith) (by unfold oV; omega_arith), word_writeW_self, v₂]
  · rw [mt, ap _ _ _ _ (by unfold oQ oR; omega_arith) (by unfold oR; omega_arith) (by unfold oQ; omega_arith), word_writeW_self, q₂]
  · rw [mt, word_writeW_self, r₂]
  · have fo := Frm.of_outside_off (B := B) (o := slot w 16) (d := 0) (n := 24) o₂ (by omega_arith) (by omega_arith)
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hx
    have hx' : ofs B x < slot w 16 ∨ slot w 16 + 64 ≤ ofs B x := hx
    rw [mt]
    rw [writeW_outside _ B _ (d := slot w 16 + oR) (by unfold oR; omega_arith) x (by unfold oR; omega_arith),
      writeW_outside _ B _ (d := slot w 16 + oQ) (by unfold oQ; omega_arith) x (by unfold oQ; omega_arith),
      writeW_outside _ B _ (d := slot w 16 + oV) (by unfold oV; omega_arith) x (by unfold oV; omega_arith),
      writeW_outside _ B _ (d := slot w 16 + oU) (by unfold oU; omega_arith) x (by unfold oU; omega_arith),
      writeW_outside _ B _ (d := slot w 16 + oD) (by unfold oD; omega_arith) x (by unfold oD; omega_arith)]
    rw [fo x (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; omega_arith), m₁,
      oS8 x (by omega_arith), oS0 x (by omega_arith)]

theorem wW (m : Mem) (B : Addr) {e d : Nat} (v : BitVec 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d) (hz : e + 8 ≤ 2 ^ 64)
    (hz' : d + 8 ≤ 2 ^ 64) : word (m.writeW (off B e) v) B d = word m B d :=
  (writeW_outside m B v hz).word h hz'

/-- The four `absS`: the coefficients' magnitudes over them and their signs' masks. -/
theorem abs4_ok {s : State} {B : Addr} {Z eW : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = off B eW)
    (hW : eW + 96 ≤ Z) :
    WP isa (.block (absS oU oMu ++ absS oV oMv ++ absS oQ oMq ++ absS oR oMr)) s fun t =>
      word t.mem B (eW + oU) = BitVec.ofNat 64 (word s.mem B (eW + oU)).toInt.natAbs ∧
      word t.mem B (eW + oMu) = mask (decide ((word s.mem B (eW + oU)).toInt < 0)) ∧
      word t.mem B (eW + oV) = BitVec.ofNat 64 (word s.mem B (eW + oV)).toInt.natAbs ∧
      word t.mem B (eW + oMv) = mask (decide ((word s.mem B (eW + oV)).toInt < 0)) ∧
      word t.mem B (eW + oQ) = BitVec.ofNat 64 (word s.mem B (eW + oQ)).toInt.natAbs ∧
      word t.mem B (eW + oMq) = mask (decide ((word s.mem B (eW + oQ)).toInt < 0)) ∧
      word t.mem B (eW + oR) = BitVec.ofNat 64 (word s.mem B (eW + oR)).toInt.natAbs ∧
      word t.mem B (eW + oMr) = mask (decide ((word s.mem B (eW + oR)).toInt < 0)) ∧
      word t.mem B (eW + oD) = word s.mem B (eW + oD) ∧ word t.mem B (eW + oMi) = word s.mem B (eW + oMi) ∧
      Frm B [(eW, 96)] s.mem t.mem ∧ Keep [.rax, .rcx, .rdx] s t := by
  have hN := hs.nowrap
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (absS_ok hs hdi (by unfold oU; omega) (by unfold oMu; omega)) fun s₁ ⟨m₁, k₁⟩ => ?_
  refine WP.mono (absS_ok (hs.congr k₁.2.2) ((k₁.gpr (by decide)).trans hdi) (by unfold oV; omega)
    (by unfold oMv; omega)) fun s₂ ⟨m₂, k₂⟩ => ?_
  refine WP.mono (absS_ok (hs.congr (k₂.2.2.trans k₁.2.2)) (((k₁.trans k₂).gpr (by decide)).trans hdi)
    (by unfold oQ; omega) (by unfold oMq; omega)) fun s₃ ⟨m₃, k₃⟩ => ?_
  refine WP.mono (absS_ok (hs.congr ((k₁.trans k₂).trans k₃).2.2) ((((k₁.trans k₂).trans k₃).gpr (by decide)).trans hdi)
    (by unfold oR; omega) (by unfold oMr; omega)) fun t ⟨m₄, k₄⟩ => ?_
  rw [m₄, m₃, m₂, m₁]
  simp only [oU, oV, oQ, oR, oMu, oMv, oMq, oMr, oD, oMi] at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ((k₁.trans k₂).trans (k₃.trans k₄)).mono (by decide)⟩
  all_goals first
    | (intro x hx
       simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hx
       rw [writeW_outside _ B _ (d := eW + 56) (by omega) x (by omega), writeW_outside _ B _ (d := eW + 8) (by omega) x (by omega),
         writeW_outside _ B _ (d := eW + 48) (by omega) x (by omega), writeW_outside _ B _ (d := eW + 0) (by omega) x (by omega),
         writeW_outside _ B _ (d := eW + 40) (by omega) x (by omega), writeW_outside _ B _ (d := eW + 72) (by omega) x (by omega),
         writeW_outside _ B _ (d := eW + 32) (by omega) x (by omega), writeW_outside _ B _ (d := eW + 64) (by omega) x (by omega)])
    | (simp (disch := omega) only [word_writeW_self, wW] <;> rfl)

/-- A batch's first block: the divsteps, then the coefficients' magnitudes and masks. -/
theorem first_ok {s : State} {B : Addr} {Z w n p mi : Nat} (L : Lay B Z w n) {I : Divstep.IState}
    (h : BSg B Z w n p mi I s) (hd : |I.d| ≤ 2 ^ 30) (hodd : I.f % 2 = 1) :
    WP isa (.block ((bStart ++ bWords ++ bSave) ++ (absS oU oMu ++ absS oV oMv ++ absS oQ oMq ++ absS oR oMr))) s
      fun t =>
      word t.mem B (slot w 16 + oD) = BitVec.ofInt 64 (Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).d ∧
      word t.mem B (slot w 16 + oU) = BitVec.ofNat 64 (Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).u.natAbs ∧
      word t.mem B (slot w 16 + oMu) = mask (decide ((Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).u < 0)) ∧
      word t.mem B (slot w 16 + oV) = BitVec.ofNat 64 (Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).v.natAbs ∧
      word t.mem B (slot w 16 + oMv) = mask (decide ((Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).v < 0)) ∧
      word t.mem B (slot w 16 + oQ) = BitVec.ofNat 64 (Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).q.natAbs ∧
      word t.mem B (slot w 16 + oMq) = mask (decide ((Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).q < 0)) ∧
      word t.mem B (slot w 16 + oR) = BitVec.ofNat 64 (Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).r.natAbs ∧
      word t.mem B (slot w 16 + oMr) = mask (decide ((Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).r < 0)) ∧
      (word t.mem B (slot w 16 + oMi)).toNat = mi ∧
      Frm B [(slot w 16, 96)] s.mem t.mem ∧ t.gpr .rdi = off B (slot w 16) ∧
      t.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14] s t := by
  have hN := L.nowrap; have hw2' := L.w2; have hZ := L.z
  have e16 := slot_eq w 16; have e26 := slot_eq w 26
  obtain ⟨bnd₁, bnd₂⟩ := Divstep.msteps_bnd I.d I.f I.g 59
  rw [WP.block_append_iff]
  refine WP.mono (dsteps_ok L h hd hodd) fun s₁ ⟨d₁, u₁, v₁, q₁, r₁, f₁, di₁, r9₁, _, k₁⟩ => ?_
  refine WP.mono (abs4_ok (h.scr.congr k₁.2.2) di₁ (by omega_arith))
    fun t ⟨u₂, mu₂, v₂, mv₂, q₂, mq₂, r₂, mr₂, d₂, mi₂, f₂, k₂⟩ => ?_
  have ts : ∀ {x : Int}, |x| ≤ 2 ^ 59 → (BitVec.ofInt 64 x).toInt = x := fun h => Divstep.toInt_small h
  have hu : |(Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).u| ≤ 2 ^ 59 := by
    have := abs_nonneg (Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).v; linarith [bnd₁]
  have hv : |(Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).v| ≤ 2 ^ 59 := by
    have := abs_nonneg (Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).u; linarith [bnd₁]
  have hq : |(Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).q| ≤ 2 ^ 59 := by
    have := abs_nonneg (Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).r; linarith [bnd₂]
  have hr : |(Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).r| ≤ 2 ^ 59 := by
    have := abs_nonneg (Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).q; linarith [bnd₂]
  rw [u₁, ts hu] at u₂ mu₂; rw [v₁, ts hv] at v₂ mv₂; rw [q₁, ts hq] at q₂ mq₂; rw [r₁, ts hr] at r₂ mr₂
  have miS : word s₁.mem B (slot w 16 + oMi) = word s.mem B (slot w 16 + oMi) :=
    f₁.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; dsimp only; unfold oMi; omega_arith)
      (by unfold oMi; omega_arith)
  refine ⟨by rw [d₂, d₁], u₂, mu₂, v₂, mv₂, q₂, mq₂, r₂, mr₂, by rw [mi₂, miS]; exact h.mi, ?_,
    (k₂.gpr (by decide)).trans di₁, (k₂.gpr (by decide)).trans r9₁, (k₁.trans k₂).mono (by decide)⟩
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hx
  rw [f₂ x (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; exact hx),
    f₁ x (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; omega_arith)]

theorem batch_eq : batch = seqs (([.block ((bStart ++ bWords ++ bSave) ++
    (absS oU oMu ++ absS oV oMv ++ absS oQ oMq ++ absS oR oMr))] : List (Prog isa)) ++ fgRow ++ abRow ++
    ([.block ([.alu .sub .rsi (.imm 1)] : List Instr)] : List (Prog isa))) := by
  simp only [batch, List.append_assoc]

/-- The window after a batch's first block, for the matrix `u v q r`. -/
structure Win (B : Addr) (w : Nat) (u v q r : Int) (s : State) : Prop where
  hU : word s.mem B (slot w 16 + oU) = BitVec.ofNat 64 u.natAbs
  hMu : word s.mem B (slot w 16 + oMu) = mask (decide (u < 0))
  hV : word s.mem B (slot w 16 + oV) = BitVec.ofNat 64 v.natAbs
  hMv : word s.mem B (slot w 16 + oMv) = mask (decide (v < 0))
  hQ : word s.mem B (slot w 16 + oQ) = BitVec.ofNat 64 q.natAbs
  hMq : word s.mem B (slot w 16 + oMq) = mask (decide (q < 0))
  hR : word s.mem B (slot w 16 + oR) = BitVec.ofNat 64 r.natAbs
  hMr : word s.mem B (slot w 16 + oMr) = mask (decide (r < 0))
  huv : |u| + |v| ≤ 2 ^ 59
  hqr : |q| + |r| ≤ 2 ^ 59

theorem natAbs_lt {x : Int} (h : |x| ≤ 2 ^ 59) : x.natAbs < 2 ^ 63 := by
  have := Int.natCast_natAbs x; omega_arith

theorem natAbs_add {x y : Int} (h : |x| + |y| ≤ 2 ^ 59) : x.natAbs + y.natAbs ≤ 2 ^ 59 := by
  have := Int.natCast_natAbs x; have := Int.natCast_natAbs y; omega_arith

theorem Win.U59 {B : Addr} {w : Nat} {u v q r : Int} {s : State} (h : Win B w u v q r s) : |u| ≤ 2 ^ 59 := by
  have := abs_nonneg v; linarith [h.huv]
theorem Win.V59 {B : Addr} {w : Nat} {u v q r : Int} {s : State} (h : Win B w u v q r s) : |v| ≤ 2 ^ 59 := by
  have := abs_nonneg u; linarith [h.huv]
theorem Win.Q59 {B : Addr} {w : Nat} {u v q r : Int} {s : State} (h : Win B w u v q r s) : |q| ≤ 2 ^ 59 := by
  have := abs_nonneg r; linarith [h.hqr]
theorem Win.R59 {B : Addr} {w : Nat} {u v q r : Int} {s : State} (h : Win B w u v q r s) : |r| ≤ 2 ^ 59 := by
  have := abs_nonneg q; linarith [h.hqr]

theorem tN {x : Int} (h : |x| ≤ 2 ^ 59) : (BitVec.ofNat 64 x.natAbs).toNat = x.natAbs := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := natAbs_lt h; omega)]

/-- `fgRow` in a batch: `(f, g) := (u f + v g, q f + r g) / 2^59`. -/
theorem fgPart_ok {s : State} {B : Addr} {Z w n : Nat} (L : Lay B Z w n) (hs : Scr s B Z)
    (hdi : s.gpr .rdi = off B (slot w 16)) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)))
    (h15 : s.gpr .r15 = BitVec.ofNat 64 n) {u v q r : Int} (W : Win B w u v q r s) {f g z₁ z₂ : Int}
    (hf : (wv s.mem B (slot w 19) (n + 1) : Int) % 2 ^ (64 * (n + 1)) = f % 2 ^ (64 * (n + 1)))
    (hg : (wv s.mem B (slot w 20) (n + 1) : Int) % 2 ^ (64 * (n + 1)) = g % 2 ^ (64 * (n + 1)))
    (hz₁ : u * f + v * g = 2 ^ 59 * z₁) (hz₂ : q * f + r * g = 2 ^ 59 * z₂)
    (hb₁ : -((2 ^ (64 * n) * 2 ^ 63 : Nat) : Int) ≤ u * f + v * g ∧ u * f + v * g < ((2 ^ (64 * n) * 2 ^ 63 : Nat) : Int))
    (hb₂ : -((2 ^ (64 * n) * 2 ^ 63 : Nat) : Int) ≤ q * f + r * g ∧ q * f + r * g < ((2 ^ (64 * n) * 2 ^ 63 : Nat) : Int)) :
    WP isa (seqs fgRow) s fun t =>
      (wv t.mem B (slot w 19) (n + 1) : Int) % 2 ^ (64 * (n + 1)) = z₁ % 2 ^ (64 * (n + 1)) ∧
      (wv t.mem B (slot w 20) (n + 1) : Int) % 2 ^ (64 * (n + 1)) = z₂ % 2 ^ (64 * (n + 1)) ∧
      Frm B [(slot w 19, 8 * (n + 1)), (slot w 19 + 8 * (w + 2), 8 * (n + 1))] s.mem t.mem ∧
      t.gpr .r15 = BitVec.ofNat 64 n ∧
      Keep [.rax, .rdx, .rcx, .rbx, .rbp, .r8, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  have hN := L.nowrap; have hn1 := L.n1; have hnw := L.nw; have hw2' := L.w2; have hZ := L.z
  have e16 := slot_eq w 16; have e19 := slot_eq w 19; have e20 := slot_eq w 20; have e26 := slot_eq w 26
  have e1920 : slot w 19 + 8 * (w + 2) = slot w 20 := by omega_arith
  have hRf : (fgR B Z w n s.mem).Ok :=
    ⟨by simp only [fgR]; omega_arith, by simp only [fgR]; omega_arith, by simp only [fgR]; omega_arith,
      by simp only [fgR]; omega_arith, by simp only [fgR]; omega_arith⟩
  have huv : ((fgR B Z w n s.mem).c oU).toNat + ((fgR B Z w n s.mem).c oV).toNat ≤ 2 ^ 59 := by
    simp only [fgR, Rw.c]; rw [W.hU, W.hV, tN W.U59, tN W.V59]; exact natAbs_add W.huv
  have hqr : ((fgR B Z w n s.mem).c oQ).toNat + ((fgR B Z w n s.mem).c oR).toNat ≤ 2 ^ 59 := by
    simp only [fgR, Rw.c]; rw [W.hQ, W.hR, tN W.Q59, tN W.R59]; exact natAbs_add W.hqr
  refine WP.mono (fgRow_ok hs hdi h9 h15 hRf huv hqr) fun t ⟨F, G, ft, r15t, kt⟩ => ⟨?_, ?_, ft, r15t, kt⟩
  · exact fg_val (R := fgR B Z w n s.mem) (c₁ := oU) (m₁ := oMu) (c₂ := oV) (m₂ := oMv) F W.hU W.hV W.hMu W.hMv
      (natAbs_lt W.U59) (natAbs_lt W.V59) hf (by simp only [fgR]; rw [e1920]; exact hg) hz₁ hb₁
  · rw [← e1920]
    exact fg_val (R := fgR B Z w n s.mem) (c₁ := oQ) (m₁ := oMq) (c₂ := oR) (m₂ := oMr) G W.hQ W.hR W.hMq W.hMr
      (natAbs_lt W.Q59) (natAbs_lt W.R59) hf (by simp only [fgR]; rw [e1920]; exact hg) hz₂ hb₂

/-- `abRow` in a batch: `(a, b) := (mredRaw (u a + v b), mredRaw (q a + r b))`. -/
theorem abPart_ok {s : State} {B : Addr} {Z w n : Nat} (L : Lay B Z w n) (hs : Scr s B Z)
    (hdi : s.gpr .rdi = off B (slot w 16)) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)))
    (h15 : s.gpr .r15 = BitVec.ofNat 64 n) {u v q r : Int} (W : Win B w u v q r s) {a b : Int} {p mi : Nat}
    (hmi : (word s.mem B (slot w 16 + oMi)).toNat = mi) (hP : wv s.mem B (slot w 25) (n + 1) = p)
    (ha : (wv s.mem B (slot w 21) (n + 1) : Int) % 2 ^ (64 * (n + 1)) = a % 2 ^ (64 * (n + 1)))
    (hb : (wv s.mem B (slot w 22) (n + 1) : Int) % 2 ^ (64 * (n + 1)) = b % 2 ^ (64 * (n + 1)))
    (ha' : -(p : Int) < a ∧ a < 2 * p) (hb' : -(p : Int) < b ∧ b < 2 * p)
    (hp : 0 < p) (hpA : p < 2 ^ (64 * n)) (hm : (p * mi + 1) % 2 ^ 64 = 0) :
    WP isa (seqs abRow) s fun t =>
      (wv t.mem B (slot w 21) (n + 1) : Int) % 2 ^ (64 * (n + 1)) =
        Divstep.mredRaw p mi (u * a + v * b) % 2 ^ (64 * (n + 1)) ∧
      (wv t.mem B (slot w 22) (n + 1) : Int) % 2 ^ (64 * (n + 1)) =
        Divstep.mredRaw p mi (q * a + r * b) % 2 ^ (64 * (n + 1)) ∧
      Frm B [(slot w 21, 8 * (n + 1)), (slot w 21 + 8 * (w + 2), 8 * (n + 1)), (slot w 16 + oKd, 8),
        (slot w 16 + oKe, 8)] s.mem t.mem ∧
      t.gpr .r15 = BitVec.ofNat 64 n ∧
      Keep [.rax, .rdx, .rcx, .rbx, .rbp, .r8, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  have hN := L.nowrap; have hn1 := L.n1; have hnw := L.nw; have hw2' := L.w2; have hZ := L.z
  have e16 := slot_eq w 16; have e21 := slot_eq w 21; have e22 := slot_eq w 22; have e25 := slot_eq w 25
  have e26 := slot_eq w 26
  have e2122 : slot w 21 + 8 * (w + 2) = slot w 22 := by omega_arith
  have e2125 : slot w 21 + 4 * (8 * (w + 2)) = slot w 25 := by omega_arith
  have hRa : (abR B Z w n s.mem).Ok :=
    ⟨by simp only [abR]; omega_arith, by simp only [abR]; omega_arith, by simp only [abR]; omega_arith,
      by simp only [abR]; omega_arith, by simp only [abR]; omega_arith⟩
  have huv : ((abR B Z w n s.mem).c oU).toNat + ((abR B Z w n s.mem).c oV).toNat ≤ 2 ^ 59 := by
    simp only [abR, Rw.c]; rw [W.hU, W.hV, tN W.U59, tN W.V59]; exact natAbs_add W.huv
  have hqr : ((abR B Z w n s.mem).c oQ).toNat + ((abR B Z w n s.mem).c oR).toNat ≤ 2 ^ 59 := by
    simp only [abR, Rw.c]; rw [W.hQ, W.hR, tN W.Q59, tN W.R59]; exact natAbs_add W.hqr
  have ha2 : |a| ≤ 2 * p := abs_le.mpr ⟨by omega_arith, by omega_arith⟩
  have hb2 : |b| ≤ 2 * p := abs_le.mpr ⟨by omega_arith, by omega_arith⟩
  have bA : ∀ x : Int, -(p : Int) < x ∧ x < 2 * p →
      -((2 ^ (64 * n) * 2 ^ 63 : Nat) : Int) ≤ x ∧ x < ((2 ^ (64 * n) * 2 ^ 63 : Nat) : Int) := fun x hx => by
    have : (p : Int) < 2 ^ (64 * n) := by exact_mod_cast hpA
    push_cast
    have : (2 : Int) * 2 ^ (64 * n) ≤ 2 ^ (64 * n) * 2 ^ 63 := by
      have := pow_pos (show (0 : Int) < 2 by norm_num) (64 * n); nlinarith
    constructor <;> linarith
  refine WP.mono (abRow_ok hs hdi h9 h15 hRa huv hqr) fun t ⟨A, B', ft, r15t, kt⟩ => ⟨?_, ?_, ft, r15t, kt⟩
  · exact ab_val (R := abR B Z w n s.mem) (c₁ := oU) (m₁ := oMu) (c₂ := oV) (m₂ := oMv) A W.hU W.hV W.hMu W.hMv
      (natAbs_lt W.U59) (natAbs_lt W.V59) hmi (by simp only [abR]; rw [e2125]; exact hP) ha
      (by simp only [abR]; rw [e2122]; exact hb) (bA _ ha') (bA _ hb') hp hpA hm
      (Divstep.comb_le2 (by norm_num) (by exact_mod_cast hp) W.huv ha2 hb2) (by simp only [abR]; omega_arith)
  · rw [← e2122]
    exact ab_val (R := abR B Z w n s.mem) (c₁ := oQ) (m₁ := oMq) (c₂ := oR) (m₂ := oMr) B' W.hQ W.hR W.hMq W.hMr
      (natAbs_lt W.Q59) (natAbs_lt W.R59) hmi (by simp only [abR]; rw [e2125]; exact hP) ha
      (by simp only [abR]; rw [e2122]; exact hb) (bA _ ha') (bA _ hb') hp hpA hm
      (Divstep.comb_le2 (by norm_num) (by exact_mod_cast hp) W.hqr ha2 hb2) (by simp only [abR]; omega_arith)

theorem keep_drop {rs : List Reg} {r : Reg} {s t : State} (k : Keep (r :: rs) s t) (h : t.gpr r = s.gpr r) :
    Keep rs s t :=
  ⟨fun x hx => by
    by_cases e : x = r
    · subst e; exact h
    · exact k.1 x (by simp [e, hx]), k.2⟩

theorem batch_ok {s : State} {B : Addr} {Z w n p mi c : Nat} (L : Lay B Z w n) {I : Divstep.IState}
    (h : BS B Z w n p mi I s) (hrsi : s.gpr .rsi = BitVec.ofNat 64 c) (hc : 1 ≤ c) (hc' : c < 2 ^ 32)
    (hd : |I.d| ≤ 2 ^ 30) (hodd : I.f % 2 = 1)
    (hF : |I.f| ≤ 2 ^ (64 * n) * 2 ^ 3) (hG : |I.g| ≤ 2 ^ (64 * n) * 2 ^ 3)
    (ha : -(p : Int) < I.a ∧ I.a < 2 * p) (hb : -(p : Int) < I.b ∧ I.b < 2 * p)
    (hp : 0 < p) (hpA : p < 2 ^ (64 * n)) (hm : (p * mi + 1) % 2 ^ 64 = 0) :
    WP isa batch s fun t =>
      BS B Z w n p mi (Divstep.batchS 59 p mi I) t ∧ t.gpr .rsi = BitVec.ofNat 64 (c - 1) ∧
      t.zf = some (decide (c - 1 = 0)) ∧
      Frm B [(slot w 16, 72 * (w + 2))] s.mem t.mem ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rbp, .rsi, .r8, .r9, .r10, .r11, .r12, .r13, .r14] s t := by
  have hN := L.nowrap
  have hn1 := L.n1; have hnw := L.nw; have hw2' := L.w2; have hZ := L.z
  have e16 := slot_eq w 16; have e19 := slot_eq w 19; have e20 := slot_eq w 20; have e21 := slot_eq w 21
  have e22 := slot_eq w 22; have e23 := slot_eq w 23; have e25 := slot_eq w 25; have e26 := slot_eq w 26
  obtain ⟨rel₁, rel₂⟩ := Divstep.msteps_mat (d := I.d) (g := I.g) hodd 59
  obtain ⟨bnd₁, bnd₂⟩ := Divstep.msteps_bnd I.d I.f I.g 59
  have hbS : Divstep.batchS 59 p mi I = ⟨(Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).d,
      ((Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).u * I.f +
        (Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).v * I.g) / 2 ^ 59,
      ((Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).q * I.f +
        (Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).r * I.g) / 2 ^ 59,
      Divstep.mredRaw p mi ((Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).u * I.a +
        (Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).v * I.b),
      Divstep.mredRaw p mi ((Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).q * I.a +
        (Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).r * I.b)⟩ := by
    simp only [Divstep.batchS]
  rw [batch_eq, seqs_append_iff _ [.block [.alu .sub .rsi (.imm 1)]] (by simp) (by simp),
    seqs_append_iff _ abRow (by simp) (by simp [abRow]),
    seqs_append_iff [.block _] fgRow (by simp) (by simp [fgRow]), hbS]
  refine WP.mono (first_ok L h.toG hd hodd) fun s₂ ⟨d₂, u₂, mu₂, v₂, mv₂, q₂, mq₂, r₂, mr₂, mi₂, f₂, di₂, r9₂, k₂⟩ => ?_
  generalize Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g) = m at *
  have hs₂ : Scr s₂ B Z := h.scr.congr k₂.2.2
  have r15₂ : s₂.gpr .r15 = BitVec.ofNat 64 n := (k₂.gpr (by decide)).trans h.r15
  have aw₂ : ∀ e k, slot w 16 + 96 ≤ e → e + 8 * k ≤ Z → wv s₂.mem B e k = wv s.mem B e k := fun e k h1 h2 =>
    f₂.wv_eq (fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; dsimp only; omega_arith)
      (by omega_arith)
  have W : Win B w m.u m.v m.q m.r s₂ := ⟨u₂, mu₂, v₂, mv₂, q₂, mq₂, r₂, mr₂, bnd₁, bnd₂⟩
  have z₁ : m.u * I.f + m.v * I.g = 2 ^ 59 * ((m.u * I.f + m.v * I.g) / 2 ^ 59) := by
    rw [← rel₁, Int.mul_ediv_cancel_left _ (by norm_num)]
  have z₂ : m.q * I.f + m.r * I.g = 2 ^ 59 * ((m.q * I.f + m.r * I.g) / 2 ^ 59) := by
    rw [← rel₂, Int.mul_ediv_cancel_left _ (by norm_num)]
  have bF : ∀ y z : Int, |y| + |z| ≤ 2 ^ 59 →
      -((2 ^ (64 * n) * 2 ^ 63 : Nat) : Int) ≤ y * I.f + z * I.g ∧ y * I.f + z * I.g < ((2 ^ (64 * n) * 2 ^ 63 : Nat) : Int) :=
    fun y z hyz => by
      have := Divstep.comb_le hyz hF hG
      rw [abs_le] at this
      push_cast
      have : (2 : Int) ^ 59 * (2 ^ (64 * n) * 2 ^ 3) < 2 ^ (64 * n) * 2 ^ 63 := by
        have := pow_pos (show (0 : Int) < 2 by norm_num) (64 * n); nlinarith
      constructor <;> linarith
  refine WP.mono (fgPart_ok L hs₂ di₂ r9₂ r15₂ W
    (by rw [aw₂ _ _ (by omega_arith) (by omega_arith)]; exact h.f)
    (by rw [aw₂ _ _ (by omega_arith) (by omega_arith)]; exact h.g) z₁ z₂ (bF _ _ bnd₁) (bF _ _ bnd₂))
    fun s₃ ⟨F₃, G₃, f₃, r15₃, k₃⟩ => ?_
  have hs₃ : Scr s₃ B Z := hs₂.congr k₃.2.2
  have di₃ : s₃.gpr .rdi = off B (slot w 16) := (k₃.gpr (by decide)).trans di₂
  have r9₃ : s₃.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) := (k₃.gpr (by decide)).trans r9₂
  have w₃ : ∀ d, d + 8 ≤ slot w 19 → word s₃.mem B d = word s₂.mem B d := fun d hd =>
    f₃.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> dsimp only <;> omega_arith) (by omega_arith)
  have aw₃ : ∀ e k, slot w 21 ≤ e → e + 8 * k ≤ Z → wv s₃.mem B e k = wv s₂.mem B e k := fun e k h1 h2 =>
    f₃.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> dsimp only <;> omega_arith) (by omega_arith)
  have wc : ∀ o, o + 8 ≤ 96 → word s₃.mem B (slot w 16 + o) = word s₂.mem B (slot w 16 + o) := fun o ho =>
    w₃ _ (by omega_arith)
  have W₃ : Win B w m.u m.v m.q m.r s₃ := ⟨by rw [wc oU (by decide)]; exact W.hU, by rw [wc oMu (by decide)]; exact W.hMu,
    by rw [wc oV (by decide)]; exact W.hV, by rw [wc oMv (by decide)]; exact W.hMv,
    by rw [wc oQ (by decide)]; exact W.hQ, by rw [wc oMq (by decide)]; exact W.hMq,
    by rw [wc oR (by decide)]; exact W.hR, by rw [wc oMr (by decide)]; exact W.hMr, W.huv, W.hqr⟩
  have hP₃ : wv s₃.mem B (slot w 25) (n + 1) = p := by
    rw [aw₃ _ _ (by omega_arith) (by omega_arith), aw₂ _ _ (by omega_arith) (by omega_arith), wv, h.P, h.Pz]; simp
  refine WP.mono (abPart_ok L hs₃ di₃ r9₃ r15₃ W₃ (by rw [wc oMi (by decide)]; exact mi₂) hP₃
    (by rw [aw₃ _ _ (by omega_arith) (by omega_arith), aw₂ _ _ (by omega_arith) (by omega_arith)]; exact h.a)
    (by rw [aw₃ _ _ (by omega_arith) (by omega_arith), aw₂ _ _ (by omega_arith) (by omega_arith)]; exact h.b)
    ha hb hp hpA hm) fun s₄ ⟨A₄, B₄, f₄, r15₄, k₄⟩ => ?_
  have rsi₄ : s₄.gpr .rsi = BitVec.ofNat 64 c := ((k₂.trans k₃).trans k₄).gpr (by decide) |>.trans hrsi
  refine WP.mono (decRsi_ok s₄ hc (by omega_arith) rsi₄) fun t ⟨rt, zt, mt, kt⟩ => ?_
  have w₄ : ∀ d, (d + 8 ≤ slot w 16 + oKd ∨ slot w 16 + oKd + 8 ≤ d) →
      (d + 8 ≤ slot w 16 + oKe ∨ slot w 16 + oKe + 8 ≤ d) → (d + 8 ≤ slot w 21 ∨ slot w 23 ≤ d) → d + 8 ≤ Z →
      word t.mem B d = word s₃.mem B d := fun d h1 h2 h3 hz => by
    rw [mt]
    exact f₄.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> dsimp only <;> omega_arith) (by omega_arith)
  have aw₄ : ∀ e k, (e + 8 * k ≤ slot w 21 ∨ slot w 23 ≤ e) → slot w 16 + 96 ≤ e → e + 8 * k ≤ Z →
      wv t.mem B e k = wv s₃.mem B e k := fun e k h1 h2 hz => by
    rw [mt]
    exact f₄.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> dsimp only <;> (try simp only [oKd, oKe]) <;> omega_arith)
      (by omega_arith)
  have k24 := (k₂.trans k₃).trans (k₄.trans kt)
  refine ⟨?_, rt, zt, ?_, ?_⟩
  · refine ⟨h.scr.congr k24.2.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [(k₄.trans kt).gpr (by decide), di₃]
    · rw [(k₄.trans kt).gpr (by decide), r9₃]
    · rw [kt.gpr (by decide), r15₄]
    · rw [w₄ _ (by unfold oD oKd; omega_arith) (by unfold oD oKe; omega_arith) (.inl (by unfold oD; omega_arith))
        (by unfold oD; omega_arith), wc oD (by decide), d₂]
    · rw [w₄ _ (by unfold oMi oKd; omega_arith) (by unfold oMi oKe; omega_arith) (.inl (by unfold oMi; omega_arith))
        (by unfold oMi; omega_arith), wc oMi (by decide)]; exact mi₂
    · rw [aw₄ _ _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith), aw₃ _ _ (by omega_arith) (by omega_arith),
        aw₂ _ _ (by omega_arith) (by omega_arith)]; exact h.P
    · rw [w₄ _ (by unfold oKd; omega_arith) (by unfold oKe; omega_arith) (.inr (by omega_arith)) (by omega_arith)]
      rw [show word s₃.mem B (slot w 25 + 8 * n) = word s₂.mem B (slot w 25 + 8 * n) from
        f₃.word_eq (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> dsimp only <;> omega_arith) (by omega_arith),
        f₂.word_eq (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; dsimp only; omega_arith) (by omega_arith)]
      exact h.Pz
    · rw [aw₄ _ _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)]; exact F₃
    · rw [aw₄ _ _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)]; exact G₃
    · rw [mt]; exact A₄
    · rw [mt]; exact B₄
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hx
    rw [mt, f₄ x (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; unfold oKd oKe; omega_arith),
      f₃ x (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega_arith),
      f₂ x (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; omega_arith)]
  · exact keep_drop (r := .r15) (k24.mono (by decide)) (by rw [kt.gpr (by decide), r15₄, h.r15])

theorem batchG_eq : batchG = seqs (([.block ((bStart ++ bWords ++ bSave) ++
    (absS oU oMu ++ absS oV oMv ++ absS oQ oMq ++ absS oR oMr))] : List (Prog isa)) ++ fgRow ++
    ([.block ([.alu .sub .rsi (.imm 1)] : List Instr)] : List (Prog isa))) := by
  simp only [batchG, List.append_assoc]

/-- A batch of the GCD alone: `Divstep.batchS 59`'s `d`, `f` and `g` on the window and arrays (`BSg`). -/
theorem batchG_ok {s : State} {B : Addr} {Z w n p mi c : Nat} (L : Lay B Z w n) {I : Divstep.IState}
    (h : BSg B Z w n p mi I s) (hrsi : s.gpr .rsi = BitVec.ofNat 64 c) (hc : 1 ≤ c) (hc' : c < 2 ^ 32)
    (hd : |I.d| ≤ 2 ^ 30) (hodd : I.f % 2 = 1)
    (hF : |I.f| ≤ 2 ^ (64 * n) * 2 ^ 3) (hG : |I.g| ≤ 2 ^ (64 * n) * 2 ^ 3) :
    WP isa batchG s fun t =>
      BSg B Z w n p mi (Divstep.batchS 59 p mi I) t ∧ t.gpr .rsi = BitVec.ofNat 64 (c - 1) ∧
      t.zf = some (decide (c - 1 = 0)) ∧
      Frm B [(slot w 16, 72 * (w + 2))] s.mem t.mem ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rbp, .rsi, .r8, .r9, .r10, .r11, .r12, .r13, .r14] s t := by
  have hN := L.nowrap
  have hn1 := L.n1; have hnw := L.nw; have hw2' := L.w2; have hZ := L.z
  have e16 := slot_eq w 16; have e19 := slot_eq w 19; have e20 := slot_eq w 20; have e21 := slot_eq w 21
  have e25 := slot_eq w 25; have e26 := slot_eq w 26
  obtain ⟨rel₁, rel₂⟩ := Divstep.msteps_mat (d := I.d) (g := I.g) hodd 59
  obtain ⟨bnd₁, bnd₂⟩ := Divstep.msteps_bnd I.d I.f I.g 59
  have hbS : Divstep.batchS 59 p mi I = ⟨(Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).d,
      ((Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).u * I.f +
        (Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).v * I.g) / 2 ^ 59,
      ((Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).q * I.f +
        (Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).r * I.g) / 2 ^ 59,
      Divstep.mredRaw p mi ((Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).u * I.a +
        (Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).v * I.b),
      Divstep.mredRaw p mi ((Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).q * I.a +
        (Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).r * I.b)⟩ := by
    simp only [Divstep.batchS]
  rw [batchG_eq, seqs_append_iff _ [.block [.alu .sub .rsi (.imm 1)]] (by simp) (by simp),
    seqs_append_iff [.block _] fgRow (by simp) (by simp [fgRow]), hbS]
  refine WP.mono (first_ok L h hd hodd) fun s₂ ⟨d₂, u₂, mu₂, v₂, mv₂, q₂, mq₂, r₂, mr₂, mi₂, f₂, di₂, r9₂, k₂⟩ => ?_
  generalize Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g) = m at *
  have hs₂ : Scr s₂ B Z := h.scr.congr k₂.2.2
  have r15₂ : s₂.gpr .r15 = BitVec.ofNat 64 n := (k₂.gpr (by decide)).trans h.r15
  have aw₂ : ∀ e k, slot w 16 + 96 ≤ e → e + 8 * k ≤ Z → wv s₂.mem B e k = wv s.mem B e k := fun e k h1 h2 =>
    f₂.wv_eq (fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; dsimp only; omega_arith)
      (by omega_arith)
  have W : Win B w m.u m.v m.q m.r s₂ := ⟨u₂, mu₂, v₂, mv₂, q₂, mq₂, r₂, mr₂, bnd₁, bnd₂⟩
  have z₁ : m.u * I.f + m.v * I.g = 2 ^ 59 * ((m.u * I.f + m.v * I.g) / 2 ^ 59) := by
    rw [← rel₁, Int.mul_ediv_cancel_left _ (by norm_num)]
  have z₂ : m.q * I.f + m.r * I.g = 2 ^ 59 * ((m.q * I.f + m.r * I.g) / 2 ^ 59) := by
    rw [← rel₂, Int.mul_ediv_cancel_left _ (by norm_num)]
  have bF : ∀ y z : Int, |y| + |z| ≤ 2 ^ 59 →
      -((2 ^ (64 * n) * 2 ^ 63 : Nat) : Int) ≤ y * I.f + z * I.g ∧ y * I.f + z * I.g < ((2 ^ (64 * n) * 2 ^ 63 : Nat) : Int) :=
    fun y z hyz => by
      have := Divstep.comb_le hyz hF hG
      rw [abs_le] at this
      push_cast
      have : (2 : Int) ^ 59 * (2 ^ (64 * n) * 2 ^ 3) < 2 ^ (64 * n) * 2 ^ 63 := by
        have := pow_pos (show (0 : Int) < 2 by norm_num) (64 * n); nlinarith
      constructor <;> linarith
  refine WP.mono (fgPart_ok L hs₂ di₂ r9₂ r15₂ W
    (by rw [aw₂ _ _ (by omega_arith) (by omega_arith)]; exact h.f)
    (by rw [aw₂ _ _ (by omega_arith) (by omega_arith)]; exact h.g) z₁ z₂ (bF _ _ bnd₁) (bF _ _ bnd₂))
    fun s₃ ⟨F₃, G₃, f₃, r15₃, k₃⟩ => ?_
  have rsi₃ : s₃.gpr .rsi = BitVec.ofNat 64 c := (k₂.trans k₃).gpr (by decide) |>.trans hrsi
  refine WP.mono (decRsi_ok s₃ hc (by omega_arith) rsi₃) fun t ⟨rt, zt, mt, kt⟩ => ?_
  have w₃ : ∀ d, d + 8 ≤ slot w 19 ∨ slot w 21 ≤ d → d + 8 ≤ Z → word t.mem B d = word s₂.mem B d :=
    fun d hd hz => by
      rw [mt]
      exact f₃.word_eq (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> dsimp only <;> omega_arith) (by omega_arith)
  have aw₃ : ∀ e k, slot w 21 ≤ e → e + 8 * k ≤ Z → wv t.mem B e k = wv s₂.mem B e k := fun e k h1 h2 => by
    rw [mt]
    exact f₃.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> dsimp only <;> omega_arith) (by omega_arith)
  have wc : ∀ o, o + 8 ≤ 96 → word t.mem B (slot w 16 + o) = word s₂.mem B (slot w 16 + o) := fun o ho =>
    w₃ _ (.inl (by omega_arith)) (by omega_arith)
  have k23 := (k₂.trans k₃).trans kt
  refine ⟨?_, rt, zt, ?_, ?_⟩
  · refine ⟨h.scr.congr k23.2.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [(k₃.trans kt).gpr (by decide), di₂]
    · rw [(k₃.trans kt).gpr (by decide), r9₂]
    · rw [kt.gpr (by decide), r15₃]
    · rw [wc oD (by decide), d₂]
    · rw [wc oMi (by decide)]; exact mi₂
    · rw [aw₃ _ _ (by omega_arith) (by omega_arith), aw₂ _ _ (by omega_arith) (by omega_arith)]; exact h.P
    · rw [w₃ _ (.inr (by omega_arith)) (by omega_arith),
        f₂.word_eq (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; dsimp only; omega_arith) (by omega_arith)]
      exact h.Pz
    · rw [mt]; exact F₃
    · rw [mt]; exact G₃
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hx
    rw [mt, f₃ x (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega_arith),
      f₂ x (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; omega_arith)]
  · exact keep_drop (r := .r15) (k23.mono (by decide)) (by rw [kt.gpr (by decide), r15₃, h.r15])

end VG.Proof.Rsa.X86_64.InvB
