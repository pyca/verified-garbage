module

public import VerifiedGarbage.Impl.Rsa.PPC64LE.KeyDiv
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyOps
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PreR2Words
import VerifiedGarbage.Proof.Mont.WordsCanonical
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Bignum.WordDiv
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Rsa.PPC64LE.Seqs
import VerifiedGarbage.Proof.Rsa.PPC64LE.IbOps
import VerifiedGarbage.Proof.Mont.PPC64LE.Row

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

/-- The first word the steps bring down, plus one: `j₀ = X - wd + 1` for the dividend's `X` words. -/
def j0 (wd : Nat) : Option Nat → Nat
  | none => wd + 1
  | some k => k + 1

/-- The dividend's words. -/
def xw (wd : Nat) : Option Nat → Nat
  | none => 2 * wd
  | some k => wd + k

theorem j0_add {wd : Nat} (top : Option Nat) (hwd : 1 ≤ wd) : j0 wd top + (wd - 1) = xw wd top := by
  cases top <;> simp only [j0, xw] <;> omega

/-- Words equal word by word. -/
theorem wordsVal_eq_of {m m' : Mem} {B : Addr} {d : Nat} :
    ∀ n, (∀ i < n, word m' B (d + 8 * i) = word m B (d + 8 * i)) → wordsVal m' B d n = wordsVal m B d n
  | 0, _ => rfl
  | n + 1, h => by
    rw [wordsVal_succ_top, wordsVal_succ_top, wordsVal_eq_of n fun i hi => h i (by omega), h n (by omega)]

/-- The low `k` of a number's `n` words, where it is below `2^(64 k)`. -/
theorem wordsVal_low_of_lt {m : Mem} {B : Addr} {d k n : Nat} (hk : k ≤ n) (h : wordsVal m B d n < 2 ^ (64 * k)) :
    wordsVal m B d n = wordsVal m B d k := by
  have e := VG.Proof.Mont.PPC64LE.wordsVal_append m B d k (n - k)
  rw [Nat.add_sub_cancel' hk] at e
  rcases Nat.eq_zero_or_pos (wordsVal m B (d + 8 * k) (n - k)) with h0 | hp
  · rw [e, h0, Nat.mul_zero, Nat.add_zero]
  · have : 2 ^ (64 * k) ≤ 2 ^ (64 * k) * wordsVal m B (d + 8 * k) (n - k) := Nat.le_mul_of_pos_right _ hp
    omega

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

/-- The step's tail: `u`'s address a word down, a step less. -/
theorem tail_ok (s : State) :
    WP isa (.block [.subi .r8 .r8 8, .subi .r4 .r4 1]) s fun t =>
      t = (s.write .r8 (s.gpr .r8 - BitVec.ofNat 64 8)).write .r4 (s.gpr .r4 - BitVec.ofNat 64 1) := by
  apply WP.of_runBlock
  rw [runBlock_cons, exec_subi (imm := 8) (by decide) (by decide), runStep_some, runBlock_cons,
    exec_subi (imm := 1) (by decide) (by decide), runStep_some, runBlock_nil]
  simp [gpr_write]

/-- The steps, from the digit `j₀` (`[r]`'s first `wd` words `P j₀` reduced) and the temporary set
up for the divisor `M` (`wd` words at `[m]`): `j₀` word steps over `[a]`'s words below `j₀` leave
`P 0 mod M` in `[r]`'s first `wd` words and zero in word `wd`, changing only those words of memory. -/
theorem loop_ok {s : State} {B : Addr} {Z w N a r m t wd z j₀ : Nat} (h : Ws s B Z w N)
    (ha : a < N) (hr : r < N) (hm : m < N) (ht : t < N) (har : a ≠ r) (hrm : r ≠ m) (hrt : r ≠ t)
    (hw : w = 4 * wd) (hwd : 4 ≤ wd) (hj : 1 ≤ j₀) (hjw : j₀ ≤ 2 * wd)
    (h5 : s.gpr .r5 = off B (arr w r)) (h8 : s.gpr .r8 = off B (arr w a + 8 * (j₀ - 1)))
    (h9 : s.gpr .r9 = off B (arr w t)) (h10 : s.gpr .r10 = off B (arr w m))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * wd)) (h4 : s.gpr .r4 = BitVec.ofNat 64 j₀)
    (hP : (word s.mem B (arr w t)).toNat = 2 ^ z) (hz : z ≤ 63)
    (hd : (word s.mem B (arr w t + 8)).toNat = wordsVal s.mem B (arr w m) wd * 2 ^ z / 2 ^ (64 * (wd - 1)))
    (hd63 : 2 ^ 63 ≤ wordsVal s.mem B (arr w m) wd * 2 ^ z / 2 ^ (64 * (wd - 1)))
    (hv : (word s.mem B (arr w t + 16)).toNat = (2 ^ 128 - 1) / (word s.mem B (arr w t + 8)).toNat - 2 ^ 64)
    (hdl : (word s.mem B (arr w t + 8)).toNat * 2 ^ 64 + (word s.mem B (arr w t + 24)).toNat =
      wordsVal s.mem B (arr w m) wd * 2 ^ z / 2 ^ (64 * (wd - 2)))
    (Pf : Nat → Nat)
    (hPf : ∀ j, 1 ≤ j → j ≤ j₀ → Pf (j - 1) = (word s.mem B (arr w a + 8 * (j - 1))).toNat + 2 ^ 64 * Pf j)
    (h0 : wordsVal s.mem B (arr w r) wd = Pf j₀ % wordsVal s.mem B (arr w m) wd)
    (htop : word s.mem B (arr w r + 8 * wd) = 0) :
    WP isa (.loop step (.nonzero .d .r4)) s fun u =>
      wordsVal u.mem B (arr w r) wd = Pf 0 % wordsVal s.mem B (arr w m) wd ∧
      word u.mem B (arr w r + 8 * wd) = 0 ∧ Outside B (arr w r) (8 * (wd + 1)) s.mem u.mem ∧
      Keep (.r4 :: .r8 :: quotRegs) s u := by
  have := h.wle
  have hnw := h.nowrap
  have fa := h.arr_fit ha
  have fr := h.arr_fit hr
  have fm := h.arr_fit hm
  have ft := h.arr_fit ht
  have dar := arr_disj (w := w) har
  have drm := arr_disj (w := w) hrm
  have drt := arr_disj (w := w) hrt
  simp only [S] at fa fr fm ft dar drm drt
  generalize hM : wordsVal s.mem B (arr w m) wd = M at hd hd63 hdl h0
  have hM0 : 0 < M := Nat.pos_of_ne_zero fun e => by
    rw [e, Nat.zero_mul, Nat.zero_div] at hd63; exact absurd hd63 (by decide)
  let Inv : Nat → State → Prop := fun j u =>
    wordsVal u.mem B (arr w r) wd = Pf (j₀ - j) % M ∧
      word u.mem B (arr w r + 8 * wd) = 0 ∧
      Outside B (arr w r) (8 * (wd + 1)) s.mem u.mem ∧
      u.gpr .r8 = off B (arr w a + 8 * (j₀ - 1) - 8 * j) ∧ Keep (.r4 :: .r8 :: quotRegs) s u
  have I0 : Inv 0 s := ⟨by rw [h0, Nat.sub_zero], htop, Outside.refl _ _ _ _, by rw [h8, Nat.mul_zero, Nat.sub_zero],
    Keep.refl _ _⟩
  refine WP.mono (wp_countdown (body := step) (cnt := .r4) (N := j₀) (by omega) (by omega) Inv
    (fun i hi u ⟨ur, _, uo, u8, uk⟩ u4 => ?_) I0 h4) fun u ⟨ur, utop, uo, _, uk⟩ =>
      ⟨by rw [ur, Nat.sub_self], utop, uo, uk⟩
  have hu := h.of_keep uk
  have g : ∀ x ∈ [Reg.r5, .r9, .r10, .r11], u.gpr x = s.gpr x := fun x hx => uk.gpr x (by revert x hx; decide)
  have om : ∀ d, d + 8 ≤ arr w r ∨ arr w r + 8 * (wd + 1) ≤ d → d + 8 ≤ 2 ^ 64 →
      word u.mem B d = word s.mem B d := fun d hd hd' => uo.word hd hd'
  have wm : wordsVal u.mem B (arr w m) wd = M := by rw [uo.wordsVal (by omega) (by omega), hM]
  have t0 := om (arr w t) (by omega) (by omega)
  have t8 := om (arr w t + 8) (by omega) (by omega)
  have t16 := om (arr w t + 16) (by omega) (by omega)
  have t24 := om (arr w t + 24) (by omega) (by omega)
  have ua := om (arr w a + 8 * (j₀ - 1 - i)) (by omega) (by omega)
  have e8 : arr w a + 8 * (j₀ - 1) - 8 * i = arr w a + 8 * (j₀ - 1 - i) := by omega
  rw [e8] at u8
  unfold step
  refine WP.seq (WP.mono (wordStepU_ok (z := z) (dU := arr w a + 8 * (j₀ - 1 - i)) hu.scr
    ((g .r9 (by decide)).trans h9) ((g .r10 (by decide)).trans h10) ((g .r5 (by decide)).trans h5) u8
    ((g .r11 (by decide)).trans h11) hwd (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [t0]; exact hP) hz (by rw [t8, wm]; exact hd) (by rw [wm]; exact hd63)
    (by rw [t16, t8]; exact hv) (by rw [t8, t24, wm]; exact hdl)
    (by rw [wm, ur]; exact Nat.mod_lt _ hM0)) fun u₁ ⟨⟨r1, top1⟩, o1, k1⟩ => ?_)
  refine WP.mono (tail_ok u₁) fun u₂ e2 => ?_
  subst e2
  refine ⟨⟨?_, by rw [mem_write, mem_write]; exact top1, by rw [mem_write, mem_write]; exact uo.trans o1,
    ?_, ?_⟩, ?_⟩
  · rw [mem_write, mem_write, r1, wm, ur, ua, show j₀ - (i + 1) = j₀ - i - 1 by omega,
      hPf (j₀ - i) (by omega) (by omega), show j₀ - 1 - i = j₀ - i - 1 by omega]
    rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]
    ac_rfl
  · simp only [gpr_write, show (Reg.r8 = Reg.r4) = False by decide, ite_false, ite_true]
    have a8 : 8 ≤ arr w a := Nat.le_trans (by decide) (Nat.le_add_right VG.Proof.Rsa.KeyWorkspace.hdr (a * S w))
    rw [k1.gpr .r8 (by decide), u8,
      show arr w a + 8 * (j₀ - 1) - 8 * (i + 1) = arr w a + 8 * (j₀ - 1 - i) - 8 by omega,
      BitVec.sub_eq_iff_eq_add, off_add, Nat.sub_add_cancel (by omega)]
  · exact ((uk.trans k1).trans ((Keep.write _ .r8 _).trans (Keep.write _ .r4 _))).mono (by decide)
  · simp only [gpr_write, ite_true]
    rw [k1.gpr .r4 (by decide)]

/-- Words above `n` that are zero add nothing. -/
theorem wordsVal_zero_top {m : Mem} {B : Addr} {d n : Nat} :
    ∀ k, (∀ i, n ≤ i → i < n + k → word m B (d + 8 * i) = 0) → wordsVal m B d (n + k) = wordsVal m B d n
  | 0, _ => rfl
  | k + 1, hz => by
    rw [← Nat.add_assoc, wordsVal_succ_top, hz (n + k) (by omega) (by omega),
      wordsVal_zero_top k fun i h1 h2 => hz i h1 (by omega)]
    rfl

/-- `ptr r14 r`, `r11 := w`. -/
theorem zeroSetup_ok {s : State} {B : Addr} {Z w N r : Nat} (h : Ws s B Z w N) (hr : r < N) (hN : N ≤ 256) :
    WP isa (.block (ptr .r14 r ++ ([.addi .r11 .r29 0] : List Instr))) s fun u =>
      u.gpr .r14 = off B (arr w r) ∧ u.gpr .r11 = BitVec.ofNat 64 w ∧ u.mem = s.mem ∧ Keep [.r11, .r14] s u := by
  refine ptr_ok h (r := .r14) (by decide) (by decide) (by decide) (show r < 2 ^ 15 by omega) ?_
  refine WP.mono (WP.keep [.r11] (Q := fun u => u.gpr .r11 = BitVec.ofNat 64 w ∧ u.mem = s.mem) (by
    prun [gpr_write, mem_write, h.r29, BitVec.add_zero]) (by decide)) fun u ⟨⟨u11, um⟩, uk⟩ =>
    ⟨by rw [uk.gpr .r14 (by decide), gpr_write]; rfl, u11, um, ((Keep.write _ .r14 _).trans uk).mono (by decide)⟩

/-- `stepsCount top`, from `r8` at `[a]` and `r11 = 2 wd`: `r8` at `[a]`'s word `j₀ - 1`, `r4 := j₀`. -/
theorem stepsCount_ok {s : State} {B : Addr} {d wd : Nat} (h8 : s.gpr .r8 = off B d) (hwd : 1 ≤ wd)
    (hwd' : wd < 2 ^ 12) {top : Option Nat} (hk : ∀ k, top = some k → k ≤ wd)
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * wd)) :
    WP isa (.block (VG.Impl.Rsa.PPC64LE.KeyDiv.stepsCount top)) s fun u =>
      (u.gpr .r8 = off B (d + 8 * (j0 wd top - 1)) ∧ u.gpr .r4 = BitVec.ofNat 64 (j0 wd top) ∧ u.mem = s.mem) ∧
      Keep [.r0, .r4, .r8] s u := by
  apply WP.of_runBlock
  cases top with
  | none =>
    have e2 : BitVec.ofNat 64 (2 * wd) <<< 2 = BitVec.ofNat 64 (8 * wd) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      omega
    have e1 : BitVec.ofNat 64 (2 * wd) >>> 1 = BitVec.ofNat 64 wd := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      omega
    simp only [VG.Impl.Rsa.PPC64LE.KeyDiv.stepsCount, runBlock_cons, runBlock_nil, runStep_some,
      exec_lsl (show 2 < 64 by decide), exec_add, exec_lsr_d (show 1 < 64 by decide),
      exec_addi (d := .r4) (n := .r4) (imm := 1) (by decide) (by decide), Option.some.injEq, exists_eq_left']
    refine ⟨⟨?_, ?_, rfl⟩, (((((Keep.write _ .r0 _).trans (Keep.write _ .r8 _)).trans (Keep.write _ .r4 _)).trans
      (Keep.write _ .r4 _))).mono (by decide)⟩
    · simp only [gpr_write, ite_true, show (Reg.r8 = Reg.r4) = False by decide, show (Reg.r8 = Reg.r0) = False by decide,
        ite_false, h8, h11, e2, off_add, j0, Nat.add_sub_cancel]
    · simp only [gpr_write, ite_true,
        show (Reg.r11 = Reg.r8) = False by decide, show (Reg.r11 = Reg.r0) = False by decide, ite_false, h11, e1, j0,
        BitVec.ofNat_add]
  | some k =>
    have := hk k rfl
    simp only [VG.Impl.Rsa.PPC64LE.KeyDiv.stepsCount, runBlock_cons, runBlock_nil, runStep_some,
      exec_addi (d := .r8) (n := .r8) (imm := 8 * k) (by decide) (by omega),
      exec_li (d := .r4) (imm := k + 1) (by omega), Option.some.injEq, exists_eq_left']
    refine ⟨⟨?_, ?_, rfl⟩, (((Keep.write _ .r8 _).trans (Keep.write _ .r4 _))).mono (by decide)⟩
    · simp only [gpr_write, ite_true, show (Reg.r8 = Reg.r4) = False by decide, ite_false, h8, off_add, j0,
        Nat.add_sub_cancel]
    · simp only [gpr_write, ite_true, j0]

/-- `stepsSetup top a r`, from `r11 = 2 wd`: `r5 := [r]`'s address, `r8 :=` that
of `[a]`'s word `j₀ - 1`, `r4 := j₀`. -/
theorem stepsSetup_ok {s : State} {B : Addr} {Z w N a r wd : Nat} (h : Ws s B Z w N) (ha : a < N) (hr : r < N)
    (hN : N ≤ 256) (hw : w = 4 * wd) (hwd : 1 ≤ wd) {top : Option Nat} (hk : ∀ k, top = some k → k ≤ wd)
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * wd)) :
    WP isa (.block (stepsSetup top a r)) s fun u =>
      u.gpr .r5 = off B (arr w r) ∧ u.gpr .r8 = off B (arr w a + 8 * (j0 wd top - 1)) ∧
      u.gpr .r4 = BitVec.ofNat 64 (j0 wd top) ∧ u.mem = s.mem ∧ Keep [.r0, .r4, .r5, .r8] s u := by
  have := h.wle
  simp only [stepsSetup, List.append_assoc]
  refine ptr_ok h (r := .r5) (by decide) (by decide) (by decide) (show r < 2 ^ 15 by omega) ?_
  refine ptr_ok (h.of_keep (Keep.write _ .r5 _)) (r := .r8) (by decide) (by decide) (by decide)
    (show a < 2 ^ 15 by omega) ?_
  refine WP.mono (stepsCount_ok (B := B) (d := arr w a) (by simp [gpr_write]) hwd (by omega) hk
    (by simp only [gpr_write]; simp [h11])) fun u ⟨⟨u8, u4, um⟩, uk⟩ =>
    ⟨by rw [uk.gpr .r5 (by decide), gpr_write]; simp [gpr_write], u8, u4, um,
      ((Keep.write _ .r5 _).trans ((Keep.write _ .r8 _).trans uk)).mono (by decide)⟩

/-- `srcOff top`, from `r6` at `[a]`: `r6` at its word `j₀`. -/
theorem srcOff_ok {s : State} {B : Addr} {d w wd : Nat} (h6 : s.gpr .r6 = off B d) (h29 : s.gpr .r29 = BitVec.ofNat 64 w)
    (hw : w = 4 * wd) (hwd' : wd < 2 ^ 11) {top : Option Nat} (hk : ∀ k, top = some k → k ≤ wd) :
    WP isa (.block (VG.Impl.Rsa.PPC64LE.KeyDiv.srcOff top)) s fun u =>
      (u.gpr .r6 = off B (d + 8 * j0 wd top) ∧ u.mem = s.mem) ∧ Keep [.r0, .r6] s u := by
  apply WP.of_runBlock
  cases top with
  | none =>
    have e2 : BitVec.ofNat 64 w <<< 1 = BitVec.ofNat 64 (8 * wd) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      omega
    simp only [VG.Impl.Rsa.PPC64LE.KeyDiv.srcOff, runBlock_cons, runBlock_nil, runStep_some,
      exec_lsl (show 1 < 64 by decide), exec_add,
      exec_addi (d := .r6) (n := .r6) (imm := 8) (by decide) (by decide), Option.some.injEq, exists_eq_left']
    refine ⟨⟨?_, rfl⟩, ((((Keep.write _ .r0 _).trans (Keep.write _ .r6 _)).trans (Keep.write _ .r6 _))).mono (by decide)⟩
    simp only [gpr_write, ite_true, show (Reg.r6 = Reg.r0) = False by decide,
      ite_false, h6, h29, e2, off_add, j0]
    rw [show d + 8 * wd + 8 = d + 8 * (wd + 1) by omega]
  | some k =>
    have := hk k rfl
    simp only [VG.Impl.Rsa.PPC64LE.KeyDiv.srcOff, runBlock_cons, runBlock_nil, runStep_some,
      exec_addi (d := .r6) (n := .r6) (imm := 8 * (k + 1)) (by decide) (by omega), Option.some.injEq, exists_eq_left']
    refine ⟨⟨?_, rfl⟩, (Keep.write _ .r6 _).mono (by decide)⟩
    simp only [gpr_write, ite_true, h6, off_add, j0]

/-- `seed top a r`: `[r]`'s first `2 (wd - 1)` digits `[a]`'s from its word `j₀` on. -/
theorem seed_ok {s : State} {B : Addr} {Z w N a r wd : Nat} (h : Ws s B Z w N) (ha : a < N) (hr : r < N)
    (har : a ≠ r) (hN : N ≤ 256) (hw : w = 4 * wd) (hwd : 4 ≤ wd) {top : Option Nat}
    (hk : ∀ k, top = some k → k ≤ wd) :
    WP isa (VG.Impl.Rsa.PPC64LE.KeyDiv.seed top a r) s fun u =>
      val32 u.mem B (arr w r) (2 * (wd - 1)) = val32 s.mem B (arr w a + 8 * j0 wd top) (2 * (wd - 1)) ∧
      Outside B (arr w r) (4 * (2 * (wd - 1))) s.mem u.mem ∧ Ws u B Z w N ∧
      Keep VG.Proof.Rsa.PPC64LE.Loops.loopRegs s u := by
  have := h.wle
  have hnw := h.nowrap
  have fa := h.arr_fit ha
  have fr := h.arr_fit hr
  have dar := arr_disj (w := w) har
  simp only [S] at fa fr dar
  have hjx : j0 wd top + (wd - 1) ≤ 2 * wd := by
    rw [j0_add top (by omega)]; cases top with
    | none => simp only [xw]; omega
    | some k => have := hk k rfl; simp only [xw]; omega
  rw [VG.Impl.Rsa.PPC64LE.KeyDiv.seed, WP.seq_iff]
  simp only [VG.Impl.Rsa.PPC64LE.KeyDiv.seedSetup, List.append_assoc]
  refine ptr_ok h (r := .r5) (by decide) (by decide) (by decide) (show r < 2 ^ 15 by omega) ?_
  refine ptr_ok (h.of_keep (Keep.write _ .r5 _)) (r := .r6) (by decide) (by decide) (by decide)
    (show a < 2 ^ 15 by omega) ?_
  rw [WP.block_append_iff]
  refine WP.mono (srcOff_ok (B := B) (d := arr w a) (wd := wd) (by simp [gpr_write]) (by simp [gpr_write, h.r29]) hw
    (by omega) hk) fun u₁ ⟨⟨u6, um₁⟩, uk₁⟩ => ?_
  refine WP.mono (WP.keep [.r8] (Q := fun u => u.gpr .r8 = BitVec.ofNat 64 (2 * (wd - 1)) ∧ u.mem = u₁.mem) (by
      have e8 : BitVec.ofNat 64 w >>> 1 - BitVec.ofNat 64 2 = BitVec.ofNat 64 (2 * (wd - 1)) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_sub, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.shiftRight_eq_div_pow]
        omega
      have h29 : u₁.gpr .r29 = BitVec.ofNat 64 w := by
        rw [uk₁.gpr .r29 (by decide)]; simp [gpr_write, h.r29]
      prun [gpr_write, mem_write, h29, e8]) (by decide)) fun u ⟨⟨u8, um⟩, uk⟩ => ?_
  have k0 : Keep [.r0, .r5, .r6, .r8] s u :=
    (((Keep.write _ .r5 _).trans ((Keep.write _ .r6 _).trans uk₁)).trans uk).mono (by decide)
  have hu : Ws u B Z w N := h.of_keep k0
  have h5 : u.gpr .r5 = off B (arr w r) := by
    rw [uk.gpr .r5 (by decide), uk₁.gpr .r5 (by decide)]; simp [gpr_write]
  have h6 : u.gpr .r6 = off B (arr w a + 8 * j0 wd top) := by rw [uk.gpr .r6 (by decide), u6]
  have hm : u.mem = s.mem := by rw [um, um₁]; rfl
  refine WP.mono (VG.Proof.Rsa.PPC64LE.Loops.copyLoop_ok hu.scr h5 h6 u8 (by omega) (by omega) (by omega) (by omega)
    (by unfold VG.Proof.Rsa.PPC64LE.Loops.Ahead; omega)) fun t ⟨tv, to, tk⟩ => ⟨?_, ?_, hu.of_keep tk, ?_⟩
  · rw [tv, hm]
  · rw [← hm]; exact to.mono (Nat.le_refl _) (by omega)
  · exact (k0.trans tk).mono (by decide)

/-- A 64-bit word of an array outside a frame. -/
theorem keep_word64 {B : Addr} {w : Nat} {js : List Nat} {m m' : Mem}
    (h : KeyWorkspace.Keep B w js [] m m') {j o : Nat} (ho : o + 8 ≤ S w) (hj : ∀ x ∈ js, x ≠ j)
    (fit : arr w j + S w ≤ 2 ^ 64) : word m' B (arr w j + o) = word m B (arr w j + o) :=
  VG.Proof.Rsa.PPC64LE.InvBatch.keep_word h (b := 64) (by omega) hj (fun d hd => absurd hd (by simp)) fit

/-- `prepA r sv`: the registers saved in `sv`, `[r]`'s `w` digits zeroed. -/
theorem prepA_ok {s : State} {B : Addr} {Z w N r sv wd : Nat} (h : Ws s B Z w N) (hr : r < N) (hsv : sv < N)
    (hrsv : r ≠ sv) (hN : N ≤ 256) (hw : w = 4 * wd) (hwd : 4 ≤ wd) :
    WP isa (prepA r sv) s fun u =>
      (∀ i < 7, word u.mem B (arr w sv + 8 * i) = s.gpr (svReg i)) ∧ (∀ i < 2 * wd, word u.mem B (arr w r + 8 * i) = 0) ∧
      KeyWorkspace.Keep B w [sv, r] [] s.mem u.mem ∧ Ws u B Z w N ∧ Keep [.r0, .r5, .r11, .r14, .r17] s u := by
  have := h.wle
  have hnw := h.nowrap
  have fr := h.arr_fit hr
  have fsv := h.arr_fit hsv
  have d := arr_disj (w := w) hrsv
  simp only [S] at fr fsv d
  rw [prepA, wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (save_ok h hsv hN (by omega)) fun s1 ⟨sv1, o1, k1⟩ => ?_
  have h1 := h.of_keep k1
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (zeroSetup_ok h1 hr hN) fun s2 ⟨r14, r11, m2, k2⟩ => ?_
  have h2 := h1.of_keep k2
  refine WP.mono (zeroWords_ok (w := 2 * wd) h2.scr r14 (by rw [r11, hw]; congr 1; omega) (by omega) (by omega)
    (by omega)) fun s3 ⟨⟨_, z3, o3⟩, k3⟩ => ⟨fun i hi => ?_, z3, ?_, h2.of_keep k3,
      ((k1.trans k2).trans k3).mono (by decide)⟩
  · rw [o3.word (by omega) (by omega), m2]; exact sv1 i hi
  · refine (KeyWorkspace.Keep.of_arr (o := sv) (d := 0) (n := 56) (by rw [Nat.add_zero]; exact o1)
      (by simp only [S]; omega) (by simp)).trans ?_
    rw [← m2]
    exact KeyWorkspace.Keep.of_arr (o := r) (d := 0) (n := 8 * (2 * wd)) (by rw [Nat.add_zero]; exact o3)
      (by simp only [S]; omega) (by simp)

/-- `x`, plus 1 if it is zero. -/
def fixW (x : BitVec 64) : BitVec 64 := x + ((0#64 - x ||| x) >>> 63 ^^^ 1#64)

theorem shr63_ofNat (y : BitVec 64) : y >>> 63 = BitVec.ofNat 64 (y.toNat / 2 ^ 63) :=
  BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    have := y.isLt; omega)

theorem fixW_toNat (x : BitVec 64) : (fixW x).toNat = x.toNat + if x.toNat = 0 then 1 else 0 := by
  by_cases hx : x = 0#64
  · subst hx; decide
  · have hx' : x.toNat ≠ 0 := fun e => hx (BitVec.eq_of_toNat_eq e)
    have e : (0#64 - x ||| x) >>> 63 = 1#64 := by
      rw [BitVec.ushiftRight_or_distrib, shr63_ofNat, shr63_ofNat (y := x), BitVec.toNat_sub,
        show (0#64).toNat = 0 from rfl, Nat.add_zero]
      have hl := x.isLt
      generalize x.toNat = b at hl hx'
      rcases (show b < 2 ^ 63 ∨ 2 ^ 63 ≤ b by omega) with h | h
      · rw [show (2 ^ 64 - b) % 2 ^ 64 / 2 ^ 63 = 1 by omega, show b / 2 ^ 63 = 0 by omega]; decide
      · rw [show b / 2 ^ 63 = 1 by omega]
        rcases (show (2 ^ 64 - b) % 2 ^ 64 / 2 ^ 63 = 0 ∨ (2 ^ 64 - b) % 2 ^ 64 / 2 ^ 63 = 1 by omega) with
          e | e <;> rw [e] <;> decide
    rw [fixW, e, show (1#64 ^^^ 1#64) = 0#64 from rfl, BitVec.add_zero, ite_eq_right hx', Nat.add_zero]

/-- `fixTop m`, `w = 4 wd`: `[m]`'s word `wd - 1` plus 1 if it is zero. -/
theorem fixTop_ok {s : State} {B : Addr} {Z w N m wd : Nat} (h : Ws s B Z w N) (hm : m < N) (hN : N ≤ 256)
    (hw : w = 4 * wd) (hwd : 4 ≤ wd) :
    WP isa (.block (fixTop m)) s fun u =>
      u.mem = s.mem.writeW (off B (arr w m + 8 * (wd - 1))) (fixW (word s.mem B (arr w m + 8 * (wd - 1)))) ∧
      Ws u B Z w N ∧ Keep [.r0, .r3, .r6, .r10, .r11, .r12] s u := by
  have := h.wle
  have hnw := h.nowrap
  have fm := h.arr_fit hm
  simp only [S] at fm
  have e11 : BitVec.ofNat 64 w >>> 1 = BitVec.ofNat 64 (2 * wd) := by
    rw [hw, show 4 * wd = 2 * (2 * wd) by omega]; exact mont_ofNat_shr1 (by omega)
  have ea := ea_top B (d := arr w m) (w := wd) (c := 8) (by omega)
  rw [show arr w m + 8 * wd - 8 = arr w m + 8 * (wd - 1) by omega] at ea
  have rT : (s.write .r10 (off B (arr w m))).mem.readW (off B (arr w m + 8 * (wd - 1))) 64 =
      word s.mem B (arr w m + 8 * (wd - 1)) := rfl
  simp only [fixTop]
  refine ptr_ok h (r := .r10) (by decide) (by decide) (by decide) (show m < 2 ^ 15 by omega) ?_
  refine WP.mono (WP.keep [.r0, .r3, .r6, .r11, .r12] (Q := fun u =>
      u.mem = s.mem.writeW (off B (arr w m + 8 * (wd - 1))) (fixW (word s.mem B (arr w m + 8 * (wd - 1))))) (by
    prun [gpr_write, mem_write, h.r29, e11, ea, rT, h.scr.ld (show arr w m + 8 * (wd - 1) + 8 ≤ Z by omega),
      h.scr.st (show arr w m + 8 * (wd - 1) + 8 ≤ Z by omega)]
    rfl) (by decide)) fun u ⟨um, uk⟩ =>
    ⟨um, (h.of_keep (Keep.write _ .r10 _)).of_keep uk, ((Keep.write _ .r10 _).trans uk).mono (by decide)⟩

/-- The divisor after `fixTop`: its top word not zero, and unchanged if it was not. -/
theorem fixTop_val {mem : Mem} {B : Addr} {d wd : Nat} (hwd : 1 ≤ wd) (hd : d + 8 * wd ≤ 2 ^ 64) :
    let mem' := mem.writeW (off B (d + 8 * (wd - 1))) (fixW (word mem B (d + 8 * (wd - 1))))
    2 ^ (64 * (wd - 1)) ≤ wordsVal mem' B d wd ∧
      (2 ^ (64 * (wd - 1)) ≤ wordsVal mem B d wd → wordsVal mem' B d wd = wordsVal mem B d wd) := by
  intro mem'
  have e' : wordsVal mem' B d wd = wordsVal mem B d (wd - 1) +
      2 ^ (64 * (wd - 1)) * (fixW (word mem B (d + 8 * (wd - 1)))).toNat := by
    show wordsVal (mem.writeW _ _) B d wd = _
    rw [show wordsVal (mem.writeW (off B (d + 8 * (wd - 1))) (fixW (word mem B (d + 8 * (wd - 1))))) B d wd =
      wordsVal (mem.writeW (off B (d + 8 * (wd - 1))) (fixW (word mem B (d + 8 * (wd - 1))))) B d (wd - 1 + 1) by
        rw [Nat.sub_add_cancel hwd], fios_wordsVal_write_top _ _ _ _ _ (by omega)]
  have e0 := wordsVal_succ_top mem B d (wd - 1)
  rw [Nat.sub_add_cancel hwd] at e0
  have hlow := wordsVal_lt mem B d (wd - 1)
  rw [e', fixW_toNat]
  generalize (word mem B (d + 8 * (wd - 1))).toNat = T at e0 ⊢
  constructor
  · have : 1 ≤ T + (if T = 0 then 1 else 0) := by split <;> omega
    have := Nat.mul_le_mul_left (2 ^ (64 * (wd - 1))) this
    omega
  · intro hT
    rcases Nat.eq_zero_or_pos T with h0 | h0
    · rw [h0, Nat.mul_zero, Nat.add_zero] at e0; omega
    · rw [ite_eq_right (by omega), Nat.add_zero, e0]

/-- `normSetup m t`: the addresses of `[m]` and `[t]`, `r11 := w / 2`. -/
theorem normSetup_ok {s : State} {B : Addr} {Z w N m t wd : Nat} (h : Ws s B Z w N) (hm : m < N) (ht : t < N)
    (hN : N ≤ 256) (hw : w = 4 * wd) (hwd : 1 ≤ wd) :
    WP isa (.block (normSetup m t)) s fun u => u.gpr .r10 = off B (arr w m) ∧ u.gpr .r9 = off B (arr w t) ∧
      u.gpr .r11 = BitVec.ofNat 64 (2 * wd) ∧ u.mem = s.mem ∧ Keep [.r9, .r10, .r11] s u := by
  have := h.wle
  have e11 : BitVec.ofNat 64 w >>> 1 = BitVec.ofNat 64 (2 * wd) := by
    rw [hw, show 4 * wd = 2 * (2 * wd) by omega]; exact mont_ofNat_shr1 (by omega)
  simp only [normSetup, List.append_assoc]
  refine ptr_ok h (r := .r10) (by decide) (by decide) (by decide) (show m < 2 ^ 15 by omega) ?_
  refine ptr_ok (h.of_keep (Keep.write _ .r10 _)) (r := .r9) (by decide) (by decide) (by decide)
    (show t < 2 ^ 15 by omega) ?_
  refine WP.mono (WP.keep [.r11] (Q := fun u => u.gpr .r11 = BitVec.ofNat 64 (2 * wd) ∧ u.mem = s.mem) (by
    prun [gpr_write, mem_write, h.r29, e11]) (by decide)) fun u ⟨⟨u11, um⟩, uk⟩ =>
    ⟨by rw [uk.gpr .r10 (by decide)]; simp [gpr_write], by rw [uk.gpr .r9 (by decide)]; simp [gpr_write], u11, um,
      ((Keep.write _ .r10 _).trans ((Keep.write _ .r9 _).trans uk)).mono (by decide)⟩

/-- `prepB a r m t`: the temporary normalizing the divisor `[m]` (`wd` words,
its top word not zero), and the steps' registers. -/
theorem prepB_ok {s : State} {B : Addr} {Z w N a r m t wd : Nat} (h : Ws s B Z w N) (ha : a < N) (hr : r < N)
    (hm : m < N) (ht : t < N) (hmt : m ≠ t) (hN : N ≤ 256) (hw : w = 4 * wd) (hwd : 4 ≤ wd)
    {top : Option Nat} (hk : ∀ k, top = some k → k ≤ wd)
    (hT : 2 ^ (64 * (wd - 1)) ≤ wordsVal s.mem B (arr w m) wd) :
    WP isa (prepB top a r m t) s fun u => ∃ z ≤ 63, (word u.mem B (arr w t)).toNat = 2 ^ z ∧
      (word u.mem B (arr w t + 8)).toNat = wordsVal s.mem B (arr w m) wd * 2 ^ z / 2 ^ (64 * (wd - 1)) ∧
      2 ^ 63 ≤ wordsVal s.mem B (arr w m) wd * 2 ^ z / 2 ^ (64 * (wd - 1)) ∧
      (word u.mem B (arr w t + 16)).toNat = (2 ^ 128 - 1) / (word u.mem B (arr w t + 8)).toNat - 2 ^ 64 ∧
      (word u.mem B (arr w t + 8)).toNat * 2 ^ 64 + (word u.mem B (arr w t + 24)).toNat =
        wordsVal s.mem B (arr w m) wd * 2 ^ z / 2 ^ (64 * (wd - 2)) ∧
      KeyWorkspace.Keep B w [t] [] s.mem u.mem ∧
      u.gpr .r5 = off B (arr w r) ∧ u.gpr .r8 = off B (arr w a + 8 * (j0 wd top - 1)) ∧
      u.gpr .r4 = BitVec.ofNat 64 (j0 wd top) ∧ u.gpr .r9 = off B (arr w t) ∧ u.gpr .r10 = off B (arr w m) ∧
      u.gpr .r11 = BitVec.ofNat 64 (2 * wd) ∧ Ws u B Z w N ∧
      Keep [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r18, .r20, .r22]
        s u := by
  have := h.wle
  have hnw := h.nowrap
  have fm := h.arr_fit hm
  have ft := h.arr_fit ht
  have d := arr_disj (w := w) hmt
  simp only [S] at fm ft d
  rw [prepB, wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (normSetup_ok h hm ht hN hw (by omega)) fun s1 ⟨r10, r9, r11, m1, k1⟩ => ?_
  have h1 := h.of_keep k1
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (normAt_ok (dN := arr w m) (dT := arr w t) h1.scr r9 r10 r11 (by omega) (by omega) (by omega)
    (by omega) (by rw [m1]; exact hT)) fun s2 ⟨⟨z, hz, hP, hd, hd63, hdl⟩, o2, k2⟩ => ?_
  rw [m1] at hd hd63 hdl
  have h2 := h1.of_keep k2
  have g2 : ∀ x ∈ [Reg.r9, .r10, .r11], s2.gpr x = s1.gpr x := fun x hx => k2.gpr x (by revert x hx; decide)
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have h63 : 2 ^ 63 ≤ (word s2.mem B (arr w t + 8)).toNat := by rw [hd]; exact hd63
  refine WP.mono (recipAt_ok (dT := arr w t) h2.scr ((g2 .r9 (by decide)).trans r9) (by omega) h63)
    fun s3 ⟨⟨v3, o3⟩, k3⟩ => ?_
  have h3 := h2.of_keep k3
  rw [show seqs [.block (VG.Impl.Rsa.PPC64LE.KeyDiv.stepsSetup top a r)] =
    .block (VG.Impl.Rsa.PPC64LE.KeyDiv.stepsSetup top a r) from rfl]
  have g3 : ∀ x ∈ [Reg.r9, .r10, .r11], s3.gpr x = s1.gpr x := fun x hx =>
    (k3.gpr x (by revert x hx; decide)).trans (g2 x hx)
  refine WP.mono (stepsSetup_ok h3 ha hr hN hw (by omega) hk ((g3 .r11 (by decide)).trans r11))
    fun u ⟨r5, r8, r4, mu, ku⟩ => ⟨z, hz, ?_, ?_, hd63, ?_, ?_, ?_, r5, r8, r4, ?_, ?_, ?_, h3.of_keep ku,
      (((k1.trans k2).trans k3).trans ku).mono (by decide)⟩
  · rw [mu, o3.word (by omega) (by omega)]; exact hP
  · rw [mu, o3.word (by omega) (by omega)]; exact hd
  · rw [mu, v3, o3.word (by omega) (by omega)]
  · rw [mu, o3.word (by omega) (by omega), o3.word (by omega) (by omega)]; exact hdl
  · rw [mu, ← m1]
    exact (KeyWorkspace.Keep.of_arr (o := t) (d := 0) (n := 32) (by rw [Nat.add_zero]; exact o2)
      (by simp only [S]; omega) (by simp)).trans (KeyWorkspace.Keep.of_arr (o := t) (d := 16) (n := 8) o3
      (by simp only [S]; omega) (by simp))
  · rw [ku.gpr .r9 (by decide), g3 .r9 (by decide), r9]
  · rw [ku.gpr .r10 (by decide), g3 .r10 (by decide), r10]
  · rw [ku.gpr .r11 (by decide), g3 .r11 (by decide), r11]

/-- Two arrays, neither of them `c`. -/
theorem two_ne {a b c : Nat} (ha : a ≠ c) (hb : b ≠ c) : ∀ x ∈ [a, b], x ≠ c := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ha
  · exact hb

/-- The registers `divW` changes. -/
abbrev divRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

/-- `divW a r m t sv top`, for `w = 4 wd`, `wd ≥ 4`: `[r] := [a] mod M` for the
divisor `M`, `[m]`'s `wd` words, its top word not zero, where the dividend has the words `top` gives;
changing the arrays `r`, `t` and `sv`, and the registers `divRegs`. -/
theorem divWAt_ok {s : State} {B : Addr} {Z w N a r m t sv wd : Nat} (h : Ws s B Z w N)
    (ha : a < N) (hr : r < N) (hm : m < N) (ht : t < N) (hsv : sv < N)
    (har : a ≠ r) (hat : a ≠ t) (hasv : a ≠ sv) (hrm : r ≠ m) (hrt : r ≠ t) (hrsv : r ≠ sv)
    (hmt : m ≠ t) (hmsv : m ≠ sv) (htsv : t ≠ sv) (hN : N ≤ 256) (hw : w = 4 * wd) (hwd : 4 ≤ wd)
    {top : Option Nat} (hk : ∀ k, top = some k → k ≤ wd)
    (hT : 2 ^ (64 * (wd - 1)) ≤ wordsVal s.mem B (arr w m) wd) :
    WP isa (divW a r m t sv top) s fun u =>
      (wordsVal s.mem B (arr w a) (2 * wd) < 2 ^ (64 * xw wd top) →
        num u.mem B w r = num s.mem B w a % wordsVal s.mem B (arr w m) wd) ∧ Ws u B Z w N ∧ Keep divRegs s u ∧
      KeyWorkspace.Keep B w [r, t, sv] [] s.mem u.mem := by
  have := h.wle
  have fa := h.fit64 ha
  have fr := h.fit64 hr
  have fm := h.fit64 hm
  have fsv := h.fit64 hsv
  have fa' := h.arr_fit ha
  have fr' := h.arr_fit hr
  have dar := arr_disj (w := w) har
  simp only [S] at fa fr fm fsv fa' fr' dar
  have hj := j0_add top (wd := wd) (by omega)
  have hxw : xw wd top ≤ 2 * wd := by
    cases top with
    | none => simp only [xw]; omega
    | some k => have := hk k rfl; simp only [xw]; omega
  have hj1 : 1 ≤ j0 wd top := by cases top <;> simp only [j0] <;> omega
  rw [divW, wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (prepA_ok h hr hsv hrsv hN hw hwd) fun s3 ⟨sv3, z3, ka, h3, k3⟩ => ?_
  -- the seed
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (seed_ok h3 ha hr har hN hw hwd hk) fun s4 ⟨v4, o4, h4, k4⟩ => ?_
  have ks : KeyWorkspace.Keep B w [r] [] s3.mem s4.mem :=
    KeyWorkspace.Keep.of_arr (o := r) (d := 0) (n := 4 * (2 * (wd - 1))) (by rw [Nat.add_zero]; exact o4)
      (by simp only [S]; omega) (by simp)
  have ka' : KeyWorkspace.Keep B w [sv, r] [] s.mem s4.mem := ka.trans (ks.mono (by simp) (by simp))
  have nm : ∀ x ∈ [sv, r], x ≠ m := two_ne (Ne.symm hmsv) hrm
  have m4 : wordsVal s4.mem B (arr w m) wd = wordsVal s.mem B (arr w m) wd := by
    rw [wordsVal_eq_val32, wordsVal_eq_val32]
    exact VG.Proof.Rsa.PPC64LE.InvBatch.keep_val ka' (by omega) nm (fun d hd => absurd hd (by simp)) fm
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (prepB_ok h4 ha hr hm ht hmt hN hw hwd hk (by rw [m4]; exact hT))
    fun s6 ⟨z, hz, hP, hd, hd63, hv, hdl, kb, r5, r8, r4, r9, r10, r11, h6, k6⟩ => ?_
  rw [m4] at hd hd63 hdl
  have nr : ∀ x ∈ [t], x ≠ r := fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact Ne.symm hrt
  have nmt : ∀ x ∈ [t], x ≠ m := fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact Ne.symm hmt
  have na : ∀ x ∈ [t], x ≠ a := fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact Ne.symm hat
  have na' : ∀ x ∈ [sv, r], x ≠ a := two_ne (Ne.symm hasv) (Ne.symm har)
  have m6 : wordsVal s6.mem B (arr w m) wd = wordsVal s.mem B (arr w m) wd := by
    rw [← m4, wordsVal_eq_val32, wordsVal_eq_val32]
    exact VG.Proof.Rsa.PPC64LE.InvBatch.keep_val kb (by omega) nmt (fun d hd => absurd hd (by simp)) fm
  -- the dividend's words, as they were
  have aw : ∀ i < 2 * wd, word s6.mem B (arr w a + 8 * i) = word s.mem B (arr w a + 8 * i) := fun i hi => by
    have na1 : ∀ x ∈ [t], x ≠ a := na
    rw [keep_word64 kb (by simp only [S]; omega) na1 fa, keep_word64 ka' (by simp only [S]; omega) na' fa]
  have hX : wordsVal s6.mem B (arr w a) (2 * wd) = num s.mem B w a := by
    rw [wordsVal_eq_val32, show 2 * (2 * wd) = w by omega,
      VG.Proof.Rsa.PPC64LE.InvBatch.keep_val kb (by omega) na (fun d hd => absurd hd (by simp)) fa,
      VG.Proof.Rsa.PPC64LE.InvBatch.keep_val ka' (by omega) na' (fun d hd => absurd hd (by simp)) fa]
  -- the remainder's words: the seed below `wd - 1`, zero from there
  have zr : ∀ i, wd - 1 ≤ i → i < 2 * wd → word s6.mem B (arr w r + 8 * i) = 0 := fun i h1 h2 => by
    rw [keep_word64 kb (by simp only [S]; omega) nr fr, o4.word (by omega) (by omega)]; exact z3 i h2
  have e1 : wordsVal s6.mem B (arr w r) wd = wordsVal s6.mem B (arr w r) (wd - 1) := by
    have := wordsVal_zero_top (m := s6.mem) (B := B) (d := arr w r) (n := wd - 1) 1 fun i h1 h2 => zr i h1 (by omega)
    rwa [show wd - 1 + 1 = wd by omega] at this
  have seedv : wordsVal s6.mem B (arr w r) wd = wordsVal s6.mem B (arr w a + 8 * j0 wd top) (wd - 1) := by
    rw [e1, wordsVal_eq_val32, wordsVal_eq_val32]
    have rk : val32 s6.mem B (arr w r) (2 * (wd - 1)) = val32 s4.mem B (arr w r) (2 * (wd - 1)) := by
      rw [← wordsVal_eq_val32, ← wordsVal_eq_val32]
      exact wordsVal_eq_of _ fun i hi => keep_word64 kb (by simp only [S]; omega) nr fr
    have ak : val32 s6.mem B (arr w a + 8 * j0 wd top) (2 * (wd - 1)) =
        val32 s3.mem B (arr w a + 8 * j0 wd top) (2 * (wd - 1)) := by
      rw [← wordsVal_eq_val32, ← wordsVal_eq_val32]
      refine wordsVal_eq_of _ fun i hi => ?_
      rw [show arr w a + 8 * j0 wd top + 8 * i = arr w a + 8 * (j0 wd top + i) by omega, aw _ (by omega),
        keep_word64 ka (by simp only [S]; omega) na' fa]
    rw [rk, v4, ak]
  have htop : word s6.mem B (arr w r + 8 * wd) = 0 := zr wd (by omega) (by omega)
  have R0lt : wordsVal s6.mem B (arr w r) wd < wordsVal s.mem B (arr w m) wd := by
    rw [e1]; exact Nat.lt_of_lt_of_le (wordsVal_lt _ _ _ _) hT
  -- the dividend's words below `j` after the remainder so far
  let R₀ := wordsVal s6.mem B (arr w r) wd
  let Pf : Nat → Nat := fun j =>
    R₀ * 2 ^ (64 * (j0 wd top - j)) + wordsVal s6.mem B (arr w a + 8 * j) (j0 wd top - j)
  have hPf : ∀ j, 1 ≤ j → j ≤ j0 wd top →
      Pf (j - 1) = (word s6.mem B (arr w a + 8 * (j - 1))).toNat + 2 ^ 64 * Pf j := fun j h1 h2 => by
    simp only [Pf]
    have ew := VG.Proof.Mont.PPC64LE.wordsVal_append s6.mem B (arr w a + 8 * (j - 1)) 1 (j0 wd top - j)
    rw [show 1 + (j0 wd top - j) = j0 wd top - (j - 1) by omega,
      show arr w a + 8 * (j - 1) + 8 * 1 = arr w a + 8 * j by omega] at ew
    rw [ew, show j0 wd top - (j - 1) = (j0 wd top - j) + 1 by omega, Nat.mul_add, Nat.pow_add]
    simp only [wordsVal, Nat.mul_zero, Nat.add_zero, Nat.mul_one]
    rw [show (2 : Nat) ^ (64 * 1) = 2 ^ 64 from rfl, Nat.mul_add]
    ac_rfl
  have h0 : wordsVal s6.mem B (arr w r) wd = Pf (j0 wd top) % wordsVal s6.mem B (arr w m) wd := by
    simp only [Pf, Nat.sub_self, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, wordsVal, Nat.add_zero, m6]
    exact (Nat.mod_eq_of_lt R0lt).symm
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (loop_ok h6 ha hr hm ht har hrm hrt hw hwd hj1 (by omega) r5 r8 r9 r10 r11 r4 hP hz
    (by rw [m6]; exact hd) (by rw [m6]; exact hd63) hv (by rw [m6]; exact hdl) Pf hPf h0 htop)
    fun s7 ⟨q7, top7, o7, k7⟩ => ?_
  rw [m6] at q7
  have h7 := h6.of_keep k7
  rw [show seqs [.block (VG.Impl.Rsa.PPC64LE.KeyDiv.restore sv)] = .block (VG.Impl.Rsa.PPC64LE.KeyDiv.restore sv)
    from rfl]
  have kc : KeyWorkspace.Keep B w [r] [] s6.mem s7.mem :=
    KeyWorkspace.Keep.of_arr (o := r) (d := 0) (n := 8 * (wd + 1)) (by rw [Nat.add_zero]; exact o7)
      (by simp only [S]; omega) (by simp)
  refine WP.mono (restore_ok h7 hsv hN (by omega)) fun u ⟨ug, um, uk⟩ => ⟨fun hXb => ?_, h7.of_keep uk, ?_, ?_⟩
  · -- `[r]`: its first `wd` words, and zeros above.
    have e1' : num u.mem B w r = wordsVal s7.mem B (arr w r) (wd + wd) := by
      show val32 u.mem B (arr w r) w = _
      rw [um, wordsVal_eq_val32]; congr 1; omega
    have P0 : Pf 0 = num s.mem B w a := by
      have nw : num s.mem B w a = wordsVal s.mem B (arr w a) (2 * wd) := by
        rw [wordsVal_eq_val32, show 2 * (2 * wd) = w by omega]
      have hX₆ : wordsVal s6.mem B (arr w a) (2 * wd) < 2 ^ (64 * xw wd top) := by rw [hX, nw]; exact hXb
      rw [← hX]
      -- the dividend's words from `j₀` on: the seed
      have es := VG.Proof.Mont.PPC64LE.wordsVal_append s6.mem B (arr w a) (j0 wd top) (2 * wd - j0 wd top)
      rw [show j0 wd top + (2 * wd - j0 wd top) = 2 * wd by omega] at es
      have hQ : wordsVal s6.mem B (arr w a + 8 * j0 wd top) (2 * wd - j0 wd top) < 2 ^ (64 * (wd - 1)) := by
        have hp : 2 ^ (64 * xw wd top) = 2 ^ (64 * j0 wd top) * 2 ^ (64 * (wd - 1)) := by
          rw [← Nat.pow_add, ← hj, Nat.mul_add]
        have : 2 ^ (64 * j0 wd top) * wordsVal s6.mem B (arr w a + 8 * j0 wd top) (2 * wd - j0 wd top) <
            2 ^ (64 * j0 wd top) * 2 ^ (64 * (wd - 1)) := by rw [← hp]; omega
        exact Nat.lt_of_mul_lt_mul_left this
      have lo := wordsVal_low_of_lt (m := s6.mem) (B := B) (d := arr w a + 8 * j0 wd top) (k := wd - 1)
        (n := 2 * wd - j0 wd top) (by omega) hQ
      simp only [Pf, Nat.sub_zero, Nat.mul_zero, Nat.add_zero]
      show R₀ * 2 ^ (64 * j0 wd top) + wordsVal s6.mem B (arr w a) (j0 wd top) = _
      rw [es, lo, ← seedv]
      ac_rfl
    rw [e1', wordsVal_zero_top wd fun i h1 h2 => ?_, q7, P0]
    rcases Nat.eq_or_lt_of_le h1 with e | e
    · rw [← e]; exact top7
    · rw [o7.word (by omega) (by omega)]; exact zr i (by omega) (by omega)
  · -- The saved registers are restored.
    have kAll := ((((k3.trans k4).trans k6).trans k7).trans uk)
    refine ⟨fun x hx => ?_, kAll.rd, kAll.wr, kAll.sp, kAll.lr⟩
    have sv7 : ∀ i < 7, word s7.mem B (arr w sv + 8 * i) = s.gpr (svReg i) := fun i hi => by
      have ns : ∀ x ∈ [r], x ≠ sv := fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact hrsv
      have ns' : ∀ x ∈ [t], x ≠ sv := fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact htsv
      rw [keep_word64 kc (by simp only [S]; omega) ns fsv, keep_word64 kb (by simp only [S]; omega) ns' fsv,
        keep_word64 ks (by simp only [S]; omega) ns fsv]
      exact sv3 i hi
    by_cases hs : x ∈ [Reg.r14, .r15, .r16, .r17, .r18, .r20, .r22]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (ug 0 (by decide)).trans (sv7 0 (by decide))
      · exact (ug 1 (by decide)).trans (sv7 1 (by decide))
      · exact (ug 2 (by decide)).trans (sv7 2 (by decide))
      · exact (ug 3 (by decide)).trans (sv7 3 (by decide))
      · exact (ug 4 (by decide)).trans (sv7 4 (by decide))
      · exact (ug 5 (by decide)).trans (sv7 5 (by decide))
      · exact (ug 6 (by decide)).trans (sv7 6 (by decide))
    · refine kAll.gpr x ?_
      cases x <;> simp [divRegs, quotRegs, VG.Proof.Rsa.PPC64LE.Loops.loopRegs] at hx hs ⊢
  · rw [um]
    exact ((ka'.mono (by simp) (by simp)).trans (kb.mono (by simp) (by simp))).trans (kc.mono (by simp) (by simp))

/-- `divW a r m t sv`, for `w = 4 wd`, `wd ≥ 4`: `[r] := [a] mod M` for the
divisor `M`, `[m]`'s `wd` words, its top word not zero; changing the arrays
`r`, `t` and `sv`, and the registers `divRegs`. -/
theorem divW_ok {s : State} {B : Addr} {Z w N a r m t sv wd : Nat} (h : Ws s B Z w N)
    (ha : a < N) (hr : r < N) (hm : m < N) (ht : t < N) (hsv : sv < N)
    (har : a ≠ r) (hat : a ≠ t) (hasv : a ≠ sv) (hrm : r ≠ m) (hrt : r ≠ t) (hrsv : r ≠ sv)
    (hmt : m ≠ t) (hmsv : m ≠ sv) (htsv : t ≠ sv) (hN : N ≤ 256) (hw : w = 4 * wd) (hwd : 4 ≤ wd)
    (hT : 2 ^ (64 * (wd - 1)) ≤ wordsVal s.mem B (arr w m) wd) :
    WP isa (divW a r m t sv) s fun u =>
      num u.mem B w r = num s.mem B w a % wordsVal s.mem B (arr w m) wd ∧ Ws u B Z w N ∧ Keep divRegs s u ∧
      KeyWorkspace.Keep B w [r, t, sv] [] s.mem u.mem :=
  WP.mono (divWAt_ok h ha hr hm ht hsv har hat hasv hrm hrt hrsv hmt hmsv htsv hN hw hwd (top := none)
    (fun _ e => nomatch e) hT) fun _ ⟨v, hu, k, kk⟩ => ⟨v (wordsVal_lt _ _ _ _), hu, k, kk⟩

end VG.Proof.Rsa.PPC64LE.KeyDiv
