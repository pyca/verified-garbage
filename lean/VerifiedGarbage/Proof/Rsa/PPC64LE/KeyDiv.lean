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

/-- The step's tail: `u`'s address a word down, a step less. -/
theorem tail_ok (s : State) :
    WP isa (.block [.subi .r8 .r8 8, .subi .r4 .r4 1]) s fun t =>
      t = (s.write .r8 (s.gpr .r8 - BitVec.ofNat 64 8)).write .r4 (s.gpr .r4 - BitVec.ofNat 64 1) := by
  apply WP.of_runBlock
  rw [runBlock_cons, exec_subi (imm := 8) (by decide) (by decide), runStep_some, runBlock_cons,
    exec_subi (imm := 1) (by decide) (by decide), runStep_some, runBlock_nil]
  simp [gpr_write]

/-- The steps, from `[r] = 0` (its first `wd` words) and the temporary set
up for the divisor `M` (`wd` words at `[m]`): `2 wd` word steps over `[a]`'s
`2 wd` words leave `[a] mod M` in `[r]`'s first `wd` words and zero in word
`wd`, changing only those words of memory. -/
theorem loop_ok {s : State} {B : Addr} {Z w N a r m t wd z : Nat} (h : Ws s B Z w N)
    (ha : a < N) (hr : r < N) (hm : m < N) (ht : t < N) (har : a ≠ r) (hrm : r ≠ m) (hrt : r ≠ t)
    (hw : w = 4 * wd) (hwd : 4 ≤ wd)
    (h5 : s.gpr .r5 = off B (arr w r)) (h8 : s.gpr .r8 = off B (arr w a + 16 * wd - 8))
    (h9 : s.gpr .r9 = off B (arr w t)) (h10 : s.gpr .r10 = off B (arr w m))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * wd)) (h4 : s.gpr .r4 = BitVec.ofNat 64 (2 * wd))
    (hP : (word s.mem B (arr w t)).toNat = 2 ^ z) (hz : z ≤ 63)
    (hd : (word s.mem B (arr w t + 8)).toNat = wordsVal s.mem B (arr w m) wd * 2 ^ z / 2 ^ (64 * (wd - 1)))
    (hd63 : 2 ^ 63 ≤ wordsVal s.mem B (arr w m) wd * 2 ^ z / 2 ^ (64 * (wd - 1)))
    (hv : (word s.mem B (arr w t + 16)).toNat = (2 ^ 128 - 1) / (word s.mem B (arr w t + 8)).toNat - 2 ^ 64)
    (hdl : (word s.mem B (arr w t + 8)).toNat * 2 ^ 64 + (word s.mem B (arr w t + 24)).toNat =
      wordsVal s.mem B (arr w m) wd * 2 ^ z / 2 ^ (64 * (wd - 2)))
    (h0 : wordsVal s.mem B (arr w r) wd = 0) :
    WP isa (.loop step (.nonzero .d .r4)) s fun u =>
      wordsVal u.mem B (arr w r) wd = wordsVal s.mem B (arr w a) (2 * wd) % wordsVal s.mem B (arr w m) wd ∧
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
  generalize hX : wordsVal s.mem B (arr w a) (2 * wd) = X
  generalize hM : wordsVal s.mem B (arr w m) wd = M at hd hd63 hdl
  have hM0 : 0 < M := Nat.pos_of_ne_zero fun e => by
    rw [e, Nat.zero_mul, Nat.zero_div] at hd63; exact absurd hd63 (by decide)
  let Inv : Nat → State → Prop := fun j u =>
    wordsVal u.mem B (arr w r) wd = X / 2 ^ (64 * (2 * wd - j)) % M ∧
      (0 < j → word u.mem B (arr w r + 8 * wd) = 0) ∧
      Outside B (arr w r) (8 * (wd + 1)) s.mem u.mem ∧
      u.gpr .r8 = off B (arr w a + 16 * wd - 8 - 8 * j) ∧ Keep (.r4 :: .r8 :: quotRegs) s u
  have hXlt : X < 2 ^ (64 * (2 * wd)) := hX ▸ wordsVal_lt _ _ _ _
  have I0 : Inv 0 s := ⟨by rw [h0, Nat.sub_zero, Nat.div_eq_of_lt hXlt, Nat.zero_mod], fun h => absurd h (by decide),
    Outside.refl _ _ _ _, by rw [h8, Nat.mul_zero, Nat.sub_zero], Keep.refl _ _⟩
  refine WP.mono (wp_countdown (body := step) (cnt := .r4) (N := 2 * wd) (by omega) (by omega) Inv
    (fun i hi u ⟨ur, _, uo, u8, uk⟩ u4 => ?_) I0 h4) fun u ⟨ur, utop, uo, _, uk⟩ =>
      ⟨by rw [ur, Nat.sub_self, Nat.mul_zero, Nat.pow_zero, Nat.div_one], utop (by omega), uo, uk⟩
  have hu := h.of_keep uk
  have g : ∀ x ∈ [Reg.r5, .r9, .r10, .r11], u.gpr x = s.gpr x := fun x hx => uk.gpr x (by revert x hx; decide)
  have om : ∀ d, d + 8 ≤ arr w r ∨ arr w r + 8 * (wd + 1) ≤ d → d + 8 ≤ 2 ^ 64 →
      word u.mem B d = word s.mem B d := fun d hd hd' => uo.word hd hd'
  have wm : wordsVal u.mem B (arr w m) wd = M := by rw [uo.wordsVal (by omega) (by omega), hM]
  have t0 := om (arr w t) (by omega) (by omega)
  have t8 := om (arr w t + 8) (by omega) (by omega)
  have t16 := om (arr w t + 16) (by omega) (by omega)
  have t24 := om (arr w t + 24) (by omega) (by omega)
  have ua := om (arr w a + 8 * (2 * wd - 1 - i)) (by omega) (by omega)
  have e8 : arr w a + 16 * wd - 8 - 8 * i = arr w a + 8 * (2 * wd - 1 - i) := by omega
  rw [e8] at u8
  unfold step
  refine WP.seq (WP.mono (wordStepU_ok (z := z) (dU := arr w a + 8 * (2 * wd - 1 - i)) hu.scr
    ((g .r9 (by decide)).trans h9) ((g .r10 (by decide)).trans h10) ((g .r5 (by decide)).trans h5) u8
    ((g .r11 (by decide)).trans h11) hwd (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [t0]; exact hP) hz (by rw [t8, wm]; exact hd) (by rw [wm]; exact hd63)
    (by rw [t16, t8]; exact hv) (by rw [t8, t24, wm]; exact hdl)
    (by rw [wm, ur]; exact Nat.mod_lt _ hM0)) fun u₁ ⟨⟨r1, top1⟩, o1, k1⟩ => ?_)
  refine WP.mono (tail_ok u₁) fun u₂ e2 => ?_
  subst e2
  refine ⟨⟨?_, fun _ => by rw [mem_write, mem_write]; exact top1, by rw [mem_write, mem_write]; exact uo.trans o1,
    ?_, ?_⟩, ?_⟩
  · rw [mem_write, mem_write, r1, wm, ur, ua]
    have hw' : (word s.mem B (arr w a + 8 * (2 * wd - 1 - i))).toNat = X / 2 ^ (64 * (2 * wd - 1 - i)) % 2 ^ 64 := by
      rw [← hX, wordsVal_word (by omega)]
    rw [hw', show 2 * wd - (i + 1) = 2 * wd - 1 - i by omega]
    exact VG.Proof.Bignum.WordStep.wordDiv_step' (W := 64) (n := 2 * wd - 1 - i) (by rw [show 2 * wd - 1 - i + 1 = 2 * wd - i by omega]) rfl
  · simp only [gpr_write, show (Reg.r8 = Reg.r4) = False by decide, ite_false, ite_true]
    have a8 : 8 ≤ arr w a := Nat.le_trans (by decide) (Nat.le_add_right VG.Proof.Rsa.KeyWorkspace.hdr (a * S w))
    rw [k1.gpr .r8 (by decide), u8,
      show arr w a + 16 * wd - 8 - 8 * (i + 1) = arr w a + 8 * (2 * wd - 1 - i) - 8 by omega,
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

/-- `stepsSetup a r`, from `r11 = 2 wd`: `r5 := [r]`'s address, `r8 :=` that
of `[a]`'s word `2 wd - 1`, `r4 := 2 wd`. -/
theorem stepsSetup_ok {s : State} {B : Addr} {Z w N a r wd : Nat} (h : Ws s B Z w N) (ha : a < N) (hr : r < N)
    (hN : N ≤ 256) (hw : w = 4 * wd) (hwd : 1 ≤ wd) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * wd)) :
    WP isa (.block (stepsSetup a r)) s fun u =>
      u.gpr .r5 = off B (arr w r) ∧ u.gpr .r8 = off B (arr w a + 16 * wd - 8) ∧
      u.gpr .r4 = BitVec.ofNat 64 (2 * wd) ∧ u.mem = s.mem ∧ Keep [.r0, .r4, .r5, .r8] s u := by
  have := h.wle
  have a8 : 8 ≤ arr w a := Nat.le_trans (by decide) (Nat.le_add_right VG.Proof.Rsa.KeyWorkspace.hdr (a * S w))
  have e3 : BitVec.ofNat 64 (2 * wd) <<< 3 = BitVec.ofNat 64 (16 * wd) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  have ea : off B (arr w a) + BitVec.ofNat 64 (16 * wd) - BitVec.ofNat 64 8 = off B (arr w a + 16 * wd - 8) := by
    rw [off_add]
    exact BitVec.sub_eq_iff_eq_add.mpr (by rw [off_add, Nat.sub_add_cancel (by omega)])
  have ea' : off B (arr w a + 16 * wd) - BitVec.ofNat 64 8 = off B (arr w a + 16 * wd - 8) :=
    BitVec.sub_eq_iff_eq_add.mpr (by rw [off_add, Nat.sub_add_cancel (by omega)])
  simp only [stepsSetup, List.append_assoc]
  refine ptr_ok h (r := .r5) (by decide) (by decide) (by decide) (show r < 2 ^ 15 by omega) ?_
  refine ptr_ok (h.of_keep (Keep.write _ .r5 _)) (r := .r8) (by decide) (by decide) (by decide)
    (show a < 2 ^ 15 by omega) ?_
  refine WP.mono (WP.keep [.r0, .r4, .r8] (Q := fun u => u.gpr .r8 = off B (arr w a + 16 * wd - 8) ∧
      u.gpr .r4 = BitVec.ofNat 64 (2 * wd) ∧ u.mem = s.mem) (by
    prun [gpr_write, mem_write, h11, e3, ea, ea', BitVec.add_zero]) (by decide)) fun u ⟨⟨u8, u4, um⟩, uk⟩ =>
    ⟨by rw [uk.gpr .r5 (by decide), gpr_write]; simp [gpr_write], u8, u4, um,
      ((Keep.write _ .r5 _).trans ((Keep.write _ .r8 _).trans uk)).mono (by decide)⟩


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
    (hT : 2 ^ (64 * (wd - 1)) ≤ wordsVal s.mem B (arr w m) wd) :
    WP isa (prepB a r m t) s fun u => ∃ z ≤ 63, (word u.mem B (arr w t)).toNat = 2 ^ z ∧
      (word u.mem B (arr w t + 8)).toNat = wordsVal s.mem B (arr w m) wd * 2 ^ z / 2 ^ (64 * (wd - 1)) ∧
      2 ^ 63 ≤ wordsVal s.mem B (arr w m) wd * 2 ^ z / 2 ^ (64 * (wd - 1)) ∧
      (word u.mem B (arr w t + 16)).toNat = (2 ^ 128 - 1) / (word u.mem B (arr w t + 8)).toNat - 2 ^ 64 ∧
      (word u.mem B (arr w t + 8)).toNat * 2 ^ 64 + (word u.mem B (arr w t + 24)).toNat =
        wordsVal s.mem B (arr w m) wd * 2 ^ z / 2 ^ (64 * (wd - 2)) ∧
      KeyWorkspace.Keep B w [t] [] s.mem u.mem ∧
      u.gpr .r5 = off B (arr w r) ∧ u.gpr .r8 = off B (arr w a + 16 * wd - 8) ∧
      u.gpr .r4 = BitVec.ofNat 64 (2 * wd) ∧ u.gpr .r9 = off B (arr w t) ∧ u.gpr .r10 = off B (arr w m) ∧
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
  rw [show seqs [.block (VG.Impl.Rsa.PPC64LE.KeyDiv.stepsSetup a r)] =
    .block (VG.Impl.Rsa.PPC64LE.KeyDiv.stepsSetup a r) from rfl]
  have g3 : ∀ x ∈ [Reg.r9, .r10, .r11], s3.gpr x = s1.gpr x := fun x hx =>
    (k3.gpr x (by revert x hx; decide)).trans (g2 x hx)
  refine WP.mono (stepsSetup_ok h3 ha hr hN hw (by omega) ((g3 .r11 (by decide)).trans r11))
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
      KeyWorkspace.Keep B w [r, t, sv] [] s.mem u.mem := by
  have := h.wle
  have fa := h.fit64 ha
  have fr := h.fit64 hr
  have fm := h.fit64 hm
  have fsv := h.fit64 hsv
  simp only [S] at fa fr fm fsv
  rw [divW, wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (prepA_ok h hr hsv hrsv hN hw hwd) fun s3 ⟨sv3, z3, ka, h3, k3⟩ => ?_
  have nm : ∀ x ∈ [sv, r], x ≠ m := two_ne (Ne.symm hmsv) hrm
  have m3 : wordsVal s3.mem B (arr w m) wd = wordsVal s.mem B (arr w m) wd := by
    rw [wordsVal_eq_val32, wordsVal_eq_val32]
    exact VG.Proof.Rsa.PPC64LE.InvBatch.keep_val ka (by omega) nm (fun d hd => absurd hd (by simp)) fm
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (prepB_ok h3 ha hr hm ht hmt hN hw hwd (by rw [m3]; exact hT))
    fun s6 ⟨z, hz, hP, hd, hd63, hv, hdl, kb, r5, r8, r4, r9, r10, r11, h6, k6⟩ => ?_
  rw [m3] at hd hd63 hdl
  have nr : ∀ x ∈ [t], x ≠ r := fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact Ne.symm hrt
  have nmt : ∀ x ∈ [t], x ≠ m := fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact Ne.symm hmt
  have na : ∀ x ∈ [t], x ≠ a := fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact Ne.symm hat
  have na' : ∀ x ∈ [sv, r], x ≠ a := two_ne (Ne.symm hasv) (Ne.symm har)
  have m6 : wordsVal s6.mem B (arr w m) wd = wordsVal s.mem B (arr w m) wd := by
    rw [← m3, wordsVal_eq_val32, wordsVal_eq_val32]
    exact VG.Proof.Rsa.PPC64LE.InvBatch.keep_val kb (by omega) nmt (fun d hd => absurd hd (by simp)) fm
  have hX : wordsVal s6.mem B (arr w a) (2 * wd) = num s.mem B w a := by
    rw [wordsVal_eq_val32, show 2 * (2 * wd) = w by omega,
      VG.Proof.Rsa.PPC64LE.InvBatch.keep_val kb (by omega) na (fun d hd => absurd hd (by simp)) fa,
      VG.Proof.Rsa.PPC64LE.InvBatch.keep_val ka (by omega) na' (fun d hd => absurd hd (by simp)) fa]
  have zr : ∀ i < 2 * wd, word s6.mem B (arr w r + 8 * i) = 0 := fun i hi => by
    rw [keep_word64 kb (by simp only [S]; omega) nr fr]; exact z3 i hi
  have h0 : wordsVal s6.mem B (arr w r) wd = 0 := by
    have := wordsVal_zero_top (m := s6.mem) (B := B) (d := arr w r) (n := 0) wd fun i _ h2 => zr i (by omega)
    rw [Nat.zero_add] at this
    rw [this]; rfl
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (loop_ok h6 ha hr hm ht har hrm hrt hw hwd r5 r8 r9 r10 r11 r4 hP hz (by rw [m6]; exact hd)
    (by rw [m6]; exact hd63) hv (by rw [m6]; exact hdl) h0) fun s7 ⟨q7, top7, o7, k7⟩ => ?_
  rw [m6, hX] at q7
  have h7 := h6.of_keep k7
  rw [show seqs [.block (VG.Impl.Rsa.PPC64LE.KeyDiv.restore sv)] = .block (VG.Impl.Rsa.PPC64LE.KeyDiv.restore sv)
    from rfl]
  have kc : KeyWorkspace.Keep B w [r] [] s6.mem s7.mem :=
    KeyWorkspace.Keep.of_arr (o := r) (d := 0) (n := 8 * (wd + 1)) (by rw [Nat.add_zero]; exact o7)
      (by simp only [S]; omega) (by simp)
  refine WP.mono (restore_ok h7 hsv hN (by omega)) fun u ⟨ug, um, uk⟩ => ⟨?_, h7.of_keep uk, ?_, ?_⟩
  · -- `[r]`: its first `wd` words, and zeros above.
    have e1 : num u.mem B w r = wordsVal s7.mem B (arr w r) (wd + wd) := by
      show val32 u.mem B (arr w r) w = _
      rw [um, wordsVal_eq_val32]; congr 1; omega
    rw [e1, wordsVal_zero_top wd fun i h1 h2 => ?_, q7]
    rcases Nat.eq_or_lt_of_le h1 with e | e
    · rw [← e]; exact top7
    · rw [o7.word (by omega) (by omega)]; exact zr i (by omega)
  · -- The saved registers are restored.
    have kAll := (((k3.trans k6).trans k7).trans uk)
    refine ⟨fun x hx => ?_, kAll.rd, kAll.wr, kAll.sp, kAll.lr⟩
    have sv7 : ∀ i < 7, word s7.mem B (arr w sv + 8 * i) = s.gpr (svReg i) := fun i hi => by
      have ns : ∀ x ∈ [r], x ≠ sv := fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact hrsv
      have ns' : ∀ x ∈ [t], x ≠ sv := fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact htsv
      rw [keep_word64 kc (by simp only [S]; omega) ns fsv, keep_word64 kb (by simp only [S]; omega) ns' fsv]
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
      cases x <;> simp [divRegs, quotRegs] at hx hs ⊢
  · rw [um]
    exact ((ka.mono (by simp) (by simp)).trans (kb.mono (by simp) (by simp))).trans (kc.mono (by simp) (by simp))

end VG.Proof.Rsa.PPC64LE.KeyDiv
