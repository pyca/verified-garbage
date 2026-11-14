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
import VerifiedGarbage.Proof.Bignum.LongDivision

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
  cases top <;> simp only [j0, xw] <;> omega_using [hwd]

/-- Words equal word by word. -/
theorem wordsVal_eq_of {m m' : Mem} {B : Addr} {d : Nat} :
    ∀ n, (∀ i < n, word m' B (d + 8 * i) = word m B (d + 8 * i)) → wordsVal m' B d n = wordsVal m B d n
  | 0, _ => rfl
  | n + 1, h => by
    rw [wordsVal_succ_top, wordsVal_succ_top, wordsVal_eq_of n fun i hi => h i (by omega_using [hi]), h n (by omega_using [])]

/-- The low `k` of a number's `n` words, where it is below `2^(64 k)`. -/
theorem wordsVal_low_of_lt {m : Mem} {B : Addr} {d k n : Nat} (hk : k ≤ n) (h : wordsVal m B d n < 2 ^ (64 * k)) :
    wordsVal m B d n = wordsVal m B d k := by
  have e := VG.Proof.Mont.PPC64LE.wordsVal_append m B d k (n - k)
  rw [Nat.add_sub_cancel' hk] at e
  rcases Nat.eq_zero_or_pos (wordsVal m B (d + 8 * k) (n - k)) with h0 | hp
  · rw [e, h0, Nat.mul_zero, Nat.add_zero]
  · have : 2 ^ (64 * k) ≤ 2 ^ (64 * k) * wordsVal m B (d + 8 * k) (n - k) := Nat.le_mul_of_pos_right _ hp
    omega_using [h, e, this]

/-- A word read through a write of another. -/
theorem word_write_ne {m : Mem} {B : Addr} {d d' : Nat} (v : BitVec 64) (h : d' + 8 ≤ d ∨ d + 8 ≤ d')
    (hd : d + 8 ≤ 2 ^ 64) (hd' : d' + 8 ≤ 2 ^ 64) : word (m.writeW (off B d) v) B d' = word m B d' :=
  (writeW_outside m B v hd).word (by omega_using [h]) hd'

/-- `save sv`: `r14`–`r18`, `r20` and `r22` into words 0–6 of the array `sv`. -/
theorem save_ok {s : State} {B : Addr} {Z w N sv : Nat} (h : Ws s B Z w N) (hsv : sv < N) (hN : N ≤ 256) (hw : 12 ≤ w) :
    WP isa (.block (save sv)) s fun t => (∀ i < 7, word t.mem B (arr w sv + 8 * i) = s.gpr (svReg i)) ∧
      Outside B (arr w sv) 56 s.mem t.mem ∧ Keep [.r5] s t := by
  have := h.wle
  have hnw := h.nowrap
  have fs := h.arr_fit hsv
  simp only [S] at fs
  refine ptr_ok h (r := .r5) (by decide) (by decide) (by decide) (show sv < 2 ^ 15 by omega_using [hsv, hN]) ?_
  refine WP.mono (WP.keep [] (Q := fun t => t.mem =
      (((((((s.mem.writeW (off B (arr w sv)) (s.gpr .r14)).writeW (off B (arr w sv + 8)) (s.gpr .r15)).writeW
        (off B (arr w sv + 16)) (s.gpr .r16)).writeW (off B (arr w sv + 24)) (s.gpr .r17)).writeW
        (off B (arr w sv + 32)) (s.gpr .r18)).writeW (off B (arr w sv + 40)) (s.gpr .r20)).writeW
        (off B (arr w sv + 48)) (s.gpr .r22))) (by
      prun [gpr_write, mem_write, off_add, h.scr.st (show arr w sv + 8 ≤ Z by omega_using [fs]),
        h.scr.st (show arr w sv + 8 + 8 ≤ Z by omega_using [hw, fs]), h.scr.st (show arr w sv + 16 + 8 ≤ Z by omega_using [hw, fs]),
        h.scr.st (show arr w sv + 24 + 8 ≤ Z by omega_using [hw, fs]), h.scr.st (show arr w sv + 32 + 8 ≤ Z by omega_using [hw, fs]),
        h.scr.st (show arr w sv + 40 + 8 ≤ Z by omega_using [hw, fs]), h.scr.st (show arr w sv + 48 + 8 ≤ Z by omega_using [hw, fs])]) (by decide))
    fun t ⟨tm, tk⟩ => ⟨fun i hi => ?_, ?_, ((Keep.write _ .r5 _).trans tk).mono (by decide)⟩
  · rw [tm]
    have b : ∀ j, j < 7 → arr w sv + 8 * j + 8 ≤ 2 ^ 64 := fun j hj => by omega_using [hw, hnw, fs, hj]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 by omega_using [hi]) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := omega) only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, show 8 * 2 = 16 from rfl,
      show 8 * 3 = 24 from rfl, show 8 * 4 = 32 from rfl, show 8 * 5 = 40 from rfl, show 8 * 6 = 48 from rfl,
      word_write_ne, word_writeW_self, svReg]
  · rw [tm]
    have o : ∀ (m : Mem) (j : Nat) (v : BitVec 64), j + 8 ≤ 56 →
        Outside B (arr w sv) 56 m (m.writeW (off B (arr w sv + j)) v) := fun m j v hj =>
      (writeW_outside m B v (by omega_using [hw, hnw, fs, hj])).mono (by omega_using []) (by omega_using [hj])
    exact (((((((o _ 0 _ (by omega_using [])).trans (o _ 8 _ (by omega_using []))).trans (o _ 16 _ (by omega_using []))).trans
      (o _ 24 _ (by omega_using []))).trans (o _ 32 _ (by omega_using []))).trans (o _ 40 _ (by omega_using []))).trans (o _ 48 _ (by omega_using [])))

/-- `restore sv`: words 0–6 of the array `sv` back into `r14`–`r18`, `r20`
and `r22`. -/
theorem restore_ok {s : State} {B : Addr} {Z w N sv : Nat} (h : Ws s B Z w N) (hsv : sv < N) (hN : N ≤ 256) (hw : 12 ≤ w) :
    WP isa (.block (restore sv)) s fun t => (∀ i < 7, t.gpr (svReg i) = word s.mem B (arr w sv + 8 * i)) ∧
      t.mem = s.mem ∧ Keep [.r5, .r14, .r15, .r16, .r17, .r18, .r20, .r22] s t := by
  have := h.wle
  have hnw := h.nowrap
  have fs := h.arr_fit hsv
  simp only [S] at fs
  refine ptr_ok h (r := .r5) (by decide) (by decide) (by decide) (show sv < 2 ^ 15 by omega_using [hsv, hN]) ?_
  have r : ∀ j, j < 7 → (s.write .r5 (off B (arr w sv))).mem.readW (off B (arr w sv) + BitVec.ofNat 64 (8 * j)) 64 =
      word s.mem B (arr w sv + 8 * j) := fun j hj => by rw [mem_write, off_add]
  refine WP.mono (WP.keep [.r14, .r15, .r16, .r17, .r18, .r20, .r22] (Q := fun t =>
      (∀ i < 7, t.gpr (svReg i) = word s.mem B (arr w sv + 8 * i)) ∧ t.mem = s.mem) (by
      prun [gpr_write, mem_write, h.scr.ld (show arr w sv + 8 ≤ Z by omega_using [fs]),
        h.scr.ld (show arr w sv + 8 + 8 ≤ Z by omega_using [hw, fs]), h.scr.ld (show arr w sv + 16 + 8 ≤ Z by omega_using [hw, fs]),
        h.scr.ld (show arr w sv + 24 + 8 ≤ Z by omega_using [hw, fs]), h.scr.ld (show arr w sv + 32 + 8 ≤ Z by omega_using [hw, fs]),
        h.scr.ld (show arr w sv + 40 + 8 ≤ Z by omega_using [hw, fs]), h.scr.ld (show arr w sv + 48 + 8 ≤ Z by omega_using [hw, fs]),
        off_add]
      intro i hi
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 by omega_using [hi]) with
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

/-- A number's lowest word and the rest. -/
theorem wordsVal_succ_low (m : Mem) (B : Addr) (d k : Nat) :
    wordsVal m B d (k + 1) = (word m B d).toNat + 2 ^ 64 * wordsVal m B (d + 8) k := rfl

/-- Numbers whose words agree. -/
theorem wordsVal_congr_words {m m' : Mem} {B : Addr} {d : Nat} :
    ∀ {k}, (∀ j < k, word m' B (d + 8 * j) = word m B (d + 8 * j)) → wordsVal m' B d k = wordsVal m B d k
  | 0, _ => rfl
  | k + 1, h => by
    rw [wordsVal_succ_top, wordsVal_succ_top, wordsVal_congr_words fun j hj => h j (by omega_using [hj]), h k (by omega_using [])]

/-- The step's tail with the quotient: its digit `q̂ + mask` stored at `r8`,
then `r8` a word down and a step less. -/
theorem tailQ_ok {s : State} {B : Addr} {Z w N d : Nat} (h : Ws s B Z w N) (h8 : s.gpr .r8 = off B d)
    (hd : d + 8 ≤ Z) :
    WP isa (.block [.add .r0 .r18 .r12, .store .d .r0 .r8 0, .subi .r8 .r8 8, .subi .r4 .r4 1]) s fun u =>
      (u.mem = s.mem.writeW (off B d) (s.gpr .r18 + s.gpr .r12) ∧ u.gpr .r8 = s.gpr .r8 - BitVec.ofNat 64 8 ∧
        u.gpr .r4 = s.gpr .r4 - BitVec.ofNat 64 1) ∧ Keep [.r0, .r4, .r8] s u := by
  refine WP.keep _ ?_ (by decide)
  prun [gpr_write, mem_write, h8, BitVec.add_zero, h.scr.st (show d + 8 ≤ Z by omega_using [hd])]

/-- A word outside every range of a frame. -/
theorem Outs.word64 {B : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs B rs m m') {d : Nat}
    (hd : ∀ r ∈ rs, d + 8 ≤ r.1 ∨ r.1 + r.2 ≤ d) (hd' : d + 8 ≤ 2 ^ 64) : word m' B d = word m B d :=
  Mem.readW_congr fun i hi => h _ fun r hr => by
    have := hd r hr
    rw [ofs_off B (by omega_using [hd', hi])]; omega_using [hi, this]

/-- The frame of the steps: `[r]`'s `D + 1` words and, with the quotient, the
dividend's `A` words at `dA`. -/
def stepsFrame (q : Bool) (w r D dA A : Nat) : List (Nat × Nat) :=
  (arr w r, 8 * (D + 1)) :: if q then [(dA, 8 * A)] else []

/-- A range outside both is outside the frame. -/
theorem stepsFrame_out {q : Bool} {w r D dA A d n : Nat} (h1 : d + n ≤ arr w r ∨ arr w r + 8 * (D + 1) ≤ d)
    (h2 : q = true → d + n ≤ dA ∨ dA + 8 * A ≤ d) :
    ∀ x ∈ stepsFrame q w r D dA A, d + n ≤ x.1 ∨ x.1 + x.2 ≤ d := by
  intro x hx
  cases q with
  | false =>
    simp only [stepsFrame, Bool.false_eq_true, ite_false, List.mem_singleton] at hx
    subst hx; exact h1
  | true =>
    simp only [stepsFrame, ite_true, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact h1
    · exact h2 rfl

/-- Frames of ranges, each inside one of the wider frame's. -/
theorem Outs.cover {B : Addr} {rs rs' : List (Nat × Nat)} {m m' : Mem} (h : Outs B rs m m')
    (hc : ∀ x ∈ rs, ∃ y ∈ rs', y.1 ≤ x.1 ∧ x.1 + x.2 ≤ y.1 + y.2) : Outs B rs' m m' :=
  fun x hx => h x fun r hr => by
    obtain ⟨y, hy, h1, h2⟩ := hc r hr
    have := hx y hy
    omega_using [h1, h2, this]

/-- The steps, from `[r] = 0` (its first `D` words) and the temporary set up
for the divisor `M` (`D` words at `[m]`): `A` word steps over the dividend
`X`, the `A` words at `dA`, most significant first, leave `X mod M` in `[r]`'s
first `D` words and zero in word `D`, and with the quotient (`q`) `⌊X / M⌋`
in the dividend's words, changing only those words of memory. -/
theorem loopG_ok (q : Bool) {s : State} {B : Addr} {Z w N r m t D A dA z R₀ : Nat} (h : Ws s B Z w N)
    (hr : r < N) (hm : m < N) (ht : t < N) (hrm : r ≠ m) (hrt : r ≠ t) (hD : 4 ≤ D) (hDw : 2 * D + 2 ≤ w + 2)
    (hA : 1 ≤ A) (hA8 : 8 ≤ dA) (hAZ : dA + 8 * A ≤ Z)
    (dar : dA + 8 * A ≤ arr w r ∨ arr w r + S w ≤ dA)
    (dam : q = true → dA + 8 * A ≤ arr w m ∨ arr w m + S w ≤ dA)
    (dat : q = true → dA + 8 * A ≤ arr w t ∨ arr w t + S w ≤ dA)
    (h5 : s.gpr .r5 = off B (arr w r)) (h8 : s.gpr .r8 = off B (dA + 8 * A - 8))
    (h9 : s.gpr .r9 = off B (arr w t)) (h10 : s.gpr .r10 = off B (arr w m))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * D)) (h4 : s.gpr .r4 = BitVec.ofNat 64 A)
    (hP : (word s.mem B (arr w t)).toNat = 2 ^ z) (hz : z ≤ 63)
    (hd : (word s.mem B (arr w t + 8)).toNat = wordsVal s.mem B (arr w m) D * 2 ^ z / 2 ^ (64 * (D - 1)))
    (hd63 : 2 ^ 63 ≤ wordsVal s.mem B (arr w m) D * 2 ^ z / 2 ^ (64 * (D - 1)))
    (hv : (word s.mem B (arr w t + 16)).toNat = (2 ^ 128 - 1) / (word s.mem B (arr w t + 8)).toNat - 2 ^ 64)
    (hdl : (word s.mem B (arr w t + 8)).toNat * 2 ^ 64 + (word s.mem B (arr w t + 24)).toNat =
      wordsVal s.mem B (arr w m) D * 2 ^ z / 2 ^ (64 * (D - 2)))
    (hR : R₀ < wordsVal s.mem B (arr w m) D) (h0 : wordsVal s.mem B (arr w r) D = R₀) :
    WP isa (.loop (stepG q) (.nonzero .d .r4)) s fun u =>
      wordsVal u.mem B (arr w r) D = (R₀ * 2 ^ (64 * A) + wordsVal s.mem B dA A) % wordsVal s.mem B (arr w m) D ∧
      word u.mem B (arr w r + 8 * D) = 0 ∧
      (q = true → wordsVal u.mem B dA A =
        (R₀ * 2 ^ (64 * A) + wordsVal s.mem B dA A) / wordsVal s.mem B (arr w m) D) ∧
      Outs B (stepsFrame q w r D dA A) s.mem u.mem ∧ Keep (.r4 :: .r8 :: quotRegs) s u := by
  have := h.wle
  have hnw := h.nowrap
  have fr := h.arr_fit hr
  have fm := h.arr_fit hm
  have ft := h.arr_fit ht
  have drm := arr_disj (w := w) hrm
  have drt := arr_disj (w := w) hrt
  simp only [S] at fr fm ft drm drt dar dam dat
  generalize hX : wordsVal s.mem B dA A = X
  generalize hM : wordsVal s.mem B (arr w m) D = M at hd hd63 hdl hR ⊢
  obtain ⟨Y, hY⟩ : ∃ Y, Y = R₀ * 2 ^ (64 * A) + X := ⟨_, rfl⟩
  rw [← hY]
  have hM0 : 0 < M := Nat.pos_of_ne_zero fun e => by
    rw [e, Nat.zero_mul, Nat.zero_div] at hd63; exact absurd hd63 (by decide)
  -- Outside `[r]`'s words and the dividend: unchanged.
  have out : ∀ {u : State} {d : Nat}, Outs B (stepsFrame q w r D dA A) s.mem u.mem →
      (d + 8 ≤ arr w r ∨ arr w r + 8 * (D + 1) ≤ d) → (q = true → d + 8 ≤ dA ∨ dA + 8 * A ≤ d) → d + 8 ≤ 2 ^ 64 →
      word u.mem B d = word s.mem B d := fun ho h1 h2 h3 => Outs.word64 ho (stepsFrame_out h1 h2) h3
  let Inv : Nat → State → Prop := fun j u =>
    wordsVal u.mem B (arr w r) D = Y / 2 ^ (64 * (A - j)) % M ∧
      (0 < j → word u.mem B (arr w r + 8 * D) = 0) ∧
      Outs B (stepsFrame q w r D dA A) s.mem u.mem ∧
      u.gpr .r8 = off B (dA + 8 * A - 8 - 8 * j) ∧
      (∀ i, i + j < A → word u.mem B (dA + 8 * i) = word s.mem B (dA + 8 * i)) ∧
      (q = true → wordsVal u.mem B (dA + 8 * (A - j)) j = Y / 2 ^ (64 * (A - j)) / M) ∧
      Keep (.r4 :: .r8 :: quotRegs) s u
  have hXlt : X < 2 ^ (64 * A) := hX ▸ wordsVal_lt _ _ _ _
  have hYt : Y / 2 ^ (64 * A) = R₀ := by
    rw [hY, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hXlt, Nat.zero_add]
  have I0 : Inv 0 s := ⟨by rw [h0, Nat.sub_zero, hYt, Nat.mod_eq_of_lt hR], fun h => absurd h (by decide),
    Outs.refl _ _ _, by rw [h8, Nat.mul_zero, Nat.sub_zero], fun _ _ => rfl,
    fun _ => by rw [Nat.sub_zero, hYt, Nat.div_eq_of_lt hR]; rfl, Keep.refl _ _⟩
  refine WP.mono (wp_countdown (body := stepG q) (cnt := .r4) (N := A) (by omega_arith) (by omega_arith) Inv
    (fun i hi u ⟨ur, _, uo, u8, ulo, uq, uk⟩ u4 => ?_) I0 h4) fun u ⟨ur, utop, uo, _, _, uq, uk⟩ =>
      ⟨by rw [ur, Nat.sub_self, Nat.mul_zero, Nat.pow_zero, Nat.div_one], utop (by omega_arith),
        fun hq => by
          have e := uq hq
          simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.div_one] at e
          exact e, uo, uk⟩
  have hu := h.of_keep uk
  have g : ∀ x ∈ [Reg.r5, .r9, .r10, .r11], u.gpr x = s.gpr x := fun x hx => uk.gpr x (by revert x hx; decide)
  have wm : wordsVal u.mem B (arr w m) D = M := by
    rw [← hM]
    exact wordsVal_congr_words fun j hj => out uo (by omega_arith) (fun hq => by have := dam hq; omega_arith) (by omega_arith)
  have t0 := out (d := arr w t) uo (by omega_arith) (fun hq => by have := dat hq; omega_arith) (by omega_arith)
  have t8 := out (d := arr w t + 8) uo (by omega_arith) (fun hq => by have := dat hq; omega_arith) (by omega_arith)
  have t16 := out (d := arr w t + 16) uo (by omega_arith) (fun hq => by have := dat hq; omega_arith) (by omega_arith)
  have t24 := out (d := arr w t + 24) uo (by omega_arith) (fun hq => by have := dat hq; omega_arith) (by omega_arith)
  have ua := ulo (A - 1 - i) (by omega_arith)
  have e8 : dA + 8 * A - 8 - 8 * i = dA + 8 * (A - 1 - i) := by omega_arith
  rw [e8] at u8
  unfold stepG
  refine WP.seq (WP.mono (wordStepQ_ok (z := z) (dU := dA + 8 * (A - 1 - i)) hu.scr
    ((g .r9 (by decide)).trans h9) ((g .r10 (by decide)).trans h10) ((g .r5 (by decide)).trans h5) u8
    ((g .r11 (by decide)).trans h11) hD (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by rw [t0]; exact hP) hz (by rw [t8, wm]; exact hd) (by rw [wm]; exact hd63)
    (by rw [t16, t8]; exact hv) (by rw [t8, t24, wm]; exact hdl)
    (by rw [wm, ur]; exact Nat.mod_lt _ hM0)) fun u₁ ⟨⟨⟨r1, top1⟩, o1, k1⟩, q1⟩ => ?_)
  rw [wm, ur, ua] at r1 q1
  -- The word brought down, and the dividend's top part.
  have hw' : (word s.mem B (dA + 8 * (A - 1 - i))).toNat = Y / 2 ^ (64 * (A - 1 - i)) % 2 ^ 64 := by
    have eY : Y = X + R₀ * 2 ^ (64 * (i + 1)) * 2 ^ (64 * (A - 1 - i)) := by
      rw [hY, Nat.mul_assoc, ← Nat.pow_add, show 64 * (i + 1) + 64 * (A - 1 - i) = 64 * A by omega_arith,
        Nat.add_comm]
    obtain ⟨c, hc⟩ : 2 ^ 64 ∣ R₀ * 2 ^ (64 * (i + 1)) :=
      ⟨R₀ * 2 ^ (64 * i), by rw [show 64 * (i + 1) = 64 + 64 * i by omega_arith, Nat.pow_add, Nat.mul_left_comm]⟩
    rw [eY, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), hc, Nat.add_mul_mod_self_left, ← hX,
      wordsVal_word (by omega_arith)]
  have hsplit : Y / 2 ^ (64 * (A - 1 - i)) = Y / 2 ^ (64 * (A - i)) * 2 ^ 64 + Y / 2 ^ (64 * (A - 1 - i)) % 2 ^ 64 := by
    rw [show 64 * (A - i) = 64 * (A - 1 - i) + 64 by omega_arith, Nat.pow_add, ← Nat.div_div_eq_div_mul]
    exact (Nat.div_add_mod' _ _).symm
  have o1' : ∀ d, (d + 8 ≤ arr w r ∨ arr w r + 8 * (D + 1) ≤ d) → d + 8 ≤ 2 ^ 64 →
      word u₁.mem B d = word u.mem B d := fun d h1 h2 => o1.word h1 h2
  have k01 := uk.trans k1
  have hi8 : u₁.gpr .r8 = off B (dA + 8 * (A - 1 - i)) := by rw [k1.gpr .r8 (by decide), u8]
  have hrem : wordsVal u₁.mem B (arr w r) D = Y / 2 ^ (64 * (A - (i + 1))) % M := by
    rw [r1, hw', show A - (i + 1) = A - 1 - i by omega_arith]
    conv => rhs; rw [hsplit, VG.Proof.Bignum.LongDivision.mod_step]
  have hdig : (u₁.gpr .r18 + u₁.gpr .r12).toNat + Y / 2 ^ (64 * (A - i)) / M * 2 ^ 64 =
      Y / 2 ^ (64 * (A - 1 - i)) / M := by
    rw [q1, hw']
    conv => rhs; rw [hsplit, VG.Proof.Bignum.LongDivision.div_step]
    omega_arith
  have e88 : off B (dA + 8 * (A - 1 - i)) - BitVec.ofNat 64 8 = off B (dA + 8 * A - 8 - 8 * (i + 1)) :=
    BitVec.sub_eq_iff_eq_add.mpr (by rw [off_add, show dA + 8 * A - 8 - 8 * (i + 1) + 8 = dA + 8 * (A - 1 - i) by omega_arith])
  cases q with
  | false =>
    refine WP.mono (tail_ok u₁) fun u₂ e2 => ?_
    subst e2
    refine ⟨⟨by rw [mem_write, mem_write]; exact hrem, fun _ => by rw [mem_write, mem_write]; exact top1,
      by rw [mem_write, mem_write]; exact uo.trans (Outs.of_outside o1 (by simp [stepsFrame])), ?_,
      fun i' hi' => by rw [mem_write, mem_write, o1' (dA + 8 * i') (by omega_arith) (by omega_arith)]; exact ulo i' (by omega_arith),
      fun hq => absurd hq (by decide), ?_⟩, ?_⟩
    · simp only [gpr_write, show (Reg.r8 = Reg.r4) = False by decide, ite_false, ite_true]
      rw [hi8, e88]
    · exact (k01.trans ((Keep.write _ .r8 _).trans (Keep.write _ .r4 _))).mono (by decide)
    · simp only [gpr_write, ite_true]
      rw [k1.gpr .r4 (by decide)]
  | true =>
    refine WP.mono (tailQ_ok (hu.of_keep k1) hi8 (by omega_arith)) fun u₂ ⟨⟨m2, r82, r42⟩, k2⟩ => ?_
    have wo : Outside B (dA + 8 * (A - 1 - i)) 8 u₁.mem u₂.mem := by
      rw [m2]; exact writeW_outside _ B _ (by omega_arith)
    refine ⟨⟨?_, fun _ => ?_, ?_, ?_, fun i' hi' => ?_, fun _ => ?_, ?_⟩, ?_⟩
    · rw [← hrem]; exact wo.wordsVal (by omega_arith) (by omega_arith)
    · rw [wo.word (d := arr w r + 8 * D) (by omega_arith) (by omega_arith)]; exact top1
    · exact (uo.trans (Outs.of_outside o1 (by simp [stepsFrame]))).trans
        (Outs.of_outside (wo.mono (by omega_arith) (by omega_arith) (n' := 8 * A) (o' := dA)) (by simp [stepsFrame]))
    · rw [r82, hi8, e88]
    · rw [wo.word (d := dA + 8 * i') (by omega_arith) (by omega_arith), o1' (dA + 8 * i') (by omega_arith) (by omega_arith)]
      exact ulo i' (by omega_arith)
    · -- The quotient's digits: the new digit below the top part's.
      have w1 : word u₂.mem B (dA + 8 * (A - 1 - i)) = u₁.gpr .r18 + u₁.gpr .r12 := by rw [m2, word_writeW_self]
      have w2 : wordsVal u₂.mem B (dA + 8 * (A - 1 - i) + 8) i = wordsVal u.mem B (dA + 8 * (A - i)) i := by
        rw [wo.wordsVal (by omega_arith) (by omega_arith), o1.wordsVal (by omega_arith) (by omega_arith),
          show dA + 8 * (A - 1 - i) + 8 = dA + 8 * (A - i) by omega_arith]
      rw [show dA + 8 * (A - (i + 1)) = dA + 8 * (A - 1 - i) by omega_arith, wordsVal_succ_low, w1, w2, uq rfl,
        show A - (i + 1) = A - 1 - i by omega_arith, ← hdig]
      omega_arith
    · exact (k01.trans k2).mono (by decide)
    · rw [r42, k1.gpr .r4 (by decide)]

/-- The digits' recurrence `P (j - 1) = u_(j-1) + 2^64 P j`, unrolled: `P (j₀ - k)` is the `k` words
from `j₀ - k` plus `2^(64 k) P j₀`. -/
theorem pf_split {m : Mem} {B : Addr} {d j₀ : Nat} (Pf : Nat → Nat)
    (hPf : ∀ j, 1 ≤ j → j ≤ j₀ → Pf (j - 1) = (word m B (d + 8 * (j - 1))).toNat + 2 ^ 64 * Pf j) :
    ∀ k, k ≤ j₀ → Pf (j₀ - k) = wordsVal m B (d + 8 * (j₀ - k)) k + 2 ^ (64 * k) * Pf j₀
  | 0, _ => by simp [wordsVal]
  | k + 1, hk => by
    have e := hPf (j₀ - k) (by omega_using [hk]) (by omega_using [])
    rw [show j₀ - k - 1 = j₀ - (k + 1) by omega_using [], pf_split Pf hPf k (by omega_using [hk])] at e
    rw [e, wordsVal_succ_low, show d + 8 * (j₀ - (k + 1)) + 8 = d + 8 * (j₀ - k) by omega_using [hk],
      show 64 * (k + 1) = 64 + 64 * k by omega_using [], Nat.pow_add, Nat.mul_add, ← Nat.mul_assoc, Nat.add_assoc]

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
    (h0 : wordsVal s.mem B (arr w r) wd = Pf j₀ % wordsVal s.mem B (arr w m) wd) :
    WP isa (.loop step (.nonzero .d .r4)) s fun u =>
      wordsVal u.mem B (arr w r) wd = Pf 0 % wordsVal s.mem B (arr w m) wd ∧
      word u.mem B (arr w r + 8 * wd) = 0 ∧ Outside B (arr w r) (8 * (wd + 1)) s.mem u.mem ∧
      Keep (.r4 :: .r8 :: quotRegs) s u := by
  have := h.wle
  have fa := h.arr_fit ha
  have dar := arr_disj (w := w) har
  simp only [S] at fa dar
  have a8 : 8 ≤ arr w a := Nat.le_trans (by decide) (Nat.le_add_right VG.Proof.Rsa.KeyWorkspace.hdr (a * S w))
  have hM0 : 0 < wordsVal s.mem B (arr w m) wd := Nat.pos_of_ne_zero fun e => by
    rw [e, Nat.zero_mul, Nat.zero_div] at hd63; exact absurd hd63 (by decide)
  refine WP.mono (loopG_ok false (A := j₀) (dA := arr w a) (D := wd) (R₀ := Pf j₀ % wordsVal s.mem B (arr w m) wd)
    h hr hm ht hrm hrt hwd (by omega_using [hw]) hj a8 (by omega_using [hw, hjw, fa]) (by simp only [S]; omega_using [hw, hjw, dar]) (fun h => absurd h (by decide))
    (fun h => absurd h (by decide)) h5 (by rw [h8]; congr 1; omega_using [hj]) h9 h10 h11 h4 hP hz hd hd63 hv hdl
    (Nat.mod_lt _ hM0) h0) fun u ⟨ur, utop, _, uo, uk⟩ => ⟨?_, utop, fun x hx => uo x fun r hr => ?_, uk⟩
  · have e := pf_split Pf hPf j₀ (Nat.le_refl _)
    rw [Nat.sub_self, Nat.mul_zero, Nat.add_zero] at e
    rw [ur, e]
    generalize wordsVal s.mem B (arr w m) wd = M
    generalize wordsVal s.mem B (arr w a) j₀ = X
    rw [Nat.add_comm (Pf j₀ % M * _), Nat.mul_comm (Pf j₀ % M), Nat.add_mod X, Nat.mul_mod _ (Pf j₀ % M),
      Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]
  · simp only [stepsFrame, Bool.false_eq_true, ite_false, List.mem_singleton] at hr
    subst hr; exact hx

/-- Words above `n` that are zero add nothing. -/
theorem wordsVal_zero_top {m : Mem} {B : Addr} {d n : Nat} :
    ∀ k, (∀ i, n ≤ i → i < n + k → word m B (d + 8 * i) = 0) → wordsVal m B d (n + k) = wordsVal m B d n
  | 0, _ => rfl
  | k + 1, hz => by
    rw [← Nat.add_assoc, wordsVal_succ_top, hz (n + k) (by omega_using []) (by omega_using []),
      wordsVal_zero_top k fun i h1 h2 => hz i h1 (by omega_using [h2])]
    rfl

/-- `ptr r14 r`, `r11 := w`. -/
theorem zeroSetup_ok {s : State} {B : Addr} {Z w N r : Nat} (h : Ws s B Z w N) (hr : r < N) (hN : N ≤ 256) :
    WP isa (.block (ptr .r14 r ++ ([.addi .r11 .r29 0] : List Instr))) s fun u =>
      u.gpr .r14 = off B (arr w r) ∧ u.gpr .r11 = BitVec.ofNat 64 w ∧ u.mem = s.mem ∧ Keep [.r11, .r14] s u := by
  refine ptr_ok h (r := .r14) (by decide) (by decide) (by decide) (show r < 2 ^ 15 by omega_using [hr, hN]) ?_
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
  refine ptr_ok h (r := .r5) (by decide) (by decide) (by decide) (show r < 2 ^ 15 by omega_using [hr, hN]) ?_
  refine ptr_ok (h.of_keep (Keep.write _ .r5 _)) (r := .r8) (by decide) (by decide) (by decide)
    (show a < 2 ^ 15 by omega_using [ha, hN]) ?_
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
      omega_using [hw]
    simp only [VG.Impl.Rsa.PPC64LE.KeyDiv.srcOff, runBlock_cons, runBlock_nil, runStep_some,
      exec_lsl (show 1 < 64 by decide), exec_add,
      exec_addi (d := .r6) (n := .r6) (imm := 8) (by decide) (by decide), Option.some.injEq, exists_eq_left']
    refine ⟨⟨?_, rfl⟩, ((((Keep.write _ .r0 _).trans (Keep.write _ .r6 _)).trans (Keep.write _ .r6 _))).mono (by decide)⟩
    simp only [gpr_write, ite_true, show (Reg.r6 = Reg.r0) = False by decide,
      ite_false, h6, h29, e2, off_add, j0]
    rw [show d + 8 * wd + 8 = d + 8 * (wd + 1) by omega_using []]
  | some k =>
    have := hk k rfl
    simp only [VG.Impl.Rsa.PPC64LE.KeyDiv.srcOff, runBlock_cons, runBlock_nil, runStep_some,
      exec_addi (d := .r6) (n := .r6) (imm := 8 * (k + 1)) (by decide) (by omega_using [hwd', this]), Option.some.injEq, exists_eq_left']
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
    rw [j0_add top (by omega_using [hwd])]; cases top with
    | none => simp only [xw]; omega_using []
    | some k => have := hk k rfl; simp only [xw]; omega_using [this]
  rw [VG.Impl.Rsa.PPC64LE.KeyDiv.seed, WP.seq_iff]
  simp only [VG.Impl.Rsa.PPC64LE.KeyDiv.seedSetup, List.append_assoc]
  refine ptr_ok h (r := .r5) (by decide) (by decide) (by decide) (show r < 2 ^ 15 by omega_using [hr, hN]) ?_
  refine ptr_ok (h.of_keep (Keep.write _ .r5 _)) (r := .r6) (by decide) (by decide) (by decide)
    (show a < 2 ^ 15 by omega_using [ha, hN]) ?_
  rw [WP.block_append_iff]
  refine WP.mono (srcOff_ok (B := B) (d := arr w a) (wd := wd) (by simp [gpr_write]) (by simp [gpr_write, h.r29]) hw
    (by omega) hk) fun u₁ ⟨⟨u6, um₁⟩, uk₁⟩ => ?_
  refine WP.mono (WP.keep [.r8] (Q := fun u => u.gpr .r8 = BitVec.ofNat 64 (2 * (wd - 1)) ∧ u.mem = u₁.mem) (by
      have e8 : BitVec.ofNat 64 w >>> 1 - BitVec.ofNat 64 2 = BitVec.ofNat 64 (2 * (wd - 1)) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_sub, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.shiftRight_eq_div_pow]
        omega_using [hw, hwd, this]
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
  refine WP.mono (VG.Proof.Rsa.PPC64LE.Loops.copyLoop_ok hu.scr h5 h6 u8 (by omega_using [hwd]) (by omega) (by omega_using [hw, fr]) (by omega_using [hw, fa, hjx])
    (by unfold VG.Proof.Rsa.PPC64LE.Loops.Ahead; omega_using [hw, dar, hjx])) fun t ⟨tv, to, tk⟩ => ⟨?_, ?_, hu.of_keep tk, ?_⟩
  · rw [tv, hm]
  · rw [← hm]; exact to.mono (Nat.le_refl _) (by omega_using [])
  · exact (k0.trans tk).mono (by decide)

/-- `stepsSetupG a r aw`, `aw` setting `r4 := A` from `r11` or `r29`:
`r5 := [r]`'s address, `r8 :=` that of the dividend's word `A - 1`. -/
theorem stepsSetupG_ok {s : State} {B : Addr} {Z w N a r A : Nat} {aw : List Instr} (h : Ws s B Z w N)
    (ha : a < N) (hr : r < N) (hN : N ≤ 256) (hA : 1 ≤ A) (hA' : A < 2 ^ 31)
    (haw : ∀ u : State, Ws u B Z w N → u.gpr .r11 = s.gpr .r11 →
      WP isa (.block aw) u fun u' => u'.gpr .r4 = BitVec.ofNat 64 A ∧ u'.mem = u.mem ∧ Keep [.r4] u u') :
    WP isa (.block (stepsSetupG a r aw)) s fun u =>
      u.gpr .r5 = off B (arr w r) ∧ u.gpr .r8 = off B (arr w a + 8 * A - 8) ∧
      u.gpr .r4 = BitVec.ofNat 64 A ∧ u.mem = s.mem ∧ Keep [.r0, .r4, .r5, .r8] s u := by
  have := h.wle
  have a8 : 8 ≤ arr w a := Nat.le_trans (by decide) (Nat.le_add_right VG.Proof.Rsa.KeyWorkspace.hdr (a * S w))
  have e3 : BitVec.ofNat 64 A <<< 3 = BitVec.ofNat 64 (8 * A) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  have ea : off B (arr w a) + BitVec.ofNat 64 (8 * A) - BitVec.ofNat 64 8 = off B (arr w a + 8 * A - 8) := by
    rw [off_add]
    exact BitVec.sub_eq_iff_eq_add.mpr (by rw [off_add, Nat.sub_add_cancel (by omega)])
  have ea' : off B (arr w a + 8 * A) - BitVec.ofNat 64 8 = off B (arr w a + 8 * A - 8) :=
    BitVec.sub_eq_iff_eq_add.mpr (by rw [off_add, Nat.sub_add_cancel (by omega)])
  simp only [stepsSetupG, List.append_assoc]
  refine ptr_ok h (r := .r5) (by decide) (by decide) (by decide) (show r < 2 ^ 15 by omega) ?_
  refine ptr_ok (h.of_keep (Keep.write _ .r5 _)) (r := .r8) (by decide) (by decide) (by decide)
    (show a < 2 ^ 15 by omega) ?_
  have k2 : Keep [.r5, .r8] s ((s.write .r5 (off B (arr w r))).write .r8 (off B (arr w a))) :=
    ((Keep.write _ .r5 _).trans (Keep.write _ .r8 _)).mono (by decide)
  refine WP.block_append (WP.mono (haw _ (h.of_keep k2) (k2.gpr .r11 (by decide))) fun u1 ⟨u4, um, uk⟩ => ?_)
  have u18 : u1.gpr .r8 = off B (arr w a) := by rw [uk.gpr .r8 (by decide)]; simp [gpr_write]
  have u15 : u1.gpr .r5 = off B (arr w r) := by rw [uk.gpr .r5 (by decide)]; simp [gpr_write]
  refine WP.mono (WP.keep [.r0, .r8] (Q := fun u => u.gpr .r8 = off B (arr w a + 8 * A - 8) ∧ u.mem = u1.mem) (by
    prun [gpr_write, mem_write, u4, u18, e3, ea, ea']) (by decide)) fun u ⟨⟨u8, umm⟩, uk2⟩ =>
    ⟨by rw [uk2.gpr .r5 (by decide), u15], u8, by rw [uk2.gpr .r4 (by decide), u4], by rw [umm, um]; simp,
      ((k2.trans uk).trans uk2).mono (by decide)⟩

/-- A 64-bit word of an array outside a frame. -/
theorem keep_word64 {B : Addr} {w : Nat} {js : List Nat} {m m' : Mem}
    (h : KeyWorkspace.Keep B w js [] m m') {j o : Nat} (ho : o + 8 ≤ S w) (hj : ∀ x ∈ js, x ≠ j)
    (fit : arr w j + S w ≤ 2 ^ 64) : word m' B (arr w j + o) = word m B (arr w j + o) :=
  VG.Proof.Rsa.PPC64LE.InvBatch.keep_word h (b := 64) (by omega_using [ho]) hj (fun d hd => absurd hd (by simp)) fit

/-- `prepA r sv`: the registers saved in `sv`, `[r]`'s `v = w / 2` words zeroed. -/
theorem prepA_ok {s : State} {B : Addr} {Z w N r sv v : Nat} (h : Ws s B Z w N) (hr : r < N) (hsv : sv < N)
    (hrsv : r ≠ sv) (hN : N ≤ 256) (hw : w = 2 * v) (hv : 6 ≤ v) :
    WP isa (prepA r sv) s fun u =>
      (∀ i < 7, word u.mem B (arr w sv + 8 * i) = s.gpr (svReg i)) ∧ (∀ i < v, word u.mem B (arr w r + 8 * i) = 0) ∧
      KeyWorkspace.Keep B w [sv, r] [] s.mem u.mem ∧ Ws u B Z w N ∧ Keep [.r0, .r5, .r11, .r14, .r17] s u := by
  have := h.wle
  have hnw := h.nowrap
  have fr := h.arr_fit hr
  have fsv := h.arr_fit hsv
  have d := arr_disj (w := w) hrsv
  simp only [S] at fr fsv d
  rw [prepA, wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (save_ok h hsv hN (by omega_using [hw, hv])) fun s1 ⟨sv1, o1, k1⟩ => ?_
  have h1 := h.of_keep k1
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (zeroSetup_ok h1 hr hN) fun s2 ⟨r14, r11, m2, k2⟩ => ?_
  have h2 := h1.of_keep k2
  refine WP.mono (zeroWords_ok (w := v) h2.scr r14 (by rw [r11, hw]) (by omega_using [hv]) (by omega)
    (by omega_using [hw, fr])) fun s3 ⟨⟨_, z3, o3⟩, k3⟩ => ⟨fun i hi => ?_, z3, ?_, h2.of_keep k3,
      ((k1.trans k2).trans k3).mono (by decide)⟩
  · rw [o3.word (by omega_using [hw, hv, d, hi]) (by omega_using [hw, hv, hnw, fsv, hi]), m2]; exact sv1 i hi
  · refine (KeyWorkspace.Keep.of_arr (o := sv) (d := 0) (n := 56) (by rw [Nat.add_zero]; exact o1)
      (by simp only [S]; omega_using [hw, hv]) (by simp)).trans ?_
    rw [← m2]
    exact KeyWorkspace.Keep.of_arr (o := r) (d := 0) (n := 8 * v) (by rw [Nat.add_zero]; exact o3)
      (by simp only [S]; omega_using [hw]) (by simp)

/-- `x`, plus 1 if it is zero. -/
def fixW (x : BitVec 64) : BitVec 64 := x + ((0#64 - x ||| x) >>> 63 ^^^ 1#64)

theorem shr63_ofNat (y : BitVec 64) : y >>> 63 = BitVec.ofNat 64 (y.toNat / 2 ^ 63) :=
  BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    have := y.isLt; omega_using [])

theorem fixW_toNat (x : BitVec 64) : (fixW x).toNat = x.toNat + if x.toNat = 0 then 1 else 0 := by
  by_cases hx : x = 0#64
  · subst hx; decide
  · have hx' : x.toNat ≠ 0 := fun e => hx (BitVec.eq_of_toNat_eq e)
    have e : (0#64 - x ||| x) >>> 63 = 1#64 := by
      rw [BitVec.ushiftRight_or_distrib, shr63_ofNat, shr63_ofNat (y := x), BitVec.toNat_sub,
        show (0#64).toNat = 0 from rfl, Nat.add_zero]
      have hl := x.isLt
      generalize x.toNat = b at hl hx'
      rcases (show b < 2 ^ 63 ∨ 2 ^ 63 ≤ b by omega_using []) with h | h
      · rw [show (2 ^ 64 - b) % 2 ^ 64 / 2 ^ 63 = 1 by omega_using [hx', h], show b / 2 ^ 63 = 0 by omega_using [h]]; decide
      · rw [show b / 2 ^ 63 = 1 by omega_using [hl, h]]
        rcases (show (2 ^ 64 - b) % 2 ^ 64 / 2 ^ 63 = 0 ∨ (2 ^ 64 - b) % 2 ^ 64 / 2 ^ 63 = 1 by omega_using []) with
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
    rw [hw, show 4 * wd = 2 * (2 * wd) by omega_using []]; exact mont_ofNat_shr1 (by omega)
  have ea := ea_top B (d := arr w m) (w := wd) (c := 8) (by omega_using [hwd])
  rw [show arr w m + 8 * wd - 8 = arr w m + 8 * (wd - 1) by omega_using [hwd]] at ea
  have rT : (s.write .r10 (off B (arr w m))).mem.readW (off B (arr w m + 8 * (wd - 1))) 64 =
      word s.mem B (arr w m + 8 * (wd - 1)) := rfl
  simp only [fixTop]
  refine ptr_ok h (r := .r10) (by decide) (by decide) (by decide) (show m < 2 ^ 15 by omega_using [hm, hN]) ?_
  refine WP.mono (WP.keep [.r0, .r3, .r6, .r11, .r12] (Q := fun u =>
      u.mem = s.mem.writeW (off B (arr w m + 8 * (wd - 1))) (fixW (word s.mem B (arr w m + 8 * (wd - 1))))) (by
    prun [gpr_write, mem_write, h.r29, e11, ea, rT, h.scr.ld (show arr w m + 8 * (wd - 1) + 8 ≤ Z by omega_using [hw, fm]),
      h.scr.st (show arr w m + 8 * (wd - 1) + 8 ≤ Z by omega_using [hw, fm])]
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
        rw [Nat.sub_add_cancel hwd], fios_wordsVal_write_top _ _ _ _ _ (by omega_using [hwd, hd])]
  have e0 := wordsVal_succ_top mem B d (wd - 1)
  rw [Nat.sub_add_cancel hwd] at e0
  have hlow := wordsVal_lt mem B d (wd - 1)
  rw [e', fixW_toNat]
  generalize (word mem B (d + 8 * (wd - 1))).toNat = T at e0 ⊢
  constructor
  · have : 1 ≤ T + (if T = 0 then 1 else 0) := by split <;> omega_arith
    have := Nat.mul_le_mul_left (2 ^ (64 * (wd - 1))) this
    omega_using [this]
  · intro hT
    rcases Nat.eq_zero_or_pos T with h0 | h0
    · rw [h0, Nat.mul_zero, Nat.add_zero] at e0; omega_using [hlow, e0, hT]
    · rw [ite_eq_right (by omega_using [h0]), Nat.add_zero, e0]

/-- `normSetup m t`: the addresses of `[m]` and `[t]`, `r11 := w / 2`. -/
theorem normSetup_ok {s : State} {B : Addr} {Z w N m t wd : Nat} (h : Ws s B Z w N) (hm : m < N) (ht : t < N)
    (hN : N ≤ 256) (hw : w = 4 * wd) (hwd : 1 ≤ wd) :
    WP isa (.block (normSetup m t)) s fun u => u.gpr .r10 = off B (arr w m) ∧ u.gpr .r9 = off B (arr w t) ∧
      u.gpr .r11 = BitVec.ofNat 64 (2 * wd) ∧ u.mem = s.mem ∧ Keep [.r9, .r10, .r11] s u := by
  have := h.wle
  have e11 : BitVec.ofNat 64 w >>> 1 = BitVec.ofNat 64 (2 * wd) := by
    rw [hw, show 4 * wd = 2 * (2 * wd) by omega_using []]; exact mont_ofNat_shr1 (by omega)
  simp only [normSetup, List.append_assoc]
  refine ptr_ok h (r := .r10) (by decide) (by decide) (by decide) (show m < 2 ^ 15 by omega_using [hm, hN]) ?_
  refine ptr_ok (h.of_keep (Keep.write _ .r10 _)) (r := .r9) (by decide) (by decide) (by decide)
    (show t < 2 ^ 15 by omega_using [ht, hN]) ?_
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
  refine WP.mono (normSetup_ok h hm ht hN hw (by omega_using [hwd])) fun s1 ⟨r10, r9, r11, m1, k1⟩ => ?_
  have h1 := h.of_keep k1
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (normAt_ok (dN := arr w m) (dT := arr w t) h1.scr r9 r10 r11 (by omega_using [hwd]) (by omega) (by omega_using [hw, fm])
    (by omega_using [hw, hwd, ft]) (by rw [m1]; exact hT)) fun s2 ⟨⟨z, hz, hP, hd, hd63, hdl⟩, o2, k2⟩ => ?_
  rw [m1] at hd hd63 hdl
  have h2 := h1.of_keep k2
  have g2 : ∀ x ∈ [Reg.r9, .r10, .r11], s2.gpr x = s1.gpr x := fun x hx => k2.gpr x (by revert x hx; decide)
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have h63 : 2 ^ 63 ≤ (word s2.mem B (arr w t + 8)).toNat := by rw [hd]; exact hd63
  refine WP.mono (recipAt_ok (dT := arr w t) h2.scr ((g2 .r9 (by decide)).trans r9) (by omega_using [hw, hwd, ft]) h63)
    fun s3 ⟨⟨v3, o3⟩, k3⟩ => ?_
  have h3 := h2.of_keep k3
  rw [show seqs [.block (VG.Impl.Rsa.PPC64LE.KeyDiv.stepsSetup top a r)] =
    .block (VG.Impl.Rsa.PPC64LE.KeyDiv.stepsSetup top a r) from rfl]
  have g3 : ∀ x ∈ [Reg.r9, .r10, .r11], s3.gpr x = s1.gpr x := fun x hx =>
    (k3.gpr x (by revert x hx; decide)).trans (g2 x hx)
  refine WP.mono (stepsSetup_ok h3 ha hr hN hw (by omega_using [hwd]) hk ((g3 .r11 (by decide)).trans r11))
    fun u ⟨r5, r8, r4, mu, ku⟩ => ⟨z, hz, ?_, ?_, hd63, ?_, ?_, ?_, r5, r8, r4, ?_, ?_, ?_, h3.of_keep ku,
      (((k1.trans k2).trans k3).trans ku).mono (by decide)⟩
  · rw [mu, o3.word (by omega_using []) (by omega_using [hnw, ft])]; exact hP
  · rw [mu, o3.word (by omega_using []) (by omega_using [hw, hwd, hnw, ft])]; exact hd
  · rw [mu, v3, o3.word (by omega_using []) (by omega_using [hw, hwd, hnw, ft])]
  · rw [mu, o3.word (by omega_using []) (by omega_using [hw, hwd, hnw, ft]), o3.word (by omega_using []) (by omega_using [hw, hwd, hnw, ft])]; exact hdl
  · rw [mu, ← m1]
    exact (KeyWorkspace.Keep.of_arr (o := t) (d := 0) (n := 32) (by rw [Nat.add_zero]; exact o2)
      (by simp only [S]; omega_using [hw, hwd]) (by simp)).trans (KeyWorkspace.Keep.of_arr (o := t) (d := 16) (n := 8) o3
      (by simp only [S]; omega_using [hw, hwd]) (by simp))
  · rw [ku.gpr .r9 (by decide), g3 .r9 (by decide), r9]
  · rw [ku.gpr .r10 (by decide), g3 .r10 (by decide), r10]
  · rw [ku.gpr .r11 (by decide), g3 .r11 (by decide), r11]

/-- `normSetupG m t dw`: the addresses of `[m]` and `[t]`, and `dw` sets
`r11 := 2 D`. -/
theorem normSetupG_ok {s : State} {B : Addr} {Z w N m t D : Nat} {dw : List Instr} (h : Ws s B Z w N)
    (hm : m < N) (ht : t < N) (hN : N ≤ 256)
    (hdw : ∀ u : State, Ws u B Z w N →
      WP isa (.block dw) u fun u' => u'.gpr .r11 = BitVec.ofNat 64 (2 * D) ∧ u'.mem = u.mem ∧ Keep [.r11] u u') :
    WP isa (.block (normSetupG m t dw)) s fun u => u.gpr .r10 = off B (arr w m) ∧ u.gpr .r9 = off B (arr w t) ∧
      u.gpr .r11 = BitVec.ofNat 64 (2 * D) ∧ u.mem = s.mem ∧ Keep [.r9, .r10, .r11] s u := by
  simp only [normSetupG, List.append_assoc]
  refine ptr_ok h (r := .r10) (by decide) (by decide) (by decide) (show m < 2 ^ 15 by omega_using [hm, hN]) ?_
  refine ptr_ok (h.of_keep (Keep.write _ .r10 _)) (r := .r9) (by decide) (by decide) (by decide)
    (show t < 2 ^ 15 by omega_using [ht, hN]) ?_
  have k2 : Keep [.r9, .r10] s ((s.write .r10 (off B (arr w m))).write .r9 (off B (arr w t))) :=
    ((Keep.write _ .r10 _).trans (Keep.write _ .r9 _)).mono (by decide)
  refine WP.mono (hdw _ (h.of_keep k2)) fun u ⟨u11, um, uk⟩ =>
    ⟨by rw [uk.gpr .r10 (by decide)]; simp [gpr_write], by rw [uk.gpr .r9 (by decide)]; simp [gpr_write], u11,
      by rw [um]; simp, (k2.trans uk).mono (by decide)⟩

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
  have hj := j0_add top (wd := wd) (by omega_using [hwd])
  have hxw : xw wd top ≤ 2 * wd := by
    cases top with
    | none => simp only [xw]; omega_using []
    | some k => have := hk k rfl; simp only [xw]; omega_using [this]
  have hj1 : 1 ≤ j0 wd top := by cases top <;> simp only [j0] <;> omega_using []
  rw [divW, wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (prepA_ok (v := 2 * wd) h hr hsv hrsv hN (by omega_using [hw]) (by omega_using [hwd])) fun s3 ⟨sv3, z3, ka, h3, k3⟩ => ?_
  -- the seed
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (seed_ok h3 ha hr har hN hw hwd hk) fun s4 ⟨v4, o4, h4, k4⟩ => ?_
  have ks : KeyWorkspace.Keep B w [r] [] s3.mem s4.mem :=
    KeyWorkspace.Keep.of_arr (o := r) (d := 0) (n := 4 * (2 * (wd - 1))) (by rw [Nat.add_zero]; exact o4)
      (by simp only [S]; omega_using [hw]) (by simp)
  have ka' : KeyWorkspace.Keep B w [sv, r] [] s.mem s4.mem := ka.trans (ks.mono (by simp) (by simp))
  have nm : ∀ x ∈ [sv, r], x ≠ m := two_ne (Ne.symm hmsv) hrm
  have m4 : wordsVal s4.mem B (arr w m) wd = wordsVal s.mem B (arr w m) wd := by
    rw [wordsVal_eq_val32, wordsVal_eq_val32]
    exact VG.Proof.Rsa.PPC64LE.InvBatch.keep_val ka' (by omega_using [hw]) nm (fun d hd => absurd hd (by simp)) fm
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
    exact VG.Proof.Rsa.PPC64LE.InvBatch.keep_val kb (by omega_using [hw]) nmt (fun d hd => absurd hd (by simp)) fm
  -- the dividend's words, as they were
  have aw : ∀ i < 2 * wd, word s6.mem B (arr w a + 8 * i) = word s.mem B (arr w a + 8 * i) := fun i hi => by
    have na1 : ∀ x ∈ [t], x ≠ a := na
    rw [keep_word64 kb (by simp only [S]; omega_using [hw, hi]) na1 fa, keep_word64 ka' (by simp only [S]; omega_using [hw, hi]) na' fa]
  have hX : wordsVal s6.mem B (arr w a) (2 * wd) = num s.mem B w a := by
    rw [wordsVal_eq_val32, show 2 * (2 * wd) = w by omega_using [hw],
      VG.Proof.Rsa.PPC64LE.InvBatch.keep_val kb (by omega_using []) na (fun d hd => absurd hd (by simp)) fa,
      VG.Proof.Rsa.PPC64LE.InvBatch.keep_val ka' (by omega_using []) na' (fun d hd => absurd hd (by simp)) fa]
  -- the remainder's words: the seed below `wd - 1`, zero from there
  have zr : ∀ i, wd - 1 ≤ i → i < 2 * wd → word s6.mem B (arr w r + 8 * i) = 0 := fun i h1 h2 => by
    rw [keep_word64 kb (by simp only [S]; omega_using [hw, h2]) nr fr, o4.word (by omega_using [h1]) (by omega_using [hw, hwd, this, fa, fr, fm, fsv, fa', fr', dar, hj, hxw, h1, h2])]; exact z3 i h2
  have e1 : wordsVal s6.mem B (arr w r) wd = wordsVal s6.mem B (arr w r) (wd - 1) := by
    have := wordsVal_zero_top (m := s6.mem) (B := B) (d := arr w r) (n := wd - 1) 1 fun i h1 h2 => zr i h1 (by omega_using [hwd, h2])
    rwa [show wd - 1 + 1 = wd by omega_using [hwd]] at this
  have seedv : wordsVal s6.mem B (arr w r) wd = wordsVal s6.mem B (arr w a + 8 * j0 wd top) (wd - 1) := by
    rw [e1, wordsVal_eq_val32, wordsVal_eq_val32]
    have rk : val32 s6.mem B (arr w r) (2 * (wd - 1)) = val32 s4.mem B (arr w r) (2 * (wd - 1)) := by
      rw [← wordsVal_eq_val32, ← wordsVal_eq_val32]
      exact wordsVal_eq_of _ fun i hi => keep_word64 kb (by simp only [S]; omega_using [hw, hi]) nr fr
    have ak : val32 s6.mem B (arr w a + 8 * j0 wd top) (2 * (wd - 1)) =
        val32 s3.mem B (arr w a + 8 * j0 wd top) (2 * (wd - 1)) := by
      rw [← wordsVal_eq_val32, ← wordsVal_eq_val32]
      refine wordsVal_eq_of _ fun i hi => ?_
      rw [show arr w a + 8 * j0 wd top + 8 * i = arr w a + 8 * (j0 wd top + i) by omega_using [], aw _ (by omega_using [hj, hxw, hi]),
        keep_word64 ka (by simp only [S]; omega_using [hw, hwd, this, fa, fr, fm, fsv, fa', fr', dar, hj, hxw, hj1, hi]) na' fa]
    rw [rk, v4, ak]
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
    rw [show 1 + (j0 wd top - j) = j0 wd top - (j - 1) by omega_using [h1, h2],
      show arr w a + 8 * (j - 1) + 8 * 1 = arr w a + 8 * j by omega_using [h1]] at ew
    rw [ew, show j0 wd top - (j - 1) = (j0 wd top - j) + 1 by omega_using [h1, h2], Nat.mul_add, Nat.pow_add]
    simp only [wordsVal, Nat.mul_zero, Nat.add_zero, Nat.mul_one]
    rw [show (2 : Nat) ^ (64 * 1) = 2 ^ 64 from rfl, Nat.mul_add]
    ac_rfl
  have h0 : wordsVal s6.mem B (arr w r) wd = Pf (j0 wd top) % wordsVal s6.mem B (arr w m) wd := by
    simp only [Pf, Nat.sub_self, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, wordsVal, Nat.add_zero, m6]
    exact (Nat.mod_eq_of_lt R0lt).symm
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (loop_ok h6 ha hr hm ht har hrm hrt hw hwd hj1 (by omega_using [hj, hxw]) r5 r8 r9 r10 r11 r4 hP hz
    (by rw [m6]; exact hd) (by rw [m6]; exact hd63) hv (by rw [m6]; exact hdl) Pf hPf h0)
    fun s7 ⟨q7, top7, o7, k7⟩ => ?_
  rw [m6] at q7
  have h7 := h6.of_keep k7
  rw [show seqs [.block (VG.Impl.Rsa.PPC64LE.KeyDiv.restore sv)] = .block (VG.Impl.Rsa.PPC64LE.KeyDiv.restore sv)
    from rfl]
  have kc : KeyWorkspace.Keep B w [r] [] s6.mem s7.mem :=
    KeyWorkspace.Keep.of_arr (o := r) (d := 0) (n := 8 * (wd + 1)) (by rw [Nat.add_zero]; exact o7)
      (by simp only [S]; omega_using [hw]) (by simp)
  refine WP.mono (restore_ok h7 hsv hN (by omega_using [hw, hwd])) fun u ⟨ug, um, uk⟩ => ⟨fun hXb => ?_, h7.of_keep uk, ?_, ?_⟩
  · -- `[r]`: its first `wd` words, and zeros above.
    have e1' : num u.mem B w r = wordsVal s7.mem B (arr w r) (wd + wd) := by
      show val32 u.mem B (arr w r) w = _
      rw [um, wordsVal_eq_val32]; congr 1; omega_using [hw]
    have P0 : Pf 0 = num s.mem B w a := by
      have nw : num s.mem B w a = wordsVal s.mem B (arr w a) (2 * wd) := by
        rw [wordsVal_eq_val32, show 2 * (2 * wd) = w by omega_using [hw]]
      have hX₆ : wordsVal s6.mem B (arr w a) (2 * wd) < 2 ^ (64 * xw wd top) := by rw [hX, nw]; exact hXb
      rw [← hX]
      -- the dividend's words from `j₀` on: the seed
      have es := VG.Proof.Mont.PPC64LE.wordsVal_append s6.mem B (arr w a) (j0 wd top) (2 * wd - j0 wd top)
      rw [show j0 wd top + (2 * wd - j0 wd top) = 2 * wd by omega_using [hj, hxw]] at es
      have hQ : wordsVal s6.mem B (arr w a + 8 * j0 wd top) (2 * wd - j0 wd top) < 2 ^ (64 * (wd - 1)) := by
        have hp : 2 ^ (64 * xw wd top) = 2 ^ (64 * j0 wd top) * 2 ^ (64 * (wd - 1)) := by
          rw [← Nat.pow_add, ← hj, Nat.mul_add]
        have : 2 ^ (64 * j0 wd top) * wordsVal s6.mem B (arr w a + 8 * j0 wd top) (2 * wd - j0 wd top) <
            2 ^ (64 * j0 wd top) * 2 ^ (64 * (wd - 1)) := by rw [← hp]; omega_using [hX₆, es]
        exact Nat.lt_of_mul_lt_mul_left this
      have lo := wordsVal_low_of_lt (m := s6.mem) (B := B) (d := arr w a + 8 * j0 wd top) (k := wd - 1)
        (n := 2 * wd - j0 wd top) (by omega_using [hj, hxw]) hQ
      simp only [Pf, Nat.sub_zero, Nat.mul_zero, Nat.add_zero]
      show R₀ * 2 ^ (64 * j0 wd top) + wordsVal s6.mem B (arr w a) (j0 wd top) = _
      rw [es, lo, ← seedv]
      ac_rfl
    rw [e1', wordsVal_zero_top wd fun i h1 h2 => ?_, q7, P0]
    rcases Nat.eq_or_lt_of_le h1 with e | e
    · rw [← e]; exact top7
    · rw [o7.word (by omega_using [e]) (by omega_using [hw, hwd, this, fa, fr, fm, fsv, fa', fr', dar, hj, hxw, h1, h2, e])]; exact zr i (by omega_using [h1]) (by omega_using [h2])
  · -- The saved registers are restored.
    have kAll := ((((k3.trans k4).trans k6).trans k7).trans uk)
    refine ⟨fun x hx => ?_, kAll.rd, kAll.wr, kAll.sp, kAll.lr⟩
    have sv7 : ∀ i < 7, word s7.mem B (arr w sv + 8 * i) = s.gpr (svReg i) := fun i hi => by
      have ns : ∀ x ∈ [r], x ≠ sv := fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact hrsv
      have ns' : ∀ x ∈ [t], x ≠ sv := fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact htsv
      rw [keep_word64 kc (by simp only [S]; omega_using [hw, hwd, this, fa, fr, fm, fsv, fa', fr', dar, hj, hxw, hi]) ns fsv, keep_word64 kb (by simp only [S]; omega_using [hw, hwd, this, fa, fr, fm, fsv, fa', fr', dar, hj, hxw, hi]) ns' fsv,
        keep_word64 ks (by simp only [S]; omega_using [hw, hwd, this, fa, fr, fm, fsv, fa', fr', dar, hj, hxw, hi]) ns fsv]
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

/-- A word outside the arrays of a frame. -/
theorem keepW_word {B : Addr} {w : Nat} {js : List Nat} {m m' : Mem} (h : KeyWorkspace.Keep B w js [] m m')
    {d : Nat} (hd : ∀ j ∈ js, d + 8 ≤ arr w j ∨ arr w j + S w ≤ d) (hd' : d + 8 ≤ 2 ^ 64) :
    word m' B d = word m B d :=
  Outs.word64 h (fun x hx => by
    simp only [KeyWorkspace.ranges, List.map_nil, List.append_nil, List.mem_map] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    exact hd j hj) hd'

/-- `divG q a r m t sv dw aw`, for `w = 2 v`: `[r]`'s `v` words := `X mod M`
for the divisor `M`, `[m]`'s `D` words (`dw`: `r11 := 2 D`), its top word
not zero, and the dividend `X`, the `A` words (`aw`: `r4 := A`) from `[a]`'s
address; with the quotient (`q`), those words := `⌊X / M⌋`. Changing the
arrays `r`, `t` and `sv`, with `q` the dividend's words, and the registers
`divRegs`. -/
theorem divG_ok (q : Bool) {s : State} {B : Addr} {Z w N a r m t sv D A v : Nat} {dw aw : List Instr}
    (h : Ws s B Z w N) (hr : r < N) (hm : m < N) (ht : t < N) (hsv : sv < N)
    (hrm : r ≠ m) (hrt : r ≠ t) (hrsv : r ≠ sv) (hmt : m ≠ t) (hmsv : m ≠ sv) (htsv : t ≠ sv)
    (hN : N ≤ 256) (hw : w = 2 * v) (hv : 6 ≤ v) (hD : 4 ≤ D) (hDv : D + 1 ≤ v) (hA : 1 ≤ A) (hA' : A < 2 ^ 31)
    (ha : a < N) (hAZ : arr w a + 8 * A ≤ Z)
    (dar : arr w a + 8 * A ≤ arr w r ∨ arr w r + S w ≤ arr w a)
    (dam : q = true → arr w a + 8 * A ≤ arr w m ∨ arr w m + S w ≤ arr w a)
    (dat : arr w a + 8 * A ≤ arr w t ∨ arr w t + S w ≤ arr w a)
    (dasv : arr w a + 8 * A ≤ arr w sv ∨ arr w sv + S w ≤ arr w a)
    (hdw : ∀ u : State, Ws u B Z w N →
      WP isa (.block dw) u fun u' => u'.gpr .r11 = BitVec.ofNat 64 (2 * D) ∧ u'.mem = u.mem ∧ Keep [.r11] u u')
    (haw : ∀ u : State, Ws u B Z w N → u.gpr .r11 = BitVec.ofNat 64 (2 * D) →
      WP isa (.block aw) u fun u' => u'.gpr .r4 = BitVec.ofNat 64 A ∧ u'.mem = u.mem ∧ Keep [.r4] u u')
    (hT : 2 ^ (64 * (D - 1)) ≤ wordsVal s.mem B (arr w m) D) :
    WP isa (divG q a r m t sv dw aw) s fun u =>
      wordsVal u.mem B (arr w r) v = wordsVal s.mem B (arr w a) A % wordsVal s.mem B (arr w m) D ∧
      (q = true → wordsVal u.mem B (arr w a) A = wordsVal s.mem B (arr w a) A / wordsVal s.mem B (arr w m) D) ∧
      Ws u B Z w N ∧ Keep divRegs s u ∧
      Outs B ((arr w r, S w) :: (arr w t, S w) :: (arr w sv, S w) :: if q then [(arr w a, 8 * A)] else [])
        s.mem u.mem := by
  have := h.wle
  have hnw := h.nowrap
  have fr := h.arr_fit hr
  have fm := h.arr_fit hm
  have ft := h.arr_fit ht
  have fsv := h.arr_fit hsv
  have drm := arr_disj (w := w) hrm
  have drt := arr_disj (w := w) hrt
  have drsv := arr_disj (w := w) hrsv
  have dmt := arr_disj (w := w) hmt
  have dmsv := arr_disj (w := w) hmsv
  have dtsv := arr_disj (w := w) htsv
  simp only [S] at fr fm ft fsv drm drt drsv dmt dmsv dtsv dar dam dat dasv
  have a8 : 8 ≤ arr w a := Nat.le_trans (by decide) (Nat.le_add_right VG.Proof.Rsa.KeyWorkspace.hdr (a * S w))
  generalize hX : wordsVal s.mem B (arr w a) A = X
  generalize hM : wordsVal s.mem B (arr w m) D = M at hT
  rw [divG, wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (prepA_ok h hr hsv hrsv hN hw hv) fun s1 ⟨sv1, z1, k1m, h1, k1⟩ => ?_
  have nsr : ∀ {d : Nat}, (d + 8 ≤ arr w sv ∨ arr w sv + 4 * (w + 2) ≤ d) →
      (d + 8 ≤ arr w r ∨ arr w r + 4 * (w + 2) ≤ d) → d + 8 ≤ 2 ^ 64 → word s1.mem B d = word s.mem B d :=
    fun h1 h2 h3 => keepW_word k1m (fun j hj => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · simp only [S]; exact h1
      · simp only [S]; exact h2) h3
  have X1 : wordsVal s1.mem B (arr w a) A = X := by
    rw [← hX]; exact wordsVal_congr_words fun j hj => nsr (d := arr w a + 8 * j) (by omega_arith) (by omega_arith) (by omega_arith)
  have M1 : wordsVal s1.mem B (arr w m) D = M := by
    rw [← hM]; exact wordsVal_congr_words fun j hj => nsr (d := arr w m + 8 * j) (by omega_arith) (by omega_arith) (by omega_arith)
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (normSetupG_ok h1 hm ht hN hdw) fun s2 ⟨r10, r9, r11, m2, k2⟩ => ?_
  have h2 := h1.of_keep k2
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (normAt_ok (dN := arr w m) (dT := arr w t) h2.scr r9 r10 r11 (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by rw [m2, M1]; exact hT)) fun s3 ⟨⟨z, hz, hP, hd, hd63, hdl⟩, o3, k3⟩ => ?_
  rw [m2, M1] at hd hd63 hdl
  have h3 := h2.of_keep k3
  have g3 : ∀ x ∈ [Reg.r9, .r10, .r11], s3.gpr x = s2.gpr x := fun x hx => k3.gpr x (by revert x hx; decide)
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have h63 : 2 ^ 63 ≤ (word s3.mem B (arr w t + 8)).toNat := by rw [hd]; exact hd63
  refine WP.mono (recipAt_ok (dT := arr w t) h3.scr ((g3 .r9 (by decide)).trans r9) (by omega_arith) h63)
    fun s4 ⟨⟨v4, o4⟩, k4⟩ => ?_
  have h4 := h3.of_keep k4
  have g4 : ∀ x ∈ [Reg.r9, .r10, .r11], s4.gpr x = s2.gpr x := fun x hx =>
    (k4.gpr x (by revert x hx; decide)).trans (g3 x hx)
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (stepsSetupG_ok h4 ha hr hN hA hA' fun u hu e => haw u hu (e.trans ((g4 .r11 (by decide)).trans r11)))
    fun s5 ⟨r5, r8, r4, m5, k5⟩ => ?_
  have h5 := h4.of_keep k5
  have g5 : ∀ x ∈ [Reg.r9, .r10, .r11], s5.gpr x = s2.gpr x := fun x hx =>
    (k5.gpr x (by revert x hx; decide)).trans (g4 x hx)
  -- Memory from `s1` to `s5`: only the temporary changed.
  have w15 : ∀ {d : Nat}, (d + 8 ≤ arr w t ∨ arr w t + 32 ≤ d) → d + 8 ≤ 2 ^ 64 →
      word s5.mem B d = word s1.mem B d := fun h1 h2 => by
    rw [m5, o4.word (by omega_arith) h2, o3.word h1 h2, m2]
  have X5 : wordsVal s5.mem B (arr w a) A = X := by
    rw [← X1]; exact wordsVal_congr_words fun j hj => w15 (d := arr w a + 8 * j) (by omega_arith) (by omega_arith)
  have M5 : wordsVal s5.mem B (arr w m) D = M := by
    rw [← M1]; exact wordsVal_congr_words fun j hj => w15 (d := arr w m + 8 * j) (by omega_arith) (by omega_arith)
  have T5 : ∀ k, k < 4 → word s5.mem B (arr w t + 8 * k) = word s4.mem B (arr w t + 8 * k) := fun k _ => by rw [m5]
  have h0 : wordsVal s5.mem B (arr w r) D = 0 := by
    have := wordsVal_zero_top (m := s5.mem) (B := B) (d := arr w r) (n := 0) D fun i _ h2 => by
      rw [w15 (d := arr w r + 8 * i) (by omega_arith) (by omega_arith)]; exact z1 i (by omega_arith)
    rw [Nat.zero_add] at this
    rw [this]; rfl
  have P5 : (word s5.mem B (arr w t)).toNat = 2 ^ z := by rw [m5, o4.word (by omega_arith) (by omega_arith)]; exact hP
  have d5 : (word s5.mem B (arr w t + 8)).toNat = wordsVal s5.mem B (arr w m) D * 2 ^ z / 2 ^ (64 * (D - 1)) := by
    rw [m5, o4.word (by omega_arith) (by omega_arith), ← m5, M5]; exact hd
  have v5 : (word s5.mem B (arr w t + 16)).toNat = (2 ^ 128 - 1) / (word s5.mem B (arr w t + 8)).toNat - 2 ^ 64 := by
    rw [m5, v4, o4.word (by omega_arith) (by omega_arith)]
  have l5 : (word s5.mem B (arr w t + 8)).toNat * 2 ^ 64 + (word s5.mem B (arr w t + 24)).toNat =
      wordsVal s5.mem B (arr w m) D * 2 ^ z / 2 ^ (64 * (D - 2)) := by
    rw [m5, o4.word (by omega_arith) (by omega_arith), o4.word (by omega_arith) (by omega_arith), ← m5, M5]; exact hdl
  have e63 : 2 ^ 63 ≤ wordsVal s5.mem B (arr w m) D * 2 ^ z / 2 ^ (64 * (D - 1)) := by rw [M5]; exact hd63
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (loopG_ok q (dA := arr w a) (R₀ := 0) h5 hr hm ht hrm hrt hD (by omega_arith) hA a8 hAZ dar dam
    (fun _ => dat) r5 r8 ((g5 .r9 (by decide)).trans r9) ((g5 .r10 (by decide)).trans r10)
    ((g5 .r11 (by decide)).trans r11) r4 P5 hz d5 e63 v5 l5
    (by rw [M5]; exact Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hT) h0) fun s6 ⟨q6, top6, qq6, o6, k6⟩ => ?_
  simp only [Nat.zero_mul, Nat.zero_add] at q6 qq6
  rw [X5, M5] at q6 qq6
  have h6 := h5.of_keep k6
  rw [show seqs [.block (VG.Impl.Rsa.PPC64LE.KeyDiv.restore sv)] = .block (VG.Impl.Rsa.PPC64LE.KeyDiv.restore sv)
    from rfl]
  have w56 : ∀ {d : Nat}, (d + 8 ≤ arr w r ∨ arr w r + 8 * (D + 1) ≤ d) →
      (q = true → d + 8 ≤ arr w a ∨ arr w a + 8 * A ≤ d) → d + 8 ≤ 2 ^ 64 → word s6.mem B d = word s5.mem B d :=
    fun h1 h2 h3 => Outs.word64 o6 (stepsFrame_out h1 h2) h3
  refine WP.mono (restore_ok h6 hsv hN (by omega_arith)) fun u ⟨ug, um, uk⟩ => ⟨?_, fun hq => ?_, h6.of_keep uk, ?_, ?_⟩
  · -- `[r]`: its first `D` words, and zeros above.
    rw [um, show v = D + (v - D) by omega_arith, wordsVal_zero_top (v - D) fun i h1 h2 => ?_, q6]
    rcases Nat.eq_or_lt_of_le h1 with e | e
    · rw [← e]; exact top6
    · rw [w56 (d := arr w r + 8 * i) (by omega_arith) (fun _ => by omega_arith) (by omega_arith),
        w15 (d := arr w r + 8 * i) (by omega_arith) (by omega_arith)]
      exact z1 i (by omega_arith)
  · rw [um]; exact qq6 hq
  · -- The saved registers are restored.
    have kAll := ((((k1.trans k2).trans k3).trans k4).trans k5).trans k6 |>.trans uk
    refine ⟨fun x hx => ?_, kAll.rd, kAll.wr, kAll.sp, kAll.lr⟩
    have sv7 : ∀ i < 7, word s6.mem B (arr w sv + 8 * i) = s.gpr (svReg i) := fun i hi => by
      rw [w56 (d := arr w sv + 8 * i) (by omega_arith) (fun _ => by omega_arith) (by omega_arith),
        w15 (d := arr w sv + 8 * i) (by omega_arith) (by omega_arith)]
      exact sv1 i hi
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
      cases x <;> simp [divRegs, quotRegs, normRegs, recipRegs] at hx hs ⊢
  · -- The frame.
    rw [um]
    have F : ∀ x, x = (arr w r, 4 * (w + 2)) ∨ x = (arr w t, 4 * (w + 2)) ∨ x = (arr w sv, 4 * (w + 2)) →
        x ∈ ((arr w r, S w) :: (arr w t, S w) :: (arr w sv, S w) ::
          if q then [(arr w a, 8 * A)] else [] : List (Nat × Nat)) := fun x hx => by
      rcases hx with rfl | rfl | rfl <;> simp
    refine (((((Outs.cover k1m fun x hx => ?_).trans (by rw [← m2]; exact Outs.refl _ _ _)).trans
      (Outs.cover (Outs.of_outside o3 (List.mem_singleton_self _)) fun x hx => ?_)).trans
      (Outs.cover (Outs.of_outside o4 (List.mem_singleton_self _)) fun x hx => ?_)).trans
      (by rw [m5]; exact Outs.refl _ _ _)).trans (Outs.cover o6 fun x hx => ?_)
    · simp only [KeyWorkspace.ranges, List.map_cons, List.map_nil, List.append_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact ⟨_, F _ (.inr (.inr rfl)), by simp, by simp⟩
      · exact ⟨_, F _ (.inl rfl), by simp, by simp⟩
    · rw [List.mem_singleton] at hx; subst hx; exact ⟨_, F _ (.inr (.inl rfl)), by simp, by simp; omega_arith⟩
    · rw [List.mem_singleton] at hx; subst hx; exact ⟨_, F _ (.inr (.inl rfl)), by simp, by simp; omega_arith⟩
    · cases q with
      | false =>
        simp only [stepsFrame, Bool.false_eq_true, ite_false, List.mem_singleton] at hx
        subst hx; exact ⟨_, F _ (.inl rfl), by simp, by simp; omega_arith⟩
      | true =>
        simp only [stepsFrame, ite_true, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact ⟨_, F _ (.inl rfl), by simp, by simp; omega_arith⟩
        · exact ⟨(arr w a, 8 * A), by simp, by simp, by simp⟩

end VG.Proof.Rsa.PPC64LE.KeyDiv
