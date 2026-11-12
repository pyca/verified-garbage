module

public import VerifiedGarbage.Impl.Rsa.PPC64LE.KeyDiv
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyOps
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PreR2Words
import VerifiedGarbage.Proof.Mont.WordsCanonical
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Bignum.WordDiv
import VerifiedGarbage.Proof.Bignum.LongDivision
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

/-- A number's lowest word and the rest. -/
theorem wordsVal_succ_low (m : Mem) (B : Addr) (d k : Nat) :
    wordsVal m B d (k + 1) = (word m B d).toNat + 2 ^ 64 * wordsVal m B (d + 8) k := rfl

/-- Numbers whose words agree. -/
theorem wordsVal_congr_words {m m' : Mem} {B : Addr} {d : Nat} :
    ∀ {k}, (∀ j < k, word m' B (d + 8 * j) = word m B (d + 8 * j)) → wordsVal m' B d k = wordsVal m B d k
  | 0, _ => rfl
  | k + 1, h => by
    rw [wordsVal_succ_top, wordsVal_succ_top, wordsVal_congr_words fun j hj => h j (by omega), h k (by omega)]

/-- The step's tail with the quotient: its digit `q̂ + mask` stored at `r8`,
then `r8` a word down and a step less. -/
theorem tailQ_ok {s : State} {B : Addr} {Z w N d : Nat} (h : Ws s B Z w N) (h8 : s.gpr .r8 = off B d)
    (hd : d + 8 ≤ Z) :
    WP isa (.block [.add .r0 .r18 .r12, .store .d .r0 .r8 0, .subi .r8 .r8 8, .subi .r4 .r4 1]) s fun u =>
      (u.mem = s.mem.writeW (off B d) (s.gpr .r18 + s.gpr .r12) ∧ u.gpr .r8 = s.gpr .r8 - BitVec.ofNat 64 8 ∧
        u.gpr .r4 = s.gpr .r4 - BitVec.ofNat 64 1) ∧ Keep [.r0, .r4, .r8] s u := by
  refine WP.keep _ ?_ (by decide)
  prun [gpr_write, mem_write, h8, BitVec.add_zero, h.scr.st (show d + 8 ≤ Z by omega)]

/-- A word outside every range of a frame. -/
theorem Outs.word64 {B : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs B rs m m') {d : Nat}
    (hd : ∀ r ∈ rs, d + 8 ≤ r.1 ∨ r.1 + r.2 ≤ d) (hd' : d + 8 ≤ 2 ^ 64) : word m' B d = word m B d :=
  Mem.readW_congr fun i hi => h _ fun r hr => by
    have := hd r hr
    rw [ofs_off B (by omega)]; omega

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
    omega

/-- The steps, from `[r] = 0` (its first `D` words) and the temporary set up
for the divisor `M` (`D` words at `[m]`): `A` word steps over the dividend
`X`, the `A` words at `dA`, most significant first, leave `X mod M` in `[r]`'s
first `D` words and zero in word `D`, and with the quotient (`q`) `⌊X / M⌋`
in the dividend's words, changing only those words of memory. -/
theorem loopG_ok (q : Bool) {s : State} {B : Addr} {Z w N r m t D A dA z : Nat} (h : Ws s B Z w N)
    (hr : r < N) (hm : m < N) (ht : t < N) (hrm : r ≠ m) (hrt : r ≠ t) (hD : 4 ≤ D) (hDw : 2 * D + 2 ≤ w + 2)
    (hA : 1 ≤ A) (hA8 : 8 ≤ dA) (hAZ : dA + 8 * A ≤ Z)
    (dar : dA + 8 * A ≤ arr w r ∨ arr w r + S w ≤ dA)
    (dam : q = true → dA + 8 * A ≤ arr w m ∨ arr w m + S w ≤ dA)
    (dat : dA + 8 * A ≤ arr w t ∨ arr w t + S w ≤ dA)
    (h5 : s.gpr .r5 = off B (arr w r)) (h8 : s.gpr .r8 = off B (dA + 8 * A - 8))
    (h9 : s.gpr .r9 = off B (arr w t)) (h10 : s.gpr .r10 = off B (arr w m))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * D)) (h4 : s.gpr .r4 = BitVec.ofNat 64 A)
    (hP : (word s.mem B (arr w t)).toNat = 2 ^ z) (hz : z ≤ 63)
    (hd : (word s.mem B (arr w t + 8)).toNat = wordsVal s.mem B (arr w m) D * 2 ^ z / 2 ^ (64 * (D - 1)))
    (hd63 : 2 ^ 63 ≤ wordsVal s.mem B (arr w m) D * 2 ^ z / 2 ^ (64 * (D - 1)))
    (hv : (word s.mem B (arr w t + 16)).toNat = (2 ^ 128 - 1) / (word s.mem B (arr w t + 8)).toNat - 2 ^ 64)
    (hdl : (word s.mem B (arr w t + 8)).toNat * 2 ^ 64 + (word s.mem B (arr w t + 24)).toNat =
      wordsVal s.mem B (arr w m) D * 2 ^ z / 2 ^ (64 * (D - 2)))
    (h0 : wordsVal s.mem B (arr w r) D = 0) :
    WP isa (.loop (stepG q) (.nonzero .d .r4)) s fun u =>
      wordsVal u.mem B (arr w r) D = wordsVal s.mem B dA A % wordsVal s.mem B (arr w m) D ∧
      word u.mem B (arr w r + 8 * D) = 0 ∧
      (q = true → wordsVal u.mem B dA A = wordsVal s.mem B dA A / wordsVal s.mem B (arr w m) D) ∧
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
  generalize hM : wordsVal s.mem B (arr w m) D = M at hd hd63 hdl ⊢
  have hM0 : 0 < M := Nat.pos_of_ne_zero fun e => by
    rw [e, Nat.zero_mul, Nat.zero_div] at hd63; exact absurd hd63 (by decide)
  -- Outside `[r]`'s words and the dividend: unchanged.
  have out : ∀ {u : State} {d : Nat}, Outs B (stepsFrame q w r D dA A) s.mem u.mem →
      (d + 8 ≤ arr w r ∨ arr w r + 8 * (D + 1) ≤ d) → (q = true → d + 8 ≤ dA ∨ dA + 8 * A ≤ d) → d + 8 ≤ 2 ^ 64 →
      word u.mem B d = word s.mem B d := fun ho h1 h2 h3 => Outs.word64 ho (stepsFrame_out h1 h2) h3
  let Inv : Nat → State → Prop := fun j u =>
    wordsVal u.mem B (arr w r) D = X / 2 ^ (64 * (A - j)) % M ∧
      (0 < j → word u.mem B (arr w r + 8 * D) = 0) ∧
      Outs B (stepsFrame q w r D dA A) s.mem u.mem ∧
      u.gpr .r8 = off B (dA + 8 * A - 8 - 8 * j) ∧
      (∀ i, i + j < A → word u.mem B (dA + 8 * i) = word s.mem B (dA + 8 * i)) ∧
      (q = true → wordsVal u.mem B (dA + 8 * (A - j)) j = X / 2 ^ (64 * (A - j)) / M) ∧
      Keep (.r4 :: .r8 :: quotRegs) s u
  have hXlt : X < 2 ^ (64 * A) := hX ▸ wordsVal_lt _ _ _ _
  have I0 : Inv 0 s := ⟨by rw [h0, Nat.sub_zero, Nat.div_eq_of_lt hXlt, Nat.zero_mod], fun h => absurd h (by decide),
    Outs.refl _ _ _, by rw [h8, Nat.mul_zero, Nat.sub_zero], fun _ _ => rfl,
    fun _ => by rw [Nat.sub_zero, Nat.div_eq_of_lt hXlt, Nat.zero_div]; rfl, Keep.refl _ _⟩
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
  have t0 := out (d := arr w t) uo (by omega_arith) (fun _ => by omega_arith) (by omega_arith)
  have t8 := out (d := arr w t + 8) uo (by omega_arith) (fun _ => by omega_arith) (by omega_arith)
  have t16 := out (d := arr w t + 16) uo (by omega_arith) (fun _ => by omega_arith) (by omega_arith)
  have t24 := out (d := arr w t + 24) uo (by omega_arith) (fun _ => by omega_arith) (by omega_arith)
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
  have hw' : (word s.mem B (dA + 8 * (A - 1 - i))).toNat = X / 2 ^ (64 * (A - 1 - i)) % 2 ^ 64 := by
    rw [← hX, wordsVal_word (by omega_arith)]
  have hsplit : X / 2 ^ (64 * (A - 1 - i)) = X / 2 ^ (64 * (A - i)) * 2 ^ 64 + X / 2 ^ (64 * (A - 1 - i)) % 2 ^ 64 := by
    rw [show 64 * (A - i) = 64 * (A - 1 - i) + 64 by omega_arith, Nat.pow_add, ← Nat.div_div_eq_div_mul]
    exact (Nat.div_add_mod' _ _).symm
  have o1' : ∀ d, (d + 8 ≤ arr w r ∨ arr w r + 8 * (D + 1) ≤ d) → d + 8 ≤ 2 ^ 64 →
      word u₁.mem B d = word u.mem B d := fun d h1 h2 => o1.word h1 h2
  have k01 := uk.trans k1
  have hi8 : u₁.gpr .r8 = off B (dA + 8 * (A - 1 - i)) := by rw [k1.gpr .r8 (by decide), u8]
  have hrem : wordsVal u₁.mem B (arr w r) D = X / 2 ^ (64 * (A - (i + 1))) % M := by
    rw [r1, hw', show A - (i + 1) = A - 1 - i by omega_arith]
    conv => rhs; rw [hsplit, VG.Proof.Bignum.LongDivision.mod_step]
  have hdig : (u₁.gpr .r18 + u₁.gpr .r12).toNat + X / 2 ^ (64 * (A - i)) / M * 2 ^ 64 =
      X / 2 ^ (64 * (A - 1 - i)) / M := by
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
    ⟨by rw [uk2.gpr .r5 (by decide), u15], u8, by rw [uk2.gpr .r4 (by decide), u4], by rw [umm, um]; simp [mem_write],
      ((k2.trans uk).trans uk2).mono (by decide)⟩

/-- A 64-bit word of an array outside a frame. -/
theorem keep_word64 {B : Addr} {w : Nat} {js : List Nat} {m m' : Mem}
    (h : KeyWorkspace.Keep B w js [] m m') {j o : Nat} (ho : o + 8 ≤ S w) (hj : ∀ x ∈ js, x ≠ j)
    (fit : arr w j + S w ≤ 2 ^ 64) : word m' B (arr w j + o) = word m B (arr w j + o) :=
  VG.Proof.Rsa.PPC64LE.InvBatch.keep_word h (b := 64) (by omega) hj (fun d hd => absurd hd (by simp)) fit

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
  refine WP.mono (save_ok h hsv hN (by omega)) fun s1 ⟨sv1, o1, k1⟩ => ?_
  have h1 := h.of_keep k1
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (zeroSetup_ok h1 hr hN) fun s2 ⟨r14, r11, m2, k2⟩ => ?_
  have h2 := h1.of_keep k2
  refine WP.mono (zeroWords_ok (w := v) h2.scr r14 (by rw [r11, hw]) (by omega) (by omega)
    (by omega)) fun s3 ⟨⟨_, z3, o3⟩, k3⟩ => ⟨fun i hi => ?_, z3, ?_, h2.of_keep k3,
      ((k1.trans k2).trans k3).mono (by decide)⟩
  · rw [o3.word (by omega) (by omega), m2]; exact sv1 i hi
  · refine (KeyWorkspace.Keep.of_arr (o := sv) (d := 0) (n := 56) (by rw [Nat.add_zero]; exact o1)
      (by simp only [S]; omega) (by simp)).trans ?_
    rw [← m2]
    exact KeyWorkspace.Keep.of_arr (o := r) (d := 0) (n := 8 * v) (by rw [Nat.add_zero]; exact o3)
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

/-- `normSetupG m t dw`: the addresses of `[m]` and `[t]`, and `dw` sets
`r11 := 2 D`. -/
theorem normSetupG_ok {s : State} {B : Addr} {Z w N m t D : Nat} {dw : List Instr} (h : Ws s B Z w N)
    (hm : m < N) (ht : t < N) (hN : N ≤ 256)
    (hdw : ∀ u : State, Ws u B Z w N →
      WP isa (.block dw) u fun u' => u'.gpr .r11 = BitVec.ofNat 64 (2 * D) ∧ u'.mem = u.mem ∧ Keep [.r11] u u') :
    WP isa (.block (normSetupG m t dw)) s fun u => u.gpr .r10 = off B (arr w m) ∧ u.gpr .r9 = off B (arr w t) ∧
      u.gpr .r11 = BitVec.ofNat 64 (2 * D) ∧ u.mem = s.mem ∧ Keep [.r9, .r10, .r11] s u := by
  simp only [normSetupG, List.append_assoc]
  refine ptr_ok h (r := .r10) (by decide) (by decide) (by decide) (show m < 2 ^ 15 by omega) ?_
  refine ptr_ok (h.of_keep (Keep.write _ .r10 _)) (r := .r9) (by decide) (by decide) (by decide)
    (show t < 2 ^ 15 by omega) ?_
  have k2 : Keep [.r9, .r10] s ((s.write .r10 (off B (arr w m))).write .r9 (off B (arr w t))) :=
    ((Keep.write _ .r10 _).trans (Keep.write _ .r9 _)).mono (by decide)
  refine WP.mono (hdw _ (h.of_keep k2)) fun u ⟨u11, um, uk⟩ =>
    ⟨by rw [uk.gpr .r10 (by decide)]; simp [gpr_write], by rw [uk.gpr .r9 (by decide)]; simp [gpr_write], u11,
      by rw [um]; simp [mem_write], (k2.trans uk).mono (by decide)⟩

/-- Two arrays, neither of them `c`. -/
theorem two_ne {a b c : Nat} (ha : a ≠ c) (hb : b ≠ c) : ∀ x ∈ [a, b], x ≠ c := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ha
  · exact hb

/-- The registers `divW` changes. -/
abbrev divRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

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
  refine WP.mono (loopG_ok q (dA := arr w a) h5 hr hm ht hrm hrt hD (by omega_arith) hA a8 hAZ dar dam dat r5 r8
    ((g5 .r9 (by decide)).trans r9) ((g5 .r10 (by decide)).trans r10) ((g5 .r11 (by decide)).trans r11) r4
    P5 hz d5 e63 v5 l5 h0) fun s6 ⟨q6, top6, qq6, o6, k6⟩ => ?_
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
  have fa := h.arr_fit ha
  have dar := arr_disj (w := w) har
  have dat := arr_disj (w := w) hat
  have dasv := arr_disj (w := w) hasv
  simp only [S] at fa dar dat dasv
  have e11 : BitVec.ofNat 64 w >>> 1 = BitVec.ofNat 64 (2 * wd) := by
    rw [hw, show 4 * wd = 2 * (2 * wd) by omega]; exact mont_ofNat_shr1 (by omega)
  have e : ∀ (mm : Mem) (j : Nat), num mm B w j = wordsVal mm B (arr w j) (2 * wd) := fun mm j => by
    rw [wordsVal_eq_val32, show 2 * (2 * wd) = w by omega]
  refine WP.mono (divG_ok false (A := 2 * wd) (v := 2 * wd) (D := wd) (dw := [.lsr .d .r11 .r29 1])
    (aw := [.addi .r4 .r11 0]) h hr hm ht hsv hrm hrt hrsv hmt hmsv htsv hN
    (by omega) (by omega) hwd (by omega) (by omega) (by omega) ha (by omega) (by simp only [S]; omega)
    (fun hq => absurd hq (by decide)) (by simp only [S]; omega) (by simp only [S]; omega)
    (fun u hu => WP.mono (WP.keep [.r11] (Q := fun u' => u'.gpr .r11 = BitVec.ofNat 64 (2 * wd) ∧ u'.mem = u.mem)
      (by prun [gpr_write, mem_write, hu.r29, e11]) (by decide)) fun _ ⟨⟨a, b⟩, k⟩ => ⟨a, b, k⟩)
    (fun u _ h11 => WP.mono (WP.keep [.r4] (Q := fun u' => u'.gpr .r4 = BitVec.ofNat 64 (2 * wd) ∧ u'.mem = u.mem)
      (by prun [gpr_write, mem_write, h11, BitVec.add_zero]) (by decide)) fun _ ⟨⟨a, b⟩, k⟩ => ⟨a, b, k⟩) hT)
    fun u ⟨ur, _, hu, uk, uo⟩ => ⟨by rw [e, e]; exact ur, hu, uk, ?_⟩
  show Outs B (KeyWorkspace.ranges w [r, t, sv] []) s.mem u.mem
  exact Outs.mono uo fun x hx => by simpa [KeyWorkspace.ranges] using hx

end VG.Proof.Rsa.PPC64LE.KeyDiv
