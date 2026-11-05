module
-- separate module: the P-521 fast window's proof is split in a chain of modules, so that a change rebuilds only the modules after it

public import VerifiedGarbage.Impl.Weierstrass.X86_64.P521Fast
public import VerifiedGarbage.Proof.Mont.X86_64.MulPX
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.X86_64.Friendly

/-!
# P-521 on x86-64: the square's products (`sqrS`)

`sqrS` (`Impl/Weierstrass/X86_64/P521Fast.lean`) leaves `[rbx]²` with its
words `0 … 7` in the temporary area, word 8 in `r15` and words `9 … 16` in
`xAcc 9 … 16`. Its rows are chains of products (`sqChain_ok`) along the
registers `q w` of consecutive words, each product added at an existing word
or put in a fresh one (`sqStep_ok`); each step states what it computes as an
equation on numbers, the carries in and out included.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64.P521F

open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64.P521F
open VG.Impl.Weierstrass.X86_64.Mont (fnTmp)
open VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono madd_ok movRdx_ok of_setReg of_setFlags adc_carry
  mulx_arith execMulx_eq mulx_ok)

variable {Z : Nat}

/-! ## The registers -/

theorem q_mod (w : Nat) : q w = q (w % 8) := by
  simp only [q]; congr 1; omega

theorem q_ne_of {w w' : Nat} (h : w % 8 ≠ w' % 8) : q w ≠ q w' := by
  rw [q_mod w, q_mod w']
  have hw := Nat.mod_lt w (show 0 < 8 by decide)
  have hw' := Nat.mod_lt w' (show 0 < 8 by decide)
  generalize w % 8 = a at *
  generalize w' % 8 = b at *
  revert a b
  decide

/-- What `q w` is not. -/
theorem q_ne (w : Nat) : q w ≠ .rax ∧ q w ≠ .rcx ∧ q w ≠ .rdx ∧ q w ≠ .rdi ∧ q w ≠ .rbx ∧ q w ≠ .r14 ∧
    q w ∈ xRegs := by
  rw [q_mod w]
  have hw := Nat.mod_lt w (show 0 < 8 by decide)
  generalize w % 8 = a at *
  revert a
  decide

/-- The words `w … w + n - 1` (`qs`): those from `f` counted as zero. -/
def qv (s : State) (w : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, f => (if 0 < f then (s.gpr (q w)).toNat else 0) + 2 ^ 64 * qv s (w + 1) n (f - 1)

theorem qv_congr {s s' : State} : ∀ {w n f : Nat}, (∀ i < n, s'.gpr (q (w + i)) = s.gpr (q (w + i))) →
    qv s' w n f = qv s w n f
  | _, 0, _, _ => rfl
  | w, n + 1, f, h => by
    simp only [qv]
    rw [show s'.gpr (q w) = s.gpr (q w) from h 0 (by omega), qv_congr (s := s) (s' := s') (w := w + 1) (n := n) (f := f - 1) fun i hi => by
      have := h (i + 1) (by omega)
      rw [show w + (i + 1) = w + 1 + i by omega] at this
      exact this]

theorem mem_qs {w n : Nat} {r : Reg} : r ∈ qs w n ↔ ∃ i < n, q (w + i) = r := by
  simp [qs]

/-! ## A product -/

/-- `sqStep fresh x y d`: `rdx · [rbx + d]` added at `x` (OF) and `y` (CF),
`y` counted as zero if `fresh`. -/
theorem sqStep_ok (s : State) {fresh : Bool} {x y : Reg} {d : Nat} {v : BitVec 64} {c o : Bool}
    (hsrc : readSrc s (asrc d) = some v) (hc : s.cf = some c) (ho : s.of = some o)
    (hz : s.gpr .r14 = 0) (hxc : x ≠ .rcx) (hxa : x ≠ .rax) (hyc : y ≠ .rcx) (hya : y ≠ .rax)
    (hxz : x ≠ .r14) (hyz : y ≠ .r14) (hxy : x ≠ y) :
    WP isa (.block (sqStep fresh x y d)) s fun s' =>
      ∃ c' o', s'.cf = some c' ∧ s'.of = some o' ∧
        (s'.gpr x).toNat + 2 ^ 64 * (s'.gpr y).toNat + 2 ^ 64 * o'.toNat + 2 ^ 128 * c'.toNat =
          (s.gpr x).toNat + 2 ^ 64 * (if fresh then 0 else (s.gpr y).toNat) + o.toNat + 2 ^ 64 * c.toNat +
            (s.gpr .rdx).toNat * v.toNat ∧
        Keeps [.rcx, .rax, x, y] s s' := by
  cases fresh with
  | false =>
    refine WP.mono (madd_ok s hsrc (fun _ h => nomatch h) hc ho hxc hxa hyc hya hxy)
      fun s' ⟨c', o', h1, h2, e, k⟩ => ⟨c', o', h1, h2, ?_, k⟩
    simp only [Bool.false_eq_true, ite_false]
    exact e
  | true =>
    apply WP.of_runBlock
    simp only [sqStep, ite_true, runBlock_cons, exec, execMulx_eq hsrc (fun _ h => nomatch h), runStep_some]
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAdox, execAdcx, readSrc,
      Option.bind_some, Option.map_some, RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne _ _ hxa,
      RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hya), RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hxy),
      RegUpd.gpr_setReg_of_ne _ _ hxy, RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hyz),
      RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hxz), RegUpd.gpr_setReg_of_ne _ _ (by decide : Reg.r14 ≠ .rax),
      RegUpd.gpr_setFlags, of_setReg, of_setFlags, RegUpd.cf_setReg, RegUpd.cf_setFlags, ho, hc, hz,
      Option.some.injEq, exists_eq_left']
    refine ⟨_, _, (by trivial), (by trivial), ?_, fun r hr => ?_, (by trivial), (by trivial), (by trivial)⟩
    · have e1 := adc_carry (s.gpr x) (BitVec.ofNat 64 ((s.gpr .rdx).toNat * v.toNat)) o
      have e2 := adc_carry (BitVec.ofNat 64 ((s.gpr .rdx).toNat * v.toNat / 2 ^ 64)) 0 c
      have e3 := mulx_arith (s.gpr .rdx) v
      have h0 : BitVec.toNat (0 : BitVec 64) = 0 := rfl
      omega_arith
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_setReg_of_ne _ _ hr.2.2.2, RegUpd.gpr_setReg_of_ne _ _ hr.2.2.1,
        RegUpd.gpr_setFlags, RegUpd.gpr_setReg_of_ne _ _ hr.2.1]

/-- `[d] = r` if `p`, the registers and flags unchanged. -/
theorem optStore_ok {s : State} {base : Addr} (hZ : 4096 ≤ Z) (hs : Scr s base Z) (p : Prop) [Decidable p] (r : Reg) {d : Nat}
    (hd : p → d + 8 ≤ 4096) :
    WP isa (.block (if p then [.store (sc d) r] else [])) s fun s' =>
      s'.gpr = s.gpr ∧ s'.cf = s.cf ∧ s'.of = s.of ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        (p → s'.mem = s.mem.writeW (off base d) (s.gpr r)) ∧ (¬p → s'.mem = s.mem) := by
  by_cases h : p
  · rw [ite_eq_left h]
    exact WP.mono (storeX_ok hs r (by have := hd h; omega)) fun s' ⟨m, g, cf, of, rd, wr⟩ =>
      ⟨g, cf, of, rd, wr, fun _ => m, fun h' => absurd h h'⟩
  · rw [ite_eq_right h]
    exact WP.block_nil ⟨rfl, rfl, rfl, rfl, rfl, fun h' => absurd h' h, fun _ => rfl⟩

theorem Outside.of_zero {base : Addr} {o o' n' : Nat} {m m' : Mem} (h : Outside base o 0 m m') :
    Outside base o' n' m m' := fun x _ => h x (by omega)

theorem T_eq (w : Nat) : T w = 4024 + 8 * w := by simp only [T, fnTmp]

theorem T_succ (w : Nat) : T (w + 1) = T w + 8 := by simp only [T]; omega

theorem T_le (w : Nat) : fnTmp ≤ T w := by simp only [T]; omega

theorem rows_q (w w' : Nat) : ∀ t ∈ [Reg.rcx, .rax, q w, q w'], t ∈ rowRegs := by
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · decide
  · decide
  · exact mem_rowRegs_x (q_ne w).2.2.2.2.2.2
  · exact mem_rowRegs_x (q_ne w').2.2.2.2.2.2

theorem q_not_qs {w w' n : Nat} (h1 : w < w') (h2 : w' + n ≤ w + 8) : q w ∉ qs w' n := by
  rw [mem_qs]
  rintro ⟨i, hi, he⟩
  exact q_ne_of (show (w' + i) % 8 ≠ w % 8 by omega) he

theorem qs_sub {w n : Nat} {r : Reg} (h : r ∈ qs (w + 1) n) : r ∈ qs w (n + 1) := by
  rw [mem_qs] at *
  obtain ⟨i, hi, he⟩ := h
  exact ⟨i + 1, by omega, by rw [← he]; congr 1; omega⟩

/-! ## A chain of products -/

/-- `sqChain n w d f st`: `rdx · [rbx + d … d + 8n)` added at the words
`w … w + n` (`qv`), those from `w + f` (from `w + 1` if `f ≤ 1`) counted as
zero, with the carries OF into word `w` and CF into word `w + 1` in, and OF
(into word `w + n`) and CF (into `w + n + 1`) out; the first `st` words
stored once final. -/
theorem sqChain_ok : ∀ (n : Nat) {w d f st : Nat} {s : State} {base bA : Addr} {c o : Bool},
    Scr s base Z → 4096 ≤ Z → PtrC s .rbx bA 72 0 → Apart bA 0 72 base fnTmp 72 → d + 8 * n ≤ 72 → n < 8 →
    (0 < st → w + st ≤ 9) → s.gpr .r14 = 0 → s.cf = some c → s.of = some o →
    WP isa (.block (sqChain n w d f st)) s fun s' => ∃ c' o', s'.cf = some c' ∧ s'.of = some o' ∧
      qv s' w (n + 1) (n + 1) + 2 ^ (64 * n) * o'.toNat + 2 ^ (64 * (n + 1)) * c'.toNat =
        qv s w (n + 1) (max f 1) + o.toNat + 2 ^ 64 * c.toNat + (s.gpr .rdx).toNat * wordsVal s.mem bA d n ∧
      (∀ i, i < st → i < n → word s'.mem base (T (w + i)) = s'.gpr (q (w + i))) ∧
      KeepRegs (.rax :: .rcx :: qs w (n + 1)) s s' ∧ Outside base (T w) (8 * min st n) s.mem s'.mem
  | 0, w, d, f, st, s, base, bA, c, o, _, _, _, _, _, _, _, _, hc, ho => by
    refine WP.block_nil ⟨c, o, hc, ho, ?_, fun _ _ h => absurd h (Nat.not_lt_zero _),
      ⟨fun _ _ => rfl, rfl, rfl⟩, Outside.refl _ _ _ _⟩
    simp only [qv, wordsVal, ite_eq_left (show 0 < max f 1 by omega), ite_eq_left (show 0 < 0 + 1 by omega)]
    omega
  | n + 1, w, d, f, st, s, base, bA, c, o, hs, hZ, hp, hap, hd, hn, hst, hz, hc, ho => by
    have hnw := hs.nowrap
    obtain ⟨hxa, hxc, hxd, hxi, hxb, hxz, -⟩ := q_ne w
    obtain ⟨hya, hyc, hyd, hyi, hyb, hyz, -⟩ := q_ne (w + 1)
    have hxy : q w ≠ q (w + 1) := q_ne_of (by omega)
    rw [sqChain, List.append_assoc, WP.block_append_iff]
    refine WP.mono (sqStep_ok s (fresh := decide (f ≤ 1)) (v := word s.mem bA d) (by exact readSrc_rcR hp (d := d) (by omega))
      hc ho hz hxc hxa hyc hya hxz hyz hxy) fun s₁ ⟨c₁, o₁, cf₁, of₁, e₁, k₁⟩ => ?_
    have hn₁ : ∀ r, r ≠ .rcx → r ≠ .rax → r ≠ q w → r ≠ q (w + 1) → s₁.gpr r = s.gpr r := fun r h1 h2 h3 h4 =>
      k₁.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h1, h2, h3, h4⟩)
    have hs₁ := hs.of_keeps k₁ (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
                                   exact ⟨by decide, by decide, Ne.symm hxi, Ne.symm hyi⟩)
    have hp₁ := hp.of_keeps k₁ (rows_q w (w + 1))
    rw [WP.block_append_iff]
    refine WP.mono (optStore_ok hZ hs₁ (0 < st) (q w) (d := T w) (fun h => by rw [T_eq] at *; omega))
      fun s₂ ⟨g₂, cf₂, of₂, rd₂, wr₂, m₂t, m₂f⟩ => ?_
    have hs₂ : Scr s₂ base Z := ⟨by rw [g₂]; exact hs₁.rdi, by rw [wr₂]; exact hs₁.wr, hs₁.nowrap⟩
    have hp₂ := hp₁.of_store g₂ rd₂ wr₂
    have hz₂ : s₂.gpr .r14 = 0 := by rw [g₂, hn₁ _ (by decide) (by decide) (Ne.symm hxz) (Ne.symm hyz)]; exact hz
    refine WP.mono (sqChain_ok n (w := w + 1) (d := d + 8) (f := f - 1) (st := st - 1) hs₂ hZ hp₂ hap (by omega)
      (by omega) (by omega) hz₂ (cf₂.trans cf₁) (of₂.trans of₁)) fun s₃ ⟨c₃, o₃, cf₃, of₃, e₃, st₃, k₃, O₃⟩ => ?_
    have hq₃ : s₃.gpr (q w) = s₁.gpr (q w) := by
      rw [k₃.gpr _ (by
        simp only [List.mem_cons, not_or]
        exact ⟨hxa, hxc, q_not_qs (by omega) (by omega)⟩), g₂]
    -- The memory.
    have O₂ : Outside base (T w) (8 * min st (n + 1)) s₁.mem s₂.mem := by
      by_cases h : 0 < st
      · rw [m₂t h]
        exact (writeW_outside _ _ _ (by rw [T_eq] at *; omega)).mono (Nat.le_refl _) (by omega)
      · rw [m₂f h]; exact Outside.refl _ _ _ _
    have O₃' : Outside base (T w) (8 * min st (n + 1)) s₂.mem s₃.mem := by
      by_cases h : st = 0
      · subst h; exact Outside.of_zero (by simpa using O₃)
      · exact O₃.mono (by rw [T_succ]; omega) (by rw [T_succ]; omega)
    have O : Outside base (T w) (8 * min st (n + 1)) s.mem s₃.mem := by
      rw [← k₁.2.1]; exact O₂.trans O₃'
    have hap' : Apart bA (d + 8) (8 * n) base (T w) (8 * min st (n + 1)) := by
      by_cases h : st = 0
      · subst h; exact fun i _ => by omega
      · exact (hap.sub (by omega) (by omega)).mono (T_le w) (by
          have := T_eq w; have : fnTmp = 4024 := rfl; omega)
    have hW : wordsVal s₂.mem bA (d + 8) n = wordsVal s.mem bA (d + 8) n := by
      rw [← k₁.2.1]; exact O₂.wordsVal' hap'
    refine ⟨c₃, o₃, cf₃, of₃, ?_, ?_, ?_, O⟩
    · -- The values.
      have hdx : s₂.gpr .rdx = s.gpr .rdx := by rw [g₂, hn₁ _ (by decide) (by decide) (Ne.symm hxd) (Ne.symm hyd)]
      have hrest : qv s₂ (w + 2) n (f - 2) = qv s (w + 2) n (f - 2) := qv_congr fun i hi => by
        rw [g₂, hn₁ _ (q_ne _).2.1 (q_ne _).1 (q_ne_of (by omega)) (q_ne_of (by omega))]
      have hy₂ : s₂.gpr (q (w + 1)) = s₁.gpr (q (w + 1)) := by rw [g₂]
      have hq2 : qv s₂ (w + 1) (n + 1) (max (f - 1) 1) =
          (s₁.gpr (q (w + 1))).toNat + 2 ^ 64 * qv s (w + 2) n (f - 2) := by
        rw [qv, ite_eq_left (by omega), hy₂, show max (f - 1) 1 - 1 = f - 2 by omega, show w + 1 + 1 = w + 2 by omega,
          hrest]
      have hq0 : qv s w (n + 1 + 1) (max f 1) = (s.gpr (q w)).toNat +
          2 ^ 64 * ((if decide (f ≤ 1) = true then 0 else (s.gpr (q (w + 1))).toNat) +
            2 ^ 64 * qv s (w + 2) n (f - 2)) := by
        rw [qv, ite_eq_left (by omega), qv, show max f 1 - 1 - 1 = f - 2 by omega, show w + 1 + 1 = w + 2 by omega]
        by_cases h : f ≤ 1
        · rw [ite_eq_right (by omega), ite_eq_left (by simpa using h)]
        · rw [ite_eq_left (by omega), ite_eq_right (by simpa using h)]
      have hq3 : qv s₃ w (n + 1 + 1) (n + 1 + 1) = (s₁.gpr (q w)).toNat + 2 ^ 64 * qv s₃ (w + 1) (n + 1) (n + 1) := by
        rw [qv, ite_eq_left (by omega), hq₃, show n + 1 + 1 - 1 = n + 1 by omega]
      rw [hq2, hdx, hW] at e₃
      rw [hq3, hq0, show wordsVal s.mem bA d (n + 1) = (word s.mem bA d).toNat + 2 ^ 64 * wordsVal s.mem bA (d + 8) n
        from rfl]
      rw [pow64_succ (n + 1), pow64_succ n] at *
      generalize 2 ^ (64 * n) = P at *
      generalize (if decide (f ≤ 1) = true then 0 else (s.gpr (q (w + 1))).toNat) = Y at *
      rw [Nat.mul_add (s.gpr .rdx).toNat, Nat.mul_left_comm (s.gpr .rdx).toNat (2 ^ 64)]
      simp only [Nat.mul_assoc] at e₃ ⊢
      omega_arith
    · intro i hi hin
      rcases i with _ | i
      · rw [Nat.add_zero, O₃.word (by rw [T_succ]; omega) (by rw [T_eq] at *; omega), m₂t hi, word_writeW_self,
          hq₃]
      · have := st₃ i (by omega) (by omega)
        rw [show w + (i + 1) = w + 1 + i by omega]
        exact this
    · refine ⟨fun r hr => ?_, ?_, ?_⟩
      · simp only [List.mem_cons, not_or] at hr
        obtain ⟨hra, hrc, hrq⟩ := hr
        rw [k₃.gpr r (by
          simp only [List.mem_cons, not_or]
          exact ⟨hra, hrc, fun h => hrq (qs_sub h)⟩), g₂]
        exact hn₁ r hrc hra (fun h => hrq (h ▸ (mem_qs.mpr ⟨0, by omega, rfl⟩)))
          (fun h => hrq (h ▸ (mem_qs.mpr ⟨1, by omega, rfl⟩)))
      · rw [k₃.rd, rd₂, k₁.2.2.1]
      · rw [k₃.wr, wr₂, k₁.2.2.2]


/-! ## Row 0 -/

/-- `xor t32, t32`: `t` and both carries clear. -/
theorem xorZ_ok (s : State) (t : Reg) :
    WP isa (.block [.alu32 .xor t (.reg t)]) s fun s' =>
      s'.gpr t = 0 ∧ s'.cf = some false ∧ s'.of = some false ∧ Keeps [t] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, readSrc32,
    Option.bind_some, State.setReg32, BitVec.xor_self, RegUpd.gpr_setReg_self,
    RegUpd.cf_setReg, of_setReg, arithFlags, State.setFlags, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, (by trivial), (by trivial), fun r hr => ?_, (by trivial), (by trivial), (by trivial)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr]

/-- `mulx y, rax, src`, `adox x, rax`: `rdx · src` added at `x` through OF, its
high half into `y` (whatever it held), CF unchanged. -/
theorem mulAccO_ok (s : State) {x y : Reg} {src : Src} {v : BitVec 64} {o : Bool}
    (hsrc : readSrc s src = some v) (himm : ∀ n, src ≠ .imm n) (ho : s.of = some o)
    (hxa : x ≠ .rax) (hya : y ≠ .rax) (hxy : x ≠ y) :
    WP isa (.block [.mulx y .rax src, .adox x (.reg .rax)]) s fun s' =>
      ∃ o', s'.of = some o' ∧ s'.cf = s.cf ∧
        (s'.gpr x).toNat + 2 ^ 64 * (s'.gpr y).toNat + 2 ^ 64 * o'.toNat =
          (s.gpr x).toNat + o.toNat + (s.gpr .rdx).toNat * v.toNat ∧
        Keeps [.rax, x, y] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, exec, execMulx_eq hsrc himm, runStep_some, runBlock_nil, execAdox, readSrc,
    Option.bind_some, Option.map_some, RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne _ _ hxa,
    RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hya), RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hxy),
    RegUpd.gpr_setReg_of_ne _ _ hxy, RegUpd.gpr_setFlags, of_setReg, of_setFlags, RegUpd.cf_setReg,
    RegUpd.cf_setFlags, ho, Option.some.injEq, exists_eq_left']
  refine ⟨(by trivial), ?_, fun r hr => ?_, (by trivial), (by trivial), (by trivial)⟩
  · have e1 := adc_carry (s.gpr x) (BitVec.ofNat 64 ((s.gpr .rdx).toNat * v.toNat)) o
    have e3 := mulx_arith (s.gpr .rdx) v
    omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr.2.2, RegUpd.gpr_setReg_of_ne _ _ hr.2.1,
      RegUpd.gpr_setFlags, RegUpd.gpr_setReg_of_ne _ _ hr.1]

theorem qs_succ (w n : Nat) : qs w (n + 1) = q w :: qs (w + 1) n := by
  simp only [qs, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, Nat.succ_eq_add_one]
  congr 1
  omega

/-- `mulAccsL (qs w (n + 1)) d`: `rdx · [rbx + d … d + 8n)` added at word `w`,
whatever the words `w + 1 … w + n` held, through OF. -/
theorem mulAccs_ok : ∀ (n : Nat) {w d : Nat} {s : State} {bA : Addr} {o : Bool},
    PtrC s .rbx bA 72 0 → d + 8 * n ≤ 72 → n < 8 → s.of = some o →
    WP isa (.block (mulAccsL (qs w (n + 1)) d)) s fun s' => ∃ o', s'.of = some o' ∧ s'.cf = s.cf ∧
      qv s' w (n + 1) (n + 1) + 2 ^ (64 * n) * o'.toNat =
        (s.gpr (q w)).toNat + o.toNat + (s.gpr .rdx).toNat * wordsVal s.mem bA d n ∧
      Keeps (.rax :: qs w (n + 1)) s s'
  | 0, w, d, s, _, o, _, _, _, ho => by
    rw [qs_succ, qs, List.range_zero, List.map_nil]
    exact WP.block_nil ⟨o, ho, rfl, by simp [qv, wordsVal], fun _ _ => rfl, rfl, rfl, rfl⟩
  | n + 1, w, d, s, bA, o, hp, hd, hn, ho => by
    obtain ⟨hxa, hxc, hxd, hxi, hxb, hxz, -⟩ := q_ne w
    obtain ⟨hya, hyc, hyd, hyi, hyb, hyz, -⟩ := q_ne (w + 1)
    have hxy : q w ≠ q (w + 1) := q_ne_of (by omega)
    rw [qs_succ, qs_succ, mulAccsL, ← qs_succ, WP.block_append_iff]
    refine WP.mono (mulAccO_ok s (v := word s.mem bA d) (by exact readSrc_rcR hp (d := d) (by omega))
      (fun _ h => nomatch h) ho hxa hya hxy) fun s₁ ⟨o₁, of₁, cf₁, e₁, k₁⟩ => ?_
    have hp₁ := hp.of_keeps k₁ (by
      intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl
      · decide
      · exact mem_rowRegs_x (q_ne w).2.2.2.2.2.2
      · exact mem_rowRegs_x (q_ne (w + 1)).2.2.2.2.2.2)
    refine WP.mono (mulAccs_ok n (w := w + 1) (d := d + 8) hp₁ (by omega) (by omega) of₁)
      fun s₂ ⟨o₂, of₂, cf₂, e₂, k₂⟩ => ⟨o₂, of₂, cf₂.trans cf₁, ?_, ?_⟩
    · have hx : s₂.gpr (q w) = s₁.gpr (q w) := k₂.1 _ (by
        simp only [List.mem_cons, not_or]
        exact ⟨hxa, q_not_qs (by omega) (by omega)⟩)
      have hdx : s₁.gpr .rdx = s.gpr .rdx := k₁.1 _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨by decide, Ne.symm hxd, Ne.symm hyd⟩)
      rw [hdx, k₁.2.1] at e₂
      rw [qv, ite_eq_left (by omega), hx, show n + 1 + 1 - 1 = n + 1 by omega,
        show wordsVal s.mem bA d (n + 1) = (word s.mem bA d).toNat + 2 ^ 64 * wordsVal s.mem bA (d + 8) n from rfl]
      rw [pow64_succ n]
      rw [Nat.mul_add (s.gpr .rdx).toNat, Nat.mul_left_comm (s.gpr .rdx).toNat (2 ^ 64)]
      simp only [Nat.mul_assoc] at e₂ ⊢
      omega_arith
    · refine (k₁.mono ?_).trans (k₂.mono ?_)
      · intro t ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht ⊢
        rcases ht with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (mem_qs.mpr ⟨0, by omega, by simp⟩))
      · intro t ht
        simp only [List.mem_cons] at ht ⊢
        rcases ht with rfl | ht
        · exact Or.inl rfl
        · exact Or.inr (Or.inr ht)


/-- The temporary area's words `w … w + n - 1`. -/
def tsum (m : Mem) (base : Addr) (w : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (word m base (T w)).toNat + 2 ^ 64 * tsum m base (w + 1) n

theorem tsum_eq (m : Mem) (base : Addr) : ∀ w n, tsum m base w n = wordsVal m base (T w) n
  | _, 0 => rfl
  | w, n + 1 => by rw [tsum, wordsVal, tsum_eq m base (w + 1) n, T_succ]

/-- Expands `qv` and `tsum` over literal counts. -/
macro "qv_simp" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic| simp only [qv, tsum, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul,
  Nat.zero_lt_succ, Nat.lt_irrefl, ite_true, ite_false, Nat.mul_zero, Nat.add_zero] $[$loc]?)

/-- Bounds on the temporary area's words at literal indices. -/
macro "t_omega" : tactic => `(tactic| (simp only [T, fnTmp] <;> omega))

/-- The registers the square may change. -/
abbrev sqRegs : List Reg := [.rax, .rcx, .rdx, .r14, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r15]

theorem q_mem (w : Nat) : q w ∈ sqRegs := by
  rw [q_mod w]
  have hw := Nat.mod_lt w (show 0 < 8 by decide)
  generalize w % 8 = a at *
  revert a
  decide

theorem qs_mem {w n : Nat} {r : Reg} (h : r ∈ qs w n) : r ∈ sqRegs := by
  obtain ⟨i, -, rfl⟩ := mem_qs.mp h
  exact q_mem _

theorem rowRegs_of_sq {t : Reg} (h : t ∈ sqRegs) (h' : t ≠ .r14) : t ∈ rowRegs := by
  revert t; decide

/-- The operand's words, apart from the temporary area. -/
theorem opnd_eq {base bA : Addr} {m m' : Mem} {a k d n : Nat} (hap : Apart bA 0 72 base fnTmp 72)
    (O : Outside base (T a) k m m') (hk : T a + k ≤ 4096) (hd : d + 8 * n ≤ 72) :
    wordsVal m' bA d n = wordsVal m bA d n :=
  O.wordsVal' ((hap.sub (by omega) (by omega)).mono (T_le a) (by have : fnTmp = 4024 := rfl; omega))

theorem opnd_word {base bA : Addr} {m m' : Mem} {a k d : Nat} (hap : Apart bA 0 72 base fnTmp 72)
    (O : Outside base (T a) k m m') (hk : T a + k ≤ 4096) (hd : d + 8 ≤ 72) :
    word m' bA d = word m bA d :=
  O.word' ((hap.sub (by omega) (by omega)).mono (T_le a) (by have : fnTmp = 4024 := rfl; omega))

theorem qsRows (w n : Nat) : ∀ t ∈ .rax :: qs w n, t ∈ rowRegs := by
  intro t ht
  simp only [List.mem_cons] at ht
  rcases ht with rfl | ht
  · decide
  · obtain ⟨i, -, rfl⟩ := mem_qs.mp ht; exact mem_rowRegs_x (q_ne _).2.2.2.2.2.2

theorem qsRows' (w n : Nat) : ∀ t ∈ .rax :: .rcx :: qs w n, t ∈ rowRegs := by
  intro t ht
  simp only [List.mem_cons] at ht
  rcases ht with rfl | rfl | ht
  · decide
  · decide
  · obtain ⟨i, -, rfl⟩ := mem_qs.mp ht; exact mem_rowRegs_x (q_ne _).2.2.2.2.2.2

theorem notin_qs {t : Reg} (h : ∀ w, q w ≠ t) {w n : Nat} : t ∉ qs w n := fun hm => by
  obtain ⟨i, -, hi⟩ := mem_qs.mp hm; exact h _ hi

theorem _root_.VG.Proof.Mont.X86_64.Scr.of_keepRegs' {rs : List Reg} {s s' : State} {base : Addr} {size : Nat}
    (hs : Scr s base size) (h : KeepRegs rs s s') (hr : .rdi ∉ rs) : Scr s' base size :=
  ⟨(h.gpr _ hr).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

theorem T_le' (a b : Nat) (h : a ≤ b := by omega) : T a ≤ T b := by rw [T_eq, T_eq]; omega

theorem keepRegs_of_keeps {rs : List Reg} {s s' : State} (h : Keeps rs s s') : KeepRegs rs s s' :=
  ⟨h.1, h.2.2.1, h.2.2.2⟩

theorem mul3 (a x y z : Nat) : a * (x + 2 ^ 64 * (y + 2 ^ 64 * z)) = a * x + 2 ^ 64 * (a * y) +
    2 ^ 64 * (2 ^ 64 * (a * z)) := by
  rw [Nat.mul_add, Nat.mul_left_comm a (2 ^ 64), Nat.mul_add, Nat.mul_left_comm a (2 ^ 64) z, Nat.mul_add,
    Nat.add_assoc]

theorem sub4 : ∀ r ∈ [Reg.rdx, .r14, q 2, q 1], r ∈ sqRegs := by decide

/-- Row 0: `a_0 [a_1 … a_7]` at the words `1 … 8`, words 1 and 2 stored. -/
theorem sqRow0_ok {s : State} {base bA : Addr} (hZ : 4096 ≤ Z) (hs : Scr s base Z) (hp : PtrC s .rbx bA 72 0)
    (hap : Apart bA 0 72 base fnTmp 72) :
    WP isa (.block sqRow0) s fun s' =>
      qv s' 1 8 8 = (word s.mem bA 0).toNat * wordsVal s.mem bA 8 7 ∧
      word s'.mem base (T 1) = s'.gpr (q 1) ∧ word s'.mem base (T 2) = s'.gpr (q 2) ∧
      s'.gpr .r14 = 0 ∧ KeepRegs sqRegs s s' ∧ Outside base (T 1) 16 s.mem s'.mem := by
  have hnw := hs.nowrap
  rw [sqRow0, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  -- `xor`, `rdx = a₀`, `a₀ a₁`, word 1 stored.
  refine WP.mono (show WP isa (.block [.alu32 .xor .r14 (.reg .r14), .mov .rdx (asrc 0),
      .mulx (q 2) (q 1) (asrc 8), .store (sc (T 1)) (q 1)]) s (fun s₄ =>
      s₄.gpr .r14 = 0 ∧ s₄.cf = some false ∧ s₄.of = some false ∧ s₄.gpr .rdx = word s.mem bA 0 ∧
      (s₄.gpr (q 1)).toNat + 2 ^ 64 * (s₄.gpr (q 2)).toNat = (word s.mem bA 0).toNat * (word s.mem bA 8).toNat ∧
      s₄.mem = s.mem.writeW (off base (T 1)) (s₄.gpr (q 1)) ∧
      KeepRegs [.rdx, .r14, q 2, q 1] s s₄) by
    rw [show [Instr.alu32 .xor .r14 (.reg .r14), .mov .rdx (asrc 0), .mulx (q 2) (q 1) (asrc 8),
      .store (sc (T 1)) (q 1)] = [.alu32 .xor .r14 (.reg .r14)] ++ ([.mov .rdx (asrc 0)] ++
      ([.mulx (q 2) (q 1) (asrc 8)] ++ [.store (sc (T 1)) (q 1)])) from rfl]
    rw [WP.block_append_iff]
    refine WP.mono (xorZ_ok s .r14) fun s₁ ⟨z₁, cf₁, of₁, k₁⟩ => ?_
    have hp₁ := hp.of_keeps k₁ (by intro t ht; simp at ht; subst ht; decide)
    rw [WP.block_append_iff]
    refine WP.mono (movRdx_ok s₁ (v := word s₁.mem bA 0) (by exact readSrc_rcR hp₁ (d := 0) (by omega))) fun s₂ ⟨d₂, cf₂, of₂, k₂⟩ => ?_
    have hp₂ := hp₁.of_keeps k₂ (by intro t ht; simp at ht; subst ht; decide)
    rw [WP.block_append_iff]
    refine WP.mono (mulx_ok s₂ (v := word s₂.mem bA 8) (by exact readSrc_rcR hp₂ (d := 8) (by omega))
      (fun _ h => nomatch h) (q_ne_of (by decide))) fun s₃ ⟨e₃, cf₃, of₃, k₃⟩ => ?_
    have hs₃ : Scr s₃ base Z := ((hs.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)).of_keeps k₃ (by decide)
    refine WP.mono (storeX_ok hs₃ (q 1) (d := T 1) (by t_omega)) fun s₄ ⟨m₄, g₄, cf₄, of₄, rd₄, wr₄⟩ => ?_
    have hm : s₃.mem = s.mem := k₃.2.1.trans (k₂.2.1.trans k₁.2.1)
    refine ⟨?_, cf₄.trans (cf₃.trans (cf₂.trans cf₁)), of₄.trans (of₃.trans (of₂.trans of₁)), ?_, ?_, ?_, ?_⟩
    · rw [g₄, k₃.1 _ (by decide), k₂.1 _ (by decide)]; exact z₁
    · rw [g₄, k₃.1 _ (by decide), d₂, k₁.2.1]
    · rw [g₄, e₃, d₂, k₂.2.1, k₁.2.1]
    · rw [m₄, hm, g₄]
    · refine ⟨fun r hr => ?_, by rw [rd₄, k₃.2.2.1, k₂.2.2.1, k₁.2.2.1], by rw [wr₄, k₃.2.2.2, k₂.2.2.2, k₁.2.2.2]⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [g₄, k₃.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hr.2.2.1, hr.2.2.2⟩),
        k₂.1 r (by simpa using hr.1), k₁.1 r (by simpa using hr.2.1)]) fun s₄ ⟨z₄, cf₄, of₄, d₄, e₄, m₄, k₄⟩ => ?_
  have hs₄ : Scr s₄ base Z := ⟨by rw [k₄.gpr _ (by decide)]; exact hs.rdi, by rw [k₄.wr]; exact hs.wr, hnw⟩
  have hp₄ := hp.of_keepRegs k₄ (by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl <;> decide)
  have O₄ : Outside base (T 1) 8 s.mem s₄.mem := by rw [m₄]; exact writeW_outside _ _ _ (by t_omega)
  -- `a₀ a₂`, word 2 stored.
  rw [WP.block_append_iff]
  refine WP.mono (mulAccs_ok 1 (w := 2) (d := 16) hp₄ (by omega) (by omega) of₄)
    fun s₅ ⟨o₅, of₅, cf₅, e₅, k₅⟩ => ?_
  have hs₅ : Scr s₅ base Z := hs₄.of_keeps k₅ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (storeX_ok hs₅ (q 2) (d := T 2) (by t_omega)) fun s₆ ⟨m₆, g₆, cf₆, of₆, rd₆, wr₆⟩ => ?_
  have hs₆ : Scr s₆ base Z := ⟨by rw [g₆]; exact hs₅.rdi, by rw [wr₆]; exact hs₅.wr, hnw⟩
  have hp₆ := (hp₄.of_keeps k₅ (qsRows 2 2)).of_store g₆ rd₆ wr₆
  have O₆ : Outside base (T 2) 8 s₅.mem s₆.mem := by rw [m₆]; exact writeW_outside _ _ _ (by t_omega)
  -- `a₀ [a₃ … a₇]`, the carry into word 8.
  rw [WP.block_append_iff]
  refine WP.mono (mulAccs_ok 5 (w := 3) (d := 24) hp₆ (by omega) (by omega) (of₆.trans of₅))
    fun s₇ ⟨o₇, of₇, cf₇, e₇, k₇⟩ => ?_
  have hz₇ : s₇.gpr .r14 = 0 := by
    rw [k₇.1 _ (by decide), g₆, k₅.1 _ (by decide)]; exact z₄
  refine WP.mono (adoxS_ok s₇ (x := q 8) (src := .reg .r14) (v := 0) (by simp [readSrc, hz₇])
    (fun _ h => nomatch h) of₇) fun s₈ ⟨o₈, of₈, cf₈, e₈, k₈⟩ => ?_
  -- The memory.
  have hm₅ : s₅.mem = s₄.mem := k₅.2.1
  have hm₈ : s₈.mem = s₆.mem := k₈.2.1.trans k₇.2.1
  have hW₁₆ : wordsVal s₄.mem bA 16 1 = wordsVal s.mem bA 16 1 := opnd_eq hap O₄ (by t_omega) (by omega)
  have O₅₆ : Outside base (T 1) 16 s₄.mem s₆.mem := by
    rw [← hm₅]; exact O₆.mono (by t_omega) (by t_omega)
  have hW₂₄ : wordsVal s₆.mem bA 24 5 = wordsVal s.mem bA 24 5 := by
    rw [← opnd_eq hap O₄ (by t_omega) (by omega)]; exact opnd_eq hap O₅₆ (by t_omega) (by omega)
  -- `rdx` through the steps.
  have hdx₆ : s₆.gpr .rdx = word s.mem bA 0 := by rw [g₆, k₅.1 _ (by decide), d₄]
  have hdx₄ : s₄.gpr .rdx = word s.mem bA 0 := d₄
  -- The registers.
  have r8 : s₈.gpr (q 1) = s₄.gpr (q 1) := by rw [k₈.1 _ (by decide), k₇.1 _ (by decide), g₆, k₅.1 _ (by decide)]
  have r82 : s₈.gpr (q 2) = s₅.gpr (q 2) := by rw [k₈.1 _ (by decide), k₇.1 _ (by decide), g₆]
  have r5 : s₅.gpr (q 3) = s₆.gpr (q 3) := by rw [g₆]
  have r4 : s₄.gpr (q 2) = s₄.gpr (q 2) := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hdx₄, hW₁₆] at e₅
    rw [hdx₆, hW₂₄, ← r5] at e₇
    qv_simp at e₅ e₇ ⊢
    rw [r8, r82, k₈.1 (q 3) (by decide), k₈.1 (q 4) (by decide), k₈.1 (q 5) (by decide), k₈.1 (q 6) (by decide),
      k₈.1 (q 7) (by decide)]
    have hW : wordsVal s.mem bA 8 7 = (word s.mem bA 8).toNat + 2 ^ 64 * (wordsVal s.mem bA 16 1 +
        2 ^ 64 * wordsVal s.mem bA 24 5) := by
      have e1 : wordsVal s.mem bA 8 7 = (word s.mem bA 8).toNat + 2 ^ 64 * ((word s.mem bA 16).toNat +
        2 ^ 64 * wordsVal s.mem bA 24 5) := rfl
      have e2 : wordsVal s.mem bA 16 1 = (word s.mem bA 16).toNat := by simp [wordsVal]
      rw [e1, e2]
    have hB := Nat.mul_lt_mul'' (word s.mem bA 0).isLt (wordsVal_lt s.mem bA 8 7)
    rw [hW, mul3 (word s.mem bA 0).toNat] at hB ⊢
    have h0 : BitVec.toNat (0 : BitVec 64) = 0 := rfl
    simp only [Bool.toNat_false, Nat.add_zero] at e₅
    omega_arith
  · rw [hm₈, O₆.word (by t_omega) (by t_omega), hm₅, m₄, word_writeW_self, r8]
  · rw [hm₈, m₆, word_writeW_self, r82]
  · rw [k₈.1 _ (by decide), hz₇]
  · refine ⟨fun r hr => ?_, ?_, ?_⟩
    · have h4 : r ∉ [Reg.rdx, .r14, q 2, q 1] := fun h => hr (sub4 r h)
      have hq : ∀ w, r ≠ q w := fun w h => hr (h ▸ q_mem w)
      rw [k₈.1 r (by simpa using hq 8), k₇.1 r (by
        simp only [List.mem_cons, not_or]; exact ⟨fun h => hr (h ▸ by decide), fun h => by obtain ⟨i, -, hi⟩ := mem_qs.mp h; exact hq _ hi.symm⟩),
        g₆, k₅.1 r (by
        simp only [List.mem_cons, not_or]; exact ⟨fun h => hr (h ▸ by decide), fun h => by obtain ⟨i, -, hi⟩ := mem_qs.mp h; exact hq _ hi.symm⟩),
        k₄.gpr r h4]
    · rw [k₈.2.2.1, k₇.2.2.1, rd₆, k₅.2.2.1, k₄.rd]
    · rw [k₈.2.2.2, k₇.2.2.2, wr₆, k₅.2.2.2, k₄.wr]
  · rw [hm₈]
    exact (O₄.mono (Nat.le_refl _) (by omega)).trans O₅₆


/-! ## Rows 1 to 3 -/

theorem q_ne_win {a b : Nat} (h : a ≠ b) (h1 : a < b + 8) (h2 : b < a + 8) : q a ≠ q b :=
  q_ne_of (by omega)

/-- Row `r` of `1 … 3` (`sqRow`), as its two chains and the last carry:
what each adds, and the words each leaves alone. -/
theorem sqRow_skel {r w1 n1 w2 st : Nat} (hr1 : 1 ≤ r) (hr3 : r ≤ 3) (hw1 : w1 = 2 * r + 1) (hn1 : n1 = 7 - r)
    (hw2 : w2 = r + 8) (hst : st = min 2 (7 - 2 * r)) {s : State} {base bA : Addr} (hZ : 4096 ≤ Z) (hs : Scr s base Z)
    (hp : PtrC s .rbx bA 72 0) (hap : Apart bA 0 72 base fnTmp 72) :
    WP isa (.block (sqRow r)) s fun s₃ => ∃ (s₁ s₂ : State) (o₁ c₁ o₂ c₂ o₃ : Bool),
      qv s₁ w1 (n1 + 1) (n1 + 1) + 2 ^ (64 * n1) * o₁.toNat + 2 ^ (64 * (n1 + 1)) * c₁.toNat =
        qv s w1 (n1 + 1) 6 + (word s.mem bA (8 * r)).toNat * wordsVal s.mem bA (8 * (r + 1)) n1 ∧
      qv s₂ w2 (r + 1) (r + 1) + 2 ^ (64 * r) * o₂.toNat + 2 ^ (64 * (r + 1)) * c₂.toNat =
        qv s₁ w2 (r + 1) (max (r - 1) 1) + o₁.toNat + 2 ^ 64 * c₁.toNat +
          (word s.mem bA (8 * (r + 4))).toNat * wordsVal s.mem bA 32 r ∧
      (s₃.gpr (q (2 * r + 8))).toNat + 2 ^ 64 * o₃.toNat = (s₂.gpr (q (2 * r + 8))).toNat + o₂.toNat ∧
      qv s₃ w1 n1 n1 = qv s₁ w1 n1 n1 ∧ qv s₃ w2 r r = qv s₂ w2 r r ∧
      qv s₁ (w2 + 1) r (r - 2) = qv s (w2 + 1) r (r - 2) ∧
      (∀ i, i < st → word s₃.mem base (T (w1 + i)) = s₃.gpr (q (w1 + i))) ∧ s₃.gpr .r14 = 0 ∧
      KeepRegs sqRegs s s₃ ∧ Outside base (T w1) (8 * st) s.mem s₃.mem := by
  subst hw1 hn1 hw2 hst
  have hnw := hs.nowrap
  rw [sqRow, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.alu32 .xor .r14 (.reg .r14), .mov .rdx (asrc (8 * r))]) s (fun s₀ =>
      s₀.gpr .r14 = 0 ∧ s₀.cf = some false ∧ s₀.of = some false ∧ s₀.gpr .rdx = word s.mem bA (8 * r) ∧
      Keeps [.rdx, .r14] s s₀) by
    rw [show [Instr.alu32 .xor .r14 (.reg .r14), .mov .rdx (asrc (8 * r))] =
      [.alu32 .xor .r14 (.reg .r14)] ++ [.mov .rdx (asrc (8 * r))] from rfl, WP.block_append_iff]
    refine WP.mono (xorZ_ok s .r14) fun s₁ ⟨z₁, cf₁, of₁, k₁⟩ => ?_
    have hp₁ := hp.of_keeps k₁ (by decide)
    refine WP.mono (movRdx_ok s₁ (v := word s₁.mem bA (8 * r)) (by exact readSrc_rcR hp₁ (by omega)))
      fun s₂ ⟨d₂, cf₂, of₂, k₂⟩ => ⟨by rw [k₂.1 _ (by decide)]; exact z₁, cf₂.trans cf₁, of₂.trans of₁,
        by rw [d₂, k₁.2.1], (k₁.mono (by decide)).trans (k₂.mono (by decide))⟩) fun s₀ ⟨z₀, cf₀, of₀, d₀, k₀⟩ => ?_
  have hs₀ := hs.of_keeps k₀ (by decide)
  have hp₀ := hp.of_keeps k₀ (by decide)
  -- The first chain.
  rw [WP.block_append_iff]
  refine WP.mono (sqChain_ok (7 - r) (w := 2 * r + 1) (d := 8 * (r + 1)) (f := 6) (st := min 2 (7 - 2 * r))
    hs₀ hZ hp₀ hap (by omega) (by omega) (by omega) z₀ cf₀ of₀) fun s₁ ⟨c₁, o₁, cf₁, of₁, E1, st₁, k₁, O₁⟩ => ?_
  have hs₁ : Scr s₁ base Z := ⟨by
      rw [k₁.gpr _ (by simp only [List.mem_cons, not_or]; exact ⟨by decide, by decide, notin_qs fun w => (q_ne w).2.2.2.1⟩)]
      exact hs₀.rdi, by rw [k₁.wr]; exact hs₀.wr, hnw⟩
  have hp₁ := hp₀.of_keepRegs k₁ (qsRows' _ _)
  have hz₁ : s₁.gpr .r14 = 0 := by
    rw [k₁.gpr _ (by simp only [List.mem_cons, not_or]; exact ⟨by decide, by decide, fun h => by
      obtain ⟨i, -, hi⟩ := mem_qs.mp h; exact (q_ne _).2.2.2.2.2.1 hi⟩)]; exact z₀
  have O₁' : Outside base (T (2 * r + 1)) (8 * min 2 (7 - 2 * r)) s.mem s₁.mem := by
    rw [← k₀.2.1, show min (min 2 (7 - 2 * r)) (7 - r) = min 2 (7 - 2 * r) by omega] at *; exact O₁
  -- `rdx = a_{r+4}`, the second chain.
  rw [WP.block_append_iff]
  refine WP.mono (movRdx_ok s₁ (v := word s₁.mem bA (8 * (r + 4))) (by exact readSrc_rcR hp₁ (by omega)))
    fun sc ⟨dc, cfc, ofc, kc⟩ => ?_
  have hsc := hs₁.of_keeps kc (by decide)
  have hpc := hp₁.of_keeps kc (by decide)
  have hzc : sc.gpr .r14 = 0 := by rw [kc.1 _ (by decide)]; exact hz₁
  rw [WP.block_append_iff]
  refine WP.mono (sqChain_ok r (w := r + 8) (d := 32) (f := r - 1) (st := 0) hsc hZ hpc hap (by omega) (by omega)
    (by omega) hzc (cfc.trans cf₁) (ofc.trans of₁)) fun s₂ ⟨c₂, o₂, cf₂, of₂, E2, _, k₂, O₂⟩ => ?_
  have hz₂ : s₂.gpr .r14 = 0 := by
    rw [k₂.gpr _ (by simp only [List.mem_cons, not_or]; exact ⟨by decide, by decide, fun h => by
      obtain ⟨i, -, hi⟩ := mem_qs.mp h; exact (q_ne _).2.2.2.2.2.1 hi⟩)]; exact hzc
  -- The last carry.
  refine WP.mono (adoxS_ok s₂ (x := q (2 * r + 8)) (src := .reg .r14) (v := 0) (by simp [readSrc, hz₂])
    (fun _ h => nomatch h) of₂) fun s₃ ⟨o₃, of₃, cf₃, e₃, k₃⟩ => ?_
  -- The memory.
  have hmc : sc.mem = s₁.mem := kc.2.1
  have hm₂ : s₂.mem = s₁.mem := by
    rw [← hmc]; funext x; exact (O₂ x (by simp only [Nat.zero_min, Nat.mul_zero]; omega))
  have hm₃ : s₃.mem = s₁.mem := k₃.2.1.trans hm₂
  have hstk : min 2 (7 - 2 * r) ≤ 2 := by omega
  have hT : T (2 * r + 1) + 8 * min 2 (7 - 2 * r) ≤ 4096 := by rw [T_eq]; omega
  have hW1 : wordsVal s₀.mem bA (8 * (r + 1)) (7 - r) = wordsVal s.mem bA (8 * (r + 1)) (7 - r) := by rw [k₀.2.1]
  have hW2 : wordsVal sc.mem bA 32 r = wordsVal s.mem bA 32 r := by
    rw [hmc]; exact opnd_eq hap O₁' hT (by omega)
  have ha4 : word s₁.mem bA (8 * (r + 4)) = word s.mem bA (8 * (r + 4)) := opnd_word hap O₁' hT (by omega)
  -- The registers.
  have hq₀ : ∀ w, s₀.gpr (q w) = s.gpr (q w) := fun w => k₀.1 _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨(q_ne w).2.2.1, (q_ne w).2.2.2.2.2.1⟩)
  have hqc : ∀ w, sc.gpr (q w) = s₁.gpr (q w) := fun w => kc.1 _ (by simpa using (q_ne w).2.2.1)
  have h2 : ∀ w, (∀ j, j < r + 1 → (w % 8) ≠ ((r + 8 + j) % 8)) → s₂.gpr (q w) = sc.gpr (q w) := fun w hw =>
    k₂.gpr _ (by
      simp only [List.mem_cons, not_or]
      refine ⟨(q_ne w).1, (q_ne w).2.1, fun h => ?_⟩
      obtain ⟨j, hj, he⟩ := mem_qs.mp h
      exact q_ne_of (hw j hj) he.symm)
  have h1 : ∀ w, (∀ j, j < 7 - r + 1 → (w % 8) ≠ ((2 * r + 1 + j) % 8)) → s₁.gpr (q w) = s₀.gpr (q w) := fun w hw =>
    k₁.gpr _ (by
      simp only [List.mem_cons, not_or]
      refine ⟨(q_ne w).1, (q_ne w).2.1, fun h => ?_⟩
      obtain ⟨j, hj, he⟩ := mem_qs.mp h
      exact q_ne_of (hw j hj) he.symm)
  have h3 : ∀ w, w % 8 ≠ (2 * r + 8) % 8 → s₃.gpr (q w) = s₂.gpr (q w) := fun w hw =>
    k₃.1 _ (by simpa using q_ne_of hw)
  refine ⟨s₁, s₂, o₁, c₁, o₂, c₂, o₃, ?_, ?_, e₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hW1, d₀, qv_congr (s := s) (s' := s₀) fun i _ => hq₀ _] at E1
    rw [show max 6 1 = 6 by omega] at E1
    exact E1
  · rw [hW2, dc, ha4, qv_congr (s := s₁) (s' := sc) fun i _ => hqc _] at E2
    exact E2
  · exact qv_congr fun i hi => by
      rw [h3 _ (by omega), h2 _ (fun j hj => by omega), hqc]
  · exact qv_congr fun i hi => h3 _ (by omega)
  · exact qv_congr fun i hi => by rw [h1 _ (fun j hj => by omega), hq₀]
  · intro i hi
    rw [hm₃, h3 _ (by omega), h2 _ (fun j hj => by omega), hqc]
    exact st₁ i (by omega) (by omega)
  · rw [k₃.1 _ (by simpa using (q_ne _).2.2.2.2.2.1.symm)]; exact hz₂
  · refine ⟨fun x hx => ?_, ?_, ?_⟩
    · have hq : ∀ w, x ≠ q w := fun w h => hx (h ▸ q_mem w)
      have hnq : ∀ w n, x ∉ qs w n := fun w n h => by obtain ⟨i, -, hi⟩ := mem_qs.mp h; exact hq _ hi.symm
      have hxa : x ≠ .rax := fun h => hx (h ▸ by decide)
      have hxc : x ≠ .rcx := fun h => hx (h ▸ by decide)
      have hxd : x ≠ .rdx := fun h => hx (h ▸ by decide)
      have hxz : x ≠ .r14 := fun h => hx (h ▸ by decide)
      rw [k₃.1 x (by simpa using hq _), k₂.gpr x (by simp only [List.mem_cons, not_or]; exact ⟨hxa, hxc, hnq _ _⟩),
        kc.1 x (by simpa using hxd), k₁.gpr x (by simp only [List.mem_cons, not_or]; exact ⟨hxa, hxc, hnq _ _⟩),
        k₀.1 x (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hxd, hxz⟩)]
    · rw [k₃.2.2.1, k₂.rd, kc.2.2.1, k₁.rd, k₀.2.2.1]
    · rw [k₃.2.2.2, k₂.wr, kc.2.2.2, k₁.wr, k₀.2.2.2]
  · rw [hm₃]; exact O₁'


/-- The products of two different words, row by row: `a_r [a_{r+1} … a_7]`
and (rows 1 to 3) `a_{r+4} [a_4 … a_{r+3}]` at their words. -/
def rowP (m : Mem) (bA : Addr) : Nat → Nat
  | 0 => (word m bA 0).toNat * wordsVal m bA 8 7
  | r => (word m bA (8 * r)).toNat * wordsVal m bA (8 * (r + 1)) (7 - r) +
      2 ^ (64 * (7 - r)) * ((word m bA (8 * (r + 4))).toNat * wordsVal m bA 32 r)

theorem rowP_pos (m : Mem) (bA : Addr) {r : Nat} (hr : 1 ≤ r) : rowP m bA r =
    (word m bA (8 * r)).toNat * wordsVal m bA (8 * (r + 1)) (7 - r) +
      2 ^ (64 * (7 - r)) * ((word m bA (8 * (r + 4))).toNat * wordsVal m bA 32 r) := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  rfl

/-- Row `r` of `1 … 3`: `a_r [a_{r+1} … a_7]` at word `2r + 1` and
`a_{r+4} [a_4 … a_{r+3}]` at word `r + 8`, added to the words `2r + 1 … 2r + 6`
into the words `2r + 1 … 2r + 8`, if the sum fits; words `2r + 1` and
`2r + 2` below 8 stored. -/
theorem sqRowN_ok {r : Nat} (hr1 : 1 ≤ r) (hr3 : r ≤ 3) {s : State} {base bA : Addr} (hZ : 4096 ≤ Z) (hs : Scr s base Z)
    (hp : PtrC s .rbx bA 72 0) (hap : Apart bA 0 72 base fnTmp 72)
    (hB : qv s (2 * r + 1) 6 6 + rowP s.mem bA r < 2 ^ (64 * 8)) :
    WP isa (.block (sqRow r)) s fun s' =>
      qv s' (2 * r + 1) 8 8 = qv s (2 * r + 1) 6 6 + rowP s.mem bA r ∧
      (∀ i, i < min 2 (7 - 2 * r) → word s'.mem base (T (2 * r + 1 + i)) = s'.gpr (q (2 * r + 1 + i))) ∧
      s'.gpr .r14 = 0 ∧ KeepRegs sqRegs s s' ∧ Outside base (T (2 * r + 1)) (8 * min 2 (7 - 2 * r)) s.mem s'.mem := by
  refine WP.mono (sqRow_skel hr1 hr3 rfl rfl rfl rfl hZ hs hp hap)
    fun s₃ ⟨s₁, s₂, o₁, c₁, o₂, c₂, o₃, E1, E2, E3, F1, F2, F3, rest⟩ => ⟨?_, rest⟩
  rw [rowP_pos _ _ hr1] at hB ⊢
  rw [← Nat.add_assoc] at hB ⊢
  generalize (word s.mem bA (8 * r)).toNat * wordsVal s.mem bA (8 * (r + 1)) (7 - r) = P1 at *
  generalize (word s.mem bA (8 * (r + 4))).toNat * wordsVal s.mem bA 32 r = P2 at *
  have := Bool.toNat_le o₁; have := Bool.toNat_le c₁; have := Bool.toNat_le o₂; have := Bool.toNat_le c₂
  have := Bool.toNat_le o₃
  have hr : r = 1 ∨ r = 2 ∨ r = 3 := by omega
  rcases hr with rfl | rfl | rfl
  · rw [show max (1 - 1) 1 = 1 from rfl] at E2
    qv_simp at E1 E2 E3 F1 F2 F3 hB ⊢
    omega_arith
  · rw [show max (2 - 1) 1 = 1 from rfl] at E2
    qv_simp at E1 E2 E3 F1 F2 F3 hB ⊢
    omega_arith
  · rw [show max (3 - 1) 1 = 2 from rfl] at E2
    qv_simp at E1 E2 E3 F1 F2 F3 hB ⊢
    omega_arith


/-! ## The squares -/

/-- `mov r, src`. -/
theorem movR_ok (s : State) (r : Reg) {src : Src} {v : BitVec 64} (hsrc : readSrc s src = some v) :
    WP isa (.block [.mov r src]) s fun s' =>
      s'.gpr r = v ∧ s'.cf = s.cf ∧ s'.of = s.of ∧ Keeps [r] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, hsrc, Option.map_some,
    RegUpd.gpr_setReg_self, RegUpd.cf_setReg, of_setReg, Option.some.injEq, exists_eq_left']
  refine ⟨(by trivial), (by trivial), (by trivial), fun r' hr => ?_, (by trivial), (by trivial), (by trivial)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr]

/-- `adox x, x`, `adcx x, d`: `x = 2 x + d` with both carries. -/
theorem dblOC_ok (s : State) {x d : Reg} (hxd : x ≠ d) {c o : Bool} (hc : s.cf = some c)
    (ho : s.of = some o) :
    WP isa (.block [.adox x (.reg x), .adcx x (.reg d)]) s fun s' => ∃ c' o', s'.cf = some c' ∧
      s'.of = some o' ∧ (s'.gpr x).toNat + 2 ^ 64 * (c'.toNat + o'.toNat) =
        2 * (s.gpr x).toNat + (s.gpr d).toNat + c.toNat + o.toNat ∧ Keeps [x] s s' := by
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (adoxS_ok s (x := x) (src := .reg x) rfl (fun _ h => nomatch h) ho)
    fun s₁ ⟨o₁, of₁, cf₁, e₁, k₁⟩ => ?_
  refine WP.mono (adcxS_ok s₁ (x := x) (src := .reg d) rfl (fun _ h => nomatch h) (cf₁.trans hc))
    fun s₂ ⟨c₂, cf₂, of₂, e₂, k₂⟩ => ?_
  have hd : s₁.gpr d = s.gpr d := k₁.1 d (by simpa using Ne.symm hxd)
  refine ⟨c₂, o₁, cf₂, by rw [of₂, of₁], ?_, (k₁.trans k₂)⟩
  change (s₁.gpr x).toNat + 2 ^ 64 * o₁.toNat = (s.gpr x).toNat + (s.gpr x).toNat + o.toNat at e₁
  change (s₂.gpr x).toNat + 2 ^ 64 * c₂.toNat = (s₁.gpr x).toNat + (s₁.gpr d).toNat + c.toNat at e₂
  rw [hd] at e₂
  omega_using [e₁, e₂]

theorem sc_ok {s : State} {base : Addr} (hZ : 4096 ≤ Z) (hs : Scr s base Z) {d : Nat} (hd : d + 8 ≤ 4096) :
    readSrc s (.mem (sc d)) = some (word s.mem base d) := readSrc_sc hs (by omega)

/-- Step `k` of `1 … 3` of the squares (`sqDiagM`). -/
theorem sqDiagM_ok {s : State} {base bA : Addr} (hZ : 4096 ≤ Z) (hs : Scr s base Z) (hp : PtrC s .rbx bA 72 0) {k : Nat}
    (hk1 : 1 ≤ k) (hk3 : k ≤ 3) {c o : Bool} (hc : s.cf = some c) (ho : s.of = some o) :
    WP isa (.block (sqDiagM k)) s fun s' => ∃ c' o', s'.cf = some c' ∧ s'.of = some o' ∧
      (word s'.mem base (T (2 * k))).toNat + 2 ^ 64 * (word s'.mem base (T (2 * k + 1))).toNat +
          2 ^ 64 * 2 ^ 64 * (c'.toNat + o'.toNat) =
        2 * ((word s.mem base (T (2 * k))).toNat + 2 ^ 64 * (word s.mem base (T (2 * k + 1))).toNat) +
          (word s.mem bA (8 * k)).toNat * (word s.mem bA (8 * k)).toNat + c.toNat + o.toNat ∧
      KeepRegs [.rax, .rcx, .rdx] s s' ∧ Outside base (T (2 * k)) 16 s.mem s'.mem := by
  have hnw := hs.nowrap
  have hT : T (2 * k + 1) + 8 ≤ 4096 := by rw [T_eq]; omega
  have hT0 : T (2 * k) + 8 ≤ 4096 := by rw [T_eq]; omega
  rw [sqDiagM, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movR_ok s .rax (sc_ok hZ hs hT0)) fun s₁ ⟨r₁, cf₁, of₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hp₁ := hp.of_keeps k₁ (by decide)
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movRdx_ok s₁ (v := word s₁.mem bA (8 * k)) (by exact readSrc_rcR hp₁ (by omega)))
    fun s₂ ⟨d₂, cf₂, of₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (mulx_ok s₂ (hi := .rcx) (lo := .rdx) (src := .reg .rdx) rfl (fun _ h => nomatch h) (by decide))
    fun s₃ ⟨e₃, cf₃, of₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  rw [show [Instr.adox .rax (.reg .rax), .adcx .rax (.reg .rdx), .store (sc (T (2 * k))) .rax,
      .mov .rax (.mem (sc (T (2 * k + 1)))), .adox .rax (.reg .rax), .adcx .rax (.reg .rcx),
      .store (sc (T (2 * k + 1))) .rax] = [.adox .rax (.reg .rax), .adcx .rax (.reg .rdx)] ++
      ([.store (sc (T (2 * k))) .rax] ++ ([.mov .rax (.mem (sc (T (2 * k + 1))))] ++
      ([.adox .rax (.reg .rax), .adcx .rax (.reg .rcx)] ++ [.store (sc (T (2 * k + 1))) .rax]))) from rfl,
    WP.block_append_iff]
  refine WP.mono (dblOC_ok s₃ (x := .rax) (d := .rdx) (by decide) (cf₃.trans (cf₂.trans (cf₁.trans hc)))
    (of₃.trans (of₂.trans (of₁.trans ho)))) fun s₄ ⟨c₄, o₄, cf₄, of₄, e₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (storeX_ok hs₄ .rax (by omega)) fun s₅ ⟨m₅, g₅, cf₅, of₅, rd₅, wr₅⟩ => ?_
  have hs₅ : Scr s₅ base Z := ⟨by rw [g₅]; exact hs₄.rdi, by rw [wr₅]; exact hs₄.wr, hnw⟩
  rw [WP.block_append_iff]
  refine WP.mono (movR_ok s₅ .rax (sc_ok hZ hs₅ hT)) fun s₆ ⟨r₆, cf₆, of₆, k₆⟩ => ?_
  have hs₆ := hs₅.of_keeps k₆ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (dblOC_ok s₆ (x := .rax) (d := .rcx) (by decide) (cf₆.trans (cf₅.trans cf₄))
    (of₆.trans (of₅.trans of₄))) fun s₇ ⟨c₇, o₇, cf₇, of₇, e₇, k₇⟩ => ?_
  have hs₇ := hs₆.of_keeps k₇ (by decide)
  refine WP.mono (storeX_ok hs₇ .rax (by omega)) fun s₈ ⟨m₈, g₈, cf₈, of₈, rd₈, wr₈⟩ => ?_
  have hm₄ : s₄.mem = s.mem := k₄.2.1.trans (k₃.2.1.trans (k₂.2.1.trans k₁.2.1))
  have hm₇ : s₇.mem = s₅.mem := k₇.2.1.trans k₆.2.1
  have O₅ : Outside base (T (2 * k)) 8 s.mem s₅.mem := by rw [m₅, hm₄]; exact writeW_outside _ _ _ (by omega)
  have O₈ : Outside base (T (2 * k + 1)) 8 s₅.mem s₈.mem := by rw [m₈, hm₇]; exact writeW_outside _ _ _ (by omega)
  refine ⟨c₇, o₇, by rw [cf₈]; exact cf₇, by rw [of₈]; exact of₇, ?_, ?_, ?_⟩
  · have w0 : word s₈.mem base (T (2 * k)) = s₄.gpr .rax := by
      rw [O₈.word (by rw [T_eq, T_eq]; omega) (by omega), m₅, word_writeW_self]
    have w1 : word s₈.mem base (T (2 * k + 1)) = s₇.gpr .rax := by rw [m₈, word_writeW_self]
    have w1' : word s₅.mem base (T (2 * k + 1)) = word s.mem base (T (2 * k + 1)) :=
      O₅.word (by rw [T_eq, T_eq]; omega) (by omega)
    rw [w0, w1]
    rw [r₆, w1', show s₆.gpr .rcx = s₃.gpr .rcx by rw [k₆.1 _ (by decide), g₅, k₄.1 _ (by decide)]] at e₇
    rw [show s₃.gpr .rax = s₁.gpr .rax by rw [k₃.1 _ (by decide), k₂.1 _ (by decide)], r₁] at e₄
    rw [d₂, k₁.2.1] at e₃
    omega_using [e₃, e₄, e₇]
  · refine ⟨fun r hr => ?_, by rw [rd₈, k₇.2.2.1, k₆.2.2.1, rd₅, k₄.2.2.1, k₃.2.2.1, k₂.2.2.1, k₁.2.2.1],
      by rw [wr₈, k₇.2.2.2, k₆.2.2.2, wr₅, k₄.2.2.2, k₃.2.2.2, k₂.2.2.2, k₁.2.2.2]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g₈, k₇.1 r (by simpa using hr.1), k₆.1 r (by simpa using hr.1), g₅, k₄.1 r (by simpa using hr.1),
      k₃.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hr.2.1, hr.2.2⟩),
      k₂.1 r (by simpa using hr.2.2), k₁.1 r (by simpa using hr.1)]
  · rw [show (16 : Nat) = 8 + 8 from rfl]
    exact (O₅.mono (Nat.le_refl _) (by omega)).trans (O₈.mono (by rw [T_eq, T_eq]; omega) (by rw [T_eq, T_eq]; omega))


/-- Step `k` of `4 … 6` of the squares (`sqDiagR`). -/
theorem sqDiagR_ok {s : State} {bA : Addr} (hp : PtrC s .rbx bA 72 0) {k : Nat}
    (hk1 : 4 ≤ k) (hk3 : k ≤ 6) {c o : Bool} (hc : s.cf = some c) (ho : s.of = some o) :
    WP isa (.block (sqDiagR k)) s fun s' => ∃ c' o', s'.cf = some c' ∧ s'.of = some o' ∧
      (s'.gpr (q (2 * k))).toNat + 2 ^ 64 * (s'.gpr (q (2 * k + 1))).toNat + 2 ^ 64 * 2 ^ 64 * (c'.toNat + o'.toNat) =
        2 * ((s.gpr (q (2 * k))).toNat + 2 ^ 64 * (s.gpr (q (2 * k + 1))).toNat) +
          (word s.mem bA (8 * k)).toNat * (word s.mem bA (8 * k)).toNat + c.toNat + o.toNat ∧
      Keeps [.rcx, .rdx, q (2 * k), q (2 * k + 1)] s s' := by
  obtain ⟨hxa, hxc, hxd, -, -, -, -⟩ := q_ne (2 * k)
  obtain ⟨hya, hyc, hyd, -, -, -, -⟩ := q_ne (2 * k + 1)
  have hxy : q (2 * k) ≠ q (2 * k + 1) := q_ne_of (by omega)
  rw [sqDiagR, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movRdx_ok s (v := word s.mem bA (8 * k)) (by exact readSrc_rcR hp (by omega)))
    fun s₂ ⟨d₂, cf₂, of₂, k₂⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (mulx_ok s₂ (hi := .rcx) (lo := .rdx) (src := .reg .rdx) rfl (fun _ h => nomatch h) (by decide))
    fun s₃ ⟨e₃, cf₃, of₃, k₃⟩ => ?_
  rw [show [Instr.adox (q (2 * k)) (.reg (q (2 * k))), .adcx (q (2 * k)) (.reg .rdx),
      .adox (q (2 * k + 1)) (.reg (q (2 * k + 1))), .adcx (q (2 * k + 1)) (.reg .rcx)] =
      [.adox (q (2 * k)) (.reg (q (2 * k))), .adcx (q (2 * k)) (.reg .rdx)] ++
      [.adox (q (2 * k + 1)) (.reg (q (2 * k + 1))), .adcx (q (2 * k + 1)) (.reg .rcx)] from rfl,
    WP.block_append_iff]
  refine WP.mono (dblOC_ok s₃ (x := q (2 * k)) (d := .rdx) hxd (cf₃.trans (cf₂.trans hc))
    (of₃.trans (of₂.trans ho))) fun s₄ ⟨c₄, o₄, cf₄, of₄, e₄, k₄⟩ => ?_
  refine WP.mono (dblOC_ok s₄ (x := q (2 * k + 1)) (d := .rcx) hyc cf₄ of₄)
    fun s₇ ⟨c₇, o₇, cf₇, of₇, e₇, k₇⟩ => ⟨c₇, o₇, cf₇, of₇, ?_, ?_⟩
  · have h1 : s₇.gpr (q (2 * k)) = s₄.gpr (q (2 * k)) := k₇.1 _ (by simpa using hxy)
    have a2 : s₃.gpr (q (2 * k + 1)) = s₂.gpr (q (2 * k + 1)) :=
      k₃.1 _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hyc, hyd⟩)
    have h2 : s₄.gpr (q (2 * k + 1)) = s.gpr (q (2 * k + 1)) := by
      rw [k₄.1 _ (by simpa using hxy.symm), a2, k₂.1 _ (by simpa using hyd)]
    have h3 : s₄.gpr .rcx = s₃.gpr .rcx := k₄.1 _ (by simpa using hxc.symm)
    have a4 : s₃.gpr (q (2 * k)) = s₂.gpr (q (2 * k)) :=
      k₃.1 _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hxc, hxd⟩)
    have h4 : s₃.gpr (q (2 * k)) = s.gpr (q (2 * k)) := by rw [a4, k₂.1 _ (by simpa using hxd)]
    rw [h1]
    rw [h2, h3] at e₇
    rw [h4] at e₄
    rw [d₂] at e₃
    omega_using [e₃, e₄, e₇]
  · refine ((k₂.mono ?_).trans (k₃.mono ?_)).trans ((k₄.mono ?_).trans (k₇.mono ?_))
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr; simp
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> simp
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr; simp
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr; simp

/-- Step 0 of the squares (`sqDiag0`), after the rows: both carries cleared. -/
theorem sqDiag0_ok {s : State} {base bA : Addr} (hZ : 4096 ≤ Z) (hs : Scr s base Z) (hp : PtrC s .rbx bA 72 0) :
    WP isa (.block sqDiag0) s fun s' => ∃ c' o', s'.cf = some c' ∧ s'.of = some o' ∧
      (word s'.mem base (T 0)).toNat + 2 ^ 64 * (word s'.mem base (T 1)).toNat +
          2 ^ 64 * 2 ^ 64 * (c'.toNat + o'.toNat) =
        2 * (2 ^ 64 * (word s.mem base (T 1)).toNat) + (word s.mem bA 0).toNat * (word s.mem bA 0).toNat ∧
      s'.gpr .r14 = 0 ∧ KeepRegs [.rax, .rcx, .rdx, .r14] s s' ∧ Outside base (T 0) 16 s.mem s'.mem := by
  have hnw := hs.nowrap
  rw [sqDiag0, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (xorZ_ok s .r14) fun s₀ ⟨z₀, cf₀, of₀, k₀⟩ => ?_
  have hs₀ := hs.of_keeps k₀ (by decide)
  have hp₀ := hp.of_keeps k₀ (by decide)
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movRdx_ok s₀ (v := word s₀.mem bA 0) (by exact readSrc_rcR hp₀ (by omega)))
    fun s₂ ⟨d₂, cf₂, of₂, k₂⟩ => ?_
  have hs₂ := hs₀.of_keeps k₂ (by decide)
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (mulx_ok s₂ (hi := .rcx) (lo := .rax) (src := .reg .rdx) rfl (fun _ h => nomatch h) (by decide))
    fun s₃ ⟨e₃, cf₃, of₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (storeX_ok hs₃ .rax (d := T 0) (by t_omega)) fun s₅ ⟨m₅, g₅, cf₅, of₅, rd₅, wr₅⟩ => ?_
  have hs₅ : Scr s₅ base Z := ⟨by rw [g₅]; exact hs₃.rdi, by rw [wr₅]; exact hs₃.wr, hnw⟩
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movR_ok s₅ .rax (sc_ok hZ hs₅ (d := T 1) (by t_omega))) fun s₆ ⟨r₆, cf₆, of₆, k₆⟩ => ?_
  have hs₆ := hs₅.of_keeps k₆ (by decide)
  rw [show [Instr.adox .rax (.reg .rax), .adcx .rax (.reg .rcx), .store (sc (T 1)) .rax] =
      [.adox .rax (.reg .rax), .adcx .rax (.reg .rcx)] ++ [.store (sc (T 1)) .rax] from rfl, WP.block_append_iff]
  refine WP.mono (dblOC_ok s₆ (x := .rax) (d := .rcx) (by decide) (cf₆.trans (cf₅.trans (cf₃.trans (cf₂.trans cf₀))))
    (of₆.trans (of₅.trans (of₃.trans (of₂.trans of₀))))) fun s₇ ⟨c₇, o₇, cf₇, of₇, e₇, k₇⟩ => ?_
  have hs₇ := hs₆.of_keeps k₇ (by decide)
  refine WP.mono (storeX_ok hs₇ .rax (d := T 1) (by t_omega)) fun s₈ ⟨m₈, g₈, cf₈, of₈, rd₈, wr₈⟩ => ?_
  have hm₃ : s₃.mem = s.mem := k₃.2.1.trans (k₂.2.1.trans k₀.2.1)
  have hm₇ : s₇.mem = s₅.mem := k₇.2.1.trans k₆.2.1
  have O₅ : Outside base (T 0) 8 s.mem s₅.mem := by rw [m₅, hm₃]; exact writeW_outside _ _ _ (by t_omega)
  have O₈ : Outside base (T 1) 8 s₅.mem s₈.mem := by rw [m₈, hm₇]; exact writeW_outside _ _ _ (by t_omega)
  refine ⟨c₇, o₇, by rw [cf₈]; exact cf₇, by rw [of₈]; exact of₇, ?_, ?_, ?_, ?_⟩
  · have w0 : word s₈.mem base (T 0) = s₃.gpr .rax := by
      rw [O₈.word (by t_omega) (by t_omega), m₅, word_writeW_self]
    have w1 : word s₈.mem base (T 1) = s₇.gpr .rax := by rw [m₈, word_writeW_self]
    have w1' : word s₅.mem base (T 1) = word s.mem base (T 1) := O₅.word (by t_omega) (by t_omega)
    rw [w0, w1]
    rw [r₆, w1', show s₆.gpr .rcx = s₃.gpr .rcx by rw [k₆.1 _ (by decide), g₅]] at e₇
    rw [d₂, k₀.2.1] at e₃
    simp only [Bool.toNat_false, Nat.add_zero] at e₇
    omega_using [e₃, e₇]
  · rw [g₈, k₇.1 _ (by decide), k₆.1 _ (by decide), g₅, k₃.1 _ (by decide), k₂.1 _ (by decide)]; exact z₀
  · refine ⟨fun r hr => ?_, by rw [rd₈, k₇.2.2.1, k₆.2.2.1, rd₅, k₃.2.2.1, k₂.2.2.1, k₀.2.2.1],
      by rw [wr₈, k₇.2.2.2, k₆.2.2.2, wr₅, k₃.2.2.2, k₂.2.2.2, k₀.2.2.2]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g₈, k₇.1 r (by simpa using hr.1), k₆.1 r (by simpa using hr.1), g₅,
      k₃.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hr.2.1, hr.1⟩),
      k₂.1 r (by simpa using hr.2.2.1), k₀.1 r (by simpa using hr.2.2.2)]
  · rw [show (16 : Nat) = 8 + 8 from rfl]
    exact (O₅.mono (Nat.le_refl _) (by omega)).trans (O₈.mono (by t_omega) (by t_omega))

/-- Step 7 of the squares (`sqDiag7`), `r14` zero. -/
theorem sqDiag7_ok {s : State} {bA : Addr} (hp : PtrC s .rbx bA 72 0) (hz : s.gpr .r14 = 0) {c o : Bool}
    (hc : s.cf = some c) (ho : s.of = some o) :
    WP isa (.block sqDiag7) s fun s' => ∃ c' o', s'.cf = some c' ∧ s'.of = some o' ∧
      (s'.gpr (q 14)).toNat + 2 ^ 64 * (s'.gpr (q 15)).toNat + 2 ^ 64 * 2 ^ 64 * (c'.toNat + o'.toNat) =
        2 * (s.gpr (q 14)).toNat + (word s.mem bA 56).toNat * (word s.mem bA 56).toNat + c.toNat + o.toNat ∧
      Keeps [.rdx, q 15, q 14] s s' := by
  rw [sqDiag7, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movRdx_ok s (v := word s.mem bA 56) (by exact readSrc_rcR hp (by omega)))
    fun s₂ ⟨d₂, cf₂, of₂, k₂⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (mulx_ok s₂ (hi := q 15) (lo := .rdx) (src := .reg .rdx) rfl (fun _ h => nomatch h) (by decide))
    fun s₃ ⟨e₃, cf₃, of₃, k₃⟩ => ?_
  rw [show [Instr.adox (q 14) (.reg (q 14)), .adcx (q 14) (.reg .rdx), .adcx (q 15) (.reg .r14),
      .adox (q 15) (.reg .r14)] = [.adox (q 14) (.reg (q 14)), .adcx (q 14) (.reg .rdx)] ++
      ([.adcx (q 15) (.reg .r14)] ++ [.adox (q 15) (.reg .r14)]) from rfl, WP.block_append_iff]
  refine WP.mono (dblOC_ok s₃ (x := q 14) (d := .rdx) (by decide) (cf₃.trans (cf₂.trans hc))
    (of₃.trans (of₂.trans ho))) fun s₄ ⟨c₄, o₄, cf₄, of₄, e₄, k₄⟩ => ?_
  have hz₄ : s₄.gpr .r14 = 0 := by rw [k₄.1 _ (by decide), k₃.1 _ (by decide), k₂.1 _ (by decide)]; exact hz
  rw [WP.block_append_iff]
  refine WP.mono (adcxS_ok s₄ (x := q 15) (src := .reg .r14) (v := 0) (by simp [readSrc, hz₄])
    (fun _ h => nomatch h) cf₄) fun s₅ ⟨c₅, cf₅, of₅, e₅, k₅⟩ => ?_
  have hz₅ : s₅.gpr .r14 = 0 := by rw [k₅.1 _ (by decide)]; exact hz₄
  refine WP.mono (adoxS_ok s₅ (x := q 15) (src := .reg .r14) (v := 0) (by simp [readSrc, hz₅])
    (fun _ h => nomatch h) (of₅.trans of₄)) fun s₆ ⟨o₆, of₆, cf₆, e₆, k₆⟩ => ⟨c₅, o₆, by rw [cf₆, cf₅], of₆, ?_, ?_⟩
  · rw [show s₆.gpr (q 14) = s₄.gpr (q 14) by rw [k₆.1 _ (by decide), k₅.1 _ (by decide)]]
    rw [show s₄.gpr (q 15) = s₃.gpr (q 15) from k₄.1 _ (by decide)] at e₅
    rw [show s₃.gpr (q 14) = s.gpr (q 14) by rw [k₃.1 _ (by decide), k₂.1 _ (by decide)]] at e₄
    rw [d₂] at e₃
    have h0 : BitVec.toNat (0 : BitVec 64) = 0 := rfl
    omega_using [e₃, e₄, e₅, e₆, h0]
  · refine ((k₂.mono ?_).trans (k₃.mono ?_)).trans ((k₄.mono ?_).trans ((k₅.mono ?_).trans (k₆.mono ?_))) <;> decide


/-! ## The top word's row -/

/-- `maddM x y src`: `rdx · src` added at `x` (CF) and `y` (OF). -/
theorem maddM_ok (s : State) {x y : Reg} {src : Src} {v : BitVec 64} {c o : Bool}
    (hsrc : readSrc s src = some v) (himm : ∀ n, src ≠ .imm n) (hc : s.cf = some c)
    (ho : s.of = some o) (hxh : x ≠ .rcx) (hxl : x ≠ .rax) (hyh : y ≠ .rcx) (hyl : y ≠ .rax)
    (hxy : x ≠ y) :
    WP isa (.block (maddM x y src)) s fun s' =>
      ∃ c' o', s'.cf = some c' ∧ s'.of = some o' ∧
        (s'.gpr x).toNat + 2 ^ 64 * (s'.gpr y).toNat + 2 ^ 64 * c'.toNat + 2 ^ 128 * o'.toNat =
          (s.gpr x).toNat + 2 ^ 64 * (s.gpr y).toNat + c.toNat + 2 ^ 64 * o.toNat +
            (s.gpr .rdx).toNat * v.toNat ∧
        Keeps [.rcx, .rax, x, y] s s' := by
  apply WP.of_runBlock
  simp only [maddM, runBlock_cons, exec, execMulx_eq hsrc himm, runStep_some]
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAdox, execAdcx, readSrc,
    Option.bind_some, Option.map_some, RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne _ _ hxh,
    RegUpd.gpr_setReg_of_ne _ _ hxl, RegUpd.gpr_setReg_of_ne _ _ (by decide : Reg.rax ≠ .rcx),
    RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hxh),
    RegUpd.gpr_setReg_of_ne _ _ hyh, RegUpd.gpr_setReg_of_ne _ _ hyl,
    RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hxy), RegUpd.gpr_setFlags, of_setReg, of_setFlags,
    RegUpd.cf_setReg, RegUpd.cf_setFlags, ho, hc, Option.some.injEq, exists_eq_left']
  refine ⟨_, _, (by trivial), (by trivial), ?_, fun r hr => ?_, (by trivial), (by trivial), (by trivial)⟩
  · simp only [RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne _ _ hxy, RegUpd.gpr_setFlags]
    have e1 := adc_carry (s.gpr x) (BitVec.ofNat 64 ((s.gpr .rdx).toNat * v.toNat)) c
    have e2 := adc_carry (s.gpr y) (BitVec.ofNat 64 ((s.gpr .rdx).toNat * v.toNat / 2 ^ 64)) o
    have e3 := mulx_arith (s.gpr .rdx) v
    omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr.2.2.2, RegUpd.gpr_setReg_of_ne _ _ hr.2.2.1,
      RegUpd.gpr_setFlags, RegUpd.gpr_setReg_of_ne _ _ hr.1, RegUpd.gpr_setReg_of_ne _ _ hr.2.1]

/-- `maddStepsC_ok` by `maddM` (`maddStepsM`): `k` products along `ts`, the
carries CF into `ts₀` and OF into `ts₁` in, and CF (into `ts_k`) and OF (into
`ts_{k+1}`) out. -/
theorem maddStepsM_ok {size : Nat} : ∀ (k : Nat) (ts : List Reg) {s : State} {base : Addr}
    {d : Nat} {c o : Bool}, PtrC s .rbx base size 0 → (∀ t ∈ ts, t ∈ xRegs) → d + 8 * k ≤ size →
    k + 1 ≤ ts.length → FreshX ts → s.cf = some c → s.of = some o →
    WP isa (.block (maddStepsM k ts d)) s fun s' => ∃ c' o', s'.cf = some c' ∧ s'.of = some o' ∧
      regsVal s' (ts.take (k + 1)) + 2 ^ (64 * k) * c'.toNat + 2 ^ (64 * (k + 1)) * o'.toNat =
        regsVal s (ts.take (k + 1)) + c.toNat + 2 ^ 64 * o.toNat +
          (s.gpr .rdx).toNat * wordsVal s.mem base d k ∧
      Keeps (.rcx :: .rax :: ts.take (k + 1)) s s'
  | 0, ts, s, _, _, c, o, _, _, _, _, _, hc, ho => by
    show WP isa (.block []) s _
    exact WP.block_nil ⟨c, o, hc, ho, by simp [wordsVal], fun _ _ => rfl, rfl, rfl, rfl⟩
  | _ + 1, [], _, _, _, _, _, _, _, _, hl, _, _, _ => absurd hl (by simp)
  | _ + 1, [_], _, _, _, _, _, _, _, _, hl, _, _, _ => absurd hl (by simp)
  | k + 1, x :: y :: rest, s, base, d, c, o, hs, hts, hd, hl, hf, hc, ho => by
    obtain ⟨hxn, hxa, hxc, hxd, -⟩ := hf.head
    obtain ⟨hyn, hya, hyc, hyd, -⟩ := hf.tail.head
    have hxy : x ≠ y := fun h => hxn (h ▸ List.mem_cons_self ..)
    simp only [List.length_cons] at hl
    rw [maddStepsM, WP.block_append_iff]
    refine WP.mono (maddM_ok s (v := word s.mem base d) (by exact readSrc_rcR hs (d := d) (by omega_arith))
      (fun _ h => nomatch h) hc ho
      hxc hxa hyc hya hxy) fun s₁ ⟨c₁, o₁, cf₁, of₁, e₁, k₁⟩ => ?_
    have hx := mem_rowRegs_x (hts x (List.mem_cons_self ..))
    have hy := mem_rowRegs_x (hts y (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    have hs₁ := hs.of_keeps k₁ (by
      intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl <;> first | decide | exact hx | exact hy)
    refine WP.mono (maddStepsM_ok k (y :: rest) hs₁ (fun t ht => hts t (List.mem_cons_of_mem _ ht))
      (d := d + 8) (by omega_arith)
      (by simp only [List.length_cons]; omega_arith) hf.tail cf₁ of₁) fun s₂ ⟨c', o', cf₂, of₂, e₂, k₂⟩ =>
      ⟨c', o', cf₂, of₂, ?_, ?_⟩
    · have hdx : s₁.gpr .rdx = s.gpr .rdx := k₁.1 .rdx (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨by decide, by decide, Ne.symm hxd, Ne.symm hyd⟩)
      have hx₂ : s₂.gpr x = s₁.gpr x := k₂.1 x (by
        simp only [List.mem_cons, not_or]
        exact ⟨hxc, hxa, fun h => hxn (List.mem_of_mem_take h)⟩)
      have hR : regsVal s₁ (rest.take k) = regsVal s (rest.take k) := regsVal_congr fun q hq => k₁.1 q (by
        have hq' := List.mem_of_mem_take hq
        have := hf.2 q (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq'))
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨this.2.1, this.1, fun h => hxn (h ▸ List.mem_cons_of_mem _ hq'),
          fun h => hyn (h ▸ hq')⟩)
      rw [k₁.2.1, hdx] at e₂
      simp only [List.take_succ_cons, regsVal, hR] at e₂ ⊢
      simp only [wordsVal]
      rw [hx₂]
      rw [pow64_succ (k + 1), pow64_succ k] at *
      simp only [Nat.mul_assoc] at e₂ ⊢
      rw [Nat.mul_add (s.gpr .rdx).toNat, Nat.mul_left_comm (s.gpr .rdx).toNat (2 ^ 64)]
      omega_arith
    · simp only [List.take_succ_cons] at k₂ ⊢
      exact (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))

/-- `imul`'s result: the low word of the product. -/
theorem imul_toNat' (a b : BitVec 64) :
    (BitVec.ofInt 64 (a.toInt * b.toInt)).toNat = a.toNat * b.toNat % 2 ^ 64 := by
  have h : BitVec.ofInt 64 (a.toInt * b.toInt) = a * b := by
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_ofInt, BitVec.toInt_mul]
  rw [h, BitVec.toNat_mul]

/-- `imul r, r`: `r²` modulo `2⁶⁴`. -/
theorem imulSq_ok (s : State) (r : Reg) :
    WP isa (.block [.imul r r]) s fun s' =>
      (s'.gpr r).toNat = (s.gpr r).toNat * (s.gpr r).toNat % 2 ^ 64 ∧ Keeps [r] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execImul, RegUpd.gpr_setReg_self,
    Option.some.injEq, exists_eq_left']
  refine ⟨imul_toNat' _ _, fun r' hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_setFlags]

/-- `add r, r` for `r < 2⁶²`: `2 r`, both carries clear. -/
theorem addSelf_ok (s : State) (r : Reg) (h : (s.gpr r).toNat < 2 ^ 62) :
    WP isa (.block [.alu .add r (.reg r)]) s fun s' =>
      (s'.gpr r).toNat = 2 * (s.gpr r).toNat ∧ s'.cf = some false ∧ s'.of = some false ∧ Keeps [r] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    RegUpd.gpr_setReg_self, RegUpd.cf_setReg, of_setReg, RegUpd.cf_arithFlags, Option.some.injEq,
    exists_eq_left']
  generalize s.gpr r = w at *
  have hm : w.msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [decide_eq_false_iff_not, Nat.not_le]; omega
  refine ⟨?_, ?_, ?_, fun r' hr => ?_, rfl, rfl, rfl⟩
  · rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]; omega
  · simp only [decide_eq_false_iff_not, Nat.not_le]; omega
  · simp only [arithFlags, State.setFlags, addOverflow, hm]
    have : (w + w).msb = false := by
      rw [BitVec.msb_eq_decide, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
      simp only [decide_eq_false_iff_not, Nat.not_le]; omega
    simp [this]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]


/-! ## The squares, all eight steps -/

/-- One more step of the squares, at weight `Q`. -/
theorem diag_acc {H H0 D Q A0 A1 B0 B1 sq c o c' : Nat}
    (inv : H + Q * (c + o) = 2 * H0 + D)
    (e : B0 + 2 ^ 64 * B1 + 2 ^ 64 * 2 ^ 64 * c' = 2 * (A0 + 2 ^ 64 * A1) + sq + c + o) :
    H + Q * (B0 + 2 ^ 64 * B1) + Q * 2 ^ 64 * 2 ^ 64 * c' = 2 * (H0 + Q * (A0 + 2 ^ 64 * A1)) + (D + Q * sq) := by
  have e' : Q * (B0 + 2 ^ 64 * B1 + 2 ^ 64 * 2 ^ 64 * c') = Q * (2 * (A0 + 2 ^ 64 * A1) + sq + c + o) := by rw [e]
  grind

/-- The squares `Σ_{k<n} 2^(128 k) f_k²`. -/
def dg (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => dg f k + (2 ^ 64) ^ (2 * k) * (f k * f k)

/-- Expands `dg` over literal counts. -/
macro "dg_simp" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic| simp only [dg, Nat.reduceMul,
  Nat.reduceAdd, Nat.zero_add, Nat.add_zero, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.mul_one] $[$loc]?)


/-- `sqDiag`: twice the products (words `1 … 7` in the temporary area and
`8 … 14` in their registers) plus the squares, into words `0 … 15`, if that
fits in sixteen words. -/
theorem sqDiag_ok {s : State} {base bA : Addr} (hZ : 4096 ≤ Z) (hs : Scr s base Z) (hp : PtrC s .rbx bA 72 0)
    (hap : Apart bA 0 72 base fnTmp 72)
    (hB : 2 * (2 ^ 64 * tsum s.mem base 1 7 + 2 ^ 512 * qv s 8 7 7) +
      dg (fun j => (word s.mem bA (8 * j)).toNat) 8 < 2 ^ 1024) :
    WP isa (.block sqDiag) s fun s' =>
      tsum s'.mem base 0 8 + 2 ^ 512 * qv s' 8 8 8 =
        2 * (2 ^ 64 * tsum s.mem base 1 7 + 2 ^ 512 * qv s 8 7 7) + dg (fun j => (word s.mem bA (8 * j)).toNat) 8 ∧
      KeepRegs sqRegs s s' ∧ Outside base (T 0) 64 s.mem s'.mem := by
  have hnw := hs.nowrap
  rw [sqDiag]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (sqDiag0_ok hZ hs hp) fun s₀ ⟨c₀, o₀, cf₀, of₀, e₀, z₀, k₀, O₀⟩ => ?_
  have hs₀ : Scr s₀ base Z := hs.of_keepRegs' k₀ (by decide)
  have hp₀ := hp.of_keepRegs k₀ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sqDiagM_ok hZ hs₀ hp₀ (k := 1) (by omega) (by omega) cf₀ of₀)
    fun s₁ ⟨c₁, o₁, cf₁, of₁, e₁, k₁, O₁⟩ => ?_
  have hs₁ : Scr s₁ base Z := hs₀.of_keepRegs' k₁ (by decide)
  have hp₁ := hp₀.of_keepRegs k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sqDiagM_ok hZ hs₁ hp₁ (k := 2) (by omega) (by omega) cf₁ of₁)
    fun s₂ ⟨c₂, o₂, cf₂, of₂, e₂, k₂, O₂⟩ => ?_
  have hs₂ : Scr s₂ base Z := hs₁.of_keepRegs' k₂ (by decide)
  have hp₂ := hp₁.of_keepRegs k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sqDiagM_ok hZ hs₂ hp₂ (k := 3) (by omega) (by omega) cf₂ of₂)
    fun s₃ ⟨c₃, o₃, cf₃, of₃, e₃, k₃, O₃⟩ => ?_
  have hp₃ := hp₂.of_keepRegs k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sqDiagR_ok hp₃ (k := 4) (by omega) (by omega) cf₃ of₃)
    fun s₄ ⟨c₄, o₄, cf₄, of₄, e₄, k₄⟩ => ?_
  have hp₄ := hp₃.of_keeps k₄ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sqDiagR_ok hp₄ (k := 5) (by omega) (by omega) cf₄ of₄)
    fun s₅ ⟨c₅, o₅, cf₅, of₅, e₅, k₅⟩ => ?_
  have hp₅ := hp₄.of_keeps k₅ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sqDiagR_ok hp₅ (k := 6) (by omega) (by omega) cf₅ of₅)
    fun s₆ ⟨c₆, o₆, cf₆, of₆, e₆, k₆⟩ => ?_
  have hp₆ := hp₅.of_keeps k₆ (by decide)
  have hz₆ : s₆.gpr .r14 = 0 := by
    rw [k₆.1 _ (by decide), k₅.1 _ (by decide), k₄.1 _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide),
      k₁.gpr _ (by decide)]; exact z₀
  refine WP.mono (sqDiag7_ok hp₆ hz₆ cf₆ of₆) fun s₇ ⟨c₇, o₇, cf₇, of₇, e₇, k₇⟩ => ?_
  -- The memory.
  have hm₇ : s₇.mem = s₃.mem := k₇.2.1.trans (k₆.2.1.trans (k₅.2.1.trans k₄.2.1))
  have O01 : Outside base (T 0) 72 s.mem s₁.mem :=
    (O₀.mono (T_le' 0 0) (by t_omega)).trans (O₁.mono (T_le' 0 2) (by t_omega))
  have O02 : Outside base (T 0) 72 s.mem s₂.mem := O01.trans (O₂.mono (T_le' 0 4) (by t_omega))
  have O03 : Outside base (T 0) 72 s.mem s₃.mem := O02.trans (O₃.mono (T_le' 0 6) (by t_omega))
  have hA : ∀ j, j < 9 → word s₃.mem bA (8 * j) = word s.mem bA (8 * j) := fun j hj =>
    opnd_word hap O03 (by t_omega) (by omega)
  have hA₀ : ∀ j, j < 9 → word s₀.mem bA (8 * j) = word s.mem bA (8 * j) := fun j hj =>
    opnd_word hap O₀ (by t_omega) (by omega)
  have hA₁ : ∀ j, j < 9 → word s₁.mem bA (8 * j) = word s.mem bA (8 * j) := fun j hj =>
    opnd_word hap O01 (by t_omega) (by omega)
  have hA₂ : ∀ j, j < 9 → word s₂.mem bA (8 * j) = word s.mem bA (8 * j) := fun j hj =>
    opnd_word hap O02 (by t_omega) (by omega)
  -- The temporary area's words.
  have t1 : word s₀.mem base (T 2) = word s.mem base (T 2) ∧ word s₀.mem base (T 3) = word s.mem base (T 3) :=
    ⟨O₀.word (by t_omega) (by t_omega), O₀.word (by t_omega) (by t_omega)⟩
  have t2 : word s₁.mem base (T 4) = word s.mem base (T 4) ∧ word s₁.mem base (T 5) = word s.mem base (T 5) :=
    ⟨by rw [O₁.word (by t_omega) (by t_omega), O₀.word (by t_omega) (by t_omega)],
     by rw [O₁.word (by t_omega) (by t_omega), O₀.word (by t_omega) (by t_omega)]⟩
  have t3 : word s₂.mem base (T 6) = word s.mem base (T 6) ∧ word s₂.mem base (T 7) = word s.mem base (T 7) :=
    ⟨by rw [O₂.word (by t_omega) (by t_omega), O₁.word (by t_omega) (by t_omega), O₀.word (by t_omega) (by t_omega)],
     by rw [O₂.word (by t_omega) (by t_omega), O₁.word (by t_omega) (by t_omega), O₀.word (by t_omega) (by t_omega)]⟩
  have f0 : word s₇.mem base (T 0) = word s₀.mem base (T 0) ∧ word s₇.mem base (T 1) = word s₀.mem base (T 1) := by
    rw [hm₇]
    exact ⟨by rw [O₃.word (by t_omega) (by t_omega), O₂.word (by t_omega) (by t_omega), O₁.word (by t_omega) (by t_omega)],
      by rw [O₃.word (by t_omega) (by t_omega), O₂.word (by t_omega) (by t_omega), O₁.word (by t_omega) (by t_omega)]⟩
  have f1 : word s₇.mem base (T 2) = word s₁.mem base (T 2) ∧ word s₇.mem base (T 3) = word s₁.mem base (T 3) := by
    rw [hm₇]
    exact ⟨by rw [O₃.word (by t_omega) (by t_omega), O₂.word (by t_omega) (by t_omega)],
      by rw [O₃.word (by t_omega) (by t_omega), O₂.word (by t_omega) (by t_omega)]⟩
  have f2 : word s₇.mem base (T 4) = word s₂.mem base (T 4) ∧ word s₇.mem base (T 5) = word s₂.mem base (T 5) := by
    rw [hm₇]
    exact ⟨O₃.word (by t_omega) (by t_omega), O₃.word (by t_omega) (by t_omega)⟩
  have f3 : word s₇.mem base (T 6) = word s₃.mem base (T 6) ∧ word s₇.mem base (T 7) = word s₃.mem base (T 7) := by
    rw [hm₇]; exact ⟨rfl, rfl⟩
  -- The registers.
  have r3 : ∀ w, s₃.gpr (q w) = s.gpr (q w) := fun w => by
    have h : q w ∉ [Reg.rax, .rcx, .rdx] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨(q_ne w).1, (q_ne w).2.1, (q_ne w).2.2.1⟩
    rw [k₃.gpr _ h, k₂.gpr _ h, k₁.gpr _ h, k₀.gpr _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨(q_ne w).1, (q_ne w).2.1, (q_ne w).2.2.1, (q_ne w).2.2.2.2.2.1⟩)]
  refine ⟨?_, ?_, ?_⟩
  · rw [hA₀ 1 (by omega)] at e₁
    rw [hA₁ 2 (by omega)] at e₂
    rw [hA₂ 3 (by omega)] at e₃
    rw [hA 4 (by omega)] at e₄
    rw [k₄.2.1, hA 5 (by omega)] at e₅
    rw [k₅.2.1, k₄.2.1, hA 6 (by omega)] at e₆
    rw [k₆.2.1, k₅.2.1, k₄.2.1, hA 7 (by omega)] at e₇
    rw [t1.1, t1.2] at e₁
    rw [t2.1, t2.2] at e₂
    rw [t3.1, t3.2] at e₃
    rw [r3, r3] at e₄
    rw [k₄.1 (q 10) (by decide), k₄.1 (q 11) (by decide), r3, r3] at e₅
    rw [k₅.1 (q 12) (by decide), k₅.1 (q 13) (by decide), k₄.1 (q 12) (by decide), k₄.1 (q 13) (by decide), r3,
      r3] at e₆
    rw [k₆.1 (q 14) (by decide), k₅.1 (q 14) (by decide), k₄.1 (q 14) (by decide), r3] at e₇
    qv_simp
    rw [f0.1, f0.2, f1.1, f1.2, f2.1, f2.2, f3.1, f3.2]
    rw [k₇.1 (q 8) (by decide), k₆.1 (q 8) (by decide), k₅.1 (q 8) (by decide),
      k₇.1 (q 9) (by decide), k₆.1 (q 9) (by decide), k₅.1 (q 9) (by decide),
      k₇.1 (q 10) (by decide), k₆.1 (q 10) (by decide), k₇.1 (q 11) (by decide), k₆.1 (q 11) (by decide),
      k₇.1 (q 12) (by decide), k₇.1 (q 13) (by decide)]
    have a1 := diag_acc (Q := 2 ^ 64 * 2 ^ 64) (by simpa using e₀) e₁
    have a2 := diag_acc a1 e₂
    have a3 := diag_acc a2 e₃
    have a4 := diag_acc a3 e₄
    have a5 := diag_acc a4 e₅
    have a6 := diag_acc a5 e₆
    have e₇' : (s₇.gpr (q 14)).toNat + 2 ^ 64 * (s₇.gpr (q 15)).toNat + 2 ^ 64 * 2 ^ 64 * (c₇.toNat + o₇.toNat) =
        2 * ((s.gpr (q 14)).toNat + 2 ^ 64 * 0) + (word s.mem bA (8 * 7)).toNat * (word s.mem bA (8 * 7)).toNat +
          c₆.toNat + o₆.toNat := by rw [Nat.mul_zero, Nat.add_zero]; exact e₇
    have a7 := diag_acc a6 e₇'
    qv_simp at hB
    dg_simp at hB a7 ⊢
    have := Bool.toNat_le c₇; have := Bool.toNat_le o₇
    omega_using [a7, hB]
  · refine ⟨fun r hr => ?_, ?_, ?_⟩
    · have hq : ∀ w, r ≠ q w := fun w h => hr (h ▸ q_mem w)
      have hra : r ≠ .rax := fun h => hr (h ▸ by decide)
      have hrc : r ≠ .rcx := fun h => hr (h ▸ by decide)
      have hrd : r ≠ .rdx := fun h => hr (h ▸ by decide)
      have hrz : r ≠ .r14 := fun h => hr (h ▸ by decide)
      have l3 : r ∉ [Reg.rax, .rcx, .rdx] := by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hra, hrc, hrd⟩
      have lR : ∀ k, r ∉ [Reg.rcx, .rdx, q (2 * k), q (2 * k + 1)] := fun k => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hrc, hrd, hq _, hq _⟩
      rw [k₇.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hrd, hq _, hq _⟩),
        k₆.1 r (lR 6), k₅.1 r (lR 5), k₄.1 r (lR 4), k₃.gpr r l3, k₂.gpr r l3, k₁.gpr r l3, k₀.gpr r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hra, hrc, hrd, hrz⟩)]
    · rw [k₇.2.2.1, k₆.2.2.1, k₅.2.2.1, k₄.2.2.1, k₃.rd, k₂.rd, k₁.rd, k₀.rd]
    · rw [k₇.2.2.2, k₆.2.2.2, k₅.2.2.2, k₄.2.2.2, k₃.wr, k₂.wr, k₁.wr, k₀.wr]
  · rw [hm₇]
    exact ((O₀.mono (T_le' 0 0) (by t_omega)).trans (O₁.mono (T_le' 0 2) (by t_omega))).trans
      ((O₂.mono (T_le' 0 4) (by t_omega)).trans (O₃.mono (T_le' 0 6) (by t_omega)))


theorem q_lit : q 8 = .r15 ∧ q 9 = .rbp ∧ q 10 = .r8 ∧ q 11 = .r9 ∧ q 12 = .r10 ∧ q 13 = .r11 ∧ q 14 = .r12 ∧
    q 15 = .r13 := by decide

theorem xWin8 : xWin 8 = [.r15, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14] := by decide

/-- `sqTop`: `a_8²` at word 16 and `2 a_8 [a_0 … a_7]` at word 8, added to the
words `8 … 15`, into `xWin 8` (words `8 … 16`), for `a_8 < 2⁹`, if that fits
in nine words. -/
theorem sqTop_ok {s : State} {bA : Addr} (hp : PtrC s .rbx bA 72 0) (h8 : (word s.mem bA 64).toNat < 2 ^ 9)
    (hB : qv s 8 8 8 + 2 ^ 512 * ((word s.mem bA 64).toNat * (word s.mem bA 64).toNat) +
      2 * (word s.mem bA 64).toNat * wordsVal s.mem bA 0 8 < 2 ^ 576) :
    WP isa (.block sqTop) s fun s' =>
      regsVal s' (xWin 8) = qv s 8 8 8 + 2 ^ 512 * ((word s.mem bA 64).toNat * (word s.mem bA 64).toNat) +
        2 * (word s.mem bA 64).toNat * wordsVal s.mem bA 0 8 ∧
      Keeps (.rcx :: .rax :: .rdx :: xWin 8) s s' := by
  rw [sqTop, ← xWin8, List.append_assoc, WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.mov .rdx (asrc 64), .mov .r14 (.reg .rdx), .imul .r14 .r14,
      .alu .add .rdx (.reg .rdx)]) s (fun s₄ => (s₄.gpr .r14).toNat = (word s.mem bA 64).toNat * (word s.mem bA 64).toNat ∧
        (s₄.gpr .rdx).toNat = 2 * (word s.mem bA 64).toNat ∧ s₄.cf = some false ∧ s₄.of = some false ∧
        Keeps [.rdx, .r14] s s₄) by
    rw [show [Instr.mov .rdx (asrc 64), .mov .r14 (.reg .rdx), .imul .r14 .r14, .alu .add .rdx (.reg .rdx)] =
      [.mov .rdx (asrc 64)] ++ ([.mov .r14 (.reg .rdx)] ++ ([.imul .r14 .r14] ++ [.alu .add .rdx (.reg .rdx)])) from rfl,
      WP.block_append_iff]
    refine WP.mono (movRdx_ok s (v := word s.mem bA 64) (by exact readSrc_rcR hp (by omega)))
      fun s₁ ⟨d₁, _, _, k₁⟩ => ?_
    rw [WP.block_append_iff]
    refine WP.mono (movR_ok s₁ .r14 (src := .reg .rdx) rfl) fun s₂ ⟨r₂, _, _, k₂⟩ => ?_
    rw [WP.block_append_iff]
    refine WP.mono (imulSq_ok s₂ .r14) fun s₃ ⟨r₃, k₃⟩ => ?_
    have hd₃ : s₃.gpr .rdx = word s.mem bA 64 := by rw [k₃.1 _ (by decide), k₂.1 _ (by decide), d₁]
    refine WP.mono (addSelf_ok s₃ .rdx (by rw [hd₃]; omega)) fun s₄ ⟨d₄, cf₄, of₄, k₄⟩ =>
      ⟨?_, by rw [d₄, hd₃], cf₄, of₄, ?_⟩
    · rw [k₄.1 _ (by decide), r₃, r₂, d₁]
      have := Nat.mul_lt_mul'' h8 h8
      exact Nat.mod_eq_of_lt (by omega)
    · exact ((k₁.mono (by decide)).trans (k₂.mono (by decide))).trans ((k₃.mono (by decide)).trans
        (k₄.mono (by decide)))) fun s₄ ⟨r₄, d₄, cf₄, of₄, k₄⟩ => ?_
  have hp₄ := hp.of_keeps k₄ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (maddStepsM_ok 8 (xWin 8) hp₄ (xWin_sub 8) (d := 0) (by omega) (by simp [xWin]) (xWin_fresh 8)
    cf₄ of₄) fun s₅ ⟨c₅, o₅, cf₅, of₅, e₅, k₅⟩ => ?_
  refine WP.mono (adc0_ok s₅ .r14 cf₅) fun s₆ ⟨c₆, cf₆, e₆, k₆⟩ => ⟨?_, ?_⟩
  · rw [List.take_of_length_le (by simp [xWin]), k₄.2.1, d₄] at e₅
    rw [xWin8] at e₅ ⊢
    obtain ⟨q8, q9, q10, q11, q12, q13, q14, q15⟩ := q_lit
    qv_simp at hB ⊢
    rw [q8, q9, q10, q11, q12, q13, q14, q15] at hB ⊢
    simp only [regsVal, Nat.mul_zero, Nat.add_zero] at e₅ ⊢
    rw [k₆.1 .r15 (by decide), k₆.1 .rbp (by decide), k₆.1 .r8 (by decide), k₆.1 .r9 (by decide),
      k₆.1 .r10 (by decide), k₆.1 .r11 (by decide), k₆.1 .r12 (by decide), k₆.1 .r13 (by decide)]
    rw [k₄.1 .r15 (by decide), k₄.1 .rbp (by decide), k₄.1 .r8 (by decide), k₄.1 .r9 (by decide),
      k₄.1 .r10 (by decide), k₄.1 .r11 (by decide), k₄.1 .r12 (by decide), k₄.1 .r13 (by decide), r₄] at e₅
    have := Bool.toNat_le c₆; have := Bool.toNat_le o₅; have := Bool.toNat_le c₅
    simp only [Bool.toNat_false, Nat.add_zero, Nat.mul_zero] at e₅
    rw [Nat.mul_assoc 2] at hB e₅ ⊢
    omega_using [e₅, e₆, hB]
  · refine (k₄.mono ?_).trans ((k₅.mono ?_).trans (k₆.mono ?_))
    · rw [xWin8]; decide
    · rw [xWin8]; decide
    · rw [xWin8]; decide


/-! ## The rows together -/

theorem rowP_le (m : Mem) (bA : Addr) (r : Nat) (hr : r ≤ 3) :
    rowP m bA r ≤ (2 ^ 64 - 1) * (2 ^ (64 * 7) - 1) := by
  have ha : ∀ d, (word m bA d).toNat ≤ 2 ^ 64 - 1 := fun d => by have := (word m bA d).isLt; omega
  have hw : ∀ d n, wordsVal m bA d n ≤ 2 ^ (64 * n) - 1 := fun d n => by have := wordsVal_lt m bA d n; omega
  rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 by omega) with rfl | rfl | rfl | rfl
  · show (word m bA 0).toNat * wordsVal m bA 8 7 ≤ _
    have := Nat.mul_le_mul (ha 0) (hw 8 7)
    omega
  · have h1 := Nat.mul_le_mul (ha (8 * 1)) (hw (8 * (1 + 1)) (7 - 1))
    have h2 := Nat.mul_le_mul (ha (8 * (1 + 4))) (hw 32 1)
    rw [rowP_pos _ _ (by omega)]
    omega
  · have h1 := Nat.mul_le_mul (ha (8 * 2)) (hw (8 * (2 + 1)) (7 - 2))
    have h2 := Nat.mul_le_mul (ha (8 * (2 + 4))) (hw 32 2)
    rw [rowP_pos _ _ (by omega)]
    omega
  · have h1 := Nat.mul_le_mul (ha (8 * 3)) (hw (8 * (3 + 1)) (7 - 3))
    have h2 := Nat.mul_le_mul (ha (8 * (3 + 4))) (hw 32 3)
    rw [rowP_pos _ _ (by omega)]
    omega

theorem rowP_congr {m m' : Mem} {bA : Addr} (h : ∀ d n, d + 8 * n ≤ 72 → wordsVal m' bA d n = wordsVal m bA d n)
    (hw : ∀ d, d + 8 ≤ 72 → word m' bA d = word m bA d) (r : Nat) (hr : r ≤ 3) : rowP m' bA r = rowP m bA r := by
  rcases Nat.eq_zero_or_pos r with rfl | hr1
  · simp only [rowP]; rw [hw _ (by omega), h _ _ (by omega)]
  · rw [rowP_pos _ _ hr1, rowP_pos _ _ hr1, hw _ (by omega), h _ _ (by omega), hw _ (by omega), h _ _ (by omega)]

/-- Rows 0 to 3: the products of two different words of `a_0 … a_7`, words
`1 … 7` in the temporary area and `8 … 14` in their registers. -/
theorem sqRows_ok {s : State} {base bA : Addr} (hZ : 4096 ≤ Z) (hs : Scr s base Z) (hp : PtrC s .rbx bA 72 0)
    (hap : Apart bA 0 72 base fnTmp 72) :
    WP isa (.block (sqRow0 ++ sqRow 1 ++ sqRow 2 ++ sqRow 3)) s fun s' =>
      2 ^ 64 * tsum s'.mem base 1 7 + 2 ^ 512 * qv s' 8 7 7 =
        2 ^ 64 * rowP s.mem bA 0 + (2 ^ 64) ^ 3 * rowP s.mem bA 1 + (2 ^ 64) ^ 5 * rowP s.mem bA 2 +
          (2 ^ 64) ^ 7 * rowP s.mem bA 3 ∧
      KeepRegs sqRegs s s' ∧ Outside base (T 1) 56 s.mem s'.mem := by
  have hnw := hs.nowrap
  have hP0 := rowP_le s.mem bA 0 (by omega)
  have hP1 := rowP_le s.mem bA 1 (by omega)
  have hP2 := rowP_le s.mem bA 2 (by omega)
  have hP3 := rowP_le s.mem bA 3 (by omega)
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (sqRow0_ok hZ hs hp hap) fun s₁ ⟨R0, t1, t2, _, k₁, O₁⟩ => ?_
  have hs₁ : Scr s₁ base Z := hs.of_keepRegs' k₁ (by decide)
  have hp₁ := hp.of_keepRegs k₁ (by decide)
  have hm₁ : ∀ d n, d + 8 * n ≤ 72 → wordsVal s₁.mem bA d n = wordsVal s.mem bA d n :=
    fun d n h => opnd_eq hap O₁ (by t_omega) h
  have hw₁ : ∀ d, d + 8 ≤ 72 → word s₁.mem bA d = word s.mem bA d := fun d h => opnd_word hap O₁ (by t_omega) h
  have sp0 : qv s₁ 1 8 8 = (s₁.gpr (q 1)).toNat + 2 ^ 64 * (s₁.gpr (q 2)).toNat + 2 ^ 128 * qv s₁ 3 6 6 := by
    qv_simp; omega
  rw [show (word s.mem bA 0).toNat * wordsVal s.mem bA 8 7 = rowP s.mem bA 0 from rfl] at R0
  -- Row 1.
  rw [WP.block_append_iff]
  refine WP.mono (sqRowN_ok (r := 1) (by omega) (by omega) hZ hs₁ hp₁ hap (by
    rw [rowP_congr hm₁ hw₁ 1 (by omega)]
    simp only [Nat.reduceMul, Nat.reduceAdd]
    omega_using [R0, sp0, hP0, hP1])) fun s₂ ⟨R1, st₂, _, k₂, O₂⟩ => ?_
  rw [rowP_congr hm₁ hw₁ 1 (by omega)] at R1
  have hs₂ : Scr s₂ base Z := hs₁.of_keepRegs' k₂ (by decide)
  have hp₂ := hp₁.of_keepRegs k₂ (by decide)
  have O12 : Outside base (T 1) 32 s.mem s₂.mem := (O₁.mono (Nat.le_refl _) (by t_omega)).trans
    (O₂.mono (T_le' 1 3) (by t_omega))
  have hm₂ : ∀ d n, d + 8 * n ≤ 72 → wordsVal s₂.mem bA d n = wordsVal s.mem bA d n :=
    fun d n h => opnd_eq hap O12 (by t_omega) h
  have hw₂ : ∀ d, d + 8 ≤ 72 → word s₂.mem bA d = word s.mem bA d := fun d h => opnd_word hap O12 (by t_omega) h
  have sp1 : qv s₂ 3 8 8 = (s₂.gpr (q 3)).toNat + 2 ^ 64 * (s₂.gpr (q 4)).toNat + 2 ^ 128 * qv s₂ 5 6 6 := by
    qv_simp; omega
  -- Row 2.
  rw [WP.block_append_iff]
  simp only [Nat.reduceMul, Nat.reduceAdd] at R1
  refine WP.mono (sqRowN_ok (r := 2) (by omega) (by omega) hZ hs₂ hp₂ hap (by
    rw [rowP_congr hm₂ hw₂ 2 (by omega)]
    simp only [Nat.reduceMul, Nat.reduceAdd]
    omega_using [R0, sp0, R1, sp1, hP0, hP1, hP2])) fun s₃ ⟨R2, st₃, _, k₃, O₃⟩ => ?_
  rw [rowP_congr hm₂ hw₂ 2 (by omega)] at R2
  simp only [Nat.reduceMul, Nat.reduceAdd] at R2
  have hs₃ : Scr s₃ base Z := hs₂.of_keepRegs' k₃ (by decide)
  have hp₃ := hp₂.of_keepRegs k₃ (by decide)
  have O13 : Outside base (T 1) 48 s.mem s₃.mem := (O12.mono (Nat.le_refl _) (by t_omega)).trans
    (O₃.mono (T_le' 1 5) (by t_omega))
  have hm₃ : ∀ d n, d + 8 * n ≤ 72 → wordsVal s₃.mem bA d n = wordsVal s.mem bA d n :=
    fun d n h => opnd_eq hap O13 (by t_omega) h
  have hw₃ : ∀ d, d + 8 ≤ 72 → word s₃.mem bA d = word s.mem bA d := fun d h => opnd_word hap O13 (by t_omega) h
  have sp2 : qv s₃ 5 8 8 = (s₃.gpr (q 5)).toNat + 2 ^ 64 * (s₃.gpr (q 6)).toNat + 2 ^ 128 * qv s₃ 7 6 6 := by
    qv_simp; omega
  -- Row 3.
  refine WP.mono (sqRowN_ok (r := 3) (by omega) (by omega) hZ hs₃ hp₃ hap (by
    rw [rowP_congr hm₃ hw₃ 3 (by omega)]
    simp only [Nat.reduceMul, Nat.reduceAdd]
    omega_using [R0, sp0, R1, sp1, R2, sp2, hP0, hP1, hP2, hP3])) fun s₄ ⟨R3, st₄, _, k₄, O₄⟩ => ?_
  rw [rowP_congr hm₃ hw₃ 3 (by omega)] at R3
  simp only [Nat.reduceMul, Nat.reduceAdd] at R3
  refine ⟨?_, (k₁.trans k₂).trans (k₃.trans k₄), ?_⟩
  · -- The stored words.
    have w1 : word s₄.mem base (T 1) = s₁.gpr (q 1) := by
      rw [O₄.word (by t_omega) (by t_omega), O₃.word (by t_omega) (by t_omega), O₂.word (by t_omega) (by t_omega), t1]
    have w2 : word s₄.mem base (T 2) = s₁.gpr (q 2) := by
      rw [O₄.word (by t_omega) (by t_omega), O₃.word (by t_omega) (by t_omega), O₂.word (by t_omega) (by t_omega), t2]
    have w3 : word s₄.mem base (T 3) = s₂.gpr (q 3) := by
      rw [O₄.word (by t_omega) (by t_omega), O₃.word (by t_omega) (by t_omega)]; exact st₂ 0 (by decide)
    have w4 : word s₄.mem base (T 4) = s₂.gpr (q 4) := by
      rw [O₄.word (by t_omega) (by t_omega), O₃.word (by t_omega) (by t_omega)]; exact st₂ 1 (by decide)
    have w5 : word s₄.mem base (T 5) = s₃.gpr (q 5) := by
      rw [O₄.word (by t_omega) (by t_omega)]; exact st₃ 0 (by decide)
    have w6 : word s₄.mem base (T 6) = s₃.gpr (q 6) := by
      rw [O₄.word (by t_omega) (by t_omega)]; exact st₃ 1 (by decide)
    have w7 : word s₄.mem base (T 7) = s₄.gpr (q 7) := st₄ 0 (by decide)
    have sp3 : qv s₄ 7 8 8 = (s₄.gpr (q 7)).toNat + 2 ^ 64 * qv s₄ 8 7 7 := by qv_simp
    have ht : tsum s₄.mem base 1 7 = (s₁.gpr (q 1)).toNat + 2 ^ 64 * ((s₁.gpr (q 2)).toNat + 2 ^ 64 * (
        (s₂.gpr (q 3)).toNat + 2 ^ 64 * ((s₂.gpr (q 4)).toNat + 2 ^ 64 * ((s₃.gpr (q 5)).toNat + 2 ^ 64 * (
          (s₃.gpr (q 6)).toNat + 2 ^ 64 * (s₄.gpr (q 7)).toNat))))) := by
      simp only [tsum, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero]
      rw [w1, w2, w3, w4, w5, w6, w7]
    rw [ht]
    omega_using [R0, sp0, R1, sp1, R2, sp2, R3, sp3]
  · exact (O13.mono (Nat.le_refl _) (by t_omega)).trans (O₄.mono (T_le' 1 7) (by t_omega))


/-! ## The square -/

/-- Twice the rows' products plus the squares is `[a_0 … a_7]²`. -/
theorem sq_ident1 (m : Mem) (bA : Addr) :
    2 * (2 ^ 64 * rowP m bA 0 + (2 ^ 64) ^ 3 * rowP m bA 1 + (2 ^ 64) ^ 5 * rowP m bA 2 + (2 ^ 64) ^ 7 * rowP m bA 3) +
      dg (fun j => (word m bA (8 * j)).toNat) 8 = wordsVal m bA 0 8 * wordsVal m bA 0 8 := by
  simp only [rowP_pos _ _ (show 1 ≤ 1 by omega), rowP_pos _ _ (show 1 ≤ 2 by omega),
    rowP_pos _ _ (show 1 ≤ 3 by omega), Nat.pow_mul]
  simp only [rowP, wordsVal, dg, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, -Nat.reducePow]
  generalize (word m bA 0).toNat = a0
  generalize (word m bA 8).toNat = a1
  generalize (word m bA 16).toNat = a2
  generalize (word m bA 24).toNat = a3
  generalize (word m bA 32).toNat = a4
  generalize (word m bA 40).toNat = a5
  generalize (word m bA 48).toNat = a6
  generalize (word m bA 56).toNat = a7
  generalize (2 : Nat) ^ 64 = X
  grind


theorem sq_add (L a Y : Nat) : (L + Y * a) * (L + Y * a) = L * L + Y * (2 * a * L) + Y * (Y * (a * a)) := by
  grind

theorem dg_congr {f g : Nat → Nat} : ∀ {n}, (∀ j < n, f j = g j) → dg f n = dg g n
  | 0, _ => rfl
  | n + 1, h => by rw [dg, dg, dg_congr fun j hj => h j (by omega), h n (by omega)]

/-- `[a_0 … a_8]` is `[a_0 … a_7] + 2⁵¹² a_8`. -/
theorem wordsVal9 (m : Mem) (bA : Addr) :
    wordsVal m bA 0 9 = wordsVal m bA 0 8 + (2 ^ 64) ^ 8 * (word m bA 64).toNat := wordsVal_succ_last m bA 0 8

/-- `sqrS`: `[rbx]²` for `[rbx] < 2⁵²¹` (its top word below `2⁹`), its words
`0 … 7` in the temporary area and `8 … 16` in `xWin 8`. -/
theorem sqrS_ok {s : State} {base bA : Addr} (hZ : 4096 ≤ Z) (hs : Scr s base Z) (hp : PtrC s .rbx bA 72 0)
    (hap : Apart bA 0 72 base fnTmp 72) (h8 : (word s.mem bA 64).toNat < 2 ^ 9) :
    WP isa (.block sqrS) s fun s' =>
      tsum s'.mem base 0 8 + 2 ^ 512 * regsVal s' (xWin 8) = wordsVal s.mem bA 0 9 * wordsVal s.mem bA 0 9 ∧
      KeepRegs sqRegs s s' ∧ Outside base (T 0) 64 s.mem s'.mem := by
  have hnw := hs.nowrap
  have hI1 := sq_ident1 s.mem bA
  have hA := wordsVal9 s.mem bA
  have hL := wordsVal_lt s.mem bA 0 8
  rw [VG.Impl.Weierstrass.X86_64.P521F.sqrS, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (sqRows_ok hZ hs hp hap) fun s₁ ⟨Rw, k₁, O₁⟩ => ?_
  have hs₁ : Scr s₁ base Z := hs.of_keepRegs' k₁ (by decide)
  have hp₁ := hp.of_keepRegs k₁ (by decide)
  have O₁' : Outside base (T 0) 64 s.mem s₁.mem := O₁.mono (T_le' 0 1) (by t_omega)
  have hw₁ : ∀ d, d + 8 ≤ 72 → word s₁.mem bA d = word s.mem bA d := fun d h => opnd_word hap O₁' (by t_omega) h
  have hdg₁ : dg (fun j => (word s₁.mem bA (8 * j)).toNat) 8 = dg (fun j => (word s.mem bA (8 * j)).toNat) 8 :=
    dg_congr fun j hj => by rw [hw₁ _ (by omega)]
  -- The squares.
  refine WP.mono (sqDiag_ok hZ hs₁ hp₁ hap (by
    rw [hdg₁]
    have hLL := Nat.mul_lt_mul'' hL hL
    omega_using [Rw, hI1, hLL])) fun s₂ ⟨D, k₂, O₂⟩ => ?_
  rw [hdg₁] at D
  have hp₂ := hp₁.of_keepRegs k₂ (by decide)
  have O₂' : Outside base (T 0) 64 s.mem s₂.mem := O₁'.trans O₂
  have hw₂ : ∀ d, d + 8 ≤ 72 → word s₂.mem bA d = word s.mem bA d := fun d h => opnd_word hap O₂' (by t_omega) h
  have hm₂ : ∀ d n, d + 8 * n ≤ 72 → wordsVal s₂.mem bA d n = wordsVal s.mem bA d n :=
    fun d n h => opnd_eq hap O₂' (by t_omega) h
  -- The bound on `[a]²`.
  have h521 : wordsVal s.mem bA 0 9 < 2 ^ 521 := by rw [hA]; omega
  have hAA := Nat.mul_lt_mul'' h521 h521
  have hI2 : wordsVal s.mem bA 0 9 * wordsVal s.mem bA 0 9 = wordsVal s.mem bA 0 8 * wordsVal s.mem bA 0 8 +
      (2 ^ 64) ^ 8 * (2 * (word s.mem bA 64).toNat * wordsVal s.mem bA 0 8) +
      (2 ^ 64) ^ 8 * ((2 ^ 64) ^ 8 * ((word s.mem bA 64).toNat * (word s.mem bA 64).toNat)) := by
    rw [hA]; exact sq_add _ _ _
  -- The top word's row.
  refine WP.mono (sqTop_ok hp₂ (by rw [hw₂ _ (by omega)]; exact h8) (by
    rw [hw₂ _ (by omega), hm₂ _ _ (by omega)]
    omega_using [D, Rw, hI1, hI2, hAA])) fun s₃ ⟨Tp, k₃⟩ => ⟨?_, ?_, ?_⟩
  · rw [Tp, k₃.2.1, hw₂ _ (by omega), hm₂ _ _ (by omega)]
    omega_using [D, Rw, hI1, hI2]
  · exact (k₁.trans k₂).trans ((keepRegs_of_keeps k₃).mono (by rw [xWin8]; decide))
  · rw [k₃.2.1]; exact O₂'

end VG.Proof.Weierstrass.X86_64.P521F
