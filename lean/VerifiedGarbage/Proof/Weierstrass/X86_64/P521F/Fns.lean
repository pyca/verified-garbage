module
-- separate module: its proofs (the field functions) build in parallel with those of `Cms`, which `Steps` also imports

public import VerifiedGarbage.Proof.Weierstrass.X86_64.P521F.Red
public import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFnX
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.KeepReg
import VerifiedGarbage.Proof.Framework.X86_64.LaneSse
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# P-521 on x86-64: the products and the square by light calls

`sqrFn`, `mulFn` and `mulFnW` (`Impl/Weierstrass/X86_64/P521Fast.lean`)
leave `[o] = [a] [b] 2⁻⁵⁷⁶ mod p` for `[a]`, `[b]` below `p`, `[o]` below
`p` (`sqrFn_ok`, `mulFn_ok`) or below `2p` (`mulFnW_ok`): the product or
the square, the reduction by shifts (`redS_ok`), whose result `Q` has
`2⁵⁷⁶ Q ≡ P (mod p)` and `Q < 2p` (`redQ_arith`, `redQ_lt`), and `xCanon`
or the stores. They change only the registers but `rdi`, `rsi` and `rsp`,
`[o]` and the temporary area.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64.P521F

open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64.P521F
open VG.Impl.Weierstrass.X86_64.Mont (fnTmp copyW fnMod)
open VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.Weierstrass.X86_64.Mont (ptrC_of apart_off wordsVal_off word_off off_off rdiRsi_ok xCanon_at
  storesC_shift copyW_ok movReg_ok)
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

variable {Z : Nat}

/-! ## The arithmetic of the reduction -/

/-- `2⁵⁷⁶ Q = P + p k`, `p = 2⁵²¹ - 1`, for `P = P_lo + 2⁵⁷⁶ P_hi`. -/
theorem redQ_arith (Plo Ph w0 : Nat) (hw : w0 % 2 ^ 55 = Plo % 2 ^ 55) :
    (Ph + w0 % 2 ^ 55 * 2 ^ 466 + Plo / 2 ^ 55) * (2 ^ 64) ^ 9 =
      Plo + 2 ^ 576 * Ph + (2 ^ 521 - 1) * (w0 % 2 ^ 55 * (2 ^ 521 + 1) + 2 ^ 55 * (Plo / 2 ^ 55)) := by
  omega

/-- `Q < 2p` for `P ≤ (p - 1)²`. -/
theorem redQ_lt (Plo Ph w0 : Nat) (hw : w0 % 2 ^ 55 = Plo % 2 ^ 55) (hlo : Plo < 2 ^ 576)
    (hP : Plo + 2 ^ 576 * Ph ≤ (2 ^ 521 - 2) * (2 ^ 521 - 2)) :
    Ph + w0 % 2 ^ 55 * 2 ^ 466 + Plo / 2 ^ 55 + 1 ≤ 2 * (2 ^ 521 - 1) := by
  omega

/-- The product of two numbers below `p`. -/
theorem mul_le_sq {A B : Nat} (hA : A < 2 ^ 521 - 1) (hB : B < 2 ^ 521 - 1) :
    A * B ≤ (2 ^ 521 - 2) * (2 ^ 521 - 2) := by
  have h1 : A ≤ 2 ^ 521 - 2 := by omega
  have h2 : B ≤ 2 ^ 521 - 2 := by omega
  have := Nat.mul_le_mul h1 h2
  omega


/-! ## The exits -/

theorem rdi_back {s s₁ s₂ s₃ : State} (d₁ : s₁.gpr .rdi = s.gpr .rdi + s.gpr .rsi)
    (r₂ : s₂.gpr .rsi = s.gpr .rsi) (h₂ : s₂.gpr .rdi = s₁.gpr .rdi) (d₃ : s₃.gpr .rdi = s₂.gpr .rdi - s₂.gpr .rsi) :
    s₃.gpr .rdi = s.gpr .rdi := by
  rw [d₃, h₂, d₁, r₂, BitVec.add_sub_cancel]

/-- `exitS`: `[o] = (W - 1) mod p` from `W` in `xWin 9`, `1 ≤ W ≤ 2p`, `o` in `rsi`. -/
theorem exitS_ok (hZ : 4096 ≤ Z) {s : State} {base : Addr} (hs : Scr s base Z) {o m : Nat} (ho : o + 72 ≤ 3520)
    (hso : s.gpr .rsi = BitVec.ofNat 64 o) (hm : m + 1 = 512 * (2 ^ 64) ^ 8)
    (hT1 : 1 ≤ hval (xg s) 9 9) (hT : hval (xg s) 9 9 ≤ 2 * m) :
    WP isa (.block exitS) s fun s' =>
      wordsVal s'.mem base o 9 = (hval (xg s) 9 9 - 1) % m ∧ KeepRegs (.rax :: xRegs) s s' ∧
        Outside base o 72 s.mem s'.mem := by
  have hnw := hs.nowrap
  rw [exitS, List.append_assoc, WP.block_append_iff]
  refine WP.mono (rdiRsi_ok s .add (Or.inl rfl)) fun s₁ ⟨d₁, k₁⟩ => ?_
  simp only [ite_true] at d₁
  have hs₁ : ScrC s₁ base Z o := ⟨by rw [d₁, hso, hs.rdi], by rw [k₁.2.2.2]; exact hs.wr, hnw⟩
  have hx₁ : hval (xg s₁) 9 9 = hval (xg s) 9 9 := hval_congr fun c _ _ => by
    simp only [xg]; rw [k₁.1 _ (by simpa using (xAcc_ne c).2.2.2.1)]
  have hc := xCanon_ok hs₁ (o := o) (by omega) hm (by rw [hx₁]; exact hT1) (by rw [hx₁]; exact hT)
  rw [← xCanon_at o] at hc
  rw [WP.block_append_iff]
  refine WP.mono hc fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  refine WP.mono (rdiRsi_ok s₂ .sub (Or.inr rfl)) fun s₃ ⟨d₃, k₃⟩ => ⟨?_, ⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · rw [k₃.2.1, e₂, hx₁]
  · simp only [reduceCtorEq, ite_false] at d₃
    by_cases hd : r = .rdi
    · subst hd
      exact rdi_back d₁ (by rw [k₂.gpr _ (by decide), k₁.1 _ (by decide)]) (k₂.gpr _ (by decide)) d₃
    · rw [k₃.1 _ (by simpa using hd), k₂.gpr _ hr, k₁.1 _ (by simpa using hd)]
  · rw [k₃.2.2.1, k₂.rd, k₁.2.2.1]
  · rw [k₃.2.2.2, k₂.wr, k₁.2.2.2]
  · rw [k₃.2.1, ← k₁.2.1]; exact O₂

/-- `exitW`: `[o] = W` from `W` in `xWin 9`, `o` in `rsi`. -/
theorem exitW_ok (hZ : 4096 ≤ Z) {s : State} {base : Addr} (hs : Scr s base Z) {o : Nat} (ho : o + 72 ≤ 3520)
    (hso : s.gpr .rsi = BitVec.ofNat 64 o) :
    WP isa (.block exitW) s fun s' =>
      wordsVal s'.mem base o 9 = hval (xg s) 9 9 ∧ KeepRegs [] s s' ∧ Outside base o 72 s.mem s'.mem := by
  have hnw := hs.nowrap
  rw [exitW, List.append_assoc, WP.block_append_iff]
  refine WP.mono (rdiRsi_ok s .add (Or.inl rfl)) fun s₁ ⟨d₁, k₁⟩ => ?_
  simp only [ite_true] at d₁
  have hs₁ : ScrC s₁ base Z o := ⟨by rw [d₁, hso, hs.rdi], by rw [k₁.2.2.2]; exact hs.wr, hnw⟩
  have hx₁ : hval (xg s₁) 9 9 = hval (xg s) 9 9 := hval_congr fun c _ _ => by
    simp only [xg]; rw [k₁.1 _ (by simpa using (xAcc_ne c).2.2.2.1)]
  have hc := storesC_ok (xWin 9) hs₁ (o := o) (by simp [xWin]; omega) (xWin_fresh 9).1
  have hsh := storesC_shift 0 o (xWin 9) 0
  simp only [Nat.zero_add] at hsh
  rw [hsh] at hc
  rw [WP.block_append_iff]
  refine WP.mono hc fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  refine WP.mono (rdiRsi_ok s₂ .sub (Or.inr rfl)) fun s₃ ⟨d₃, k₃⟩ => ⟨?_, ⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · rw [k₃.2.1, show (xWin 9).length = 9 from rfl] at *
    rw [e₂, regsVal_xWin, hx₁]
  · simp only [reduceCtorEq, ite_false] at d₃
    by_cases hd : r = .rdi
    · subst hd
      exact rdi_back d₁ (by rw [k₂.gpr _ (by decide), k₁.1 _ (by decide)]) (k₂.gpr _ (by decide)) d₃
    · rw [k₃.1 _ (by simpa using hd), k₂.gpr _ hr, k₁.1 _ (by simpa using hd)]
  · rw [k₃.2.2.1, k₂.rd, k₁.2.2.1]
  · rw [k₃.2.2.2, k₂.wr, k₁.2.2.2]
  · rw [k₃.2.1, ← k₁.2.1]
    simpa [xWin] using O₂


/-! ## The functions -/

theorem keepRegs_of_keeps' {rs : List Reg} {s s₁ s₂ : State} (k : KeepRegs rs s s₁) (g : s₂.gpr = s₁.gpr)
    (rd : s₂.rd = s₁.rd) (wr : s₂.wr = s₁.wr) : KeepRegs rs s s₂ :=
  ⟨fun r hr => by rw [g]; exact k.gpr r hr, rd.trans k.rd, wr.trans k.wr⟩

/-- The registers the functions change. -/
abbrev lclob : List Reg := [.rax, .rbx, .rcx, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-- What a function leaves at `[o]`, for `P = [a] [b]`: below `p` (or `2p`
if `weak`), and `2⁻⁵⁷⁶ P` modulo `p`. -/
def FnPost (m : Nat) (weak : Bool) (base : Addr) (o P : Nat) (s s' : State) : Prop :=
  wordsVal s'.mem base o 9 < (if weak then 2 * m else m) ∧ wordsVal s'.mem base o 9 * (2 ^ 64) ^ 9 % m = P % m ∧
    KeepRegs lclob s s' ∧
    ∀ x, (ofs base x < o ∨ o + 72 ≤ ofs base x) → (ofs base x < fnTmp ∨ 4096 ≤ ofs base x) → s'.mem x = s.mem x

theorem tsum_succ8 (mm : Mem) (base : Addr) :
    tsum mm base 0 9 = tsum mm base 0 8 + (2 ^ 64) ^ 8 * (word mm base (T 8)).toNat := by
  rw [tsum_eq, tsum_eq, wordsVal_succ_last, show T 0 + 8 * 8 = T 8 by rw [T_eq, T_eq]]

theorem tsum_lo (mm : Mem) (base : Addr) :
    tsum mm base 0 9 = (word mm base (T 0)).toNat + 2 ^ 64 * tsum mm base 1 8 := rfl

/-- The reduction and the exit, from `P` in the temporary area and `xAcc 9 … 16`, `P ≤ (p - 1)²`. -/
theorem redExit_ok (hZ : 4096 ≤ Z) {s : State} {base : Addr} (hs : Scr s base Z) {o m : Nat} (ho : o + 72 ≤ 3520)
    (hso : s.gpr .rsi = BitVec.ofNat 64 o) (hm : m + 1 = 512 * (2 ^ 64) ^ 8) (weak : Bool)
    (hP : tsum s.mem base 0 9 + 2 ^ 576 * hval (xg s) 9 8 ≤ (2 ^ 521 - 2) * (2 ^ 521 - 2)) :
    WP isa (.block (redS (!weak) ++ (if weak then exitW else exitS))) s
      (FnPost m weak base o (tsum s.mem base 0 9 + 2 ^ 576 * hval (xg s) 9 8) s) := by
  have hm' : m = 2 ^ 521 - 1 := by omega
  have hlo : tsum s.mem base 0 9 < 2 ^ 576 := by
    have e := tsum_eq s.mem base 0 9; have := wordsVal_lt s.mem base (T 0) 9; omega
  have hl8 := hval_succ_last (xg s) 9 7
  simp only [Nat.reduceAdd] at hl8
  have hl7 : hval (xg s) 9 7 < (2 ^ 64) ^ 7 := hval_lt fun c _ _ => (s.gpr _).isLt
  have h16 : xg s 16 < 2 ^ 18 := by omega
  have hw : (word s.mem base (T 0)).toNat % 2 ^ 55 = tsum s.mem base 0 9 % 2 ^ 55 := by rw [tsum_lo]; omega
  have hQ := redQ_lt (tsum s.mem base 0 9) (hval (xg s) 9 8) _ hw hlo hP
  have hA := redQ_arith (tsum s.mem base 0 9) (hval (xg s) 9 8) _ hw
  rw [← hm'] at hQ hA
  rw [WP.block_append_iff]
  refine WP.mono (redS_ok hZ hs (!weak) h16 (by unfold redQ; omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ : Scr s₁ base Z := hs.of_keepRegs' k₁ (by decide)
  have hso₁ : s₁.gpr .rsi = BitVec.ofNat 64 o := by rw [k₁.gpr _ (by decide), hso]
  have hfr : ∀ (s₂ : State), KeepRegs (.rax :: xRegs) s₁ s₂ → Outside base o 72 s₁.mem s₂.mem →
      KeepRegs lclob s s₂ ∧ ∀ x, (ofs base x < o ∨ o + 72 ≤ ofs base x) →
        (ofs base x < fnTmp ∨ 4096 ≤ ofs base x) → s₂.mem x = s.mem x := fun s₂ k₂ O₂ =>
    ⟨(k₁.trans (k₂.mono (by decide))).mono (by decide), fun x hx ht => by
      rw [O₂ x hx, O₁ x (by rw [T_eq]; simp only [fnTmp] at ht; omega)]⟩
  unfold redQ at e₁
  cases weak with
  | false =>
    simp only [Bool.not_false, Bool.toNat_true] at e₁
    refine WP.mono (exitS_ok hZ hs₁ ho hso₁ hm (by omega) (Nat.le_trans (Nat.le_of_eq e₁) hQ))
      fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
    obtain ⟨kk, OO⟩ := hfr s₂ k₂ O₂
    refine ⟨?_, ?_, kk, OO⟩
    · rw [e₂]; simp only [Bool.false_eq_true, ite_false]; exact Nat.mod_lt _ (by omega)
    · rw [e₂, e₁, Nat.add_sub_cancel, Nat.mod_mul_mod, hA, Nat.add_mul_mod_self_left]
  | true =>
    refine WP.mono (exitW_ok hZ hs₁ ho hso₁) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
    obtain ⟨kk, OO⟩ := hfr s₂ (k₂.mono (by decide)) O₂
    refine ⟨?_, ?_, kk, OO⟩
    · rw [e₂, e₁]; simp only [Bool.not_true, Bool.toNat_false, ite_true]; omega
    · rw [e₂, e₁]
      simp only [Bool.not_true, Bool.toNat_false, Nat.add_zero]
      rw [hA, Nat.add_mul_mod_self_left]


/-- `FnPost` after a part that changes only `lclob` and the temporary area. -/
theorem FnPost.pre {m : Nat} {weak : Bool} {base : Addr} {o P : Nat} {s s₁ s₂ : State}
    (k : KeepRegs lclob s s₁) (O : ∀ x, (ofs base x < fnTmp ∨ 4096 ≤ ofs base x) → s₁.mem x = s.mem x)
    (h : FnPost m weak base o P s₁ s₂) : FnPost m weak base o P s s₂ :=
  ⟨h.1, h.2.1, k.trans h.2.2.1, fun x hx ht => (h.2.2.2 x hx ht).trans (O x ht)⟩

theorem a8_lt {mm : Mem} {base : Addr} {a m : Nat} (hm : m + 1 = 512 * (2 ^ 64) ^ 8) (hA : wordsVal mm base a 9 < m) :
    (word mm base (a + 64)).toNat < 2 ^ 9 := by
  have e := wordsVal_succ_last mm base a 8
  rw [show a + 8 * 8 = a + 64 from rfl, show 8 + 1 = 9 from rfl] at e
  omega

theorem off_word_eq {mm : Mem} {base : Addr} {a : Nat} : word mm (off base a) 64 = word mm base (a + 64) :=
  word_off mm base a 64

/-- `vg_p521_sqr_adx`: `[o] = [a]² 2⁻⁵⁷⁶ mod p`, below `p`, for `rbx = ws + a`, `rsi = o`, `[a] < p`. -/
theorem sqrFn_ok (hZ : 4096 ≤ Z) {s : State} {base : Addr} (hs : Scr s base Z) {a o m : Nat}
    (hbx : s.gpr .rbx = off base a) (hso : s.gpr .rsi = BitVec.ofNat 64 o) (ha : a + 72 ≤ 3520) (ho : o + 72 ≤ 3520)
    (hm : m + 1 = 512 * (2 ^ 64) ^ 8) (hA : wordsVal s.mem base a 9 < m) :
    WP isa sqrFn s (FnPost m false base o (wordsVal s.mem base a 9 * wordsVal s.mem base a 9) s) := by
  have hnw := hs.nowrap
  have hp := ptrC_of hs hbx (show a + 72 ≤ Z by omega) (by decide) (Or.inr (Or.inr rfl))
  have hap : Apart (off base a) 0 72 base fnTmp 72 := apart_off base (by simp only [fnTmp]; omega) (by omega)
  have hA' : wordsVal s.mem (off base a) 0 9 = wordsVal s.mem base a 9 := by rw [wordsVal_off, Nat.add_zero]
  have h8 : (word s.mem (off base a) 64).toNat < 2 ^ 9 := by rw [off_word_eq]; exact a8_lt hm hA
  rw [sqrFn, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (sqrS_ok hZ hs hp hap h8) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ : Scr s₁ base Z := hs.of_keepRegs' k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (storeX_ok hs₁ .r15 (d := T 8) (by rw [T_eq]; omega)) fun s₂ ⟨m₂, g₂, _, _, rd₂, wr₂⟩ => ?_
  have hs₂ : Scr s₂ base Z := ⟨by rw [g₂]; exact hs₁.rdi, by rw [wr₂]; exact hs₁.wr, hnw⟩
  have hso₂ : s₂.gpr .rsi = BitVec.ofNat 64 o := by rw [g₂, k₁.gpr _ (by decide), hso]
  have O₂ : Outside base (T 8) 8 s₁.mem s₂.mem := by rw [m₂]; exact writeW_outside _ _ _ (by rw [T_eq]; omega)
  -- The square, as the reduction reads it.
  have ht8 : tsum s₂.mem base 0 8 = tsum s₁.mem base 0 8 := by
    rw [tsum_eq, tsum_eq]; exact O₂.wordsVal (by rw [T_eq, T_eq]; omega) (by rw [T_eq]; omega)
  have hw8 : (word s₂.mem base (T 8)).toNat = xg s₁ 8 := by rw [m₂, word_writeW_self]; rfl
  have hx : hval (xg s₂) 9 8 = hval (xg s₁) 9 8 := hval_congr fun c _ _ => by simp only [xg]; rw [g₂]
  have hr : regsVal s₁ (xWin 8) = xg s₁ 8 + 2 ^ 64 * hval (xg s₁) 9 8 := by
    rw [regsVal_xWin, hval]
  have hP : tsum s₂.mem base 0 9 + 2 ^ 576 * hval (xg s₂) 9 8 =
      wordsVal s.mem base a 9 * wordsVal s.mem base a 9 := by
    rw [tsum_succ8, ht8, hw8, hx, ← hA', ← e₁, hr]
    omega
  have hle := mul_le_sq (A := wordsVal s.mem base a 9) (B := wordsVal s.mem base a 9) (by omega) (by omega)
  refine WP.mono (redExit_ok hZ hs₂ ho hso₂ hm false (by rw [hP]; exact hle)) fun s₃ h => ?_
  rw [hP] at h
  refine FnPost.pre ((keepRegs_of_keeps' k₁ g₂ rd₂ wr₂).mono (by decide)) (fun x ht => ?_) h
  rw [O₂ x (by rw [T_eq]; simp only [fnTmp] at ht; omega), O₁ x (by rw [T_eq]; simp only [fnTmp] at ht; omega)]


/-- A block that writes no vector register keeps them. -/
private theorem runBlock_xmm : ∀ (is : List Instr) {s s' : State}, is.all (fun i => !KeepReg.writesVec i) = true →
    runBlock isa is s = some s' → s'.xmm = s.xmm
  | [], s, s', _, h => by simp only [runBlock, Option.some.injEq] at h; rw [h]
  | i :: is, s, s', hw, h => by
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hw
    simp only [runBlock] at h
    cases he : exec i s with
    | none => simp only [isa, he, Option.bind_none, reduceCtorEq] at h
    | some t =>
      simp only [isa, he, Option.bind_some] at h
      rw [runBlock_xmm is hw.2 h, KeepReg.exec_xmm hw.1 he]

private theorem WP.keep_xmm {is : List Instr} (hw : is.all (fun i => !KeepReg.writesVec i) = true) {s : State}
    {Q : State → Prop} (h : WP isa (.block is) s Q) : WP isa (.block is) s fun s' => Q s' ∧ s'.xmm = s.xmm := by
  obtain ⟨s', hr, hq⟩ := WP.runBlock_of h
  exact WP.of_runBlock ⟨s', hr, hq, runBlock_xmm is hw hr⟩

/-- `mulRows`' first two instructions: the output's offset into `xmm13`, `rsi = rcx`. -/
theorem mulPro_ok (s : State) :
    WP isa (.block [.xop (.movq .xmm13 .rsi), .mov .rsi (.reg .rcx)]) s fun s' =>
      s'.gpr .rsi = s.gpr .rcx ∧ (∀ r, r ≠ .rsi → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
        s'.wr = s.wr ∧ (s'.xmm .xmm13).extractLsb' 0 64 = s.gpr .rsi := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, readSrc, Option.map_some]
  refine ⟨_, rfl, ?_, fun r hr => ?_, rfl, rfl, rfl, ?_⟩
  · simp only [RegUpd.gpr_setReg_self, RegUpd.gpr_setXmm]
  · simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_setXmm]
  · simp only [RegUpd.xmm_setReg, RegUpd.xmm_setXmm_self, BitVec.extractLsb'_append_eq_right]

/-- `mulRows`' last instruction: `rsi` from `xmm13`. -/
theorem mulEpi_ok (s : State) :
    WP isa (.block [.movqR .rsi .xmm13]) s fun s' =>
      s'.gpr .rsi = (s.xmm .xmm13).extractLsb' 0 64 ∧ (∀ r, r ≠ .rsi → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, exec]
  exact ⟨_, rfl, RegUpd.gpr_setReg_self .., fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl⟩

/-- `mulRows`: `[a] [b]` with its words `0 … 8` in the temporary area and `9 … 17` in `xWin 9`,
for `rbx = ws + a` and `rcx = ws + b`. -/
theorem mulRows_ok (hZ : 4096 ≤ Z) {s : State} {base : Addr} (hs : Scr s base Z) {a b : Nat}
    (hbx : s.gpr .rbx = off base a) (hcx : s.gpr .rcx = off base b) (ha : a + 72 ≤ 3520) (hb : b + 72 ≤ 3520) :
    WP isa (.block mulRows) s fun s' =>
      wordsVal s'.mem base fnTmp 9 + (2 ^ 64) ^ 9 * hval (xg s') 9 9 = wordsVal s.mem base a 9 * wordsVal s.mem base b 9 ∧
      KeepRegs (.rax :: .rcx :: .rdx :: .rbx :: xRegs) s s' ∧ Outside base fnTmp 72 s.mem s'.mem := by
  have hnw := hs.nowrap
  have hft : (fnMod true).tmp = fnTmp := rfl
  have hft' : fnTmp = 4024 := rfl
  rw [mulRows, List.append_assoc, WP.block_append_iff]
  refine WP.mono (mulPro_ok s) fun s₁ ⟨v₁, k₁, m₁, rd₁, wr₁, x₁⟩ => ?_
  have hs₁ : Scr s₁ base Z := ⟨by rw [k₁ _ (by decide)]; exact hs.rdi, wr₁ ▸ hs.wr, hnw⟩
  have hbx₁ : s₁.gpr .rbx = off base a := by rw [k₁ _ (by decide), hbx]
  have hsi₁ : s₁.gpr .rsi = off base b := by rw [v₁, hcx]
  have hpa := ptrC_of hs₁ hbx₁ (show a + 72 ≤ Z by omega) (by decide) (Or.inr (Or.inr rfl))
  have hpb := ptrC_of hs₁ hsi₁ (show b + 72 ≤ Z by omega) (by decide) (Or.inr (Or.inl rfl))
  have hat : ∀ n < 9, Apart (off base a) (0 + 8 * n) 8 base (fnMod true).tmp (8 * n) := fun n hn i hi => by
    rw [show off (off base a) (0 + 8 * n) + BitVec.ofNat 64 i = off base (a + (0 + 8 * n) + i) by
      rw [off_off]; exact Offset.add_add base _ i, ofs_off0 base (by omega), hft, hft']
    omega
  have hbt : Apart (off base b) 0 72 base (fnMod true).tmp 72 :=
    apart_off base (by rw [hft, hft']; omega) (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep_xmm (by rw [List.all_flatMap, List.all_eq_true]; decide) (xRows_ok hs₁.toC hpa hpb (M := fnMod true) (a := 0) (b := 0) (by omega)
    (by omega) (by rw [hft, hft']; omega) hat hbt 8 (Nat.le_refl _))) fun s₂ ⟨⟨k₂, O₂, e₂⟩, x₂⟩ => ?_
  refine WP.mono (mulEpi_ok s₂) fun s₃ ⟨v₃, k₃, m₃, rd₃, wr₃⟩ => ?_
  have hA₁ : wordsVal s₁.mem (off base a) 0 9 = wordsVal s.mem base a 9 := by rw [wordsVal_off, Nat.add_zero, m₁]
  have hB₁ : wordsVal s₁.mem (off base b) 0 9 = wordsVal s.mem base b 9 := by rw [wordsVal_off, Nat.add_zero, m₁]
  have hx : ∀ j, xg s₃ j = xg s₂ j := fun j => by
    simp only [xg]; rw [k₃ _ (fun h => absurd (h ▸ (xAcc_ne j).2.2.2.2) (by decide))]
  refine ⟨?_, ?_, ?_⟩
  · rw [m₃, hval_congr fun j _ _ => hx j, ← hft, e₂, hA₁, hB₁]
  · refine ⟨fun r hr => ?_, by rw [rd₃, k₂.rd, rd₁], by rw [wr₃, k₂.wr, wr₁]⟩
    simp only [List.mem_cons, not_or] at hr
    by_cases hrs : r = .rsi
    · subst hrs; rw [v₃, x₂, x₁]
    · rw [k₃ r hrs, k₂.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.2]), k₁ r hrs]
  · intro x hx'
    rw [m₃, O₂ x (by rw [hft]; exact hx'), m₁]

/-- `vg_p521_mul_adx` (`weak = false`) and `vg_p521_mulw_adx` (`weak`): `[o] = [a] [b] 2⁻⁵⁷⁶ mod p`. -/
theorem mulFnG_ok (weak : Bool) (hZ : 4096 ≤ Z) {s : State} {base : Addr} (hs : Scr s base Z) {a b o m : Nat}
    (hbx : s.gpr .rbx = off base a) (hcx : s.gpr .rcx = off base b) (hso : s.gpr .rsi = BitVec.ofNat 64 o)
    (ha : a + 72 ≤ 3520) (hb : b + 72 ≤ 3520) (ho : o + 72 ≤ 3520)
    (hm : m + 1 = 512 * (2 ^ 64) ^ 8) (hA : wordsVal s.mem base a 9 < m) (hB : wordsVal s.mem base b 9 < m) :
    WP isa (.block (mulRows ++ (redS (!weak) ++ (if weak then exitW else exitS)))) s
      (FnPost m weak base o (wordsVal s.mem base a 9 * wordsVal s.mem base b 9) s) := by
  have hnw := hs.nowrap
  rw [WP.block_append_iff]
  refine WP.mono (mulRows_ok hZ hs hbx hcx ha hb) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ : Scr s₁ base Z := hs.of_keepRegs' k₁ (by decide)
  have hso₁ : s₁.gpr .rsi = BitVec.ofNat 64 o := by rw [k₁.gpr _ (by decide), hso]
  have hle := mul_le_sq (A := wordsVal s.mem base a 9) (B := wordsVal s.mem base b 9) (by omega) (by omega)
  have hl := hval_succ_last (xg s₁) 9 8
  simp only [Nat.reduceAdd] at hl
  have hT : tsum s₁.mem base 0 9 = wordsVal s₁.mem base fnTmp 9 := tsum_eq _ _ _ _
  have hP : tsum s₁.mem base 0 9 + 2 ^ 576 * hval (xg s₁) 9 8 = wordsVal s.mem base a 9 * wordsVal s.mem base b 9 := by
    rw [hT]; omega
  refine WP.mono (redExit_ok hZ hs₁ ho hso₁ hm weak (by rw [hP]; exact hle)) fun s₂ h => ?_
  rw [hP] at h
  exact FnPost.pre (k₁.mono (by decide)) (fun x ht => O₁ x (by simp only [fnTmp] at ht ⊢; omega)) h

theorem mulFn_ok (hZ : 4096 ≤ Z) {s : State} {base : Addr} (hs : Scr s base Z) {a b o m : Nat}
    (hbx : s.gpr .rbx = off base a) (hcx : s.gpr .rcx = off base b) (hso : s.gpr .rsi = BitVec.ofNat 64 o)
    (ha : a + 72 ≤ 3520) (hb : b + 72 ≤ 3520) (ho : o + 72 ≤ 3520)
    (hm : m + 1 = 512 * (2 ^ 64) ^ 8) (hA : wordsVal s.mem base a 9 < m) (hB : wordsVal s.mem base b 9 < m) :
    WP isa mulFn s (FnPost m false base o (wordsVal s.mem base a 9 * wordsVal s.mem base b 9) s) := by
  have h := mulFnG_ok false hZ hs hbx hcx hso ha hb ho hm hA hB
  simp only [Bool.not_false, Bool.false_eq_true, ite_false] at h
  rw [mulFn, List.append_assoc]; exact h

theorem mulFnW_ok (hZ : 4096 ≤ Z) {s : State} {base : Addr} (hs : Scr s base Z) {a b o m : Nat}
    (hbx : s.gpr .rbx = off base a) (hcx : s.gpr .rcx = off base b) (hso : s.gpr .rsi = BitVec.ofNat 64 o)
    (ha : a + 72 ≤ 3520) (hb : b + 72 ≤ 3520) (ho : o + 72 ≤ 3520)
    (hm : m + 1 = 512 * (2 ^ 64) ^ 8) (hA : wordsVal s.mem base a 9 < m) (hB : wordsVal s.mem base b 9 < m) :
    WP isa mulFnW s (FnPost m true base o (wordsVal s.mem base a 9 * wordsVal s.mem base b 9) s) := by
  have h := mulFnG_ok true hZ hs hbx hcx hso ha hb ho hm hA hB
  simp only [Bool.not_true, ite_true] at h
  rw [mulFnW, List.append_assoc]; exact h

end VG.Proof.Weierstrass.X86_64.P521F
