import VerifiedGarbage.Proof.Mont.X86_64.SqrPX
import VerifiedGarbage.Proof.Mont.X86_64.Chain
import VerifiedGarbage.Impl.Weierstrass.X86_64.Mont
import VerifiedGarbage.Proof.Framework.X86_64.VecKeep

/-!
# P-521's product modulo `p` as a function, with BMI2 and ADX, on x86-64

`mulFnX` (`Impl/Weierstrass/X86_64/Mont.lean`) runs the rows of the inline
product `mulPX` (or of the square `sqrPX`, when `a = b`) with its operands
read through `rbx = ws + a` and `rcx` or `rbx = ws + b` (`PtrC`) and its temporary
area at `fnTmp`, then the reduction and `xCanon` with `rdi` moved to `[o]`
(`mulFnX_ok`). It saves the callee-saved registers it writes in
`xmm0`–`xmm5` and restores them from there, and keeps `o` in
`rsi`, which the product leaves alone (`Mid`): it changes only the registers
`fnClob`, `[o]` and its temporary area, bytes `fnTmp` to 4095 of the working
space. The product reads `[a]` from a copy in the temporary area (`copyW`),
each word before the row that stores over it, as `rdi` addresses it.
-/

namespace VG.Proof.Weierstrass.X86_64.Mont

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Impl.Weierstrass.X86_64.Mont
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono movRdx_ok)

/-! ## Restoring registers -/

/-- `loads ts a`, word by word, for distinct registers other than `rdi`. -/
theorem loads_words {size : Nat} : ∀ (ts : List Reg) {s : State} {base : Addr} {a : Nat},
    Scr s base size → a + 8 * ts.length ≤ size → ts.Nodup → .rdi ∉ ts →
    WP isa (.block (loads ts a)) s fun s' =>
      (∀ i (h : i < ts.length), s'.gpr ts[i] = word s.mem base (a + 8 * i)) ∧ Keeps ts s s'
  | [], s, _, _, _, _, _, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ _ => rfl, rfl, rfl, rfl⟩
  | t :: ts, s, base, a, hs, ha, hd, hdi => by
    have hn := hs.nowrap
    simp only [List.length_cons] at ha
    simp only [List.nodup_cons] at hd
    simp only [List.mem_cons, not_or] at hdi
    rw [loads, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (show WP isa (.block [.mov t (.mem (sc a))]) s fun s' =>
        s'.gpr t = word s.mem base a ∧ Keeps [t] s s' by
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc_sc hs (show a + 8 ≤ size by omega),
        Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self, true_and]
      refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
      simp only [List.mem_singleton] at hr
      simp only [RegUpd.gpr_setReg_of_ne _ _ hr]) fun s₁ ⟨v₁, k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (by simpa using hdi.1)
    refine WP.mono (loads_words ts hs₁ (a := a + 8) (by omega) hd.2 hdi.2) fun s₂ ⟨w₂, k₂⟩ => ?_
    refine ⟨fun i hi => ?_, (k₁.mono fun r hr => ?_).trans (k₂.mono fun r hr => ?_)⟩
    · cases i with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.mul_zero, Nat.add_zero]
        rw [k₂.1 t hd.1, v₁]
      | succ i =>
        simp only [List.getElem_cons_succ, List.length_cons] at hi ⊢
        rw [w₂ i (by omega), k₁.2.1, show a + 8 + 8 * i = a + 8 * (i + 1) by omega]
    · simp only [List.mem_singleton] at hr; exact hr ▸ List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ hr

/-! ## The entry -/

theorem zext_ok (s : State) :
    WP isa (.block zext) s fun s' =>
      (s'.gpr .rsi).toNat = ((s.gpr .rsi).setWidth 32).toNat ∧
      (s'.gpr .rdx).toNat = ((s.gpr .rdx).setWidth 32).toNat ∧
      (s'.gpr .rcx).toNat = ((s.gpr .rcx).setWidth 32).toNat ∧ Keeps [.rsi, .rdx, .rcx] s s' := by
  apply WP.of_runBlock
  simp only [zext, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
    State.setReg32, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg, reduceCtorEq, ite_true,
    ite_false, BitVec.toNat_setWidth]
  refine ⟨by omega, by omega, by omega, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  all_goals rw [RegUpd.gpr_setReg_of_ne _ _ hr.2.2, RegUpd.gpr_setReg_of_ne _ _ hr.2.1,
    RegUpd.gpr_setReg_of_ne _ _ hr.1]

/-- The pointers to the operands, `rbx = ws + a` and `rcx = ws + b`, and ZF
set iff they are the same. -/
theorem ptrs_ok {s : State} {base : Addr} {a b : Nat} (hdi : s.gpr .rdi = base) (ha : (s.gpr .rdx).toNat = a)
    (hb : (s.gpr .rcx).toNat = b) :
    WP isa (.block [.mov .rbx (.reg .rdx), .alu .add .rbx (.reg .rdi), .alu .add .rcx (.reg .rdi),
        .alu .cmp .rbx (.reg .rcx)]) s fun s' =>
      s'.gpr .rbx = off base a ∧ s'.gpr .rcx = off base b ∧ s'.zf = some (decide (a = b)) ∧
        Keeps [.rbx, .rcx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some,
    Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg, reduceCtorEq, ite_true,
    ite_false, RegUpd.gpr_arithFlags, RegUpd.zf_arithFlags]
  have ea : ∀ (v : BitVec 64) (x : Nat), v.toNat = x → v + s.gpr .rdi = off base x := fun v x h => by
    rw [hdi, BitVec.add_comm]; congr 1; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, ← h]; omega
  refine ⟨ea _ _ ha, ea _ _ hb, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [← ha, ← hb]
    have e : s.gpr .rdx + s.gpr .rdi - (s.gpr .rcx + s.gpr .rdi) = s.gpr .rdx - s.gpr .rcx := by bv_omega
    rw [e]
    by_cases h : s.gpr .rdx = s.gpr .rcx
    · simp [h]
    · have h' : s.gpr .rdx - s.gpr .rcx ≠ 0 := fun h0 => h (by bv_omega)
      have h'' : (s.gpr .rdx).toNat ≠ (s.gpr .rcx).toNat := fun h0 => h (BitVec.eq_of_toNat_eq h0)
      simp only [h'', decide_false, beq_eq_false_iff_ne]; exact h'
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_arithFlags, RegUpd.gpr_setReg_of_ne _ _ hr.1, RegUpd.gpr_setReg_of_ne _ _ hr.2]

/-! ## Operands through pointers -/

theorem off_off (base : Addr) (a d : Nat) : off (off base a) d = off base (a + d) :=
  Offset.add_add base a d

theorem wordsVal_off (m : Mem) (base : Addr) (a : Nat) : ∀ d k,
    wordsVal m (off base a) d k = wordsVal m base (a + d) k
  | _, 0 => rfl
  | d, k + 1 => by
    simp only [wordsVal, Mont.word, off_off]
    rw [wordsVal_off m base a (d + 8) k, Nat.add_assoc]

theorem word_off (m : Mem) (base : Addr) (a d : Nat) :
    Mont.word m (off base a) d = Mont.word m base (a + d) := by
  simp only [Mont.word, off_off]

/-- The pointer `ws + a` in `r`, to `size'` bytes within the working space. -/
theorem ptrC_of {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {r : Reg} {a size' : Nat}
    (hr : s.gpr r = off base a) (ha : a + size' ≤ size) (hz : 0 < size') (hreg : r = .rdi ∨ r = .rsi ∨ r = .rbx) :
    PtrC s r (off base a) size' 0 := by
  have hn := hs.nowrap
  refine ⟨by rw [hr, off_off, Nat.add_zero], ⟨_, List.mem_append_right _ hs.wr, fun d hd => ?_⟩, ?_, hreg⟩
  · rw [off_off]; exact Offset.contains_base base (by omega) (by omega)
  · have h64 : a < 2 ^ 64 := by omega
    have : (off base a).toNat = base.toNat + a := by
      simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64]
      exact Nat.mod_eq_of_lt (by omega)
    omega

theorem apart_off (base : Addr) {a n o k : Nat} (h : a + n ≤ o ∨ o + k ≤ a) (hw : a + n ≤ 2 ^ 64) :
    Apart (off base a) 0 n base o k := fun i hi => by
  rw [show off (off base a) 0 + BitVec.ofNat 64 i = off base (a + i) by
    rw [off_off, Nat.add_zero]; exact Offset.add_add base a i, ofs_off0 base (by omega)]
  omega

/-! ## The product and the square -/

/-- What the core of a branch leaves: only the registers of the rows and the
temporary area changed, and the result plus one, `W`, in `xWin 9`, with
`2⁵⁷⁶ (W - 1) = A B + U p`. -/
def Core (m : Nat) (base : Addr) (A B : Nat) (s s' : State) : Prop :=
  KeepRegs (.rax :: .rcx :: .rdx :: xRegs) s s' ∧ Outside base fnTmp 72 s.mem s'.mem ∧
    1 ≤ hval (xg s') 9 9 ∧ hval (xg s') 9 9 ≤ 2 * m ∧
    ∃ U, (2 ^ 64) ^ 9 * (hval (xg s') 9 9 - 1) = A * B + U * m

/-- What a branch leaves: `Core`, but `rbx` changed too. -/
def Mid (m : Nat) (base : Addr) (A B : Nat) (s s' : State) : Prop :=
  KeepRegs (.rax :: .rcx :: .rdx :: .rbx :: xRegs) s s' ∧ Outside base fnTmp 72 s.mem s'.mem ∧
    1 ≤ hval (xg s') 9 9 ∧ hval (xg s') 9 9 ≤ 2 * m ∧
    ∃ U, (2 ^ 64) ^ 9 * (hval (xg s') 9 9 - 1) = A * B + U * m

theorem Core.mid {m : Nat} {base : Addr} {A B : Nat} {s s' : State} (h : Core m base A B s s') :
    Mid m base A B s s' :=
  ⟨⟨fun r hr => h.1.gpr r fun h' => hr (by
      simp only [List.mem_cons] at h' ⊢; rcases h' with h' | h' | h' | h' <;> simp [h']), h.1.rd, h.1.wr⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem fnTmp_val : (fnMod true).tmp = 4024 := rfl

theorem sqrCore_ok {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) (hZ : 4096 ≤ Z) {a m : Nat}
    (hbx : s.gpr .rbx = off base a) (ha : a + 72 ≤ 3520)
    (hm : m + 1 = 512 * (2 ^ 64) ^ 8) (hB : wordsVal s.mem base a 9 < m) :
    WP isa (.block sqrCore) s
      (Core m base (wordsVal s.mem base a 9) (wordsVal s.mem base a 9) s) := by
  have hnw := hs.nowrap
  have hs₁ := hs.toC
  have hp := ptrC_of hs hbx (show a + 72 ≤ Z by omega) (by decide) (Or.inr (Or.inr rfl))
  have hat := apart_off base (show a + 72 ≤ (fnMod true).tmp ∨ _ by rw [fnTmp_val]; omega)
    (show a + 72 ≤ 2 ^ 64 by omega) (k := 72)
  have htmp : (fnMod true).tmp + 72 ≤ Z := by rw [fnTmp_val]; omega
  rw [sqrCore, List.append_assoc, WP.block_append_iff]
  refine WP.mono (sRows_ok hs₁ hp (M := fnMod true) (a := 0) (by omega) htmp hat 7 (by omega))
    fun s₂ ⟨k₂, O₂, e₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have hp₂ := hp.of_keepRegs k₂ (by decide)
  rw [WP.block_append_iff, sDiag, WP.block_append_iff, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (storeXC_ok hs₂ (xAcc 8) (d := (fnMod true).tmp + 64) (by omega))
    fun s₃ ⟨m₃, g₃, cf₃, of₃, rd₃, wr₃⟩ => ?_
  have hs₃ : ScrC s₃ base Z 0 := ⟨by rw [g₃]; exact hs₂.rdi, by rw [wr₃]; exact hs₂.wr, hs₂.nowrap⟩
  have hp₃ : PtrC s₃ .rbx (off base a) 72 0 := hp₂.of_store (by rw [g₃]) rd₃ wr₃
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movZero_ok s₃ (xAcc 17)) fun s₄ ⟨z₄, _, _, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by simpa using (xAcc_ne 17).2.2.2.1.symm)
  have hp₄ := hp₃.of_keeps k₄ (fun t ht => by
    simp only [List.mem_singleton] at ht; exact ht ▸ mem_rowRegs_x (xAcc_ne _).2.2.2.2)
  refine WP.mono (xorRax_ok s₄) fun s₅ ⟨c₅, o₅, k₅⟩ => ?_
  have hs₅ := hs₄.of_keeps k₅ (by decide)
  have hp₅ := hp₄.of_keeps k₅ (by decide)
  have hm₅ : s₅.mem = s₃.mem := k₅.2.1.trans k₄.2.1
  have O₃ : Outside base ((fnMod true).tmp + 64) 8 s₂.mem s₃.mem := by
    rw [m₃]; exact writeW_outside _ _ _ (by omega)
  have hx₅ : ∀ c, 9 ≤ c → c < 17 → xg s₅ c = xg s₂ c := fun c h1 h2 => by
    simp only [xg]
    rw [k₅.1 _ (by simpa using (xAcc_ne c).1), k₄.1 _ (by simpa using (xAcc_ne_of h2 (by omega))), g₃]
  have h17 : xg s₅ 17 = 0 := by
    simp only [xg]; rw [k₅.1 _ (by simpa using (xAcc_ne 17).1), z₄]; rfl
  have hS₅ : hval (sqWord (fnMod true) base s₅) 0 18 =
      wordsVal s₂.mem base (fnMod true).tmp 8 + (2 ^ 64) ^ 8 * hval (xg s₂) 8 9 := by
    have hlo : hval (sqWord (fnMod true) base s₅) 0 8 = wordsVal s₂.mem base (fnMod true).tmp 8 := by
      rw [show (fnMod true).tmp = (fnMod true).tmp + 8 * 0 from rfl, wordsVal_hval]
      exact hval_congr fun c _ h2 => by
        simp only [sqWord, show c ≤ 8 by omega, ↓reduceIte, hm₅]
        exact congrArg BitVec.toNat (O₃.word (by omega) (by omega))
    have h8 : sqWord (fnMod true) base s₅ 8 = xg s₂ 8 := by
      simp only [sqWord, show (8 : Nat) ≤ 8 from Nat.le_refl _, ↓reduceIte, hm₅, m₃, xg]
      rw [show (fnMod true).tmp + 8 * 8 = (fnMod true).tmp + 64 from rfl, word_writeW_self]
    have hhi : hval (sqWord (fnMod true) base s₅) 9 8 = hval (xg s₂) 9 8 :=
      hval_congr fun c h1 h2 => by
        simp only [sqWord, show ¬ c ≤ 8 by omega, ↓reduceIte]
        exact hx₅ c h1 (by omega)
    have h17' : sqWord (fnMod true) base s₅ 17 = 0 := by
      simp only [sqWord, show ¬ (17 ≤ 8) by decide, ↓reduceIte]; exact h17
    rw [hval_add (sqWord (fnMod true) base s₅) 0 8 10, Nat.zero_add, hlo, show (10 : Nat) = 9 + 1 from rfl,
      hval, h8, hval_succ_last, hhi, h17', Nat.mul_zero, Nat.add_zero]
    rw [show hval (xg s₂) 8 9 = xg s₂ 8 + 2 ^ 64 * hval (xg s₂) 9 8 from rfl]
  refine WP.mono (sDiags_ok hs₅ hp₅ (M := fnMod true) (a := 0) htmp (by omega) hat c₅ o₅ 9 (Nat.le_refl _))
    fun s₆ ⟨c₆, o₆, _, _, e₆, _, k₆, O₆⟩ => ?_
  have hs₆ := hs₅.of_keepRegs k₆ (by decide)
  generalize hf : (fun j => (Mont.word s.mem (off base a) (0 + 8 * j)).toNat) = f at e₂
  have hf₅ : sDg (fun j => (Mont.word s₅.mem (off base a) (0 + 8 * j)).toNat) 9 = sDg f 9 :=
    sDg_congr fun j hj => by
      rw [← hf]
      simp only [hm₅, m₃, word_off]
      exact congrArg BitVec.toNat ((writeW_outside _ _ _ (by omega)).word
        (by rw [fnTmp_val]; omega) (by omega) |>.trans
        (O₂.word (by rw [fnTmp_val]; omega) (by omega)))
  have hA : wordsVal s.mem base a 9 = hval f 0 9 := by
    rw [← hf, ← wordsVal_hval s.mem (off base a) 0 0 9, Nat.mul_zero, Nat.add_zero, wordsVal_off, Nat.add_zero]
  have hAl : wordsVal s.mem base a 9 < (2 ^ 64) ^ 9 := by rw [← Nat.pow_mul]; exact wordsVal_lt _ _ _ 9
  rw [hS₅, e₂, hf₅, ← sq_ident, ← hA, show 2 * 9 = 18 from rfl] at e₆
  have hT : hval (sqWord (fnMod true) base s₆) 0 18 =
      wordsVal s₆.mem base (fnMod true).tmp 9 + (2 ^ 64) ^ 9 * hval (xg s₆) 9 9 := by
    have h1 : hval (sqWord (fnMod true) base s₆) 0 9 = wordsVal s₆.mem base (fnMod true).tmp 9 := by
      rw [show (fnMod true).tmp = (fnMod true).tmp + 8 * 0 from rfl, wordsVal_hval]
      exact hval_congr fun c _ h2 => by simp only [sqWord, show c ≤ 8 by omega, ↓reduceIte]
    have h2 : hval (sqWord (fnMod true) base s₆) 9 9 = hval (xg s₆) 9 9 :=
      hval_congr fun c h1 _ => by simp only [sqWord, show ¬ c ≤ 8 by omega, ↓reduceIte]
    rw [show (18 : Nat) = 9 + 9 from rfl, hval_add, Nat.zero_add, h1, h2]
  have e₆' : wordsVal s₆.mem base (fnMod true).tmp 9 + (2 ^ 64) ^ 9 * hval (xg s₆) 9 9 =
      wordsVal s.mem base a 9 * wordsVal s.mem base a 9 := by
    rw [← hT]
    have hAA : wordsVal s.mem base a 9 * wordsVal s.mem base a 9 < (2 ^ 64) ^ 18 := by
      rw [show (18 : Nat) = 9 + 9 from rfl, Nat.pow_add]; exact Nat.mul_lt_mul'' hAl hAl
    have : (2 ^ 64) ^ 18 * (c₆.toNat + o₆.toNat) < (2 ^ 64) ^ 18 * 1 := by omega
    have := Nat.lt_of_mul_lt_mul_left this
    omega
  refine WP.mono (xRed_ok hs₆ (M := fnMod true) (by omega)) fun s₇ ⟨acc, e₇, k₇, O₇⟩ => ?_
  rw [e₆'] at e₇
  have hU : wordsVal s₇.mem base (fnMod true).tmp 9 < (2 ^ 64) ^ 9 := by
    rw [← Nat.pow_mul]; exact wordsVal_lt _ _ _ 9
  obtain ⟨hW1, hW2, eW⟩ := mulP_arith1 hm hAl hB hU e₇.symm
  refine ⟨⟨fun r hr => ?_, ?_, ?_⟩, fun x hx => ?_, hW1, hW2, _, eW⟩
  · have hr' : ∀ k, xAcc k ≠ r := fun k h => hr (h ▸ List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (xAcc_ne k).2.2.2.2)))
    rw [k₇.gpr r hr, k₆.gpr r hr, k₅.1 r (fun h => hr (by simp only [List.mem_singleton] at h; exact h ▸ List.mem_cons_self ..)),
      k₄.1 r (by simpa using (hr' 17).symm), g₃, k₂.gpr r hr]
  · rw [k₇.rd, k₆.rd, k₅.2.2.1, k₄.2.2.1, rd₃, k₂.rd]
  · rw [k₇.wr, k₆.wr, k₅.2.2.2, k₄.2.2.2, wr₃, k₂.wr]
  · have hx' : ofs base x < (fnMod true).tmp ∨ (fnMod true).tmp + 72 ≤ ofs base x := by
      rw [fnTmp_val]; simpa only [fnTmp] using hx
    rw [O₇ x (by omega), O₆ x hx', hm₅, O₃ x (by omega), O₂ x hx']

/-! ## Moves -/

/-- `mov d, r`. -/
theorem movReg_ok (s : State) (d r : Reg) :
    WP isa (.block [.mov d (.reg r)]) s fun s' => s'.gpr d = s.gpr r ∧ Keeps [d] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self, true_and]
  refine ⟨fun q hq => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hq
  simp only [RegUpd.gpr_setReg_of_ne _ _ hq]

/-! ## The middles -/

/-- `mov r, [p + d]` through any register `p = ws + a`. -/
theorem readSrc_ptr {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) {r : Reg} {a d : Nat}
    (hr : s.gpr r = off base a) (h : a + d + 8 ≤ Z) :
    readSrc s (.mem (rcR r 0 d)) = some (Mont.word s.mem base (a + d)) := by
  have hnw := hs.nowrap
  have he : s.ea (rcR r 0 d) = off base (a + d) := by
    simp only [State.ea, rcR, hr, off, BitVec.add_assoc]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
    omega
  show s.load64 (s.ea (rcR r 0 d)) = _
  rw [he, State.load64, ite_eq_left (ld_sc hs (by omega))]

/-- `mov r, [p + d]`. -/
theorem ldPtr_ok {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) (r p : Reg) {a d : Nat}
    (hp : s.gpr p = off base a) (h : a + d + 8 ≤ Z) :
    WP isa (.block [.mov r (.mem (rcR p 0 d))]) s fun s' =>
      s'.gpr r = Mont.word s.mem base (a + d) ∧ Keeps [r] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc_ptr hs hp h, Option.map_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self, true_and]
  refine ⟨fun q hq => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hq
  simp only [RegUpd.gpr_setReg_of_ne _ _ hq]

/-- `copyW k i`: words `i … i + k - 1` of `[a]` into the temporary area. -/
theorem copyW_ok {base : Addr} {Z : Nat} (hZ : 4096 ≤ Z) {a : Nat} (ha : a + 72 ≤ 3520) :
    ∀ (k i : Nat) {s : State}, Scr s base Z → s.gpr .rbx = off base a → i + k ≤ 9 →
      WP isa (.block (copyW k i)) s fun s' =>
        (∀ j, i ≤ j → j < i + k → Mont.word s'.mem base (fnTmp + 8 * j) = Mont.word s.mem base (a + 8 * j)) ∧
        KeepRegs [.rax] s s' ∧ Outside base (fnTmp + 8 * i) (8 * k) s.mem s'.mem
  | 0, _, s, _, _, _ => WP.block_nil ⟨fun _ h1 h2 => absurd h2 (by omega), ⟨fun _ _ => rfl, rfl, rfl⟩,
      Outside.refl _ _ _ _⟩
  | k + 1, i, s, hs, hbx, hk => by
    have hnw := hs.nowrap
    have hft : fnTmp = 4024 := rfl
    rw [copyW, List.cons_append, List.cons_append, List.nil_append, ← List.singleton_append,
      WP.block_append_iff]
    refine WP.mono (ldPtr_ok hs .rax .rbx (d := 8 * i) hbx (by omega)) fun s₁ ⟨v₁, k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (by decide)
    rw [← List.singleton_append, WP.block_append_iff]
    refine WP.mono (storeX_ok hs₁ .rax (d := fnTmp + 8 * i) (by omega)) fun s₂ ⟨m₂, g₂, _, _, rd₂, wr₂⟩ => ?_
    have hs₂ : Scr s₂ base Z := ⟨by rw [g₂]; exact hs₁.rdi, by rw [wr₂]; exact hs₁.wr, hnw⟩
    have hbx₂ : s₂.gpr .rbx = off base a := by rw [g₂, k₁.1 _ (by decide), hbx]
    have O₂ : Outside base (fnTmp + 8 * i) 8 s.mem s₂.mem := by
      rw [m₂, k₁.2.1]; exact writeW_outside _ _ _ (by omega)
    refine WP.mono (copyW_ok hZ ha k (i + 1) hs₂ hbx₂ (by omega)) fun s₃ ⟨w₃, k₃, O₃⟩ => ?_
    refine ⟨fun j h1 h2 => ?_, ⟨fun r hr => ?_, k₃.rd.trans (rd₂.trans k₁.2.2.1),
      k₃.wr.trans (wr₂.trans k₁.2.2.2)⟩, fun x hx => ?_⟩
    · rcases Nat.eq_or_lt_of_le h1 with rfl | h1
      · rw [O₃.word (by omega) (by omega), m₂, word_writeW_self, v₁]
      · rw [w₃ j (by omega) (by omega), O₂.word (by omega) (by omega)]
    · rw [k₃.gpr r hr, g₂, k₁.1 r (by simpa using hr)]
    · rw [O₃ x (by omega), O₂ x (by omega)]

/-- The product: `[a]` copied into the temporary area, `rbx = ws + b`, the
rows, reading `[a]` there, and the reduction. -/
theorem mulX_ok {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) (hZ : 4096 ≤ Z) {a b m : Nat}
    (hbx : s.gpr .rbx = off base a) (hcx : s.gpr .rcx = off base b) (ha : a + 72 ≤ 3520) (hb : b + 72 ≤ 3520)
    (hm : m + 1 = 512 * (2 ^ 64) ^ 8) (hB : wordsVal s.mem base b 9 < m) :
    WP isa (.block mulX) s (Mid m base (wordsVal s.mem base a 9) (wordsVal s.mem base b 9) s) := by
  have hnw := hs.nowrap
  have hft : (fnMod true).tmp = fnTmp := rfl
  have hft' : fnTmp = 4024 := rfl
  rw [mulX, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (copyW_ok hZ ha 9 0 hs hbx (by omega)) fun s₁ ⟨w₁, k₁, O₁⟩ => ?_
  have hs₁ : Scr s₁ base Z := ⟨(k₁.gpr _ (by decide)).trans hs.rdi, k₁.wr ▸ hs.wr, hnw⟩
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movReg_ok s₁ .rbx .rcx) fun s₂ ⟨v₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have hm₂ : s₂.mem = s₁.mem := k₂.2.1
  have hbx₂ : s₂.gpr .rbx = off base b := by rw [v₂, k₁.gpr _ (by decide), hcx]
  have hpa : PtrC s₂ .rdi base Z 0 :=
    ⟨by rw [hs₂.rdi]; simp [off], ⟨_, List.mem_append_right _ hs₂.wr, fun d hd => hs₂.contains hd (by decide)⟩,
      hnw, Or.inl rfl⟩
  have hpb := ptrC_of hs₂ hbx₂ (show b + 72 ≤ Z by omega) (by decide) (Or.inr (Or.inr rfl))
  have hat : ∀ n < 9, Apart base ((fnMod true).tmp + 8 * n) 8 base (fnMod true).tmp (8 * n) := fun n hn i hi => by
    rw [ofs_off base (by rw [hft, hft']; omega)]; omega
  have hbt : Apart (off base b) 0 72 base (fnMod true).tmp 72 :=
    apart_off base (by rw [hft, hft']; omega) (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (xRows_ok hs₂.toC hpa hpb (M := fnMod true) (a := fnTmp) (b := 0) (by rw [hft']; omega)
    (by omega) (by rw [hft, hft']; omega) hat hbt 8 (Nat.le_refl _)) fun s₃ ⟨k₃, O₃, e₃⟩ => ?_
  have hs₃ : ScrC s₃ base Z 0 := hs₂.toC.of_keepRegs k₃ (by decide)
  refine WP.mono (xRed_ok hs₃ (M := fnMod true) (by rw [hft, hft']; omega)) fun s₄ ⟨acc, e₄, k₄, O₄⟩ => ?_
  have hw : ∀ (mm : Mem) (d : Nat), wordsVal mm base d 9 = hval (fun i => (Mont.word mm base (d + 8 * i)).toNat) 0 9 :=
    fun mm d => by rw [← wordsVal_hval mm base d 0 9, Nat.mul_zero, Nat.add_zero]
  have hA₁ : wordsVal s₂.mem base fnTmp 9 = wordsVal s.mem base a 9 := by
    rw [hm₂, hw, hw]
    exact hval_congr fun j _ hj => by rw [w₁ j (by omega) (by omega)]
  have hB₁ : wordsVal s₂.mem (off base b) 0 9 = wordsVal s.mem base b 9 := by
    rw [wordsVal_off, Nat.add_zero, hm₂]
    exact O₁.wordsVal (by rw [hft']; omega) (by omega)
  have e₃' : wordsVal s₃.mem base (fnMod true).tmp 9 + (2 ^ 64) ^ 9 * hval (xg s₃) 9 9 =
      wordsVal s.mem base a 9 * wordsVal s.mem base b 9 := by
    have := e₃; rw [hB₁, hA₁] at this; exact this
  rw [e₃'] at e₄
  have hAl : wordsVal s.mem base a 9 < (2 ^ 64) ^ 9 := by rw [← Nat.pow_mul]; exact wordsVal_lt _ _ _ 9
  have hU : wordsVal s₄.mem base (fnMod true).tmp 9 < (2 ^ 64) ^ 9 := by
    rw [← Nat.pow_mul]; exact wordsVal_lt _ _ _ 9
  obtain ⟨hW1, hW2, eW⟩ := mulP_arith1 hm hAl hB hU e₄.symm
  refine ⟨⟨fun r hr => ?_, by rw [k₄.rd, k₃.rd, k₂.2.2.1, k₁.rd], by rw [k₄.wr, k₃.wr, k₂.2.2.2, k₁.wr]⟩,
    fun x hx => ?_, hW1, hW2, _, eW⟩
  · simp only [List.mem_cons, not_or] at hr
    rw [k₄.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.2]), k₃.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1,
      hr.2.2.2.2]), k₂.1 r (by simpa using hr.2.2.2.1), k₁.gpr r (by simpa using hr.1)]
  · rw [O₄ x (by rw [hft]; simp only [fnTmp] at hx ⊢; omega), O₃ x (by rw [hft]; exact hx), hm₂,
      O₁ x (by simp only [Nat.mul_zero, Nat.add_zero]; exact hx)]

/-- The square. -/
theorem sqrX_ok {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) (hZ : 4096 ≤ Z) {a m : Nat}
    (hbx : s.gpr .rbx = off base a) (ha : a + 72 ≤ 3520)
    (hm : m + 1 = 512 * (2 ^ 64) ^ 8) (hB : wordsVal s.mem base a 9 < m) :
    WP isa (.block sqrX) s (Mid m base (wordsVal s.mem base a 9) (wordsVal s.mem base a 9) s) :=
  WP.mono (sqrCore_ok hs hZ hbx ha hm hB) fun _ h => h.mid

/-! ## The exit -/

theorem storesC_shift (c e : Nat) : ∀ (ts : List Reg) (d : Nat), storesC (c + e) ts (d + e) = storesC c ts d
  | [], _ => rfl
  | t :: ts, d => by
    simp only [storesC]
    rw [show d + e + 8 = d + 8 + e by omega, storesC_shift c e ts (d + 8)]
    congr 2
    simp only [rc, MemOp.mk.injEq, true_and]
    push_cast; omega

theorem xCanon_at (o : Nat) : xCanon 0 0 = xCanon o o := by
  have := storesC_shift 0 o (xWin 9) 0
  simp only [Nat.zero_add] at this
  simp only [xCanon, this]

/-- `op rdi, rsi`. -/
theorem rdiRsi_ok (s : State) (op : AluOp) (hop : op = .add ∨ op = .sub) :
    WP isa (.block [.alu op .rdi (.reg .rsi)]) s fun s' =>
      s'.gpr .rdi = (if op = .add then s.gpr .rdi + s.gpr .rsi else s.gpr .rdi - s.gpr .rsi) ∧
        Keeps [.rdi] s s' := by
  apply WP.of_runBlock
  rcases hop with rfl | rfl <;>
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some,
      Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self, reduceCtorEq, ite_true, ite_false,
      true_and]
    refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]

theorem qword_lo (hi lo : BitVec 64) : qword (hi ++ lo) 0 = lo := by
  ext i h; simp only [qword, BitVec.getElem_extractLsb']; rw [BitVec.getLsbD_append]; simp [h]

/-- `restores`: the callee-saved registers out of `xmm0`–`xmm5`. -/
theorem restores_ok (s : State) :
    WP isa (.block restores) s fun s' =>
      s'.gpr .rbx = qword (s.xmm .xmm0) 0 ∧ s'.gpr .rbp = qword (s.xmm .xmm1) 0 ∧
      s'.gpr .r12 = qword (s.xmm .xmm2) 0 ∧ s'.gpr .r13 = qword (s.xmm .xmm3) 0 ∧
      s'.gpr .r14 = qword (s.xmm .xmm4) 0 ∧ s'.gpr .r15 = qword (s.xmm .xmm5) 0 ∧ Keeps saved s s' := by
  apply WP.of_runBlock
  simp only [restores, runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left',
    RegUpd.xmm_setReg]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  all_goals try (simp only [RegUpd.gpr_setReg, reduceCtorEq, ↓reduceIte]; rfl)
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr.1, RegUpd.gpr_setReg_of_ne _ _ hr.2.1, RegUpd.gpr_setReg_of_ne _ _ hr.2.2.1,
    RegUpd.gpr_setReg_of_ne _ _ hr.2.2.2.1, RegUpd.gpr_setReg_of_ne _ _ hr.2.2.2.2.1,
    RegUpd.gpr_setReg_of_ne _ _ hr.2.2.2.2.2]

/-- The exit, from `o` in `rsi` and `W` in `xWin 9`: `[o] = (W - 1) mod m`,
`rdi = ws`, the saved registers out of `xmm0`–`xmm5`. -/
theorem exit_ok {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) (hZ : 4096 ≤ Z) {o m : Nat}
    (ho : o + 72 ≤ 3520)
    (hso : s.gpr .rsi = BitVec.ofNat 64 o) (hm : m + 1 = 512 * (2 ^ 64) ^ 8)
    (hT1 : 1 ≤ hval (xg s) 9 9) (hT : hval (xg s) 9 9 ≤ 2 * m) :
    WP isa (.block exit) s fun s' =>
      wordsVal s'.mem base o 9 = (hval (xg s) 9 9 - 1) % m ∧
      s'.gpr .rbx = qword (s.xmm .xmm0) 0 ∧ s'.gpr .rbp = qword (s.xmm .xmm1) 0 ∧
      s'.gpr .r12 = qword (s.xmm .xmm2) 0 ∧ s'.gpr .r13 = qword (s.xmm .xmm3) 0 ∧
      s'.gpr .r14 = qword (s.xmm .xmm4) 0 ∧ s'.gpr .r15 = qword (s.xmm .xmm5) 0 ∧
      KeepRegs (.rax :: .rbx :: xRegs) s s' ∧
      ∀ x, (ofs base x < o ∨ o + 72 ≤ ofs base x) → (ofs base x < fnTmp ∨ fnTmp + 72 ≤ ofs base x) →
        s'.mem x = s.mem x := by
  have hnw := hs.nowrap
  have ho64 : o < 2 ^ 64 := by omega
  have hft : fnTmp = 4024 := rfl
  simp only [exit, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.vecKeep (by decide) (rdiRsi_ok s .add (Or.inl rfl))) fun s₁ ⟨⟨d₁, k₁⟩, x₁, _⟩ => ?_
  simp only [ite_true] at d₁
  have hs₁ : ScrC s₁ base Z o := ⟨by rw [d₁, hso, hs.rdi], by rw [k₁.2.2.2]; exact hs.wr, hnw⟩
  have hx₁ : hval (xg s₁) 9 9 = hval (xg s) 9 9 := hval_congr fun c _ _ => by
    simp only [xg]; rw [k₁.1 _ (by simpa using (xAcc_ne c).2.2.2.1)]
  have hc := xCanon_ok hs₁ (o := o) (by omega) hm (by rw [hx₁]; exact hT1) (by rw [hx₁]; exact hT)
  rw [← xCanon_at o] at hc
  rw [WP.block_append_iff]
  refine WP.mono (WP.vecKeep (by decide) hc) fun s₂ ⟨⟨e₂, k₂, O₂⟩, x₂, _⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.vecKeep (by decide) (rdiRsi_ok s₂ .sub (Or.inr rfl))) fun s₃ ⟨⟨d₃, k₃⟩, x₃, _⟩ => ?_
  simp only [reduceCtorEq, ite_false] at d₃
  have rsi₂ : s₂.gpr .rsi = BitVec.ofNat 64 o := by
    rw [k₂.gpr _ (by decide), k₁.1 _ (by decide), hso]
  refine WP.mono (restores_ok s₃) fun s₅ ⟨b₅, p₅, r12₅, r13₅, r14₅, r15₅, k₅⟩ => ?_
  have hxm : s₃.xmm = s.xmm := by rw [x₃, x₂, x₁]
  have hm₃ : s₃.mem = s₂.mem := k₃.2.1
  refine ⟨?_, by rw [b₅, hxm], by rw [p₅, hxm], by rw [r12₅, hxm], by rw [r13₅, hxm], by rw [r14₅, hxm],
    by rw [r15₅, hxm], ⟨fun r hr => ?_, ?_, ?_⟩, fun x hx _ => ?_⟩
  · rw [k₅.2.1, hm₃, e₂, hx₁]
  · have hsv : r ∉ saved := fun h => hr ((show ∀ r ∈ saved, r ∈ Reg.rax :: .rbx :: xRegs by decide) r h)
    simp only [List.mem_cons, not_or] at hr
    by_cases hd : r = .rdi
    · subst hd
      rw [k₅.1 _ hsv, d₃, rsi₂, k₂.gpr _ (by decide), hs₁.rdi, hs.rdi]
      simp only [off]; rw [BitVec.add_sub_cancel]
    · rw [k₅.1 _ hsv, k₃.1 _ (by simpa using hd), k₂.gpr _ (by simp [hr.1, hr.2.2]),
        k₁.1 _ (by simpa using hd)]
  · rw [k₅.2.2.1, k₃.2.2.1, k₂.rd, k₁.2.2.1]
  · rw [k₅.2.2.2, k₃.2.2.2, k₂.wr, k₁.2.2.2]
  · rw [k₅.2.1, hm₃, O₂ x hx, k₁.2.1]

/-! ## Saving the registers -/

/-- The low halves of the offset arguments. -/
abbrev argOf (s : State) (r : Reg) : Nat := ((s.gpr r).setWidth 32).toNat

theorem setXmm_gpr (s : State) (r : XReg) (v : BitVec 128) : (s.setXmm r v).gpr = s.gpr := rfl
theorem setXmm_mem (s : State) (r : XReg) (v : BitVec 128) : (s.setXmm r v).mem = s.mem := rfl
theorem setXmm_rd (s : State) (r : XReg) (v : BitVec 128) : (s.setXmm r v).rd = s.rd := rfl
theorem setXmm_wr (s : State) (r : XReg) (v : BitVec 128) : (s.setXmm r v).wr = s.wr := rfl
theorem setXmm_xmm (s : State) (r r' : XReg) (v : BitVec 128) :
    (s.setXmm r v).xmm r' = if r' = r then v else s.xmm r' := rfl

/-- `saves`: the callee-saved registers in `xmm0`–`xmm5`. -/
theorem saves_ok (s : State) :
    WP isa (.block saves) s fun s' =>
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.xmm .xmm0 = (0 : BitVec 64) ++ s.gpr .rbx ∧ s'.xmm .xmm1 = (0 : BitVec 64) ++ s.gpr .rbp ∧
      s'.xmm .xmm2 = (0 : BitVec 64) ++ s.gpr .r12 ∧ s'.xmm .xmm3 = (0 : BitVec 64) ++ s.gpr .r13 ∧
      s'.xmm .xmm4 = (0 : BitVec 64) ++ s.gpr .r14 ∧ s'.xmm .xmm5 = (0 : BitVec 64) ++ s.gpr .r15 := by
  apply WP.of_runBlock
  simp only [saves, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    Option.some.injEq, exists_eq_left', setXmm_gpr, setXmm_mem, setXmm_rd, setXmm_wr, setXmm_xmm,
    reduceCtorEq, ↓reduceIte]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

theorem entry_ok {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) :
    WP isa (.block (zext ++ setup)) s fun s' =>
      Scr s' base Z ∧ s'.gpr .rbx = off base (argOf s .rdx) ∧ s'.gpr .rcx = off base (argOf s .rcx) ∧
      s'.zf = some (decide (argOf s .rdx = argOf s .rcx)) ∧ s'.gpr .rsi = BitVec.ofNat 64 (argOf s .rsi) ∧
      s'.xmm .xmm0 = (0 : BitVec 64) ++ s.gpr .rbx ∧ s'.xmm .xmm1 = (0 : BitVec 64) ++ s.gpr .rbp ∧
      s'.xmm .xmm2 = (0 : BitVec 64) ++ s.gpr .r12 ∧ s'.xmm .xmm3 = (0 : BitVec 64) ++ s.gpr .r13 ∧
      s'.xmm .xmm4 = (0 : BitVec 64) ++ s.gpr .r14 ∧ s'.xmm .xmm5 = (0 : BitVec 64) ++ s.gpr .r15 ∧
      KeepRegs [.rsi, .rdx, .rcx, .rbx] s s' ∧ s'.mem = s.mem := by
  have hnw := hs.nowrap
  rw [WP.block_append_iff]
  refine WP.mono (zext_ok s) fun s₁ ⟨si₁, dx₁, cx₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [setup, WP.block_append_iff]
  refine WP.mono (saves_ok s₁) fun s₂ ⟨g₂, m₂, rd₂, wr₂, x0, x1, x2, x3, x4, x5⟩ => ?_
  have hs₂ : Scr s₂ base Z := ⟨by rw [g₂]; exact hs₁.rdi, by rw [wr₂]; exact hs₁.wr, hnw⟩
  refine WP.mono (WP.vecKeep (by decide) (ptrs_ok (s := s₂) (a := argOf s .rdx) (b := argOf s .rcx) hs₂.rdi
    (by rw [g₂, dx₁]) (by rw [g₂, cx₁]))) fun s₄ ⟨⟨bx₄, cx₄, zf₄, k₄⟩, xm₄, _⟩ => ?_
  have hk : ∀ r, r ∉ [Reg.rsi, .rdx, .rcx] → s₁.gpr r = s.gpr r := fun r hr => k₁.1 r hr
  refine ⟨hs₂.of_keeps k₄ (by decide), bx₄, cx₄, zf₄, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · rw [k₄.1 _ (by decide), g₂]
    apply BitVec.eq_of_toNat_eq; rw [si₁, BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (Nat.lt_trans (BitVec.isLt _) (by decide))).symm
  · rw [xm₄, x0, hk _ (by decide)]
  · rw [xm₄, x1, hk _ (by decide)]
  · rw [xm₄, x2, hk _ (by decide)]
  · rw [xm₄, x3, hk _ (by decide)]
  · rw [xm₄, x4, hk _ (by decide)]
  · rw [xm₄, x5, hk _ (by decide)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [k₄.1 _ (by simp [hr.2.2.1, hr.2.2.2]), g₂, k₁.1 _ (by simp [hr.1, hr.2.1, hr.2.2.1])]
  · rw [k₄.2.2.1, rd₂, k₁.2.2.1]
  · rw [k₄.2.2.2, wr₂, k₁.2.2.2]
  · rw [k₄.2.1, m₂, k₁.2.1]

/-! ## The function -/

/-- The registers the function changes. -/
def fnClob : List Reg := [.rax, .rcx, .rdx, .rsi, .r8, .r9, .r10, .r11]

theorem not_clob_cases : ∀ r : Reg, r ∉ fnClob → r ∈ saved ∨ r = .rdi ∨ r = .rsp := by
  intro r; cases r <;> decide

/-- What the middle of a function does, between the entry and the exit:
from the pointers to `[a]` and `[b]` in `rbx` and `rcx` and ZF set iff
`a = b`, `Mid`. -/
def MidOk (mid : Prog isa) (m : Nat) : Prop :=
  ∀ (Z : Nat), 4096 ≤ Z → ∀ (s : State) (base : Addr) (a b : Nat), Scr s base Z → s.gpr .rbx = off base a →
    s.gpr .rcx = off base b → s.zf = some (decide (a = b)) → a + 72 ≤ 3520 → b + 72 ≤ 3520 →
    wordsVal s.mem base b 9 < m →
    WP isa mid s (Mid m base (wordsVal s.mem base a 9) (wordsVal s.mem base b 9) s)

/-- `[o] = [a] [b] 2⁻⁵⁷⁶ mod p` for P-521's `p = m`, the offsets the low halves
of `rsi`, `rdx` and `rcx`, by the entry, a middle that computes the product
plus one (`MidOk`) and does not touch the vector registers, and the exit:
the function changes only `fnClob`, `[o]` and its temporary area, bytes
`fnTmp` to 4095. -/
theorem fnShape_ok {mid : Prog isa} (hsc : scalCode mid = true) {s : State} {base : Addr} {Z : Nat}
    (hs : Scr s base Z) (hZ : 4096 ≤ Z) {m : Nat} (hm : m + 1 = 512 * (2 ^ 64) ^ 8) (hmid : MidOk mid m)
    (ho : argOf s .rsi + 72 ≤ 3520) (ha : argOf s .rdx + 72 ≤ 3520) (hb : argOf s .rcx + 72 ≤ 3520)
    (hB : wordsVal s.mem base (argOf s .rcx) 9 < m) :
    WP isa (.seq (.block zext) (.seq (.block setup) (.seq mid (.block exit)))) s fun s' =>
      wordsVal s'.mem base (argOf s .rsi) 9 < m ∧
      wordsVal s'.mem base (argOf s .rsi) 9 * (2 ^ 64) ^ 9 % m =
        wordsVal s.mem base (argOf s .rdx) 9 * wordsVal s.mem base (argOf s .rcx) 9 % m ∧
      KeepRegs fnClob s s' ∧
      ∀ x, (ofs base x < argOf s .rsi ∨ argOf s .rsi + 72 ≤ ofs base x) →
        (ofs base x < fnTmp ∨ 4096 ≤ ofs base x) → s'.mem x = s.mem x := by
  have hnw := hs.nowrap
  have hft : fnTmp = 4024 := rfl
  refine WP.seq (WP.mono (WP.block_append_iff.mp (entry_ok hs)) fun s₀ h₀ => WP.seq (WP.mono h₀
    fun s₁ ⟨hs₁, bx₁, cx₁, zf₁, si₁, x0, x1, x2, x3, x4, x5, k₁, m₁⟩ => ?_))
  generalize hO : argOf s .rsi = o at *
  generalize hA : argOf s .rdx = a at *
  generalize hBb : argOf s .rcx = b at *
  refine WP.seq (WP.mono (WP.vecKeep hsc (hmid Z hZ s₁ base a b hs₁ bx₁ cx₁ zf₁ ha hb (by rw [m₁]; exact hB)))
    fun s₂ ⟨M₂, xm₂, _⟩ => ?_)
  rw [m₁] at M₂
  obtain ⟨k₂, O₂, hW1, hW2, U, eW⟩ := M₂
  have hs₂ : Scr s₂ base Z := ⟨(k₂.gpr _ (by decide)).trans hs₁.rdi, k₂.wr ▸ hs₁.wr, hnw⟩
  have si₂ : s₂.gpr .rsi = BitVec.ofNat 64 o := by rw [k₂.gpr _ (by decide), si₁]
  refine WP.mono (exit_ok hs₂ hZ ho si₂ hm hW1 hW2) fun s₃ ⟨e₃, b₃, p₃, r12₃, r13₃, r14₃, r15₃, k₃, O₃⟩ => ?_
  have hmo : 0 < m := by omega
  refine ⟨by rw [e₃]; exact Nat.mod_lt _ hmo, by rw [e₃, Nat.mod_mul_mod, Nat.mul_comm, eW, Nat.add_mul_mod_self_right],
    ⟨fun r hr => ?_, by rw [k₃.rd, k₂.rd, k₁.rd], by rw [k₃.wr, k₂.wr, k₁.wr]⟩, fun x hx hx' => ?_⟩
  · rcases not_clob_cases r hr with hsv | rfl | rfl
    · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hsv
      rcases hsv with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [b₃, xm₂, x0, qword_lo]
      · rw [p₃, xm₂, x1, qword_lo]
      · rw [r12₃, xm₂, x2, qword_lo]
      · rw [r13₃, xm₂, x3, qword_lo]
      · rw [r14₃, xm₂, x4, qword_lo]
      · rw [r15₃, xm₂, x5, qword_lo]
    · rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide), k₁.gpr _ (by decide)]
    · rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide), k₁.gpr _ (by decide)]
  · rw [O₃ x hx (by rw [hft] at hx' ⊢; omega), O₂ x (by rw [hft] at hx' ⊢; omega), m₁]

/-- The middle of `mulFnX`: the product or the square, by rows. -/
theorem midX_ok {m : Nat} (hm : m + 1 = 512 * (2 ^ 64) ^ 8) :
    MidOk (.ite .e (.block sqrX) (.block mulX)) m := by
  intro Z hZ s base a b hs bx cx zf ha hb hB
  refine WP.ite (decide (a = b)) zf (fun h => ?_) (fun _ => mulX_ok hs hZ bx cx ha hb hm hB)
  have hab : a = b := of_decide_eq_true h
  subst hab
  exact sqrX_ok hs hZ bx ha hm hB

/-- `[o] = [a] [b] 2⁻⁵⁷⁶ mod p` for P-521's `p = m`, with BMI2 and ADX. -/
theorem mulFnX_ok {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) (hZ : 4096 ≤ Z) {m : Nat}
    (hm : m + 1 = 512 * (2 ^ 64) ^ 8) (ho : argOf s .rsi + 72 ≤ 3520) (ha : argOf s .rdx + 72 ≤ 3520)
    (hb : argOf s .rcx + 72 ≤ 3520) (hB : wordsVal s.mem base (argOf s .rcx) 9 < m) :
    WP isa mulFnX s fun s' =>
      wordsVal s'.mem base (argOf s .rsi) 9 < m ∧
      wordsVal s'.mem base (argOf s .rsi) 9 * (2 ^ 64) ^ 9 % m =
        wordsVal s.mem base (argOf s .rdx) 9 * wordsVal s.mem base (argOf s .rcx) 9 % m ∧
      KeepRegs fnClob s s' ∧
      ∀ x, (ofs base x < argOf s .rsi ∨ argOf s .rsi + 72 ≤ ofs base x) →
        (ofs base x < fnTmp ∨ 4096 ≤ ofs base x) → s'.mem x = s.mem x :=
  fnShape_ok (by decide +kernel) hs hZ hm (midX_ok hm) ho ha hb hB

end VG.Proof.Weierstrass.X86_64.Mont
