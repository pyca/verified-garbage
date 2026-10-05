import VerifiedGarbage.Proof.Mont.X86_64.WideMul
import VerifiedGarbage.Proof.Mont.X86_64.OpsReg

/-!
# Montgomery arithmetic on x86-64: the operations with the accumulator in memory

For any number of words: chains of additions and subtractions of numbers in
memory into memory, word by word through `r8` (`chainWAdd_ok`,
`chainWSub_ok`), each source either the destination itself or apart from
it (`Near`); the selection under a mask (`selectsW_ok`); the conditional
subtraction (`csubW_ok`); and `mulW_ok`, `addW_ok` and `subW_ok`, which are
`mulR_ok`, `addR_ok` and `subR_ok` for any number of words, given that the
operands and the result are apart from the temporary area.
-/

namespace VG.Proof.Mont.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

/-- The `k` words at `x` are those at `t`, or apart from them. -/
def Near (x t k : Nat) : Prop := x = t ∨ x + 8 * k ≤ t ∨ t + 8 * k ≤ x

theorem Near.succ {x t k : Nat} (h : Near x t (k + 1)) : Near (x + 8) (t + 8) k := by
  unfold Near at h ⊢; omega

/-- Words at `x + 8` on are unchanged by a write to the word at `t`. -/
theorem Near.rest {x t k : Nat} (h : Near x t (k + 1)) : x + 8 + 8 * k ≤ t ∨ t + 8 ≤ x + 8 := by
  unfold Near at h; omega

theorem Near.head {x t k : Nat} (h : Near x t (k + 1)) (hx : x ≠ t) : x + 8 ≤ t ∨ t + 8 ≤ x := by
  unfold Near at h; omega

theorem fresh_r8 : Fresh [.r8] := ⟨by decide, by decide⟩

/-! ## Chains in memory -/

/-- One word of a sum: `[t] + 2⁶⁴ c' = [a] + [b] + c` (`op` is `add`, with no
carry in, or `adc`). -/
theorem addWord_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {op : AluOp}
    {c : Bool} (hop : (op = .add ∧ c = false) ∨ (op = .adc ∧ s.cf = some c)) {t a b : Nat}
    (ht : t + 8 ≤ size) (ha : a + 8 ≤ size) (hb : b + 8 ≤ size) :
    WP isa (.block [.mov .r8 (.mem (sc a)), .alu op .r8 (.mem (sc b)), .store (sc t) .r8]) s fun s' =>
      ∃ c' : Bool, s'.cf = some c' ∧
        (word s'.mem base t).toNat + 2 ^ 64 * c'.toNat =
          (word s.mem base a).toNat + (word s.mem base b).toNat + c.toNat ∧
        KeepRegs [.r8] s s' ∧ s'.mem = s.mem.writeW (off base t) (word s'.mem base t) := by
  rw [show ([.mov .r8 (.mem (sc a)), .alu op .r8 (.mem (sc b)), .store (sc t) .r8] : List Instr) =
    [.mov .r8 (.mem (sc a))] ++ (chain op .adc [.r8] b ++ [.store (sc t) .r8]) from rfl,
    WP.block_append_iff]
  refine WP.mono (movMem_ok hs .r8 ha) fun s₁ ⟨l₁, cf₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have step : WP isa (.block (chain op .adc [.r8] b)) s₁ fun s₂ => ∃ c' : Bool, s₂.cf = some c' ∧
      (s₂.gpr .r8).toNat + 2 ^ 64 * c'.toNat = (s₁.gpr .r8).toNat + (word s₁.mem base b).toNat + c.toNat ∧
      Keeps [.r8] s₁ s₂ := by
    rcases hop with ⟨rfl, rfl⟩ | ⟨rfl, hc⟩
    · refine WP.mono (chainAdd_ok hs₁ (t := .r8) (ts := []) (b := b) (by simp; omega) fresh_r8)
        fun s₂ h => ?_
      obtain ⟨c', c₂, e₂, k₂⟩ := h
      refine ⟨c', c₂, ?_, k₂⟩
      simp only [regsVal, wordsVal, List.length_cons, List.length_nil] at e₂
      simp only [Bool.toNat_false, Nat.add_zero]
      omega
    · refine WP.mono (chainAdc_ok [.r8] hs₁ (by rw [cf₁]; exact hc) (b := b) (by simp; omega) fresh_r8)
        fun s₂ h => ?_
      obtain ⟨c', c₂, e₂, k₂⟩ := h
      refine ⟨c', c₂, ?_, k₂⟩
      simp only [regsVal, wordsVal, List.length_cons, List.length_nil] at e₂
      omega
  rw [WP.block_append_iff]
  refine WP.mono step fun s₂ ⟨c', c₂, e₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  refine WP.mono (storeReg_ok hs₂ .r8 ht) fun s₃ ⟨m₃, _, cf₃, k₃⟩ => ?_
  have hm₂ : s₂.mem = s.mem := by rw [k₂.2.1, k₁.2.1]
  refine ⟨c', by rw [cf₃, c₂], ?_, ((Keeps.regs k₁).trans (Keeps.regs k₂)).trans (k₃.mono (by sub_regs')),
    by rw [m₃, hm₂, word_writeW_self]⟩
  rw [m₃, word_writeW_self, e₂, l₁, k₁.2.1]

/-- One word of a difference: `[t] + [b] + c = [a] + 2⁶⁴ c'` (`op` is `sub`,
with no borrow in, or `sbb`). -/
theorem subWord_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {op : AluOp}
    {c : Bool} (hop : (op = .sub ∧ c = false) ∨ (op = .sbb ∧ s.cf = some c)) {t a b : Nat}
    (ht : t + 8 ≤ size) (ha : a + 8 ≤ size) (hb : b + 8 ≤ size) :
    WP isa (.block [.mov .r8 (.mem (sc a)), .alu op .r8 (.mem (sc b)), .store (sc t) .r8]) s fun s' =>
      ∃ c' : Bool, s'.cf = some c' ∧
        (word s'.mem base t).toNat + (word s.mem base b).toNat + c.toNat =
          (word s.mem base a).toNat + 2 ^ 64 * c'.toNat ∧
        KeepRegs [.r8] s s' ∧ s'.mem = s.mem.writeW (off base t) (word s'.mem base t) := by
  rw [show ([.mov .r8 (.mem (sc a)), .alu op .r8 (.mem (sc b)), .store (sc t) .r8] : List Instr) =
    [.mov .r8 (.mem (sc a))] ++ (chain op .sbb [.r8] b ++ [.store (sc t) .r8]) from rfl,
    WP.block_append_iff]
  refine WP.mono (movMem_ok hs .r8 ha) fun s₁ ⟨l₁, cf₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have step : WP isa (.block (chain op .sbb [.r8] b)) s₁ fun s₂ => ∃ c' : Bool, s₂.cf = some c' ∧
      (s₂.gpr .r8).toNat + (word s₁.mem base b).toNat + c.toNat = (s₁.gpr .r8).toNat + 2 ^ 64 * c'.toNat ∧
      Keeps [.r8] s₁ s₂ := by
    rcases hop with ⟨rfl, rfl⟩ | ⟨rfl, hc⟩
    · refine WP.mono (chainSub_ok hs₁ (t := .r8) (ts := []) (b := b) (by simp; omega) fresh_r8)
        fun s₂ h => ?_
      obtain ⟨c', c₂, e₂, k₂⟩ := h
      refine ⟨c', c₂, ?_, k₂⟩
      simp only [regsVal, wordsVal, List.length_cons, List.length_nil] at e₂
      simp only [Bool.toNat_false, Nat.add_zero]
      omega
    · refine WP.mono (chainSbb_ok [.r8] hs₁ (by rw [cf₁]; exact hc) (b := b) (by simp; omega) fresh_r8)
        fun s₂ h => ?_
      obtain ⟨c', c₂, e₂, k₂⟩ := h
      refine ⟨c', c₂, ?_, k₂⟩
      simp only [regsVal, wordsVal, List.length_cons, List.length_nil] at e₂
      omega
  rw [WP.block_append_iff]
  refine WP.mono step fun s₂ ⟨c', c₂, e₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  refine WP.mono (storeReg_ok hs₂ .r8 ht) fun s₃ ⟨m₃, _, cf₃, k₃⟩ => ?_
  have hm₂ : s₂.mem = s.mem := by rw [k₂.2.1, k₁.2.1]
  refine ⟨c', by rw [cf₃, c₂], ?_, ((Keeps.regs k₁).trans (Keeps.regs k₂)).trans (k₃.mono (by sub_regs')),
    by rw [m₃, hm₂, word_writeW_self]⟩
  rw [m₃, word_writeW_self, ← l₁, ← k₁.2.1]
  exact e₂

/-- `[t] + 2^(64 k) c' = [a] + [b] + c`, `k` words, with the carry `c` in
(`op` is `add`, with no carry in, or `adc`) and `c'` out. -/
theorem chainWAdd_ok {size : Nat} : ∀ (k : Nat) {s : State} {base : Addr} {op : AluOp} {c : Bool}
    {t a b : Nat}, Scr s base size → ((op = .add ∧ c = false) ∨ (op = .adc ∧ s.cf = some c)) →
    0 < k ∨ op = .adc →
    t + 8 * k ≤ size → a + 8 * k ≤ size → b + 8 * k ≤ size → Near a t k → Near b t k →
    WP isa (.block (chainW op .adc k t a b)) s fun s' => ∃ c' : Bool, s'.cf = some c' ∧
      wordsVal s'.mem base t k + 2 ^ (64 * k) * c'.toNat =
        wordsVal s.mem base a k + wordsVal s.mem base b k + c.toNat ∧
      KeepRegs [.r8] s s' ∧ Outside base t (8 * k) s.mem s'.mem
  | 0, s, _, op, c, _, _, _, _, hop, hk, _, _, _, _, _ => by
    have hc : s.cf = some c := by
      rcases hop with ⟨rfl, _⟩ | ⟨_, hc⟩
      · simp at hk
      · exact hc
    exact WP.block_nil ⟨c, hc, by simp [wordsVal], ⟨fun _ _ => rfl, rfl, rfl⟩, Outside.refl _ _ _ _⟩
  | k + 1, s, base, op, c, t, a, b, hs, hop, _, ht, ha, hb, hna, hnb => by
    have hn := hs.nowrap
    rw [chainW, WP.block_append_iff]
    refine WP.mono (addWord_ok hs hop (t := t) (a := a) (b := b) (by omega) (by omega) (by omega))
      fun s₁ ⟨c₁, cf₁, e₁, k₁, m₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    have O₁ : Outside base t 8 s.mem s₁.mem := by rw [m₁]; exact writeW_outside _ _ _ (by omega)
    refine WP.mono (chainWAdd_ok k hs₁ (op := .adc) (.inr ⟨rfl, cf₁⟩) (.inr rfl) (t := t + 8)
      (a := a + 8) (b := b + 8) (by omega) (by omega) (by omega) hna.succ hnb.succ)
      fun s₂ ⟨c₂, cf₂, e₂, k₂, O₂⟩ => ?_
    have hA : wordsVal s₁.mem base (a + 8) k = wordsVal s.mem base (a + 8) k :=
      O₁.wordsVal hna.rest (by omega)
    have hB : wordsVal s₁.mem base (b + 8) k = wordsVal s.mem base (b + 8) k :=
      O₁.wordsVal hnb.rest (by omega)
    have hT : word s₂.mem base t = word s₁.mem base t := O₂.word (by omega) (by omega)
    rw [hA, hB] at e₂
    refine ⟨c₂, cf₂, ?_, k₁.trans k₂, fun x hx => by rw [O₂ x (by omega), O₁ x (by omega)]⟩
    simp only [wordsVal, pow64_succ, hT]
    rw [Nat.mul_assoc]
    omega

/-- `[t] + [b] + c = [a] + 2^(64 k) c'`, `k` words, with the borrow `c` in
(`op` is `sub`, with no borrow in, or `sbb`) and `c'` out. -/
theorem chainWSub_ok {size : Nat} : ∀ (k : Nat) {s : State} {base : Addr} {op : AluOp} {c : Bool}
    {t a b : Nat}, Scr s base size → ((op = .sub ∧ c = false) ∨ (op = .sbb ∧ s.cf = some c)) →
    0 < k ∨ op = .sbb →
    t + 8 * k ≤ size → a + 8 * k ≤ size → b + 8 * k ≤ size → Near a t k → Near b t k →
    WP isa (.block (chainW op .sbb k t a b)) s fun s' => ∃ c' : Bool, s'.cf = some c' ∧
      wordsVal s'.mem base t k + wordsVal s.mem base b k + c.toNat =
        wordsVal s.mem base a k + 2 ^ (64 * k) * c'.toNat ∧
      KeepRegs [.r8] s s' ∧ Outside base t (8 * k) s.mem s'.mem
  | 0, s, _, op, c, _, _, _, _, hop, hk, _, _, _, _, _ => by
    have hc : s.cf = some c := by
      rcases hop with ⟨rfl, _⟩ | ⟨_, hc⟩
      · simp at hk
      · exact hc
    exact WP.block_nil ⟨c, hc, by simp [wordsVal], ⟨fun _ _ => rfl, rfl, rfl⟩, Outside.refl _ _ _ _⟩
  | k + 1, s, base, op, c, t, a, b, hs, hop, _, ht, ha, hb, hna, hnb => by
    have hn := hs.nowrap
    rw [chainW, WP.block_append_iff]
    refine WP.mono (subWord_ok hs hop (t := t) (a := a) (b := b) (by omega) (by omega) (by omega))
      fun s₁ ⟨c₁, cf₁, e₁, k₁, m₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    have O₁ : Outside base t 8 s.mem s₁.mem := by rw [m₁]; exact writeW_outside _ _ _ (by omega)
    refine WP.mono (chainWSub_ok k hs₁ (op := .sbb) (.inr ⟨rfl, cf₁⟩) (.inr rfl) (t := t + 8)
      (a := a + 8) (b := b + 8) (by omega) (by omega) (by omega) hna.succ hnb.succ)
      fun s₂ ⟨c₂, cf₂, e₂, k₂, O₂⟩ => ?_
    have hA : wordsVal s₁.mem base (a + 8) k = wordsVal s.mem base (a + 8) k :=
      O₁.wordsVal hna.rest (by omega)
    have hB : wordsVal s₁.mem base (b + 8) k = wordsVal s.mem base (b + 8) k :=
      O₁.wordsVal hnb.rest (by omega)
    have hT : word s₂.mem base t = word s₁.mem base t := O₂.word (by omega) (by omega)
    rw [hA, hB] at e₂
    refine ⟨c₂, cf₂, ?_, k₁.trans k₂, fun x hx => by rw [O₂ x (by omega), O₁ x (by omega)]⟩
    simp only [wordsVal, pow64_succ, hT]
    rw [Nat.mul_assoc]
    omega

/-! ## The selection and the conditional subtraction -/

theorem select_val' (t d : BitVec 64) (k : Bool) :
    (d ^^^ t) &&& (if k then 0 else BitVec.allOnes 64) ^^^ t = if k then t else d := by
  rw [BitVec.xor_comm _ t]; exact select_val t d k

/-- Each word at `o` replaced by the word at `x` if the mask `rax` is zero
(`k` true), and kept if it is all ones. -/
theorem selectsW_ok {size : Nat} : ∀ (k : Nat) {s : State} {base : Addr} {x o : Nat} (kk : Bool),
    Scr s base size → x + 8 * k ≤ size → o + 8 * k ≤ size → (x + 8 * k ≤ o ∨ o + 8 * k ≤ x) →
    s.gpr .rax = (if kk then 0 else BitVec.allOnes 64) →
    WP isa (.block (selectsW k x o)) s fun s' =>
      wordsVal s'.mem base o k = (if kk then wordsVal s.mem base x k else wordsVal s.mem base o k) ∧
      KeepRegs [.rdx, .r8] s s' ∧ Outside base o (8 * k) s.mem s'.mem
  | 0, s, _, _, _, kk, _, _, _, _, _ => WP.block_nil ⟨by cases kk <;> rfl, ⟨fun _ _ => rfl, rfl, rfl⟩,
      Outside.refl _ _ _ _⟩
  | k + 1, s, base, x, o, kk, hs, hx, ho, hsep, hk => by
    have hn := hs.nowrap
    rw [selectsW, WP.block_append_iff]
    refine WP.mono (show WP isa (.block [.mov .rdx (.mem (sc o)), .mov .r8 (.mem (sc x)),
        .alu .xor .rdx (.reg .r8), .alu .and .rdx (.reg .rax), .alu .xor .rdx (.reg .r8),
        .store (sc o) .rdx]) s (fun s₁ => s₁.mem = s.mem.writeW (off base o)
          (if kk then word s.mem base x else word s.mem base o) ∧ KeepRegs [.rdx, .r8] s s₁) by
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
        Option.map_some, State.load64, State.store64, ea_sc, RegUpd.gpr_setReg,
        RegUpd.gpr_arithFlags, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
        RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.mem_arithFlags, reduceCtorEq, ite_true,
        ite_false, hs.rdi, ld_sc hs (d := o) (by omega), ld_sc hs (d := x) (by omega),
        st_sc hs (d := o) (by omega), hk, Option.some.injEq, exists_eq_left']
      refine ⟨by rw [select_val'], ⟨fun r hr => ?_, rfl, rfl⟩⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]) fun s₁ ⟨m₁, k₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    have O₁ : Outside base o 8 s.mem s₁.mem := by rw [m₁]; exact writeW_outside _ _ _ (by omega)
    refine WP.mono (selectsW_ok k kk hs₁ (x := x + 8) (o := o + 8) (by omega) (by omega) (by omega)
      (by rw [k₁.gpr _ (by decide), hk])) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
    have hX : wordsVal s₁.mem base (x + 8) k = wordsVal s.mem base (x + 8) k :=
      O₁.wordsVal (by omega) (by omega)
    have hO : wordsVal s₁.mem base (o + 8) k = wordsVal s.mem base (o + 8) k :=
      O₁.wordsVal (by omega) (by omega)
    refine ⟨?_, k₁.trans k₂, fun y hy => by rw [O₂ y (by omega), O₁ y (by omega)]⟩
    rw [wordsVal, O₂.word (by omega) (by omega), m₁, word_writeW_self, e₂, hX, hO]
    cases kk <;> simp [wordsVal]

/-- `csubW`: `[tmp] + 2^(64 n) r9 < 2m` reduced modulo `m` into `[o]`. -/
theorem csubW_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {o : Nat}
    (hn : 0 < M.n) (hmo : M.mo + 8 * M.n ≤ size) (htmp : M.tmp + 8 * M.n ≤ size)
    (ho : o + 8 * M.n ≤ size)
    (hoT : o + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ o) (hoM : o + 8 * M.n ≤ M.mo ∨ M.mo + 8 * M.n ≤ o)
    {m : Nat} (hm : wordsVal s.mem base M.mo M.n = m)
    (hV : wordsVal s.mem base M.tmp M.n + 2 ^ (64 * M.n) * (s.gpr .r9).toNat < 2 * m) :
    WP isa (.block (csubW M o)) s fun s' =>
      wordsVal s'.mem base o M.n = (wordsVal s.mem base M.tmp M.n + 2 ^ (64 * M.n) * (s.gpr .r9).toNat) % m ∧
      KeepRegs [.rax, .rdx, .r8] s s' ∧ Outside base o (8 * M.n) s.mem s'.mem := by
  have hnw := hs.nowrap
  have hmX : m < 2 ^ (64 * M.n) := hm ▸ wordsVal_lt _ _ _ _
  rw [csubW, List.append_assoc, WP.block_append_iff]
  refine WP.mono (chainWSub_ok M.n hs (op := .sub) (c := false) (.inl ⟨rfl, rfl⟩) (.inl hn)
    (t := o) (a := M.tmp) (b := M.mo) ho htmp hmo (by unfold Near; omega) (by unfold Near; omega))
    fun s₁ ⟨b, c₁, e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mask_ok s₁ .r9 c₁) fun s₂ ⟨x₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have hr9 : s₁.gpr .r9 = s.gpr .r9 := k₁.gpr .r9 (by decide)
  rw [hr9] at x₂
  refine WP.mono (selectsW_ok M.n (decide ((s.gpr .r9).toNat < b.toNat)) hs₂ (x := M.tmp) (o := o)
    htmp ho (by omega) (by rw [x₂]; simp only [decide_eq_true_eq]))
    fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have hT₂ : wordsVal s₂.mem base M.tmp M.n = wordsVal s.mem base M.tmp M.n := by
    rw [k₂.2.1]; exact O₁.wordsVal (by omega) (by omega)
  have hO₂ : wordsVal s₂.mem base o M.n = wordsVal s₁.mem base o M.n := by rw [k₂.2.1]
  rw [hm] at e₁
  simp only [Bool.toNat_false, Nat.add_zero] at e₁
  refine ⟨?_, (k₁.mono (by sub_regs')).trans (((Keeps.regs k₂).mono (by sub_regs')).trans
    (k₃.mono (by sub_regs'))), fun x hx => by rw [O₃ x hx, k₂.2.1, O₁ x hx]⟩
  rw [e₃, hT₂, hO₂]
  simp only [decide_eq_true_eq]
  exact csub_arith (b := b) hmX (wordsVal_lt _ _ _ _) hV e₁

end VG.Proof.Mont.X86_64
