import VerifiedGarbage.Proof.Mont.X86_64.Rounds

/-!
# Montgomery arithmetic on x86-64: the conditional subtraction

`csub M ts top` reduces `V = ts + 2^(64 n) top < 2m` below `m`
(`csub_ok`, in `CsubS.lean` with P-384's `csubS`). Up to four words use the
register-only `csubC`; larger register accumulators use `csubM`, computing the difference in the
temporary area (`diffs`) and selecting it with conditional moves
(`selects`). Both use the final borrow directly. The mask lemmas also
serve the memory-backed reduction for wider moduli.
-/

namespace VG.Proof.Mont.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono se0 sub_borrow sbb_borrow toNat_ofBool)

/-- The registers but `rs` and the regions are unchanged (memory may change). -/
structure KeepRegs (rs : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ rs → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem KeepRegs.trans {rs : List Reg} {s₁ s₂ s₃ : State} (h₁ : KeepRegs rs s₁ s₂)
    (h₂ : KeepRegs rs s₂ s₃) : KeepRegs rs s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

theorem KeepRegs.mono {rs rs' : List Reg} {s s' : State} (h : KeepRegs rs s s')
    (hs : ∀ r ∈ rs, r ∈ rs') : KeepRegs rs' s s' :=
  ⟨fun r hr => h.gpr r fun h' => hr (hs r h'), h.rd, h.wr⟩

theorem Keeps.regs {rs : List Reg} {s s' : State} (h : Keeps rs s s') : KeepRegs rs s s' :=
  ⟨h.1, h.2.2.1, h.2.2.2⟩

theorem Scr.of_keepRegs {rs : List Reg} {s s' : State} {base : Addr} {size : Nat}
    (hs : Scr s base size) (h : KeepRegs rs s s') (hr : .rdi ∉ rs) : Scr s' base size :=
  ⟨(h.gpr _ hr).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

/-! ## The differences -/

/-- One word of the difference: `[tmp] = t - [mo] - c` (`op` is `sub`, with
no borrow in, or `sbb`). -/
theorem diff1_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (t : Reg)
    {op : AluOp} {c : Bool}
    (hop : (op = .sub ∧ c = false) ∨ (op = .sbb ∧ s.cf = some c)) {mo tmp : Nat}
    (hmo : mo + 8 ≤ size) (htmp : tmp + 8 ≤ size) :
    WP isa (.block [.mov .rax (.reg t), .alu op .rax (.mem (sc mo)), .store (sc tmp) .rax]) s
      fun s' => (word s'.mem base tmp).toNat + (word s.mem base mo).toNat + c.toNat =
          (s.gpr t).toNat + 2 ^ 64 * (decide ((s.gpr t).toNat < (word s.mem base mo).toNat +
            c.toNat)).toNat ∧
        s'.cf = some (decide ((s.gpr t).toNat < (word s.mem base mo).toNat + c.toNat)) ∧
        KeepRegs [.rax] s s' ∧ s'.mem = s.mem.writeW (off base tmp) (word s'.mem base tmp) := by
  rcases hop with ⟨rfl, rfl⟩ | ⟨rfl, hc⟩
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.map_some,
      Option.bind_some, State.load64, State.store64, ea_sc, RegUpd.gpr_setReg,
      RegUpd.gpr_arithFlags, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
      RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.mem_arithFlags, reduceCtorEq, ite_true,
      ite_false, hs.rdi, ld_sc hs hmo, st_sc hs htmp]
    simp only [Option.some.injEq, exists_eq_left', RegUpd.cf_setReg, RegUpd.cf_arithFlags,
      word_writeW_self, Bool.toNat_false, Nat.add_zero]
    refine ⟨sub_borrow _ _, trivial, ⟨fun r hr => ?_, rfl, rfl⟩, trivial⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.map_some,
      Option.bind_some, State.load64, State.store64, ea_sc, RegUpd.gpr_setReg,
      RegUpd.gpr_arithFlags, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
      RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.mem_arithFlags, reduceCtorEq, ite_true,
      ite_false, hs.rdi, ld_sc hs hmo, st_sc hs htmp, RegUpd.cf_setReg, hc]
    simp only [Option.some.injEq, exists_eq_left', RegUpd.cf_arithFlags, word_writeW_self]
    refine ⟨?_, trivial, ⟨fun r hr => ?_, rfl, rfl⟩, trivial⟩
    · have := sbb_borrow (s.gpr t) (word s.mem base mo) c
      omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- The difference of the words `ts` and the words at `mo`, with the borrow
`c` in, into the words at `tmp`, and its borrow out. -/
theorem diffsSbb_ok {size : Nat} : ∀ (ts : List Reg) {s : State} {base : Addr} {c : Bool}
    {mo tmp : Nat}, Scr s base size → s.cf = some c → mo + 8 * ts.length ≤ size →
    tmp + 8 * ts.length ≤ size → (mo + 8 * ts.length ≤ tmp ∨ tmp + 8 * ts.length ≤ mo) → Fresh ts →
    WP isa (.block (diffs .sbb ts mo tmp)) s fun s' => ∃ b : Bool, s'.cf = some b ∧
      wordsVal s'.mem base tmp ts.length + wordsVal s.mem base mo ts.length + c.toNat =
        regsVal s ts + 2 ^ (64 * ts.length) * b.toNat ∧
      KeepRegs [.rax] s s' ∧ Outside base tmp (8 * ts.length) s.mem s'.mem
  | [], s, _, c, _, _, _, hc, _, _, _, _ => WP.block_nil ⟨c, hc, by simp [wordsVal, regsVal],
      ⟨fun _ _ => rfl, rfl, rfl⟩, Outside.refl _ _ _ _⟩
  | t :: ts, s, base, c, mo, tmp, hs, hc, hmo, htmp, hsep, hf => by
    have hn := hs.nowrap
    simp only [List.length_cons] at hmo htmp hsep
    rw [diffs, WP.block_append_iff]
    refine WP.mono (diff1_ok hs t (.inr ⟨rfl, hc⟩) (mo := mo) (tmp := tmp) (by omega) (by omega))
      fun s₁ ⟨e₁, c₁, k₁, m₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    have O₁ : Outside base tmp 8 s.mem s₁.mem := by
      rw [m₁]; exact writeW_outside _ _ _ (by omega)
    refine WP.mono (diffsSbb_ok ts hs₁ c₁ (mo := mo + 8) (tmp := tmp + 8) (by omega) (by omega)
      (by omega) hf.tail) fun s₂ ⟨b, c₂, e₂, k₂, O₂⟩ => ?_
    have hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.gpr q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; exact (hf.tail.2 q hq).1)
    have hM : wordsVal s₁.mem base (mo + 8) ts.length = wordsVal s.mem base (mo + 8) ts.length :=
      O₁.wordsVal (by omega) (by omega)
    have hT : word s₂.mem base tmp = word s₁.mem base tmp := O₂.word (by omega) (by omega)
    rw [hR, hM] at e₂
    refine ⟨b, c₂, ?_, k₁.trans k₂, fun x hx => ?_⟩
    · simp only [wordsVal, regsVal, List.length_cons, pow64_succ, hT]
      rw [Nat.mul_assoc]
      omega
    · simp only [List.length_cons] at hx
      rw [O₂ x (by omega), O₁ x (by omega)]

/-- The difference of the words `ts` and the words at `mo` into the words at
`tmp`, and its borrow. -/
theorem diffs_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {t : Reg}
    {ts : List Reg} {mo tmp : Nat} (hmo : mo + 8 * (t :: ts).length ≤ size)
    (htmp : tmp + 8 * (t :: ts).length ≤ size)
    (hsep : mo + 8 * (t :: ts).length ≤ tmp ∨ tmp + 8 * (t :: ts).length ≤ mo)
    (hf : Fresh (t :: ts)) :
    WP isa (.block (diffs .sub (t :: ts) mo tmp)) s fun s' => ∃ b : Bool, s'.cf = some b ∧
      wordsVal s'.mem base tmp (t :: ts).length + wordsVal s.mem base mo (t :: ts).length =
        regsVal s (t :: ts) + 2 ^ (64 * (t :: ts).length) * b.toNat ∧
      KeepRegs [.rax] s s' ∧ Outside base tmp (8 * (t :: ts).length) s.mem s'.mem := by
  have hn := hs.nowrap
  simp only [List.length_cons] at hmo htmp hsep ⊢
  rw [diffs, WP.block_append_iff]
  refine WP.mono (diff1_ok hs t (.inl ⟨rfl, rfl⟩) (mo := mo) (tmp := tmp) (by omega) (by omega))
    fun s₁ ⟨e₁, c₁, k₁, m₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  have O₁ : Outside base tmp 8 s.mem s₁.mem := by
    rw [m₁]; exact writeW_outside _ _ _ (by omega)
  refine WP.mono (diffsSbb_ok ts hs₁ c₁ (mo := mo + 8) (tmp := tmp + 8) (by omega) (by omega)
    (by omega) hf.tail) fun s₂ ⟨b, c₂, e₂, k₂, O₂⟩ => ?_
  have hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.gpr q (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; exact (hf.tail.2 q hq).1)
  have hM : wordsVal s₁.mem base (mo + 8) ts.length = wordsVal s.mem base (mo + 8) ts.length :=
    O₁.wordsVal (by omega) (by omega)
  have hT : word s₂.mem base tmp = word s₁.mem base tmp := O₂.word (by omega) (by omega)
  rw [hR, hM] at e₂
  refine ⟨b, c₂, ?_, k₁.trans k₂, fun x hx => ?_⟩
  · simp only [wordsVal, regsVal, pow64_succ, hT]
    simp only [Bool.toNat_false, Nat.add_zero] at e₁ e₂ ⊢
    rw [Nat.mul_assoc]
    omega
  · rw [O₂ x (by omega), O₁ x (by omega)]

/-! ## The mask and the selection -/

theorem mask_val (x : BitVec 64) (c : Bool) :
    (x - x - (BitVec.ofBool c).setWidth 64) ^^^ BitVec.signExtend 64 (-1 : BitVec 32) =
      if c then 0 else BitVec.allOnes 64 := by
  cases c <;> simp

/-- The top word less the borrow `b`, and its borrow as a mask: all ones if
it does not borrow. -/
theorem mask_ok (s : State) (top : Reg) {b : Bool} (hb : s.cf = some b) :
    WP isa (.block [.mov .rax (.reg top), .alu .sbb .rax (.imm 0), .alu .sbb .rax (.reg .rax),
      .alu .xor .rax (.imm (-1))]) s fun s' =>
      s'.gpr .rax = (if (s.gpr top).toNat < b.toNat then 0 else BitVec.allOnes 64) ∧
      Keeps [.rax] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.map_some,
    Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_setReg,
    RegUpd.cf_arithFlags, ite_true, hb, Option.some.injEq, exists_eq_left', se0]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [mask_val]
    have h0 : (0 : BitVec 64).toNat = 0 := rfl
    simp only [h0, Nat.zero_add, decide_eq_true_eq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem select_val (t d : BitVec 64) (k : Bool) :
    t ^^^ ((d ^^^ t) &&& (if k then 0 else BitVec.allOnes 64)) = if k then t else d := by
  cases k
  · simp only [Bool.false_eq_true, ite_false]
    rw [BitVec.and_allOnes, BitVec.xor_comm d t, ← BitVec.xor_assoc, BitVec.xor_self,
      BitVec.zero_xor]
  · simp

/-- Select the temporary word when CF is clear, without changing flags. -/
theorem cmovWord_ok {s : State} {base : Addr} {size tmp : Nat}
    (hs : Scr s base size) (htmp : tmp + 8 ≤ size) (t : Reg) (k : Bool)
    (hk : s.cf = some k) :
    WP isa (.block [.cmov .ae t (.mem (sc tmp))]) s fun s' =>
      s'.gpr t = (if k then s.gpr t else word s.mem base tmp) ∧
      s'.cf = some k ∧ Keeps [t] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execCmov, readSrc,
    load_sc hs htmp, eval, hk, Option.bind_some, Option.map_some]
  cases k <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true,
    ite_false, ite_true, Option.some.injEq, exists_eq_left']
  · refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
    · simp only [RegUpd.gpr_setReg_self]
    · simpa only [RegUpd.cf_setReg] using hk
    · simp only [List.mem_singleton] at hr
      simp only [RegUpd.gpr_setReg, hr, ite_false]
  · exact ⟨trivial, hk, fun _ _ => rfl, rfl, rfl, rfl⟩

/-- Select the reduced words if the full subtraction did not borrow. -/
theorem selects_ok {size : Nat} : ∀ (ts : List Reg) {s : State} {base : Addr} {tmp : Nat} (k : Bool),
    Scr s base size → tmp + 8 * ts.length ≤ size → Fresh ts → s.cf = some k →
    WP isa (.block (selects ts tmp)) s fun s' =>
      regsVal s' ts = (if k then regsVal s ts else wordsVal s.mem base tmp ts.length) ∧
      Keeps (.rdx :: ts) s s'
  | [], s, _, _, k, _, _, _, _ => WP.block_nil ⟨by cases k <;> rfl, fun _ _ => rfl, rfl, rfl, rfl⟩
  | t :: ts, s, base, tmp, k, hs, htmp, hf, hk => by
    obtain ⟨htn, hta, -, htd, -, -⟩ := hf.head
    simp only [List.length_cons] at htmp
    rw [selects, WP.block_append_iff]
    refine WP.mono (cmovWord_ok hs (tmp := tmp) (by omega) t k hk) fun s₁ ⟨e₁, c₁, k₁'⟩ => ?_
    have k₁ : Keeps [.rdx, t] s s₁ := k₁'.mono (by sub_regs)
    have hs₁ := hs.of_keeps k₁ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨by decide, fun h => hf.head.2.2.2.2.2 h.symm⟩)
    refine WP.mono (selects_ok ts k hs₁ (tmp := tmp + 8) (by omega) hf.tail c₁) fun s₂ ⟨e₂, k₂⟩ => ?_
    have hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.1 q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨(hf.tail.2 q hq).2.2.1, fun h => htn (h ▸ hq)⟩)
    have ht₂ : s₂.gpr t = s₁.gpr t := k₂.1 t (by simp [htn, htd])
    refine ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
    rw [regsVal, ht₂, e₁, e₂, hR, k₁.2.1]
    cases k <;> rfl

/-- The top word less the incoming borrow sets the full subtraction's borrow. -/
theorem topBorrow_ok (s : State) (top : Reg) {b : Bool} (hb : s.cf = some b) :
    WP isa (.block [.mov .rax (.reg top), .alu .sbb .rax (.imm 0)]) s fun s' =>
      s'.cf = some (decide ((s.gpr top).toNat < b.toNat)) ∧ Keeps [.rax] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.map_some,
    Option.bind_some, RegUpd.gpr_setReg, RegUpd.cf_setReg,
    RegUpd.cf_arithFlags, ite_true, hb, Option.some.injEq, exists_eq_left', se0]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have h0 : (0 : BitVec 64).toNat = 0 := rfl
    simp only [h0, Nat.zero_add]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-! ## The conditional subtraction -/

/-- `csubM`: `ts + 2^(64 n) top < 2m` reduced modulo `m`. -/
theorem csubM_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod}
    {ts : List Reg} {top : Reg} (hlen : ts.length = M.n) (hn : 0 < M.n) (hf : Fresh (top :: ts))
    (hmo : M.mo + 8 * M.n ≤ size) (htmp : M.tmp + 8 * M.n ≤ size)
    (hsep : M.mo + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ M.mo) {m : Nat}
    (hm : wordsVal s.mem base M.mo M.n = m)
    (hV : regsVal s ts + 2 ^ (64 * M.n) * (s.gpr top).toNat < 2 * m) :
    WP isa (.block (csubM M ts top)) s fun s' =>
      regsVal s' ts = (regsVal s ts + 2 ^ (64 * M.n) * (s.gpr top).toNat) % m ∧
      KeepRegs (.rax :: .rdx :: ts) s s' ∧ Outside base M.tmp (8 * M.n) s.mem s'.mem := by
  obtain ⟨t, ts', rfl⟩ : ∃ t ts', ts = t :: ts' := by
    cases ts with
    | nil => simp at hlen; omega
    | cons t ts' => exact ⟨t, ts', rfl⟩
  have hft := hf.tail
  have htop := hf.head
  have hmX : m < 2 ^ (64 * M.n) := hm ▸ wordsVal_lt _ _ _ _
  rw [csubM, List.append_assoc, WP.block_append_iff]
  refine WP.mono (diffs_ok hs (mo := M.mo) (tmp := M.tmp) (by rw [hlen]; omega) (by rw [hlen]; omega)
    (by rw [hlen]; omega) hft) fun s₁ ⟨b, c₁, e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (topBorrow_ok s₁ top c₁) fun s₂ ⟨x₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have htop₁ : s₁.gpr top = s.gpr top := k₁.gpr top (by simp [htop.2.1])
  rw [htop₁] at x₂
  refine WP.mono (selects_ok _ (decide ((s.gpr top).toNat < b.toNat)) hs₂ (tmp := M.tmp)
    (by rw [hlen]; omega) hft x₂)
    fun s₃ ⟨e₃, k₃⟩ => ?_
  have hR₂ : regsVal s₂ (t :: ts') = regsVal s (t :: ts') := by
    rw [regsVal_congr fun q hq => k₂.1 q (by simp [(hft.2 q hq).1])]
    exact regsVal_congr fun q hq => k₁.gpr q (by simp [(hft.2 q hq).1])
  rw [hlen] at e₁ e₃
  rw [hm] at e₁
  rw [k₂.2.1] at e₃
  refine ⟨?_, (k₁.mono (by sub_regs)).trans (((Keeps.regs k₂).mono (by sub_regs)).trans
    ((Keeps.regs k₃).mono (by sub_regs))), fun x hx => ?_⟩
  · rw [e₃, hR₂]
    simp only [decide_eq_true_eq]
    exact csub_arith (b := b) hmX (wordsVal_lt _ _ _ _) hV e₁
  · rw [k₃.2.1, k₂.2.1, O₁ x (by rw [hlen]; exact hx)]

/-! ## In registers, with `cmov` -/

/-- One word of the difference in a register: `d = t - [mo] - c` (`op` is
`sub`, with no borrow in, or `sbb`). -/
theorem diffC1_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (t d : Reg)
    (hd : d ≠ .rdi) {op : AluOp} {c : Bool}
    (hop : (op = .sub ∧ c = false) ∨ (op = .sbb ∧ s.cf = some c)) {mo : Nat} (hmo : mo + 8 ≤ size) :
    WP isa (.block [.mov d (.reg t), .alu op d (.mem (sc mo))]) s
      fun s' => (s'.gpr d).toNat + (word s.mem base mo).toNat + c.toNat =
          (s.gpr t).toNat + 2 ^ 64 * (decide ((s.gpr t).toNat < (word s.mem base mo).toNat +
            c.toNat)).toNat ∧
        s'.cf = some (decide ((s.gpr t).toNat < (word s.mem base mo).toNat + c.toNat)) ∧
        Keeps [d] s s' := by
  have hd' : Reg.rdi ≠ d := Ne.symm hd
  rcases hop with ⟨rfl, rfl⟩ | ⟨rfl, hc⟩
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.map_some,
      Option.bind_some, State.load64, ea_sc, RegUpd.gpr_setReg, RegUpd.mem_setReg,
      RegUpd.rd_setReg, RegUpd.wr_setReg, hd', ite_true, ite_false, hs.rdi, ld_sc hs hmo]
    simp only [Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self, RegUpd.cf_setReg,
      RegUpd.cf_arithFlags, Bool.toNat_false, Nat.add_zero]
    refine ⟨sub_borrow _ _, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.map_some,
      Option.bind_some, State.load64, ea_sc, RegUpd.gpr_setReg, RegUpd.mem_setReg,
      RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.cf_setReg, hd', ite_true, ite_false, hs.rdi, ld_sc hs hmo, hc]
    simp only [Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self, RegUpd.cf_setReg,
      RegUpd.cf_arithFlags]
    refine ⟨?_, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
    · have := sbb_borrow (s.gpr t) (word s.mem base mo) c
      omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- The difference of the words `ts` and the words at `mo`, with the borrow
`c` in, into the registers `ds`, and its borrow out. -/
theorem diffsCSbb_ok {size : Nat} : ∀ (ts ds : List Reg) {s : State} {base : Addr} {c : Bool}
    {mo : Nat}, Scr s base size → s.cf = some c → ds.length = ts.length →
    mo + 8 * ts.length ≤ size → (∀ d ∈ ds, d ∉ ts ∧ d ≠ .rdi) → ds.Nodup →
    WP isa (.block (diffsC .sbb ts ds mo)) s fun s' => ∃ b : Bool, s'.cf = some b ∧
      regsVal s' ds + wordsVal s.mem base mo ts.length + c.toNat =
        regsVal s ts + 2 ^ (64 * ts.length) * b.toNat ∧ Keeps ds s s'
  | [], [], s, _, c, _, _, hc, _, _, _, _ => WP.block_nil ⟨c, hc, by simp [wordsVal, regsVal],
      fun _ _ => rfl, rfl, rfl, rfl⟩
  | [], _ :: _, _, _, _, _, _, _, hl, _, _, _ => by simp at hl
  | _ :: _, [], _, _, _, _, _, _, hl, _, _, _ => by simp at hl
  | t :: ts, d :: ds, s, base, c, mo, hs, hc, hl, hmo, hd, hnd => by
    have hn := hs.nowrap
    simp only [List.length_cons] at hmo hl
    have hd₀ := hd d (List.mem_cons_self ..)
    have hds : ∀ q ∈ ds, q ∉ ts ∧ q ≠ .rdi := fun q hq => by
      have := hd q (List.mem_cons_of_mem _ hq)
      exact ⟨fun h => this.1 (List.mem_cons_of_mem _ h), this.2⟩
    rw [diffsC, WP.block_append_iff]
    refine WP.mono (diffC1_ok hs t d hd₀.2 (.inr ⟨rfl, hc⟩) (mo := mo) (by omega))
      fun s₁ ⟨e₁, c₁, k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (by simp [hd₀.2.symm])
    refine WP.mono (diffsCSbb_ok ts ds hs₁ c₁ (mo := mo + 8) (by omega) (by omega) hds
      (List.nodup_cons.mp hnd).2) fun s₂ ⟨b, c₂, e₂, k₂⟩ => ?_
    have hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.1 q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact fun h => hd₀.1 (h ▸ List.mem_cons_of_mem _ hq))
    have hD : s₂.gpr d = s₁.gpr d := k₂.1 d (List.nodup_cons.mp hnd).1
    rw [hR, k₁.2.1] at e₂
    refine ⟨b, c₂, ?_, k₁.mono (by simp) |>.trans (k₂.mono (by
      intro q hq; exact List.mem_cons_of_mem _ hq))⟩
    simp only [wordsVal, regsVal, List.length_cons, pow64_succ, hD]
    rw [Nat.mul_assoc]
    omega

/-- The difference of the words `ts` and the words at `mo` into the
registers `ds`, and its borrow. -/
theorem diffsC_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {t d : Reg}
    {ts ds : List Reg} {mo : Nat} (hl : ds.length = ts.length) (hmo : mo + 8 * (t :: ts).length ≤ size)
    (hd : ∀ q ∈ d :: ds, q ∉ t :: ts ∧ q ≠ .rdi) (hnd : (d :: ds).Nodup) :
    WP isa (.block (diffsC .sub (t :: ts) (d :: ds) mo)) s fun s' => ∃ b : Bool, s'.cf = some b ∧
      regsVal s' (d :: ds) + wordsVal s.mem base mo (t :: ts).length =
        regsVal s (t :: ts) + 2 ^ (64 * (t :: ts).length) * b.toNat ∧ Keeps (d :: ds) s s' := by
  have hn := hs.nowrap
  simp only [List.length_cons] at hmo ⊢
  have hd₀ := hd d (List.mem_cons_self ..)
  have hds : ∀ q ∈ ds, q ∉ ts ∧ q ≠ .rdi := fun q hq => by
    have := hd q (List.mem_cons_of_mem _ hq)
    exact ⟨fun h => this.1 (List.mem_cons_of_mem _ h), this.2⟩
  rw [diffsC, WP.block_append_iff]
  refine WP.mono (diffC1_ok hs t d hd₀.2 (.inl ⟨rfl, rfl⟩) (mo := mo) (by omega))
    fun s₁ ⟨e₁, c₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by simp [hd₀.2.symm])
  refine WP.mono (diffsCSbb_ok ts ds hs₁ c₁ (mo := mo + 8) hl (by omega) hds
    (List.nodup_cons.mp hnd).2) fun s₂ ⟨b, c₂, e₂, k₂⟩ => ?_
  have hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.1 q (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    exact fun h => hd₀.1 (h ▸ List.mem_cons_of_mem _ hq))
  have hD : s₂.gpr d = s₁.gpr d := k₂.1 d (List.nodup_cons.mp hnd).1
  rw [hR, k₁.2.1] at e₂
  refine ⟨b, c₂, ?_, k₁.mono (by simp) |>.trans (k₂.mono (by
    intro q hq; exact List.mem_cons_of_mem _ hq))⟩
  simp only [wordsVal, regsVal, pow64_succ, hD]
  simp only [Bool.toNat_false, Nat.add_zero] at e₁ e₂ ⊢
  rw [Nat.mul_assoc]
  omega

/-- `top = top - b` and its borrow in CF. -/
theorem sbbTop_ok (s : State) (top : Reg) {b : Bool} (hb : s.cf = some b) :
    WP isa (.block [.alu .sbb top (.imm 0)]) s fun s' =>
      s'.cf = some (decide ((s.gpr top).toNat < b.toNat)) ∧ Keeps [top] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.map_some,
    Option.bind_some, RegUpd.cf_setReg, RegUpd.cf_arithFlags, hb, Option.some.injEq,
    exists_eq_left', se0]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have h0 : (0 : BitVec 64).toNat = 0 := rfl
    simp only [h0, Nat.zero_add]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- Each word of `ts` replaced by the register of `ds` at its place if CF is
clear (`k` false), and kept if it is set. -/
theorem cmovs_ok : ∀ (ts ds : List Reg) {s : State} (k : Bool), s.cf = some k →
    ds.length = ts.length → ts.Nodup → (∀ d ∈ ds, d ∉ ts) →
    WP isa (.block (cmovs ts ds)) s fun s' =>
      regsVal s' ts = (if k then regsVal s ts else regsVal s ds) ∧ Keeps ts s s'
  | [], [], s, k, _, _, _, _ => WP.block_nil ⟨by cases k <;> rfl, fun _ _ => rfl, rfl, rfl, rfl⟩
  | [], _ :: _, _, _, _, hl, _, _ => by simp at hl
  | _ :: _, [], _, _, _, hl, _, _ => by simp at hl
  | t :: ts, d :: ds, s, k, hk, hl, hnd, hd => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    have htn := (List.nodup_cons.mp hnd).1
    have hds : ∀ q ∈ ds, q ∉ ts := fun q hq h =>
      hd q (List.mem_cons_of_mem _ hq) (List.mem_cons_of_mem _ h)
    rw [cmovs, show Instr.cmov .ae t (.reg d) :: cmovs ts ds = [.cmov .ae t (.reg d)] ++ cmovs ts ds
      from rfl, WP.block_append_iff]
    refine WP.mono (show WP isa (.block [.cmov .ae t (.reg d)]) s (fun s₁ =>
        s₁.gpr t = (if k then s.gpr t else s.gpr d) ∧ s₁.cf = s.cf ∧ Keeps [t] s s₁) by
      apply WP.of_runBlock
      cases k
      · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execCmov, readSrc, VG.X86_64.eval, hk,
          Option.bind_some, Option.map_some, Bool.not_false, ite_true, Option.some.injEq,
          exists_eq_left', RegUpd.gpr_setReg_self, RegUpd.cf_setReg, Bool.false_eq_true, ite_false]
        refine ⟨trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        simp only [RegUpd.gpr_setReg, hr, ite_false]
      · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execCmov, readSrc, VG.X86_64.eval, hk,
          Option.bind_some, Option.map_some, Bool.not_true, Bool.false_eq_true, ite_false,
          ite_true, Option.some.injEq, exists_eq_left']
        exact ⟨trivial, trivial, fun _ _ => rfl, rfl, rfl, rfl⟩) fun s₁ ⟨e₁, c₁, k₁⟩ => ?_
    refine WP.mono (cmovs_ok ts ds k (c₁.trans hk) hl (List.nodup_cons.mp hnd).2 hds)
      fun s₂ ⟨e₂, k₂⟩ => ?_
    have hR : ∀ rs : List Reg, t ∉ rs → regsVal s₁ rs = regsVal s rs := fun rs h =>
      regsVal_congr fun q hq => k₁.1 q (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun e => h (e ▸ hq))
    have ht : s₂.gpr t = s₁.gpr t := k₂.1 t htn
    have hdt : t ∉ ds := fun h => hd t (List.mem_cons_of_mem _ h) (List.mem_cons_self ..)
    refine ⟨?_, (k₁.mono (by simp)).trans (k₂.mono fun q hq => List.mem_cons_of_mem _ hq)⟩
    simp only [regsVal, ht, e₁, e₂, hR ts htn, hR ds hdt]
    cases k <;> simp only [Bool.false_eq_true, ite_true, ite_false]

theorem diffsC_take : ∀ (op : AluOp) (ts ds : List Reg) (mo : Nat),
    diffsC op ts ds mo = diffsC op ts (ds.take ts.length) mo
  | _, [], ds, _ => by cases ds <;> rfl
  | _, _ :: _, [], _ => rfl
  | op, t :: ts, d :: ds, mo => by
    simp only [List.length_cons, List.take_succ_cons, diffsC]
    rw [← diffsC_take]

theorem cmovs_take : ∀ (ts ds : List Reg), cmovs ts ds = cmovs ts (ds.take ts.length)
  | [], ds => by cases ds <;> rfl
  | _ :: _, [] => rfl
  | t :: ts, d :: ds => by
    simp only [List.length_cons, List.take_succ_cons, cmovs]
    rw [← cmovs_take]

/-- `csubC`: `ts + 2^(64 n) top < 2m` reduced modulo `m`, for at most four
words. -/
theorem csubC_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod}
    {ts : List Reg} {top : Reg} (hlen : ts.length = M.n) (hn : 0 < M.n) (h4 : M.n ≤ 4)
    (hf : Fresh (top :: ts)) (hmo : M.mo + 8 * M.n ≤ size) {m : Nat}
    (hm : wordsVal s.mem base M.mo M.n = m)
    (hV : regsVal s ts + 2 ^ (64 * M.n) * (s.gpr top).toNat < 2 * m) :
    WP isa (.block (csubC M ts top)) s fun s' =>
      regsVal s' ts = (regsVal s ts + 2 ^ (64 * M.n) * (s.gpr top).toNat) % m ∧
      Keeps (.rax :: .rcx :: .rdx :: .rbp :: top :: ts) s s' := by
  obtain ⟨t, ts', rfl⟩ : ∃ t ts', ts = t :: ts' := by
    cases ts with
    | nil => simp at hlen; omega
    | cons t ts' => exact ⟨t, ts', rfl⟩
  have hft := hf.tail
  have htop := hf.head
  have hmX : m < 2 ^ (64 * M.n) := hm ▸ wordsVal_lt _ _ _ _
  -- The registers of the difference, as many as the words.
  have hcr : ∀ q ∈ cregs.take (t :: ts').length, q = .rax ∨ q = .rcx ∨ q = .rdx ∨ q = .rbp := by
    intro q hq
    have := List.mem_of_mem_take hq
    simp only [cregs, List.mem_cons, List.not_mem_nil, or_false] at this
    exact this
  have hdl : (cregs.take (t :: ts').length).length = (t :: ts').length := by
    rw [List.length_take, cregs]; simp only [List.length_cons] at hlen ⊢; omega
  have hd : ∀ q ∈ cregs.take (t :: ts').length, q ∉ t :: ts' ∧ q ≠ .rdi ∧ q ≠ top := by
    intro q hq
    rcases hcr q hq with rfl | rfl | rfl | rfl <;>
      exact ⟨fun h => by have := hft.2 _ h; simp at this, by decide, fun h => by
        have := htop.2; subst h; simp at this⟩
  have hnd : (cregs.take (t :: ts').length).Nodup :=
    List.Nodup.sublist (List.take_sublist _ _) (by decide)
  rw [csubC, diffsC_take, cmovs_take, List.append_assoc, WP.block_append_iff]
  generalize cregs.take (t :: ts').length = D at hcr hdl hd hnd
  obtain ⟨d, ds, rfl⟩ : ∃ d ds, D = d :: ds := by
    cases D with
    | nil => simp at hdl
    | cons d ds => exact ⟨d, ds, rfl⟩
  have hl' : ds.length = ts'.length := by simpa using hdl
  refine WP.mono (diffsC_ok hs (t := t) (ts := ts') (d := d) (ds := ds) (mo := M.mo) hl'
    (by rw [hlen]; omega) (fun q hq => ⟨(hd q hq).1, (hd q hq).2.1⟩) hnd)
    fun s₁ ⟨b, c₁, e₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (sbbTop_ok s₁ top c₁) fun s₂ ⟨c₂, k₂⟩ => ?_
  have htop₁ : s₁.gpr top = s.gpr top := k₁.1 top (fun h => (hd top h).2.2 rfl)
  rw [htop₁] at c₂
  refine WP.mono (cmovs_ok (t :: ts') (d :: ds) _ c₂ hdl hft.1 (fun q hq => (hd q hq).1))
    fun s₃ ⟨e₃, k₃⟩ => ?_
  have hR₂ : regsVal s₂ (t :: ts') = regsVal s (t :: ts') := by
    rw [regsVal_congr fun q hq => k₂.1 q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact fun h => htop.1 (h ▸ hq))]
    exact regsVal_congr fun q hq => k₁.1 q fun h => (hd q h).1 hq
  have hD₂ : regsVal s₂ (d :: ds) = regsVal s₁ (d :: ds) :=
    regsVal_congr fun q hq => k₂.1 q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact fun h => (hd q hq).2.2 h)
  have hDlt : regsVal s₁ (d :: ds) < 2 ^ (64 * M.n) := by
    have := regsVal_lt s₁ (d :: ds); rwa [hdl, hlen] at this
  rw [hlen, hm] at e₁
  refine ⟨?_, ?_⟩
  · rw [e₃, hR₂, hD₂]
    simp only [decide_eq_true_eq]
    exact csub_arith (b := b) hmX hDlt hV e₁
  · refine ((k₁.mono fun q hq => ?_).trans (k₂.mono (by simp))).trans (k₃.mono fun q hq => by
      simp only [List.mem_cons] at hq ⊢; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hq)))))
    rcases hcr q hq with rfl | rfl | rfl | rfl <;> simp

end VG.Proof.Mont.X86_64
