import VerifiedGarbage.Impl.Mont.X86_64
import VerifiedGarbage.Proof.X25519.X86_64.Step
import VerifiedGarbage.Proof.Mont.Words
import Mathlib.Tactic.Tauto
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/- Proofs formerly in `VerifiedGarbage.Proof.Mont.X86_64.Words`. -/
section

/-!
# Montgomery arithmetic on x86-64: words in registers and in the working space

Numbers of several words: in registers (`regsVal`, little-endian over a list
of registers) and in the working space (`wordsVal`), which is `size` bytes at
`base`, the value of `rdi` (`Scr`). The loads and stores of the arithmetic,
and what they leave unchanged.
-/

namespace VG.Proof.Mont.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

/-- The registers `rs` read as a little-endian number. -/
def regsVal (s : State) : List Reg → Nat
  | [] => 0
  | r :: rs => (s.gpr r).toNat + 2 ^ 64 * VG.Proof.Mont.X86_64.regsVal s rs

theorem regsVal_lt (s : State) (rs : List Reg) : VG.Proof.Mont.X86_64.regsVal s rs < 2 ^ (64 * rs.length) := by
  induction rs with
  | nil => exact Nat.one_pos
  | cons r rs ih =>
    rw [List.length_cons, pow64_succ]
    exact word_add_lt (s.gpr r).isLt ih

theorem regsVal_append (s : State) (rs qs : List Reg) :
    VG.Proof.Mont.X86_64.regsVal s (rs ++ qs) = VG.Proof.Mont.X86_64.regsVal s rs + 2 ^ (64 * rs.length) * VG.Proof.Mont.X86_64.regsVal s qs := by
  induction rs with
  | nil => simp only [List.nil_append, VG.Proof.Mont.X86_64.regsVal, List.length_nil, Nat.mul_zero, Nat.pow_zero,
      Nat.one_mul, Nat.zero_add]
  | cons r rs ih =>
    rw [List.cons_append, VG.Proof.Mont.X86_64.regsVal, ih, VG.Proof.Mont.X86_64.regsVal, List.length_cons, pow64_succ, Nat.mul_add,
      Nat.mul_assoc]
    omega

theorem regsVal_congr {s s' : State} {rs : List Reg} (h : ∀ r ∈ rs, s'.gpr r = s.gpr r) :
    VG.Proof.Mont.X86_64.regsVal s' rs = VG.Proof.Mont.X86_64.regsVal s rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [VG.Proof.Mont.X86_64.regsVal, h r (List.mem_cons_self ..), ih fun q hq => h q (List.mem_cons_of_mem _ hq)]

/-- The working space: `rdi` holds its base `base`, it is writable and it
does not wrap around. -/
structure Scr (s : State) (base : Addr) (size : Nat) : Prop where
  rdi : s.gpr .rdi = base
  wr : (⟨base, size⟩ : Region) ∈ s.wr
  nowrap : base.toNat + size ≤ 2 ^ 64

theorem ea_sc (s : State) (d : Nat) : s.ea (sc d) = off (s.gpr .rdi) d := by
  simp only [State.ea, sc, BitVec.ofInt_natCast]

theorem Scr.contains {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.X86_64.Scr s base size) {d n : Nat}
    (h : d + n ≤ size) (hn : 0 < n) : (⟨base, size⟩ : Region).Contains (off base d) n :=
  Offset.contains_base base h (by have := hs.nowrap; omega)

theorem load_sc {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.X86_64.Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) : s.load64 (s.ea (sc d)) = some (word s.mem base d) := by
  rw [VG.Proof.Mont.X86_64.ea_sc, hs.rdi, State.load64, ite_eq_left ⟨_, List.mem_append_right _ hs.wr, hs.contains hd (by decide)⟩]

theorem readSrc_sc {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.X86_64.Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) : readSrc s (.mem (sc d)) = some (word s.mem base d) := VG.Proof.Mont.X86_64.load_sc hs hd

theorem store_sc {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.X86_64.Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) (v : BitVec 64) :
    s.store64 (s.ea (sc d)) v = some { s with mem := s.mem.writeW (off base d) v } := by
  rw [VG.Proof.Mont.X86_64.ea_sc, hs.rdi, State.store64, ite_eq_left ⟨_, hs.wr, hs.contains hd (by decide)⟩]

theorem ld_sc {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.X86_64.Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) : InRegions (s.rd ++ s.wr) (off base d) 8 :=
  ⟨_, List.mem_append_right _ hs.wr, hs.contains hd (by decide)⟩

theorem st_sc {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.X86_64.Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) : InRegions s.wr (off base d) 8 :=
  ⟨_, hs.wr, hs.contains hd (by decide)⟩

theorem Scr.of_keeps {rs : List Reg} {s s' : State} {base : Addr} {size : Nat}
    (hs : VG.Proof.Mont.X86_64.Scr s base size) (h : Keeps rs s s') (hr : .rdi ∉ rs) : VG.Proof.Mont.X86_64.Scr s' base size :=
  ⟨(h.1 _ hr).trans hs.rdi, h.2.2.2 ▸ hs.wr, hs.nowrap⟩

end VG.Proof.Mont.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Mont.X86_64.Row`. -/
section

/-!
# Montgomery arithmetic on x86-64: rows of multiply-accumulate steps

`mulSteps ts d` adds `rcx · [d]` (as many words as `ts`) to the words `ts`,
with the carry word `rbp` in and out (`mulSteps_ok`), by induction over the
words, from X25519's multiply-accumulate step.
-/

namespace VG.Proof.Mont.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono mulStep_ok)

/-- Registers the arithmetic can use for words: distinct, and none of `rax`,
`rcx`, `rdx`, `rbp` and `rdi`. -/
def Fresh (ts : List Reg) : Prop :=
  ts.Nodup ∧ ∀ t ∈ ts, t ≠ .rax ∧ t ≠ .rcx ∧ t ≠ .rdx ∧ t ≠ .rbp ∧ t ≠ .rdi

theorem Fresh.tail {t : Reg} {ts : List Reg} (h : VG.Proof.Mont.X86_64.Fresh (t :: ts)) : VG.Proof.Mont.X86_64.Fresh ts :=
  ⟨(List.nodup_cons.mp h.1).2, fun q hq => h.2 q (List.mem_cons_of_mem _ hq)⟩

theorem Fresh.head {t : Reg} {ts : List Reg} (h : VG.Proof.Mont.X86_64.Fresh (t :: ts)) :
    t ∉ ts ∧ t ≠ .rax ∧ t ≠ .rcx ∧ t ≠ .rdx ∧ t ≠ .rbp ∧ t ≠ .rdi :=
  ⟨(List.nodup_cons.mp h.1).1, h.2 t (List.mem_cons_self ..)⟩

/-- Closes `∀ r ∈ rs, r ∈ rs'` for literal lists of registers and variables. -/
macro "sub_regs" : tactic => `(tactic| (intro q hq; simp only [List.mem_cons, List.mem_append,
  List.mem_singleton, List.not_mem_nil, or_false] at hq ⊢; grind))

theorem mulStep_eq (t c ai : Reg) (src : Src) :
    mulStep t c ai src = Impl.X25519.X86_64.mulStep t c ai src := rfl

/-- A row: `ts + 2^(64 |ts|) rbp = ts + rbp + rcx · [d]`. -/
theorem mulSteps_ok {size : Nat} : ∀ (ts : List Reg) {s : State} {base : Addr} {d : Nat},
    VG.Proof.Mont.X86_64.Scr s base size → d + 8 * ts.length ≤ size → VG.Proof.Mont.X86_64.Fresh ts →
    WP isa (.block (mulSteps ts d)) s fun s' =>
      VG.Proof.Mont.X86_64.regsVal s' ts + 2 ^ (64 * ts.length) * (s'.gpr .rbp).toNat =
        VG.Proof.Mont.X86_64.regsVal s ts + (s.gpr .rbp).toNat + (s.gpr .rcx).toNat * wordsVal s.mem base d ts.length ∧
      Keeps (.rbp :: .rax :: .rdx :: ts) s s'
  | [], s, _, _, _, _, _ => WP.block_nil ⟨by simp [VG.Proof.Mont.X86_64.regsVal, wordsVal],
      fun _ _ => rfl, rfl, rfl, rfl⟩
  | t :: ts, s, base, d, hs, hd, hf => by
    obtain ⟨htn, hta, htc, htd, htb, hti⟩ := hf.head
    rw [mulSteps, VG.Proof.Mont.X86_64.mulStep_eq, WP.block_append_iff]
    refine WP.mono (mulStep_ok s (VG.Proof.Mont.X86_64.readSrc_sc hs (d := d) (by simp at hd; omega)) hta htd
      (by decide) (by decide) (by decide) htb) fun s₁ ⟨e₁, k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (by simp [Ne.symm hti])
    refine WP.mono (VG.Proof.Mont.X86_64.mulSteps_ok ts hs₁ (d := d + 8) (by simp at hd; omega) hf.tail)
      fun s₂ ⟨e₂, k₂⟩ => ?_
    have g₂ : ∀ r, r ∉ Reg.rbp :: Reg.rax :: Reg.rdx :: ts → s₂.gpr r = s₁.gpr r := k₂.1
    have g₁ : ∀ r, r ∉ [t, Reg.rbp, Reg.rax, Reg.rdx] → s₁.gpr r = s.gpr r := k₁.1
    have ht₂ : s₂.gpr t = s₁.gpr t := g₂ t (by simp [htn, htb, hta, htd])
    have hc₁ : s₁.gpr .rcx = s.gpr .rcx := g₁ .rcx (by simp [Ne.symm htc])
    have hR₁ : VG.Proof.Mont.X86_64.regsVal s₁ ts = VG.Proof.Mont.X86_64.regsVal s ts := VG.Proof.Mont.X86_64.regsVal_congr fun q hq => g₁ q (by
      have := hf.tail.2 q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun h => htn (h ▸ hq), this.2.2.2.1, this.1, this.2.2.1⟩)
    rw [k₁.2.1] at e₂
    refine ⟨?_, ?_⟩
    · rw [hR₁, hc₁] at e₂
      simp only [VG.Proof.Mont.X86_64.regsVal, wordsVal, List.length_cons, pow64_succ, ht₂]
      have h1 : (s.gpr .rcx).toNat * ((word s.mem base d).toNat + 2 ^ 64 * wordsVal s.mem base (d + 8)
          ts.length) = (s.gpr .rcx).toNat * (word s.mem base d).toNat +
          2 ^ 64 * ((s.gpr .rcx).toNat * wordsVal s.mem base (d + 8) ts.length) := by
        rw [Nat.mul_add, Nat.mul_left_comm]
      have h2 : 2 ^ 64 * 2 ^ (64 * ts.length) * (s₂.gpr .rbp).toNat =
          2 ^ 64 * (2 ^ (64 * ts.length) * (s₂.gpr .rbp).toNat) := Nat.mul_assoc _ _ _
      rw [h1, h2]
      have := VG.Proof.Mont.X86_64.readSrc_sc hs (d := d) (by simp at hd; omega)
      omega
    · exact (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))

end VG.Proof.Mont.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Mont.X86_64.Blocks`. -/
section

/-!
# Montgomery arithmetic on x86-64: the small blocks of a round

Each run symbolically once, for any registers: loading a word into `rcx`,
a row with its carry word cleared first (`mulRow`), the carry of a row into
the two top words (`carryUp`), and the computation of `u = t₀ m' mod 2⁶⁴`.
-/

namespace VG.Proof.Mont.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono se0 add_carry adc_carry toNat_ofBool)

theorem movRcx_ok {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.X86_64.Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) :
    WP isa (.block [.mov .rcx (.mem (sc d))]) s fun s' =>
      s'.gpr .rcx = word s.mem base d ∧ Keeps [.rcx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.Proof.Mont.X86_64.readSrc_sc hs hd, Option.map_some,
    RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

/-- A row, with the carry word cleared first. -/
theorem mulRow_ok {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.X86_64.Scr s base size) {ts : List Reg}
    {d : Nat} (hd : d + 8 * ts.length ≤ size) (hf : VG.Proof.Mont.X86_64.Fresh ts) :
    WP isa (.block (mulRow ts d)) s fun s' =>
      VG.Proof.Mont.X86_64.regsVal s' ts + 2 ^ (64 * ts.length) * (s'.gpr .rbp).toNat =
        VG.Proof.Mont.X86_64.regsVal s ts + (s.gpr .rcx).toNat * wordsVal s.mem base d ts.length ∧
      Keeps (.rbp :: .rax :: .rdx :: ts) s s' := by
  rw [mulRow, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.mov32 .rbp (.imm 0)]) s
      (fun s₁ => s₁.gpr .rbp = 0 ∧ Keeps [.rbp] s s₁) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
      State.setReg32, RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨rfl, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s₁ ⟨b₁, k₁⟩ => ?_
  refine WP.mono (VG.Proof.Mont.X86_64.mulSteps_ok ts (hs.of_keeps k₁ (by decide)) hd hf) fun s₂ ⟨e₂, k₂⟩ => ?_
  have hR : VG.Proof.Mont.X86_64.regsVal s₁ ts = VG.Proof.Mont.X86_64.regsVal s ts := VG.Proof.Mont.X86_64.regsVal_congr fun q hq => k₁.1 q (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; exact (hf.2 q hq).2.2.2.1)
  rw [b₁, hR, k₁.2.1, k₁.1 .rcx (by decide)] at e₂
  refine ⟨by simpa using e₂, (k₁.mono (by sub_regs)).trans k₂⟩

/-- The carry word `rbp` into `tn` and its carry into `tn1`, if that does not
overflow. -/
theorem carryUp_ok (s : State) {tn tn1 : Reg} (h1 : tn ≠ tn1)
    (hb : (s.gpr tn).toNat + 2 ^ 64 * (s.gpr tn1).toNat + (s.gpr .rbp).toNat < 2 ^ 128) :
    WP isa (.block (carryUp tn tn1)) s fun s' =>
      (s'.gpr tn).toNat + 2 ^ 64 * (s'.gpr tn1).toNat =
        (s.gpr tn).toNat + 2 ^ 64 * (s.gpr tn1).toNat + (s.gpr .rbp).toNat ∧
      Keeps [tn, tn1] s s' := by
  apply WP.of_runBlock
  simp only [carryUp, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    Option.map_some, Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.cf_arithFlags, RegUpd.cf_setReg, ite_true, ite_false, h1, Ne.symm h1,
    Option.some.injEq, exists_eq_left', se0]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have e0 := add_carry (s.gpr tn) (s.gpr .rbp)
    have e1 := adc_carry (s.gpr tn1) 0 (decide (2 ^ 64 ≤ (s.gpr tn).toNat + (s.gpr .rbp).toNat))
    have hz : (0 : BitVec 64).toNat = 0 := rfl
    rw [hz, Nat.add_zero] at e1
    have := (s.gpr tn1 + 0 + (BitVec.ofBool (decide (2 ^ 64 ≤ (s.gpr tn).toNat +
      (s.gpr .rbp).toNat))).setWidth 64).isLt
    have := Bool.toNat_le (decide (2 ^ 64 ≤ (s.gpr tn1).toNat +
      (decide (2 ^ 64 ≤ (s.gpr tn).toNat + (s.gpr .rbp).toNat)).toNat))
    have hc : (decide (2 ^ 64 ≤ (s.gpr tn1).toNat +
      (decide (2 ^ 64 ≤ (s.gpr tn).toNat + (s.gpr .rbp).toNat)).toNat)).toNat = 0 := by
      have := Bool.toNat_le (decide (2 ^ 64 ≤ (s.gpr tn).toNat + (s.gpr .rbp).toNat))
      omega
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]

/-- `rcx = t₀ m' mod 2⁶⁴`. -/
theorem uBlock_ok (s : State) (t0 : Reg) (minv : BitVec 64) :
    WP isa (.block [.mov .rax (.reg t0), .movImm64 .rcx minv, .mul .rcx, .mov .rcx (.reg .rax)]) s
      fun s' => (s'.gpr .rcx).toNat = (s.gpr t0).toNat * minv.toNat % 2 ^ 64 ∧
        Keeps [.rax, .rcx, .rdx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execMul, Option.map_some,
    RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq, Option.some.injEq,
    exists_eq_left']
  refine ⟨BitVec.toNat_ofNat _ _, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2.1, hr.2.2, ite_false]

end VG.Proof.Mont.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Mont.X86_64.Round`. -/
section

/-!
# Montgomery arithmetic on x86-64: a round of the multiplication

The accumulator's window of registers (`wins n i`), how it rotates from one
round to the next, and a round (`round_ok`): the accumulator `T < 2m`
becomes `(T + a_i B + u m) / 2⁶⁴ < 2m` for some `u`, with the low word of
`T + a_i B + u m` zero.
-/

namespace VG.Proof.Mont.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

/-! ## The window -/

theorem win_succ (n i j : Nat) : win n (i + 1) j = win n i (j + 1) := by
  simp only [win, Nat.add_assoc, Nat.add_comm 1 j]

theorem win_wrap (n i : Nat) : win n i (n + 2) = win n i 0 := by
  simp only [win, Nat.add_zero, Nat.add_mod_right]

theorem win_mod (n i j : Nat) : win n i j = win n (i % (n + 2)) j := by
  simp only [win, Nat.add_mod i j, Nat.mod_mod, Nat.add_mod (i % (n + 2)) j]

theorem wins_mod (n i : Nat) : wins n i = wins n (i % (n + 2)) := by
  simp only [wins]; exact List.map_congr_left fun j _ => VG.Proof.Mont.X86_64.win_mod n i j

theorem wins_length (n i : Nat) : (wins n i).length = n + 2 := by simp [wins]

theorem wins_cons (n i : Nat) :
    wins n i = win n i 0 :: (List.range (n + 1)).map (fun j => win n i (j + 1)) := by
  simp only [wins, List.range_succ_eq_map, List.map_cons, List.map_map]
  rfl

theorem wins_succ (n i : Nat) :
    wins n (i + 1) = (List.range (n + 1)).map (fun j => win n i (j + 1)) ++ [win n i 0] := by
  rw [wins, show win n (i + 1) = fun j => win n i (j + 1) from funext (VG.Proof.Mont.X86_64.win_succ n i)]
  simp only [List.range_succ (n := n + 1), List.map_append, List.map_cons, List.map_nil, VG.Proof.Mont.X86_64.win_wrap]

theorem wins_split (n i : Nat) :
    wins n i = (List.range n).map (win n i) ++ [win n i n, win n i (n + 1)] := by
  simp only [wins, List.range_succ, List.map_append, List.map_cons, List.map_nil,
    List.append_assoc, List.singleton_append]

theorem nodup_wins_lt : ∀ n < 7, ∀ i < n + 2, (wins n i).Nodup := by decide

theorem regs_wins_lt : ∀ n < 7, ∀ i < n + 2, ∀ t ∈ wins n i, t ≠ .rax ∧ t ≠ .rcx ∧ t ≠ .rdx := by
  decide

theorem regs_wins_lt' : ∀ n < 7, ∀ i < n + 2, ∀ t ∈ wins n i, t ≠ .rbp ∧ t ≠ .rdi := by decide

theorem fresh_wins_lt (n : Nat) (hn : n < 7) (i : Nat) (hi : i < n + 2) : VG.Proof.Mont.X86_64.Fresh (wins n i) :=
  ⟨VG.Proof.Mont.X86_64.nodup_wins_lt n hn i hi, fun t ht =>
    have h := VG.Proof.Mont.X86_64.regs_wins_lt n hn i hi t ht
    have h' := VG.Proof.Mont.X86_64.regs_wins_lt' n hn i hi t ht
    ⟨h.1, h.2.1, h.2.2, h'.1, h'.2⟩⟩

theorem fresh_wins {n : Nat} (hn : n < 7) (i : Nat) : VG.Proof.Mont.X86_64.Fresh (wins n i) := by
  rw [VG.Proof.Mont.X86_64.wins_mod]; exact VG.Proof.Mont.X86_64.fresh_wins_lt n hn _ (Nat.mod_lt _ (by omega))

/-! ## A row and its carry -/

/-- A row of `rcx · [d]` into the low words of `W = low ++ [tn, tn1]`, and its
carry into `tn` and `tn1`, if the sum fits. -/
theorem rowCarry_ok {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.X86_64.Scr s base size)
    {low : List Reg} {tn tn1 : Reg} (hf : VG.Proof.Mont.X86_64.Fresh (low ++ [tn, tn1])) {d : Nat}
    (hd : d + 8 * low.length ≤ size)
    (hb : VG.Proof.Mont.X86_64.regsVal s (low ++ [tn, tn1]) + (s.gpr .rcx).toNat * wordsVal s.mem base d low.length <
      2 ^ (64 * low.length) * 2 ^ 128) :
    WP isa (.block (mulRow low d ++ carryUp tn tn1)) s fun s' =>
      VG.Proof.Mont.X86_64.regsVal s' (low ++ [tn, tn1]) =
        VG.Proof.Mont.X86_64.regsVal s (low ++ [tn, tn1]) + (s.gpr .rcx).toNat * wordsVal s.mem base d low.length ∧
      Keeps (.rbp :: .rax :: .rdx :: (low ++ [tn, tn1])) s s' := by
  have hfl : VG.Proof.Mont.X86_64.Fresh low := ⟨(List.nodup_append.mp hf.1).1, fun q hq => hf.2 q (by simp [hq])⟩
  have hn : tn ∉ low ∧ tn1 ∉ low ∧ tn ≠ tn1 := by
    have h := hf.1
    simp only [List.nodup_append, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false] at h
    exact ⟨fun hm => h.2.2 tn hm tn (by simp) rfl, fun hm => h.2.2 tn1 hm tn1 (by simp) rfl,
      h.2.1.1⟩
  have ftn := hf.2 tn (by simp)
  have ftn1 := hf.2 tn1 (by simp)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Mont.X86_64.mulRow_ok hs hd hfl) fun s₁ ⟨e₁, k₁⟩ => ?_
  have gtn : s₁.gpr tn = s.gpr tn := k₁.1 tn (by simp [hn.1, ftn.1, ftn.2.2.1, ftn.2.2.2.1])
  have gtn1 : s₁.gpr tn1 = s.gpr tn1 := k₁.1 tn1 (by simp [hn.2.1, ftn1.1, ftn1.2.2.1, ftn1.2.2.2.1])
  have hX := VG.Proof.Mont.X86_64.regsVal_lt s₁ low
  simp only [VG.Proof.Mont.X86_64.regsVal_append, VG.Proof.Mont.X86_64.regsVal, Nat.mul_zero, Nat.add_zero] at hb ⊢
  -- The carry fits.
  have hc : (s₁.gpr tn).toNat + 2 ^ 64 * (s₁.gpr tn1).toNat + (s₁.gpr .rbp).toNat < 2 ^ 128 := by
    rw [gtn, gtn1]
    have h' : 2 ^ (64 * low.length) * ((s.gpr tn).toNat + 2 ^ 64 * (s.gpr tn1).toNat +
        (s₁.gpr .rbp).toNat) < 2 ^ (64 * low.length) * 2 ^ 128 := by
      rw [Nat.mul_add]; omega
    exact Nat.lt_of_mul_lt_mul_left h'
  refine WP.mono (VG.Proof.Mont.X86_64.carryUp_ok s₁ hn.2.2 hc) fun s₂ ⟨e₂, k₂⟩ => ?_
  have hl : VG.Proof.Mont.X86_64.regsVal s₂ low = VG.Proof.Mont.X86_64.regsVal s₁ low := VG.Proof.Mont.X86_64.regsVal_congr fun q hq => k₂.1 q (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨fun h => hn.1 (h ▸ hq), fun h => hn.2.1 (h ▸ hq)⟩)
  refine ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
  rw [hl, e₂, gtn, gtn1]
  have : 2 ^ (64 * low.length) * ((s.gpr tn).toNat + 2 ^ 64 * (s.gpr tn1).toNat +
      (s₁.gpr .rbp).toNat) = 2 ^ (64 * low.length) * ((s.gpr tn).toNat + 2 ^ 64 * (s.gpr tn1).toNat) +
      2 ^ (64 * low.length) * (s₁.gpr .rbp).toNat := Nat.mul_add _ _ _
  rw [this]
  omega

/-! ## A round -/

theorem round_eq (M : Mod) (a b i : Nat) :
    round M a b i = ([.mov .rcx (.mem (sc (a + 8 * i)))] : List Instr) ++
      ((mulRow ((List.range M.n).map (win M.n i)) b ++ carryUp (win M.n i M.n) (win M.n i (M.n + 1))) ++
        (([.mov .rax (.reg (win M.n i 0)), .movImm64 .rcx M.minv, .mul .rcx, .mov .rcx (.reg .rax)] :
          List Instr) ++
          (mulRow ((List.range M.n).map (win M.n i)) M.mo ++
            carryUp (win M.n i M.n) (win M.n i (M.n + 1))))) := by
  simp only [round, List.append_assoc]

/-- Round `i` of the multiplication: `2⁶⁴ T' = T + a_i B + u m`, and
`T' < 2m` if `T < 2m`. -/
theorem round_ok {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.X86_64.Scr s base size) {M : Mod}
    (hn : M.n < 7) {a b i m : Nat} (ha : a + 8 * i + 8 ≤ size) (hb : b + 8 * M.n ≤ size)
    (hmo : M.mo + 8 * M.n ≤ size) (hm : wordsVal s.mem base M.mo M.n = m)
    (hinv : (m * M.minv.toNat + 1) % 2 ^ 64 = 0) (hB : wordsVal s.mem base b M.n < m)
    (hT : VG.Proof.Mont.X86_64.regsVal s (wins M.n i) < 2 * m) :
    WP isa (.block (round M a b i)) s fun s' =>
      (∃ u, 2 ^ 64 * VG.Proof.Mont.X86_64.regsVal s' (wins M.n (i + 1)) = VG.Proof.Mont.X86_64.regsVal s (wins M.n i) +
        (word s.mem base (a + 8 * i)).toNat * wordsVal s.mem base b M.n + u * m) ∧
      VG.Proof.Mont.X86_64.regsVal s' (wins M.n (i + 1)) < 2 * m ∧
      Keeps (.rax :: .rcx :: .rdx :: .rbp :: wins M.n i) s s' := by
  have hW := VG.Proof.Mont.X86_64.wins_split M.n i
  have hf : VG.Proof.Mont.X86_64.Fresh ((List.range M.n).map (win M.n i) ++ [win M.n i M.n, win M.n i (M.n + 1)]) :=
    hW ▸ VG.Proof.Mont.X86_64.fresh_wins hn i
  have hl : ((List.range M.n).map (win M.n i)).length = M.n := by simp
  have hm' : m < 2 ^ (64 * M.n) := hm ▸ wordsVal_lt _ _ _ _
  have hP : 2 ^ (64 * M.n) * 2 ^ 128 = 2 ^ (64 * M.n) * 2 ^ 64 * 2 ^ 64 := by
    rw [Nat.mul_assoc]
  rw [VG.Proof.Mont.X86_64.round_eq, WP.block_append_iff]
  refine WP.mono (VG.Proof.Mont.X86_64.movRcx_ok hs ha) fun s₁ ⟨c₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hT₁ : VG.Proof.Mont.X86_64.regsVal s₁ (wins M.n i) = VG.Proof.Mont.X86_64.regsVal s (wins M.n i) := VG.Proof.Mont.X86_64.regsVal_congr fun q hq =>
    k₁.1 q (by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact (VG.Proof.Mont.X86_64.fresh_wins hn i).2 q hq |>.2.1)
  rw [WP.block_append_iff]
  have hA := (word s.mem base (a + 8 * i)).isLt
  have hAB : (word s.mem base (a + 8 * i)).toNat * wordsVal s.mem base b M.n ≤ (2 ^ 64 - 1) * m :=
    Nat.mul_le_mul (by omega) (by omega)
  refine WP.mono (VG.Proof.Mont.X86_64.rowCarry_ok hs₁ hf (d := b) (by rw [hl]; omega) (by
      rw [← hW, hl, hT₁, c₁, k₁.2.1, hP]
      have : (2 ^ 64 - 1) * m ≤ 2 ^ (64 * M.n) * 2 ^ 64 := by
        rw [Nat.mul_comm]; exact Nat.mul_le_mul (by omega) (by omega)
      omega)) fun s₂ ⟨e₂, k₂⟩ => ?_
  rw [← hW, hl, hT₁, c₁, k₁.2.1] at e₂
  have hs₂ := hs₁.of_keeps k₂ (by
    intro h; rw [← hW] at h
    simp only [List.mem_cons] at h
    rcases h with h | h | h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact (VG.Proof.Mont.X86_64.fresh_wins hn i).2 _ h |>.2.2.2.2 rfl)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Mont.X86_64.uBlock_ok s₂ (win M.n i 0) M.minv) fun s₃ ⟨u₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  have hT₃ : VG.Proof.Mont.X86_64.regsVal s₃ (wins M.n i) = VG.Proof.Mont.X86_64.regsVal s₂ (wins M.n i) := VG.Proof.Mont.X86_64.regsVal_congr fun q hq =>
    k₃.1 q (by
      have := (VG.Proof.Mont.X86_64.fresh_wins hn i).2 q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨this.1, this.2.1, this.2.2.1⟩)
  have hu := (s₃.gpr .rcx).isLt
  have hum : (s₃.gpr .rcx).toNat * m ≤ (2 ^ 64 - 1) * m := Nat.mul_le_mul (by omega) (Nat.le_refl _)
  have hmem₃ : s₃.mem = s.mem := by rw [k₃.2.1, k₂.2.1, k₁.2.1]
  refine WP.mono (VG.Proof.Mont.X86_64.rowCarry_ok hs₃ hf (d := M.mo) (by rw [hl]; omega) (by
      rw [← hW, hl, hT₃, e₂, hmem₃, hm, hP]
      have : (2 ^ 64 - 1) * m ≤ 2 ^ (64 * M.n) * 2 ^ 64 := by
        rw [Nat.mul_comm]; exact Nat.mul_le_mul (by omega) (by omega)
      omega)) fun s₄ ⟨e₄, k₄⟩ => ?_
  rw [← hW, hl, hT₃, e₂, hmem₃, hm] at e₄
  -- The window's value, and its low word, which is zero.
  have hcons := VG.Proof.Mont.X86_64.wins_cons M.n i
  have ht0₂ : (VG.Proof.Mont.X86_64.regsVal s₂ (wins M.n i)) % 2 ^ 64 = (s₂.gpr (win M.n i 0)).toNat := by
    rw [hcons, VG.Proof.Mont.X86_64.regsVal]; omega
  have h₄ : (VG.Proof.Mont.X86_64.regsVal s₄ (wins M.n i)) % 2 ^ 64 = (s₄.gpr (win M.n i 0)).toNat := by
    rw [hcons, VG.Proof.Mont.X86_64.regsVal]; omega
  have hlow : (s₄.gpr (win M.n i 0)).toNat = 0 := by
    have h := mont_low (s₂.gpr (win M.n i 0)).toNat M.minv.toNat m hinv
    rw [← u₃] at h
    rw [← e₂] at e₄
    omega
  have hrot : 2 ^ 64 * VG.Proof.Mont.X86_64.regsVal s₄ (wins M.n (i + 1)) = VG.Proof.Mont.X86_64.regsVal s₄ (wins M.n i) := by
    rw [VG.Proof.Mont.X86_64.wins_succ, VG.Proof.Mont.X86_64.regsVal_append, hcons, VG.Proof.Mont.X86_64.regsVal]
    simp only [VG.Proof.Mont.X86_64.regsVal, hlow, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
  refine ⟨⟨(s₃.gpr .rcx).toNat, by rw [hrot, e₄]⟩, ?_, ?_⟩
  · have : 2 ^ 64 * VG.Proof.Mont.X86_64.regsVal s₄ (wins M.n (i + 1)) < 2 ^ 64 * (2 * m) := by
      rw [hrot, e₄]; omega
    exact Nat.lt_of_mul_lt_mul_left this
  · rw [← hW] at k₂ k₄
    exact (((k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))).trans
      (k₃.mono (by sub_regs))).trans (k₄.mono (by sub_regs))

end VG.Proof.Mont.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Mont.X86_64.Rounds`. -/
section

/-!
# Montgomery arithmetic on x86-64: the rounds of the multiplication

From a cleared accumulator (`zeros_ok`), `k` rounds leave `T_k < 2m` with
`2^(64k) T_k = A_k B + U m` (`rounds_ok`), `A_k` the low `k` words of `[a]`.
-/

namespace VG.Proof.Mont.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

theorem regsVal_zero {s : State} {rs : List Reg} (h : ∀ r ∈ rs, s.gpr r = 0) : VG.Proof.Mont.X86_64.regsVal s rs = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rw [VG.Proof.Mont.X86_64.regsVal, h r (List.mem_cons_self ..), ih fun q hq => h q (List.mem_cons_of_mem _ hq)]
    rfl

theorem zeros_ok (s : State) : ∀ ts : List Reg,
    WP isa (.block (zeros ts)) s fun s' => (∀ t ∈ ts, s'.gpr t = 0) ∧ Keeps ts s s'
  | [] => WP.block_nil ⟨fun _ h => absurd h (List.not_mem_nil), fun _ _ => rfl, rfl, rfl, rfl⟩
  | t :: ts => by
    rw [zeros, List.map_cons, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (show WP isa (.block [.mov32 t (.imm 0)]) s
        (fun s₁ => s₁.gpr t = 0 ∧ Keeps [t] s s₁) by
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
        State.setReg32, RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left']
      refine ⟨rfl, fun r hr => ?_, rfl, rfl, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s₁ ⟨z₁, k₁⟩ => ?_
    refine WP.mono (VG.Proof.Mont.X86_64.zeros_ok s₁ ts) fun s₂ ⟨z₂, k₂⟩ => ⟨fun q hq => ?_, (k₁.mono (by sub_regs)).trans
      (k₂.mono (by sub_regs))⟩
    by_cases hqt : q ∈ ts
    · exact z₂ q hqt
    · have : q = t := by simpa [hqt] using hq
      subst this; rw [k₂.1 _ hqt, z₁]

theorem wins_sub_acc_lt : ∀ n < 7, ∀ i < n + 2, ∀ r ∈ wins n i, r ∈ acc n := by decide

theorem wins_sub_acc {n : Nat} (hn : n < 7) (i : Nat) : ∀ r ∈ wins n i, r ∈ acc n := by
  rw [VG.Proof.Mont.X86_64.wins_mod]; exact VG.Proof.Mont.X86_64.wins_sub_acc_lt n hn _ (Nat.mod_lt _ (by omega))

theorem acc_regs_lt : ∀ n < 7, ∀ r ∈ acc n, r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .rbp ∧ r ≠ .rdi := by
  decide

/-- `k` rounds, from a cleared accumulator. -/
theorem rounds_ok {M : Mod} (hn : M.n < 7) {a b m size : Nat}
    (ha : a + 8 * M.n ≤ size) (hb : b + 8 * M.n ≤ size) (hmo : M.mo + 8 * M.n ≤ size)
    (hinv : (m * M.minv.toNat + 1) % 2 ^ 64 = 0) :
    ∀ k ≤ M.n, ∀ {s : State} {base : Addr}, VG.Proof.Mont.X86_64.Scr s base size →
      wordsVal s.mem base M.mo M.n = m → wordsVal s.mem base b M.n < m →
      VG.Proof.Mont.X86_64.regsVal s (wins M.n 0) = 0 →
      WP isa (.block ((List.range k).flatMap (round M a b))) s fun s' =>
        (∃ U, 2 ^ (64 * k) * VG.Proof.Mont.X86_64.regsVal s' (wins M.n k) =
          wordsVal s.mem base a k * wordsVal s.mem base b M.n + U * m) ∧
        VG.Proof.Mont.X86_64.regsVal s' (wins M.n k) < 2 * m ∧
        Keeps (.rax :: .rcx :: .rdx :: .rbp :: acc M.n) s s'
  | 0, _, s, _, _, _, hB, h0 => WP.block_nil ⟨⟨0, by simp [h0, wordsVal]⟩, by rw [h0]; omega,
      fun _ _ => rfl, rfl, rfl, rfl⟩
  | k + 1, hk, s, base, hs, hm, hB, h0 => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (VG.Proof.Mont.X86_64.rounds_ok hn ha hb hmo hinv k (by omega) hs hm hB h0)
      fun s₁ ⟨⟨U, eU⟩, hT, k₁⟩ => ?_
    have hmem : s₁.mem = s.mem := k₁.2.1
    have hs₁ := hs.of_keeps k₁ (by
      intro h
      simp only [List.mem_cons] at h
      rcases h with h | h | h | h | h
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact (VG.Proof.Mont.X86_64.acc_regs_lt _ hn _ h).2.2.2.2 rfl)
    refine WP.mono (VG.Proof.Mont.X86_64.round_ok hs₁ hn (i := k) (by omega) hb hmo (by rw [hmem, hm]) hinv
      (by rw [hmem]; exact hB) hT) fun s₂ ⟨⟨u, eu⟩, hT₂, k₂⟩ => ?_
    rw [hmem] at eu
    refine ⟨⟨U + 2 ^ (64 * k) * u, ?_⟩, hT₂, k₁.trans (k₂.mono fun q hq => ?_)⟩
    · calc 2 ^ (64 * (k + 1)) * VG.Proof.Mont.X86_64.regsVal s₂ (wins M.n (k + 1))
          = 2 ^ (64 * k) * (2 ^ 64 * VG.Proof.Mont.X86_64.regsVal s₂ (wins M.n (k + 1))) := by
            rw [Nat.mul_succ, Nat.pow_add, Nat.mul_assoc]
        _ = 2 ^ (64 * k) * VG.Proof.Mont.X86_64.regsVal s₁ (wins M.n k) +
            2 ^ (64 * k) * (word s.mem base (a + 8 * k)).toNat * wordsVal s.mem base b M.n +
            2 ^ (64 * k) * u * m := by rw [eu]; simp only [Nat.mul_add, Nat.mul_assoc]
        _ = (wordsVal s.mem base a k + 2 ^ (64 * k) * (word s.mem base (a + 8 * k)).toNat) *
            wordsVal s.mem base b M.n + (U + 2 ^ (64 * k) * u) * m := by
            rw [eU, Nat.add_mul, Nat.add_mul]; omega
        _ = _ := by rw [wordsVal_succ_top]
    · simp only [List.mem_cons] at hq ⊢
      rcases hq with h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (VG.Proof.Mont.X86_64.wins_sub_acc hn k q h))))

end VG.Proof.Mont.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Mont.X86_64.Csub`. -/
section

/-!
# Montgomery arithmetic on x86-64: the conditional subtraction

`csub M ts top` reduces `V = ts + 2^(64 n) top < 2m` below `m`
(`csub_ok`): the difference `V - m` is computed word by word into the
temporary area (`diffs`), its borrow becomes a mask (`rax`, all ones if
`V ≥ m`), and the mask selects the difference (`selects`).
-/

namespace VG.Proof.Mont.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono se0 sub_borrow sbb_borrow toNat_ofBool)

/-- The registers but `rs` and the regions are unchanged (memory may change). -/
structure KeepRegs (rs : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ rs → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem KeepRegs.trans {rs : List Reg} {s₁ s₂ s₃ : State} (h₁ : VG.Proof.Mont.X86_64.KeepRegs rs s₁ s₂)
    (h₂ : VG.Proof.Mont.X86_64.KeepRegs rs s₂ s₃) : VG.Proof.Mont.X86_64.KeepRegs rs s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

theorem KeepRegs.mono {rs rs' : List Reg} {s s' : State} (h : VG.Proof.Mont.X86_64.KeepRegs rs s s')
    (hs : ∀ r ∈ rs, r ∈ rs') : VG.Proof.Mont.X86_64.KeepRegs rs' s s' :=
  ⟨fun r hr => h.gpr r fun h' => hr (hs r h'), h.rd, h.wr⟩

theorem Keeps.regs {rs : List Reg} {s s' : State} (h : Keeps rs s s') : VG.Proof.Mont.X86_64.KeepRegs rs s s' :=
  ⟨h.1, h.2.2.1, h.2.2.2⟩

theorem Scr.of_keepRegs {rs : List Reg} {s s' : State} {base : Addr} {size : Nat}
    (hs : VG.Proof.Mont.X86_64.Scr s base size) (h : VG.Proof.Mont.X86_64.KeepRegs rs s s') (hr : .rdi ∉ rs) : VG.Proof.Mont.X86_64.Scr s' base size :=
  ⟨(h.gpr _ hr).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

/-! ## The differences -/

/-- One word of the difference: `[tmp] = t - [mo] - c` (`op` is `sub`, with
no borrow in, or `sbb`). -/
theorem diff1_ok {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.X86_64.Scr s base size) (t : Reg)
    {op : AluOp} {c : Bool}
    (hop : (op = .sub ∧ c = false) ∨ (op = .sbb ∧ s.cf = some c)) {mo tmp : Nat}
    (hmo : mo + 8 ≤ size) (htmp : tmp + 8 ≤ size) :
    WP isa (.block [.mov .rax (.reg t), .alu op .rax (.mem (sc mo)), .store (sc tmp) .rax]) s
      fun s' => (word s'.mem base tmp).toNat + (word s.mem base mo).toNat + c.toNat =
          (s.gpr t).toNat + 2 ^ 64 * (decide ((s.gpr t).toNat < (word s.mem base mo).toNat +
            c.toNat)).toNat ∧
        s'.cf = some (decide ((s.gpr t).toNat < (word s.mem base mo).toNat + c.toNat)) ∧
        VG.Proof.Mont.X86_64.KeepRegs [.rax] s s' ∧ s'.mem = s.mem.writeW (off base tmp) (word s'.mem base tmp) := by
  rcases hop with ⟨rfl, rfl⟩ | ⟨rfl, hc⟩
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.map_some,
      Option.bind_some, State.load64, State.store64, VG.Proof.Mont.X86_64.ea_sc, RegUpd.gpr_setReg,
      RegUpd.gpr_arithFlags, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
      RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.mem_arithFlags, reduceCtorEq, ite_true,
      ite_false, hs.rdi, VG.Proof.Mont.X86_64.ld_sc hs hmo, VG.Proof.Mont.X86_64.st_sc hs htmp]
    simp only [Option.some.injEq, exists_eq_left', RegUpd.cf_setReg, RegUpd.cf_arithFlags,
      word_writeW_self, Bool.toNat_false, Nat.add_zero]
    refine ⟨sub_borrow _ _, trivial, ⟨fun r hr => ?_, rfl, rfl⟩, trivial⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.map_some,
      Option.bind_some, State.load64, State.store64, VG.Proof.Mont.X86_64.ea_sc, RegUpd.gpr_setReg,
      RegUpd.gpr_arithFlags, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
      RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.mem_arithFlags, reduceCtorEq, ite_true,
      ite_false, hs.rdi, VG.Proof.Mont.X86_64.ld_sc hs hmo, VG.Proof.Mont.X86_64.st_sc hs htmp, RegUpd.cf_setReg, hc]
    simp only [Option.some.injEq, exists_eq_left', RegUpd.cf_arithFlags, word_writeW_self]
    refine ⟨?_, trivial, ⟨fun r hr => ?_, rfl, rfl⟩, trivial⟩
    · have := sbb_borrow (s.gpr t) (word s.mem base mo) c
      omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- The difference of the words `ts` and the words at `mo`, with the borrow
`c` in, into the words at `tmp`, and its borrow out. -/
theorem diffsSbb_ok {size : Nat} : ∀ (ts : List Reg) {s : State} {base : Addr} {c : Bool}
    {mo tmp : Nat}, VG.Proof.Mont.X86_64.Scr s base size → s.cf = some c → mo + 8 * ts.length ≤ size →
    tmp + 8 * ts.length ≤ size → (mo + 8 * ts.length ≤ tmp ∨ tmp + 8 * ts.length ≤ mo) → VG.Proof.Mont.X86_64.Fresh ts →
    WP isa (.block (diffs .sbb ts mo tmp)) s fun s' => ∃ b : Bool, s'.cf = some b ∧
      wordsVal s'.mem base tmp ts.length + wordsVal s.mem base mo ts.length + c.toNat =
        VG.Proof.Mont.X86_64.regsVal s ts + 2 ^ (64 * ts.length) * b.toNat ∧
      VG.Proof.Mont.X86_64.KeepRegs [.rax] s s' ∧ Outside base tmp (8 * ts.length) s.mem s'.mem
  | [], s, _, c, _, _, _, hc, _, _, _, _ => WP.block_nil ⟨c, hc, by simp [wordsVal, VG.Proof.Mont.X86_64.regsVal],
      ⟨fun _ _ => rfl, rfl, rfl⟩, Outside.refl _ _ _ _⟩
  | t :: ts, s, base, c, mo, tmp, hs, hc, hmo, htmp, hsep, hf => by
    have hn := hs.nowrap
    simp only [List.length_cons] at hmo htmp hsep
    rw [diffs, WP.block_append_iff]
    refine WP.mono (VG.Proof.Mont.X86_64.diff1_ok hs t (.inr ⟨rfl, hc⟩) (mo := mo) (tmp := tmp) (by omega) (by omega))
      fun s₁ ⟨e₁, c₁, k₁, m₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    have O₁ : Outside base tmp 8 s.mem s₁.mem := by
      rw [m₁]; exact writeW_outside _ _ _ (by omega)
    refine WP.mono (VG.Proof.Mont.X86_64.diffsSbb_ok ts hs₁ c₁ (mo := mo + 8) (tmp := tmp + 8) (by omega) (by omega)
      (by omega) hf.tail) fun s₂ ⟨b, c₂, e₂, k₂, O₂⟩ => ?_
    have hR : VG.Proof.Mont.X86_64.regsVal s₁ ts = VG.Proof.Mont.X86_64.regsVal s ts := VG.Proof.Mont.X86_64.regsVal_congr fun q hq => k₁.gpr q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; exact (hf.tail.2 q hq).1)
    have hM : wordsVal s₁.mem base (mo + 8) ts.length = wordsVal s.mem base (mo + 8) ts.length :=
      O₁.wordsVal (by omega) (by omega)
    have hT : word s₂.mem base tmp = word s₁.mem base tmp := O₂.word (by omega) (by omega)
    rw [hR, hM] at e₂
    refine ⟨b, c₂, ?_, k₁.trans k₂, fun x hx => ?_⟩
    · simp only [wordsVal, VG.Proof.Mont.X86_64.regsVal, List.length_cons, pow64_succ, hT]
      rw [Nat.mul_assoc]
      omega
    · simp only [List.length_cons] at hx
      rw [O₂ x (by omega), O₁ x (by omega)]

/-- The difference of the words `ts` and the words at `mo` into the words at
`tmp`, and its borrow. -/
theorem diffs_ok {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.X86_64.Scr s base size) {t : Reg}
    {ts : List Reg} {mo tmp : Nat} (hmo : mo + 8 * (t :: ts).length ≤ size)
    (htmp : tmp + 8 * (t :: ts).length ≤ size)
    (hsep : mo + 8 * (t :: ts).length ≤ tmp ∨ tmp + 8 * (t :: ts).length ≤ mo)
    (hf : VG.Proof.Mont.X86_64.Fresh (t :: ts)) :
    WP isa (.block (diffs .sub (t :: ts) mo tmp)) s fun s' => ∃ b : Bool, s'.cf = some b ∧
      wordsVal s'.mem base tmp (t :: ts).length + wordsVal s.mem base mo (t :: ts).length =
        VG.Proof.Mont.X86_64.regsVal s (t :: ts) + 2 ^ (64 * (t :: ts).length) * b.toNat ∧
      VG.Proof.Mont.X86_64.KeepRegs [.rax] s s' ∧ Outside base tmp (8 * (t :: ts).length) s.mem s'.mem := by
  have hn := hs.nowrap
  simp only [List.length_cons] at hmo htmp hsep ⊢
  rw [diffs, WP.block_append_iff]
  refine WP.mono (VG.Proof.Mont.X86_64.diff1_ok hs t (.inl ⟨rfl, rfl⟩) (mo := mo) (tmp := tmp) (by omega) (by omega))
    fun s₁ ⟨e₁, c₁, k₁, m₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  have O₁ : Outside base tmp 8 s.mem s₁.mem := by
    rw [m₁]; exact writeW_outside _ _ _ (by omega)
  refine WP.mono (VG.Proof.Mont.X86_64.diffsSbb_ok ts hs₁ c₁ (mo := mo + 8) (tmp := tmp + 8) (by omega) (by omega)
    (by omega) hf.tail) fun s₂ ⟨b, c₂, e₂, k₂, O₂⟩ => ?_
  have hR : VG.Proof.Mont.X86_64.regsVal s₁ ts = VG.Proof.Mont.X86_64.regsVal s ts := VG.Proof.Mont.X86_64.regsVal_congr fun q hq => k₁.gpr q (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; exact (hf.tail.2 q hq).1)
  have hM : wordsVal s₁.mem base (mo + 8) ts.length = wordsVal s.mem base (mo + 8) ts.length :=
    O₁.wordsVal (by omega) (by omega)
  have hT : word s₂.mem base tmp = word s₁.mem base tmp := O₂.word (by omega) (by omega)
  rw [hR, hM] at e₂
  refine ⟨b, c₂, ?_, k₁.trans k₂, fun x hx => ?_⟩
  · simp only [wordsVal, VG.Proof.Mont.X86_64.regsVal, pow64_succ, hT]
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
  · rw [VG.Proof.Mont.X86_64.mask_val]
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

/-- Each word of `ts` replaced by the word at `tmp` if the mask `rax` is all
ones (`k` false), and kept if it is zero (`k` true). -/
theorem selects_ok {size : Nat} : ∀ (ts : List Reg) {s : State} {base : Addr} {tmp : Nat} (k : Bool),
    VG.Proof.Mont.X86_64.Scr s base size → tmp + 8 * ts.length ≤ size → VG.Proof.Mont.X86_64.Fresh ts →
    s.gpr .rax = (if k then 0 else BitVec.allOnes 64) →
    WP isa (.block (selects ts tmp)) s fun s' =>
      VG.Proof.Mont.X86_64.regsVal s' ts = (if k then VG.Proof.Mont.X86_64.regsVal s ts else wordsVal s.mem base tmp ts.length) ∧
      Keeps (.rdx :: ts) s s'
  | [], s, _, _, k, _, _, _, _ => WP.block_nil ⟨by cases k <;> rfl, fun _ _ => rfl, rfl, rfl, rfl⟩
  | t :: ts, s, base, tmp, k, hs, htmp, hf, hk => by
    obtain ⟨htn, hta, -, htd, -, -⟩ := hf.head
    simp only [List.length_cons] at htmp
    rw [selects, WP.block_append_iff]
    refine WP.mono (show WP isa (.block [.mov .rdx (.mem (sc tmp)), .alu .xor .rdx (.reg t),
        .alu .and .rdx (.reg .rax), .alu .xor t (.reg .rdx)]) s (fun s₁ =>
        s₁.gpr t = (if k then s.gpr t else word s.mem base tmp) ∧ Keeps [.rdx, t] s s₁) by
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
        Option.map_some, Option.bind_some, VG.Proof.Mont.X86_64.load_sc hs (d := tmp) (by omega), RegUpd.gpr_setReg,
        RegUpd.gpr_arithFlags, ite_true, Option.some.injEq, exists_eq_left', htd, ite_false, hk,
        reduceCtorEq]
      refine ⟨VG.Proof.Mont.X86_64.select_val _ _ k, fun r hr => ?_, rfl, rfl, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]) fun s₁ ⟨e₁, k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨by decide, fun h => hf.head.2.2.2.2.2 h.symm⟩)
    have hk₁ : s₁.gpr .rax = (if k then 0 else BitVec.allOnes 64) := by
      rw [k₁.1 _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨by decide, Ne.symm hta⟩), hk]
    refine WP.mono (VG.Proof.Mont.X86_64.selects_ok ts k hs₁ (tmp := tmp + 8) (by omega) hf.tail hk₁) fun s₂ ⟨e₂, k₂⟩ => ?_
    have hR : VG.Proof.Mont.X86_64.regsVal s₁ ts = VG.Proof.Mont.X86_64.regsVal s ts := VG.Proof.Mont.X86_64.regsVal_congr fun q hq => k₁.1 q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨(hf.tail.2 q hq).2.2.1, fun h => htn (h ▸ hq)⟩)
    have ht₂ : s₂.gpr t = s₁.gpr t := k₂.1 t (by simp [htn, htd])
    refine ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
    rw [VG.Proof.Mont.X86_64.regsVal, ht₂, e₁, e₂, hR, k₁.2.1]
    cases k <;> rfl

/-! ## The conditional subtraction -/

/-- `csub`: `ts + 2^(64 n) top < 2m` reduced modulo `m`. -/
theorem csub_ok {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.X86_64.Scr s base size) {M : Mod}
    {ts : List Reg} {top : Reg} (hlen : ts.length = M.n) (hn : 0 < M.n) (hf : VG.Proof.Mont.X86_64.Fresh (top :: ts))
    (hmo : M.mo + 8 * M.n ≤ size) (htmp : M.tmp + 8 * M.n ≤ size)
    (hsep : M.mo + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ M.mo) {m : Nat}
    (hm : wordsVal s.mem base M.mo M.n = m)
    (hV : VG.Proof.Mont.X86_64.regsVal s ts + 2 ^ (64 * M.n) * (s.gpr top).toNat < 2 * m) :
    WP isa (.block (csub M ts top)) s fun s' =>
      VG.Proof.Mont.X86_64.regsVal s' ts = (VG.Proof.Mont.X86_64.regsVal s ts + 2 ^ (64 * M.n) * (s.gpr top).toNat) % m ∧
      VG.Proof.Mont.X86_64.KeepRegs (.rax :: .rdx :: ts) s s' ∧ Outside base M.tmp (8 * M.n) s.mem s'.mem := by
  obtain ⟨t, ts', rfl⟩ : ∃ t ts', ts = t :: ts' := by
    cases ts with
    | nil => simp at hlen; omega
    | cons t ts' => exact ⟨t, ts', rfl⟩
  have hft := hf.tail
  have htop := hf.head
  have hmX : m < 2 ^ (64 * M.n) := hm ▸ wordsVal_lt _ _ _ _
  rw [csub, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Mont.X86_64.diffs_ok hs (mo := M.mo) (tmp := M.tmp) (by rw [hlen]; omega) (by rw [hlen]; omega)
    (by rw [hlen]; omega) hft) fun s₁ ⟨b, c₁, e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Mont.X86_64.mask_ok s₁ top c₁) fun s₂ ⟨x₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have htop₁ : s₁.gpr top = s.gpr top := k₁.gpr top (by simp [htop.2.1])
  rw [htop₁] at x₂
  refine WP.mono (VG.Proof.Mont.X86_64.selects_ok _ (decide ((s.gpr top).toNat < b.toNat)) hs₂ (tmp := M.tmp)
    (by rw [hlen]; omega) hft (by rw [x₂]; simp only [decide_eq_true_eq]))
    fun s₃ ⟨e₃, k₃⟩ => ?_
  have hR₂ : VG.Proof.Mont.X86_64.regsVal s₂ (t :: ts') = VG.Proof.Mont.X86_64.regsVal s (t :: ts') := by
    rw [VG.Proof.Mont.X86_64.regsVal_congr fun q hq => k₂.1 q (by simp [(hft.2 q hq).1])]
    exact VG.Proof.Mont.X86_64.regsVal_congr fun q hq => k₁.gpr q (by simp [(hft.2 q hq).1])
  rw [hlen] at e₁ e₃
  rw [hm] at e₁
  rw [k₂.2.1] at e₃
  refine ⟨?_, (k₁.mono (by sub_regs)).trans (((Keeps.regs k₂).mono (by sub_regs)).trans
    ((Keeps.regs k₃).mono (by sub_regs))), fun x hx => ?_⟩
  · rw [e₃, hR₂]
    simp only [decide_eq_true_eq]
    exact csub_arith (b := b) hmX (wordsVal_lt _ _ _ _) hV e₁
  · rw [k₃.2.1, k₂.2.1, O₁ x (by rw [hlen]; exact hx)]

end VG.Proof.Mont.X86_64

end
