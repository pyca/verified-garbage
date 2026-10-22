module

public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512Tail.Rounds
import VerifiedGarbage.Proof.Framework.Block

/-!
# ChaCha20 on x86-64 with AVX-512, the last bytes: the rounds of five blocks

`rounds5` is `rounds2` with the second set's instructions in their 128-bit
forms (`HI.instr5`): each writes lane 0 of its register and zeroes the
others. The words of every lane are computed as in `rounds2` (`hstep`), but
the registers hold those of the second set in lane 0 only (`HH5`): what
`rounds2` proves of the first set's four blocks and of the second's first
then holds of `rounds5` (`HB5`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86_64.Avx512Tail

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx512Tail
open VG.Spec.ChaCha20 (Word innerBlock)
open VG.Proof.ChaCha20
open VG.Proof.ChaCha20.X86_64.Avx512 (xidx xidx_inj sel2_eq sel2_lt Same Same.trans zreg_xidx xidx_zreg)
open VG.Impl.ChaCha20.X86_64.Avx512 (zreg)

/-- A write of 128 bits (`VEX.128`, `EVEX.128`): lane 0 of the register, its
other lanes zeroed. -/
theorem zlane_setV128 (s : State) (d r : XReg) (lo hi : BitVec 128) {i : Nat} (hi4 : i < 4) :
    (s.setV .l128 d lo hi).zlane r i = if r = d then (if i = 0 then lo else 0) else s.zlane r i := by
  simp only [State.zlane, State.lane, State.setV]
  by_cases h : r = d
  · subst h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> simp
  · simp [h]

theorem lane0_zlane (s : State) (r : XReg) : s.lane r 0 = s.zlane r 0 := by
  simp [State.zlane]

/-- An instruction of the rounds, in its 128-bit form if it writes a register
of the second set. -/
def HI.instr5 (i : HI) : Instr :=
  match i with
  | .add d a b => if 4 ≤ xidx d then .vop (.vbin .vpaddd .l128 d a b) else i.instr
  | .xor d a b => if 4 ≤ xidx d then .vop (.vbin .vpxor .l128 d a b) else i.instr
  | .rol d a n => if 4 ≤ xidx d then .vop (.vprold .l128 d a n) else i.instr
  | .shuf d a o => if 4 ≤ xidx d then .vop (.vpshufd .l128 d a o) else i.instr

/-- The registers an instruction of the rounds reads or writes. -/
def HI.regs : HI → List XReg
  | .add d a b | .xor d a b => [d, a, b]
  | .rol d a _ | .shuf d a _ => [d, a]

/-- Its registers are all of the first set, or all of the second. -/
def HI.ok5 (i : HI) : Bool :=
  i.regs.all (fun r => decide (xidx r < 4)) || i.regs.all (fun r => decide (4 ≤ xidx r ∧ xidx r < 8))

/-- The registers hold the words of the four lanes, the second set's in lane
0 only. -/
def HH5 (ws : Nat → W) (s : State) : Prop :=
  ∀ r l q, l < 4 → q < 4 → (xidx r < 4 ∨ l = 0) → dword (s.zlane r l) q = ws l (4 * xidx r + q)

theorem HH.hh5 {ws : Nat → W} {s : State} (h : HH ws s) : HH5 ws s :=
  fun r l q hl hq _ => h r l q hl hq

/-- Of an instruction that is all of one set: in the first set, all of its
registers are; in the second, its sources are. -/
theorem ok5_cases {d : XReg} {rs : List XReg} (h : (d :: rs).all (fun r => decide (xidx r < 4)) ||
    (d :: rs).all (fun r => decide (4 ≤ xidx r ∧ xidx r < 8)) = true) :
    (xidx d < 4 ∧ ∀ r ∈ rs, xidx r < 4) ∨ (4 ≤ xidx d ∧ ∀ r ∈ rs, 4 ≤ xidx r) := by
  simp only [Bool.or_eq_true, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact .inl ⟨h₁, h₂⟩
  · exact .inr ⟨h₁.1, fun r hr => (h₂ r hr).1⟩

/-- One instruction of the rounds, in its 128-bit form on the second set. -/
theorem step5_ok (i : HI) (hi : i.ok5 = true) {ws : Nat → W} {s : State} (h : HH5 ws s) :
    ∃ s', exec i.instr5 s = some s' ∧ HH5 (fun l => hstep (ws l) i) s' ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  cases i with
  | add d a b =>
    rcases ok5_cases hi with ⟨hd, hs⟩ | ⟨hd, hs⟩
    · have ha := hs a (by simp); have hb := hs b (by simp)
      simp only [HI.instr5, show ¬ 4 ≤ xidx d by omega, ite_false, HI.instr]
      refine ⟨_, rfl, fun r l q hl hq hc => ?_, by simp, by simp, by simp, by simp⟩
      simp only [zlane_zbin _ _ _ _ _ _ hl, hstep, setRow_row _ _ _ _ hq, xidx_inj]
      split
      · simp only [ZBinOp.sse, dword_paddd _ _ hq]
        rw [h a l q hl hq (.inl ha), h b l q hl hq (.inl hb)]
      · exact h r l q hl hq hc
    · have ha := hs a (by simp); have hb := hs b (by simp)
      simp only [HI.instr5, hd, ite_true]
      refine ⟨_, rfl, fun r l q hl hq hc => ?_, by simp [VOp.exec], by simp [VOp.exec], by simp [VOp.exec],
        by simp [VOp.exec]⟩
      simp only [VOp.exec, zlane_setV128 _ _ _ _ _ hl, hstep, setRow_row _ _ _ _ hq, xidx_inj]
      split
      · rename_i hr; subst hr
        obtain rfl : l = 0 := by omega
        simp only [ite_true, VBinOp.sse, dword_paddd _ _ hq, lane0_zlane]
        rw [h a 0 q hl hq (.inr rfl), h b 0 q hl hq (.inr rfl)]
      · exact h r l q hl hq hc
  | xor d a b =>
    rcases ok5_cases hi with ⟨hd, hs⟩ | ⟨hd, hs⟩
    · have ha := hs a (by simp); have hb := hs b (by simp)
      simp only [HI.instr5, show ¬ 4 ≤ xidx d by omega, ite_false, HI.instr]
      refine ⟨_, rfl, fun r l q hl hq hc => ?_, by simp, by simp, by simp, by simp⟩
      simp only [zlane_zbin _ _ _ _ _ _ hl, hstep, setRow_row _ _ _ _ hq, xidx_inj]
      split
      · simp only [ZBinOp.sse, dword_pxor]
        rw [h a l q hl hq (.inl ha), h b l q hl hq (.inl hb)]
      · exact h r l q hl hq hc
    · have ha := hs a (by simp); have hb := hs b (by simp)
      simp only [HI.instr5, hd, ite_true]
      refine ⟨_, rfl, fun r l q hl hq hc => ?_, by simp [VOp.exec], by simp [VOp.exec], by simp [VOp.exec],
        by simp [VOp.exec]⟩
      simp only [VOp.exec, zlane_setV128 _ _ _ _ _ hl, hstep, setRow_row _ _ _ _ hq, xidx_inj]
      split
      · rename_i hr; subst hr
        obtain rfl : l = 0 := by omega
        simp only [ite_true, VBinOp.sse, dword_pxor, lane0_zlane]
        rw [h a 0 q hl hq (.inr rfl), h b 0 q hl hq (.inr rfl)]
      · exact h r l q hl hq hc
  | rol d a n =>
    rcases ok5_cases hi with ⟨hd, hs⟩ | ⟨hd, hs⟩
    · have ha := hs a (by simp)
      simp only [HI.instr5, show ¬ 4 ≤ xidx d by omega, ite_false, HI.instr]
      refine ⟨_, rfl, fun r l q hl hq hc => ?_, by simp, by simp, by simp, by simp⟩
      simp only [zlane_vprold _ _ _ _ _ hl, hstep, setRow_row _ _ _ _ hq, xidx_inj]
      split
      · rw [dword_rolDwords _ _ hq, h a l q hl hq (.inl ha)]
      · exact h r l q hl hq hc
    · have ha := hs a (by simp)
      simp only [HI.instr5, hd, ite_true]
      refine ⟨_, rfl, fun r l q hl hq hc => ?_, by simp [VOp.exec], by simp [VOp.exec], by simp [VOp.exec],
        by simp [VOp.exec]⟩
      simp only [VOp.exec, zlane_setV128 _ _ _ _ _ hl, hstep, setRow_row _ _ _ _ hq, xidx_inj]
      split
      · rename_i hr; subst hr
        obtain rfl : l = 0 := by omega
        simp only [ite_true, lane0_zlane]
        rw [dword_rolDwords _ _ hq, h a 0 q hl hq (.inr rfl)]
      · exact h r l q hl hq hc
  | shuf d a o =>
    rcases ok5_cases hi with ⟨hd, hs⟩ | ⟨hd, hs⟩
    · have ha := hs a (by simp)
      simp only [HI.instr5, show ¬ 4 ≤ xidx d by omega, ite_false, HI.instr]
      refine ⟨_, rfl, fun r l q hl hq hc => ?_, by simp, by simp, by simp, by simp⟩
      simp only [zlane_vpshufd _ _ _ _ _ hl, hstep, setRow_row _ _ _ _ hq, xidx_inj]
      split
      · rw [dword_shufDwords _ _ hq, sel2_eq, h a l _ hl (sel2_lt _ _) (.inl ha)]
      · exact h r l q hl hq hc
    · have ha := hs a (by simp)
      simp only [HI.instr5, hd, ite_true]
      refine ⟨_, rfl, fun r l q hl hq hc => ?_, by simp [VOp.exec], by simp [VOp.exec], by simp [VOp.exec],
        by simp [VOp.exec]⟩
      simp only [VOp.exec, zlane_setV128 _ _ _ _ _ hl, hstep, setRow_row _ _ _ _ hq, xidx_inj]
      split
      · rename_i hr; subst hr
        obtain rfl : l = 0 := by omega
        simp only [ite_true, lane0_zlane]
        rw [dword_shufDwords _ _ hq, sel2_eq, h a 0 _ hl (sel2_lt _ _) (.inr rfl)]
      · exact h r l q hl hq hc

/-- Instructions of the rounds, in sequence, with the second set's on 128 bits. -/
theorem block5_ok : ∀ (is : List HI), is.all HI.ok5 = true → ∀ {ws : Nat → W} {s : State}, HH5 ws s →
    WP isa (.block (is.map HI.instr5)) s fun s' => HH5 (fun l => is.foldl hstep (ws l)) s' ∧ Same s s'
  | [], _, _, _, h => WP.block_nil ⟨h, rfl, rfl, rfl, rfl⟩
  | i :: is, ha, _, _, h => by
    simp only [List.all_cons, Bool.and_eq_true] at ha
    obtain ⟨s', he, h', g, m, r, w⟩ := step5_ok i ha.1 h
    exact WP.block_cons_iff.2 ⟨s', he, WP.mono (block5_ok is ha.2 h') fun _ ⟨ht, hs⟩ =>
      ⟨ht, hs.gpr.trans g, hs.mem.trans m, hs.rd.trans r, hs.wr.trans w⟩⟩

theorem doubleRound5_eq : doubleRound5 = (cols2H ++ diags2H).map HI.instr5 := by
  decide

theorem ok5_all : (cols2H ++ diags2H).all HI.ok5 = true := by decide

/-! ## The five blocks -/

/-- The states of the first set's four blocks are in the registers (`HB 1`),
and that of the fifth block in lane 0 of the second set's. -/
def HB5 (vs : Nat → CState) (s : State) : Prop :=
  HB 1 vs s ∧ ∀ i (hi : i < 16), dword (s.zlane (zreg (4 + i / 4)) 0) (i % 4) = (vs 4)[i]

theorem HB.hb5 {vs : Nat → CState} {s : State} (h : HB 2 vs s) : HB5 vs s :=
  ⟨fun k hk l hl i hi => h k (by omega) l hl i hi, fun i hi => h 1 (by decide) 0 (by decide) i hi⟩

theorem doubleRound5_ok {vs : Nat → CState} {s : State} (h : HB5 vs s) :
    WP isa (.block doubleRound5) s fun s' => HB5 (fun j => innerBlock (vs j)) s' ∧ Same s s' := by
  rw [doubleRound5_eq]
  refine WP.mono (block5_ok _ ok5_all (hh_wordsOf s).hh5) fun s' ⟨h', hs⟩ => ⟨⟨?_, ?_⟩, hs⟩
  · intro k hk l hl i hi
    obtain rfl : k = 0 := by omega
    have e := h' (zreg (4 * 0 + i / 4)) l (i % 4) hl (Nat.mod_lt _ (by decide))
      (.inl (by rw [xidx_zreg _ (by omega)]; omega))
    rw [e, xidx_zreg _ (by omega), show 4 * (4 * 0 + i / 4) + i % 4 = 16 * 0 + i by omega]
    have b := dr2_words (wordsOf s l) (k := 0) (by decide)
    rw [blk_wordsOf h.1 (by decide) hl] at b
    have := congrArg (fun v : CState => v[i]) b
    simpa only [blk, Vector.getElem_ofFn, Nat.mul_zero, Nat.zero_add] using this
  · intro i hi
    have e := h' (zreg (4 + i / 4)) 0 (i % 4) (by decide) (Nat.mod_lt _ (by decide)) (.inr rfl)
    rw [e, xidx_zreg _ (by omega), show 4 * (4 + i / 4) + i % 4 = 16 * 1 + i by omega]
    have hb : blk (wordsOf s 0) 1 = vs 4 := by
      apply Vector.ext; intro j hj
      simp only [blk, Vector.getElem_ofFn, wordsOf]
      rw [show (16 * 1 + j) / 4 = 4 + j / 4 by omega, show (16 * 1 + j) % 4 = j % 4 by omega]
      exact h.2 j hj
    have b := dr2_words (wordsOf s 0) (k := 1) (by decide)
    rw [hb] at b
    have := congrArg (fun v : CState => v[i]) b
    simpa only [blk, Vector.getElem_ofFn] using this

theorem rounds5_ok {vs : Nat → CState} {s₀ : State} (h : HB5 vs s₀) :
    ∀ n, WP isa (rounds5 n) s₀ fun s => HB5 (fun j => Nat.repeat innerBlock n (vs j)) s ∧ Same s₀ s
  | 0 => WP.block_nil ⟨h, rfl, rfl, rfl, rfl⟩
  | n + 1 => WP.seq (WP.mono (rounds5_ok h n) fun _ ⟨h₁, hs⟩ =>
      WP.mono (doubleRound5_ok h₁) fun _ ⟨h₂, hs'⟩ => ⟨h₂, hs.trans hs'⟩)

/-- The state in lanes `l` of the second set's registers. -/
def regBlk (s : State) (l : Nat) : CState :=
  Vector.ofFn fun (i : Fin 16) => dword (s.zlane (zreg (4 + i.1 / 4)) l) (i.1 % 4)

/-- `vs` for the first five blocks, the second set's lanes 1–3 for the rest. -/
def vs5 (vs : Nat → CState) (s : State) (j : Nat) : CState :=
  if j < 5 then vs j else regBlk s (j - 4)

theorem HB5.hb2 {vs : Nat → CState} {s : State} (h : HB5 vs s) : HB 2 (vs5 vs s) s := by
  intro k hk l hl i hi
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · rw [vs5, ite_eq_left (by omega)]; exact h.1 0 (by decide) l hl i hi
  · by_cases hl0 : l = 0
    · subst hl0; rw [vs5, ite_eq_left (by omega)]; exact h.2 i hi
    · rw [vs5, ite_eq_right (by omega)]
      simp only [regBlk, Vector.getElem_ofFn, show 4 * 1 + l - 4 = l by omega]

end VG.Proof.ChaCha20.X86_64.Avx512Tail
