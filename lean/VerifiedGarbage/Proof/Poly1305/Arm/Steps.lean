module

public import VerifiedGarbage.Proof.Poly1305.Arm.Blocks
public import VerifiedGarbage.Proof.Poly1305.Arm.Umaal
import VerifiedGarbage.Proof.Poly1305.Stream
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Poly1305.Arm.Lit

/-!
# Poly1305 on 32-bit ARM: the steps of `blocks`, `update` and `finalize`

The code takes a flag, `umaal`, for its arithmetic: the baseline's, in radix
`2¹³` (`Bytes.lean`, `Blocks.lean`), or that of CPUs with `umaal`, in radix
`2³²` (`Umaal.lean`). What the functions need of either is the same
(`AccI`): at a block boundary (`Acc`), the accumulator is congruent modulo
`p` to an accumulator followed by some blocks; the setup (`setupAcc_ok`),
absorbing a block (`absorbI_ok`, `absorbAcc_ok`), the loop body of `blocks`
over any blocks (`body_gen`), and reducing and storing the accumulator
(`reduceI_ok`, `storeAcc_ok`) keep track of them, each proven for both by
cases. The callee-saved registers are saved in and restored from `scratch`
(`saveScr_ok`, `restoreScr_ok`), and bytes are copied into the buffer, bytes
56–71 of the state (`copy_ok`). `blocks` itself is the last section.
-/

@[expose] public section

namespace VG.Proof.Poly1305.Arm

open VG VG.Arm VG.Impl.Poly1305.Arm
open VG.Spec.Poly1305 (P leNum bytesAt accumulate Repr)

/-! ## At a block boundary, for either arithmetic -/

/-- What holds at a block boundary of the state at `B` and the registers,
with the accumulator congruent to `v` modulo `p`: for the baseline, the limbs
`R` of `r` are stored and the columns (`ColsD`) are below the bound that
keeps the next ones in a word; with `umaal`, `WAcc`. -/
def AccI : Bool → Addr → (Nat → Nat) → Nat → State → Prop
  | false, B, R, v, s => (∀ k < 10, rval s.mem B k = R k) ∧
      ∃ D, ColsD D B s ∧ (∀ k < 10, D k ≤ 3564723200) ∧ val D % P = v % P
  | true, B, R, v, s => WAcc B (val R) v s

theorem AccI.congr {umaal : Bool} {B : Addr} {R : Nat → Nat} {v v' : Nat} {s : State}
    (h : AccI umaal B R v s) (hv : v % P = v' % P) : AccI umaal B R v' s := by
  cases umaal
  · obtain ⟨hr, D, hc, hb, hd⟩ := h
    exact ⟨hr, D, hc, hb, hd.trans hv⟩
  · exact WAcc.congr h hv

theorem wregs_yregs : ∀ q ∈ wregs, q ∈ yregs := by decide

/-- `AccI` holds while the registers `r3`–`r11` and the state's words at
`[16, 20)` and `[88, 124)` stay. -/
theorem AccI.keep {umaal : Bool} {B : Addr} {R : Nat → Nat} {v : Nat} {s s' : State} (h : AccI umaal B R v s)
    {ws : List Reg} {l : List (Nat × Nat)} (hk : KeepsF ws (offR B l) s s')
    (hn : ∀ r ∈ ws, r ∉ yregs)
    (hl : (l.all fun p => (20 ≤ p.1 ∨ p.1 + p.2 ≤ 16) ∧ (124 ≤ p.1 ∨ p.1 + p.2 ≤ 88)) = true)
    (hl' : (l.all fun p => p.1 + p.2 < 2 ^ 32) = true) : AccI umaal B R v s' := by
  cases umaal
  · obtain ⟨hr, D, hcD, hDb, hDv⟩ := h
    refine ⟨fun k hk' => ?_, D, ⟨fun k hk' => ?_, ?_⟩, hDb, hDv⟩
    · rw [rval_frame' hk.frame (by
        rw [List.all_eq_true] at hl ⊢
        intro p hp; have := hl p hp; simp only [decide_eq_true_eq] at this ⊢; exact this.2) hl' hk']
      exact hr k hk'
    · rw [hk.gpr _ fun h' => hn _ h' (yr_yregs k hk')]; exact hcD.1 k hk'
    · rw [hk.frame.word (by
        rw [List.all_eq_true] at hl ⊢
        intro p hp; have := hl p hp; simp only [decide_eq_true_eq] at this ⊢; omega_using [this]) (by decide) hl']
      exact hcD.2
  · refine WAcc.keep h (fun q hq => hk.gpr _ fun h' => hn _ h' (wregs_yregs q hq)) fun i hi => ?_
    exact hk.frame.word (by
      rw [List.all_eq_true] at hl ⊢
      intro p hp; have := hl p hp; simp only [decide_eq_true_eq] at this ⊢; omega_using [this, hi])
      (by omega_using [hi]) hl'

/-- `r0` points at the state `st`, and (`AccI`) the accumulator is congruent
modulo `p` to the accumulator `A` followed by the blocks `X`, with `R` the
limbs of `r`. -/
structure Acc (umaal : Bool) (st : BitVec 32) (R : Nat → Nat) (A : Nat) (X : List Byte) (s : State) :
    Prop where
  r0 : s.gpr .r0 = st
  wr : stR st ∈ s.wr
  inv : AccI umaal (State.addr st) R (Poly1305.absorbAll (val R) A X) s

/-- `Acc` holds while the registers `r0` and `r3`–`r11`, the writable regions
and the state's words at `[16, 20)` and `[88, 124)` stay. -/
theorem Acc.keep {umaal : Bool} {st : BitVec 32} {R : Nat → Nat} {A : Nat} {X : List Byte} {s s' : State}
    (h : Acc umaal st R A X s) {ws : List Reg} {l : List (Nat × Nat)}
    (hk : KeepsF ws (offR (State.addr st) l) s s')
    (hws : (ws.all fun r => r != .r0 && !yregs.contains r) = true)
    (hl : (l.all fun p => (20 ≤ p.1 ∨ p.1 + p.2 ≤ 16) ∧ (124 ≤ p.1 ∨ p.1 + p.2 ≤ 88)) = true)
    (hl' : (l.all fun p => p.1 + p.2 < 2 ^ 32) = true) : Acc umaal st R A X s' := by
  obtain hn : ∀ r ∈ ws, r ≠ .r0 ∧ r ∉ yregs := fun r hr => by
    have := List.all_eq_true.mp hws r hr
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at this
    exact this
  exact ⟨by rw [hk.gpr _ fun h' => (hn _ h').1 rfl, h.r0], by rw [hk.wr]; exact h.wr,
    h.inv.keep hk (fun r hr => (hn r hr).2) hl hl'⟩

/-! ## The code of either arithmetic -/

theorem setup_false : setup false = setupR ++ loadAcc := rfl
theorem setup_true : setup true = setupU ++ loadAccU := rfl
theorem absorbV_false (pad : Bool) : absorbV false pad = absorb pad := rfl
theorem absorbV_true (pad : Bool) : absorbV true pad = absorbU pad := rfl
theorem reduceV_false : reduceV false = reduce ++ toWords := rfl
theorem reduceV_true : reduceV true = reduceU := rfl

section
variable {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32)
include hfit

/-- The multipliers and the accumulator, from the state's key and accumulator. -/
theorem setupAcc_ok {umaal : Bool} {s : State} (h0 : s.gpr .r0 = st) (hw : stR st ∈ s.wr) :
    WP isa (.block (setup umaal)) s fun s' =>
      AccI umaal (State.addr st) (rlimb s.mem (State.addr st)) (val (accD s.mem (State.addr st))) s' ∧
      KeepsF (.r1 :: .r2 :: .r12 :: yregs) (offR (State.addr st) [(0, 20), (88, 36)]) s s' := by
  cases umaal
  · rw [setup_false]
    exact WP.mono (setupB_ok hfit h0 hw) fun s' ⟨hr, hc, k⟩ =>
      ⟨⟨hr, _, hc, fun k _ => by have := accD_lt s.mem (State.addr st) k; omega_using [this], rfl⟩, k⟩
  · rw [setup_true]
    refine WP.mono (setupU_wacc hfit h0 hw) fun s' ⟨ha, k⟩ => ⟨ha, (k.mono ?_).sub ?_⟩
    · decide
    · intro r hr
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_map.mpr ⟨(88, 36), by decide, rfl⟩, fun _ h => h⟩

/-- Absorbing the block at `r1`, plus `2¹²⁸` if `pad`. -/
theorem absorbI_ok {umaal : Bool} (pad : Bool) {R : Nat → Nat} (hR : ∀ i < 10, R i < 2 ^ 13) {v : Nat}
    {s : State} (h0 : s.gpr .r0 = st) (hw : stR st ∈ s.wr) (h : AccI umaal (State.addr st) R v s)
    (hin : ∀ i < 4, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * i))) 4) :
    WP isa (.block (absorbV umaal pad)) s fun s' =>
      AccI umaal (State.addr st) R ((v + msgVal s + if pad then 2 ^ 128 else 0) * val R) s' ∧
      KeepsF work [accR (State.addr st)] s s' := by
  cases umaal
  · obtain ⟨hr, D, hcD, hDb, hDv⟩ := h
    rw [absorbV_false]
    refine WP.mono (absorb_ok hfit pad hR hDb h0 hw hr hcD hin) fun s' ⟨D', hc', hb', hv', k'⟩ =>
      ⟨⟨fun k hk => ?_, D', hc', hb', ?_⟩, k'⟩
    · rw [rval_frame k'.frame hk]; exact hr k hk
    · rw [hv', Nat.mul_mod, Nat.add_mod (val D + msgVal s), Nat.add_mod (val D), hDv, ← Nat.add_mod v,
        ← Nat.add_mod, ← Nat.mul_mod]
  · rw [absorbV_true]
    exact WP.mono (absorbU_wacc hfit pad h0 hw h hin) fun s' ⟨ha, k⟩ => ⟨ha, k.keepsF _⟩

/-- Absorbing the block at `a`, at `r1`. -/
theorem absorbAcc_ok {umaal : Bool} {R : Nat → Nat} (hR : ∀ i < 10, R i < 2 ^ 13) {A : Nat} {X : List Byte}
    (hX : X.length % 16 = 0) {s : State} (h : Acc umaal st R A X s) {a : Addr}
    (ha : ∀ j < 4, State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * j)) = a + BitVec.ofNat 64 (4 * j))
    (hin : ∀ j < 4, InRegions (s.rd ++ s.wr) (a + BitVec.ofNat 64 (4 * j)) 4) :
    WP isa (.block (absorbV umaal true)) s fun s' =>
      Acc umaal st R A (X ++ bytesAt s.mem a 16) s' ∧ KeepsF work [accR (State.addr st)] s s' := by
  refine WP.mono (absorbI_ok hfit true hR h.r0 h.wr h.inv fun j hj => by rw [ha j hj]; exact hin j hj)
    fun s' ⟨hi', k'⟩ => ⟨⟨by rw [k'.gpr _ (by decide), h.r0], by rw [k'.wr]; exact h.wr, hi'.congr ?_⟩, k'⟩
  have hmsg : msgVal s = leNum (bytesAt s.mem a 16) := by
    rw [leNum_bytesAt_16, msgVal]
    simp only [word]
    rw [ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide)]
  obtain hl := Poly1305.length_bytesAt s.mem a 16
  rw [Poly1305.absorbAll_append hX,
    Poly1305.absorbAll_block (b := bytesAt s.mem a 16) (by omega_using [hl]) (by omega_using [hl]), hmsg,
    leNum_pad _ hl, iteT rfl, Nat.mod_mod, Nat.mul_comm (val R), Nat.add_assoc]

omit hfit in
theorem body_eq (umaal : Bool) :
    body umaal = .block (([.ldr .r1 .r0 ptrOff, .dp .add .r2 .r1 (.imm 16), .str .r2 .r0 ptrOff] : List Instr) ++
      (absorbV umaal true ++ ([.ldr .r1 .r0 cntOff, .subs .r1 .r1 (.imm 1), .str .r1 .r0 cntOff] : List Instr))) := by
  simp only [body, List.append_assoc]

/-- The loop body of `blocks`, with the block pointer `p` and the count `c`
stored in the state. -/
theorem body_gen {umaal : Bool} {R : Nat → Nat} (hR : ∀ i < 10, R i < 2 ^ 13) {A : Nat} {X : List Byte}
    (hX : X.length % 16 = 0) {s : State} (h : Acc umaal st R A X s) {p : BitVec 32} {c : Nat}
    (hptr : s.mem.readW (State.addr st + BitVec.ofNat 64 124) 32 = p)
    (hcnt : s.mem.readW (State.addr st + BitVec.ofNat 64 20) 32 = BitVec.ofNat 32 c) (hc : 0 < c)
    (hc32 : c < 2 ^ 32) (hpf : p.toNat + 16 ≤ 2 ^ 32)
    (hin : ∀ j < 4, InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 (4 * j)) 4)
    (hd : (⟨State.addr p, 16⟩ : Region).Disjoint ⟨State.addr st + BitVec.ofNat 64 124, 4⟩) :
    WP isa (body umaal) s fun s' => Acc umaal st R A (X ++ bytesAt s.mem (State.addr p) 16) s' ∧
      KeepsF work (offR (State.addr st) [(0, 24), (124, 4)]) s s' ∧
      s'.mem.readW (State.addr st + BitVec.ofNat 64 124) 32 = p + 16 ∧
      s'.mem.readW (State.addr st + BitVec.ofNat 64 20) 32 = BitVec.ofNat 32 (c - 1) ∧
      s'.z = decide (c - 1 = 0) := by
  have hs0 := h.r0
  have hw := h.wr
  rw [body_eq, List.cons_append, List.cons_append, List.cons_append, List.nil_append]
  refine wp_ldr (a := State.addr st + BitVec.ofNat 64 124) (by decide)
    (by rw [hs0]; exact ea hfit (off := 124) (by decide)) (inSt hw (off := 124) (n := 4) (by decide))
    fun s₁ u₁ => ?_
  refine wp_add (op2_imm (by decide)) fun s₂ u₂ => ?_
  refine wp_str (a := State.addr st + BitVec.ofNat 64 124) (by decide)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hs0]; exact ea hfit (off := 124) (by decide))
    (by rw [u₂.wr, u₁.wr]; exact outSt hw (off := 124) (n := 4) (by decide)) fun s₃ u₃ => ?_
  obtain hp₃ : s₃.gpr .r1 = p := by rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, hptr]
  obtain m₃ : s₃.mem = s.mem.writeW (State.addr st + BitVec.ofNat 64 124) (p + 16) := by
    rw [u₃.mem, u₂.gpr, u₁.gpr, u₂.mem, u₁.mem, hptr]
  obtain f₃ : Frame (offR (State.addr st) [(124, 4)]) s.mem s₃.mem := by
    rw [m₃]
    exact Frame.writeOff (Frame.refl _ _) (a := 124) (len := 4) (List.mem_singleton_self _) (Nat.le_refl _) (Nat.le_refl _)
      (by decide) _ rfl
  obtain k₃ : KeepsF [.r1, .r2] (offR (State.addr st) [(124, 4)]) s s₃ :=
    ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [u₃.gpr, u₂.other _ hr.2, u₁.other _ hr.1],
      f₃, by rw [u₃.rd, u₂.rd, u₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr], by rw [u₃.sp, u₂.sp, u₁.sp]⟩
  obtain hA₃ : Acc umaal st R A X s₃ := h.keep k₃ (by decide) (by decide) (by decide)
  obtain hblk : bytesAt s₃.mem (State.addr p) 16 = bytesAt s.mem (State.addr p) 16 :=
    bytesAt_frame f₃ (fun r hr => by
      simp only [offR, List.map_cons, List.map_nil, List.mem_singleton] at hr; subst hr; exact hd)
      (by decide)
  rw [← List.append_nil [Instr.ldr .r1 .r0 cntOff, .subs .r1 .r1 (.imm 1), .str .r1 .r0 cntOff]]
  refine WP.append (absorbAcc_ok hfit hR hX hA₃ (a := State.addr p)
    (fun j hj => by rw [hp₃]; exact addr_add (by omega_using [hpf, hj]))
    (fun j hj => by rw [k₃.rd, k₃.wr]; exact hin j hj)) fun s₄ ⟨hA₄, k₄⟩ => ?_
  rw [hblk] at hA₄
  have hs40 : s₄.gpr .r0 = st := hA₄.r0
  have hw₄ : stR st ∈ s₄.wr := hA₄.wr
  obtain f₄ : Frame (offR (State.addr st) [(0, 20)]) s₃.mem s₄.mem := by rw [← accR_offR]; exact k₄.frame
  refine wp_ldr (a := State.addr st + BitVec.ofNat 64 20) (by decide)
    (by rw [hs40]; exact ea hfit (off := 20) (by decide)) (inSt hw₄ (off := 20) (n := 4) (by decide))
    fun s₅ u₅ => ?_
  refine wp_subs (op2_imm (by decide)) fun s₆ u₆ hz₆ => ?_
  refine wp_str (a := State.addr st + BitVec.ofNat 64 20) (by decide)
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), hs40]; exact ea hfit (off := 20) (by decide))
    (by rw [u₆.wr, u₅.wr]; exact outSt hw₄ (off := 20) (n := 4) (by decide)) fun s₇ u₇ => WP.block_nil ?_
  obtain hc₅ : s₅.gpr .r1 = BitVec.ofNat 32 c := by
    rw [u₅.gpr, f₄.word (by decide) (by decide) (by decide), f₃.word (by decide) (by decide) (by decide), hcnt]
  obtain hc₆ : s₆.gpr .r1 = BitVec.ofNat 32 (c - 1) := by
    rw [u₆.gpr, hc₅, show c = (c - 1) + 1 by omega_using [hc, hc32], BitVec.ofNat_add, Nat.add_sub_cancel]
    exact BitVec.add_sub_cancel _ _
  obtain m₇ : s₇.mem = s₄.mem.writeW (State.addr st + BitVec.ofNat 64 20) (BitVec.ofNat 32 (c - 1)) := by
    rw [u₇.mem, hc₆, u₆.mem, u₅.mem]
  obtain k₄₇ : KeepsF [.r1] (offR (State.addr st) [(20, 4)]) s₄ s₇ := by
    refine ⟨fun r hr => ?_, ?_, by rw [u₇.rd, u₆.rd, u₅.rd], by rw [u₇.wr, u₆.wr, u₅.wr],
      by rw [u₇.sp, u₆.sp, u₅.sp]⟩
    · have h1 : r ≠ .r1 := by rintro rfl; exact hr (by decide)
      rw [u₇.gpr, u₆.other _ h1, u₅.other _ h1]
    · rw [m₇]
      exact Frame.writeOff (Frame.refl _ _) (a := 20) (len := 4) (List.mem_singleton_self _) (Nat.le_refl _) (Nat.le_refl _)
        (by decide) _ rfl
  refine ⟨hA₄.keep k₄₇ (by decide) (by decide) (by decide), ?_, ?_, by rw [m₇, Mem.readW_writeW_self32], ?_⟩
  · refine ((k₃.mono (by simp [work])).sub (sub_offR _ (by decide) (by decide))).trans
      (((k₄.sub (by rw [accR_offR]; exact sub_offR _ (by decide) (by decide))).trans
        ((k₄₇.mono (by simp [work])).sub (sub_offR _ (by decide) (by decide)))))
  · rw [m₇, readW_writeW_off _ _ _ (by decide) (by decide) (by decide),
      f₄.word (by decide) (by decide) (by decide), m₃, Mem.readW_writeW_self32]
  · rw [u₇.z, hz₆, ← u₆.gpr, hc₆, ofNat_beq_zero (by omega_using [hc, hc32])]

/-- The accumulator reduced fully: its words, of `v mod p`. -/
theorem reduceI_ok {umaal : Bool} {R : Nat → Nat} {v : Nat} {s : State} (h0 : s.gpr .r0 = st)
    (hw : stR st ∈ s.wr) (h : AccI umaal (State.addr st) R v s) :
    WP isa (.block (reduceV umaal)) s fun s' => ∃ w0 w1 w2 w3 w4, OutW w0 w1 w2 w3 w4 s' ∧
      Limbs32.val5 w0 w1 w2 w3 w4 = v % P ∧ Keeps work s s' := by
  cases umaal
  · obtain ⟨-, D, hcD, hDb, hDv⟩ := h
    obtain hE : ∀ j < 10, D j < 2 ^ 32 - 2 ^ 19 := fun j hj => by have := hDb j hj; omega_using [this]
    obtain ⟨-, -, -, hvL, hlL⟩ := red_facts D hE
    rw [reduceV_false]
    refine WP.append (reduce_ok hfit hDb h0 hw hcD) fun s₁ ⟨hc₁, k₁⟩ => ?_
    refine WP.mono (toWords_ok hc₁ fun j hj => hlL j (by omega_using [hj])) fun s₂ ⟨e3, e5, e7, e10, e1, k₂⟩ =>
      ⟨_, _, _, _, _, ⟨e3, e5, e7, e10, e1⟩, ?_, ?_⟩
    · rw [← hDv, ← hvL, val_toWords fun j hj => hlL j (by omega_using [hj])]
      rfl
    · exact (k₁.mono (by decide)).trans (k₂.mono (by decide))
  · rw [reduceV_true]
    exact reduceU_wacc h

/-- Reducing the accumulator fully and storing it. -/
theorem storeAcc_ok {umaal : Bool} {R : Nat → Nat} {A : Nat} {X : List Byte} {s : State}
    (h : Acc umaal st R A X s) :
    WP isa (.block (reduceV umaal ++ storeAcc)) s fun s' =>
      leNum (bytesAt s'.mem (State.addr st) 24) = Poly1305.absorbAll (val R) A X % P ∧
      KeepsF work (offR (State.addr st) [(0, 24)]) s s' := by
  refine WP.append (reduceI_ok hfit h.r0 h.wr h.inv) fun s₂ ⟨w0, w1, w2, w3, w4, ⟨o3, o5, o7, o10, o1⟩, hv, k₂⟩ => ?_
  obtain hs₂0 : s₂.gpr .r0 = st := by rw [k₂.gpr _ (by decide), h.r0]
  obtain hw₂ : stR st ∈ s₂.wr := by rw [k₂.wr]; exact h.wr
  rw [show storeAcc = accList.map (storeI .r0) ++ [.mov .r2 (.imm 0), .str .r2 .r0 20] from rfl]
  refine WP.append (stores_ok .r0 hfit rfl accList s₂ hs₂0 hw₂ (by decide) (by decide))
    fun s₃ ⟨hs₃, hf₃, hg₃, hrd₃, hwr₃, hsp₃⟩ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₄ u₄ => ?_
  refine wp_str (a := State.addr st + BitVec.ofNat 64 20) (by decide)
    (by rw [u₄.other _ (by decide), hg₃, hs₂0]; exact ea hfit (off := 20) (by decide))
    (by rw [u₄.wr, hwr₃]; exact outSt hw₂ (off := 20) (n := 4) (by decide)) fun s₅ u₅ => WP.block_nil ?_
  obtain m₅ : s₅.mem = s₃.mem.writeW (State.addr st + BitVec.ofNat 64 20) (0 : BitVec 32) := by
    rw [u₅.mem, u₄.gpr, u₄.mem]
  obtain f₅ : Frame (offR (State.addr st) [(0, 24)]) s.mem s₅.mem := by
    rw [m₅, ← k₂.mem]
    rw [accList_frame] at hf₃
    exact Frame.writeOff (hf₃.offR_sub (by decide) (by decide)) (a := 0) (len := 24) (by decide) (by decide)
      (by decide) (by decide) _ rfl
  -- The words stored.
  obtain w : ∀ x ∈ accList, ∀ d, x.2.1 = d → x.2.2 = false →
      s₅.mem.readW (State.addr st + BitVec.ofNat 64 d) 32 = s₂.gpr x.1 := by
    intro x hx d hd hb
    have := hs₃ x hx
    obtain ⟨r, o, b⟩ := x
    simp only at hd hb; subst hd hb
    obtain hl : o + 4 ≤ 20 := by
      have : ∀ x ∈ accList, x.2.1 + 4 ≤ 20 := by decide
      exact this _ hx
    rw [m₅, readW_writeW_off _ _ _ (by omega_using [hl]) (by decide) (by omega_using [hl])]
    exact this
  refine ⟨?_, ⟨fun r hr => ?_, f₅, ?_, ?_, ?_⟩⟩
  · have e0 := w _ (by decide : (Reg.r3, 0, false) ∈ accList) 0 rfl rfl
    obtain e4 := w _ (by decide : (Reg.r5, 4, false) ∈ accList) 4 rfl rfl
    obtain e8 := w _ (by decide : (Reg.r7, 8, false) ∈ accList) 8 rfl rfl
    obtain e12 := w _ (by decide : (Reg.r10, 12, false) ∈ accList) 12 rfl rfl
    obtain e16 := w _ (by decide : (Reg.r1, 16, false) ∈ accList) 16 rfl rfl
    obtain e20 : s₅.mem.readW (State.addr st + BitVec.ofNat 64 20) 32 = 0 := by rw [m₅, Mem.readW_writeW_self32]
    simp only at e0 e4 e8 e12 e16
    rw [leNum_bytesAt_24, e0, e4, e8, e12, e16, e20, o3, o5, o7, o10, o1, ← hv]
    rfl
  · obtain h2 : r ≠ .r2 := by rintro rfl; exact hr (by decide)
    rw [u₅.gpr, u₄.other _ h2, hg₃]
    exact k₂.gpr r hr
  · rw [u₅.rd, u₄.rd, hrd₃, k₂.rd]
  · rw [u₅.wr, u₄.wr, hwr₃, k₂.wr]
  · rw [u₅.sp, u₄.sp, hsp₃, k₂.sp]

end

theorem accD_of_words {m m' : Mem} {B : Addr}
    (h : ∀ i < 5, m'.readW (B + BitVec.ofNat 64 (4 * i)) 32 = m.readW (B + BitVec.ofNat 64 (4 * i)) 32) :
    accD m' B = accD m B := by
  obtain hw : ∀ i < 5, hwd m' B i = hwd m B i := fun i hi => by simp only [hwd, h i hi]
  funext k
  simp only [accD, hw 0 (by decide), hw 1 (by decide), hw 2 (by decide), hw 3 (by decide), hw 4 (by decide)]

/-! ## Arguments on the stack -/

theorem wp_sub {is : List Instr} {s : State} {Q : State → Prop} {d n : Reg} {o : Op2} {y : BitVec 32}
    (ho : o.eval s = some y) (k : ∀ s', Upd s s' d (s.gpr n - y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .sub d n o :: is)) s Q :=
  WP.cons (s' := s.setReg d (s.gpr n - y)) (by simp [exec, ho]) (k _ (Upd.setReg _ _ _))

theorem Fupd.keeps {s s' : State} (h : Fupd s s') (ws : List Reg) : Keeps ws s s' :=
  ⟨fun r _ => by rw [h.gpr], h.mem, h.rd, h.wr, h.sp⟩

theorem wp_ldrSp {is : List Instr} {s : State} {Q : State → Prop} {t : Reg} {off : Nat} {a : Addr}
    (ho : off < 4096) (ha : State.addr (s.sp + BitVec.ofNat 32 off) = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', Upd s s' t (s.mem.readW a 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldrSp t off :: is)) s Q := by
  subst ha
  exact WP.cons (s' := s.setReg t (s.mem.readW _ 32)) (by simp [exec, ho, State.load32, hin])
    (k _ (Upd.setReg _ _ _))

/-! ## The registers saved in `scratch` -/

/-- The registers `g` saved at `[0, 32)` of the scratch space at `C`. -/
def SavedS (C : Addr) (g : Reg → BitVec 32) (m : Mem) : Prop :=
  ∀ i < 8, m.readW (C + BitVec.ofNat 64 (4 * i)) 32 = g (savedReg i)

def saveSList : List (Reg × Nat × Bool) := (List.range 8).map fun i => (savedReg i, 4 * i, false)

theorem saveScr_eq : saveScr = saveSList.map (storeI .r12) := rfl

/-- The scratch space's region. -/
abbrev scrR (sc : BitVec 32) : Region := ⟨State.addr sc, 128⟩

section
variable {sc : BitVec 32} (hsc : sc.toNat + 128 ≤ 2 ^ 32)
include hsc

theorem saveScr_ok {s : State} (h12 : s.gpr .r12 = sc) (hw : scrR sc ∈ s.wr) :
    WP isa (.block saveScr) s fun s' => SavedS (State.addr sc) s.gpr s'.mem ∧
      Frame [⟨State.addr sc, 32⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
  rw [saveScr_eq]
  refine WP.mono (stores_ok .r12 hsc rfl saveSList s h12 hw (by decide) (by decide))
    fun s' ⟨hs, hf, hg, hrd, hwr, hsp⟩ => ⟨fun i hi => ?_, hf.sub fun r hr => ?_, hg, hrd, hwr, hsp⟩
  · exact hs (savedReg i, 4 * i, false) (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have := List.mem_range.mp hi
    exact ⟨_, List.mem_singleton_self _, sub_base _ (by simp only [ssize]; omega_using [this]) (by decide)⟩

theorem restoreScr_ok {s : State} {g : Reg → BitVec 32} (h12 : s.gpr .r12 = sc) (hw : scrR sc ∈ s.wr)
    (hs : SavedS (State.addr sc) g s.mem) :
    WP isa (.block restoreScr) s fun s' => (∀ i < 8, s'.gpr (savedReg i) = g (savedReg i)) ∧
      Keeps [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] s s' := by
  obtain hsr : ∀ i < 8, savedReg i ∈ [Reg.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] := by decide +kernel
  obtain hinj : ∀ i < 8, ∀ j < 8, savedReg i = savedReg j → i = j := by decide +kernel
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s' => (∀ i < n, s'.gpr (savedReg i) = g (savedReg i)) ∧
      Keeps [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] s s')
    (fun n s' hn ⟨hl, hk⟩ => ?_) 8 (Nat.le_refl _) s ⟨fun _ h => absurd h (by omega_using [h]), Keeps.refl _ _⟩)
    fun s' h => h
  refine wp_ldr (a := State.addr sc + BitVec.ofNat 64 (4 * n)) (by omega_using [hn])
    (by rw [hk.gpr _ (by decide), h12]; exact addr_add (by omega_using [hsc, hn]))
    (by rw [hk.rd, hk.wr]; exact ⟨_, List.mem_append_right _ hw, contains_off (by omega_using [hn]) (by omega_using [hn])⟩)
    fun s1 u1 => WP.block_nil ⟨fun i hi => ?_, hk.trans (u1.keeps (hsr n hn))⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | rfl
  · rw [u1.other _ (fun e => absurd (hinj _ (by omega_using [hn, h']) _ hn e) (by omega_using [h']))]; exact hl i h'
  · rw [u1.gpr, hk.mem]; exact hs i hn

end

/-! ## Copying bytes into the buffer -/

theorem add_ofNat_one (x : BitVec 32) (j : Nat) : x + BitVec.ofNat 32 j + 1 = x + BitVec.ofNat 32 (j + 1) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl

/-- The buffer of the state at `B`. -/
abbrev bufR (B : Addr) : Region := ⟨B + BitVec.ofNat 64 56, 16⟩

/-- What copying the bytes `xs` from `src` needs, in the state `sI`: they are
readable, not in the buffer, and in memory. -/
def SrcOk (sI : State) (B : Addr) (src : BitVec 32) (xs : List Byte) : Prop :=
  ∀ i < xs.length, InRegions (sI.rd ++ sI.wr) (State.addr src + BitVec.ofNat 64 i) 1 ∧
    ¬ (bufR B).Contains (State.addr src + BitVec.ofNat 64 i) 1 ∧
    sI.mem (State.addr src + BitVec.ofNat 64 i) = xs.getD i 0

/-- While copying the bytes `xs` from `src` to the buffer of the state at `st`
from its byte `j0` on, from the state `sI`: after `j` bytes. -/
structure CopyInv (sI : State) (st src : BitVec 32) (j0 : Nat) (xs : List Byte) (j : Nat) (s : State) :
    Prop where
  j_le : j ≤ xs.length
  r5 : s.gpr .r5 = src + BitVec.ofNat 32 j
  r1 : s.gpr .r1 = st + BitVec.ofNat 32 (j0 + j)
  r8 : s.gpr .r8 = BitVec.ofNat 32 (xs.length - j)
  keep : ∀ r, r ∉ [Reg.r1, .r5, .r8, .r12] → s.gpr r = sI.gpr r
  rd : s.rd = sI.rd
  wr : s.wr = sI.wr
  sp : s.sp = sI.sp
  mem : s.mem = writeBytes sI.mem (State.addr st + BitVec.ofNat 64 (56 + j0)) (xs.take j)

section
variable {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32)
include hfit

theorem copy_step {sI : State} {src : BitVec 32} {j0 : Nat} {xs : List Byte} (hj0 : j0 + xs.length ≤ 16)
    (hsrc : src.toNat + xs.length ≤ 2 ^ 32) (hw : stR st ∈ sI.wr) (hS : SrcOk sI (State.addr st) src xs)
    {j : Nat} (hj : j < xs.length) {s : State} (h : CopyInv sI st src j0 xs j s) :
    WP isa (.block copyBody) s fun s' =>
      CopyInv sI st src j0 xs (j + 1) s' ∧ s'.z = decide (xs.length - (j + 1) = 0) := by
  obtain ⟨hin, hnb, hm₀⟩ := hS j hj
  obtain hq : (bufR (State.addr st)).Contains (State.addr st + BitVec.ofNat 64 (56 + j0)) (xs.take j).length := by
    rw [List.length_take]
    exact contains_sub _ (by omega_using []) (by omega_using [hj0, hj]) (by decide)
  obtain hbyte : s.mem (State.addr src + BitVec.ofNat 64 j) = xs.getD j 0 := by
    rw [h.mem, ← hm₀]
    exact writeBytes_frame _ _ _ hq _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hnb
  refine wp_ldrb (t := .r12) (a := State.addr src + BitVec.ofNat 64 j) (by decide)
    (by rw [h.r5, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_zero]; exact addr_add (by omega_using [hsrc, hj]))
    (by rw [h.rd, h.wr]; exact hin) fun s₁ u₁ => ?_
  refine wp_strb (t := .r12) (a := State.addr st + BitVec.ofNat 64 (56 + j0 + j)) (by decide)
    (by rw [u₁.other _ (by decide), h.r1, BitVec.add_assoc, ← BitVec.ofNat_add,
      show j0 + j + 56 = 56 + j0 + j by omega_using []]; exact ea hfit (by omega_using [hj0, hj]))
    (by rw [u₁.wr, h.wr]; exact outSt hw (by omega_using [hj0, hj])) fun s₂ m₂ => ?_
  refine wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_add (op2_imm (by decide)) fun s₄ u₄ => ?_
  refine wp_subs (op2_imm (by decide)) fun s₅ u₅ hz => WP.block_nil ?_
  obtain hr8 : s₅.gpr .r8 = BitVec.ofNat 32 (xs.length - (j + 1)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), m₂.gpr, u₁.other _ (by decide), h.r8,
      show xs.length - j = (xs.length - (j + 1)) + 1 by omega_using [hj], BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _
  refine ⟨⟨by omega_using [hj], ?_, ?_, hr8, fun r hr => ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, m₂.gpr, u₁.other _ (by decide), h.r5,
      add_ofNat_one]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), m₂.gpr, u₁.other _ (by decide), h.r1,
      ← Nat.add_assoc, add_ofNat_one]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₅.other _ hr.2.2.1, u₄.other _ hr.1, u₃.other _ hr.2.1, m₂.gpr, u₁.other _ hr.2.2.2]
    exact h.keep r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2])
  · rw [u₅.rd, u₄.rd, u₃.rd, m₂.rd, u₁.rd, h.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, m₂.wr, u₁.wr, h.wr]
  · rw [u₅.sp, u₄.sp, u₃.sp, m₂.sp, u₁.sp, h.sp]
  · have hl : (xs.take j).length = j := by rw [List.length_take, Nat.min_eq_left (by omega_using [hj])]
    obtain hv : (s₁.gpr .r12).setWidth 8 = xs[j] := by
      rw [u₁.gpr, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq, hbyte]
      simp [List.getD_eq_getElem?_getD, hj]
    rw [u₅.mem, u₄.mem, u₃.mem, m₂.mem, hv, u₁.mem, h.mem, List.take_add_one,
      List.getElem?_eq_getElem hj, Option.toList_some, writeBytes_snoc _ _ _ _ (by omega_using [hsrc, hj, hl]), hl, off_add]
  · rw [hz, ← u₅.gpr, hr8, ofNat_beq_zero (by omega_using [hj0, hj])]

theorem copy_ok {sI : State} {src : BitVec 32} {j0 : Nat} {xs : List Byte} (hj0 : j0 + xs.length ≤ 16)
    (hsrc : src.toNat + xs.length ≤ 2 ^ 32) (hn : 0 < xs.length) (hw : stR st ∈ sI.wr)
    (hS : SrcOk sI (State.addr st) src xs) (h5 : sI.gpr .r5 = src)
    (h1 : sI.gpr .r1 = st + BitVec.ofNat 32 j0) (h8 : sI.gpr .r8 = BitVec.ofNat 32 xs.length) :
    WP isa copyIn sI (CopyInv sI st src j0 xs xs.length) := by
  obtain h₀ : CopyInv sI st src j0 xs 0 sI :=
    ⟨by omega_using [hn], by rw [h5]; simp, by rw [h1, Nat.add_zero], by rw [h8, Nat.sub_zero], fun _ _ => rfl, rfl, rfl,
      rfl, by rw [List.take_zero, writeBytes_nil]⟩
  refine WP.loop (M := isa) (fun k s => ∃ j, k = xs.length - j ∧ j < xs.length ∧ CopyInv sI st src j0 xs j s)
    ?_ xs.length sI ⟨0, by omega_using [hn], hn, h₀⟩
  rintro k s ⟨j, rfl, hj, hc⟩
  refine WP.mono (copy_step hfit hj0 hsrc hw hS hj hc) fun s' ⟨hc', hz⟩ => ?_
  by_cases hl : xs.length - (j + 1) = 0
  · refine .inl ⟨by rw [eval_ne, hz]; simp [hl], ?_⟩
    rwa [show j + 1 = xs.length by omega_using [hj, hl]] at hc'
  · exact .inr ⟨by rw [eval_ne, hz]; simp [hl], _, by omega_using [hj], j + 1, rfl, by omega_using [hj, hl], hc'⟩

omit hfit in
/-- After copying: the buffer's first `j0` bytes and the bytes copied. -/
theorem CopyInv.buf {sI : State} {src : BitVec 32} {j0 : Nat} {xs : List Byte} (hj0 : j0 + xs.length ≤ 16)
    {s : State} (h : CopyInv sI st src j0 xs xs.length s) :
    bytesAt s.mem (State.addr st + 56) (j0 + xs.length) = bytesAt sI.mem (State.addr st + 56) j0 ++ xs := by
  rw [h.mem, List.take_of_length_le (Nat.le_refl _), ← off_add]
  exact bytesAt_writeBytes sI.mem (State.addr st + 56) j0 xs (by omega_using [hj0])

omit hfit in
theorem CopyInv.frame {sI : State} {src : BitVec 32} {j0 : Nat} {xs : List Byte} (hj0 : j0 + xs.length ≤ 16)
    {s : State} (h : CopyInv sI st src j0 xs xs.length s) : Frame [bufR (State.addr st)] sI.mem s.mem := by
  rw [h.mem, List.take_of_length_le (Nat.le_refl _)]
  exact writeBytes_frame _ _ _ (contains_sub _ (by omega_using []) (by omega_using [hj0]) (by decide))

end

/-! ## `blocks`

After saving the registers, storing the block pointer and count in the state,
computing the multipliers and loading the accumulator (`prologue_ok`), each
block is absorbed (`blocksBody_ok`); then the accumulator is reduced and
stored (`epilogue_ok`). Between blocks (`Common`) it is congruent modulo `p`
to the accumulator of the blocks so far. -/

/-- Between blocks, after `i` of them. -/
structure Common (umaal : Bool) (s₀ : State) (i : Nat) (s : State) : Prop where
  keeps : KeepsF work (offR (stB s₀) wkL) s₀ s
  saved : Saved (stB s₀) s₀.gpr s.mem
  acc : Acc umaal (s₀.gpr .r0) (Rl s₀) (A0 s₀) (blks s₀ i) s

/-- The loop invariant, before block `i`. -/
structure LInv (umaal : Bool) (s₀ : State) (i : Nat) (s : State) : Prop extends Common umaal s₀ i s where
  ptr : s.mem.readW (stB s₀ + BitVec.ofNat 64 124) 32 = s₀.gpr .r1 + BitVec.ofNat 32 (16 * i)
  cnt : s.mem.readW (stB s₀ + BitVec.ofNat 64 20) 32 = BitVec.ofNat 32 (nb s₀ - i)

variable {umaal : Bool}

theorem blocksBody_ok {s₀ : State} (hp : BPre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv umaal s₀ i s) :
    WP isa (body umaal) s fun s' =>
      (isa.eval .ne s' = some false ∧ Common umaal s₀ (nb s₀) s') ∨
      (isa.eval .ne s' = some true ∧ i + 1 < nb s₀ ∧ LInv umaal s₀ (i + 1) s') := by
  have hfit := hp.st_fit
  have hbf := hp.bl_fit
  obtain hn32 : nb s₀ < 2 ^ 32 := (s₀.gpr .r2).isLt
  have hk := hL.keeps
  obtain hpA : State.addr (s₀.gpr .r1 + BitVec.ofNat 32 (16 * i)) =
      State.addr (s₀.gpr .r1) + BitVec.ofNat 64 (16 * i) := addr_add (by omega_using [hi, hbf])
  obtain hsub : Region.Sub ⟨State.addr (s₀.gpr .r1) + BitVec.ofNat 64 (16 * i), 16⟩ (blR s₀) :=
    sub_base _ (by omega_using [hi]) (by omega_using [hn32])
  obtain hfr : Frame [stR (s₀.gpr .r0)] s₀.mem s.mem :=
    hk.frame.sub fun r hr => by
      obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hr
      simp only [wkL, List.mem_cons, List.not_mem_nil, or_false] at hp'
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      rcases hp' with rfl | rfl
      · exact sub_base _ (by decide) (by decide)
      · exact sub_base _ (by decide) (by decide)
  obtain hblk : bytesAt s.mem (State.addr (s₀.gpr .r1 + BitVec.ofNat 32 (16 * i))) 16 =
      bytesAt s₀.mem (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 (16 * i)) 16 := by
    rw [hpA]
    exact Poly1305.bytesAt_frame hfr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.st_bl.sub_right hsub).symm) (by decide)
  refine WP.mono (body_gen hfit (fun i _ => rlimb_lt _ _ i)
      (by simp only [blks, Poly1305.length_bytesAt]; omega_using []) hL.acc hL.ptr hL.cnt
      (by omega_using [hi]) (by omega_using [hi, hn32])
      (by rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * i) (by omega_using [hi, hbf]),
            Nat.mod_eq_of_lt (by omega_using [hi, hbf])]
          omega_using [hi, hbf])
      (fun j hj => by
        rw [hpA, off_add, hk.rd, hp.rd]
        exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _),
          contains_off (off := 16 * i + 4 * j) (n := 4) (len := 16 * nb s₀) (by omega_using [hi, hj])
            (by omega_using [hi, hn32, hj])⟩)
      (by rw [hpA]
          exact ((hp.st_bl.sub_right hsub).sub_left (sub_base _ (a := 124) (len := 4) (len' := 128) (by decide)
            (by decide))).symm))
    fun s' ⟨hA', k', hptr, hcnt, hz⟩ => ?_
  obtain hC : Common umaal s₀ (i + 1) s' := by
    refine ⟨hk.trans (k'.sub (sub_offR _ (by decide) (by decide))), hL.saved.frame k'.frame (by decide) (by decide), ?_⟩
    rw [hblk, ← blks_succ] at hA'
    exact hA'
  by_cases hlast : i + 1 = nb s₀
  · exact .inl ⟨by rw [eval_ne, hz]; simp; omega_using [hlast], hlast ▸ hC⟩
  · refine .inr ⟨by rw [eval_ne, hz]; simp; omega_using [hi, hlast], by omega_using [hi, hlast],
      { hC with ptr := ?_, cnt := ?_ }⟩
    · rw [hptr, BitVec.add_assoc, show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, ← BitVec.ofNat_add]
      rfl
    · rw [hcnt, Nat.sub_sub]

theorem prologue_ok {s₀ : State} (hp : BPre s₀) :
    WP isa (.block (saveRegs ++ ([.str .r1 .r0 ptrOff, .str .r2 .r0 cntOff] : List Instr) ++ setup umaal ++
      ([.ldr .r1 .r0 cntOff, .cmp .r1 (.imm 0)] : List Instr))) s₀ fun s =>
      LInv umaal s₀ 0 s ∧ s.z = (s₀.gpr .r2 == 0) := by
  have hfit := hp.st_fit
  obtain hw : stR (s₀.gpr .r0) ∈ s₀.wr := by rw [hp.wr]; exact List.mem_singleton_self _
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine WP.append (saveRegs_ok hfit rfl hw) fun s₁ ⟨hsv, hf₁, hg₁, hrd₁, hwr₁, hsp₁⟩ => ?_
  obtain hw₁ : stR (s₀.gpr .r0) ∈ s₁.wr := by rw [hwr₁]; exact hw
  refine wp_str (a := stB s₀ + BitVec.ofNat 64 124) (by decide)
    (by rw [hg₁]; exact ea hfit (off := 124) (by decide)) (outSt hw₁ (off := 124) (n := 4) (by decide))
    fun s₂ u₂ => ?_
  refine wp_str (a := stB s₀ + BitVec.ofNat 64 20) (by decide)
    (by rw [u₂.gpr, hg₁]; exact ea hfit (off := 20) (by decide))
    (by rw [u₂.wr]; exact outSt hw₁ (off := 20) (n := 4) (by decide)) fun s₃ u₃ => ?_
  obtain m₃ : s₃.mem = (s₁.mem.writeW (stB s₀ + BitVec.ofNat 64 124) (s₀.gpr .r1)).writeW
      (stB s₀ + BitVec.ofNat 64 20) (s₀.gpr .r2) := by rw [u₃.mem, u₂.mem, u₂.gpr, hg₁]
  obtain f₁₃ : Frame (offR (stB s₀) [(20, 4), (124, 4)]) s₁.mem s₃.mem := by
    rw [m₃]
    exact Frame.writeOff (Frame.writeOff (Frame.refl _ _) (a := 124) (len := 4) (by decide) (Nat.le_refl _) (Nat.le_refl _)
      (by decide) _ rfl) (a := 20) (len := 4) (by decide) (Nat.le_refl _) (Nat.le_refl _) (by decide) _ rfl
  obtain hs₃0 : s₃.gpr .r0 = s₀.gpr .r0 := by rw [u₃.gpr, u₂.gpr, hg₁]
  obtain hw₃ : stR (s₀.gpr .r0) ∈ s₃.wr := by rw [u₃.wr, u₂.wr]; exact hw₁
  refine WP.append (setupAcc_ok hfit hs₃0 hw₃) fun s₄ ⟨ha₄, k₄⟩ => ?_
  obtain hs₄0 : s₄.gpr .r0 = s₀.gpr .r0 := by rw [k₄.gpr _ (by decide), hs₃0]
  obtain hw₄ : stR (s₀.gpr .r0) ∈ s₄.wr := by rw [k₄.wr]; exact hw₃
  refine wp_ldr (a := stB s₀ + BitVec.ofNat 64 20) (by decide)
    (by rw [hs₄0]; exact ea hfit (off := 20) (by decide)) (inSt hw₄ (off := 20) (n := 4) (by decide))
    fun s₅ u₅ => wp_cmp (op2_imm (by decide)) fun s₆ u₆ hz => WP.block_nil ?_
  have f₀₁ : Frame (offR (stB s₀) [(56, 32)]) s₀.mem s₁.mem := hf₁
  obtain f₁₄ : Frame (offR (stB s₀) [(0, 20), (20, 4), (88, 36), (124, 4)]) s₁.mem s₄.mem :=
    (f₁₃.offR_sub (by decide) (by decide)).trans (k₄.frame.offR_sub (by decide) (by decide))
  obtain m₆ : s₆.mem = s₄.mem := by rw [u₆.mem, u₅.mem]
  -- The key and the stored accumulator on entry.
  obtain f₀₃ : Frame (offR (stB s₀) [(20, 4), (56, 32), (124, 4)]) s₀.mem s₃.mem :=
    (f₀₁.offR_sub (by decide) (by decide)).trans (f₁₃.offR_sub (by decide) (by decide))
  obtain hRl : rlimb s₃.mem (stB s₀) = Rl s₀ := rlimb_frame' f₀₃ (by decide) (by decide)
  obtain hA : accD s₃.mem (stB s₀) = accD s₀.mem (stB s₀) := accD_frame f₀₃ (by decide) (by decide)
  rw [hRl, hA] at ha₄
  obtain hptr : s₄.mem.readW (stB s₀ + BitVec.ofNat 64 124) 32 = s₀.gpr .r1 := by
    rw [k₄.frame.word (by decide) (by decide) (by decide), m₃,
      readW_writeW_off _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  obtain hcnt : s₄.mem.readW (stB s₀ + BitVec.ofNat 64 20) 32 = s₀.gpr .r2 := by
    rw [k₄.frame.word (by decide) (by decide) (by decide), m₃, Mem.readW_writeW_self32]
  obtain k₄₆ : KeepsF [.r1] (offR (stB s₀) []) s₄ s₆ :=
    ((u₅.keeps (ws := [.r1]) (by simp)).trans ⟨fun r _ => by rw [u₆.gpr], u₆.mem, u₆.rd, u₆.wr, u₆.sp⟩).keepsF _
  refine ⟨⟨⟨⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · have h1 : r ≠ .r1 := by rintro rfl; exact hr (by decide)
    rw [u₆.gpr, u₅.other _ h1, k₄.gpr _ (by
      simp only [yregs, List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨h1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> exact hr (by decide)),
      u₃.gpr, u₂.gpr, hg₁]
  · rw [m₆]
    exact (f₀₁.offR_sub (by decide) (by decide)).trans (f₁₄.offR_sub (by decide) (by decide))
  · rw [u₆.rd, u₅.rd, k₄.rd, u₃.rd, u₂.rd, hrd₁]
  · rw [u₆.wr, u₅.wr, k₄.wr, u₃.wr, u₂.wr, hwr₁]
  · rw [u₆.sp, u₅.sp, k₄.sp, u₃.sp, u₂.sp, hsp₁]
  · rw [m₆]; exact hsv.frame f₁₄ (by decide) (by decide)
  · exact (Acc.mk hs₄0 hw₄ (by rw [blks_zero, Poly1305.absorbAll_nil]; exact ha₄)).keep k₄₆ (by decide)
      (by decide) (by decide)
  · rw [m₆, hptr]; simp
  · rw [m₆, hcnt]; simp [nb]
  · rw [hz, u₅.gpr, hcnt]; simp

theorem epilogue_ok {s₀ : State} (hp : BPre s₀) {s : State} (hc : Common umaal s₀ (nb s₀) s) :
    WP isa (.block (reduceV umaal ++ storeAcc ++ restoreRegs)) s fun s' =>
      abiPreserved s₀ s' ∧ Proof.Poly1305.blocksArm.post s₀ s' := by
  have hfit := hp.st_fit
  refine WP.append (storeAcc_ok hfit hc.acc) fun s₅ ⟨hv₅, k₅⟩ => ?_
  obtain hs₅0 : s₅.gpr .r0 = s₀.gpr .r0 := by rw [k₅.gpr _ (by decide), hc.acc.r0]
  obtain hw₅ : stR (s₀.gpr .r0) ∈ s₅.wr := by rw [k₅.wr]; exact hc.acc.wr
  refine WP.mono (restoreRegs_ok hfit hs₅0 hw₅ (hc.saved.frame k₅.frame (by decide) (by decide)))
    fun s' ⟨hr', k'⟩ => ?_
  obtain f' : Frame (offR (stB s₀) wkL) s₀.mem s'.mem := by
    rw [k'.mem]; exact hc.keeps.frame.trans (k₅.frame.offR_sub (by decide) (by decide))
  refine ⟨⟨fun r hr => ?_, ?_⟩, fun key msg hrep => ?_⟩
  · rcases preserved_cases r hr with rfl | ⟨i, hi, rfl⟩
    · rw [k'.gpr _ (by decide), k₅.gpr _ (by decide), hc.keeps.gpr _ (by decide)]
    · exact hr' i hi
  · rw [k'.sp, k₅.sp, hc.keeps.sp]
  · obtain ⟨hlen, hkey, hacc⟩ := hrep
    have hkey' := hkey
    rw [← key_frame f' (by decide) (by decide)] at hkey'
    refine ⟨?_, hkey', ?_⟩
    · rw [List.length_append, Poly1305.length_bytesAt]; omega_using [hlen]
    · rw [← hkey, take_bytesAt _ _ (by decide), ← val_rlimb, Poly1305.accumulate_append hlen]
      rw [← hkey, take_bytesAt _ _ (by decide), ← val_rlimb] at hacc
      obtain hlt : leNum (bytesAt s₀.mem (stB s₀) 24) < P := by
        rw [hacc]; exact Poly1305.accumulate_lt _ _
      obtain hA : accumulate (Rn s₀) msg = A0 s₀ := by
        rw [A0, val_accD_eq hlt]; exact hacc.symm
      obtain hlt' := Poly1305.absorbAll_lt (r := Rn s₀) (a := A0 s₀) (by rw [← hA]; exact Poly1305.accumulate_lt _ _)
        (blks s₀ (nb s₀))
      rw [hA, k'.mem, hv₅, Nat.mod_eq_of_lt hlt']

theorem blocks_correct {s₀ : State} (hp : BPre s₀) :
    WP isa (blocks umaal) s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Poly1305.blocksArm.post s₀ s' := by
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨hL, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := Common umaal s₀ (nb s₀)) ?_ fun s₂ hc => epilogue_ok hp hc)
  refine WP.ite s₁.z (eval_eq _) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by rw [h] at hz; simp only [nb]; rw [eq_of_beq hz.symm]; rfl
    exact WP.block_nil (M := isa) (h0 ▸ hL.toCommon)
  · have hpos : 0 < nb s₀ := by
      rw [h] at hz
      refine Nat.pos_of_ne_zero fun h' => ?_
      have : s₀.gpr .r2 = 0 := BitVec.eq_of_toNat_eq (by simpa [nb] using h')
      simp [this] at hz
    refine WP.loop (M := isa) (fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv umaal s₀ i s) ?_ (nb s₀) s₁
      ⟨0, rfl, hpos, hL⟩
    rintro m s ⟨i, rfl, hi, hLi⟩
    refine WP.mono (blocksBody_ok hp hi hLi) fun s' h' => ?_
    rcases h' with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
    · exact .inl ⟨he, hc⟩
    · exact .inr ⟨he, nb s₀ - (i + 1), by omega_using [hi'], i + 1, rfl, hi', hL'⟩

theorem blocks_ok (s : State) (hs : Proof.Poly1305.blocksArm.pre s) :
    ∃ t s', Exec isa (Impl.Poly1305.Arm.blocks umaal) s t s' ∧ abiPreserved s s' ∧
      Proof.Poly1305.blocksArm.post s s' :=
  blocks_correct (BPre.of s hs)

end VG.Proof.Poly1305.Arm
