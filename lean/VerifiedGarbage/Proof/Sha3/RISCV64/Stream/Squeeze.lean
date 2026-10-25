module

public import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Common
public import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.Sha3.Lanes
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Wp
import VerifiedGarbage.Proof.Sha3.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public import VerifiedGarbage.Proof.Sha3.RISCV64.Contract
public import VerifiedGarbage.Spec.Sha3.Contract

/-!
# The SHA-3 sponge on RISC-V: `squeeze`

The structure of the PPC64LE proof (`Proof/Sha3/PPC64LE/Stream/Squeeze.lean`),
a byte at a time, in the frame of `Stream/Common.lean`.
-/

@[expose] public section

namespace VG.Proof.Sha3.RISCV64.Stream.Squeeze

open VG VG.RISCV64 VG.RISCV64.Wp VG.Impl.Sha3.RISCV64.Stream
open VG.Proof.Sha3.RISCV64 VG.Proof.Sha3.RISCV64.Stream
open VG.Spec.Sha3 (stateAt keccakF bytesAt rates)
open VG.Proof.Sha3 (byteOf byteOf_stateAt iterF iterF_succ length_squeezeFrom squeezeFrom_getElem
  squeezeFrom_iterF ofNat_beq_zero sub_beq_zero sub_ofNat writeW8_self writeW8_other div_mod_eq
  toNat_ofNat_lt)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev stp : Addr := s₀.gpr .a0
abbrev rate : Nat := (s₀.gpr .a1).toNat
abbrev pos₀ : Nat := (s₀.gpr .a2).toNat
abbrev outp : Addr := s₀.gpr .a3
abbrev outn : Nat := (s₀.gpr .a4).toNat
abbrev SR : Region := ⟨stp s₀, 200⟩
abbrev OR : Region := ⟨outp s₀, outn s₀⟩
/-- The initial state. -/
abbrev S₀ : Spec.Sha3.State := stateAt s₀.mem (stp s₀)

end

structure SPre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [SR s₀, OR s₀]
  st_o : (SR s₀).Disjoint (OR s₀)
  stk : Stk s₀
  k_st : (KR s₀).Disjoint (SR s₀)
  k_o : (KR s₀).Disjoint (OR s₀)
  rate_mem : rate s₀ ∈ rates
  pos_le : pos₀ s₀ ≤ rate s₀

theorem pre_of {s₀ : State} (h : Proof.Sha3.squeezeRISCV64.pre s₀) : SPre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, ⟨h4, h5⟩, h6, h7, h8, h9⟩

theorem SPre.rate_pos {s₀ : State} (hp : SPre s₀) : 0 < rate s₀ ∧ rate s₀ ≤ 200 := by
  have := Proof.Sha3.rate_bounds hp.rate_mem
  omega

theorem outn_lt (s₀ : State) : outn s₀ < 2 ^ 64 := (s₀.gpr .a4).isLt

/-- The callee-saved registers our code never writes. -/
abbrev untouched : List Reg := [.s0, .s1, .s7, .s8, .s9, .s10, .s11]

/-! ## The loop invariant -/

/-- After `i` bytes of output, `k` permutations and `pos` bytes of the
current block: `pos₀ + i = rate * k + pos`. -/
structure Inv (s₀ : State) (i k pos : Nat) (s : State) : Prop where
  i_le : i ≤ outn s₀
  hi : pos₀ s₀ + i = rate s₀ * k + pos
  pos_le : pos ≤ rate s₀
  rd : s.rd = []
  wr : s.wr = [BR s₀, SR s₀, OR s₀]
  s2 : s.gpr .s2 = stp s₀
  s3 : s.gpr .s3 = s₀.gpr .a1
  s4 : s.gpr .s4 = BitVec.ofNat 64 pos
  s5 : s.gpr .s5 = outp s₀ + BitVec.ofNat 64 i
  s6 : s.gpr .s6 = BitVec.ofNat 64 (outn s₀ - i)
  sp : s.sp = B s₀
  frame : Frame [SR s₀, OR s₀, KR s₀] s₀.mem s.mem
  saved : Saved (B s₀) s₀.gpr s.mem
  untouched : ∀ r ∈ untouched, s.gpr r = s₀.gpr r
  state : stateAt s.mem (stp s₀) = iterF k (S₀ s₀)
  out : ∀ j < i, s.mem (outp s₀ + BitVec.ofNat 64 j) =
    byteOf (iterF ((pos₀ s₀ + j) / rate s₀) (S₀ s₀)) ((pos₀ s₀ + j) % rate s₀)

/-- The registers of the invariant, besides `untouched`. -/
abbrev keep : List Reg := [.s2, .s3, .s4, .s5, .s6] ++ untouched

theorem Inv.congr {s₀ : State} {i k pos : Nat} {s s' : State} (h : Inv s₀ i k pos s)
    (hg : ∀ r ∈ keep, s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    Inv s₀ i k pos s' where
  i_le := h.i_le
  hi := h.hi
  pos_le := h.pos_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  s2 := by rw [hg _ (by decide)]; exact h.s2
  s3 := by rw [hg _ (by decide)]; exact h.s3
  s4 := by rw [hg _ (by decide)]; exact h.s4
  s5 := by rw [hg _ (by decide)]; exact h.s5
  s6 := by rw [hg _ (by decide)]; exact h.s6
  sp := hsp.trans h.sp
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved
  untouched := fun r hr => (hg r (List.mem_append_right _ hr)).trans (h.untouched r hr)
  state := by rw [hm]; exact h.state
  out := by rw [hm]; exact h.out

theorem prologue_ok {s₀ : State} (hp : SPre s₀) :
    WP isa (.block setup) (allocd 560 s₀) (Inv s₀ 0 0 (pos₀ s₀)) := by
  have hk := hp.stk
  unfold setup
  refine save_ok (s := allocd 560 s₀) hk.B_al (fun d hd₁ hd₂ => ⟨BR s₀, List.mem_cons_self ..,
      Offset.contains_base _ (by omega) (by omega)⟩)
    fun s₁ g₁ rd₁ wr₁ sp₁ sv₁ f₁ => ?_
  refine wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ =>
    wp_mv fun s₆ u₆ => WP.block_nil ?_
  have hm : s₆.mem = s₁.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  have hsub : Region.Sub ⟨(allocd 560 s₀).sp + BitVec.ofNat 64 512, 48⟩ (KR s₀) := by
    rw [show (allocd 560 s₀).sp = B s₀ from rfl, hk.B_off]; exact sub_K s₀ (by omega)
  have g : ∀ r, r ≠ .t0 → s₁.gpr r = s₀.gpr r := fun r h => g₁ r h
  have hf : Frame [SR s₀, OR s₀, KR s₀] s₀.mem s₁.mem := f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨KR s₀, by simp, hsub⟩
  refine ⟨Nat.zero_le _, by simp, hp.pos_le, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by rw [hm]; exact hf, by rw [hm]; exact sv₁, fun r hr => ?_, ?_, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]; exact hp.rd
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]; simp only [allocd, hp.wr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, g _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), g _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), g _ (by decide)]; simp
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g _ (by decide)]; simp
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g _ (by decide)]; simp
  · rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]; rfl
  · have : r ≠ .s2 ∧ r ≠ .s3 ∧ r ≠ .s4 ∧ r ≠ .s5 ∧ r ≠ .s6 ∧ r ≠ .t0 := by revert r; decide
    rw [u₆.other _ this.2.2.2.2.1, u₅.other _ this.2.2.2.1, u₄.other _ this.2.2.1,
      u₃.other _ this.2.1, u₂.other _ this.1, g _ this.2.2.2.2.2]
  · rw [hm]
    exact Proof.Sha3.stateAt_congr fun j hj => f₁.bytes (R := SR s₀)
      (by simpa using (hp.k_st.sub_left hsub).symm) (by show 200 ≤ 2 ^ 64; decide) hj

/-! ## One iteration -/

theorem keep_preserved : ∀ r ∈ untouched, r ∈ preserved := by decide

theorem permute_ok {s₀ : State} (hp : SPre s₀) {i k : Nat} {s : State} (hI : Inv s₀ i k (rate s₀) s) :
    WP isa (.seq (.block [.li .s4 0]) permuteAt) s (Inv s₀ i (k + 1) 0) := by
  have hk := hp.stk
  refine WP.seq (wp_li (by decide) fun s₁ u₁ => WP.block_nil ?_)
  have sp₁ : s₁.sp = B s₀ := by rw [u₁.sp, hI.sp]
  refine permuteAt_ok (st := stp s₀) (by rw [u₁.other _ (by decide), hI.s2])
    (by rw [sp₁]; exact hk.B_al) (by rw [sp₁]; exact hk.B_608)
    (by rw [sp₁]; exact (hp.k_st.sub_left hk.scr_sub).symm)
    (by rw [sp₁]; exact hp.k_st.sub_left hk.below_sub) ?_
    fun s' rd' wr' sp' cs' hf hst => ?_
  · rw [u₁.wr, hI.wr, sp₁]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨SR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨BR s₀, by simp, 0, by simp, by simp⟩
  rw [sp₁, u₁.mem] at hf
  have hd : ∀ r ∈ [(⟨stp s₀, 200⟩ : Region), ⟨B s₀, 512⟩, ⟨B s₀ - 608, 608⟩], (OR s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.st_o.symm
    · exact (hp.k_o.sub_left hk.scr_sub).symm
    · exact (hp.k_o.sub_left hk.below_sub).symm
  refine ⟨hI.i_le, by rw [hI.hi, Nat.mul_succ]; rfl, Nat.zero_le _, rd'.trans (u₁.rd.trans hI.rd),
    wr'.trans (u₁.wr.trans hI.wr), ?_, ?_, ?_, ?_, ?_, by rw [sp', sp₁], ?_, ?_, (fun r hr => by
      rw [cs' r (keep_preserved r hr), u₁.other r (by revert r; decide)]
      exact hI.untouched r hr), ?_, fun j hj => ?_⟩
  · rw [cs' _ (by decide), u₁.other _ (by decide), hI.s2]
  · rw [cs' _ (by decide), u₁.other _ (by decide), hI.s3]
  · rw [cs' _ (by decide), u₁.gpr]
  · rw [cs' _ (by decide), u₁.other _ (by decide), hI.s5]
  · rw [cs' _ (by decide), u₁.other _ (by decide), hI.s6]
  · exact hI.frame.trans (hf.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨SR s₀, by simp, fun _ h => h⟩
      · exact ⟨KR s₀, by simp, hk.scr_sub⟩
      · exact ⟨KR s₀, by simp, hk.below_sub⟩)
  · refine hI.saved.frame (fun d h₁ h₂ r hr => ?_) hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.k_st.sub_left (hk.slot_sub h₁ h₂)
    · exact slot_scr s₀ h₁ h₂
    · exact hk.slot_below h₁ h₂
  · rw [hst, u₁.mem, hI.state, iterF_succ]
  · refine Eq.trans (hf.bytes (R := OR s₀) hd (Nat.le_of_lt (outn_lt s₀))
      (by have := hI.i_le; omega : j < outn s₀)) ?_
    exact hI.out j hj

theorem store_ok {s₀ : State} (hp : SPre s₀) {i k pos : Nat} {s : State} (hI : Inv s₀ i k pos s)
    (hlt : pos < rate s₀) (hi : i < outn s₀) :
    WP isa (.block squeezeByte) s (Inv s₀ (i + 1) k (pos + 1)) := by
  have ⟨hr0, hr200⟩ := hp.rate_pos
  have hn := outn_lt s₀
  refine wp_add fun s₁ u₁ => ?_
  refine wp_lbu (a := stp s₀ + BitVec.ofNat 64 pos) (by decide) (by rw [u₁.gpr, hI.s2, hI.s4]; simp)
    ⟨SR s₀, by simp [u₁.rd, u₁.wr, hI.rd, hI.wr], Offset.contains_base _ (by omega) (by omega)⟩
    fun s₂ u₂ => ?_
  refine wp_sb (a := outp s₀ + BitVec.ofNat 64 i) (by decide)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hI.s5]; simp)
    (by rw [u₂.wr, u₁.wr, hI.wr]; exact ⟨OR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩)
    fun s₃ g₃ => ?_
  refine wp_addi (by decide) fun s₄ u₄ => wp_addi (by decide) fun s₅ u₅ =>
    wp_subi (imm := 1) (by decide) fun s₆ u₆ => WP.block_nil ?_
  have g : ∀ r, r ≠ .t2 → r ≠ .t1 → r ≠ .s5 → r ≠ .s4 → r ≠ .s6 → s₆.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by
      rw [u₆.other r h5, u₅.other r h4, u₄.other r h3, g₃.gpr, u₂.other r h2, u₁.other r h1]
  have hb : s.mem (stp s₀ + BitVec.ofNat 64 pos) = byteOf (iterF k (S₀ s₀)) pos := by
    rw [← hI.state, byteOf_stateAt _ _ (by omega)]
  have hm : s₆.mem = s.mem.writeW (outp s₀ + BitVec.ofNat 64 i) (byteOf (iterF k (S₀ s₀)) pos) := by
    rw [u₆.mem, u₅.mem, u₄.mem, g₃.mem, u₂.gpr, u₂.mem, u₁.mem,
      BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq, hb]
  have hfw : Frame [OR s₀] s.mem s₆.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega) (by omega))
  refine ⟨by omega, by have := hI.hi; omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hI.frame.trans (hfw.mono (by simp)), ?_, (fun r hr => by
      have : r ≠ .t2 ∧ r ≠ .t1 ∧ r ≠ .s5 ∧ r ≠ .s4 ∧ r ≠ .s6 := by revert r; decide
      rw [g r this.1 this.2.1 this.2.2.1 this.2.2.2.1 this.2.2.2.2]
      exact hI.untouched r hr), ?_, fun j hj => ?_⟩
  · rw [u₆.rd, u₅.rd, u₄.rd, g₃.rd, u₂.rd, u₁.rd, hI.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, g₃.wr, u₂.wr, u₁.wr, hI.wr]
  · rw [g .s2 (by decide) (by decide) (by decide) (by decide) (by decide), hI.s2]
  · rw [g .s3 (by decide) (by decide) (by decide) (by decide) (by decide), hI.s3]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), hI.s4, ← BitVec.ofNat_add]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), hI.s5, BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), hI.s6, sub_ofNat (by omega), Nat.sub_sub]
  · rw [u₆.sp, u₅.sp, u₄.sp, g₃.sp, u₂.sp, u₁.sp, hI.sp]
  · exact hI.saved.frame (fun d h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.k_o.sub_left (hp.stk.slot_sub h₁ h₂)) hfw
  · rw [Proof.Sha3.stateAt_congr fun j hj => hfw.bytes (R := SR s₀) (by simpa using hp.st_o)
      (by show 200 ≤ 2 ^ 64; decide) hj]
    exact hI.state
  · rw [hm]
    by_cases e : j = i
    · subst e
      obtain ⟨d, m⟩ := div_mod_eq (k := k) hr0 hlt
      rw [writeW8_self, hI.hi, d, m]
    · rw [writeW8_other _ _ (Offset.add_ofNat_ne _ (by omega) (by omega) e)]
      exact hI.out j (by omega)

theorem body_ok {s₀ : State} (hp : SPre s₀) {i k pos : Nat} {s : State} (hI : Inv s₀ i k pos s)
    (hi : i < outn s₀) :
    WP isa squeezeBody s fun s' => ∃ k' pos', Inv s₀ (i + 1) k' pos' s' := by
  have ⟨hr0, _⟩ := hp.rate_pos
  unfold squeezeBody permuteIfFull
  refine WP.seq (WP.seq (wp_sub fun s₁ u₁ => WP.block_nil ?_))
  have hI₁ := hI.congr (fun r hr => u₁.other r (by revert r; decide)) u₁.mem u₁.rd u₁.wr u₁.sp
  have hz : isa.eval (.zero .t1) s₁ = some (decide (pos = rate s₀)) := by
    show eval (.zero .t1) s₁ = _
    rw [eval_zero, u₁.gpr, hI.s4, hI.s3,
      sub_beq_zero (by have := hI.pos_le; have := (s₀.gpr .a1).isLt; omega)]
  refine WP.mono (Q := fun s => ∃ k' pos', Inv s₀ i k' pos' s ∧ pos' < rate s₀) ?_
    fun s₂ ⟨k', pos', hI₂, hlt⟩ => WP.mono (store_ok hp hI₂ hlt hi) fun s' h => ⟨k', pos' + 1, h⟩
  refine WP.ite (decide (pos = rate s₀)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    subst hb
    exact WP.mono (permute_ok hp hI₁) fun s' h => ⟨k + 1, 0, h, hr0⟩
  · simp only [decide_eq_false_iff_not] at hb
    exact WP.block_nil ⟨k, pos, hI₁, by have := hI.pos_le; omega⟩

/-! ## The whole function -/

theorem preserved_split : ∀ r ∈ preserved, r ∈ saved.map Prod.fst ∨ r ∈ untouched := by decide

theorem correct {s₀ : State} (hp : SPre s₀) :
    WP isa squeeze s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Sha3.squeezeRISCV64.post s₀ s' := by
  have hk := hp.stk
  have hn := outn_lt s₀
  have ⟨hr0, hr200⟩ := hp.rate_pos
  unfold squeeze withLoop frameBytes
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by have := hk.sp; omega) ?_
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ hI => ?_)
  refine WP.seq (WP.mono (Q := fun s => ∃ k pos, Inv s₀ (outn s₀) k pos s) ?_
    fun s₂ ⟨k, pos, hI₂⟩ => ?_)
  · refine WP.ite (decide (outn s₀ = 0))
      (by show eval (.zero .s6) s₁ = _
          rw [eval_zero, hI.s6, Nat.sub_zero, ofNat_beq_zero (by omega)])
      (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      exact WP.block_nil ⟨0, pos₀ s₀, by rw [hb]; exact hI⟩
    · simp only [decide_eq_false_iff_not] at hb
      refine WP.loop (M := isa) (fun n s => ∃ i k pos, n = outn s₀ - i ∧ i < outn s₀ ∧ Inv s₀ i k pos s)
        ?_ (outn s₀) s₁ ⟨0, 0, pos₀ s₀, by omega, by omega, hI⟩
      rintro n s ⟨i, k, pos, rfl, hi, hI⟩
      refine WP.mono (body_ok hp hI hi) fun s' ⟨k', pos', hI'⟩ => ?_
      have hz : isa.eval (.nonzero .s6) s' = some (decide (outn s₀ - (i + 1) ≠ 0)) := by
        show eval (.nonzero .s6) s' = _
        rw [eval_nonzero, hI'.s6, bne, ofNat_beq_zero (by omega)]
        simp
      by_cases hl : outn s₀ - (i + 1) = 0
      · exact .inl ⟨by rw [hz]; simp [hl], k', pos', by rwa [show i + 1 = outn s₀ by omega] at hI'⟩
      · exact .inr ⟨by rw [hz]; simp [hl], _, by omega, i + 1, k', pos', rfl, by omega, hI'⟩
  · have hpl := hI₂.pos_le
    refine epilogue_ok (g := s₀.gpr) (by rw [hI₂.sp]; exact hk.B_al)
      (fun d hd₁ hd₂ => by
        rw [hI₂.rd, hI₂.wr, hI₂.sp]
        exact ⟨BR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩)
      (by rw [hI₂.sp]; exact hI₂.saved) fun s' h0 hsv hother hm hrd hwr hsp => ?_
    have hx0 : s'.gpr .a0 = BitVec.ofNat 64 pos := by rw [h0, hI₂.s4]
    refine ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_, fun d => ?_⟩
    · show s'.gpr r = _
      rcases preserved_split r hr with h | h
      · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp h
        exact hsv p hp'
      · rw [hother r (by revert r; decide) (by revert r; decide) (by revert r; decide)]
        exact hI₂.untouched r h
    · show s'.sp + BitVec.ofNat 64 560 = s₀.sp
      rw [hsp, hI₂.sp, BitVec.sub_add_cancel]
    · exact hsv (.ra, 512) (by decide)
    · simp only [freed]
      show bytesAt s'.mem (outp s₀) (outn s₀) = Spec.Sha3.squeezeFrom (rate s₀) (S₀ s₀) (pos₀ s₀) (outn s₀)
      rw [hm]
      refine List.ext_getElem (by rw [length_squeezeFrom hr0 hr200]; simp [bytesAt]) fun j h₁ _ => ?_
      have hj : j < outn s₀ := by simpa [bytesAt] using h₁
      rw [squeezeFrom_getElem hr0 hr200 _ hj]
      simp only [bytesAt, List.getElem_map, List.getElem_range]
      exact hI₂.out j hj
    · simp only [freed]
      rw [hx0, toNat_ofNat_lt (by omega)]; exact hpl
    · simp only [freed]
      show Spec.Sha3.squeezeFrom (rate s₀) (stateAt s'.mem (stp s₀)) (s'.gpr .a0).toNat d =
        Spec.Sha3.squeezeFrom (rate s₀) (S₀ s₀) (pos₀ s₀ + outn s₀) d
      rw [hm, hI₂.state, hx0, toNat_ofNat_lt (by omega), squeezeFrom_iterF hr0 hr200, ← hI₂.hi]

end VG.Proof.Sha3.RISCV64.Stream.Squeeze
