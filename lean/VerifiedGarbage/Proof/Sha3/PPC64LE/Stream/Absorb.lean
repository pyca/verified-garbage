module

public import VerifiedGarbage.Proof.Sha3.PPC64LE.Call
public import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.Wp
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The SHA-3 sponge on PPC64LE: `absorb`

The same structure as the AArch64 proof (`VG.Proof.Sha3.AArch64.Stream.Absorb`):
`absorbMain`, whose frame saving the link register `correct` adds
(`WP.frameReg`).
-/

@[expose] public section

namespace VG.Proof.Sha3.PPC64LE.Stream.Absorb

open VG VG.PPC64LE VG.Impl.Sha3.PPC64LE.Stream
open VG.Proof.Sha3.PPC64LE VG.Proof.Sha3.PPC64LE.Stream
open VG.Proof.MdStream.PPC64LE (Upd Mupd wp_addi wp_mov wp_subi wp_li wp_add wp_sub wp_and wp_lsr
  wp_lbz wp_stb wp_std wp_ld eval_zero eval_nonzero contains_offset toNat_ofNat_lt)
open VG.Proof.Sha3 (Rep rep_snoc xorByte stateAt_xorByte ofNat_beq_zero sub_beq_zero sub_ofNat
  xor_setWidth writeW8_apply bytesAt_succ bytesAt_length xorAt xorAt_single byteOf_xorAt rep_append
  byteOf_stateAt writeW64_byte)
open VG.Spec.Sha3 (stateAt keccakF bytesAt rates)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .r3
abbrev rt : Nat := (s₀.gpr .r4).toNat
abbrev pos : Nat := (s₀.gpr .r5).toNat
abbrev dp : Addr := s₀.gpr .r6
abbrev len : Nat := (s₀.gpr .r7).toNat
abbrev scr : Addr := s₀.gpr .r8
abbrev stR : Region := ⟨st s₀, 200⟩
abbrev dR : Region := ⟨dp s₀, len s₀⟩
abbrev scR : Region := ⟨scr s₀, 640⟩
/-- The frame saving the link register, below the stack pointer. -/
abbrev stkR : Region := ⟨s₀.sp - 48, 48⟩
/-- The first `c` bytes of data. -/
abbrev D (c : Nat) : List Byte := bytesAt s₀.mem (dp s₀) c

/-- The messages the initial state and position represent. -/
def Msg (msg : List Byte) : Prop :=
  stateAt s₀.mem (st s₀) = Rep (rt s₀) msg ∧ pos s₀ = msg.length % rt s₀

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [dR s₀]
  wr : s₀.wr = [stR s₀, scR s₀]
  st_scr : (stR s₀).Disjoint (scR s₀)
  d_st : (dR s₀).Disjoint (stR s₀)
  d_scr : (dR s₀).Disjoint (scR s₀)
  rate : rt s₀ ∈ rates
  pos_lt : pos s₀ < rt s₀

/-- The frame is below the stack pointer, and disjoint from the buffers. -/
structure Stack (s₀ : State) : Prop where
  sp48 : 48 ≤ s₀.sp.toNat
  st : (stkR s₀).Disjoint (stR s₀)
  d : (stkR s₀).Disjoint (dR s₀)
  scr : (stkR s₀).Disjoint (scR s₀)

theorem pre_of {s₀ : State} (h : Proof.Sha3.absorbPPC64LE.pre s₀) : Pre s₀ ∧ Stack s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5, h10, h11⟩, ⟨h6, h7, h8, h9⟩⟩

theorem Pre.rt_pos {s₀ : State} (hp : Pre s₀) : 0 < rt s₀ ∧ rt s₀ ≤ 168 := by
  have h := Proof.Sha3.rate_bounds hp.rate
  omega_arith

theorem len_lt (s₀ : State) : len s₀ < 2 ^ 64 := (s₀.gpr .r7).isLt

/-! ## Invariants -/

/-- The registers the body never writes. -/
abbrev keep : List Reg := [.r26, .r27, .r28, .r30, .r31] ++ untouched

theorem keepNe {r : Reg} (hr : r ∈ keep) (x : Reg) (hx : x ∉ keep := by decide) : r ≠ x :=
  fun h => hx (h ▸ hr)

theorem keep_preserved : ∀ r ∈ keep, r ∈ preserved := by decide

/-- What holds throughout, after consuming `c` bytes of data. -/
structure Common (s₀ : State) (c : Nat) (s : State) : Prop where
  c_le : c ≤ len s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  r26 : s.gpr .r26 = st s₀
  r27 : s.gpr .r27 = scr s₀
  sp : s.sp = s₀.sp
  r28 : s.gpr .r28 = s₀.gpr .r4
  r30 : s.gpr .r30 = dp s₀ + BitVec.ofNat 64 c
  r31 : s.gpr .r31 = BitVec.ofNat 64 (len s₀ - c)
  frame : Frame [stR s₀, scR s₀] s₀.mem s.mem
  saved : Saved (scr s₀) s₀.gpr s.mem
  untouched : ∀ r ∈ untouched, s.gpr r = s₀.gpr r

/-- The loop invariant: the state represents the message followed by the
first `c` bytes of data. -/
structure Inv (s₀ : State) (c : Nat) (s : State) : Prop extends Common s₀ c s where
  r29 : s.gpr .r29 = BitVec.ofNat 64 ((pos s₀ + c) % rt s₀)
  repr : ∀ msg, Msg s₀ msg → stateAt s.mem (st s₀) = Rep (rt s₀) (msg ++ D s₀ c)

theorem Common.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : Common s₀ c s)
    (hg : ∀ r ∈ keep, s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    Common s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  r26 := by rw [hg _ (by decide)]; exact h.r26
  r27 := by rw [hg _ (by decide)]; exact h.r27
  sp := hsp.trans h.sp
  r28 := by rw [hg _ (by decide)]; exact h.r28
  r30 := by rw [hg _ (by decide)]; exact h.r30
  r31 := by rw [hg _ (by decide)]; exact h.r31
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved
  untouched := fun r hr => (hg r (List.mem_append_right _ hr)).trans (h.untouched r hr)

/-- A call of the permutation keeps what holds throughout. -/
theorem Common.after_call {s₀ : State} (hp : Pre s₀) {c : Nat} {s s' : State} (h : Common s₀ c s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp)
    (hcs : ∀ r ∈ preserved, s'.gpr r = s.gpr r)
    (hf : Frame [stR s₀, ⟨scr s₀, 512⟩] s.mem s'.mem) : Common s₀ c s' :=
  have hg : ∀ r ∈ keep, s'.gpr r = s.gpr r := fun r hr => hcs r (keep_preserved r hr)
  { c_le := h.c_le
    rd := hrd.trans h.rd
    wr := hwr.trans h.wr
    r26 := by rw [hg _ (by decide)]; exact h.r26
    r27 := by rw [hg _ (by decide)]; exact h.r27
    sp := hsp.trans h.sp
    r28 := by rw [hg _ (by decide)]; exact h.r28
    r30 := by rw [hg _ (by decide)]; exact h.r30
    r31 := by rw [hg _ (by decide)]; exact h.r31
    untouched := fun r hr => (hg r (List.mem_append_right _ hr)).trans (h.untouched r hr)
    frame := h.frame.trans (hf.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨stR s₀, by simp, fun _ h => h⟩
      · exact ⟨scR s₀, by simp, Region.sub_prefix (by omega_arith)⟩)
    saved := h.saved.permute hp.st_scr hf }

/-- The data is unchanged. -/
theorem Common.data {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (h : Common s₀ c s) {i : Nat}
    (hi : i < len s₀) : s.mem (dp s₀ + BitVec.ofNat 64 i) = s₀.mem (dp s₀ + BitVec.ofNat 64 i) :=
  h.frame.bytes (R := dR s₀) (by simpa using ⟨hp.d_st, hp.d_scr⟩) (Nat.le_of_lt (len_lt s₀)) hi

/-! ## The prologue -/

theorem prologue_ok {s₀ : State} (hp : Pre s₀) : WP isa (.block setup) s₀ (Inv s₀ 0) := by
  unfold setup
  refine save_ok (by decide) (fun d hd₁ hd₂ => ⟨scR s₀, by simp [hp.wr], Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  refine wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ =>
    wp_mov fun s₆ u₆ => wp_mov fun s₇ u₇ => WP.block_nil ?_
  have hm : s₇.mem = s₁.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  have f₁ : Frame [scR s₀] s₀.mem s₁.mem := by
    rw [m₁]
    exact (saveMem_frame _ _ _).sub fun r hr => ⟨scR s₀, by simp,
      by simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by omega_arith)⟩
  have hf : Frame [stR s₀, scR s₀] s₀.mem s₁.mem := f₁.mono (by simp)
  have oth : ∀ r, r ∉ [Reg.r26, .r27, .r28, .r29, .r30, .r31] → s₇.gpr r = s₀.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₇.other _ hr.2.2.2.2.2, u₆.other _ hr.2.2.2.2.1, u₅.other _ hr.2.2.2.1, u₄.other _ hr.2.2.1,
      u₃.other _ hr.2.1, u₂.other _ hr.1, g₁]
  refine ⟨⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [hm]; exact hf,
      by rw [hm, m₁]; exact saveMem_saved _ _ _, fun r hr => oth r (by revert r; decide)⟩,
    ?_, fun msg ⟨hs, _⟩ => ?_⟩
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, g₁]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), g₁]
  · rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), g₁]
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g₁]
    simp
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g₁, Nat.sub_zero]
    simp [len]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g₁, Nat.add_zero,
      Nat.mod_eq_of_lt hp.pos_lt]
    simp [pos]
  · rw [hm, show D s₀ 0 = [] by simp [bytesAt], List.append_nil, ← hs]
    exact Proof.Sha3.stateAt_congr fun i hi =>
      f₁.bytes (R := stR s₀) (by simpa using hp.st_scr) (by simp) hi

/-! ## One iteration -/

/-- The block of the body: the byte at position `j` XORed in. -/
theorem body_byte {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c < len s₀) {s : State}
    (hI : Inv s₀ c s) :
    WP isa (.block absorbByte) s fun s' =>
      Common s₀ (c + 1) s' ∧ s'.gpr .r29 = BitVec.ofNat 64 ((pos s₀ + c) % rt s₀ + 1) ∧
      eval (.zero .d .r9) s' = some (decide ((pos s₀ + c) % rt s₀ + 1 = rt s₀)) ∧
      stateAt s'.mem (st s₀) = xorByte (stateAt s.mem (st s₀)) ((pos s₀ + c) % rt s₀)
        (s₀.mem (dp s₀ + BitVec.ofNat 64 c)) := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  have hl := len_lt s₀
  have hj : (pos s₀ + c) % rt s₀ < rt s₀ := Nat.mod_lt _ hr₀
  generalize hjd : (pos s₀ + c) % rt s₀ = j at hj ⊢
  have hr22 : s.gpr .r29 = BitVec.ofNat 64 j := by rw [hI.r29, hjd]
  have hsin : ∀ rs : List Region, stR s₀ ∈ rs → InRegions rs (st s₀ + BitVec.ofNat 64 j) 1 :=
    fun rs h => ⟨stR s₀, h, contains_offset (by omega_arith) (by omega_arith)⟩
  refine wp_lbz (t := .r9) (a := dp s₀ + BitVec.ofNat 64 c) (by decide) (by rw [hI.r30]; simp)
    ⟨dR s₀, by simp [hI.rd, hp.rd], contains_offset (by omega_arith) (by omega_arith)⟩ fun s₁ u₁ => ?_
  refine wp_add fun s₂ u₂ => ?_
  have ea : s₂.gpr .r10 + BitVec.ofNat 64 0 = st s₀ + BitVec.ofNat 64 j := by
    rw [u₂.gpr, u₁.other _ (by decide), u₁.other _ (by decide), hI.r26, hr22]; simp
  refine wp_lbz (t := .r11) (a := st s₀ + BitVec.ofNat 64 j) (by decide) ea
    (hsin _ (by simp [u₂.rd, u₂.wr, u₁.rd, u₁.wr, hI.rd, hI.wr, hp.wr])) fun s₃ u₃ => ?_
  refine wp_xor fun s₄ u₄ => ?_
  refine wp_stb (a := st s₀ + BitVec.ofNat 64 j) (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide)]; exact ea)
    (hsin _ (by simp [u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr, hp.wr])) fun s₅ g₅ => ?_
  refine wp_addi (by decide) fun s₆ u₆ => wp_addi (by decide) fun s₇ u₇ =>
    wp_subi (by decide) fun s₈ u₈ => wp_sub fun s₉ u₉ => WP.block_nil ?_
  -- The byte stored.
  have hv : (s₄.gpr .r9).setWidth 8 =
      s₀.mem (dp s₀ + BitVec.ofNat 64 c) ^^^ s.mem (st s₀ + BitVec.ofNat 64 j) := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, u₃.gpr, u₂.mem, u₁.mem,
      xor_setWidth, hI.data hp hc]
  have hm₉ : s₉.mem = s.mem.writeW (st s₀ + BitVec.ofNat 64 j)
      (s₀.mem (dp s₀ + BitVec.ofNat 64 c) ^^^ s.mem (st s₀ + BitVec.ofNat 64 j)) := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, g₅.mem, hv, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hf : Frame [stR s₀] s.mem s₉.mem := by
    rw [hm₉]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_offset (by omega_arith) (by omega_arith))
  have g : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r30 → r ≠ .r29 → r ≠ .r31 →
      s₉.gpr r = s.gpr r := fun r h9 h10 h11 h23 h22 h24 => by
    rw [u₉.other r h9, u₈.other r h24, u₇.other r h22, u₆.other r h23, g₅.gpr, u₄.other r h9,
      u₃.other r h11, u₂.other r h10, u₁.other r h9]
  have h22 : s₉.gpr .r29 = BitVec.ofNat 64 (j + 1) := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hr22, ← BitVec.ofNat_add]
  have h21 : s₉.gpr .r28 = s₀.gpr .r4 := by
    rw [g .r28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.r28]
  refine ⟨⟨by omega_arith, ?_, ?_, ?_, ?_, ?_, h21, ?_, ?_, ?_, ?_, fun r hr => by
      have hne : r ≠ .r9 ∧ r ≠ .r10 ∧ r ≠ .r11 ∧ r ≠ .r30 ∧ r ≠ .r29 ∧ r ≠ .r31 :=
        ⟨notU hr _, notU hr _, notU hr _, notU hr _, notU hr _, notU hr _⟩
      rw [g r hne.1 hne.2.1 hne.2.2.1 hne.2.2.2.1 hne.2.2.2.2.1 hne.2.2.2.2.2]
      exact hI.untouched r hr⟩, h22, ?_, ?_⟩
  · rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, g₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hI.rd]
  · rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, g₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr]
  · rw [g .r26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.r26]
  · rw [g .r27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.r27]
  · rw [u₉.sp, u₈.sp, u₇.sp, u₆.sp, g₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, hI.sp]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hI.r30, BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hI.r31, sub_ofNat (by omega_arith), Nat.sub_sub]
  · exact hI.frame.trans (hf.mono (by simp))
  · exact hI.saved.state hp.st_scr hf
  · rw [eval_zero, u₉.gpr, ← u₉.other .r29 (by decide),
      ← u₉.other .r28 (by decide), h22, h21, sub_beq_zero (by omega_arith)]
  · refine stateAt_xorByte (by omega_arith) ?_ fun i hi hij => ?_
    · rw [hm₉, writeW8_apply, ite_eq_left_of_eq_true _ _ (eq_true rfl), BitVec.xor_comm]
    · rw [hm₉, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (VG.Proof.Sha3.ne_of_lt200 hi (by omega_arith) hij))]

/-- The bytes `c … c + n - 1` of the data follow the first `c`. -/
theorem bytesAt_add (m : Mem) (p : Addr) (c : Nat) :
    ∀ n, bytesAt m p (c + n) = bytesAt m p c ++ bytesAt m (p + BitVec.ofNat 64 c) n
  | 0 => by simp [bytesAt]
  | n + 1 => by
    rw [← Nat.add_assoc, bytesAt_succ, bytesAt_add m p c n, bytesAt_succ, List.append_assoc,
      BitVec.add_assoc, ← BitVec.ofNat_add]

theorem rate_mod8 {r : Nat} (h : r ∈ rates) : r % 8 = 0 := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- A lane of a state in memory written: its 8 bytes XORed with `bs`. -/
theorem stateAt_write_lane {m : Mem} {p : Addr} {j : Nat} (hj : j + 8 ≤ 200) {v : BitVec 64}
    {bs : List Byte} (hbs : bs.length = 8)
    (hv : ∀ d < 8, v.extractLsb' (8 * d) 8 = m (p + BitVec.ofNat 64 (j + d)) ^^^ bs.getD d 0) :
    stateAt (m.writeW (p + BitVec.ofNat 64 j) v) p = xorAt (stateAt m p) j bs :=
  Proof.Sha3.ext_bytes fun i hi => by
    rw [byteOf_xorAt _ _ _ hi, byteOf_stateAt _ _ hi, byteOf_stateAt _ _ hi, hbs]
    by_cases c : j ≤ i ∧ i < j + 8
    · rw [ite_eq_left c, show p + BitVec.ofNat 64 i = p + BitVec.ofNat 64 j + BitVec.ofNat 64 (i - j) by
          rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' c.1],
        writeW64_byte _ _ _ (by omega_arith), hv _ (by omega_arith), Nat.add_sub_cancel' c.1,
        show p + BitVec.ofNat 64 j + BitVec.ofNat 64 (i - j) = p + BitVec.ofNat 64 i by
          rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' c.1]]
    · rw [ite_eq_right c, Mem.writeW, Mem.write_apply]
      rw [show p + BitVec.ofNat 64 i - (p + BitVec.ofNat 64 j) = BitVec.ofNat 64 i - BitVec.ofNat 64 j by
        bv_omega, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega_arith

/-- The block of the body: the lane of data at `c` XORed into the lane at
position `j`. -/
theorem body_word {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c + 8 ≤ len s₀) {s : State}
    (hI : Inv s₀ c s) (hj8 : (pos s₀ + c) % rt s₀ % 8 = 0) :
    WP isa (.block absorbWord) s fun s' =>
      Common s₀ (c + 8) s' ∧ s'.gpr .r29 = BitVec.ofNat 64 ((pos s₀ + c) % rt s₀ + 8) ∧
      eval (.zero .d .r9) s' = some (decide ((pos s₀ + c) % rt s₀ + 8 = rt s₀)) ∧
      stateAt s'.mem (st s₀) = xorAt (stateAt s.mem (st s₀)) ((pos s₀ + c) % rt s₀)
        (bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) 8) := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  have hl := len_lt s₀
  have h8 := rate_mod8 hp.rate
  have hj : (pos s₀ + c) % rt s₀ < rt s₀ := Nat.mod_lt _ hr₀
  generalize hjd : (pos s₀ + c) % rt s₀ = j at hj hj8 ⊢
  have hj' : j + 8 ≤ rt s₀ := by omega_arith
  have hr22 : s.gpr .r29 = BitVec.ofNat 64 j := by rw [hI.r29, hjd]
  have hsin : ∀ rs : List Region, stR s₀ ∈ rs → InRegions rs (st s₀ + BitVec.ofNat 64 j) 8 :=
    fun rs h => ⟨stR s₀, h, contains_offset (by omega_arith) (by omega_arith)⟩
  refine wp_ld (t := .r9) (a := dp s₀ + BitVec.ofNat 64 c) (by decide) (by rw [hI.r30]; simp)
    ⟨dR s₀, by simp [hI.rd, hp.rd], contains_offset (by omega_arith) (by omega_arith)⟩ fun s₁ u₁ => ?_
  refine wp_add fun s₂ u₂ => ?_
  have ea : s₂.gpr .r10 + BitVec.ofNat 64 0 = st s₀ + BitVec.ofNat 64 j := by
    rw [u₂.gpr, u₁.other _ (by decide), u₁.other _ (by decide), hI.r26, hr22]; simp
  refine wp_ld (t := .r11) (a := st s₀ + BitVec.ofNat 64 j) (by decide) ea
    (hsin _ (by simp [u₂.rd, u₂.wr, u₁.rd, u₁.wr, hI.rd, hI.wr, hp.wr])) fun s₃ u₃ => ?_
  refine wp_xor fun s₄ u₄ => ?_
  refine wp_std (a := st s₀ + BitVec.ofNat 64 j) (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide)]; exact ea)
    (hsin _ (by simp [u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr, hp.wr])) fun s₅ g₅ => ?_
  refine wp_addi (by decide) fun s₆ u₆ => wp_addi (by decide) fun s₇ u₇ =>
    wp_subi (by decide) fun s₈ u₈ => wp_sub fun s₉ u₉ => WP.block_nil ?_
  have hv : s₄.gpr .r9 = s.mem.readW (dp s₀ + BitVec.ofNat 64 c) 64 ^^^
      s.mem.readW (st s₀ + BitVec.ofNat 64 j) 64 := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, u₃.gpr, u₂.mem, u₁.mem]
  have hm₉ : s₉.mem = s.mem.writeW (st s₀ + BitVec.ofNat 64 j) (s₄.gpr .r9) := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, g₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hf : Frame [stR s₀] s.mem s₉.mem := by
    rw [hm₉]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_offset (by omega_arith) (by omega_arith))
  have g : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r30 → r ≠ .r29 → r ≠ .r31 →
      s₉.gpr r = s.gpr r := fun r h9 h10 h11 h23 h22 h24 => by
    rw [u₉.other r h9, u₈.other r h24, u₇.other r h22, u₆.other r h23, g₅.gpr, u₄.other r h9,
      u₃.other r h11, u₂.other r h10, u₁.other r h9]
  have h22 : s₉.gpr .r29 = BitVec.ofNat 64 (j + 8) := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hr22, ← BitVec.ofNat_add]
  have h21 : s₉.gpr .r28 = s₀.gpr .r4 := by
    rw [g .r28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.r28]
  refine ⟨⟨by omega_arith, ?_, ?_, ?_, ?_, ?_, h21, ?_, ?_, ?_, ?_, fun r hr => by
      have hne : r ≠ .r9 ∧ r ≠ .r10 ∧ r ≠ .r11 ∧ r ≠ .r30 ∧ r ≠ .r29 ∧ r ≠ .r31 :=
        ⟨notU hr _, notU hr _, notU hr _, notU hr _, notU hr _, notU hr _⟩
      rw [g r hne.1 hne.2.1 hne.2.2.1 hne.2.2.2.1 hne.2.2.2.2.1 hne.2.2.2.2.2]
      exact hI.untouched r hr⟩, h22, ?_, ?_⟩
  · rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, g₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hI.rd]
  · rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, g₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr]
  · rw [g .r26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.r26]
  · rw [g .r27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.r27]
  · rw [u₉.sp, u₈.sp, u₇.sp, u₆.sp, g₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, hI.sp]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hI.r30, BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hI.r31, sub_ofNat (by omega_arith), Nat.sub_sub]
  · exact hI.frame.trans (hf.mono (by simp))
  · exact hI.saved.state hp.st_scr hf
  · rw [eval_zero, u₉.gpr, ← u₉.other .r29 (by decide),
      ← u₉.other .r28 (by decide), h22, h21, sub_beq_zero (by omega_arith)]
  · rw [hm₉]
    refine stateAt_write_lane (by omega_arith) (bytesAt_length _ _ _) fun d hd => ?_
    rw [hv, BitVec.extractLsb'_xor, Mem.readW, Mem.readW, BitVec.setWidth_eq, BitVec.setWidth_eq,
      Mem.extractLsb'_read _ _ (show d < 64 / 8 by omega_arith), Mem.extractLsb'_read _ _ (show d < 64 / 8 by omega_arith),
      BitVec.xor_comm, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 1
    simp only [bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hd,
      Option.map_some, Option.getD_some]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, hI.data hp (by omega_arith)]

/-- After a lane or a byte of data: what the permutation, if the block is
complete, turns into the invariant. -/
structure After (s₀ : State) (s : State) (c n : Nat) (s' : State) : Prop where
  common : Common s₀ (c + n) s'
  r29 : s'.gpr .r29 = BitVec.ofNat 64 ((pos s₀ + c) % rt s₀ + n)
  z : eval (.zero .d .r9) s' = some (decide ((pos s₀ + c) % rt s₀ + n = rt s₀))
  st : stateAt s'.mem (st s₀) = xorAt (stateAt s.mem (st s₀)) ((pos s₀ + c) % rt s₀)
    (bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) n)

/-- The permutation if the block is complete. -/
theorem after_ok {s₀ : State} (hp : Pre s₀) {c n : Nat} (hn : 0 < n)
    (hfit : (pos s₀ + c) % rt s₀ + n ≤ rt s₀) {s s₁ : State} (hI : Inv s₀ c s) (h : After s₀ s c n s₁) :
    WP isa (.ite (.zero .d .r9) (.seq (.block [.li .r29 0]) permuteAt) (.block [])) s₁
      (Inv s₀ (c + n)) := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  have hC := h.common
  have hlen : ∀ msg, Msg s₀ msg → (msg ++ D s₀ c).length % rt s₀ = (pos s₀ + c) % rt s₀ :=
    fun msg ⟨_, hpm⟩ => by rw [List.length_append, bytesAt_length, hpm, Nat.mod_add_mod]
  have hrep : ∀ msg, Msg s₀ msg → Rep (rt s₀) (msg ++ D s₀ (c + n)) =
      if (pos s₀ + c) % rt s₀ + n = rt s₀ then keccakF (stateAt s₁.mem (st s₀))
      else stateAt s₁.mem (st s₀) := fun msg hm => by
    rw [D, bytesAt_add, ← List.append_assoc, rep_append hr₀ (by omega_arith) _ _
      (by rw [bytesAt_length]; exact hn) (by rw [bytesAt_length, hlen msg hm]; exact hfit),
      hlen msg hm, bytesAt_length, h.st, hI.repr msg hm]
  have hpc : (pos s₀ + (c + n)) % rt s₀ = if (pos s₀ + c) % rt s₀ + n = rt s₀ then 0
      else (pos s₀ + c) % rt s₀ + n := by
    have e := Nat.div_add_mod (pos s₀ + c) (rt s₀)
    rw [show pos s₀ + (c + n) = (pos s₀ + c) + n by omega_arith]
    generalize (pos s₀ + c) % rt s₀ = j at e hfit ⊢
    generalize (pos s₀ + c) / rt s₀ = q at e
    rw [← e]
    split
    · rw [Nat.add_assoc, ‹j + n = rt s₀›, ← Nat.mul_succ, Nat.mul_mod_right]
    · rw [Nat.add_assoc, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega_arith)]
  refine WP.ite (decide ((pos s₀ + c) % rt s₀ + n = rt s₀)) h.z (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine WP.seq (wp_li (by decide) fun s₂ u₂ => WP.block_nil ?_)
    have hC₂ := hC.of_gpr (fun r hr => u₂.other r (keepNe hr _)) u₂.mem u₂.rd u₂.wr u₂.sp
    refine permuteAt_ok hC₂.r26 hC₂.r27 (hp.st_scr.sub_right (Region.sub_prefix (by omega_arith)))
      ?_ fun s₃ rd₃ wr₃ sp₃ cs₃ f₃ e₃ => ?_
    · rw [hC₂.wr, hp.wr]
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
      · exact ⟨scR s₀, by simp, 0, by simp, by simp⟩
    · refine { hC₂.after_call hp rd₃ wr₃ sp₃ cs₃ f₃ with r29 := ?_, repr := fun msg hm => ?_ }
      · rw [cs₃ _ (by decide), u₂.gpr, hpc, ite_eq_left_of_eq_true _ _ (eq_true hb)]
      · rw [e₃, u₂.mem, hrep msg hm, ite_eq_left_of_eq_true _ _ (eq_true hb)]
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.block_nil { hC with r29 := ?_, repr := fun msg hm => ?_ }
    · rw [h.r29, hpc, ite_eq_right_of_eq_false _ _ (eq_false hb)]
    · rw [hrep msg hm, ite_eq_right_of_eq_false _ _ (eq_false hb)]

/-- The whole body: a lane or a byte of data. -/
theorem body_ok {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c < len s₀) {s : State} (hI : Inv s₀ c s) :
    WP isa (absorbBody) s fun s' => ∃ c', c < c' ∧ c' ≤ len s₀ ∧ Inv s₀ c' s' := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  have h8 := rate_mod8 hp.rate
  have hj : (pos s₀ + c) % rt s₀ < rt s₀ := Nat.mod_lt _ hr₀
  unfold absorbBody
  refine WP.seq (wp_li (by decide) fun s₃ u₃ => wp_and fun s₄ u₄ => wp_subi (by decide) fun s₅ u₅ =>
    wp_lsr (by decide) fun s₆ u₆ => wp_or fun s₇ u₇ => WP.block_nil ?_)
  have oth : ∀ r, r ≠ .r10 → r ≠ .r11 → s₇.gpr r = s.gpr r := fun r h10 h11 => by
    rw [u₇.other r h10, u₆.other r h11, u₅.other r h11, u₄.other r h10, u₃.other r h10]
  have m₇ : s₇.mem = s.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have hI₇ : Inv s₀ c s₇ :=
    { hI.toCommon.of_gpr (fun r hr => oth r (keepNe hr _) (keepNe hr _)) m₇
        (by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd]) (by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr])
        (by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp]) with
      r29 := by rw [oth _ (by decide) (by decide)]; exact hI.r29
      repr := fun msg hm => by rw [m₇]; exact hI.repr msg hm }
  have hx10 : s₇.gpr .r10 = 0 → (pos s₀ + c) % rt s₀ % 8 = 0 ∧ 8 ≤ len s₀ - c := fun h0 => by
    rw [u₇.gpr, u₆.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₃.gpr, u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), hI.r29, hI.r31] at h0
    have h0' := congrArg BitVec.toNat h0
    simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_sub,
      BitVec.toNat_ofNat] at h0'
    have hpos : (pos s₀ + c) % rt s₀ < 2 ^ 64 := by have := (s₀.gpr .r4).isLt; omega_arith
    simp only [show 7 % 2 ^ 64 = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      Nat.shiftRight_eq_div_pow, show BitVec.toNat (0 : BitVec 64) = 0 from rfl,
      Nat.or_eq_zero_iff] at h0'
    have hl := len_lt s₀
    omega_arith
  refine WP.seq (WP.mono (Q := fun s₁ => ∃ n, 0 < n ∧ (pos s₀ + c) % rt s₀ + n ≤ rt s₀ ∧
      c + n ≤ len s₀ ∧ After s₀ s₇ c n s₁) ?_
    fun s₁ ⟨n, hn, hfit, hcn, hA⟩ => WP.mono (after_ok hp hn hfit hI₇ hA)
      fun s' h => ⟨c + n, by omega_arith, hcn, h⟩)
  refine WP.ite (s₇.gpr .r10 == 0) (eval_zero _ _) (fun hb => ?_) (fun _ => ?_)
  · obtain ⟨m8, l8⟩ := hx10 (by simpa using hb)
    exact WP.mono (body_word hp (by omega_arith) hI₇ m8) fun s₁ ⟨hC, h22, hz, hst⟩ =>
      ⟨8, by decide, by omega_arith, by omega_arith, hC, h22, hz, hst⟩
  · refine WP.mono (body_byte hp hc hI₇) fun s₁ ⟨hC, h22, hz, hst⟩ =>
      ⟨1, by decide, by omega_arith, by omega_arith, hC, h22, hz, ?_⟩
    rw [hst]
    simp [bytesAt, xorAt_single]

/-! ## The epilogue -/

/-- The epilogue's postcondition. -/
def Post (s₀ s' : State) : Prop :=
  (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.sp = s₀.sp ∧ Proof.Sha3.absorbPPC64LE.post s₀ s'

theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {s : State} (hI : Inv s₀ (len s₀) s) :
    WP isa (.block (mov .r3 .r29 :: restore)) s (Post s₀) := by
  have ⟨hr₀, _⟩ := hp.rt_pos
  refine wp_mov fun s₁ u₁ => ?_
  refine restore_ok (scr := scr s₀) (by rw [u₁.other _ (by decide), hI.r27])
    (fun d hd₁ hd₂ => ⟨scR s₀, by simp [u₁.rd, u₁.wr, hI.rd, hI.wr, hp.wr],
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    s₀.gpr (by rw [u₁.mem]; exact hI.saved) fun s' hsv other m _ _ sp => ⟨preserved_of hsv fun r hr => ?_,
      by rw [sp, u₁.sp, hI.sp], ⟨fun msg hm hpm => ?_, ?_⟩⟩
  · rw [other r (by revert r; decide), u₁.other r (notU hr _)]
    exact hI.untouched r hr
  · rw [Proof.Sha3.repr_iff, m, u₁.mem]
    exact hI.repr msg ⟨hm, hpm⟩
  · rw [other _ (by decide), u₁.gpr, hI.r29,
      toNat_ofNat_lt (by have := Nat.mod_lt (pos s₀ + len s₀) hr₀; omega_arith)]

/-! ## The whole function -/

theorem absorb_eq : absorbMain = .seq (.block setup)
    (.seq (.ite (.zero .d .r31) (.block []) (.loop absorbBody (.nonzero .d .r31)))
      (.block (mov .r3 .r29 :: restore))) := rfl

/-- `absorb` without its frame. -/
theorem correctMain {s₀ : State} (hp : Pre s₀) : WP isa absorbMain s₀ (Post s₀) := by
  have hl := len_lt s₀
  rw [absorb_eq]
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ hI => ?_)
  refine WP.seq (WP.mono (Q := Inv s₀ (len s₀)) ?_ fun s₂ hI₂ => epilogue_ok hp hI₂)
  refine WP.ite (decide (len s₀ = 0))
    (by show VG.PPC64LE.eval (.zero .d .r31) s₁ = _
        rw [eval_zero, hI.r31, Nat.sub_zero, ofNat_beq_zero (by omega_arith)])
    (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.block_nil (hb ▸ hI)
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.loop (M := isa) (fun n s => ∃ c, n = len s₀ - c ∧ c < len s₀ ∧ Inv s₀ c s) ?_ (len s₀) s₁
      ⟨0, rfl, by omega_arith, hI⟩
    rintro n s ⟨c, rfl, hcl, hI⟩
    refine WP.mono (body_ok hp hcl hI) fun s' ⟨c', hcc, hc', hI'⟩ => ?_
    have hz : isa.eval (.nonzero .d .r31) s' = some (decide (len s₀ - c' ≠ 0)) := by
      show VG.PPC64LE.eval (.nonzero .d .r31) s' = _
      rw [eval_nonzero, hI'.r31, bne, ofNat_beq_zero (by omega_arith)]
      simp
    by_cases he : len s₀ - c' = 0
    · refine .inl ⟨by rw [hz]; simp [he], ?_⟩
      rwa [show c' = len s₀ by omega_arith] at hI'
    · exact .inr ⟨by rw [hz]; simp [he], len s₀ - c', by omega_arith, c', rfl, by omega_arith, hI'⟩

end VG.Proof.Sha3.PPC64LE.Stream.Absorb
