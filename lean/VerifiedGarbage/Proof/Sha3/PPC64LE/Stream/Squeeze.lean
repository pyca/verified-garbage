module

public import VerifiedGarbage.Proof.Sha3.PPC64LE.Call
public import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.Wp
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The SHA-3 sponge on PPC64LE: `squeeze`

The same structure as the AArch64 proof (`VG.Proof.Sha3.AArch64.Stream.Squeeze`):
`squeezeMain`, whose frame saving the link register `correct` adds
(`WP.frameReg`).
-/

@[expose] public section

namespace VG.Proof.Sha3.PPC64LE.Stream.Squeeze

open VG VG.PPC64LE VG.Impl.Sha3.PPC64LE.Stream
open VG.Proof.Sha3.PPC64LE VG.Proof.Sha3.PPC64LE.Stream
open VG.Proof.MdStream.PPC64LE (Upd Mupd wp_addi wp_mov wp_subi wp_li wp_add wp_sub wp_and wp_lsr
  wp_lbz wp_stb wp_std wp_ld eval_zero eval_nonzero contains_offset toNat_ofNat_lt)
open VG.Spec.Sha3 (stateAt keccakF bytesAt rates)
open VG.Proof.Sha3 (byteOf byteOf_stateAt iterF iterF_succ length_squeezeFrom squeezeFrom_getElem
  squeezeFrom_iterF ofNat_beq_zero sub_beq_zero sub_ofNat writeW8_self writeW8_other div_mod_eq
  writeW64_byte)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev stp : Addr := s₀.gpr .r3
abbrev rate : Nat := (s₀.gpr .r4).toNat
abbrev pos₀ : Nat := (s₀.gpr .r5).toNat
abbrev outp : Addr := s₀.gpr .r6
abbrev outn : Nat := (s₀.gpr .r7).toNat
abbrev scrp : Addr := s₀.gpr .r8
abbrev SR : Region := ⟨stp s₀, 200⟩
abbrev OR : Region := ⟨outp s₀, outn s₀⟩
abbrev CR : Region := ⟨scrp s₀, 640⟩
/-- The frame saving the link register, below the stack pointer. -/
abbrev KR : Region := ⟨s₀.sp - 48, 48⟩
/-- The initial state. -/
abbrev S₀ : Spec.Sha3.State := stateAt s₀.mem (stp s₀)

end

structure SPre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [SR s₀, OR s₀, CR s₀]
  st_o : (SR s₀).Disjoint (OR s₀)
  st_c : (SR s₀).Disjoint (CR s₀)
  o_c : (OR s₀).Disjoint (CR s₀)
  rate_mem : rate s₀ ∈ rates
  pos_le : pos₀ s₀ ≤ rate s₀

/-- The frame is below the stack pointer, and disjoint from the buffers. -/
structure Stack (s₀ : State) : Prop where
  sp48 : 48 ≤ s₀.sp.toNat
  st : (KR s₀).Disjoint (SR s₀)
  o : (KR s₀).Disjoint (OR s₀)
  c : (KR s₀).Disjoint (CR s₀)

theorem pre_of {s₀ : State} (h : Proof.Sha3.squeezePPC64LE.pre s₀) : SPre s₀ ∧ Stack s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5, h10, h11⟩, ⟨h6, h7, h8, h9⟩⟩

theorem SPre.rate_pos {s₀ : State} (hp : SPre s₀) : 0 < rate s₀ ∧ rate s₀ ≤ 200 := by
  have := Proof.Sha3.rate_bounds hp.rate_mem
  omega_arith

theorem outn_lt (s₀ : State) : outn s₀ < 2 ^ 64 := (s₀.gpr .r7).isLt

/-- The registers the body never writes but by the call. -/
abbrev keep : List Reg := [.r26, .r27, .r28, .r29, .r30, .r31] ++ untouched

theorem keepNe {r : Reg} (hr : r ∈ keep) (x : Reg) (hx : x ∉ keep := by decide) : r ≠ x :=
  fun h => hx (h ▸ hr)

/-! ## The loop invariant -/

/-- After `i` bytes of output, `k` permutations and `pos` bytes of the
current block: `pos₀ + i = rate * k + pos`. -/
structure Inv (s₀ : State) (i k pos : Nat) (s : State) : Prop where
  i_le : i ≤ outn s₀
  hi : pos₀ s₀ + i = rate s₀ * k + pos
  pos_le : pos ≤ rate s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  r26 : s.gpr .r26 = stp s₀
  r27 : s.gpr .r27 = scrp s₀
  r28 : s.gpr .r28 = s₀.gpr .r4
  r29 : s.gpr .r29 = BitVec.ofNat 64 pos
  r30 : s.gpr .r30 = outp s₀ + BitVec.ofNat 64 i
  r31 : s.gpr .r31 = BitVec.ofNat 64 (outn s₀ - i)
  sp : s.sp = s₀.sp
  frame : Frame [SR s₀, OR s₀, CR s₀] s₀.mem s.mem
  saved : Saved (scrp s₀) s₀.gpr s.mem
  untouched : ∀ r ∈ untouched, s.gpr r = s₀.gpr r
  state : stateAt s.mem (stp s₀) = iterF k (S₀ s₀)
  out : ∀ j < i, s.mem (outp s₀ + BitVec.ofNat 64 j) =
    byteOf (iterF ((pos₀ s₀ + j) / rate s₀) (S₀ s₀)) ((pos₀ s₀ + j) % rate s₀)

theorem Inv.congr {s₀ : State} {i k pos : Nat} {s s' : State} (h : Inv s₀ i k pos s)
    (hg : ∀ r ∈ keep, s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    Inv s₀ i k pos s' where
  i_le := h.i_le
  hi := h.hi
  pos_le := h.pos_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  r26 := by rw [hg _ (by decide)]; exact h.r26
  r27 := by rw [hg _ (by decide)]; exact h.r27
  r28 := by rw [hg _ (by decide)]; exact h.r28
  r29 := by rw [hg _ (by decide)]; exact h.r29
  r30 := by rw [hg _ (by decide)]; exact h.r30
  r31 := by rw [hg _ (by decide)]; exact h.r31
  sp := hsp.trans h.sp
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved
  untouched := fun r hr => (hg r (List.mem_append_right _ hr)).trans (h.untouched r hr)
  state := by rw [hm]; exact h.state
  out := by rw [hm]; exact h.out

theorem prologue_ok {s₀ : State} (hp : SPre s₀) : WP isa (.block setup) s₀ (Inv s₀ 0 0 (pos₀ s₀)) := by
  unfold setup
  refine save_ok (by decide) (fun d hd₁ hd₂ => ⟨CR s₀, by simp [hp.wr], Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    fun s g₁ rd₁ wr₁ sp₁ m₁ => ?_
  refine wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ =>
    wp_mov fun s₅ u₅ => wp_mov fun s₆ u₆ => WP.block_nil ?_
  have hm : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hf : Frame [CR s₀] s₀.mem s.mem := by
    rw [m₁]
    exact (saveMem_frame _ _ _).sub fun r hr => ⟨CR s₀, by simp,
      by simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by omega_arith)⟩
  have oth : ∀ r, r ∉ [Reg.r26, .r27, .r28, .r29, .r30, .r31] → s₆.gpr r = s₀.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₆.other _ hr.2.2.2.2.2, u₅.other _ hr.2.2.2.2.1, u₄.other _ hr.2.2.2.1, u₃.other _ hr.2.2.1,
      u₂.other _ hr.2.1, u₁.other _ hr.1, g₁]
  refine ⟨Nat.zero_le _, by simp, hp.pos_le, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by rw [hm]; exact hf.mono (by simp), by rw [hm, m₁]; exact saveMem_saved _ _ _,
    fun r hr => oth r (by revert r; decide), ?_, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, rd₁]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, wr₁]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, g₁]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), g₁]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), g₁]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), g₁]; simp
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), g₁]; simp
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), g₁]; simp
  · rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, sp₁]
  · rw [hm]
    exact Proof.Sha3.stateAt_congr fun j hj => hf.bytes (R := SR s₀) (by simpa using hp.st_c) (by simp) hj

/-! ## One iteration -/

theorem permute_ok {s₀ : State} (hp : SPre s₀) {i k : Nat} {s : State} (hI : Inv s₀ i k (rate s₀) s) :
    WP isa (.seq (.block [.li .r29 0]) permuteAt) s (Inv s₀ i (k + 1) 0) := by
  refine WP.seq (wp_li (by decide) fun s₁ u₁ => WP.block_nil ?_)
  have e200 : Region.Sub ⟨stp s₀, 200⟩ (SR s₀) := fun _ h => h
  have e512 : Region.Sub ⟨scrp s₀, 512⟩ (CR s₀) := Region.sub_prefix (by omega_arith)
  refine permuteAt_ok (st := stp s₀) (scr := scrp s₀) (by rw [u₁.other _ (by decide), hI.r26])
    (by rw [u₁.other _ (by decide), hI.r27]) (hp.st_c.sub_right e512) ?_
    fun s' rd' wr' sp' cs' hf hst => ?_
  · rw [u₁.wr, hI.wr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨SR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨CR s₀, by simp, 0, by simp, by simp⟩
  have cs : ∀ r ∈ preserved, s'.gpr r = s₁.gpr r := cs'
  have hd : ∀ r ∈ [(⟨stp s₀, 200⟩ : Region), ⟨scrp s₀, 512⟩], (OR s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.st_o.symm
    · exact hp.o_c.sub_right e512
  refine ⟨hI.i_le, by rw [hI.hi, Nat.mul_succ]; rfl, Nat.zero_le _, rd'.trans (u₁.rd.trans hI.rd),
    wr'.trans (u₁.wr.trans hI.wr), ?_, ?_, ?_, ?_, ?_, ?_, by rw [sp', u₁.sp, hI.sp], ?_, ?_, (fun r hr => by
      rw [cs r (untouched_preserved r hr), u₁.other r (notU hr _)]
      exact hI.untouched r hr), ?_,
    fun j hj => ?_⟩
  · rw [cs _ (by decide), u₁.other _ (by decide), hI.r26]
  · rw [cs _ (by decide), u₁.other _ (by decide), hI.r27]
  · rw [cs _ (by decide), u₁.other _ (by decide), hI.r28]
  · rw [cs _ (by decide), u₁.gpr]
  · rw [cs _ (by decide), u₁.other _ (by decide), hI.r30]
  · rw [cs _ (by decide), u₁.other _ (by decide), hI.r31]
  · have hfs : Frame [SR s₀, OR s₀, CR s₀] s₁.mem s'.mem := by
      refine hf.sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨SR s₀, by simp, e200⟩
      · exact ⟨CR s₀, by simp, e512⟩
    rw [u₁.mem] at hfs
    exact hI.frame.trans hfs
  · exact Saved.permute (by rw [u₁.mem]; exact hI.saved) hp.st_c hf
  · rw [hst, u₁.mem, hI.state, iterF_succ]
  · refine Eq.trans (hf.bytes (R := OR s₀) hd (Nat.le_of_lt (outn_lt s₀)) (by have := hI.i_le; omega_arith : j < outn s₀)) ?_
    rw [u₁.mem]; exact hI.out j hj

theorem store_ok {s₀ : State} (hp : SPre s₀) {i k pos : Nat} {s : State} (hI : Inv s₀ i k pos s)
    (hlt : pos < rate s₀) (hi : i < outn s₀) :
    WP isa (.block squeezeByte) s (Inv s₀ (i + 1) k (pos + 1)) := by
  have ⟨hr0, hr200⟩ := hp.rate_pos
  have hn := outn_lt s₀
  refine wp_add fun s₁ u₁ => ?_
  refine wp_lbz (a := stp s₀ + BitVec.ofNat 64 pos) (by decide) (by rw [u₁.gpr, hI.r26, hI.r29]; simp)
    ⟨SR s₀, by simp [u₁.rd, u₁.wr, hI.rd, hI.wr, hp.rd, hp.wr], contains_offset (by omega_arith) (by omega_arith)⟩
    fun s₂ u₂ => ?_
  refine wp_stb (a := outp s₀ + BitVec.ofNat 64 i) (by decide)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hI.r30]; simp)
    (by rw [u₂.wr, u₁.wr, hI.wr, hp.wr]; exact ⟨OR s₀, by simp, contains_offset (by omega_arith) (by omega_arith)⟩)
    fun s₃ g₃ => ?_
  refine wp_addi (by decide) fun s₄ u₄ => wp_addi (by decide) fun s₅ u₅ =>
    wp_subi (by decide) fun s₆ u₆ => WP.block_nil ?_
  have g : ∀ r, r ≠ .r10 → r ≠ .r9 → r ≠ .r30 → r ≠ .r29 → r ≠ .r31 → s₆.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by
      rw [u₆.other r h5, u₅.other r h4, u₄.other r h3, g₃.gpr, u₂.other r h2, u₁.other r h1]
  have hb : s.mem (stp s₀ + BitVec.ofNat 64 pos) = byteOf (iterF k (S₀ s₀)) pos := by
    rw [← hI.state, byteOf_stateAt _ _ (by omega_arith)]
  have hm : s₆.mem = s.mem.writeW (outp s₀ + BitVec.ofNat 64 i) (byteOf (iterF k (S₀ s₀)) pos) := by
    rw [u₆.mem, u₅.mem, u₄.mem, g₃.mem, u₂.gpr, u₂.mem, u₁.mem, BitVec.setWidth_setWidth_of_le _ (by omega_arith),
      BitVec.setWidth_eq, hb]
  have hfw : Frame [OR s₀] s.mem s₆.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_offset (by omega_arith) (by omega_arith))
  refine ⟨by omega_arith, by have := hI.hi; omega_arith, by omega_arith, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hI.frame.trans (hfw.mono (by simp)), ?_, (fun r hr => by
      rw [g r (notU hr _) (notU hr _) (notU hr _) (notU hr _) (notU hr _)]
      exact hI.untouched r hr), ?_, fun j hj => ?_⟩
  · rw [u₆.rd, u₅.rd, u₄.rd, g₃.rd, u₂.rd, u₁.rd, hI.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, g₃.wr, u₂.wr, u₁.wr, hI.wr]
  · rw [g .r26 (by decide) (by decide) (by decide) (by decide) (by decide), hI.r26]
  · rw [g .r27 (by decide) (by decide) (by decide) (by decide) (by decide), hI.r27]
  · rw [g .r28 (by decide) (by decide) (by decide) (by decide) (by decide), hI.r28]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), hI.r29, ← BitVec.ofNat_add]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), hI.r30, BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), hI.r31, sub_ofNat (by omega_arith), Nat.sub_sub]
  · rw [u₆.sp, u₅.sp, u₄.sp, g₃.sp, u₂.sp, u₁.sp, hI.sp]
  · exact hI.saved.disjoint hp.o_c hfw
  · rw [Proof.Sha3.stateAt_congr fun j hj => hfw.bytes (R := SR s₀) (by simpa using hp.st_o) (by simp) hj]
    exact hI.state
  · rw [hm]
    by_cases e : j = i
    · subst e
      obtain ⟨d, m⟩ := div_mod_eq (k := k) hr0 hlt
      rw [writeW8_self, hI.hi, d, m]
    · rw [writeW8_other _ _ (Offset.add_ofNat_ne _ (by omega_arith) (by omega_arith) e)]
      exact hI.out j (by omega_arith)

/-- Every rate is a whole number of lanes. -/
theorem rate_mod8 {r : Nat} (h : r ∈ rates) : r % 8 = 0 := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem store8_ok {s₀ : State} (hp : SPre s₀) {i k pos : Nat} {s : State} (hI : Inv s₀ i k pos s)
    (hlt : pos + 8 ≤ rate s₀) (hi : i + 8 ≤ outn s₀) :
    WP isa (.block squeezeWord) s (Inv s₀ (i + 8) k (pos + 8)) := by
  have ⟨hr0, hr200⟩ := hp.rate_pos
  have hn := outn_lt s₀
  refine wp_add fun s₁ u₁ => ?_
  refine wp_ld (a := stp s₀ + BitVec.ofNat 64 pos) (by decide) (by rw [u₁.gpr, hI.r26, hI.r29]; simp)
    ⟨SR s₀, by simp [u₁.rd, u₁.wr, hI.rd, hI.wr, hp.rd, hp.wr], contains_offset (by omega_arith) (by omega_arith)⟩
    fun s₂ u₂ => ?_
  refine wp_std (a := outp s₀ + BitVec.ofNat 64 i) (by decide)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hI.r30]; simp)
    (by rw [u₂.wr, u₁.wr, hI.wr, hp.wr]; exact ⟨OR s₀, by simp, contains_offset (by omega_arith) (by omega_arith)⟩)
    fun s₃ g₃ => ?_
  refine wp_addi (by decide) fun s₄ u₄ => wp_addi (by decide) fun s₅ u₅ =>
    wp_subi (by decide) fun s₆ u₆ => WP.block_nil ?_
  have g : ∀ r, r ≠ .r10 → r ≠ .r9 → r ≠ .r30 → r ≠ .r29 → r ≠ .r31 → s₆.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by
      rw [u₆.other r h5, u₅.other r h4, u₄.other r h3, g₃.gpr, u₂.other r h2, u₁.other r h1]
  have hm : s₆.mem = s.mem.writeW (outp s₀ + BitVec.ofNat 64 i) (s.mem.readW (stp s₀ + BitVec.ofNat 64 pos) 64) := by
    rw [u₆.mem, u₅.mem, u₄.mem, g₃.mem, u₂.gpr, u₂.mem, u₁.mem]
  have hfw : Frame [OR s₀] s.mem s₆.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_offset (by omega_arith) (by omega_arith))
  refine ⟨by omega_arith, by have := hI.hi; omega_arith, by omega_arith, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hI.frame.trans (hfw.mono (by simp)), ?_, (fun r hr => by
      rw [g r (notU hr _) (notU hr _) (notU hr _) (notU hr _) (notU hr _)]
      exact hI.untouched r hr), ?_, fun j hj => ?_⟩
  · rw [u₆.rd, u₅.rd, u₄.rd, g₃.rd, u₂.rd, u₁.rd, hI.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, g₃.wr, u₂.wr, u₁.wr, hI.wr]
  · rw [g .r26 (by decide) (by decide) (by decide) (by decide) (by decide), hI.r26]
  · rw [g .r27 (by decide) (by decide) (by decide) (by decide) (by decide), hI.r27]
  · rw [g .r28 (by decide) (by decide) (by decide) (by decide) (by decide), hI.r28]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), hI.r29, ← BitVec.ofNat_add]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), hI.r30, BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), hI.r31, sub_ofNat (by omega_arith), Nat.sub_sub]
  · rw [u₆.sp, u₅.sp, u₄.sp, g₃.sp, u₂.sp, u₁.sp, hI.sp]
  · exact hI.saved.disjoint hp.o_c hfw
  · rw [Proof.Sha3.stateAt_congr fun j hj => hfw.bytes (R := SR s₀) (by simpa using hp.st_o) (by simp) hj]
    exact hI.state
  · rw [hm]
    by_cases e : i ≤ j
    · rw [show outp s₀ + BitVec.ofNat 64 j = outp s₀ + BitVec.ofNat 64 i + BitVec.ofNat 64 (j - i) by
          rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' e],
        writeW64_byte _ _ _ (by omega_arith), Mem.readW, BitVec.setWidth_eq,
        Mem.extractLsb'_read s.mem (stp s₀ + BitVec.ofNat 64 pos) (n := 64 / 8) (show j - i < 64 / 8 by omega_arith),
        BitVec.add_assoc, ← BitVec.ofNat_add,
        ← byteOf_stateAt s.mem (stp s₀) (show pos + (j - i) < 200 by omega_arith), hI.state]
      obtain ⟨d, m⟩ := div_mod_eq (k := k) hr0 (show pos + (j - i) < rate s₀ by omega_arith)
      rw [show pos₀ s₀ + j = rate s₀ * k + (pos + (j - i)) by have := hI.hi; omega_arith, d, m]
    · rw [Mem.writeW, Mem.write_apply (by
        rw [show outp s₀ + BitVec.ofNat 64 j - (outp s₀ + BitVec.ofNat 64 i) =
          BitVec.ofNat 64 (2 ^ 64 - (i - j)) by bv_omega, BitVec.toNat_ofNat]
        omega_arith)]
      exact hI.out j (by omega_arith)

theorem body_ok {s₀ : State} (hp : SPre s₀) {i k pos : Nat} {s : State} (hI : Inv s₀ i k pos s)
    (hi : i < outn s₀) :
    WP isa (squeezeBody) s fun s' => ∃ i' k' pos', i < i' ∧ i' ≤ outn s₀ ∧ Inv s₀ i' k' pos' s' := by
  have ⟨hr0, _⟩ := hp.rate_pos
  have h8 := rate_mod8 hp.rate_mem
  unfold squeezeBody
  refine WP.seq (wp_sub fun s₁ u₁ => WP.block_nil ?_)
  have hI₁ := hI.congr (fun r hr => u₁.other r (keepNe hr _)) u₁.mem u₁.rd u₁.wr u₁.sp
  have hz : eval (.zero .d .r9) s₁ = some (decide (pos = rate s₀)) := by
    rw [eval_zero, u₁.gpr, hI.r29, hI.r28,
      sub_beq_zero (by have := hI.pos_le; have := (s₀.gpr .r4).isLt; omega_arith)]
  refine WP.seq (WP.mono (Q := fun s => ∃ k' pos', Inv s₀ i k' pos' s ∧ pos' < rate s₀) ?_
    fun s₂ ⟨k', pos', hI₂, hlt⟩ => ?_)
  · refine WP.ite (decide (pos = rate s₀)) hz (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      subst hb
      exact WP.mono (permute_ok hp hI₁) fun s' h => ⟨k + 1, 0, h, hr0⟩
    · simp only [decide_eq_false_iff_not] at hb
      exact WP.block_nil ⟨k, pos, hI₁, by have := hI.pos_le; omega_arith⟩
  -- a lane or a byte
  refine WP.seq (wp_li (by decide) fun s₃ u₃ => wp_and fun s₄ u₄ => wp_subi (by decide) fun s₅ u₅ =>
    wp_lsr (by decide) fun s₆ u₆ => wp_or fun s₇ u₇ => WP.block_nil ?_)
  have hI₇ := hI₂.congr (fun r hr => by
    rw [u₇.other r (keepNe hr _), u₆.other r (keepNe hr _), u₅.other r (keepNe hr _),
      u₄.other r (keepNe hr _), u₃.other r (keepNe hr _)])
    (by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]) (by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd])
    (by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr]) (by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp])
  have hx10 : s₇.gpr .r10 = 0 → pos' % 8 = 0 ∧ 8 ≤ outn s₀ - i := fun h0 => by
    rw [u₇.gpr, u₆.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₃.gpr, u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), hI₂.r29, hI₂.r31] at h0
    have h0' := congrArg BitVec.toNat h0
    simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_sub,
      BitVec.toNat_ofNat] at h0'
    have hpos : pos' < 2 ^ 64 := by have := hI₂.pos_le; have := (s₀.gpr .r4).isLt; omega_arith
    simp only [show 7 % 2 ^ 64 = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      Nat.shiftRight_eq_div_pow, show BitVec.toNat (0 : BitVec 64) = 0 from rfl,
      Nat.or_eq_zero_iff] at h0'
    have hn := outn_lt s₀
    omega_arith
  refine WP.ite (s₇.gpr .r10 == 0) (eval_zero _ _) (fun hb => ?_) (fun _ => ?_)
  · obtain ⟨m8, l8⟩ := hx10 (by simpa using hb)
    exact WP.mono (store8_ok hp hI₇ (by have := hI₇.pos_le; omega_arith) (by omega_arith))
      fun s' h => ⟨i + 8, k', pos' + 8, by omega_arith, by omega_arith, h⟩
  · exact WP.mono (store_ok hp hI₇ hlt hi) fun s' h => ⟨i + 1, k', pos' + 1, by omega_arith, by omega_arith, h⟩

/-! ## The epilogue -/

/-- The epilogue's postcondition. -/
def Post (s₀ s' : State) : Prop :=
  (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.sp = s₀.sp ∧ Proof.Sha3.squeezePPC64LE.post s₀ s'

theorem epilogue_ok {s₀ : State} (hp : SPre s₀) {k pos : Nat} {s : State} (hI : Inv s₀ (outn s₀) k pos s) :
    WP isa (.block (mov .r3 .r29 :: restore)) s (Post s₀) := by
  have ⟨hr0, hr200⟩ := hp.rate_pos
  have hpl := hI.pos_le
  refine wp_mov fun s₁ u₁ => ?_
  have hx0 : s₁.gpr .r3 = BitVec.ofNat 64 pos := by rw [u₁.gpr, hI.r29]
  refine restore_ok (scr := scrp s₀) (by rw [u₁.other _ (by decide), hI.r27])
    (fun d hd₁ hd₂ => ⟨CR s₀, by simp [u₁.rd, u₁.wr, hI.rd, hI.wr, hp.rd, hp.wr],
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    s₀.gpr (by rw [u₁.mem]; exact hI.saved) fun s' hsv other m _ _ sp => ⟨preserved_of hsv fun r hr => ?_,
      by rw [sp, u₁.sp, hI.sp], ⟨?_, ?_, fun d => ?_⟩⟩
  · rw [other r (by revert r; decide), u₁.other r (notU hr _)]
    exact hI.untouched r hr
  · have ax : s'.gpr .r3 = s₁.gpr .r3 := other _ (by decide)
    show bytesAt s'.mem (outp s₀) (outn s₀) = Spec.Sha3.squeezeFrom (rate s₀) (S₀ s₀) (pos₀ s₀) (outn s₀)
    rw [m, u₁.mem]
    refine List.ext_getElem (by rw [length_squeezeFrom hr0 hr200]; simp [bytesAt]) fun j h₁ _ => ?_
    have hj : j < outn s₀ := by simpa [bytesAt] using h₁
    rw [squeezeFrom_getElem hr0 hr200 _ hj]
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    exact hI.out j hj
  · rw [other _ (by decide), hx0, toNat_ofNat_lt (by omega_arith)]; exact hI.pos_le
  · show Spec.Sha3.squeezeFrom (rate s₀) (stateAt s'.mem (stp s₀)) (s'.gpr .r3).toNat d =
      Spec.Sha3.squeezeFrom (rate s₀) (S₀ s₀) (pos₀ s₀ + outn s₀) d
    rw [m, u₁.mem, hI.state, other _ (by decide), hx0, toNat_ofNat_lt (by have := hI.pos_le; omega_arith),
      squeezeFrom_iterF hr0 hr200, ← hI.hi]

/-! ## The whole function -/

theorem squeeze_eq : squeezeMain = .seq (.block setup)
    (.seq (.ite (.zero .d .r31) (.block []) (.loop squeezeBody (.nonzero .d .r31)))
      (.block (mov .r3 .r29 :: restore))) := rfl

/-- `squeeze` without its frame. -/
theorem correctMain {s₀ : State} (hp : SPre s₀) : WP isa squeezeMain s₀ (Post s₀) := by
  have hn := outn_lt s₀
  rw [squeeze_eq]
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ hI => ?_)
  refine WP.seq (WP.mono (Q := fun s => ∃ k pos, Inv s₀ (outn s₀) k pos s) ?_
    fun s₂ ⟨k, pos, hI₂⟩ => epilogue_ok hp hI₂)
  refine WP.ite (decide (outn s₀ = 0))
    (by show VG.PPC64LE.eval (.zero .d .r31) s₁ = _
        rw [eval_zero, hI.r31, Nat.sub_zero, ofNat_beq_zero (by omega_arith)])
    (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.block_nil ⟨0, pos₀ s₀, by rw [hb]; exact hI⟩
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.loop (M := isa) (fun n s => ∃ i k pos, n = outn s₀ - i ∧ i < outn s₀ ∧ Inv s₀ i k pos s)
      ?_ (outn s₀) s₁ ⟨0, 0, pos₀ s₀, by omega_arith, by omega_arith, hI⟩
    rintro n s ⟨i, k, pos, rfl, hi, hI⟩
    refine WP.mono (body_ok hp hI hi) fun s' ⟨i', k', pos', hii, hi', hI'⟩ => ?_
    have hz : isa.eval (.nonzero .d .r31) s' = some (decide (outn s₀ - i' ≠ 0)) := by
      show VG.PPC64LE.eval (.nonzero .d .r31) s' = _
      rw [eval_nonzero, hI'.r31, bne, ofNat_beq_zero (by omega_arith)]
      simp
    by_cases hl : outn s₀ - i' = 0
    · exact .inl ⟨by rw [hz]; simp [hl], k', pos', by rwa [show i' = outn s₀ by omega_arith] at hI'⟩
    · exact .inr ⟨by rw [hz]; simp [hl], _, by omega_arith, i', k', pos', rfl, by omega_arith, hI'⟩

end VG.Proof.Sha3.PPC64LE.Stream.Squeeze
