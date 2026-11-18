module

public import VerifiedGarbage.Proof.Sha3.Contract
public import VerifiedGarbage.Proof.Sha3.X86_64.Permute
import VerifiedGarbage.Proof.Sha3.Arith
public import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sha3.Contract
meta import VerifiedGarbage.Proof.Sha3.X86_64.Permute
meta import VerifiedGarbage.Proof.Sha3.Arith
meta import VerifiedGarbage.Proof.Sha3.Stream
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Word
meta import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Word

/-! ### `Sha3.X86_64.Stream.Squeeze`, which the modules that import this one used -/

section

/-!
# The SHA-3 sponge on x86-64: `squeeze`
-/

@[expose] public section

namespace VG.Proof.Sha3.X86_64.Stream.Squeeze

open VG VG.X86_64
open VG.Impl.Sha3.X86_64 (at_)
open VG.Impl.Sha3.X86_64.Stream (squeeze squeezeBody squeezeWord squeezeByte wordTest permuteAt save restore stByte)
open VG.Spec.Sha3 (stateAt keccakF bytesAt rates)
open VG.Proof.Sha3 (byteOf byteOf_stateAt iterF iterF_succ length_squeezeFrom squeezeFrom_getElem
  squeezeFrom_iterF)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev stp : Addr := s₀.gpr .rdi
abbrev rate : Nat := (s₀.gpr .rsi).toNat
abbrev pos₀ : Nat := (s₀.gpr .rdx).toNat
abbrev outp : Addr := s₀.gpr .rcx
abbrev outn : Nat := (s₀.gpr .r8).toNat
abbrev scrp : Addr := s₀.gpr .r9
abbrev SR : Region := ⟨stp s₀, 200⟩
abbrev OR : Region := ⟨outp s₀, outn s₀⟩
abbrev CR : Region := ⟨scrp s₀, 640⟩
abbrev RR : Region := ⟨s₀.gpr .rsp, 8⟩
/-- Where the call of `vg_keccak_f1600` stores its return address. -/
abbrev KR : Region := below (s₀.gpr .rsp) 8
/-- The initial state. -/
abbrev S₀ : Spec.Sha3.State := stateAt s₀.mem (stp s₀)

end

theorem saved_bound : ∀ p ∈ Impl.Sha3.X86_64.Stream.saved, 512 ≤ p.2 ∧ p.2 + 8 ≤ 560 := by decide

/-- The caller's callee-saved registers are saved in the scratch space. -/
abbrev Saved (s₀ : State) (m : Mem) : Prop := Spill.Saved m (scrp s₀) s₀.gpr Impl.Sha3.X86_64.Stream.saved

structure SPre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [SR s₀, OR s₀, CR s₀]
  st_o : (SR s₀).Disjoint (OR s₀)
  st_c : (SR s₀).Disjoint (CR s₀)
  o_c : (OR s₀).Disjoint (CR s₀)
  ret_st : (RR s₀).Disjoint (SR s₀)
  ret_o : (RR s₀).Disjoint (OR s₀)
  ret_c : (RR s₀).Disjoint (CR s₀)
  stk_st : (KR s₀).Disjoint (SR s₀)
  stk_o : (KR s₀).Disjoint (OR s₀)
  stk_c : (KR s₀).Disjoint (CR s₀)
  rate_mem : rate s₀ ∈ rates
  pos_le : pos₀ s₀ ≤ rate s₀

theorem pre_of {s₀ : State} (h : Proof.Sha3.squeezeX86_64.pre s₀) : SPre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

theorem SPre.rate_pos {s₀ : State} (hp : SPre s₀) : 0 < rate s₀ ∧ rate s₀ ≤ 200 := by
  have := hp.rate_mem
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at this
  omega_arith

theorem outn_lt (s₀ : State) : outn s₀ < 2 ^ 64 := (s₀.gpr .r8).isLt

theorem ret_stk (s₀ : State) : (RR s₀).Disjoint (KR s₀) := by
  intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega

/-- The saved registers lie in the scratch space, past the permutation's. -/
theorem slot_sub (s₀ : State) {p : Reg × Nat} (hp : p ∈ Impl.Sha3.X86_64.Stream.saved) :
    Region.Sub ⟨Spill.slot (scrp s₀) p.2, 8⟩ (CR s₀) := by
  have := saved_bound p hp; exact sub_offset (by omega_arith) (by omega_arith)

theorem slot_scr (s₀ : State) {p : Reg × Nat} (hp : p ∈ Impl.Sha3.X86_64.Stream.saved) :
    Region.Disjoint ⟨Spill.slot (scrp s₀) p.2, 8⟩ ⟨scrp s₀, 512⟩ := by
  have := saved_bound p hp; exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)

theorem Saved.frame {s₀ : State} {m m' : Mem} (h : Saved s₀ m) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ p ∈ Impl.Sha3.X86_64.Stream.saved, ∀ r ∈ rs, Region.Disjoint ⟨Spill.slot (scrp s₀) p.2, 8⟩ r) : Saved s₀ m' :=
  Spill.Saved.frame h hf hd

/-! ## Arithmetic -/

theorem sx1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide

/-! ## The prologue -/

/-! ## The loop invariant -/

/-- After `i` bytes of output, `k` permutations and `pos` bytes of the
current block: `pos₀ + i = rate * k + pos`. -/
structure Inv (s₀ : State) (i k pos : Nat) (s : State) : Prop where
  i_le : i ≤ outn s₀
  hi : pos₀ s₀ + i = rate s₀ * k + pos
  pos_le : pos ≤ rate s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rbx : s.gpr .rbx = stp s₀
  rbp : s.gpr .rbp = s₀.gpr .rsi
  r12 : s.gpr .r12 = BitVec.ofNat 64 pos
  r13 : s.gpr .r13 = outp s₀ + BitVec.ofNat 64 i
  r14 : s.gpr .r14 = BitVec.ofNat 64 (outn s₀ - i)
  r15 : s.gpr .r15 = scrp s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  frame : Frame [SR s₀, OR s₀, CR s₀, KR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem
  state : stateAt s.mem (stp s₀) = iterF k (S₀ s₀)
  out : ∀ j < i, s.mem (outp s₀ + BitVec.ofNat 64 j) =
    byteOf (iterF ((pos₀ s₀ + j) / rate s₀) (S₀ s₀)) ((pos₀ s₀ + j) % rate s₀)

theorem Inv.congr {s₀ : State} {i k pos : Nat} {s s' : State} (h : Inv s₀ i k pos s)
    (hg : ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Inv s₀ i k pos s' where
  i_le := h.i_le
  hi := h.hi
  pos_le := h.pos_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  rbx := by rw [hg _ (by simp)]; exact h.rbx
  rbp := by rw [hg _ (by simp)]; exact h.rbp
  r12 := by rw [hg _ (by simp)]; exact h.r12
  r13 := by rw [hg _ (by simp)]; exact h.r13
  r14 := by rw [hg _ (by simp)]; exact h.r14
  r15 := by rw [hg _ (by simp)]; exact h.r15
  rsp := by rw [hg _ (by simp)]; exact h.rsp
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved
  state := by rw [hm]; exact h.state
  out := by rw [hm]; exact h.out

theorem prologue_ok {s₀ : State} (hp : SPre s₀) :
    WP isa (.block (save .r9 ++ ([.mov .rbx (.reg .rdi), .mov .rbp (.reg .rsi), .mov .r12 (.reg .rdx),
      .mov .r13 (.reg .rcx), .mov .r14 (.reg .r8), .mov .r15 (.reg .r9), .alu .test .r14 (.reg .r14)] : List Instr))) s₀
      fun s => Inv s₀ 0 0 (pos₀ s₀) s ∧ s.zf = some (decide (outn s₀ = 0)) := by
  refine WP.block_append_iff.mpr (WP.mono (Spill.save_ok .r9 Impl.Sha3.X86_64.Stream.saved s₀ fun p hp' => ?_)
    fun s ⟨hg, hrd, hwr, hm₀⟩ => ?_)
  · have := saved_bound p hp'
    rw [hp.wr]; exact ⟨CR s₀, by simp, contains_offset (by omega_arith) (by omega_arith)⟩
  obtain hf : Frame [CR s₀] s₀.mem s.mem := hm₀ ▸ Spill.saveMem_frame_base _ _ _ _
    (fun p hp => by have := saved_bound p hp; omega_arith) (by decide)
  refine wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ =>
    wp_mov fun s₅ u₅ => wp_mov fun s₆ u₆ => wp_test fun s₇ g₇ m₇ rd₇ wr₇ z₇ => wp_nil ?_
  obtain hm : s₇.mem = s.mem := by rw [m₇, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain h14 : s₇.gpr .r14 = s₀.gpr .r8 := by
    rw [g₇, u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hg]
  refine ⟨⟨Nat.zero_le _, by simp, hp.pos_le, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by rw [hm]; exact hf.mono (by simp), by rw [hm, hm₀]; exact Spill.saveMem_saved _ _ _ _ (by decide), ?_,
    fun j hj => absurd hj (Nat.not_lt_zero _)⟩, ?_⟩
  · rw [rd₇, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hrd]
  · rw [wr₇, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hwr]
  · rw [g₇, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hg]
  · rw [g₇, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hg]
  · rw [g₇, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hg]; simp
  · rw [g₇, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hg]; simp
  · rw [h14]; simp
  · rw [g₇, u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hg]
  · rw [g₇, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hg]
  · rw [hm]
    exact VG.Proof.Sha3.stateAt_congr fun j hj => hf.bytes (R := SR s₀) (by simpa using hp.st_c) (by simp) hj
  · rw [z₇, ← g₇, h14, BitVec.and_self, beq_zero]

/-! ## One iteration -/

theorem permute_ok {s₀ : State} (hp : SPre s₀) {i k : Nat} {s : State} (hI : Inv s₀ i k (rate s₀) s) :
    WP isa (.seq (.block [.mov32 .r12 (.imm 0)]) permuteAt) s (Inv s₀ i (k + 1) 0) := by
  refine WP.seq (wp_mov32i fun s₁ u₁ => wp_nil ?_)
  obtain hsp : s₁.gpr .rsp = s₀.gpr .rsp := by rw [u₁.other _ (by decide), hI.rsp]
  obtain e200 : Region.Sub ⟨stp s₀, 200⟩ (SR s₀) := fun _ h => h
  obtain e512 : Region.Sub ⟨scrp s₀, 512⟩ (CR s₀) := sub_prefix' (by omega_arith)
  refine permuteAt_ok (st := stp s₀) (scr := scrp s₀) (by rw [u₁.other _ (by decide), hI.rbx])
    (by rw [u₁.other _ (by decide), hI.r15]) (hp.st_c.sub_right e512) (by rw [hsp]; exact hp.stk_st)
    (by rw [hsp]; exact hp.stk_c.sub_right e512) ?_ fun s' rd' wr' cs' hf hst => ?_
  · rw [u₁.wr, hI.wr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨SR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨CR s₀, by simp, 0, by simp, by simp⟩
  have cs : ∀ r ∈ calleeSaved, s'.gpr r = s₁.gpr r := cs'
  obtain hd : ∀ r ∈ [(⟨stp s₀, 200⟩ : Region), ⟨scrp s₀, 512⟩, below (s₁.gpr .rsp) 8], (OR s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.st_o.symm
    · exact hp.o_c.sub_right e512
    · rw [hsp]; exact hp.stk_o.symm
  refine ⟨hI.i_le, by rw [hI.hi, Nat.mul_succ]; rfl, Nat.zero_le _, rd'.trans (u₁.rd.trans hI.rd),
    wr'.trans (u₁.wr.trans hI.wr), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_⟩
  · rw [cs _ (by decide), u₁.other _ (by decide), hI.rbx]
  · rw [cs _ (by decide), u₁.other _ (by decide), hI.rbp]
  · rw [cs _ (by decide), u₁.gpr]; rfl
  · rw [cs _ (by decide), u₁.other _ (by decide), hI.r13]
  · rw [cs _ (by decide), u₁.other _ (by decide), hI.r14]
  · rw [cs _ (by decide), u₁.other _ (by decide), hI.r15]
  · rw [cs _ (by decide), hsp]
  · have hfs : Frame [SR s₀, OR s₀, CR s₀, KR s₀] s₁.mem s'.mem := by
      refine hf.sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨SR s₀, by simp, e200⟩
      · exact ⟨CR s₀, by simp, e512⟩
      · exact ⟨KR s₀, by simp, by rw [hsp]; exact fun _ h => h⟩
    rw [u₁.mem] at hfs
    exact hI.frame.trans hfs
  · refine Saved.frame (by rw [u₁.mem]; exact hI.saved) hf fun k hk r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.st_c.symm.sub_left (slot_sub s₀ hk)
    · exact slot_scr s₀ hk
    · rw [hsp]; exact hp.stk_c.symm.sub_left (slot_sub s₀ hk)
  · rw [hst, u₁.mem, hI.state, iterF_succ]
  · refine Eq.trans (hf.bytes (R := OR s₀) hd (Nat.le_of_lt (outn_lt s₀)) (by have := hI.i_le; omega_arith : j < outn s₀)) ?_
    rw [u₁.mem]; exact hI.out j hj

theorem store_ok {s₀ : State} (hp : SPre s₀) {i k pos : Nat} {s : State} (hI : Inv s₀ i k pos s)
    (hlt : pos < rate s₀) (hi : i < outn s₀) :
    WP isa (.block squeezeByte) s fun s' =>
      Inv s₀ (i + 1) k (pos + 1) s' ∧ s'.zf = some (decide (outn s₀ - (i + 1) = 0)) := by
  have ⟨hr0, hr200⟩ := hp.rate_pos
  obtain hn := outn_lt s₀
  unfold squeezeByte
  refine wp_movzx8 (a := stp s₀ + BitVec.ofNat 64 pos) (by simp [State.ea, stByte, hI.rbx, hI.r12])
    ⟨SR s₀, by simp [hI.rd, hI.wr, hp.rd, hp.wr], contains_offset (by omega_arith) (by omega_arith)⟩ fun s₁ u₁ => ?_
  refine wp_store8 (a := outp s₀ + BitVec.ofNat 64 i) (by simp [State.ea, u₁.other .r13 (by decide), hI.r13])
    (by rw [u₁.wr, hI.wr, hp.wr]; exact ⟨OR s₀, by simp, contains_offset (by omega_arith) (by omega_arith)⟩)
    fun s₂ g₂ m₂ rd₂ wr₂ => ?_
  refine wp_addi fun s₃ u₃ => wp_addi fun s₄ u₄ => wp_subi fun s₅ u₅ hz₅ => wp_nil ?_
  obtain g : ∀ r, r ≠ .rax → r ≠ .r13 → r ≠ .r12 → r ≠ .r14 → s₅.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₅.other r h4, u₄.other r h3, u₃.other r h2, g₂, u₁.other r h1]
  obtain hb : s.mem (stp s₀ + BitVec.ofNat 64 pos) = byteOf (iterF k (S₀ s₀)) pos := by
    rw [← hI.state, byteOf_stateAt _ _ (by omega_arith)]
  obtain hm : s₅.mem = s.mem.writeW (outp s₀ + BitVec.ofNat 64 i) (byteOf (iterF k (S₀ s₀)) pos) := by
    rw [u₅.mem, u₄.mem, u₃.mem, m₂, u₁.gpr, u₁.mem, BitVec.setWidth_setWidth_of_le _ (by omega_arith),
      BitVec.setWidth_eq, hb]
  obtain hfw : Frame [OR s₀] s.mem s₅.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_offset (by omega_arith) (by omega_arith))
  obtain h14 : s₅.gpr .r14 = BitVec.ofNat 64 (outn s₀ - (i + 1)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂, u₁.other _ (by decide), hI.r14, sx1,
      ofNat_pred (by omega_arith), Nat.sub_sub]
  refine ⟨⟨by omega_arith, by have := hI.hi; omega_arith, by omega_arith, ?_, ?_, ?_, ?_, ?_, ?_, h14, ?_, ?_,
    hI.frame.trans (hfw.mono (by simp)), ?_, ?_, fun j hj => ?_⟩, ?_⟩
  · rw [u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd, hI.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr, hI.wr]
  · rw [g .rbx (by decide) (by decide) (by decide) (by decide), hI.rbx]
  · rw [g .rbp (by decide) (by decide) (by decide) (by decide), hI.rbp]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂, u₁.other _ (by decide), hI.r12, sx1,
      ofNat_succ]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂, u₁.other _ (by decide), hI.r13, sx1,
      ofNat_succ, BitVec.add_assoc]
  · rw [g .r15 (by decide) (by decide) (by decide) (by decide), hI.r15]
  · rw [g .rsp (by decide) (by decide) (by decide) (by decide), hI.rsp]
  · refine hI.saved.frame hfw fun k hk r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact hp.o_c.symm.sub_left (slot_sub s₀ hk)
  · rw [VG.Proof.Sha3.stateAt_congr fun j hj => hfw.bytes (R := SR s₀) (by simpa using hp.st_o) (by simp) hj]
    exact hI.state
  · rw [hm]
    by_cases e : j = i
    · subst e
      obtain ⟨d, m⟩ := div_mod_eq (k := k) hr0 hlt
      rw [writeW8_self, hI.hi, d, m]
    · rw [writeW8_other _ _ (Offset.add_ofNat_ne _ (by omega_arith) (by omega_arith) e)]
      exact hI.out j (by omega_arith)
  · rw [hz₅, u₄.other _ (by decide), u₃.other _ (by decide), g₂, u₁.other _ (by decide), hI.r14, sx1,
      ofNat_pred (by omega_arith), beq_zero, toNat_ofNat_lt (by omega_arith), Nat.sub_sub]

theorem storeW_ok {s₀ : State} (hp : SPre s₀) {i k pos : Nat} {s : State} (hI : Inv s₀ i k pos s)
    (hlt : pos + 8 ≤ rate s₀) (hi : i + 8 ≤ outn s₀) :
    WP isa (.block squeezeWord) s fun s' =>
      Inv s₀ (i + 8) k (pos + 8) s' ∧ s'.zf = some (decide (outn s₀ - (i + 8) = 0)) := by
  have ⟨hr0, hr200⟩ := hp.rate_pos
  obtain hn := outn_lt s₀
  unfold squeezeWord
  refine wp_movm (a := stp s₀ + BitVec.ofNat 64 pos) (by simp [State.ea, stByte, hI.rbx, hI.r12])
    ⟨SR s₀, by simp [hI.rd, hI.wr, hp.rd, hp.wr], contains_offset (by omega_arith) (by omega_arith)⟩ fun s₁ u₁ => ?_
  refine wp_store (a := outp s₀ + BitVec.ofNat 64 i) (by simp [State.ea, u₁.other .r13 (by decide), hI.r13])
    (by rw [u₁.wr, hI.wr, hp.wr]; exact ⟨OR s₀, by simp, contains_offset (by omega_arith) (by omega_arith)⟩)
    fun s₂ g₂ m₂ rd₂ wr₂ => ?_
  refine wp_addi fun s₃ u₃ => wp_addi fun s₄ u₄ => wp_subi fun s₅ u₅ hz₅ => wp_nil ?_
  obtain g : ∀ r, r ≠ .rax → r ≠ .r13 → r ≠ .r12 → r ≠ .r14 → s₅.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₅.other r h4, u₄.other r h3, u₃.other r h2, g₂, u₁.other r h1]
  obtain hm : s₅.mem = s.mem.writeW (outp s₀ + BitVec.ofNat 64 i) (s.mem.readW (stp s₀ + BitVec.ofNat 64 pos) 64) := by
    rw [u₅.mem, u₄.mem, u₃.mem, m₂, u₁.gpr, u₁.mem]
  obtain hfw : Frame [OR s₀] s.mem s₅.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_offset (by omega_arith) (by omega_arith))
  obtain h14 : s₅.gpr .r14 = BitVec.ofNat 64 (outn s₀ - (i + 8)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂, u₁.other _ (by decide), hI.r14, sx8,
      sub_ofNat (by omega_arith), Nat.sub_sub]
  refine ⟨⟨by omega_arith, by have := hI.hi; omega_arith, by omega_arith, ?_, ?_, ?_, ?_, ?_, ?_, h14, ?_, ?_,
    hI.frame.trans (hfw.mono (by simp)), ?_, ?_, fun j hj => ?_⟩, ?_⟩
  · rw [u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd, hI.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr, hI.wr]
  · rw [g .rbx (by decide) (by decide) (by decide) (by decide), hI.rbx]
  · rw [g .rbp (by decide) (by decide) (by decide) (by decide), hI.rbp]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂, u₁.other _ (by decide), hI.r12, sx8,
      ← BitVec.ofNat_add]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂, u₁.other _ (by decide), hI.r13, sx8,
      BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [g .r15 (by decide) (by decide) (by decide) (by decide), hI.r15]
  · rw [g .rsp (by decide) (by decide) (by decide) (by decide), hI.rsp]
  · refine hI.saved.frame hfw fun k hk r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact hp.o_c.symm.sub_left (slot_sub s₀ hk)
  · rw [VG.Proof.Sha3.stateAt_congr fun j hj => hfw.bytes (R := SR s₀) (by simpa using hp.st_o) (by simp) hj]
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
        rw [Offset.sub_toNat' _ (by omega_arith) (by omega_arith), ite_eq_right_of_eq_false _ _ (eq_false e)]
        omega_arith)]
      exact hI.out j (by omega_arith)
  · rw [hz₅, u₄.other _ (by decide), u₃.other _ (by decide), g₂, u₁.other _ (by decide), hI.r14, sx8,
      sub_ofNat (by omega_arith), beq_zero, toNat_ofNat_lt (by omega_arith), Nat.sub_sub]

theorem body_ok {s₀ : State} (hp : SPre s₀) {i k pos : Nat} {s : State} (hI : Inv s₀ i k pos s)
    (hi : i < outn s₀) :
    WP isa squeezeBody s fun s' => ∃ i' k' pos', i < i' ∧ i' ≤ outn s₀ ∧ Inv s₀ i' k' pos' s' ∧
      s'.zf = some (decide (outn s₀ - i' = 0)) := by
  have ⟨hr0, _⟩ := hp.rate_pos
  obtain h8 := rate_mod8 hp.rate_mem
  unfold squeezeBody
  refine WP.seq (wp_cmp fun s₁ g₁ m₁ rd₁ wr₁ _ z₁ => wp_nil ?_)
  obtain hI₁ := hI.congr (fun r _ => by rw [g₁]) m₁ rd₁ wr₁
  obtain hz : s₁.zf = some (decide (pos = rate s₀)) := by
    rw [z₁, hI.r12, hI.rbp, sub_beq_zero (by have := hI.pos_le; have := (s₀.gpr .rsi).isLt; omega_arith)]
  refine WP.seq (WP.mono (Q := fun s => ∃ k' pos', Inv s₀ i k' pos' s ∧ pos' < rate s₀) ?_
    fun s₂ ⟨k', pos', hI₂, hlt⟩ => ?_)
  · refine WP.ite (decide (pos = rate s₀)) (by rw [show isa.eval .e s₁ = s₁.zf from rfl, hz])
      (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      subst hb
      exact WP.mono (permute_ok hp hI₁) fun s' h => ⟨k + 1, 0, h, hr0⟩
    · simp only [decide_eq_false_iff_not] at hb
      exact wp_nil ⟨k, pos, hI₁, by have := hI.pos_le; omega_arith⟩
  -- a lane or a byte
  refine WP.seq (WP.mono (wordTest_ok hI₂.r12 hI₂.r14 (by have := outn_lt s₀; omega_arith))
    fun s₃ ⟨g₃, m₃, rd₃, wr₃, b, z₃, hb₃⟩ => ?_)
  obtain hI₃ := hI₂.congr (fun r hr => g₃ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) m₃ rd₃ wr₃
  refine WP.ite b (by rw [show isa.eval .e s₃ = s₃.zf from rfl, z₃]) (fun hb => ?_) (fun _ => ?_)
  · obtain ⟨m8, l8⟩ := hb₃ hb
    exact WP.mono (storeW_ok hp hI₃ (by omega_arith) (by omega_arith))
      fun s' ⟨h, hz⟩ => ⟨i + 8, k', pos' + 8, by omega_arith, by omega_arith, h, hz⟩
  · exact WP.mono (store_ok hp hI₃ hlt hi) fun s' ⟨h, hz⟩ => ⟨i + 1, k', pos' + 1, by omega_arith, by omega_arith, h, hz⟩

/-! ## The epilogue -/

theorem epilogue_ok {s₀ : State} (hp : SPre s₀) {k pos : Nat} {s : State} (hI : Inv s₀ (outn s₀) k pos s) :
    WP isa (.block (.mov .rax (.reg .r12) :: restore)) s fun s' =>
      gprPreserved s₀ s' ∧ Proof.Sha3.squeezeX86_64.post s₀ s' := by
  have ⟨hr0, hr200⟩ := hp.rate_pos
  refine wp_mov fun s₁ u₁ => ?_
  obtain hI₁ : Inv s₀ (outn s₀) k pos s₁ := hI.congr (fun r hr => u₁.other r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) u₁.mem u₁.rd u₁.wr
  obtain hax : s₁.gpr .rax = BitVec.ofNat 64 pos := by rw [u₁.gpr, hI.r12]
  refine WP.mono (Spill.restore_ok .r15 Impl.Sha3.X86_64.Stream.saved s₀.gpr s₁ (by decide) (fun p hp' => ?_)
    (by rw [hI₁.r15]; exact hI₁.saved)) fun s' ⟨h₁, h₂, m, _⟩ => ?_
  · have := saved_bound p hp'
    rw [hI₁.r15]
    exact ⟨CR s₀, by simp [hI₁.rd, hI₁.wr, hp.rd, hp.wr], contains_offset (by omega_arith) (by omega_arith)⟩
  · have ax : s'.gpr .rax = s₁.gpr .rax := h₂ _ (by decide)
    have hpos : pos ≤ rate s₀ := hI.pos_le
    obtain hst : stateAt s'.mem (stp s₀) = iterF k (S₀ s₀) := by rw [m]; exact hI₁.state
    obtain hrax : (s'.gpr .rax).toNat = pos := by rw [ax, hax, toNat_ofNat_lt (by omega_arith)]
    refine ⟨⟨Spill.calleeSaved_ok h₁ h₂ (by decide) hI₁.rsp, ?_⟩, ?_, by rw [hrax]; exact hpos,
      fun d => ?_⟩
    · rw [m]
      exact hI₁.frame.readW (Region.contains_self _ _)
        (by simpa using ⟨hp.ret_st, hp.ret_o, hp.ret_c, ret_stk s₀⟩) (by decide)
    · show bytesAt s'.mem (outp s₀) (outn s₀) = Spec.Sha3.squeezeFrom (rate s₀) (S₀ s₀) (pos₀ s₀) (outn s₀)
      rw [m]
      refine List.ext_getElem (by rw [length_squeezeFrom hr0 hr200]; simp [bytesAt]) fun j h₁ _ => ?_
      obtain hj : j < outn s₀ := by simpa [bytesAt] using h₁
      rw [squeezeFrom_getElem hr0 hr200 _ hj]
      simp only [bytesAt, List.getElem_map, List.getElem_range]
      exact hI₁.out j hj
    · show Spec.Sha3.squeezeFrom (rate s₀) (stateAt s'.mem (stp s₀)) (s'.gpr .rax).toNat d =
        Spec.Sha3.squeezeFrom (rate s₀) (S₀ s₀) (pos₀ s₀ + outn s₀) d
      rw [hst, hrax, squeezeFrom_iterF hr0 hr200, ← hI.hi]

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : SPre s₀) :
    WP isa squeeze s₀ fun s' => gprPreserved s₀ s' ∧ Proof.Sha3.squeezeX86_64.post s₀ s' := by
  unfold squeeze
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨hI, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun s => ∃ k pos, Inv s₀ (outn s₀) k pos s) ?_
    fun s₂ ⟨k, pos, hI₂⟩ => epilogue_ok hp hI₂)
  refine WP.ite (decide (outn s₀ = 0)) (by rw [show isa.eval .e s₁ = s₁.zf from rfl, hz])
    (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact wp_nil ⟨0, pos₀ s₀, by rw [hb]; exact hI⟩
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.loop (M := isa) (fun n s => ∃ i k pos, n = outn s₀ - i ∧ i < outn s₀ ∧ Inv s₀ i k pos s) ?_
      (outn s₀) s₁ ⟨0, 0, pos₀ s₀, by omega_arith, by omega_arith, hI⟩
    rintro n s ⟨i, k, pos, rfl, hi, hI⟩
    refine WP.mono (body_ok hp hI hi) fun s' ⟨i', k', pos', hii, hi', hI', hz'⟩ => ?_
    by_cases hl : outn s₀ - i' = 0
    · exact .inl ⟨by simp [eval, hz', hl], k', pos', by rwa [show i' = outn s₀ by omega_arith] at hI'⟩
    · exact .inr ⟨by simp [eval, hz', hl], _, by omega_arith, i', k', pos', rfl, by omega_arith, hI'⟩

/-! ## Constant time -/

/-- The initial taint: the arguments and `rsp` are public, and `rdi`, `rcx`
and `r9` point at the writable regions (of which `out` has unknown length). -/
def τ₀ : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], flags := false, lens := [200, 0, 640],
    bases := [(.rdi, 0, 0), (.rcx, 1, 0), (.r9, 2, 0)] }

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Sha3.squeezeX86_64.pre s₁)
    (h₂ : Proof.Sha3.squeezeX86_64.pre s₂) (hpub : Proof.Sha3.squeezeX86_64.pub s₁ s₂) :
    X86_64.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := hpub
  obtain wf : ∀ s, Proof.Sha3.squeezeX86_64.pre s → X86_64.Taint.Wf τ₀ s := by
    intro s hs
    obtain ⟨-, hw, d1, d2, d3, -⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, τ₀], by simp [hw, d1, d2, d3],
      by simpa [hw] using (Nat.le_of_lt (s.gpr .r8).isLt)⟩, fun p hp => ?_⟩
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_,
    X86_64.Taint.noLo, X86_64.Taint.noXr⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption
  · rw [h₁.2.1, h₂.2.1, p1, p4, p5, p6]
  · intro sl h; simp [τ₀] at h
  · intro sl h; simp [τ₀] at h

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 72 | .rcx => 0x2000 | .r8 => 16 | .r9 => 0x3000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 200⟩, ⟨0x2000, 16⟩, ⟨0x3000, 640⟩]

theorem squeeze_correct (s : State) (hs : Proof.Sha3.squeezeX86_64.pre s) :
    ∃ t s', Exec isa squeeze s t s' ∧ abiPreserved s s' ∧ Proof.Sha3.squeezeX86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct (pre_of hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩

theorem squeeze_ct : ConstantTime isa Proof.Sha3.squeezeX86_64.pre Proof.Sha3.squeezeX86_64.pub
    squeeze := by
  exact VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp)
    (by taint_decide_weak VG.Proof.Sha3.X86_64.dropRC)

end VG.Proof.Sha3.X86_64.Stream.Squeeze

end

end

/-! ### `Sha3.X86_64.Stream.Absorb`, which the modules that import this one used -/

section

/-!
# The SHA-3 sponge on x86-64: `absorb`
-/

@[expose] public section

namespace VG.Proof.Sha3.X86_64.Stream.Absorb

open VG VG.X86_64 VG.Impl.Sha3.X86_64.Stream
open VG.Impl.Sha3.X86_64 (at_)
open VG.Proof.Sha3.X86_64 (Upd wp_mov wp_movm wp_movzx8 wp_store8 wp_store wp_xor wp_xorm wp_addi wp_subi
  wp_cmp wp_test wp_mov32i wp_nil ea_at
  permuteAt_ok wordTest_ok rate_mod8 sx8 bytesAt_add stateAt_write_lane)
open VG.Proof.Sha3 (Rep rep_snoc rep_append xorByte xorAt xorAt_single stateAt_xorByte)
open VG.Spec.Sha3 (stateAt keccakF bytesAt rates)

/-! ## Arithmetic -/

theorem sx1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .rdi
abbrev rt : Nat := (s₀.gpr .rsi).toNat
abbrev pos : Nat := (s₀.gpr .rdx).toNat
abbrev dp : Addr := s₀.gpr .rcx
abbrev len : Nat := (s₀.gpr .r8).toNat
abbrev scr : Addr := s₀.gpr .r9
abbrev stR : Region := ⟨st s₀, 200⟩
abbrev dR : Region := ⟨dp s₀, len s₀⟩
abbrev scR : Region := ⟨scr s₀, 640⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
/-- Where the call of `vg_keccak_f1600` stores its return address. -/
abbrev stkR : Region := below (s₀.gpr .rsp) 8
/-- The first `c` bytes of data. -/
abbrev D (c : Nat) : List Byte := bytesAt s₀.mem (dp s₀) c

/-- The caller's callee-saved registers are saved in the scratch space. -/
abbrev Saved (m : Mem) : Prop := Spill.Saved m (scr s₀) s₀.gpr saved

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
  ret_st : (retR s₀).Disjoint (stR s₀)
  ret_scr : (retR s₀).Disjoint (scR s₀)
  stk_st : (stkR s₀).Disjoint (stR s₀)
  stk_d : (stkR s₀).Disjoint (dR s₀)
  stk_scr : (stkR s₀).Disjoint (scR s₀)
  rate : rt s₀ ∈ rates
  pos_lt : pos s₀ < rt s₀

theorem pre_of {s₀ : State} (h : Proof.Sha3.absorbX86_64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

theorem Pre.rt_pos {s₀ : State} (hp : Pre s₀) : 0 < rt s₀ ∧ rt s₀ ≤ 168 := by
  have h := hp.rate
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h
  omega_arith

theorem ret_stk (s₀ : State) : (retR s₀).Disjoint (stkR s₀) := by
  intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega

theorem len_lt (s₀ : State) : len s₀ < 2 ^ 64 := (s₀.gpr .r8).isLt

theorem rsi_eq (s₀ : State) : s₀.gpr .rsi = BitVec.ofNat 64 (rt s₀) := by simp [rt]

theorem saved_bound : ∀ p ∈ saved, 512 ≤ p.2 ∧ p.2 + 8 ≤ 560 := by decide

/-- Writes to the state, the first 512 bytes of scratch and below the stack
keep the saved registers. -/
theorem Saved.frame {s₀ : State} (hp : Pre s₀) {m m' : Mem} (h : Saved s₀ m)
    (hf : Frame [stR s₀, ⟨scr s₀, 512⟩, stkR s₀] m m') : Saved s₀ m' :=
  Spill.Saved.frame h hf fun p hp' r hr => by
    have := saved_bound p hp'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.st_scr.symm.sub_left (sub_offset (by omega_arith) (by omega_arith))
    · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
    · exact hp.stk_scr.symm.sub_left (sub_offset (by omega_arith) (by omega_arith))

/-! ## Invariants -/

/-- What holds throughout, after consuming `c` bytes of data. -/
structure Common (s₀ : State) (c : Nat) (s : State) : Prop where
  c_le : c ≤ len s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rbx : s.gpr .rbx = st s₀
  r15 : s.gpr .r15 = scr s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbp : s.gpr .rbp = s₀.gpr .rsi
  r13 : s.gpr .r13 = dp s₀ + BitVec.ofNat 64 c
  r14 : s.gpr .r14 = BitVec.ofNat 64 (len s₀ - c)
  frame : Frame [stR s₀, scR s₀, stkR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem

/-- The loop invariant: the state represents the message followed by the
first `c` bytes of data. -/
structure Inv (s₀ : State) (c : Nat) (s : State) : Prop extends Common s₀ c s where
  r12 : s.gpr .r12 = BitVec.ofNat 64 ((pos s₀ + c) % rt s₀)
  repr : ∀ msg, Msg s₀ msg → stateAt s.mem (st s₀) = Rep (rt s₀) (msg ++ D s₀ c)

theorem Common.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : Common s₀ c s)
    (hg : ∀ r ∈ [Reg.rbx, .r15, .rsp, .rbp, .r13, .r14], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Common s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  rbx := by rw [hg _ (by simp)]; exact h.rbx
  r15 := by rw [hg _ (by simp)]; exact h.r15
  rsp := by rw [hg _ (by simp)]; exact h.rsp
  rbp := by rw [hg _ (by simp)]; exact h.rbp
  r13 := by rw [hg _ (by simp)]; exact h.r13
  r14 := by rw [hg _ (by simp)]; exact h.r14
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

/-- A call of the permutation keeps what holds throughout. -/
theorem Common.after_call {s₀ : State} (hp : Pre s₀) {c : Nat} {s s' : State} (h : Common s₀ c s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hcs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r)
    (hf : Frame [stR s₀, ⟨scr s₀, 512⟩, stkR s₀] s.mem s'.mem) : Common s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  rbx := by rw [hcs _ (by decide)]; exact h.rbx
  r15 := by rw [hcs _ (by decide)]; exact h.r15
  rsp := by rw [hcs _ (by decide)]; exact h.rsp
  rbp := by rw [hcs _ (by decide)]; exact h.rbp
  r13 := by rw [hcs _ (by decide)]; exact h.r13
  r14 := by rw [hcs _ (by decide)]; exact h.r14
  frame := h.frame.trans (hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀, by simp, fun _ h => h⟩
    · exact ⟨scR s₀, by simp, Region.sub_prefix (by omega_arith)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩)
  saved := h.saved.frame hp hf

/-- The data is unchanged. -/
theorem Common.data {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (h : Common s₀ c s) {i : Nat}
    (hi : i < len s₀) : s.mem (dp s₀ + BitVec.ofNat 64 i) = s₀.mem (dp s₀ + BitVec.ofNat 64 i) :=
  h.frame.bytes (R := dR s₀) (by simpa using ⟨hp.d_st, hp.d_scr, hp.stk_d.symm⟩) (Nat.le_of_lt (len_lt s₀)) hi

/-! ## The prologue -/

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (save .r9 ++ ([.mov .rbx (.reg .rdi), .mov .rbp (.reg .rsi), .mov .r12 (.reg .rdx),
      .mov .r13 (.reg .rcx), .mov .r14 (.reg .r8), .mov .r15 (.reg .r9), .alu .test .r14 (.reg .r14)] : List Instr)))
      s₀ fun s => Inv s₀ 0 s ∧ s.zf = some (decide (len s₀ = 0)) := by
  rw [WP.block_append_iff]
  refine WP.mono (Spill.save_ok .r9 saved s₀ fun p hp' => ?_) fun s₁ ⟨g₁, rd₁, wr₁, m₁⟩ => ?_
  · have := saved_bound p hp'
    exact ⟨scR s₀, by simp [hp.wr], contains_offset (by omega_arith) (by omega_arith)⟩
  obtain f₁ : Frame [scR s₀] s₀.mem s₁.mem := m₁ ▸ Spill.saveMem_frame_base _ _ _ _
    (fun p hp => by have := saved_bound p hp; omega_arith) (by decide)
  obtain v₁ : Saved s₀ s₁.mem := m₁ ▸ Spill.saveMem_saved _ _ _ _ (by decide)
  refine wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ =>
    wp_mov fun s₆ u₆ => wp_mov fun s₇ u₇ => wp_test fun s₈ g₈ m₈ rd₈ wr₈ z₈ => wp_nil ?_
  obtain hm : s₈.mem = s₁.mem := by rw [m₈, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  obtain hrd : s₈.rd = s₀.rd := by rw [rd₈, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]
  obtain hwr : s₈.wr = s₀.wr := by rw [wr₈, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]
  obtain hf : Frame [stR s₀, scR s₀, stkR s₀] s₀.mem s₁.mem := f₁.mono (by simp)
  obtain h14 : s₈.gpr .r14 = s₀.gpr .r8 := by
    rw [g₈, u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), g₁]
  obtain hl := len_lt s₀
  refine ⟨⟨⟨Nat.zero_le _, hrd, hwr, ?_, ?_, ?_, ?_, ?_, ?_, by rw [hm]; exact hf,
    by rw [hm]; exact v₁⟩, ?_, fun msg ⟨hs, _⟩ => ?_⟩, ?_⟩
  · rw [g₈, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, g₁]
  · rw [g₈, u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), g₁]
  · rw [g₈, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g₁]
  · rw [g₈, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), g₁]
  · rw [g₈, u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), g₁]
    simp
  · rw [h14, Nat.sub_zero]; simp [len]
  · rw [g₈, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), g₁, Nat.add_zero, Nat.mod_eq_of_lt hp.pos_lt]
    simp [pos]
  · rw [hm, show D s₀ 0 = [] by simp [bytesAt], List.append_nil, ← hs]
    exact Proof.Sha3.stateAt_congr fun i hi =>
      f₁.bytes (R := stR s₀) (by simpa using hp.st_scr)
        (by simp) hi
  · rw [z₈, ← congrFun g₈ .r14, h14, BitVec.and_self]
    rw [show s₀.gpr .r8 = BitVec.ofNat 64 (len s₀) by simp [len], ofNat_beq_zero hl]

/-! ## One iteration -/

/-- The state after absorbing `c` bytes, then the byte at the position `j`
XORed in. -/
theorem body_block {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c < len s₀) {s : State}
    (hI : Inv s₀ c s) :
    WP isa (.block absorbByte) s fun s' =>
      Common s₀ (c + 1) s' ∧ s'.gpr .r12 = BitVec.ofNat 64 ((pos s₀ + c) % rt s₀ + 1) ∧
      s'.zf = some (decide ((pos s₀ + c) % rt s₀ + 1 = rt s₀)) ∧
      stateAt s'.mem (st s₀) = xorByte (stateAt s.mem (st s₀)) ((pos s₀ + c) % rt s₀)
        (s₀.mem (dp s₀ + BitVec.ofNat 64 c)) := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  obtain hl := len_lt s₀
  obtain hj : (pos s₀ + c) % rt s₀ < rt s₀ := Nat.mod_lt _ hr₀
  generalize hjd : (pos s₀ + c) % rt s₀ = j at hj ⊢
  obtain hr12 : s.gpr .r12 = BitVec.ofNat 64 j := by rw [hI.r12, hjd]
  have hrbx := hI.rbx
  obtain hin : InRegions (s.rd ++ s.wr) (dp s₀ + BitVec.ofNat 64 c) 1 :=
    ⟨dR s₀, by simp [hI.rd, hp.rd], contains_offset (by omega_arith) (by omega_arith)⟩
  obtain hst : ∀ t : State, t.gpr .rbx = st s₀ → t.gpr .r12 = BitVec.ofNat 64 j →
      t.ea stByte = st s₀ + BitVec.ofNat 64 j := fun t h1 h2 => by
    simp [State.ea, stByte, h1, h2]
  obtain hsin : ∀ rs : List Region, stR s₀ ∈ rs → InRegions rs (st s₀ + BitVec.ofNat 64 j) 1 :=
    fun rs h => ⟨stR s₀, h, contains_offset (by omega_arith) (by omega_arith)⟩
  unfold absorbByte
  refine wp_movzx8 (d := .rax) (a := dp s₀ + BitVec.ofNat 64 c) (by simp [State.ea, hI.r13]) hin
    fun s₁ u₁ => ?_
  refine wp_movzx8 (d := .rcx) (a := st s₀ + BitVec.ofNat 64 j)
    (hst _ (by rw [u₁.other _ (by decide), hrbx]) (by rw [u₁.other _ (by decide), hr12]))
    (hsin _ (by simp [u₁.rd, u₁.wr, hI.rd, hI.wr, hp.wr])) fun s₂ u₂ => ?_
  refine wp_xor fun s₃ u₃ => ?_
  refine wp_store8 (r := .rax) (a := st s₀ + BitVec.ofNat 64 j)
    (hst _ (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hrbx])
      (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hr12]))
    (hsin _ (by simp [u₃.wr, u₂.wr, u₁.wr, hI.wr, hp.wr])) fun s₄ g₄ m₄ rd₄ wr₄ => ?_
  refine wp_addi fun s₅ u₅ => wp_addi fun s₆ u₆ => wp_subi fun s₇ u₇ _ =>
    wp_cmp fun s₈ g₈ m₈ rd₈ wr₈ _ z₈ => wp_nil ?_
  -- The byte stored.
  obtain hv : (s₃.gpr .rax).setWidth 8 =
      s₀.mem (dp s₀ + BitVec.ofNat 64 c) ^^^ s.mem (st s₀ + BitVec.ofNat 64 j) := by
    rw [u₃.gpr, u₂.other _ (by decide), u₂.gpr, u₁.gpr, u₁.mem, xor_setWidth, hI.data hp hc]
  obtain hm₈ : s₈.mem = s.mem.writeW (st s₀ + BitVec.ofNat 64 j)
      (s₀.mem (dp s₀ + BitVec.ofNat 64 c) ^^^ s.mem (st s₀ + BitVec.ofNat 64 j)) := by
    rw [m₈, u₇.mem, u₆.mem, u₅.mem, m₄, hv, u₃.mem, u₂.mem, u₁.mem]
  obtain hf : Frame [stR s₀] s.mem s₈.mem := by
    rw [hm₈]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_offset (by omega_arith) (by omega_arith))
  obtain g : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r13 → r ≠ .r12 → r ≠ .r14 → s₈.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by
      rw [g₈, u₇.other r h5, u₆.other r h4, u₅.other r h3, g₄, u₃.other r h1, u₂.other r h2,
        u₁.other r h1]
  obtain h12 : s₈.gpr .r12 = BitVec.ofNat 64 (j + 1) := by
    rw [g₈, u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), g₄, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hr12, sx1, ofNat_succ]
  refine ⟨⟨by omega_arith, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, h12, ?_, ?_⟩
  · rw [rd₈, u₇.rd, u₆.rd, u₅.rd, rd₄, u₃.rd, u₂.rd, u₁.rd, hI.rd]
  · rw [wr₈, u₇.wr, u₆.wr, u₅.wr, wr₄, u₃.wr, u₂.wr, u₁.wr, hI.wr]
  · rw [g .rbx (by decide) (by decide) (by decide) (by decide) (by decide), hrbx]
  · rw [g .r15 (by decide) (by decide) (by decide) (by decide) (by decide), hI.r15]
  · rw [g .rsp (by decide) (by decide) (by decide) (by decide) (by decide), hI.rsp]
  · rw [g .rbp (by decide) (by decide) (by decide) (by decide) (by decide), hI.rbp]
  · rw [g₈, u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, g₄, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hI.r13, sx1, ofNat_succ, BitVec.add_assoc]
  · rw [g₈, u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), g₄, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hI.r14, sx1, ofNat_pred (by omega_arith), Nat.sub_sub]
  · exact hI.frame.trans (hf.mono (by simp))
  · exact hI.saved.frame hp (hf.mono (by simp))
  · rw [z₈, ← congrFun g₈ .r12, ← congrFun g₈ .rbp, h12, g .rbp (by decide) (by decide) (by decide) (by decide) (by decide), hI.rbp, rsi_eq,
      sub_beq (by omega_arith) (by omega_arith)]
  · refine stateAt_xorByte (by omega_arith) ?_ fun i hi hij => ?_
    · rw [hm₈, writeW8_apply, ite_eq_left_of_eq_true _ _ (eq_true rfl), BitVec.xor_comm]
    · rw [hm₈, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (VG.Proof.Sha3.ne_of_lt200 hi (by omega_arith) hij))]

/-- The block of the body: the lane of data at `c` XORed into the lane at
position `j`. -/
theorem body_word {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c + 8 ≤ len s₀) {s : State}
    (hI : Inv s₀ c s) (hj8 : (pos s₀ + c) % rt s₀ % 8 = 0) :
    WP isa (.block absorbWord) s fun s' =>
      Common s₀ (c + 8) s' ∧ s'.gpr .r12 = BitVec.ofNat 64 ((pos s₀ + c) % rt s₀ + 8) ∧
      s'.zf = some (decide ((pos s₀ + c) % rt s₀ + 8 = rt s₀)) ∧
      stateAt s'.mem (st s₀) = xorAt (stateAt s.mem (st s₀)) ((pos s₀ + c) % rt s₀)
        (bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) 8) := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  obtain hl := len_lt s₀
  obtain h8 := rate_mod8 hp.rate
  obtain hj : (pos s₀ + c) % rt s₀ < rt s₀ := Nat.mod_lt _ hr₀
  generalize hjd : (pos s₀ + c) % rt s₀ = j at hj hj8 ⊢
  obtain hj' : j + 8 ≤ rt s₀ := by omega_arith
  obtain hr12 : s.gpr .r12 = BitVec.ofNat 64 j := by rw [hI.r12, hjd]
  have hrbx := hI.rbx
  obtain hst : ∀ t : State, t.gpr .rbx = st s₀ → t.gpr .r12 = BitVec.ofNat 64 j →
      t.ea stByte = st s₀ + BitVec.ofNat 64 j := fun t h1 h2 => by
    simp [State.ea, stByte, h1, h2]
  obtain hsin : ∀ rs : List Region, stR s₀ ∈ rs → InRegions rs (st s₀ + BitVec.ofNat 64 j) 8 :=
    fun rs h => ⟨stR s₀, h, contains_offset (by omega_arith) (by omega_arith)⟩
  unfold absorbWord
  refine wp_movm (d := .rax) (a := dp s₀ + BitVec.ofNat 64 c) (by simp [State.ea, hI.r13])
    ⟨dR s₀, by simp [hI.rd, hp.rd], contains_offset (by omega_arith) (by omega_arith)⟩ fun s₁ u₁ => ?_
  refine wp_xorm (a := st s₀ + BitVec.ofNat 64 j)
    (hst _ (by rw [u₁.other _ (by decide), hrbx]) (by rw [u₁.other _ (by decide), hr12]))
    (hsin _ (by simp [u₁.rd, u₁.wr, hI.rd, hI.wr, hp.wr])) fun s₂ u₂ => ?_
  refine wp_store (r := .rax) (a := st s₀ + BitVec.ofNat 64 j)
    (hst _ (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hrbx])
      (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hr12]))
    (hsin _ (by simp [u₂.wr, u₁.wr, hI.wr, hp.wr])) fun s₃ g₃ m₃ rd₃ wr₃ => ?_
  refine wp_addi fun s₄ u₄ => wp_addi fun s₅ u₅ => wp_subi fun s₆ u₆ _ =>
    wp_cmp fun s₇ g₇ m₇ rd₇ wr₇ _ z₇ => wp_nil ?_
  obtain hv : s₂.gpr .rax = s.mem.readW (dp s₀ + BitVec.ofNat 64 c) 64 ^^^
      s.mem.readW (st s₀ + BitVec.ofNat 64 j) 64 := by
    rw [u₂.gpr, u₁.gpr, u₁.mem]
  obtain hm₇ : s₇.mem = s.mem.writeW (st s₀ + BitVec.ofNat 64 j) (s₂.gpr .rax) := by
    rw [m₇, u₆.mem, u₅.mem, u₄.mem, m₃, u₂.mem, u₁.mem]
  obtain hf : Frame [stR s₀] s.mem s₇.mem := by
    rw [hm₇]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_offset (by omega_arith) (by omega_arith))
  obtain g : ∀ r, r ≠ .rax → r ≠ .r13 → r ≠ .r12 → r ≠ .r14 → s₇.gpr r = s.gpr r :=
    fun r h1 h3 h4 h5 => by
      rw [g₇, u₆.other r h5, u₅.other r h4, u₄.other r h3, g₃, u₂.other r h1, u₁.other r h1]
  obtain h12 : s₇.gpr .r12 = BitVec.ofNat 64 (j + 8) := by
    rw [g₇, u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), g₃, u₂.other _ (by decide),
      u₁.other _ (by decide), hr12, sx8, ← BitVec.ofNat_add]
  refine ⟨⟨by omega_arith, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, h12, ?_, ?_⟩
  · rw [rd₇, u₆.rd, u₅.rd, u₄.rd, rd₃, u₂.rd, u₁.rd, hI.rd]
  · rw [wr₇, u₆.wr, u₅.wr, u₄.wr, wr₃, u₂.wr, u₁.wr, hI.wr]
  · rw [g .rbx (by decide) (by decide) (by decide) (by decide), hrbx]
  · rw [g .r15 (by decide) (by decide) (by decide) (by decide), hI.r15]
  · rw [g .rsp (by decide) (by decide) (by decide) (by decide), hI.rsp]
  · rw [g .rbp (by decide) (by decide) (by decide) (by decide), hI.rbp]
  · rw [g₇, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, g₃, u₂.other _ (by decide),
      u₁.other _ (by decide), hI.r13, sx8, BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [g₇, u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), g₃, u₂.other _ (by decide),
      u₁.other _ (by decide), hI.r14, sx8, sub_ofNat (by omega_arith), Nat.sub_sub]
  · exact hI.frame.trans (hf.mono (by simp))
  · exact hI.saved.frame hp (hf.mono (by simp))
  · rw [z₇, ← congrFun g₇ .r12, ← congrFun g₇ .rbp, h12, g .rbp (by decide) (by decide) (by decide) (by decide),
      hI.rbp, rsi_eq, sub_beq (by omega_arith) (by omega_arith)]
  · rw [hm₇]
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
  r12 : s'.gpr .r12 = BitVec.ofNat 64 ((pos s₀ + c) % rt s₀ + n)
  z : s'.zf = some (decide ((pos s₀ + c) % rt s₀ + n = rt s₀))
  st : stateAt s'.mem (st s₀) = xorAt (stateAt s.mem (st s₀)) ((pos s₀ + c) % rt s₀)
    (bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) n)

/-- The permutation if the block is complete. -/
theorem after_ok {s₀ : State} (hp : Pre s₀) {c n : Nat} (hn : 0 < n)
    (hfit : (pos s₀ + c) % rt s₀ + n ≤ rt s₀) {s s₁ : State} (hI : Inv s₀ c s) (h : After s₀ s c n s₁) :
    WP isa (.ite .e (.seq (.block [.mov32 .r12 (.imm 0)]) permuteAt) (.block [])) s₁
      (Inv s₀ (c + n)) := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  have hC := h.common
  obtain hlen : ∀ msg, Msg s₀ msg → (msg ++ D s₀ c).length % rt s₀ = (pos s₀ + c) % rt s₀ :=
    fun msg ⟨_, hpm⟩ => by rw [List.length_append, bytesAt_length, hpm, Nat.mod_add_mod]
  obtain hrep : ∀ msg, Msg s₀ msg → Rep (rt s₀) (msg ++ D s₀ (c + n)) =
      if (pos s₀ + c) % rt s₀ + n = rt s₀ then keccakF (stateAt s₁.mem (st s₀))
      else stateAt s₁.mem (st s₀) := fun msg hm => by
    rw [D, bytesAt_add, ← List.append_assoc, rep_append hr₀ (by omega_arith) _ _
      (by rw [bytesAt_length]; exact hn) (by rw [bytesAt_length, hlen msg hm]; exact hfit),
      hlen msg hm, bytesAt_length, h.st, hI.repr msg hm]
  obtain hpc : (pos s₀ + (c + n)) % rt s₀ = if (pos s₀ + c) % rt s₀ + n = rt s₀ then 0
      else (pos s₀ + c) % rt s₀ + n := by
    obtain e := Nat.div_add_mod (pos s₀ + c) (rt s₀)
    rw [show pos s₀ + (c + n) = (pos s₀ + c) + n by omega_arith]
    generalize (pos s₀ + c) % rt s₀ = j at e hfit ⊢
    generalize (pos s₀ + c) / rt s₀ = q at e
    rw [← e]
    split
    · rw [Nat.add_assoc, ‹j + n = rt s₀›, ← Nat.mul_succ, Nat.mul_mod_right]
    · rw [Nat.add_assoc, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega_arith)]
  refine WP.ite (decide ((pos s₀ + c) % rt s₀ + n = rt s₀)) h.z (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine WP.seq (wp_mov32i fun s₂ u₂ => wp_nil ?_)
    obtain hC₂ := hC.of_gpr (fun r hr => u₂.other r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) u₂.mem u₂.rd u₂.wr
    have hsp := hC₂.rsp
    refine permuteAt_ok hC₂.rbx hC₂.r15 (hp.st_scr.sub_right (Region.sub_prefix (by omega_arith)))
      (by rw [hsp]; exact hp.stk_st) (by rw [hsp]; exact hp.stk_scr.sub_right (Region.sub_prefix (by omega_arith)))
      ?_ fun s₃ rd₃ wr₃ cs₃ f₃ e₃ => ?_
    · rw [hC₂.wr, hp.wr]
      intro a n ⟨r, hr, hcn⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨stR s₀, by simp, hcn⟩
      · exact ⟨scR s₀, by simp, by simp only [Region.Contains] at hcn ⊢; omega_arith⟩
    · have f₃' : Frame [stR s₀, ⟨scr s₀, 512⟩, stkR s₀] s₂.mem s₃.mem := by
        have := f₃; rw [hsp] at this; exact this
      refine { hC₂.after_call hp rd₃ wr₃ cs₃ f₃' with r12 := ?_, repr := fun msg hm => ?_ }
      · rw [cs₃ _ (by decide), u₂.gpr, hpc, ite_eq_left_of_eq_true _ _ (eq_true hb)]; rfl
      · rw [e₃, u₂.mem, hrep msg hm, ite_eq_left_of_eq_true _ _ (eq_true hb)]
  · simp only [decide_eq_false_iff_not] at hb
    refine wp_nil { hC with r12 := ?_, repr := fun msg hm => ?_ }
    · rw [h.r12, hpc, ite_eq_right_of_eq_false _ _ (eq_false hb)]
    · rw [hrep msg hm, ite_eq_right_of_eq_false _ _ (eq_false hb)]

/-- The whole body: a lane or a byte of data, and the test of the bytes left. -/
theorem body_ok {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c < len s₀) {s : State} (hI : Inv s₀ c s) :
    WP isa absorbBody s fun s' => ∃ c', c < c' ∧ c' ≤ len s₀ ∧
      ((isa.eval .ne s' = some false ∧ c' = len s₀ ∧ Inv s₀ (len s₀) s') ∨
        (isa.eval .ne s' = some true ∧ c' < len s₀ ∧ Inv s₀ c' s')) := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  obtain h8 := rate_mod8 hp.rate
  obtain hj : (pos s₀ + c) % rt s₀ < rt s₀ := Nat.mod_lt _ hr₀
  obtain hl := len_lt s₀
  unfold absorbBody
  refine WP.seq (WP.mono (wordTest_ok hI.r12 hI.r14 (by omega_arith)) fun s₇ ⟨oth, m₇, rd₇, wr₇, b, z₇, hb₇⟩ => ?_)
  obtain hI₇ : Inv s₀ c s₇ :=
    { hI.toCommon.of_gpr (fun r hr => oth r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) m₇ rd₇ wr₇ with
      r12 := by rw [oth _ (by decide) (by decide)]; exact hI.r12
      repr := fun msg hm => by rw [m₇]; exact hI.repr msg hm }
  -- The final test.
  obtain tail : ∀ c', c < c' → c' ≤ len s₀ → ∀ t : State, Inv s₀ c' t →
      WP isa (.block [.alu .test .r14 (.reg .r14)]) t fun s' => ∃ c', c < c' ∧ c' ≤ len s₀ ∧
        ((isa.eval .ne s' = some false ∧ c' = len s₀ ∧ Inv s₀ (len s₀) s') ∨
          (isa.eval .ne s' = some true ∧ c' < len s₀ ∧ Inv s₀ c' s')) := by
    intro c' hcc hcl t ht
    refine wp_test fun s' g' m' rd' wr' z' => wp_nil ?_
    obtain ht' : Inv s₀ c' s' :=
      { ht.toCommon.of_gpr (fun r _ => by rw [g']) m' rd' wr' with
        r12 := by rw [g']; exact ht.r12
        repr := by rw [m']; exact ht.repr }
    obtain hz : isa.eval .ne s' = some (!decide (len s₀ - c' = 0)) := by
      simp only [eval, z', ht.r14, BitVec.and_self, ofNat_beq_zero (show len s₀ - c' < 2 ^ 64 by omega_arith),
        Option.map_some]
    by_cases he : c' = len s₀
    · exact ⟨c', hcc, hcl, .inl ⟨by rw [hz]; simp [he], he, he ▸ ht'⟩⟩
    · exact ⟨c', hcc, hcl, .inr ⟨by rw [hz]; simp; omega_arith, by omega_arith, ht'⟩⟩
  refine WP.seq (WP.mono (Q := fun s₁ => ∃ n, 0 < n ∧ (pos s₀ + c) % rt s₀ + n ≤ rt s₀ ∧
      c + n ≤ len s₀ ∧ After s₀ s₇ c n s₁) ?_
    fun s₁ ⟨n, hn, hfit, hcn, hA⟩ => WP.seq (WP.mono (after_ok hp hn hfit hI₇ hA)
      fun s' h => tail (c + n) (by omega_arith) hcn s' h))
  refine WP.ite b (by rw [show isa.eval .e s₇ = s₇.zf from rfl, z₇]) (fun hb => ?_) (fun _ => ?_)
  · obtain ⟨m8, l8⟩ := hb₇ hb
    exact WP.mono (body_word hp (by omega_arith) hI₇ m8) fun s₁ ⟨hC, h12, hz, hst⟩ =>
      ⟨8, by decide, by omega_arith, by omega_arith, hC, h12, hz, hst⟩
  · refine WP.mono (body_block hp hc hI₇) fun s₁ ⟨hC, h12, hz, hst⟩ =>
      ⟨1, by decide, by omega_arith, by omega_arith, hC, h12, hz, ?_⟩
    rw [hst]
    simp [bytesAt, xorAt_single]

/-! ## The epilogue -/

theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {s : State} (hI : Inv s₀ (len s₀) s) :
    WP isa (.block (.mov .rax (.reg .r12) :: restore)) s fun s' =>
      gprPreserved s₀ s' ∧ Proof.Sha3.absorbX86_64.post s₀ s' := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  refine wp_mov fun s₁ u₁ => ?_
  obtain r15 : s₁.gpr .r15 = scr s₀ := by rw [u₁.other _ (by decide), hI.r15]
  refine WP.mono (Spill.restore_ok .r15 saved s₀.gpr s₁ (by decide) (fun p hp' => ?_)
    (by rw [r15, u₁.mem]; exact hI.saved)) fun s' ⟨h₁, h₂, m, _⟩ => ?_
  · have := saved_bound p hp'
    rw [r15]
    exact ⟨scR s₀, by simp [u₁.rd, u₁.wr, hI.wr, hp.wr], contains_offset (by omega_arith) (by omega_arith)⟩
  · have ax : s'.gpr .rax = s₁.gpr .rax := h₂ _ (by decide)
    refine ⟨⟨Spill.calleeSaved_ok h₁ h₂ (by decide) (by rw [u₁.other _ (by decide), hI.rsp]), ?_⟩,
      fun msg hm hpm => ?_, ?_⟩
    · rw [m, u₁.mem]
      exact hI.frame.readW (Region.contains_self _ _) (by simpa using ⟨hp.ret_st, hp.ret_scr, ret_stk s₀⟩)
        (by decide)
    · rw [Proof.Sha3.repr_iff, m, u₁.mem]
      exact hI.repr msg ⟨hm, hpm⟩
    · rw [ax, u₁.gpr, hI.r12, toNat_ofNat_lt (by have := Nat.mod_lt (pos s₀ + len s₀) hr₀; omega_arith)]

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa absorb s₀ fun s' => gprPreserved s₀ s' ∧ Proof.Sha3.absorbX86_64.post s₀ s' := by
  unfold absorb
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨hI, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := Inv s₀ (len s₀)) ?_ fun s₂ hI₂ => epilogue_ok hp hI₂)
  refine WP.ite (decide (len s₀ = 0)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact wp_nil (by rw [hb]; exact hI)
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.loop (M := isa) (fun n s => ∃ c, n = len s₀ - c ∧ c < len s₀ ∧ Inv s₀ c s) ?_ (len s₀) s₁
      ⟨0, rfl, by omega_arith, hI⟩
    rintro n s ⟨c, rfl, hc, hI⟩
    refine WP.mono (body_ok hp hc hI) fun s' ⟨c', hcc, hcl, h⟩ => ?_
    rcases h with ⟨he, _, hI'⟩ | ⟨he, hc', hI'⟩
    · exact .inl ⟨he, hI'⟩
    · exact .inr ⟨he, len s₀ - c', by omega_arith, c', rfl, hc', hI'⟩

/-! ## Constant time -/

/-- The initial taint: the arguments and `rsp` are public, and `rdi` and `r9`
point at the writable regions. -/
def τ₀ : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], flags := false, lens := [200, 640],
    bases := [(.rdi, 0, 0), (.r9, 1, 0)] }

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Sha3.absorbX86_64.pre s₁)
    (h₂ : Proof.Sha3.absorbX86_64.pre s₂) (hpub : Proof.Sha3.absorbX86_64.pub s₁ s₂) :
    X86_64.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := hpub
  obtain wf : ∀ s, Proof.Sha3.absorbX86_64.pre s → X86_64.Taint.Wf τ₀ s := by
    intro s hs
    obtain ⟨-, hw, hd, -⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, τ₀], by simp [hw, hd], by simp [hw]⟩, fun p hp => ?_⟩
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_,
    X86_64.Taint.noLo, X86_64.Taint.noXr⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption
  · rw [h₁.2.1, h₂.2.1, p1, p6]
  · intro sl h; simp [τ₀] at h
  · intro sl h; simp [τ₀] at h

/-- A state satisfying the precondition (with no data). -/
def sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 72 | .rcx => 0x2000 | .r9 => 0x3000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 200⟩, ⟨0x3000, 640⟩]

theorem absorb_correct (s : State) (hs : Proof.Sha3.absorbX86_64.pre s) :
    ∃ t s', Exec isa absorb s t s' ∧ abiPreserved s s' ∧ Proof.Sha3.absorbX86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct (pre_of hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩

theorem absorb_ct : ConstantTime isa Proof.Sha3.absorbX86_64.pre Proof.Sha3.absorbX86_64.pub absorb
    := by
  exact VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp)
    (by taint_decide_weak VG.Proof.Sha3.X86_64.dropRC)

end VG.Proof.Sha3.X86_64.Stream.Absorb

end

end

/-!
# SHA-3 on x86-64: `pad`
-/

@[expose] public section

namespace VG.Proof.Sha3.X86_64.Stream.Pad

open VG VG.X86_64 VG.Impl.Sha3.X86_64.Stream
open VG.Spec.Sha3 (stateAt keccakF absorb pad rates Repr)
open VG.Proof.Sha3 (xorByte Rep stateAt_xorByte absorb_pad)

theorem xor_0x80 (b : BitVec 8) :
    (b.setWidth 64 ^^^ (0x80 : BitVec 32).signExtend 64).setWidth 8 = b ^^^ 0x80 := by
  rw [xor_byte]; rfl

theorem ret_below (sp : Addr) : Region.Disjoint ⟨sp, 8⟩ (below sp 8) := by
  intro x h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega

theorem correct {s₀ : State} (hp : Proof.Sha3.padX86_64.pre s₀) :
    WP isa Impl.Sha3.X86_64.Stream.pad s₀ fun s' => gprPreserved s₀ s' ∧ Proof.Sha3.padX86_64.post s₀ s' := by
  obtain ⟨hrd, hwr, d_ss, d_rs, d_rc, d_ks, d_kc, hrate, hpos⟩ := hp
  have hr := rate_bounds hrate
  let st := s₀.gpr .rdi
  try rewrite [show s₀.gpr .rdi = st from rfl] at *
  have hst : st = s₀.gpr .rdi := rfl
  let scr := s₀.gpr .r8
  try rewrite [show s₀.gpr .r8 = scr from rfl] at *
  have hscr : scr = s₀.gpr .r8 := rfl
  let rate := (s₀.gpr .rsi).toNat
  try rewrite [show (s₀.gpr .rsi).toNat = rate from rfl] at *
  have hrate' : rate = (s₀.gpr .rsi).toNat := rfl
  let pos := (s₀.gpr .rdx).toNat
  try rewrite [show (s₀.gpr .rdx).toNat = pos from rfl] at *
  have hpos' : pos = (s₀.gpr .rdx).toNat := rfl
  have hin : ∀ j < 200, (⟨st, 200⟩ : Region).Contains (st + BitVec.ofNat 64 j) 1 := fun j hj =>
    Proof.Sha3.contains_offset (by omega_using [hj]) (by omega_using [hj])
  have hw : ∀ j < 200, InRegions s₀.wr (st + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [hwr]; exact ⟨_, List.mem_cons_self .., hin j hj⟩
  have hw' : ∀ j < 200, InRegions (s₀.rd ++ s₀.wr) (st + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [hrd]; exact hw j hj
  have e₁ : s₀.ea { base := .rdi, index := some .rdx, scale := 1 } = st + BitVec.ofNat 64 pos := by
    simp only [State.ea, BitVec.mul_one, hpos', BitVec.ofNat_toNat, BitVec.setWidth_eq, ← hst]
    simp
  have e₂ : s₀.ea { base := .rdi, index := some .rsi, scale := 1, disp := -1 } =
      st + BitVec.ofNat 64 (rate - 1) := by
    simp only [State.ea, BitVec.mul_one, ← hst]
    exact Offset.add_ofInt_neg_one _ _ (by omega)
  unfold Impl.Sha3.X86_64.Stream.pad
  refine WP.seq (wp_movzx8 e₁ (hw' _ (by omega_using [hr, hpos])) fun s₁ u₁ => wp_xor fun s₂ u₂ =>
    wp_store8 (a := st + BitVec.ofNat 64 pos) ?_ ?_ fun s₃ g₃ m₃ rd₃ wr₃ => ?_)
  · rw [← e₁]; simp only [State.ea, u₂.other _ (by decide : Reg.rdi ≠ .rax),
      u₁.other _ (by decide : Reg.rdi ≠ .rax), u₂.other _ (by decide : Reg.rdx ≠ .rax),
      u₁.other _ (by decide : Reg.rdx ≠ .rax)]
  · rw [u₂.wr, u₁.wr]; exact hw _ (by omega_using [hr, hpos])
  have k₃ : ∀ r, r ≠ .rax → s₃.gpr r = s₀.gpr r := fun r h => by rw [g₃, u₂.other _ h, u₁.other _ h]
  refine wp_movzx8 (a := st + BitVec.ofNat 64 (rate - 1)) ?_
    (by rw [rd₃, wr₃, u₂.rd, u₁.rd, u₂.wr, u₁.wr]; exact hw' _ (by omega_using [hr]))
    fun s₄ u₄ => wp_xori fun s₅ u₅ => wp_store8 (a := st + BitVec.ofNat 64 (rate - 1)) ?_ ?_
    fun s₆ g₆ m₆ rd₆ wr₆ => wp_mov fun s₇ u₇ => wp_nil ?_
  · rw [← e₂]; simp only [State.ea, k₃ _ (by decide : Reg.rdi ≠ .rax), k₃ _ (by decide : Reg.rsi ≠ .rax)]
  · rw [← e₂]; simp only [State.ea, u₅.other _ (by decide : Reg.rdi ≠ .rax),
      u₄.other _ (by decide : Reg.rdi ≠ .rax), u₅.other _ (by decide : Reg.rsi ≠ .rax),
      u₄.other _ (by decide : Reg.rsi ≠ .rax), k₃ _ (by decide : Reg.rdi ≠ .rax),
      k₃ _ (by decide : Reg.rsi ≠ .rax)]
  · rw [u₅.wr, u₄.wr, wr₃, u₂.wr, u₁.wr]; exact hw _ (by omega_using [hr])
  -- The two bytes written.
  have hb₁ : s₃.mem = s₀.mem.writeW (st + BitVec.ofNat 64 pos)
      (s₀.mem (st + BitVec.ofNat 64 pos) ^^^ (s₀.gpr .rcx).setWidth 8) := by
    rw [m₃, u₂.gpr, u₁.gpr, u₁.other _ (by decide), u₂.mem, u₁.mem, xor_byte]
  have hb₂ : s₆.mem = s₃.mem.writeW (st + BitVec.ofNat 64 (rate - 1))
      (s₃.mem (st + BitVec.ofNat 64 (rate - 1)) ^^^ 0x80) := by
    rw [m₆, u₅.gpr, u₄.gpr, u₅.mem, u₄.mem, xor_0x80]
  have hS : stateAt s₆.mem st =
      xorByte (xorByte (stateAt s₀.mem st) pos ((s₀.gpr .rcx).setWidth 8)) (rate - 1) 0x80 := by
    rw [← stateAt_xorByte (m := s₀.mem) (m' := s₃.mem) (by omega_using [hr, hpos])
      (by simp only [hb₁, writeW8_apply, ↓reduceIte])
      (fun i hi hne => by simp only [hb₁, writeW8_apply, ne_of_lt200 hi (by omega_using [hr, hpos]) hne, ite_false])]
    exact stateAt_xorByte (by omega_using [hr]) (by simp only [hb₂, writeW8_apply, ↓reduceIte])
      (fun i hi hne => by simp only [hb₂, writeW8_apply, ne_of_lt200 hi (by omega_using [hr]) hne, ite_false])
  have hf₆ : Frame [⟨st, 200⟩] s₀.mem s₆.mem := by
    rw [hb₂, hb₁]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (hin _ (by omega_using [hr, hpos]))).writeW
      (List.mem_singleton_self _) _ (hin _ (by omega_using [hr]))
  have k₇ : ∀ r, r ≠ .rax → r ≠ .rsi → s₇.gpr r = s₀.gpr r := fun r h h' => by
    rw [u₇.other _ h', g₆, u₅.other _ h, u₄.other _ h, k₃ _ h]
  have d₁ : Region.Disjoint ⟨st, 200⟩ ⟨scr, 512⟩ := d_ss.sub_right (Region.sub_prefix (base := scr) (len := 512) (len' := 640) (by omega_using []))
  have hsp₇ : s₇.gpr .rsp = s₀.gpr .rsp := k₇ _ (by decide) (by decide)
  have hbl : below (s₀.gpr .rsp) 8 = ⟨s₀.gpr .rsp - 8, 8⟩ := rfl
  refine call_ok (st := st) (scr := scr) (by rw [k₇ _ (by decide) (by decide)])
    (by rw [u₇.gpr, g₆, u₅.other _ (by decide), u₄.other _ (by decide), k₃ _ (by decide)]) d₁
    (by rw [hsp₇, hbl]; exact d_ks) (by rw [hsp₇, hbl]; exact d_kc.sub_right (Region.sub_prefix (base := scr) (len := 512) (len' := 640) (by omega_using [])))
    (fun a n h => by
      rw [u₇.wr, wr₆, u₅.wr, u₄.wr, wr₃, u₂.wr, u₁.wr, hwr]
      obtain ⟨r, hr, hc⟩ := h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., hc⟩
      · exact ⟨⟨scr, 640⟩, by simp, by simp only [Region.Contains] at hc ⊢; omega_using [hc]⟩) ?_
  intro s' _ _ cs' f' e' _ _
  rw [u₇.mem] at f' e'
  refine ⟨⟨fun r hr => ?_, ?_⟩, fun msg hR hm => ?_⟩
  · rw [cs' r hr, k₇ r (fun h => by subst h; simp [calleeSaved] at hr)
      (fun h => by subst h; simp [calleeSaved] at hr)]
  · rw [hsp₇] at f'
    have hf : Frame [⟨st, 200⟩, ⟨scr, 512⟩, below (s₀.gpr .rsp) 8] s₀.mem s'.mem :=
      (hf₆.mono fun r hr => by simp at hr; simp [hr]).trans f'
    exact hf.readW (Region.contains_self _ _) (by
      simpa using ⟨d_rs, d_rc.sub_right (Region.sub_prefix (base := scr) (len := 512) (len' := 640) (by omega_using [])), ret_below _⟩) (by decide)
  · rw [e', hS, absorb_pad (by omega) (by omega), ← hm, show Rep rate msg = stateAt s₀.mem st from hR.symm]

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 136 | .r8 => 0x3000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 200⟩, ⟨0x3000, 640⟩]

theorem pad_correct (s : State) (hs : Proof.Sha3.padX86_64.pre s) :
    ∃ t s', Exec isa Impl.Sha3.X86_64.Stream.pad s t s' ∧ abiPreserved s s' ∧
      Proof.Sha3.padX86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct hs
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩

theorem pad_ct : ConstantTime isa Proof.Sha3.padX86_64.pre Proof.Sha3.padX86_64.pub
    Impl.Sha3.X86_64.Stream.pad := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .r8, .rsp]) ?_
    (by taint_decide_weak VG.Proof.Sha3.X86_64.dropRC)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

end VG.Proof.Sha3.X86_64.Stream.Pad
