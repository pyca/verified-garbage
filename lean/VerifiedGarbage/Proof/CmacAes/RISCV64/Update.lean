module

public import VerifiedGarbage.Proof.CmacAes.RISCV64.Contract
public import VerifiedGarbage.Impl.CmacAes.RISCV64
public import VerifiedGarbage.Proof.AesCbc.RISCV64.Loop
public import VerifiedGarbage.Proof.AesCbc.RISCV64.Call
import VerifiedGarbage.Proof.AesCbc.RISCV64.Body
import VerifiedGarbage.Proof.AesCbc.Spec
import VerifiedGarbage.Proof.Aes.RISCV64.BlocksVerified
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.CmacAes.RISCV64.Subkeys
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# AES-CMAC on RISC-V: `vg_cmac_aes_update`

AES-CBC's registers, prologue and epilogue (`Proof/AesCbc/RISCV64/Loop.lean`),
with the chaining value at `state` and the data only read, as on PPC64LE
(`Proof/CmacAes/PPC64LE/Update.lean`): the invariant after `k` blocks
(`UInv`) has the state `C` chained over the first `k` blocks
(`Spec.Cmac.chain`), and each block (`body_ok`) XORs the next block into the
state and enciphers it in place.
-/

@[expose] public section

namespace VG.Proof.CmacAes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.CmacAes.RISCV64
open VG.Impl.AesCbc.RISCV64 (save setup restore xorInto advance whole saved savePtr)
open VG.Proof.AesCbc.RISCV64 (W R Iv Dp N S sv q schR ivR dataR scrR wsR cR saveL saveG savedMem vars
  saved_bound savedMem_frame slots_sub slot_contains slot_sub in_rw a1_ofNat a4_ofNat advance_regs save_eq
  restore_eq xorInto_wp CallPre blk_call savePtr_ok q_lt sv_add wsR_sub encryptBlocks_noFrames)
open VG.Spec.Aes (bytesAt)

/-- The blocks on entry. -/
abbrev cblks (s₀ : State) : List (List Byte) := Spec.Cmac.blocksAt s₀.mem (Dp s₀) 16 (N s₀)

/-- `CIPH_K`. -/
abbrev ciph (s₀ : State) : Spec.Cmac.Cipher := ciphAt s₀.mem (W s₀) (R s₀)

/-- The state on entry. -/
abbrev st0 (s₀ : State) : List Byte := bytesAt s₀.mem (Iv s₀) 16

/-- The address of block `k`. -/
abbrev blk (s₀ : State) (k : Nat) : Addr := Dp s₀ + BitVec.ofNat 64 (16 * k)

/-- The precondition, by name. -/
structure UPre (s₀ : State) : Prop where
  rd : s₀.rd = [schR s₀, dataR s₀]
  wr : s₀.wr = [ivR s₀, scrR s₀]
  sch_st : (schR s₀).Disjoint (ivR s₀)
  sch_scr : (schR s₀).Disjoint (scrR s₀)
  data_st : (dataR s₀).Disjoint (ivR s₀)
  data_scr : (dataR s₀).Disjoint (scrR s₀)
  st_scr : (ivR s₀).Disjoint (scrR s₀)
  st_wrap : (Iv s₀).toNat + 16 ≤ 2 ^ 64
  data_wrap : (Dp s₀).toNat + 16 * N s₀ ≤ 2 ^ 64
  scr_wrap : (S s₀).toNat + 2176 ≤ 2 ^ 64
  rounds : R s₀ = 10 ∨ R s₀ = 12 ∨ R s₀ = 14

theorem UPre.of {s₀ : State} (h : updateRISCV64.pre s₀) : UPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k⟩

/-- The loop invariant, after `k` blocks. -/
structure UInv (s₀ : State) (k : Nat) (s : State) : Prop where
  s1 : s.gpr .s1 = W s₀
  s2 : s.gpr .s2 = s₀.gpr .a1
  s3 : s.gpr .s3 = Iv s₀
  s4 : s.gpr .s4 = blk s₀ k
  s5 : s.gpr .s5 = BitVec.ofNat 64 (N s₀ - k)
  s6 : s.gpr .s6 = S s₀
  keep : ∀ r ∈ preserved, r ∉ vars → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [ivR s₀, wsR s₀] (savedMem s₀) s.mem
  st : bytesAt s.mem (Iv s₀) 16 = Spec.Cmac.chain (ciph s₀) (st0 s₀) ((cblks s₀).take k)

section
variable {s₀ : State} (hp : UPre s₀)
include hp

omit hp in
/-- Memory after saving the registers and changing at most the state and
the working space. -/
theorem UPre.of_frame {m : Mem} (hf : Frame [ivR s₀, wsR s₀] (savedMem s₀) m) :
    Frame [ivR s₀, scrR s₀] s₀.mem m :=
  ((savedMem_frame s₀).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, slots_sub s₀⟩).trans
    (hf.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨ivR s₀, by simp, fun _ h => h⟩
      · exact ⟨scrR s₀, by simp, wsR_sub⟩)

theorem UPre.sched {m : Mem} (hf : Frame [ivR s₀, scrR s₀] s₀.mem m) :
    bytesAt m (W s₀) (16 * (R s₀ + 1)) = bytesAt s₀.mem (W s₀) (16 * (R s₀ + 1)) := by
  have hR : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  refine AesCbc.RISCV64.bytesAt_frame hf (fun r hr => ?_) (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.sch_st.sub_left (Region.sub_prefix hR)
  · exact hp.sch_scr.sub_left (Region.sub_prefix hR)

omit hp in
theorem UPre.blk_sub {k : Nat} (hk : k < N s₀) : Region.Sub ⟨blk s₀ k, 16⟩ (dataR s₀) :=
  Offset.sub_base _ (by omega)

theorem UPre.block {m : Mem} (hf : Frame [ivR s₀, scrR s₀] s₀.mem m) {k : Nat} (hk : k < N s₀) :
    bytesAt m (blk s₀ k) 16 = (cblks s₀)[k]'(by simp [Spec.Cmac.blocksAt]; exact hk) := by
  rw [AesCbc.RISCV64.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.data_st.sub_left (UPre.blk_sub hk)
    · exact hp.data_scr.sub_left (UPre.blk_sub hk)) (by decide)]
  simp [Spec.Cmac.blocksAt, blk]

theorem UPre.blk_wrap {k : Nat} (hk : k < N s₀) : (blk s₀ k).toNat + 16 ≤ 2 ^ 64 := by
  have := hp.data_wrap
  rw [blk, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * k) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

end

/-! ## The prologue -/

theorem prologue_wp {s₀ : State} (hp : UPre s₀) : WP isa (.block (save ++ setup)) s₀ (UInv s₀ 0) := by
  have hN := (s₀.gpr .a4).isLt
  rw [save_eq, List.append_assoc, WP.block_append_iff]
  refine WP.mono (savePtr_ok .a5) fun s₁ e => ?_
  subst e
  have t₀ : (s₀.write .t0 (sv s₀)).gpr .t0 = sv s₀ := RegUpd.gpr_write_self _ _ _
  refine Spill.save_ok (b := .t0) (l := saveL) (by rw [t₀]; exact Align.align_al _) (by decide)
    (fun p hp' => ?_) ?_
  · have := saved_bound p hp'
    rw [t₀]
    show InRegions s₀.wr _ 8
    rw [hp.wr]
    exact in_rw (r := scrR s₀) (by simp) (slot_contains s₀ this.1 this.2)
  unfold setup Impl.AesCbc.RISCV64.mov
  refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ =>
    wp_mv fun s₅ u₅ => wp_mv fun s₆ u₆ => WP.block_nil ?_
  have m₆ : s₆.mem = savedMem s₀ := by
    rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    show Spill.saveMem s₀.mem ((s₀.write .t0 (sv s₀)).gpr .t0) _ _ = _
    rw [t₀]
  have g₀ (r : Reg) (hr : r ≠ .t0) : (s₀.write .t0 (sv s₀)).gpr r = s₀.gpr r :=
    RegUpd.gpr_write_of_ne _ _ hr
  have stS : bytesAt (savedMem s₀) (Iv s₀) 16 = st0 s₀ :=
    AesCbc.RISCV64.bytesAt_frame (savedMem_frame s₀) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_scr.sub_right (slots_sub s₀)) (by decide)
  exact {
    s1 := by
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.gpr]; exact g₀ .a0 (by decide)
    s2 := by
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.gpr, u₁.other _ (by decide)]; exact g₀ .a1 (by decide)
    s3 := by
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
        u₂.other _ (by decide), u₁.other _ (by decide)]; exact g₀ .a2 (by decide)
    s4 := by
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide), g₀ .a3 (by decide)]; simp
    s5 := by
      rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide), g₀ .a4 (by decide), a4_ofNat]; rfl
    s6 := by
      rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide)]; exact g₀ .a5 (by decide)
    keep := fun r hr hv => by
      simp only [vars, List.mem_cons, List.not_mem_nil, or_false, not_or] at hv
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hv
      rw [u₆.other _ h6, u₅.other _ h5, u₄.other _ h4, u₃.other _ h3, u₂.other _ h2, u₁.other _ h1]
      exact g₀ _ (preserved_ne r hr).1
    rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]; rfl
    wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; rfl
    sp := by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]; rfl
    frame := by rw [m₆]; exact Frame.refl _ _
    st := by rw [m₆, stS, List.take_zero]; rfl }

/-! ## One block -/

/-- The arguments of the call on the state. -/
theorem updArgs_wp {s₀ : State} (hp : UPre s₀) {s : State} (s1 : s.gpr .s1 = W s₀)
    (s2 : s.gpr .s2 = s₀.gpr .a1) (s3 : s.gpr .s3 = Iv s₀) (s6 : s.gpr .s6 = S s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block updArgs) s fun s' => CallPre s' (W s₀) (Iv s₀) (S s₀) (R s₀) ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
  unfold updArgs Impl.AesCbc.RISCV64.mov
  refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_li (imm := 1) (by decide) fun s₄ u₄ =>
    wp_mv fun s₅ u₅ => WP.block_nil ⟨?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, hp.rounds, hp.sch_st,
      hp.sch_scr.sub_right (Region.sub_prefix (by decide)),
      hp.st_scr.sub_right (Region.sub_prefix (by decide)), hp.st_wrap, ?_, ?_⟩
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        u₁.gpr, s1]
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
        u₁.other _ (by decide), s2, a1_ofNat]
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
        u₁.other _ (by decide), s3]
    · rw [u₅.other _ (by decide), u₄.gpr]
    · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide), s6]
    · rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrd, hwr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
      · exact ⟨ivR s₀, by simp, 0, by simp, by simp⟩
      · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
    · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hwr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨ivR s₀, by simp, 0, by simp, by simp⟩
      · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
  · obtain ⟨-, -, -, -, -, -, -, -, h0, h1, h2, h3, h4, -⟩ := preserved_ne r hr
    rw [u₅.other _ h4, u₄.other _ h3, u₃.other _ h2, u₂.other _ h1, u₁.other _ h0]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]

/-- The block XORed into the state, and the arguments of the call. -/
theorem bodyPre_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : UInv s₀ k s) :
    WP isa (.block (xorInto .s3 .s4 ++ updArgs)) s fun s' =>
      CallPre s' (W s₀) (Iv s₀) (S s₀) (R s₀) ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      bytesAt s'.mem (Iv s₀) 16 = Spec.Cmac.xor (bytesAt s.mem (Iv s₀) 16) (bytesAt s.mem (blk s₀ k) 16) ∧
      Frame [ivR s₀] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have hR : s.rd ++ s.wr = [schR s₀, dataR s₀, ivR s₀, scrR s₀] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have hW : s.wr = [ivR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  refine xorInto_wp (P := Iv s₀) (Q := blk s₀ k) (by decide) (by decide) (by decide) (by decide)
    h.s3 h.s4 ⟨dataR s₀, by rw [hR]; simp, UPre.blk_sub hk⟩ ⟨ivR s₀, by rw [hW]; simp, fun _ h => h⟩
    (hp.data_st.symm.sub_right (UPre.blk_sub hk)) fun s₁ g₁ x₁ f₁ rd₁ wr₁ sp₁ => ?_
  have g₁' (r : Reg) (hr : r ∈ preserved) : s₁.gpr r = s.gpr r := by
    obtain ⟨-, -, -, h3, h4, -⟩ := preserved_ne r hr
    exact g₁ r h3 h4
  exact WP.mono (updArgs_wp hp (by rw [g₁' _ (by decide), h.s1]) (by rw [g₁' _ (by decide), h.s2])
    (by rw [g₁' _ (by decide), h.s3]) (by rw [g₁' _ (by decide), h.s6]) (by rw [rd₁, h.rd])
    (by rw [wr₁, h.wr])) fun s₂ ⟨c, g₂, mem₂, rd₂, wr₂, sp₂⟩ =>
      ⟨c, fun r hr => by rw [g₂ r hr, g₁' r hr], by rw [mem₂, x₁]; rfl, by rw [mem₂]; exact f₁,
        by rw [rd₂, rd₁], by rw [wr₂, wr₁], by rw [sp₂, sp₁]⟩

theorem body_ok {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : UInv s₀ k s) :
    WP isa body s (UInv s₀ (k + 1)) := by
  have pre := bodyPre_wp hp hk h
  refine WP.seq (WP.mono pre fun s₂ ⟨c₂, g₂, x₂, f₂, rd₂, wr₂, sp₂⟩ =>
    WP.seq (WP.mono (blk_call (name := "vg_aes_encrypt_blocks")
      Proof.Aes.RISCV64.encryptBlocks_correct encryptBlocks_noFrames c₂) fun s₃ c => ?_))
  have g₃ (r : Reg) (hr : r ∈ preserved) : s₃.gpr r = s.gpr r := by rw [c.saved r hr, g₂ r hr]
  refine advance_regs (s := s₃) hk (by rw [g₃ _ (by decide), h.s4]) (by rw [g₃ _ (by decide), h.s5])
    fun s₄ s4₄ s5₄ keep₄ mem₄ rd₄ wr₄ sp₄ => ?_
  have g (r : Reg) (hr : r ∈ preserved) (h4 : r ≠ .s4) (h5 : r ≠ .s5) : s₄.gpr r = s.gpr r := by
    rw [keep₄ r h4 h5, g₃ r hr]
  -- Memory.
  have fStep : Frame [ivR s₀, wsR s₀] s.mem s₄.mem := by
    rw [mem₄]
    refine (f₂.sub fun r hr => ?_).trans (c.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨wsR s₀, by simp, fun _ h => h⟩
  have big : Frame [ivR s₀, scrR s₀] s₀.mem s₂.mem :=
    (UPre.of_frame h.frame).trans (f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
  have blkB : bytesAt s.mem (blk s₀ k) 16 = (cblks s₀)[k]'(by simp [Spec.Cmac.blocksAt]; exact hk) :=
    hp.block (UPre.of_frame h.frame) hk
  have newSt : bytesAt s₄.mem (Iv s₀) 16 =
      Spec.Cmac.chain (ciph s₀) (st0 s₀) ((cblks s₀).take (k + 1)) := by
    rw [mem₄, c.out, cipher_bytes, hp.sched big, x₂, h.st, blkB,
      List.take_add_one, List.getElem?_eq_getElem (by simp [Spec.Cmac.blocksAt]; exact hk), Option.toList_some,
      Proof.Cmac.chain_append, Proof.Cmac.chain_single]
  refine ⟨?_, ?_, ?_, s4₄, s5₄, ?_, fun r hr hv => ?_, ?_, ?_, ?_, h.frame.trans fStep, newSt⟩
  · rw [g .s1 (by decide) (by decide) (by decide), h.s1]
  · rw [g .s2 (by decide) (by decide) (by decide), h.s2]
  · rw [g .s3 (by decide) (by decide) (by decide), h.s3]
  · rw [g .s6 (by decide) (by decide) (by decide), h.s6]
  · rw [g r hr (fun e => hv (by simp [e])) (fun e => hv (by simp [e])), h.keep r hr hv]
  · rw [rd₄, c.rd, rd₂, h.rd]
  · rw [wr₄, c.wr, wr₂, h.wr]
  · rw [sp₄, c.sp, sp₂, h.sp]

/-! ## The loop, and the whole function -/

theorem loop_ok {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : UInv s₀ k s) :
    WP isa (.loop body (.nonzero .s5)) s (UInv s₀ (N s₀)) := by
  have hN := (s₀.gpr .a4).isLt
  refine WP.loop (M := isa) (body := body) (c := .nonzero .s5) (Q := UInv s₀ (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ UInv s₀ j t) ?_ (N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (body_ok hp hk h) fun s' h' => ?_
  have ev := eval_nonzero_ofNat s' .s5 (k := N s₀ - (k + 1)) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hN) h'.s5
  by_cases hz : N s₀ - (k + 1) = 0
  · left
    refine ⟨by rw [ev]; simp [hz], ?_⟩
    rwa [show N s₀ = k + 1 by omega]
  · right
    refine ⟨by rw [ev]; simp [hz], N s₀ - (k + 1), by omega, k + 1, rfl, by omega, h'⟩

theorem mid_wp {s₀ : State} (hp : UPre s₀) {s₁ : State} (h : UInv s₀ 0 s₁) :
    WP isa (.ite (.zero .s5) (.block []) (.loop body (.nonzero .s5))) s₁ (UInv s₀ (N s₀)) := by
  have hN := (s₀.gpr .a4).isLt
  have ev := eval_zero_ofNat s₁ .s5 (k := N s₀ - 0) (by omega) h.s5
  rw [Nat.sub_zero] at ev
  by_cases hn : N s₀ = 0
  · refine WP.ite true (by rw [ev, hn]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact h
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact loop_ok hp (by omega) h

/-- The postcondition, with the stack pointer. -/
def UDone (s₀ s' : State) : Prop :=
  (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧ s'.sp = s₀.sp ∧
    updateRISCV64.post s₀ s'

theorem epilogue_wp {s₀ : State} (hp : UPre s₀) {s₂ : State} (h₂ : UInv s₀ (N s₀) s₂) :
    WP isa (.block restore) s₂ (UDone s₀) := by
  have hsv : Spill.Saved (sv s₀) (saveG s₀) saveL s₂.mem :=
    (Spill.saveMem_saved (by decide) _ _ _).frame h₂.frame fun p hp' r hr => by
      have hb := saved_bound p hp'
      have := q_lt s₀
      have := hp.scr_wrap
      have hsub : Region.Sub ⟨sv s₀ + BitVec.ofNat 64 p.2, 8⟩ (scrR s₀) := slot_sub s₀ hb.1 hb.2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.st_scr.symm.sub_left hsub
      · rw [sv_add]; exact Offset.disjoint_base _ (by omega) (by omega)
  have hall : (cblks s₀).take (N s₀) = cblks s₀ := List.take_of_length_le (by simp [Spec.Cmac.blocksAt])
  rw [restore_eq, WP.block_append_iff]
  refine WP.mono (savePtr_ok .s6) fun s₃ e => ?_
  subst e
  rw [h₂.s6]
  refine WP.mono (Spill.restore_wp (b := .t0) (l := saveL) (B := sv s₀) (Align.align_al _)
    (RegUpd.gpr_write_self _ _ _) (by decide) (by decide) (fun p hp' => ?_) hsv) fun s₄ r₄ => ?_
  · have := saved_bound p hp'
    show InRegions (s₂.rd ++ s₂.wr) _ 8
    rw [h₂.rd, h₂.wr, hp.rd, hp.wr]
    exact in_rw (r := scrR s₀) (by simp) (slot_contains s₀ this.1 this.2)
  have g₀ (r : Reg) (hr : r ≠ .t0) : saveG s₀ r = s₀.gpr r := RegUpd.gpr_write_of_ne _ _ hr
  refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
  · have h0 : r ≠ .t0 := (preserved_ne r hr).1
    rw [r₄.gpr_of (r := r) ?_, g₀ r h0]
    by_cases hv : r ∈ vars
    · left
      simp only [vars, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · right
      rw [RegUpd.gpr_write_of_ne _ _ h0, h₂.keep r hr hv, g₀ r h0]
  · rw [r₄.gpr (.ra, 16) (by decide), g₀ .ra (by decide)]
  · rw [r₄.sp, RegUpd.sp_write, h₂.sp]
  · show bytesAt s₄.mem (s₀.gpr .a2) 16 = _
    rw [r₄.mem, RegUpd.mem_write]
    show bytesAt s₂.mem (Iv s₀) 16 = _
    rw [h₂.st, hall]

theorem update_wp {s₀ : State} (h0 : updateRISCV64.pre s₀) : WP isa update s₀ (UDone s₀) := by
  have hp := UPre.of h0
  exact WP.seq (WP.mono (prologue_wp hp) fun s₁ h₁ =>
    WP.seq (WP.mono (mid_wp hp h₁) fun _ h₂ => epilogue_wp hp h₂))

end VG.Proof.CmacAes.RISCV64
