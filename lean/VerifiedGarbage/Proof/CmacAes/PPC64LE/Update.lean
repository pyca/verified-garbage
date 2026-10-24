module

public import VerifiedGarbage.Proof.CmacAes.PPC64LE.Contract
public import VerifiedGarbage.Impl.CmacAes.PPC64LE
public import VerifiedGarbage.Proof.AesCbc.PPC64LE.Loop
import VerifiedGarbage.Proof.AesCbc.PPC64LE.Body
import VerifiedGarbage.Proof.CmacAes.PPC64LE.Subkeys
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.AesCbc.PPC64LE
public import VerifiedGarbage.Proof.AesCbc.PPC64LE.Call

/-!
# AES-CMAC on PPC64LE: `vg_cmac_aes_update`

AES-CBC's registers, prologue and epilogue (`Proof/AesCbc/PPC64LE/Loop.lean`),
with the chaining value at `state` and the data only read: the invariant
after `k` blocks (`UInv`) has the state `C` chained over the first `k`
blocks (`Spec.Cmac.chain`), and each block (`body_ok`) XORs the next block
into the state and enciphers it in place.
-/

@[expose] public section

namespace VG.Proof.CmacAes.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacAes.PPC64LE
open VG.Impl.AesCbc.PPC64LE (save setup restore xorInto advance whole lrOff saved)
open VG.Proof.AesCbc.PPC64LE (W R Iv Dp N S schR ivR dataR scrR blk saveL saveG savedMem vars wK
  saved_bound savedMem_frame in_rw r4_ofNat r7_ofNat advance_regs save_eq restore_eq preserved_ne_r0
  xorInto_wp CallPre blk_call bytesAt_frame)
open VG.Proof.AesCbc (xorMem xorMem_frame xorMem_bytes)
open VG.Spec.Aes (bytesAt)

/-- The blocks on entry. -/
abbrev cblks (s₀ : State) : List (List Byte) := Spec.Cmac.blocksAt s₀.mem (Dp s₀) 16 (N s₀)

/-- `CIPH_K`. -/
abbrev ciph (s₀ : State) : Spec.Cmac.Cipher := ciphAt s₀.mem (W s₀) (R s₀)

/-- The state on entry. -/
abbrev st0 (s₀ : State) : List Byte := bytesAt s₀.mem (Iv s₀) 16

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

theorem UPre.of {s₀ : State} (h : updatePPC64LE.pre s₀) : UPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k⟩

/-- The loop invariant, after `k` blocks. -/
structure UInv (s₀ : State) (k : Nat) (s : State) : Prop where
  r14 : s.gpr .r14 = W s₀
  r15 : s.gpr .r15 = s₀.gpr .r4
  r16 : s.gpr .r16 = Iv s₀
  r17 : s.gpr .r17 = blk s₀ k
  r18 : s.gpr .r18 = BitVec.ofNat 64 (N s₀ - k)
  r19 : s.gpr .r19 = S s₀
  keep : ∀ r ∈ preserved, r ∉ vars → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [ivR s₀, ⟨S s₀, 2064⟩] (savedMem s₀) s.mem
  st : bytesAt s.mem (Iv s₀) 16 = Spec.Cmac.chain (ciph s₀) (st0 s₀) ((cblks s₀).take k)

section
variable {s₀ : State} (hp : UPre s₀)
include hp

omit hp in
/-- Memory after saving the registers and changing at most the state and
the first 2064 bytes of the scratch buffer. -/
theorem UPre.of_frame {m : Mem} (hf : Frame [ivR s₀, ⟨S s₀, 2064⟩] (savedMem s₀) m) :
    Frame [ivR s₀, scrR s₀] s₀.mem m :=
  ((savedMem_frame s₀).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, AesCbc.PPC64LE.UPre.scr_sub (by decide)⟩).trans
    (hf.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨ivR s₀, by simp, fun _ h => h⟩
      · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩)

theorem UPre.sched {m : Mem} (hf : Frame [ivR s₀, scrR s₀] s₀.mem m) :
    bytesAt m (W s₀) (16 * (R s₀ + 1)) = wK s₀ := by
  have hR : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  refine bytesAt_frame hf (fun r hr => ?_) (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.sch_st.sub_left (Region.sub_prefix hR)
  · exact hp.sch_scr.sub_left (Region.sub_prefix hR)

omit hp in
theorem UPre.blk_sub {k : Nat} (hk : k < N s₀) : Region.Sub ⟨blk s₀ k, 16⟩ (dataR s₀) :=
  Offset.sub_base _ (by omega)

theorem UPre.block {m : Mem} (hf : Frame [ivR s₀, scrR s₀] s₀.mem m) {k : Nat} (hk : k < N s₀) :
    bytesAt m (blk s₀ k) 16 = (cblks s₀)[k]'(by simp [Spec.Cmac.blocksAt]; exact hk) := by
  rw [bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.data_st.sub_left (UPre.blk_sub hk)
    · exact hp.data_scr.sub_left (UPre.blk_sub hk)) (by decide)]
  simp [Spec.Cmac.blocksAt, blk]

end

/-! ## The prologue -/

theorem prologue_wp {s₀ : State} (hp : UPre s₀) : WP isa (.block (save ++ setup)) s₀ (UInv s₀ 0) := by
  have hN := (s₀.gpr .r7).isLt
  rw [save_eq, List.cons_append]
  refine WP.cons exec_mflr (Spill.save_ok (b := .r8) (l := saveL) (by decide) (by decide) (fun p hp' => ?_) ?_)
  · have := saved_bound p hp'
    show InRegions s₀.wr (S s₀ + BitVec.ofNat 64 p.2) 8
    rw [hp.wr]
    exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega))
  unfold setup Impl.AesCbc.PPC64LE.mov
  refine wp_mr fun s₁ u₁ => wp_mr fun s₂ u₂ => wp_mr fun s₃ u₃ => wp_mr fun s₄ u₄ =>
    wp_mr fun s₅ u₅ => wp_mr fun s₆ u₆ => wp_nil ?_
  have m₆ : s₆.mem = savedMem s₀ := by
    rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]; rfl
  have g₀ (r : Reg) (hr : r ≠ .r0) : (s₀.write .r0 s₀.lr).gpr r = s₀.gpr r := by
    simp [State.write, hr]
  have stS : bytesAt (savedMem s₀) (Iv s₀) 16 = st0 s₀ :=
    bytesAt_frame (savedMem_frame s₀) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_scr.sub_right (AesCbc.PPC64LE.UPre.scr_sub (by decide))) (by decide)
  exact {
    r14 := by
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.gpr]; exact g₀ .r3 (by decide)
    r15 := by
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.gpr, u₁.other _ (by decide)]; exact g₀ .r4 (by decide)
    r16 := by
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
        u₂.other _ (by decide), u₁.other _ (by decide)]; exact g₀ .r5 (by decide)
    r17 := by
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide), g₀ .r6 (by decide)]; simp [blk]
    r18 := by
      rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide), g₀ .r7 (by decide), r7_ofNat]; rfl
    r19 := by
      rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide)]; exact g₀ .r8 (by decide)
    keep := fun r hr hv => by
      simp only [vars, List.mem_cons, List.not_mem_nil, or_false, not_or] at hv
      obtain ⟨h14, h15, h16, h17, h18, h19⟩ := hv
      rw [u₆.other _ h19, u₅.other _ h18, u₄.other _ h17, u₃.other _ h16, u₂.other _ h15, u₁.other _ h14]
      exact g₀ _ (preserved_ne_r0 r hr)
    rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]; rfl
    wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; rfl
    frame := by rw [m₆]; exact Frame.refl _ _
    st := by rw [m₆, stS, List.take_zero]; rfl }

/-! ## One block -/

/-- The arguments of the call on the state. -/
theorem updArgs_wp {s₀ : State} (hp : UPre s₀) {s : State} (r14 : s.gpr .r14 = W s₀)
    (r15 : s.gpr .r15 = s₀.gpr .r4) (r16 : s.gpr .r16 = Iv s₀) (r19 : s.gpr .r19 = S s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block updArgs) s fun s' => CallPre s' (W s₀) (Iv s₀) (S s₀) (R s₀) ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold updArgs Impl.AesCbc.PPC64LE.mov
  refine wp_mr fun s₁ u₁ => wp_mr fun s₂ u₂ => wp_mr fun s₃ u₃ => wp_li (by decide) fun s₄ u₄ =>
    wp_mr fun s₅ u₅ => wp_nil ⟨?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, hp.rounds, hp.sch_st,
      hp.sch_scr.sub_right (Region.sub_prefix (by decide)),
      hp.st_scr.sub_right (Region.sub_prefix (by decide)), hp.st_wrap, ?_, ?_⟩
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        u₁.gpr, r14]
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
        u₁.other _ (by decide), r15, r4_ofNat]
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
        u₁.other _ (by decide), r16]
    · rw [u₅.other _ (by decide), u₄.gpr]
    · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide), r19]
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
  · obtain ⟨-, h3, h4, h5, h6, h7, -⟩ := preserved_ne r hr
    rw [u₅.other _ h7, u₄.other _ h6, u₃.other _ h5, u₂.other _ h4, u₁.other _ h3]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

/-- The block XORed into the state, and the arguments of the call. -/
theorem bodyPre_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : UInv s₀ k s) :
    WP isa (.block (xorInto .r16 .r17 ++ updArgs)) s fun s' =>
      CallPre s' (W s₀) (Iv s₀) (S s₀) (R s₀) ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      s'.mem = xorMem s.mem (Iv s₀) (blk s₀ k) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hR : s.rd ++ s.wr = [schR s₀, dataR s₀, ivR s₀, scrR s₀] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have hW : s.wr = [ivR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  have dw := hp.data_wrap
  have cB0 : (dataR s₀).Contains (blk s₀ k) 8 := Offset.contains_base _ (by omega) (by omega)
  have cB8 : (dataR s₀).Contains (blk s₀ k + BitVec.ofNat 64 8) 8 := by
    rw [Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega)
  refine xorInto_wp (P := Iv s₀) (Q := blk s₀ k) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) h.r16 h.r17
    (by rw [hR]; exact in_rw (by simp) AesCbc.PPC64LE.cIv0) (by rw [hR]; exact in_rw (by simp) AesCbc.PPC64LE.cIv8)
    (by rw [hR]; exact in_rw (by simp) cB0) (by rw [hR]; exact in_rw (by simp) cB8)
    (by rw [hW]; exact in_rw (by simp) AesCbc.PPC64LE.cIv0) (by rw [hW]; exact in_rw (by simp) AesCbc.PPC64LE.cIv8)
    fun s₁ g₁ mem₁ rd₁ wr₁ => ?_
  have g₁' (r : Reg) (hr : r ∈ preserved) : s₁.gpr r = s.gpr r := by
    obtain ⟨-, -, -, -, -, -, -, h9, h10, -⟩ := preserved_ne r hr
    exact g₁ r h9 h10
  exact WP.mono (updArgs_wp hp (by rw [g₁' _ (by decide), h.r14]) (by rw [g₁' _ (by decide), h.r15])
    (by rw [g₁' _ (by decide), h.r16]) (by rw [g₁' _ (by decide), h.r19]) (by rw [rd₁, h.rd])
    (by rw [wr₁, h.wr])) fun s₂ ⟨c, g₂, mem₂, rd₂, wr₂⟩ =>
      ⟨c, fun r hr => by rw [g₂ r hr, g₁' r hr], by rw [mem₂, mem₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩

theorem body_ok {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : UInv s₀ k s) :
    WP isa body s (UInv s₀ (k + 1)) := by
  have bS : (⟨Iv s₀, 16⟩ : Region).Disjoint ⟨blk s₀ k, 16⟩ := hp.data_st.symm.sub_right (UPre.blk_sub hk)
  have pre := bodyPre_wp hp hk h
  refine WP.seq (WP.mono pre fun s₂ ⟨c₂, g₂, mem₂, rd₂, wr₂⟩ => WP.seq (WP.mono (blk_call (name := "vg_aes_encrypt_blocks")
    Proof.Aes.PPC64LE.encryptBlocks_correct AesCbc.PPC64LE.encryptBlocks_noFrames c₂) fun s₃ c => ?_))
  have g₃ (r : Reg) (hr : r ∈ preserved) : s₃.gpr r = s.gpr r := by rw [c.saved r hr, g₂ r hr]
  refine advance_regs (s := s₃) hk (by rw [g₃ _ (by decide), h.r17]) (by rw [g₃ _ (by decide), h.r18])
    fun s₄ r17₄ r18₄ keep₄ mem₄ rd₄ wr₄ => ?_
  have g (r : Reg) (hr : r ∈ preserved) (h17 : r ≠ .r17) (h18 : r ≠ .r18) : s₄.gpr r = s.gpr r := by
    rw [keep₄ r h17 h18, g₃ r hr]
  -- Memory.
  have f₂ : Frame [ivR s₀] s.mem s₂.mem := by rw [mem₂]; exact xorMem_frame _ _ _
  have fStep : Frame [ivR s₀, ⟨S s₀, 2064⟩] s.mem s₄.mem := by
    rw [mem₄]
    refine (f₂.sub fun r hr => ?_).trans (c.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨S s₀, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
  have big : Frame [ivR s₀, scrR s₀] s₀.mem s₂.mem :=
    (UPre.of_frame h.frame).trans (f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
  have blkB : bytesAt s.mem (blk s₀ k) 16 = (cblks s₀)[k]'(by simp [Spec.Cmac.blocksAt]; exact hk) :=
    hp.block (UPre.of_frame h.frame) hk
  have newSt : bytesAt s₄.mem (Iv s₀) 16 =
      Spec.Cmac.chain (ciph s₀) (st0 s₀) ((cblks s₀).take (k + 1)) := by
    rw [mem₄, c.out, cipher_bytes, hp.sched big, mem₂, xorMem_bytes _ bS, h.st, blkB,
      List.take_add_one, List.getElem?_eq_getElem (by simp [Spec.Cmac.blocksAt]; exact hk), Option.toList_some,
      Proof.Cmac.chain_append, Proof.Cmac.chain_single]
    rfl
  refine ⟨?_, ?_, ?_, r17₄, r18₄, ?_, fun r hr hv => ?_, ?_, ?_, h.frame.trans fStep, newSt⟩
  · rw [g .r14 (by decide) (by decide) (by decide), h.r14]
  · rw [g .r15 (by decide) (by decide) (by decide), h.r15]
  · rw [g .r16 (by decide) (by decide) (by decide), h.r16]
  · rw [g .r19 (by decide) (by decide) (by decide), h.r19]
  · rw [g r hr (fun e => hv (by simp [e])) (fun e => hv (by simp [e])), h.keep r hr hv]
  · rw [rd₄, c.rd, rd₂, h.rd]
  · rw [wr₄, c.wr, wr₂, h.wr]

/-! ## The loop, and the whole function -/

theorem loop_ok {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : UInv s₀ k s) :
    WP isa (.loop body (.nonzero .d .r18)) s (UInv s₀ (N s₀)) := by
  have hN := (s₀.gpr .r7).isLt
  refine WP.loop (M := isa) (body := body) (c := .nonzero .d .r18) (Q := UInv s₀ (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ UInv s₀ j t) ?_ (N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (body_ok hp hk h) fun s' h' => ?_
  have ev := eval_nonzero_ofNat' s' .r18 (k := N s₀ - (k + 1)) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hN) h'.r18
  by_cases hz : N s₀ - (k + 1) = 0
  · left
    refine ⟨by rw [ev]; simp [hz], ?_⟩
    rwa [show N s₀ = k + 1 by omega]
  · right
    refine ⟨by rw [ev]; simp [hz], N s₀ - (k + 1), by omega, k + 1, rfl, by omega, h'⟩

theorem mid_wp {s₀ : State} (hp : UPre s₀) {s₁ : State} (h : UInv s₀ 0 s₁) :
    WP isa (.ite (.zero .d .r18) (.block []) (.loop body (.nonzero .d .r18))) s₁ (UInv s₀ (N s₀)) := by
  have hN := (s₀.gpr .r7).isLt
  have ev := eval_zero_ofNat s₁ .r18 (k := N s₀ - 0) (by omega) h.r18
  rw [Nat.sub_zero] at ev
  by_cases hn : N s₀ = 0
  · refine WP.ite true (by rw [ev, hn]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact h
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact loop_ok hp (by omega) h

/-- The postcondition, but for the stack pointer. -/
def UDone (s₀ s' : State) : Prop :=
  (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.lr = s₀.lr ∧ updatePPC64LE.post s₀ s'

theorem epilogue_wp {s₀ : State} (hp : UPre s₀) {s₂ : State} (h₂ : UInv s₀ (N s₀) s₂) :
    WP isa (.block restore) s₂ (UDone s₀) := by
  have rdwr : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr]
  have hsv : Spill.Saved (S s₀) (saveG s₀) saveL s₂.mem :=
    (Spill.saveMem_saved (by decide) _ _ _).frame h₂.frame fun p hp' r hr => by
      have hb := saved_bound p hp'
      have hsub : Region.Sub ⟨S s₀ + BitVec.ofNat 64 p.2, 8⟩ (scrR s₀) := AesCbc.PPC64LE.UPre.scr_sub (by omega)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.st_scr.symm.sub_left hsub
      · exact Offset.disjoint_base _ (by omega) (by have := hp.scr_wrap; omega)
  have hall : (cblks s₀).take (N s₀) = cblks s₀ := List.take_of_length_le (by simp [Spec.Cmac.blocksAt])
  rw [restore_eq]
  refine Spill.restore_ok (b := .r19) (l := saveL) (by decide) h₂.r19 (by decide) (by decide)
    (fun p hp' => ?_) hsv fun s₃ r₃ => ?_
  · have := saved_bound p hp'
    rw [rdwr, hp.rd, hp.wr]
    exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ (by omega) (by have := hp.scr_wrap; omega))
  refine WP.cons exec_mtlr (wp_nil ⟨fun r hr => ?_, ?_, ?_⟩)
  · show s₃.gpr r = _
    have h0 : saveG s₀ r = s₀.gpr r := ite_eq_right_iff.mpr fun h => absurd h (preserved_ne_r0 r hr)
    rw [r₃.gpr_of (r := r) ?_, h0]
    by_cases hv : r ∈ vars
    · left
      simp only [vars, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · right; rw [h₂.keep r hr hv, h0]
  · show s₃.gpr .r0 = _
    rw [r₃.gpr (.r0, lrOff) (by decide)]; rfl
  · show bytesAt s₃.mem (s₀.gpr .r5) 16 = _
    rw [r₃.mem, h₂.st, hall]

theorem update_wp {s₀ : State} (h0 : updatePPC64LE.pre s₀) : WP isa update s₀ (UDone s₀) := by
  have hp := UPre.of h0
  exact WP.seq (WP.mono (prologue_wp hp) fun s₁ h₁ =>
    WP.seq (WP.mono (mid_wp hp h₁) fun _ h₂ => epilogue_wp hp h₂))

end VG.Proof.CmacAes.PPC64LE
