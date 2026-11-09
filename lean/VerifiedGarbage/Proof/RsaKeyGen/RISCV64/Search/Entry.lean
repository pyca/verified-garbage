module

public import VerifiedGarbage.Impl.RsaKeyGen.RISCV64.Search
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Search.Data
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
import VerifiedGarbage.Proof.RsaKeyGen.InitWords
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

-- separate module: its proofs build in parallel with those of `Call` and `Step`, which `Correct` and `CT` also import

/-! # The search's entry (RISC-V)

In the frame the search allocates, the stack arguments and the state's
first word are loaded, the caller's `s0` saved in word 4 and the arguments
and public words stored in the frame (`entry_ok`); then, in the frame saving
`ra` (`WP.frameRegAny`, for a body with any frames), the search is at the
tape's start with its counted candidates (`search_start`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Search

open VG.Proof.RsaKeyGen.SearchFrame
open VG VG.RISCV64 VG.Proof.Bignum VG.Proof.Bignum.RISCV64
open VG.Impl.RsaKeyGen.RISCV64.Search
open VG.Spec.RsaKeyGen (primeEntropy)

/-- `WP.frameReg` for a body with any frames (`sdepth`), as on PPC64LE
(`Proof/Framework/PPC64LE/CallAny.lean`). -/
theorem WP.frameRegAny {r : Reg} {main : Prog isa} {s₀ : State} {Q : State → Prop}
    (hsp : 16 ≤ s₀.sp.toNat) (hd : ∀ R ∈ s₀.wr, Region.Disjoint ⟨s₀.sp - 16, 16⟩ R)
    (hmain : WP isa main (framed r s₀) fun s₂ => Q { s₂.write r (s₀.gpr r) with sp := s₀.sp })
    (hn : sdepth main + 16 < 2 ^ 64) :
    WP isa (.frame (.push r) main (.pop r)) s₀ Q := by
  refine WP.frame hsp (WP.narrowAny (rd := s₀.rd) (wr := s₀.wr) hmain ?_ ?_ ?_ (by omega))
  · intro a n hi
    exact InRegions_append_cons.mpr (.inr hi)
  · intro a n hi
    exact InRegions_append_cons (xs := []).mpr (.inr hi)
  · intro s' hrd hwr hsp' hf hq
    have hread : s'.mem.read (s'.sp + 8) 8 = s₀.gpr r := by
      rw [hsp', show (pushed r s₀).sp = s₀.sp - 16 from rfl,
        hf.read (r := ⟨s₀.sp - 16, 16⟩) (frame_contains s₀.sp) (fun R hR => ?_) (by decide)]
      · exact read_write_self _ _ _
      · rcases List.mem_append.mp hR with hR | hR
        · exact hd R hR
        · simp only [List.mem_singleton] at hR; subst hR
          exact frame_not_below s₀.sp hn
    have e : popped r s' = { (s'.withRegions s₀.rd s₀.wr).write r (s₀.gpr r) with sp := s₀.sp } := by
      simp only [popped, hread]
      simp only [hsp', hwr, pushed, List.tail_cons, BitVec.sub_add_cancel]
      cases s'
      simp only [pushed] at hrd
      subst hrd
      rfl
    rw [e]; exact hq

/-- The frame's words on entry, in the order the entry stores them. -/
def entryValues (s : State) : List (Nat × BitVec 64) :=
  [(4, s.gpr .s0), (5, s.gpr .a0), (6, s.gpr .a1), (7, s.gpr .a2), (8, s.gpr .a3), (9, s.gpr .a4),
    (10, s.gpr .a5), (11, s.gpr .a6), (12, s.gpr .a7), (13, stackArg s 0), (14, stackArg s 1),
    (15, stackArg s 2), (18, stackArg s 3), (0, s.mem.readW (stackArg s 3) 64), (1, s.gpr .a1),
    (2, (s.gpr .a1 <<< 15) + s.gpr .a1), (3, 0), (16, 0)]

theorem entryValues_bound (s : State) : ∀ e ∈ entryValues s, e.1 < 20 := by
  simp only [entryValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl) <;> dsimp only <;> decide

/-- The stack arguments' addresses, from the frame's base. -/
theorem arg_addr (sp : Addr) (k : Nat) :
    sp - BitVec.ofNat 64 160 + BitVec.ofNat 64 (160 + 8 * k) = sp + BitVec.ofNat 64 (8 * k) := by
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem input_args {p : SearchPublic} {s : State} (h : SearchInput p s) (j : Nat) (hj : j < 4) :
    InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (8 * j)) 8 := by
  refine ⟨inArgs s, List.mem_append_left _ (h.rd_mem (by simp [inReads])), ?_⟩
  simp only [inArgs, stackArgAddr, Nat.mul_zero, BitVec.add_zero]
  exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])

/-- The registers the entry writes. -/
abbrev entryRegs : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .s0]

theorem alloc_wr {p : SearchPublic} {s : State} (h : SearchInput p s) :
    (allocd 160 s).wr = p.frame :: s.wr := by
  show _ = (⟨p.sp - _, 160⟩ : Region) :: s.wr
  rw [h.sp_eq]; rfl

theorem alloc_sp {p : SearchPublic} {s : State} (h : SearchInput p s) : (allocd 160 s).sp = p.F := by
  show _ = p.sp - _
  rw [h.sp_eq]; rfl

theorem entry_ok {p : SearchPublic} {s : State} (h : SearchInput p s) :
    WP isa (.block entry) (allocd 160 s) fun t =>
      ((t.gpr .s0 = p.F ∧ t.mem = writeFrame s.mem p.F (entryValues s)) ∧
      Keep entryRegs (allocd 160 s) t) ∧ t.sp = p.F := by
  have scr := h.frame_scr (alloc_wr h)
  have hsp := alloc_sp h
  have hF : p.F = s.sp - BitVec.ofNat 64 160 := by show p.sp - _ = _; rw [h.sp_eq]
  have hrd : (allocd 160 s).rd ++ (allocd 160 s).wr = s.rd ++ (p.frame :: s.wr) := by
    rw [← alloc_wr h]; rfl
  have ha (k : Nat) (hk : k < 4) :
      InRegions ((allocd 160 s).rd ++ (allocd 160 s).wr) (p.F + BitVec.ofNat 64 (160 + 8 * k)) 8 := by
    rw [hF, arg_addr]
    obtain ⟨r, hr, hc⟩ := input_args h k hk
    refine ⟨r, ?_, hc⟩
    rcases List.mem_append.mp hr with hr | hr
    · exact List.mem_append_left _ hr
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
  have hv (k : Nat) (hk : k < 4) :
      s.mem.readW (p.F + BitVec.ofNat 64 (160 + 8 * k)) 64 = stackArg s k := by
    rw [hF, arg_addr]; rfl
  have hal (k : Nat) (hk : k < 4) : (p.F + BitVec.ofNat 64 (160 + 8 * k)).toNat % 8 = 0 := by
    rw [hF, arg_addr]
    have h16 : s.sp.toNat % 16 = 0 := by have := h.sp16; rwa [h.sp_eq] at this
    have ht : s.sp.toNat + 32 ≤ 2 ^ 64 := by have := h.top; rwa [h.sp_eq] at this
    have e : (s.sp + BitVec.ofNat 64 (8 * k)).toNat = s.sp.toNat + 8 * k := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    rw [e]; omega
  have hst : InRegions ((allocd 160 s).rd ++ (allocd 160 s).wr) (stackArg s 3 + BitVec.ofNat 64 0) 8 := by
    rw [hrd, BitVec.add_zero]
    refine ⟨inState s, ?_, ?_⟩
    · rw [h.wr_eq]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ (by simp [inWrites]))
    · simp only [inState, Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]
      decide
  have hsal : (stackArg s 3 + BitVec.ofNat 64 0).toNat % 8 = 0 := by
    rw [BitVec.add_zero]; exact h.state_al
  have a0 := ha 0 (by decide)
  have a1 := ha 1 (by decide)
  have a2 := ha 2 (by decide)
  have a3 := ha 3 (by decide)
  have v0 := hv 0 (by decide)
  have v1 := hv 1 (by decide)
  have v2 := hv 2 (by decide)
  have v3 := hv 3 (by decide)
  have l0 := hal 0 (by decide)
  have l1 := hal 1 (by decide)
  have l2 := hal 2 (by decide)
  have l3 := hal 3 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd] at a0 a1 a2 a3 v0 v1 v2 v3 l0 l1 l2 l3
  have hmem : (allocd 160 s).mem = s.mem := rfl
  refine WP.mono (WP.rdwr (WP.keep entryRegs ?_ (by decide +kernel))) fun t ⟨⟨hq, k⟩, _, _, hsp'⟩ =>
    ⟨⟨hq, k⟩, hsp'.trans hsp⟩
  have ea : ∀ t : State, exec (.addSp .t6 0) t = some (t.write .t6 (t.sp + BitVec.ofNat 64 0)) := by
    intro t; simp [exec]
  have hz : p.F + BitVec.ofNat 64 0 = p.F := BitVec.add_zero _
  have hs0 : InRegions (allocd 160 s).wr p.F 8 := by
    have := scr.st (d := 0) (n := 8) (by decide); simpa only [off, hz] using this
  have hl0 : p.F.toNat % 8 = 0 := by
    have := scr.al8 (d := 0) (by decide) (by decide); simpa only [off, hz] using this
  unfold entry writeFrame entryValues
  simp only [List.foldl_cons, List.foldl_nil]
  brun [stf, ea, hsp, hz, hs0, hl0, hmem, exec_li, a0, a1, a2, a3, v0, v1, v2, v3, l0, l1, l2, l3, hst, hsal,
    scr.st (d := 0) (n := 8) (by decide), scr.al8 (d := 0) (by decide) (by decide), scr.st (d := 8) (n := 8) (by decide), scr.al8 (d := 8) (by decide) (by decide), scr.st (d := 16) (n := 8) (by decide), scr.al8 (d := 16) (by decide) (by decide), scr.st (d := 24) (n := 8) (by decide), scr.al8 (d := 24) (by decide) (by decide), scr.st (d := 32) (n := 8) (by decide), scr.al8 (d := 32) (by decide) (by decide), scr.st (d := 40) (n := 8) (by decide), scr.al8 (d := 40) (by decide) (by decide), scr.st (d := 48) (n := 8) (by decide), scr.al8 (d := 48) (by decide) (by decide), scr.st (d := 56) (n := 8) (by decide), scr.al8 (d := 56) (by decide) (by decide), scr.st (d := 64) (n := 8) (by decide), scr.al8 (d := 64) (by decide) (by decide), scr.st (d := 72) (n := 8) (by decide), scr.al8 (d := 72) (by decide) (by decide), scr.st (d := 80) (n := 8) (by decide), scr.al8 (d := 80) (by decide) (by decide), scr.st (d := 88) (n := 8) (by decide), scr.al8 (d := 88) (by decide) (by decide), scr.st (d := 96) (n := 8) (by decide), scr.al8 (d := 96) (by decide) (by decide), scr.st (d := 104) (n := 8) (by decide), scr.al8 (d := 104) (by decide) (by decide), scr.st (d := 112) (n := 8) (by decide), scr.al8 (d := 112) (by decide) (by decide), scr.st (d := 120) (n := 8) (by decide), scr.al8 (d := 120) (by decide) (by decide), scr.st (d := 128) (n := 8) (by decide), scr.al8 (d := 128) (by decide) (by decide), scr.st (d := 144) (n := 8) (by decide), scr.al8 (d := 144) (by decide) (by decide), off]
  simp only [BitVec.add_zero]
  rfl

theorem F_16_8 (p : SearchPublic) : p.F - 16 + 8 = p.sp - BitVec.ofNat 64 168 := by
  rw [SearchPublic.F, BitVec.sub_sub, Offset.sub_ofNat_eq p.sp (show 168 ≤ 176 by decide)]; rfl

/-- The push of `ra` writes only below the frame. -/
theorem push_frame {p : SearchPublic} {s : State} (h : SearchInput p s) (m : Mem) (v : BitVec 64) :
    Frame (SearchInput.callChanges s) m (m.write (p.F - 16 + 8) 8 v) := by
  refine Frame.write (Frame.refl _ _) (r := ⟨s.sp - BitVec.ofNat 64 stackUse, 336⟩)
    (by simp [SearchInput.callChanges]) _ ?_
  rw [F_16_8, h.sp_eq]
  exact Offset.contains_below s.sp (a := 168) (b := 496) (by decide) (by decide) (by decide)

theorem search_start {p : SearchPublic} {s t : State} (h : SearchInput p s)
    (hx : t.gpr .s0 = p.F) (hm : t.mem = writeFrame s.mem p.F (entryValues s))
    (k : Keep entryRegs (allocd 160 s) t) (htsp : t.sp = p.F) (hy : t.syms = s.syms) :
    SearchLive p s 0 p.remaining (framed .ra t) := by
  have hb := entryValues_bound s
  have hf₁ : Frame (SearchInput.changes s) s.mem t.mem := by
    rw [hm]
    apply (writeFrame_frame s.mem p.F _ hb).sub
    intro region hregion
    obtain rfl := List.mem_singleton.mp hregion
    exact ⟨_, by simp [SearchInput.changes], h.frame_sub⟩
  have hp := push_frame h t.mem (t.gpr .ra)
  rw [← htsp] at hp
  have hf₂ : Frame (SearchInput.changes s) s.mem (framed .ra t).mem :=
    hf₁.trans (frame_of_callChanges s hp)
  have hc (j : Nat) (hj : j < 20) : word (framed .ra t).mem p.F (8 * j) = word t.mem p.F (8 * j) :=
    h.frame_words hp j hj
  have hw (j : Nat) (hj : j < 20) :
      word (framed .ra t).mem p.F (8 * j) = frameValue (entryValues s) j (word s.mem p.F (8 * j)) := by
    rw [hc j hj, hm]; exact writeFrame_word _ _ _ hb j hj
  have hL : p.len ≤ 512 := by rw [← h.2]; exact h.base.2.2.2.2.2.2.2.2.2.1.2.1
  have hx1 : s.gpr .a1 = BitVec.ofNat 64 p.len := by
    rw [← h.2]; exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _) |>.symm
  have hcap : (s.gpr .a1 <<< 15) + s.gpr .a1 = BitVec.ofNat 64 (primeEntropy p.len) := by
    rw [hx1, SearchInit.shl_ofNat _ _ (by omega), SearchInit.add_ofNat]
    unfold primeEntropy; congr 1; omega
  refine ⟨h, Nat.zero_le _, Nat.le_refl _, k.2.1, k.2.2.trans (alloc_wr h), ?_, hx, ?_, hy, ?_, ?_, ?_, ?_,
    hf₂, ?_⟩
  · show t.sp - 16 = p.F - 16
    rw [htsp]
  · intro r hr h0
    exact k.gpr (by revert r hr h0; decide)
  · rw [show (32 : Nat) = 8 * 4 from rfl, hw 4 (by decide)]
    rfl
  · rw [h.random_frame hf₂]; rw [← h.2]; rfl
  · rw [h.e_frame hf₂]; rw [← h.2]; rfl
  · rw [h.p_frame hf₂]; rw [← h.2]; rfl
  · intro e he
    rw [hw e.1 (SearchPublic.headers_bound _ _ _ e he)]
    rw [← h.2] at he hcap hx1 ⊢
    simp only [SearchPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;>
      simp only [frameValue, entryValues, List.foldl_cons, List.foldl_nil, searchOfState, searchRemaining,
        searchLen, BitVec.ofNat_toNat, BitVec.setWidth_eq, hcap, BitVec.add_zero, Nat.sub_zero,
        Nat.mul_div_cancel _ (show 0 < 8 by decide)] <;>
      rfl

end VG.Proof.RsaKeyGen.RISCV64.Search
