module

public import VerifiedGarbage.Impl.RsaKeyGen.AArch64.Search
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.Data
import VerifiedGarbage.Proof.RsaKeyGen.InitWords
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

-- separate module: its proofs build in parallel with those of `Call` and `Step`, which `Correct` and `CT` also import

/-! # The search's entry (AArch64)

In the frame the search allocates, the stack arguments and the state's
first word are loaded, the caller's `x19` saved in word 4 and the arguments
and public words stored in the frame (`entry_ok`); then, in the frame saving
`x30`, the search is at the tape's start with its counted candidates
(`search_start`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Search

open VG.Proof.RsaKeyGen.SearchFrame
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.AArch64 (ld mov movi)
open VG.Impl.RsaKeyGen.AArch64.Search
open VG.Spec.RsaKeyGen (primeEntropy)

theorem imm64 {n : Nat} (hn : n < 65536) : (BitVec.ofNat 16 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- The frame's words on entry, in the order the entry stores them. -/
def entryValues (s : State) : List (Nat × BitVec 64) :=
  [(4, s.gpr .x19), (5, s.gpr .x0), (6, s.gpr .x1), (7, s.gpr .x2), (8, s.gpr .x3), (9, s.gpr .x4),
    (10, s.gpr .x5), (11, s.gpr .x6), (12, s.gpr .x7), (13, stackArg s 0), (14, stackArg s 1),
    (15, stackArg s 2), (18, stackArg s 3), (0, s.mem.readW (stackArg s 3) 64), (1, s.gpr .x1),
    (2, (s.gpr .x1 <<< 15) + s.gpr .x1), (3, 0), (16, 0)]

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
  refine ⟨inArgs s, ?_, ?_⟩
  · rw [h.1.2.2.1]
    exact List.mem_append_left _ (by simp [inReads])
  · simp only [inArgs, stackArgAddr, Nat.mul_zero, BitVec.add_zero]
    exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])

/-- The registers the entry writes. -/
abbrev entryRegs : List Reg := [.x8, .x9, .x10, .x11, .x12, .x13, .x14, .x19]

theorem alloc_wr {p : SearchPublic} {s : State} (h : SearchInput p s) :
    (allocated 160 s).wr = p.frame :: s.wr := by
  show _ = (⟨p.sp - _, 160⟩ : Region) :: s.wr
  rw [h.sp_eq]; rfl

theorem alloc_sp {p : SearchPublic} {s : State} (h : SearchInput p s) : (allocated 160 s).sp = p.F := by
  show _ = p.sp - _
  rw [h.sp_eq]; rfl

theorem entry_ok {p : SearchPublic} {s : State} (h : SearchInput p s) :
    WP isa (.block entry) (allocated 160 s) fun t =>
      (t.gpr .x19 = p.F ∧ t.mem = writeFrame s.mem p.F (entryValues s)) ∧
      Keep entryRegs (allocated 160 s) t := by
  have scr := h.frame_scr (alloc_wr h)
  have hs : ∀ d, d + 8 ≤ 160 → InRegions (allocated 160 s).wr (p.F + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.st hd
  have hsp := alloc_sp h
  have hF : p.F = s.sp - BitVec.ofNat 64 160 := by show p.sp - _ = _; rw [h.sp_eq]
  have hrd : (allocated 160 s).rd ++ (allocated 160 s).wr = s.rd ++ (p.frame :: s.wr) := by
    rw [← alloc_wr h]; rfl
  have ha (k : Nat) (hk : k < 4) :
      InRegions ((allocated 160 s).rd ++ (allocated 160 s).wr)
        (p.F + BitVec.ofNat 64 (160 + 8 * k)) 8 := by
    rw [hF, arg_addr]
    obtain ⟨r, hr, hc⟩ := input_args h k hk
    refine ⟨r, ?_, hc⟩
    rcases List.mem_append.mp hr with hr | hr
    · exact List.mem_append_left _ hr
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
  have hv (k : Nat) (hk : k < 4) :
      s.mem.readW (p.F + BitVec.ofNat 64 (160 + 8 * k)) 64 = stackArg s k := by
    rw [hF, arg_addr]; rfl
  have hst : InRegions ((allocated 160 s).rd ++ (allocated 160 s).wr) (stackArg s 3) 8 := by
    refine ⟨inState s, ?_, ?_⟩
    · rw [hrd, h.1.2.2.2.1]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ (by simp [inWrites]))
    · simp only [inState, Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]
      decide
  have a0 := ha 0 (by decide)
  have a1 := ha 1 (by decide)
  have a2 := ha 2 (by decide)
  have a3 := ha 3 (by decide)
  have v0 := hv 0 (by decide)
  have v1 := hv 1 (by decide)
  have v2 := hv 2 (by decide)
  have v3 := hv 3 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd] at a0 a1 a2 a3 v0 v1 v2 v3
  have hmem : (allocated 160 s).mem = s.mem := rfl
  refine WP.keep entryRegs ?_ (by decide) (by decide) (by decide +kernel)
  unfold entry writeFrame entryValues
  simp only [List.foldl_cons, List.foldl_nil]
  brun [ldf, stf, exec_addSp (show 0 < 4096 by decide), imm64 (show 0 < 65536 by decide), hsp, hmem,
    a0, a1, a2, a3, v0, v1, v2, v3, hst, BitVec.add_zero,
    hs 32 (by decide), hs 40 (by decide), hs 48 (by decide), hs 56 (by decide), hs 64 (by decide),
    hs 72 (by decide), hs 80 (by decide), hs 88 (by decide), hs 96 (by decide), hs 104 (by decide),
    hs 112 (by decide), hs 120 (by decide), hs 144 (by decide), hs 0 (by decide), hs 8 (by decide),
    hs 16 (by decide), hs 24 (by decide), hs 128 (by decide)]
  rfl

/-- The state the body of the frame saving `x30` starts in (`WP.frameReg`). -/
abbrev pushedX30 (t : State) : State :=
  { t with sp := t.sp - 16, mem := t.mem.write (t.sp - 16) 8 (t.gpr .x30) }

theorem F_16 (p : SearchPublic) : p.F - 16 = p.sp - BitVec.ofNat 64 176 := by
  rw [SearchPublic.F, BitVec.sub_sub]; rfl

/-- The push of `x30` writes only below the frame. -/
theorem push_frame {p : SearchPublic} {s : State} (h : SearchInput p s) (m : Mem) (v : BitVec 64) :
    Frame (SearchInput.callChanges s) m (m.write (p.F - 16) 8 v) := by
  refine Frame.write (Frame.refl _ _) (r := ⟨s.sp - BitVec.ofNat 64 stackUse, 48⟩)
    (by simp [SearchInput.callChanges]) _ ?_
  rw [F_16, h.sp_eq]
  exact Offset.contains_below s.sp (a := 176) (b := 208) (by decide) (by decide) (by decide)

theorem search_start {p : SearchPublic} {s t : State} (h : SearchInput p s)
    (hx : t.gpr .x19 = p.F) (hm : t.mem = writeFrame s.mem p.F (entryValues s))
    (k : Keep entryRegs (allocated 160 s) t) :
    SearchLive p s 0 p.remaining (pushedX30 t) := by
  have hb := entryValues_bound s
  have hf₁ : Frame (SearchInput.changes s) s.mem t.mem := by
    rw [hm]
    apply (writeFrame_frame s.mem p.F _ hb).sub
    intro region hregion
    obtain rfl := List.mem_singleton.mp hregion
    exact ⟨_, by simp [SearchInput.changes], h.frame_sub⟩
  have htsp : t.sp = p.F := k.sp.trans (alloc_sp h)
  have hp := push_frame h t.mem (t.gpr .x30)
  rw [← htsp] at hp
  have hf₂ : Frame (SearchInput.changes s) s.mem (pushedX30 t).mem :=
    hf₁.trans (frame_of_callChanges s hp)
  have hc (j : Nat) (hj : j < 20) : word (pushedX30 t).mem p.F (8 * j) = word t.mem p.F (8 * j) :=
    h.frame_words hp j hj
  have hw (j : Nat) (hj : j < 20) :
      word (pushedX30 t).mem p.F (8 * j) = frameValue (entryValues s) j (word s.mem p.F (8 * j)) := by
    rw [hc j hj, hm]; exact writeFrame_word _ _ _ hb j hj
  have hL : p.len ≤ 512 := by rw [← h.2]; exact h.1.2.2.2.2.2.2.2.2.1.2.1
  have hx1 : s.gpr .x1 = BitVec.ofNat 64 p.len := by
    rw [← h.2]; exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _) |>.symm
  have hcap : (s.gpr .x1 <<< 15) + s.gpr .x1 = BitVec.ofNat 64 (primeEntropy p.len) := by
    rw [hx1, SearchInit.shl_ofNat _ _ (by omega), SearchInit.add_ofNat]
    unfold primeEntropy; congr 1; omega
  refine ⟨h, Nat.zero_le _, Nat.le_refl _, k.rd, k.wr.trans (alloc_wr h), ?_, hx, ?_, k.vcs, ?_, ?_, ?_,
    ?_, ?_⟩
  · show t.sp - 16 = p.F - 16
    rw [htsp]
  · intro r hr h19 _
    exact k.gpr r (by revert r hr h19; decide)
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

end VG.Proof.RsaKeyGen.AArch64.Search
