module

public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Search
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Search.Data
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
import VerifiedGarbage.Proof.RsaKeyGen.InitWords
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

-- separate module: its proofs build in parallel with those of `Call` and `Step`, which `Correct` and `CT` also import

/-! # The search's entry (PPC64LE)

In the frame the search allocates, the caller's `r31` is saved in word 4 and
the register arguments stored (`entrySave_ok`); then the stack arguments and
the state's first word are loaded and the rest of the words stored
(`entryLoad_ok`); then, after `mflr r0`, in the frame saving it, the search
is at the tape's start with its counted candidates (`search_start`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Search

open VG.Proof.RsaKeyGen.SearchFrame
open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Search
open VG.Spec.RsaKeyGen (primeEntropy)

/-- The frame's words the first block stores. -/
def saveValues (s : State) : List (Nat × BitVec 64) :=
  [(4, s.gpr .r31), (5, s.gpr .r3), (6, s.gpr .r4), (7, s.gpr .r5), (8, s.gpr .r6), (9, s.gpr .r7),
    (10, s.gpr .r8), (11, s.gpr .r9), (12, s.gpr .r10)]

/-- The frame's words the second block stores. -/
def loadValues (s : State) : List (Nat × BitVec 64) :=
  [(13, stackArg s 0), (14, stackArg s 1), (15, stackArg s 2), (18, stackArg s 3),
    (0, s.mem.readW (stackArg s 3) 64), (1, s.gpr .r4), (2, (s.gpr .r4 <<< 15) + s.gpr .r4), (3, 0), (16, 0)]

/-- The frame's words on entry, in the order the entry stores them. -/
abbrev entryValues (s : State) : List (Nat × BitVec 64) := saveValues s ++ loadValues s

theorem entryValues_bound (s : State) : ∀ e ∈ entryValues s, e.1 < 20 := by
  simp only [entryValues, saveValues, loadValues, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl) <;> dsimp only <;> decide

theorem add_ofNat_zero (x : Addr) : x + BitVec.ofNat 64 0 = x := BitVec.add_zero x

/-- The frame's words' base, from the stack pointer the allocation leaves. -/
theorem frame_base (x : Addr) : x - BitVec.ofNat 64 192 + 32 = x - BitVec.ofNat 64 160 :=
  (Offset.sub_ofNat_eq x (by decide : 160 ≤ 192)).symm

theorem alloc_wr {p : SearchPublic} {s : State} (h : SearchInput p s) :
    (allocated 192 s).wr = p.frame :: s.wr := by
  show (⟨s.sp - BitVec.ofNat 64 192 + 32, 192 - 32⟩ : Region) :: s.wr = (⟨p.sp - _, 160⟩ : Region) :: s.wr
  rw [frame_base, h.sp_eq]

theorem alloc_sp {p : SearchPublic} {s : State} (h : SearchInput p s) :
    (allocated 192 s).sp + BitVec.ofNat 64 32 = p.F := by
  show s.sp - BitVec.ofNat 64 192 + 32 = p.sp - _
  rw [frame_base, h.sp_eq]

theorem alloc_room {s : State} (h : stackUse ≤ s.sp.toNat) : 192 ≤ s.sp.toNat := by
  have : 192 ≤ stackUse := by decide
  omega

/-- The back chain of the search's frame and the frame's words: below the
stack pointer. -/
theorem entry_frame {p : SearchPublic} {s : State} (h : SearchInput p s) (values : List (Nat × BitVec 64))
    (hb : ∀ e ∈ values, e.1 < 20) :
    Frame [below s.sp stackUse] s.mem (writeFrame (allocated 192 s).mem p.F values) := by
  have h₁ : Frame [below s.sp stackUse] s.mem (allocated 192 s).mem :=
    Frame.write (Frame.refl _ _) (List.mem_singleton_self _) _
      (Offset.contains_below s.sp (a := 192) (b := stackUse) (by decide) (by decide) (by decide))
  refine h₁.trans ((writeFrame_frame _ p.F values hb).sub fun r hr => ?_)
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨_, List.mem_singleton_self _, h.frame_sub⟩

/-- The stack arguments' addresses, from the frame's base. -/
theorem arg_addr (sp : Addr) (k : Nat) :
    sp - BitVec.ofNat 64 160 + BitVec.ofNat 64 (256 + 8 * k) = sp + BitVec.ofNat 64 (32 + 8 * (8 + k)) := by
  rw [show 256 + 8 * k = 160 + (32 + 8 * (8 + k)) by omega, BitVec.ofNat_add, ← BitVec.add_assoc,
    BitVec.sub_add_cancel]

theorem args_contains (s : State) (k : Nat) (hk : k < 4) :
    (inArgs s).Contains (s.sp + BitVec.ofNat 64 (32 + 8 * (8 + k))) 8 := by
  have e : s.sp + BitVec.ofNat 64 (32 + 8 * (8 + k)) = stackArgAddr s 0 + BitVec.ofNat 64 (8 * k) := by
    unfold stackArgAddr
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    omega
  rw [e]
  exact Offset.contains_base _ (by omega) (by omega)

theorem input_args {p : SearchPublic} {s : State} (h : SearchInput p s) (k : Nat) (hk : k < 4) :
    InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (32 + 8 * (8 + k))) 8 :=
  ⟨inArgs s, List.mem_append_left _ (h.rd_mem (by simp [inReads])), args_contains s k hk⟩

/-- The registers the first block writes. -/
abbrev saveRegs : List Reg := [.r11, .r31]

theorem entrySave_ok {p : SearchPublic} {s : State} (h : SearchInput p s) :
    WP isa (.block entrySave) (allocated 192 s) fun t =>
      (t.gpr .r31 = p.F ∧ t.mem = writeFrame (allocated 192 s).mem p.F (saveValues s)) ∧
      Keep saveRegs (allocated 192 s) t := by
  have scr := h.frame_scr (alloc_wr h)
  have hs : ∀ d, d + 8 ≤ 160 → InRegions (allocated 192 s).wr (p.F + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.st hd
  have ea : ∀ t : State, exec (.addSp .r11 32) t = some (t.write .r11 (t.sp + BitVec.ofNat 64 32)) := by
    intro t; simp [exec]
  have hsp := alloc_sp h
  have hg : ∀ r, (allocated 192 s).gpr r = s.gpr r := fun _ => rfl
  refine WP.keep saveRegs ?_ (by decide)
  unfold entrySave writeFrame saveValues
  simp only [List.foldl_cons, List.foldl_nil]
  prun [ldf, stf, ea, hsp, hg, add_ofNat_zero, hs 32 (by decide), hs 40 (by decide), hs 48 (by decide),
    hs 56 (by decide), hs 64 (by decide), hs 72 (by decide), hs 80 (by decide), hs 88 (by decide),
    hs 96 (by decide), off]

/-- The registers the second block writes. -/
abbrev loadRegs : List Reg := [.r8, .r9, .r10, .r11, .r12]

theorem entryLoad_ok {p : SearchPublic} {s u : State} (h : SearchInput p s)
    (h31 : u.gpr .r31 = p.F) (hm : u.mem = writeFrame (allocated 192 s).mem p.F (saveValues s))
    (ku : Keep saveRegs (allocated 192 s) u) :
    WP isa (.block entryLoad) u fun t =>
      t.mem = writeFrame u.mem p.F (loadValues s) ∧ Keep loadRegs u t := by
  have hw : u.wr = p.frame :: s.wr := ku.wr.trans (alloc_wr h)
  have scr := h.frame_scr hw
  have hs : ∀ d, d + 8 ≤ 160 → InRegions u.wr (p.F + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.st hd
  have hrd : u.rd ++ u.wr = s.rd ++ (p.frame :: s.wr) := by rw [ku.rd, hw]; rfl
  have hF : p.F = s.sp - BitVec.ofNat 64 160 := by show p.sp - _ = _; rw [h.sp_eq]
  have hfr := entry_frame h (saveValues s) (by
    simp only [saveValues, List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide)
  rw [← hm] at hfr
  have ha (k : Nat) (hk : k < 4) : InRegions (u.rd ++ u.wr) (p.F + BitVec.ofNat 64 (256 + 8 * k)) 8 := by
    rw [hrd, hF, arg_addr]
    obtain ⟨r, hr, hc⟩ := input_args h k hk
    refine ⟨r, ?_, hc⟩
    rcases List.mem_append.mp hr with hr | hr
    · exact List.mem_append_left _ hr
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
  have hv (k : Nat) (hk : k < 4) : u.mem.readW (p.F + BitVec.ofNat 64 (256 + 8 * k)) 64 = stackArg s k := by
    rw [hF, arg_addr]
    refine hfr.readW (r := inArgs s) (args_contains s k hk) (fun r hr => ?_) (by decide)
    · obtain rfl := List.mem_singleton.mp hr
      exact (h.stack_disjoint (List.mem_append_right _ (by simp [inReads]))).symm
  have hst : InRegions (u.rd ++ u.wr) (stackArg s 3 + BitVec.ofNat 64 0) 8 := by
    rw [hrd, add_ofNat_zero]
    refine ⟨inState s, List.mem_append_right _ (List.mem_cons_of_mem _ ?_), ?_⟩
    · rw [h.wr_eq]; simp [inWrites]
    · simp only [inState, Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]
      decide
  have hw0 : u.mem.readW (stackArg s 3 + BitVec.ofNat 64 0) 64 = s.mem.readW (stackArg s 3) 64 := by
    rw [add_ofNat_zero]
    refine hfr.readW (r := inState s) ?_ (fun r hr => ?_) (by decide)
    · simp only [inState, Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]
      decide
    · obtain rfl := List.mem_singleton.mp hr
      exact (h.stack_disjoint (List.mem_append_left _ (by simp [inWrites]))).symm
  have a0 := ha 0 (by decide)
  have a1 := ha 1 (by decide)
  have a2 := ha 2 (by decide)
  have a3 := ha 3 (by decide)
  have v0 := hv 0 (by decide)
  have v1 := hv 1 (by decide)
  have v2 := hv 2 (by decide)
  have v3 := hv 3 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd] at a0 a1 a2 a3 v0 v1 v2 v3
  have h4 : u.gpr .r4 = s.gpr .r4 := ku.gpr .r4 (by decide)
  refine WP.keep loadRegs ?_ (by decide)
  unfold entryLoad writeFrame loadValues
  simp only [List.foldl_cons, List.foldl_nil]
  prun [ldf, stf, h31, h4, a0, a1, a2, a3, v0, v1, v2, v3, hst, hw0, hs 104 (by decide), hs 112 (by decide),
    hs 120 (by decide), hs 144 (by decide), hs 0 (by decide), hs 8 (by decide), hs 16 (by decide),
    hs 24 (by decide), hs 128 (by decide), off]
  rfl

theorem sp_240 (x : Addr) : x - BitVec.ofNat 64 192 - 48 = x - BitVec.ofNat 64 160 - 80 := by
  rw [BitVec.sub_sub, BitVec.sub_sub]; rfl

theorem sp_208 (x : Addr) : x - BitVec.ofNat 64 192 - 48 + 32 = x - BitVec.ofNat 64 208 := by
  rw [BitVec.sub_sub, Offset.sub_ofNat_eq x (show 208 ≤ 240 by decide)]; rfl

/-- The push of the frame saving the link register writes only below the
search's frame. -/
theorem push_frame {s : State} {x : Addr}
    (hx : x = s.sp - BitVec.ofNat 64 192) (m : Mem) (v w : BitVec 64) :
    Frame (SearchInput.callChanges s) m ((m.write (x - 48) 8 v).write (x - 48 + 32) 8 w) := by
  have hr : (⟨s.sp - BitVec.ofNat 64 stackUse, 576⟩ : Region) ∈ SearchInput.callChanges s := by
    simp [SearchInput.callChanges]
  refine Frame.write (Frame.write (Frame.refl _ _) hr _ ?_) hr _ ?_
  · rw [hx, sp_240, BitVec.sub_sub]
    exact Offset.contains_below s.sp (a := 240) (b := stackUse) (by decide) (by decide) (by decide)
  · rw [hx, sp_208]
    exact Offset.contains_below s.sp (a := 208) (b := stackUse) (by decide) (by decide) (by decide)

/-- The registers the entry and `mflr r0` write. -/
abbrev entryRegs : List Reg := saveRegs ++ loadRegs ++ [.r0]

theorem search_start {p : SearchPublic} {s t : State} (h : SearchInput p s)
    (hx : t.gpr .r31 = p.F) (hm : t.mem = writeFrame (allocated 192 s).mem p.F (entryValues s))
    (k : Keep entryRegs (allocated 192 s) t) (hy : t.syms = s.syms) :
    SearchLive p s 0 p.remaining (framed .r0 t) := by
  have hb := entryValues_bound s
  have hf₁ : Frame (SearchInput.changes s) s.mem t.mem := by
    rw [hm]
    exact (entry_frame h _ hb).sub fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, by simp [SearchInput.changes], fun _ hi => hi⟩
  have htsp : t.sp = s.sp - BitVec.ofNat 64 192 := k.sp
  have hp := push_frame htsp t.mem t.sp (t.gpr .r0)
  have hf₂ : Frame (SearchInput.changes s) s.mem (framed .r0 t).mem :=
    hf₁.trans (frame_of_callChanges s hp)
  have hc (j : Nat) (hj : j < 20) : word (framed .r0 t).mem p.F (8 * j) = word t.mem p.F (8 * j) :=
    h.frame_words hp j hj
  have hw (j : Nat) (hj : j < 20) : word (framed .r0 t).mem p.F (8 * j) =
      frameValue (entryValues s) j (word (allocated 192 s).mem p.F (8 * j)) := by
    rw [hc j hj, hm]; exact writeFrame_word _ _ _ hb j hj
  have hL : p.len ≤ 512 := by rw [← h.2]; exact h.base.2.2.2.2.2.2.2.2.1.2.1
  have hx4 : s.gpr .r4 = BitVec.ofNat 64 p.len := by
    rw [← h.2]; exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _) |>.symm
  have hcap : (s.gpr .r4 <<< 15) + s.gpr .r4 = BitVec.ofNat 64 (primeEntropy p.len) := by
    rw [hx4, SearchInit.shl_ofNat _ _ (by omega), SearchInit.add_ofNat]
    unfold primeEntropy; congr 1; omega
  refine ⟨h, Nat.zero_le _, Nat.le_refl _, k.rd, k.wr.trans (alloc_wr h), ?_, hx, ?_, hy, ?_, ?_, ?_, ?_, hf₂, ?_⟩
  · show t.sp - 48 = p.sp - BitVec.ofNat 64 160 - 80
    rw [htsp, h.sp_eq, sp_240]
  · intro r hr h31
    exact k.gpr r (by revert r hr h31; decide)
  · rw [show (32 : Nat) = 8 * 4 from rfl, hw 4 (by decide)]
    rfl
  · rw [h.random_frame hf₂]; rw [← h.2]; rfl
  · rw [h.e_frame hf₂]; rw [← h.2]; rfl
  · rw [h.p_frame hf₂]; rw [← h.2]; rfl
  · intro e he
    rw [hw e.1 (SearchPublic.headers_bound _ _ _ e he)]
    rw [← h.2] at he hcap hx4 ⊢
    simp only [SearchPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;>
      simp only [frameValue, entryValues, saveValues, loadValues, List.cons_append, List.nil_append,
        List.foldl_cons, List.foldl_nil, searchOfState, searchRemaining,
        searchLen, BitVec.ofNat_toNat, BitVec.setWidth_eq, hcap, BitVec.add_zero, Nat.sub_zero,
        Nat.mul_div_cancel _ (show 0 < 8 by decide)] <;>
      rfl

end VG.Proof.RsaKeyGen.PPC64LE.Search
