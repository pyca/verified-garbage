module

public import VerifiedGarbage.Impl.RsaKeyGen.AArch64.Search
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.Data
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Base
import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Init
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset

-- separate module: it builds in parallel with `Classify` and `Loop`, which `Correct` also imports

/-! # The RSA prime search's entry (AArch64)

In the search's frame, the stack arguments are loaded, the caller's `x19`
saved in word 4, the arguments and the public words stored; then, in the
frame saving `x30`, the search is at the tape's start with its counted
candidates (`search_start`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Search

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Ffdh.AArch64 (Slots)
open VG.Proof.Ffdh.Control (writeController controllerValue)
open VG.Proof.Ffdh.AArch64.Generation (imm64 shift_ofNat)
open VG.Impl.RsaKeyGen.AArch64.Search
open VG.Spec.RsaKeyGen (primeEntropy)

/-- The frame's words the entry stores, in order. -/
def entryValues (s : State) : List (Nat × BitVec 64) :=
  (4, s.gpr .x19) :: ([(5, s.gpr .x0), (6, s.gpr .x1), (7, s.gpr .x2), (8, s.gpr .x3), (9, s.gpr .x4),
    (10, s.gpr .x7), (11, stackArg s 0), (13, stackArg s 1), (15, stackArg s 2), (16, s.gpr .x5),
    (17, s.gpr .x6), (18, stackArg s 3), (0, s.mem.readW (stackArg s 3) 64), (1, s.gpr .x1)] ++
    [(2, s.gpr .x1 <<< 15 + s.gpr .x1), (3, 0), (12, 0)])

theorem entryValues_bound (s : State) : ∀ e ∈ entryValues s, e.1 < 20 := by
  simp only [entryValues, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl) <;> dsimp only <;> decide

/-! ## Stores of the frame's words -/

theorem stf_exec {s : State} {F : Addr} {r : Reg} {j : Nat} (hx : s.gpr .x19 = F) (hj : j < 20)
    (hst : InRegions s.wr (F + BitVec.ofNat 64 (8 * j)) 8) :
    isa.exec (stf r j) s = some { s with mem := s.mem.writeW (off F (8 * j)) (s.gpr r) } := by
  have h1 : 8 * j % 8 = 0 := by omega
  have h2 : 8 * j < 4096 * 8 := by omega
  simp only [stf, isa, exec, addr, h1, h2, and_self, ite_true, Option.bind_some, State.store, hx, hst,
    State.read, Size.bytes, Size.bits, BitVec.setWidth_eq, off]
  rfl

/-- Stores of registers to the frame's words. -/
theorem stores_ok {F : Addr} (L : List (Reg × Nat)) {s : State} (hx : s.gpr .x19 = F)
    (hL : ∀ e ∈ L, e.2 < 20) (hst : ∀ d, d + 8 ≤ 160 → InRegions s.wr (F + BitVec.ofNat 64 d) 8) :
    WP isa (.block (L.map fun e => stf e.1 e.2)) s fun t =>
      t = { s with mem := writeController s.mem F (L.map fun e => (e.2, s.gpr e.1)) } := by
  induction L generalizing s with
  | nil => exact WP.block_nil (by cases s; rfl)
  | cons e L ih =>
    have he := hL e (List.mem_cons_self ..)
    refine WP.block_cons_iff.mpr ⟨_, stf_exec hx he (hst _ (by omega)), ?_⟩
    exact ih (s := { s with mem := s.mem.writeW (off F (8 * e.2)) (s.gpr e.1) }) hx
      (fun x hx => hL x (List.mem_cons_of_mem _ hx)) hst

theorem input_args {p : SPub} {s : State} (h : SInput p s) (j : Nat) (hj : j < 4) :
    InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (8 * j)) 8 := by
  refine ⟨inArgs s, ?_, ?_⟩
  · rw [h.1.2.2.1]
    exact List.mem_append_left _ (by simp [inReads])
  · simp only [inArgs, stackArgAddr, Nat.mul_zero, BitVec.add_zero]
    exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])

theorem input_state {p : SPub} {s : State} (h : SInput p s) :
    InRegions (s.rd ++ s.wr) (stackArg s 3) 8 := by
  refine ⟨inState s, ?_, ?_⟩
  · rw [h.1.2.2.2.1]
    exact List.mem_append_right _ (by simp [inWrites])
  · simpa only [inState, BitVec.add_zero] using
      Offset.contains_base (stackArg s 3) (d := 0) (n := 8) (k := 32) (by decide) (by decide)

/-- The registers the entry writes. -/
abbrev entryRegs : List Reg := [.x8, .x9, .x10, .x11, .x12, .x13, .x14, .x19]

theorem F_eq {p : SPub} {s : State} (h : SInput p s) :
    (allocated frameBytes s).sp = p.F := by
  show s.sp - BitVec.ofNat 64 160 = _; rw [← h.sp_eq]

/-- The head: the loads, the caller's `x19` saved and the frame's base. -/
theorem entryHead_ok {p : SPub} {s : State} (h : SInput p s) :
    WP isa (.block entryHead) (allocated frameBytes s) fun t =>
      (t.gpr .x9 = stackArg s 0 ∧ t.gpr .x10 = stackArg s 1 ∧ t.gpr .x11 = stackArg s 2 ∧
        t.gpr .x12 = stackArg s 3 ∧ t.gpr .x13 = s.mem.readW (stackArg s 3) 64 ∧ t.gpr .x19 = p.F ∧
        t.mem = s.mem.writeW (off p.F (8 * 4)) (s.gpr .x19)) ∧
      Keep entryRegs (allocated frameBytes s) t := by
  have scr := h.frame_scr (t := allocated frameBytes s) (by
    show (⟨s.sp - BitVec.ofNat 64 160, 160⟩ :: s.wr) = _; rw [← h.sp_eq])
  have hs : InRegions (allocated frameBytes s).wr (p.F + BitVec.ofNat 64 32) 8 := scr.st (by decide)
  have hsp : s.sp - BitVec.ofNat 64 160 + BitVec.ofNat 64 160 = s.sp := BitVec.sub_add_cancel _ _
  have hwid (a : Addr) (n : Nat) (ha : InRegions (s.rd ++ s.wr) a n) :
      InRegions ((allocated frameBytes s).rd ++ (allocated frameBytes s).wr) a n := by
    obtain ⟨r, hr, hc⟩ := ha
    refine ⟨r, ?_, hc⟩
    rcases List.mem_append.mp hr with hr | hr
    · exact List.mem_append_left _ hr
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
  have ha0 : InRegions ((allocated frameBytes s).rd ++ (allocated frameBytes s).wr) s.sp 8 :=
    hwid _ _ (by simpa only [Nat.mul_zero, BitVec.add_zero] using input_args h 0 (by decide))
  have ha1 := hwid _ _ (input_args h 1 (by decide))
  have ha2 := hwid _ _ (input_args h 2 (by decide))
  have ha3 := hwid _ _ (input_args h 3 (by decide))
  have hst := hwid _ _ (input_state h)
  simp only [stackArg, stackArgAddr] at hst
  have hFp : p.F = s.sp - BitVec.ofNat 64 160 := by rw [← h.sp_eq]
  refine WP.keep entryRegs ?_ (by decide) (by decide) (by decide +kernel)
  unfold entryHead
  simp only [frameBytes, allocated] at hs ha0 ha1 ha2 ha3 hst ⊢
  rw [hFp] at hs ⊢
  brun [exec_addSp (show 160 < 4096 by decide), exec_addSp (show 0 < 4096 by decide), hsp,
    ha0, ha1, ha2, ha3, hst, hs]
  simp only [stackArg, stackArgAddr, Nat.mul_zero, BitVec.add_zero, Nat.reduceMul, and_self]

theorem entry_ok {p : SPub} {s : State} (h : SInput p s) :
    WP isa (.block entry) (allocated frameBytes s) fun t =>
      (t.gpr .x19 = p.F ∧ t.mem = writeController s.mem p.F (entryValues s)) ∧
      Keep entryRegs (allocated frameBytes s) t := by
  have scr := h.frame_scr (t := allocated frameBytes s) (by
    show (⟨s.sp - BitVec.ofNat 64 160, 160⟩ :: s.wr) = _; rw [← h.sp_eq])
  unfold entry
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (entryHead_ok h) fun u ⟨⟨h9, h10, h11, h12, h13, h19, hm⟩, k⟩ => ?_
  have scu := scr.congr k.wr
  refine WP.mono (stores_ok entryStores h19 (by decide) fun d hd => scu.st hd) fun v hv => ?_
  subst hv
  have hst : ∀ d, d + 8 ≤ 160 → InRegions u.wr (p.F + BitVec.ofNat 64 d) 8 := fun d hd => scu.st hd
  have hu1 : u.gpr .x1 = s.gpr .x1 := k.gpr .x1 (by decide)
  refine WP.mono (WP.keep [.x13] (Q := fun t => t.gpr .x19 = p.F ∧
      t.mem = writeController (writeController u.mem p.F (entryStores.map fun e => (e.2, u.gpr e.1))) p.F
        [(2, s.gpr .x1 <<< 15 + s.gpr .x1), (3, 0), (12, 0)]) ?_ (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨ht19, htm⟩, kt⟩ => ⟨⟨ht19, ?_⟩, ?_⟩
  · unfold entryWords writeController
    simp only [List.foldl_cons, List.foldl_nil]
    brun [stf, h19, hu1, imm64 (show 0 < 65536 by decide), hst 16 (by decide), hst 24 (by decide),
      hst 96 (by decide)]
    simp only [off, Nat.reduceMul]
    rfl
  · rw [htm, hm]
    unfold entryValues
    simp only [entryStores, List.map_cons, List.map_nil, writeController, List.foldl_cons, List.foldl_nil,
      List.cons_append, List.nil_append, h9, h10, h11, h12, h13,
      k.gpr .x0 (by decide), k.gpr .x1 (by decide), k.gpr .x2 (by decide), k.gpr .x3 (by decide),
      k.gpr .x4 (by decide), k.gpr .x5 (by decide), k.gpr .x6 (by decide), k.gpr .x7 (by decide)]
    rfl
  · have kv : Keep [] u { u with mem := writeController u.mem p.F (entryStores.map fun e => (e.2, u.gpr e.1)) } :=
      ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
    exact ((k.trans kv).trans kt).mono (by decide)

/-- The state the body of the frame saving `x30` starts in (`WP.frameReg`). -/
abbrev pushedX30 (t : State) : State :=
  { t with sp := t.sp - 16, mem := t.mem.write (t.sp - 16) 8 (t.gpr .x30) }

private theorem word_zero (m : Mem) (B : Addr) : word m B 0 = m.readW B 64 := by
  simp only [Bignum.word, off, BitVec.add_zero]

theorem entropy_word (L : Nat) :
    BitVec.ofNat 64 L <<< 15 + BitVec.ofNat 64 L = BitVec.ofNat 64 (primeEntropy L) := by
  rw [shift_ofNat, ← BitVec.ofNat_add]; unfold primeEntropy; congr 1; omega

theorem SInput.len_le {p : SPub} {s : State} (h : SInput p s) : p.len ≤ 512 := by
  rw [← h.2]; have := h.1.2.2.2.2.2.2.2.2.1; unfold Spec.RsaKeyGen.primeLenValid at this; exact this.2.1

theorem entry_headers {p : SPub} {s : State} (h : SInput p s) :
    Slots (writeController s.mem p.F (entryValues s)) p.F (p.headers 0 p.remaining) := by
  have hL := h.len_le
  cases h.2
  intro e he
  simp only [SPub.headers, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [frame_word _ _ _ (entryValues_bound s) _ (by dsimp only; decide)] <;>
    simp only [sOfState, controllerValue, entryValues, List.cons_append, List.nil_append,
      List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff, ite_true, ite_false,
      Nat.sub_zero, Nat.mul_zero, BitVec.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      Nat.mul_div_cancel _ (by decide : 0 < 8), searchRemaining, searchLen]
  · have := entropy_word (s.gpr .x1).toNat
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
    exact this
  all_goals rfl

/-- The push of `x30` writes only below the frame. -/
theorem push_frame {p : SPub} {s : State} (h : SInput p s) (m : Mem) (v : BitVec 64) :
    Frame (SInput.callChanges s) m (m.write (p.F - 16) 8 v) := by
  refine Frame.write (Frame.refl _ _) (r := ⟨s.sp - BitVec.ofNat 64 stackUse, 48⟩)
    (by simp [SInput.callChanges]) _ ?_
  rw [← h.sp_eq]
  have e : p.F - 16 = p.sp - BitVec.ofNat 64 176 := by rw [SPub.F, BitVec.sub_sub]; rfl
  rw [e]
  exact Offset.contains_below p.sp (a := 176) (b := 208) (by decide) (by decide) (by decide)

theorem search_start {p : SPub} {s t : State} (h : SInput p s)
    (hx : t.gpr .x19 = p.F) (hm : t.mem = writeController s.mem p.F (entryValues s))
    (k : Keep entryRegs (allocated frameBytes s) t) :
    SLive p s 0 p.remaining (pushedX30 t) := by
  have hf₁ : Frame (SInput.changes s) s.mem t.mem := by
    rw [hm]
    exact (frame_frame s.mem p.F (entryValues s) (entryValues_bound s)).sub fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, by simp [SInput.changes], h.frame_sub⟩
  have htsp : t.sp = p.F := by rw [k.sp]; exact F_eq h
  have hp := push_frame h t.mem (t.gpr .x30)
  rw [← htsp] at hp
  have hf₂ : Frame (SInput.changes s) s.mem (pushedX30 t).mem :=
    hf₁.trans (frame_of_callChanges s hp)
  have hc (j : Nat) (hj : j < 20) : word (pushedX30 t).mem p.F (8 * j) = word t.mem p.F (8 * j) :=
    h.frame_words hp j hj
  refine ⟨h, Nat.zero_le _, Nat.le_refl _, k.rd, ?_, ?_, hx, ?_, k.vcs, ?_, ?_, ?_, ?_, ?_⟩
  · rw [k.wr]; show (⟨s.sp - BitVec.ofNat 64 160, 160⟩ :: s.wr) = _; rw [← h.sp_eq]
  · show t.sp - 16 = p.F - 16; rw [htsp]
  · intro r hr h19 _
    exact k.gpr r (by revert r hr h19; decide)
  · rw [show (32 : Nat) = 8 * 4 from rfl, hc 4 (by decide), hm,
      frame_word _ _ _ (entryValues_bound s) 4 (by decide)]
    rfl
  · rw [h.random_frame hf₂]; cases h.2; rfl
  · rw [h.e_frame hf₂]; cases h.2; rfl
  · rw [h.p_frame hf₂]; cases h.2; rfl
  · intro e he
    rw [hc e.1 (SPub.headers_index he), hm]
    exact entry_headers h e he

end VG.Proof.RsaKeyGen.AArch64.Search
