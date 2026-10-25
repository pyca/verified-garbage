module

public import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Steps
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Entry
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # The attempt's frame of arguments (x86)

The attempt allocates 44 bytes below the entry's stack pointer and stores
`vg_ffdh_generate_key`'s eleven arguments there (`arguments_ok`). With the
call's return address and the callee's 172 bytes below them, they are the
220 bytes below the entry's stack pointer, at offsets of `low o`
(`low_sub`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.KeySearch

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Ffdh.X86.KeySearch
open VG.Proof.Dsa.X86 (argumentPointer)

/-- The base of the stack the controller uses. -/
abbrev low (o : State) : Addr := (o.gpr .esp).setWidth 64 - 220#64

theorem low_toNat {o : State} (A : KeySearchABI o) : (low o).toNat = (o.gpr .esp).toNat - 220 := by
  have : 220 ≤ (o.gpr .esp).toNat := A.stackLow
  have := (o.gpr .esp).isLt
  simp only [low, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_arith

/-- A stack pointer `k ≤ 220` bytes below the entry's, at its offset from `low o`. -/
theorem sw_sub {o : State} (A : KeySearchABI o) {k : Nat} (hk : k ≤ 220) :
    (o.gpr .esp - BitVec.ofNat 32 k).setWidth 64 = low o + BitVec.ofNat 64 (220 - k) := by
  have h1 : 220 ≤ (o.gpr .esp).toNat := A.stackLow
  have h2 := (o.gpr .esp).isLt
  have hl := low_toNat A
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, hl]
  omega_arith

/-- A word at `d` above a stack pointer `k` bytes below the entry's. -/
theorem addr_sub {o : State} (A : KeySearchABI o) {k d : Nat} (hk : k ≤ 220) (hd : d ≤ k) :
    addr (o.gpr .esp - BitVec.ofNat 32 k) d = low o + BitVec.ofNat 64 (220 - k + d) := by
  have h1 : 220 ≤ (o.gpr .esp).toNat := A.stackLow
  have h2 := (o.gpr .esp).isLt
  have hl := low_toNat A
  apply BitVec.eq_of_toNat_eq
  simp only [addr, BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, hl]
  omega_arith

theorem lowR_eq {o : State} : lowR o = ⟨low o, 220⟩ := rfl

/-- A range at offsets of `low o` lies in the stack the controller uses. -/
theorem low_sub {o : State} {d n : Nat} (h : d + n ≤ 220) : Region.Sub ⟨low o + BitVec.ofNat 64 d, n⟩ (lowR o) :=
  Offset.sub_base _ h

theorem low_contains {o : State} (A : KeySearchABI o) {d n : Nat} (h : d + n ≤ 220) :
    (lowR o).Contains (low o + BitVec.ofNat 64 d) n := by
  have : 220 ≤ (o.gpr .esp).toNat := A.stackLow
  exact Offset.contains_base _ h (by omega_arith)

/-- The frame's region. -/
abbrev frR (o : State) : Region := ⟨low o + BitVec.ofNat 64 176, 44⟩

/-- A state in the attempt's frame: `St` but for the stack pointer and the frame's region. -/
structure Fr (o : State) (ds : List Nat) (f : Nat → BitVec 32) (s : State) : Prop where
  abi : KeySearchABI o
  rd : s.rd = o.rd
  wr : s.wr = frR o :: o.wr
  esp : s.gpr .esp = o.gpr .esp - BitVec.ofNat 32 argsBytes
  esi : s.gpr .esi = arg o 12
  saved : ∀ r ∈ calleeSaved, r ≠ .esi → r ≠ .esp → s.gpr r = o.gpr r
  frame : Frame (frameR o) o.mem s.mem
  words : Ctl s.mem (arg o 12) ds f

theorem St.alloc {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) :
    Fr o ds f (allocFrame argsBytes s) := by
  refine ⟨h.abi, h.rd, ?_, by rw [allocFrame_esp, h.esp], by rw [allocFrame_gpr _ _ (by decide), h.esi],
    fun r hr hne hsp => by rw [allocFrame_gpr _ _ hsp, h.saved r hr hne], h.frame, h.words⟩
  rw [allocFrame_wr, h.esp, h.wr, sw_sub h.abi (by decide)]; rfl

/-- `vg_ffdh_generate_key`'s arguments for `used` octets consumed. -/
def callArg (o : State) (used : Nat) (j : Nat) : BitVec 32 :=
  if j = 0 then arg o 0 else
  if j = 2 then arg o 2 else
  if j = 4 then arg o 5 else
  if j = 5 then arg o 6 else
  if j = 7 then arg o 8 + BitVec.ofNat 32 used else
  if j = 9 then arg o 10 else
  if j = 10 then arg o 11 else arg o 7

/-- The first `k` arguments are in the frame. -/
def ArgsAt (o : State) (used k : Nat) (m : Mem) : Prop :=
  ∀ j < k, m.readW (low o + BitVec.ofNat 64 (176 + 4 * j)) 32 = callArg o used j

/-- `pass d j`: the state's word at `d`, argument `j`, to the frame. -/
theorem pass_ok {o s : State} {ds : List Nat} {f : Nat → BitVec 32} {used : Nat} (h : Fr o ds f s)
    (hA : Aligned ds) {d j : Nat} (hd : d ∈ ds) (hd4 : d + 4 ≤ 128) (hj : j < 11) (hv : f d = callArg o used j)
    (ha : ArgsAt o used j s.mem) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Fr o ds f t → ArgsAt o used (j + 1) t.mem → WP isa (.block rest) t Q) :
    WP isa (.block (pass d j ++ rest)) s Q := by
  have A := h.abi
  have hS := A.sBound
  show WP isa (.block (.mov .eax (.mem ⟨.esi, d⟩) :: .store ⟨.esp, 4 * j⟩ .eax :: rest)) s Q
  have rin : InRegions (s.rd ++ s.wr) (addr (arg o 12) d) 4 := by
    rw [h.rd, h.wr]; exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ (sR_mem A)), st_in A hd4⟩
  refine wp_movS (readSrc_mem h.esi rin) fun t U _ => ?_
  have ea : addr (t.gpr .esp) (4 * j) = low o + BitVec.ofNat 64 (176 + 4 * j) := by
    rw [U.other _ (by decide), h.esp, addr_sub A (by decide) (by unfold argsBytes; omega_arith)]; rfl
  have win : (frR o).Contains (low o + BitVec.ofNat 64 (176 + 4 * j)) 4 := by
    have : 220 ≤ (o.gpr .esp).toNat := A.stackLow
    exact Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)
  refine wp_storeS (show t.ea ⟨.esp, 4 * j⟩ = _ by rw [ea_mk, ea])
    (by rw [U.wr, h.wr]; exact ⟨_, List.mem_cons_self .., win⟩) fun t' M => k t' ?_ ?_
  · have lc := low_contains A (d := 176 + 4 * j) (n := 4) (by omega_arith)
    have fr : Frame [lowR o] s.mem t'.mem := by
      rw [M.mem, U.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ lc
    refine ⟨A, M.rd.trans (U.rd.trans h.rd), M.wr.trans (U.wr.trans h.wr), ?_, ?_, fun r hr hne hsp => ?_,
      h.frame.trans (fr.mono fun r hr => ?_), h.words.frame hS hA fr fun r hr => ?_⟩
    · rw [M.gpr, U.other _ (by decide), h.esp]
    · rw [M.gpr, U.other _ (by decide), h.esi]
    · rw [M.gpr, U.other _ (saved_ne (Or.inl rfl) hr), h.saved r hr hne hsp]
    · simp only [List.mem_singleton] at hr; subst hr; exact List.mem_append_right _ (List.mem_singleton_self _)
    · simp only [List.mem_singleton] at hr; subst hr; exact A.lowS.symm
  · have hl := low_toNat A
    have hb := A.stackBound
    intro i hi
    rw [M.mem, U.gpr, U.mem]
    by_cases hij : i = j
    · subst hij; rw [Mem.readW_writeW_self32, h.words.get hd, hv]
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
      exact ha i (by omega_arith)

theorem arguments_ok {o s : State} {e : BitVec 32} {used keys scalars : Nat}
    (h : Fr o liveDs (liveF (ofState o) e used keys scalars) s) :
    WP isa (.block arguments) s fun t => Fr o liveDs (liveF (ofState o) e used keys scalars) t ∧
      ArgsAt o used 11 t.mem := by
  have hA : Aligned liveDs := by decide
  show WP isa (.block (pass xOff 0 ++ pass lenOff 1 ++ pass yOff 2 ++ pass lenOff 3 ++ pass domOff 4 ++
    pass dlenOff 5 ++ pass lenOff 6 ++ pass randOff 7 ++ pass lenOff 8 ++ pass scratchOff 9 ++
    pass slenOff 10 ++ [])) s _
  simp only [List.append_assoc]
  refine pass_ok (used := used) h hA (by decide) (by decide) (by decide) (by simp [liveF, callArg, ofState, xOff])
    (fun _ h => absurd h (Nat.not_lt_zero _)) fun t h a => ?_
  refine pass_ok h hA (by decide) (by decide) (by decide) (by simp [liveF, callArg, ofState, lenOff]) a
    fun t h a => ?_
  refine pass_ok h hA (by decide) (by decide) (by decide) (by simp [liveF, callArg, ofState, yOff]) a
    fun t h a => ?_
  refine pass_ok h hA (by decide) (by decide) (by decide) (by simp [liveF, callArg, ofState, lenOff]) a
    fun t h a => ?_
  refine pass_ok h hA (by decide) (by decide) (by decide) (by simp [liveF, callArg, ofState, domOff]) a
    fun t h a => ?_
  refine pass_ok h hA (by decide) (by decide) (by decide) (by simp [liveF, callArg, ofState, dlenOff]) a
    fun t h a => ?_
  refine pass_ok h hA (by decide) (by decide) (by decide) (by simp [liveF, callArg, ofState, lenOff]) a
    fun t h a => ?_
  refine pass_ok h hA (by decide) (by decide) (by decide) (by simp [liveF, callArg, ofState, randOff]) a
    fun t h a => ?_
  refine pass_ok h hA (by decide) (by decide) (by decide) (by simp [liveF, callArg, ofState, lenOff]) a
    fun t h a => ?_
  refine pass_ok h hA (by decide) (by decide) (by decide) (by simp [liveF, callArg, ofState, scratchOff]) a
    fun t h a => ?_
  refine pass_ok h hA (by decide) (by decide) (by decide) (by simp [liveF, callArg, ofState, slenOff]) a
    fun t h a => WP.block_nil ⟨h, a⟩

end VG.Proof.Ffdh.X86.KeySearch
