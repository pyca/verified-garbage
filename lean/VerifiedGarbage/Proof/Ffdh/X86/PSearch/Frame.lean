module

public import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Steps
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.Framework.Offset

/-! # The attempt's frame of arguments (x86)

The attempt allocates 36 bytes below the entry's stack pointer and stores
`vg_ffdh_parameter_candidate_sieved`'s nine arguments there
(`arguments_ok`). With the call's return address and the callee's 172 bytes
below them, they are the 212 bytes below the entry's stack pointer, at
offsets of `low o` (`low_sub`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.PSearch

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Ffdh.X86.ParamSearch
open VG.Proof.Ffdh.X86.KeySearch (Ctl Aligned upd Scratch saved_ne)
open VG.Proof.Dsa.X86 (argumentPointer)

/-- The base of the stack the controller uses. -/
abbrev low (o : State) : Addr := (o.gpr .esp).setWidth 64 - 212#64

theorem low_toNat {o : State} (A : PSearchABI o) : (low o).toNat = (o.gpr .esp).toNat - 212 := by
  have : 212 ≤ (o.gpr .esp).toNat := A.stackLow
  have := (o.gpr .esp).isLt
  simp only [low, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- A stack pointer `k ≤ 212` bytes below the entry's, at its offset from `low o`. -/
theorem sw_sub {o : State} (A : PSearchABI o) {k : Nat} (hk : k ≤ 212) :
    (o.gpr .esp - BitVec.ofNat 32 k).setWidth 64 = low o + BitVec.ofNat 64 (212 - k) := by
  have h1 : 212 ≤ (o.gpr .esp).toNat := A.stackLow
  have h2 := (o.gpr .esp).isLt
  have hl := low_toNat A
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, hl]
  omega

/-- A word at `d` above a stack pointer `k` bytes below the entry's. -/
theorem addr_sub {o : State} (A : PSearchABI o) {k d : Nat} (hk : k ≤ 212) (hd : d ≤ k) :
    addr (o.gpr .esp - BitVec.ofNat 32 k) d = low o + BitVec.ofNat 64 (212 - k + d) := by
  have h1 : 212 ≤ (o.gpr .esp).toNat := A.stackLow
  have h2 := (o.gpr .esp).isLt
  have hl := low_toNat A
  apply BitVec.eq_of_toNat_eq
  simp only [addr, BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, hl]
  omega

theorem lowR_eq {o : State} : lowR o = ⟨low o, 212⟩ := rfl

/-- A range at offsets of `low o` lies in the stack the controller uses. -/
theorem low_sub {o : State} {d n : Nat} (h : d + n ≤ 212) : Region.Sub ⟨low o + BitVec.ofNat 64 d, n⟩ (lowR o) :=
  Offset.sub_base _ h

theorem low_contains {o : State} (A : PSearchABI o) {d n : Nat} (h : d + n ≤ 212) :
    (lowR o).Contains (low o + BitVec.ofNat 64 d) n := by
  have : 212 ≤ (o.gpr .esp).toNat := A.stackLow
  exact Offset.contains_base _ h (by omega)

/-- The frame's region. -/
abbrev frR (o : State) : Region := ⟨low o + BitVec.ofNat 64 176, 36⟩

/-- A state in the attempt's frame: `St` but for the stack pointer and the frame's region. -/
structure Fr (o : State) (ds : List Nat) (f : Nat → BitVec 32) (s : State) : Prop where
  abi : PSearchABI o
  rd : s.rd = o.rd
  wr : s.wr = frR o :: o.wr
  syms : s.syms = o.syms
  esp : s.gpr .esp = o.gpr .esp - BitVec.ofNat 32 argsBytes
  esi : s.gpr .esi = arg o 9
  saved : ∀ r ∈ calleeSaved, r ≠ .esi → r ≠ .esp → s.gpr r = o.gpr r
  frame : Frame (frameR o) o.mem s.mem
  words : Ctl s.mem (arg o 9) ds f

theorem St.alloc {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) :
    Fr o ds f (allocFrame argsBytes s) := by
  refine ⟨h.abi, h.rd, ?_, h.syms, by rw [allocFrame_esp, h.esp], by rw [allocFrame_gpr _ _ (by decide), h.esi],
    fun r hr hne hsp => by rw [allocFrame_gpr _ _ hsp, h.saved r hr hne], h.frame, h.words⟩
  rw [allocFrame_wr, h.esp, h.wr, sw_sub h.abi (by decide)]; rfl

theorem Fr.reg {o s t : State} {ds : List Nat} {f : Nat → BitVec 32} (h : Fr o ds f s) {r : Reg} {v : BitVec 32}
    (U : Upd s t r v) (hr : Scratch r) : Fr o ds f t := by
  refine ⟨h.abi, U.rd.trans h.rd, U.wr.trans h.wr, U.syms.trans h.syms, ?_, ?_, fun q hq hne hsp => ?_,
    U.mem ▸ h.frame, U.mem ▸ h.words⟩
  · rw [U.other _ (saved_ne hr (by decide)), h.esp]
  · rw [U.other _ (saved_ne hr (by decide)), h.esi]
  · rw [U.other _ (saved_ne hr hq), h.saved q hq hne hsp]

/-- `vg_ffdh_parameter_candidate_sieved`'s arguments for `used` octets consumed. -/
def callArg (o : State) (used : Nat) (j : Nat) : BitVec 32 :=
  if j = 0 then arg o 0 else
  if j = 1 then arg o 1 else
  if j = 2 then arg o 9 + BitVec.ofNat 32 candOff else
  if j = 3 then arg o 3 else
  if j = 4 then arg o 4 else
  if j = 5 then arg o 5 + BitVec.ofNat 32 used else
  if j = 6 then BitVec.ofNat 32 ((arg o 6).toNat - used) else
  if j = 7 then arg o 7 else arg o 8

/-- The first `k` arguments are in the frame. -/
def ArgsAt (o : State) (used k : Nat) (m : Mem) : Prop :=
  ∀ j < k, m.readW (low o + BitVec.ofNat 64 (176 + 4 * j)) 32 = callArg o used j

/-- `mov [esp + 4 j], eax`, argument `j` in `eax`. -/
theorem storeArg_ok {o s : State} {ds : List Nat} {f : Nat → BitVec 32} {used : Nat} (h : Fr o ds f s)
    (hA : Aligned ds) {j : Nat} (hj : j < 9) (hv : s.gpr .eax = callArg o used j)
    (ha : ArgsAt o used j s.mem) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Fr o ds f t → ArgsAt o used (j + 1) t.mem → WP isa (.block rest) t Q) :
    WP isa (.block (.store (at_ .esp (4 * j)) .eax :: rest)) s Q := by
  have A := h.abi
  have hS := A.sBound
  have ea : addr (s.gpr .esp) (4 * j) = low o + BitVec.ofNat 64 (176 + 4 * j) := by
    rw [h.esp, addr_sub A (by decide) (by unfold argsBytes; omega)]; rfl
  have win : (frR o).Contains (low o + BitVec.ofNat 64 (176 + 4 * j)) 4 := by
    have : 212 ≤ (o.gpr .esp).toNat := A.stackLow
    exact Offset.contains _ (by omega) (by omega) (by omega)
  refine wp_storeS (show s.ea ⟨.esp, 4 * j⟩ = _ by rw [ea_mk, ea])
    (by rw [h.wr]; exact ⟨_, List.mem_cons_self .., win⟩) fun t' M => k t' ?_ ?_
  · have lc := low_contains A (d := 176 + 4 * j) (n := 4) (by omega)
    have fr : Frame [lowR o] s.mem t'.mem := by
      rw [M.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ lc
    refine ⟨A, M.rd.trans h.rd, M.wr.trans h.wr, M.syms.trans h.syms, ?_, ?_, fun r hr hne hsp => ?_,
      h.frame.trans (fr.mono fun r hr => ?_), h.words.frame hS hA fr fun r hr => ?_⟩
    · rw [M.gpr, h.esp]
    · rw [M.gpr, h.esi]
    · rw [M.gpr, h.saved r hr hne hsp]
    · simp only [List.mem_singleton] at hr; subst hr; exact List.mem_append_right _ (List.mem_singleton_self _)
    · simp only [List.mem_singleton] at hr; subst hr; exact A.lowS.symm
  · have hl := low_toNat A
    have hb := A.stackBound
    intro i hi
    rw [M.mem]
    by_cases hij : i = j
    · subst hij; rw [Mem.readW_writeW_self32, hv]
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
      exact ha i (by omega)

/-- `pass d j`: the state's word at `d`, argument `j`, to the frame. -/
theorem pass_ok {o s : State} {ds : List Nat} {f : Nat → BitVec 32} {used : Nat} (h : Fr o ds f s)
    (hA : Aligned ds) {d j : Nat} (hd : d ∈ ds) (hd4 : d + 4 ≤ 128) (hj : j < 9) (hv : f d = callArg o used j)
    (ha : ArgsAt o used j s.mem) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Fr o ds f t → ArgsAt o used (j + 1) t.mem → WP isa (.block rest) t Q) :
    WP isa (.block (pass d j ++ rest)) s Q := by
  have A := h.abi
  show WP isa (.block (.mov .eax (.mem ⟨.esi, d⟩) :: .store (at_ .esp (4 * j)) .eax :: rest)) s Q
  have rin : InRegions (s.rd ++ s.wr) (addr (arg o 9) d) 4 := by
    rw [h.rd, h.wr]; exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ (sR_mem A)), st_in A hd4⟩
  refine wp_movS (readSrc_mem h.esi rin) fun t U _ => ?_
  refine storeArg_ok (h.reg U (Or.inl rfl)) hA hj (by rw [U.gpr, h.words.get hd, hv]) (by rw [U.mem]; exact ha) k

theorem arguments_ok {o s : State} {e : BitVec 32} {used n : Nat}
    (h : Fr o liveDs (liveF (ofState o) e used n) s) :
    WP isa (.block arguments) s fun t => Fr o liveDs (liveF (ofState o) e used n) t ∧ ArgsAt o used 9 t.mem := by
  have hA : Aligned liveDs := by decide
  show WP isa (.block (pass outOff 0 ++ pass widthOff 1 ++
    ([.mov .eax (.reg .esi), .alu .add .eax (.imm (BitVec.ofNat 32 candOff)), .store (at_ .esp (4 * 2)) .eax] ++
    (pass bitsOff 3 ++ pass genOff 4 ++ pass randOff 5 ++ pass leftOff 6 ++ pass scratchOff 7 ++
    pass slenOff 8 ++ [])))) s _
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine pass_ok (used := used) h hA (by decide) (by decide) (by decide) (by simp [liveF, callArg, ofState, outOff])
    (fun _ h => absurd h (Nat.not_lt_zero _)) fun t h a => ?_
  refine pass_ok h hA (by decide) (by decide) (by decide) (by simp [liveF, callArg, ofState, widthOff]) a
    fun t h a => ?_
  refine wp_mov fun t₁ U₁ => wp_addi fun t₂ U₂ => ?_
  refine storeArg_ok ((h.reg U₁ (Or.inl rfl)).reg U₂ (Or.inl rfl)) hA (j := 2) (by decide)
    (by rw [U₂.gpr, U₁.gpr, h.esi]; simp [callArg]) (by rw [U₂.mem, U₁.mem]; exact a) fun t h a => ?_
  refine pass_ok h hA (by decide) (by decide) (by decide) (by simp [liveF, callArg, ofState, bitsOff]) a
    fun t h a => ?_
  refine pass_ok h hA (by decide) (by decide) (by decide) (by simp [liveF, callArg, ofState, genOff]) a
    fun t h a => ?_
  refine pass_ok h hA (by decide) (by decide) (by decide) (by simp [liveF, callArg, ofState, randOff]) a
    fun t h a => ?_
  refine pass_ok h hA (by decide) (by decide) (by decide) (by simp [liveF, callArg, ofState, leftOff]) a
    fun t h a => ?_
  refine pass_ok h hA (by decide) (by decide) (by decide) (by simp [liveF, callArg, ofState, scratchOff]) a
    fun t h a => ?_
  refine pass_ok h hA (by decide) (by decide) (by decide) (by simp [liveF, callArg, ofState, slenOff]) a
    fun t h a => WP.block_nil ⟨h, a⟩

end VG.Proof.Ffdh.X86.PSearch
