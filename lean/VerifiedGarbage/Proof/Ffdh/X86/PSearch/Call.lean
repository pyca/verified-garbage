module

public import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Steps
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Framework.X86.Inline
public import VerifiedGarbage.Proof.Ffdh.X86.Cand.Top
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABI
public import VerifiedGarbage.Proof.Ffdh.Contract
import VerifiedGarbage.Proof.Ffdh.X86.Cand.Verified
import VerifiedGarbage.Proof.Rsa.X86.StackTactic
meta import VerifiedGarbage.Proof.Rsa.X86.StackTactic
meta import VerifiedGarbage.Proof.Ffdh.Contract
import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Entry
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.X86.Syms
public import VerifiedGarbage.Impl.Ffdh.X86.Candidate
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
public import VerifiedGarbage.Spec.Ffdh.SievedContract
public import VerifiedGarbage.Proof.Weierstrass.PointContract

/-! ### `Ffdh.X86.PSearch.CallPre`, which only this module used -/

section

/-! ### `Ffdh.X86.PSearch.Frame`, which only this module used -/

section

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
  omega_arith

/-- A stack pointer `k ≤ 212` bytes below the entry's, at its offset from `low o`. -/
theorem sw_sub {o : State} (A : PSearchABI o) {k : Nat} (hk : k ≤ 212) :
    (o.gpr .esp - BitVec.ofNat 32 k).setWidth 64 = low o + BitVec.ofNat 64 (212 - k) := by
  have h1 : 212 ≤ (o.gpr .esp).toNat := A.stackLow
  obtain h2 := (o.gpr .esp).isLt
  obtain hl := low_toNat A
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, hl]
  omega_arith

/-- A word at `d` above a stack pointer `k` bytes below the entry's. -/
theorem addr_sub {o : State} (A : PSearchABI o) {k d : Nat} (hk : k ≤ 212) (hd : d ≤ k) :
    addr (o.gpr .esp - BitVec.ofNat 32 k) d = low o + BitVec.ofNat 64 (212 - k + d) := by
  have h1 : 212 ≤ (o.gpr .esp).toNat := A.stackLow
  obtain h2 := (o.gpr .esp).isLt
  obtain hl := low_toNat A
  apply BitVec.eq_of_toNat_eq
  simp only [addr, BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, hl]
  omega_arith

/-- A range at offsets of `low o` lies in the stack the controller uses. -/
theorem low_sub {o : State} {d n : Nat} (h : d + n ≤ 212) : Region.Sub ⟨low o + BitVec.ofNat 64 d, n⟩ (lowR o) :=
  Offset.sub_base _ h

theorem low_contains {o : State} (A : PSearchABI o) {d n : Nat} (h : d + n ≤ 212) :
    (lowR o).Contains (low o + BitVec.ofNat 64 d) n := by
  have : 212 ≤ (o.gpr .esp).toNat := A.stackLow
  exact Offset.contains_base _ h (by omega_arith)

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
  obtain ea : addr (s.gpr .esp) (4 * j) = low o + BitVec.ofNat 64 (176 + 4 * j) := by
    rw [h.esp, addr_sub A (by decide) (by unfold argsBytes; omega_arith)]; rfl
  obtain win : (frR o).Contains (low o + BitVec.ofNat 64 (176 + 4 * j)) 4 := by
    have : 212 ≤ (o.gpr .esp).toNat := A.stackLow
    exact Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)
  refine wp_storeS (show s.ea ⟨.esp, 4 * j⟩ = _ by rw [ea_mk, ea])
    (by rw [h.wr]; exact ⟨_, List.mem_cons_self .., win⟩) fun t' M => k t' ?_ ?_
  · have lc := low_contains A (d := 176 + 4 * j) (n := 4) (by omega_arith)
    obtain fr : Frame [lowR o] s.mem t'.mem := by
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
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
      exact ha i (by omega_arith)

/-- `pass d j`: the state's word at `d`, argument `j`, to the frame. -/
theorem pass_ok {o s : State} {ds : List Nat} {f : Nat → BitVec 32} {used : Nat} (h : Fr o ds f s)
    (hA : Aligned ds) {d j : Nat} (hd : d ∈ ds) (hd4 : d + 4 ≤ 128) (hj : j < 9) (hv : f d = callArg o used j)
    (ha : ArgsAt o used j s.mem) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Fr o ds f t → ArgsAt o used (j + 1) t.mem → WP isa (.block rest) t Q) :
    WP isa (.block (pass d j ++ rest)) s Q := by
  have A := h.abi
  show WP isa (.block (.mov .eax (.mem ⟨.esi, d⟩) :: .store (at_ .esp (4 * j)) .eax :: rest)) s Q
  obtain rin : InRegions (s.rd ++ s.wr) (addr (arg o 9) d) 4 := by
    rw [h.rd, h.wr]; exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ (sR_mem A)), st_in A hd4⟩
  refine wp_movS (readSrc_mem h.esi rin) fun t U _ => ?_
  refine storeArg_ok (h.reg U (Or.inl rfl)) hA hj (by rw [U.gpr, h.words.get hd, hv]) (by rw [U.mem]; exact ha) k

theorem arguments_ok {o s : State} {e : BitVec 32} {used n : Nat}
    (h : Fr o liveDs (liveF (ofState o) e used n) s) :
    WP isa (.block arguments) s fun t => Fr o liveDs (liveF (ofState o) e used n) t ∧ ArgsAt o used 9 t.mem := by
  obtain hA : Aligned liveDs := by decide
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

end

end


/-! # The attempt's precondition (x86)

With its nine arguments in the frame (`ArgsAt`),
`vg_ffdh_parameter_candidate_sieved`'s contract holds on its entry, narrowed
to the rest of the tape and RSA's table, which it reads, and to the output,
the state's word for its `used`, the working space and its frame of
arguments, which it writes (`call_pre`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.PSearch

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Ffdh.X86.ParamSearch
open VG.Proof.Dsa.X86 (argumentPointer)

/-- The table's region, as the constants name it. -/
abbrev tableRs (o : State) : List Region :=
  Abi.constRegions (fun name => (o.syms name).setWidth 64) VG.Impl.RsaKeyGen.TrialTable32.consts

/-- The rest of the tape. -/
abbrev winR (o : State) (used : Nat) : Region :=
  ⟨(arg o 5 + BitVec.ofNat 32 used).setWidth 64, (arg o 6).toNat - used⟩

/-- The state's word the candidate writes its `used` to. -/
abbrev cuR (o : State) : Region := ⟨(arg o 9 + BitVec.ofNat 32 candOff).setWidth 64, 8⟩

/-- What the callee may read and write. -/
abbrev callRd (o : State) (used : Nat) : List Region := winR o used :: tableRs o
abbrev callWr (o : State) : List Region := [oR o, cuR o, bR o, frR o]

theorem tableRs_eq (o : State) : tableRs o = [tR o] := by
  rw [tableRs, VG.Impl.RsaKeyGen.TrialTable32.consts, Abi.constRegions_cons, Abi.constRegions_nil,
    VG.Proof.RsaKeyGen.X86.Candidate.packed_length]

/-- The callee's arguments, on its entry. -/
theorem ce_arg {o t : State} {used : Nat} (A : PSearchABI o)
    (he : t.gpr .esp = o.gpr .esp - BitVec.ofNat 32 argsBytes) (ha : ArgsAt o used 9 t.mem)
    (rd wr : List Region) {j : Nat} (hj : j < 9) :
    arg (t.callEntry.withRegions rd wr) j = callArg o used j := by
  have h1 : 212 ≤ (o.gpr .esp).toNat := A.stackLow
  have hb := A.stackBound
  obtain hn : (t.gpr .esp).toNat = (o.gpr .esp).toNat - 36 := by
    rw [he]; exact VG.X86.sub_toNat (by unfold argsBytes; omega_using [h1])
  rw [arg_withRegions, arg_callEntry (by omega_using [h1, hn]) (by omega_using [hj, hn]), ← ha j hj]
  congr 1
  rw [show (t.gpr .esp + BitVec.ofNat 32 (4 * j)).setWidth 64 = addr (t.gpr .esp) (4 * j) from rfl, he,
    addr_sub A (by decide) (by unfold argsBytes; omega_using [hj])]
  rfl

/-- Constants held, through writes apart from them. -/
theorem held_frame {m m' : Mem} {f : String → BitVec 64} {cs : List (String × List (BitVec 64))}
    (h : Abi.constsHeld m f cs) {rs : List Region} (hf : Frame rs m m') (hb : ∀ c ∈ cs, 8 * c.2.length ≤ 2 ^ 64)
    (hd : ∀ t ∈ Abi.constRegions f cs, ∀ r ∈ rs, t.Disjoint r) : Abi.constsHeld m' f cs := by
  intro c hc i hi
  have := hb c hc
  rw [hf.readW (r := ⟨f c.1, 8 * c.2.length⟩) (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, this]))
    (hd _ (List.mem_map_of_mem hc)) (by decide)]
  exact h c hc i hi

/-- The rest of the tape, at its offset in the tape. -/
theorem win_base {o : State} (A : PSearchABI o) {used : Nat} (hu : used < (arg o 6).toNat) :
    (arg o 5 + BitVec.ofNat 32 used).setWidth 64 = argumentPointer o 5 + BitVec.ofNat 64 used := by
  have := A.rBound
  exact addr_eq (by omega_using [hu, this])

theorem win_toNat {o : State} (A : PSearchABI o) {used : Nat} (hu : used < (arg o 6).toNat) :
    (arg o 5 + BitVec.ofNat 32 used).toNat = (arg o 5).toNat + used := by
  have := A.rBound
  have := (arg o 6).isLt
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := used) (by omega_using [hu])]
  exact Nat.mod_eq_of_lt (by omega_arith)

theorem win_sub {o : State} (A : PSearchABI o) {used : Nat} (hu : used < (arg o 6).toNat) :
    Region.Sub (winR o used) (rR o) := by
  rw [winR, win_base A hu]; exact Offset.sub_base _ (by omega_using [hu])

theorem cu_base {o : State} (A : PSearchABI o) :
    (arg o 9 + BitVec.ofNat 32 candOff).setWidth 64 = argumentPointer o 9 + BitVec.ofNat 64 80 :=
  Spill.addr_eq_of A.sBound (d := 80) (by decide)

theorem cu_sub {o : State} (A : PSearchABI o) : Region.Sub (cuR o) (sR o) := by
  rw [cuR, cu_base A]; exact Offset.sub_base _ (by decide)

/-- The callee's stack pointer on its entry. -/
theorem esp_sub4 {o t : State} (A : PSearchABI o) (he : t.gpr .esp = o.gpr .esp - BitVec.ofNat 32 argsBytes) :
    t.gpr .esp - 4 = o.gpr .esp - BitVec.ofNat 32 40 := by
  have h1 : 212 ≤ (o.gpr .esp).toNat := A.stackLow
  rw [he]; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, argsBytes]
  have := (o.gpr .esp).isLt
  show (2 ^ 32 - 4 % 2 ^ 32 + (2 ^ 32 - 36 % 2 ^ 32 + (o.gpr .esp).toNat) % 2 ^ 32) % 2 ^ 32 = _
  omega_using []

/-- The table, apart from every region the run may write. -/
theorem table_far {o : State} (A : PSearchABI o) :
    (tR o).base.toNat + 8192 ≤ 2 ^ 32 ∧ (∀ r ∈ frameR o, (tR o).Disjoint r) ∧ (tR o).Disjoint (retR o) := by
  obtain F := A.tableFar (tR o) (by
    rw [Abi.constRegions_cons, Abi.constRegions_nil, VG.Proof.RsaKeyGen.X86.Candidate.packed_length]
    exact List.mem_singleton_self _)
  refine ⟨F.1, fun r hr => ?_, F.2.2.1⟩
  rcases List.mem_append.mp hr with hr | hr
  · exact F.2.1 r hr
  · simp only [List.mem_singleton] at hr; subst hr; exact F.2.2.2

theorem call_pre {o t : State} {used : Nat} (A : PSearchABI o) (hu : used < (arg o 6).toNat)
    (he : t.gpr .esp = o.gpr .esp - BitVec.ofNat 32 argsBytes) (ha : ArgsAt o used 9 t.mem)
    (hsy : t.syms = o.syms) (hm : Frame (frameR o) o.mem t.mem) :
    Cand.contract.pre (t.callEntry.withRegions (callRd o used) (callWr o)) := by
  have h1 : 212 ≤ (o.gpr .esp).toNat := A.stackLow
  have hb := A.stackBound
  obtain hs4 := esp_sub4 A he
  obtain hs4n : (o.gpr .esp - BitVec.ofNat 32 40).toNat = (o.gpr .esp).toNat - 40 := VG.X86.sub_toNat (by omega_using [h1])
  obtain ha0 : argAddr (t.callEntry.withRegions (callRd o used) (callWr o)) 0 = low o + BitVec.ofNat 64 176 := by
    rw [argAddr_withRegions, argAddr_callEntry, show 4 * 0 = 0 from rfl, BitVec.add_zero, he,
      sw_sub A (by decide)]; rfl
  obtain hret : (o.gpr .esp - BitVec.ofNat 32 40).setWidth 64 = low o + BitVec.ofNat 64 172 := sw_sub A (by decide)
  obtain hlen : (BitVec.ofNat 32 ((arg o 6).toNat - used)).toNat = (arg o 6).toNat - used := by
    have := (arg o 6).isLt; rw [BitVec.toNat_ofNat]; omega_using []
  obtain hT : Abi.constRegions (fun name => BitVec.setWidth 64 (t.syms name))
      [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)] = [tR o] := by
    rw [hsy, Abi.constRegions_cons, Abi.constRegions_nil, VG.Proof.RsaKeyGen.X86.Candidate.packed_length]
  obtain TF := table_far A
  obtain W := win_sub A hu
  obtain Cu := cu_sub A
  obtain Fs : Region.Sub (frR o) (lowR o) := low_sub (by decide)
  obtain Rs : Region.Sub ⟨low o + BitVec.ofNat 64 172, 4⟩ (lowR o) := low_sub (by decide)
  obtain Bs : Region.Sub ⟨low o, 172⟩ (lowR o) := Region.sub_prefix (by decide)
  obtain oIn := oR_mem A
  obtain bIn := bR_mem A
  obtain sIn := sR_mem A
  -- The callee's regions, apart.
  obtain dOC : (oR o).Disjoint (cuR o) := A.os.sub_right Cu
  obtain dOW : (oR o).Disjoint (winR o used) := A.or_.sub_right W
  have dOB : (oR o).Disjoint (bR o) := A.ob
  obtain dOF : (oR o).Disjoint (frR o) := A.lowO.symm.sub_right Fs
  obtain dCW : (cuR o).Disjoint (winR o used) := (A.rs.symm.sub_left Cu).sub_right W
  obtain dCB : (cuR o).Disjoint (bR o) := A.bs.symm.sub_left Cu
  obtain dCF : (cuR o).Disjoint (frR o) := (A.lowS.symm.sub_left Cu).sub_right Fs
  obtain dWB : (winR o used).Disjoint (bR o) := A.rb.sub_left W
  obtain dWF : (winR o used).Disjoint (frR o) := (A.lowRand.symm.sub_left W).sub_right Fs
  obtain dBF : (bR o).Disjoint (frR o) := A.lowB.symm.sub_right Fs
  obtain rO : Region.Disjoint ⟨low o + BitVec.ofNat 64 172, 4⟩ (oR o) := A.lowO.sub_left Rs
  obtain rC : Region.Disjoint ⟨low o + BitVec.ofNat 64 172, 4⟩ (cuR o) := (A.lowS.sub_left Rs).sub_right Cu
  obtain rW : Region.Disjoint ⟨low o + BitVec.ofNat 64 172, 4⟩ (winR o used) := (A.lowRand.sub_left Rs).sub_right W
  obtain rB : Region.Disjoint ⟨low o + BitVec.ofNat 64 172, 4⟩ (bR o) := A.lowB.sub_left Rs
  obtain rF : Region.Disjoint ⟨low o + BitVec.ofNat 64 172, 4⟩ (frR o) :=
    Offset.disjoint _ (by omega_using []) (by omega_using []) (by omega_using [])
  obtain bO : Region.Disjoint ⟨low o, 172⟩ (oR o) := A.lowO.sub_left Bs
  obtain bC : Region.Disjoint ⟨low o, 172⟩ (cuR o) := (A.lowS.sub_left Bs).sub_right Cu
  obtain bW : Region.Disjoint ⟨low o, 172⟩ (winR o used) := (A.lowRand.sub_left Bs).sub_right W
  obtain bB : Region.Disjoint ⟨low o, 172⟩ (bR o) := A.lowB.sub_left Bs
  obtain bF : Region.Disjoint ⟨low o, 172⟩ (frR o) := Offset.base_disjoint _ (by omega_using []) (by omega_using [])
  have oB := A.oBound
  obtain cB : (arg o 9 + BitVec.ofNat 32 candOff).toNat + 8 ≤ 2 ^ 32 := by
    have := A.sBound
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, show candOff = 80 from rfl]
    rw [Nat.mod_eq_of_lt (a := 80) (by decide), Nat.mod_eq_of_lt (by omega_using [this])]; omega_using [this]
  obtain wB : (arg o 5 + BitVec.ofNat 32 used).toNat + ((arg o 6).toNat - used) ≤ 2 ^ 32 := by
    rw [win_toNat A hu]; have := A.rBound; omega_using [hu, this]
  have sB := A.bBound
  have bL := A.bitsLow
  have bH := A.bitsHigh
  have oL := A.outLen
  have gG := A.gen
  have sL := A.scratchLength
  obtain st : Proof.Ffdh.X86.stack ≤ (o.gpr .esp - BitVec.ofNat 32 40).toNat := by
    rw [hs4n]; show 172 ≤ _; omega_using [h1]
  obtain st' : (o.gpr .esp - BitVec.ofNat 32 40).toNat + 4 + 36 ≤ 2 ^ 32 := by rw [hs4n]; omega_using []
  obtain held : Abi.constsHeld (t.mem.writeW (low o + BitVec.ofNat 64 172) (t.unknowns 0))
      (fun name => BitVec.setWidth 64 (t.syms name))
      [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)] := by
    have H := A.held
    rw [hsy]
    obtain hb : ∀ c ∈ [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)],
        8 * c.2.length ≤ 2 ^ 64 := by
      intro c hc; simp only [List.mem_singleton] at hc; subst hc
      rw [VG.Proof.RsaKeyGen.X86.Candidate.packed_length]; decide
    refine held_frame (held_frame H hm hb fun r hr => ?_) ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Region.contains_self _ _)) hb fun r hr => ?_
    · rw [Abi.constRegions_cons, Abi.constRegions_nil, VG.Proof.RsaKeyGen.X86.Candidate.packed_length] at hr
      simp only [List.mem_singleton] at hr; subst hr; exact TF.2.1
    · rw [Abi.constRegions_cons, Abi.constRegions_nil, VG.Proof.RsaKeyGen.X86.Candidate.packed_length] at hr
      simp only [List.mem_singleton] at hr; subst hr
      intro q hq; simp only [List.mem_singleton] at hq; subst hq
      exact (TF.2.1 _ (List.mem_append_right _ (List.mem_singleton_self _))).sub_right Rs
  sig_pre [Cand.contract, Proof.Ffdh.sievedParameterCandidateContract, Proof.Ffdh.parameterCandidateSig, abi,
    argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts,
    VG.Proof.RsaKeyGen.X86.Candidate.packed_length, stackBelow]
  simp only [ce_arg A he ha _ _ (show 0 < 9 by decide), ce_arg A he ha _ _ (show 1 < 9 by decide),
    ce_arg A he ha _ _ (show 2 < 9 by decide), ce_arg A he ha _ _ (show 3 < 9 by decide),
    ce_arg A he ha _ _ (show 4 < 9 by decide), ce_arg A he ha _ _ (show 5 < 9 by decide),
    ce_arg A he ha _ _ (show 6 < 9 by decide), ce_arg A he ha _ _ (show 7 < 9 by decide),
    ce_arg A he ha _ _ (show 8 < 9 by decide), callArg, Nat.reduceEqDiff, ↓reduceIte, hs4, ha0, hret,
    hlen, hT, BitVec.add_sub_cancel]
  obtain hrd : callRd o used = [winR o used, tR o] := by rw [callRd, tableRs_eq]
  obtain tW : ∀ r ∈ o.wr, (tR o).Disjoint r := fun r hr => TF.2.1 r (List.mem_append_left _ hr)
  obtain tL : (tR o).Disjoint (lowR o) := TF.2.1 _ (List.mem_append_right _ (List.mem_singleton_self _))
  obtain tO : (tR o).Disjoint (oR o) := tW _ oIn
  obtain tC : (tR o).Disjoint (cuR o) := (tW _ sIn).sub_right Cu
  obtain tB : (tR o).Disjoint (bR o) := tW _ bIn
  obtain tF : (tR o).Disjoint (frR o) := tL.sub_right Fs
  obtain tRet : (tR o).Disjoint ⟨low o + BitVec.ofNat 64 172, 4⟩ := tL.sub_right Rs
  obtain tBel : (tR o).Disjoint ⟨low o, 172⟩ := tL.sub_right Bs
  have tBd := TF.1
  obtain tAl : (tR o).base.toNat % 64 = 0 := A.tableAligned (tR o) (by
    rw [Abi.constRegions_cons, Abi.constRegions_nil, VG.Proof.RsaKeyGen.X86.Candidate.packed_length]
    exact List.mem_singleton_self _)
  sig_and_intros
  all_goals first
    | exact True.intro
    | with_reducible assumption
    | with_reducible exact Region.Disjoint.symm ‹_›
    | (rw [hrd]; rfl)
    | (intro r hr; simp only [List.mem_singleton] at hr; subst hr
       exact ⟨tBd, tO, tC, tB, tF, tRet, tBel⟩)
    | (intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact tAl)


end VG.Proof.Ffdh.X86.PSearch

end

end


/-! # The attempt's call (x86)

`vg_ffdh_parameter_candidate_sieved`, called with its arguments in the
frame, returns the status of the candidate at the tape's offset, writes its
output and the octets it consumed (to the state's word at 80), changing
memory only at the output, that word, the working space and the stack the
controller uses (`call_ok`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.PSearch

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86 VG.Spec.Ffdh
open VG.Impl.Ffdh.X86.ParamSearch
open VG.Proof.Ffdh.X86.KeySearch (Ctl Aligned upd bytes_frame)
open VG.Proof.Dsa.X86 (argumentPointer)

theorem callee_stack : stackUse Impl.Ffdh.X86.Candidate.code = 172 := by rsa_stack_use

/-- No instruction of the callee writes `esp`: walked once, for `callee_noSp` and `body_noSp`. -/
private theorem callee_all :
    Impl.Ffdh.X86.Candidate.code.allInstrs (fun i => !Taint.clobbers i .esp) = true := by rsa_stack_shape

theorem callee_noSp : NoSp Impl.Ffdh.X86.Candidate.code := NoSp.of_all callee_all

/-- The bytes `[u, u + l)` of `n` at `p`. -/
theorem bytes_window (m : Mem) (p : Addr) {u l n : Nat} (h : u + l ≤ n) :
    Spec.Rsa.bytesAt m (p + BitVec.ofNat 64 u) l = ((Spec.Rsa.bytesAt m p n).drop u).take l := by
  apply List.ext_getElem (by simp [Spec.Rsa.bytesAt]; omega_arith)
  intro i h₁ h₂
  simp only [Spec.Rsa.bytesAt, List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range,
    BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- The candidate at the tape's offset `used`. -/
abbrev candOf (o : State) (used : Nat) : Option (Option Nat × Spec.RsaKeyGen.Rand) :=
  candAt (ofState o).bits (ofState o).gen (ofState o).rand used

/-- What an attempt leaves at the output. -/
def AttemptOut (o : State) (used : Nat) (m : Mem) : Prop :=
  Spec.Rsa.bytesAt m (argumentPointer o 0) (arg o 1).toNat =
    match candOf o used with
    | some (some q, _) => Spec.Rsa.i2osp q (arg o 1).toNat
    | _ => List.replicate (arg o 1).toNat 0

/-- Words of the state, through writes apart from each of them. -/
theorem ctl_frameW {m m' : Mem} {S : BitVec 32} {ds : List Nat} {f : Nat → BitVec 32} (h : Ctl m S ds f)
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ d ∈ ds, ∀ r ∈ rs, (⟨addr S d, 4⟩ : Region).Disjoint r) :
    Ctl m' S ds f := fun d hd' => by
  rw [hf.readW (Region.contains_self _ _) (hd d hd') (by decide)]; exact h d hd'

theorem call_covers {o t : State} {used : Nat} (A : PSearchABI o) (hu : used < (arg o 6).toNat)
    (hrd : t.rd = o.rd) (hwr : t.wr = frR o :: o.wr) :
    Covers (callRd o used ++ callWr o) (t.rd ++ t.wr) ∧ Covers (callWr o) t.wr := by
  obtain hw : ∀ r ∈ callWr o, ∃ r' ∈ t.wr, ∃ off, r.base = r'.base + BitVec.ofNat 64 off ∧ off + r.len ≤ r'.len := by
    intro r hr
    rw [hwr, A.wr]
    simp only [callWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨oR o, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨sR o, by simp, 80, cu_base A, show 80 + 8 ≤ 128 by decide⟩
    · exact ⟨bR o, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨frR o, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  obtain hT : o.rd = [rR o, tR o] := by
    have hp := A.rdPrefix
    have hd := A.rdTable
    rw [← List.take_append_drop (o.rd.length - 1) o.rd, hp, hd]
    show [rR o] ++ tableRs o = _
    rw [tableRs_eq]; rfl
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub hw⟩
  rcases List.mem_append.mp hr with hr | hr
  · rw [hrd, hT]
    rw [callRd, tableRs_eq] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨rR o, by simp, used, win_base A hu, show used + ((arg o 6).toNat - used) ≤ (arg o 6).toNat by omega_arith⟩
    · exact ⟨tR o, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  · obtain ⟨r', hr', off, hb⟩ := hw r hr
    exact ⟨r', List.mem_append_right _ hr', off, hb⟩

/-- A region apart from every region the run may write. -/
theorem apart {o : State} (A : PSearchABI o) {R : Region} (ho : R.Disjoint (oR o)) (hu : R.Disjoint (uR o))
    (hb : R.Disjoint (bR o)) (hs : R.Disjoint (sR o)) (ha : R.Disjoint (aR o)) (hl : R.Disjoint (lowR o)) :
    ∀ r ∈ frameR o, R.Disjoint r := by
  intro r hr
  rw [frameR, A.wr] at hr
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [ho, hu, hb, hs, ha, hl]

/-- The tape, through the run's writes. -/
theorem rand_apart {o : State} (A : PSearchABI o) : ∀ r ∈ frameR o, (rR o).Disjoint r :=
  apart A A.or_.symm A.ur.symm A.rb A.rs A.ra A.lowRand.symm

/-- The call's return address. -/
theorem ret_eq {o t : State} (A : PSearchABI o) (he : t.gpr .esp = o.gpr .esp - BitVec.ofNat 32 argsBytes) :
    (t.gpr .esp - 4).setWidth 64 = low o + BitVec.ofNat 64 172 := by
  rw [esp_sub4 A he, sw_sub A (by decide)]

/-- The stack below the call. -/
theorem below_eq {o t : State} (A : PSearchABI o) (he : t.gpr .esp = o.gpr .esp - BitVec.ofNat 32 argsBytes) :
    below (t.gpr .esp) (stackUse Impl.Ffdh.X86.Candidate.code + 4) = ⟨low o, 176⟩ := by
  have h1 : 212 ≤ (o.gpr .esp).toNat := A.stackLow
  obtain hl := low_toNat A
  have := (o.gpr .esp).isLt
  obtain e : (o.gpr .esp - BitVec.ofNat 32 argsBytes - BitVec.ofNat 32 (172 + 4)).setWidth 64 = low o := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat, hl, argsBytes]
    omega_arith
  rw [callee_stack, below, he, e]

theorem rand_length {o : State} : (ofState o).rand.length = (arg o 6).toNat := by
  simp only [ofState, Spec.Rsa.bytesAt, List.length_map, List.length_range]

/-- The callee's tape, on its entry. -/
theorem entry_bytes {o t : State} {ds : List Nat} {f : Nat → BitVec 32} {used : Nat} (h : Fr o ds f t)
    (hu : used < (arg o 6).toNat) (v : BitVec 32) :
    Spec.Rsa.bytesAt (t.mem.writeW (low o + BitVec.ofNat 64 172) v) ((arg o 5 + BitVec.ofNat 32 used).setWidth 64)
      ((arg o 6).toNat - used) = (ofState o).rand.drop used := by
  have A := h.abi
  have hrb := A.rBound
  obtain Rs : Region.Sub ⟨low o + BitVec.ofNat 64 172, 4⟩ (lowR o) := low_sub (by decide)
  obtain W := win_sub A hu
  obtain fe : Frame [⟨low o + BitVec.ofNat 64 172, 4⟩] t.mem (t.mem.writeW (low o + BitVec.ofNat 64 172) v) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  rw [bytes_frame fe (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ((A.lowRand.sub_left Rs).sub_right W).symm)
      (by omega_arith), bytes_frame h.frame (fun r hr => (rand_apart A r hr).sub_left W) (by omega_arith),
    win_base A hu, bytes_window _ _ (show used + ((arg o 6).toNat - used) ≤ (arg o 6).toNat by omega_arith)]
  show _ = (Spec.Rsa.bytesAt o.mem (argumentPointer o 5) (arg o 6).toNat).drop used
  rw [List.take_of_length_le (by simp [Spec.Rsa.bytesAt])]

theorem candidateStatus_le (c : Option (Option Nat × Spec.RsaKeyGen.Rand)) : candidateStatus c ≤ 2 := by
  unfold candidateStatus; split <;> decide

/-- The state's word at `d < 80`, apart from the candidate's `used`. -/
theorem word_cu {o : State} (A : PSearchABI o) {d : Nat} (hd : d + 4 ≤ 80) :
    (⟨addr (arg o 9) d, 4⟩ : Region).Disjoint (cuR o) := by
  rw [cuR, cu_base A, Spill.addr_eq_of A.sBound (d := d) (by omega_arith)]
  exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)

/-- The state's word at `d` lies in the state's region. -/
theorem word_sub {o : State} (A : PSearchABI o) {d : Nat} (hd : d + 4 ≤ 128) :
    Region.Sub ⟨addr (arg o 9) d, 4⟩ (sR o) := by
  rw [Spill.addr_eq_of A.sBound hd]; exact Offset.sub_base _ hd

theorem call_ok {o t : State} {e : BitVec 32} {used n : Nat}
    (h : Fr o liveDs (liveF (ofState o) e used n) t) (hu : used < (arg o 6).toNat) (ha : ArgsAt o used 9 t.mem) :
    WP isa (.call "vg_ffdh_parameter_candidate_sieved" Impl.Ffdh.X86.Candidate.code) t fun u =>
      Fr o liveDs (liveF (ofState o) e used n) u ∧
      u.gpr .eax = BitVec.ofNat 32 (candidateStatus (candOf o used)) ∧ AttemptOut o used u.mem ∧
      u.mem.readW (addr (arg o 9) candOff) 32 =
        BitVec.ofNat 32 (candUsed (ofState o).bits (ofState o).gen (ofState o).rand used) := by
  have A := h.abi
  have h1 : 212 ≤ (o.gpr .esp).toNat := A.stackLow
  have hb := A.stackBound
  obtain hn : (t.gpr .esp).toNat = (o.gpr .esp).toNat - 36 := by
    rw [h.esp]; exact VG.X86.sub_toNat (by unfold argsBytes; omega_arith)
  obtain ⟨hc, hcw⟩ := call_covers (t := t) A hu h.rd h.wr
  refine WP.of_syms (WP.call Cand.verified.1 callee_noSp (by rw [callee_stack, hn]; omega_arith)
    (call_pre A hu h.esp ha h.syms h.frame) hc hcw fun u hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ sy => ?_)
  have hp := hpost
  sig_post [Cand.contract, Proof.Ffdh.sievedParameterCandidateContract, Proof.Ffdh.parameterCandidateSig, abi,
    argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts] at hp
  simp only [ce_arg A h.esp ha _ _ (show 0 < 9 by decide), ce_arg A h.esp ha _ _ (show 1 < 9 by decide),
    ce_arg A h.esp ha _ _ (show 2 < 9 by decide), ce_arg A h.esp ha _ _ (show 3 < 9 by decide),
    ce_arg A h.esp ha _ _ (show 4 < 9 by decide), ce_arg A h.esp ha _ _ (show 5 < 9 by decide),
    ce_arg A h.esp ha _ _ (show 6 < 9 by decide), callArg, Nat.reduceEqDiff, ↓reduceIte, ret_eq A h.esp] at hp
  obtain hlen : (BitVec.ofNat 32 ((arg o 6).toNat - used)).toNat = (arg o 6).toNat - used := by
    have := (arg o 6).isLt; rw [BitVec.toNat_ofNat]; omega_arith
  rw [hlen, show low o + 172#64 = low o + BitVec.ofNat 64 172 from rfl, entry_bytes h hu] at hp
  obtain ⟨hr, hout, hw⟩ := hp
  rw [BitVec.setWidth_append_eq_right, hg₂ .eax (by decide)] at hr
  have hS := A.sBound
  obtain hA : Aligned liveDs := by decide
  obtain Fs : Region.Sub (frR o) (lowR o) := low_sub (by decide)
  obtain Bs : Region.Sub ⟨low o, 176⟩ (lowR o) := Region.sub_prefix (by decide)
  obtain fr : Frame (frameR o) t.mem u.mem := hf.sub fun r hr => by
    rw [below_eq A h.esp] at hr
    simp only [callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨oR o, List.mem_append_left _ (oR_mem A), fun _ h => h⟩
    · exact ⟨sR o, List.mem_append_left _ (sR_mem A), cu_sub A⟩
    · exact ⟨bR o, List.mem_append_left _ (bR_mem A), fun _ h => h⟩
    · exact ⟨lowR o, List.mem_append_right _ (List.mem_singleton_self _), Fs⟩
    · exact ⟨lowR o, List.mem_append_right _ (List.mem_singleton_self _), Bs⟩
  refine ⟨⟨A, hrd.trans h.rd, hwr.trans h.wr, sy.trans h.syms, by rw [hcs .esp (by decide), h.esp],
    by rw [hcs .esi (by decide), h.esi], fun r hr hne hsp => by rw [hcs r hr, h.saved r hr hne hsp],
    h.frame.trans fr, ctl_frameW h.words hf fun d hd r hr => ?_⟩, ?_, ?_, ?_⟩
  · have hd4 : d + 4 ≤ 76 := by
      simp only [liveDs, List.mem_cons, List.not_mem_nil, or_false] at hd; omega_arith
    obtain ws := word_sub A (d := d) (by omega_arith)
    rw [below_eq A h.esp] at hr
    simp only [callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact A.os.symm.sub_left ws
    · exact word_cu A (by omega_arith)
    · exact A.bs.symm.sub_left ws
    · exact (A.lowS.symm.sub_left ws).sub_right Fs
    · exact (A.lowS.symm.sub_left ws).sub_right Bs
  · apply BitVec.eq_of_toNat_eq
    rw [hr, toNat_ofNat_lt (Nat.lt_of_le_of_lt (candidateStatus_le _) (by decide))]
    rfl
  · show Spec.Rsa.bytesAt u.mem ((arg o 0).setWidth 64) (arg o 1).toNat = _
    rw [← hm₂]; exact hout
  · have w1 : Spec.Rsa.wordsAt s₂.mem (addr (arg o 9) candOff) 1 =
        [s₂.mem.readW (addr (arg o 9) candOff + BitVec.ofNat 64 0) 64] := rfl
    rw [show (arg o 9 + BitVec.ofNat 32 candOff).setWidth 64 = addr (arg o 9) candOff from rfl, w1,
      BitVec.add_zero, List.cons.injEq] at hw
    rw [← hm₂]
    refine (halves hw.1 ?_).1.trans ?_
    · split <;> (have := (arg o 6).isLt; omega_arith)
    · unfold candUsed
      rw [rand_length]
      rfl

theorem body_noSp :
    NoSp (Code.seq (.block arguments)
      (.call "vg_ffdh_parameter_candidate_sieved" Impl.Ffdh.X86.Candidate.code) : Prog isa) :=
  NoSp.of_all (by rsa_stack_shape [callee_all])

/-- Back from the frame. -/
theorem Fr.free {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : Fr o ds f s) :
    St o ds f (freed argsBytes s) := by
  refine ⟨h.abi, h.rd, by rw [freed_wr, h.wr]; rfl, h.syms, ?_,
    by rw [freed_gpr _ _ (by decide), h.esi], fun r hr hne => ?_, h.frame, h.words⟩
  · rw [freed_esp, h.esp, BitVec.sub_add_cancel]
  · by_cases hsp : r = .esp
    · subst hsp; rw [freed_esp, h.esp, BitVec.sub_add_cancel]
    · rw [freed_gpr _ _ hsp, h.saved r hr hne hsp]

theorem attempt_ok {p : PPub} {o s : State} {used n : Nat} (h : Live p o used n s) (hu : used < p.randLen) :
    WP isa attempt s fun u => St o liveDs (liveF p (o.gpr .esi) used n) u ∧
      u.gpr .eax = BitVec.ofNat 32 (candidateStatus (candOf o used)) ∧ AttemptOut o used u.mem ∧
      u.mem.readW (addr (arg o 9) candOff) 32 = BitVec.ofNat 32 (candUsed p.bits p.gen p.rand used) := by
  have S := h.st
  obtain ⟨A, rfl⟩ := h.input
  have h1 : 212 ≤ (o.gpr .esp).toNat := A.stackLow
  refine WP.frameAlloc (by decide) (by decide) (by decide) (by rw [S.esp]; unfold argsBytes; omega_arith) body_noSp ?_
  refine WP.seq (WP.mono (arguments_ok S.alloc) fun t ⟨F, a⟩ => ?_)
  exact WP.mono (call_ok F hu a) fun u ⟨F', e, out, cu⟩ =>
    ⟨F'.free, by rw [freed_gpr _ _ (by decide)]; exact e, by rw [freed_mem]; exact out, by rw [freed_mem]; exact cu⟩

end VG.Proof.Ffdh.X86.PSearch
