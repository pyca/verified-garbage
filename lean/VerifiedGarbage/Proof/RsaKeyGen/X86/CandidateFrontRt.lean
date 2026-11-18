module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.FrontRt
public import VerifiedGarbage.Proof.RsaKeyGen.X86.FrontRt.Load
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentRt.Code
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSieveInput
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFinishReady
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateLoadInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateArrays
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateShape
import VerifiedGarbage.Proof.RsaKeyGen.X86.FilterStack
import VerifiedGarbage.Proof.RsaKeyGen.X86.WorkspaceDisjoint
import VerifiedGarbage.Proof.RsaKeyGen.FrameOutside
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory
import VerifiedGarbage.Proof.Framework.X86.Syms
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidatePreparedResult
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.TCB.X86.State
public import VerifiedGarbage.Proof.MillerRabin.X86.WorkspaceFrame
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.MillerRabin.X86.Caller
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Spec.RsaKeyGen
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveStack
public import VerifiedGarbage.Proof.Mont.X86.WordOps
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops2
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessRt.Loop
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Mont.X86.Rt.Step
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Near
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessRt.Blocks
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveStep
import VerifiedGarbage.Proof.RsaKeyGen.TrialFilter
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentRt

/-! ### `RsaKeyGen.X86.CandidateExponentInput`, which this module and modules that import it used -/

section

/-! # Exponent filtering retains all live candidate inputs and the consumed entropy count -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Bignum.X86.PublicContext

theorem exponent_ok {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (D : Drawn E eBytes pBytes entropy s) :
    WP isa VG.Impl.RsaKeyGen.X86.ExponentRt.code s fun t =>
      Drawn E eBytes pBytes entropy t ∧
      t.gpr .eax = BitVec.ofNat 32 (decide (Nat.gcd (candidateValue E entropy - 1) (Spec.Rsa.os2ip eBytes) = 1)).toNat ∧
      val32 t.mem E.base (slot E.width 5) (2 * E.width) = candidateValue E entropy - 1 ∧
      WorkFrame E s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have space : 256 ≤ E.size := v.geometry.headerFit
  have fit : 40 ≤ (s.gpr .esp).toNat := by rw [D.input.stack]; have := v.low; omega_using [this]
  have stack : (s.gpr .esp).toNat ≤ E.base.toNat ∨ E.base.toNat + E.size + 40 ≤ (s.gpr .esp).toNat := by
    rw [D.input.stack]
    rcases v.workspaceStack with h | h <;> omega_using [h]
  have outLen : s.mem.readW (off E.base 4) 32 = BitVec.ofNat 32 (8 * E.width) := by
    rw [D.input.header 1 (by decide), v.length_eq]; rfl
  refine WP.mono_syms (ExponentRt.code_ok D.input.scratch v.width_bounds.1 v.width_bounds.2
    (v.slotFit (by decide : 5 < 28)) D.candidate (by have := candidate_large v entropy; omega_using [this]) (candidate_odd v entropy)
    D.input.exponent_eq (D.input.exponentLength_eq v) (by have := v.exponentLength; omega_using [this]) v.exponentLength.2
    v.exponentFit D.input.memory.exponentRead (v.readWorkspace List.mem_cons_self) fit stack outLen)
    fun t ⟨result, value, saved, W, F, K⟩ syms => ?_
  rw [D.input.memory.exponentBytes] at result
  rw [D.input.stack] at F
  have frame : WorkFrame E s.mem t.mem := VG.X86.Frame.below_mono (wr := [E.workspaceRegion]) (a := 20) F (by decide) v.low
  have low : ∀ r ∈ ExponentRt.ranges E.width, 48 ≤ r.1 := by
    intro r mem
    rcases List.mem_append.mp mem with mem | mem
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl
      · exact Nat.le_trans (by decide) (E.slotHeader 5)
      · decide
    · rcases List.mem_append.mp mem with mem | mem
      · have := ExponentFilter.gcd_ranges_class mem; omega_using [this]
      · obtain rfl := List.mem_singleton.mp mem
        exact Nat.le_trans (by decide) (E.slotHeader 0)
  have I := D.input.keepWorkspace v K (by decide) (by decide) frame W low (by rw [syms])
  have used : t.mem.readW (off E.geometry.W 152) 32 = s.mem.readW (off E.geometry.W 152) 32 :=
    W.read32 (by change 152 + 4 ≤ E.size; omega_using [space]) (by
      intro r mem
      rcases List.mem_append.mp mem with mem | mem
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with rfl | rfl
        · exact Or.inl (by have := E.slotHeader 5; omega)
        · exact Or.inr (by decide)
      · exact ExponentFilter.ranges_apart (by right; constructor <;> decide) mem)
  exact ⟨⟨I, value, (congrArg BitVec.toNat used).trans D.used, (frame.output v).trans D.zeros⟩,
    result, saved, frame, K⟩

end VG.Proof.RsaKeyGen.X86.Candidate

end

end

/-! ### `RsaKeyGen.X86.FrontRt.Sieve`, which this module and modules that import it used -/

section

/-! # Trial division with the candidate's end and the table's length from its run-time length -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.FrontRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.RsaKeyGen.X86.Sieve
open VG.Impl.RsaKeyGen.X86.FrontRt
open VG.Impl.RsaKeyGen.X86.Sieve (tableCount tableAddress stackSlots)

theorem candidateSlots_ok {g : Geometry} (v : g.Valid) {c : Nat} {s : State} (C : Context g c s)
    (pointer : s.gpr .edi = g.candidate) (len : s.gpr .edx = BitVec.ofNat 32 (8 * g.w)) :
    WP isa (.block candidateSlots) s fun t =>
      CandidateReady g c t ∧ Outside (g.sp.setWidth 64) 0 20 s.mem t.mem ∧ Keeps [.eax] s t := by
  change WP isa (.block ([.store (VG.Impl.RsaKeyGen.X86.Sieve.slot 0) .edi] ++ [.mov .eax (.reg .edi),
    .alu .add .eax (.reg .edx), .store (VG.Impl.RsaKeyGen.X86.Sieve.slot 4) .eax])) s _
  refine WP.block_append (WP.mono (C.stack.store 0 (by decide) .edi) fun a ⟨Ma, Oa, Ka, Ca⟩ => ?_)
  refine wp_movS rfl fun b B _ => wp_addS rfl fun d D _ => ?_
  have K : Keeps [.eax] s d := ((Ka.mono (by decide)).widen B.keeps).trans D.keeps
  have Md : d.mem = a.mem := D.mem.trans B.mem
  have value : d.gpr .eax = g.ending := by
    rw [D.gpr, B.gpr, B.other .edx (by decide), Ka.1 .edi (by decide), Ka.1 .edx (by decide), pointer, len]
    rfl
  refine WP.mono ((C.stack.keep K (by decide)).store 4 (by decide) .eax)
    fun t ⟨Mt, Ot, Kt, _⟩ => ?_
  have mem : t.mem = (s.mem.writeW (off (g.sp.setWidth 64) 0) g.candidate).writeW (off (g.sp.setWidth 64) 4) g.ending := by
    rw [Mt, value, Md, Ma, pointer]
  have outside : Outside (g.sp.setWidth 64) 0 20 s.mem t.mem := by
    rw [Md] at Ot
    exact (Oa.mono (by decide) (by decide)).trans (Ot.mono (by decide) (by decide))
  have keep : Keeps [.eax] s t := K.widen Kt
  refine ⟨⟨C.keep v keep (by decide) (outsideStack_frame outside), ?_, ?_⟩, outside, keep⟩
  · rw [mem, stack_write_ne (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [mem, Mem.readW_writeW_self32]

/-- `tableSlots`' branch-free table length. -/
theorem count_value (w : Nat) (bound : w ≤ 128) :
    ((0#32 - (BitVec.ofBool (decide ((BitVec.ofNat 32 (8 * w)).toNat < (129#32 : BitVec 32).toNat))).setWidth 32) &&&
      BitVec.ofInt 32 (-512)) + 1024#32 = BitVec.ofNat 32 (tableCount w) := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [bound])]
  unfold tableCount
  by_cases small : w ≤ 16
  · rw [decide_eq_true (show 8 * w < (129#32 : BitVec 32).toNat by change 8 * w < 129; omega_using [small])]
    simp only [small, ↓reduceIte]
    decide
  · rw [decide_eq_false (show ¬ 8 * w < (129#32 : BitVec 32).toNat by change ¬ 8 * w < 129; omega_using [small])]
    simp only [small, ↓reduceIte]
    decide

theorem tableSlots_ok {g : Geometry} (v : g.Valid) {c : Nat} {s : State} (C : CandidateReady g c s)
    (length : g.limit = tableCount g.w) (pointer : s.gpr .eax = g.table)
    (len : s.gpr .edx = BitVec.ofNat 32 (8 * g.w)) :
    WP isa (.block tableSlots) s fun t =>
      StateAt g c 0 g.limit t ∧ Outside (g.sp.setWidth 64) 0 20 s.mem t.mem ∧ Keeps [.eax] s t := by
  change WP isa (.block ([.store (VG.Impl.RsaKeyGen.X86.Sieve.slot 8) .eax] ++ ([.mov .eax (.reg .edx),
    .alu .cmp .eax (.imm 129), .alu .sbb .eax (.reg .eax), .alu .and .eax (.imm (BitVec.ofInt 32 (-512))),
    .alu .add .eax (.imm 1024)] ++ ([.store (VG.Impl.RsaKeyGen.X86.Sieve.slot 12) .eax] ++
    [.mov .eax (.imm 0), .store (VG.Impl.RsaKeyGen.X86.Sieve.slot 16) .eax])))) s _
  refine WP.block_append (WP.mono (C.context.stack.store 8 (by decide) .eax) fun a ⟨Ma, Oa, Ka, Ca⟩ => ?_)
  refine WP.block_append (wp_movS rfl fun b B _ => wp_cmpCarry rfl fun e E carry =>
    wp_sbbS rfl carry fun f Fs _ => wp_andi fun h H => wp_addS rfl fun u U _ => WP.block_nil ?_)
  have Ku : Keeps [.eax] a u :=
    ((((B.keeps.widen (E.keeps [])).widen Fs.keeps).widen H.keeps).widen U.keeps)
  have Mu : u.mem = a.mem := by rw [U.mem, H.mem, Fs.mem, E.mem, B.mem]
  have edxA : a.gpr .edx = BitVec.ofNat 32 (8 * g.w) := (Ka.1 .edx (by decide)).trans len
  have value : u.gpr .eax = BitVec.ofNat 32 g.limit := by
    have eaxE : e.gpr .eax = BitVec.ofNat 32 (8 * g.w) := by rw [E.gpr, B.gpr, edxA]
    rw [U.gpr, H.gpr, Fs.gpr, eaxE, BitVec.sub_self, B.gpr, edxA, length]
    exact count_value g.w v.widthBound
  have Cu : StackContext g.sp u := Ca.keep Ku (by decide)
  refine WP.block_append (WP.mono (Cu.store 12 (by decide) .eax) fun b' ⟨Mb, Ob, Kb, Cb⟩ => ?_)
  refine WP.mono (Cb.literal 16 (by decide) 0#32) fun t ⟨Mt, Ot, Kt, _⟩ => ?_
  have mem : t.mem = ((s.mem.writeW (off (g.sp.setWidth 64) 8) g.table).writeW
      (off (g.sp.setWidth 64) 12) (BitVec.ofNat 32 g.limit)).writeW (off (g.sp.setWidth 64) 16) 0#32 := by
    rw [Mt, Mb, value, Mu, Ma, pointer]
  rw [Mu] at Ob
  have outside : Outside (g.sp.setWidth 64) 0 20 s.mem t.mem :=
    ((Oa.mono (by decide) (by decide)).trans (Ob.mono (by decide) (by decide))).trans (Ot.mono (by decide) (by decide))
  have keep : Keeps [.eax] s t := (((Ka.mono (by decide)).trans Ku).trans (Kb.mono (by decide))).trans Kt
  refine ⟨⟨C.context.keep v keep (by decide) (outsideStack_frame outside), ?_, ?_, ?_, ?_⟩, outside, keep⟩
  · rw [mem, stack_write_ne (by decide) (by decide) (by decide),
      stack_write_ne (by decide) (by decide) (by decide), stack_write_ne (by decide) (by decide) (by decide)]
    exact C.candidate
  · rw [mem, stack_write_ne (by decide) (by decide) (by decide),
      stack_write_ne (by decide) (by decide) (by decide), stack_write_ne (by decide) (by decide) (by decide)]
    exact C.ending
  · rw [mem, stack_write_ne (by decide) (by decide) (by decide),
      stack_write_ne (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
    unfold Geometry.cursor
    rw [Nat.mul_zero, show BitVec.ofNat 32 0 = 0#32 from rfl, BitVec.add_zero]
  · rw [mem, stack_write_ne (by decide) (by decide) (by decide), Mem.readW_writeW_self32]

theorem setup_ok {g : Geometry} (v : g.Valid) {c : Nat} {s : State} (C : Context g c s)
    (pointer : s.gpr .edi = g.candidate) (len : s.gpr .edx = BitVec.ofNat 32 (8 * g.w))
    (length : g.limit = tableCount g.w)
    (symbol : s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = g.table) (low : 4 ≤ g.sp.toNat)
    (candidateFar : g.candidateRegion.Disjoint (below g.sp 4))
    (tableFar : g.tableRegion.Disjoint (below g.sp 4)) :
    WP isa (.seq (.block candidateSlots) (.seq tableAddress (.block tableSlots))) s
      fun t => StateAt g c 0 g.limit t ∧ Frame (setupWrites g) s.mem t.mem ∧ Keeps [.eax, .ecx] s t := by
  refine WP.seq (WP.mono_syms (candidateSlots_ok v C pointer len) fun a ⟨A, Oa, Ka⟩ Sa => ?_)
  refine WP.seq (WP.mono (symFrame_ok VG.Impl.RsaKeyGen.TrialTable32.symbol a (by rw [A.context.stack.sp]; exact low)) fun b R => ?_)
  have B : CandidateReady g c b :=
    ⟨A.context.keepSymbol v R candidateFar tableFar,
      (symbol_stack_word A.context R low (by decide : 0 + 4 ≤ 20)).trans A.candidate,
      (symbol_stack_word A.context R low (by decide : 4 + 4 ≤ 20)).trans A.ending⟩
  have address : b.gpr .eax = g.table := by rw [R.addr, Sa]; exact symbol
  have symbolFrame : Frame [below g.sp 4] a.mem b.mem := by rw [← A.context.stack.sp]; exact R.frame
  have Kb : Keeps [.eax, .ecx] a b := ⟨R.gpr, R.rd, R.wr⟩
  have edxB : b.gpr .edx = BitVec.ofNat 32 (8 * g.w) := by
    rw [Kb.1 .edx (by decide), Ka.1 .edx (by decide), len]
  refine WP.mono (tableSlots_ok v B length address edxB) fun t ⟨T, Ot, Kt⟩ => ?_
  exact ⟨T, ((setupFrame_stack (outsideStack_frame Oa)).trans (setupFrame_symbol symbolFrame)).trans
    (setupFrame_stack (outsideStack_frame Ot)), ((Ka.mono (by decide)).trans Kb).widen Kt⟩

theorem body_full_ok {g : Geometry} (v : g.Valid) {c : Nat} {s : State} (C : Context g c s)
    (pointer : s.gpr .edi = g.candidate) (len : s.gpr .edx = BitVec.ofNat 32 (8 * g.w))
    (length : g.limit = tableCount g.w)
    (symbol : s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = g.table) (low : 4 ≤ g.sp.toNat)
    (candidateFar : g.candidateRegion.Disjoint (below g.sp 4))
    (tableFar : g.tableRegion.Disjoint (below g.sp 4)) (large : 8161 < c) :
    WP isa sieveBody s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (Spec.RsaKeyGen.obviouslyComposite (64 * g.w) c).toNat ∧
      Frame (setupWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s t ∧
      t.mem.readW (off (g.sp.setWidth 64) 0) 32 = g.candidate := by
  have run := WP.seq (WP.mono (setup_ok v C pointer len length symbol low candidateFar tableFar)
    fun u ⟨U, F, K₀⟩ => WP.mono (loop_full_ok v U) fun t ⟨value, O, K, candidate⟩ =>
      (show t.gpr .eax = BitVec.ofNat 32 (Spec.RsaKeyGen.obviouslyComposite (64 * g.w) c).toNat ∧
        Frame (setupWrites g) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s t ∧
          t.mem.readW (off (g.sp.setWidth 64) 0) 32 = g.candidate from by
        refine ⟨?_, F.trans (setupFrame_stack (outsideStack_frame O)), (K₀.mono (by decide)).trans K, candidate⟩
        rw [length, tableCount, VG.Proof.RsaKeyGen.trialPrefix_spec large] at value
        exact value))
  exact WP.seq (WP.mono (WP.seq_iff.mp (WP.assoc run)) fun a H => WP.assoc H)

theorem sieveInner_ok {g : Geometry} (v : g.Valid) {c : Nat} {s : State} (C : Context g c s)
    (lenRead : readSrc s (.mem (VG.Impl.Mont.X86.sc 4)) = some (BitVec.ofNat 32 (8 * g.w)))
    (pointer : s.gpr .edi + 256#32 = g.candidate) (length : g.limit = tableCount g.w)
    (symbol : s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = g.table) (low : 4 ≤ g.sp.toNat)
    (candidateFar : g.candidateRegion.Disjoint (below g.sp 4))
    (tableFar : g.tableRegion.Disjoint (below g.sp 4)) (large : 8161 < c) :
    WP isa (.seq (.block [.mov .edx (.mem (VG.Impl.Mont.X86.sc 4)), .alu .add .edi (.imm 256)])
      (.seq sieveBody (.block VG.Impl.RsaKeyGen.X86.CandidateSieve.restore))) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (Spec.RsaKeyGen.obviouslyComposite (64 * g.w) c).toNat ∧
      Frame (setupWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  refine WP.seq (wp_movS lenRead fun a A _ => wp_addS rfl fun b B _ => WP.block_nil ?_)
  have Kb : Keeps [.edx, .edi] s b := (A.keeps.mono (by decide)).widen B.keeps
  have Mb : b.mem = s.mem := B.mem.trans A.mem
  have Cb : Context g c b := by
    refine ⟨C.stack.keep Kb (by decide), ?_, ?_, ?_, ?_⟩
    · intro i index; rw [Kb.2.1, Kb.2.2]; exact C.candidateRead i index
    · intro i index d mem; rw [Kb.2.1, Kb.2.2]; exact C.tableRead i index d mem
    · intro i index; rw [Mb]; exact C.tableWords i index
    · rw [Mb]; exact C.candidateValue
  have ediB : b.gpr .edi = g.candidate := by rw [B.gpr, A.other .edi (by decide)]; exact pointer
  have edxB : b.gpr .edx = BitVec.ofNat 32 (8 * g.w) := by rw [B.other .edx (by decide), A.gpr]
  have symB : b.syms = s.syms := B.syms.trans A.syms
  refine WP.seq (WP.mono (body_full_ok v Cb ediB edxB length
    (by rw [symB]; exact symbol) low candidateFar tableFar large) fun d ⟨result, F, Kd, saved⟩ => ?_)
  have Cd := Cb.stack.keep Kd (by decide)
  unfold VG.Impl.RsaKeyGen.X86.CandidateSieve.restore
  refine wp_movS (v := g.candidate) (by
    change readSrc d (.mem (VG.Impl.RsaKeyGen.X86.Sieve.slot 0)) = some g.candidate
    rw [Cd.read 0 (by decide), saved]) fun e E _ => wp_subS rfl fun t T _ => WP.block_nil ?_
  have all : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s t :=
    (((Kb.mono (by decide)).trans Kd).widen E.keeps).widen T.keeps
  have edi : t.gpr .edi = s.gpr .edi := by
    rw [T.gpr, E.gpr, ← pointer]
    exact BitVec.add_sub_cancel _ _
  have K : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
    refine ⟨?_, all.2⟩
    intro r mem
    by_cases same : r = .edi
    · subst r; exact edi
    · exact all.1 r (by cases r <;> simp_all)
  refine ⟨?_, ?_, K⟩
  · rw [T.other .eax (by decide), E.other .eax (by decide)]; exact result
  · rw [Mb] at F
    rw [T.mem, E.mem]
    exact F

theorem sieve_ok {g : Geometry} (v : g.Valid) {c : Nat} {s : State}
    (C : Context g c (allocFrame 20 s)) (fit : 20 ≤ (s.gpr .esp).toNat)
    (lenRead : readSrc (allocFrame 20 s) (.mem (VG.Impl.Mont.X86.sc 4)) = some (BitVec.ofNat 32 (8 * g.w)))
    (pointer : s.gpr .edi + 256#32 = g.candidate) (length : g.limit = tableCount g.w)
    (symbol : s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = g.table) (low : 4 ≤ g.sp.toNat)
    (candidateFar : g.candidateRegion.Disjoint (below g.sp 4))
    (tableFar : g.tableRegion.Disjoint (below g.sp 4)) (large : 8161 < c) :
    WP isa sieve s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (Spec.RsaKeyGen.obviouslyComposite (64 * g.w) c).toNat ∧
      Frame (setupWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold sieve
  refine WP.frameAlloc (by decide) (by decide) (by decide) fit (NoSp.of_all (by rfl)) ?_
  refine WP.mono (sieveInner_ok v C lenRead (by rw [allocFrame_gpr _ _ (by decide)]; exact pointer)
    length symbol low candidateFar tableFar large) fun t ⟨result, F, K⟩ m _ fl => ?_
  exact ⟨by show (freed 20 t).gpr .eax = _; rw [freed_gpr _ _ (by decide)]; exact result,
    F.trans (VG.Proof.RsaKeyGen.X86.Sieve.setupFrame_alloc C fl), FilterStack.freed_keeps K (by decide)⟩

/-- In the sieve's frame: the candidate at `edi + 256` and its length at header byte 4. -/
def SieveIn (g : Geometry) (c : Nat) (s : State) : Prop :=
  Context g c s ∧ s.gpr .edi + 256#32 = g.candidate ∧
    s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = g.table ∧
    readSrc s (.mem (VG.Impl.Mont.X86.sc 4)) = some (BitVec.ofNat 32 (8 * g.w))

/-- Ready for the sieve's body: the candidate at `edi` and its length in `edx`. -/
def BodyIn (g : Geometry) (c : Nat) (s : State) : Prop :=
  Context g c s ∧ s.gpr .edi = g.candidate ∧ s.gpr .edx = BitVec.ofNat 32 (8 * g.w) ∧
    s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = g.table

end VG.Proof.RsaKeyGen.X86.FrontRt

end

end

/-! ### `RsaKeyGen.X86.FrontRt.Other`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.FrontRt.Near`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.NearValues`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.NearTop`, which this module and modules that import it used -/

section

/-! # The native words the separation comparison reads -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Near
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

def word (m : Mem) (base : Addr) (offset : Nat) : BitVec 32 := m.readW (off base offset) 32

end VG.Proof.RsaKeyGen.X86.Near

end

end

/-! # Relate the threshold comparison's bitwise accumulators to native integers -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Near
open VG VG.Proof.Mont

theorem word_zero (x : BitVec 32) : x = 0#32 ↔ x.toNat = 0 :=
  ⟨fun H => congrArg BitVec.toNat H, fun H => BitVec.eq_of_toNat_eq H⟩

theorem high_zero (m : Mem) (base : Addr) (out : Nat) :
    (word m base out ||| word m base (out + 4)) ||| word m base (out + 8) = 0#32 ↔
      val32 m base out 3 = 0 := by
  simp only [BitVec.or_eq_zero_iff, word_zero]
  change ((w32 m base out = 0 ∧ w32 m base (out + 4) = 0) ∧ w32 m base (out + 8) = 0) ↔ _
  simp [val32, Nat.add_assoc, and_assoc, Nat.mul_eq_zero]

theorem low_mask (x : BitVec 32) : (x &&& 0x0fffffff).toNat = x.toNat % 2 ^ 28 := by
  rw [BitVec.toNat_and]
  change x.toNat &&& (2 ^ 28 - 1) = _
  exact Nat.and_two_pow_sub_one_eq_mod ..

theorem low_zero (acc x : BitVec 32) :
    (acc ||| (x &&& 0x0fffffff)).toNat = 0 ↔ acc = 0#32 ∧ x.toNat % 2 ^ 28 = 0 := by
  rw [← word_zero, BitVec.or_eq_zero_iff, word_zero (x &&& 0x0fffffff), low_mask]

theorem nibble_value (x : BitVec 32) : (x >>> 28).toNat = x.toNat / 2 ^ 28 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem nibble_bound (x : BitVec 32) : (x >>> 28).toNat < 16 := by
  rw [nibble_value]
  have := x.isLt
  omega_using []

end VG.Proof.RsaKeyGen.X86.Near

end

end

/-! ### `RsaKeyGen.X86.NearFinish`, which this module and modules that import it used -/

section

/-! # The scalar separation comparison executes without branches -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Near
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Near

theorem finish_ok (s : State) (bound : (s.gpr .ecx).toNat < 16) :
    WP isa (.block finish) s fun t =>
      t.gpr .eax = bit (decide ((s.gpr .ecx).toNat + (decide ((s.gpr .ebx).toNat ≠ 0)).toNat ≤ 1) &&
        decide ((s.gpr .edx).toNat = 0)) ∧ t.mem = s.mem ∧ Keeps [.eax, .ebx, .ecx, .edx] s t := by
  unfold finish
  refine wp_movS rfl fun a A _ => wp_subS rfl fun b B cfB => wp_sbbS rfl cfB fun c C _ => ?_
  have Kc : Keeps [.eax, .ebx] s c := ((A.keeps.mono (by decide)).widen B.keeps).widen C.keeps
  have delta : c.gpr .eax = bit (decide ((s.gpr .ebx).toNat ≠ 0)) := by
    rw [C.gpr, B.other .eax (by decide), A.gpr, A.other .ebx (by decide)]
    exact nonzero_bit _
  refine wp_addS rfl fun d D _ => ?_
  have sum : (d.gpr .ecx).toNat = (s.gpr .ecx).toNat + (decide ((s.gpr .ebx).toNat ≠ 0)).toNat := by
    rw [D.gpr, delta, Kc.1 .ecx (by decide)]
    exact nibble_sum _ _ bound
  refine wp_movS rfl fun e E _ => wp_subS rfl fun f F cfF => wp_adcS rfl cfF fun h H _ => ?_
  have flag : h.gpr .eax = bit (decide ((s.gpr .ecx).toNat + (decide ((s.gpr .ebx).toNat ≠ 0)).toNat ≤ 1)) := by
    rw [H.gpr, F.other .eax (by decide), E.gpr]
    change 0#32 + 0#32 + _ = _
    rw [BitVec.zero_add, BitVec.zero_add, carry_bit, E.other .ecx (by decide), sum]
    congr 1
  have Kh : Keeps [.eax, .ebx, .ecx] s h :=
    ((((Kc.mono (by decide)).widen D.keeps).widen E.keeps).widen F.keeps).widen H.keeps
  refine wp_movS rfl fun i I _ => wp_subS rfl fun j J cfJ => wp_adcS rfl cfJ fun k K _ => ?_
  have high : k.gpr .ecx = bit (decide ((s.gpr .edx).toNat = 0)) := by
    rw [K.gpr, J.other .ecx (by decide), I.gpr]
    change 0#32 + 0#32 + _ = _
    rw [BitVec.zero_add, BitVec.zero_add, carry_bit, I.other .edx (by decide), Kh.1 .edx (by decide)]
    apply congrArg bit
    apply decide_eq_decide.mpr
    change (s.gpr .edx).toNat < 1 ↔ (s.gpr .edx).toNat = 0
    omega_using []
  refine wp_and fun t T => WP.block_nil ?_
  refine ⟨?_, ?_, (((Kh.mono (by decide)).widen I.keeps).widen J.keeps).widen K.keeps |>.widen T.keeps⟩
  · rw [T.gpr, high, K.other .eax (by decide), J.other .eax (by decide), I.other .eax (by decide), flag, bit_and]
  · rw [T.mem, K.mem, J.mem, I.mem, H.mem, F.mem, E.mem, D.mem, C.mem, B.mem, A.mem]

end VG.Proof.RsaKeyGen.X86.Near

end

end

/-! ### `RsaKeyGen.Near`, which only this module used -/

section

/-! # A low-part nonzero bit reduces comparison with a power of two -/

@[expose] public section
namespace VG.Proof.RsaKeyGen

theorem le_power_iff {low high power : Nat} (positive : 0 < power) (bound : low < power) :
    low + power * high ≤ power ↔ high + (decide (low ≠ 0)).toNat ≤ 1 := by
  by_cases zero : low = 0
  · rw [zero, decide_eq_false (by omega_using [] : ¬ (0 : Nat) ≠ 0)]
    change 0 + power * high ≤ power ↔ high + 0 ≤ 1
    constructor
    · intro H
      refine Classical.byContradiction fun bad => ?_
      have := Nat.mul_le_mul_left power (by omega_using [bad] : 2 ≤ high)
      omega_using [positive, H, this]
    · intro H
      have := Nat.mul_le_mul_left power (show high ≤ 1 by omega_using [H])
      omega_using [this]
  · rw [decide_eq_true zero]
    change low + power * high ≤ power ↔ high + 1 ≤ 1
    constructor
    · intro H
      refine Classical.byContradiction fun bad => ?_
      have := Nat.mul_le_mul_left power (by omega_using [bad] : 1 ≤ high)
      omega_using [zero, H, this]
    · intro H
      have : high = 0 := by omega_using [H]
      rw [this, Nat.mul_zero]
      omega_using [bound]

theorem le_power_nibble {low nibble high power : Nat} (positive : 0 < power) (bound : low < power) :
    low + power * (nibble + 16 * high) ≤ power ↔
      high = 0 ∧ nibble + (decide (low ≠ 0)).toNat ≤ 1 := by
  rw [le_power_iff positive bound]
  omega_using []

theorem le_native_threshold {low word high radix : Nat} (positive : 0 < radix) (bound : low < radix) :
    low + radix * (word + 2 ^ 32 * high) ≤ radix * 2 ^ 28 ↔
      high = 0 ∧ word / 2 ^ 28 + (decide (low ≠ 0 ∨ word % 2 ^ 28 ≠ 0)).toNat ≤ 1 := by
  let bottom := low + radix * (word % 2 ^ 28)
  have split := Nat.div_add_mod word (2 ^ 28)
  have remainder := Nat.mod_lt word (by decide : 0 < 2 ^ 28)
  have endBound := Nat.mul_le_mul_left radix (by omega_using [] : word % 2 ^ 28 + 1 ≤ 2 ^ 28)
  rw [Nat.mul_add, Nat.mul_one] at endBound
  have bottomBound : bottom < radix * 2 ^ 28 := by dsimp only [bottom]; omega_using [bound, endBound]
  have rearrange : low + radix * (word + 2 ^ 32 * high) =
      bottom + (radix * 2 ^ 28) * (word / 2 ^ 28 + 16 * high) := by
    dsimp only [bottom]
    rw [show (2 : Nat) ^ 32 = 2 ^ 28 * 16 by decide]
    grind
  have zero : bottom = 0 ↔ low = 0 ∧ word % 2 ^ 28 = 0 := by
    dsimp only [bottom]
    rw [Nat.add_eq_zero_iff, Nat.mul_eq_zero]
    have nz : radix ≠ 0 := Nat.ne_of_gt positive
    simp only [nz, false_or]
  rw [rearrange, le_power_nibble (Nat.mul_pos positive (by decide)) bottomBound]
  have nonzero : decide (bottom ≠ 0) = decide (low ≠ 0 ∨ word % 2 ^ 28 ≠ 0) := by
    apply decide_eq_decide.mpr
    omega_using [zero]
  rw [nonzero]

end VG.Proof.RsaKeyGen

end

end

/-! # Whether `|c − p|` in array 2 is at most the threshold, at the run-time width -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/NearWords32.lean`, which only this module imported.
section

/-! # The RSA separation threshold in native little-endian words -/

section
namespace VG.Proof.RsaKeyGen
open VG VG.Proof.Mont

theorem near_words32 (m : Mem) (base : Addr) (out n : Nat) (positive : 4 ≤ n) :
    val32 m base out n ≤ 2 ^ (32 * n - 100) ↔
      val32 m base (out + 4 * (n - 4) + 4) 3 = 0 ∧
      w32 m base (out + 4 * (n - 4)) / 2 ^ 28 +
        (decide (val32 m base out (n - 4) ≠ 0 ∨
          w32 m base (out + 4 * (n - 4)) % 2 ^ 28 ≠ 0)).toNat ≤ 1 := by
  have split : val32 m base out n = val32 m base out (n - 4) + 2 ^ (32 * (n - 4)) *
      (w32 m base (out + 4 * (n - 4)) + 2 ^ 32 * val32 m base (out + 4 * (n - 4) + 4) 3) := by
    have H := val32_append m base out (n - 4) 4
    rw [show n - 4 + 4 = n by omega] at H
    exact H
  have power : 2 ^ (32 * n - 100) = 2 ^ (32 * (n - 4)) * 2 ^ 28 := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [split, power, le_native_threshold (Nat.two_pow_pos _) (val32_lt ..)]

end VG.Proof.RsaKeyGen
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.FrontRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Impl.Bignum.X86.PublicContext VG.Impl.RsaKeyGen.X86.FrontRt
open VG.Impl.Mont.X86 (sc at_)
open VG.Proof.RsaKeyGen.X86.Near (bit)
local notation "nword" => VG.Proof.RsaKeyGen.X86.Near.word

theorem orScanSetup_ok {W : Addr} {L w : Nat} {s : State} (S : Space W L w s) :
    WP isa (.block (([.mov .ebx (.imm 0)] : List Instr) ++ lenPtr .ebp .edx 2 ++
      ([.mov .ecx (.mem (sc 4)), .shift .shr .ecx 2, .alu .sub .ecx (.imm 4)] : List Instr))) s fun u =>
      PtrAt u W .ebp (slot w 2) ∧ (u.gpr .ecx).toNat = 2 * w - 4 ∧ u.gpr .ebx = 0#32 ∧ u.mem = s.mem ∧
        Keeps [.ebx, .ebp, .ecx, .edx] s u := by
  have width := S.width
  have bound := S.widthBound
  refine WP.block_append (WP.block_append (wp_movS rfl fun a A _ => WP.block_nil ?_))
  have Sa := S.keepMem A.keeps (by decide) (by decide) A.mem
  refine WP.mono (lenPtr_ok Sa 2 (by decide) (by decide : Reg.edx ≠ .ebp) (by decide) (by decide))
    fun b ⟨P, Mb, Kb⟩ => ?_
  have Sb := Sa.keepMem Kb (by decide) (by decide) Mb
  refine wp_movS Sb.lenRead fun c C _ => VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun d D =>
    wp_subS rfl fun u U _ => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, by rw [U.mem, D.mem, C.mem, Mb, A.mem],
    ((((A.keeps.mono (by decide)).trans (Kb.mono (by decide))).widen C.keeps).widen D.keeps).widen U.keeps⟩
  · rw [PtrAt, U.other .ebp (by decide), D.other .ebp (by decide), C.other .ebp (by decide)]; exact P
  · rw [U.gpr, D.gpr, C.gpr, BitVec.toNat_sub, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow, show (4 : BitVec 32).toNat = 4 from rfl]
    omega_using [width, bound]
  · rw [U.other .ebx (by decide), D.other .ebx (by decide), C.other .ebx (by decide), Kb.1 .ebx (by decide), A.gpr]
    rfl

theorem orScan_ok {W : Addr} {L w : Nat} {s : State} (S : Space W L w s) :
    WP isa orScan s fun t =>
      (t.gpr .ebx = 0#32 ↔ val32 s.mem W (slot w 2) (2 * w - 4) = 0) ∧ t.mem = s.mem ∧
        PtrAt t W .ebp (slot w 2 + 4 * (2 * w - 4)) ∧ Keeps [.ebx, .ebp, .ecx, .edx] s t := by
  have width := S.width
  have space := S.space
  have fit : slot w 2 + 8 * w ≤ L := by unfold slot stride VG.Impl.Bignum.hdrBytes at space ⊢; omega_using [space]
  unfold orScan
  refine WP.seq (WP.mono (orScanSetup_ok S) fun u ⟨Pu, cnt, zero, Mu, Ku⟩ => ?_)
  refine WP.mono (orLoop_ok (S.ws.of_keeps Ku) (by omega_using [width]) (by omega_using [fit]) Pu cnt zero) fun t ⟨Z, M, Pt, Kt⟩ => ?_
  rw [Mu] at Z
  exact ⟨Z, M.trans Mu, Pt, Ku.trans (Kt.mono (by decide))⟩

theorem topAt_ok {s : State} {W : Addr} {L x : Nat} (hw : Ws s W L) (P : PtrAt s W .ebp x) (fit : x + 16 ≤ L) :
    WP isa (.block top) s fun t =>
      t.gpr .ecx = nword s.mem W x >>> 28 ∧
      t.gpr .ebx = s.gpr .ebx ||| (nword s.mem W x &&& 0x0fffffff) ∧
      t.gpr .edx = (nword s.mem W (x + 4) ||| nword s.mem W (x + 8)) ||| nword s.mem W (x + 12) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ebx, .ecx, .edx] s t := by
  unfold top
  refine wp_movS (readSrc_ptr hw P (d := 0) (by omega_using [fit])) fun a A _ => wp_movS rfl fun b B _ =>
    VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun c C => wp_andi fun d D => wp_orS rfl fun e E => ?_
  have Ke : Keeps [.eax, .ebx, .ecx] s e :=
    ((((A.keeps.mono (by decide)).widen B.keeps).widen C.keeps).widen D.keeps).widen E.keeps
  have Me : e.mem = s.mem := E.mem.trans (D.mem.trans (C.mem.trans (B.mem.trans A.mem)))
  have Pe : PtrAt e W .ebp x := by rw [PtrAt, Ke.1 .ebp (by decide)]; exact P
  have he := hw.of_keeps Ke
  refine wp_movS (readSrc_ptr he Pe (d := 4) (by omega_using [fit])) fun f F _ => ?_
  have Pf : PtrAt f W .ebp x := by rw [PtrAt, F.other .ebp (by decide)]; exact Pe
  refine wp_orS (readSrc_ptr (he.of_keeps F.keeps) Pf (d := 8) (by omega_using [fit])) fun h H => ?_
  have Ph : PtrAt h W .ebp x := by rw [PtrAt, H.other .ebp (by decide)]; exact Pf
  refine wp_orS (readSrc_ptr ((he.of_keeps F.keeps).of_keeps H.keeps) Ph (d := 12) (by omega_using [fit])) fun t T =>
    WP.block_nil ?_
  refine ⟨?_, ?_, ?_, T.mem.trans (H.mem.trans (F.mem.trans Me)),
    (((Ke.mono (by decide)).widen F.keeps).widen H.keeps).widen T.keeps⟩
  · rw [T.other .ecx (by decide), H.other .ecx (by decide), F.other .ecx (by decide),
      E.other .ecx (by decide), D.other .ecx (by decide), C.gpr, B.gpr, A.gpr, Nat.add_zero]
    rfl
  · rw [T.other .ebx (by decide), H.other .ebx (by decide), F.other .ebx (by decide), E.gpr,
      D.other .ebx (by decide), C.other .ebx (by decide), B.other .ebx (by decide), A.other .ebx (by decide),
      D.gpr, C.other .eax (by decide), B.other .eax (by decide), A.gpr, Nat.add_zero]
    rfl
  · rw [T.gpr, H.gpr, F.gpr, H.mem, F.mem, Me]
    rfl

theorem near_ok {W : Addr} {L w : Nat} {s : State} (S : Space W L w s) :
    WP isa near s fun t =>
      t.gpr .eax = bit (decide (val32 s.mem W (slot w 2) (2 * w) ≤ 2 ^ (32 * (2 * w) - 100))) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  have width := S.width
  have space := S.space
  have fit : slot w 2 + 4 * (2 * w) ≤ L := by unfold slot stride VG.Impl.Bignum.hdrBytes at space ⊢; omega_using [space]
  unfold near
  refine WP.seq (WP.mono (orScan_ok S) fun a ⟨Z, Ma, Pa, Ka⟩ => ?_)
  refine WP.block_append (WP.mono (topAt_ok (S.ws.of_keeps Ka) Pa (by omega_using [width, fit])) fun b ⟨C, Lo, H, Mb, Kb⟩ => ?_)
  rw [Ma] at C Lo H
  have bound : (b.gpr .ecx).toNat < 16 := by rw [C]; exact Near.nibble_bound _
  have nibble : (b.gpr .ecx).toNat = w32 s.mem W (slot w 2 + 4 * (2 * w - 4)) / 2 ^ 28 := by
    rw [C, Near.nibble_value]
    rfl
  have low : (b.gpr .ebx).toNat = 0 ↔ val32 s.mem W (slot w 2) (2 * w - 4) = 0 ∧
      w32 s.mem W (slot w 2 + 4 * (2 * w - 4)) % 2 ^ 28 = 0 := by
    rw [Lo, Near.low_zero, Z]
    rfl
  have high : (b.gpr .edx).toNat = 0 ↔ val32 s.mem W (slot w 2 + 4 * (2 * w - 4) + 4) 3 = 0 := by
    rw [← Near.word_zero, H]
    simpa only [Nat.add_assoc, Nat.reduceAdd] using Near.high_zero s.mem W (slot w 2 + 4 * (2 * w - 4) + 4)
  refine WP.mono (Near.finish_ok b bound) fun t ⟨value, Mt, Kt⟩ => ?_
  refine ⟨?_, Mt.trans (Mb.trans Ma), ((Ka.mono (by decide)).widen Kb).widen Kt⟩
  rw [value, nibble]
  have lowFlag : decide ((b.gpr .ebx).toNat ≠ 0) =
      decide (val32 s.mem W (slot w 2) (2 * w - 4) ≠ 0 ∨ w32 s.mem W (slot w 2 + 4 * (2 * w - 4)) % 2 ^ 28 ≠ 0) :=
    decide_eq_decide.mpr (by omega_using [low])
  rw [lowFlag, decide_eq_decide.mpr high, Bool.and_comm, ← Bool.decide_and]
  apply congrArg bit
  exact decide_eq_decide.mpr (VG.Proof.RsaKeyGen.near_words32 s.mem W (slot w 2) (2 * w) (by omega_using [width])).symm

end VG.Proof.RsaKeyGen.X86.FrontRt

end

end

/-! ### `RsaKeyGen.X86.FrontRt.Close`, which this module and modules that import it used -/

section

/-! # The distance to `p` at the run-time width: the subtractions and the select -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/Difference.lean`, which only this module imported.
section

/-! # Selecting the unborrowed difference computes the required absolute value -/

section
namespace VG.Proof.RsaKeyGen

theorem absDiff_select {c p d e r : Nat} {borrow reverse : Bool}
    (forward : d + p = c + r * borrow.toNat)
    (backward : e + c = p + r * reverse.toNat)
    (dBound : d < r) (eBound : e < r) :
    (if borrow then e else d) = Spec.RsaKeyGen.absDiff c p := by
  cases borrow <;> cases reverse <;>
    simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero,
      Bool.false_eq_true, ↓reduceIte] at forward backward ⊢ <;>
    unfold Spec.RsaKeyGen.absDiff <;> split <;> omega

end VG.Proof.RsaKeyGen
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.FrontRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Impl.Bignum.X86.PublicContext VG.Impl.RsaKeyGen.X86.FrontRt
open VG.Impl.Mont.X86 (sc at_)

/-- In the distance check's frame at `q`: the workspace pointer saved at its
bottom, the frame apart from the workspace. -/
structure Framed (W : Addr) (L w : Nat) (q : BitVec 32) (s : State) : Prop where
  space : Space W L w s
  stack : VG.Proof.RsaKeyGen.X86.Sieve.StackContext q s
  apart : (⟨W, L⟩ : Region).Disjoint ⟨q.setWidth 64, 20⟩
  saved : s.mem.readW (off (q.setWidth 64) 0) 32 = BitVec.ofNat 32 W.toNat

/-- The arrays a check uses: 0, 2, 3 and 4. -/
def Arrays (j : Nat) : Prop := j = 0 ∨ j = 2 ∨ j = 3 ∨ j = 4

theorem Arrays.fit {W : Addr} {L w : Nat} {s : State} (S : Space W L w s) {j : Nat} (A : Arrays j) :
    slot w j + 8 * w ≤ L ∧ 256 ≤ slot w j ∧ j < 32 := by
  have space := S.space
  unfold slot stride VG.Impl.Bignum.hdrBytes at space ⊢
  rcases A with rfl | rfl | rfl | rfl <;> omega_using [space]

theorem Arrays.apart {w : Nat} {i j : Nat} (I : Arrays i) (J : Arrays j) (different : i ≠ j) :
    slot w i + 4 * (2 * w) ≤ slot w j ∨ slot w j + 4 * (2 * w) ≤ slot w i := by
  unfold slot stride VG.Impl.Bignum.hdrBytes
  rcases I with rfl | rfl | rfl | rfl <;> rcases J with rfl | rfl | rfl | rfl <;> first | omega | exact absurd rfl different

theorem Framed.keepMem {W : Addr} {L w : Nat} {q : BitVec 32} {s t : State} (F : Framed W L w q s)
    {rs : List Reg} (K : Keeps rs s t) (edi : .edi ∉ rs) (esp : .esp ∉ rs) (M : t.mem = s.mem) :
    Framed W L w q t :=
  ⟨F.space.keepMem K edi esp M, F.stack.keep K esp, F.apart, by rw [M]; exact F.saved⟩

theorem Framed.edi_value {W : Addr} {L w : Nat} {q : BitVec 32} {s : State} (F : Framed W L w q s) :
    s.gpr .edi = BitVec.ofNat 32 W.toNat := by
  apply BitVec.eq_of_toNat_eq
  have := F.space.scratch.nowrap
  have := F.space.header
  rw [F.space.edi_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]

/-- The frame again once `edi` is back at the workspace. -/
theorem Framed.rebuild {W : Addr} {L w : Nat} {q : BitVec 32} {s t : State} (F : Framed W L w q s)
    {rs : List Reg} (K : Keeps rs s t) (esp : .esp ∉ rs) (edi : t.gpr .edi = s.gpr .edi) {d n : Nat}
    (O : Outside W d n s.mem t.mem) (header : 8 ≤ d) (fit : d + n ≤ L) : Framed W L w q t := by
  have nowrap := F.space.scratch.nowrap
  obtain Fr := VG.Proof.Bignum.outside_frame O (by omega_using [fit, nowrap])
  obtain Sc : Scr t W L := ⟨by rw [edi]; exact F.space.scratch.edi, by rw [K.2.2]; exact F.space.scratch.wr,
    nowrap, by rw [K.1 .esp esp]; exact F.space.scratch.stk⟩
  refine ⟨⟨Sc, F.space.width, F.space.widthBound, F.space.space,
    (BitVec.eq_of_toNat_eq (O.w32 (d := 4) (Or.inl (by omega_using [header])) (by omega_using []))).trans F.space.len⟩,
    ⟨F.stack.ws.of_keeps K, (K.1 .esp esp).trans F.stack.sp⟩, F.apart, ?_⟩
  rw [Fr.readW (r := ⟨q.setWidth 64, 20⟩) ?_ ?_ (by decide)]
  · exact F.saved
  · exact Offset.contains_base _ (by decide) (by decide)
  · intro r mem
    obtain rfl := List.mem_singleton.mp mem
    exact (F.apart.sub_left (Offset.sub_base W fit)).symm

theorem subSetup_ok {W : Addr} {L w : Nat} {q : BitVec 32} {s : State} (F : Framed W L w q s)
    {out a b : Nat} (Io : Arrays out) (Ia : Arrays a) (Ib : Arrays b) :
    WP isa (.block (lenPtr .ebp .edx a ++ lenPtr .ebx .edx b ++ lenPtr .eax .edx out ++
      ([.mov .edx (.mem (sc 4)), .mov .edi (.reg .eax), .mov .ecx (.imm 0)] : List Instr))) s fun u =>
      PtrAt u W .ebp (slot w a) ∧ PtrAt u W .ebx (slot w b) ∧ PtrAt u W .edi (slot w out) ∧
      (u.gpr .edx).toNat = 4 * (2 * w) ∧ u.gpr .ecx = cmask false ∧ u.mem = s.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s u := by
  have S := F.space
  have bound := S.widthBound
  refine WP.block_append (WP.block_append (WP.block_append (WP.mono
    (lenPtr_ok S a (Ia.fit S).2.2 (by decide : Reg.edx ≠ .ebp) (by decide) (by decide)) fun s₁ ⟨Pa, M₁, K₁⟩ => ?_)))
  obtain S₁ := S.keepMem K₁ (by decide) (by decide) M₁
  refine WP.mono (lenPtr_ok S₁ b (Ib.fit S).2.2 (by decide : Reg.edx ≠ .ebx) (by decide) (by decide))
    fun s₂ ⟨Pb, M₂, K₂⟩ => ?_
  obtain S₂ := S₁.keepMem K₂ (by decide) (by decide) M₂
  refine WP.mono (lenPtr_ok S₂ out (Io.fit S).2.2 (by decide : Reg.edx ≠ .eax) (by decide) (by decide))
    fun s₃ ⟨Po, M₃, K₃⟩ => ?_
  obtain S₃ := S₂.keepMem K₃ (by decide) (by decide) M₃
  refine wp_movS S₃.lenRead fun s₄ U₄ _ => wp_movS rfl fun s₅ U₅ _ => wp_movS rfl fun u U _ => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, U.gpr, by rw [U.mem, U₅.mem, U₄.mem, M₃, M₂, M₁], ?_⟩
  · rw [PtrAt, U.other .ebp (by decide), U₅.other .ebp (by decide), U₄.other .ebp (by decide),
      K₃.1 .ebp (by decide), K₂.1 .ebp (by decide)]; exact Pa
  · rw [PtrAt, U.other .ebx (by decide), U₅.other .ebx (by decide), U₄.other .ebx (by decide),
      K₃.1 .ebx (by decide)]; exact Pb
  · rw [PtrAt, U.other .edi (by decide), U₅.gpr, U₄.other .eax (by decide)]; exact Po
  · rw [U.other .edx (by decide), U₅.other .edx (by decide), U₄.gpr, BitVec.toNat_ofNat]; omega_using [bound]
  · exact (((((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (K₃.mono (by decide))).widen U₄.keeps).widen
      U₅.keeps).widen U.keeps

/-- A subtraction's pointers, count and borrow set from the frame at `s`. -/
structure SubSet (W : Addr) (L w : Nat) (q : BitVec 32) (out a b : Nat) (s u : State) : Prop where
  framed : Framed W L w q s
  aPtr : PtrAt u W .ebp (slot w a)
  bPtr : PtrAt u W .ebx (slot w b)
  outPtr : PtrAt u W .edi (slot w out)
  count : (u.gpr .edx).toNat = 4 * (2 * w)
  mask : u.gpr .ecx = cmask false
  mem : u.mem = s.mem
  keeps : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s u

/-- The subtraction's loop and `edi` restored. -/
theorem subRest_ok {W : Addr} {L w : Nat} {q : BitVec 32} {s u : State} {out a b : Nat}
    (H : SubSet W L w q out a b s u) (Io : Arrays out) (Ia : Arrays a) (Ib : Arrays b) (oa : out ≠ a) (ob : out ≠ b) :
    WP isa (.seq subLoop (.block [.mov .edi (.mem (at_ .esp 0))])) u fun t =>
      (∃ c : Bool, t.gpr .ecx = cmask c ∧ val32 t.mem W (slot w out) (2 * w) + val32 s.mem W (slot w b) (2 * w) =
        val32 s.mem W (slot w a) (2 * w) + 2 ^ (32 * (2 * w)) * c.toNat) ∧
      Outside W (slot w out) (4 * (2 * w)) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t ∧
      Framed W L w q t := by
  have F := H.framed
  have S := F.space
  have width := S.width
  have ⟨fo, lo, _⟩ := Io.fit S
  have ⟨fa, _, _⟩ := Ia.fit S
  have ⟨fb, _, _⟩ := Ib.fit S
  have Mu := H.mem
  have Ku := H.keeps
  obtain hw : Ws u W L := S.ws.of_keeps Ku
  obtain hda : slot w out ≤ slot w a ∨ slot w a + 4 * (2 * w) ≤ slot w out := by
    rcases Arrays.apart Io Ia oa with h | h
    · exact Or.inl (Nat.le_trans (Nat.le_add_right _ _) h)
    · exact Or.inr h
  obtain hdm : slot w out ≤ slot w b ∨ slot w b + 4 * (2 * w) ≤ slot w out := by
    rcases Arrays.apart Io Ib ob with h | h
    · exact Or.inl (Nat.le_trans (Nat.le_add_right _ _) h)
    · exact Or.inr h
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86.PublicRt.reduceLoop_ok hw (a := slot w a) (m := slot w b)
    (d := slot w out) (N := 2 * w) (by omega_using [width]) (by omega_using [fa]) (by omega_using [fb]) (by omega_using [fo]) hda hdm H.aPtr H.bPtr H.outPtr
    H.count H.mask) fun v ⟨Ov, _, ⟨c, mask, value⟩, Kv⟩ => ?_)
  rw [Mu] at Ov value
  obtain Kuv : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s v := Ku.trans Kv
  obtain stack := F.stack.keep Kuv (by decide)
  obtain Fr := VG.Proof.Bignum.outside_frame Ov (by have := S.scratch.nowrap; omega_using [fo, this])
  obtain saved : v.mem.readW (off (q.setWidth 64) 0) 32 = BitVec.ofNat 32 W.toNat := by
    rw [Fr.readW (r := ⟨q.setWidth 64, 20⟩) (Offset.contains_base _ (by decide) (by decide)) (by
      intro r mem
      obtain rfl := List.mem_singleton.mp mem
      exact (F.apart.sub_left (Offset.sub_base W (by omega_using [fo]))).symm) (by decide)]
    exact F.saved
  refine wp_movS (stack.read 0 (by decide)) fun t T _ => WP.block_nil ?_
  obtain edi : t.gpr .edi = s.gpr .edi := by rw [T.gpr, saved, F.edi_value]
  obtain Kt : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
    refine ⟨fun r mem => ?_, (Kuv.widen T.keeps).2⟩
    by_cases h : r = .edi
    · subst h; exact edi
    · rw [T.other r h]; exact Kuv.1 r (by simp_all)
  obtain Ot : Outside W (slot w out) (4 * (2 * w)) s.mem t.mem := by rw [T.mem]; exact Ov
  refine ⟨⟨c, by rw [T.other .ecx (by decide)]; exact mask, by rw [T.mem]; exact value⟩, Ot, Kt,
    F.rebuild Kt (by decide) edi Ot (by omega_using [lo]) (by omega_using [fo])⟩

/-- `[out] := [a] − [b]`, its borrow a mask in `ecx`, and the frame again. -/
theorem sub_ok {W : Addr} {L w : Nat} {q : BitVec 32} {s : State} (F : Framed W L w q s)
    {out a b : Nat} (Io : Arrays out) (Ia : Arrays a) (Ib : Arrays b) (oa : out ≠ a) (ob : out ≠ b) :
    WP isa (sub out a b) s fun t =>
      (∃ c : Bool, t.gpr .ecx = cmask c ∧ val32 t.mem W (slot w out) (2 * w) + val32 s.mem W (slot w b) (2 * w) =
        val32 s.mem W (slot w a) (2 * w) + 2 ^ (32 * (2 * w)) * c.toNat) ∧
      Outside W (slot w out) (4 * (2 * w)) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t ∧
      Framed W L w q t := by
  unfold sub
  exact WP.seq (WP.mono (subSetup_ok F Io Ia Ib) fun u ⟨Pa, Pb, Po, cnt, ecx0, Mu, Ku⟩ =>
    subRest_ok ⟨F, Pa, Pb, Po, cnt, ecx0, Mu, Ku⟩ Io Ia Ib oa ob)

theorem arrays0 : Arrays 0 := Or.inl rfl
theorem arrays2 : Arrays 2 := Or.inr (Or.inl rfl)
theorem arrays3 : Arrays 3 := Or.inr (Or.inr (Or.inl rfl))
theorem arrays4 : Arrays 4 := Or.inr (Or.inr (Or.inr rfl))

/-- The select's pointers, count and mask set from the frame at `s`. -/
structure SelectSet (W : Addr) (L w : Nat) (q : BitVec 32) (k : Bool) (s u : State) : Prop where
  framed : Framed W L w q s
  fromPtr : PtrAt u W .ebp (slot w 3)
  toPtr : PtrAt u W .ebx (slot w 2)
  count : (u.gpr .edi).toNat = 4 * (2 * w)
  mask : u.gpr .ecx = cmask k
  mem : u.mem = s.mem
  keeps : Keeps [.ebx, .ecx, .edx, .ebp, .edi] s u

theorem selectSetup_ok {W : Addr} {L w : Nat} {q : BitVec 32} {s : State} (F : Framed W L w q s) {k : Bool}
    (mask : s.gpr .esi = cmask k) :
    WP isa (.block (lenPtr .ebp .edx 3 ++ lenPtr .ebx .edx 2 ++
      ([.mov .edi (.mem (sc 4)), .mov .ecx (.reg .esi)] : List Instr))) s (SelectSet W L w q k s) := by
  have S := F.space
  have width := S.width
  have bound := S.widthBound
  refine WP.block_append (WP.block_append (WP.mono
    (lenPtr_ok S 3 (by decide) (by decide : Reg.edx ≠ .ebp) (by decide) (by decide)) fun s₁ ⟨P₃, M₁, K₁⟩ => ?_))
  obtain S₁ := S.keepMem K₁ (by decide) (by decide) M₁
  refine WP.mono (lenPtr_ok S₁ 2 (by decide) (by decide : Reg.edx ≠ .ebx) (by decide) (by decide))
    fun s₂ ⟨P₂, M₂, K₂⟩ => ?_
  obtain S₂ := S₁.keepMem K₂ (by decide) (by decide) M₂
  refine wp_movS S₂.lenRead fun s₃ U₃ _ => wp_movS rfl fun u U _ => WP.block_nil ?_
  refine ⟨F, ?_, ?_, ?_, ?_, by rw [U.mem, U₃.mem, M₂, M₁],
    (((K₁.mono (by decide)).trans (K₂.mono (by decide))).widen U₃.keeps).widen U.keeps⟩
  · rw [PtrAt, U.other .ebp (by decide), U₃.other .ebp (by decide), K₂.1 .ebp (by decide)]; exact P₃
  · rw [PtrAt, U.other .ebx (by decide), U₃.other .ebx (by decide)]; exact P₂
  · rw [U.other .edi (by decide), U₃.gpr, BitVec.toNat_ofNat]; omega_using [bound]
  · rw [U.gpr, U₃.other .esi (by decide), K₂.1 .esi (by decide), K₁.1 .esi (by decide), mask]

/-- The select's loop and `edi` restored. -/
theorem selectRest_ok {W : Addr} {L w : Nat} {q : BitVec 32} {k : Bool} {s u : State}
    (H : SelectSet W L w q k s u) :
    WP isa (.seq selectLoop (.block [.mov .edi (.mem (at_ .esp 0))])) u
      fun t => val32 t.mem W (slot w 2) (2 * w) =
          (if k then val32 s.mem W (slot w 3) (2 * w) else val32 s.mem W (slot w 2) (2 * w)) ∧
        Outside W (slot w 2) (4 * (2 * w)) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t ∧
        Framed W L w q t := by
  have F := H.framed
  have S := F.space
  have width := S.width
  have ⟨f2, l2, _⟩ := arrays2.fit S
  have ⟨f3, l3, _⟩ := arrays3.fit S
  have Ku := H.keeps
  have Mu := H.mem
  obtain apart : slot w 2 + 4 * (2 * w) ≤ slot w 3 ∨ slot w 3 + 4 * (2 * w) ≤ slot w 2 :=
    Arrays.apart arrays2 arrays3 (by decide)
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86.PublicRt.selectLoop_ok (S.ws.of_keeps Ku) k (x := slot w 3)
    (d := slot w 2) (N := 2 * w) (by omega_using [width]) (by omega_using [f3]) (by omega_using [f2]) apart H.fromPtr H.toPtr H.count H.mask)
    fun v ⟨Ov, value, _, Kv⟩ => ?_)
  rw [Mu] at Ov value
  obtain Kuv : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s v := (Ku.mono (by decide)).trans (Kv.mono (by decide))
  obtain stack := F.stack.keep Kuv (by decide)
  obtain Fr := VG.Proof.Bignum.outside_frame Ov (by have := S.scratch.nowrap; omega_using [f2, this])
  obtain saved : v.mem.readW (off (q.setWidth 64) 0) 32 = BitVec.ofNat 32 W.toNat := by
    rw [Fr.readW (r := ⟨q.setWidth 64, 20⟩) (Offset.contains_base _ (by decide) (by decide)) (by
      intro r mem
      obtain rfl := List.mem_singleton.mp mem
      exact (F.apart.sub_left (Offset.sub_base W (by omega_using [f2]))).symm) (by decide)]
    exact F.saved
  refine wp_movS (stack.read 0 (by decide)) fun t T _ => WP.block_nil ?_
  obtain edi : t.gpr .edi = s.gpr .edi := by rw [T.gpr, saved, F.edi_value]
  obtain Kt : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
    refine ⟨fun r mem => ?_, (Kuv.widen T.keeps).2⟩
    by_cases h : r = .edi
    · subst h; exact edi
    · rw [T.other r h]; exact Kuv.1 r (by simp_all)
  obtain Ot : Outside W (slot w 2) (4 * (2 * w)) s.mem t.mem := by rw [T.mem]; exact Ov
  exact ⟨by rw [T.mem]; exact value, Ot, Kt, F.rebuild Kt (by decide) edi Ot (by omega_using [l2]) (by omega_using [f2])⟩

/-- `[2] := [3]` where the mask `ecx` (saved in `esi`) is all ones, and the frame again. -/
theorem select_ok {W : Addr} {L w : Nat} {q : BitVec 32} {s : State} (F : Framed W L w q s) {k : Bool}
    (mask : s.gpr .esi = cmask k) :
    WP isa (.seq (.block (lenPtr .ebp .edx 3 ++ lenPtr .ebx .edx 2 ++
      ([.mov .edi (.mem (sc 4)), .mov .ecx (.reg .esi)] : List Instr))) (.seq selectLoop (.block [.mov .edi (.mem (at_ .esp 0))]))) s
      fun t => val32 t.mem W (slot w 2) (2 * w) =
          (if k then val32 s.mem W (slot w 3) (2 * w) else val32 s.mem W (slot w 2) (2 * w)) ∧
        Outside W (slot w 2) (4 * (2 * w)) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t ∧
        Framed W L w q t :=
  WP.seq (WP.mono (selectSetup_ok F mask) fun _ H => selectRest_ok H)

/-- `|c − p|` into array 2, through array 3. -/
theorem difference_ok {W : Addr} {L w : Nat} {q : BitVec 32} {s : State} (F : Framed W L w q s) :
    WP isa difference s fun t =>
      val32 t.mem W (slot w 2) (2 * w) =
        Spec.RsaKeyGen.absDiff (val32 s.mem W (slot w 0) (2 * w)) (val32 s.mem W (slot w 4) (2 * w)) ∧
      Outs W [(slot w 2, 4 * (2 * w)), (slot w 3, 4 * (2 * w))] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t ∧ Framed W L w q t := by
  have S := F.space
  have nowrap := S.scratch.nowrap
  have ⟨f0, l0, _⟩ := arrays0.fit S
  have ⟨f2, l2, _⟩ := arrays2.fit S
  have ⟨f3, l3, _⟩ := arrays3.fit S
  have ⟨f4, l4, _⟩ := arrays4.fit S
  unfold difference
  refine WP.seq (WP.mono (sub_ok F arrays2 arrays0 arrays4 (by decide) (by decide))
    fun u ⟨⟨borrow, mask, forward⟩, Ou, Ku, Fu⟩ => ?_)
  refine WP.seq (wp_movS rfl fun v V _ => WP.block_nil ?_)
  obtain Fv := Fu.keepMem V.keeps (by decide) (by decide) V.mem
  refine WP.seq (WP.mono (sub_ok Fv arrays3 arrays4 arrays0 (by decide) (by decide))
    fun z ⟨⟨reverse, _, backward⟩, Oz, Kz, Fz⟩ => ?_)
  obtain maskZ : z.gpr .esi = cmask borrow := by rw [Kz.1 .esi (by decide), V.gpr, mask]
  refine WP.mono (select_ok Fz maskZ) fun t ⟨value, Ot, Kt, Ft⟩ => ?_
  obtain a02 := Arrays.apart arrays0 arrays2 (w := w) (by decide)
  obtain a42 := Arrays.apart arrays4 arrays2 (w := w) (by decide)
  obtain a03 := Arrays.apart arrays0 arrays3 (w := w) (by decide)
  obtain a43 := Arrays.apart arrays4 arrays3 (w := w) (by decide)
  obtain a23 := Arrays.apart arrays2 arrays3 (w := w) (by decide)
  obtain aSame : val32 v.mem W (slot w 0) (2 * w) = val32 s.mem W (slot w 0) (2 * w) := by
    rw [V.mem]; exact Ou.val32 a02 (by omega_using [nowrap, f0, l0, f2, l2, f3, l3, f4, l4, a02, a42, a03, a43, a23])
  obtain bSame : val32 v.mem W (slot w 4) (2 * w) = val32 s.mem W (slot w 4) (2 * w) := by
    rw [V.mem]; exact Ou.val32 a42 (by omega_using [nowrap, f0, l0, f2, l2, f3, l3, f4, l4, a02, a42, a03, a43, a23])
  rw [aSame, bSame] at backward
  obtain dSame : val32 z.mem W (slot w 2) (2 * w) = val32 u.mem W (slot w 2) (2 * w) := by
    rw [Oz.val32 (by rcases a23 with h | h; exact Or.inl h; exact Or.inr h) (by omega_using [nowrap, f0, l0, f2, l2, f3, l3, f4, l4, a02, a42, a03, a43, a23]), V.mem]
  obtain values : val32 t.mem W (slot w 2) (2 * w) =
      if borrow then val32 z.mem W (slot w 3) (2 * w) else val32 u.mem W (slot w 2) (2 * w) := by
    rw [value]
    cases borrow
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact dSame
    · rfl
  obtain K₁ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s v := (Ku.mono (by decide)).widen V.keeps
  obtain K₂ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := (K₁.trans (Kz.mono (by decide))).trans (Kt.mono (by decide))
  refine ⟨values.trans (VG.Proof.RsaKeyGen.absDiff_select forward backward (val32_lt ..) (val32_lt ..)), ?_,
    K₂, Ft⟩
  obtain O₁ : Outs W [(slot w 2, 4 * (2 * w)), (slot w 3, 4 * (2 * w))] s.mem v.mem := by
    rw [V.mem]; exact Outs.of_outside Ou (by simp)
  obtain O₂ : Outs W [(slot w 2, 4 * (2 * w)), (slot w 3, 4 * (2 * w))] v.mem z.mem :=
    Outs.of_outside Oz (by simp)
  exact (O₁.trans O₂).trans (Outs.of_outside Ot (by simp))

end VG.Proof.RsaKeyGen.X86.FrontRt

end

end

/-! # A supplied prime imported into array 4, and its distance to the candidate checked in a frame -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.FrontRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Bignum.X86.PublicContext VG.Impl.RsaKeyGen.X86.FrontRt
open VG.Impl.Mont.X86 (sc at_)

theorem other_ok {W : Addr} {L w : Nat} {s : State} (S : Space W L w s)
    (fit : 40 ≤ (s.gpr .esp).toNat)
    (separateStack : (s.gpr .esp).toNat ≤ W.toNat ∨ W.toNat + L + 40 ≤ (s.gpr .esp).toNat)
    {p : BitVec 32} (pointer : s.mem.readW (off W 20) 32 = p)
    (sourceFit : p.toNat + 8 * w ≤ 2 ^ 32)
    (readable : InRegions (s.rd ++ s.wr) (p.setWidth 64) (8 * w))
    (separate : (⟨p.setWidth 64, 8 * w⟩ : Region).Disjoint ⟨W, L⟩) :
    WP isa other s fun t =>
      t.gpr .eax = Near.bit (Spec.RsaKeyGen.tooClose (64 * w)
        (some (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (p.setWidth 64) (8 * w))))
        (val32 s.mem W (slot w 0) (2 * w))) ∧
      Frame [⟨W, L⟩, below (s.gpr .esp) 20] s.mem t.mem ∧
      WorkspaceFrame ⟨W, L, w⟩ [(slot w 4, 8 * w), (slot w 2, 8 * w), (slot w 3, 8 * w)] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have nowrap := S.scratch.nowrap
  have head := S.header
  have ⟨f0, l0, _⟩ := arrays0.fit S
  have ⟨f2, l2, _⟩ := arrays2.fit S
  have ⟨f3, l3, _⟩ := arrays3.fit S
  have ⟨f4, l4, _⟩ := arrays4.fit S
  obtain a04 := Arrays.apart arrays0 arrays4 (w := w) (by decide)
  unfold other
  refine WP.seq (wp_movS (readSrc_sc S.scratch (d := 20) (by omega_using [head])) fun a A _ => WP.block_nil ?_)
  obtain Sa := S.keepMem A.keeps (by decide) (by decide) A.mem
  refine WP.seq (WP.mono (importAt_ok Sa 4 (by decide) f4 (A.gpr.trans pointer)
      sourceFit (by rw [A.keeps.2.1, A.keeps.2.2]; exact readable) separate) fun b ⟨value, Fb, Kb⟩ => ?_)
  rw [A.mem] at value Fb
  obtain Ob : Outside W (slot w 4) (8 * w) s.mem b.mem := VG.Proof.RsaKeyGen.frame_outside Fb (by omega_using [separateStack, sourceFit, nowrap, head, f0, l0, f2, l2, f3, l3, f4, l4, a04])
  obtain lenB : b.mem.readW (off W 4) 32 = a.mem.readW (off W 4) 32 := by
    rw [A.mem]; exact BitVec.eq_of_toNat_eq (Ob.w32 (d := 4) (Or.inl (by omega_using [l4])) (by omega_using []))
  obtain Sb := Sa.keep Kb (by decide) (by decide) lenB
  obtain Kab : Keeps [.eax, .ebx, .esi, .ecx, .edx] s b := (A.keeps.mono (by decide)).trans Kb
  obtain spB : b.gpr .esp = s.gpr .esp := Kab.1 .esp (by decide)
  refine WP.frameAlloc (by decide) (by decide) (by decide) (by rw [spB]; omega_using [fit]) (NoSp.of_all (by rfl)) ?_
  obtain St := FilterStack.allocated_context (s := b) (by rw [spB]; omega_using [fit])
  obtain apartQ : (⟨W, L⟩ : Region).Disjoint ⟨(b.gpr .esp - 20#32).setWidth 64, 20⟩ :=
    FilterStack.allocated_apart (by rw [spB]; omega_using [fit]) nowrap (by rw [spB]; rcases separateStack with h | h; exact Or.inl h; exact Or.inr (by omega_using [h]))
  obtain Sc : Space W L w (allocFrame 20 b) :=
    ⟨FilterStack.allocated_scratch Sb.scratch (by rw [spB]; omega_using [fit]) (by rw [spB]; rcases separateStack with h | h; exact Or.inl h; exact Or.inr (by omega_using [h])),
      Sb.width, Sb.widthBound, Sb.space, Sb.len⟩
  obtain ediB : b.gpr .edi = BitVec.ofNat 32 W.toNat := by
    apply BitVec.eq_of_toNat_eq
    rw [Sb.edi_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [nowrap, head])]
  refine WP.seq (WP.mono (St.store 0 (by decide) .edi) fun c ⟨Mc, Oc, Kc, Stc⟩ => ?_)
  obtain Fc := VG.Proof.Bignum.outside_frame Oc (by decide)
  obtain Wc : WorkspaceFrame ⟨W, L, w⟩ [] b.mem c.mem := by
    obtain H := VG.Proof.RsaKeyGen.X86.workspace_of_frame (g := ⟨W, L, w⟩) Fc nowrap (by
      intro r mem
      obtain rfl := List.mem_singleton.mp mem
      exact apartQ.sub_right (Offset.sub_base _ (by decide)))
    exact H
  obtain Fcx : Framed W L w (b.gpr .esp - 20#32) c := by
    refine ⟨Sc.keep Kc (by decide) (by decide) (Wc.read32 (d := 4) (by change 4 + 4 ≤ L; omega_using [head]) (fun _ mem => nomatch mem)),
      Stc, apartQ, ?_⟩
    rw [Mc, Mem.readW_writeW_self32, allocFrame_gpr _ _ (by decide), ediB]
  refine WP.seq (WP.mono (difference_ok Fcx) fun d ⟨D, Od, Kd, Fd⟩ => ?_)
  refine WP.mono (near_ok Fd.space) fun t ⟨result, Mt, Kt⟩ m _ fl => ?_
  rw [show 4 * (2 * w) = 8 * w by omega_using []] at Od
  obtain cand : val32 c.mem W (slot w 0) (2 * w) = val32 s.mem W (slot w 0) (2 * w) := by
    rw [Wc.val32 (d := slot w 0) (n := 2 * w) (by change _ ≤ L; omega_using [f0]) (fun _ mem => nomatch mem)]
    exact Ob.val32 (by rcases a04 with h | h; exact Or.inl h; exact Or.inr (by omega_using [h])) (by omega_using [separateStack, sourceFit, nowrap, head, f0, l0, f2, l2, f3, l3, f4, l4, a04])
  obtain prime : val32 c.mem W (slot w 4) (2 * w) = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (p.setWidth 64) (8 * w)) := by
    rw [Wc.val32 (d := slot w 4) (n := 2 * w) (by change _ ≤ L; omega_using [f4]) (fun _ mem => nomatch mem)]
    exact value
  rw [Mt] at fl
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (freed 20 t).gpr .eax = _
    rw [freed_gpr _ _ (by decide), result, D, cand, prime, show 32 * (2 * w) = 64 * w by omega_using []]
    rfl
  · show Frame _ s.mem m
    obtain F1 : Frame [⟨W, L⟩, below (s.gpr .esp) 20] s.mem b.mem :=
      Fb.sub fun r mem => by
        obtain rfl := List.mem_singleton.mp mem
        exact ⟨_, List.mem_cons_self, Offset.sub_base W f4⟩
    obtain F2 : Frame [⟨W, L⟩, below (s.gpr .esp) 20] b.mem c.mem := by
      change Frame _ b.mem c.mem at Fc
      refine Fc.sub fun r mem => ?_
      obtain rfl := List.mem_singleton.mp mem
      refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
      rw [spB]
      exact Offset.sub_base _ (by decide)
    obtain F3 : Frame [⟨W, L⟩, below (s.gpr .esp) 20] c.mem d.mem :=
      (workspaceGlobalFrame (g := ⟨W, L, w⟩) Od (by
        intro r mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with rfl | rfl
        · exact f2
        · exact f3)).mono fun r mem => by
          obtain rfl := List.mem_singleton.mp mem
          exact List.mem_cons_self
    refine ((F1.trans F2).trans F3).trans (fl.mono fun r mem => ?_)
    rw [List.mem_singleton.mp mem, spB]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  · show WorkspaceFrame _ _ s.mem m
    obtain W1 : WorkspaceFrame ⟨W, L, w⟩ [(slot w 4, 8 * w), (slot w 2, 8 * w), (slot w 3, 8 * w)] s.mem b.mem :=
      WorkspaceFrame.of_outs nowrap (Outs.of_outside Ob List.mem_cons_self)
    obtain W2 : WorkspaceFrame ⟨W, L, w⟩ [(slot w 4, 8 * w), (slot w 2, 8 * w), (slot w 3, 8 * w)] b.mem c.mem := by
      exact Wc.mono fun _ mem => nomatch mem
    obtain W3 : WorkspaceFrame ⟨W, L, w⟩ [(slot w 4, 8 * w), (slot w 2, 8 * w), (slot w 3, 8 * w)] c.mem d.mem :=
      (WorkspaceFrame.of_outs (g := ⟨W, L, w⟩) nowrap Od).mono fun r mem => List.mem_cons_of_mem _ mem
    obtain W4 : WorkspaceFrame ⟨W, L, w⟩ [(slot w 4, 8 * w), (slot w 2, 8 * w), (slot w 3, 8 * w)] d.mem m :=
      (VG.Proof.RsaKeyGen.X86.workspace_of_frame (g := ⟨W, L, w⟩) fl nowrap (by
        intro r mem
        obtain rfl := List.mem_singleton.mp mem
        exact apartQ)).mono fun _ mem => nomatch mem
    exact ((W1.trans W2).trans W3).trans W4
  · have Kin : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] (allocFrame 20 b) t :=
      ((Kc.mono (by decide)).trans Kd).trans (Kt.mono (by decide))
    exact (Kab.mono (by decide)).trans (FilterStack.freed_keeps Kin (by decide))

theorem close_ok {W : Addr} {L w : Nat} {s : State} (S : Space W L w s)
    (fit : 40 ≤ (s.gpr .esp).toNat)
    (separateStack : (s.gpr .esp).toNat ≤ W.toNat ∨ W.toNat + L + 40 ≤ (s.gpr .esp).toNat)
    {p plen : BitVec 32} (pointer : s.mem.readW (off W 20) 32 = p)
    (lengthEq : s.mem.readW (off W 24) 32 = plen)
    (source : plen ≠ 0#32 → p.toNat + 8 * w ≤ 2 ^ 32 ∧
      InRegions (s.rd ++ s.wr) (p.setWidth 64) (8 * w) ∧
      (⟨p.setWidth 64, 8 * w⟩ : Region).Disjoint ⟨W, L⟩) :
    WP isa close s fun t =>
      t.gpr .eax = Near.bit (Spec.RsaKeyGen.tooClose (64 * w)
        (if plen = 0#32 then none else some (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (p.setWidth 64) (8 * w))))
        (val32 s.mem W (slot w 0) (2 * w))) ∧
      Frame [⟨W, L⟩, below (s.gpr .esp) 20] s.mem t.mem ∧
      WorkspaceFrame ⟨W, L, w⟩ [(slot w 4, 8 * w), (slot w 2, 8 * w), (slot w 3, 8 * w)] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have head := S.header
  unfold close
  refine WP.seq (wp_movS (readSrc_sc S.scratch (d := 24) (by omega_using [head])) fun a A _ =>
    wp_cmpS rfl fun b B Z => WP.block_nil ?_)
  obtain K : Keeps [.eax] s b := A.keeps.widen (B.keeps [])
  obtain M : b.mem = s.mem := B.mem.trans A.mem
  obtain condition : isa.eval .e b = some (decide (plen = 0#32)) := by
    change b.zf = _
    rw [Z, A.gpr, lengthEq]
    change some (plen - 0#32 == 0#32) = _
    rw [BitVec.sub_zero]
    rfl
  obtain spB : b.gpr .esp = s.gpr .esp := K.1 .esp (by decide)
  by_cases absent : plen = 0#32
  · refine WP.ite true (by rw [condition, decide_eq_true absent]) (fun _ => ?_) (fun impossible => nomatch impossible)
    refine wp_movS rfl fun t T _ => WP.block_nil ?_
    obtain Mt : t.mem = s.mem := T.mem.trans M
    refine ⟨?_, by rw [Mt]; exact Frame.refl _ _, by rw [Mt]; exact WorkspaceFrame.refl _ _ _,
      (K.mono (by decide)).widen T.keeps⟩
    rw [T.gpr]
    simp only [absent, ↓reduceIte, Spec.RsaKeyGen.tooClose, Near.bit, Bool.toNat_false]
    rfl
  · refine WP.ite false (by rw [condition, decide_eq_false absent]) (fun impossible => nomatch impossible) (fun _ => ?_)
    obtain ⟨sourceFit, readable, separate⟩ := source absent
    refine WP.mono (other_ok (S.keepMem K (by decide) (by decide) M) (by rw [spB]; exact fit)
      (by rw [spB]; exact separateStack) (by rw [M]; exact pointer) sourceFit
      (by rw [K.2.1, K.2.2]; exact readable) separate) fun t ⟨result, F, Wt, Kt⟩ => ?_
    rw [M] at result F Wt
    rw [spB] at F
    exact ⟨by simpa only [absent, ↓reduceIte] using result, F, Wt, (K.mono (by decide)).trans Kt⟩

/-- A supplied prime's source, at header byte 20. -/
structure OtherIn (W : Addr) (L w : Nat) (q p : BitVec 32) (s : State) : Prop where
  base : Base W L w q s
  pointer : s.mem.readW (off W 20) 32 = p
  sourceFit : p.toNat + 8 * w ≤ 2 ^ 32
  readable : InRegions (s.rd ++ s.wr) (p.setWidth 64) (8 * w)
  separate : (⟨p.setWidth 64, 8 * w⟩ : Region).Disjoint ⟨W, L⟩

/-- The distance check's inputs: `p` at header byte 20 and its length at 24. -/
structure CloseIn (W : Addr) (L w : Nat) (q p plen : BitVec 32) (s : State) : Prop where
  base : Base W L w q s
  pointer : s.mem.readW (off W 20) 32 = p
  length : s.mem.readW (off W 24) 32 = plen
  source : plen ≠ 0#32 → p.toNat + 8 * w ≤ 2 ^ 32 ∧
    InRegions (s.rd ++ s.wr) (p.setWidth 64) (8 * w) ∧ (⟨p.setWidth 64, 8 * w⟩ : Region).Disjoint ⟨W, L⟩

end VG.Proof.RsaKeyGen.X86.FrontRt

end

end

/-! ### `RsaKeyGen.X86.CandidateSizedResult`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.CandidateCloseInput`, which this module and modules that import it used -/

section

/-! # Optional-prime distance filtering retains the drawn candidate and input snapshots -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Bignum.X86.PublicContext

theorem MemoryFacts.other_choice {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (M : MemoryFacts E eBytes pBytes entropy s) :
    (if BitVec.ofNat 32 E.otherLength = 0#32 then none else
      some (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (E.other.setWidth 64) (8 * E.width)))) = Spec.RsaKeyGen.otherPrime pBytes := by
  have pLength : pBytes.length = E.otherLength := by rw [← M.otherBytes]; exact VG.Proof.Bignum.bytesAt_length _ _ _
  have lengthBound : E.otherLength < 2 ^ 32 := by
    have prime := v.length; unfold Spec.RsaKeyGen.primeLenValid at prime
    have := v.otherLength; omega_using [prime, this]
  by_cases empty : E.otherLength = 0
  · have pEmpty : pBytes = [] := List.length_eq_zero_iff.mp (by rw [pLength, empty])
    rw [empty, pEmpty]
    rfl
  · have lengthEq : E.otherLength = E.length := v.otherLength.resolve_left empty
    have pNonempty : pBytes ≠ [] := by intro nil; rw [nil] at pLength; exact empty pLength.symm
    have nativeNonzero : BitVec.ofNat 32 E.otherLength ≠ 0#32 := by
      intro zero
      have H := congrArg BitVec.toNat zero
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt lengthBound] at H
      exact empty H
    simp only [nativeNonzero, ↓reduceIte, Spec.RsaKeyGen.otherPrime, pNonempty]
    rw [v.length_eq, ← lengthEq, M.otherBytes]

end VG.Proof.RsaKeyGen.X86.Candidate

end

end

/-! ### `RsaKeyGen.X86.CandidateSieveResult`, which this module and modules that import it used -/

section

/-! # Trial division: the status 3 written, or `eax = 4` to go on -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidateExponentResult.lean`, which only this module imported.
section

/-! # Coprimality rejection, at a run-time width, and prepared primality testing for the width compose -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Bignum.X86.PublicContext (slot)

def ExponentOutputs (E : Environment) (e : Nat) (entropy : List Byte) (s : State) : Prop :=
  if Nat.gcd (candidateValue E entropy - 1) e = 1 then PrimalityOutputs E (candidateValue E entropy) entropy s
  else Outputs E 3 E.length (List.replicate E.length 0) s

theorem exponent_result_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (D : Drawn E eBytes pBytes entropy s) (enough : E.length ≤ E.randLength) :
    WP isa (VG.Impl.RsaKeyGen.X86.Candidate.exponentCheck montName mont roundName round) s fun t =>
      ExponentOutputs E (Spec.Rsa.os2ip eBytes) entropy t ∧ MutableFrame E s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  unfold VG.Impl.RsaKeyGen.X86.Candidate.exponentCheck
  refine WP.seq (WP.mono (exponent_ok v D) fun a ⟨Da, flag, saved, F, K⟩ => ?_)
  refine WP.seq (WP.mono (cmp_bool flag) fun b ⟨B, cond, _⟩ => ?_)
  have Db := Da.keepMem v B.mem (B.keeps []) (by decide) (by decide) B.syms
  have Fb : MutableFrame E s.mem b.mem := by rw [B.mem]; exact F.mutable
  have Kb : Keeps WitnessStep.clob s b := (K.mono (by unfold WitnessStep.clob; decide)).widen (B.keeps [])
  by_cases good : Nat.gcd (candidateValue E entropy - 1) (Spec.Rsa.os2ip eBytes) = 1
  · refine WP.ite false (by rw [cond, decide_eq_true good]; rfl) (fun bad => nomatch bad) (fun _ => ?_)
    refine WP.mono (tested_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v Db
      (by rw [B.mem]; exact saved) enough) fun t ⟨output, Ft, Kt⟩ => ?_
    exact ⟨by simpa only [ExponentOutputs, good, ↓reduceIte] using output, Fb.trans Ft, Kb.trans Kt⟩
  · refine WP.ite true (by rw [cond, decide_eq_false good]; rfl) (fun _ => ?_) (fun bad => nomatch bad)
    refine WP.mono (finish_used_ok (status := 3) v (Db.finishReady v)) fun t ⟨output, Ft, Kt⟩ => ?_
    rw [Db.used] at output
    exact ⟨by simpa only [ExponentOutputs, good, ↓reduceIte] using output, Fb.trans Ft, Kb.trans Kt⟩

end VG.Proof.RsaKeyGen.X86.Candidate
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

def SieveOutputs (E : Environment) (e : Nat) (entropy : List Byte) (s : State) : Prop :=
  if Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E entropy) then
    Outputs E 3 E.length (List.replicate E.length 0) s
  else ExponentOutputs E e entropy s

end VG.Proof.RsaKeyGen.X86.Candidate

end

end

/-! # A supported candidate width draws the candidate and filters it by distance and trial division -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

def FilteredOutputs (E : Environment) (e : Nat) (p : Option Nat) (entropy : List Byte) (s : State) : Prop :=
  if Spec.RsaKeyGen.tooClose (8 * E.length) p (candidateValue E entropy) then
    Outputs E 2 E.length (List.replicate E.length 0) s
  else SieveOutputs E e entropy s

/-- After the code for the width: the status 2 or 3 written, or `eax = 4`
and the drawn candidate to go on. -/
def FrontOutputs (E : Environment) (eBytes pBytes entropy : List Byte) (s : State) : Prop :=
  if Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E entropy) then
    Outputs E 2 E.length (List.replicate E.length 0) s
  else if Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E entropy) then
    Outputs E 3 E.length (List.replicate E.length 0) s
  else Drawn E eBytes pBytes entropy s ∧ s.gpr .eax = 4

end VG.Proof.RsaKeyGen.X86.Candidate

end

end

/-! # The candidate drawn, compared with `p` and sieved at the run-time width -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Bignum.X86.PublicContext

theorem Input.space {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (I : Input E eBytes pBytes entropy s) : FrontRt.Space E.base E.size E.width s := by
  have five := v.slotFit (j := 5) (by decide)
  refine ⟨I.scratch, v.width_bounds.1, v.width_bounds.2, by omega_using [five], ?_⟩
  rw [I.header 1 (by decide), v.length_eq]
  rfl

theorem Environment.Valid.stackApart {E : Environment} (v : E.Valid) :
    E.p.toNat ≤ E.base.toNat ∨ E.base.toNat + E.size + 40 ≤ E.p.toNat := by
  rcases v.workspaceStack with h | h <;> omega_using [h]

theorem Input.loadIn {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (I : Input E eBytes pBytes entropy s) (enough : E.length ≤ E.randLength) :
    FrontRt.LoadIn E.base E.size E.width E.p E.rand s := by
  have length := v.length_eq
  refine ⟨⟨I.space v, I.stack⟩, I.rand_eq, by have := v.randFit; omega_using [enough, length, this], ?_, ?_⟩
  · obtain ⟨r, mem, contains⟩ := I.memory.randRead
    refine ⟨r, mem, ?_⟩
    change (E.rand.setWidth 64 - r.base).toNat + 8 * E.width ≤ r.len
    change (E.rand.setWidth 64 - r.base).toNat + E.randLength ≤ r.len at contains
    omega_using [enough, length, contains]
  · exact (v.readWorkspace (r := E.randRegion) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))).sub_left
      (Region.sub_prefix (by omega_using [enough, length]))

theorem load_rt_ok {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (I : Input E eBytes pBytes entropy s)
    (zeros : Spec.Rsa.bytesAt s.mem (E.out.setWidth 64) E.length = List.replicate E.length 0)
    (enough : E.length ≤ E.randLength) :
    WP isa VG.Impl.RsaKeyGen.X86.FrontRt.load s fun t =>
      Drawn E eBytes pBytes entropy t ∧ WorkFrame E s.mem t.mem ∧ Keeps [.eax, .ebx, .esi, .ecx, .edx] s t := by
  have space : 256 ≤ E.size := v.geometry.headerFit
  have outFit := v.slotFit (j := 0) (by decide)
  have length := v.length_eq
  have L := I.loadIn v enough
  have firstBytes : Spec.Rsa.bytesAt s.mem (E.rand.setWidth 64) E.length = entropy.take E.length := by
    have first := VG.Proof.RsaKeyGen.seg_bytesAt s.mem (E.rand.setWidth 64) (a := 0) (n := E.length) (k := E.randLength) (by omega_using [enough])
    rw [I.memory.entropy] at first
    simpa only [VG.Proof.RsaKeyGen.seg, List.drop_zero, show BitVec.ofNat 64 0 = 0#64 from rfl,
      BitVec.add_zero] using first.symm
  refine WP.mono_syms (FrontRt.load_ok L.base.1 L.sourceFit L.source L.readable L.separate)
    fun t ⟨value, count, F, K⟩ syms => ?_
  have O : Outs E.base [(slot E.width 0, 8 * E.width), (152, 8)] s.mem t.mem :=
    VG.Proof.RsaKeyGen.frame_outs F (by
      intro r mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl <;> change _ ≤ 2 ^ 64 <;> have := I.scratch.nowrap <;> omega)
  have W : WorkspaceFrame E.geometry [(slot E.width 0, 8 * E.width), (152, 8)] s.mem t.mem :=
    WorkspaceFrame.of_outs I.scratch.nowrap O
  have frame : WorkFrame E s.mem t.mem := F.sub (by
    intro r mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact ⟨E.workspaceRegion, List.mem_cons_self, Offset.sub_base E.base outFit⟩
    · exact ⟨E.workspaceRegion, List.mem_cons_self, Offset.sub_base E.base (by change 152 + 8 ≤ E.size; omega_using [space])⟩)
  have J := I.keepWorkspace v K (by decide) (by decide) frame W (by
    intro r mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact Nat.le_trans (by decide) (E.slotHeader 0)
    · decide) (by rw [syms])
  refine ⟨⟨J, ?_, ?_, (frame.output v).trans zeros⟩, frame, K⟩
  · rw [show 64 * E.width = 8 * E.length by omega_using [length], length, firstBytes] at value
    exact value
  · rw [length] at count
    exact count_low v count

theorem Drawn.closeIn {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (D : Drawn E eBytes pBytes entropy s) :
    FrontRt.CloseIn E.base E.size E.width E.p E.other (BitVec.ofNat 32 E.otherLength) s := by
  have length := v.length_eq
  refine ⟨⟨D.input.space v, D.input.stack⟩, D.input.other_eq, D.input.header 6 (by decide), ?_⟩
  intro nonzero
  have positive : E.otherLength ≠ 0 := by intro zero; apply nonzero; rw [zero]
  have eqLength := v.otherLength.resolve_left positive
  refine ⟨by have := v.otherFit; omega_using [length, eqLength, this], ?_, ?_⟩
  · have read := D.input.memory.otherRead
    rw [eqLength, ← length] at read
    exact read
  · have far := v.readWorkspace (r := E.otherRegion) (List.mem_cons_of_mem _ List.mem_cons_self)
    change (⟨E.other.setWidth 64, E.otherLength⟩ : Region).Disjoint E.workspaceRegion at far
    rw [eqLength, ← length] at far
    exact far

theorem close_rt_ok {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (D : Drawn E eBytes pBytes entropy s) :
    WP isa VG.Impl.RsaKeyGen.X86.FrontRt.close s fun t =>
      Drawn E eBytes pBytes entropy t ∧
      t.gpr .eax = Near.bit (Spec.RsaKeyGen.tooClose (8 * E.length)
        (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E entropy)) ∧
      WorkFrame E s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have space : 256 ≤ E.size := v.geometry.headerFit
  have length := v.length_eq
  have fit : 40 ≤ (s.gpr .esp).toNat := by rw [D.input.stack]; have := v.low; omega_using [this]
  have C := D.closeIn v
  refine WP.mono_syms (FrontRt.close_ok C.base.1 fit (by rw [D.input.stack]; exact v.stackApart)
    C.pointer C.length C.source) fun t ⟨result, F, W, K⟩ syms => ?_
  · change t.gpr .eax = Near.bit (Spec.RsaKeyGen.tooClose (64 * E.width)
      (if BitVec.ofNat 32 E.otherLength = 0#32 then none else
        some (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (E.other.setWidth 64) (8 * E.width))))
      (val32 s.mem E.base (slot E.width 0) (2 * E.width))) at result
    rw [D.input.memory.other_choice v, show 64 * E.width = 8 * E.length by omega_using [length], D.candidate] at result
    rw [D.input.stack] at F
    have frame : WorkFrame E s.mem t.mem := VG.X86.Frame.below_mono (wr := [E.workspaceRegion]) (a := 20) F (by decide) v.low
    have headerFar : ∀ r ∈ [(slot E.width 4, 8 * E.width), (slot E.width 2, 8 * E.width), (slot E.width 3, 8 * E.width)], 256 ≤ r.1 := by
      intro r mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl
      · exact E.slotHeader 4
      · exact E.slotHeader 2
      · exact E.slotHeader 3
    have I := D.input.keepWorkspace v K (by decide) (by decide) frame W
      (fun r mem => Nat.le_trans (by decide) (headerFar r mem)) (by rw [syms])
    refine ⟨⟨I, ?_, ?_, (frame.output v).trans D.zeros⟩, result, frame, K⟩
    · have same := W.val32 (d := slot E.width 0) (n := 2 * E.width) (by change slot E.width 0 + 4 * (2 * E.width) ≤ E.size; have := v.slotFit (j := 0) (by decide); omega_using [this]) (by
        intro r mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with rfl | rfl | rfl
        · exact Or.inl (by have := E.slotBefore (i := 0) (j := 4) (by decide); omega_using [this])
        · exact Or.inl (by have := E.slotBefore (i := 0) (j := 2) (by decide); omega_using [this])
        · exact Or.inl (by have := E.slotBefore (i := 0) (j := 3) (by decide); omega_using [this]))
      exact same.trans D.candidate
    · have same := W.read32 (d := 152) (by change 152 + 4 ≤ E.size; omega_using [space])
        (fun r mem => Or.inl (by have := headerFar r mem; omega_using [this]))
      exact (congrArg BitVec.toNat same).trans D.used

theorem Drawn.sieveIn {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (D : Drawn E eBytes pBytes entropy s) :
    FrontRt.SieveIn E.sieveGeometry (candidateValue E entropy) (allocFrame 20 s) := by
  have space : 256 ≤ E.size := v.geometry.headerFit
  have stackFit : 40 ≤ (s.gpr .esp).toNat := by rw [D.input.stack]; have := v.low; omega_using [this]
  have Sa : Scr (allocFrame 20 s) E.base E.size :=
    FilterStack.allocated_scratch D.input.scratch stackFit (by rw [D.input.stack]; exact v.stackApart)
  refine ⟨sieve_context v D, ?_, D.input.memory.symbol, ?_⟩
  · rw [allocFrame_gpr _ _ (by decide)]
    change s.gpr .edi + 256#32 = E.workspace + 256#32
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [D.input.scratch.edi_toNat]
    change (E.workspace.setWidth 64).toNat = E.workspace.toNat
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans E.workspace.isLt (by decide))]
  rw [readSrc_sc Sa (d := 4) (by omega_using [space]), allocFrame_mem, (D.input.space v).len]
  rfl

theorem sieve_rt_ok {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (D : Drawn E eBytes pBytes entropy s) :
    WP isa VG.Impl.RsaKeyGen.X86.FrontRt.sieve s fun t =>
      Drawn E eBytes pBytes entropy t ∧
      t.gpr .eax = BitVec.ofNat 32 (Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E entropy)).toNat ∧
      WorkFrame E s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have space : 256 ≤ E.size := v.geometry.headerFit
  have privateSub : (below E.sieveGeometry.sp 4).Sub (below E.p 136) := below_inner (by decide) v.low
  have workspaceFar : E.workspaceRegion.Disjoint (below E.p 136) :=
    v.stackFar E.workspaceRegion (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have tableFar : E.tableRegion.Disjoint (below E.p 136) :=
    v.stackFar E.tableRegion (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
  have pointer : s.gpr .edi = E.workspace := by
    apply BitVec.eq_of_toNat_eq
    have H := D.input.scratch.edi_toNat
    change (s.gpr .edi).toNat = (E.workspace.setWidth 64).toNat at H
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans E.workspace.isLt (by decide))] at H
    exact H
  have stackFit : 40 ≤ (s.gpr .esp).toNat := by rw [D.input.stack]; have := v.low; omega_using [this]
  have Sa : Scr (allocFrame 20 s) E.base E.size :=
    FilterStack.allocated_scratch D.input.scratch stackFit (by rw [D.input.stack]; exact v.stackApart)
  have lenRead : readSrc (allocFrame 20 s) (.mem (VG.Impl.Mont.X86.sc 4)) =
      some (BitVec.ofNat 32 (8 * E.sieveGeometry.w)) := by
    rw [readSrc_sc Sa (d := 4) (by omega_using [space]), allocFrame_mem, (D.input.space v).len]
    rfl
  refine WP.mono_syms (FrontRt.sieve_ok v.sieve_valid (sieve_context v D)
    (by omega_using [stackFit]) lenRead (by change s.gpr .edi + 256#32 = E.workspace + 256#32; rw [pointer])
    rfl D.input.memory.symbol (by change 4 ≤ (E.p - 20#32).toNat; rw [sub_toNat (by have := v.low; omega_using [this])]; have := v.low; omega_using [this])
    ((workspaceFar.sub_left v.sieveCandidateSub).sub_right privateSub) (tableFar.sub_right privateSub)
    (candidate_large v entropy)) fun t ⟨result, F, K⟩ syms => ?_
  change t.gpr .eax = BitVec.ofNat 32 (Spec.RsaKeyGen.obviouslyComposite (64 * E.width) (candidateValue E entropy)).toNat at result
  rw [show 64 * E.width = 8 * E.length by have := v.length_eq; omega_using [this]] at result
  have stackFrame : Frame [below E.p 136] s.mem t.mem := F.sub (by
    intro r mem
    simp only [Sieve.setupWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact ⟨_, List.mem_singleton_self _, v.sieveStackSub⟩
    · exact ⟨_, List.mem_singleton_self _, privateSub⟩)
  have frame : WorkFrame E s.mem t.mem := stackFrame.mono (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact List.mem_cons_of_mem _ List.mem_cons_self)
  have W : WorkspaceFrame E.geometry [] s.mem t.mem := workspace_of_frame stackFrame D.input.scratch.nowrap
    (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact workspaceFar)
  have I := D.input.keepWorkspace v K (by decide) (by decide) frame W (by intro r mem; cases mem) (by rw [syms])
  have value := W.val32 (d := slot E.width 0) (n := 2 * E.width)
    (by have := v.slotFit (j := 0) (by decide); change slot E.width 0 + 4 * (2 * E.width) ≤ E.size; omega_using [this])
    (by intro r mem; cases mem)
  have used := W.read32 (d := 152) (by change 152 + 4 ≤ E.size; omega_using [space]) (by intro r mem; cases mem)
  exact ⟨⟨I, value.trans D.candidate, (congrArg BitVec.toNat used).trans D.used, (frame.output v).trans D.zeros⟩,
    result, frame, K⟩

theorem front_rt_ok {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (I : Input E eBytes pBytes entropy s)
    (zeros : Spec.Rsa.bytesAt s.mem (E.out.setWidth 64) E.length = List.replicate E.length 0)
    (enough : E.length ≤ E.randLength) :
    WP isa VG.Impl.RsaKeyGen.X86.FrontRt.code s fun t =>
      FrontOutputs E eBytes pBytes entropy t ∧ MutableFrame E s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  unfold VG.Impl.RsaKeyGen.X86.FrontRt.code
  refine WP.seq (WP.mono (load_rt_ok v I zeros enough) fun a ⟨D, F₀, K₀⟩ => ?_)
  have F₀' : MutableFrame E s.mem a.mem := F₀.mutable
  have K₀' : Keeps WitnessStep.clob s a := K₀.mono (by unfold WitnessStep.clob; decide)
  refine WP.seq (WP.mono (close_rt_ok v D) fun a' ⟨Da, flag, F, K⟩ => ?_)
  refine WP.seq (WP.mono (cmp_bool flag) fun b ⟨B, _, cond⟩ => ?_)
  have Db := Da.keepMem v B.mem (B.keeps []) (by decide) (by decide) B.syms
  have Fb : MutableFrame E s.mem b.mem := by rw [B.mem]; exact F₀'.trans F.mutable
  have Kb : Keeps WitnessStep.clob s b :=
    (K₀'.trans (K.mono (by unfold WitnessStep.clob; decide))).widen (B.keeps [])
  cases close : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E entropy)
  · refine WP.ite false (by rw [cond, close]) (fun bad => nomatch bad) (fun _ => ?_)
    refine WP.seq (WP.mono (sieve_rt_ok v Db) fun c ⟨Dc, flag', F', K'⟩ => ?_)
    refine WP.seq (WP.mono (cmp_bool flag') fun d ⟨Bd, _, cond'⟩ => ?_)
    have Dd := Dc.keepMem v Bd.mem (Bd.keeps []) (by decide) (by decide) Bd.syms
    have Fd : MutableFrame E s.mem d.mem := by rw [Bd.mem]; exact Fb.trans F'.mutable
    have Kd : Keeps WitnessStep.clob s d := (Kb.trans (K'.mono (by unfold WitnessStep.clob; decide))).widen (Bd.keeps [])
    cases composite : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E entropy)
    · refine WP.ite false (by rw [cond', composite]) (fun bad => nomatch bad) (fun _ => ?_)
      refine wp_movS rfl fun t T _ => WP.block_nil ?_
      refine ⟨?_, by rw [T.mem]; exact Fd, Kd.widen T.keeps⟩
      simp only [FrontOutputs, close, composite, Bool.false_eq_true, ↓reduceIte]
      exact ⟨Dd.keepMem v T.mem T.keeps (by decide) (by decide) T.syms, T.gpr⟩
    · refine WP.ite true (by rw [cond', composite]) (fun _ => ?_) (fun bad => nomatch bad)
      refine WP.mono (finish_used_ok (status := 3) v (Dd.finishReady v)) fun t ⟨output, Ft, Kt⟩ => ?_
      rw [Dd.used] at output
      exact ⟨by simpa only [FrontOutputs, close, composite, Bool.false_eq_true, ↓reduceIte] using output,
        Fd.trans Ft, Kd.trans Kt⟩
  · refine WP.ite true (by rw [cond, close]) (fun _ => ?_) (fun bad => nomatch bad)
    refine WP.mono (finish_used_ok (status := 2) v (Db.finishReady v)) fun t ⟨output, Ft, Kt⟩ => ?_
    rw [Db.used] at output
    exact ⟨by simpa only [FrontOutputs, close, ↓reduceIte] using output, Fb.trans Ft, Kb.trans Kt⟩

end VG.Proof.RsaKeyGen.X86.Candidate
