module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateLoadInput
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveContext
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateShape
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateArrays
import VerifiedGarbage.Proof.RsaKeyGen.X86.FilterStack
import VerifiedGarbage.Proof.RsaKeyGen.X86.WorkspaceDisjoint
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.TCB.X86.State
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateEnvironment
public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateSieve
import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveLoop
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveAdvancedMem
import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveFrame
public import VerifiedGarbage.Proof.Framework.X86.Call

/-! ### `RsaKeyGen.X86.SieveSetup`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.SieveCandidateSlots`, which this module and modules that import it used -/

section

/-! # Install the candidate's fixed public pointer and end in the sieve frame -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.Sieve

structure CandidateReady (g : Geometry) (c : Nat) (s : State) : Prop where
  context : Context g c s
  candidate : s.mem.readW (off (g.sp.setWidth 64) 0) 32 = g.candidate
  ending : s.mem.readW (off (g.sp.setWidth 64) 4) 32 = g.ending

theorem candidateSlots_ok {g : Geometry} (v : g.Valid) {c : Nat} {s : State} (C : Context g c s)
    (pointer : s.gpr .edi = g.candidate) :
    WP isa (.block (candidateSlots stackSlots g.w)) s fun t =>
      CandidateReady g c t ∧ Outside (g.sp.setWidth 64) 0 20 s.mem t.mem ∧ Keeps [.eax] s t := by
  change WP isa (.block ([.store (slot 0) .edi] ++ [.mov .eax (.reg .edi),
    .alu .add .eax (.imm (BitVec.ofNat 32 (8 * g.w))), .store (slot 4) .eax])) s _
  refine WP.block_append (WP.mono (C.stack.store 0 (by decide) .edi) fun a ⟨Ma, Oa, Ka, Ca⟩ => ?_)
  refine wp_movS rfl fun b B _ => wp_addS rfl fun d D _ => ?_
  have K : Keeps [.eax] s d := ((Ka.mono (by decide)).widen B.keeps).trans D.keeps
  have Md : d.mem = a.mem := D.mem.trans B.mem
  have value : d.gpr .eax = g.ending := by
    rw [D.gpr, B.gpr, Ka.1 .edi (by decide), pointer]
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

end VG.Proof.RsaKeyGen.X86.Sieve

end

end

/-! ### `RsaKeyGen.X86.SieveTableSlots`, which only this module used -/

section

/-! # Initialize the static cursor, public table length and hit word -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.Sieve

theorem tableSlots_ok {g : Geometry} (v : g.Valid) {c : Nat} {s : State} (C : CandidateReady g c s)
    (length : g.limit = tableCount g.w) (pointer : s.gpr .eax = g.table) :
    WP isa (.block (tableSlots stackSlots g.w)) s fun t =>
      StateAt g c 0 g.limit t ∧ Outside (g.sp.setWidth 64) 0 20 s.mem t.mem ∧ Keeps [.eax] s t := by
  change WP isa (.block ([.store (slot 8) .eax] ++ ([.mov .eax (.imm (BitVec.ofNat 32 (tableCount g.w))),
    .store (slot 12) .eax] ++ [.mov .eax (.imm 0), .store (slot 16) .eax]))) s _
  refine WP.block_append (WP.mono (C.context.stack.store 8 (by decide) .eax) fun a ⟨Ma, Oa, Ka, Ca⟩ => ?_)
  refine WP.block_append (WP.mono (Ca.literal 12 (by decide) (BitVec.ofNat 32 (tableCount g.w)))
    fun b ⟨Mb, Ob, Kb, Cb⟩ => ?_)
  refine WP.mono (Cb.literal 16 (by decide) 0#32) fun t ⟨Mt, Ot, Kt, _⟩ => ?_
  have mem : t.mem = ((s.mem.writeW (off (g.sp.setWidth 64) 8) g.table).writeW
      (off (g.sp.setWidth 64) 12) (BitVec.ofNat 32 g.limit)).writeW (off (g.sp.setWidth 64) 16) 0#32 := by
    rw [Mt, Mb, Ma, pointer, ← length]
  have outside : Outside (g.sp.setWidth 64) 0 20 s.mem t.mem :=
    ((Oa.mono (by decide) (by decide)).trans (Ob.mono (by decide) (by decide))).trans (Ot.mono (by decide) (by decide))
  have keep : Keeps [.eax] s t := ((Ka.mono (by decide)).trans Kb).trans Kt
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

end VG.Proof.RsaKeyGen.X86.Sieve

end

end


/-! # The static-address prefix establishes all sieve-loop preconditions -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.X86.Sieve

def setupWrites (g : Geometry) : List Region := [g.stackRegion, below g.sp 4]

theorem setupFrame_stack {g : Geometry} {m m' : Mem} (F : Frame [g.stackRegion] m m') :
    Frame (setupWrites g) m m' := by
  apply F.sub
  intro r mem
  obtain rfl := List.mem_singleton.mp mem
  exact ⟨_, List.mem_cons_self .., fun _ h => h⟩

theorem setupFrame_symbol {g : Geometry} {m m' : Mem} (F : Frame [below g.sp 4] m m') :
    Frame (setupWrites g) m m' := by
  apply F.sub
  intro r mem
  obtain rfl := List.mem_singleton.mp mem
  exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩

theorem setup_ok {g : Geometry} (v : g.Valid) {c : Nat} {s : State} (C : Context g c s)
    (pointer : s.gpr .edi = g.candidate) (length : g.limit = tableCount g.w)
    (symbol : s.syms TrialTable32.symbol = g.table) (low : 4 ≤ g.sp.toNat)
    (candidateFar : g.candidateRegion.Disjoint (below g.sp 4))
    (tableFar : g.tableRegion.Disjoint (below g.sp 4)) :
    WP isa (.seq (.block (candidateSlots stackSlots g.w)) (.seq tableAddress (.block (tableSlots stackSlots g.w)))) s
      fun t => StateAt g c 0 g.limit t ∧ Frame (setupWrites g) s.mem t.mem ∧ Keeps [.eax, .ecx] s t := by
  refine WP.seq (WP.mono_syms (candidateSlots_ok v C pointer) fun a ⟨A, Oa, Ka⟩ Sa => ?_)
  refine WP.seq (WP.mono (symFrame_ok TrialTable32.symbol a (by rw [A.context.stack.sp]; exact low)) fun b R => ?_)
  have B : CandidateReady g c b :=
    ⟨A.context.keepSymbol v R candidateFar tableFar,
      (symbol_stack_word A.context R low (by decide : 0 + 4 ≤ 20)).trans A.candidate,
      (symbol_stack_word A.context R low (by decide : 4 + 4 ≤ 20)).trans A.ending⟩
  have address : b.gpr .eax = g.table := by rw [R.addr, Sa]; exact symbol
  have symbolFrame : Frame [below g.sp 4] a.mem b.mem := by rw [← A.context.stack.sp]; exact R.frame
  have Kb : Keeps [.eax, .ecx] a b := ⟨R.gpr, R.rd, R.wr⟩
  refine WP.mono (tableSlots_ok v B length address) fun t ⟨T, Ot, Kt⟩ => ?_
  exact ⟨T, ((setupFrame_stack (outsideStack_frame Oa)).trans (setupFrame_symbol symbolFrame)).trans
    (setupFrame_stack (outsideStack_frame Ot)), ((Ka.mono (by decide)).trans Kb).widen Kt⟩

end VG.Proof.RsaKeyGen.X86.Sieve

end

end

/-! ### `RsaKeyGen.X86.CandidateSieve`, which this module and modules that import it used -/

section

/-! # Native sieve setup and cleanup preserve the workspace pointer and candidate -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/SieveBody.lean`, which only this module imported.
section

/-! # The complete prepared sieve computes the specified compositeness filter -/

section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.X86.Sieve

theorem body_full_ok {g : Geometry} (v : g.Valid) {c : Nat} {s : State} (C : Context g c s)
    (pointer : s.gpr .edi = g.candidate) (length : g.limit = tableCount g.w)
    (symbol : s.syms TrialTable32.symbol = g.table) (low : 4 ≤ g.sp.toNat)
    (candidateFar : g.candidateRegion.Disjoint (below g.sp 4))
    (tableFar : g.tableRegion.Disjoint (below g.sp 4)) (large : 8161 < c) :
    WP isa (body stackSlots g.w) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (Spec.RsaKeyGen.obviouslyComposite (64 * g.w) c).toNat ∧
      Frame (setupWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s t ∧
      t.mem.readW (off (g.sp.setWidth 64) 0) 32 = g.candidate := by
  have run := WP.seq (WP.mono (setup_ok v C pointer length symbol low candidateFar tableFar)
    fun u ⟨U, F, K₀⟩ => WP.mono (loop_full_ok v U) fun t ⟨value, O, K, candidate⟩ =>
      (show t.gpr .eax = BitVec.ofNat 32 (Spec.RsaKeyGen.obviouslyComposite (64 * g.w) c).toNat ∧
        Frame (setupWrites g) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s t ∧
          t.mem.readW (off (g.sp.setWidth 64) 0) 32 = g.candidate from by
        refine ⟨?_, F.trans (setupFrame_stack (outsideStack_frame O)), (K₀.mono (by decide)).trans K, candidate⟩
        rw [length, tableCount, VG.Proof.RsaKeyGen.trialPrefix_spec large] at value
        exact value))

  exact WP.seq (WP.mono (WP.seq_iff.mp (WP.assoc run)) fun a H => WP.assoc H)

end VG.Proof.RsaKeyGen.X86.Sieve
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateSieve
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.X86.CandidateSieve

theorem body_ok {g : Sieve.Geometry} (v : g.Valid) {c : Nat} {s : State} (C : Sieve.Context g c s)
    (pointer : s.gpr .edi + 256#32 = g.candidate) (length : g.limit = VG.Impl.RsaKeyGen.X86.Sieve.tableCount g.w)
    (symbol : s.syms TrialTable32.symbol = g.table) (low : 4 ≤ g.sp.toNat)
    (candidateFar : g.candidateRegion.Disjoint (below g.sp 4))
    (tableFar : g.tableRegion.Disjoint (below g.sp 4)) (large : 8161 < c) :
    WP isa (body g.w) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (Spec.RsaKeyGen.obviouslyComposite (64 * g.w) c).toNat ∧
      Frame (Sieve.setupWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold body setup
  refine WP.seq (wp_addS rfl fun a A _ => WP.block_nil ?_)
  have Ca : Sieve.Context g c a := by
    refine ⟨C.stack.keep A.keeps (by decide), ?_, ?_, ?_, ?_⟩
    · intro i index; rw [A.keeps.2.1, A.keeps.2.2]; exact C.candidateRead i index
    · intro i index d mem; rw [A.keeps.2.1, A.keeps.2.2]; exact C.tableRead i index d mem
    · intro i index; rw [A.mem]; exact C.tableWords i index
    · rw [A.mem]; exact C.candidateValue
  refine WP.seq (WP.mono (Sieve.body_full_ok v Ca (A.gpr.trans pointer) length
    (by rw [A.syms]; exact symbol) low candidateFar tableFar large) fun b ⟨result, F, Kb, saved⟩ => ?_)
  have Cb := Ca.stack.keep Kb (by decide)
  unfold restore
  refine wp_movS (v := g.candidate) (by
    change readSrc b (.mem (VG.Impl.RsaKeyGen.X86.Sieve.slot 0)) = some g.candidate
    rw [Cb.read 0 (by decide), saved]) fun d D _ => wp_subS rfl fun t T _ => WP.block_nil ?_
  have all : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s t :=
    (((A.keeps.mono (by decide)).trans Kb).widen D.keeps).widen T.keeps
  have edi : t.gpr .edi = s.gpr .edi := by
    rw [T.gpr, D.gpr, ← pointer]
    change s.gpr .edi + 256#32 - 256#32 = s.gpr .edi
    exact BitVec.add_sub_cancel _ _
  have K : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
    refine ⟨?_, all.2⟩
    intro r mem
    by_cases same : r = .edi
    · subst r; exact edi
    · exact all.1 r (by cases r <;> simp_all)
  refine ⟨?_, ?_, K⟩
  · rw [T.other .eax (by decide), D.other .eax (by decide)]; exact result
  · rw [A.mem] at F
    rw [T.mem, D.mem]
    exact F

theorem code_ok {g : Sieve.Geometry} (v : g.Valid) {c : Nat} {s : State}
    (C : Sieve.Context g c (allocFrame 20 s)) (fit : 20 ≤ (s.gpr .esp).toNat)
    (pointer : s.gpr .edi + 256#32 = g.candidate) (length : g.limit = VG.Impl.RsaKeyGen.X86.Sieve.tableCount g.w)
    (symbol : s.syms TrialTable32.symbol = g.table) (low : 4 ≤ g.sp.toNat)
    (candidateFar : g.candidateRegion.Disjoint (below g.sp 4))
    (tableFar : g.tableRegion.Disjoint (below g.sp 4)) (large : 8161 < c) :
    WP isa (code g.w) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (Spec.RsaKeyGen.obviouslyComposite (64 * g.w) c).toNat ∧
      Frame (Sieve.setupWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold code
  refine WP.frameAlloc (by decide) (by decide) (by decide) fit (NoSp.of_all (by rfl)) ?_
  refine WP.mono (body_ok v C (by rw [allocFrame_gpr _ _ (by decide)]; exact pointer)
    length symbol low candidateFar tableFar large) fun t ⟨result, F, K⟩ => ?_
  exact ⟨by rw [freed_gpr _ _ (by decide)]; exact result, F, FilterStack.freed_keeps K (by decide)⟩

end VG.Proof.RsaKeyGen.X86.CandidateSieve

end

end

/-! ### `RsaKeyGen.X86.CandidateSieveGeometry`, which this module and modules that import it used -/

section

/-! # The sieve's private stack and candidate array fit the outer candidate frame -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

def Environment.sieveGeometry (E : Environment) : Sieve.Geometry :=
  ⟨E.p - 20#32, E.workspace + 256#32, E.table, E.width, VG.Impl.RsaKeyGen.X86.Sieve.tableCount E.width⟩

theorem Environment.Valid.candidateAddress {E : Environment} (v : E.Valid) :
    (E.workspace + 256#32).setWidth 64 = off E.base 256 := by
  have space := v.slotFit (j := 0) (by decide)
  change 256 + 0 * (8 * (E.width + 2)) + 8 * E.width ≤ E.size at space
  have width := v.width_bounds.1
  have fit := v.workspaceFit
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat, off, Environment.base]
  change ((E.workspace.toNat + 256) % 2 ^ 32) % 2 ^ 64 =
    (E.workspace.toNat % 2 ^ 64 + 256) % 2 ^ 64
  have := E.workspace.isLt
  omega_using [space, width, fit]

theorem Environment.Valid.sieveCandidateSub {E : Environment} (v : E.Valid) :
    E.sieveGeometry.candidateRegion.Sub E.workspaceRegion := by
  change (⟨(E.workspace + 256#32).setWidth 64, 8 * E.width⟩ : Region).Sub E.workspaceRegion
  rw [v.candidateAddress]
  exact Offset.sub_base E.base (by
    have fit := v.slotFit (j := 0) (by decide)
    change 256 + 0 * (8 * (E.width + 2)) + 8 * E.width ≤ E.size at fit
    omega_using [fit])

theorem Environment.Valid.sieveStackSub {E : Environment} (v : E.Valid) :
    E.sieveGeometry.stackRegion.Sub (below E.p 136) :=
  below_sub (by decide) v.low

theorem Environment.Valid.sieve_valid {E : Environment} (v : E.Valid) : E.sieveGeometry.Valid := by
  have width := v.width_bounds
  have candidateFit := v.slotFit (j := 0) (by decide)
  have candidateNat : (E.workspace + 256#32).toNat = E.workspace.toNat + 256 := by
    change 256 + 0 * (8 * (E.width + 2)) + 8 * E.width ≤ E.size at candidateFit
    rw [BitVec.toNat_add]
    change (E.workspace.toNat + 256) % 2 ^ 32 = E.workspace.toNat + 256
    have fit := v.workspaceFit
    have := E.workspace.isLt
    omega_using [width, candidateFit, fit]
  refine ⟨by change 0 < E.width; omega_using [width], by change E.width ≤ 128; omega_using [width], ?_, ?_, ?_, v.tableFit, ?_, ?_⟩
  · change 0 < VG.Impl.RsaKeyGen.X86.Sieve.tableCount E.width
    unfold VG.Impl.RsaKeyGen.X86.Sieve.tableCount
    split <;> decide
  · change VG.Impl.RsaKeyGen.X86.Sieve.tableCount E.width ≤ 1024
    unfold VG.Impl.RsaKeyGen.X86.Sieve.tableCount
    split <;> decide
  · change (E.workspace + 256#32).toNat + 8 * E.width ≤ 2 ^ 32
    rw [candidateNat]
    have fit := v.workspaceFit
    change 256 + 0 * (8 * (E.width + 2)) + 8 * E.width ≤ E.size at candidateFit
    omega_using [fit, candidateFit]
  · exact ((v.stackFar E.workspaceRegion (List.mem_append_left _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))).sub_left v.sieveCandidateSub).sub_right v.sieveStackSub
  · exact (v.stackFar E.tableRegion (List.mem_append_right _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))).sub_right v.sieveStackSub

end VG.Proof.RsaKeyGen.X86.Candidate

end

end

/-! # Native trial division preserves the entire candidate workspace -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Bignum.X86.PublicContext

theorem read_offset {rs : List Region} {base : Addr} {L d n : Nat}
    (R : InRegions rs base L) (bound : d + n ≤ L) (fit : d < 2 ^ 64) :
    InRegions rs (off base d) n := by
  obtain ⟨r, mem, contains⟩ := R
  refine ⟨r, mem, ?_⟩
  have distance : (off base d - r.base).toNat ≤ d + (base - r.base).toNat := by
    rw [← Offset.sub_add_sub_cancel (off base d) base r.base, BitVec.toNat_add]
    have first : (off base d - base).toNat = d := Mem.sub_ofNat_toNat base fit
    rw [first]
    exact Nat.mod_le _ _
  change (base - r.base).toNat + L ≤ r.len at contains
  change (off base d - r.base).toNat + n ≤ r.len
  omega_using [bound, distance, contains]

theorem sieve_context {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (D : Drawn E eBytes pBytes entropy s) :
    Sieve.Context E.sieveGeometry (candidateValue E entropy) (allocFrame 20 s) := by
  have fit : 20 ≤ (s.gpr .esp).toNat := by rw [D.input.stack]; have := v.low; omega_using [this]
  have stack := FilterStack.allocated_context fit
  rw [D.input.stack] at stack
  refine ⟨stack, ?_, ?_, ?_, ?_⟩
  · intro i index
    change i < 2 * E.width at index
    change InRegions ((allocFrame 20 s).rd ++ (allocFrame 20 s).wr)
      (off ((E.workspace + 256#32).setWidth 64) (4 * i)) 4
    rw [v.candidateAddress, off, Offset.add_add]
    have source := D.input.scratch.read (d := 256 + 4 * i) (n := 4) (by
      have := v.slotFit (j := 0) (by decide)
      change 256 + 0 * stride E.width + 8 * E.width ≤ E.size at this
      omega_using [index, this])
    obtain ⟨r, mem, contains⟩ := source
    refine ⟨r, ?_, contains⟩
    simp only [allocFrame_rd, allocFrame_wr, List.mem_append, List.mem_cons]
    exact (List.mem_append.mp mem).elim Or.inl (fun h => Or.inr (Or.inr h))
  · intro i index d mem
    have native := v.sieve_valid
    have dBound : d = 0 ∨ d = 4 := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using mem
    have address : addr (E.sieveGeometry.cursor i) d = off (E.table.setWidth 64) (8 * i + d) := by
      rw [addr_eq (by have := native.cursor_fit index; rcases dBound with rfl | rfl <;> omega_arith), native.cursor_addr index]
      exact Offset.add_add _ _ _
    rw [address]
    obtain ⟨r, member, contains⟩ := read_offset D.input.memory.tableRead (d := 8 * i + d) (n := 4)
      (by rcases dBound with rfl | rfl <;> omega_using [index]) (by rcases dBound with rfl | rfl <;> omega_using [index])
    refine ⟨r, ?_, contains⟩
    simp only [allocFrame_rd, allocFrame_wr, List.mem_append, List.mem_cons]
    exact (List.mem_append.mp member).elim Or.inl (fun h => Or.inr (Or.inr h))
  · intro i index
    exact D.input.memory.table i index
  · change val32 s.mem ((E.workspace + 256#32).setWidth 64) 0 (2 * E.width) = candidateValue E entropy
    rw [v.candidateAddress, ← VG.Proof.Bignum.read_eq_val32, ← D.candidate, ← VG.Proof.Bignum.read_eq_val32]
    congr 2
    change off (off E.base 256) 0 = off E.base (slot E.width 0)
    simp only [off, BitVec.add_zero, slot, VG.Impl.Bignum.hdrBytes, Nat.zero_mul, Nat.add_zero]

end VG.Proof.RsaKeyGen.X86.Candidate
