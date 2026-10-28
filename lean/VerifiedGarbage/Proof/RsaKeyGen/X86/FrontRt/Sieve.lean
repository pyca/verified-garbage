module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveSetup
import VerifiedGarbage.Proof.RsaKeyGen.X86.CmpCarry
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveCandidateSlots
public import VerifiedGarbage.Impl.RsaKeyGen.X86.FrontRt
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveLoop
import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveAdvancedMem
import VerifiedGarbage.Proof.RsaKeyGen.TrialFilter
import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveFrame
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.RsaKeyGen.X86.FilterStack

import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Mont.X86.Instr

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
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold tableCount
  by_cases small : w ≤ 16
  · rw [decide_eq_true (show 8 * w < (129#32 : BitVec 32).toNat by change 8 * w < 129; omega)]
    simp only [small, ↓reduceIte]
    decide
  · rw [decide_eq_false (show ¬ 8 * w < (129#32 : BitVec 32).toNat by change ¬ 8 * w < 129; omega)]
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
    length symbol low candidateFar tableFar large) fun t ⟨result, F, K⟩ => ?_
  exact ⟨by rw [freed_gpr _ _ (by decide)]; exact result, F, FilterStack.freed_keeps K (by decide)⟩

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
