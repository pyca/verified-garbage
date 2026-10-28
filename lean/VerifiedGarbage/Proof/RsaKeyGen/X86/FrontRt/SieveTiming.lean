module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.FrontRt.Sieve
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveLoopTiming
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.RsaKeyGen.X86.FrontRt.LoadTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.TimingSeg
import VerifiedGarbage.Proof.Framework.X86.SymFrame
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Trial division at the run-time width releases only the trial divisors' pattern -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.FrontRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Dsa.X86 VG.Proof.RsaKeyGen.X86.Sieve
open VG.Impl.RsaKeyGen.X86.FrontRt
open VG.Impl.RsaKeyGen.X86.Sieve (tableCount tableAddress stackSlots)

theorem enter_ok {g : Geometry} {c : Nat} {s : State} (S : SieveIn g c s) :
    WP isa (.block [.mov .edx (.mem (VG.Impl.Mont.X86.sc 4)), .alu .add .edi (.imm 256)]) s (BodyIn g c) := by
  obtain ⟨C, pointer, symbol, lenRead⟩ := S
  refine wp_movS lenRead fun a A _ => wp_addS rfl fun b B _ => WP.block_nil ?_
  have Kb : Keeps [.edx, .edi] s b := (A.keeps.mono (by decide)).widen B.keeps
  have Mb : b.mem = s.mem := B.mem.trans A.mem
  refine ⟨⟨C.stack.keep Kb (by decide), ?_, ?_, ?_, ?_⟩, by rw [B.gpr, A.other .edi (by decide)]; exact pointer,
    by rw [B.other .edx (by decide), A.gpr], by rw [B.syms, A.syms]; exact symbol⟩
  · intro i index; rw [Kb.2.1, Kb.2.2]; exact C.candidateRead i index
  · intro i index d mem; rw [Kb.2.1, Kb.2.2]; exact C.tableRead i index d mem
  · intro i index; rw [Mb]; exact C.tableWords i index
  · rw [Mb]; exact C.candidateValue

theorem enter_trace {g : Geometry} {c d : Nat} :
    RelCT isa (fun s t => SieveIn g c s ∧ SieveIn g d t)
      (.block [.mov .edx (.mem (VG.Impl.Mont.X86.sc 4)), .alu .add .edi (.imm 256)])
      (fun u z => BodyIn g c u ∧ BodyIn g d z) := by
  intro s t tr ur u z ⟨S, T⟩ E G
  have A : VG.X86.Taint.Agree (τr [.esp, .edi]) s t := by
    apply agree_regs
    intro r mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact S.1.stack.sp.trans T.1.stack.sp.symm
    · have H := congrArg (fun x : BitVec 32 => x - 256#32) (S.2.1.trans T.2.1.symm)
      simpa only [BitVec.add_sub_cancel] using H
  exact ⟨((rawBlock (rs := [.esp, .edi]) (by decide +kernel)) _ _ _ _ _ _ A E G).1,
    wp_result (enter_ok S) E, wp_result (enter_ok T) G⟩

theorem setup_trace {g : Geometry} (v : g.Valid) {c d : Nat} (low : 4 ≤ g.sp.toNat)
    (length : g.limit = tableCount g.w) (candidateFar : g.candidateRegion.Disjoint (below g.sp 4))
    (tableFar : g.tableRegion.Disjoint (below g.sp 4)) :
    RelCT isa (fun s t => BodyIn g c s ∧ BodyIn g d t)
      (.seq (.block candidateSlots) (.seq tableAddress (.block tableSlots)))
      (fun s t => StateAt g c 0 g.limit s ∧ StateAt g d 0 g.limit t) := by
  have first : RelCT isa (fun s t => BodyIn g c s ∧ BodyIn g d t) (.block candidateSlots)
      (fun s t => s.gpr .esp = g.sp ∧ t.gpr .esp = g.sp) := by
    intro s t tr ur u z ⟨S, T⟩ E G
    have A : VG.X86.Taint.Agree (τr [.esp]) s t :=
      agree_regs (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact S.1.stack.sp.trans T.1.stack.sp.symm)
    have trace := ((rawBlock (rs := [.esp]) (code := candidateSlots) (by decide +kernel)) _ _ _ _ _ _ A E G).1
    have U := wp_result (candidateSlots_ok v S.1 S.2.1 S.2.2.1) E
    have Z := wp_result (candidateSlots_ok v T.1 T.2.1 T.2.2.1) G
    exact ⟨trace, U.1.context.stack.sp, Z.1.context.stack.sp⟩
  have middle : RelCT isa (fun s t => s.gpr .esp = g.sp ∧ t.gpr .esp = g.sp)
      tableAddress (VG.X86.Taint.Agree (τr [.esp])) := by
    intro s t tr ur u z ⟨S, T⟩ E G
    have Ls : 4 ≤ (s.gpr .esp).toNat := by rw [S]; exact low
    have Lt : 4 ≤ (t.gpr .esp).toNat := by rw [T]; exact low
    have U := wp_result (symFrame_ok VG.Impl.RsaKeyGen.TrialTable32.symbol s Ls) E
    have Z := wp_result (symFrame_ok VG.Impl.RsaKeyGen.TrialTable32.symbol t Lt) G
    refine ⟨?_, agree_regs (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact
      (U.gpr .esp (by decide)).trans (S.trans (T.symm.trans (Z.gpr .esp (by decide)).symm)))⟩
    rw [symFrame_trace Ls E, symFrame_trace Lt G, S, T]
  have raw : RelCT isa (fun s t => BodyIn g c s ∧ BodyIn g d t)
      (.seq (.block candidateSlots) (.seq tableAddress (.block tableSlots))) (fun _ _ => True) :=
    RelCT.seq first (RelCT.seq middle (rawBlock (by decide +kernel)))
  intro s t tr ur u z ⟨S, T⟩ E G
  exact ⟨(raw _ _ _ _ _ _ ⟨S, T⟩ E G).1,
    (wp_result (setup_ok v S.1 S.2.1 S.2.2.1 length S.2.2.2 low candidateFar tableFar) E).1,
    (wp_result (setup_ok v T.1 T.2.1 T.2.2.1 length T.2.2.2 low candidateFar tableFar) G).1⟩

theorem body_trace {g : Geometry} (v : g.Valid) {c d : Nat} (pattern : SamePattern g c d)
    (length : g.limit = tableCount g.w) (low : 4 ≤ g.sp.toNat)
    (candidateFar : g.candidateRegion.Disjoint (below g.sp 4))
    (tableFar : g.tableRegion.Disjoint (below g.sp 4)) :
    RelCT isa (fun s t => BodyIn g c s ∧ BodyIn g d t) sieveBody (VG.X86.Taint.Agree (τr [.esp])) := by
  have setup := setup_trace (c := c) (d := d) v low length candidateFar tableFar
  intro s t tr ur u z H E G
  cases E with
  | seq A E =>
    cases E with
    | seq B E =>
      cases E with
      | seq C L =>
        cases G with
        | seq D G =>
          cases G with
          | seq F G =>
            cases G with
            | seq K N =>
              have R := RelCT.seq setup (loop_trace v pattern) _ _ _ _ _ _ H
                (.seq (.seq A (.seq B C)) L) (.seq (.seq D (.seq F K)) N)
              simpa only [List.append_assoc] using R

theorem sieve_trace {g : Geometry} (v : g.Valid) {c d : Nat} (pattern : SamePattern g c d)
    (length : g.limit = tableCount g.w) (low : 4 ≤ g.sp.toNat)
    (candidateFar : g.candidateRegion.Disjoint (below g.sp 4))
    (tableFar : g.tableRegion.Disjoint (below g.sp 4)) :
    RelCT isa (fun s t => SieveIn g c (allocFrame 20 s) ∧ SieveIn g d (allocFrame 20 t)) sieve (fun _ _ => True) := by
  unfold sieve
  apply RelCT.frameAlloc
  refine (RelCT.seq enter_trace (RelCT.seq (body_trace v pattern length low candidateFar tableFar)
    (rawBlock (by decide +kernel)))).mono ?_ (fun _ _ h => h)
  rintro _ _ ⟨s, t, H, rfl, rfl⟩
  exact H

end VG.Proof.RsaKeyGen.X86.FrontRt
