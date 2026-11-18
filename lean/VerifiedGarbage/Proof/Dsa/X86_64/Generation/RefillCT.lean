module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillContract
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillCorrect
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Entry
public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hashes
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeCall
import VerifiedGarbage.Proof.Framework.X86_64.FrameAlloc
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillEntry
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Spec.Dsa.Generate
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import Mathlib.Algebra.Group.Nat.Defs
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeometryTape
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Context
public import VerifiedGarbage.TCB.X86_64.Target
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ParameterCTState
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillABI
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillCTLoop
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillFinish
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Generation.Layout
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.TCB.Registration
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillCTLoop
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillEntry
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillFinish
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
meta import VerifiedGarbage.Proof.Dsa.Generation.Memory
meta import VerifiedGarbage.Proof.Dsa.Generation.Layout
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.Registration
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSlice
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSuccess
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ParameterInvariant
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSlice
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextFrame
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSuccess
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ParameterInvariant
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OnSuccess
import VerifiedGarbage.Proof.RsaOaep.X86_64.Out
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OnSuccess
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillABI
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.Out
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
public import VerifiedGarbage.Proof.RsaOaep.X86_64.CtBase
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Output
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.ToAdditive
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.CtBase
meta import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Output
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Context
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
meta import Mathlib.Tactic.Push
meta import Mathlib.Tactic.Attr.Core
meta import Aesop.BuiltinRules
meta import Mathlib.Tactic.ToAdditive
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.RsaKeyGen.Hdr
meta import VerifiedGarbage.Proof.RsaKeyGen.Slots
meta import VerifiedGarbage.Proof.RsaKeyGen.Table
meta import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
meta import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
meta import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Entry
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `Dsa.X86_64.Generation.EntrySetupCT`, which only this module used -/

section

/-! # Entry setup accesses only fixed offsets of the public stack pointer -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Dsa.X86_64.Generation

def EntryStackAgree (s t : State) : Prop := s.gpr .rsp = t.gpr .rsp

theorem entrySave_ct : RelCT isa EntryStackAgree (.block saveRegisters) (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (Taint.ofRegs [.rsp])
  · intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r; exact h
  · taint_decide

theorem entryRestore_ct : RelCT isa EntryStackAgree (.block restoreRegisters) (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (Taint.ofRegs [.rsp])
  · intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r; exact h
  · taint_decide

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! ### `Dsa.X86_64.Generation.RefillCTOutput`, which only this module used -/

section

/-! ### `Dsa.X86_64.Generation.RefillCTFinish`, which only this module used -/

section

/-! ### `Dsa.X86_64.Generation.OutputCT`, which only this module used -/

section

/-! # Output copying and failure zeroing use public frame inputs -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Proof.MlKem.X86_64

structure OutputPublic where
  context : GenerationContext
  accepted : Bool
  ws : List Region

def OutputBefore (n : Nat) (p : OutputPublic) (s : State) : Prop :=
  (∃ W, GenerationMemory p.context W s ∧ (W 19 == 1) = p.accepted) ∧ FrV n p.context.geo.F p.ws s

def OutputPublic.words (p : OutputPublic) : Nat → BitVec 64 := p.context.saved

theorem output_frame {n : Nat} {p : OutputPublic} {s : State} (h : OutputBefore n p s) :
    FrV n p.context.geo.F p.ws s ∧
    ∀ k ∈ [5, 6, 7], word s.mem p.context.geo.F (8 * k) = p.words k := by
  obtain ⟨⟨W, hm, _⟩, hf⟩ := h
  obtain ⟨V, R⟩ := hm.rep
  refine ⟨hf, fun k hk => ?_⟩
  have bound : k < 37 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; omega_using [hk]
  rw [R.fr k bound]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · simpa [OutputPublic.words, upd] using hm.slots 5 (by simp [generationSlots])
  · simpa [OutputPublic.words, upd] using hm.slots 6 (by simp [generationSlots])
  · simpa [OutputPublic.words, upd] using hm.slots 7 (by simp [generationSlots])

theorem output_pins (n : Nat) : Pins (OutputBefore n) [.rsp] := by
  intro p s t ⟨⟨Ws, hs, _⟩, _⟩ ⟨⟨Wt, ht, _⟩, _⟩ r hr
  obtain rfl := List.mem_singleton.mp hr
  exact hs.layout.rsp.trans ht.layout.rsp.symm

theorem output_check {n : Nat} {p : OutputPublic} {s : State} (h : OutputBefore n p s) :
    WP isa (.block Impl.Dsa.X86_64.Generation.successStatus) s
      (fun t => OutputBefore n p t ∧ isa.eval .e t = some p.accepted) := by
  obtain ⟨⟨W, hm, hs⟩, hf⟩ := h
  obtain ⟨V, R⟩ := hm.rep
  refine WP.mono (successStatus_ok hm.layout R) fun t ⟨hz, he, hk⟩ => ?_
  exact ⟨⟨⟨W, hm.congr he hk, hs⟩, hf.congr (hk.gpr (by decide)) hk.2.2⟩,
    by simp only [eval, hz, hs]⟩

theorem outputCopy_ct (n : Nat) (hn : n = 2 ∨ n = 3 ∨ n = 6) :
    RelCT isa (Two (OutputBefore n)) Impl.Dsa.X86_64.Generation.outputCopy (fun _ _ => True) := by
  refine two_taintF [] [5, 6, 7] (fun p => p.context.geo.F) OutputPublic.ws OutputPublic.words
    (fun _ _ h => output_frame h) (by intro _ _ _ _ _ r hr; simp at hr) (by decide) ?_
  rcases hn with rfl | rfl | rfl
  all_goals exact ⟨_, by taint_decide⟩

theorem outputZero_ct (n : Nat) (hn : n = 2 ∨ n = 3 ∨ n = 6) :
    RelCT isa (Two (OutputBefore n)) Impl.Dsa.X86_64.Generation.outputZero (fun _ _ => True) := by
  refine two_taintF [] [5, 6, 7] (fun p => p.context.geo.F) OutputPublic.ws OutputPublic.words
    (fun _ _ h => output_frame h) (by intro _ _ _ _ _ r hr; simp at hr) (by decide) ?_
  rcases hn with rfl | rfl | rfl
  all_goals exact ⟨_, by taint_decide⟩

theorem finishOutput_ct (n : Nat) (hn : n = 2 ∨ n = 3 ∨ n = 6) :
    RelCT isa (Two (OutputBefore n)) Impl.Dsa.X86_64.Generation.finishOutput (fun _ _ => True) := by
  refine RelCT.seq (two_piece [.rsp] (output_pins n) (by taint_decide)
    (fun _ _ h => output_check h)) ?_
  refine two_ite (fun _ _ _ hs ht => hs.2.trans ht.2.symm) ?_ ?_
  · exact two_map (fun p : OutputPublic => p) (fun _ _ h => h.1.1) (outputCopy_ct n hn)
  · exact two_map (fun p : OutputPublic => p) (fun _ _ h => h.1.1) (outputZero_ct n hn)

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Timing of the refillable-tape search's end

`finish`: the words written to `used` and `state` (`results`), at addresses
the controller's words hold, which are public; the output; the status.
Every branch is on the controller's public status and the octets consumed. -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Mgf1.X86_64 (sp)
open VG.Impl.Bignum.X86_64 (at0)

/-! ## The end's state -/

theorem doneAt_rsp {n pLen qLen : Nat} {D : DonePublic} {t : State} (h : DoneAt n pLen qLen D t) :
    t.gpr .rsp = D.ctx.geo.F := h.2.2.2.1.rsp

theorem doneAt_pins (n pLen qLen : Nat) : Pins (DoneAt n pLen qLen) [.rsp] := by
  intro D s t hs ht r hr
  obtain rfl := List.mem_singleton.mp hr
  exact (doneAt_rsp hs).trans (doneAt_rsp ht).symm

/-- `DoneAt` across a step that keeps the memory and the stack pointer. -/
theorem doneAt_keep' {n pLen qLen : Nat} {D : DonePublic} {s t : State} (h : DoneAt n pLen qLen D s)
    (hm : t.mem = s.mem) {rs : List Reg} (hk : Keep rs s t) (hsp : Reg.rsp ∉ rs) : DoneAt n pLen qLen D t := by
  obtain ⟨⟨W, hW, rest⟩, ⟨c0, c1, c2, cw⟩, c3, hf, hw, more⟩ := h
  refine ⟨⟨W, Refill.genMem_keep hW hm hk hsp, rest⟩, ⟨?_, ?_, ?_, hk.2.2 ▸ cw⟩, ?_,
    hf.congr (hk.gpr hsp) hk.2.2, hk.2.2.trans hw, more⟩
  · rw [Refill.ctlWord_eq_of_mem hm]; exact c0
  · rw [Refill.ctlWord_eq_of_mem hm]; exact c1
  · rw [Refill.ctlWord_eq_of_mem hm]; exact c2
  · rw [Refill.ctlWord_eq_of_mem hm]; exact c3

/-- `DoneAt` across writes to `state` and `used`. -/
theorem doneAt_frame {n pLen qLen : Nat} {D : DonePublic} {s t : State} (h : DoneAt n pLen qLen D s)
    (hf : Frame [⟨D.c1, 32⟩, ⟨D.c0, 8⟩] s.mem t.mem) (hsp : t.gpr .rsp = s.gpr .rsp) (hr : t.rd = s.rd)
    (hw : t.wr = s.wr) : DoneAt n pLen qLen D t := by
  obtain ⟨⟨W, hm, rest⟩, ⟨c0, c1, c2, cw⟩, c3, fv, hwr, more⟩ := h
  have e := D.ends
  obtain ⟨V, R⟩ := hm.rep
  have frameIn : (⟨D.ctx.geo.F, frameBytes⟩ : Region) ∈ D.ctx.changed := by simp [GenerationContext.changed]
  have Rt : Rep t.mem D.ctx.geo.F D.ctx.geo.hash V W := rep_of_disjoint_frame R hf
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (e.stChanged _ frameIn).symm
      · exact (e.usChanged _ frameIn).symm)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact e.stHash.symm
      · exact e.usHash.symm)
  have hmt : GenerationMemory (D.ctx.withHs D.hs) W t :=
    ⟨lay_of_rep hm.layout R Rt rfl hsp hw, ⟨V, Rt⟩, hm.slots, hm.scratch.congr hw,
      Refill.tapeMemory_frame hm.seeds hf (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact e.stSeeds.symm
        · exact e.usSeeds.symm) hr hw,
      Refill.tapeMemory_frame hm.hs hf (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact e.stRand.symm.sub_left D.hsIn
        · exact e.usRand.symm.sub_left D.hsIn) hr hw,
      Refill.tapeMemory_frame hm.rand hf (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact e.stRand.symm
        · exact e.usRand.symm) hr hw⟩
  have cwd : ∀ k < 4, Refill.ctlWord t.mem D.ctx.geo.F k = Refill.ctlWord s.mem D.ctx.geo.F k :=
    fun k hk => Refill.ctlWord_frame hf (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact e.stCtl.symm
      · exact e.usCtl.symm) hk
  exact ⟨⟨W, hmt, rest⟩, ⟨(cwd 0 (by decide)).trans c0, (cwd 1 (by decide)).trans c1,
    (cwd 2 (by decide)).trans c2, hw ▸ cw⟩, (cwd 3 (by decide)).trans c3, fv.congr hsp hw, hw.trans hwr, more⟩

theorem doneAt_ctlIn {n pLen qLen : Nat} {D : DonePublic} {t : State} (h : DoneAt n pLen qLen D t) {k : Nat}
    (hk : k < 4) : InRegions (t.rd ++ t.wr) (off D.ctx.geo.F (296 + 8 * k)) 8 := by
  have cs : Scr t (off D.ctx.geo.F 296) 32 := Scr.of_mem h.2.1.2.2.2 (by
    have := D.ok.bound; simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [this])
  have := cs.ld (d := 8 * k) (by omega_using [hk])
  simpa [off_off] using this

theorem doneAt_stIn {n pLen qLen : Nat} {D : DonePublic} {t : State} (h : DoneAt n pLen qLen D t) {d : Nat}
    (hd : d + 8 ≤ 32) : InRegions t.wr (off D.c1 d) 8 :=
  (Scr.of_mem (h.2.2.2.2.1 ▸ D.ends.stIn) D.ends.stBound).st hd

theorem doneAt_usIn {n pLen qLen : Nat} {D : DonePublic} {t : State} (h : DoneAt n pLen qLen D t) :
    InRegions t.wr (off D.c0 0) 8 :=
  (Scr.of_mem (h.2.2.2.2.1 ▸ D.ends.usIn) D.ends.usBound).st (d := 0) (by decide)

/-! ## The pieces -/

theorem ctlLoad_ready {n pLen qLen : Nat} {D : DonePublic} {s : State} (h : DoneAt n pLen qLen D s) {k : Nat}
    (hk : k < 4) :
    WP isa (.block [.mov .rcx (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl k))]) s fun t =>
      DoneAt n pLen qLen D t ∧ t.gpr .rcx = Refill.ctlWord s.mem D.ctx.geo.F k := by
  have hr := doneAt_ctlIn h hk
  refine WP.mono (WP.keep [.rcx] (Q := fun t => t.gpr .rcx = Refill.ctlWord s.mem D.ctx.geo.F k ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨rc, mt⟩, kt⟩ => ⟨doneAt_keep' h mt kt (by decide), rc⟩
  xrun [Impl.Dsa.X86_64.Generation.Refill.ctl, Impl.Dsa.X86_64.Generation.Refill.frameBytes, ea_sp,
    doneAt_rsp h, hr]
  rfl

theorem stateWords_ready {n pLen qLen : Nat} {D : DonePublic} {s : State} (h : DoneAt n pLen qLen D s)
    (hrcx : s.gpr .rcx = D.c1) (first : List Instr)
    (hfirst : first = [.mov .rax (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 2)), .store (at0 .rcx) .rax,
        .store { base := .rcx, disp := 24 } .rdx] ∨
      first = [.mov32 .rax (.imm 0), .store (at0 .rcx) .rax, .store { base := .rcx, disp := 24 } .rax]) :
    WP isa (.block first) s (DoneAt n pLen qLen D) := by
  have s0 := doneAt_stIn h (d := 0) (by decide)
  have s3 := doneAt_stIn h (d := 24) (by decide)
  have c2 : InRegions (s.rd ++ s.wr) (off D.ctx.geo.F 312) 8 := doneAt_ctlIn h (k := 2) (by decide)
  replace s0 : InRegions s.wr D.c1 8 := by simpa [off] using s0
  have post : ∀ t : State, (∃ a b : BitVec 64, t.mem = (s.mem.writeW D.c1 a).writeW (off D.c1 24) b) →
      Keep [.rax] s t → DoneAt n pLen qLen D t := by
    intro t ⟨a, b, hm⟩ kt
    refine doneAt_frame h ?_ (kt.gpr (by decide)) kt.2.1 kt.2.2
    rw [hm]
    exact ((Frame.refl _ _).writeW (List.mem_cons_self ..) _ (Refill.contains_head _ (by decide))).writeW
      (List.mem_cons_self ..) _ (Offset.contains_base _ (d := 24) (by decide) (by decide))
  rcases hfirst with rfl | rfl
  · refine WP.mono (WP.keep [.rax] (Q := fun t => ∃ a b : BitVec 64,
      t.mem = (s.mem.writeW D.c1 a).writeW (off D.c1 24) b) ?_ rfl) fun t ⟨ht, kt⟩ => post t ht kt
    xrun [Impl.Dsa.X86_64.Generation.Refill.ctl, Impl.Dsa.X86_64.Generation.Refill.frameBytes, ea_sp,
      Refill.ea_at0', Refill.ea_24, doneAt_rsp h, hrcx, c2, s0, s3]
    exact ⟨_, _, rfl⟩
  · refine WP.mono (WP.keep [.rax] (Q := fun t => ∃ a b : BitVec 64,
      t.mem = (s.mem.writeW D.c1 a).writeW (off D.c1 24) b) ?_ rfl) fun t ⟨ht, kt⟩ => post t ht kt
    xrun [Refill.ea_at0', Refill.ea_24, hrcx, s0, s3]
    exact ⟨_, _, rfl⟩

theorem usedLoad_ready {n pLen qLen : Nat} {D : DonePublic} {s : State} (h : DoneAt n pLen qLen D s)
    (src : MemOp) (hsrc : src = Impl.Dsa.X86_64.Generation.Refill.ctl 3 ∨ src = sp 128) :
    WP isa (.block [.mov .rax (.mem src), .mov .rcx (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 0))]) s fun t =>
      DoneAt n pLen qLen D t ∧ t.gpr .rcx = D.c0 := by
  have c0 : InRegions (s.rd ++ s.wr) (off D.ctx.geo.F 296) 8 := doneAt_ctlIn h (k := 0) (by decide)
  have c3 : InRegions (s.rd ++ s.wr) (off D.ctx.geo.F 320) 8 := doneAt_ctlIn h (k := 3) (by decide)
  obtain ⟨⟨W, hm, _⟩, ⟨w0, _⟩, _⟩ := id h
  have w0' : s.mem.readW (off D.ctx.geo.F 296) 64 = D.c0 := w0
  have hsp : s.gpr .rsp = D.ctx.geo.F := hm.layout.rsp
  have f128 : InRegions (s.rd ++ s.wr) (off D.ctx.geo.F 128) 8 := hm.layout.ld (by decide)
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t => t.gpr .rcx = D.c0 ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨rc, mt⟩, kt⟩ => ⟨doneAt_keep' h mt kt (by decide), rc⟩
  rcases hsrc with rfl | rfl
  · xrun [Impl.Dsa.X86_64.Generation.Refill.ctl, Impl.Dsa.X86_64.Generation.Refill.frameBytes, ea_sp,
      hsp, c0, c3, w0']
  · xrun [Impl.Dsa.X86_64.Generation.Refill.ctl, Impl.Dsa.X86_64.Generation.Refill.frameBytes, ea_sp,
      hsp, c0, f128, w0']

theorem usedStore_ready {n pLen qLen : Nat} {D : DonePublic} {s : State} (h : DoneAt n pLen qLen D s)
    (hrcx : s.gpr .rcx = D.c0) : WP isa (.block [.store (at0 .rcx) .rax]) s (DoneAt n pLen qLen D) := by
  have u0 : InRegions s.wr D.c0 8 := by simpa [off] using doneAt_usIn h
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s.mem.writeW D.c0 (s.gpr .rax)) ?_ rfl) fun t ⟨hm, kt⟩ => ?_
  · xrun [Refill.ea_at0', hrcx, u0]
  refine doneAt_frame h ?_ (kt.gpr (by decide)) kt.2.1 kt.2.2
  rw [hm]
  exact (Frame.refl _ _).writeW (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _
    (Refill.contains_head _ (by decide))

/-! ## The blocks writing `state` and `used` -/

theorem doneAt_rcx_pins (n pLen qLen : Nat) (f : DonePublic → BitVec 64) :
    Pins (fun D s => DoneAt n pLen qLen D s ∧ s.gpr .rcx = f D) [.rsp, .rcx] := by
  intro D s t hs ht r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (doneAt_rsp hs.1).trans (doneAt_rsp ht.1).symm
  · exact hs.2.trans ht.2.symm

theorem stateBlock_ct (n pLen qLen : Nat) (first : List Instr)
    (hfirst : first = [.mov .rax (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 2)), .store (at0 .rcx) .rax,
        .store { base := .rcx, disp := 24 } .rdx] ∨
      first = [.mov32 .rax (.imm 0), .store (at0 .rcx) .rax, .store { base := .rcx, disp := 24 } .rax]) :
    RelCT isa (Two (DoneAt n pLen qLen))
      (.block ([.mov .rcx (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 1))] ++ first)) (Two (DoneAt n pLen qLen)) := by
  have tf : ∃ hc, (taint.check (Taint.ofRegs [.rsp, .rcx]) (.block first) hc).isSome = true := by
    rcases hfirst with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := fun D t => DoneAt n pLen qLen D t ∧ t.gpr .rcx = D.c1)
    [.rsp] (doneAt_pins n pLen qLen) (by taint_decide) fun D s h => ?_)
    (two_piece [.rsp, .rcx] (doneAt_rcx_pins n pLen qLen _) tf.choose_spec
      fun D s h => stateWords_ready h.1 h.2 first hfirst))
  exact WP.mono (ctlLoad_ready h (k := 1) (by decide)) fun t ⟨ht, hr⟩ => ⟨ht, hr.trans h.2.1.2.1⟩

theorem usedBlock_ct (n pLen qLen : Nat) (src : MemOp)
    (hsrc : src = Impl.Dsa.X86_64.Generation.Refill.ctl 3 ∨ src = sp 128) :
    RelCT isa (Two (DoneAt n pLen qLen))
      (.block (([.mov .rax (.mem src), .mov .rcx (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 0))] : List Instr) ++
        ([.store (at0 .rcx) .rax] : List Instr))) (Two (DoneAt n pLen qLen)) := by
  have ts : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .rax (.mem src),
      .mov .rcx (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 0))]) hc).isSome = true := by
    rcases hsrc with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  exact RelCT.block_append (RelCT.seq (two_piece (Ψ := fun D t => DoneAt n pLen qLen D t ∧ t.gpr .rcx = D.c0)
    [.rsp] (doneAt_pins n pLen qLen) ts.choose_spec fun D s h => usedLoad_ready h src hsrc)
    (two_piece [.rsp, .rcx] (doneAt_rcx_pins n pLen qLen _) (by taint_decide)
      fun D s h => usedStore_ready h.1 h.2))

/-! ## A seed that ran out -/

def DonePublic.withStatus (D : DonePublic) (st : BitVec 64) : DonePublic := { D with status := st }

def DonePublic.ranOutStatus (D : DonePublic) : BitVec 64 :=
  if D.ctx.rand.bytes.length - D.cursor < 32769 * D.ctx.geo.pLen then 0 else 2

/-- A status stored. -/
theorem doneStatus_ready {n pLen qLen : Nat} {D : DonePublic} {s : State} (h : DoneAt n pLen qLen D s)
    (k : Nat) (hk : k = 0 ∨ k = 2) :
    WP isa (.block (Impl.Dsa.X86_64.Generation.stackStatus k)) s
      (DoneAt n pLen qLen (D.withStatus (BitVec.ofNat 64 k))) := by
  obtain ⟨⟨W, hm, _⟩, ⟨c0, c1, c2, cw⟩, c3, hf, hw, _, hp, hq⟩ := h
  refine WP.mono (Refill.statusMem_ok hm k (by omega_using [hk])) fun u ⟨mu, fu, ku⟩ => ?_
  have cwd : ∀ j < 4, Refill.ctlWord u.mem D.ctx.geo.F j = Refill.ctlWord s.mem D.ctx.geo.F j :=
    fun j hj => D.ok.word fu hj
  refine ⟨⟨_, mu, by simp [upd, DonePublic.withStatus], fun h1 => ?_⟩,
    ⟨(cwd 0 (by decide)).trans c0, (cwd 1 (by decide)).trans c1, (cwd 2 (by decide)).trans c2, ku.2.2 ▸ cw⟩,
    (cwd 3 (by decide)).trans c3, hf.congr (ku.gpr (by decide)) ku.2.2, ku.2.2.trans hw, ?_, hp, hq⟩
  · rcases hk with rfl | rfl <;> simp [DonePublic.withStatus] at h1
  · rcases hk with rfl | rfl <;> simp [DonePublic.withStatus]

def RanOutCompared (n pLen qLen : Nat) (D : DonePublic) (t : State) : Prop :=
  (DoneAt n pLen qLen D t ∧ D.status = 0) ∧
  t.gpr .rcx = BitVec.ofNat 64 (D.ctx.rand.bytes.length - D.cursor) ∧
  t.gpr .rdx = BitVec.ofNat 64 (32769 * D.ctx.geo.pLen) ∧
  isa.eval .b t = some (decide (D.ctx.rand.bytes.length - D.cursor < 32769 * D.ctx.geo.pLen))

theorem ranOut_ct (n pLen qLen : Nat) (hp : pLen = 128 ∨ pLen = 256 ∨ pLen = 384) :
    RelCT isa (Two fun (D : DonePublic) s => DoneAt n pLen qLen D s ∧ D.status = 0)
      (Impl.Dsa.X86_64.Generation.Refill.ranOut pLen)
      (Two fun (D : DonePublic) s => DoneAt n pLen qLen (D.withStatus D.ranOutStatus) s) := by
  have tc : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .rcx (.mem (sp 120)),
      .alu .sub .rcx (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 3)),
      .mov32 .rdx (.imm (BitVec.ofNat 32 (Impl.Dsa.X86_64.Generation.Refill.budget pLen))),
      .alu .cmp .rcx (.reg .rdx)]) hc).isSome = true := by
    rcases hp with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩
  have tr : ∃ hc, (taint.check (Taint.ofRegs [.rsp, .rcx, .rdx])
      (.seq (.block [.mov32 .rax (.imm (BitVec.ofNat 32 (256 * pLen))), .alu .cmp .rcx (.reg .rax)])
        (.seq (.ite .b (.block []) (.block [.mov .rax (.reg .rcx)]))
          (.seq (.block [.alu .add .rax (.reg .rax), .alu .cmp .rax (.reg .rdx)])
            (.ite .b (.block [.mov .rdx (.reg .rax)]) (.block []))))) hc).isSome = true := by
    rcases hp with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩
  have pn : pLen ≤ 384 := by omega_using [hp]
  unfold Impl.Dsa.X86_64.Generation.Refill.ranOut
  refine RelCT.seq (two_piece (Ψ := RanOutCompared n pLen qLen) [.rsp]
    (fun D s t hs ht => doneAt_pins n pLen qLen D s t hs.1 ht.1) tc.choose_spec fun D s h => ?_) ?_
  · obtain ⟨hd, h0⟩ := h
    obtain ⟨⟨W, hm, _⟩, _, c3, _, _, _, hpl, _⟩ := id hd
    obtain ⟨V, R⟩ := hm.rep
    have h15 : W 15 = BitVec.ofNat 64 D.ctx.rand.bytes.length :=
      (hm.slots 15 (by simp [generationSlots])).trans (D.ctx.withHs D.hs).randLengthSlot
    have h3r : InRegions (s.rd ++ s.wr) (off D.ctx.geo.F 320) 8 := doneAt_ctlIn hd (k := 3) (by decide)
    have h3 : s.mem.readW (off D.ctx.geo.F 320) 64 = BitVec.ofNat 64 D.cursor := c3
    refine WP.mono (Refill.ranOutCmp_ok hm.layout R h3r h3 h15 D.cursorBound D.ends.lenBound pn)
      fun t ⟨⟨rc, rd, cf, mt⟩, kt⟩ => ?_
    subst pLen
    exact ⟨⟨doneAt_keep' hd mt kt (by decide), h0⟩, rc, rd, by simp only [eval, cf]⟩
  refine two_ite (fun D s t hs ht => hs.2.2.2.trans ht.2.2.2.symm) ?_ ?_
  · refine two_post (Ψ := fun (D : DonePublic) s => DoneAt n pLen qLen (D.withStatus D.ranOutStatus) s)
      (two_taint [.rsp, .rcx, .rdx] ?_ tr.choose_spec) fun D s h => ?_
    · intro D s t hs ht r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (doneAt_rsp hs.1.1.1).trans (doneAt_rsp ht.1.1.1).symm
      · exact hs.1.2.1.trans ht.1.2.1.symm
      · exact hs.1.2.2.1.trans ht.1.2.2.1.symm
    · obtain ⟨⟨⟨hd, h0⟩, rc, rd, cb⟩, hb⟩ := h
      have lt : D.ctx.rand.bytes.length - D.cursor < 32769 * D.ctx.geo.pLen := by
        have := cb.symm.trans hb; simpa using this
      have e : D.withStatus D.ranOutStatus = D := by
        simp only [DonePublic.ranOutStatus, lt, ↓reduceIte, ← h0]; rfl
      have pl : D.ctx.geo.pLen = pLen := hd.2.2.2.2.2.2.1
      subst pLen
      have hl := D.ends.lenBound
      refine WP.mono (Refill.request_ok (L := D.ctx.rand.bytes.length - D.cursor) (by omega_using [hl]) (by omega_using [hp])
        (by omega_using [hp]) rc rd) fun t ⟨_, mt, kt⟩ => ?_
      rw [e]; exact doneAt_keep' hd mt kt (by decide)
  · refine two_piece [.rsp] (fun D s t hs ht => doneAt_pins n pLen qLen D s t hs.1.1.1 ht.1.1.1)
      (by taint_decide) fun D s h => ?_
    obtain ⟨⟨⟨hd, _⟩, _, _, cb⟩, hb⟩ := h
    have ge : ¬ D.ctx.rand.bytes.length - D.cursor < 32769 * D.ctx.geo.pLen := by
      have := cb.symm.trans hb; simpa using this
    have e : D.ranOutStatus = BitVec.ofNat 64 2 := by simp only [DonePublic.ranOutStatus, ge, ↓reduceIte]; rfl
    rw [e]; exact doneStatus_ready hd 2 (Or.inr rfl)

/-! ## `results` -/

def ZeroTested (n pLen qLen : Nat) (D : DonePublic) (t : State) : Prop :=
  DoneAt n pLen qLen D t ∧ isa.eval .e t = some (D.status == 0)

theorem zeroTest_ready {n pLen qLen : Nat} {D : DonePublic} {s : State} (h : DoneAt n pLen qLen D s) :
    WP isa (.block [.mov .rax (.mem (sp 152)), .alu .test .rax (.reg .rax)]) s (ZeroTested n pLen qLen D) := by
  obtain ⟨⟨W, hm, h19, _⟩, _⟩ := id h
  refine WP.mono (Refill.zeroTest_ok hm) fun t ⟨z, _, mt, kt⟩ => ?_
  exact ⟨doneAt_keep' h mt kt (by decide), by simp only [eval, z, h19]⟩

theorem zeroTest_ct (n pLen qLen : Nat) :
    RelCT isa (Two (DoneAt n pLen qLen)) (.block [.mov .rax (.mem (sp 152)), .alu .test .rax (.reg .rax)])
      (Two (ZeroTested n pLen qLen)) :=
  two_piece [.rsp] (doneAt_pins n pLen qLen) (by taint_decide) fun _ _ h => zeroTest_ready h

def OneTested (n pLen qLen : Nat) (D : DonePublic) (t : State) : Prop :=
  DoneAt n pLen qLen D t ∧ isa.eval .e t = some (D.status == 1)

theorem results_ct (n pLen qLen : Nat) (hp : pLen = 128 ∨ pLen = 256 ∨ pLen = 384) :
    RelCT isa (Two (DoneAt n pLen qLen)) (Impl.Dsa.X86_64.Generation.Refill.results pLen)
      (Two (DoneAt n pLen qLen)) := by
  have zpins : Pins (ZeroTested n pLen qLen) [.rsp] := fun D s t hs ht => doneAt_pins n pLen qLen D s t hs.1 ht.1
  unfold Impl.Dsa.X86_64.Generation.Refill.results
  refine RelCT.seq (zeroTest_ct n pLen qLen) (two_ite (fun D s t hs ht => hs.2.trans ht.2.symm) ?_ ?_)
  · refine RelCT.seq (((ranOut_ct n pLen qLen hp).mono (fun s t h => ?_) fun _ _ h => two_image _ h)) ?_
    · obtain ⟨D, ⟨⟨hs, es⟩, bs⟩, ⟨⟨ht, _⟩, _⟩⟩ := h
      have z : D.status = 0 := by have := es.symm.trans bs; simpa using this
      exact ⟨D, ⟨hs, z⟩, ⟨ht, z⟩⟩
    refine RelCT.seq (zeroTest_ct n pLen qLen) (two_ite (fun D s t hs ht => hs.2.trans ht.2.symm) ?_ ?_)
    · refine (show RelCT isa _ (.block (([.mov .rcx (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 1))] ++
          [.mov .rax (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 2)), .store (at0 .rcx) .rax,
            .store { base := .rcx, disp := 24 } .rdx]) ++
          ([.mov .rax (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 3)),
            .mov .rcx (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 0))] ++ [.store (at0 .rcx) .rax]))) _ from ?_)
      refine RelCT.block_append (RelCT.seq ((stateBlock_ct n pLen qLen _ (Or.inl rfl)).mono
        (fun _ _ h => two_mono (fun _ _ h => h.1.1) h) fun _ _ h => h) (usedBlock_ct n pLen qLen _ (Or.inl rfl)))
    · refine (show RelCT isa _ (.block (([.mov .rcx (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 1))] ++
          [.mov32 .rax (.imm 0), .store (at0 .rcx) .rax, .store { base := .rcx, disp := 24 } .rax]) ++
          ([.mov .rax (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 3)),
            .mov .rcx (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 0))] ++ [.store (at0 .rcx) .rax]))) _ from ?_)
      refine RelCT.block_append (RelCT.seq ((stateBlock_ct n pLen qLen _ (Or.inr rfl)).mono
        (fun _ _ h => two_mono (fun _ _ h => h.1.1) h) fun _ _ h => h) (usedBlock_ct n pLen qLen _ (Or.inl rfl)))
  · refine RelCT.seq (R := Two (OneTested n pLen qLen)) ?_
      (two_ite (fun D s t hs ht => hs.2.trans ht.2.symm) ?_ ?_)
    · refine (show RelCT isa _ (.block (([.mov .rcx (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 1))] ++
          [.mov32 .rax (.imm 0), .store (at0 .rcx) .rax, .store { base := .rcx, disp := 24 } .rax]) ++
          Impl.Dsa.X86_64.Generation.successStatus)) _ from ?_)
      refine RelCT.block_append (RelCT.seq ((stateBlock_ct n pLen qLen _ (Or.inr rfl)).mono
        (fun _ _ h => two_mono (fun _ _ h => h.1.1) h) fun _ _ h => h)
        (two_piece [.rsp] (doneAt_pins n pLen qLen) (by taint_decide) fun D s h => ?_))
      obtain ⟨⟨W, hm, h19, _⟩, _⟩ := id h
      obtain ⟨V, R⟩ := hm.rep
      refine WP.mono (successStatus_ok hm.layout R) fun t ⟨z, mt, kt⟩ => ?_
      exact ⟨doneAt_keep' h mt kt (by decide), by simp only [eval, z, h19]⟩
    · exact (show RelCT isa _ (.block ([.mov .rax (.mem (sp 128)),
          .mov .rcx (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 0))] ++ [.store (at0 .rcx) .rax])) _ from
        (usedBlock_ct n pLen qLen _ (Or.inr rfl)).mono (fun _ _ h => two_mono (fun _ _ h => h.1.1) h)
          fun _ _ h => h)
    · exact (show RelCT isa _ (.block ([.mov .rax (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 3)),
          .mov .rcx (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 0))] ++ [.store (at0 .rcx) .rax])) _ from
        (usedBlock_ct n pLen qLen _ (Or.inl rfl)).mono (fun _ _ h => two_mono (fun _ _ h => h.1.1) h)
          fun _ _ h => h)

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Timing of the refillable-tape search's output and status -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Mgf1.X86_64 (sp)

/-- The frame's status word, after the output. -/
def StatusAt (D : DonePublic) (t : State) : Prop :=
  ∃ V W, Lay t D.ctx.geo.F D.ctx.geo.hash ∧ Rep t.mem D.ctx.geo.F D.ctx.geo.hash V W ∧ W 19 = D.status

theorem DonePublic.outputPlan (D : DonePublic) : OutputPlan (D.ctx.withHs D.hs) :=
  ⟨D.ends.out.lengthSlot, D.ends.out.bound, D.ends.out.separate⟩

theorem finishOutput_status {n pLen qLen : Nat} {D : DonePublic} {s : State} (h : DoneAt n pLen qLen D s) :
    WP isa Impl.Dsa.X86_64.Generation.finishOutput s (StatusAt D) := by
  obtain ⟨⟨W, hm, h19, _⟩, _, _, _, hwr, _⟩ := h
  have o := D.outputPlan
  have pn : 0 < D.ctx.geo.pLen ∧ D.ctx.geo.pLen ≤ 384 := by rcases D.ctx.geo.width with hh | hh | hh <;> omega_using [hh]
  have qn : D.ctx.geo.qLen ≤ 32 := by rcases D.ctx.geo.qWidth with hh | hh <;> omega_using [hh]
  have pn' : 0 < (D.ctx.withHs D.hs).geo.pLen ∧ (D.ctx.withHs D.hs).geo.pLen ≤ 384 := pn
  have qn' : (D.ctx.withHs D.hs).geo.qLen ≤ 32 := qn
  have hw : (⟨(D.ctx.withHs D.hs).saved 6, 2 * D.ctx.geo.pLen + D.ctx.geo.qLen⟩ : Region) ∈ s.wr := by
    rw [hwr]; simpa [GenerationContext.withHs] using D.ends.outIn
  obtain ⟨V, R⟩ := hm.rep
  unfold Impl.Dsa.X86_64.Generation.finishOutput
  refine WP.seq (WP.mono (successStatus_ok hm.layout R) fun u ⟨hz, hmu, ku⟩ => ?_)
  have mu := hm.congr hmu ku
  have hwu : (⟨(D.ctx.withHs D.hs).saved 6, 2 * D.ctx.geo.pLen + D.ctx.geo.qLen⟩ : Region) ∈ u.wr := by
    rw [ku.2.2]; exact hw
  obtain ⟨Vu, Ru⟩ := mu.rep
  by_cases e : W 19 = 1
  · refine WP.ite true (by simp only [eval, hz, e, beq_self_eq_true]) (fun _ => ?_)
      (fun impossible => Bool.noConfusion impossible)
    refine WP.mono (output_copy_context mu o hwu _ (VG.Proof.Bignum.bytesAt_length _ _ _) rfl)
      fun u₁ ⟨_, _, f₁, k₁⟩ => ?_
    have R₁ : Rep u₁.mem D.ctx.geo.F D.ctx.geo.hash Vu W := Ru.apart o.apart f₁
    exact ⟨Vu, W, lay_of_rep mu.layout Ru R₁ rfl (k₁.gpr (by decide)) k₁.2.2, R₁, h19⟩
  · refine WP.ite false (by simp only [eval, hz, beq_eq_false_iff_ne.mpr e])
      (fun impossible => Bool.noConfusion impossible) (fun _ => ?_)
    have h6 := mu.slots 6 (by simp [generationSlots])
    have h7 := (mu.slots 7 (by simp [generationSlots])).trans o.lengthSlot
    unfold Impl.Dsa.X86_64.Generation.outputZero
    refine WP.seq (WP.mono (zeroArgs_ok mu.layout Ru) fun u₁ ⟨L₁, R₁, _, k₁⟩ => ?_)
    refine WP.mono (zeroOut_ok L₁ R₁ (by simp [upd, h6]) (by simpa [upd] using h7) (by omega_using [pn']) (by omega_using [pn', qn'])
      (by rw [k₁.2.2]; exact hwu) o.bound o.apart) fun u₂ ⟨L₂, _, R₂, _, _, _⟩ => ?_
    exact ⟨_, _, L₂, R₂, by simpa [upd] using h19⟩

def StatusTested (D : DonePublic) (t : State) : Prop :=
  StatusAt D t ∧ isa.eval .e t = some (D.status == 2)

theorem statusAt_pins : Pins StatusAt [.rsp] := by
  intro D s t ⟨_, _, Ls, _⟩ ⟨_, _, Lt, _⟩ r hr
  obtain rfl := List.mem_singleton.mp hr
  exact Ls.rsp.trans Lt.rsp.symm

theorem returnStatus_ct :
    RelCT isa (Two StatusAt) Impl.Dsa.X86_64.Generation.Refill.returnStatus (fun _ _ => True) := by
  unfold Impl.Dsa.X86_64.Generation.Refill.returnStatus
  refine RelCT.seq (two_piece (Ψ := StatusTested) [.rsp] statusAt_pins (by taint_decide) fun D s h => ?_) ?_
  · obtain ⟨V, W, L, R, h19⟩ := h
    refine WP.mono (WP.keep [.rax] (Q := fun t => t.zf = some (W 19 == 2) ∧ t.mem = s.mem) ?_ rfl)
      fun t ⟨⟨z, mt⟩, kt⟩ => ?_
    · xrun [ea_sp, L.rsp, L.ld (d := 152) (by decide), R.slot (d := 152) (k := 19) rfl (by decide) rfl]
      rw [sub_beq_zero]
    have Rt : Rep t.mem D.ctx.geo.F D.ctx.geo.hash V W := mt ▸ R
    exact ⟨⟨V, W, lay_of_rep L R Rt rfl (kt.gpr (by decide)) kt.2.2, Rt, h19⟩, by simp only [eval, z, h19]⟩
  refine two_ite (fun D s t hs ht => hs.2.trans ht.2.symm) ?_ ?_
  · exact two_taint [] (by intro _ _ _ _ _ r hr; simp at hr) (by taint_decide)
  · exact two_taint [] (by intro _ _ _ _ _ r hr; simp at hr) (by taint_decide)

theorem finish_ct (pLen qLen : Nat) (hp : pLen = 128 ∨ pLen = 256 ∨ pLen = 384) :
    RelCT isa (Two (DoneAt 6 pLen qLen)) (Impl.Dsa.X86_64.Generation.Refill.finish pLen) (fun _ _ => True) := by
  unfold Impl.Dsa.X86_64.Generation.Refill.finish
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine RelCT.seq (results_ct 6 pLen qLen hp) (RelCT.seq (two_post (Ψ := StatusAt) ?_
    fun D s h => finishOutput_status h) returnStatus_ct)
  refine two_map (fun D : DonePublic => (⟨D.ctx.withHs D.hs, D.status == 1, D.ws⟩ : OutputPublic))
    (fun D s h => ?_) (finishOutput_ct 6 (Or.inr (Or.inr rfl)))
  obtain ⟨⟨W, hm, h19, _⟩, _, _, hf, _⟩ := h
  exact ⟨⟨W, hm, by rw [h19]⟩, hf⟩

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! ### `Dsa.X86_64.Generation.RefillCTStep`, which only this module used -/

section

/-! # Timing of one step of the refillable-tape search's controller -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Proof.MillerRabin.X86_64
open VG.Impl.Mgf1.X86_64 (sp)

variable {checkName : String}

/-! ## The iteration's public states -/

def Begun (n pLen qLen : Nat) (P : LoopPublic) (t : State) : Prop :=
  RefillLoopBefore n pLen qLen P t ∧ Refill.ctlWord t.mem P.ctx.geo.F 3 = BitVec.ofNat 64 P.start ∧
  t.gpr .rax = BitVec.ofNat 64 P.start

def Started (n pLen qLen : Nat) (P : LoopPublic) (t : State) : Prop :=
  Begun n pLen qLen P t ∧ isa.eval .e t = some (decide (P.left = 0))

def Roomed (n pLen qLen : Nat) (P : LoopPublic) (t : State) : Prop :=
  Begun n pLen qLen P t ∧ P.left ≠ 0 ∧
  isa.eval .b t = some (decide (P.ctx.rand.bytes.length - P.start < P.ctx.geo.qLen))

/-- The seed's public inputs. -/
def LoopPublic.seedPub (P : LoopPublic) (room : P.start + P.ctx.geo.qLen ≤ P.ctx.rand.bytes.length) :
    SeedPublic where
  context := P.context
  seed := P.ctx.rand.slice P.start P.ctx.geo.qLen room
  length := by
    show ((P.ctx.rand.bytes.drop P.start).take P.ctx.geo.qLen).length = P.ctx.geo.qLen
    simp only [List.length_take, List.length_drop]; omega_using [room]
  used := P.start + P.ctx.geo.qLen
  seedCursor := 0
  bound := room
  ws := P.ws
  wr := P.wr
  header := P.header

def Seeded (n pLen qLen : Nat) (P : LoopPublic) (t : State) : Prop :=
  (∃ room, SeedAttemptBefore n pLen qLen (P.seedPub room) t) ∧
  CtlAt P.ctx.geo.F P.c0 P.c1 P.left t ∧ Refill.ctlWord t.mem P.ctx.geo.F 3 = BitVec.ofNat 64 P.start ∧
  P.left ≠ 0

def Attempted (n pLen qLen : Nat) (P : LoopPublic) (t : State) : Prop :=
  (∃ W used, GenerationMemory (P.ctx.withHs P.hsNext) W t ∧ used ≤ P.ctx.rand.bytes.length ∧
    W 16 = BitVec.ofNat 64 used ∧ W 10 = 0 ∧ SeedOutcome P.context P.res W used t) ∧
  CtlAt P.ctx.geo.F P.c0 P.c1 P.left t ∧ Refill.ctlWord t.mem P.ctx.geo.F 3 = BitVec.ofNat 64 P.start ∧
  FrV n P.ctx.geo.F P.ws t ∧ t.wr = P.wr ∧ P.left ≠ 0 ∧ P.ctx.geo.pLen = pLen ∧ P.ctx.geo.qLen = qLen

def Tested (n pLen qLen : Nat) (P : LoopPublic) (t : State) : Prop :=
  Attempted n pLen qLen P t ∧ isa.eval .e t = some (P.status == 3)

/-! ## Each piece -/

theorem head_ready {n pLen qLen : Nat} {P : LoopPublic} {s : State} (h : RefillLoopBefore n pLen qLen P s) :
    WP isa (.block [.mov .rax (.mem (sp 128)), .store (Impl.Dsa.X86_64.Generation.Refill.ctl 3) .rax,
        .mov .rcx (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 2)), .alu .test .rcx (.reg .rcx)]) s
      (Started n pLen qLen P) := by
  obtain ⟨⟨W, hm, h16, h10⟩, ⟨c0, c1, c2, cw⟩, hf, hw, hp, hq⟩ := h
  obtain ⟨V, R⟩ := hm.rep
  have h2 : (s.mem.writeW (off P.ctx.geo.F 320) (BitVec.ofNat 64 P.start)).readW (off P.ctx.geo.F 312) 64 =
      BitVec.ofNat 64 P.left := by
    rw [← c2]; exact Refill.ctlWord_write_other s.mem _ (j := 2) (k := 3) (by decide) (by decide) (by decide) _
  have ln : P.left < 2 ^ 64 := by have := P.leftBound; unfold Spec.Dsa.parameterSeeds at this; omega_using [this]
  refine WP.mono (Refill.iterStart_ok hm.layout R cw P.ok.bound h16 ln h2) fun t ⟨rax, zf, mt, kt⟩ => ?_
  have fr : Frame [Refill.ctlRegion P.ctx.geo.F] s.mem t.mem := by
    rw [mt]; exact Refill.ctl_write s.mem _ (k := 3) (by decide) _
  have hmt := P.ok.gm P.hsIn hm fr (kt.gpr (by decide)) kt.2.1 kt.2.2
  refine ⟨⟨⟨⟨W, hmt, h16, h10⟩, ⟨?_, ?_, ?_, kt.2.2 ▸ cw⟩, hf.congr (kt.gpr (by decide)) kt.2.2,
    kt.2.2.trans hw, hp, hq⟩, ?_, rax⟩, by simp only [eval, zf]⟩
  · rw [mt]; exact (Refill.ctlWord_write_other s.mem _ (j := 0) (k := 3) (by decide) (by decide) (by decide) _).trans c0
  · rw [mt]; exact (Refill.ctlWord_write_other s.mem _ (j := 1) (k := 3) (by decide) (by decide) (by decide) _).trans c1
  · rw [mt]; exact (Refill.ctlWord_write_other s.mem _ (j := 2) (k := 3) (by decide) (by decide) (by decide) _).trans c2
  · rw [mt]; exact Refill.ctlWord_write_self s.mem _ 3 _

/-- A status word stored, with the controller's words kept. -/
theorem stopped_ready {n pLen qLen m : Nat} {P : LoopPublic} {t : State} (h : Begun n pLen qLen P t)
    (status : Nat) (hs : status = 0 ∨ status = 2) :
    WP isa (.block (Impl.Dsa.X86_64.Generation.stackStatus status)) t
      (LoopMid n pLen qLen m (.inr (P.stop (BitVec.ofNat 64 status)))) := by
  obtain ⟨⟨⟨W, hm, _, _⟩, ⟨c0, c1, c2, cw⟩, hf, hw, hp, hq⟩, c3, _⟩ := h
  refine WP.mono (Refill.statusMem_ok hm status (by omega_using [hs])) fun u ⟨mu, fu, ku⟩ => ?_
  have cwd : ∀ k < 4, Refill.ctlWord u.mem P.ctx.geo.F k = Refill.ctlWord t.mem P.ctx.geo.F k :=
    fun k hk => P.ok.word fu hk
  refine ⟨⟨_, mu, by simp [upd, LoopPublic.stop], fun h1 => ?_⟩,
    ⟨(cwd 0 (by decide)).trans c0, (cwd 1 (by decide)).trans c1, (cwd 2 (by decide)).trans c2, ku.2.2 ▸ cw⟩,
    (cwd 3 (by decide)).trans c3, hf.congr (ku.gpr (by decide)) ku.2.2, ku.2.2.trans hw, ?_, hp, hq⟩
  · rcases hs with rfl | rfl <;> simp [LoopPublic.stop] at h1
  · rcases hs with rfl | rfl <;> simp [LoopPublic.stop]

theorem room_ready {n pLen qLen : Nat} {P : LoopPublic} {t : State} (h : Started n pLen qLen P t)
    (he : isa.eval .e t = some false) :
    WP isa (.block [.mov .rcx (.mem (sp 120)), .alu .sub .rcx (.reg .rax),
        .alu .cmp .rcx (.imm (BitVec.ofNat 32 qLen))]) t (Roomed n pLen qLen P) := by
  obtain ⟨hb, hz⟩ := h
  obtain ⟨hl, c3, rax⟩ := id hb
  obtain ⟨⟨W, hm, _, _⟩, _, _, _, _, hq⟩ := id hl
  obtain ⟨V, R⟩ := hm.rep
  have ne : P.left ≠ 0 := by
    intro e; have := hz.symm.trans he; simp [e] at this
  have h15 : W 15 = BitVec.ofNat 64 P.ctx.rand.bytes.length :=
    (hm.slots 15 (by simp [generationSlots])).trans (P.ctx.withHs P.hs).randLengthSlot
  have q31 : qLen < 2 ^ 31 := by rcases P.ctx.geo.qWidth with hh | hh <;> omega
  refine WP.mono (Refill.roomCheck_ok hm.layout R rax h15 P.startBound P.ctx.rand.size q31)
    fun u ⟨cf, mu, ku⟩ => ?_
  refine ⟨⟨loopBefore_keep hl mu (ku.mono (by decide)), by rw [Refill.ctlWord_eq_of_mem mu]; exact c3,
    (ku.gpr (by decide)).trans rax⟩, ne, by simp only [eval, cf, hq]⟩

theorem seedStart_ready {n pLen qLen : Nat} {P : LoopPublic} {t : State} (h : Roomed n pLen qLen P t)
    (hb : isa.eval .b t = some false) :
    WP isa (.block (Impl.Dsa.X86_64.Generation.Refill.seedStart qLen)) t (Seeded n pLen qLen P) := by
  obtain ⟨⟨⟨⟨W, hm, _, h10⟩, ⟨c0, c1, c2, cw⟩, hf, hw, hp, hq⟩, c3, rax⟩, ne, hc⟩ := h
  have room : P.start + P.ctx.geo.qLen ≤ P.ctx.rand.bytes.length := by
    have h1 := hc.symm.trans hb; have := P.startBound
    simp only [Option.some.injEq, decide_eq_false_iff_not, Nat.not_lt] at h1; omega_using [this, h1]
  obtain ⟨V, R⟩ := hm.rep
  have h13 : W 13 = P.ctx.rand.ptr :=
    (hm.slots 13 (by simp [generationSlots])).trans (P.ctx.withHs P.hs).randSlot
  have q31 : qLen < 2 ^ 31 := by rcases P.ctx.geo.qWidth with hh | hh <;> omega
  refine WP.mono (Refill.seedStart_ok hm.layout R rax h13 q31) fun u ⟨Lu, Ru, fu, ku⟩ => ?_
  have hmu : GenerationMemory P.context (upd (upd W 1 (off P.ctx.rand.ptr P.start)) 16
      (BitVec.ofNat 64 (P.start + qLen))) u := by
    refine hm.frame Lu ⟨V, Ru⟩ ?_ (GenerationContext.frame_single fu) ku.2.1 ku.2.2
    intro k hk
    simp only [generationSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have cwd : ∀ k < 4, Refill.ctlWord u.mem P.ctx.geo.F k = Refill.ctlWord t.mem P.ctx.geo.F k := fun k hk =>
    Refill.ctlWord_frame fu (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact Refill.ctl_frame _) hk
  subst hq
  refine ⟨⟨room, ⟨⟨_, hmu, by simp [upd, LoopPublic.seedPub, GenerationTape.slice], by simp [upd, LoopPublic.seedPub],
    by simpa [upd, LoopPublic.seedPub] using h10⟩, hmu.rand.slice room, hf.congr (ku.gpr (by decide)) ku.2.2,
    ku.2.2.trans hw, rfl⟩, hp⟩,
    ⟨(cwd 0 (by decide)).trans c0, (cwd 1 (by decide)).trans c1, (cwd 2 (by decide)).trans c2, ku.2.2 ▸ cw⟩,
    (cwd 3 (by decide)).trans c3, ne⟩

theorem attempt_ready (H : GenerationHashes) (M : Mont) (Sq : MontS) (T : PrimeTest)
    {n pLen qLen : Nat} {P : LoopPublic} {t : State} (h : Seeded n pLen qLen P t) :
    WP isa (Impl.Dsa.X86_64.Generation.Refill.refillAttempt (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm
      T.run pLen qLen) t (Attempted n pLen qLen P) := by
  obtain ⟨⟨room, ⟨⟨W, hm, h1, h16, h10⟩, seed, hf, hw, hq⟩, hp⟩, ⟨c0, c1, c2, cw⟩, c3, ne⟩ := h
  have call := ctAttempt_ok (checkName := checkName) H M Sq T hm (P.seedPub room).seed (P.seedPub room).length
    seed h1 h16 room
  change P.ctx.geo.pLen = pLen at hp
  change P.ctx.geo.qLen = qLen at hq
  subst hp; subst hq
  refine WP.mono call fun u ⟨W', used, mu, hu, u16, slots, outcome, fu, ru, wu⟩ => ?_
  have cwd : ∀ k < 4, Refill.ctlWord u.mem P.ctx.geo.F k = Refill.ctlWord t.mem P.ctx.geo.F k :=
    fun k hk => P.ok.word fu hk
  have mu' : GenerationMemory (P.ctx.withHs P.hsNext) W' u := Refill.withHs_withHs P.ctx P.hs _ ▸ mu
  refine ⟨⟨W', used, mu', hu, u16, ?_, outcome⟩,
    ⟨(cwd 0 (by decide)).trans c0, (cwd 1 (by decide)).trans c1, (cwd 2 (by decide)).trans c2, wu ▸ cw⟩,
    (cwd 3 (by decide)).trans c3, hf.congr (mu.layout.rsp.trans hm.layout.rsp.symm) wu, wu.trans hw, ne, rfl, rfl⟩
  rw [slots 10 (by simp [refillSlots]), h10]; rfl

theorem LoopPublic.status_cases (P : LoopPublic) : P.status = 0 ∨ P.status = 1 ∨ P.status = 3 := by
  unfold LoopPublic.status; split <;> simp

theorem outcome_public {P : LoopPublic} {W : Nat → BitVec 64} {used : Nat} {t : State}
    (h : SeedOutcome P.context P.res W used t) (hu : used ≤ P.ctx.rand.bytes.length) :
    W 19 = P.status ∧ (P.status ≠ 0 → used = P.after) := by
  rcases h with ⟨h19, hr⟩ | ⟨h19, hr⟩ | ⟨h19, a, hr, _⟩
  · exact ⟨by rw [h19]; simp [LoopPublic.status, hr], fun h0 => by simp [LoopPublic.status, hr] at h0⟩
  · refine ⟨by rw [h19]; simp [LoopPublic.status, hr], fun _ => ?_⟩
    simp only [LoopPublic.after, hr]
    change used = P.ctx.rand.bytes.length - (P.ctx.rand.bytes.drop used).length
    rw [List.length_drop]; omega_using [hu]
  · refine ⟨by rw [h19]; simp [LoopPublic.status, hr], fun _ => ?_⟩
    simp only [LoopPublic.after, hr]
    change used = P.ctx.rand.bytes.length - (P.ctx.rand.bytes.drop used).length
    rw [List.length_drop]; omega_using [hu]

theorem attempted_keep {n pLen qLen : Nat} {P : LoopPublic} {s t : State} (h : Attempted n pLen qLen P s)
    (hm : t.mem = s.mem) (hk : Keep [.rax] s t) : Attempted n pLen qLen P t := by
  obtain ⟨⟨W, used, hW, hu, h16, h10, outcome⟩, ⟨c0, c1, c2, cw⟩, c3, hf, hw, rest⟩ := h
  refine ⟨⟨W, used, hW.congr hm hk, hu, h16, h10, ?_⟩, ⟨?_, ?_, ?_, hk.2.2 ▸ cw⟩, ?_,
    hf.congr (hk.gpr (by decide)) hk.2.2, hk.2.2.trans hw, rest⟩
  · rcases outcome with o | o | ⟨h19, a, hr, bytes⟩
    · exact Or.inl o
    · exact Or.inr (Or.inl o)
    · exact Or.inr (Or.inr ⟨h19, a, hr, hm ▸ bytes⟩)
  · rw [Refill.ctlWord_eq_of_mem hm]; exact c0
  · rw [Refill.ctlWord_eq_of_mem hm]; exact c1
  · rw [Refill.ctlWord_eq_of_mem hm]; exact c2
  · rw [Refill.ctlWord_eq_of_mem hm]; exact c3

theorem test_ready {n pLen qLen : Nat} {P : LoopPublic} {t : State} (h : Attempted n pLen qLen P t) :
    WP isa (.block Impl.Dsa.X86_64.Generation.tapeStatus) t (Tested n pLen qLen P) := by
  obtain ⟨⟨W, used, hm, hu, _, _, outcome⟩, _⟩ := id h
  have h19 := (outcome_public outcome hu).1
  refine WP.mono (Refill.statusTest_ok hm) fun u ⟨z, _, mu, ku⟩ => ?_
  exact ⟨attempted_keep h mu ku, by rw [z, h19]⟩

theorem reject_ready {n pLen qLen m : Nat} {P : LoopPublic} {t : State} (h : Tested n pLen qLen P t)
    (he : isa.eval .e t = some true) (hl : P.left = m) :
    WP isa (.block Impl.Dsa.X86_64.Generation.Refill.rejected) t (LoopMid n pLen qLen m (.inl P.next)) := by
  obtain ⟨⟨⟨W, used, hm, hu, h16, h10, outcome⟩, ⟨c0, c1, c2, cw⟩, c3, hf, hw, ne, hp, hq⟩, hs⟩ := h
  have s3 : P.status = 3 := by
    have := hs.symm.trans he; simpa using this
  obtain ⟨h19, hafter⟩ := outcome_public outcome hu
  have uafter := hafter (by rw [s3]; decide)
  have ln : P.left - 1 + 1 < 2 ^ 64 := by have := P.leftBound; unfold Spec.Dsa.parameterSeeds at this; omega_using [this]
  have h2 : t.mem.readW (off P.ctx.geo.F 312) 64 = BitVec.ofNat 64 (P.left - 1 + 1) := by
    rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero ne)]; exact c2
  refine WP.mono (Refill.rejected_ok hm.layout.rsp cw P.ok.bound ln h2) fun u ⟨mu, ku⟩ => ?_
  have fr : Frame [Refill.ctlRegion P.ctx.geo.F] t.mem u.mem := by
    rw [mu]; exact Refill.ctl_write t.mem _ (k := 2) (by decide) _
  have hmu := P.ok.gm (refillHs_sub P.context _ _ P.hsIn) hm fr (ku.gpr (by decide)) ku.2.1 ku.2.2
  refine ⟨⟨⟨W, hmu, by rw [h16, uafter]; rfl, h10⟩, ⟨?_, ?_, ?_, ku.2.2 ▸ cw⟩,
    hf.congr (ku.gpr (by decide)) ku.2.2, ku.2.2.trans hw, hp, hq⟩, ⟨W, hmu, h19.trans s3⟩, ?_⟩
  · rw [mu]; exact (Refill.ctlWord_write_other t.mem _ (j := 0) (k := 2) (by decide) (by decide) (by decide) _).trans c0
  · rw [mu]; exact (Refill.ctlWord_write_other t.mem _ (j := 1) (k := 2) (by decide) (by decide) (by decide) _).trans c1
  · rw [mu]; exact Refill.ctlWord_write_self t.mem _ 2 _
  · show P.left - 1 < m; omega_using [hl, ne]

theorem stop_ready {n pLen qLen m : Nat} {P : LoopPublic} {t : State} (h : Tested n pLen qLen P t)
    (he : isa.eval .e t = some false) :
    WP isa (.block []) t (LoopMid n pLen qLen m (.inr P.done)) := by
  obtain ⟨⟨⟨W, used, hm, hu, h16, _, outcome⟩, ⟨c0, c1, c2, cw⟩, c3, hf, hw, _, hp, hq⟩, hs⟩ := h
  have s3 : P.status ≠ 3 := by
    intro e; have := hs.symm.trans he; simp [e] at this
  obtain ⟨h19, hafter⟩ := outcome_public outcome hu
  refine WP.block_nil ⟨⟨W, hm, h19, fun h1 => ?_⟩, ⟨c0, c1, c2, cw⟩, c3, hf, hw, ?_, hp, hq⟩
  · change W 16 = BitVec.ofNat 64 P.after
    rw [h16, hafter (by change P.status = 1 at h1; rw [h1]; decide)]
  · rcases P.status_cases with e | e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact absurd e s3

theorem doneAt_keep {n pLen qLen : Nat} {D : DonePublic} {s t : State} (h : DoneAt n pLen qLen D s)
    (hm : t.mem = s.mem) (hk : Keep [.rax] s t) : DoneAt n pLen qLen D t := by
  obtain ⟨⟨W, hW, rest⟩, ⟨c0, c1, c2, cw⟩, c3, hf, hw, more⟩ := h
  refine ⟨⟨W, hW.congr hm hk, rest⟩, ⟨?_, ?_, ?_, hk.2.2 ▸ cw⟩, ?_, hf.congr (hk.gpr (by decide)) hk.2.2,
    hk.2.2.trans hw, more⟩
  · rw [Refill.ctlWord_eq_of_mem hm]; exact c0
  · rw [Refill.ctlWord_eq_of_mem hm]; exact c1
  · rw [Refill.ctlWord_eq_of_mem hm]; exact c2
  · rw [Refill.ctlWord_eq_of_mem hm]; exact c3

theorem final_ready {n pLen qLen m : Nat} (x : LoopPublic ⊕ DonePublic) {t : State}
    (h : LoopMid n pLen qLen m x t) :
    WP isa (.block Impl.Dsa.X86_64.Generation.tapeStatus) t (LoopPost n pLen qLen m x) := by
  cases x with
  | inl P =>
    obtain ⟨hl, ⟨W, hm, h19⟩, hlt⟩ := h
    refine WP.mono (Refill.statusTest_ok hm) fun u ⟨z, _, mu, ku⟩ => ?_
    exact ⟨by rw [z, h19]; rfl, loopBefore_keep hl mu (ku.mono (by decide)), hlt⟩
  | inr D =>
    obtain ⟨⟨W, hm, h19, _⟩, _, _, _, _, hs, _⟩ := id h
    refine WP.mono (Refill.statusTest_ok hm) fun u ⟨z, _, mu, ku⟩ => ?_
    refine ⟨by rw [z, h19]; rcases hs with e | e | e <;> rw [e] <;> rfl, doneAt_keep h mu ku⟩

/-! ## The step -/

theorem pins_of {α : Type} {Φ : α → State → Prop} (F : α → Addr) (h : ∀ a s, Φ a s → s.gpr .rsp = F a) :
    Pins Φ [.rsp] := by
  intro a s t hs ht r hr
  obtain rfl := List.mem_singleton.mp hr
  exact (h a s hs).trans (h a t ht).symm

theorem loopMid_rsp {n pLen qLen m : Nat} : ∀ (x : LoopPublic ⊕ DonePublic) (s : State),
    LoopMid n pLen qLen m x s → s.gpr .rsp = (match x with | .inl P => P.ctx.geo.F | .inr D => D.ctx.geo.F)
  | .inl _, _, h => loopBefore_rsp h.1
  | .inr _, _, h => h.2.2.2.1.rsp

theorem iteration_ct_of {n pLen qLen : Nat} (m : Nat) {attempt : Prog isa}
    (hct : RelCT isa (Two (SeedAttemptBefore n pLen qLen)) attempt (fun _ _ => True))
    (hwp : ∀ P t, Seeded n pLen qLen P t → WP isa attempt t (Attempted n pLen qLen P))
    (troom : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .rcx (.mem (sp 120)), .alu .sub .rcx (.reg .rax),
        .alu .cmp .rcx (.imm (BitVec.ofNat 32 qLen))]) hc).isSome = true)
    (tseed : ∃ hc, (taint.check (Taint.ofRegs [.rsp])
        (.block (Impl.Dsa.X86_64.Generation.Refill.seedStart qLen)) hc).isSome = true) :
    RelCT isa (Two fun P s => RefillLoopBefore n pLen qLen P s ∧ P.left = m)
      (Impl.Dsa.X86_64.Generation.Refill.iteration attempt qLen) (Two (LoopPost n pLen qLen m)) := by
  unfold Impl.Dsa.X86_64.Generation.Refill.iteration
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine RelCT.seq (two_piece (Ψ := fun P s => Started n pLen qLen P s ∧ P.left = m) [.rsp]
    (pins_of (fun P => P.ctx.geo.F) fun _ _ h => loopBefore_rsp h.1) (by taint_decide)
    fun P s h => WP.mono (head_ready h.1) fun _ ht => ⟨ht, h.2⟩) ?_
  refine RelCT.seq (R := Two (LoopMid n pLen qLen m)) ?_ (two_piece [.rsp]
    (pins_of _ fun x s h => loopMid_rsp x s h) (by taint_decide) fun x s h => final_ready x h)
  refine two_ite (fun P s t hs ht => hs.1.2.trans ht.1.2.symm) ?_ ?_
  · exact (two_piece (Ψ := fun P s => LoopMid n pLen qLen m (.inr (P.stop (BitVec.ofNat 64 2))) s) [.rsp]
      (pins_of (fun P => P.ctx.geo.F) fun _ _ h => loopBefore_rsp h.1.1.1.1) (by taint_decide)
      fun P s h => stopped_ready h.1.1.1 2 (Or.inr rfl)).mono (fun _ _ h => h) fun _ _ h => two_image _ h
  refine RelCT.seq (two_piece (Ψ := fun P s => Roomed n pLen qLen P s ∧ P.left = m) [.rsp]
    (pins_of (fun P => P.ctx.geo.F) fun _ _ h => loopBefore_rsp h.1.1.1.1) troom.choose_spec
    fun P s h => WP.mono (room_ready h.1.1 h.2) fun _ ht => ⟨ht, h.1.2⟩) ?_
  refine two_ite (fun P s t hs ht => hs.1.2.2.trans ht.1.2.2.symm) ?_ ?_
  · exact (two_piece (Ψ := fun P s => LoopMid n pLen qLen m (.inr (P.stop (BitVec.ofNat 64 0))) s) [.rsp]
      (pins_of (fun P => P.ctx.geo.F) fun _ _ h => loopBefore_rsp h.1.1.1.1) (by taint_decide)
      fun P s h => stopped_ready h.1.1.1 0 (Or.inl rfl)).mono (fun _ _ h => h) fun _ _ h => two_image _ h
  refine RelCT.seq (two_piece (Ψ := fun P s => Seeded n pLen qLen P s ∧ P.left = m) [.rsp]
    (pins_of (fun P => P.ctx.geo.F) fun _ _ h => loopBefore_rsp h.1.1.1.1) tseed.choose_spec
    fun P s h => WP.mono (seedStart_ready h.1.1 h.2) fun _ ht => ⟨ht, h.1.2⟩) ?_
  refine RelCT.seq (two_post (Ψ := fun P s => Attempted n pLen qLen P s ∧ P.left = m)
    (hct.mono (fun s t h => by
      obtain ⟨P, ⟨⟨⟨r, a⟩, _⟩, _⟩, ⟨⟨⟨_, b⟩, _⟩, _⟩⟩ := h
      exact ⟨P.seedPub r, a, b⟩) fun _ _ h => h)
    fun P s h => WP.mono (hwp P s h.1) fun _ ht => ⟨ht, h.2⟩) ?_
  refine RelCT.seq (two_piece (Ψ := fun P s => Tested n pLen qLen P s ∧ P.left = m) [.rsp]
    (pins_of (fun P => P.ctx.geo.F) fun _ _ h => h.1.2.2.2.1.rsp) (by taint_decide)
    fun P s h => WP.mono (test_ready h.1) fun _ ht => ⟨ht, h.2⟩) ?_
  refine two_ite (fun P s t hs ht => hs.1.2.trans ht.1.2.symm) ?_ ?_
  · exact (two_piece (Ψ := fun P s => LoopMid n pLen qLen m (.inl P.next) s) [.rsp]
      (pins_of (fun P => P.ctx.geo.F) fun _ _ h => h.1.1.1.2.2.2.1.rsp) (by taint_decide)
      fun P s h => reject_ready h.1.1 h.2 h.1.2).mono (fun _ _ h => h) fun _ _ h => two_image _ h
  · exact (two_post (Ψ := fun P s => LoopMid n pLen qLen m (.inr P.done) s)
      (two_taint [] (by intro _ _ _ _ _ r hr; simp at hr) (by taint_decide))
      fun P s h => stop_ready h.1.1 h.2).mono (fun _ _ h => h) fun _ _ h => two_image _ h

theorem loop_ct_of {n pLen qLen : Nat} {attempt : Prog isa}
    (hstep : ∀ m, RelCT isa (Two fun P s => RefillLoopBefore n pLen qLen P s ∧ P.left = m)
      (Impl.Dsa.X86_64.Generation.Refill.iteration attempt qLen) (Two (LoopPost n pLen qLen m))) :
    RelCT isa (Two (RefillLoopBefore n pLen qLen))
      (.loop (Impl.Dsa.X86_64.Generation.Refill.iteration attempt qLen) .e) (Two (DoneAt n pLen qLen)) := by
  have step : ∀ m, RelCT isa (Two fun P s => RefillLoopBefore n pLen qLen P s ∧ P.left = m)
      (Impl.Dsa.X86_64.Generation.Refill.iteration attempt qLen) fun s t =>
        isa.eval .e s = isa.eval .e t ∧ (isa.eval .e s = some false → Two (DoneAt n pLen qLen) s t) ∧
        (isa.eval .e s = some true → ∃ k < m, Two (fun P s => RefillLoopBefore n pLen qLen P s ∧ P.left = k) s t) := by
    intro m
    refine (hstep m).mono (fun _ _ h => h) ?_
    rintro s t ⟨x, hs, ht⟩
    cases x with
    | inl P =>
      refine ⟨hs.1.trans ht.1.symm, fun hf => absurd (hs.1.symm.trans hf) (by simp), fun _ => ?_⟩
      exact ⟨P.left, hs.2.2, P, ⟨hs.2.1, rfl⟩, ⟨ht.2.1, rfl⟩⟩
    | inr D =>
      exact ⟨hs.1.trans ht.1.symm, fun _ => ⟨D, hs.2, ht.2⟩, fun hf => absurd (hs.1.symm.trans hf) (by simp)⟩
  rintro s t a b s' t' ⟨P, hs, ht⟩ es et
  exact RelCT.loop (fun m => Two fun P s => RefillLoopBefore n pLen qLen P s ∧ P.left = m) step P.left
    s t a b s' t' ⟨P, ⟨hs, rfl⟩, ⟨ht, rfl⟩⟩ es et

theorem controller_ct (H : GenerationHashes) (M : Mont) (Sq : MontS) (T : PrimeTest)
    (pLen qLen : Nat) (sizes : GenerationSizes pLen qLen) :
    RelCT isa (Two (RefillLoopBefore 6 pLen qLen))
      (Impl.Dsa.X86_64.Generation.Refill.controller (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run pLen qLen)
      (Two (DoneAt 6 pLen qLen)) := by
  have width : qLen = 20 ∨ qLen = 32 := by
    rcases sizes with h | h | h <;> simp [h.2]
  have troom : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .rcx (.mem (sp 120)),
      .alu .sub .rcx (.reg .rax), .alu .cmp .rcx (.imm (BitVec.ofNat 32 qLen))]) hc).isSome = true := by
    rcases width with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  have tseed : ∃ hc, (taint.check (Taint.ofRegs [.rsp])
      (.block (Impl.Dsa.X86_64.Generation.Refill.seedStart qLen)) hc).isSome = true := by
    rcases width with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  unfold Impl.Dsa.X86_64.Generation.Refill.controller
  exact loop_ct_of fun m => iteration_ct_of m
    (refillAttempt_ct (checkName := checkName) H M Sq T 6 (Or.inr (Or.inr rfl)) pLen qLen sizes)
    (fun P t h => attempt_ready (checkName := checkName) H M Sq T h) troom tseed

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! ### `Dsa.X86_64.Generation.RefillCTEntry`, which only this module used -/

section

/-! # Timing of the refillable-tape search's entry

The controller's public state on entry (`loopPublic`) is a function of the
arguments, the stack pointer, `rand` and `state[0]`, which the contract
makes public; the entry's stores are at fixed offsets of the stack pointer
and at `state`, a public argument. -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp)
open VG.Impl.Bignum.X86_64 (at0)
open Refill (RefillABI inOut inUsed inRand inScr inState inArgs low refillBase refillGeometry refillContext randTape)

/-- The writable regions in the attempts' frame. -/
def refillWs (s : State) : List Region := Refill.ctlRegion (refillBase s) :: ⟨off (low s) 520, 48⟩ :: s.wr

def refillWr (s : State) : List Region := ⟨refillBase s, frameBytes⟩ :: refillWs s

section
variable {pBytes : Nat} {s₀ : State} (h : RefillABI pBytes s₀)
include h

theorem refillWr_eq : refillWr s₀ = [⟨refillBase s₀, frameBytes⟩, Refill.ctlRegion (refillBase s₀),
    ⟨off (low s₀) 520, 48⟩, inOut s₀, inUsed s₀, inScr s₀, inState s₀] := by
  simp only [refillWr, refillWs, h.wr]

theorem refillWr_pairwise : (refillWr s₀).Pairwise Region.Disjoint := by
  rw [refillWr_eq h]
  have fs : (⟨refillBase s₀, frameBytes⟩ : Region).Disjoint ⟨off (low s₀) 520, 48⟩ :=
    Offset.disjoint (low s₀) (d := 192) (n := 296) (e := 520) (k := 48) (by decide) (by decide) (by
      have := Refill.low_toNat h; have := (s₀.gpr .rsp).isLt; have : 568 ≤ (s₀.gpr .rsp).toNat := h.stackLower
      omega_using [])
  have cs : (Refill.ctlRegion (refillBase s₀)).Disjoint ⟨off (low s₀) 520, 48⟩ := by
    rw [Refill.ctlRegion_eq]
    exact Offset.disjoint (low s₀) (d := 488) (n := 32) (e := 520) (k := 48) (by decide) (by decide) (by
      have := Refill.low_toNat h; have := (s₀.gpr .rsp).isLt; have : 568 ≤ (s₀.gpr .rsp).toNat := h.stackLower
      omega_using [])
  have ab := fun {r : Region} (hr : r = inOut s₀ ∨ r = inUsed s₀ ∨ r = inRand s₀ ∨ r = inScr s₀ ∨ r = inState s₀ ∨
      r = inArgs s₀) => h.frame_disjoint hr
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    List.Pairwise.nil, and_true]
  refine ⟨⟨(Refill.ctl_frame _).symm, fs, (ab (by simp) _ (by simp)).symm, (ab (by simp) _ (by simp)).symm,
    (ab (by simp) _ (by simp)).symm, (ab (by simp) _ (by simp)).symm⟩,
    ⟨cs, (ab (by simp) _ (by simp)).symm, (ab (by simp) _ (by simp)).symm, (ab (by simp) _ (by simp)).symm,
      (ab (by simp) _ (by simp)).symm⟩,
    ⟨(ab (by simp) _ (by simp)).symm, (ab (by simp) _ (by simp)).symm, (ab (by simp) _ (by simp)).symm,
      (ab (by simp) _ (by simp)).symm⟩,
    ⟨h.outUsed, h.outScr, h.outState⟩, ⟨h.usedScr, h.usedState⟩, h.scrState, fun _ hh => hh.elim⟩

theorem refillWr_lengths : ∀ r ∈ refillWr s₀, r.len ≤ 2 ^ 64 := by
  rw [refillWr_eq h]
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · show 296 ≤ 2 ^ 64; decide
  · show 32 ≤ 2 ^ 64; decide
  · show 48 ≤ 2 ^ 64; decide
  · exact Nat.le_of_lt (s₀.gpr .rsi).isLt
  · show 8 ≤ 2 ^ 64; decide
  · show (stackArg s₀ 0).toNat * 8 ≤ 2 ^ 64
    have := h.scrBound; omega_using [this]
  · show 32 ≤ 2 ^ 64; decide

theorem refill_header : PrimeHeaderLayout (refillGeometry h).B (refillWr s₀) := by
  refine Or.inr ⟨_, _, _, _, _, _, (stackArg s₀ 0).toNat * 8, refillWr_eq h, ?_, refillWr_pairwise h,
    refillWr_lengths h⟩
  have hs := h.scratchSize
  have hw : pBytes = 128 ∨ pBytes = 256 ∨ pBytes = 384 := by
    have := h.lengths; unfold Spec.Dsa.generationLengthsValid at this; omega_using [this]
  have : 28928 ≤ VG.Impl.Dsa.Generation.Layout.usedBytes pBytes := by
    rcases hw with rfl | rfl | rfl <;> decide
  omega_using [hs, this]

theorem refill_ctlOK : CtlOK (refillContext h) (s₀.gpr .rdx) (stackArg s₀ 1) :=
  ⟨Refill.ctl_changed h, Refill.rand_ctl h, Refill.rand_ctl h, h.ctl_hash, Refill.refillBase_bound h⟩

theorem refill_endOK : EndOK (refillContext h) (s₀.gpr .rdx) (stackArg s₀ 1) (refillWr s₀) := by
  have hrl : (⟨(randTape h).ptr, (randTape h).bytes.length⟩ : Region) = inRand s₀ := by
    simp only [randTape, bytesAt_length, inRand]
  have st := Refill.written_regions h (inState s₀) (by simp)
  have us := Refill.written_regions h (inUsed s₀) (by simp)
  have below : below (refillContext h).geo.F 192 = ⟨off (low s₀) 0, 192⟩ := by
    change below (refillBase s₀) 192 = _
    rw [Refill.refillBase_below]; simp [off]
  have changed : ∀ {r : Region}, (r = inUsed s₀ ∨ r = inState s₀) → r.Disjoint ⟨s₀.gpr .r9,
      VG.Impl.Dsa.Generation.Layout.usedBytes pBytes⟩ → ∀ q ∈ (refillContext h).changed, r.Disjoint q := by
    intro r hr ha q hq
    simp only [GenerationContext.changed, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact ha
    · exact h.frame_disjoint (r := r) (by rcases hr with rfl | rfl <;> simp) _
        (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · rw [below]; exact h.stack_disjoint (d := 0) (n := 192) (by decide) (by rcases hr with rfl | rfl <;> simp) |>.symm
  refine
    { stIn := by rw [refillWr_eq h]; simp [inState]
      usIn := by rw [refillWr_eq h]; simp [inUsed]
      stBound := h.stateBound
      usBound := h.usedBound
      stChanged := changed (Or.inr rfl) st.2.2.2.2
      usChanged := changed (Or.inl rfl) us.2.2.2.2
      stRand := st.2.2.1.symm
      usRand := us.2.2.1.symm
      stSeeds := st.2.2.1.symm
      usSeeds := us.2.2.1.symm
      stHash := st.2.1
      usHash := us.2.1
      stCtl := st.2.2.2.1
      usCtl := us.2.2.2.1
      out := Refill.refillOutputPlan h
      outIn := ?_
      lenBound := ?_ }
  · have outLen : 2 * pBytes + Spec.Dsa.generationQLen pBytes = (s₀.gpr .rsi).toNat := by
      rw [h.outLength, h.width]
    change (⟨s₀.gpr .rdi, 2 * pBytes + Spec.Dsa.generationQLen pBytes⟩ : Region) ∈ refillWr s₀
    rw [outLen, refillWr_eq h]; simp [inOut]
  · change (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .rcx) (s₀.gpr .r8).toNat).length < 2 ^ 32
    rw [bytesAt_length]
    have := h.randLength
    have hw : Refill.refillPLen s₀ ≤ 384 := by
      have := h.valid; unfold Spec.Dsa.generationPLenValid at this; simp at this; omega_using [this]
    unfold Spec.Dsa.parameterEntropy at this
    omega_using [this, hw]

/-- The controller's public state on entry. -/
def loopPublic : LoopPublic where
  ctx := refillContext h
  hs := (refillContext h).hs
  start := 0
  left := (s₀.mem.readW (stackArg s₀ 1) 64).toNat
  c0 := s₀.gpr .rdx
  c1 := stackArg s₀ 1
  ws := refillWs s₀
  wr := refillWr s₀
  header := refill_header h
  startBound := Nat.zero_le _
  leftBound := h.seeds
  hsIn := by
    intro a ha
    simp [Region.Contains, refillContext, GenerationTape.slice] at ha
  ok := refill_ctlOK h
  ends := refill_endOK h

end

/-- A state the body starts from, with the controller's public state on entry `P`. -/
def RefillInit (pBytes : Nat) (P : LoopPublic) (u : State) : Prop :=
  ∃ (s₀ : State) (h : RefillABI pBytes s₀), Refill.RefillAllocated h u ∧ u.wr = refillWr s₀ ∧ loopPublic h = P

theorem entry_ready {pBytes qBytes : Nat} (hq : qBytes = Spec.Dsa.generationQLen pBytes) {P : LoopPublic}
    {u : State} (hi : RefillInit pBytes P u) :
    WP isa (.block (Impl.Dsa.X86_64.Generation.Refill.entryHeader pBytes qBytes ++
      Impl.Dsa.X86_64.Generation.entryDerived)) u (RefillLoopBefore 6 pBytes qBytes P) := by
  obtain ⟨s₀, h, a, hwr, rfl⟩ := hi
  refine WP.mono (Refill.entry_ok h a hq) fun v ⟨W, hm, h16, h10, c0, c1, c2, _, kV⟩ => ?_
  have wv : v.wr = refillWr s₀ := kV.2.2.trans hwr
  have hm' : GenerationMemory ((refillContext h).withHs (refillContext h).hs) W v := by
    rw [Refill.withHs_self]; exact hm
  refine ⟨⟨W, hm', by rw [h16]; rfl, h10⟩,
    ⟨c0, c1, ?_, kV.2.2 ▸ a.ctl⟩,
    ⟨(kV.gpr (by decide)).trans a.rsp, wv, ?_, refillWr_pairwise h,
      fun r hr => refillWr_lengths h r (List.mem_cons_of_mem _ hr)⟩, wv, rfl, hq.symm⟩
  · show Refill.ctlWord v.mem (refillBase s₀) 2 = BitVec.ofNat 64 (s₀.mem.readW (stackArg s₀ 1) 64).toNat
    rw [c2, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · show (refillWs s₀).length = 6
    simp only [refillWs, h.wr, List.length_cons, List.length_nil]

def EntryLoaded (P : LoopPublic) (t : State) : Prop :=
  t.gpr .rsp = P.ctx.geo.F ∧ t.gpr .rax = P.c1

theorem entryFirst_ready {pBytes qBytes : Nat} {P : LoopPublic} {u : State} (hi : RefillInit pBytes P u)
    (hp : pBytes < 2 ^ 31) (hq : qBytes < 2 ^ 31) :
    WP isa (.block (Refill.headerA pBytes qBytes ++ ([.mov .rax (.mem (sp (Impl.Dsa.X86_64.Generation.Refill.frameBytes + 32 + 48 + 16))),
      .store (Impl.Dsa.X86_64.Generation.Refill.ctl 1) .rax] : List Instr))) u (EntryLoaded P) := by
  obtain ⟨s₀, h, a, _, rfl⟩ := hi
  have hb := Refill.refillBase_bound h
  apply WP.block_append
  refine WP.mono (Refill.headerA_ok a.rsp a.frame a.ctl hb hp hq) fun t ⟨hm, kt⟩ => ?_
  have fA : Frame [⟨refillBase s₀, frameBytes⟩, Refill.ctlRegion (refillBase s₀)] u.mem t.mem := by
    rw [hm]; exact Refill.chainA_frame _ _ _ _ _
  have argsC : (inArgs s₀).Contains (off (refillBase s₀) 392) 8 := by
    rw [Refill.refillBase_args]
    exact Offset.contains (s₀.gpr .rsp) (e := 8) (d := 16) (by decide) (by decide) (by decide)
  have hall : Frame [(⟨off (low s₀) 520, 48⟩ : Region), ⟨refillBase s₀, frameBytes⟩,
      Refill.ctlRegion (refillBase s₀)] s₀.mem t.mem :=
    (a.mem.mono (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact List.mem_cons_self ..)).trans
      (fA.mono fun r hr => List.mem_cons_of_mem _ hr)
  have hav : t.mem.readW (off (refillBase s₀) 392) 64 = stackArg s₀ 1 := by
    rw [hall.readW argsC (h.frame_disjoint (r := inArgs s₀) (by simp)) (by decide), Refill.refillBase_args]; rfl
  have ha : InRegions (t.rd ++ t.wr) (off (refillBase s₀) 392) 8 :=
    ⟨inArgs s₀, List.mem_append_left _ (by rw [kt.2.1, a.rd, h.rd]; simp), argsC⟩
  have hsp : t.gpr .rsp = refillBase s₀ := (kt.gpr (by decide)).trans a.rsp
  have cs : Scr t (off (refillBase s₀) 296) 32 := Scr.of_mem (by rw [kt.2.2]; exact a.ctl) (by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [hb])
  have c1 : InRegions t.wr (off (refillBase s₀) 304) 8 := by simpa [off_off] using cs.st (d := 8) (by decide)
  refine WP.mono (WP.keep [.rax] (Q := fun v => v.gpr .rax = stackArg s₀ 1) ?_ rfl) fun v ⟨hv, kv⟩ =>
    ⟨(kv.gpr (by decide)).trans hsp, hv⟩
  xrun [Impl.Dsa.X86_64.Generation.Refill.ctl, Impl.Dsa.X86_64.Generation.Refill.frameBytes,
    ea_sp, hsp, ha, hav, c1]

theorem entry_ct (pBytes qBytes : Nat) (hp : pBytes = 128 ∨ pBytes = 256 ∨ pBytes = 384)
    (hq : qBytes = Spec.Dsa.generationQLen pBytes) :
    RelCT isa (Two (RefillInit pBytes))
      (.block (Impl.Dsa.X86_64.Generation.Refill.entryHeader pBytes qBytes ++ Impl.Dsa.X86_64.Generation.entryDerived))
      (Two (RefillLoopBefore 6 pBytes qBytes)) := by
  have t₁ : ∃ hc, (taint.check (Taint.ofRegs [.rsp])
      (.block (Refill.headerA pBytes qBytes ++ ([.mov .rax (.mem (sp (Impl.Dsa.X86_64.Generation.Refill.frameBytes + 32 + 48 + 16))),
      .store (Impl.Dsa.X86_64.Generation.Refill.ctl 1) .rax] : List Instr))) hc).isSome = true := by
    subst hq; rcases hp with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩
  have p31 : pBytes < 2 ^ 31 := by omega_using [hp]
  have q31 : qBytes < 2 ^ 31 := by subst hq; rcases hp with rfl | rfl | rfl <;> decide
  refine two_post ?_ fun P u hi => entry_ready hq hi
  have e : Impl.Dsa.X86_64.Generation.Refill.entryHeader pBytes qBytes ++ Impl.Dsa.X86_64.Generation.entryDerived =
      (Refill.headerA pBytes qBytes ++ ([.mov .rax (.mem (sp (Impl.Dsa.X86_64.Generation.Refill.frameBytes + 32 + 48 + 16))),
      .store (Impl.Dsa.X86_64.Generation.Refill.ctl 1) .rax] : List Instr)) ++
        (([.mov .rax (.mem (at0 .rax)), .store (Impl.Dsa.X86_64.Generation.Refill.ctl 2) .rax] : List Instr) ++ Impl.Dsa.X86_64.Generation.entryDerived) := by
    simp only [Refill.entryHeader_eq, Refill.headerB, List.append_assoc, List.cons_append, List.nil_append]
  rw [e]
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := EntryLoaded) [.rsp] ?_ t₁.choose_spec
    fun P u hi => entryFirst_ready hi p31 q31) (two_taint [.rsp, .rax] ?_ (by taint_decide)))
  · intro P s t ⟨s₀, h, a, _, e₀⟩ ⟨t₀, h', a', _, e₁⟩ r hr
    obtain rfl := List.mem_singleton.mp hr
    rw [a.rsp, a'.rsp]
    have := congrArg (fun P : LoopPublic => P.ctx.geo.F) (e₀.trans e₁.symm)
    exact this
  · intro P s t hs ht r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hs.1.trans ht.1.symm
    · exact hs.2.trans ht.2.symm

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! ### `Dsa.X86_64.Generation.EntryInnerCT`, which only this module used -/

section

/-! # The inner ABI frame preserves the proved generator trace and stack pointer -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MillerRabin.X86_64 VG.Impl.Dsa.X86_64.Generation

variable {checkName : String}

theorem generation_alloc {s : State} {bytes : Nat}
    (hb : 0 < bytes ∧ bytes < 4096 ∧ bytes % 8 = 0) (hl : bytes ≤ (s.gpr .rsp).toNat) :
    isa.push (.alloc bytes) s = some (allocState bytes s) := by
  simp only [isa, push, allocState]
  exact ite_eq_left ⟨hb.1, hb.2.1, hb.2.2, hl⟩

theorem generation_free_rsp {s u v : State} {bytes : Nat}
    (h : isa.pop (.free bytes) (allocState bytes s) u = some v) : v.gpr .rsp = s.gpr .rsp := by
  simp only [isa, pop] at h
  split at h
  · rename_i hc
    obtain rfl := Option.some.inj h
    exact freeState_rsp hc.2.2.2.1
  · cases h

end VG.Proof.Dsa.X86_64.Generation

end

end


-- separate module: its proofs build in parallel with the correctness ones, `RefillBackend`

/-! # The refillable-tape search for one width is constant time

`refill_ct`: two runs from states whose public data agree (the arguments in
registers and on the stack, the stack pointer, `state`'s four words and the
whole tape `rand`) leak the same trace. The controller's public state on
entry is a function of that data (`loopPublic_eq`), and the entry, the
controller (`controller_ct`) and the end (`finish_ct`) keep their states
related. -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Proof.MillerRabin.X86_64
open Refill (RefillABI inOut inUsed inRand inScr inState inArgs low refillBase refillGeometry refillContext randTape)

variable {checkName : String}

/-! ## Public data -/

/-- What two runs' public data agree on. -/
structure RefillAgree (s t : State) : Prop where
  rsp : s.gpr .rsp = t.gpr .rsp
  regs : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9], s.gpr r = t.gpr r
  arg0 : stackArg s 0 = stackArg t 0
  arg1 : stackArg s 1 = stackArg t 1
  rand : Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat = Spec.Rsa.bytesAt t.mem (t.gpr .rcx) (t.gpr .r8).toNat
  seeds : s.mem.readW (stackArg s 1) 64 = t.mem.readW (stackArg t 1) 64

theorem refill_wordsAt_four (m : Mem) (p : Addr) : (Spec.Rsa.wordsAt m p 4).map (·.toNat) =
    [(m.readW (p + BitVec.ofNat 64 0) 64).toNat, (m.readW (p + 8) 64).toNat, (m.readW (p + 16) 64).toNat,
      (m.readW (p + 24) 64).toNat] := rfl

theorem refill_agree {pBytes S : Nat} {s t : State} (h : (Refill.contract pBytes abi S).pub s t) :
    RefillAgree s t := by
  sig_pub [Refill.contract, Spec.Dsa.parameterSearchSig, abi, argRegs, Refill.stackArgs_two] at h
  obtain ⟨hsp, hl, r1, r2, r3, r4, r5, r6, a0, a1⟩ := h
  rw [refill_wordsAt_four, refill_wordsAt_four] at hl
  -- the lengths of the four words, as numerals: `rfl` would first compare the words
  have hp := List.append_inj hl (Eq.refl 4)
  simp only [List.cons.injEq] at hp
  refine ⟨hsp, ?_, by simpa using a0, by simpa using a1, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption
  · exact (List.map_inj_right fun a b e => BitVec.eq_of_toNat_eq e).mp hp.2
  · have := BitVec.eq_of_toNat_eq hp.1.1
    simpa only [BitVec.add_zero, BitVec.ofNat_eq_ofNat] using this

theorem GenerationTape.heq_of {p q : GenerationGeometry} {a : GenerationTape p} {b : GenerationTape q}
    (hg : p = q) (hp : a.ptr = b.ptr) (hb : a.bytes = b.bytes) : HEq a b := by
  cases hg; cases a; cases b; cases hp; cases hb; rfl

theorem GenerationContext.ext' {a b : GenerationContext} (hg : a.geo = b.geo) (hs : HEq a.seeds b.seeds)
    (hh : HEq a.hs b.hs) (hr : HEq a.rand b.rand) (hw : a.saved = b.saved) : a = b := by
  cases a; cases b; cases hg; cases hs; cases hh; cases hr; cases hw; rfl

theorem LoopPublic.ext' {P Q : LoopPublic} (hc : P.ctx = Q.ctx) (hh : HEq P.hs Q.hs) (h1 : P.start = Q.start)
    (h2 : P.left = Q.left) (h3 : P.c0 = Q.c0) (h4 : P.c1 = Q.c1) (h5 : P.ws = Q.ws) (h6 : P.wr = Q.wr) :
    P = Q := by
  cases P; cases Q
  dsimp only at hc hh h1 h2 h3 h4 h5 h6
  subst hc; cases hh; subst h1; subst h2; subst h3; subst h4; subst h5; subst h6; rfl

theorem RefillAgree.wr {pBytes : Nat} {s t : State} (hs : RefillABI pBytes s) (ht : RefillABI pBytes t)
    (a : RefillAgree s t) : s.wr = t.wr := by
  rw [hs.wr, ht.wr]
  simp only [inOut, inUsed, inScr, inState, a.regs .rdi (by simp), a.regs .rsi (by simp), a.regs .rdx (by simp),
    a.regs .r9 (by simp), a.arg0, a.arg1]

theorem refillContext_eq {pBytes : Nat} {s t : State} (hs : RefillABI pBytes s) (ht : RefillABI pBytes t)
    (a : RefillAgree s t) : refillContext hs = refillContext ht := by
  have base : refillBase s = refillBase t := by simp only [refillBase, low, a.rsp]
  have hg : refillGeometry hs = refillGeometry ht := by
    have ext : ∀ {x y : GenerationGeometry}, x.B = y.B → x.F = y.F → x.pLen = y.pLen → x.qLen = y.qLen → x = y := by
      intro x y hB hF hp hq
      cases x; cases y
      dsimp only at hB hF hp hq
      subst hB; subst hF; subst hp; subst hq; rfl
    exact ext (a.regs .r9 (by simp)) base rfl rfl
  have tape : HEq (randTape hs) (randTape ht) :=
    GenerationTape.heq_of hg (a.regs .rcx (by simp)) a.rand
  refine GenerationContext.ext' hg tape ?_ tape ?_
  · refine GenerationTape.heq_of hg ?_ ?_
    · show off (s.gpr .rcx) 0 = off (t.gpr .rcx) 0
      rw [a.regs .rcx (by simp)]
    · show ((randTape hs).bytes.drop 0).take 0 = ((randTape ht).bytes.drop 0).take 0
      simp only [List.take_zero]
  · funext k
    show Refill.refillWords pBytes s k = Refill.refillWords pBytes t k
    unfold Refill.refillWords
    split <;> simp only [a.regs .rdi (by simp), a.regs .rsi (by simp), a.regs .rcx (by simp),
      a.regs .r8 (by simp), a.regs .r9 (by simp)]

theorem loopPublic_eq {pBytes : Nat} {s t : State} (hs : RefillABI pBytes s) (ht : RefillABI pBytes t)
    (a : RefillAgree s t) : loopPublic hs = loopPublic ht := by
  have e := refillContext_eq hs ht a
  refine LoopPublic.ext' e (by change HEq (refillContext hs).hs (refillContext ht).hs; rw [e]) rfl ?_
    (a.regs .rdx (by simp)) a.arg1 ?_ ?_
  · change (s.mem.readW (stackArg s 1) 64).toNat = (t.mem.readW (stackArg t 1) 64).toNat
    rw [a.seeds]
  · change refillWs s = refillWs t
    simp only [refillWs, refillBase, low, a.rsp, a.wr hs ht]
  · change refillWr s = refillWr t
    simp only [refillWr, refillWs, refillBase, low, a.rsp, a.wr hs ht]

/-! ## The body -/

theorem body_ct (H : GenerationHashes) (M : Mont) (Sq : MontS) (T : PrimeTest) (pBytes qBytes : Nat)
    (hp : pBytes = 128 ∨ pBytes = 256 ∨ pBytes = 384) (hq : qBytes = Spec.Dsa.generationQLen pBytes) :
    RelCT isa (Two (RefillInit pBytes))
      (Impl.Dsa.X86_64.Generation.Refill.body (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run pBytes qBytes)
      (fun _ _ => True) := by
  have sizes : GenerationSizes pBytes qBytes := by
    subst hq; rcases hp with rfl | rfl | rfl
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  unfold Impl.Dsa.X86_64.Generation.Refill.body
  simp only [VG.Impl.Bignum.X86_64.seqs]
  exact RelCT.seq (entry_ct pBytes qBytes hp hq)
    (RelCT.seq (controller_ct (checkName := checkName) H M Sq T pBytes qBytes sizes) (finish_ct pBytes qBytes hp))

/-- The body's starting state, after the frames' allocation and the saved registers. -/
theorem refill_init {pBytes : Nat} {s₀ u : State} (h : RefillABI pBytes s₀)
    (hg : u.gpr = (allocState 48 s₀).gpr) (hr : u.rd = s₀.rd) (hw : u.wr = (allocState 48 s₀).wr)
    (hf : Frame [⟨(allocState 48 s₀).gpr .rsp, 48⟩] s₀.mem u.mem) :
    RefillInit pBytes (loopPublic h) (allocState 296 (allocState 32 u)) := by
  have lower : 568 ≤ (s₀.gpr .rsp).toNat := h.stackLower
  have ursp : u.gpr .rsp = s₀.gpr .rsp - BitVec.ofNat 64 48 := by rw [hg]; rfl
  have e : (allocState 296 (allocState 32 u)).gpr .rsp = refillBase s₀ := by
    change u.gpr .rsp - BitVec.ofNat 64 32 - BitVec.ofNat 64 296 = _
    rw [ursp, Refill.rsp_alloc]; rfl
  have ectl : u.gpr .rsp - BitVec.ofNat 64 32 = off (refillBase s₀) 296 := by
    rw [ursp, Refill.ctl_alloc]; rfl
  have wr : (allocState 296 (allocState 32 u)).wr = refillWr s₀ := by
    change ⟨(allocState 296 (allocState 32 u)).gpr .rsp, 296⟩ :: ⟨u.gpr .rsp - BitVec.ofNat 64 32, 32⟩ :: u.wr = _
    rw [e, ectl, hw]
    change _ :: _ :: ⟨s₀.gpr .rsp - BitVec.ofNat 64 48, 48⟩ :: s₀.wr = _
    rw [Refill.saved_alloc]; rfl
  refine ⟨s₀, h, ?_, wr, rfl⟩
  exact
    { rsp := e
      frame := by rw [wr]; exact List.mem_cons_self ..
      ctl := by rw [wr]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
      wr := fun r hr => by rw [wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
      rd := hr
      regs := fun r hne => by simp only [allocState, State.setReg, hne, ↓reduceIte, hg]
      mem := by
        change Frame _ s₀.mem u.mem
        rw [show off (low s₀) 520 = (allocState 48 s₀).gpr .rsp from (Refill.saved_alloc _).symm]; exact hf }

theorem refill_post_of_exec {c : Prog isa} {s t : State} {trace : List Leak} {Q : State → Prop}
    (h : WP isa c s Q) (he : Exec isa c s trace t) : Q t := by
  obtain ⟨_, u, hu, hq⟩ := h
  obtain ⟨_, heq⟩ := Exec.det he hu
  rw [heq]
  exact hq

/-- The two inner frames and the body. -/
theorem refillInner_ct (H : GenerationHashes) (M : Mont) (Sq : MontS) (T : PrimeTest) (pBytes qBytes : Nat)
    (hp : pBytes = 128 ∨ pBytes = 256 ∨ pBytes = 384) (hq : qBytes = Spec.Dsa.generationQLen pBytes)
    {s t a b u v : State} (hs : RefillABI pBytes s) (ht : RefillABI pBytes t) (agree : RefillAgree s t)
    (ga : a.gpr = (allocState 48 s).gpr) (ra : a.rd = s.rd) (wa : a.wr = (allocState 48 s).wr)
    (fa : Frame [⟨(allocState 48 s).gpr .rsp, 48⟩] s.mem a.mem)
    (gb : b.gpr = (allocState 48 t).gpr) (rb : b.rd = t.rd) (wb : b.wr = (allocState 48 t).wr)
    (fb : Frame [⟨(allocState 48 t).gpr .rsp, 48⟩] t.mem b.mem) {tsa tsb : List Leak}
    (ea : Exec isa (.frame (.alloc 32) (.frame (.alloc Impl.Dsa.X86_64.Generation.Refill.frameBytes)
        (Impl.Dsa.X86_64.Generation.Refill.body (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run pBytes qBytes)
        (.free Impl.Dsa.X86_64.Generation.Refill.frameBytes)) (.free 32)) a tsa u)
    (eb : Exec isa (.frame (.alloc 32) (.frame (.alloc Impl.Dsa.X86_64.Generation.Refill.frameBytes)
        (Impl.Dsa.X86_64.Generation.Refill.body (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run pBytes qBytes)
        (.free Impl.Dsa.X86_64.Generation.Refill.frameBytes)) (.free 32)) b tsb v) :
    tsa = tsb ∧ u.gpr .rsp = v.gpr .rsp := by
  have la : 568 ≤ (s.gpr .rsp).toNat := hs.stackLower
  have lb : 568 ≤ (t.gpr .rsp).toNat := ht.stackLower
  have arsp : (a.gpr .rsp).toNat = (s.gpr .rsp).toNat - 48 := by
    rw [ga]; exact Refill.toNat_sub_k (by omega_using [la])
  have brsp : (b.gpr .rsp).toNat = (t.gpr .rsp).toNat - 48 := by
    rw [gb]; exact Refill.toNat_sub_k (by omega_using [lb])
  cases ea with
  | frame pa ia qa =>
    cases eb with
    | frame pb ib qb =>
      rw [generation_alloc (by decide) (by omega_using [la, arsp]), Option.some.injEq] at pa
      rw [generation_alloc (by decide) (by omega_using [lb, brsp]), Option.some.injEq] at pb
      subst pa; subst pb
      cases ia with
      | frame pa' ba qa' =>
        cases ib with
        | frame pb' bb qb' =>
          rw [generation_alloc (by decide) (by
            change 296 ≤ (a.gpr .rsp - BitVec.ofNat 64 32).toNat
            rw [Refill.toNat_sub_k (by omega_using [la, arsp])]; omega_using [la, arsp]), Option.some.injEq] at pa'
          rw [generation_alloc (by decide) (by
            change 296 ≤ (b.gpr .rsp - BitVec.ofNat 64 32).toNat
            rw [Refill.toNat_sub_k (by omega_using [lb, brsp])]; omega_using [lb, brsp]), Option.some.injEq] at pb'
          subst pa'; subst pb'
          have ia := refill_init hs ga ra wa fa
          have ib := refill_init ht gb rb wb fb
          rw [← loopPublic_eq hs ht agree] at ib
          have traces := (body_ct (checkName := checkName) H M Sq T pBytes qBytes hp hq _ _ _ _ _ _
            ⟨loopPublic hs, ia, ib⟩ ba bb).1
          refine ⟨by simpa only [isa, addrs, List.map_nil, List.nil_append, List.append_nil] using traces, ?_⟩
          rw [generation_free_rsp qa, generation_free_rsp qb, ga, gb]
          change s.gpr .rsp - BitVec.ofNat 64 48 = t.gpr .rsp - BitVec.ofNat 64 48
          rw [agree.rsp]

/-! ## The function -/

theorem refill_ct (H : GenerationHashes) (M : Mont) (Sq : MontS) (T : PrimeTest) (pBytes qBytes : Nat)
    (hp : pBytes = 128 ∨ pBytes = 256 ∨ pBytes = 384) (hq : qBytes = Spec.Dsa.generationQLen pBytes) :
    ConstantTime isa (Refill.contract pBytes abi Refill.refillStack).pre
      (Refill.contract pBytes abi Refill.refillStack).pub
      (Impl.Dsa.X86_64.Generation.Refill.code (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run
        pBytes qBytes) := by
  intro s t tsa tsb u v hs ht hpub ea eb
  have hsa := Refill.refillABI_of hs
  have hta := Refill.refillABI_of ht
  have agree := refill_agree hpub
  have la : 568 ≤ (s.gpr .rsp).toNat := hsa.stackLower
  have lb : 568 ≤ (t.gpr .rsp).toNat := hta.stackLower
  unfold Impl.Dsa.X86_64.Generation.Refill.code at ea eb
  cases ea with
  | frame pa ba _ =>
    cases eb with
    | frame pb bb _ =>
      rw [generation_alloc (by decide) (by omega_using [la] : 48 ≤ (s.gpr .rsp).toNat), Option.some.injEq] at pa
      rw [generation_alloc (by decide) (by omega_using [lb] : 48 ≤ (t.gpr .rsp).toNat), Option.some.injEq] at pb
      subst pa; subst pb
      cases ba with | seq sa restA => cases restA with | seq ia ra =>
      cases bb with | seq sb restB => cases restB with | seq ib rb =>
      have saveTrace := (entrySave_ct _ _ _ _ _ _ (by
        change s.gpr .rsp - BitVec.ofNat 64 48 = t.gpr .rsp - BitVec.ofNat 64 48
        rw [agree.rsp]) sa sb).1
      obtain ⟨ga, rda, wra, _, fa⟩ :=
        refill_post_of_exec (entrySave_ok (s := allocState 48 s) (List.mem_cons_self ..)) sa
      obtain ⟨gb, rdb, wrb, _, fb⟩ :=
        refill_post_of_exec (entrySave_ok (s := allocState 48 t) (List.mem_cons_self ..)) sb
      have inner := refillInner_ct (checkName := checkName) H M Sq T pBytes qBytes hp hq hsa hta agree
        ga rda wra fa gb rdb wrb fb ia ib
      have restoreTrace := (entryRestore_ct _ _ _ _ _ _ inner.2 ra rb).1
      simp only [addrs, List.map_nil, List.nil_append, List.append_nil]
      rw [saveTrace, inner.1, restoreTrace]

end VG.Proof.Dsa.X86_64.Generation
