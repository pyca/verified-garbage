module

public import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.Correct
public import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.Geometry
import VerifiedGarbage.Proof.Ffdh.VettedTableFacts
import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import Batteries.Logic
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ffdh.Contract
meta import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Impl.Ffdh.X86_64.VettedValidation
import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.ScanTiming
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.Table
public import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.Restore

/-! ### `Ffdh.X86_64.VettedValidation.Timing`, which only this module used -/

section

/-! ### `Ffdh.X86_64.VettedValidation.PrefixTiming`, which only this module used -/

section

/-! ### `Ffdh.X86_64.VettedValidation.PublicState`, which this module and modules that import it used -/

section

/-! Shared public anchors for two imports with unrelated scratch contents. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86_64.VettedValidation
open VG VG.X86_64
open VG.Impl.Ffdh.X86_64.VettedValidation

def publicRegs : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]

structure Start (a s : State) : Prop where
  pre : contract.pre s
  regs : ∀ r ∈ publicRegs, s.gpr r = a.gpr r
  domain : CheckDomain.cdDom s = CheckDomain.cdDom a
  symbol : s.syms tableSym = a.syms tableSym
  mx : s.mxcsr = a.mxcsr

private theorem singleton_sym {name : String} {words : List (BitVec 64)} {s t : State}
    (h : ∀ c ∈ [(name, words)], s.syms c.1 = t.syms c.1) :
    s.syms name = t.syms name := h (name, words) List.mem_cons_self

theorem start_of_pub {a s : State} (hs : contract.pre s)
    (hp : contract.pub a s) : Start a s := by
  have relation : (Spec.Ffdh.checkDomainContract abi 8).pub a s ∧
      ∀ c ∈ tableConsts, a.syms c.1 = s.syms c.1 := pub_consts.mp hp
  have symbols := singleton_sym (name := tableSym) (words := VG.Impl.Ffdh.VettedGroups.tableWords) relation.2
  have pubBase := relation.1
  sig_pub_keep [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argRegs, List.append_eq] at pubBase
  obtain ⟨rsp, mx, bytes, rdi, rsi, rdx, rcx, r8⟩ := pubBase
  refine ⟨hs, ?_, ?_, symbols.symm, mx.symm⟩
  · intro r hr
    simp only [publicRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact rdi.symm
    · exact rsi.symm
    · exact rdx.symm
    · exact rcx.symm
    · exact r8.symm
    · exact rsp.symm
  · have byteEq := congrArg (List.map (BitVec.ofNat 8)) bytes
    simp only [List.map_map, Function.comp_def, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, List.map_id'] at byteEq
    exact byteEq.symm

def After (a t : State) : Prop := ∃ s, Start a s ∧ Result s t

def Ready (a t : State) : Prop := ∃ s, Start a s ∧ Restored s t

theorem Ready.pre {a t : State} (h : Ready a t) :
    (Spec.Ffdh.checkDomainContract abi 8).pre (plain t) := by
  obtain ⟨s, start, restored⟩ := h
  exact restored.pre start.pre

theorem Ready.public {a s t : State} (hs : Ready a s) (ht : Ready a t) :
    (Spec.Ffdh.checkDomainContract abi 8).pub s t := by
  obtain ⟨s0, startS, restoredS⟩ := hs
  obtain ⟨t0, startT, restoredT⟩ := ht
  have domainS := (restoredS.domain (geometry startS.pre)).trans startS.domain
  have domainT := (restoredT.domain (geometry startT.pre)).trans startT.domain
  have spS := (restoredS.keep.gpr (r := .rsp) (by decide)).trans (startS.regs .rsp (by decide))
  have spT := (restoredT.keep.gpr (r := .rsp) (by decide)).trans (startT.regs .rsp (by decide))
  sig_pub [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argRegs, List.append_eq]
  refine ⟨spS.trans spT.symm, (restoredS.mxcsr.trans startS.mx).trans (restoredT.mxcsr.trans startT.mx).symm,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (CheckDomain.cdDom s).map (·.toNat) = (CheckDomain.cdDom t).map (·.toNat)
    rw [domainS, domainT]
  · exact (restoredS.args.1.trans (startS.regs .rdi (by decide))).trans
      (restoredT.args.1.trans (startT.regs .rdi (by decide))).symm
  · exact (restoredS.args.2.1.trans (startS.regs .rsi (by decide))).trans
      (restoredT.args.2.1.trans (startT.regs .rsi (by decide))).symm
  · exact (restoredS.args.2.2.1.trans (startS.regs .rdx (by decide))).trans
      (restoredT.args.2.2.1.trans (startT.regs .rdx (by decide))).symm
  · exact (restoredS.args.2.2.2.1.trans (startS.regs .rcx (by decide))).trans
      (restoredT.args.2.2.2.1.trans (startT.regs .rcx (by decide))).symm
  · exact (restoredS.args.2.2.2.2.trans (startS.regs .r8 (by decide))).trans
      (restoredT.args.2.2.2.2.trans (startT.regs .r8 (by decide))).symm

end VG.Proof.Ffdh.X86_64.VettedValidation

end

end

/-! Saving arguments and scanning the table depends only on the original public domain. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86_64.VettedValidation
open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.VettedValidation
open VG.Impl.Ffdh.VettedGroups

theorem recognize_ct (a : State) :
    RelCT isa (fun s t => Start a s ∧ Start a t) recognizeCode (fun _ _ => True) := by
  let Q := fun s : State => Context (a.gpr .rcx) (a.gpr .rdi) (a.gpr .rdx).toNat
    (CheckDomain.cdDom a) s ∧ s.syms tableSym = a.syms tableSym ∧ TableAt (a.syms tableSym) groups s
  have entryCT : RelCT isa (fun s t => Start a s ∧ Start a t) (.block entry) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.rcx]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact (h.1.regs .rcx (by decide)).trans (h.2.regs .rcx (by decide)).symm
  have entryWP (s : State) (h : Start a s) : WP isa (.block entry) s Q := by
    have g := geometry h.pre
    refine WP.mono_syms (entry_ok g) ?_
    rintro t ⟨base, mem, rest⟩ sym
    have context := entry_context g base mem rest
    rw [h.regs .rcx (by decide), h.regs .rdi (by decide), h.regs .rdx (by decide), h.domain] at context
    have frame : Frame [⟨s.gpr .rcx, (s.gpr .r8).toNat * 8⟩] s.mem t.mem := by
      rw [mem]; exact entryMem_frame g
    have table := consts_table_after g.consts frame rest g.writable
    rw [h.symbol] at table
    exact ⟨context, (congrFun sym tableSym).trans h.symbol, table⟩
  have fit : 0 + (groups.flatMap Group.bytes).length ≤ 17744 := by
    simpa only [Nat.zero_add, tableBytes] using
      (Nat.le_of_eq VG.Proof.Ffdh.VettedTableFacts.tableBytes_length)
  have valid : ∀ g ∈ groups, g.len < 2 ^ 31 := by
    intro g hg
    simp only [groups, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have scanning := (scan_ct (base := a.gpr .rcx) (src := a.gpr .rdi) (table := a.syms tableSym)
    (k := (a.gpr .rdx).toNat) (dom := CheckDomain.cdDom a) groups 0 fit valid).mono
    (P' := fun s t => Q s ∧ Q t)
    (fun _ _ h => by simpa only [BitVec.add_zero] using h) (fun _ _ h => h)
  unfold recognizeCode
  exact ((entryCT.wp (fun s t h => ⟨entryWP s h.1, entryWP t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2⟩)).seq scanning

end VG.Proof.Ffdh.X86_64.VettedValidation

end

end

/-! The fast path and the selected general fallback preserve the API's timing policy. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86_64.VettedValidation
open VG VG.X86_64 VG.Proof.MlKem.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Impl.Ffdh.X86_64.VettedValidation

theorem Start.recognized_eq {a s : State} (h : Start a s) : recognized s = recognized a := by
  unfold recognized
  rw [h.regs .rdx (by decide), h.domain]

theorem After.base {a s : State} (h : After a s) : s.gpr .r9 = a.gpr .rcx := by
  obtain ⟨u, start, result⟩ := h
  exact result.context.baseReg.trans (start.regs .rcx (by decide))

theorem anchored_ct (v : RoundImpl) (e : ExpImpl) (a : State) :
    RelCT isa (fun s t => Start a s ∧ Start a t) (emittedCode v e) (fun _ _ => True) := by
  let R := fun s : State => After a s ∧ s.zf = some (recognized a == 0)
  have scanWP (s : State) (h : Start a s) : WP isa recognizeCode s (After a) :=
    WP.mono (recognize_ok (geometry h.pre)) (fun t result => ⟨s, h, result⟩)
  have scanStage : RelCT isa (fun s t => Start a s ∧ Start a t) recognizeCode
      (fun s t => After a s ∧ After a t) := ((recognize_ct a).wp (fun s t h => ⟨scanWP s h.1, scanWP t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2⟩)
  have testCT : RelCT isa (fun s t => After a s ∧ After a t)
      (.block [.alu .test .rax (.reg .rax)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro _ _ _
    exact Taint.agree_ofRegs (by simp)
  have testWP (s : State) (h : After a s) :
      WP isa (.block [.alu .test .rax (.reg .rax)]) s R := by
    obtain ⟨u, start, result⟩ := h
    refine WP.mono (test_result result) ?_
    rintro t ⟨resultT, zero⟩
    rw [start.recognized_eq] at zero
    exact ⟨⟨u, start, resultT⟩, zero⟩
  have testStage : RelCT isa (fun s t => After a s ∧ After a t)
      (.block [.alu .test .rax (.reg .rax)]) (fun s t => R s ∧ R t) := (testCT.wp (fun s t h => ⟨testWP s h.1, testWP t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2⟩)
  have restoreCT : RelCT isa (fun s t => After a s ∧ After a t) (.block restore) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r9]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact h.1.base.trans h.2.base.symm
  have restoreWP (s : State) (h : After a s) : WP isa (.block restore) s (Ready a) := by
    obtain ⟨u, start, result⟩ := h
    exact WP.mono (restore_ok result) (fun t restored => ⟨u, start, restored⟩)
  have fallbackCT := (fallback_ct v e).mono (P' := fun s t => Ready a s ∧ Ready a t)
    (fun _ _ h => ⟨h.1.pre, h.2.pre, Ready.public h.1 h.2⟩) (fun _ _ h => h)
  have fallbackStage := ((restoreCT.wp (fun s t h => ⟨restoreWP s h.1, restoreWP t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2⟩)).seq fallbackCT
  have choice : RelCT isa (fun s t => R s ∧ R t)
      (.ite .ne (.block [.mov32 .rax (.imm 1)]) (.seq (.block restore) (CheckDomain.domainCode v e)))
      (fun _ _ => True) := by
    apply RelCT.ite (fun s t h => by simp only [eval, h.1.2, h.2.2])
    · apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
      intro _ _ _
      exact Taint.agree_ofRegs (by simp)
    · exact fallbackStage.mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) (fun _ _ h => h)
  exact scanStage.seq (testStage.seq choice)

theorem constantTime (v : RoundImpl) (e : ExpImpl) : ConstantTime isa contract.pre contract.pub (emittedCode v e) := by
  intro s t ts tt u w hs ht hp es et
  have left : Start s s := ⟨hs, fun _ _ => rfl, rfl, rfl, rfl⟩
  exact (anchored_ct v e s s t ts tt u w ⟨left, start_of_pub ht hp⟩ es et).1

end VG.Proof.Ffdh.X86_64.VettedValidation

end

end

/-! ### `Ffdh.X86_64.VettedValidation.Sat`, which only this module used -/

section

/-! A concrete SysV caller satisfies the unchanged signature with the shared constants. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86_64.VettedValidation
open VG VG.X86_64
open VG.Impl.Ffdh.X86_64.VettedValidation
open VG.Impl.Ffdh.VettedGroups

private def satState (words : List (BitVec 64)) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 128 | .rdx => 64 | .rcx => 0x4000 | .r8 => 1056
    | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := constMem 0x100000 words
  rd := [⟨0x1000, 128⟩, ⟨0x100000, 17744⟩]
  wr := [⟨0x4000, 8448⟩]
  syms _ := 0x100000

private theorem satPre (words : List (BitVec 64)) :
    (Spec.Ffdh.checkDomainContract abi 8).pre (stripConsts [(tableSym, words)] (satState words)) := by
  sig_pre [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argRegs,
    List.append_eq, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid, Spec.Rsa.scratchWords]
  repeat' apply And.intro
  all_goals first | rfl | decide | (apply Region.disjoint_of_sep; decide)

private theorem satLayout (words : List (BitVec 64)) (size : words.length = 2218) :
    (satState words).rd.drop ((satState words).rd.length - 1) =
      constRegs [(tableSym, words)] (satState words) := by
  simp only [constRegs, Abi.constRegions, satState, List.map_cons, List.map_nil, size]
  rfl

private theorem satHeld (words : List (BitVec 64)) (size : words.length = 2218) :
    Abi.constsHeld (satState words).mem (satState words).syms [(tableSym, words)] := by
  intro c hc i hi
  obtain rfl := List.mem_singleton.mp hc
  exact constMem_held 0x100000 words (by rw [size]; decide) i hi

private theorem fixedGeometry :
    (0x100000 : Addr).toNat + 17744 ≤ 2 ^ 64 ∧
    (⟨0x100000, 17744⟩ : Region).Disjoint ⟨0x4000, 8448⟩ ∧
    (⟨0x100000, 17744⟩ : Region).Disjoint ⟨0x8000, 8⟩ ∧
    (⟨0x100000, 17744⟩ : Region).Disjoint ⟨(0x8000 : Addr) - BitVec.ofNat 64 8, 8⟩ := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  all_goals exact Region.disjoint_of_sep (by decide)

private theorem satRegions (words : List (BitVec 64)) (size : words.length = 2218) :
    ∀ r ∈ constRegs [(tableSym, words)] (satState words),
      r.base.toNat + r.len ≤ 2 ^ abi.ptrBits ∧
      (∀ q ∈ (satState words).wr, r.Disjoint q) ∧
      ∀ q ∈ abi.reserved 8 (satState words), r.Disjoint q := by
  intro r hr
  simp only [constRegs, Abi.constRegions, List.mem_map, List.mem_singleton] at hr
  obtain ⟨c, rfl, rfl⟩ := hr
  rw [size]
  refine ⟨fixedGeometry.1, ?_, ?_⟩
  · intro q hq
    change q ∈ ([⟨0x4000, 8448⟩] : List Region) at hq
    obtain rfl := List.mem_singleton.mp hq
    exact fixedGeometry.2.1
  · intro q hq
    change q ∈ ([⟨0x8000, 8⟩, ⟨(0x8000 : Addr) - BitVec.ofNat 64 8, 8⟩] : List Region) at hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact fixedGeometry.2.2.1
    · obtain rfl := List.mem_singleton.mp hq
      exact fixedGeometry.2.2.2

private theorem satConsts (words : List (BitVec 64)) (size : words.length = 2218) :
    ConstsOk [(tableSym, words)] 8 (satState words) :=
  ⟨satLayout words size, satHeld words size, satRegions words size, fun r hr => by
    simp only [constRegs, Abi.constRegions, List.mem_map, List.mem_singleton] at hr
    obtain ⟨c, rfl, rfl⟩ := hr
    exact (by decide : (0x100000 : BitVec 64).toNat % 64 = 0)⟩

private theorem satAux (words : List (BitVec 64)) (size : words.length = 2218) :
    ∃ s, (Spec.Ffdh.checkDomainContract (abi.withConsts [(tableSym, words)]) 8).pre s :=
  ⟨satState words, pre_consts.mpr ⟨satPre words, satConsts words size⟩⟩

theorem sat : ∃ s, contract.pre s :=
  satAux tableWords VG.Proof.Ffdh.VettedTableFacts.tableWords_length

end VG.Proof.Ffdh.X86_64.VettedValidation

end

end

/-! Every selected Montgomery backend inherits the same certified standard-domain fast path. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86_64.VettedValidation
open VG VG.X86_64 VG.Proof.MillerRabin.X86_64

theorem verified (v : RoundImpl) (e : ExpImpl) : Verified target (emittedCode v e) contract :=
  ⟨correct v e, constantTime v e, sat⟩

end VG.Proof.Ffdh.X86_64.VettedValidation
