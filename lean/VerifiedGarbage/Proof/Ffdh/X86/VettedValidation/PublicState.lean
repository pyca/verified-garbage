module

import VerifiedGarbage.Proof.Ffdh.X86.CheckDomainCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Geometry
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.VettedValidation.Facts
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Ffdh.X86.Entry
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ffdh.X86.CheckDomainTop
import Mathlib.Tactic.ToAdditive
public import VerifiedGarbage.Proof.Weierstrass.PointContract
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Ffdh.VettedTableFacts
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Table
public import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.State
import VerifiedGarbage.Proof.Framework.X86.SymFrame
public import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Scan
import VerifiedGarbage.Proof.Framework.X86.Spill

/-! ### `Ffdh.X86.VettedValidation.Correct`, which this module and modules that import it used -/

section

/-! ### `Ffdh.X86.VettedValidation.Recognize`, which this module and modules that import it used -/

section

/-! ### `Ffdh.X86.VettedValidation.Frame`, which only this module used -/

section

/-! Prefix writes stay in the original scratch buffer and the balanced four-byte symbol frame. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86.VettedValidation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Bignum.X86

def writes (s : State) : List Region := [scratch s, below (s.gpr .esp) 4]

theorem symbol_sub {s : State} (h : contract.pre s) :
    Region.Sub (below (s.gpr .esp) 4) ⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ := by
  have low := stack_low h
  unfold below
  rw [VG.X86.Taint.sub_setWidth (by omega_using [low])]
  exact Offset.sub_below _ (by decide) (by decide)

theorem args_separate {s : State} (h : contract.pre s) :
    ∀ r ∈ writes s, (⟨argAddr s 0, 20⟩ : Region).Disjoint r := by
  intro r hr
  simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (geometry h).scratchArgs.symm
  · have g := geometry h
    have pointer : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 :=
      addr_eq (by have := stack_bound h; omega_using [this])
    rw [pointer, below, VG.X86.Taint.sub_setWidth (by have := stack_low h; omega_using [this])]
    exact (Offset.disjoint_below_above _ (by decide)).symm

theorem domain_separate {s : State} (h : contract.pre s) :
    ∀ r ∈ writes s, (⟨byteAddr (arg s 0), (arg s 1).toNat⟩ : Region).Disjoint r := by
  intro r hr
  simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (geometry h).domScratch
  · have belowDom : (⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ : Region).Disjoint
        ⟨byteAddr (arg s 0), (arg s 1).toNat⟩ := (geometry h).belowDom
    exact (belowDom.sub_left (symbol_sub h)).symm

theorem return_separate {s : State} (h : contract.pre s) :
    ∀ r ∈ writes s, (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint r := by
  intro r hr
  simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (geometry h).retScratch
  · rw [below, VG.X86.Taint.sub_setWidth (by have := stack_low h; omega_using [this])]
    simpa only [BitVec.add_zero] using
      (Offset.disjoint_below_above ((s.gpr .esp).setWidth 64) (m := 4) (a := 0) (l := 4) (by decide)).symm

theorem args_frame {s t : State} (h : contract.pre s) (sp : t.gpr .esp = s.gpr .esp)
    (F : Frame (writes s) s.mem t.mem) : ∀ i < 5, arg t i = arg s i := by
  intro i hi
  unfold arg argAddr
  rw [sp]
  have pointer : (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 =
      argAddr s 0 + BitVec.ofNat 64 (4 * i) := by
    have top := stack_bound h
    change addr (s.gpr .esp) (4 + 4 * i) = _
    rw [addr_eq (x := s.gpr .esp) (k := 4 + 4 * i) (by omega_using [hi, top])]
    change _ = addr (s.gpr .esp) 4 + _
    rw [addr_eq (by omega_using [top]), BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  exact F.readW (r := ⟨argAddr s 0, 20⟩) (by rw [pointer]; exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi]))
    (args_separate h) (by decide)

theorem domain_frame {s t : State} (h : contract.pre s) (args : ∀ i < 5, arg t i = arg s i)
    (F : Frame (writes s) s.mem t.mem) : domain t = domain s := by
  unfold domain
  rw [args 0 (by decide), args 1 (by decide)]
  exact VG.Proof.Rsa.rsa_bytes_frame F (by have := (arg s 1).isLt; omega_using []) (domain_separate h)

end VG.Proof.Ffdh.X86.VettedValidation

end

end

/-! ### `Ffdh.X86.VettedValidation.Setup`, which only this module used -/

section

/-! ### `Ffdh.X86.VettedValidation.Entry`, which only this module used -/

section

/-! Reuse the original verified register-save prefix before recognizing standard domains. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86.VettedValidation
open VG VG.X86 VG.X86.Wp VG.X86.Spill VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Ffdh.X86.VettedValidation

structure EntryPost (s t : State) : Prop where
  base : t.gpr .ebx = arg s 3
  saved : Saved t.mem (addr (arg s 3)) s.gpr saved
  frame : Frame [scratch s] s.mem t.mem
  keep : Keeps [.eax, .edi, .ebx] s t
  syms : t.syms = s.syms

theorem wrapper {s : State} (h : contract.pre s) : WrapABI VG.Impl.Ffdh.X86.CheckDomain.args 5 s := by
  have old := CheckDomain.wrapABI (geometry h)
  exact ⟨old.below, old.stackLow, old.stackBound, old.argsIn, old.wsIn, old.scratchArgs,
    old.retScratch, old.belowScratch, old.scratchBound, old.lower, old.upper, old.scratchLength⟩

theorem entry_ok {s : State} (h : contract.pre s) :
    WP isa (.block VG.Impl.Ffdh.X86.VettedValidation.entry) s (EntryPost s) := by
  have wrap := wrapper h
  rw [VG.Impl.Ffdh.X86.VettedValidation.entry, WP.block_append_iff]
  refine WP.mono_syms (VG.Proof.Ffdh.X86.entry_ok wrap) ?_
  rintro u ⟨buffer, savedU, keepU, outside⟩ symsU
  have pointer : u.gpr .edi = arg s 3 := by
    have value := congrArg BitVec.toNat buffer.edi
    change ((u.gpr .edi).setWidth 64).toNat = ((arg s 3).setWidth 64).toNat at value
    apply BitVec.eq_of_toNat_eq
    simpa only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt
      (Nat.lt_trans (u.gpr .edi).isLt (by decide : 2 ^ 32 < 2 ^ 64)), Nat.mod_eq_of_lt
      (Nat.lt_trans (arg s 3).isLt (by decide : 2 ^ 32 < 2 ^ 64))] using value
  refine wp_mov fun t T => WP.block_nil ⟨T.gpr.trans pointer, ?_, ?_,
    (keepU.mono (by decide)).widen T.keeps, T.syms.trans symsU⟩
  · intro p hp
    have member : p ∈ VG.Impl.Bignum.X86.Crt.savedRegisters := by
      revert p
      decide
    have bound : (arg s 3).toNat + (arg s 4).toNat * 8 ≤ 2 ^ 32 := (geometry h).scratchBound
    have room : 48 ≤ (arg s 4).toNat * 8 := scratch_room h
    have po : p.2 + 4 ≤ 48 := by revert p; decide
    rw [T.mem, addr_eq (by omega_using [bound, room, po])]
    exact savedU p member
  · rw [T.mem]
    have fit : (arg s 4).toNat * 8 < 2 ^ 64 := by have := (arg s 4).isLt; omega_using []
    have F := VG.Proof.Bignum.outside_frame outside
      (by change 0 + (arg s 4).toNat * 8 ≤ 2 ^ 64; omega_using [])
    change Frame [⟨byteAddr (arg s 3) + BitVec.ofNat 64 0, (arg s 4).toNat * 8⟩] s.mem u.mem at F
    change Frame [⟨byteAddr (arg s 3), (arg s 4).toNat * 8⟩] s.mem u.mem
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using F


end VG.Proof.Ffdh.X86.VettedValidation

end

end

/-! ### `Ffdh.X86.VettedValidation.Tracking`, which only this module used -/

section

/-! The prefix leaves stack arguments, source bytes, and the read-only table intact. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86.VettedValidation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Ffdh.X86.VettedValidation VG.Impl.Ffdh.VettedGroups

structure Tracking (s t : State) : Prop where
  stack : t.gpr .esp = s.gpr .esp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (writes s) s.mem t.mem

theorem Tracking.args {s t : State} (track : Tracking s t) (h : contract.pre s) :
    ∀ i < 5, arg t i = arg s i := args_frame h track.stack track.frame

theorem Tracking.domain_eq {s t : State} (track : Tracking s t) (h : contract.pre s) : domain t = domain s :=
  domain_frame h (track.args h) track.frame

theorem Tracking.after {s t u : State} {rs : List Reg} (track : Tracking s t)
    (mem : u.mem = t.mem) (rest : Keeps rs t u) (noSp : .esp ∉ rs) : Tracking s u :=
  ⟨(rest.1 _ noSp).trans track.stack, rest.2.1.trans track.rd, rest.2.2.trans track.wr,
    by rw [mem]; exact track.frame⟩

theorem Tracking.pre {s t : State} (track : Tracking s t) (h : contract.pre s) :
    (Spec.Ffdh.checkDomainContract abi 172).pre (plain t) := by
  have old := (pre_plain h).1
  sig_pre [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argSlots, argVal, argBytes,
    stackBelow] at old ⊢
  simp only [plain_arg, plain_argAddr] at old ⊢
  rw [track.stack, track.rd, track.wr, track.args h 0 (by decide), track.args h 1 (by decide),
    track.args h 2 (by decide), track.args h 3 (by decide), track.args h 4 (by decide)]
  have addr : argAddr t 0 = argAddr s 0 := by unfold argAddr; rw [track.stack]
  rw [addr]
  exact old

private theorem singleton_regions {name : String} {words : List (BitVec 64)} {s : State} {st : Nat}
    (h : ConstsOk [(name, words)] st s) :
    (∀ r ∈ s.wr, (⟨symAddr s name, 8 * words.length⟩ : Region).Disjoint r) ∧
    (∀ r ∈ abi.reserved st s, (⟨symAddr s name, 8 * words.length⟩ : Region).Disjoint r) :=
  (h.2.2.1 ⟨symAddr s name, 8 * words.length⟩ List.mem_cons_self).2

theorem table_separate {s : State} (h : contract.pre s) :
    ∀ r ∈ writes s, (⟨symAddr s tableSym, 17744⟩ : Region).Disjoint r := by
  have regions := singleton_regions (pre_plain h).2
  rw [VG.Proof.Ffdh.VettedTableFacts.tableWords_length] at regions
  intro r hr
  simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact regions.1 _ (by
      have wr := (geometry h).wr
      change s.wr = [scratch s, ⟨argAddr s 0, 20⟩] at wr
      rw [wr]; exact List.mem_cons_self)
  · have full : (⟨symAddr s tableSym, 17744⟩ : Region).Disjoint
        ⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ := regions.2 _ (by
      change _ ∈ ([⟨(s.gpr .esp).setWidth 64, 4⟩] ++ stackBelow ((s.gpr .esp).setWidth 64) 172)
      simp only [stackBelow, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      exact Or.inr trivial)
    exact full.sub_right (symbol_sub h)

theorem Tracking.table {s t : State} (track : Tracking s t) (h : contract.pre s) :
    TableAt (symAddr s tableSym) groups t := by
  apply tableOfBytes groups _ t
  · rw [track.rd, track.wr]; exact consts_read (pre_plain h).2
  · rw [VG.Proof.Rsa.rsa_bytes_frame track.frame
      (by change tableBytes.length < 2 ^ 64; rw [VG.Proof.Ffdh.VettedTableFacts.tableBytes_length]; decide)
      (by change ∀ r ∈ writes s, (⟨symAddr s tableSym, tableBytes.length⟩ : Region).Disjoint r
          rw [VG.Proof.Ffdh.VettedTableFacts.tableBytes_length]; exact table_separate h)]
    exact consts_bytes (pre_plain h).2
  · change tableBytes.length ≤ 17744
    rw [VG.Proof.Ffdh.VettedTableFacts.tableBytes_length]
  · intro g hg
    simp only [groups, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end VG.Proof.Ffdh.X86.VettedValidation

end

end


/-! Saving the static table address establishes the read-only scan context. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86.VettedValidation
open VG VG.X86 VG.X86.Wp VG.X86.Spill VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Ffdh.X86.VettedValidation

def setup : Prog isa := .seq (.block VG.Impl.Ffdh.X86.VettedValidation.entry)
  (.seq tableAddress (.block saveTable))

structure Ready (s t : State) : Prop where
  tracking : Tracking s t
  context : Context (arg s 3) (arg s 0) (s.gpr .esp) (s.syms tableSym) (arg s 2).toNat (domain s) t
  saved : Saved t.mem (addr (arg s 3)) s.gpr saved

theorem setup_ok {s : State} (h : contract.pre s) : WP isa setup s (Ready s) := by
  rw [setup, WP.seq_iff]
  refine WP.mono (entry_ok h) ?_
  intro u entry
  have spU : u.gpr .esp = s.gpr .esp := entry.keep.1 _ (by decide)
  rw [WP.seq_iff]
  refine WP.mono (symFrame_ok tableSym u (by rw [spU]; have := stack_low h; omega_arith)) ?_
  intro v R
  have spV : v.gpr .esp = s.gpr .esp := (R.gpr _ (by decide)).trans spU
  have baseV : v.gpr .ebx = arg s 3 := (R.gpr _ (by decide)).trans entry.base
  have F1 : Frame (writes s) s.mem u.mem := entry.frame.sub (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_cons_self, fun _ h => h⟩)
  have symbolFrame : Frame [below (s.gpr .esp) 4] u.mem v.mem := by
    simpa only [spU] using R.frame
  have F2 : Frame (writes s) u.mem v.mem := symbolFrame.sub (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩)
  have F : Frame (writes s) s.mem v.mem := F1.trans F2
  have trackV : Tracking s v := ⟨spV, R.rd.trans entry.keep.2.1, R.wr.trans entry.keep.2.2, F⟩
  have bound : (arg s 3).toNat + (arg s 4).toNat * 8 ≤ 2 ^ 32 := (geometry h).scratchBound
  have room : 48 ≤ (arg s 4).toNat * 8 := scratch_room h
  have fits : Fits ((arg s 4).toNat * 8) saved := by
    have small : Fits 48 saved := by decide
    exact ⟨fun p hp => Nat.le_trans (small.1 p hp) room, small.2⟩
  have savedV : Saved v.mem (addr (arg s 3)) s.gpr saved :=
    entry.saved.of_frame R.frame (R := scratch s) (contains_of_fits bound fits) (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      rw [spU]
      have sep : (⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ : Region).Disjoint (scratch s) :=
        (geometry h).belowScratch
      exact (sep.sub_left (symbol_sub h)).symm)
  have writable : InRegions v.wr (addr (v.gpr .ebx) 16) 4 := by
    rw [baseV, trackV.wr, addr_eq (by omega_arith)]
    exact ⟨scratch s, by
      have wr := (geometry h).wr
      change s.wr = [scratch s, ⟨argAddr s 0, 20⟩] at wr
      rw [wr]; exact List.mem_cons_self,
      Offset.contains_base _ (by omega_arith) (by decide)⟩
  have tableValue : v.gpr .eax = s.syms tableSym := by rw [R.addr, entry.syms]
  unfold saveTable
  refine wp_stm rfl writable fun t T => WP.block_nil ?_
  have frameT : Frame (writes s) s.mem t.mem := by
    rw [T.mem, baseV, addr_eq (by omega_arith)]
    exact F.writeW List.mem_cons_self _ (Offset.contains_base _ (by omega_arith) (by decide))
  have trackT : Tracking s t := ⟨by rw [T.gpr]; exact spV, T.rd.trans trackV.rd,
    T.wr.trans trackV.wr, frameT⟩
  refine ⟨trackT, ?_, ?_⟩
  · have length : (domain s).length = (arg s 1).toNat := by
      simp only [domain, Spec.Rsa.bytesAt, List.length_map, List.length_range]
    refine ⟨by rw [T.gpr]; exact baseV, trackT.stack, trackT.args h 0 (by decide), ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, table_fit h, by have := stack_bound h; omega_arith, ?_, (geometry h).pLen.1, (geometry h).pLen.2⟩
    · rw [trackT.args h 1 (by decide), length, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [trackT.args h 2 (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · have read := CallLay.inRegions_sub (read_args h) (off := 0) (l := 12) (by decide) (by decide)
      simp only [BitVec.add_zero] at read
      rw [trackT.rd, trackT.wr, argAddr, trackT.stack]
      exact read
    · rw [trackT.rd, trackT.wr]
      exact ⟨scratch s, List.mem_append_right _ (by
        have wr := (geometry h).wr
        change s.wr = [scratch s, ⟨argAddr s 0, 20⟩] at wr
        rw [wr]; exact List.mem_cons_self), by
        rw [addr_eq (by omega_arith)]; exact Offset.contains_base _ (by omega_arith) (by decide)⟩
    · rw [T.mem, baseV, Mem.readW_writeW_self32, tableValue]
    · rw [trackT.rd, trackT.wr, length]
      exact read_domain h
    · have dom := trackT.domain_eq h
      unfold domain at dom
      rw [trackT.args h 0 (by decide), trackT.args h 1 (by decide)] at dom
      rw [length]
      exact dom
    · rw [length]; exact (geometry h).domBound
    · rw [length]; exact (geometry h).dLen
  · rw [T.mem, baseV]
    exact savedV.writeW_addr bound (fun p hp => fits.1 p hp) (by omega_arith)
      (by decide) _

end VG.Proof.Ffdh.X86.VettedValidation

end

end


/-! The exact-recognition prefix restores every nonvolatile register and the original stack arguments. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86.VettedValidation
open VG VG.X86 VG.X86.Wp VG.X86.Spill VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Ffdh.X86.VettedValidation VG.Impl.Ffdh.VettedGroups

def recognized (s : State) : BitVec 32 := BitVec.ofNat 32 (recognizeList groups (arg s 2).toNat (domain s))

structure Result (s t : State) : Prop where
  tracking : Tracking s t
  value : t.gpr .eax = recognized s
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r

theorem Result.abi {s t : State} (result : Result s t) (h : contract.pre s) : abiPreserved s t :=
  ⟨result.regs, result.tracking.frame.readW (Region.contains_self _ _) (return_separate h) (by decide)⟩

theorem restore_ok {s u : State} (h : contract.pre s) (ready : Ready s u)
    (value : u.gpr .eax = recognized s) : WP isa (.block restore) u (Result s) := by
  have bound : (arg s 3).toNat + (arg s 4).toNat * 8 ≤ 2 ^ 32 := (geometry h).scratchBound
  have room : 48 ≤ (arg s 4).toNat * 8 := scratch_room h
  have base := ready.context.baseReg
  have read : ∀ p ∈ saved, InRegions (u.rd ++ u.wr) (addr (u.gpr .ebx) p.2) 4 := by
    intro p hp
    have fit : p.2 + 4 ≤ 48 := by revert p; decide
    rw [base, ready.tracking.rd, ready.tracking.wr, addr_eq (by omega_using [bound, room, fit])]
    exact ⟨scratch s, List.mem_append_right _ (by
      have wr := (geometry h).wr
      change s.wr = [scratch s, ⟨argAddr s 0, 20⟩] at wr
      rw [wr]; exact List.mem_cons_self), Offset.contains_base _ (by omega_using [room, fit]) (by omega_using [fit])⟩
  change WP isa (.block (restoreCode .ebx ([(.ebp, 36), (.esi, 40), (.edi, 44)] ++ [(.ebx, 32)]) ++ [])) u _
  refine restoreBase_ok _ (by decide) read (by rw [base]; exact ready.saved) fun t R => WP.block_nil ?_
  have stack : t.gpr .esp = s.gpr .esp :=
    (R.other _ (by decide)).trans ready.tracking.stack
  exact ⟨⟨stack, R.rd.trans ready.tracking.rd, R.wr.trans ready.tracking.wr,
    by rw [R.mem]; exact ready.tracking.frame⟩,
    (R.other _ (by decide)).trans value,
    R.abi (by decide) (by decide) ready.tracking.stack⟩

theorem recognize_ok {s : State} (h : contract.pre s) : WP isa recognize s (Result s) := by
  rw [recognize, WP.seq_iff]
  refine WP.mono (setup_ok h) ?_
  intro t ready
  rw [WP.seq_iff]
  have fit : 0 + (groups.flatMap Group.bytes).length ≤ 17744 := by
    simpa only [Nat.zero_add, tableBytes] using
      Nat.le_of_eq VG.Proof.Ffdh.VettedTableFacts.tableBytes_length
  refine WP.mono (scan_ok groups 0 t ready.context
    (by simpa only [BitVec.add_zero, byteAddr, symAddr] using ready.tracking.table h) fit) ?_
  rintro u ⟨value, mem, rest⟩
  exact restore_ok h ⟨ready.tracking.after mem rest (by decide), ready.context.after mem rest,
    by rw [mem]; exact ready.saved⟩ value

end VG.Proof.Ffdh.X86.VettedValidation

end

end

/-! ### `Ffdh.X86.VettedValidation.Fallback`, which only this module used -/

section

/-! Read-only recognition constants do not alter the selected general validator. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86.VettedValidation
open VG VG.X86

theorem fallback_run {s : State}
    (h : (Spec.Ffdh.checkDomainContract abi 172).pre (plain s)) :
    ∃ trace t, Exec isa VG.Impl.Ffdh.X86.CheckDomain.code s trace t ∧
      abiPreserved s t ∧ (Spec.Ffdh.checkDomainContract abi 172).post s t := by
  obtain ⟨trace, t, run, preserved, post⟩ := CheckDomain.verified.1 (plain s) h
  have wide := VG.X86.Exec.widen run (rd := s.rd) (wr := s.wr)
    (plain_covers s) (Covers.refl _)
  refine ⟨trace, t.withRegions s.rd s.wr, ?_, preserved, post⟩
  simpa only [plain, stripConsts, State.withRegions_withRegions, State.withRegions_self] using wide

theorem fallback_ct :
    RelCT isa (fun s t =>
      (Spec.Ffdh.checkDomainContract abi 172).pre (plain s) ∧
      (Spec.Ffdh.checkDomainContract abi 172).pre (plain t) ∧
      (Spec.Ffdh.checkDomainContract abi 172).pub s t)
      VG.Impl.Ffdh.X86.CheckDomain.code (fun _ _ => True) := by
  intro s t ts tt u w ⟨hs, ht, hp⟩ es et
  obtain ⟨ts', u', eu, _, _⟩ := CheckDomain.verified.1 (plain s) hs
  obtain ⟨tt', w', ew, _, _⟩ := CheckDomain.verified.1 (plain t) ht
  have eus : Exec isa VG.Impl.Ffdh.X86.CheckDomain.code s ts' (u'.withRegions s.rd s.wr) := by
    simpa only [plain, stripConsts, State.withRegions_withRegions, State.withRegions_self] using
      (VG.X86.Exec.widen eu (rd := s.rd) (wr := s.wr) (plain_covers s) (Covers.refl _))
  have ewt : Exec isa VG.Impl.Ffdh.X86.CheckDomain.code t tt' (w'.withRegions t.rd t.wr) := by
    simpa only [plain, stripConsts, State.withRegions_withRegions, State.withRegions_self] using
      (VG.X86.Exec.widen ew (rd := t.rd) (wr := t.wr) (plain_covers t) (Covers.refl _))
  have sameS := (Exec.det es eus).1
  have sameT := (Exec.det et ewt).1
  refine ⟨?_, True.intro⟩
  rw [sameS, sameT]
  exact CheckDomain.verified.2.1 _ _ _ _ _ _ hs ht hp eu ew

end VG.Proof.Ffdh.X86.VettedValidation

end

end


/-! Exact certificate success and complete general validation share the unchanged API contract. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86.VettedValidation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Ffdh.X86.VettedValidation VG.Impl.Ffdh.VettedGroups

theorem test_result {s u : State} (h : Result s u) :
    WP isa (.block [.alu .test .eax (.reg .eax)]) u fun t =>
      Result s t ∧ t.zf = some (recognized s == 0) := by
  refine wp_test fun t T zero => WP.block_nil ⟨?_, ?_⟩
  · exact ⟨h.tracking.after T.mem (T.keeps []) (by decide),
      by rw [T.gpr]; exact h.value, fun r hr => by rw [T.gpr]; exact h.regs r hr⟩
  · simpa only [BitVec.and_self, h.value] using zero

private theorem abi_trans {s t u : State} (a : abiPreserved s t) (b : abiPreserved t u) :
    abiPreserved s u := by
  have ret := b.2
  rw [a.1 .esp (by decide)] at ret
  exact ⟨fun r hr => (b.1 r hr).trans (a.1 r hr), ret.trans a.2⟩

theorem correct (s : State) (h : contract.pre s) :
    WP isa code s fun t => abiPreserved s t ∧ contract.post s t := by
  rw [code, WP.seq_iff]
  refine WP.mono (recognize_ok h) ?_
  intro t result
  rw [WP.seq_iff]
  refine WP.mono (test_result result) ?_
  rintro u ⟨tested, zero⟩
  refine WP.ite (!(recognized s == 0)) (by simp only [eval, zero, Option.map_some]) ?_ ?_
  · intro hit
    have nonzero : recognized s ≠ 0 := by simpa only [Bool.not_eq_true', beq_eq_false_iff_ne] using hit
    have raw : recognizeList groups (arg s 2).toNat (domain s) ≠ 0 := by
      intro bad
      exact nonzero (by unfold recognized; rw [bad]; rfl)
    have len : (domain s).length = (arg s 1).toNat := by
      simp only [domain, Spec.Rsa.bytesAt, List.length_map, List.length_range]
    have shape : (domain s).length = 2 * (arg s 2).toNat ∨ (domain s).length = 3 * (arg s 2).toNat := by
      rw [len]; exact (geometry h).dLen
    have valid := VG.Proof.Ffdh.VettedValidation.recognized_domain_valid groups (fun _ hg => hg) shape raw
    refine wp_movi fun w W => WP.block_nil ⟨?_, ?_⟩
    · have kept := tested.abi h
      exact ⟨fun r hr => (W.other r (by revert r; decide)).trans (kept.1 r hr),
        by rw [W.mem]; exact kept.2⟩
    · change (Spec.Ffdh.checkDomainContract abi 172).post s w
      sig_post [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argSlots, argVal, argBytes]
      rw [BitVec.setWidth_append_eq_right, W.gpr]
      change 1 = if Spec.Ffdh.domainValid (arg s 2).toNat (domain s) then 1 else 0
      rw [valid]; rfl
  · intro _
    obtain ⟨tr, w, run, kept, post⟩ := fallback_run (tested.tracking.pre h)
    refine ⟨tr, w, run, abi_trans (tested.abi h) kept, ?_⟩
    change (Spec.Ffdh.checkDomainContract abi 172).post s w
    sig_post [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argSlots, argVal, argBytes] at post ⊢
    rw [BitVec.setWidth_append_eq_right] at post ⊢
    change (w.gpr .eax).toNat = if Spec.Ffdh.domainValid (arg u 2).toNat (domain u) then 1 else 0 at post
    change (w.gpr .eax).toNat = if Spec.Ffdh.domainValid (arg s 2).toNat (domain s) then 1 else 0
    rw [tested.tracking.args h 2 (by decide), tested.tracking.domain_eq h] at post
    exact post

end VG.Proof.Ffdh.X86.VettedValidation

end

end

/-! Public anchors permit unrelated nonvolatile registers and scratch contents. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86.VettedValidation
open VG VG.X86 VG.Proof.Bignum.X86
open VG.Impl.Ffdh.X86.VettedValidation

structure Start (a s : State) : Prop where
  pre : contract.pre s
  stack : s.gpr .esp = a.gpr .esp
  args : ∀ i < 5, arg s i = arg a i
  domain : domain s = domain a
  symbol : s.syms tableSym = a.syms tableSym

private theorem singleton_sym {name : String} {words : List (BitVec 64)} {s t : State}
    (h : ∀ c ∈ [(name, words)], symAddr s c.1 = symAddr t c.1) : s.syms name = t.syms name := by
  have wide := h (name, words) List.mem_cons_self
  have value := congrArg BitVec.toNat wide
  apply BitVec.eq_of_toNat_eq
  simpa only [symAddr, BitVec.toNat_setWidth, Nat.mod_eq_of_lt
    (Nat.lt_trans (s.syms name).isLt (by decide : 2 ^ 32 < 2 ^ 64)), Nat.mod_eq_of_lt
    (Nat.lt_trans (t.syms name).isLt (by decide : 2 ^ 32 < 2 ^ 64))] using value

theorem start_of_pub {a s : State} (h : contract.pre s) (pub : contract.pub a s) : Start a s := by
  have relation : (Spec.Ffdh.checkDomainContract abi 172).pub a s ∧
      ∀ c ∈ tableConsts, symAddr a c.1 = symAddr s c.1 := pub_consts.mp pub
  obtain ⟨sp, args, bytes⟩ := CheckDomain.pub_facts relation.1
  exact ⟨h, sp.symm, fun i hi => (args i hi).symm, bytes.symm, (singleton_sym relation.2).symm⟩

def After (a t : State) : Prop := ∃ s, Start a s ∧ Result s t

theorem After.pre {a t : State} (h : After a t) : (Spec.Ffdh.checkDomainContract abi 172).pre (plain t) := by
  obtain ⟨s, start, result⟩ := h
  exact result.tracking.pre start.pre

theorem After.args {a t : State} (h : After a t) : ∀ i < 5, arg t i = arg a i := by
  obtain ⟨s, start, result⟩ := h
  intro i hi
  exact (result.tracking.args start.pre i hi).trans (start.args i hi)

theorem After.stack {a t : State} (h : After a t) : t.gpr .esp = a.gpr .esp := by
  obtain ⟨s, start, result⟩ := h
  exact result.tracking.stack.trans start.stack

theorem After.domain_eq {a t : State} (h : After a t) : domain t = domain a := by
  obtain ⟨s, start, result⟩ := h
  exact (result.tracking.domain_eq start.pre).trans start.domain

theorem After.public {a s t : State} (hs : After a s) (ht : After a t) :
    (Spec.Ffdh.checkDomainContract abi 172).pub s t := by
  sig_pub [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argSlots, argVal, argBytes]
  refine ⟨hs.stack.trans ht.stack.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (domain s).map (·.toNat) = (domain t).map (·.toNat)
    rw [hs.domain_eq, ht.domain_eq]
  all_goals exact (hs.args _ (by decide)).trans (ht.args _ (by decide)).symm

end VG.Proof.Ffdh.X86.VettedValidation
