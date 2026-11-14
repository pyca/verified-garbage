module

public import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Frame
public import VerifiedGarbage.Proof.Ffdh.X86.Entry
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ffdh.X86.CheckDomainTop
import Mathlib.Tactic.ToAdditive
public import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Geometry
public import VerifiedGarbage.Proof.Weierstrass.PointContract
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ffdh.VettedTableFacts
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Table
public import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.State
import VerifiedGarbage.Proof.Framework.X86.SymFrame
public import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Scan
import VerifiedGarbage.Proof.Framework.X86.Spill

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
