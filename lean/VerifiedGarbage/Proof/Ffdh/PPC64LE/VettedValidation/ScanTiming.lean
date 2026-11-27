module

import VerifiedGarbage.Proof.Ffdh.VettedTableFacts
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Impl.Ffdh.PPC64LE.VettedValidation
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.VettedValidation.Record
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.VettedValidation.State
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchConsts
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.CallLay
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckDomainFn
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckDomainCT
meta import VerifiedGarbage.Proof.Framework.Contract

/-! ### `Ffdh.PPC64LE.VettedValidation.Recognize`, which the modules that import this one used -/

section

/-! ### `Ffdh.PPC64LE.VettedValidation.Geometry`, which this module and modules that import it used -/

section

/-! ### `Ffdh.PPC64LE.Domain.CheckDomainVerified`, which only this module used -/

section

/-!
# `vg_ffdh_check_domain` on PPC64LE: verified against the shared contract

`cdContract` states the shared contract on the registers (`cd_implies`);
with correctness (`cd_correct`) and constant time (`cd_ct`), `checkDomain`
is verified (`cd_verified`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Domain

open VG VG.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain

/-- A state meeting `cdContract.pre`: a 512-bit p without q, the domain at
`0x1000` and the working space at `0x4000`. -/
def cdSatState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 128 | .r5 => 64 | .r6 => 0x4000 | .r7 => 1056 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x4000, 8448⟩]

theorem cd_implies : cdContract.Implies (Spec.Ffdh.checkDomainContract abi) := by
  sig_implies [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argRegs, cdContract,
    Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid] [cdSatState] using cdSatState

/-- `vg_ffdh_check_domain`. -/
theorem cd_verified : Verified target checkDomain (Spec.Ffdh.checkDomainContract abi) :=
  Verified.of_correct cd_correct cd_ct cd_implies

end VG.Proof.Ffdh.PPC64LE.Domain

end

end

/-! ### `Ffdh.PPC64LE.VettedValidation.Table`, which this module and modules that import it used -/

section

/-! The shared emitted table supplies every exact-recognition record. -/

@[expose] public section
namespace VG.Proof.Ffdh.PPC64LE.VettedValidation
open VG VG.PPC64LE
open VG.Impl.Ffdh.PPC64LE.VettedValidation
open VG.Impl.Ffdh.VettedGroups
open VG.Proof.Ffdh.VettedTableFacts

theorem tableOfBytes (gs : List Group) (ptr : Addr) (s : State)
    (read : InRegions (s.rd ++ s.wr) ptr (gs.flatMap Group.bytes).length)
    (bytes : Spec.Rsa.bytesAt s.mem ptr (gs.flatMap Group.bytes).length = gs.flatMap Group.bytes)
    (bound : (gs.flatMap Group.bytes).length ≤ 17744)
    (valid : ∀ g ∈ gs, 0 < g.len ∧ g.len < 2 ^ 15 ∧ g.bits < 2 ^ 15) :
    TableAt ptr gs s := by
  induction gs generalizing ptr with
  | nil => trivial
  | cons g gs ih =>
    have length := groupBytes_length g
    have total : ((g :: gs).flatMap Group.bytes).length =
        8 + 3 * g.len + (gs.flatMap Group.bytes).length := by
      rw [List.flatMap_cons, List.length_append, length]
    have domainLength : g.domain.length = 3 * g.len := by
      simp only [Group.domain, List.length_append, VG.Proof.Rsa.i2osp_length]
      omega_arith
    have headerLength : (wordBytes g.len ++ wordBytes g.bits).length = 8 := by
      simp only [wordBytes, List.length_append, List.length_map, List.length_range]
    have domain : (((g :: gs).flatMap Group.bytes).drop 8).take (3 * g.len) = g.domain := by
      rw [List.flatMap_cons, Group.bytes, List.append_assoc, ← headerLength,
        List.drop_left, List.take_left' domainLength]
    have tailBytes : (((g :: gs).flatMap Group.bytes).drop (8 + 3 * g.len)).take
        (gs.flatMap Group.bytes).length = gs.flatMap Group.bytes := by
      rw [List.flatMap_cons, ← length, List.drop_left, List.take_length]
    have part (d n : Nat) (size : d + n ≤ ((g :: gs).flatMap Group.bytes).length) :
        InRegions (s.rd ++ s.wr) (ptr + BitVec.ofNat 64 d) n :=
      CallLay.inRegions_sub read size (by omega_arith)
    have slice (d n : Nat) (size : d + n ≤ ((g :: gs).flatMap Group.bytes).length) :
        Spec.Rsa.bytesAt s.mem (ptr + BitVec.ofNat 64 d) n =
          (((g :: gs).flatMap Group.bytes).drop d).take n := by
      rw [← VG.Proof.Dsa.bytesAt_slice s.mem ptr size, bytes]
    have v := valid g (by simp)
    refine ⟨⟨v.1, v.2.1, v.2.2, part 8 (3 * g.len) (by rw [total]; omega_arith),
      (slice 8 (3 * g.len) (by rw [total]; omega_arith)).trans domain⟩, ?_⟩
    exact ih _ (part _ _ (by rw [total]))
      ((slice _ _ (by rw [total])).trans tailBytes)
      (by rw [total] at bound; omega_arith) (fun g hg => valid g (by simp [hg]))

private theorem singleton_held {name : String} {words : List (BitVec 64)}
    {s : State} {stack : Nat} (hc : ConstsOk [(name, words)] stack s) :
    ∀ i < words.length, s.mem.readW (s.syms name + BitVec.ofNat 64 (8 * i)) 64 = words.getD i 0 := by
  intro i hi
  exact hc.2.1 (name, words) List.mem_cons_self i hi

private theorem singleton_read {name : String} {words : List (BitVec 64)}
    {s : State} {stack : Nat} (hc : ConstsOk [(name, words)] stack s) :
    InRegions (s.rd ++ s.wr) (s.syms name) (8 * words.length) := by
  have member : (⟨s.syms name, 8 * words.length⟩ : Region) ∈ s.rd := by
    apply List.mem_of_mem_drop
    rw [hc.1]
    exact List.mem_cons_self
  exact ⟨_, List.mem_append_left _ member, Region.contains_self _ _⟩

theorem consts_bytes {s : State} {stack : Nat} (hc : ConstsOk tableConsts stack s) :
    Spec.Rsa.bytesAt s.mem (s.syms tableSym) tableBytes.length = tableBytes := by
  apply List.ext_getElem
  · simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
  · intro i hi hj
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
    have held := singleton_held (name := tableSym) (words := tableWords) hc
    rw [table_held_byte held hj]
    exact (List.getElem_eq_getD (h := hj) 0).symm

theorem consts_read {s : State} {stack : Nat} (hc : ConstsOk tableConsts stack s) :
    InRegions (s.rd ++ s.wr) (s.syms tableSym) tableBytes.length := by
  have read := singleton_read (name := tableSym) (words := tableWords) hc
  simpa only [tableWords_length, tableBytes_length] using read

theorem consts_table {s : State} {stack : Nat} (hc : ConstsOk tableConsts stack s) :
    TableAt (s.syms tableSym) groups s := by
  apply tableOfBytes groups _ s (consts_read hc) (consts_bytes hc)
    (by change tableBytes.length ≤ 17744; rw [tableBytes_length])
  intro g hg
  simp only [groups, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end VG.Proof.Ffdh.PPC64LE.VettedValidation

end

end

/-! The existing shared signature supplies the same input and working-space geometry. -/

@[expose] public section
namespace VG.Proof.Ffdh.PPC64LE.VettedValidation
open VG VG.PPC64LE
open VG.Impl.Ffdh.PPC64LE.VettedValidation

def contract := Spec.Ffdh.checkDomainContract (abi.withConsts tableConsts)
def plain (s : State) := stripConsts tableConsts s

theorem pre_plain {s : State} (h : contract.pre s) :
    (Spec.Ffdh.checkDomainContract abi).pre (plain s) ∧ ConstsOk tableConsts 0 s :=
  pre_consts.mp h

theorem cd_pre {s : State} (h : contract.pre s) : Domain.cdContract.pre (plain s) :=
  Domain.cd_implies.pre _ (pre_plain h).1

def domain (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat

theorem context {s : State} (h : contract.pre s) :
    Context (s.gpr .r3) (s.gpr .r5).toNat (domain s) s := by
  obtain ⟨rd, _, _, _, _, sizes, shape, _⟩ := cd_pre h
  have len : (domain s).length = (s.gpr .r4).toNat := by
    simp only [domain, Spec.Rsa.bytesAt, List.length_map, List.length_range]
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, sizes.1, sizes.2⟩
  · rw [len, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [len]
    have read : InRegions ((plain s).rd ++ (plain s).wr) (s.gpr .r3) (s.gpr .r4).toNat :=
      ⟨_, List.mem_append_left _ (by rw [rd]; exact List.mem_cons_self), Region.contains_self _ _⟩
    obtain ⟨r, member, contains⟩ := read
    refine ⟨r, ?_, contains⟩
    rcases List.mem_append.mp member with hr | hw
    · exact List.mem_append_left _ (List.mem_of_mem_take hr)
    · exact List.mem_append_right _ hw
  · rw [len]; rfl
  · rw [len]
    exact shape

end VG.Proof.Ffdh.PPC64LE.VettedValidation

end

end

/-! ### `Ffdh.PPC64LE.VettedValidation.Scan`, which only this module used -/

section

/-! The finite scan returns the same recognition result as the shared pure table. -/

@[expose] public section
namespace VG.Proof.Ffdh.PPC64LE.VettedValidation
open VG VG.PPC64LE
open VG.Impl.Ffdh.PPC64LE.VettedValidation
open VG.Impl.Ffdh.VettedGroups

theorem return_ok (s : State) (n : Nat) (fit : n < 2 ^ 15) :
    WP isa (.block [.li .r8 n]) s fun t =>
      t.gpr .r8 = BitVec.ofNat 64 n ∧ t.mem = s.mem ∧ Keep clobbers s t := by
  exact VG.Proof.RsaPkcs1Sig.PPC64LE.wp_li fit fun t o value =>
    VG.Proof.RsaPkcs1Sig.PPC64LE.wp_nil ⟨value, o.mem,
      (show Keep [.r8] s t from ⟨o.gpr, o.rd, o.wr⟩).mono (by decide)⟩

theorem scan_ok {src table : Addr} {k : Nat} {dom : List Byte}
    (gs : List Group) (offset : Nat) (s : State)
    (h : Context src k dom s) (sym : s.syms tableSym = table)
    (data : TableAt (table + BitVec.ofNat 64 offset) gs s)
    (fit : offset + (gs.flatMap Group.bytes).length ≤ 17744) :
    WP isa (scan gs offset) s fun t =>
      t.gpr .r8 = BitVec.ofNat 64 (recognizeList gs k dom) ∧
      t.mem = s.mem ∧ Keep clobbers s t := by
  induction gs generalizing offset s with
  | nil => exact return_ok s 0 (by decide)
  | cons g gs ih =>
    have total : ((g :: gs).flatMap Group.bytes).length =
        8 + 3 * g.len + (gs.flatMap Group.bytes).length := by
      rw [List.flatMap_cons, List.length_append, VG.Proof.Ffdh.VettedTableFacts.groupBytes_length]
    rw [scan, WP.seq_iff]
    refine WP.mono_syms (record_ok h g sym data.1 (by rw [total] at fit; omega_arith)) ?_
    rintro u ⟨zero, memU, restU⟩ symU
    refine WP.ite (decide (g.len = k ∧ dom = g.domain.take dom.length))
      (by
        rw [VG.Proof.RsaPkcs1Sig.PPC64LE.eval_zero]
        congr 1
        exact Bool.eq_iff_iff.mpr (by simpa only [beq_iff_eq, decide_eq_true_eq] using zero)) ?_ ?_
    · intro hit
      refine WP.mono (return_ok u g.bits data.1.bitsFit) ?_
      rintro t ⟨value, memT, restT⟩
      exact ⟨by simpa only [recognizeList, ite_eq_left (of_decide_eq_true hit)] using value,
        memT.trans memU, keep_trans restU restT⟩
    · intro miss
      have tail := (data.after memU restU).2
      have ptr : (table + BitVec.ofNat 64 offset) + BitVec.ofNat 64 (8 + 3 * g.len) =
          table + BitVec.ofNat 64 (offset + 8 + 3 * g.len) := by
        rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
        congr 2
        omega_arith
      rw [ptr] at tail
      refine WP.mono (ih (offset + 8 + 3 * g.len) u (h.after memU restU)
        (by rw [symU]; exact sym) tail (by rw [total] at fit; omega_arith)) ?_
      rintro t ⟨value, memT, restT⟩
      exact ⟨by simpa only [recognizeList, ite_eq_right (of_decide_eq_false miss)] using value,
        memT.trans memU, keep_trans restU restT⟩

end VG.Proof.Ffdh.PPC64LE.VettedValidation

end

end


/-! The read-only prefix restores LR and preserves the original domain arguments. -/

@[expose] public section
namespace VG.Proof.Ffdh.PPC64LE.VettedValidation
open VG VG.PPC64LE
open VG.Impl.Ffdh.PPC64LE.VettedValidation VG.Impl.Ffdh.VettedGroups

def allClobbers : List Reg := .r12 :: clobbers

def recognized (s : State) : BitVec 64 :=
  BitVec.ofNat 64 (recognizeList groups (s.gpr .r5).toNat (domain s))

structure Result (s t : State) : Prop where
  value : t.gpr .r8 = recognized s
  mem : t.mem = s.mem
  keep : Keep allClobbers s t
  lr : t.lr = s.lr

theorem recognize_ok {s : State} (h : contract.pre s) :
    WP isa recognize s fun t => Result s t := by
  have input := context h
  have table := consts_table (pre_plain h).2
  have fit : 0 + (groups.flatMap Group.bytes).length ≤ 17744 := by
    simpa only [Nat.zero_add, tableBytes] using
      (Nat.le_of_eq VG.Proof.Ffdh.VettedTableFacts.tableBytes_length)
  rw [recognize, WP.seq_iff]
  refine WP.mono_syms (VG.Proof.RsaPkcs1Sig.PPC64LE.wp_mflr
    (Q := fun u : State => VG.Proof.RsaPkcs1Sig.PPC64LE.Only [.r12] s u ∧ u.gpr .r12 = s.lr)
    (fun u o saved => VG.Proof.RsaPkcs1Sig.PPC64LE.wp_nil ⟨o, saved⟩)) ?_
  rintro u ⟨only, saved⟩ symU
  rw [WP.seq_iff]
  refine WP.mono (scan_ok (src := s.gpr .r3) (table := s.syms tableSym)
    (k := (s.gpr .r5).toNat) (dom := domain s) groups 0 u ?_ ?_ ?_ fit) ?_
  · exact ⟨(only.get .r3).trans input.source, (only.get .r4).trans input.length,
      (only.get .r5).trans input.width, by rw [only.rd, only.wr]; exact input.read,
      by rw [only.mem]; exact input.bytes, input.shape, input.lower, input.upper⟩
  · rw [symU]
  · have after := table.after only.mem (show Keep [.r12] s u from ⟨only.gpr, only.rd, only.wr⟩)
    rw [symU] at *
    simpa only [BitVec.add_zero] using after
  · rintro v ⟨value, memV, restV⟩
    refine VG.Proof.RsaPkcs1Sig.PPC64LE.wp_mtlr fun w regs memW rdW wrW spW lrW =>
      VG.Proof.RsaPkcs1Sig.PPC64LE.wp_nil ⟨by rw [regs, value]; rfl,
        memW.trans (memV.trans only.mem), ?_, by rw [lrW, restV.gpr (by decide), saved]⟩
    refine ⟨?_, rdW.trans (restV.2.1.trans only.rd), wrW.trans (restV.2.2.trans only.wr)⟩
    intro r hr
    rw [regs, restV.gpr (by intro hc; exact hr (List.mem_cons_of_mem _ hc)),
      only.gpr r (by simpa only [allClobbers, List.mem_cons, List.not_mem_nil, or_false] using
        (fun eq : r = .r12 => hr (by rw [eq]; exact List.mem_cons_self))) ]

end VG.Proof.Ffdh.PPC64LE.VettedValidation

end

end

/-! ### `Ffdh.PPC64LE.VettedValidation.RecordTiming`, which this module and modules that import it used -/

section

/-! Fixed-length comparison leaks only the original public lengths and pointers. -/

@[expose] public section
namespace VG.Proof.Ffdh.PPC64LE.VettedValidation
open VG VG.PPC64LE
open VG.Impl.Ffdh.PPC64LE.VettedValidation VG.Impl.Ffdh.VettedGroups

theorem withSp {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun t => Q t ∧ t.sp = s.sp := by
  obtain ⟨tr, t, run, post⟩ := h
  exact ⟨tr, t, run, post, Exec.sp run⟩

theorem record_ct {src table stack : Addr} {k offset : Nat} {dom : List Byte}
    (g : Group) (lenFit : g.len < 2 ^ 15) (offsetFit : offset + 8 < 2 ^ 15) :
    RelCT isa (fun s t =>
      (Context src k dom s ∧ s.syms tableSym = table ∧ s.sp = stack) ∧
      (Context src k dom t ∧ t.syms tableSym = table ∧ t.sp = stack))
      (record g offset) (fun _ _ => True) := by
  let P := fun s : State => Context src k dom s ∧ s.syms tableSym = table ∧ s.sp = stack
  let H := fun s : State => P s ∧ (s.gpr .r0 = 0 ↔ g.len = k)
  let A := fun s : State => Context src k dom s ∧
    s.gpr .r8 = table + BitVec.ofNat 64 (offset + 8) ∧ s.sp = stack
  have headerCT : RelCT isa (fun s t => P s ∧ P t)
      (.block [.subi .r0 .r5 g.len]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (hc := .block []) (by rfl)
    intro s t h
    exact ⟨h.1.2.2.trans h.2.2.2.symm, by simp [Taint.ofRegs]⟩
  have headerWP (s : State) (h : P s) : WP isa (.block [.subi .r0 .r5 g.len]) s H := by
    refine WP.mono_syms (withSp (header_ok h.1 g lenFit)) ?_
    rintro t ⟨⟨zero, mem, rest⟩, sp⟩ sym
    exact ⟨⟨h.1.after mem rest, sym ▸ h.2.1, sp.trans h.2.2⟩, zero⟩
  have argsCT : RelCT isa (fun s t => P s ∧ P t)
      (.block [.adrSym .r8 tableSym, .addi .r8 .r8 (offset + 8)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taintSym [tableSym]) (Taint.ofRegs []) _ (hc := .block []) (by rfl)
    intro s t h
    refine ⟨⟨h.1.2.2.trans h.2.2.2.symm, by simp [Taint.ofRegs]⟩, ?_⟩
    intro name member
    obtain rfl := List.mem_singleton.mp member
    exact h.1.2.1.trans h.2.2.1.symm
  have argsWP (s : State) (h : P s) :
      WP isa (.block [.adrSym .r8 tableSym, .addi .r8 .r8 (offset + 8)]) s A := by
    refine WP.mono (withSp (args_ok h.2.1 offsetFit)) ?_
    rintro t ⟨⟨ptr, mem, rest⟩, sp⟩
    exact ⟨h.1.after mem rest, ptr, sp.trans h.2.2⟩
  have compareCT : RelCT isa (fun s t => A s ∧ A t)
      VG.Impl.Ffdh.PPC64LE.VettedValidation.compare (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r3, .r4, .r8]) _ (by taint_decide)
    intro s t h
    refine ⟨h.1.2.2.trans h.2.2.2.symm, ?_⟩
    intro r hr
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.1.1.source.trans h.2.1.source.symm
    · exact h.1.1.length.trans h.2.1.length.symm
    · exact h.1.2.1.trans h.2.2.1.symm
  have compareStage := ((argsCT.wp (fun s t h => ⟨argsWP s h.1, argsWP t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2⟩)).seq compareCT
  have choice : RelCT isa (fun s t => H s ∧ H t)
      (.ite (.zero .d .r0)
        (.seq (.block [.adrSym .r8 tableSym, .addi .r8 .r8 (offset + 8)])
          VG.Impl.Ffdh.PPC64LE.VettedValidation.compare) (.block [.li .r10 1]))
      (fun _ _ => True) := by
    apply RelCT.ite (fun s t h => ?_)
    · exact compareStage.mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) (fun _ _ h => h)
    · apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
      intro s t h
      exact ⟨h.1.1.1.2.2.trans h.1.2.1.2.2.symm, by simp [Taint.ofRegs]⟩
    · rw [VG.Proof.RsaPkcs1Sig.PPC64LE.eval_zero, VG.Proof.RsaPkcs1Sig.PPC64LE.eval_zero]
      congr 1
      apply Bool.eq_iff_iff.mpr
      simpa only [beq_iff_eq] using h.1.2.trans h.2.2.symm
  unfold record
  exact ((headerCT.wp (fun s t h => ⟨headerWP s h.1, headerWP t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2⟩)).seq choice

end VG.Proof.Ffdh.PPC64LE.VettedValidation

end

end

/-! The scan branches only on exact matches against the already-public input. -/

@[expose] public section
namespace VG.Proof.Ffdh.PPC64LE.VettedValidation
open VG VG.PPC64LE
open VG.Impl.Ffdh.PPC64LE.VettedValidation
open VG.Impl.Ffdh.VettedGroups

theorem scan_ct {src table stack : Addr} {k : Nat} {dom : List Byte}
    (gs : List Group) (offset : Nat)
    (fit : offset + (gs.flatMap Group.bytes).length ≤ 17744)
    (valid : ∀ g ∈ gs, g.len < 2 ^ 15) :
    RelCT isa (fun s t =>
      (Context src k dom s ∧ s.syms tableSym = table ∧
        TableAt (table + BitVec.ofNat 64 offset) gs s ∧ s.sp = stack) ∧
      (Context src k dom t ∧ t.syms tableSym = table ∧
        TableAt (table + BitVec.ofNat 64 offset) gs t ∧ t.sp = stack))
      (scan gs offset) (fun _ _ => True) := by
  induction gs generalizing offset with
  | nil =>
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (hc := .block []) (by rfl)
    intro s t h
    exact ⟨h.1.2.2.2.trans h.2.2.2.2.symm, by simp [Taint.ofRegs]⟩
  | cons g gs ih =>
    have total : ((g :: gs).flatMap Group.bytes).length =
        8 + 3 * g.len + (gs.flatMap Group.bytes).length := by
      rw [List.flatMap_cons, List.length_append, VG.Proof.Ffdh.VettedTableFacts.groupBytes_length]
    let P := fun s : State => Context src k dom s ∧ s.syms tableSym = table ∧
      TableAt (table + BitVec.ofNat 64 offset) (g :: gs) s ∧ s.sp = stack
    let H := fun s : State => P s ∧
      (s.gpr .r10 = 0 ↔ g.len = k ∧ dom = g.domain.take dom.length)
    have stepWP (s : State) (h : P s) : WP isa (record g offset) s H := by
      refine WP.mono_syms (withSp (record_ok h.1 g h.2.1 h.2.2.1.1 (by rw [total] at fit; omega_using [fit]))) ?_
      rintro t ⟨⟨zero, mem, rest⟩, sp⟩ sym
      exact ⟨⟨h.1.after mem rest, sym ▸ h.2.1, h.2.2.1.after mem rest, sp.trans h.2.2.2⟩, zero⟩
    have stepCT := (record_ct (src := src) (table := table) (stack := stack) (k := k) (dom := dom)
      g (valid g (by simp)) (offset := offset) (by rw [total] at fit; omega_using [fit])).mono
      (P' := fun s t => P s ∧ P t)
      (fun _ _ h => ⟨⟨h.1.1, h.1.2.1, h.1.2.2.2⟩, ⟨h.2.1, h.2.2.1, h.2.2.2.2⟩⟩) (fun _ _ h => h)
    have branches : RelCT isa (fun s t => H s ∧ H t)
        (.ite (.zero .d .r10) (.block [.li .r8 g.bits])
          (scan gs (offset + 8 + 3 * g.len))) (fun _ _ => True) := by
      apply RelCT.ite (fun s t h => by
        rw [VG.Proof.RsaPkcs1Sig.PPC64LE.eval_zero, VG.Proof.RsaPkcs1Sig.PPC64LE.eval_zero]
        congr 1
        apply Bool.eq_iff_iff.mpr
        simpa only [beq_iff_eq] using h.1.2.trans h.2.2.symm)
      · apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (hc := .block []) (by rfl)
        intro s t h
        exact ⟨h.1.1.1.2.2.2.trans h.1.2.1.2.2.2.symm, by simp [Taint.ofRegs]⟩
      · have ptr : (table + BitVec.ofNat 64 offset) + BitVec.ofNat 64 (8 + 3 * g.len) =
            table + BitVec.ofNat 64 (offset + 8 + 3 * g.len) := by
          rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
          congr 2
          omega_using []
        exact (ih (offset + 8 + 3 * g.len) (by rw [total] at fit; omega_using [fit])
          (fun x hx => valid x (by simp [hx]))).mono
          (fun s t h => ⟨⟨h.1.1.1.1, h.1.1.1.2.1, by rw [← ptr]; exact h.1.1.1.2.2.1.2, h.1.1.1.2.2.2⟩,
            ⟨h.1.2.1.1, h.1.2.1.2.1, by rw [← ptr]; exact h.1.2.1.2.2.1.2, h.1.2.1.2.2.2⟩⟩)
          (fun _ _ h => h)
    rw [scan]
    exact ((stepCT.wp (fun s t h => ⟨stepWP s h.1, stepWP t h.2⟩)).mono
      (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2⟩)).seq branches

end VG.Proof.Ffdh.PPC64LE.VettedValidation
