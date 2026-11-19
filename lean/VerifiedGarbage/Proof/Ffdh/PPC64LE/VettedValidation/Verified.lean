module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.VettedValidation.ScanTiming
import VerifiedGarbage.Proof.Ffdh.VettedTableFacts
import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import Batteries.Logic
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ffdh.Contract
meta import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Impl.Ffdh.PPC64LE.VettedValidation
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Ffdh.VettedValidation.Facts

/-! ### `Ffdh.PPC64LE.VettedValidation.Timing`, which only this module used -/

section

/-! ### `Ffdh.PPC64LE.VettedValidation.PrefixTiming`, which this module and modules that import it used -/

section

/-! ### `Ffdh.PPC64LE.VettedValidation.Correct`, which this module and modules that import it used -/

section

/-! ### `Ffdh.PPC64LE.VettedValidation.Fallback`, which only this module used -/

section

/-! Read-only recognition constants do not alter the selected general validator. -/

@[expose] public section
namespace VG.Proof.Ffdh.PPC64LE.VettedValidation
open VG VG.PPC64LE

theorem plain_covers (s : State) : Covers ((plain s).rd ++ (plain s).wr) (s.rd ++ s.wr) :=
  (Covers.of_mem (fun _ h => List.mem_of_mem_take h)).append (Covers.refl _)

theorem fallback_run {s : State}
    (h : (Spec.Ffdh.checkDomainContract abi).pre (plain s)) :
    ∃ trace t, Exec isa VG.Impl.Ffdh.PPC64LE.Domain.checkDomain s trace t ∧
      abiPreserved s t ∧ (Spec.Ffdh.checkDomainContract abi).post s t := by
  obtain ⟨trace, t, run, preserved, post⟩ := Domain.cd_verified.1 (plain s) h
  have wide := VG.PPC64LE.Exec.widen run (rd := s.rd) (wr := s.wr)
    (plain_covers s) (Covers.refl _)
  refine ⟨trace, t.withRegions s.rd s.wr, ?_, preserved, post⟩
  simpa only [plain, stripConsts, State.withRegions_withRegions, State.withRegions_self] using wide

theorem fallback_ct :
    RelCT isa (fun s t =>
      (Spec.Ffdh.checkDomainContract abi).pre (plain s) ∧
      (Spec.Ffdh.checkDomainContract abi).pre (plain t) ∧
      (Spec.Ffdh.checkDomainContract abi).pub s t)
      VG.Impl.Ffdh.PPC64LE.Domain.checkDomain (fun _ _ => True) := by
  intro s t ts tt u w ⟨hs, ht, hp⟩ es et
  obtain ⟨ts', u', eu, _, _⟩ := Domain.cd_verified.1 (plain s) hs
  obtain ⟨tt', w', ew, _, _⟩ := Domain.cd_verified.1 (plain t) ht
  have eus : Exec isa VG.Impl.Ffdh.PPC64LE.Domain.checkDomain s ts' (u'.withRegions s.rd s.wr) := by
    simpa only [plain, stripConsts, State.withRegions_withRegions, State.withRegions_self] using
      (VG.PPC64LE.Exec.widen eu (rd := s.rd) (wr := s.wr) (plain_covers s) (Covers.refl _))
  have ewt : Exec isa VG.Impl.Ffdh.PPC64LE.Domain.checkDomain t tt' (w'.withRegions t.rd t.wr) := by
    simpa only [plain, stripConsts, State.withRegions_withRegions, State.withRegions_self] using
      (VG.PPC64LE.Exec.widen ew (rd := t.rd) (wr := t.wr) (plain_covers t) (Covers.refl _))
  have sameS := (Exec.det es eus).1
  have sameT := (Exec.det et ewt).1
  refine ⟨?_, True.intro⟩
  rw [sameS, sameT]
  exact Domain.cd_verified.2.1 _ _ _ _ _ _ hs ht hp eu ew

end VG.Proof.Ffdh.PPC64LE.VettedValidation

end

end


/-! Certified recognition success, with the complete original validator on every miss. -/

@[expose] public section
namespace VG.Proof.Ffdh.PPC64LE.VettedValidation
open VG VG.PPC64LE
open VG.Impl.Ffdh.PPC64LE.VettedValidation VG.Impl.Ffdh.VettedGroups

theorem Result.pre {s t : State} (h : Result s t) (pre : contract.pre s) :
    (Spec.Ffdh.checkDomainContract abi).pre (plain t) := by
  have base := (pre_plain pre).1
  sig_pre [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argRegs] at base ⊢
  rw [h.keep.gpr (r := .r3) (by decide), h.keep.gpr (r := .r4) (by decide),
    h.keep.gpr (r := .r5) (by decide), h.keep.gpr (r := .r6) (by decide),
    h.keep.gpr (r := .r7) (by decide), h.keep.2.1, h.keep.2.2]
  exact base

private theorem post_shared {s t : State} (h : Domain.cdContract.post s t) : contract.post s t := by
  change (Spec.Ffdh.checkDomainContract abi).post s t
  sig_post [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argRegs]
  exact h

theorem correct (s : State) (pre : contract.pre s) :
    WP isa code s fun t => abiPreserved s t ∧ contract.post s t := by
  rw [code, WP.seq_iff]
  obtain ⟨tr, u, run, result⟩ := recognize_ok pre
  refine ⟨tr, u, run, ?_⟩
  have sp : u.sp = s.sp := Exec.sp run
  have preserved : abiPreserved s u := ⟨fun r hr => result.keep.gpr (by revert r; decide), sp, result.lr⟩
  refine WP.ite (recognized s != 0) (by
    rw [VG.Proof.RsaPkcs1Sig.PPC64LE.eval_nonzero, result.value]) ?_ ?_
  · intro hit
    have nonzero : recognized s ≠ 0 := by simpa only [bne_iff_ne] using hit
    have raw : recognizeList groups (s.gpr .r5).toNat (domain s) ≠ 0 := by
      intro bad
      exact nonzero (by unfold recognized; rw [bad]; rfl)
    have valid := VG.Proof.Ffdh.VettedValidation.recognized_domain_valid groups
      (fun _ hg => hg) (context pre).shape raw
    refine VG.Proof.RsaPkcs1Sig.PPC64LE.wp_li (by decide) fun t only value =>
      VG.Proof.RsaPkcs1Sig.PPC64LE.wp_nil ⟨?_, post_shared ?_⟩
    · exact ⟨fun r hr => (only.gpr r (by revert r; decide)).trans (preserved.1 r hr),
        only.sp.trans preserved.2.1, only.lr.trans preserved.2.2⟩
    · change ((t.gpr .r3).setWidth 32).toNat = if Spec.Ffdh.domainValid
        (s.gpr .r5).toNat (domain s) then 1 else 0
      rw [value, valid]
      rfl
  · intro _
    obtain ⟨tr, t, run, kept, post⟩ := fallback_run (result.pre pre)
    refine ⟨tr, t, run, ⟨fun r hr => (kept.1 r hr).trans (preserved.1 r hr),
      kept.2.1.trans preserved.2.1, kept.2.2.trans preserved.2.2⟩, ?_⟩
    change (Spec.Ffdh.checkDomainContract abi).post s t
    change (Spec.Ffdh.checkDomainContract abi).post u t at post
    sig_post [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argRegs] at post ⊢
    rw [result.keep.gpr (r := .r3) (by decide), result.keep.gpr (r := .r4) (by decide),
      result.keep.gpr (r := .r5) (by decide), result.mem] at post
    exact post

end VG.Proof.Ffdh.PPC64LE.VettedValidation

end

end

/-! ### `Ffdh.PPC64LE.VettedValidation.PublicState`, which only this module used -/

section

/-! Public anchors allow unrelated scratch contents and link-register values. -/

@[expose] public section
namespace VG.Proof.Ffdh.PPC64LE.VettedValidation
open VG VG.PPC64LE
open VG.Impl.Ffdh.PPC64LE.VettedValidation

def publicRegs : List Reg := [.r3, .r4, .r5, .r6, .r7]

structure Start (a s : State) : Prop where
  pre : contract.pre s
  regs : ∀ r ∈ publicRegs, s.gpr r = a.gpr r
  domain : domain s = domain a
  symbol : s.syms tableSym = a.syms tableSym
  sp : s.sp = a.sp

private theorem singleton_sym {name : String} {words : List (BitVec 64)} {s t : State}
    (h : ∀ c ∈ [(name, words)], s.syms c.1 = t.syms c.1) :
    s.syms name = t.syms name := h (name, words) List.mem_cons_self

theorem start_of_pub {a s : State} (hs : contract.pre s) (hp : contract.pub a s) : Start a s := by
  have relation : (Spec.Ffdh.checkDomainContract abi).pub a s ∧
      ∀ c ∈ tableConsts, a.syms c.1 = s.syms c.1 := pub_consts.mp hp
  have symbols := singleton_sym (name := tableSym) (words := VG.Impl.Ffdh.VettedGroups.tableWords) relation.2
  have pubBase := relation.1
  sig_pub [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argRegs] at pubBase
  obtain ⟨sp, bytes, r3, r4, r5, r6, r7⟩ := pubBase
  refine ⟨hs, ?_, ?_, symbols.symm, sp.symm⟩
  · intro r hr
    simp only [publicRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact r3.symm
    · exact r4.symm
    · exact r5.symm
    · exact r6.symm
    · exact r7.symm
  · have byteEq := congrArg (List.map (BitVec.ofNat 8)) bytes
    simp only [List.map_map, Function.comp_def, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, List.map_id'] at byteEq
    exact byteEq.symm

def After (a t : State) : Prop := ∃ s, Start a s ∧ Result s t ∧ t.sp = s.sp

theorem After.pre {a t : State} (h : After a t) :
    (Spec.Ffdh.checkDomainContract abi).pre (plain t) := by
  obtain ⟨s, start, result, _⟩ := h
  exact result.pre start.pre

theorem After.regs {a t : State} (h : After a t) : ∀ r ∈ publicRegs, t.gpr r = a.gpr r := by
  obtain ⟨s, start, result, _⟩ := h
  intro r hr
  exact (result.keep.gpr (by revert r; decide)).trans (start.regs r hr)

theorem After.sp {a t : State} (h : After a t) : t.sp = a.sp := by
  obtain ⟨s, start, _, sp⟩ := h
  exact sp.trans start.sp

theorem After.domain_eq {a t : State} (h : After a t) : domain t = domain a := by
  obtain ⟨s, start, result, _⟩ := h
  unfold domain
  rw [result.mem, result.keep.gpr (r := .r3) (by decide), result.keep.gpr (r := .r4) (by decide)]
  exact start.domain

theorem After.public {a s t : State} (hs : After a s) (ht : After a t) :
    (Spec.Ffdh.checkDomainContract abi).pub s t := by
  sig_pub [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argRegs]
  refine ⟨hs.sp.trans ht.sp.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (domain s).map (·.toNat) = (domain t).map (·.toNat)
    rw [hs.domain_eq, ht.domain_eq]
  all_goals exact (hs.regs _ (by decide)).trans (ht.regs _ (by decide)).symm

end VG.Proof.Ffdh.PPC64LE.VettedValidation

end

end


/-! Link-register preservation adds no secret-dependent trace to the public scan. -/

@[expose] public section
namespace VG.Proof.Ffdh.PPC64LE.VettedValidation
open VG VG.PPC64LE
open VG.Impl.Ffdh.PPC64LE.VettedValidation VG.Impl.Ffdh.VettedGroups

theorem recognize_ct (a : State) :
    RelCT isa (fun s t => Start a s ∧ Start a t) recognize (fun _ _ => True) := by
  let Q := fun s : State => Context (a.gpr .r3) (a.gpr .r5).toNat (domain a) s ∧
    s.syms tableSym = a.syms tableSym ∧ TableAt (a.syms tableSym) groups s ∧ s.sp = a.sp
  have entryCT : RelCT isa (fun s t => Start a s ∧ Start a t)
      (.block [.mflr .r12]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t h
    exact ⟨h.1.sp.trans h.2.sp.symm, by simp [Taint.ofRegs]⟩
  have entryWP (s : State) (h : Start a s) : WP isa (.block [.mflr .r12]) s Q := by
    refine WP.mono_syms (VG.Proof.RsaPkcs1Sig.PPC64LE.wp_mflr
      (Q := fun t : State => VG.Proof.RsaPkcs1Sig.PPC64LE.Only [.r12] s t)
      (fun t only _ => VG.Proof.RsaPkcs1Sig.PPC64LE.wp_nil only)) ?_
    intro t only sym
    have input := context h.pre
    have ctx : Context (s.gpr .r3) (s.gpr .r5).toNat (domain s) t :=
      ⟨(only.get .r3).trans input.source, (only.get .r4).trans input.length,
        (only.get .r5).trans input.width, by rw [only.rd, only.wr]; exact input.read,
        by rw [only.mem]; exact input.bytes, input.shape, input.lower, input.upper⟩
    rw [h.regs .r3 (by decide), h.regs .r5 (by decide), h.domain] at ctx
    have table := (consts_table (pre_plain h.pre).2).after only.mem
      (show Keep [.r12] s t from ⟨only.gpr, only.rd, only.wr⟩)
    rw [h.symbol] at table
    exact ⟨ctx, (congrFun sym tableSym).trans h.symbol, table, only.sp.trans h.sp⟩
  have fit : 0 + (groups.flatMap Group.bytes).length ≤ 17744 := by
    simpa only [Nat.zero_add, tableBytes] using
      (Nat.le_of_eq VG.Proof.Ffdh.VettedTableFacts.tableBytes_length)
  have valid : ∀ g ∈ groups, g.len < 2 ^ 15 := by
    intro g hg
    simp only [groups, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have scanning := (scan_ct (src := a.gpr .r3) (table := a.syms tableSym)
    (stack := a.sp) (k := (a.gpr .r5).toNat) (dom := domain a) groups 0 fit valid).mono
    (P' := fun s t => Q s ∧ Q t)
    (fun _ _ h => by simpa only [BitVec.add_zero] using h) (fun _ _ h => h)
  have scanStage := ((entryCT.wp (fun s t h => ⟨entryWP s h.1, entryWP t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2⟩)).seq scanning
  have restoreCT : RelCT isa (fun _ _ => True) (.block [.mtlr .r12]) (fun _ _ => True) := by
    intro s t ts tt u v _ es et
    have niltrace {s t : State} {tr : List Leak} (e : Exec isa (.block [.mtlr .r12]) s tr t) : tr = [] := by
      cases e with
      | block e =>
        simp only [execBlock, isa, exec, addrs, Option.map_some,
          Option.some.injEq, Prod.mk.injEq] at e
        exact e.2.symm
    exact ⟨(niltrace es).trans (niltrace et).symm, trivial⟩
  unfold recognize
  exact (scanStage.seq restoreCT).assoc

end VG.Proof.Ffdh.PPC64LE.VettedValidation

end

end

/-! The success branch and complete fallback obey the original public-domain timing policy. -/

@[expose] public section
namespace VG.Proof.Ffdh.PPC64LE.VettedValidation
open VG VG.PPC64LE
open VG.Impl.Ffdh.PPC64LE.VettedValidation

theorem Start.recognized_eq {a s : State} (h : Start a s) : recognized s = recognized a := by
  unfold recognized
  rw [h.regs .r5 (by decide), h.domain]

theorem After.value {a t : State} (h : After a t) : t.gpr .r8 = recognized a := by
  obtain ⟨s, start, result, _⟩ := h
  exact result.value.trans start.recognized_eq

theorem anchored_ct (a : State) :
    RelCT isa (fun s t => Start a s ∧ Start a t) code (fun _ _ => True) := by
  have scanWP (s : State) (h : Start a s) : WP isa recognize s (After a) :=
    WP.mono (withSp (recognize_ok h.pre)) (fun t ⟨result, sp⟩ => ⟨s, h, result, sp⟩)
  have scanStage : RelCT isa (fun s t => Start a s ∧ Start a t) recognize
      (fun s t => After a s ∧ After a t) := ((recognize_ct a).wp
        (fun s t h => ⟨scanWP s h.1, scanWP t h.2⟩)).mono
          (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2⟩)
  have choice : RelCT isa (fun s t => After a s ∧ After a t)
      (.ite (.nonzero .d .r8) (.block [.li .r3 1]) VG.Impl.Ffdh.PPC64LE.Domain.checkDomain)
      (fun _ _ => True) := by
    apply RelCT.ite (fun s t h => by
      rw [VG.Proof.RsaPkcs1Sig.PPC64LE.eval_nonzero, VG.Proof.RsaPkcs1Sig.PPC64LE.eval_nonzero,
        h.1.value, h.2.value])
    · apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
      intro s t h
      exact ⟨h.1.1.sp.trans h.1.2.sp.symm, by simp [Taint.ofRegs]⟩
    · exact fallback_ct.mono (fun _ _ h => ⟨h.1.1.pre, h.1.2.pre, After.public h.1.1 h.1.2⟩)
        (fun _ _ h => h)
  exact scanStage.seq choice

theorem constantTime : ConstantTime isa contract.pre contract.pub code := by
  intro s t ts tt u w hs ht hp es et
  have left : Start s s := ⟨hs, fun _ _ => rfl, rfl, rfl, rfl⟩
  exact (anchored_ct s s t ts tt u w ⟨left, start_of_pub ht hp⟩ es et).1

end VG.Proof.Ffdh.PPC64LE.VettedValidation

end

end

/-! ### `Ffdh.PPC64LE.VettedValidation.Sat`, which only this module used -/

section

/-! A concrete PPC64LE caller satisfies the unchanged signature with the shared constants. -/

@[expose] public section
namespace VG.Proof.Ffdh.PPC64LE.VettedValidation
open VG VG.PPC64LE
open VG.Impl.Ffdh.PPC64LE.VettedValidation
open VG.Impl.Ffdh.VettedGroups

private def satState (words : List (BitVec 64)) : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 128 | .r5 => 64 | .r6 => 0x4000 | .r7 => 1056
    | _ => 0
  sp := 0x8000
  lr := 0
  mem := constMem 0x100000 words
  rd := [⟨0x1000, 128⟩, ⟨0x100000, 17744⟩]
  wr := [⟨0x4000, 8448⟩]
  syms _ := 0x100000

private theorem satPre (words : List (BitVec 64)) :
    (Spec.Ffdh.checkDomainContract abi).pre (stripConsts [(tableSym, words)] (satState words)) := by
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
    (⟨0x100000, 17744⟩ : Region).Disjoint ⟨0x4000, 8448⟩ := by
  exact ⟨by decide, Region.disjoint_of_sep (by decide)⟩

private theorem satRegions (words : List (BitVec 64)) (size : words.length = 2218) :
    ∀ r ∈ constRegs [(tableSym, words)] (satState words),
      r.base.toNat + r.len ≤ 2 ^ abi.ptrBits ∧
      (∀ q ∈ (satState words).wr, r.Disjoint q) ∧
      ∀ q ∈ abi.reserved 0 (satState words), r.Disjoint q := by
  intro r hr
  simp only [constRegs, Abi.constRegions, List.mem_map, List.mem_singleton] at hr
  obtain ⟨c, rfl, rfl⟩ := hr
  rw [size]
  refine ⟨fixedGeometry.1, ?_, ?_⟩
  · intro q hq
    change q ∈ ([⟨0x4000, 8448⟩] : List Region) at hq
    obtain rfl := List.mem_singleton.mp hq
    exact fixedGeometry.2
  · intro q hq
    change q ∈ ([] : List Region) at hq
    contradiction

private theorem satConsts (words : List (BitVec 64)) (size : words.length = 2218) :
    ConstsOk [(tableSym, words )] 0 (satState words) :=
  ⟨satLayout words size, satHeld words size, satRegions words size, fun r hr => by
    simp only [constRegs, Abi.constRegions, List.mem_map, List.mem_singleton] at hr
    obtain ⟨c, rfl, rfl⟩ := hr
    exact (by decide : (0x100000 : BitVec 64).toNat % 64 = 0)⟩

private theorem satAux (words : List (BitVec 64)) (size : words.length = 2218) :
    ∃ s, (Spec.Ffdh.checkDomainContract (abi.withConsts [(tableSym, words)])).pre s :=
  ⟨satState words, pre_consts.mpr ⟨satPre words, satConsts words size⟩⟩

theorem sat : ∃ s, contract.pre s :=
  satAux tableWords VG.Proof.Ffdh.VettedTableFacts.tableWords_length

end VG.Proof.Ffdh.PPC64LE.VettedValidation

end

end

/-! Exact certified imports share the original validation, timing, and ABI contract. -/

@[expose] public section
namespace VG.Proof.Ffdh.PPC64LE.VettedValidation
open VG VG.PPC64LE

theorem verified : Verified target VG.Impl.Ffdh.PPC64LE.VettedValidation.code contract :=
  ⟨correct, constantTime, sat⟩

end VG.Proof.Ffdh.PPC64LE.VettedValidation
