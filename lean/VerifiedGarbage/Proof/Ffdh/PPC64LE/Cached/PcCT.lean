module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Body
import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Cut
import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.ScalarEq
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.AttemptCorrect
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Body
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Cut
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.PcBody
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.VettedValidation.Recognize
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckDomainFn
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicFn
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckDomainCT
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.VettedValidation.Geometry
import VerifiedGarbage.Proof.Ffdh.VettedTableFacts
import VerifiedGarbage.Proof.Ffdh.GenerationPrecompute
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Ffdh.PPC64LE.Cached
public import VerifiedGarbage.Impl.Ffdh.PPC64LE.VettedValidation
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
import VerifiedGarbage.Proof.Ffdh.CachedSat
import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
meta import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Ffdh.PPC64LE.VettedValidation.ScanTiming
meta import VerifiedGarbage.Impl.Ffdh.PPC64LE.VettedValidation
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.PcBody
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.VettedValidation.Recognize
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckDomainFn
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicFn
meta import VerifiedGarbage.Proof.Mont.Words
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckDomainCT
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.VettedValidation.Geometry
meta import VerifiedGarbage.Proof.Ffdh.VettedTableFacts
meta import VerifiedGarbage.Proof.Ffdh.GenerationPrecompute
meta import VerifiedGarbage.Proof.Ffdh.Domain
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Impl.Ffdh.PPC64LE.Cached
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
meta import VerifiedGarbage.Proof.Ffdh.CachedSat
meta import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.VettedValidation.ScanTiming

/-! ### `Ffdh.PPC64LE.Cached.PcCorrect`, which only this module used -/

section

/-! ### `Ffdh.PPC64LE.Cached.PcRecog`, which only this module used -/

section

/-! # The vetted groups' recognition on PPC64LE, from its context and table

`recognize_ok` and `recognize_ct` of `VettedValidation` with what they read
of `vg_ffdh_check_domain`'s precondition as hypotheses: the domain's context
(`Context`) and the table, for a caller other than `vg_ffdh_check_domain`. -/

@[expose] public section
namespace VG.Proof.Ffdh.PPC64LE.VettedValidation
open VG VG.PPC64LE
open VG.Impl.Ffdh.PPC64LE.VettedValidation VG.Impl.Ffdh.VettedGroups

/-- `recognize`: `r8 :=` the domain's recognized width. -/
theorem recognize_ok' {s : State} {src : Addr} {k : Nat} {dom : List Byte} (input : Context src k dom s)
    (table : TableAt (s.syms tableSym) groups s) :
    WP isa recognize s fun t =>
      t.gpr .r8 = BitVec.ofNat 64 (recognizeList groups k dom) ∧ t.mem = s.mem ∧ Keep allClobbers s t ∧
        t.lr = s.lr := by
  have fit : 0 + (groups.flatMap Group.bytes).length ≤ 17744 := by
    simpa only [Nat.zero_add, tableBytes] using
      (Nat.le_of_eq VG.Proof.Ffdh.VettedTableFacts.tableBytes_length)
  rw [recognize, WP.seq_iff]
  refine WP.mono_syms (VG.Proof.RsaPkcs1Sig.PPC64LE.wp_mflr
    (Q := fun u : State => VG.Proof.RsaPkcs1Sig.PPC64LE.Only [.r12] s u ∧ u.gpr .r12 = s.lr)
    (fun u o saved => VG.Proof.RsaPkcs1Sig.PPC64LE.wp_nil ⟨o, saved⟩)) ?_
  rintro u ⟨only, saved⟩ symU
  rw [WP.seq_iff]
  refine WP.mono (scan_ok (src := src) (table := s.syms tableSym) (k := k) (dom := dom) groups 0 u ?_ ?_ ?_ fit) ?_
  · exact ⟨(only.get .r3).trans input.source, (only.get .r4).trans input.length,
      (only.get .r5).trans input.width, by rw [only.rd, only.wr]; exact input.read,
      by rw [only.mem]; exact input.bytes, input.shape, input.lower, input.upper⟩
  · rw [symU]
  · have after := table.after only.mem (show Keep [.r12] s u from ⟨only.gpr, only.rd, only.wr⟩)
    rw [symU] at *
    simpa only [BitVec.add_zero] using after
  · rintro v ⟨value, memV, restV⟩
    refine VG.Proof.RsaPkcs1Sig.PPC64LE.wp_mtlr fun w regs memW rdW wrW spW lrW =>
      VG.Proof.RsaPkcs1Sig.PPC64LE.wp_nil ⟨by rw [regs, value], memW.trans (memV.trans only.mem), ?_,
        by rw [lrW, restV.gpr (by decide), saved]⟩
    refine ⟨?_, rdW.trans (restV.2.1.trans only.rd), wrW.trans (restV.2.2.trans only.wr)⟩
    intro r hr
    rw [regs, restV.gpr (by intro hc; exact hr (List.mem_cons_of_mem _ hc)),
      only.gpr r (by simpa only [allClobbers, List.mem_cons, List.not_mem_nil, or_false] using
        (fun eq : r = .r12 => hr (by rw [eq]; exact List.mem_cons_self))) ]

/-- What `recognize`'s timing depends on. -/
def RI (src : Addr) (k : Nat) (dom : List Byte) (tbl stack : Addr) (s : State) : Prop :=
  Context src k dom s ∧ s.syms tableSym = tbl ∧ TableAt tbl groups s ∧ s.sp = stack

theorem recognize_ct' (src : Addr) (k : Nat) (dom : List Byte) (tbl stack : Addr) :
    RelCT isa (fun s t => RI src k dom tbl stack s ∧ RI src k dom tbl stack t) recognize (fun _ _ => True) := by
  let Q := fun s : State => Context src k dom s ∧ s.syms tableSym = tbl ∧ TableAt tbl groups s ∧ s.sp = stack
  have entryCT : RelCT isa (fun s t => RI src k dom tbl stack s ∧ RI src k dom tbl stack t)
      (.block [.mflr .r12]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t h
    exact ⟨h.1.2.2.2.trans h.2.2.2.2.symm, by simp [Taint.ofRegs]⟩
  have entryWP (s : State) (h : RI src k dom tbl stack s) : WP isa (.block [.mflr .r12]) s Q := by
    refine WP.mono_syms (VG.Proof.RsaPkcs1Sig.PPC64LE.wp_mflr
      (Q := fun t : State => VG.Proof.RsaPkcs1Sig.PPC64LE.Only [.r12] s t)
      (fun t only _ => VG.Proof.RsaPkcs1Sig.PPC64LE.wp_nil only)) ?_
    intro t only sym
    obtain ⟨input, hsym, table, hsp⟩ := h
    have ctx : Context src k dom t :=
      ⟨(only.get .r3).trans input.source, (only.get .r4).trans input.length,
        (only.get .r5).trans input.width, by rw [only.rd, only.wr]; exact input.read,
        by rw [only.mem]; exact input.bytes, input.shape, input.lower, input.upper⟩
    exact ⟨ctx, (congrFun sym tableSym).trans hsym,
      table.after only.mem (show Keep [.r12] s t from ⟨only.gpr, only.rd, only.wr⟩), only.sp.trans hsp⟩
  have fit : 0 + (groups.flatMap Group.bytes).length ≤ 17744 := by
    simpa only [Nat.zero_add, tableBytes] using
      (Nat.le_of_eq VG.Proof.Ffdh.VettedTableFacts.tableBytes_length)
  have valid : ∀ g ∈ groups, g.len < 2 ^ 15 := by
    intro g hg
    simp only [groups, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have scanning := (scan_ct (src := src) (table := tbl)
    (stack := stack) (k := k) (dom := dom) groups 0 fit valid).mono
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

/-! ### `Ffdh.PPC64LE.Cached.PcFn`, which only this module used -/

section

/-!
# `vg_ffdh_generate_key_precompute` on PPC64LE: the function

`vg_ffdh_generate_key_precompute(ctx = r3, ctx_len = r4, domain = r5,
domain_len = r6, p_len = r7, scratch = r8, scratch_len = r9)`, with the
vetted groups' table (`pcContract`), and the shared contract
(`pc_implies`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Cached

open VG VG.PPC64LE
open VG.Impl.Ffdh.PPC64LE.VettedValidation (tableSym tableConsts)

/-- The context's region. -/
abbrev pcCtx (s : State) : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat * 8⟩

/-- The domain's region. -/
abbrev pcDomR (s : State) : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩

/-- The working space's region. -/
abbrev pcScr (s : State) : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat * 8⟩

/-- The domain's bytes. -/
abbrev pcDom (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat

def pcPre (s : State) : Prop :=
  s.rd = [pcDomR s] ∧ s.wr = [pcCtx s, pcScr s] ∧ (pcCtx s).Disjoint (pcDomR s) ∧
    (pcCtx s).Disjoint (pcScr s) ∧ (pcDomR s).Disjoint (pcScr s) ∧
    (s.gpr .r3).toNat + (s.gpr .r4).toNat * 8 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + (s.gpr .r9).toNat * 8 ≤ 2 ^ 64 ∧
    Spec.Ffdh.pLenValid (s.gpr .r7).toNat ∧ Spec.Ffdh.domainLenValid (s.gpr .r7).toNat (s.gpr .r6).toNat ∧
    (s.gpr .r4).toNat = Spec.Ffdh.generationPrecomputedWords (s.gpr .r7).toNat ∧
    Spec.Rsa.scratchWords (s.gpr .r7).toNat ≤ (s.gpr .r9).toNat ∧
    Spec.Ffdh.domainValid (s.gpr .r7).toNat (pcDom s)

def pcPost (s t : State) : Prop :=
  (t.gpr .r3).setWidth 32 = 1 ∧
    Spec.Ffdh.generationPrecompute (s.gpr .r7).toNat (pcDom s) = some (Spec.Rsa.wordsAt t.mem (s.gpr .r3) (s.gpr .r4).toNat)

def pcPub (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ (pcDom s₁).map (·.toNat) = (pcDom s₂).map (·.toNat) ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.gpr .r6 = s₂.gpr .r6 ∧
    s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9

/-- `vg_ffdh_generate_key_precompute`, with the vetted groups' table. -/
def pcContract : Contract isa where
  pre s := pcPre (stripConsts tableConsts s) ∧ ConstsOk tableConsts 0 s
  post := pcPost
  pub s₁ s₂ := pcPub s₁ s₂ ∧ s₁.syms tableSym = s₂.syms tableSym

theorem pc_pre0 {s : State} (h : (Spec.Ffdh.generationPrecomputeContract abi).pre s) : pcPre s := by
  sig_pre [Spec.Ffdh.generationPrecomputeContract, Spec.Ffdh.generationPrecomputeSig, abi, argRegs,
    List.append_eq, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid] at h
  sig_split h
  sig_reduce [pcPre, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid]
  sig_and_intros
  sig_close
  all_goals first | with_reducible assumption | sig_disjoint_symm | omega

theorem pc_post0 {s t : State} (h : pcPost s t) : (Spec.Ffdh.generationPrecomputeContract abi).post s t := by
  sig_post [Spec.Ffdh.generationPrecomputeContract, Spec.Ffdh.generationPrecomputeSig, abi, argRegs,
    List.append_eq]
  sig_reduce [pcPost, pcDom] at h
  exact h

theorem pc_pub0 {s₁ s₂ : State} (h : (Spec.Ffdh.generationPrecomputeContract abi).pub s₁ s₂) : pcPub s₁ s₂ := by
  sig_pub [Spec.Ffdh.generationPrecomputeContract, Spec.Ffdh.generationPrecomputeSig, abi, argRegs,
    List.append_eq, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid] at h
  exact h

/-! ## A caller meeting the contract -/

/-- The domain at `0x3000` and a table of `words` at `0x100000`. -/
private def pcSatMem (words : List (BitVec 64)) (a : Addr) : Byte :=
  if (a - 0x100000).toNat < 17744 then constMem 0x100000 words a else CachedSat.domainMem a

/-- The context at `0x200000`, the working space at `0x4000`. -/
private def pcSatState (words : List (BitVec 64)) : State where
  gpr r := match r with
    | .r3 => 0x200000 | .r4 => 275 | .r5 => 0x3000 | .r6 => 128 | .r7 => 64 | .r8 => 0x4000 | .r9 => 1056
    | _ => 0
  sp := 0x8000
  lr := 0
  mem := pcSatMem words
  rd := [⟨0x3000, 128⟩, ⟨0x100000, 17744⟩]
  wr := [⟨0x200000, 2200⟩, ⟨0x4000, 8448⟩]
  syms _ := 0x100000

private theorem pcSat_domain (words : List (BitVec 64)) :
    Spec.Rsa.bytesAt (pcSatState words).mem 0x3000 128 = CachedSat.domain := by
  apply CachedSat.bytesAt_eq
  intro i hi
  show pcSatMem words _ = _
  unfold pcSatMem
  apply ite_eq_right
  have : ∀ i < 128, ¬ ((0x3000 : BitVec 64) + BitVec.ofNat 64 i - 0x100000).toNat < 17744 := by decide
  exact this i hi

private theorem pcSat_pre (words : List (BitVec 64)) :
    (Spec.Ffdh.generationPrecomputeContract abi).pre (stripConsts [(tableSym, words)] (pcSatState words)) := by
  sig_pre [Spec.Ffdh.generationPrecomputeContract, Spec.Ffdh.generationPrecomputeSig, abi, argRegs,
    List.append_eq, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid, Spec.Rsa.scratchWords]
  refine ⟨rfl, rfl, Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, ?_⟩
  change Spec.Ffdh.domainValid 64 (Spec.Rsa.bytesAt (pcSatState words).mem 0x3000 128) = true
  rw [pcSat_domain]; exact CachedSat.domain_valid

private theorem pcGeometry :
    (0x100000 : Addr).toNat + 8 * 2218 ≤ 2 ^ 64 ∧
    (⟨0x100000, 8 * 2218⟩ : Region).Disjoint ⟨0x200000, 2200⟩ ∧
    (⟨0x100000, 8 * 2218⟩ : Region).Disjoint ⟨0x4000, 8448⟩ :=
  ⟨by decide, Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide)⟩

private theorem pcSat_consts (words : List (BitVec 64)) (size : words.length = 2218) :
    ConstsOk [(tableSym, words)] 0 (pcSatState words) := by
  refine ⟨?_, ?_, ?_, fun r hr => ?_⟩
  · simp only [constRegs, Abi.constRegions, pcSatState, List.map_cons, List.map_nil, size]
    rfl
  · intro c hc i hi
    obtain rfl := List.mem_singleton.mp hc
    rw [← constMem_held 0x100000 words (by rw [size]; decide) i hi]
    apply Mem.readW_congr
    intro j hj
    show pcSatMem words _ = _
    unfold pcSatMem
    apply ite_eq_left
    have hi' : i < 2218 := by rw [← size]; exact hi
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    change ((0x100000 : BitVec 64) + BitVec.ofNat 64 (8 * i + j) - 0x100000).toNat < 17744
    rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
    omega_using [hj, hi']
  · intro r hr
    simp only [constRegs, Abi.constRegions, List.mem_map, List.mem_singleton] at hr
    obtain ⟨c, rfl, rfl⟩ := hr
    rw [size]
    refine ⟨pcGeometry.1, fun q hq => ?_, fun q hq => ?_⟩
    · change q ∈ ([⟨0x200000, 2200⟩, ⟨0x4000, 8448⟩] : List Region) at hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact pcGeometry.2.1
      · exact pcGeometry.2.2
    · change q ∈ ([] : List Region) at hq
      contradiction
  · simp only [constRegs, Abi.constRegions, List.mem_map, List.mem_singleton] at hr
    obtain ⟨c, rfl, rfl⟩ := hr
    exact (by decide : (0x100000 : BitVec 64).toNat % 64 = 0)

private theorem pcSatAux (words : List (BitVec 64)) (size : words.length = 2218) :
    ∃ s, (Spec.Ffdh.generationPrecomputeContract (abi.withConsts [(tableSym, words)])).pre s :=
  ⟨pcSatState words, pre_consts.mpr ⟨pcSat_pre words, pcSat_consts words size⟩⟩

theorem precompute_sat : ∃ s, (Spec.Ffdh.generationPrecomputeContract (abi.withConsts tableConsts)).pre s :=
  pcSatAux VG.Impl.Ffdh.VettedGroups.tableWords VG.Proof.Ffdh.VettedTableFacts.tableWords_length

theorem pc_implies : pcContract.Implies (Spec.Ffdh.generationPrecomputeContract (abi.withConsts tableConsts)) where
  pre s h := by
    obtain ⟨hp, hc⟩ := pre_consts.mp h
    exact ⟨pc_pre0 hp, hc⟩
  post _ _ _ h := post_consts.mpr (pc_post0 h)
  pub _ _ _ _ h := ⟨pc_pub0 (pub_consts.mp h).1, (pub_consts.mp h).2 _ List.mem_cons_self⟩
  sat := precompute_sat

end VG.Proof.Ffdh.PPC64LE.Cached

end

end

/-!
# `vg_ffdh_generate_key_precompute` on PPC64LE: correctness

`front` saves the registers in the working space and the context's pointer
in its header (`pc_front`); the domain is recognized (`recognize_ok'`) and
the width stored in the header; then the setup, p's check, which the
domain's validity passes, `main_ok`, and the registers restored
(`pc_correct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Cached

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain
open VG.Impl.Ffdh.PPC64LE.Cached VG.Impl.Ffdh.PPC64LE.Cached.Precompute
open VG.Proof.Ffdh.PPC64LE.Domain
open VG.Proof.Bignum (slot)
open VG.Impl.Ffdh.PPC64LE.VettedValidation (tableSym tableConsts)

/-- The bytes at `Q` apart from `[S, S + Z)`. -/
theorem bytes_out {m m' : Mem} {S : Addr} {Z : Nat} (hf : ∀ x, Z ≤ ofs S x → m' x = m x) {Q : Addr} {n : Nat}
    (hsep : ∀ i < n, ∀ x, ofs S x < Z → off Q i ≠ x) : Spec.Rsa.bytesAt m' Q n = Spec.Rsa.bytesAt m Q n := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => hf _ ?_
  by_contra hc
  exact hsep i (List.mem_range.mp hi) _ (by simp only [off]; omega_using [hc]) rfl

/-- What code ends in, with `sp` too. -/
theorem wp_sp {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun t => Q t ∧ t.sp = s.sp := by
  obtain ⟨tr, t, he, hq⟩ := h
  exact ⟨tr, t, he, hq, Exec.sp he⟩

/-- The context's pointer into the header, and the domain's arguments where
`recognize` reads them. -/
theorem pcHdr_ok {s : State} {S : Addr} (h23 : s.gpr .r23 = S) (hin : InRegions s.wr (off S 0) 8) :
    WP isa (.block [sth .r3 hCtx, .addi .r3 .r5 0, .addi .r4 .r6 0, .addi .r5 .r7 0]) s fun t =>
      (t.gpr .r3 = s.gpr .r5 ∧ t.gpr .r4 = s.gpr .r6 ∧ t.gpr .r5 = s.gpr .r7 ∧
        t.mem = s.mem.writeW (off S 0) (s.gpr .r3)) ∧ Bignum.PPC64LE.Keep [.r3, .r4, .r5] s t := by
  refine Bignum.PPC64LE.WP.keep _ ?_ (by decide)
  have i0 : InRegions s.wr (S + BitVec.ofNat 64 0) 8 := hin
  unfold sth
  prun [hCtx, h23, i0]
  simp

/-- `front`. -/
theorem pc_front {s : State} {S : Addr} {Z : Nat} (h8 : s.gpr .r8 = S) (hZ : 256 ≤ Z)
    (hin : ∀ i < 18, InRegions s.wr (off (savW S) (8 * i)) 8) (hin0 : InRegions s.wr (off S 0) 8) :
    WP isa (.block front) s fun t =>
      t.gpr .r23 = S ∧ t.gpr .r3 = s.gpr .r5 ∧ t.gpr .r4 = s.gpr .r6 ∧ t.gpr .r5 = s.gpr .r7 ∧
      word t.mem S 0 = s.gpr .r3 ∧ (∀ i < 18, word t.mem S (112 + 8 * i) = s.gpr (Impl.Ffdh.PPC64LE.Domain.saved i)) ∧
      (∀ x, Z ≤ ofs S x → t.mem x = s.mem x) ∧ Bignum.PPC64LE.Keep [.r23, .r3, .r4, .r5] s t := by
  unfold front
  refine WP.block_append (WP.mono (save_ok (ws := .r8) (by decide) s (by rw [h8]; exact hin)) fun s₁ hS => ?_)
  have h23 : s₁.gpr .r23 = S := hS.r23.trans h8
  refine WP.mono (pcHdr_ok h23 (by rw [hS.keep.wr]; exact hin0)) fun t ⟨⟨t3, t4, t5, tm⟩, kt⟩ => ?_
  have o := writeW_outside s₁.mem S (d := 0) (s₁.gpr .r3) (by omega_using [])
  rw [← tm] at o
  refine ⟨(kt.gpr .r23 (by decide)).trans h23, ?_, ?_, ?_, ?_, fun i hi => ?_, fun x hx => ?_, hS.keep.trans kt⟩
  · rw [t3, hS.keep.gpr .r5 (by decide)]
  · rw [t4, hS.keep.gpr .r6 (by decide)]
  · rw [t5, hS.keep.gpr .r7 (by decide)]
  · rw [tm, word_writeW_self, hS.keep.gpr .r3 (by decide)]
  · rw [o.word (by omega_using []) (by omega_using [hi])]
    have ea : off (savW S) (8 * i) = off S (112 + 8 * i) := by rw [off, off, Offset.add_add]
    rw [← hS.saved i hi, h8, ea]
  · rw [o x (.inr (by omega_using [hZ, hx]))]
    refine hS.frame x fun r hr hcx => ?_
    rw [List.mem_singleton] at hr
    subst hr
    rw [h8] at hcx
    have hc' := (Offset.sub_base (n := 144) (k := Z) S (d := 112) (by omega_using [hZ])) _ hcx
    simp only [Region.Contains] at hc'
    simp only [ofs] at hx
    omega_using [hx, hc']

/-- The width into the header. -/
theorem pcCap_ok {s : State} {S : Addr} (h23 : s.gpr .r23 = S) (hin : InRegions s.wr (off S 96) 8) :
    WP isa (.block [sth .r8 hCap]) s fun t => (t.mem = s.mem.writeW (off S 96) (s.gpr .r8)) ∧ Bignum.PPC64LE.Keep [] s t := by
  refine Bignum.PPC64LE.WP.keep _ ?_ (by decide)
  have i0 : InRegions s.wr (S + BitVec.ofNat 64 96) 8 := hin
  unfold sth
  prun [hCap, h23, i0]

/-- A table is apart from the writable regions. -/
theorem const_disjoint {K : List (String × List (BitVec 64))} {st : Nat} {s : State} {name : String}
    {ws : List (BitVec 64)} (h : ConstsOk K st s) (hc : (name, ws) ∈ K) :
    ∀ r ∈ s.wr, (⟨s.syms name, 8 * ws.length⟩ : Region).Disjoint r :=
  (h.2.2.1 ⟨s.syms name, 8 * ws.length⟩ (List.mem_map_of_mem (f := fun c =>
    (⟨s.syms c.1, 8 * c.2.length⟩ : Region)) hc)).2.1

/-- The table, in a state whose bytes apart from the working space are the
caller's. -/
theorem table_after {s t : State} {S : Addr} {Z : Nat} (hc : ConstsOk tableConsts 0 s)
    (hS : (⟨S, Z⟩ : Region) ∈ s.wr) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) (hsym : t.syms = s.syms)
    (hfr : ∀ x, Z ≤ ofs S x → t.mem x = s.mem x) :
    VettedValidation.TableAt (t.syms tableSym) VG.Impl.Ffdh.VettedGroups.groups t := by
  have hK : (tableSym, VG.Impl.Ffdh.VettedGroups.tableWords) ∈ tableConsts := List.mem_cons_self
  have dTS := const_disjoint hc hK _ hS
  rw [VG.Proof.Ffdh.VettedTableFacts.tableWords_length, show 8 * 2218 = 17744 by decide] at dTS
  have sepT := sep_of_disjoint (L := 17744) dTS (by decide)
  have tread := VettedValidation.consts_read hc
  have tbytes := VettedValidation.consts_bytes hc
  rw [hsym]
  apply VettedValidation.tableOfBytes _ _ t (by rw [hrd, hwr]; exact tread)
    (by rw [bytes_out hfr fun i hi => sepT i (by
        change i < VG.Impl.Ffdh.VettedGroups.tableBytes.length at hi
        rw [VG.Proof.Ffdh.VettedTableFacts.tableBytes_length] at hi; exact hi)]
        exact tbytes)
    (by change VG.Impl.Ffdh.VettedGroups.tableBytes.length ≤ 17744
        rw [VG.Proof.Ffdh.VettedTableFacts.tableBytes_length])
  intro g hg
  simp only [VG.Impl.Ffdh.VettedGroups.groups, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem pc_pres_not_written : ∀ r ∈ preserved, (∀ i < 18, r ≠ Impl.Ffdh.PPC64LE.Domain.saved i) →
    r ∉ ([.r23, .r3, .r4, .r5] : List Reg) ++ VettedValidation.allClobbers ++ (([] : List Reg) ++ setup0Regs) ++
      ([.r0, .r6, .r12, .r14, .r15, .r16, .r17, .r18] : List Reg) ++ mainRegs := by
  decide

/-! ## The public data and the stages

`pc_s1` … `pc_s5` run the code up to the registers' restoring, each from the
stage before; the constant-time proof uses them too. -/

/-- A run's public data: the context, the domain, the working space, `p_len`,
`domain_len`, the working space's size in bytes, the domain's bytes, the
table's address and the stack pointer. -/
structure PQ where
  C : Addr
  D : Addr
  S : Addr
  k : Nat
  L : Nat
  Z : Nat
  db : List Byte
  T : Addr
  sp : Addr

abbrev PQ.w (q : PQ) : Nat := (q.k + 7) / 8

/-- The recognized width. -/
abbrev PQ.cap (q : PQ) : Nat :=
  VG.Impl.Ffdh.VettedGroups.recognizeList VG.Impl.Ffdh.VettedGroups.groups q.k q.db

def pqOf (s : State) : PQ :=
  ⟨s.gpr .r3, s.gpr .r5, s.gpr .r8, (s.gpr .r7).toNat, (s.gpr .r6).toNat, (s.gpr .r9).toNat * 8,
    Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat, s.syms tableSym, s.sp⟩

/-- The domain's public data, as `vg_ffdh_check_domain`'s proof has it. -/
def PQ.cd (q : PQ) : CD := ⟨q.D, q.D, q.S, q.k, q.L, q.Z, q.db, q.db.take q.k⟩

/-- What the precondition gives. -/
structure Geo (q : PQ) (s : State) : Prop where
  r3 : s.gpr .r3 = q.C
  r4 : (s.gpr .r4).toNat = 3 + 34 * q.w
  r5 : s.gpr .r5 = q.D
  r6 : (s.gpr .r6).toNat = q.L
  r7 : (s.gpr .r7).toNat = q.k
  r8 : s.gpr .r8 = q.S
  wr : s.wr = [⟨q.C, (3 + 34 * q.w) * 8⟩, ⟨q.S, q.Z⟩]
  memD : (⟨q.D, q.L⟩ : Region) ∈ s.rd
  dCD : (⟨q.C, (3 + 34 * q.w) * 8⟩ : Region).Disjoint ⟨q.D, q.L⟩
  dCS : (⟨q.C, (3 + 34 * q.w) * 8⟩ : Region).Disjoint ⟨q.S, q.Z⟩
  dDS : (⟨q.D, q.L⟩ : Region).Disjoint ⟨q.S, q.Z⟩
  nwC : q.C.toNat + (3 + 34 * q.w) * 8 ≤ 2 ^ 64
  nwD : q.D.toNat + q.L ≤ 2 ^ 64
  nwS : q.S.toNat + q.Z ≤ 2 ^ 64
  hk : 64 ≤ q.k
  hk' : q.k ≤ 1024
  hL : q.L = 2 * q.k ∨ q.L = 3 * q.k
  hZw : slot q.w 28 ≤ q.Z
  dom : Spec.Rsa.bytesAt s.mem q.D q.L = q.db
  dv : Spec.Ffdh.domainValid q.k q.db = true
  tab : ∀ t : State, t.rd = s.rd → t.wr = s.wr → t.syms = s.syms → (∀ x, q.Z ≤ ofs q.S x → t.mem x = s.mem x) →
    VettedValidation.TableAt (t.syms tableSym) VG.Impl.Ffdh.VettedGroups.groups t
  syms : s.syms tableSym = q.T
  sp : s.sp = q.sp

theorem geo_of_pre {s : State} (h : pcContract.pre s) : Geo (pqOf s) s := by
  obtain ⟨⟨hrd, hwr, dCD, dCS, dDS, nwC, nwD, nwS, ⟨hk, hk'⟩, hL, hcl, hsl, hdv⟩, hc⟩ := h
  simp only [stripConsts_gpr, stripConsts_wr, pcCtx, pcDomR, pcScr] at hwr dCD dCS dDS nwC nwD nwS hrd
  simp only [stripConsts_gpr, stripConsts_mem, pcDom] at hk hk' hL hcl hsl hdv
  simp only [Spec.Rsa.scratchWords] at hsl
  have memD : (⟨s.gpr .r5, (s.gpr .r6).toNat⟩ : Region) ∈ s.rd := by
    have : (⟨s.gpr .r5, (s.gpr .r6).toNat⟩ : Region) ∈ (stripConsts tableConsts s).rd := by
      rw [hrd]; exact List.mem_singleton_self _
    exact List.mem_of_mem_take this
  have hcl' : (s.gpr .r4).toNat = 3 + 34 * (((s.gpr .r7).toNat + 7) / 8) := by
    rw [hcl]
    simp only [Spec.Ffdh.generationPrecomputedWords, Spec.Rsa.FixedBaseComb.precomputedWords,
      Spec.Rsa.precomputedWords, Spec.Rsa.FixedBaseComb.entries, Spec.Rsa.FixedBaseComb.teeth, Spec.Rsa.modulusWords]
    omega_using []
  rw [hcl'] at hwr dCD dCS nwC
  refine ⟨rfl, hcl', rfl, rfl, rfl, rfl, hwr, memD, dCD, dCS, dDS, nwC, nwD, nwS, hk, hk',
    by show (s.gpr .r6).toNat = 2 * (s.gpr .r7).toNat ∨ (s.gpr .r6).toNat = 3 * (s.gpr .r7).toNat
       simp only [Spec.Ffdh.domainLenValid] at hL; omega_using [hL], ?_, rfl, hdv,
    fun t => table_after (t := t) hc (by rw [hwr]; simp [pqOf]), rfl, rfl⟩
  show slot (((s.gpr .r7).toNat + 7) / 8) 28 ≤ (s.gpr .r9).toNat * 8
  rw [Domain.slot_eq]; omega_using [hsl, hk', hk]

theorem slot0 (w : Nat) : slot w 0 = 256 := by rw [Domain.slot_eq]; omega_using []

section Geo
variable {q : PQ} {s : State} (g : Geo q s)
include g

theorem Geo.hw4 : 4 ≤ q.w := by have := g.hk; simp only [PQ.w]; omega_using [this]
theorem Geo.hw' : q.w ≤ 128 := by have := g.hk'; simp only [PQ.w]; omega_using [this]
theorem Geo.hZ : 256 + 28 * (8 * (q.w + 2)) ≤ q.Z := by have := g.hZw; rw [Domain.slot_eq] at this; omega_using [this]
theorem Geo.hs : Scr s q.S q.Z := Scr.of_mem (by rw [g.wr]; simp) g.nwS
theorem Geo.hinS : ∀ d, d + 8 ≤ 256 → InRegions s.wr (off q.S d) 8 := fun d hd => by
  have := g.hZ; have := g.nwS
  exact ⟨⟨q.S, q.Z⟩, by rw [g.wr]; simp, Offset.contains_base q.S (by omega_arith) (by omega_using [hd])⟩
theorem Geo.hin : ∀ i < 18, InRegions s.wr (off (savW q.S) (8 * i)) 8 := fun i hi => by
  have := g.hZ; have := g.nwS
  exact ⟨⟨q.S, q.Z⟩, by rw [g.wr]; simp, by
    rw [off, Offset.add_add]; exact Offset.contains_base q.S (by omega_arith) (by omega_using [hi])⟩
theorem Geo.sepD : ∀ i < q.L, ∀ x, ofs q.S x < q.Z → off q.D i ≠ x :=
  sep_of_disjoint (L := q.L) g.dDS (by have := g.nwD; omega_using [this])
theorem Geo.sepDC : ∀ i < q.L, ∀ x, ofs q.C x < (3 + 34 * q.w) * 8 → off q.D i ≠ x :=
  sep_of_disjoint (L := q.L) g.dCD.symm (by have := g.nwD; omega_using [this])
theorem Geo.rdD : ∀ i < q.L, InRegions (s.rd ++ s.wr) (off q.D i) 1 :=
  rd_of_mem (s := s) (D := q.D) (L := q.L) g.memD (by have := g.nwD; omega_using [this])
theorem Geo.sepCB : ∀ x, ofs q.C x < 8 * (3 + 34 * q.w) → q.Z ≤ ofs q.S x := fun x hx => by
  have := Pub.sep_of_disjoint g.dCS x (by simp only [VG.Proof.Bignum.ofs, ofs] at hx ⊢; omega_using [hx])
  simp only [VG.Proof.Bignum.ofs, ofs] at this ⊢; omega_using [this]
theorem Geo.sepBC : ∀ x, ofs q.S x < q.Z → 8 * (3 + 34 * q.w) ≤ ofs q.C x := fun x hx => by
  have := Pub.sep_of_disjoint g.dCS.symm x (by simp only [VG.Proof.Bignum.ofs, ofs] at hx ⊢; omega_using [hx])
  simp only [VG.Proof.Bignum.ofs, ofs] at this ⊢; omega_using [this]
theorem Geo.hlen : q.db.length = q.L := by rw [← g.dom]; exact VG.Proof.Bignum.bytesAt_length _ _ _
theorem Geo.hmod : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (q.db.take q.k)) q.k = true :=
  VG.Proof.Ffdh.domainValid_mod g.dv
theorem Geo.hgen : Spec.Ffdh.generationPrecompute q.k q.db = some (VG.Proof.Ffdh.generationValues q.k q.db) :=
  VG.Proof.Ffdh.generationPrecompute_eq (by rw [g.hlen]; rcases g.hL with h | h <;> omega_using [h]) g.hmod

end Geo

/-- After `front`. -/
structure St1 (q : PQ) (s₀ s : State) : Prop where
  r23 : s.gpr .r23 = q.S
  r3 : s.gpr .r3 = q.D
  r4 : s.gpr .r4 = BitVec.ofNat 64 q.L
  r5 : s.gpr .r5 = BitVec.ofNat 64 q.k
  w0 : word s.mem q.S 0 = q.C
  sav : ∀ i < 18, word s.mem q.S (112 + 8 * i) = s₀.gpr (Impl.Ffdh.PPC64LE.Domain.saved i)
  fr : ∀ x, q.Z ≤ ofs q.S x → s.mem x = s₀.mem x
  keep : Bignum.PPC64LE.Keep [.r23, .r3, .r4, .r5] s₀ s
  syms : s.syms = s₀.syms

theorem pc_s1 {q : PQ} {s : State} (g : Geo q s) : WP isa (.block front) s (St1 q s) :=
  WP.mono_syms (pc_front (Z := q.Z) g.r8 (Nat.le_trans (Nat.le_add_right _ _) g.hZ) g.hin (g.hinS 0 (by decide)))
    fun _ ⟨a23, a3, a4, a5, w0, wsav, fr1, k1⟩ sym1 =>
      ⟨a23, a3.trans g.r5, by rw [a4, ← g.r6, BitVec.ofNat_toNat, BitVec.setWidth_eq],
        by rw [a5, ← g.r7, BitVec.ofNat_toNat, BitVec.setWidth_eq], w0.trans g.r3, wsav, fr1, k1, sym1⟩

/-- What `recognize` reads, after `front`. -/
theorem St1.ri {q : PQ} {s₀ s : State} (g : Geo q s₀) (h : St1 q s₀ s) :
    VettedValidation.RI q.D q.k q.db q.T q.sp s := by
  refine ⟨⟨h.r3, by rw [h.r4, g.hlen], h.r5, ?_, ?_, by rw [g.hlen]; exact g.hL, g.hk, g.hk'⟩,
    by rw [h.syms, g.syms], by rw [← g.syms, ← h.syms]; exact g.tab s h.keep.rd h.keep.wr h.syms h.fr,
    h.keep.sp.trans g.sp⟩
  · rw [g.hlen, h.keep.rd, h.keep.wr]
    exact ⟨_, List.mem_append_left _ g.memD, Region.contains_self _ _⟩
  · rw [g.hlen, bytes_out h.fr g.sepD, g.dom]

/-- After `recognize`. -/
def St2 (q : PQ) (s₀ s : State) : Prop :=
  ∃ s₁, St1 q s₀ s₁ ∧ s.gpr .r8 = BitVec.ofNat 64 q.cap ∧ s.mem = s₁.mem ∧
    Bignum.PPC64LE.Keep VettedValidation.allClobbers s₁ s

theorem pc_s2 {q : PQ} {s₀ s : State} (g : Geo q s₀) (h : St1 q s₀ s) :
    WP isa VG.Impl.Ffdh.PPC64LE.VettedValidation.recognize s (St2 q s₀) :=
  WP.mono (wp_sp (VettedValidation.recognize_ok' (h.ri g).1 (by rw [(h.ri g).2.1]; exact (h.ri g).2.2.1)))
    fun _ ⟨⟨r8v, m2, k2, lr2⟩, sp2⟩ => ⟨s, h, r8v, m2, ⟨k2.1, k2.2.1, k2.2.2, sp2, lr2⟩⟩

/-- The registers the stages write. -/
abbrev rs3 : List Reg := [.r23, .r3, .r4, .r5] ++ VettedValidation.allClobbers ++ (([] : List Reg) ++ setup0Regs)
abbrev rs4 : List Reg := rs3 ++ ([.r0, .r6, .r12, .r14, .r15, .r16, .r17, .r18] : List Reg)
abbrev rs5 : List Reg := rs4 ++ mainRegs

/-- What the stages keep in the header and apart from the working space. -/
structure Sx (rs : List Reg) (q : PQ) (s₀ s : State) : Prop where
  w0 : word s.mem q.S 0 = q.C
  wcap : word s.mem q.S 96 = BitVec.ofNat 64 q.cap
  sav : ∀ i < 18, word s.mem q.S (112 + 8 * i) = s₀.gpr (Impl.Ffdh.PPC64LE.Domain.saved i)
  fr : ∀ x, q.Z ≤ ofs q.S x → s.mem x = s₀.mem x
  keep : Bignum.PPC64LE.Keep rs s₀ s

/-- After the width's store and `setup`. -/
def St3 (q : PQ) (s₀ s : State) : Prop := Base q.cd s ∧ Sx rs3 q s₀ s

theorem pc_s3 {q : PQ} {s₀ s : State} (g : Geo q s₀) (h : St2 q s₀ s) :
    WP isa (.block ([sth .r8 hCap] ++ VG.Impl.Ffdh.PPC64LE.Domain.setup)) s (St3 q s₀) := by
  obtain ⟨s₁, h1, r8v, m2, k2⟩ := h
  have hZ := g.hZ
  have hnw := g.nwS
  have k12 := h1.keep.trans k2
  have g23 : s.gpr .r23 = q.S := (k2.gpr .r23 (by decide)).trans h1.r23
  refine WP.block_append (WP.mono (pcCap_ok g23 (by rw [k12.wr]; exact g.hinS 96 (by decide)))
    fun s₂' ⟨m2', kc⟩ => ?_)
  refine WP.mono (setup0_ok (D := q.D) (L := q.L) (k := q.k)
    ((kc.gpr .r3 (by decide)).trans ((k2.gpr .r3 (by decide)).trans h1.r3))
    (by rw [kc.gpr .r4 (by decide), k2.gpr .r4 (by decide), h1.r4])
    (by rw [kc.gpr .r5 (by decide), k2.gpr .r5 (by decide), h1.r5])
    ((kc.gpr .r23 (by decide)).trans g23) g.hk') fun s₃ ⟨⟨a21, a27, a28, a11, a29, a10, a31, m3⟩, k3⟩ => ?_
  have k13 := (k12.trans kc).trans k3
  have oc := writeW_outside s.mem q.S (d := 96) (s.gpr .r8) (by omega_using [])
  rw [← m2'] at oc
  have fr3 : ∀ x, q.Z ≤ ofs q.S x → s₃.mem x = s₀.mem x := fun x hx => by
    rw [m3, oc x (.inr (by omega_using [hZ, hx])), m2]; exact h1.fr x hx
  have w3 : ∀ d, d + 8 ≤ 96 ∨ 104 ≤ d → d + 8 ≤ 256 → word s₃.mem q.S d = word s₁.mem q.S d := fun d hd hd' => by
    rw [m3, oc.word (by omega_using [hd]) (by omega_using [hd']), m2]
  have hk := g.hk
  have hL := g.hL
  refine ⟨⟨⟨g.hs.congr k13.wr, a10, a29, a11, a31, g.hw4, g.hw', g.hZw⟩, a21,
    (k3.gpr .r23 (by decide)).trans ((kc.gpr .r23 (by decide)).trans g23), a27, a28, g.hk, g.hk', g.hL,
    fun i hi => by rw [k13.rd, k13.wr]; exact g.rdD i hi, g.sepD,
    fun i hi => by rw [k13.rd, k13.wr]; exact g.rdD i (by show i < q.L; change i < q.k at hi; omega_using [hL, hi]),
    fun i hi => g.sepD i (by change i < q.k at hi; omega_using [hL, hi]), ?_, ?_⟩,
    ⟨by rw [w3 0 (by omega_using []) (by omega_using [])]; exact h1.w0, ?_, fun i hi => by rw [w3 _ (by omega_using []) (by omega_using [hi])]; exact h1.sav i hi,
      fr3, k13⟩⟩
  · show Spec.Rsa.bytesAt s₃.mem q.D q.L = q.db
    rw [bytes_out fr3 g.sepD, g.dom]
  · show Spec.Rsa.bytesAt s₃.mem q.D q.k = q.db.take q.k
    rw [bytes_out fr3 (fun i hi => g.sepD i (by omega_using [hL, hi])), ← g.dom,
      VG.Proof.Ffdh.take_bytesAt s₀.mem q.D (by omega_using [hL] : q.k ≤ q.L)]
  · rw [m3, m2', word_writeW_self, r8v]

/-- After p's check. -/
def St4 (q : PQ) (s₀ s : State) : Prop := E4 q.cd s ∧ Sx rs4 q s₀ s

theorem pc_s4 {q : PQ} {s₀ s : State} (g : Geo q s₀) (h : St3 q s₀ s) : WP isa loadP s (St4 q s₀) := by
  obtain ⟨hb, hX⟩ := h
  have hZ := g.hZ
  have e0 := slot0 q.w
  refine WP.mono (loadP_ok hb.env hb.r21 hb.r28 rfl g.hk g.hk' (fun i hi => hb.rdY i hi) (fun i hi => hb.sepY i hi))
    fun s₄ ⟨⟨p4, c4, b4⟩, k4⟩ => ?_
  have hy : Spec.Rsa.bytesAt s.mem q.cd.D q.cd.k = q.db.take q.k := hb.bY
  rw [hy] at p4 c4
  refine ⟨⟨hb.keep k4 b4, p4, c4⟩, ⟨?_, ?_, fun i hi => ?_, fun x hx => ?_, hX.keep.trans k4⟩⟩
  all_goals change Body q.S q.w s.mem s₄.mem at b4
  · rw [Outside.word b4 (by omega_using [e0]) (by omega_using [])]; exact hX.w0
  · rw [Outside.word b4 (by omega_using [e0]) (by omega_using [])]; exact hX.wcap
  · rw [Outside.word b4 (by omega_using [e0, hi]) (by omega_using [hi])]; exact hX.sav i hi
  · rw [b4 x (.inr (by rw [e0]; omega_using [hZ, hx]))]; exact hX.fr x hx

/-- `main`'s precondition, after p's check. -/
theorem St4.mp {q : PQ} {s₀ s : State} (g : Geo q s₀) (h : St4 q s₀ s) : MP q.S q.D q.C q.Z q.k q.L s := by
  obtain ⟨⟨hb, p4, -⟩, hx⟩ := h
  have hb' : Spec.Rsa.bytesAt s.mem q.D q.L = q.db := hb.bD
  have nwC := g.nwC
  have hw : q.w = (q.k + 7) / 8 := rfl
  refine ⟨hb.env, hb.r23, hb.r21, hb.r27, hb.r28, g.hk, g.hk', g.hL, hb.rdD, g.sepD,
    fun i hi x hx => g.sepDC i hi x (by rw [ctxWords] at hx; omega_using [hw, hx]), ?_,
    fun x hx => g.sepCB x (by rw [ctxWords] at hx; omega_using [hw, hx]),
    fun x hx => by have := g.sepBC x hx; rw [ctxWords]; omega_using [hw, this], hx.w0, by rw [hb']; exact hx.wcap, ?_,
    by rw [hb']; exact g.dv⟩
  · exact Scr.of_mem (by rw [hx.keep.wr, g.wr]; simp [ctxWords]; omega_using [hw]) (by rw [ctxWords]; omega_using [nwC, hw])
  · rw [hb']; exact p4

/-- After the branch. -/
structure St5 (q : PQ) (s₀ s : State) : Prop where
  r3 : s.gpr .r3 = BitVec.ofNat 64 1
  words : Spec.Rsa.wordsAt s.mem q.C (3 + 34 * q.w) = VG.Proof.Ffdh.generationValues q.k q.db
  sav : ∀ i < 18, word s.mem q.S (112 + 8 * i) = s₀.gpr (Impl.Ffdh.PPC64LE.Domain.saved i)
  keep : Bignum.PPC64LE.Keep rs5 s₀ s
  r23 : s.gpr .r23 = q.S

/-- `main`, with p valid. -/
theorem pc_main {q : PQ} {s₀ s : State} (g : Geo q s₀) (h : St4 q s₀ s) : WP isa main s (St5 q s₀) := by
  have mp := h.mp g
  have hZ := g.hZ
  have hb' : Spec.Rsa.bytesAt s.mem q.D q.L = q.db := h.1.1.bD
  refine WP.mono (main_ok mp) fun t ⟨⟨t3, tw, tm⟩, kt⟩ => ⟨t3, by rw [tw, hb'], fun i hi => ?_,
    h.2.keep.trans kt, (kt.gpr .r23 (by decide)).trans h.1.1.r23⟩
  have hm : Outside q.S (slot q.w 1) (2 ^ 64) s.mem t.mem := fun x hx => by
    rcases hx with hx | hx
    · exact tm x hx
    · exact absurd hx (by have := (x - q.S).isLt; simp only [ofs]; omega_using [])
  rw [Outside.word hm (by rw [Domain.slot_eq]; omega_using [hi]) (by omega_using [hi])]
  exact h.2.sav i hi

theorem pc_s5 {q : PQ} {s₀ s : State} (g : Geo q s₀) (h : St4 q s₀ s) :
    WP isa (.ite (.zero .d .r0) main (.block [.li .r3 0])) s (St5 q s₀) :=
  WP.ite (s.gpr .r0 == 0) (eval_zero _ _) (fun _ => pc_main g h)
    (fun hz => absurd (h.1.2.2.mpr g.hmod) (by simpa using hz))

theorem pc_correct (s : State) (h : pcContract.pre s) :
    ∃ tr t, Exec isa Precompute.code s tr t ∧ abiPreserved s t ∧ pcContract.post s t := by
  show WP isa Precompute.code s fun t => abiPreserved s t ∧ pcPost s t
  have g := geo_of_pre h
  unfold Precompute.code
  refine WP.seq (WP.mono (pc_s1 g) fun s₁ h1 => ?_)
  refine WP.seq (WP.mono (pc_s2 g h1) fun s₂ h2 => ?_)
  refine WP.seq (WP.mono (pc_s3 g h2) fun s₃ h3 => ?_)
  refine WP.seq (WP.mono (pc_s4 g h3) fun s₄ h4 => ?_)
  refine WP.seq (WP.mono (pc_s5 g h4) fun t₅ h5 => ?_)
  have hsav' : ∀ i < 18, t₅.mem.readW (off (savW (pqOf s).S) (8 * i)) 64 =
      s.gpr (Impl.Ffdh.PPC64LE.Domain.saved i) := fun i hi => by
    have ea : off (savW (pqOf s).S) (8 * i) = off (pqOf s).S (112 + 8 * i) := by rw [off, off, Offset.add_add]
    rw [ea]
    exact h5.sav i hi
  refine WP.mono (restore_ok t₅ h5.r23 (by rw [h5.keep.wr]; exact g.hin) hsav')
    fun u ⟨urs, uot, um, _, _, usp, ulr⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [usp, h5.keep.sp], by rw [ulr, h5.keep.lr]⟩, ?_, ?_⟩
  · by_cases hs' : ∃ i < 18, r = Impl.Ffdh.PPC64LE.Domain.saved i
    · obtain ⟨i, hi, rfl⟩ := hs'
      exact urs i hi
    · have hn : ∀ i < 18, r ≠ Impl.Ffdh.PPC64LE.Domain.saved i := fun i hi e => hs' ⟨i, hi, e⟩
      rw [uot r hn, h5.keep.gpr r (pc_pres_not_written r hr hn)]
  · rw [uot .r3 (by decide), h5.r3]; rfl
  · show Spec.Ffdh.generationPrecompute (pqOf s).k (pqOf s).db =
      some (Spec.Rsa.wordsAt u.mem (pqOf s).C (s.gpr .r4).toNat)
    rw [g.r4, um, h5.words]
    exact g.hgen

end VG.Proof.Ffdh.PPC64LE.Cached

end

end

/-!
# `vg_ffdh_generate_key_precompute` on PPC64LE: constant time

Everything the precomputation computes is public: its addresses, counts and
branches are functions of the domain, its length, `p_len`, the context's,
the working space's and the table's addresses. The stages of `pc_correct`
fix the registers each piece reads; `main` runs as nine pieces (`mainG`), each
checked by the taint analysis from the registers that the one before fixes
(`main_pins`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Cached

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain
open VG.Impl.Ffdh.PPC64LE.Cached VG.Impl.Ffdh.PPC64LE.Cached.Precompute
open VG.Proof.Ffdh.PPC64LE.Domain
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.PPC64LE (Two Pins two_post two_taint)
open VG.Proof.Ffdh.PPC64LE.GenerateKey (bptr boundPtr_ok scan_ok scanRegs bptr_bnd)
open VG.Impl.Ffdh.PPC64LE.VettedValidation (tableSym tableConsts)
open VG.Spec.RsaKeyGen (bitLength)

/-! ## `main`, in pieces -/

/-- `boundBits` up to the bit loop. -/
def bbA : Prog isa :=
  .seq VG.Impl.Ffdh.PPC64LE.GenerateKey.boundPtr (.seq (.block VG.Impl.Ffdh.PPC64LE.GenerateKey.scanSetup)
    (.seq (VG.Impl.Bignum.PPC64LE.Precompute.countLoop .r6 VG.Impl.Ffdh.PPC64LE.GenerateKey.scanBody)
      (.block [.li .r15 0])))

/-- The bit loop and the bound's bit length. -/
def bbX : Prog isa :=
  .seq (.loop (.block [.lsr .d .r14 .r14 1, .addi .r15 .r15 1]) (.nonzero .d .r14))
    (.block [.sub .r16 .r28 .r22, .lsl .r16 .r16 3, .subi .r16 .r16 8, .add .r16 .r16 .r15])

def w1 : List Instr := [ldh .r8 hCap, .sub .r9 .r8 .r16, .lsr .d .r9 .r9 63]

def iteW : Prog isa := .ite (.zero .d .r8) (.block []) (.ite (.zero .d .r9) (.block []) (.block [.addi .r16 .r8 0]))

def m1 : List Instr := [.addi .r17 .r16 7, .lsr .d .r17 .r17 3]

def mrest : List Instr := [.store .d .r16 .r30 0, .store .d .r17 .r30 8, .store .d .r18 .r30 16, .addi .r24 .r18 0]

def tail : Prog isa := .seq montgomery (.seq storePrefix (.seq table (.block [.li .r3 1])))

/-- `main`, in the pieces the constant-time proof checks. -/
def mainG : Prog isa :=
  .seq bbA (.seq bbX (.seq (.block w1) (.seq iteW (.seq (.block m1) (.seq rows
    (.seq (.block [ldh .r30 hCtx]) (.seq (.block mrest) tail)))))))

theorem exec_block_split {l₁ l₂ : List Instr} {s t : State} {tr : List Leak}
    (e : Exec isa (.block (l₁ ++ l₂)) s tr t) : Exec isa (.seq (.block l₁) (.block l₂)) s tr t := by
  rw [Exec.block_iff, execBlock_append] at e
  obtain ⟨⟨a, u⟩, ha, hb⟩ := Option.bind_eq_some_iff.mp e
  obtain ⟨⟨b, w⟩, hc, he⟩ := Option.map_eq_some_iff.mp hb
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact .seq (.block ha) (.block hc)

theorem WP.block_split {l₁ l₂ : List Instr} {s : State} {Q : State → Prop}
    (h : WP isa (.block (l₁ ++ l₂)) s Q) : WP isa (.block l₁) s fun t => WP isa (.block l₂) t Q := by
  obtain ⟨tr, t, e, hq⟩ := h
  obtain e' := exec_block_split e
  cases e' with
  | seq a b => exact ⟨_, _, a, _, _, b, hq⟩

theorem exec_bb {s t : State} {tr : List Leak} (e : Exec isa boundBits s tr t) :
    Exec isa (.seq bbA bbX) s tr t := by
  unfold boundBits at e
  cases e with
  | seq b1 e =>
    cases e with
    | seq b2 e =>
      cases e with
      | seq b3 e =>
        cases e with
        | seq b4 b5 =>
          have := Exec.seq (Exec.seq b1 (Exec.seq b2 (Exec.seq b3 b4))) b5
          simp only [List.append_assoc] at this
          exact this

theorem Exec.seq_inv {a b : Prog isa} {s t : State} {tr : List Leak} (e : Exec isa (.seq a b) s tr t) :
    ∃ t₁ u t₂, tr = t₁ ++ t₂ ∧ Exec isa a s t₁ u ∧ Exec isa b u t₂ t := by
  cases e with
  | seq h₁ h₂ => exact ⟨_, _, _, rfl, h₁, h₂⟩

theorem exec_main {s t : State} {tr : List Leak} (e : Exec isa main s tr t) : Exec isa mainG s tr t := by
  have e : Exec isa (.seq boundBits (.seq width (.seq metadata tail))) s tr t := e
  obtain ⟨a1, u1, a2, h1, eB, e⟩ := Exec.seq_inv e
  obtain ⟨b1, v1, b2, h2, eA, eX⟩ := Exec.seq_inv (exec_bb eB)
  obtain ⟨c1, u2, c2, h3, eW, e⟩ := Exec.seq_inv e
  obtain ⟨d1, v2, d2, h4, ew, ei⟩ := Exec.seq_inv (a := .block w1) (b := iteW) eW
  obtain ⟨e1, u3, e2, h5, eM, eT⟩ := Exec.seq_inv e
  obtain ⟨f1, v3, f2, h6, em, eM⟩ := Exec.seq_inv (a := .block m1) eM
  obtain ⟨g1, v4, g2, h7, er, el⟩ := Exec.seq_inv eM
  obtain ⟨i1, v5, i2, h8, el1, el2⟩ := Exec.seq_inv (exec_block_split (l₁ := [ldh .r30 hCtx]) (l₂ := mrest) el)
  have := Exec.seq eA (Exec.seq eX (Exec.seq ew (Exec.seq ei (Exec.seq em (Exec.seq er
    (Exec.seq el1 (Exec.seq el2 eT)))))))
  rw [h1, h2, h3, h4, h5, h6, h7, h8]
  simp only [List.append_assoc] at this ⊢
  exact this

theorem WP.main_G {s : State} {Q : State → Prop} (h : WP isa main s Q) : WP isa mainG s Q := by
  obtain ⟨tr, t, e, hq⟩ := h
  exact ⟨tr, t, exec_main e, hq⟩

theorem WP.bb {s : State} {Q : State → Prop} (h : WP isa boundBits s Q) : WP isa (.seq bbA bbX) s Q := by
  obtain ⟨tr, t, e, hq⟩ := h
  exact ⟨tr, t, exec_bb e, hq⟩

theorem RelCT.of_exec {P Q : State → State → Prop} {c c' : Prog isa}
    (hc : ∀ s tr t, Exec isa c' s tr t → Exec isa c s tr t) (h : RelCT isa P c Q) : RelCT isa P c' Q :=
  fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ _ _ _ _ hp (hc _ _ _ e₁) (hc _ _ _ e₂)

/-! ## The pieces' registers -/

/-- `bbA`: the bound's first nonzero octet in `r14`, and `r15 = 0`. -/
theorem bbA_ok {s : State} {D : Addr} {k L : Nat} (h21 : s.gpr .r21 = D)
    (h27 : s.gpr .r27 = BitVec.ofNat 64 L) (h28 : s.gpr .r28 = BitVec.ofNat 64 k) (hL : L = 2 * k ∨ L = 3 * k)
    (hk : 1 ≤ k) (hk32 : k < 2 ^ 32) (hrd : ∀ i < L, InRegions (s.rd ++ s.wr) (off D i) 1) :
    WP isa bbA s fun t =>
      (t.gpr .r14 = BitVec.ofNat 64 (leadOct (VG.Proof.Ffdh.KeyScalar.bnd k (Spec.Rsa.bytesAt s.mem D L))) ∧
        t.gpr .r15 = BitVec.ofNat 64 0) ∧ Bignum.PPC64LE.Keep (([.r0, .r12] : List Reg) ++ scanRegs ++ ([.r15] : List Reg)) s t := by
  unfold bbA
  refine WP.seq (WP.mono (boundPtr_ok h21 h27 h28 (by omega_using [hL, hk32]) hk32) fun s₁ ⟨⟨a12, m1⟩, k1⟩ => ?_)
  obtain hbytes : Spec.Rsa.bytesAt s₁.mem (bptr D k L) k =
      VG.Proof.Ffdh.KeyScalar.bnd k (Spec.Rsa.bytesAt s.mem D L) := by rw [m1, bptr_bnd _ _ hL]
  obtain hrdP : ∀ i < k, InRegions (s₁.rd ++ s₁.wr) (off (bptr D k L) i) 1 := fun i hi => by
    rw [k1.rd, k1.wr]
    unfold bptr
    split
    · rw [VG.Proof.Ffdh.PPC64LE.Domain.off_off']; exact hrd _ (by omega_arith)
    · exact hrd _ (by omega_using [hL, hi])
  refine WP.seq (WP.mono (scan_ok hk hk32 hrdP a12 ((k1.gpr .r28 (by decide)).trans h28))
    fun u hu => WP.seq (WP.mono hu fun s₂ ⟨⟨_, a14, _⟩, k2⟩ => ?_))
  rw [hbytes] at a14
  refine WP.mono (Bignum.PPC64LE.WP.keep [.r15] (Q := fun t => t.gpr .r15 = BitVec.ofNat 64 0) (by prun) (by decide))
    fun t ⟨a15, k3⟩ => ⟨⟨?_, a15⟩, (k1.trans k2).trans k3⟩
  rw [k3.gpr .r14 (by decide), a14]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, leadOct]
  try omega

/-- `w1`: the recognized width in `r8`, and whether it is below `r16`'s. -/
theorem w1_ok {s : State} {S : Addr} {Z cap bl : Nat} (hs : Scr s S Z) (hZ : 104 ≤ Z) (h23 : s.gpr .r23 = S)
    (hcap : s.mem.readW (off S hCap) 64 = BitVec.ofNat 64 cap) (h16 : s.gpr .r16 = BitVec.ofNat 64 bl)
    (hc : cap < 2 ^ 32) (hb : bl < 2 ^ 32) :
    WP isa (.block w1) s fun t => (t.gpr .r8 = BitVec.ofNat 64 cap ∧
      t.gpr .r9 = BitVec.ofNat 64 (if cap < bl then 1 else 0)) ∧ Bignum.PPC64LE.Keep [.r8, .r9] s t := by
  obtain l96 : InRegions (s.rd ++ s.wr) (s.gpr .r23 + BitVec.ofNat 64 96) 8 := by
    rw [h23]; exact hs.ld (d := 96) (n := 8) (by omega_using [hZ])
  obtain v96 : s.mem.readW (s.gpr .r23 + BitVec.ofNat 64 96) 64 = BitVec.ofNat 64 cap := by rw [h23]; exact hcap
  refine Bignum.PPC64LE.WP.keep [.r8, .r9] ?_ (by decide)
  unfold w1 ldh
  prun [hCap, l96, v96, h16, lt_bit hc hb]

/-- `r30 :=` the context's address, from the header. -/
theorem ldh30_ok {s : State} {S C : Addr} {Z : Nat} (hs : Scr s S Z) (hZ : 8 ≤ Z) (h23 : s.gpr .r23 = S)
    (hC : s.mem.readW (off S hCtx) 64 = C) :
    WP isa (.block [ldh .r30 hCtx]) s fun t => t.gpr .r30 = C ∧ Bignum.PPC64LE.Keep [.r30] s t := by
  obtain l0 : InRegions (s.rd ++ s.wr) (s.gpr .r23 + BitVec.ofNat 64 0) 8 := by
    rw [h23]; exact hs.ld (d := 0) (n := 8) (by omega_using [hZ])
  obtain v0 : s.mem.readW (s.gpr .r23 + BitVec.ofNat 64 0) 64 = C := by rw [h23]; exact hC
  refine Bignum.PPC64LE.WP.keep [.r30] ?_ (by decide)
  unfold ldh
  prun [hCtx, l0, v0]

/-! ## What each piece reads -/

abbrev PQ.bd (q : PQ) : List Byte := VG.Proof.Ffdh.KeyScalar.bnd q.k q.db

/-- The bound's bit length. -/
abbrev PQ.bl (q : PQ) : Nat := 8 * (q.k - VG.Proof.Ffdh.lead q.bd - 1) + bitLength (leadOct q.bd)

/-- The width. -/
abbrev PQ.bits (q : PQ) : Nat := widthOf q.cap q.bl

abbrev PQ.rows (q : PQ) : Nat := Spec.Rsa.FixedBaseComb.rows q.bits

/-- The registers `Base` fixes, with their values. -/
def BV (q : PQ) (s : State) : Prop :=
  s.gpr .r10 = off q.S (slot q.w 0) ∧ s.gpr .r11 = BitVec.ofNat 64 (2 * q.w) ∧ s.gpr .r21 = q.D ∧
    s.gpr .r23 = q.S ∧ s.gpr .r27 = BitVec.ofNat 64 q.L ∧ s.gpr .r28 = BitVec.ofNat 64 q.k ∧
    s.gpr .r29 = BitVec.ofNat 64 (8 * (q.w + 2)) ∧ s.gpr .r31 = q.S

theorem BV.of_base {q : PQ} {s : State} (h : Base q.cd s) : BV q s :=
  ⟨h.env.h10, h.env.h11, h.r21, h.r23, h.r27, h.r28, h.env.h29, h.env.h31⟩

theorem BV.keep {q : PQ} {s t : State} {rs : List Reg} (h : BV q s) (k : Bignum.PPC64LE.Keep rs s t)
    (hr : ∀ r ∈ baseRegs, r ∉ rs := by decide) : BV q t := by
  obtain ⟨h10, h11, h21, h23, h27, h28, h29, h31⟩ := h
  simp only [baseRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
  exact ⟨(k.gpr _ hr.1).trans h10, (k.gpr _ hr.2.1).trans h11, (k.gpr _ hr.2.2.1).trans h21,
    (k.gpr _ hr.2.2.2.1).trans h23, (k.gpr _ hr.2.2.2.2.1).trans h27, (k.gpr _ hr.2.2.2.2.2.1).trans h28,
    (k.gpr _ hr.2.2.2.2.2.2.1).trans h29, (k.gpr _ hr.2.2.2.2.2.2.2).trans h31⟩

theorem BV.pins {q : PQ} {s₁ s₂ : State} (h₁ : BV q s₁) (h₂ : BV q s₂) :
    ∀ r ∈ baseRegs, s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [baseRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  obtain ⟨a10, a11, a21, a23, a27, a28, a29, a31⟩ := h₁
  obtain ⟨b10, b11, b21, b23, b27, b28, b29, b31⟩ := h₂
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a10, b10]
  · rw [a11, b11]
  · rw [a21, b21]
  · rw [a23, b23]
  · rw [a27, b27]
  · rw [a28, b28]
  · rw [a29, b29]
  · rw [a31, b31]

def V1 (q : PQ) (s : State) : Prop :=
  s.gpr .r14 = BitVec.ofNat 64 (leadOct q.bd) ∧ s.gpr .r15 = BitVec.ofNat 64 0 ∧ s.gpr .r23 = q.S
def V2 (q : PQ) (s : State) : Prop := s.gpr .r23 = q.S
def V3 (q : PQ) (s : State) : Prop :=
  s.gpr .r8 = BitVec.ofNat 64 q.cap ∧ s.gpr .r9 = BitVec.ofNat 64 (if q.cap < q.bl then 1 else 0) ∧
    s.gpr .r16 = BitVec.ofNat 64 q.bl ∧ s.gpr .r23 = q.S
def V4 (q : PQ) (s : State) : Prop := s.gpr .r16 = BitVec.ofNat 64 q.bits ∧ s.gpr .r23 = q.S
def V6 (q : PQ) (s : State) : Prop := BV q s ∧ s.gpr .r18 = BitVec.ofNat 64 q.rows
def V7 (q : PQ) (s : State) : Prop := BV q s ∧ s.gpr .r30 = q.C ∧ s.gpr .r18 = BitVec.ofNat 64 q.rows
def V8 (q : PQ) (s : State) : Prop := BV q s ∧ s.gpr .r30 = q.C ∧ s.gpr .r24 = BitVec.ofNat 64 q.rows

/-- From each piece on, the registers each later piece reads. -/
def C7 (q : PQ) (s : State) : Prop := WP isa (.block mrest) s fun t => V8 q t ∧ True
def C6 (q : PQ) (s : State) : Prop := WP isa (.block [ldh .r30 hCtx]) s fun t => V7 q t ∧ C7 q t
def C5 (q : PQ) (s : State) : Prop := WP isa rows s fun t => V6 q t ∧ C6 q t
def C4 (q : PQ) (s : State) : Prop := WP isa (.block m1) s fun t => V4 q t ∧ C5 q t
def C3 (q : PQ) (s : State) : Prop := WP isa iteW s fun t => V4 q t ∧ C4 q t
def C2 (q : PQ) (s : State) : Prop := WP isa (.block w1) s fun t => V3 q t ∧ C3 q t
def C1 (q : PQ) (s : State) : Prop := WP isa bbX s fun t => V2 q t ∧ C2 q t
def C0 (q : PQ) (s : State) : Prop := WP isa bbA s fun t => V1 q t ∧ C1 q t

theorem m1_ok (s : State) : WP isa (.block m1) s fun t => t.mem = s.mem ∧ Bignum.PPC64LE.Keep [.r17] s t := by
  refine Bignum.PPC64LE.WP.keep [.r17] ?_ (by decide)
  unfold m1
  prun

/-- `main`'s pieces read what `C0` says. -/
theorem main_pins {q : PQ} {s₀ s : State} (g : Geo q s₀) (h : St4 q s₀ s) : C0 q s := by
  obtain mp := h.mp g
  have hb := h.1.1
  obtain bv := BV.of_base hb
  have hZ := mp.env.hZ
  obtain hk := g.hk; have hk' := g.hk'
  have hCn := mp.hc.nowrap
  have hdom : Spec.Rsa.bytesAt s.mem q.D q.L = q.db := hb.bD
  obtain hd : q.db.length = 2 * q.k ∨ q.db.length = 3 * q.k := by rw [g.hlen]; exact g.hL
  obtain hv' := (VG.Proof.Ffdh.domainValid_iff q.k q.db).mp g.dv
  obtain hpf := VG.Proof.Ffdh.PPC64LE.Domain.modulus_facts hv'.1
  have hmv := hv'.1
  obtain hnorm : 2 ^ (64 * ((q.k + 7) / 8 - 1)) ≤ Spec.Rsa.os2ip (q.db.take q.k) := by
    change 2 ^ (64 * ((q.k + 7) / 8 - 1)) ≤ (Spec.Ffdh.domainOf q.k q.db).p
    simp only [Spec.Rsa.modulusValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hmv
    refine Nat.le_trans ?_ hmv.2
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega_using [])
  obtain hlead := lead_ne (by omega_using [hk]) hd g.dv
  obtain hcap := recognize_lt (by omega_using [hk]) hd hnorm
  obtain hlo : leadOct q.bd < 256 := (q.bd.getD (VG.Proof.Ffdh.lead q.bd) 0).isLt
  obtain hbl8 : bitLength (leadOct q.bd) ≤ 8 := bitLength_le_of_lt (by simpa using hlo)
  obtain hbl1 : 1 ≤ bitLength (leadOct q.bd) := bitLength_pos hlead
  obtain hbl : q.bl ≤ 8 * q.k := by simp only [PQ.bl]; omega_using [hk, hbl8]
  obtain hbl1' : 1 ≤ q.bl := by simp only [PQ.bl]; omega_using [hbl1]
  have hcap' : q.cap ≤ 400 := hcap
  obtain hbits1 : 1 ≤ q.bits := by simp only [PQ.bits, widthOf]; split <;> omega_arith
  obtain hbits : q.bits ≤ 8192 := by simp only [PQ.bits, widthOf]; split <;> omega_arith
  obtain hBB := WP.bb (boundBits_ok mp.h21 mp.h27 mp.h28 mp.hL (by omega_using [hk]) (by omega_using [hk']) mp.rdD (by rw [hdom]; exact hlead))
  rw [WP.seq_iff] at hBB
  refine WP.mono (WP.and (bbA_ok mp.h21 mp.h27 mp.h28 mp.hL (by omega_using [hk]) (by omega_using [hk']) mp.rdD) hBB)
    fun s₁ ⟨⟨⟨a14, a15⟩, k1⟩, hX⟩ => ⟨⟨by rw [a14, hdom], a15, (k1.gpr .r23 (by decide)).trans mp.h23⟩, ?_⟩
  refine WP.mono hX fun s₂ ⟨⟨a16, m2⟩, k2⟩ => ⟨(k2.gpr .r23 (by decide)).trans mp.h23, ?_⟩
  rw [hdom] at a16
  replace a16 : s₂.gpr .r16 = BitVec.ofNat 64 q.bl := a16
  obtain g23 : s₂.gpr .r23 = q.S := (k2.gpr .r23 (by decide)).trans mp.h23
  obtain hcap2 : s₂.mem.readW (off q.S hCap) 64 = BitVec.ofNat 64 q.cap := by rw [m2]; have := mp.hcap; rw [hdom] at this; exact this
  obtain hs2 := mp.env.hs.congr k2.wr
  obtain hW := width_ok (cap := q.cap) hs2 (Nat.le_trans (by simp only [slot]; omega_using []) hZ) g23 hcap2 a16
    (by omega_using [hcap']) (by omega_using [hk', hbl])
  unfold width at hW
  rw [WP.seq_iff] at hW
  refine WP.mono (WP.and (w1_ok hs2 (Nat.le_trans (by simp only [slot]; omega_using []) hZ) g23 hcap2 a16 (by omega_using [hcap'])
    (by omega_using [hk', hbl])) hW) fun s₃ ⟨⟨⟨a8, a9⟩, k3⟩, hI⟩ =>
      ⟨⟨a8, a9, (k3.gpr .r16 (by decide)).trans a16, (k3.gpr .r23 (by decide)).trans g23⟩, ?_⟩
  refine WP.mono hI fun s₄ ⟨⟨a16', m4⟩, k4⟩ => ⟨⟨a16', (k4.gpr .r23 (by decide)).trans g23⟩, ?_⟩
  obtain g23' : s₄.gpr .r23 = q.S := (k4.gpr .r23 (by decide)).trans g23
  obtain k24 := k2.trans k4
  obtain m4' : s₄.mem = s.mem := by rw [m4, m2]
  obtain hc24 : Scr s₄ q.C 24 := ⟨let ⟨B₀, o, L', hm, hb, hL, hL'⟩ := (mp.hc.congr k24.wr).wr
    ⟨B₀, o, L', hm, hb, by unfold ctxWords at hL; omega_using [hL], hL'⟩, by unfold ctxWords at hCn; omega_using [hCn]⟩
  obtain hM := metadata_ok (mp.env.hs.congr k24.wr) (by simp only [slot] at hZ; omega_using [hZ]) g23' (by rw [m4']; exact mp.hC)
    hc24 a16' hbits1 hbits
  unfold metadata at hM
  rw [WP.seq_iff] at hM
  refine WP.mono (WP.and (m1_ok s₄) hM) fun s₅ ⟨⟨m5, k5⟩, hR⟩ =>
    ⟨⟨(k5.gpr .r16 (by decide)).trans a16', (k5.gpr .r23 (by decide)).trans g23'⟩, ?_⟩
  rw [WP.seq_iff] at hR
  refine WP.mono (WP.and (rowsLoop_ok hbits1 (by omega_using [hbits]) ((k5.gpr .r16 (by decide)).trans a16')) hR)
    fun s₆ ⟨⟨⟨a18, m6⟩, k6⟩, hL⟩ => ⟨⟨((((bv.keep k2).keep k4).keep k5).keep k6), a18⟩, ?_⟩
  obtain bv6 : BV q s₆ := ((((bv.keep k2).keep k4).keep k5).keep k6)
  obtain k26 := (k24.trans k5).trans k6
  obtain hL' := WP.block_split (l₁ := [ldh .r30 hCtx]) (l₂ := mrest) hL
  refine WP.mono (WP.and (ldh30_ok (mp.env.hs.congr k26.wr) (by simp only [slot] at hZ; omega_using [hZ]) bv6.2.2.2.1
      (by rw [m6, m5, m4']; exact mp.hC)) hL')
    fun s₇ ⟨⟨a30, k7⟩, hMr⟩ => ⟨⟨bv6.keep k7, a30, (k7.gpr .r18 (by decide)).trans a18⟩, ?_⟩
  exact WP.mono hMr fun t ⟨⟨t30, t24, _⟩, kt⟩ => ⟨⟨(bv.keep k24).keep kt, t30, t24⟩, trivial⟩

/-! ## Constant time -/

/-- On entry, with the public data `q`. -/
def P0 (q : PQ) (s : State) : Prop := pcContract.pre s ∧ pqOf s = q

theorem P0.geo {q : PQ} {s : State} (h : P0 q s) : Geo q s := h.2 ▸ geo_of_pre h.1

def F1 (q : PQ) (s : State) : Prop := ∃ s₀, P0 q s₀ ∧ St1 q s₀ s
def F2 (q : PQ) (s : State) : Prop := ∃ s₀, P0 q s₀ ∧ St2 q s₀ s
def F3 (q : PQ) (s : State) : Prop := ∃ s₀, P0 q s₀ ∧ St3 q s₀ s
def F4 (q : PQ) (s : State) : Prop := ∃ s₀, P0 q s₀ ∧ St4 q s₀ s
def F5 (q : PQ) (s : State) : Prop := ∃ s₀, P0 q s₀ ∧ St5 q s₀ s

/-- A stage of `main`: the registers `V` fixes, what the later pieces read
(`C`), and the rest `R` of `main` to come. -/
def MS (V C : PQ → State → Prop) (R : Prog isa) (q : PQ) (s : State) : Prop :=
  V q s ∧ C q s ∧ ∃ s₀, P0 q s₀ ∧ WP isa R s (St5 q s₀)

theorem ms_rel {V V' C' : PQ → State → Prop} {a R : Prog isa} (rs : List Reg) (hp : Pins V rs)
    {hc : VG.Taint.Hint T} (ht : (taint.check (ofRegs rs) a hc).isSome = true) :
    RelCT isa (Two (MS V (fun q s => WP isa a s fun t => V' q t ∧ C' q t) (.seq a R))) a (Two (MS V' C' R)) :=
  two_post (two_taint rs (fun q s₁ s₂ h₁ h₂ => hp q s₁ s₂ h₁.1 h₂.1) ht) fun q s ⟨_, hc, s₀, h0, hw⟩ => by
    rw [WP.seq_iff] at hw
    exact WP.mono (WP.and hc hw) fun t ⟨⟨hv, hc'⟩, hr⟩ => ⟨hv, hc', s₀, h0, hr⟩

theorem ms_last {V : PQ → State → Prop} {a : Prog isa} (rs : List Reg) (hp : Pins V rs)
    {hc : VG.Taint.RHint T} (ht : (taint.checkR montSums (ofRegs rs) a hc).isSome = true)
    (hf : VG.Taint.fillR montSums a hc = a := by rfl) :
    RelCT isa (Two (MS V (fun _ _ => True) a)) a (Two F5) :=
  two_post (two_taintR rs (fun q s₁ s₂ h₁ h₂ => hp q s₁ s₂ h₁.1 h₂.1) ht hf) fun _ _ ⟨_, _, s₀, h0, hw⟩ =>
    WP.mono hw fun _ ht => ⟨s₀, h0, ht⟩

theorem pins_BV : Pins BV baseRegs := fun _ _ _ h₁ h₂ => BV.pins h₁ h₂

theorem pins_V1 : Pins V1 [.r14, .r15, .r23] := by
  rintro q s₁ s₂ ⟨a, b, c⟩ ⟨a', b', c'⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [a, a']
  · rw [b, b']
  · rw [c, c']

theorem pins_V2 : Pins V2 [.r23] := by
  rintro q s₁ s₂ a a' r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; rw [a, a']

theorem pins_V3 : Pins V3 [.r8, .r9, .r16, .r23] := by
  rintro q s₁ s₂ ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [a, a']
  · rw [b, b']
  · rw [c, c']
  · rw [d, d']

theorem pins_V4 : Pins V4 [.r16, .r23] := by
  rintro q s₁ s₂ ⟨a, b⟩ ⟨a', b'⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [a, a']
  · rw [b, b']

theorem pins_V6 : Pins V6 (baseRegs ++ ([.r18] : List Reg)) := by
  rintro q s₁ s₂ ⟨a, b⟩ ⟨a', b'⟩ r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact a.pins a' r hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; rw [b, b']

theorem pins_V7 : Pins V7 (baseRegs ++ ([.r30, .r18] : List Reg)) := by
  rintro q s₁ s₂ ⟨a, b, c⟩ ⟨a', b', c'⟩ r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact a.pins a' r hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [b, b']
    · rw [c, c']

theorem pins_V8 : Pins V8 (baseRegs ++ ([.r30, .r24] : List Reg)) := by
  rintro q s₁ s₂ ⟨a, b, c⟩ ⟨a', b', c'⟩ r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact a.pins a' r hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [b, b']
    · rw [c, c']

theorem mainG_rel : RelCT isa (Two (MS BV C0 mainG)) mainG (Two F5) := by
  unfold mainG
  exact RelCT.seq (ms_rel (V' := V1) (C' := C1) _ pins_BV (by taint_decide))
    (RelCT.seq (ms_rel (V' := V2) (C' := C2) _ pins_V1 (by taint_decide))
      (RelCT.seq (ms_rel (V' := V3) (C' := C3) _ pins_V2 (by taint_decide))
        (RelCT.seq (ms_rel (V' := V4) (C' := C4) _ pins_V3 (by taint_decide))
          (RelCT.seq (ms_rel (V' := V4) (C' := C5) _ pins_V4 (by taint_decide))
            (RelCT.seq (ms_rel (V' := V6) (C' := C6) _ pins_V4 (by taint_decide))
              (RelCT.seq (ms_rel (V' := V7) (C' := C7) _ pins_V6 (by taint_decide))
                (RelCT.seq (ms_rel (V' := V8) (C' := fun _ _ => True) _ pins_V7 (by taint_decide))
                  (ms_last _ pins_V8 (by taint_decide_rel)))))))))

/-- `main`'s entry: p valid. -/
def M0 (q : PQ) (s : State) : Prop := F4 q s ∧ s.gpr .r0 = 0

theorem main_rel : RelCT isa (Two M0) main (Two F5) :=
  RelCT.of_exec (fun _ _ _ e => exec_main e) (mainG_rel.mono (fun _ _ ⟨q, ⟨⟨a, ha, h₁⟩, _⟩, ⟨⟨b, hb, h₂⟩, _⟩, hsp⟩ =>
    ⟨q, ⟨BV.of_base h₁.1.1, main_pins ha.geo h₁, a, ha, WP.main_G (pc_main ha.geo h₁)⟩,
      ⟨BV.of_base h₂.1.1, main_pins hb.geo h₂, b, hb, WP.main_G (pc_main hb.geo h₂)⟩, hsp⟩) fun _ _ h => h)

theorem pins_P0 : Pins P0 [.r3, .r4, .r5, .r6, .r7, .r8, .r9] := by
  rintro q s₁ s₂ h₁ h₂ r hr
  have g₁ := h₁.geo
  have g₂ := h₂.geo
  obtain ⟨_, e₁⟩ := h₁
  obtain ⟨_, e₂⟩ := h₂
  obtain z₁ := congrArg PQ.Z e₁
  obtain z₂ := congrArg PQ.Z e₂
  simp only [pqOf] at z₁ z₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [g₁.r3, g₂.r3]
  · exact BitVec.eq_of_toNat_eq (g₁.r4.trans g₂.r4.symm)
  · rw [g₁.r5, g₂.r5]
  · exact BitVec.eq_of_toNat_eq (g₁.r6.trans g₂.r6.symm)
  · exact BitVec.eq_of_toNat_eq (g₁.r7.trans g₂.r7.symm)
  · rw [g₁.r8, g₂.r8]
  · exact BitVec.eq_of_toNat_eq (by omega_using [z₁, z₂])

theorem front_rel : RelCT isa (Two P0) (.block front) (Two F1) :=
  two_post (two_taint _ pins_P0 (by taint_decide)) fun _ s h => WP.mono (pc_s1 h.geo) fun _ ht => ⟨s, h, ht⟩

theorem rec_rel : RelCT isa (Two F1) VG.Impl.Ffdh.PPC64LE.VettedValidation.recognize (Two F2) := by
  refine two_post ?_ fun _ _ ⟨s₀, h0, h1⟩ => WP.mono (pc_s2 h0.geo h1) fun _ ht => ⟨s₀, h0, ht⟩
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨q, ⟨a, ha, h₁⟩, ⟨b, hb, h₂⟩, _⟩ e₁ e₂
  exact VettedValidation.recognize_ct' q.D q.k q.db q.T q.sp s₁ s₂ t₁ t₂ s₁' s₂'
    ⟨h₁.ri ha.geo, h₂.ri hb.geo⟩ e₁ e₂

theorem pins_F2 : Pins F2 [.r3, .r4, .r5, .r23] := by
  rintro q s₁ s₂ ⟨_, _, a, ha, -, -, ka⟩ ⟨_, _, b, hb, -, -, kb⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [ka.gpr .r3 (by decide), kb.gpr .r3 (by decide), ha.r3, hb.r3]
  · rw [ka.gpr .r4 (by decide), kb.gpr .r4 (by decide), ha.r4, hb.r4]
  · rw [ka.gpr .r5 (by decide), kb.gpr .r5 (by decide), ha.r5, hb.r5]
  · rw [ka.gpr .r23 (by decide), kb.gpr .r23 (by decide), ha.r23, hb.r23]

theorem setup_rel :
    RelCT isa (Two F2) (.block ([sth .r8 hCap] ++ VG.Impl.Ffdh.PPC64LE.Domain.setup)) (Two F3) :=
  two_post (two_taint _ pins_F2 (by taint_decide)) fun _ _ ⟨s₀, h0, h2⟩ =>
    WP.mono (pc_s3 h0.geo h2) fun _ ht => ⟨s₀, h0, ht⟩

/-- In p's check, with what is left of it. -/
def L1 (q : PQ) (s : State) : Prop :=
  E1a q.cd s ∧ ∃ s₀, P0 q s₀ ∧
    WP isa (.seq VG.Impl.Bignum.PPC64LE.Precompute.loadN VG.Impl.Bignum.PPC64LE.Precompute.check) s (St4 q s₀)
def L2 (q : PQ) (s : State) : Prop :=
  E2 q.cd s ∧ ∃ s₀, P0 q s₀ ∧ WP isa VG.Impl.Bignum.PPC64LE.Precompute.check s (St4 q s₀)
def L3 (q : PQ) (s : State) : Prop :=
  E3 q.cd s ∧ ∃ s₀, P0 q s₀ ∧ WP isa VG.Impl.Bignum.PPC64LE.Precompute.check2 s (St4 q s₀)

theorem L1_of {q : PQ} {s : State} (h : F3 q s) :
    WP isa (.block [.addi .r12 .r21 0, .addi .r6 .r28 0]) s (L1 q) := by
  obtain ⟨s₀, h0, h3⟩ := h
  obtain w := pc_s4 h0.geo h3
  unfold loadP at w
  rw [WP.seq_iff] at w
  exact WP.mono (WP.and (DA h3.1) w) fun _ ⟨e, r⟩ => ⟨e, s₀, h0, r⟩

theorem L2_of {q : PQ} {s : State} (h : L1 q s) : WP isa VG.Impl.Bignum.PPC64LE.Precompute.loadN s (L2 q) := by
  obtain ⟨e, s₀, h0, w⟩ := h
  rw [WP.seq_iff] at w
  exact WP.mono (WP.and (DL e) w) fun _ ⟨e', r⟩ => ⟨e', s₀, h0, r⟩

theorem L3_of {q : PQ} {s : State} (h : L2 q s) :
    WP isa (.block VG.Impl.Bignum.PPC64LE.Precompute.check1) s (L3 q) := by
  obtain ⟨e, s₀, h0, w⟩ := h
  unfold VG.Impl.Bignum.PPC64LE.Precompute.check at w
  rw [WP.seq_iff] at w
  exact WP.mono (WP.and (DC1 e) w) fun _ ⟨e', r⟩ => ⟨e', s₀, h0, r⟩

theorem loadP_rel : RelCT isa (Two F3) loadP (Two F4) := by
  unfold loadP VG.Impl.Bignum.PPC64LE.Precompute.check
  exact RelCT.seq (two_post (two_taint baseRegs (fun _ _ _ ⟨_, _, h₁⟩ ⟨_, _, h₂⟩ => h₁.1.pins h₂.1) (by taint_decide))
      fun _ _ h => L1_of h)
    (RelCT.seq (two_post (two_taint _ (fun q s₁ s₂ h₁ h₂ => pins_E1a (fun _ _ h => h) q.cd s₁ s₂ h₁.1 h₂.1)
      (by taint_decide)) fun _ _ h => L2_of h)
      (RelCT.seq (two_post (two_taint _ (fun q s₁ s₂ h₁ h₂ => pins_E1a (fun _ _ h => h.1) q.cd s₁ s₂ h₁.1 h₂.1)
        (by taint_decide)) fun _ _ h => L3_of h)
        (two_post (two_taint _ (fun q s₁ s₂ h₁ h₂ => pins_E3 q.cd s₁ s₂ h₁.1 h₂.1) (by taint_decide))
          fun _ _ ⟨_, s₀, h0, w⟩ => WP.mono w fun _ ht => ⟨s₀, h0, ht⟩)))

theorem branch_rel : RelCT isa (Two F4) (.ite (.zero .d .r0) main (.block [.li .r3 0])) (Two F5) :=
  two_ite (Φ := F4) (fun _ _ _ ⟨_, _, h₁⟩ ⟨_, _, h₂⟩ => h₁.1.2.2.trans h₂.1.2.2.symm) main_rel
    (RelCT.of_false fun _ _ ⟨_, ⟨⟨_, h0, h4⟩, hne⟩, _⟩ => hne (h4.1.2.2.mpr h0.geo.hmod))

theorem pins_F5 : Pins F5 [.r23] := by
  rintro q s₁ s₂ ⟨_, _, h₁⟩ ⟨_, _, h₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; rw [h₁.r23, h₂.r23]

theorem pc_rel : RelCT isa (Two P0) Precompute.code fun _ _ => True := by
  unfold Precompute.code
  exact RelCT.seq front_rel (RelCT.seq rec_rel (RelCT.seq setup_rel (RelCT.seq loadP_rel
    (RelCT.seq branch_rel (two_taint _ pins_F5 (by taint_decide))))))

theorem pqOf_eq {s t : State} (h : pcContract.pub s t) : pqOf s = pqOf t := by
  obtain ⟨⟨hsp, hdom, h3, h4, h5, h6, h7, h8, h9⟩, hsym⟩ := h
  obtain hb := (List.map_inj_right (fun _ _ h => BitVec.eq_of_toNat_eq h)).mp hdom
  simp only [pcDom] at hb
  rw [h5, h6] at hb
  simp only [pqOf, h3, h5, h6, h7, h8, h9, hsym, hsp, hb]

theorem pc_ct : ConstantTime isa pcContract.pre pcContract.pub Precompute.code :=
  RelCT.constantTime (pc_rel.mono (fun s _ ⟨hs, ht, hp⟩ =>
    ⟨pqOf s, ⟨hs, rfl⟩, ⟨ht, (pqOf_eq hp).symm⟩, hp.1.1⟩) fun _ _ h => h)

theorem pc_verified :
    Verified target Precompute.code (Spec.Ffdh.generationPrecomputeContract (abi.withConsts tableConsts)) :=
  Verified.of_correct pc_correct pc_ct pc_implies

end VG.Proof.Ffdh.PPC64LE.Cached
