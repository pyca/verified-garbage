module

public import VerifiedGarbage.Impl.RsaPss.X86
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Entry
public import VerifiedGarbage.Spec.RsaPss.MdTable
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.RsaPss.X86.Base
public import VerifiedGarbage.Proof.RsaOaep.X86.Base
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.Exec
public import VerifiedGarbage.Proof.RsaPss.X86.Params
public import VerifiedGarbage.Proof.RsaPss.X86.Hash
import VerifiedGarbage.Proof.RsaPss.X86.CtBase
public import VerifiedGarbage.Proof.RsaPss.VerifyCases
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Loops
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.PubCall
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyPublicCall
import VerifiedGarbage.Proof.RsaPss.X86.CtInit
import VerifiedGarbage.Proof.RsaPss.X86.CtMgf
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.RsaOaep.X86.MgfSlots
import VerifiedGarbage.Proof.RsaOaep.X86.Mgf
import VerifiedGarbage.Proof.RsaPss.X86.SgEnc3
import VerifiedGarbage.Proof.RsaPss.X86.CtXor

/-! ### `RsaPss.X86.VfScan`, which only this module used -/

section

/-! ### `RsaPss.X86.VfAcc`, which only this module used -/

section

/-! ### `RsaPss.X86.VfCall`, which only this module used -/

section

/-! ### `RsaPss.X86.VfChk`, which only this module used -/

section

/-! ### `RsaPss.X86.VfBase`, which only this module used -/

section

/-!
# RSASSA-PSS verification with a precomputed public key on x86: where everything is

As on ARMv7 (`Proof/RsaPss/Arm/VfFixed.lean`): `EP`, what two runs share
(the frame's base `B`, the pointers, the lengths, `salt_len`,
`any_salt_len`, the public key's bytes and precomputed words, and the
tables, as for signing (`SgBase.lean`): the hash function's of `MdHash` at
`tabH` and MGF1's of `MdHash` at `tab`, whose hash function is `g`), and its
layout (`EP.lay`), with the 100 bytes below the frame that the call of
`vg_rsa_public_precomputed_checked` (100) and the hash functions' calls (48)
use. `In D P σ`: the state `σ` the body starts from, for digests of `D`
bytes (`in_of_pre`, `D` the argument `digest_len`); the working space's bound
is used in one place, `In.pubScr`.

`VQ F c G`: a piece correct (`wp`) and constant time with nothing after it
(`ct`), as the end of a body; the pieces after the call are proven over the
state the call leaves (`VQ.reidx`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Vf

open VG VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes

/-- What two runs share. -/
structure EP where
  B : BitVec 32
  n : BitVec 32
  e : BitVec 32
  dig : BitVec 32
  sig : BitVec 32
  scr : BitVec 32
  pre : BitVec 32
  K : Nat
  el : Nat
  gl : Nat
  slt : Nat
  any : BitVec 32
  scl : Nat
  rl : Nat
  nB : List Byte
  eB : List Byte
  pw : List (BitVec 64)
  tabH : BitVec 32
  hai : BitVec 32
  hac : BitVec 32
  had : BitVec 32
  TH : State → Prop
  tab : BitVec 32
  ai : BitVec 32
  au : BitVec 32
  af : BitVec 32
  T : State → Prop
  g : Proof.RsaOaep.X86.OHash

namespace EP

variable (D : Nat) (P : EP)

abbrev N : Region := ⟨P.n.setWidth 64, P.K⟩
abbrev E : Region := ⟨P.e.setWidth 64, P.el⟩
abbrev DIG : Region := ⟨P.dig.setWidth 64, D⟩
abbrev SIG : Region := ⟨P.sig.setWidth 64, P.gl⟩
abbrev SCR : Region := ⟨P.scr.setWidth 64, P.scl * 8⟩
abbrev PRE : Region := ⟨P.pre.setWidth 64, P.rl * 8⟩
abbrev TABH : Region := Sig.tableRegion 32 (P.tabH.setWidth 64) 11
abbrev TAB : Region := Sig.tableRegion 32 (P.tab.setWidth 64) 11

/-- The arguments, in order. -/
abbrev argv : List (BitVec 32) :=
  [P.n, BitVec.ofNat 32 P.K, P.e, BitVec.ofNat 32 P.el, P.dig, BitVec.ofNat 32 D, P.sig, BitVec.ofNat 32 P.gl,
    BitVec.ofNat 32 P.slt, P.any, P.scr, BitVec.ofNat 32 P.scl, P.pre, BitVec.ofNat 32 P.rl, P.tabH, P.tab]

abbrev ro : List Region := [P.N, P.E, P.DIG D, P.SIG, P.PRE, P.TABH, P.TAB]
abbrev rw : List Region := [P.SCR]

abbrev lay : Lay where
  B := P.B
  F := frameBytes
  argv := P.argv D
  ro := P.ro D
  rw := P.rw
  C := 100

end EP

/-- The state the body starts from. -/
structure In (D : Nat) (P : EP) (σ : State) : Prop where
  ok : (P.lay D).Ok σ
  kv : Spec.Rsa.lenValid P.K
  el1 : 1 ≤ P.el
  elK : P.el ≤ P.K
  glK : P.gl = P.K
  scrK : Spec.RsaPss.publicScratchWords P.K ≤ P.scl
  rlK : P.rl = Spec.Rsa.precomputedWords P.K
  slt32 : P.slt < 2 ^ 32
  scl32 : P.scl < 2 ^ 32
  nB : Spec.Rsa.bytesAt σ.mem (P.n.setWidth 64) P.K = P.nB
  eB : Spec.Rsa.bytesAt σ.mem (P.e.setWidth 64) P.el = P.eB
  pw : Spec.Rsa.wordsAt σ.mem (P.pre.setWidth 64) P.rl = P.pw
  tabTH : P.TH σ
  tabT : P.T σ

namespace In

variable {D : Nat} {P : EP} {σ : State} (h : In D P σ)
include h

theorem k64 : 64 ≤ P.K := h.kv.1
theorem k1024 : P.K ≤ 1024 := h.kv.2

/-- The working space: ours, and the public operation's after it. This is
the one place the contract's bound on `scratch_len` is used. -/
theorem pubScr : Spec.Rsa.publicScratchWords P.K ≤ P.scl - 1024 ∧ 1025 ≤ P.scl := by
  have := h.scrK
  unfold Spec.RsaPss.publicScratchWords Spec.Rsa.publicScratchWords at this
  unfold Spec.Rsa.publicScratchWords
  omega_using [this]

/-- Our part of `scratch`. -/
theorem geo : Geo (P.lay D) P.scr := by
  have hs := h.pubScr.2
  obtain hf := h.ok.fits (P.SCR) (by simp)
  simp only [BitVec.toNat_setWidth] at hf
  rw [Nat.mod_eq_of_lt (by have := P.scr.isLt; omega_using [])] at hf
  exact ⟨rfl, by unfold oRsa; omega_using [hs, hf], ⟨P.scl * 8, by unfold oRsa; omega_using [hs], by simp⟩, ⟨σ, h.ok⟩,
    by show 48 ≤ 100; decide⟩

/-- The table of `MdHash`, in a buffer only read: its words 0 to 4. -/
theorem tblH : ∀ k, k < 5 → ∃ R ∈ (P.lay D).ro, R.Contains (VG.X86.addr P.tabH (4 * k)) 4 := by
  obtain hf := h.ok.fits P.TABH (by simp)
  simp only [Sig.tableRegion, BitVec.toNat_setWidth] at hf
  rw [Nat.mod_eq_of_lt (by have := P.tabH.isLt; omega_using [])] at hf
  intro k hk
  refine ⟨P.TABH, by simp, ?_⟩
  show (⟨P.tabH.setWidth 64, 11 * (32 / 8)⟩ : Region).Contains (VG.X86.addr P.tabH (4 * k)) 4
  rw [addr_eq (by omega_using [hf, hk])]
  exact Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])

/-- Its word 5, the hash function's index. -/
theorem tblH5 : ∃ R ∈ (P.lay D).ro, R.Contains (VG.X86.addr P.tabH 20) 4 := by
  obtain hf := h.ok.fits P.TABH (by simp)
  simp only [Sig.tableRegion, BitVec.toNat_setWidth] at hf
  rw [Nat.mod_eq_of_lt (by have := P.tabH.isLt; omega_using [])] at hf
  refine ⟨P.TABH, by simp, ?_⟩
  show (⟨P.tabH.setWidth 64, 11 * (32 / 8)⟩ : Region).Contains (VG.X86.addr P.tabH 20) 4
  rw [addr_eq (by omega_using [hf])]
  exact Offset.contains_base _ (by omega_using []) (by omega_using [])

/-- The table of `MdHash`, in a buffer only read. -/
theorem tbl : ∃ R ∈ (P.lay D).ro, ∀ o, o + 4 ≤ 44 → R.Contains (VG.X86.addr P.tab o) 4 := by
  obtain hf := h.ok.fits P.TAB (by simp)
  simp only [Sig.tableRegion, BitVec.toNat_setWidth] at hf
  rw [Nat.mod_eq_of_lt (by have := P.tab.isLt; omega_using [])] at hf
  refine ⟨P.TAB, by simp, fun o ho => ?_⟩
  show (⟨P.tab.setWidth 64, 11 * (32 / 8)⟩ : Region).Contains (VG.X86.addr P.tab o) 4
  rw [addr_eq (by omega_using [hf, ho])]
  exact Offset.contains_base _ (by omega_using [ho]) (by omega_using [ho])

end In

/-! ## The entry -/

/-- The stack the function uses: the push, the inner frame and the calls'. -/
abbrev stackBytes : Nat := 16 + frameBytes + 100

/-- The shared contract, with the hash function's table one of `tsH` and
MGF1's one of `ts`, and that stack. -/
abbrev spec (tsH ts : List FnTable) : Contract isa :=
  Spec.RsaPss.verifyPrecomputedMdTableContract
    (abi.withTables Spec.RsaPss.verifyPrecomputedMdTableSig [("hash", tsH), ("mgf1", ts)]) stackBytes

/-- Unfolds the contract's precondition at `h`. -/
macro "verify_pre" " at " h:ident : tactic => `(tactic| (
  sig_pre [Spec.RsaPss.verifyPrecomputedMdTableContract, Spec.RsaPss.verifyPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes, stackBelow] at $h:ident
  sig_pre [Spec.RsaPss.verifyPrecomputedMdTableContract, Spec.RsaPss.verifyPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes, stackBelow] at $h:ident
  simp only [Option.map_some, Nat.reduceAdd, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq,
    exists_eq_left'] at $h:ident))

/-- The public parameters of an entry state, with the hash function's
functions at `hai`, `hac` and `had` and MGF1's at `ai`, `au` and `af`, and
`TH` and `T` of the entry. -/
def ep (s : State) (hai hac had : BitVec 32) (TH : State → Prop) (ai au af : BitVec 32) (T : State → Prop)
    (g : Proof.RsaOaep.X86.OHash) : EP where
  B := s.gpr .esp - BitVec.ofNat 32 16 - BitVec.ofNat 32 frameBytes
  n := arg s 0
  e := arg s 2
  dig := arg s 4
  sig := arg s 6
  scr := arg s 10
  pre := arg s 12
  K := (arg s 1).toNat
  el := (arg s 3).toNat
  gl := (arg s 7).toNat
  slt := (arg s 8).toNat
  any := arg s 9
  scl := (arg s 11).toNat
  rl := (arg s 13).toNat
  nB := Spec.Rsa.bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat
  eB := Spec.Rsa.bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat
  pw := Spec.Rsa.wordsAt s.mem ((arg s 12).setWidth 64) (arg s 13).toNat
  tabH := arg s 14
  hai := hai
  hac := hac
  had := had
  TH := TH
  tab := arg s 15
  ai := ai
  au := au
  af := af
  T := T
  g := g

variable {hai hac had : BitVec 32} {TH : State → Prop} {ai au af : BitVec 32} {T : State → Prop}
  {g : Proof.RsaOaep.X86.OHash}

theorem ep_lay (D : Nat) (s : State) :
    (ep s hai hac had TH ai au af T g).lay D = layOf frameBytes ((ep s hai hac had TH ai au af T g).argv D)
      ((ep s hai hac had TH ai au af T g).ro D) (ep s hai hac had TH ai au af T g).rw s 100 := rfl

/-- The tables, as the contract gives them: the hash function's one of `tsH`
at the argument 14 and MGF1's one of `ts` at 15, with the functions of
distinct names at distinct addresses, and the digest's length. -/
theorem spec_tab {tsH ts : List FnTable} {s : State} (h : (spec tsH ts).pre s) :
    (∃ T ∈ tsH, Abi.tableHeld 32 s.mem ((arg s 14).setWidth 64) (FnTable.words isa s T)) ∧
      (∃ T ∈ ts, Abi.tableHeld 32 s.mem ((arg s 15).setWidth 64) (FnTable.words isa s T)) ∧
      ((tsH.map (fun T : FnTable => T.fns)).flatten ++ ((ts.map (fun T : FnTable => T.fns)).flatten ++ [])).Pairwise
        (fun f g => f ≠ g → (s.syms f).setWidth 64 ≠ (s.syms g).setWidth 64) ∧
      (arg s 14).toNat + 44 ≤ 2 ^ 32 ∧ (arg s 15).toNat + 44 ≤ 2 ^ 32 ∧
      Spec.RsaPss.digestLenOk 32 s.mem ((arg s 14).setWidth 64) (arg s 5) := by
  verify_pre at h
  sig_split h
  rename_i hsp hsa hheldH hheld hpw hrd hwr nS nA eS eA dS dA gS gA sR sTH sT sA rAr thA tA rN rE rD rG rS rR rTH rT
    rA kN kE kD kG kS kR kTH kT kA fN fE fD fG fS fR fTH fT kv el1 elK glK scrK rlK
  exact ⟨hheldH, hheld, hpw, fTH, fT, h⟩

theorem in_of_pre {tsH ts : List FnTable} {s : State} (h : (spec tsH ts).pre s)
    (hTH : TH (entered frameBytes s)) (hT : T (entered frameBytes s)) :
    In (arg s 5).toNat (ep s hai hac had TH ai au af T g) (entered frameBytes s) := by
  verify_pre at h
  sig_split h
  rename_i hsp hsa hheldH hheld hpw hrd hwr nS nA eS eA dS dA gS gA sR sTH sT sA rAr thA tA rN rE rD rG rS rR rTH rT
    rA kN kE kD kG kS kR kTH kT kA fN fE fD fG fS fR fTH fT kv el1 elK glK scrK rlK
  simp only [stackBytes, frameBytes, Nat.reduceAdd] at hsp kN kE kD kG kS kR kTH kT kA
  obtain h16 : 4 * Impl.RsaPkcs1Sig.X86.savedRegs.length ≤ (s.gpr .esp).toNat := by
    simp only [Impl.RsaPkcs1Sig.X86.savedRegs, List.length_cons, List.length_nil]; omega_arith
  obtain hpush : Frame [below (s.gpr .esp) (4 * Impl.RsaPkcs1Sig.X86.savedRegs.length)] s.mem
      (entered frameBytes s).mem :=
    pushed_frame (by decide) h16
  obtain below16 : Region.Sub (below (s.gpr .esp) (4 * Impl.RsaPkcs1Sig.X86.savedRegs.length))
      ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 260, 260⟩ := by
    simp only [below, Impl.RsaPkcs1Sig.X86.savedRegs, List.length_cons, List.length_nil]
    rw [Taint.sub_setWidth (by omega_arith)]
    exact Offset.sub_below _ (by omega_arith) (by omega_arith)
  refine
    { ok := ?_
      kv := kv, el1 := el1, elK := elK, glK := glK, scrK := scrK, rlK := rlK
      slt32 := (arg s 8).isLt
      scl32 := (arg s 11).isLt
      nB := Proof.RsaPkcs1Sig.bytesAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kN.sub_left below16).symm)
        (by show (arg s 1).toNat ≤ 2 ^ 64; omega_arith)
      eB := Proof.RsaPkcs1Sig.bytesAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kE.sub_left below16).symm)
        (by show (arg s 3).toNat ≤ 2 ^ 64; omega_arith)
      pw := Proof.RsaPkcs1Sig.wordsAt_frame' hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kR.sub_left below16).symm)
        (by show (arg s 13).toNat * 8 ≤ 2 ^ 64; have := (arg s 13).isLt; omega_arith)
      tabTH := hTH
      tabT := hT }
  rw [ep_lay]
  refine ok_entered (S := 260) rfl (by decide) hsp (by simp) (by simp; omega_arith) hrd
    (by rw [hwr]; rfl) ?_ ?_ ?_ ?_ ?_ ?_
  · intro r hr
    simp only [EP.ro, EP.rw, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [kN, kE, kD, kG, kR, kTH, kT, kS]
  · intro r hr
    simp only [EP.rw, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact rS
  · intro w hw r hr
    simp only [EP.rw, List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [EP.ro, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hw
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [nS.symm, eS.symm, dS.symm, gS.symm, sR, sTH, sT, sA]
  · exact List.pairwise_singleton _ _
  · intro r hr
    simp only [EP.ro, EP.rw, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [ep, BitVec.toNat_setWidth, Sig.tableRegion]
    all_goals first
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 0).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 2).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 4).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 6).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 12).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 14).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 15).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 10).isLt; omega_arith)]; omega_arith)
  · intro j hj
    have : j < 16 := hj
    rcases (by omega_using [this] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨
        j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [ep]

/-! ## Pieces at the end of the body -/

/-- Correct, and constant time with nothing after it. -/
def VQ (F : State → State → Prop) (c : Prog isa) (G : State → State → Prop) : Prop :=
  (∀ σ s, F σ s → WP isa c s (G σ)) ∧ RelCT isa (Two F) c fun _ _ => True

theorem VQ.of_vp {F G : State → State → Prop} {c : Prog isa} (h : VP F c G) : VQ F c G :=
  ⟨h.wp, h.ct.mono (fun _ _ h => h) fun _ _ _ => trivial⟩

theorem VQ.seq {F G H : State → State → Prop} {c₁ c₂ : Prog isa} (h₁ : VP F c₁ G) (h₂ : VQ G c₂ H) :
    VQ F (.seq c₁ c₂) H :=
  ⟨fun σ s hs => WP.seq (WP.mono (h₁.wp σ s hs) fun t ht => h₂.1 σ t ht), RelCT.seq h₁.ct h₂.2⟩

theorem VQ.ite {F G : State → State → Prop} {c : Cond} {t e : Prog isa}
    (hd : ∀ σ s, F σ s → ∃ b, isa.eval c s = some b)
    (hc : ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → isa.eval c s₁ = isa.eval c s₂)
    (ht : VQ (fun σ s => F σ s ∧ isa.eval c s = some true) t G)
    (he : VQ (fun σ s => F σ s ∧ isa.eval c s = some false) e G) : VQ F (.ite c t e) G := by
  refine ⟨fun σ s hs => ?_, ?_⟩
  · obtain ⟨b, hb⟩ := hd σ s hs
    exact WP.ite b hb (fun h => ht.1 σ s ⟨hs, by rw [hb, h]⟩) (fun h => he.1 σ s ⟨hs, by rw [hb, h]⟩)
  · refine RelCT.ite (fun s₁ s₂ ⟨σ₁, σ₂, h₁, h₂⟩ => hc _ _ _ _ h₁ h₂) ?_ ?_
    · exact ht.2.mono (fun s₁ s₂ ⟨⟨σ₁, σ₂, h₁, h₂⟩, e⟩ =>
        ⟨σ₁, σ₂, ⟨h₁, e⟩, h₂, (hc _ _ _ _ h₁ h₂).symm.trans e⟩) fun _ _ h => h
    · exact he.2.mono (fun s₁ s₂ ⟨⟨σ₁, σ₂, h₁, h₂⟩, e⟩ =>
        ⟨σ₁, σ₂, ⟨h₁, e⟩, h₂, (hc _ _ _ _ h₁ h₂).symm.trans e⟩) fun _ _ h => h

/-- A piece proven over the state it starts from, as a piece of a run from `σ`. -/
theorem VQ.reidx {F F' G G' : State → State → Prop} {c : Prog isa} (h : VP F' c G')
    (hF : ∀ σ s, F σ s → F' s s) (hG : ∀ σ s t, F σ s → G' s t → G σ t) : VQ F c G :=
  ⟨fun σ s hs => WP.mono (h.wp s s (hF σ s hs)) fun t ht => hG σ s t hs ht,
    h.ct.mono (fun s₁ s₂ ⟨_, _, h₁, h₂⟩ => ⟨s₁, s₂, hF _ _ h₁, hF _ _ h₂⟩) fun _ _ _ => trivial⟩

end VG.Proof.RsaPss.X86.Vf

end

end


/-!
# RSASSA-PSS verification with a precomputed public key on x86: the checks

As on ARMv7 (`Proof/RsaPss/Arm/VfFixed.lean`): `scratch` into `ebp`,
`[any_salt_len ≠ 0]` to its slot and the expected salt length `sLen`
(`salt_len`, or 0 if any) for `params`, then the encoding's parameters and
whether everything fits (`chk_vp`): the modulus' first byte not zero, and
`lo + hLen + 2 + sLen ≤ k`; if not, 0 (`fail_vp`), as the specification
answers (`verify_false`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Vf

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes

variable (h : PssHash)

/-- A state of the body. -/
abbrev S (P : EP) (σ s : State) : Prop := In h.D P σ ∧ (P.lay h.D).St σ s

/-- The modulus' first byte, `lo`, the salt length the checks take, and
whether everything fits. -/
abbrev n0 (P : EP) : Byte := P.nB.getD 0 0
abbrev lo (P : EP) : Nat := if (n0 P).toNat ≤ 1 then 1 else 0
abbrev eLen (P : EP) : Nat := if P.any = 0 then P.slt else 0
abbrev fits (P : EP) : Prop := n0 P ≠ 0 ∧ lo P + h.D + 2 + eLen P ≤ P.K

/-- The salt length verification expects. -/
abbrev sLenO (P : EP) : Option Nat := if P.any = 0 then some P.slt else none

/-- The buffers the body only reads, in the run from `σ`. -/
abbrev digB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (P.dig.setWidth 64) h.D
abbrev sigB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (P.sig.setWidth 64) P.K

/-- The result, with MGF1's hash function that of `P.g`. -/
abbrev Res (P : EP) (σ : State) (r : BitVec 32) : Prop :=
  Spec.Rsa.publicPrecompute P.nB = some P.pw →
    r = if Spec.RsaPss.verify h.G P.g.G P.nB P.eB (digB h P σ) (sigB P σ) (sLenO P) then 1 else 0

/-- The end of the body. -/
abbrev Fin (P : EP) (σ s : State) : Prop := S h P σ s ∧ Res h P σ (s.gpr .eax)

/-- The modulus' first byte, in a state of the body. -/
theorem n0_at {D : Nat} {P : EP} {σ s : State} (hi : In D P σ) (hs : (P.lay D).St σ s) :
    s.mem (addr P.n 0) = n0 P ∧ InRegions (s.rd ++ s.wr) (addr P.n 0) 1 := by
  have hK := hi.k64
  obtain a : addr P.n 0 = P.n.setWidth 64 := by simp [addr]
  rw [a]
  refine ⟨?_, ⟨P.N, by rw [hs.rd]; exact List.mem_append_left _ (hi.ok.rd _ (by simp)), by
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using [hK]⟩⟩
  obtain e : Spec.Rsa.bytesAt s.mem (P.n.setWidth 64) P.K = P.nB := (hs.ro (R := P.N) (by simp)).trans hi.nB
  show s.mem (P.n.setWidth 64) = P.nB.getD 0 0
  rw [← e, RsaPkcs1Sig.bytesAt_getD (by omega_using [hK]), BitVec.add_zero]

/-- `[any_salt_len ≠ 0]`, in its slot. -/
abbrev anyW (P : EP) : BitVec 32 := if P.any = 0 then 0 else 1

/-- After `verifyChk`. -/
abbrev C0 (P : EP) (σ s : State) : Prop :=
  Ctx (P.lay h.D) P.scr σ s ∧ In h.D P σ ∧ s.gpr .esi = P.n ∧ s.gpr .ecx = BitVec.ofNat 32 P.K ∧
    s.gpr .edx = BitVec.ofNat 32 (eLen P) ∧ s.mem.readW ((P.lay h.D).fr sAny) 32 = anyW P

/-- After the checks. -/
abbrev C1 (P : EP) (σ s : State) : Prop :=
  Ctx (P.lay h.D) P.scr σ s ∧ In h.D P σ ∧ s.mem.readW ((P.lay h.D).fr sC) 32 = cW ((n0 P).setWidth 32) ∧
    s.mem.readW ((P.lay h.D).fr sLo) 32 = BitVec.ofNat 32 (lo P) ∧
    s.mem.readW ((P.lay h.D).fr sDb) 32 = dbW P.K h.D ((n0 P).setWidth 32) ∧
    s.mem.readW ((P.lay h.D).fr sAny) 32 = anyW P ∧ s.zf = some (decide (fits h P))

theorem any_lt (a : BitVec 32) : decide ((0 : BitVec 32).toNat < a.toNat) = !decide (a = 0) := by
  by_cases e : a = 0
  · subst e; rfl
  · have : a.toNat ≠ 0 := fun h' => e (BitVec.eq_of_toNat_eq h')
    show decide (0 < a.toNat) = _
    simp only [e, decide_false, Bool.not_false]
    exact decide_eq_true (by omega_using [this])

theorem and_mask (x : BitVec 32) (c : Bool) :
    x &&& ((if c then BitVec.allOnes 32 else 0) ^^^ BitVec.allOnes 32) = if c then 0 else x := by
  cases c
  · show x &&& (0#32 ^^^ BitVec.allOnes 32) = x
    rw [BitVec.zero_xor, BitVec.and_allOnes]
  · show x &&& (BitVec.allOnes 32 ^^^ BitVec.allOnes 32) = 0
    rw [BitVec.xor_self, BitVec.and_zero]; rfl

theorem mask_and1 (c : Bool) : (if c then BitVec.allOnes 32 else 0) &&& 1 = if c then 1 else 0 := by
  cases c <;> rfl

theorem chk_vp (P : EP) : VP (S h P) (.block (verifyChk ++ params h.H)) (C1 h P) := by
  refine VP.block_append (G := C0 h P) (VP.taint [.esp] verifyChk_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.sp, h₂.2.sp]) fun σ s ⟨hi, hs⟩ => ?_)
    (VP.taint _ h.certs.params (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s ⟨hc, hi, si, cx, dx, sa⟩ => ?_)
  · have hl : ∀ j, j < 16 → j < ((P.lay h.D).argv).length := fun j hj => by simp; omega_using [hj]
    have hg := hi.geo
    simp only [verifyChk, ld, st, mi]
    refine hs.wp_arg (hl 10 (by decide)) (by decide) fun t1 s1 u1 => ?_
    obtain c1 : Ctx (P.lay h.D) P.scr σ t1 := ⟨s1, by rw [u1.gpr]; rfl⟩
    refine c1.wp_arg hg (hl 8 (by decide)) (by decide) (by decide) fun t2 c2 u2 => ?_
    refine c2.wp_arg hg (hl 9 (by decide)) (by decide) (by decide) fun t3 c3 u3 => ?_
    refine wp_movi fun t4 u4 => wp_cmp fun t5 f5 cf5 _ => wp_sbb_self cf5 fun t6 u6 => ?_
    obtain c6 := ((c3.upd u4 (by decide) (by decide)).fupd f5).upd u6 (by decide) (by decide)
    refine wp_mov fun t7 u7 => wp_andi fun t8 u8 => ?_
    obtain c8 := (c6.upd u7 (by decide) (by decide)).upd u8 (by decide) (by decide)
    refine c8.wp_st hg (d := sAny) (by decide) fun t9 c9 m9 => ?_
    refine wp_xorI fun t10 u10 => wp_and fun t11 u11 => ?_
    obtain c11 := (c9.upd u10 (by decide) (by decide)).upd u11 (by decide) (by decide)
    refine c11.wp_arg hg (hl 0 (by decide)) (by decide) (by decide) fun t12 c12 u12 => ?_
    refine c12.wp_arg hg (hl 1 (by decide)) (by decide) (by decide) fun t13 c13 u13 => WP.block_nil ?_
    obtain e8 : t3.gpr .edi = P.any := by rw [u3.gpr]; rfl
    obtain e4 : t4.gpr .edi = P.any := by rw [u4.other _ (by decide), e8]
    obtain e5 : t4.gpr .eax = 0 := by rw [u4.gpr]; rfl
    rw [e5, e4, any_lt] at u6
    refine ⟨c13, hi, ?_, ?_, ?_, ?_⟩
    · simp (disch := decide) only [u13.other, u12.gpr]; rfl
    · rw [u13.gpr]; rfl
    · simp (disch := decide) only [u13.other, u12.other, u11.gpr, u10.gpr, u10.other, f5.gpr, u6.gpr,
        u6.other, u7.other, u8.other, m9.gpr, u4.other, u3.other, u2.gpr]
      rw [and_mask]
      by_cases e : P.any = 0
      · rw [ite_eq_right (c := (!decide (P.any = 0)) = true) (fun h' => by
          rw [decide_eq_true e] at h'; exact absurd h' (by decide))]
        show _ = BitVec.ofNat 32 (if P.any = 0 then P.slt else 0)
        rw [ite_eq_left e]; rfl
      · rw [ite_eq_left (c := (!decide (P.any = 0)) = true) (by rw [decide_eq_false e]; rfl)]
        show _ = BitVec.ofNat 32 (if P.any = 0 then P.slt else 0)
        rw [ite_eq_right e]; rfl
    · rw [u13.mem, u12.mem, u11.mem, u10.mem, m9.mem, Mem.readW_writeW_self32]
      simp (disch := decide) only [u8.gpr, u7.gpr, u6.gpr]
      rw [mask_and1]
      by_cases e : P.any = 0
      · rw [ite_eq_right (c := (!decide (P.any = 0)) = true) (fun h' => by
          rw [decide_eq_true e] at h'; exact absurd h' (by decide))]
        show _ = if P.any = 0 then 0 else 1
        rw [ite_eq_left e]
      · rw [ite_eq_left (c := (!decide (P.any = 0)) = true) (by rw [decide_eq_false e]; rfl)]
        show _ = if P.any = 0 then 0 else 1
        rw [ite_eq_right e]
  · obtain ⟨c₁, -, a1, b1, d1, -⟩ := h₁
    obtain ⟨c₂, -, a2, b2, d2, -⟩ := h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [c₁.st.sp, c₂.st.sp]
    · rw [c₁.ebp, c₂.ebp]
    · rw [a1, a2]
    · rw [b1, b2]
    · rw [d1, d2]
  have hg := hi.geo
  have hK := hi.k1024
  obtain hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega_arith
  obtain ⟨nb, hn⟩ := n0_at hi hc.st
  rw [← si] at hn nb
  refine WP.mono (params_wp h.H hg hc rfl hn cx dx) fun t ⟨m, rd, wr, sp, bp, z⟩ => ?_
  rw [nb] at m z
  obtain fr : Frame [slotR (P.lay h.D) sLo, slotR (P.lay h.D) sC, slotR (P.lay h.D) sDb] s.mem t.mem := by
    rw [m]
    exact (((slot_frame _ _ _ _).mono (by simp)).trans ((slot_frame _ _ _ _).mono (by simp))).trans
      ((slot_frame _ _ _ _).mono (by simp))
  refine ⟨hc.write fr (fun r hr => ?_) rd wr sp bp, hi, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      exact ⟨(P.lay h.D).FR, List.mem_cons_self, Offset.sub_base _ (by show _ ≤ frameBytes; decide)⟩
  · rw [m, Lay.readW_fr_other (d := sC) (e := sDb) _ _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]
  · rw [m, Lay.readW_fr_other (d := sLo) (e := sDb) _ _ _ (by decide) (by decide) (by decide),
      Lay.readW_fr_other (d := sLo) (e := sC) _ _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32, loW_byte]
  · rw [m, Mem.readW_writeW_self32]
  · rw [m, Lay.readW_fr_other (d := sAny) (e := sDb) _ _ _ (by decide) (by decide) (by decide),
      Lay.readW_fr_other (d := sAny) (e := sC) _ _ _ (by decide) (by decide) (by decide),
      Lay.readW_fr_other (d := sAny) (e := sLo) _ _ _ (by decide) (by decide) (by decide), sa]
  · rw [z, failW_z hK (show h.H.D ≤ 64 from hD) (by unfold eLen; have := hi.slt32; split <;> omega_arith)]

/-! ## When something does not fit -/

theorem nB_length {D : Nat} {P : EP} {σ : State} (hi : In D P σ) : P.nB.length = P.K := by
  rw [← hi.nB, RsaPkcs1Sig.bytesAt_len]

/-- `emLen = k - lo`, for a modulus whose first byte is not zero. -/
theorem emLen_eq {P : EP} {b : Byte} {rest : List Byte} (hbr : P.nB = b :: rest) (hl : rest.length + 1 = P.K)
    (hbt : b.toNat ≠ 0) :
    Spec.RsaPss.emLength (Spec.RsaPss.bitLength (Spec.Rsa.os2ip (b :: rest)) - 1) = P.K - lo P := by
  obtain hb0 : b ≠ 0 := fun e => hbt (by rw [e]; rfl)
  obtain e2 := RsaPss.emLength_eq rest hb0
  obtain hn0 : n0 P = b := by simp [n0, hbr]
  unfold lo; rw [hn0]
  by_cases hb1 : b.toNat = 1
  · rw [ite_eq_left hb1] at e2; rw [ite_eq_left (by omega_using [hb1])]; all_goals omega_using [hl, e2]
  · rw [ite_eq_right hb1] at e2; rw [ite_eq_right (by have := b.isLt; omega_using [hbt, hb1])]; all_goals omega_using [hl, e2]

/-- The specification refuses what does not fit. -/
theorem verify_false {P : EP} {σ : State} (hi : In h.D P σ) (hf : ¬ fits h P) :
    Spec.RsaPss.verify h.G P.g.G P.nB P.eB (digB h P σ) (sigB P σ) (sLenO P) = false := by
  obtain hl := nB_length hi
  have hK := hi.k64
  obtain ⟨b, rest, hbr⟩ : ∃ b rest, P.nB = b :: rest := by
    cases e : P.nB with
    | nil => rw [e] at hl; simp at hl; omega
    | cons b rest => exact ⟨b, rest, rfl⟩
  obtain hn0 : n0 P = b := by simp [n0, hbr]
  rw [hbr]
  by_cases hb : b.toNat = 0
  · have : b = 0 := BitVec.eq_of_toNat_eq hb
    subst this
    exact RsaPss.verify_zero₂ P.g.G h.G ..
  · rw [hbr, List.length_cons] at hl
    obtain hem := emLen_eq hbr hl hb
    refine RsaPss.verify_short₂ P.g.G h.G _ _ _ ?_
    have gl : h.G.len = h.D := h.glen
    obtain hs : (sLenO P).getD 0 = eLen P := by unfold sLenO eLen; split <;> rfl
    rw [hem, gl, hs]
    unfold fits at hf
    rw [hn0] at hf
    obtain hb0 : b ≠ 0 := fun e => hb (by rw [e]; rfl)
    have : lo P ≤ 1 := by unfold lo; split <;> omega_using []
    simp only [ne_eq, hb0, not_false_eq_true, true_and] at hf
    omega_using [hf]

theorem fail_vp (P : EP) :
    VP (fun σ s => C1 h P σ s ∧ isa.eval .ne s = some true) (.block [mi .eax 0]) (Fin h P) := by
  refine VP.taint [.esp, .ebp] ret0_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.1.1.st.sp, h₂.1.1.st.sp]
      · rw [h₁.1.1.ebp, h₂.1.1.ebp]) fun σ s ⟨⟨hc, hi, _, _, _, _, z⟩, e⟩ => ?_
  obtain hf : ¬ fits h P := fun hfits => by
    simp only [eval, z, decide_eq_true hfits] at e
    exact absurd e (by decide)
  simp only [mi]
  refine wp_movi fun t u => WP.block_nil ⟨⟨hi, hc.st.upd u (by decide)⟩, fun _ => ?_⟩
  rw [u.gpr, verify_false h hi hf]
  rfl

end VG.Proof.RsaPss.X86.Vf

end

end


/-!
# RSASSA-PSS verification with a precomputed public key on x86: the call

As on ARMv7 (`Proof/RsaPss/Arm/VfFixed.lean`): the ten arguments of
`vg_rsa_public_precomputed_checked`, one word of the frame at a time
(`pa_vp`): `EM`'s place (`oEm`), `pre`, `e`, the signature, and the rest of
`scratch` from `oRsa` on; and the call (`call_vp`, correct and constant
time: its arguments and the public data it reads are the same in two runs),
which writes RSAVP1 of the signature to `EM`, or zeros (`CR`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Vf

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes

variable (h : PssHash)

/-- `dbLen`. -/
abbrev dbN (P : EP) : Nat := P.K - lo P - h.D - 1

/-- The slots after the checks. -/
abbrev Bm (P : EP) (m : Mem) : Prop :=
  m.readW ((P.lay h.D).fr sC) 32 = cW ((n0 P).setWidth 32) ∧
    m.readW ((P.lay h.D).fr sLo) 32 = BitVec.ofNat 32 (lo P) ∧
    m.readW ((P.lay h.D).fr sDb) 32 = BitVec.ofNat 32 (dbN h P) ∧ m.readW ((P.lay h.D).fr sAny) 32 = anyW P

/-- When everything fits. -/
abbrev M0 (P : EP) (σ s : State) : Prop := Ctx (P.lay h.D) P.scr σ s ∧ In h.D P σ ∧ fits h P ∧ Bm h P s.mem

theorem m0_of {P : EP} {σ s : State} (hc : C1 h P σ s) (e : isa.eval .ne s = some false) : M0 h P σ s := by
  obtain ⟨hc, hi, sc, sl, sd, sa, z⟩ := hc
  obtain hf : fits h P := by
    simp only [eval, z, Option.map_some, Option.some.injEq, Bool.not_eq_false', decide_eq_true_eq] at e
    exact e
  refine ⟨hc, hi, hf, sc, sl, ?_, sa⟩
  rw [sd, dbW_byte]
  have : lo P ≤ 1 := by unfold lo; split <;> omega_arith
  rw [Offset.ofNat_sub_ofNat (show lo P ≤ P.K by have := hf.2; omega_arith), Offset.ofNat_sub_ofNat (by have := hf.2; omega_arith)]
  congr 1

/-- The slots of the parameters keep their words through a frame missing them. -/
theorem Bm.keep {P : EP} {m m' : Mem} {rs : List Region} (hb : Bm h P m) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, ∀ d ∈ [sC, sLo, sDb, sAny], (slotR (P.lay h.D) d).Disjoint r) : Bm h P m' :=
  ⟨slot_keep hf (fun r hr => hd r hr sC (by simp)) hb.1, slot_keep hf (fun r hr => hd r hr sLo (by simp)) hb.2.1,
    slot_keep hf (fun r hr => hd r hr sDb (by simp)) hb.2.2.1, slot_keep hf (fun r hr => hd r hr sAny (by simp)) hb.2.2.2⟩

/-- The call's arguments. -/
abbrev outv (P : EP) : List (BitVec 32) :=
  pubArgv (P.scr + BitVec.ofNat 32 oEm) P.pre P.e P.sig (P.scr + BitVec.ofNat 32 oRsa) P.K P.rl P.el (P.scl - 1024)

/-- The first `k` of them in the frame. -/
def Slots (P : EP) (m : Mem) (k : Nat) : Prop :=
  ∀ i < k, m.readW ((P.lay h.D).fr (4 * i)) 32 = (outv P).getD i 0

/-- During the call's arguments. -/
abbrev A0 (P : EP) (σ s : State) (k : Nat) : Prop := M0 h P σ s ∧ Slots h P s.mem k

theorem vf_arg {j : Nat} (hj : j < 16) {P : EP} : j < ((P.lay h.D).argv).length := by simp; omega_arith

/-- A word stored below the slots keeps them. -/
theorem keepSlot {P : EP} {m : Mem} {d : Nat} (hd : d + 4 ≤ sLo) (v : BitVec 32) (hb : Bm h P m) :
    Bm h P (m.writeW ((P.lay h.D).fr d) v) :=
  hb.keep h (slot_frame (P.lay h.D) m d v) fun r hr e he => by
    simp only [List.mem_singleton] at hr; subst hr
    have e1 : sLo = 40 := rfl
    have e2 : sC = 44 := rfl
    have e3 : sDb = 48 := rfl
    have e4 : sAny = 52 := rfl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> exact slotSep (by decide) (by unfold frameBytes; omega_arith) (by omega_arith)

theorem slots_next {P : EP} {m : Mem} {i : Nat} (hs : Slots h P m i) (hi : i < 10) (v : BitVec 32)
    (hv : v = (outv P).getD i 0) : Slots h P (m.writeW ((P.lay h.D).fr (4 * i)) v) (i + 1) := by
  intro k hk
  rcases (by omega_arith : k = i ∨ k < i) with rfl | hki
  · rw [Mem.readW_writeW_self32, hv]
  · rw [Lay.readW_fr_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
    exact hs k hki

/-- `mov eax, [arg j]; mov [esp + 4 i], eax`: argument `j` to the call's argument `i`. -/
theorem copySlot {P : EP} {σ s : State} {i j : Nat} (ha : A0 h P σ s i) (hi : i < 10)
    (hj : j < 16) (hv : (P.argv h.D).getD j 0 = (outv P).getD i 0) {is : List Instr} {Q : State → Prop}
    (kk : ∀ t, A0 h P σ t (i + 1) → WP isa (.block is) t Q) :
    WP isa (.block (copyArg j i ++ is)) s Q := by
  obtain ⟨⟨hc, hin, hf, hb⟩, hs⟩ := ha
  have hg := hin.geo
  simp only [copyArg, ld, st, List.cons_append, List.nil_append]
  refine hc.wp_arg hg (vf_arg h hj) (by decide) (by decide) fun t1 c1 u1 =>
    c1.wp_st hg (d := 4 * i) (by unfold frameBytes; omega_arith) fun t2 c2 m2 => kk t2 ⟨⟨c2, hin, hf, ?_⟩, ?_⟩
  · rw [m2.mem, u1.mem]
    exact keepSlot h (show 4 * i + 4 ≤ sLo by unfold sLo; omega_arith) _ hb
  · rw [m2.mem, u1.mem, u1.gpr]
    exact slots_next h hs hi _ hv

/-- `scratch + o` to the call's argument `i`. -/
theorem scrSlot {P : EP} {σ s : State} {i o : Nat} (ha : A0 h P σ s i) (hi : i < 10)
    (hv : P.scr + BitVec.ofNat 32 o = (outv P).getD i 0) {is : List Instr} {Q : State → Prop}
    (kk : ∀ t, A0 h P σ t (i + 1) → WP isa (.block is) t Q) :
    WP isa (.block (atS .eax o ++ [st .eax (4 * i)] ++ is)) s Q := by
  obtain ⟨⟨hc, hin, hf, hb⟩, hs⟩ := ha
  have hg := hin.geo
  simp only [atS, addi, st, List.cons_append, List.nil_append]
  refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
  refine ((hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)).wp_st hg (d := 4 * i)
    (by unfold frameBytes; omega_arith) fun t3 c3 m3 => kk t3 ⟨⟨c3, hin, hf, ?_⟩, ?_⟩
  · rw [m3.mem, u2.mem, u1.mem]
    exact keepSlot h (show 4 * i + 4 ≤ sLo by unfold sLo; omega_arith) _ hb
  · rw [m3.mem, u2.mem, u1.mem, u2.gpr, u1.gpr, hc.ebp]
    exact slots_next h hs hi _ hv

theorem pubArgs_eq : pubArgs = (atS .eax oEm ++ [st .eax (4 * 0)]) ++ copyArg 1 1 ++ copyArg 12 2 ++
    copyArg 13 3 ++ copyArg 2 4 ++ copyArg 3 5 ++ copyArg 6 6 ++ copyArg 1 7 ++
    (atS .eax oRsa ++ [st .eax (4 * 8)]) ++ [ld .eax (arg 11), .alu .sub .eax (.imm 1024), st .eax (4 * 9)] := by
  simp only [pubArgs, List.append_assoc]; rfl

/-- Before the call. -/
abbrev V1 (P : EP) (σ s : State) : Prop :=
  M0 h P σ s ∧ PubArgs s (P.scr + BitVec.ofNat 32 oEm) P.pre P.e P.sig (P.scr + BitVec.ofNat 32 oRsa) P.K P.rl
    P.el (P.scl - 1024)

theorem pa_vp (P : EP) : VP (M0 h P) (.block pubArgs) (V1 h P) := by
  refine VP.taint [.esp, .ebp] pubArgs_taint (sp_bp fun _ _ h => h.1) fun σ s hm => ?_
  have hi := hm.2.1
  have hg := hi.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have hs1 := hi.pubScr
  rw [pubArgs_eq]
  simp only [List.append_assoc]
  obtain z0 : A0 h P σ s 0 := ⟨hm, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  refine scrSlot h z0 (by decide) (by simp [outv, pubArgv]) fun t1 z1 => ?_
  refine copySlot h z1 (by decide) (j := 1) (by decide) (by simp [EP.argv, outv, pubArgv]) fun t2 z2 => ?_
  refine copySlot h z2 (by decide) (j := 12) (by decide) (by simp [EP.argv, outv, pubArgv]) fun t3 z3 => ?_
  refine copySlot h z3 (by decide) (j := 13) (by decide) (by simp [EP.argv, outv, pubArgv]) fun t4 z4 => ?_
  refine copySlot h z4 (by decide) (j := 2) (by decide) (by simp [EP.argv, outv, pubArgv]) fun t5 z5 => ?_
  refine copySlot h z5 (by decide) (j := 3) (by decide) (by simp [EP.argv, outv, pubArgv]) fun t6 z6 => ?_
  refine copySlot h z6 (by decide) (j := 6) (by decide) (by simp [EP.argv, outv, pubArgv, hi.glK]) fun t7 z7 => ?_
  refine copySlot h z7 (by decide) (j := 1) (by decide) (by simp [EP.argv, outv, pubArgv]) fun t8 z8 => ?_
  rw [← List.append_assoc (atS .eax oRsa)]
  refine scrSlot h z8 (by decide) (by simp [outv, pubArgv]) fun t9 z9 => ?_
  obtain ⟨⟨c9, -, hf9, b9⟩, s9⟩ := z9
  simp only [ld, st]
  refine c9.wp_arg hg (vf_arg h (j := 11) (by decide)) (by decide) (by decide) fun t10 c10 u10 =>
    wp_subi fun t11 u11 _ _ => (c10.upd u11 (by decide) (by decide)).wp_st hg (d := 4 * 9) (by decide)
      fun t12 c12 m12 => WP.block_nil ?_
  obtain v : t11.gpr .eax = BitVec.ofNat 32 (P.scl - 1024) := by
    rw [u11.gpr, u10.gpr]
    exact Offset.ofNat_sub_ofNat (w := 32) (d := 1024) (by omega_arith)
  obtain m : t12.mem = t9.mem.writeW ((P.lay h.D).fr (4 * 9)) (t11.gpr .eax) := by
    rw [m12.mem, u11.mem, u10.mem]
  obtain kb := keepSlot h (show 4 * 9 + 4 ≤ sLo by decide) (t11.gpr .eax) b9
  obtain sl := slots_next h s9 (by decide) _ (v.trans (by simp [outv, pubArgv]))
  rw [← m] at kb sl
  have hfit := ok.fit
  simp only [Lay.A, EP.argv, List.length_cons, List.length_nil, frameBytes] at hfit
  refine ⟨⟨c12, hi, hf9, kb⟩, fun i hi' => ?_, by rw [c12.st.sp]; have : 100 ≤ P.B.toNat := ok.BC; show 100 ≤ P.B.toNat; omega_arith,
    by rw [c12.st.sp]; show P.B.toNat + 40 ≤ _; omega_arith, hi.kv, hi.rlK, hi.el1, hi.elK, hs1.1,
    by have := hi.scl32; omega_arith⟩
  rw [c12.st.sp, hg.aFr ok (4 * i) (by unfold frameBytes; omega_arith)]
  exact sl i hi'

/-- What the call writes to `EM` and returns. -/
abbrev CR (P : EP) (σ : State) (m : Mem) (r : BitVec 32) : Prop :=
  Spec.Rsa.publicPrecompute P.nB = some P.pw →
    Spec.Rsa.written m ((P.scr + BitVec.ofNat 32 oEm).setWidth 64) P.K r
      (Spec.Rsa.publicOpChecked P.nB P.eB (sigB P σ))

/-- After the call. -/
abbrev V2 (P : EP) (σ s : State) : Prop := M0 h P σ s ∧ CR P σ s.mem (s.gpr .eax)

/-- The call's output and working space, in `scratch`. -/
abbrev emR (P : EP) : Region := ⟨(P.scr + BitVec.ofNat 32 oEm).setWidth 64, P.K⟩
abbrev scrR (P : EP) : Region := ⟨(P.scr + BitVec.ofNat 32 oRsa).setWidth 64, (P.scl - 1024) * 8⟩

theorem call_geo {P : EP} {σ : State} (hi : In h.D P σ) :
    (P.scr + BitVec.ofNat 32 oEm).setWidth 64 = P.scr.setWidth 64 + BitVec.ofNat 64 oEm ∧
    (P.scr + BitVec.ofNat 32 oRsa).setWidth 64 = P.scr.setWidth 64 + BitVec.ofNat 64 oRsa ∧
    Region.Sub (emR P) P.SCR ∧ Region.Sub (scrR P) P.SCR ∧ (emR P).Disjoint (scrR P) ∧
    P.scr.toNat + P.scl * 8 ≤ 2 ^ 32 ∧ 1025 ≤ P.scl ∧ P.K ≤ 1024 := by
  obtain hf := hi.ok.fits P.SCR (by simp)
  simp only [BitVec.toNat_setWidth] at hf
  rw [Nat.mod_eq_of_lt (by have := P.scr.isLt; omega_arith)] at hf
  have hs := hi.pubScr.2
  have hK := hi.k1024
  obtain e1 : (P.scr + BitVec.ofNat 32 oEm).setWidth 64 = P.scr.setWidth 64 + BitVec.ofNat 64 oEm :=
    addr_eq (by unfold oEm; omega_arith)
  obtain e2 : (P.scr + BitVec.ofNat 32 oRsa).setWidth 64 = P.scr.setWidth 64 + BitVec.ofNat 64 oRsa :=
    addr_eq (by unfold oRsa; omega_arith)
  refine ⟨e1, e2, ?_, ?_, ?_, hf, hs, hK⟩
  · rw [emR, e1]; exact Offset.sub_base _ (by unfold oEm; omega_arith)
  · rw [scrR, e2]; exact Offset.sub_base _ (by unfold oRsa; omega_arith)
  · rw [emR, scrR, e1, e2]; exact Offset.disjoint _ (by unfold oEm oRsa; omega_arith) (by unfold oEm; omega_arith)
      (by unfold oRsa; omega_arith)

theorem sigR {P : EP} {σ : State} (hi : In h.D P σ) : (⟨P.sig.setWidth 64, P.K⟩ : Region) = P.SIG := by
  show _ = (⟨P.sig.setWidth 64, P.gl⟩ : Region); rw [hi.glK]

theorem nB_at {P : EP} {σ s : State} (hi : In h.D P σ) (hs : (P.lay h.D).St σ s) :
    Spec.Rsa.bytesAt s.mem (P.n.setWidth 64) P.K = P.nB := (hs.ro (R := P.N) (by simp)).trans hi.nB

theorem eB_at {P : EP} {σ s : State} (hi : In h.D P σ) (hs : (P.lay h.D).St σ s) :
    Spec.Rsa.bytesAt s.mem (P.e.setWidth 64) P.el = P.eB := (hs.ro (R := P.E) (by simp)).trans hi.eB

/-- `pre`'s words, in a state of the body. -/
theorem pw_at {P : EP} {σ s : State} (hi : In h.D P σ) (hs : (P.lay h.D).St σ s) :
    Spec.Rsa.wordsAt s.mem (P.pre.setWidth 64) P.rl = P.pw := by
  have ok := hi.ok
  obtain hR : P.PRE ∈ (P.lay h.D).ro := by simp
  obtain hf : (P.pre.setWidth 64).toNat + P.rl * 8 ≤ 2 ^ 32 := ok.fits P.PRE (List.mem_append_left _ hR)
  refine (Proof.RsaPkcs1Sig.wordsAt_frame' hs.frame (fun r hr => ?_) (by omega_arith)).trans hi.pw
  simp only [Lay.W, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
    false_or] at hr
  rcases hr with rfl | rfl | rfl
  · exact ((ok.stk P.PRE (List.mem_append_left _ hR)).sub_left Lay.FR_stk).symm
  · exact (ok.wro P.SCR (by simp) P.PRE (List.mem_append_left _ hR)).symm
  · exact ((ok.stk P.PRE (List.mem_append_left _ hR)).sub_left Lay.low_stk).symm

/-- `pre`'s words, in a callee's entry state. -/
theorem callPw {P : EP} {σ s : State} (hi : In h.D P σ) (hs : (P.lay h.D).St σ s) :
    Spec.Rsa.wordsAt s.callEntry.mem (P.pre.setWidth 64) P.rl = P.pw := by
  have ok := hi.ok
  obtain hR : P.PRE ∈ (P.lay h.D).ro := by simp
  obtain hf : (P.pre.setWidth 64).toNat + P.rl * 8 ≤ 2 ^ 32 := ok.fits P.PRE (List.mem_append_left _ hR)
  refine (Proof.RsaPkcs1Sig.wordsAt_frame' (hs.callEntry_frame (by show 4 ≤ 100; decide)) (fun r hr => ?_)
    (by omega_arith)).trans (pw_at h hi hs)
  simp only [List.mem_singleton] at hr; subst hr
  exact ((ok.stk P.PRE (List.mem_append_left _ hR)).sub_left Lay.low_stk).symm

theorem call_vp (P : EP) (c : Ver.PublicImpl) : VP (V1 h P) (.call c.name c.code) (V2 h P) := by
  refine VP.call c.verified.1 c.verified.2.1 c.noSp
    (pubRd P.pre P.e P.sig P.K P.rl P.el) (pubWr P.B (P.scr + BitVec.ofNat 32 oEm) (P.scr + BitVec.ofNat 32 oRsa)
      P.K (P.scl - 1024))
    (fun σ s hr => ?_) (fun σ s hr => ?_) (fun σ s hr => ?_)
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.1.1.st.sp, h₂.1.1.st.sp]) (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_)
    (fun σ s s' hr rd wr cs fr po => ?_)
  · -- The callee's precondition.
    obtain ⟨⟨hc, hi, -, -⟩, pa⟩ := hr
    have ok := hi.ok
    obtain ⟨e1, e2, sI, sS', dIS, hf, hs1, hK⟩ := call_geo h hi
    have fit := ok.fit
    simp only [Lay.A, EP.argv, List.length_cons, List.length_nil, frameBytes] at fit
    obtain sg := sigR h hi
    obtain args0 : (⟨P.B.setWidth 64, 40⟩ : Region) = ⟨(P.lay h.D).fr 0, 40⟩ := by simp
    have hsp := hc.st.sp
    rw [show (P.lay h.D).B = P.B from rfl] at hsp
    rw [← hsp] at args0
    rw [← hsp]
    refine pub_pre pa ?_ ?_ ?_ ?_
    · intro w hw r hr
      simp only [pubWr, List.mem_cons, List.not_mem_nil, or_false] at hw
      simp only [pubRd, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hw with rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl
      · exact (ok.rw_ro (w := P.SCR) (r := P.PRE) (by simp) (by simp)).sub_left sI
      · exact (ok.rw_ro (w := P.SCR) (r := P.E) (by simp) (by simp)).sub_left sI
      · rw [sg]; exact (ok.rw_ro (w := P.SCR) (r := P.SIG) (by simp) (by simp)).sub_left sI
      · exact (ok.rw_ro (w := P.SCR) (r := P.PRE) (by simp) (by simp)).sub_left sS'
      · exact (ok.rw_ro (w := P.SCR) (r := P.E) (by simp) (by simp)).sub_left sS'
      · rw [sg]; exact (ok.rw_ro (w := P.SCR) (r := P.SIG) (by simp) (by simp)).sub_left sS'
      all_goals rw [args0]
      · exact ok.stk_fr (.inl (by simp)) (by show 0 + 40 ≤ frameBytes + 16; decide)
      · exact ok.stk_fr (.inl (by simp)) (by show 0 + 40 ≤ frameBytes + 16; decide)
      · rw [sg]; exact ok.stk_fr (.inl (by simp)) (by show 0 + 40 ≤ frameBytes + 16; decide)
    · simp only [pubWr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, List.Pairwise.nil, and_true]
      refine ⟨⟨dIS, ?_⟩, ?_⟩
      · rw [args0]; exact ((ok.stk_fr (R := P.SCR) (.inr (by simp))
          (by show 0 + 40 ≤ frameBytes + 16; decide)).symm).sub_left sI
      · rw [args0]; exact ⟨((ok.stk_fr (R := P.SCR) (.inr (by simp))
          (by show 0 + 40 ≤ frameBytes + 16; decide)).symm).sub_left sS', fun _ h => h.elim⟩
    · intro r hr
      obtain low : Region.Sub (below P.B 100) (P.lay h.D).LOW := by
        rw [← ok.low_eq]; exact below_sub (show 100 ≤ 100 by decide) ok.BC
      rw [hsp]
      simp only [pubWr, pubRd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ((ok.low_buf (R := P.SCR) (.inr (by simp))).sub_right sI).sub_left low
      · exact ((ok.low_buf (R := P.SCR) (.inr (by simp))).sub_right sS').sub_left low
      · rw [args0]; exact ((Lay.fr_low (by omega_arith) (by show (100 : Nat) ≤ 2 ^ 32; decide)).symm).sub_left low
      · exact (ok.low_buf (R := P.PRE) (.inl (by simp))).sub_left low
      · exact (ok.low_buf (R := P.E) (.inl (by simp))).sub_left low
      · rw [sg]; exact (ok.low_buf (R := P.SIG) (.inl (by simp))).sub_left low
    · intro r hr
      have hg := hi.geo
      simp only [pubWr, pubRd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · show ((P.scr + BitVec.ofNat 32 oEm).setWidth 64).toNat + P.K ≤ 2 ^ 32
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (P.scr + BitVec.ofNat 32 oEm).isLt; omega_arith),
          hg.scr_lt (by decide)]
        unfold oEm; omega_arith
      · show ((P.scr + BitVec.ofNat 32 oRsa).setWidth 64).toNat + (P.scl - 1024) * 8 ≤ 2 ^ 32
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (P.scr + BitVec.ofNat 32 oRsa).isLt; omega_arith),
          hg.scr_lt (Nat.le_refl _)]
        unfold oRsa; omega_arith
      · rw [hsp]
        show (P.B.setWidth 64).toNat + 40 ≤ 2 ^ 32
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := P.B.isLt; omega_arith)]
        omega_arith
      · exact ok.fits _ (by simp)
      · exact ok.fits _ (by simp)
      · rw [sg]; exact ok.fits _ (by simp)
  · -- What the callee is given is ours.
    obtain ⟨⟨hc, hi, -, -⟩, -⟩ := hr
    have ok := hi.ok
    have hs := hc.st
    obtain ⟨e1, e2, sI, sS', dIS, hf, hs1, hK⟩ := call_geo h hi
    obtain hro : ∀ R ∈ (P.lay h.D).ro, Covers [R] (s.rd ++ s.wr) := fun R hR =>
      Covers.of_mem fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hs.inRo hR
    obtain inS : ∀ {o n : Nat}, o + n ≤ P.scl * 8 → Covers [⟨P.scr.setWidth 64 + BitVec.ofNat 64 o, n⟩] s.wr :=
      fun hon => Covers.one ⟨P.SCR, hs.inRw (by simp), Offset.contains_base _ hon (by omega_arith)⟩
    obtain hA : Covers [⟨P.B.setWidth 64, 40⟩] s.wr := by
      have := hs.inFr (d := 0) (n := 40) (by simp only [frameBytes]; omega_arith)
      simp only [Lay.fr, BitVec.add_zero] at this
      exact Covers.one this
    obtain wr : Covers (pubWr P.B (P.scr + BitVec.ofNat 32 oEm) (P.scr + BitVec.ofNat 32 oRsa) P.K (P.scl - 1024))
        s.wr :=
      (show Covers [emR P] s.wr by rw [emR, e1]; exact inS (by unfold oEm; omega_arith)).cons
        ((show Covers [scrR P] s.wr by rw [scrR, e2]; exact inS (by unfold oRsa; omega_arith)).cons (hA.cons Covers.nil))
    refine ⟨Covers.append_left ?_ wr.right, wr⟩
    exact (hro P.PRE (by simp)).cons ((hro P.E (by simp)).cons
      ((show Covers [⟨P.sig.setWidth 64, P.K⟩] (s.rd ++ s.wr) by rw [sigR h hi]; exact hro P.SIG (by simp)).cons
        Covers.nil))
  · rw [hr.1.1.st.sp]
    have : 100 ≤ P.B.toNat := hr.1.2.1.ok.BC
    have := c.stack
    show _ ≤ P.B.toNat
    omega_arith
  · refine pub_pub h₁.2 h₂.2 (by rw [h₁.1.1.st.sp, h₂.1.1.st.sp]) ?_ ?_ ?_ ?_ _ _
    · rw [pw_at h h₁.1.2.1 h₁.1.1.st, pw_at h h₂.1.2.1 h₂.1.1.st]
    · rw [eB_at h h₁.1.2.1 h₁.1.1.st, eB_at h h₂.1.2.1 h₂.1.1.st]
    · have ok := h₁.1.2.1.ok
      rw [h₁.1.1.st.sp]
      exact (ok.low_buf (R := P.PRE) (.inl (by simp))).sub_left
        (by rw [← ok.low_eq]; exact below_sub (show 100 ≤ 100 by decide) ok.BC)
    · have ok := h₁.1.2.1.ok
      rw [h₁.1.1.st.sp]
      exact (ok.low_buf (R := P.E) (.inl (by simp))).sub_left
        (by rw [← ok.low_eq]; exact below_sub (show 100 ≤ 100 by decide) ok.BC)
  · -- After the call.
    obtain ⟨⟨hc, hi, hf, hb⟩, pa⟩ := hr
    have ok := hi.ok
    have hs := hc.st
    have hsp := hs.sp
    obtain ⟨e1, e2, sI, sS', dIS, hfit, hs1, hK⟩ := call_geo h hi
    obtain low : Region.Sub (below (s.gpr .esp) (stackUse c.code + 4)) (P.lay h.D).LOW := by
      rw [hsp, ← ok.low_eq]
      exact below_sub (by have := c.stack; show _ ≤ 100; omega_arith) ok.BC
    obtain args0 : (⟨P.B.setWidth 64, 40⟩ : Region) = ⟨(P.lay h.D).fr 0, 40⟩ := by simp
    obtain hw : ∀ r ∈ pubWr P.B (P.scr + BitVec.ofNat 32 oEm) (P.scr + BitVec.ofNat 32 oRsa) P.K (P.scl - 1024) ++
        [below (s.gpr .esp) (stackUse c.code + 4)], ∃ R ∈ (P.lay h.D).W, Region.Sub r R := fun r hr => by
      simp only [pubWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨P.SCR, by simp, sI⟩
      · exact ⟨P.SCR, by simp, sS'⟩
      · refine ⟨(P.lay h.D).FR, by simp, ?_⟩
        rw [args0]; exact Offset.sub_base _ (by simp only [frameBytes]; omega_arith)
      · exact ⟨(P.lay h.D).LOW, by simp, low⟩
    obtain st : (P.lay h.D).St σ s' := hs.write fr hw rd wr (cs .esp (by simp [calleeSaved]))
    obtain hct : Ctx (P.lay h.D) P.scr σ s' := ⟨st, by rw [cs .ebp (by simp [calleeSaved]), hc.ebp]⟩
    obtain hb' : Bm h P s'.mem := hb.keep h fr fun r hr d hd => by
      obtain hd' : 40 ≤ d ∧ d + 4 ≤ frameBytes := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl | rfl | rfl <;> decide
      simp only [pubWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (ok.stk_fr (R := P.SCR) (.inr (by simp)) (by show d + 4 ≤ frameBytes + 16; omega_arith)).sub_right sI
      · exact (ok.stk_fr (R := P.SCR) (.inr (by simp)) (by show d + 4 ≤ frameBytes + 16; omega_arith)).sub_right sS'
      · rw [args0]; exact Lay.fr_sep (by omega_arith) (by simp only [frameBytes] at hd' ⊢; omega_arith) (by decide)
      · exact (Lay.fr_low (by simp only [frameBytes] at hd'; omega_arith)
          (by show (100 : Nat) ≤ 2 ^ 32; decide)).sub_right low
    refine ⟨⟨hct, hi, hf, hb'⟩, fun hp => ?_⟩
    obtain ⟨s₂, m₂, g₂, po⟩ := po
    have := pub_post pa po P.nB (nB_length hi) (by rw [callPw h hi hs]; exact hp)
    rw [m₂, g₂ .eax (by decide)] at this
    obtain eE : Spec.Rsa.bytesAt s.callEntry.mem (P.e.setWidth 64) P.el = P.eB :=
      (hs.callEntry_ro (by show 4 ≤ 100; decide) (R := P.E) (by simp)).trans hi.eB
    obtain eS : Spec.Rsa.bytesAt s.callEntry.mem (P.sig.setWidth 64) P.K = sigB P σ := by
      obtain e := hs.callEntry_ro (by show 4 ≤ 100; decide) (R := P.SIG) (by simp)
      dsimp only at e; rw [hi.glK] at e; exact e
    rw [eE, eS] at this
    exact this

end VG.Proof.RsaPss.X86.Vf

end

end


/-!
# RSASSA-PSS verification with a precomputed public key on x86: after the call

As on ARMv7 (`Proof/RsaPss/Arm/VfFixed.lean`): the pieces after the call are
proven over the state `τ` the call leaves (`VQ.reidx`), so that `EM`'s bytes
are those of `τ` (`emv`). `acc` (`accW`): `EM`'s last byte `⊕ 0xbc`, its first
if `lo = 1`, and the top bits of `maskedDB`'s first byte (`acc_vp`); then
`DB = maskedDB ⊕ MGF1(H, dbLen)` with its top bits cleared (`unmask_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Vf

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes
open VG.Proof.RsaPss.X86.Sg (andByte add_ofNat_sub away3_scr away3_slot away3_ctW Away3)

variable (h : PssHash)

/-- A state of a body is one the body may start from. -/
theorem St.ok_self {L : Lay} {σ s : State} (hs : L.St σ s) : L.Ok s :=
  { sp := hs.sp, rd := hs.rd ▸ hs.ok.rd, wr := hs.wr ▸ hs.ok.wr, argsW := hs.wr ▸ hs.ok.argsW, BC := hs.ok.BC, fit := hs.ok.fit,
    stk := hs.ok.stk, ret := hs.ok.ret, wro := hs.ok.wro, wrw := hs.ok.wrw, fits := hs.ok.fits,
    args := fun _ hj => hs.arg hj }

theorem In.self {P : EP} {σ s : State} (hi : In h.D P σ) (hs : (P.lay h.D).St σ s) (hTH : P.TH s) (hT : P.T s) :
    In h.D P s :=
  { ok := St.ok_self hs, kv := hi.kv, el1 := hi.el1, elK := hi.elK, glK := hi.glK, scrK := hi.scrK, rlK := hi.rlK,
    slt32 := hi.slt32, scl32 := hi.scl32, nB := nB_at h hi hs, eB := eB_at h hi hs, pw := pw_at h hi hs,
    tabTH := hTH, tabT := hT }

/-- `EM`'s bytes, as the call leaves them. -/
abbrev emv (P : EP) (τ : State) (i : Nat) : Byte := τ.mem (sa P.scr (oEm + i))

/-- `acc`. -/
abbrev accW (P : EP) (τ : State) : BitVec 32 :=
  ((emv P τ (P.K - 1)).setWidth 32 ^^^ 0xbc ||| (emv P τ 0).setWidth 32 &&& (0 - BitVec.ofNat 32 (lo P))) |||
    (emv P τ (lo P)).setWidth 32 &&& (cW ((n0 P).setWidth 32) ^^^ 0xFF)

/-- After the call, over the state `τ` it leaves. -/
abbrev W0 (P : EP) (τ s : State) : Prop :=
  Ctx (P.lay h.D) P.scr τ s ∧ In h.D P τ ∧ fits h P ∧ Bm h P s.mem ∧ ∀ i < P.K, s.mem (sa P.scr (oEm + i)) = emv P τ i

theorem w0_self {P : EP} {σ s : State} (hv : V2 h P σ s) (hTH : P.TH s) (hT : P.T s) : W0 h P s s := by
  obtain ⟨⟨hc, hi, hf, hb⟩, -⟩ := hv
  obtain hi' := In.self h hi hc.st hTH hT
  exact ⟨⟨⟨hi'.ok, hc.st.sp, rfl, rfl, Frame.refl _ _⟩, hc.ebp⟩, hi', hf, hb, fun _ _ => rfl⟩

/-- What `acc` keeps. -/
abbrev Ka (P : EP) (τ : State) (m : Mem) : Prop :=
  In h.D P τ ∧ fits h P ∧ Bm h P m ∧ m.readW ((P.lay h.D).fr sAcc) 32 = accW P τ

/-- The bounds of the encoding when everything fits. -/
theorem fitB {P : EP} {σ : State} (hi : In h.D P σ) (hf : fits h P) :
    lo P ≤ 1 ∧ eLen P + 1 ≤ dbN h P ∧ lo P + dbN h P + h.D + 1 = P.K ∧ P.K ≤ 1024 ∧ h.D ≤ 64 ∧ 0 < h.D ∧
      64 ≤ P.K := by
  have := hf.2
  have := hi.k1024
  have := hi.k64
  have := h.D_le
  have := h.N_le
  have := h.D_pos
  have : lo P ≤ 1 := by unfold lo; split <;> omega_arith
  refine ⟨this, ?_, ?_, hi.k1024, by omega_arith, h.D_pos, hi.k64⟩ <;> unfold dbN <;> omega_arith

/-- `acc`, to its slot. -/
theorem acc_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (W0 h P) (.seq (.block accSet) (.block acc0))
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Ka h P τ s.mem ∧
        ∀ i < P.K, s.mem (sa P.scr (oEm + i)) = emv P τ i) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.2.2.1
  obtain ⟨hlo, hdb, hsum, hK, hD, hD0, hK0⟩ := fitB h hi₀ hf
  have e1 : oEm = 1024 := rfl
  have e2 : oRsa = 8192 := rfl
  have fit := hg.fit
  refine VP.seq (G := fun τ s => W0 h P τ s ∧ s.gpr .esi = P.scr + BitVec.ofNat 32 oEm ∧
      s.gpr .edi = P.scr + BitVec.ofNat 32 (oEm + P.K - 1) ∧ s.gpr .ebx = P.scr + BitVec.ofNat 32 (oEm + lo P))
    (VP.taint [.esp, .ebp] accSet_taint (sp_bp fun _ _ h => h.1) fun τ s ⟨hc, hi, hf', hb, he⟩ => ?_)
    (VP.taint _ acc0_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun τ s ⟨⟨hc, hi, hf', hb, he⟩, si, di, bx⟩ => ?_)
  · simp only [accSet, atS, addSlot, addi, Impl.RsaPkcs1Sig.X86.stk, List.cons_append, List.nil_append]
    refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => wp_mov fun t3 u3 => ?_
    obtain c3 : Ctx (P.lay h.D) P.scr τ t3 :=
      ((hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)).upd u3 (by decide) (by decide)
    refine wp_addm (B := (P.lay h.D).B) (by rw [c3.st.sp]) (by rw [hg.aArg ok 1 (by simp)]; exact
      (by rw [c3.st.rd, c3.st.wr]; exact c3.st.ok.arg_read (vf_arg h (by decide)))) fun t4 u4 => ?_
    refine wp_subi fun t5 u5 _ _ => wp_mov fun t6 u6 => ?_
    obtain c6 : Ctx (P.lay h.D) P.scr τ t6 :=
      ((c3.upd u4 (by decide) (by decide)).upd u5 (by decide) (by decide)).upd u6 (by decide) (by decide)
    refine wp_addm (B := (P.lay h.D).B) (by rw [c6.st.sp])
      (by rw [hg.aFr ok sLo (by decide)]; exact c6.rFr hg sLo (by decide)) fun t7 u7 => WP.block_nil ?_
    obtain m7 : t7.mem = s.mem := by rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    obtain esi2 : t2.gpr .esi = P.scr + BitVec.ofNat 32 oEm := by rw [u2.gpr, u1.gpr, hc.ebp]
    refine ⟨⟨c6.upd u7 (by decide) (by decide), hi, hf', m7 ▸ hb, m7 ▸ he⟩, ?_, ?_, ?_⟩
    · simp (disch := decide) only [u7.other, u6.other, u5.other, u4.other, u3.other]; exact esi2
    · rw [u7.other _ (by decide), u6.other _ (by decide), u5.gpr, u4.gpr, u3.gpr, esi2, u3.mem, u2.mem, u1.mem,
        hg.aArg ok 1 (by simp), hc.st.arg (vf_arg h (by decide)),
        show (P.lay h.D).argv.getD 1 0 = BitVec.ofNat 32 P.K from rfl,
        BitVec.add_assoc, BitVec.ofNat_add_ofNat, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
        add_ofNat_sub (by omega_arith)]
    · rw [u7.gpr, u6.gpr, u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), esi2, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, hg.aFr ok sLo (by decide),
        hb.2.1, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₁.1.1.st.sp, h₂.1.1.st.sp]
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2, h₂.2.2.2]
  · have aK : addr (P.scr + BitVec.ofNat 32 (oEm + P.K - 1)) 0 = sa P.scr (oEm + (P.K - 1)) := by
      rw [hg.addrD (by omega_arith)]; congr 1; omega_arith
    obtain a0 : addr (P.scr + BitVec.ofNat 32 oEm) 0 = sa P.scr (oEm + 0) := hg.addrD (by omega_arith)
    obtain al : addr (P.scr + BitVec.ofNat 32 (oEm + lo P)) 0 = sa P.scr (oEm + lo P) := by
      rw [hg.addrD (by omega_arith), Nat.add_zero]
    obtain rK : InRegions (s.rd ++ s.wr) (sa P.scr (oEm + (P.K - 1))) 1 := hg.rd hc.st (by omega_arith)
    obtain r0' : InRegions (s.rd ++ s.wr) (sa P.scr (oEm + 0)) 1 := hg.rd hc.st (by omega_arith)
    obtain rl : InRegions (s.rd ++ s.wr) (sa P.scr (oEm + lo P)) 1 := hg.rd hc.st (by omega_arith)
    simp only [acc0, mi, ld, st, Impl.RsaPkcs1Sig.X86.at_, Impl.RsaPkcs1Sig.X86.stk]
    refine wp_movzx8 (a := sa P.scr (oEm + (P.K - 1))) (by rw [ea_at, di]; exact aK) rK fun t1 u1 => ?_
    refine wp_xorI fun t2 u2 => ?_
    refine wp_movzx8 (a := sa P.scr (oEm + 0))
      (by rw [ea_at, u2.other _ (by decide), u1.other _ (by decide), si]; exact a0)
      (by rw [u2.rd, u2.wr, u1.rd, u1.wr]; exact r0') fun t3 u3 => ?_
    refine wp_movi fun t4 u4 => ?_
    obtain c4 : Ctx (P.lay h.D) P.scr τ t4 :=
      (((hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)).upd u3 (by decide) (by decide)).upd u4
        (by decide) (by decide)
    refine wp_subm (B := (P.lay h.D).B) (by rw [c4.st.sp])
      (by rw [hg.aFr ok sLo (by decide)]; exact c4.rFr hg sLo (by decide)) fun t5 u5 => ?_
    refine wp_and fun t6 u6 => wp_or fun t7 u7 => ?_
    refine wp_movzx8 (a := sa P.scr (oEm + lo P))
      (by simp (disch := decide) only [ea_at, u7.other, u6.other, u5.other, u4.other, u3.other, u2.other,
        u1.other]; rw [bx]; exact al)
      (by rw [u7.rd, u7.wr, u6.rd, u6.wr, u5.rd, u5.wr, u4.rd, u4.wr, u3.rd, u3.wr, u2.rd, u2.wr, u1.rd, u1.wr]
          exact rl) fun t8 u8 => ?_
    obtain c8 : Ctx (P.lay h.D) P.scr τ t8 :=
      (((c4.upd u5 (by decide) (by decide)).upd u6 (by decide) (by decide)).upd u7 (by decide) (by decide)).upd u8
        (by decide) (by decide)
    refine c8.wp_slot hg (d := sC) (by decide) (by decide) (by decide) fun t9 c9 u9 => ?_
    refine wp_xorI fun t10 u10 => wp_and fun t11 u11 => wp_or fun t12 u12 => ?_
    obtain c12 : Ctx (P.lay h.D) P.scr τ t12 :=
      ((c9.upd u10 (by decide) (by decide)).upd u11 (by decide) (by decide)).upd u12 (by decide) (by decide)
    refine c12.wp_st hg (d := sAcc) (by decide) fun t13 c13 m13 => WP.block_nil ?_
    obtain mm : t12.mem = s.mem := by
      rw [u12.mem, u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    obtain v : t12.gpr .eax = accW P τ := by
      simp (disch := decide) only [u12.gpr, u11.gpr, u11.other, u10.gpr, u10.other, u9.gpr, u9.other,
        u8.gpr, u8.other, u7.gpr, u6.gpr, u6.other, u5.gpr, u5.other, u4.gpr, u4.other, u3.gpr,
        u3.other, u2.gpr, u1.gpr]
      rw [u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, hg.aFr ok sLo (by decide), hb.2.1,
        hb.1, he _ (by omega_arith), he _ (by omega_arith), he _ (by omega_arith)]
      rfl
    obtain m : t13.mem = s.mem.writeW ((P.lay h.D).fr sAcc) (accW P τ) := by rw [m13.mem, mm, v]
    obtain fr : Frame [slotR (P.lay h.D) sAcc] s.mem t13.mem := by rw [m]; exact slot_frame _ _ _ _
    refine ⟨c13, ⟨hi, hf', ?_, by rw [m, Mem.readW_writeW_self32]⟩, fun i hi' => ?_⟩
    · rw [m]
      exact ⟨by rw [Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide)]; exact hb.1,
        by rw [Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide)]; exact hb.2.1,
        by rw [Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide)]; exact hb.2.2.1,
        by rw [Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide)]; exact hb.2.2.2⟩
    · rw [← he i hi']
      exact fr _ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hg.slot ok (o := oEm + i) (n := 1) (d := sAcc) (k := 4) (by omega_arith) (by rw [hg.F]; decide)).symm _
          (Region.contains_self _ _)

/-- `H`, as the call leaves it. -/
abbrev seedV (P : EP) (τ : State) : List Byte := (List.range h.D).map fun i => emv P τ (lo P + dbN h P + i)

/-- The mask. -/
abbrev mkV (P : EP) (τ : State) : List Byte := Spec.Mgf1.mgf1 P.g.G (seedV h P τ) (dbN h P)

/-- `DB`, unmasked, with its top bits cleared. -/
abbrev dbF (P : EP) (τ : State) (i : Nat) : Byte :=
  if i = 0 then (emv P τ (lo P) ^^^ (mkV h P τ).getD 0 0) &&& (cW ((n0 P).setWidth 32)).setWidth 8
  else emv P τ (lo P + i) ^^^ (mkV h P τ).getD i 0

/-- After the unmasking. -/
abbrev U0 (P : EP) (τ s : State) : Prop :=
  Ctx (P.lay h.D) P.scr τ s ∧ Ka h P τ s.mem ∧
    (∀ i < dbN h P, s.mem (sa P.scr (oEm + lo P + i)) = dbF h P τ i) ∧
    ∀ i < h.D, s.mem (sa P.scr (oEm + lo P + dbN h P + i)) = (seedV h P τ).getD i 0

/-- MGF1's slots: `H` its source, `DB` its destination. -/
abbrev Ms (P : EP) (m : Mem) : Prop :=
  Proof.RsaOaep.X86.Sl (P.lay h.D) P.scr (oEm + lo P + dbN h P) h.D (oEm + lo P) (dbN h P) m

/-- The slots of MGF1, other than its own, that the unmasking keeps. -/
theorem margs_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Ka h P τ s.mem ∧ ∀ i < P.K, s.mem (sa P.scr (oEm + i)) = emv P τ i)
      (.block (mgfArgsT h.H))
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ (Ka h P τ s.mem ∧ Ms h P s.mem) ∧
        (∀ i < dbN h P, s.mem (sa P.scr (oEm + lo P + i)) = emv P τ (lo P + i)) ∧
        ∀ i < h.D, s.mem (sa P.scr (oEm + lo P + dbN h P + i)) = (seedV h P τ).getD i 0) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.2.1.2.1
  obtain ⟨hlo, hdb, hsum, hK, hD, hD0, hK0⟩ := fitB h hi₀ hf
  have e1 : oEm = 1024 := rfl
  have e2 : oRsa = 8192 := rfl
  have fit := hg.fit
  refine VP.taint [.esp, .ebp] h.certs.mgfArgs (sp_bp fun _ _ h => h.1) fun τ s ⟨hc, hk, he⟩ => ?_
  simp only [mgfArgsT, atDb, atS, addSlot, addi, ld, st, mi, Impl.RsaPkcs1Sig.X86.stk, List.cons_append,
    List.nil_append]
  refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
  obtain c2 : Ctx (P.lay h.D) P.scr τ t2 := (hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)
  refine wp_addm (B := (P.lay h.D).B) (by rw [c2.st.sp])
    (by rw [hg.aFr ok sLo (by decide)]; exact c2.rFr hg sLo (by decide)) fun t3 u3 => ?_
  refine (c2.upd u3 (by decide) (by decide)).wp_st hg (by decide) fun t4 c4 m4 => ?_
  refine c4.wp_slot hg (by decide) (by decide) (by decide) fun t5 c5 u5 => ?_
  refine c5.wp_st hg (by decide) fun t6 c6 m6 => wp_add fun t7 u7 _ => ?_
  refine (c6.upd u7 (by decide) (by decide)).wp_st hg (by decide) fun t8 c8 m8 => wp_movi fun t9 u9 => ?_
  refine (c8.upd u9 (by decide) (by decide)).wp_st hg (by decide) fun t10 c10 m10 => WP.block_nil ?_
  obtain e3 : t3.gpr .eax = P.scr + BitVec.ofNat 32 (oEm + lo P) := by
    rw [u3.gpr, u2.gpr, u1.gpr, u2.mem, u1.mem, hc.ebp, hg.aFr ok sLo (by decide), hk.2.2.1.2.1, BitVec.add_assoc,
      BitVec.ofNat_add_ofNat]
  obtain e5 : t5.gpr .ecx = BitVec.ofNat 32 (dbN h P) := by
    rw [u5.gpr, m4.mem, Lay.readW_fr_other (d := sDb) (e := Impl.RsaOaep.X86.sDst) _ _ _ (by decide) (by decide)
      (by decide), u3.mem, u2.mem, u1.mem, hk.2.2.1.2.2.1]
  obtain e7 : t7.gpr .eax = P.scr + BitVec.ofNat 32 (oEm + lo P + dbN h P) := by
    rw [u7.gpr, m6.gpr, u5.other _ (by decide), m4.gpr, e3, e5, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  obtain m10 : t10.mem = (((s.mem.writeW ((P.lay h.D).fr Impl.RsaOaep.X86.sDst) (P.scr + BitVec.ofNat 32 (oEm + lo P))).writeW
      ((P.lay h.D).fr Impl.RsaOaep.X86.sDstLen) (BitVec.ofNat 32 (dbN h P))).writeW ((P.lay h.D).fr Impl.RsaOaep.X86.sSrc)
        (P.scr + BitVec.ofNat 32 (oEm + lo P + dbN h P))).writeW ((P.lay h.D).fr Impl.RsaOaep.X86.sSrcLen)
          (BitVec.ofNat 32 h.D) := by
    rw [m10.mem, u9.gpr, u9.mem, m8.mem, e7, u7.mem, m6.mem, e5, u5.mem, m4.mem, e3, u3.mem, u2.mem, u1.mem]
  obtain ⟨c, fr, r1, r2, r3, r4⟩ := Sg.slots4 hc hg m10 (by rw [c10.st.rd, hc.st.rd]) (by rw [c10.st.wr, hc.st.wr])
    (by rw [c10.st.sp, hc.st.sp]) (by rw [c10.ebp, hc.ebp])
  obtain dis := Sg.slots4_dis hg
  obtain sl : ∀ d, d + 4 ≤ 80 → ∀ r ∈ [slotR (P.lay h.D) Impl.RsaOaep.X86.sDst, slotR (P.lay h.D) Impl.RsaOaep.X86.sDstLen,
      slotR (P.lay h.D) Impl.RsaOaep.X86.sSrc, slotR (P.lay h.D) Impl.RsaOaep.X86.sSrcLen], (slotR (P.lay h.D) d).Disjoint r :=
    fun d hd r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact slotSep (Nat.le_trans hd (by decide)) (by decide)
        (.inl (Nat.le_trans hd (by decide)))
  obtain sa' : ∀ r ∈ [slotR (P.lay h.D) Impl.RsaOaep.X86.sDst, slotR (P.lay h.D) Impl.RsaOaep.X86.sDstLen,
      slotR (P.lay h.D) Impl.RsaOaep.X86.sSrc, slotR (P.lay h.D) Impl.RsaOaep.X86.sSrcLen],
      (slotR (P.lay h.D) sAcc).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact slotSep (by decide) (by decide) (by decide)
  obtain kb : Bm h P t10.mem := ⟨slot_keep fr (sl sC (by decide)) hk.2.2.1.1,
    slot_keep fr (sl sLo (by decide)) hk.2.2.1.2.1, slot_keep fr (sl sDb (by decide)) hk.2.2.1.2.2.1,
    slot_keep fr (sl sAny (by decide)) hk.2.2.1.2.2.2⟩
  obtain he' : ∀ i < P.K, t10.mem (sa P.scr (oEm + i)) = emv P τ i := fun i hi =>
    by rw [sbytes_keep (o := oEm) (n := P.K) fr (dis _ _ (by omega_using [hK, e1, e2])) (by omega_using [hK, e1]) he i hi]
  refine ⟨c, ⟨⟨hk.1, hk.2.1, kb, slot_keep fr sa' hk.2.2.2⟩, r1, r2, r3, r4⟩, fun i hi => ?_, fun i hi => ?_⟩
  · rw [Nat.add_assoc, he' _ (by omega_using [hsum, hi])]
  · rw [Nat.add_assoc, Nat.add_assoc, he' _ (by omega_using [hsum, hi])]
    simp [hi, Nat.add_assoc]

/-- `DB`'s first byte's top bits cleared. -/
theorem topV_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Ka h P τ s.mem ∧
        (∀ i < dbN h P, s.mem (sa P.scr (oEm + lo P + i)) = emv P τ (lo P + i) ^^^ (mkV h P τ).getD i 0) ∧
        ∀ i < h.D, s.mem (sa P.scr (oEm + lo P + dbN h P + i)) = (seedV h P τ).getD i 0)
      (.seq (.block topSet) (.block topAnd)) (U0 h P) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.2.1.2.1
  obtain ⟨hlo, hdb, hsum, hK, hD, hD0, hK0⟩ := fitB h hi₀ hf
  have e1 : oEm = 1024 := rfl
  have e2 : oRsa = 8192 := rfl
  have e3 : oY = 2048 := rfl
  have fit := hg.fit
  refine VP.seq (G := fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ Ka h P τ s.mem ∧
        (∀ i < dbN h P, s.mem (sa P.scr (oEm + lo P + i)) = emv P τ (lo P + i) ^^^ (mkV h P τ).getD i 0) ∧
        ∀ i < h.D, s.mem (sa P.scr (oEm + lo P + dbN h P + i)) = (seedV h P τ).getD i 0) ∧
      s.gpr .esi = P.scr + BitVec.ofNat 32 (oEm + lo P))
    (VP.taint [.esp, .ebp] topSet_taint (sp_bp fun _ _ h => h.1) fun τ s ⟨hc, hk, hd, hh⟩ => ?_)
    (VP.taint _ topAnd_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun τ s ⟨⟨hc, hk, hd, hh⟩, si⟩ => ?_)
  · simp only [topSet, atDb, atS, addSlot, addi, Impl.RsaPkcs1Sig.X86.stk, List.cons_append, List.nil_append]
    refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
    obtain c2 : Ctx (P.lay h.D) P.scr τ t2 := (hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)
    refine wp_addm (B := (P.lay h.D).B) (by rw [c2.st.sp])
      (by rw [hg.aFr ok sLo (by decide)]; exact c2.rFr hg sLo (by decide)) fun t3 u3 => WP.block_nil ?_
    obtain m3 : t3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
    refine ⟨⟨c2.upd u3 (by decide) (by decide), m3 ▸ hk, m3 ▸ hd, m3 ▸ hh⟩, ?_⟩
    rw [u3.gpr, u2.gpr, u1.gpr, u2.mem, u1.mem, hc.ebp, hg.aFr ok sLo (by decide), hk.2.2.1.2.1, BitVec.add_assoc,
      BitVec.ofNat_add_ofNat]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.1.1.st.sp, h₂.1.1.st.sp]
    · rw [h₁.2, h₂.2]
  · have ad : addr (P.scr + BitVec.ofNat 32 (oEm + lo P)) 0 = sa P.scr (oEm + lo P) := by
      rw [hg.addrD (by omega_arith), Nat.add_zero]
    obtain rd : InRegions (s.rd ++ s.wr) (sa P.scr (oEm + lo P)) 1 := hg.rd hc.st (by omega_arith)
    obtain wd : InRegions s.wr (sa P.scr (oEm + lo P)) 1 := hg.wr hc.st (by omega_arith)
    simp only [topAnd, Impl.RsaPkcs1Sig.X86.at_, Impl.RsaPkcs1Sig.X86.stk]
    refine wp_movzx8 (a := sa P.scr (oEm + lo P)) (by rw [ea_at, si]; exact ad) rd fun t1 u1 => ?_
    obtain c1 : Ctx (P.lay h.D) P.scr τ t1 := hc.upd u1 (by decide) (by decide)
    obtain rC := c1.rFr hg sC (by decide)
    refine wp_andS (readSrc_mem (B := (P.lay h.D).B) (by rw [c1.st.sp]) (by rw [hg.aFr ok sC (by decide)]; exact rC))
      fun t2 u2 => ?_
    obtain a2 : t2.ea ⟨.esi, 0⟩ = sa P.scr (oEm + lo P) := by
      rw [ea_at, u2.other .esi (by decide), u1.other .esi (by decide), si]; exact ad
    refine wp_store8 (a := sa P.scr (oEm + lo P)) a2 (by rw [u2.wr, u1.wr]; exact wd) fun t3 u3 => WP.block_nil ?_
    obtain m3 : t3.mem = s.mem.writeW (sa P.scr (oEm + lo P))
        (s.mem (sa P.scr (oEm + lo P)) &&& (cW ((n0 P).setWidth 32)).setWidth 8) := by
      rw [u3.mem, Reg8.reg, u2.gpr, u2.mem, u1.gpr, u1.mem, hg.aFr ok sC (by decide), hk.2.2.1.1, andByte]
    obtain fr : Frame [sR P.scr (oEm + lo P) 1] s.mem t3.mem := by
      rw [m3]; exact frame_byte P.scr _ _ (Nat.le_refl _) (by omega_arith) (by omega_arith)
    obtain kk : ∀ d, d + 4 ≤ frameBytes → t3.mem.readW ((P.lay h.D).fr d) 32 = s.mem.readW ((P.lay h.D).fr d) 32 :=
      fun d hd => by
        rw [slot_keep (v := s.mem.readW ((P.lay h.D).fr d) 32) fr (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact hg.slot ok (by omega_arith)
            (by rw [hg.F]; unfold frameBytes at hd ⊢; omega_arith)) rfl]
    obtain hb' : Bm h P t3.mem := ⟨by rw [kk _ (by decide)]; exact hk.2.2.1.1, by rw [kk _ (by decide)]; exact hk.2.2.1.2.1,
      by rw [kk _ (by decide)]; exact hk.2.2.1.2.2.1, by rw [kk _ (by decide)]; exact hk.2.2.1.2.2.2⟩
    obtain ha' : t3.mem.readW ((P.lay h.D).fr sAcc) 32 = accW P τ := by rw [kk _ (by decide)]; exact hk.2.2.2
    refine ⟨(c1.upd u2 (by decide) (by decide)).write (by rw [u2.mem, u1.mem]; exact fr) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hg.inW (by omega_arith)) u3.rd u3.wr (by rw [u3.gpr])
        (by rw [u3.gpr]), ⟨hk.1, hk.2.1, hb', ha'⟩, fun i hi => ?_, fun i hi => ?_⟩
    · rw [m3, sa_write P.scr _ _ (by omega_arith) (by omega_arith)]
      unfold dbF
      by_cases e : i = 0
      · subst e
        rw [ite_eq_left (by omega_arith), ite_eq_left rfl, show oEm + lo P = oEm + lo P + 0 from rfl, hd 0 (by omega_arith),
          Nat.add_zero]
      · rw [ite_eq_right (by omega_arith), ite_eq_right e, hd i hi]
    · rw [m3, sa_write P.scr _ _ (by omega_arith) (by omega_arith), ite_eq_right (by omega_arith), hh i hi]

/-- `DB = maskedDB ⊕ MGF1(H, dbLen)`, its top bits cleared: MGF1 with the
hash function `P.g` of the table at the argument 15. -/
theorem unmask_vp (P : EP) (hP : ∃ σ, In h.D P σ) {fG : Impl.RsaOaep.X86.Fns}
    (hT : ∀ σ, P.T σ → Proof.RsaOaep.X86.TabFacts P.g.H fG P.tab P.ai P.au P.af σ)
    (fne : fG.init ≠ [] ∧ fG.upd ≠ [] ∧ fG.fin ≠ []) {R : Prog isa} {G : State → State → Prop}
    (hR : VP (fun τ s => U0 h P τ s ∧ s.syms = τ.syms) R G) :
    VP (fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ Ka h P τ s.mem ∧ ∀ i < P.K, s.mem (sa P.scr (oEm + i)) = emv P τ i) ∧
        s.syms = τ.syms)
      (.seq (.block (mgfArgsT h.H)) (.seq (Impl.RsaOaep.X86.mgfXor fG 15) (.seq (.block topSet) (.seq (.block topAnd) R))))
      G := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.1.2.1.2.1
  obtain ⟨hlo, hdb, hsum, hK, hD, hD0, hK0⟩ := fitB h hi₀ hf
  have e1 : oEm = 1024 := rfl
  have e5 : Impl.RsaOaep.X86.oBuf = 2048 := rfl
  obtain hX : ∀ τ m m', Ka h P τ m → Frame (Proof.RsaOaep.X86.mgfW P.g (P.lay h.D) P.scr (oEm + lo P) (dbN h P)) m m' →
      Ka h P τ m' := fun τ m m' ⟨hi, hf', hb, ha⟩ hfr => by
    obtain k : ∀ d, d + 4 ≤ 104 → ∀ r ∈ Proof.RsaOaep.X86.mgfW P.g (P.lay h.D) P.scr (oEm + lo P) (dbN h P),
        (slotR (P.lay h.D) d).Disjoint r := fun d hd =>
      Proof.RsaOaep.X86.mgfW_slot P.g hg (by omega_using [hsum, hK, e1, e5]) (Nat.le_trans hd (by decide)) (.inl (Nat.le_trans hd (by decide)))
        (.inl (Nat.le_trans hd (by decide)))
    exact ⟨hi, hf', ⟨slot_keep hfr (k sC (by decide)) hb.1, slot_keep hfr (k sLo (by decide)) hb.2.1,
      slot_keep hfr (k sDb (by decide)) hb.2.2.1, slot_keep hfr (k sAny (by decide)) hb.2.2.2⟩,
      slot_keep hfr (Proof.RsaOaep.X86.mgfW_slot P.g hg (by omega_using [hsum, hK, e1, e5]) (by decide) (.inr (by decide))
        (.inl (by decide))) ha⟩
  obtain mp := Proof.RsaOaep.X86.mpOf P.g hg (so := oEm + lo P + dbN h P) (sl := h.D) (dOff := oEm + lo P)
    (dl := dbN h P) hD0 (by omega_using [hdb]) (by omega_using []) (by omega_using []) (by omega_using [hsum, hK, e1, e5]) (by omega_using [hsum, hK, e1, e5]) (.inr (Nat.le_refl _))
    (seed := seedV h P) (fun τ => by simp) hX (vf_arg h (j := 15) (by decide)) hi₀.tbl
    Proof.RsaOaep.X86.tabArg15_taint (fun τ m hk => hT τ hk.1.tabT) fne
  exact (Proof.RsaOaep.X86.VP.syms (margs_vp h P ⟨σ₀, hi₀⟩)).seq (((Proof.RsaOaep.X86.mgf_vp P.g mp
    (dstv := fun τ i => emv P τ (lo P + i))).mono (fun _ _ h => h)
      fun τ s ⟨⟨hc, ⟨hk, _⟩, hd, hh⟩, sy⟩ => ⟨⟨hc, hk, hd, hh⟩, sy⟩).seq
        (Sg.vpAssoc ((Proof.RsaOaep.X86.VP.syms (topV_vp h P ⟨σ₀, hi₀⟩)).seq hR)))

end VG.Proof.RsaPss.X86.Vf

end

end


/-!
# RSASSA-PSS verification with a precomputed public key on x86: the scan

As on ARMv7 (`Proof/RsaPss/Arm/VfFixed.lean`): the scan of `DB` finds the
index (`pzJ`) and the value (`vzJ`) of its first byte that is not zero, if
any (`nfJ`), without a branch (`scan_vp`). On x86 the index and the value
are kept in their slots, through `ebp`, which `posChk` loads with `scratch`
again: the loop's states are states of the body (`Lay.St`), not `Ctx`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Vf

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes

variable (h : PssHash)

/-- `DB`, as a list. -/
abbrev dbL (P : EP) (τ : State) : List Byte := (List.range (dbN h P)).map (dbF h P τ)

/-- Where the padding ends. -/
abbrev lzF (P : EP) (τ : State) : Nat := RsaPss.lz (dbL h P τ)

/-- The index and value of `DB`'s first byte not zero, after `j` bytes, and
whether none was found. -/
abbrev pzJ (P : EP) (τ : State) (j : Nat) : Nat := if lzF h P τ < j then lzF h P τ else 0
abbrev vzJ (P : EP) (τ : State) (j : Nat) : Byte := if lzF h P τ < j then dbF h P τ (lzF h P τ) else 0
abbrev nfJ (P : EP) (τ : State) (j : Nat) : BitVec 32 := if lzF h P τ < j then 0 else BitVec.allOnes 32

/-- The mask `sub r, 1; sbb r, r` leaves of a byte. -/
theorem bz : ∀ b : Byte, (if decide ((b.setWidth 32).toNat < (1 : BitVec 32).toNat) = true then BitVec.allOnes 32
    else 0) = if b = 0 then BitVec.allOnes 32 else (0 : BitVec 32) := by decide

/-- What the scan keeps. -/
abbrev Kd (P : EP) (τ : State) (m : Mem) : Prop :=
  Ka h P τ m ∧ (∀ i < dbN h P, m (sa P.scr (oEm + lo P + i)) = dbF h P τ i) ∧
    ∀ i < h.D, m (sa P.scr (oEm + lo P + dbN h P + i)) = (seedV h P τ).getD i 0

/-- A word stored in a slot apart from those `Kd` reads keeps it. -/
theorem Kd.slot {P : EP} {τ : State} {m : Mem} (hk : Kd h P τ m) {d : Nat} (hd : d + 4 ≤ frameBytes)
    (hs : ∀ e ∈ [sC, sLo, sDb, sAny, sAcc], d + 4 ≤ e ∨ e + 4 ≤ d) (v : BitVec 32) :
    Kd h P τ (m.writeW ((P.lay h.D).fr d) v) := by
  have hg := hk.1.1.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have hf := hk.1.2.1
  obtain ⟨hlo, hdb, hsum, hK, hD, hD0, hK0⟩ := fitB h hk.1.1 hf
  have e1 : oEm = 1024 := rfl
  have e2 : oRsa = 8192 := rfl
  obtain rw' : ∀ e ∈ [sC, sLo, sDb, sAny, sAcc],
      (m.writeW ((P.lay h.D).fr d) v).readW ((P.lay h.D).fr e) 32 = m.readW ((P.lay h.D).fr e) 32 :=
    fun e he => Lay.readW_fr_other _ _ _ ((hs e he).symm) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl <;> decide) (by unfold frameBytes at hd; omega_using [hd])
  obtain kb : ∀ o, o + 1 ≤ oRsa → (m.writeW ((P.lay h.D).fr d) v) (sa P.scr o) = m (sa P.scr o) := fun o ho =>
    slot_frame (P.lay h.D) m d v _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hg.slot ok (o := o) (n := 1) (by omega_using [ho]) (by rw [hg.F]; unfold frameBytes at hd ⊢; omega_using [hd])).symm _
        (Region.contains_self _ _)
  refine ⟨⟨hk.1.1, hf, ⟨?_, ?_, ?_, ?_⟩, ?_⟩, fun i hi => ?_, fun i hi => ?_⟩
  · rw [rw' sC (by simp)]; exact hk.1.2.2.1.1
  · rw [rw' sLo (by simp)]; exact hk.1.2.2.1.2.1
  · rw [rw' sDb (by simp)]; exact hk.1.2.2.1.2.2.1
  · rw [rw' sAny (by simp)]; exact hk.1.2.2.1.2.2.2
  · rw [rw' sAcc (by simp)]; exact hk.1.2.2.2
  · rw [kb _ (by omega_using [hsum, hK, e1, e2, hi])]; exact hk.2.1 i hi
  · rw [kb _ (by omega_using [hsum, hK, e1, e2, hi])]; exact hk.2.2 i hi

/-- After `j` bytes of the scan. -/
structure SC (P : EP) (τ : State) (j : Nat) (s : State) : Prop where
  esi : s.gpr .esi = P.scr + BitVec.ofNat 32 (oEm + lo P + j)
  edi : s.gpr .edi = BitVec.ofNat 32 j
  ecx : s.gpr .ecx = BitVec.ofNat 32 (dbN h P - j)
  ebx : s.gpr .ebx = nfJ h P τ j
  pos : s.mem.readW ((P.lay h.D).fr sPos) 32 = BitVec.ofNat 32 (pzJ h P τ j)
  val : s.mem.readW ((P.lay h.D).fr sVal) 32 = (vzJ h P τ j).setWidth 32

/-- The scan's registers and slots. -/
theorem scanSet_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (U0 h P) (.block scanSet)
      (fun τ s => (P.lay h.D).St τ s ∧ Kd h P τ s.mem ∧ fits h P ∧ SC h P τ 0 s) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  refine VP.taint [.esp, .ebp] scanSet_taint (sp_bp fun _ _ h => h.1) fun τ s ⟨hc, hk, hd, hh⟩ => ?_
  simp only [scanSet, atDb, atS, addSlot, addi, ld, mi, st, Impl.RsaPkcs1Sig.X86.stk, List.cons_append,
    List.nil_append]
  refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
  obtain c2 : Ctx (P.lay h.D) P.scr τ t2 := (hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)
  refine wp_addm (B := (P.lay h.D).B) (by rw [c2.st.sp])
    (by rw [hg.aFr ok sLo (by decide)]; exact c2.rFr hg sLo (by decide)) fun t3 u3 => ?_
  obtain c3 : Ctx (P.lay h.D) P.scr τ t3 := c2.upd u3 (by decide) (by decide)
  refine c3.wp_slot hg (d := sDb) (by decide) (by decide) (by decide) fun t4 c4 u4 => ?_
  refine wp_movi fun t5 u5 => wp_movi fun t6 u6 => ?_
  obtain c6 : Ctx (P.lay h.D) P.scr τ t6 := (c4.upd u5 (by decide) (by decide)).upd u6 (by decide) (by decide)
  refine c6.wp_st hg (d := sPos) (by decide) fun t7 c7 m7 => c7.wp_st hg (d := sVal) (by decide) fun t8 c8 m8 => ?_
  refine wp_movi fun t9 u9 => wp_subi fun t10 u10 _ _ => WP.block_nil ?_
  obtain m6 : t6.mem = s.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  obtain ax : t6.gpr .eax = 0 := by rw [u6.gpr]; rfl
  obtain mem : t10.mem = (s.mem.writeW ((P.lay h.D).fr sPos) (0 : BitVec 32)).writeW ((P.lay h.D).fr sVal)
      (0 : BitVec 32) := by
    rw [u10.mem, u9.mem, m8.mem, m7.gpr, ax, m7.mem, ax, m6]
  obtain kd : Kd h P τ t10.mem := by
    rw [mem]
    exact (Kd.slot h ⟨hk, hd, hh⟩ (d := sPos) (by decide) (by decide) 0).slot h (d := sVal) (by decide)
      (by decide) 0
  refine ⟨(c8.upd u9 (by decide) (by decide)).upd u10 (by decide) (by decide) |>.st, kd, hk.2.1, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · simp (disch := decide) only [u10.other, u9.other, m8.gpr, m7.gpr, u6.other, u5.other, u4.other, u3.gpr,
      u2.gpr, u1.gpr, u2.mem, u1.mem, hc.ebp]
    rw [hg.aFr ok sLo (by decide), hk.2.2.1.2.1, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; rfl
  · simp (disch := decide) only [u10.other, u9.other, m8.gpr, m7.gpr, u6.other, u5.gpr]
  · simp (disch := decide) only [u10.other, u9.other, m8.gpr, m7.gpr, u6.other, u5.other, u4.gpr]
    rw [u3.mem, u2.mem, u1.mem, hk.2.2.1.2.2.1]; rfl
  · rw [u10.gpr, u9.gpr]; simp only [nfJ, Nat.not_lt_zero, ite_false]; decide
  · rw [mem, Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
    simp only [pzJ, Nat.not_lt_zero, ite_false]; rfl
  · rw [mem, Mem.readW_writeW_self32]
    simp only [vzJ, Nat.not_lt_zero, ite_false]; rfl

theorem dbL_getD {P : EP} {τ : State} {j : Nat} (hj : j < dbN h P) : (dbL h P τ).getD j 0 = dbF h P τ j := by
  simp [dbL, List.getD_eq_getElem?_getD, hj]

/-- One byte of the scan. -/
theorem scan_step {P : EP} {τ : State} {j : Nat} (hj : j < dbN h P) (b : Byte) (hb : b = dbF h P τ j) :
    let m : BitVec 32 := ((if b = 0 then BitVec.allOnes 32 else 0) ^^^ BitVec.allOnes 32) &&& nfJ h P τ j
    BitVec.ofNat 32 (pzJ h P τ j) ||| BitVec.ofNat 32 j &&& m = BitVec.ofNat 32 (pzJ h P τ (j + 1)) ∧
    (vzJ h P τ j).setWidth 32 ||| b.setWidth 32 &&& m = (vzJ h P τ (j + 1)).setWidth 32 ∧
    nfJ h P τ j &&& (m ^^^ BitVec.allOnes 32) = nfJ h P τ (j + 1) := by
  intro m
  obtain az : ∀ x : BitVec 32, x &&& 0 = 0 := fun x => BitVec.and_zero
  obtain za : ∀ x : BitVec 32, 0 &&& x = 0 := fun x => BitVec.zero_and
  obtain oz : ∀ x : BitVec 32, x ||| 0 = x := fun x => BitVec.or_zero
  obtain zo : ∀ x : BitVec 32, 0 ||| x = x := fun x => BitVec.zero_or
  obtain hlt : lzF h P τ ≤ dbN h P := by
    obtain e := RsaPss.lz_le (dbL h P τ)
    rw [show (dbL h P τ).length = dbN h P by simp [dbL]] at e
    exact e
  rcases Nat.lt_trichotomy (lzF h P τ) j with hl | hl | hl
  · have h8 : m = 0 := by simp only [m, nfJ, ite_eq_left hl, az]
    simp only [h8, az, oz, pzJ, vzJ, nfJ, ite_eq_left hl, ite_eq_left (by omega_using [hl] : lzF h P τ < j + 1), za]
    exact ⟨trivial, trivial, trivial⟩
  · have hne : b ≠ 0 := by
      rw [hb, ← hl, ← dbL_getD h (by omega_using [hj, hl])]
      exact RsaPss.getD_lz_ne (by
        show lzF h P τ < (dbL h P τ).length
        rw [show (dbL h P τ).length = dbN h P by simp [dbL]]; omega_using [hj, hl])
    obtain h8 : m = BitVec.allOnes 32 := by
      simp only [m, hne, ite_false, nfJ, ite_eq_right (show ¬ lzF h P τ < j by omega_using [hl])]; decide
    simp only [h8, BitVec.and_allOnes, pzJ, vzJ, nfJ, ite_eq_right (show ¬ lzF h P τ < j by omega_using [hl]),
      ite_eq_left (show lzF h P τ < j + 1 by omega_using [hl])]
    have sz : (0 : Byte).setWidth 32 = 0 := rfl
    refine ⟨by rw [hl, BitVec.zero_or], by rw [hl, hb, sz, zo], by decide⟩
  · have hz : b = 0 := by rw [hb, ← dbL_getD h hj]; exact RsaPss.getD_lt_lz hl
    obtain h8 : m = 0 := by
      simp only [m, hz, ite_true]; rw [show BitVec.allOnes 32 ^^^ BitVec.allOnes 32 = 0 by decide, za]
    simp only [h8, az, oz, pzJ, vzJ, nfJ, ite_eq_right (show ¬ lzF h P τ < j by omega_using [hl]),
      ite_eq_right (show ¬ lzF h P τ < j + 1 by omega_using [hl])]
    exact ⟨trivial, trivial, by decide⟩

/-- The scan of `DB`. -/
theorem scan_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => (P.lay h.D).St τ s ∧ Kd h P τ s.mem ∧ fits h P ∧ SC h P τ 0 s)
      (countLoop scanBody)
      (fun τ s => (P.lay h.D).St τ s ∧ Kd h P τ s.mem ∧ fits h P ∧ SC h P τ (dbN h P) s) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.2.2.1
  obtain ⟨hlo, hdb, hsum, hK, hD, hD0, hK0⟩ := fitB h hi₀ hf
  have e1 : oEm = 1024 := rfl
  have e2 : oRsa = 8192 := rfl
  have fit := hg.fit
  let I : Nat → State → State → Prop := fun k τ s => k ≤ dbN h P ∧ (P.lay h.D).St τ s ∧ Kd h P τ s.mem ∧
    fits h P ∧ SC h P τ (dbN h P - k) s
  refine (VP.loop (I := I) (fun k => ?_) (dbN h P - 1)).mono (fun τ s ⟨hc, hx, hf', hs⟩ => ⟨by omega_using [hdb], hc, hx, hf',
    by rw [show dbN h P - (dbN h P - 1 + 1) = 0 by omega_using []]; exact hs⟩) fun _ _ h => h
  refine VP.taint _ scanBody_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun τ s ⟨hk, hs, hx, hf', hp⟩ => ?_
  · obtain ⟨-, s₁, -, -, p₁⟩ := h₁
    obtain ⟨-, s₂, -, -, p₂⟩ := h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [s₁.sp, s₂.sp]
    · rw [p₁.esi, p₂.esi]
    · rw [p₁.edi, p₂.edi]
    · rw [p₁.ecx, p₂.ecx]
  generalize hj : dbN h P - (k + 1) = j at hp
  obtain hjn : j < dbN h P := by omega_using [hdb, hj]
  obtain ad : addr (P.scr + BitVec.ofNat 32 (oEm + lo P + j)) 0 = sa P.scr (oEm + lo P + j) := by
    rw [hg.addrD (by omega_using [hlo, hdb, hsum, hK, hD, hD0, hK0, e1, e2, fit, hk, hj, hjn]), Nat.add_zero]
  obtain rd : InRegions (s.rd ++ s.wr) (sa P.scr (oEm + lo P + j)) 1 := hg.rd hs (by omega_using [hlo, hdb, hsum, hK, hD, hD0, hK0, e1, e2, fit, hk, hj, hjn])
  obtain hb := hx.2.1 j hjn
  simp only [scanBody, isZero, ld, st, addi, Impl.RsaPkcs1Sig.X86.at_, List.cons_append, List.nil_append]
  refine wp_movzx8 (a := sa P.scr (oEm + lo P + j)) (by rw [ea_at, hp.esi]; exact ad) rd fun t1 u1 => ?_
  refine wp_mov fun t2 u2 => wp_subi fun t3 u3 cf3 _ => wp_sbb_self cf3 fun t4 u4 => ?_
  refine wp_xorI fun t5 u5 => wp_and fun t6 u6 => wp_and fun t7 u7 => ?_
  obtain s7 : (P.lay h.D).St τ t7 := (((((((hs.upd u1 (by decide)).upd u2 (by decide)).upd u3 (by decide)).upd u4
    (by decide)).upd u5 (by decide)).upd u6 (by decide)).upd u7 (by decide))
  refine s7.wp_slot (d := sVal) (by show sVal + 4 ≤ frameBytes; decide) (by decide) fun t8 s8 u8 => wp_or fun t9 u9 => ?_
  refine (s8.upd u9 (by decide)).wp_strFr (d := sVal) (by show sVal + 4 ≤ frameBytes; decide) fun t10 s10 m10 => ?_
  refine wp_mov fun t11 u11 => wp_and fun t12 u12 => ?_
  obtain s12 : (P.lay h.D).St τ t12 := (s10.upd u11 (by decide)).upd u12 (by decide)
  refine s12.wp_slot (d := sPos) (by show sPos + 4 ≤ frameBytes; decide) (by decide) fun t13 s13 u13 => wp_or fun t14 u14 => ?_
  refine (s13.upd u14 (by decide)).wp_strFr (d := sPos) (by show sPos + 4 ≤ frameBytes; decide) fun t15 s15 m15 => ?_
  refine wp_xorI fun t16 u16 => wp_and fun t17 u17 => wp_addi fun t18 u18 => wp_addi fun t19 u19 => ?_
  refine wp_subi fun t20 u20 _ z20 => WP.block_nil ?_
  -- The values.
  obtain b1 : t1.gpr .eax = (dbF h P τ j).setWidth 32 := by rw [u1.gpr, hb]
  obtain e2 : t2.gpr .edx = (dbF h P τ j).setWidth 32 := by rw [u2.gpr, b1]
  rw [e2, bz] at u4
  obtain mk : t6.gpr .edx = ((if dbF h P τ j = 0 then BitVec.allOnes 32 else 0) ^^^ BitVec.allOnes 32) &&&
      nfJ h P τ j := by
    simp (disch := decide) only [u6.gpr, u5.gpr, u4.gpr, u5.other, u4.other, u3.other, u2.other, u1.other, hp.ebx]
  obtain st := scan_step h hjn _ rfl (τ := τ)
  obtain m7 : t7.mem = s.mem := by rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  obtain a6 : t6.gpr .eax = (dbF h P τ j).setWidth 32 := by
    simp (disch := decide) only [u6.other, u5.other, u4.other, u3.other, u2.other, b1]
  obtain vV : t9.gpr .ebp = (vzJ h P τ (j + 1)).setWidth 32 := by
    rw [u9.gpr, u8.gpr, u8.other .eax (by decide), u7.gpr, mk, m7, hp.val, a6]
    exact st.2.1
  obtain d9 : t9.gpr .edx = t6.gpr .edx := by simp (disch := decide) only [u9.other, u8.other, u7.other]
  obtain i9 : t9.gpr .edi = BitVec.ofNat 32 j := by
    simp (disch := decide) only [u9.other, u8.other, u7.other, u6.other, u5.other, u4.other, u3.other, u2.other,
      u1.other, hp.edi]
  obtain mm10 : t10.mem = s.mem.writeW ((P.lay h.D).fr sVal) ((vzJ h P τ (j + 1)).setWidth 32) := by
    rw [m10.mem, vV, u9.mem, u8.mem, m7]
  obtain pV : t14.gpr .ebp = BitVec.ofNat 32 (pzJ h P τ (j + 1)) := by
    rw [u14.gpr, u13.gpr, u13.other .eax (by decide), u12.gpr, u11.gpr, u12.mem, u11.mem, mm10,
      Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide), hp.pos, u11.other .edx (by decide),
      m10.gpr, d9, mk, i9]
    exact st.1
  obtain mm15 : t20.mem = (s.mem.writeW ((P.lay h.D).fr sVal) ((vzJ h P τ (j + 1)).setWidth 32)).writeW
      ((P.lay h.D).fr sPos) (BitVec.ofNat 32 (pzJ h P τ (j + 1))) := by
    rw [u20.mem, u19.mem, u18.mem, u17.mem, u16.mem, m15.mem, pV, u14.mem, u13.mem, u12.mem, u11.mem, mm10]
  obtain s20 : (P.lay h.D).St τ t20 :=
    ((((s15.upd u16 (by decide)).upd u17 (by decide)).upd u18 (by decide)).upd u19 (by decide)).upd u20 (by decide)
  obtain kd : Kd h P τ t20.mem := by
    rw [mm15]
    exact (Kd.slot h hx (d := sVal) (by decide) (by decide) _).slot h (d := sPos) (by decide) (by decide) _
  obtain c19 : t19.gpr .ecx = BitVec.ofNat 32 (dbN h P - j) := by
    simp (disch := decide) only [u19.other, u18.other, u17.other, u16.other, m15.gpr, u14.other, u13.other,
      u12.other, u11.other, m10.gpr, u9.other, u8.other, u7.other, u6.other, u5.other, u4.other, u3.other,
      u2.other, u1.other, hp.ecx]
  obtain sk : SC h P τ (j + 1) t20 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp (disch := decide) only [u20.other, u19.other, u18.gpr, u17.other, u16.other, m15.gpr, u14.other,
        u13.other, u12.other, u11.other, m10.gpr, u9.other, u8.other, u7.other, u6.other, u5.other, u4.other,
        u3.other, u2.other, u1.other, hp.esi]
      rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_assoc]
    · simp (disch := decide) only [u20.other, u19.gpr, u18.other, u17.other, u16.other, m15.gpr, u14.other,
        u13.other, u12.other, u11.other, m10.gpr, u9.other, u8.other, u7.other, u6.other, u5.other, u4.other,
        u3.other, u2.other, u1.other, hp.edi]
      rw [BitVec.ofNat_add_ofNat]
    · rw [u20.gpr, c19, ofNat_pred (by omega_using [hdb, hj]), Nat.sub_sub]
    · have b9 : t9.gpr .ebx = nfJ h P τ j := by
        simp (disch := decide) only [u9.other, u8.other, u7.other, u6.other, u5.other, u4.other, u3.other,
          u2.other, u1.other, hp.ebx]
      obtain x16 : t16.gpr .edx = t6.gpr .edx ^^^ BitVec.allOnes 32 := by
        rw [u16.gpr, m15.gpr, u14.other .edx (by decide), u13.other .edx (by decide), u12.other .edx (by decide),
          u11.other .edx (by decide), m10.gpr, d9]
      obtain b16 : t16.gpr .ebx = t9.gpr .ebx := by
        rw [u16.other .ebx (by decide), m15.gpr, u14.other .ebx (by decide), u13.other .ebx (by decide),
          u12.other .ebx (by decide), u11.other .ebx (by decide), m10.gpr]
      rw [u20.other _ (by decide), u19.other _ (by decide), u18.other _ (by decide), u17.gpr, x16, b16, b9, mk]
      exact st.2.2
    · rw [mm15, Mem.readW_writeW_self32]
    · rw [mm15, Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  rw [c19, ofNat_pred (by omega_using [hdb, hj]), Nat.sub_sub, ofNat_beq_zero (by omega_using [hsum, hK]),
    show dbN h P - (j + 1) = k by omega_using [hk, hj]] at z20
  refine ⟨?_, fun h0 => ⟨s20, kd, hf', by rw [show dbN h P = j + 1 by omega_using [hdb, hj, h0]]; exact sk⟩,
    fun hpos => ⟨by omega_using [hk], s20, kd, hf', by rw [show dbN h P - k = j + 1 by omega_using [hk, hj]]; exact sk⟩⟩
  show eval .ne t20 = _
  simp only [eval, z20]
  by_cases h0 : k = 0 <;> simp [h0] <;> omega_using [h0]

end VG.Proof.RsaPss.X86.Vf

end

end


/-!
# RSASSA-PSS verification with a precomputed public key on x86: the scan's result

As on ARMv7 (`Proof/RsaPss/Arm/VfFixed.lean`): `scratch` into `ebp` again;
`acc` takes in that `DB`'s first nonzero byte is `0x01` and, if a salt length
is expected, that the salt after it has that length (`acc2`); then the flags
of `any_salt_len = 0` (`pos_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Vf

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes

variable (h : PssHash)

/-- The index of `DB`'s first nonzero byte, 0 if none. -/
abbrev pzF (P : EP) (τ : State) : Nat := pzJ h P τ (dbN h P)

/-- `acc` after the scan. -/
abbrev acc2 (P : EP) (τ : State) : BitVec 32 :=
  ((accW P τ ||| ((vzJ h P τ (dbN h P)).setWidth 32 ^^^ (1 : BitVec 32))) ||| nfJ h P τ (dbN h P) >>> 31) |||
    ((BitVec.ofNat 32 (dbN h P) - BitVec.ofNat 32 (pzF h P τ) - 1 ^^^ BitVec.ofNat 32 P.slt) &&& (anyW P - 1))

/-- What the paths after the scan keep. -/
abbrev K2 (P : EP) (τ : State) (m : Mem) : Prop :=
  In h.D P τ ∧ fits h P ∧ Bm h P m ∧ (∀ i < dbN h P, m (sa P.scr (oEm + lo P + i)) = dbF h P τ i) ∧
    (∀ i < h.D, m (sa P.scr (oEm + lo P + dbN h P + i)) = (seedV h P τ).getD i 0) ∧
    m.readW ((P.lay h.D).fr sPos) 32 = BitVec.ofNat 32 (pzF h P τ) ∧
    m.readW ((P.lay h.D).fr sAcc) 32 = acc2 h P τ

theorem anyW_z (P : EP) : (anyW P &&& anyW P == 0) = decide (P.any = 0) := by
  by_cases e : P.any = 0
  · rw [anyW, ite_eq_left e, decide_eq_true e]; rfl
  · rw [anyW, ite_eq_right e, decide_eq_false e]; rfl

/-- `acc` to its slot, and the flags of `any_salt_len = 0`. -/
theorem pos_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => (P.lay h.D).St τ s ∧ Kd h P τ s.mem ∧ fits h P ∧ SC h P τ (dbN h P) s) (.block posChk)
      (fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ K2 h P τ s.mem) ∧ s.zf = some (decide (P.any = 0))) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  refine VP.taint [.esp] posChk_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.sp, h₂.1.sp])
    fun τ s ⟨hs, hx, hf, hp⟩ => ?_
  have hi := hx.1.1
  simp only [posChk, ld, st, Impl.RsaPkcs1Sig.X86.stk]
  refine hs.wp_arg (vf_arg h (j := 10) (by decide)) (by decide) fun t1 s1 u1 => ?_
  obtain c1 : Ctx (P.lay h.D) P.scr τ t1 := ⟨s1, by rw [u1.gpr]; rfl⟩
  refine c1.wp_slot hg (d := sAcc) (by decide) (by decide) (by decide) fun t2 c2 u2 => ?_
  refine c2.wp_slot hg (d := sVal) (by decide) (by decide) (by decide) fun t3 c3 u3 => ?_
  refine wp_xorI fun t4 u4 => wp_or fun t5 u5 => wp_shr (by decide) fun t6 u6 _ => wp_or fun t7 u7 => ?_
  obtain c7 : Ctx (P.lay h.D) P.scr τ t7 :=
    (((c3.upd u4 (by decide) (by decide)).upd u5 (by decide) (by decide)).upd u6 (by decide) (by decide)).upd u7
      (by decide) (by decide)
  refine c7.wp_slot hg (d := sDb) (by decide) (by decide) (by decide) fun t8 c8 u8 => ?_
  refine wp_subm (B := (P.lay h.D).B) (by rw [c8.st.sp])
    (by rw [hg.aFr ok sPos (by decide)]; exact c8.rFr hg sPos (by decide)) fun t9 u9 => ?_
  refine wp_subi fun t10 u10 _ _ => ?_
  obtain c10 : Ctx (P.lay h.D) P.scr τ t10 := (c8.upd u9 (by decide) (by decide)).upd u10 (by decide) (by decide)
  refine wp_xorm (B := (P.lay h.D).B) (by rw [c10.st.sp]) (by rw [hg.aArg ok 8 (by simp)]; exact
      (by rw [c10.st.rd, c10.st.wr]; exact c10.st.ok.arg_read (vf_arg h (by decide)))) fun t11 u11 => ?_
  obtain c11 : Ctx (P.lay h.D) P.scr τ t11 := c10.upd u11 (by decide) (by decide)
  refine c11.wp_slot hg (d := sAny) (by decide) (by decide) (by decide) fun t12 c12 u12 => ?_
  refine wp_subi fun t13 u13 _ _ => wp_and fun t14 u14 => wp_or fun t15 u15 => ?_
  obtain c15 : Ctx (P.lay h.D) P.scr τ t15 :=
    ((c12.upd u13 (by decide) (by decide)).upd u14 (by decide) (by decide)).upd u15 (by decide) (by decide)
  refine c15.wp_st hg (d := sAcc) (by decide) fun t16 c16 m16 => ?_
  refine c16.wp_slot hg (d := sAny) (by decide) (by decide) (by decide) fun t17 c17 u17 => ?_
  refine wp_test fun t18 f18 z18 => WP.block_nil ?_
  -- The memory before the store, and `acc`.
  obtain m15 : t15.mem = s.mem := by
    rw [u15.mem, u14.mem, u13.mem, u12.mem, u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem,
      u3.mem, u2.mem, u1.mem]
  obtain va : t15.gpr .eax = acc2 h P τ := by
    obtain e7 : t7.gpr .eax = (accW P τ ||| ((vzJ h P τ (dbN h P)).setWidth 32 ^^^ (1 : BitVec 32))) |||
        nfJ h P τ (dbN h P) >>> 31 := by
      simp (disch := decide) only [u7.gpr, u6.gpr, u6.other, u5.gpr, u5.other, u4.gpr, u4.other, u3.gpr, u3.other,
        u2.gpr, u2.other, u1.other]
      rw [u2.mem, u1.mem, hx.1.2.2.2, hp.val, hp.ebx]
    obtain e14 : t14.gpr .edx = (BitVec.ofNat 32 (dbN h P) - BitVec.ofNat 32 (pzF h P τ) - 1 ^^^
        BitVec.ofNat 32 P.slt) &&& (anyW P - 1) := by
      simp (disch := decide) only [u14.gpr, u13.gpr, u13.other, u12.gpr, u12.other, u11.gpr, u10.gpr, u9.gpr,
        u8.gpr]
      rw [u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem,
        hg.aFr ok sPos (by decide), hp.pos, hx.1.2.2.1.2.2.1, hx.1.2.2.1.2.2.2, hg.aArg ok 8 (by simp),
        hs.arg (vf_arg h (by decide))]
      rfl
    rw [u15.gpr, e14, u14.other .eax (by decide), u13.other .eax (by decide), u12.other .eax (by decide),
      u11.other .eax (by decide), u10.other .eax (by decide), u9.other .eax (by decide), u8.other .eax (by decide),
      e7]
  obtain mm : t18.mem = s.mem.writeW ((P.lay h.D).fr sAcc) (acc2 h P τ) := by
    rw [f18.mem, u17.mem, m16.mem, m15, va]
  obtain fr : Frame [slotR (P.lay h.D) sAcc] s.mem t18.mem := by rw [mm]; exact slot_frame _ _ _ _
  obtain kk : ∀ d, d + 4 ≤ frameBytes → (d + 4 ≤ sAcc ∨ sAcc + 4 ≤ d) →
      t18.mem.readW ((P.lay h.D).fr d) 32 = s.mem.readW ((P.lay h.D).fr d) 32 := fun d hd hd' => by
    rw [mm, Lay.readW_fr_other _ _ _ hd' (by unfold frameBytes at hd; omega_using [hd]) (by decide)]
  obtain kb : ∀ o, o + 1 ≤ oRsa → t18.mem (sa P.scr o) = s.mem (sa P.scr o) := fun o ho =>
    fr _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hg.slot ok (o := o) (n := 1) (by omega_using [ho]) (by rw [hg.F]; decide)).symm _ (Region.contains_self _ _)
  obtain ⟨hlo, hdb, hsum, hK, hD, hD0, hK0⟩ := fitB h hi hf
  have e1 : oEm = 1024 := rfl
  have e2 : oRsa = 8192 := rfl
  refine ⟨⟨c17.fupd f18, hi, hf, ⟨by rw [kk _ (by decide) (by decide)]; exact hx.1.2.2.1.1,
      by rw [kk _ (by decide) (by decide)]; exact hx.1.2.2.1.2.1, by rw [kk _ (by decide) (by decide)]; exact hx.1.2.2.1.2.2.1,
      by rw [kk _ (by decide) (by decide)]; exact hx.1.2.2.1.2.2.2⟩,
    fun i hi' => by rw [kb _ (by omega_using [hsum, hK, e1, e2, hi'])]; exact hx.2.1 i hi',
    fun i hi' => by rw [kb _ (by omega_using [hsum, hK, e1, e2, hi'])]; exact hx.2.2 i hi',
    by rw [kk _ (by decide) (by decide)]; exact hp.pos, by rw [mm, Mem.readW_writeW_self32]⟩, ?_⟩
  rw [z18, u17.gpr, m16.mem, m15, Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide),
    hx.1.2.2.1.2.2.2, anyW_z]

end VG.Proof.RsaPss.X86.Vf
