module

public import VerifiedGarbage.Impl.RsaPss.X86
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Entry
public import VerifiedGarbage.Spec.RsaPss
public import VerifiedGarbage.Spec.RsaPss.Contract
public import VerifiedGarbage.Spec.RsaPss.MdTable
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.RsaPss.X86.Base
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.Exec
public import VerifiedGarbage.Proof.RsaPss.X86.Params
public import VerifiedGarbage.Proof.RsaPss.X86.Hash
import VerifiedGarbage.Proof.RsaPss.X86.Taint
import VerifiedGarbage.Proof.RsaPss.X86.CtBase
import VerifiedGarbage.Proof.RsaPss.SignCases
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Loops
public import VerifiedGarbage.Proof.RsaOaep.X86.Mgf
public import VerifiedGarbage.Proof.RsaPss.X86.CtTab
public import VerifiedGarbage.Proof.RsaPss.X86.YDig
import VerifiedGarbage.Proof.RsaPss.X86.CtInit
import VerifiedGarbage.Proof.RsaPss.X86.CtLen
public import VerifiedGarbage.Proof.RsaPss.EncBytes
import VerifiedGarbage.Proof.RsaPss.CtPad
import VerifiedGarbage.Proof.RsaPss.X86.CtHash
import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.RsaOaep.X86.MgfSlots
import VerifiedGarbage.Proof.RsaOaep.X86.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-- `pomega` (`CtBase.lean`), with `omega_arith` for its `omega`: the frame's offsets as facts, and of
the context only the arithmetic facts connected to the goal. -/
local macro "pomega_arith" : tactic => `(tactic| (have _ : VG.Impl.RsaPss.X86.oCW = 0 := rfl; have _ : VG.Impl.RsaPss.X86.oSt = 512 := rfl; have _ : VG.Impl.RsaPss.X86.oSel = 768 := rfl; have _ : VG.Impl.RsaPss.X86.oDig = 832 := rfl; have _ : VG.Impl.RsaPss.X86.oLen = 896 := rfl; have _ : VG.Impl.RsaPss.X86.oEm = 1024 := rfl; have _ : VG.Impl.RsaPss.X86.oY = 2048 := rfl; have _ : VG.Impl.RsaPss.X86.oRsa = 8192 := rfl; have _ : VG.Impl.RsaPss.X86.frameBytes = 144 := rfl; omega_arith))

/-! ### `RsaPss.X86.SgEnc2`, which only this module used -/

section

/-! ### `RsaPss.X86.SgEnc1`, which only this module used -/

section

/-! ### `RsaPss.X86.SgChk`, which only this module used -/

section

/-! ### `RsaPss.X86.SgBase`, which only this module used -/

section

/-!
# RSASSA-PSS signing on x86: where everything is

As on ARMv7 (`Proof/RsaPss/Arm/SgBase.lean`): `EP`, what two runs share
(the frame's base `B`, the pointers, the lengths, the public key's bytes
`nB` and `eB`, and the tables: the hash function's of `MdHash` at `tabH`,
whose functions are at `hai`, `hac` and `had`, and MGF1's of `MdHash` at
`tab`, whose functions are at `ai`, `au` and `af`, with what each run's
entry state holds of them, `TH` and `T`), and its layout (`EP.lay`), with
the 3448 bytes below the frame that the hash function's calls and the
private-key operation use. `In D P σ`: the state `σ` the body starts from,
for digests of `D` bytes. The shared contract, with the stack of the frames
and of the calls, gives `In D (ep s …) (entered frameBytes s)` for the
digest length `D` that the argument `digest_len` is (`in_of_pre`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Sg

open VG VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes

/-- What two runs share. -/
structure EP where
  B : BitVec 32
  out : BitVec 32
  n : BitVec 32
  e : BitVec 32
  p : BitVec 32
  q : BitVec 32
  dp : BitVec 32
  dq : BitVec 32
  qinv : BitVec 32
  dig : BitVec 32
  salt : BitVec 32
  scr : BitVec 32
  K : Nat
  el : Nat
  pl : Nat
  ql : Nat
  sl : Nat
  scl : Nat
  nB : List Byte
  eB : List Byte
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

namespace EP

variable (D : Nat) (P : EP)

abbrev OUT : Region := ⟨P.out.setWidth 64, P.K⟩
abbrev N : Region := ⟨P.n.setWidth 64, P.K⟩
abbrev E : Region := ⟨P.e.setWidth 64, P.el⟩
abbrev PP : Region := ⟨P.p.setWidth 64, P.pl⟩
abbrev QQ : Region := ⟨P.q.setWidth 64, P.ql⟩
abbrev DP : Region := ⟨P.dp.setWidth 64, P.pl⟩
abbrev DQ : Region := ⟨P.dq.setWidth 64, P.ql⟩
abbrev QI : Region := ⟨P.qinv.setWidth 64, P.pl⟩
abbrev DIG : Region := ⟨P.dig.setWidth 64, D⟩
abbrev SALT : Region := ⟨P.salt.setWidth 64, P.sl⟩
abbrev SCR : Region := ⟨P.scr.setWidth 64, P.scl * 8⟩
abbrev TABH : Region := Sig.tableRegion 32 (P.tabH.setWidth 64) 11
abbrev TAB : Region := Sig.tableRegion 32 (P.tab.setWidth 64) 11

/-- The arguments, in order. -/
abbrev argv : List (BitVec 32) :=
  [P.out, BitVec.ofNat 32 P.K, P.n, BitVec.ofNat 32 P.K, P.e, BitVec.ofNat 32 P.el, P.p, BitVec.ofNat 32 P.pl,
    P.q, BitVec.ofNat 32 P.ql, P.dp, BitVec.ofNat 32 P.pl, P.dq, BitVec.ofNat 32 P.ql, P.qinv,
    BitVec.ofNat 32 P.pl, P.dig, BitVec.ofNat 32 D, P.salt, BitVec.ofNat 32 P.sl, P.scr, BitVec.ofNat 32 P.scl,
    P.tabH, P.tab]

abbrev ro : List Region := [P.N, P.E, P.PP, P.QQ, P.DP, P.DQ, P.QI, P.DIG D, P.SALT, P.TABH, P.TAB]
abbrev rw : List Region := [P.OUT, P.SCR]

abbrev lay : Lay where
  B := P.B
  F := frameBytes
  argv := P.argv D
  ro := P.ro D
  rw := P.rw
  C := 3448

end EP

/-- The state the body starts from. -/
structure In (D : Nat) (P : EP) (σ : State) : Prop where
  ok : (P.lay D).Ok σ
  kv : Spec.Rsa.lenValid P.K
  el1 : 1 ≤ P.el
  elK : P.el ≤ P.K
  pl1 : 1 ≤ P.pl
  plK : P.pl < P.K
  ql1 : 1 ≤ P.ql
  qlK : P.ql < P.K
  slK : Spec.RsaPss.scratchWords P.K ≤ P.scl
  sl32 : P.sl < 2 ^ 32
  scl32 : P.scl < 2 ^ 32
  nB : Spec.Rsa.bytesAt σ.mem (P.n.setWidth 64) P.K = P.nB
  eB : Spec.Rsa.bytesAt σ.mem (P.e.setWidth 64) P.el = P.eB
  tabTH : P.TH σ
  tabT : P.T σ

namespace In

variable {D : Nat} {P : EP} {σ : State} (h : In D P σ)
include h

theorem k64 : 64 ≤ P.K := h.kv.1
theorem k1024 : P.K ≤ 1024 := h.kv.2

/-- Our part of `scratch`. -/
theorem geo : Geo (P.lay D) P.scr := by
  have hs := h.slK
  have hK := h.k1024
  obtain hf := h.ok.fits (P.SCR) (by simp)
  simp only [BitVec.toNat_setWidth] at hf
  rw [Nat.mod_eq_of_lt (by have := P.scr.isLt; omega_using [])] at hf
  unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at hs
  exact ⟨rfl, by unfold oRsa; omega_using [hs, hf], ⟨P.scl * 8, by unfold oRsa; omega_using [hs], by simp⟩, ⟨σ, h.ok⟩,
    by show 48 ≤ 3448; decide⟩

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
abbrev stackBytes : Nat := 16 + frameBytes + 3448

/-- The shared contract, with the hash function's table one of `tsH` and
MGF1's one of `ts`, and that stack. -/
abbrev spec (tsH ts : List FnTable) : Contract isa :=
  Spec.RsaPss.signMdTableContract (abi.withTables Spec.RsaPss.signMdTableSig [("hash", tsH), ("mgf1", ts)]) stackBytes

/-- Unfolds the contract's precondition at `h`. -/
macro "sign_pre" " at " h:ident : tactic => `(tactic| (
  sig_pre [Spec.RsaPss.signMdTableContract, Spec.RsaPss.signMdTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argSlots, argVal, argBytes, stackBelow] at $h:ident
  sig_pre [Spec.RsaPss.signMdTableContract, Spec.RsaPss.signMdTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argSlots, argVal, argBytes, stackBelow] at $h:ident
  simp only [Option.map_some, Nat.reduceAdd, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq,
    exists_eq_left'] at $h:ident))

/-- The public parameters of an entry state, with the hash function's
functions at `hai`, `hac` and `had` and MGF1's at `ai`, `au` and `af`, and
`TH` and `T` of the entry. -/
def ep (s : State) (hai hac had : BitVec 32) (TH : State → Prop) (ai au af : BitVec 32) (T : State → Prop) :
    EP where
  B := s.gpr .esp - BitVec.ofNat 32 16 - BitVec.ofNat 32 frameBytes
  out := arg s 0
  n := arg s 2
  e := arg s 4
  p := arg s 6
  q := arg s 8
  dp := arg s 10
  dq := arg s 12
  qinv := arg s 14
  dig := arg s 16
  salt := arg s 18
  scr := arg s 20
  K := (arg s 3).toNat
  el := (arg s 5).toNat
  pl := (arg s 7).toNat
  ql := (arg s 9).toNat
  sl := (arg s 19).toNat
  scl := (arg s 21).toNat
  nB := Spec.Rsa.bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat
  eB := Spec.Rsa.bytesAt s.mem ((arg s 4).setWidth 64) (arg s 5).toNat
  tabH := arg s 22
  hai := hai
  hac := hac
  had := had
  TH := TH
  tab := arg s 23
  ai := ai
  au := au
  af := af
  T := T

variable {hai hac had : BitVec 32} {TH : State → Prop} {ai au af : BitVec 32} {T : State → Prop}

theorem ep_lay (D : Nat) (s : State) :
    (ep s hai hac had TH ai au af T).lay D = layOf frameBytes ((ep s hai hac had TH ai au af T).argv D)
      ((ep s hai hac had TH ai au af T).ro D) (ep s hai hac had TH ai au af T).rw s 3448 := rfl

/-- The tables, as the contract gives them: the hash function's one of `tsH`
at the argument 22 and MGF1's one of `ts` at 23, with the functions of
distinct names at distinct addresses, and the digest's length. -/
theorem spec_tab {tsH ts : List FnTable} {s : State} (h : (spec tsH ts).pre s) :
    (∃ T ∈ tsH, Abi.tableHeld 32 s.mem ((arg s 22).setWidth 64) (FnTable.words isa s T)) ∧
      (∃ T ∈ ts, Abi.tableHeld 32 s.mem ((arg s 23).setWidth 64) (FnTable.words isa s T)) ∧
      ((tsH.map (fun T : FnTable => T.fns)).flatten ++ ((ts.map (fun T : FnTable => T.fns)).flatten ++ [])).Pairwise
        (fun f g => f ≠ g → (s.syms f).setWidth 64 ≠ (s.syms g).setWidth 64) ∧
      (arg s 22).toNat + 44 ≤ 2 ^ 32 ∧ (arg s 23).toNat + 44 ≤ 2 ^ 32 ∧
      Spec.RsaPss.digestLenOk 32 s.mem ((arg s 22).setWidth 64) (arg s 17) := by
  sign_pre at h
  sig_split h
  rename_i hsp hsa hheldH hheld hpw hrd hwr oN oE oP oQ oDP oDQ oQI oD oSl oS oTH oT oA nS nA eS eA pS pA qS qA dpS
    dpA dqS dqA qiS qiA dS dA slS slA sTH sT sA thA tA rO rN rE rP rQ rDP rDQ rQI rD rSl rS rTH rT rA kO kN kE kP kQ
    kDP kDQ kQI kD kSl kS kTH kT kA fO fN fE fP fQ fDP fDQ fQI fD fSl fS fTH fT kv olk el1 elK pl1 plK ql1 qlK dpl
    qil dql slK
  exact ⟨hheldH, hheld, hpw, fTH, fT, h⟩

theorem in_of_pre {tsH ts : List FnTable} {s : State} (h : (spec tsH ts).pre s)
    (hTH : TH (entered frameBytes s)) (hT : T (entered frameBytes s)) :
    In (arg s 17).toNat (ep s hai hac had TH ai au af T) (entered frameBytes s) := by
  sign_pre at h
  sig_split h
  rename_i hsp hsa hheldH hheld hpw hrd hwr oN oE oP oQ oDP oDQ oQI oD oSl oS oTH oT oA nS nA eS eA pS pA qS qA dpS
    dpA dqS dqA qiS qiA dS dA slS slA sTH sT sA thA tA rO rN rE rP rQ rDP rDQ rQI rD rSl rS rTH rT rA kO kN kE kP kQ
    kDP kDQ kQI kD kSl kS kTH kT kA fO fN fE fP fQ fDP fDQ fQI fD fSl fS fTH fT kv olk el1 elK pl1 plK ql1 qlK dpl
    qil dql slK
  simp only [stackBytes, frameBytes, Nat.reduceAdd] at hsp kO kN kE kP kQ kDP kDQ kQI kD kSl kS kTH kT kA
  obtain a1 : arg s 1 = arg s 3 := BitVec.eq_of_toNat_eq olk
  obtain a11 : arg s 11 = arg s 7 := BitVec.eq_of_toNat_eq dpl
  obtain a15 : arg s 15 = arg s 7 := BitVec.eq_of_toNat_eq qil
  obtain a13 : arg s 13 = arg s 9 := BitVec.eq_of_toNat_eq dql
  rw [olk] at hwr oN oE oP oQ oDP oDQ oQI oD oSl oS oTH oT oA rO kO fO
  rw [dpl] at hrd oDP dpS dpA rDP kDP fDP
  rw [qil] at hrd oQI qiS qiA rQI kQI fQI
  rw [dql] at hrd oDQ dqS dqA rDQ kDQ fDQ
  obtain h16 : 4 * Impl.RsaPkcs1Sig.X86.savedRegs.length ≤ (s.gpr .esp).toNat := by
    simp only [Impl.RsaPkcs1Sig.X86.savedRegs, List.length_cons, List.length_nil]; omega_using [hsp]
  obtain hpush : Frame [below (s.gpr .esp) (4 * Impl.RsaPkcs1Sig.X86.savedRegs.length)] s.mem
      (entered frameBytes s).mem :=
    pushed_frame (by decide) h16
  obtain below16 : Region.Sub (below (s.gpr .esp) (4 * Impl.RsaPkcs1Sig.X86.savedRegs.length))
      ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 3608, 3608⟩ := by
    simp only [below, Impl.RsaPkcs1Sig.X86.savedRegs, List.length_cons, List.length_nil]
    rw [Taint.sub_setWidth (by omega_using [hsp])]
    exact Offset.sub_below _ (by omega_using []) (by omega_using [])
  refine
    { ok := ?_
      kv := kv, el1 := el1, elK := elK, pl1 := pl1, plK := plK, ql1 := ql1, qlK := qlK, slK := slK
      sl32 := (arg s 19).isLt
      scl32 := (arg s 21).isLt
      nB := Proof.RsaPkcs1Sig.bytesAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kN.sub_left below16).symm)
        (by show (arg s 3).toNat ≤ 2 ^ 64; omega_using [])
      eB := Proof.RsaPkcs1Sig.bytesAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kE.sub_left below16).symm)
        (by show (arg s 5).toNat ≤ 2 ^ 64; omega_using [])
      tabTH := hTH
      tabT := hT }
  rw [ep_lay]
  refine ok_entered (S := 3608) rfl (by decide) hsp (by simp) (by simp; omega_using [hsa]) hrd
    (by rw [hwr]; rfl) ?_ ?_ ?_ ?_ ?_ ?_
  · intro r hr
    simp only [EP.ro, EP.rw, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [kN, kE, kP, kQ, kDP, kDQ, kQI, kD, kSl, kTH, kT, kO, kS]
  · intro r hr
    simp only [EP.rw, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [rO, rS]
  · intro w hw r hr
    simp only [EP.rw, List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [EP.ro, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hw with rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [oN, oE, oP, oQ, oDP, oDQ, oQI, oD, oSl, oTH, oT, oA, nS.symm, eS.symm, pS.symm, qS.symm, dpS.symm,
      dqS.symm, qiS.symm, dS.symm, slS.symm, sTH, sT, sA]
  · exact List.pairwise_pair.mpr oS
  · intro r hr
    simp only [EP.ro, EP.rw, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [ep, BitVec.toNat_setWidth, Sig.tableRegion]
    all_goals first
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 2).isLt; omega_using [])]; omega_using [fN, fE, fP, fQ, fDP, fDQ, fQI,
          fD, fSl, fTH, fT, fO, fS])
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 4).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 6).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 8).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 10).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 12).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 14).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 16).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 18).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 22).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 23).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 0).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 20).isLt; omega_arith)]; omega_arith)
  · intro j hj
    have : j < 24 := hj
    obtain h24 : ∀ j < 24, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨
        j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨
        j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 := by decide
    rcases h24 j this with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl <;> simp [ep, a1, a11, a13, a15]

end VG.Proof.RsaPss.X86.Sg

end

end


/-!
# RSASSA-PSS signing on x86: the checks

`scratch` into `ebp` and the arguments of `params`, then the encoding's
parameters and whether everything fits (`chk_vp`): the modulus' first byte
not zero, and `lo + hLen + 2 + sLen ≤ k`; if not, zeros to `out` and 0
returned (`fail_vp`), the result the specification gives (`sign_invalid`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Sg

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes

variable (h : PssHash)

/-- A state of the body. -/
abbrev S (P : EP) (σ s : State) : Prop := In h.D P σ ∧ (P.lay h.D).St σ s

/-- The modulus' first byte, `lo` and whether everything fits. -/
abbrev n0 (P : EP) : Byte := P.nB.getD 0 0
abbrev lo (P : EP) : Nat := if (n0 P).toNat ≤ 1 then 1 else 0
abbrev fits (P : EP) : Prop := n0 P ≠ 0 ∧ lo P + h.D + 2 + P.sl ≤ P.K

/-- The buffers the body only reads, in the run from `σ`. -/
abbrev pB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (P.p.setWidth 64) P.pl
abbrev qB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (P.q.setWidth 64) P.ql
abbrev dpB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (P.dp.setWidth 64) P.pl
abbrev dqB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (P.dq.setWidth 64) P.ql
abbrev qiB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (P.qinv.setWidth 64) P.pl
abbrev digB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (P.dig.setWidth 64) h.D
abbrev saltB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (P.salt.setWidth 64) P.sl

/-- The result, with MGF1's hash function `G`. -/
abbrev Res (G : Spec.Mgf1.Hash) (P : EP) (σ : State) (m : Mem) (r : BitVec 32) : Prop :=
  Spec.Rsa.writtenOutcome m (P.out.setWidth 64) P.K r
    (Spec.RsaPss.sign h.G G P.nB P.eB (pB P σ) (qB P σ) (dpB P σ) (dqB P σ) (qiB P σ) (digB h P σ) (saltB P σ))

/-- The end of the body. -/
abbrev Fin (G : Spec.Mgf1.Hash) (P : EP) (σ s : State) : Prop := S h P σ s ∧ Res h G P σ s.mem (s.gpr .eax)

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

/-- After the checks. -/
abbrev C1 (P : EP) (σ s : State) : Prop :=
  Ctx (P.lay h.D) P.scr σ s ∧ In h.D P σ ∧ s.mem.readW ((P.lay h.D).fr sC) 32 = cW ((n0 P).setWidth 32) ∧
    s.mem.readW ((P.lay h.D).fr sLo) 32 = BitVec.ofNat 32 (lo P) ∧
    s.mem.readW ((P.lay h.D).fr sDb) 32 = dbW P.K h.D ((n0 P).setWidth 32) ∧ s.zf = some (decide (fits h P))

/-- After `signChk`. -/
abbrev C0 (P : EP) (σ s : State) : Prop :=
  Ctx (P.lay h.D) P.scr σ s ∧ In h.D P σ ∧ s.gpr .esi = P.n ∧ s.gpr .ecx = BitVec.ofNat 32 P.K ∧
    s.gpr .edx = BitVec.ofNat 32 P.sl

theorem chk_vp (P : EP) : VP (S h P) (.block (signChk ++ params h.H)) (C1 h P) := by
  refine VP.block_append (G := C0 h P) (VP.taint [.esp] signChk_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.sp, h₂.2.sp]) fun σ s ⟨hi, hs⟩ => ?_)
    (VP.taint _ h.certs.params (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s ⟨hc, hi, si, cx, dx⟩ => ?_)
  · have hl : ∀ j, j < 24 → j < ((P.lay h.D).argv).length := fun j hj => by simp; omega_using [hj]
    simp only [signChk, ld]
    refine hs.wp_arg (hl 20 (by decide)) (by decide) fun t1 s1 u1 => ?_
    refine s1.wp_arg (hl 2 (by decide)) (by decide) fun t2 s2 u2 => ?_
    refine s2.wp_arg (hl 3 (by decide)) (by decide) fun t3 s3 u3 => ?_
    refine s3.wp_arg (hl 19 (by decide)) (by decide) fun t4 s4 u4 => WP.block_nil ?_
    refine ⟨⟨s4, by simp (disch := decide) only [u4.other, u3.other, u2.other, u1.gpr]; rfl⟩, hi, ?_, ?_, ?_⟩
    · simp (disch := decide) only [u4.other, u3.other, u2.gpr]; rfl
    · simp (disch := decide) only [u4.other, u3.gpr]; rfl
    · rw [u4.gpr]; rfl
  · obtain ⟨c₁, -, a1, b1, d1⟩ := h₁
    obtain ⟨c₂, -, a2, b2, d2⟩ := h₂
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
  obtain ⟨σ', ok⟩ := hg.ok
  obtain ⟨nb, hn⟩ := n0_at hi hc.st
  rw [← si] at hn nb
  refine WP.mono (params_wp h.H hg hc rfl hn cx dx) fun t ⟨m, rd, wr, sp, bp, z⟩ => ?_
  rw [nb] at m z
  obtain fr : Frame [slotR (P.lay h.D) sLo, slotR (P.lay h.D) sC, slotR (P.lay h.D) sDb] s.mem t.mem := by
    rw [m]
    exact (((slot_frame _ _ _ _).mono (by simp)).trans ((slot_frame _ _ _ _).mono (by simp))).trans
      ((slot_frame _ _ _ _).mono (by simp))
  refine ⟨hc.write fr (fun r hr => ?_) rd wr sp bp, hi, ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      exact ⟨(P.lay h.D).FR, List.mem_cons_self, Offset.sub_base _ (by show _ ≤ frameBytes; decide)⟩
  · rw [m, Lay.readW_fr_other (d := sC) (e := sDb) _ _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]
  · rw [m, Lay.readW_fr_other (d := sLo) (e := sDb) _ _ _ (by decide) (by decide) (by decide),
      Lay.readW_fr_other (d := sLo) (e := sC) _ _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32, loW_byte]
  · rw [m, Mem.readW_writeW_self32]
  · rw [z, failW_z hK (show h.H.D ≤ 64 from hD) hi.sl32]

/-! ## When something does not fit -/

theorem nB_length {D : Nat} {P : EP} {σ : State} (hi : In D P σ) : P.nB.length = P.K := by
  rw [← hi.nB, RsaPkcs1Sig.bytesAt_len]

/-- The specification refuses what does not fit. -/
theorem sign_invalid (G : Spec.Mgf1.Hash) {P : EP} {σ : State} (hi : In h.D P σ) (hf : ¬ fits h P) :
    Spec.RsaPss.sign h.G G P.nB P.eB (pB P σ) (qB P σ) (dpB P σ) (dqB P σ) (qiB P σ) (digB h P σ)
      (saltB P σ) = .invalid := by
  obtain hl := nB_length hi
  have hK := hi.k64
  obtain ⟨b, rest, hbr⟩ : ∃ b rest, P.nB = b :: rest := by
    cases e : P.nB with
    | nil => rw [e] at hl; simp at hl; omega
    | cons b rest => exact ⟨b, rest, rfl⟩
  obtain hn0 : n0 P = b := by simp [n0, hbr]
  unfold fits lo at hf
  rw [hn0] at hf
  rw [hbr]
  by_cases hb : b = 0
  · subst hb
    exact RsaPss.sign_zero₂ G h.G ..
  · refine RsaPss.sign_long₂ G h.G _ _ _ _ _ _ _ _ ?_
    obtain e1 := lo_eq hb rest
    obtain e2 := RsaPss.emLength_eq rest hb
    have gl : h.G.len = h.D := h.glen
    rw [gl, RsaPkcs1Sig.bytesAt_len]
    rw [hbr, List.length_cons] at hl
    rw [List.length_cons] at e1
    split at e2 <;> split at e1 <;> split at hf <;> simp only [hb, ne_eq, not_false_eq_true, true_and] at hf <;>
      omega

/-- `out` zeros and 0, the specification's result. -/
abbrev F1 (P : EP) (σ s : State) : Prop :=
  Ctx (P.lay h.D) P.scr σ s ∧ In h.D P σ ∧ ¬ fits h P ∧ s.gpr .esi = P.out ∧
    s.gpr .ecx = BitVec.ofNat 32 P.K ∧ s.gpr .eax = 0

abbrev F2 (P : EP) (σ s : State) : Prop :=
  Ctx (P.lay h.D) P.scr σ s ∧ In h.D P σ ∧ ¬ fits h P ∧ Spec.Rsa.bytesAt s.mem (P.out.setWidth 64) P.K = List.replicate P.K 0

theorem fail_vp (G : Spec.Mgf1.Hash) (P : EP) :
    VP (fun σ s => C1 h P σ s ∧ isa.eval .ne s = some true) (signFail) (Fin h G P) := by
  show VP _ (.seq (.block [ld .esi (arg 0), ld .ecx (arg 3), mi .eax 0]) (.seq zeroLoop (.block [mi .eax 0]))) _
  refine VP.seq (G := F1 h P) (VP.taint [.esp] failArgs_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.1.st.sp, h₂.1.1.st.sp])
    fun σ s ⟨⟨hc, hi, _, _, _, z⟩, e⟩ => ?_) (VP.seq (G := F2 h P) ?_ ?_)
  · have hf : ¬ fits h P := fun hfits => by
      simp only [eval, z, decide_eq_true hfits] at e
      exact absurd e (by decide)
    have hg := hi.geo
    obtain hl : ∀ j, j < 24 → j < ((P.lay h.D).argv).length := fun j hj => by simp; omega_using [hj]
    simp only [ld, mi]
    refine hc.wp_arg hg (hl 0 (by decide)) (by decide) (by decide) fun t1 c1 u1 =>
      c1.wp_arg hg (hl 3 (by decide)) (by decide) (by decide) fun t2 c2 u2 => wp_movi fun t3 u3 =>
        WP.block_nil ⟨c2.upd u3 (by decide) (by decide), hi, hf, ?_, ?_, ?_⟩
    · simp (disch := decide) only [u3.other, u2.other, u1.gpr]; rfl
    · simp (disch := decide) only [u3.other, u2.gpr]; rfl
    · rw [u3.gpr]; rfl
  · by_cases hP : ∃ σ, In h.D P σ
    swap
    · exact VP.empty fun σ s hs => hP ⟨σ, hs.2.1⟩
    obtain ⟨σ₀, hi₀⟩ := hP
    have hK := hi₀.k1024
    obtain hfo := hi₀.ok.fits P.OUT (by simp)
    simp only [BitVec.toNat_setWidth] at hfo
    rw [Nat.mod_eq_of_lt (by have := P.out.isLt; omega_using [])] at hfo
    obtain wb : WBuf (P.lay h.D) P.out P.K := ⟨hfo, by omega_using [hK], ⟨P.OUT, by simp, Region.contains_self _ _⟩⟩
    refine (zero_vp (scr := P.scr) wb (by have := hi₀.k64; omega_using [this])
      (Inv := fun σ _ => In h.D P σ ∧ ¬ fits h P) fun _ _ _ hi _ => hi).mono
      (fun σ s ⟨hc, hi, hf, si, cx, ax⟩ => ⟨hc, ⟨hi, hf⟩, si, cx, ax⟩) fun σ s ⟨hc, ⟨hi, hf⟩, hz⟩ => ?_
    refine ⟨hc, hi, hf, ?_⟩
    apply List.ext_getElem (by simp [RsaPkcs1Sig.bytesAt_len])
    intro i h₁ h₂
    rw [RsaPkcs1Sig.bytesAt_len] at h₁
    rw [List.getElem_replicate, ← hz i h₁, ← RsaPkcs1Sig.bytesAt_getD (m := s.mem) (p := P.out.setWidth 64) h₁ 0, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [RsaPkcs1Sig.bytesAt_len]; exact h₁)]; rfl
  · refine VP.taint [.esp, .ebp] ret0_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.1.st.sp, h₂.1.st.sp]
      · rw [h₁.1.ebp, h₂.1.ebp]) fun σ s ⟨hc, hi, hf, hz⟩ => ?_
    simp only [mi]
    refine wp_movi fun t u => WP.block_nil ⟨⟨hi, hc.st.upd u (by decide)⟩, ?_⟩
    rw [Res, sign_invalid h G hi hf, u.gpr, u.mem]
    exact ⟨rfl, hz⟩

end VG.Proof.RsaPss.X86.Sg

end

end


/-!
# RSASSA-PSS signing on x86: `H = Hash(M')`

When everything fits (`E0`): `M' = 0x00 ×8 ‖ mHash ‖ salt` in `Y`
(`yDig_sg`, `salt_vp`), its length and blocks to their slots (`lenSet_vp`),
and its hash `H` at `oDig` (`hash_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Sg

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes

variable (h : PssHash)

/-- The modulus' first byte, as a word; `dbLen`. -/
abbrev xB (P : EP) : BitVec 32 := (n0 P).setWidth 32
abbrev dbN (P : EP) : Nat := P.K - lo P - h.D - 1

/-- The slots of the encoding's parameters. -/
abbrev Bm (P : EP) (m : Mem) : Prop :=
  m.readW ((P.lay h.D).fr sC) 32 = cW (xB P) ∧ m.readW ((P.lay h.D).fr sLo) 32 = BitVec.ofNat 32 (lo P) ∧
    m.readW ((P.lay h.D).fr sDb) 32 = BitVec.ofNat 32 (dbN h P)

/-- What the encoding keeps. -/
abbrev Kp (P : EP) (σ : State) (m : Mem) : Prop := In h.D P σ ∧ fits h P ∧ Bm h P m

/-- When everything fits. -/
abbrev E0 (P : EP) (σ s : State) : Prop := Ctx (P.lay h.D) P.scr σ s ∧ Kp h P σ s.mem

/-- What misses the slots of the parameters. -/
abbrev Away3 (L : Lay) (r : Region) : Prop :=
  (slotR L sC).Disjoint r ∧ (slotR L sLo).Disjoint r ∧ (slotR L sDb).Disjoint r

theorem Kp.keep {P : EP} {σ : State} {m m' : Mem} {rs : List Region} (hk : Kp h P σ m) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Away3 (P.lay h.D) r) : Kp h P σ m' :=
  ⟨hk.1, hk.2.1, slot_keep hf (fun r hr => (hd r hr).1) hk.2.2.1, slot_keep hf (fun r hr => (hd r hr).2.1) hk.2.2.2.1,
    slot_keep hf (fun r hr => (hd r hr).2.2) hk.2.2.2.2⟩

theorem away3_scr {L : Lay} {scr : BitVec 32} (hg : Geo L scr) {o n : Nat} (ho : o + n ≤ oRsa) :
    Away3 L (sR scr o n) := by
  obtain ⟨σ', ok⟩ := hg.ok
  exact ⟨hg.slot ok ho (by rw [hg.F]; decide), hg.slot ok ho (by rw [hg.F]; decide),
    hg.slot ok ho (by rw [hg.F]; decide)⟩

theorem away3_slot {L : Lay} {d : Nat} (hd : d + 4 ≤ frameBytes) (h₁ : d + 4 ≤ sLo ∨ sDb + 4 ≤ d) :
    Away3 L (slotR L d) := by
  have e1 : sLo = 40 := rfl
  have e2 : sC = 44 := rfl
  have e3 : sDb = 48 := rfl
  exact ⟨slotSep (by decide) hd (by omega_using [h₁, e1, e2, e3]), slotSep (by decide) hd (by omega_using [h₁, e1, e3]), slotSep (by decide) hd (by omega_using [h₁, e1, e3])⟩

theorem away3_ctW {L : Lay} {scr : BitVec 32} (hg : Geo L scr) {T : Nat} (hT : T ≤ 2048) :
    ∀ r ∈ ctW h L scr T, Away3 L r := fun r hr =>
  ⟨ctW_slot h hg hT (by decide) (by decide) (by decide) r hr, ctW_slot h hg hT (by decide) (by decide) (by decide) r hr,
    ctW_slot h hg hT (by decide) (by decide) (by decide) r hr⟩

/-- Everything fits, and the parameters are in their slots. -/
theorem e0_of {P : EP} {σ s : State} (hc : C1 h P σ s) (e : isa.eval .ne s = some false) : E0 h P σ s := by
  obtain ⟨hc, hi, sc, sl, sd, z⟩ := hc
  obtain hf : fits h P := by
    simp only [eval, z, Option.map_some, Option.some.injEq, Bool.not_eq_false', decide_eq_true_eq] at e
    exact e
  refine ⟨hc, hi, hf, sc, sl, ?_⟩
  rw [sd, dbW_byte]
  have : lo P ≤ 1 := by unfold lo; split <;> omega_using []
  have hD : h.H.D = h.D := rfl
  rw [Offset.ofNat_sub_ofNat (show lo P ≤ P.K by have := hf.2; omega_using [this]), Offset.ofNat_sub_ofNat (by have := hf.2; omega_using [this])]
  congr 1

/-- The digest, a buffer the body only reads. -/
theorem dig_buf {P : EP} (hP : ∃ σ, In h.D P σ) : RBuf (P.lay h.D) P.dig h.D := by
  obtain ⟨σ, hi⟩ := hP
  obtain hf := hi.ok.fits (P.DIG h.D) (by simp)
  simp only [BitVec.toNat_setWidth] at hf
  rw [Nat.mod_eq_of_lt (by have := P.dig.isLt; omega_using [])] at hf
  obtain hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega_arith
  exact ⟨hf, by omega_using [hD], ⟨P.DIG h.D, by simp, Region.contains_self _ _⟩⟩

/-- `M'`. -/
abbrev Mp (P : EP) (σ : State) : List Byte := Spec.RsaPss.zeros 8 ++ digB h P σ ++ saltB P σ

/-- `Y` cleared, and the digest after 8 zeros. -/
theorem yDig_sg (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (E0 h P) (yDig h.H 16)
      (fun σ s => E0 h P σ s ∧ ∀ i < 2048, s.mem (sa P.scr (oY + i)) = (Spec.RsaPss.zeros 8 ++ digB h P σ).getD i 0) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  refine (yDig_vp h hg (j := 16) h.certs.cpDig16 (by simp) (dgP := P.dig) rfl (dig_buf h ⟨σ₀, hi₀⟩)
    (fun o n hon => (hg.ro ok hon (R := P.DIG h.D) (by simp)).symm) (dl := digB h P)
    (fun σ => RsaPkcs1Sig.bytesAt_len _ _ _) (fun σ s hc i hi => ?_) (X := Kp h P)
    fun σ m m' hk hf => hk.keep h hf fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact away3_scr hg (by decide)).mono
    (fun σ s h => h) fun σ s ⟨hc, hk, hy⟩ => ⟨⟨hc, hk⟩, hy⟩
  obtain e : Spec.Rsa.bytesAt s.mem (P.dig.setWidth 64) h.D = Spec.Rsa.bytesAt σ.mem (P.dig.setWidth 64) h.D :=
    hc.st.ro (R := P.DIG h.D) (by simp)
  show s.mem (P.dig.setWidth 64 + BitVec.ofNat 64 i) = (Spec.Rsa.bytesAt σ.mem (P.dig.setWidth 64) h.D).getD i 0
  rw [← e, RsaPkcs1Sig.bytesAt_getD hi]

/-- `Y` before and after the salt. -/
abbrev Y1 (P : EP) (σ : State) (m : Mem) : Prop :=
  ∀ i < 2048, m (sa P.scr (oY + i)) = (Spec.RsaPss.zeros 8 ++ digB h P σ).getD i 0
abbrev Y2 (P : EP) (σ : State) (m : Mem) : Prop := ∀ i < 2048, m (sa P.scr (oY + i)) = (Mp h P σ).getD i 0

theorem salt_buf {P : EP} (hP : ∃ σ, In h.D P σ) : RBuf (P.lay h.D) P.salt P.sl := by
  obtain ⟨σ, hi⟩ := hP
  obtain hf := hi.ok.fits P.SALT (by simp)
  simp only [BitVec.toNat_setWidth] at hf
  rw [Nat.mod_eq_of_lt (by have := P.salt.isLt; omega_using [])] at hf
  exact ⟨hf, hi.sl32, ⟨P.SALT, by simp, Region.contains_self _ _⟩⟩

theorem salt_at {P : EP} {σ s : State} (hc : Ctx (P.lay h.D) P.scr σ s) {i : Nat} (hi : i < P.sl) :
    s.mem (byteAt P.salt i) = (saltB P σ).getD i 0 := by
  obtain e : Spec.Rsa.bytesAt s.mem (P.salt.setWidth 64) P.sl = Spec.Rsa.bytesAt σ.mem (P.salt.setWidth 64) P.sl :=
    hc.st.ro (R := P.SALT) (by simp)
  show s.mem (P.salt.setWidth 64 + BitVec.ofNat 64 i) = (Spec.Rsa.bytesAt σ.mem (P.salt.setWidth 64) P.sl).getD i 0
  rw [← e, RsaPkcs1Sig.bytesAt_getD hi]

/-- The arguments of `sign`. -/
theorem sg_arg {j : Nat} (hj : j < 24) {P : EP} : j < ((P.lay h.D).argv).length := by simp; omega_using [hj]

/-- The salt after the digest. -/
theorem salt_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun σ s => E0 h P σ s ∧ Y1 h P σ s.mem)
      (.seq (.block (cpSalt h.H)) (.ite .e (.block []) Impl.Bignum.X86.copyBytes))
      (fun σ s => E0 h P σ s ∧ Y2 h P σ s.mem) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  obtain hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega_arith
  have eD : h.H.D = h.D := rfl
  have hK := hi₀.k1024
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.1.2.2.1
  obtain hsl : P.sl + h.D + 2 ≤ P.K := by have := hf.2; omega_using [this]
  refine VP.seq (G := fun σ s => (E0 h P σ s ∧ Y1 h P σ s.mem) ∧
      s.gpr .ebx = P.scr + BitVec.ofNat 32 (oY + 8 + h.D) ∧
      s.gpr .esi = P.salt ∧ s.gpr .ecx = BitVec.ofNat 32 P.sl ∧ s.zf = some (decide (P.sl = 0)))
    (VP.taint [.esp, .ebp] h.certs.cpSalt (sp_bp fun _ _ h => h.1.1) fun σ s ⟨⟨hc, hk⟩, hy⟩ => ?_)
    (VP.ite (fun σ s h' => ⟨_, h'.2.2.2.2⟩) (fun _ _ _ _ h₁ h₂ => by simp only [eval, h₁.2.2.2.2, h₂.2.2.2.2])
      (VP.block_nil fun σ s ⟨⟨⟨⟨hc, hk⟩, hy⟩, _, _, _, z⟩, e⟩ => ⟨⟨hc, hk⟩, fun i hi => ?_⟩) ?_)
  · simp only [cpSalt, atS, ld, addi, List.cons_append, List.nil_append]
    refine hc.wp_arg hg (sg_arg h (j := 18) (by decide)) (by decide) (by decide) fun t1 c1 u1 =>
      wp_mov fun t2 u2 => wp_addi fun t3 u3 => ?_
    refine (((c1.upd u2 (by decide) (by decide)).upd u3 (by decide) (by decide))).wp_arg hg
      (sg_arg h (j := 19) (by decide)) (by decide) (by decide) fun t4 c4 u4 => wp_test fun t5 u5 z5 => WP.block_nil ?_
    obtain m5 : t5.mem = s.mem := by rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    refine ⟨⟨⟨c4.fupd u5, m5 ▸ hk⟩, m5 ▸ hy⟩, ?_, ?_, ?_, ?_⟩
    · rw [u5.gpr]; simp (disch := decide) only [u4.other, u3.gpr, u2.gpr, u1.other, hc.ebp]
    · rw [u5.gpr]; simp (disch := decide) only [u4.other, u3.other, u2.other, u1.gpr]; rfl
    · rw [u5.gpr, u4.gpr]; rfl
    · rw [z5, u4.gpr, BitVec.and_self]
      exact congrArg some (ofNat_beq_zero hi₀.sl32)
  · have h0 : P.sl = 0 := by
      simp only [eval, z, Option.some.injEq, decide_eq_true_eq] at e; exact e
    rw [hy i hi]
    simp [Mp, saltB, h0, Spec.Rsa.bytesAt]
  · by_cases h0 : P.sl = 0
    · exact VP.empty fun σ s ⟨⟨_, _, _, _, z⟩, e⟩ => by
        simp only [eval, z, decide_eq_true h0] at e; exact absurd e (by decide)
    refine (copy_vp (hg.wbuf (o := oY + 8 + h.D) (n := P.sl) (by pomega_arith) (by omega_using [h0]))
      (salt_buf h ⟨σ₀, hi₀⟩) (by rw [hg.scrA (by pomega_arith)]; exact (hg.ro ok (by pomega_arith) (R := P.SALT)
        (by simp)).symm) (by omega_using [h0]) (f := fun σ i => (saltB P σ).getD i 0)
      (Inv := fun σ m => Kp h P σ m ∧ (∀ i < 8 + h.D, m (sa P.scr (oY + i)) =
        (Spec.RsaPss.zeros 8 ++ digB h P σ).getD i 0) ∧ YZ P.scr (8 + h.D + P.sl) m) fun σ m m' ⟨hk, h1, h2⟩ hf => ?_).mono
      (fun σ s ⟨⟨⟨⟨hc, hk⟩, hy⟩, bx, si, cx, _⟩, _⟩ => ⟨hc, ⟨hk, fun i hi => hy i (by omega_using [hD, hi]), fun i hi => ?_⟩, bx, si,
        cx, fun i hi => salt_at h hc hi⟩) fun σ s ⟨hc, ⟨hk, h1, h2⟩, hs⟩ => ⟨⟨hc, hk⟩, fun i hi => ?_⟩
    · rw [hg.scrA (by pomega_arith)] at hf
      refine ⟨hk.keep h hf fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact away3_scr hg (by pomega_arith),
        sbytes_keep hf (fun r hr => ?_) (by pomega_arith) h1, sbytes_keep hf (fun r hr => ?_) (by pomega_arith) h2⟩
      · simp only [List.mem_singleton] at hr; subst hr; exact Geo.sep (by pomega_arith) (by pomega_arith) (by pomega_arith)
      · simp only [List.mem_singleton] at hr; subst hr; exact Geo.sep (by pomega_arith) (by pomega_arith) (by pomega_arith)
    · rw [show oY + (8 + h.D + P.sl) + i = oY + (8 + h.D + P.sl + i) by omega_using [], hy _ (by omega_using [hi]),
        getD_ge (by simp only [List.length_append, RsaPss.zeros_length, digB, RsaPkcs1Sig.bytesAt_len]; omega_using [])]
    · have hl : (Spec.RsaPss.zeros 8 ++ digB h P σ).length = 8 + h.D := by
        simp only [List.length_append, RsaPss.zeros_length, digB, RsaPkcs1Sig.bytesAt_len]
      rw [RsaPss.getD_app, hl]
      by_cases e1 : i < 8 + h.D
      · rw [ite_eq_left e1]; exact h1 i e1
      rw [ite_eq_right e1]
      by_cases e2 : i < 8 + h.D + P.sl
      · rw [← hs (i - (8 + h.D)) (by omega_using [h0, e2]), hg.byteAt_scr (by pomega_arith),
          show oY + 8 + h.D + (i - (8 + h.D)) = oY + i by omega_using [e1]]
      · rw [getD_ge (l := saltB P σ) (by rw [RsaPkcs1Sig.bytesAt_len]; omega_using [e2]),
          show oY + i = oY + (8 + h.D + P.sl) + (i - (8 + h.D + P.sl)) by omega_using [e2]]
        exact h2 _ (by omega_using [hi, e2])

/-- `M'`'s blocks. -/
abbrev nbS (P : EP) : Nat := (P.sl + (8 + h.D) + h.L) / h.B + 1

/-- What `ctHash` keeps, with `M'`'s length and blocks in their slots. -/
abbrev Kh (P : EP) (σ : State) (m : Mem) : Prop :=
  Kp h P σ m ∧ m.readW ((P.lay h.D).fr sL) 32 = BitVec.ofNat 32 (Mp h P σ).length ∧
    m.readW ((P.lay h.D).fr sNb) 32 = BitVec.ofNat 32 (nbS h P)

theorem Mp_length (P : EP) (σ : State) : (Mp h P σ).length = P.sl + (8 + h.D) := by
  simp only [Mp, List.length_append, RsaPss.zeros_length, digB, saltB, RsaPkcs1Sig.bytesAt_len]; omega_using []

/-- `M'`'s length and blocks. -/
theorem lenSet_vp (P : EP) :
    VP (fun σ s => E0 h P σ s ∧ Y2 h P σ s.mem) (.block (lenArgs h.H 19))
      (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Kh h P σ s.mem ∧ Y2 h P σ s.mem) := by
  refine VP.taint [.esp, .ebp] h.certs.lenArgs19 (sp_bp fun _ _ h => h.1.1) fun σ s ⟨⟨hc, hk⟩, hy⟩ => ?_
  have hg := hk.1.geo
  obtain hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega_arith
  have hL := h.L_le
  have hB := h.B_ge
  have hsl := hk.1.sl32
  obtain hsl2 : P.sl + h.D + 2 ≤ P.K := by have := hk.2.1.2; omega_using [this]
  have hK := hk.1.k1024
  obtain e1 : BitVec.ofNat 32 (P.sl + (8 + h.D) + h.L) >>> lgB h.H =
      BitVec.ofNat 32 ((P.sl + (8 + h.D) + h.L) / h.B) := by
    rw [ofNat_shr (by omega_using [hL, hsl2, hK]), h.pow_lg]
  obtain ⟨σ', ok⟩ := hg.ok
  simp only [lenArgs, ld, st, addi]
  refine hc.wp_arg hg (sg_arg h (j := 19) (by decide)) (by decide) (by decide) fun t1 c1 u1 =>
    wp_addi fun t2 u2 => (c1.upd u2 (by decide) (by decide)).wp_st hg (by decide) fun t3 c3 u3 =>
      wp_addi fun t4 u4 => wp_shr h.lg_range fun t5 u5 _ => wp_addi fun t6 u6 => ?_
  refine ((((c3.upd u4 (by decide) (by decide)).upd u5 (by decide) (by decide)).upd u6 (by decide)
    (by decide))).wp_st hg (by decide) fun t7 c7 u7 => WP.block_nil ?_
  obtain e2 : t2.gpr .eax = BitVec.ofNat 32 (P.sl + (8 + h.D)) := by
    rw [u2.gpr, u1.gpr]; exact BitVec.ofNat_add_ofNat ..
  obtain e6 : t6.gpr .eax = BitVec.ofNat 32 (nbS h P) := by
    rw [u6.gpr, u5.gpr, u4.gpr, u3.gpr, e2, BitVec.ofNat_add_ofNat]
    show BitVec.ofNat 32 (P.sl + (8 + h.D) + h.L) >>> lgB h.H + _ = _
    rw [e1, BitVec.ofNat_add_ofNat]
  obtain m7 : t7.mem = (s.mem.writeW ((P.lay h.D).fr sL) (BitVec.ofNat 32 (P.sl + (8 + h.D)))).writeW
      ((P.lay h.D).fr sNb) (BitVec.ofNat 32 (nbS h P)) := by
    rw [u7.mem, e6, u6.mem, u5.mem, u4.mem, u3.mem, e2, u2.mem, u1.mem]
  obtain fr : Frame [slotR (P.lay h.D) sL, slotR (P.lay h.D) sNb] s.mem t7.mem := by
    rw [m7]
    exact (slot_frame _ _ _ _).mono (by simp) |>.trans ((slot_frame _ _ _ _).mono (by simp))
  refine ⟨c7, ⟨hk.keep h fr fun r hr => ?_, ?_, ?_⟩, sbytes_keep fr (fun r hr => ?_) (by pomega_arith) hy⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact away3_slot (by decide) (by decide)
  · rw [m7, Lay.readW_fr_other (d := sL) (e := sNb) _ _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32, Mp_length]
  · rw [m7, Mem.readW_writeW_self32]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hg.slot ok (by pomega_arith) (by rw [hg.F]; decide)).symm
    · exact (hg.slot ok (by pomega_arith) (by rw [hg.F]; decide)).symm

/-- `ctHashT`'s writes miss the parameters' slots. -/
theorem away3_ctWT {L : Lay} {scr : BitVec 32} (hg : Geo L scr) {T : Nat} (hT : T ≤ 2048) :
    ∀ r ∈ ctWT h L scr T, Away3 L r := fun r hr => by
  rcases List.mem_cons.mp hr with rfl | hr
  · exact away3_slot (by decide) (.inr (by decide))
  · exact away3_ctW h hg hT r hr

/-- `H = Hash(M')`, at `oDig`, with the hash function of the table at the
argument 22. -/
theorem hash_vp (P : EP) (hP : ∃ σ, In h.D P σ) {dn : String} {f : MdFns}
    (hTH : ∀ σ, P.TH σ → HFacts h dn f P.tabH P.hai P.hac P.had σ)
    (fne : f.init ≠ [] ∧ f.comp ≠ [] ∧ f.dig ≠ []) :
    VP (fun σ s => (Ctx (P.lay h.D) P.scr σ s ∧ Kh h P σ s.mem ∧ Y2 h P σ s.mem) ∧ s.syms = σ.syms)
      (ctHashT f h.H 22)
      (fun σ s => (E0 h P σ s ∧ Dg h P.scr (Mp h P σ) s.mem) ∧ s.syms = σ.syms) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.1.2.1.1.2.1
  obtain hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega_arith
  have hL := h.L_le
  have hB := h.B_le
  obtain hB0 : 0 < h.B := by have := h.B_ge; omega_using [this]
  obtain hsl2 : P.sl + h.D + 2 ≤ P.K := by have := hf.2; omega_using [this]
  have hK := hi₀.k1024
  obtain q1 := Nat.lt_mul_div_succ (P.sl + (8 + h.D) + h.L) hB0
  obtain q2 := Nat.mul_div_le (P.sl + (8 + h.D) + h.L) h.B
  obtain hT : nbS h P * h.B ≤ 2048 := by
    show ((P.sl + (8 + h.D) + h.L) / h.B + 1) * h.B ≤ 2048
    rw [Nat.succ_mul, Nat.mul_comm]; omega_using [hL, hB, hsl2, hK, q2]
  obtain dT : ∀ d, d = sL ∨ d = sNb → ∀ r ∈ ctWT h (P.lay h.D) P.scr (nbS h P * h.B), (slotR (P.lay h.D) d).Disjoint r := by
    intro d hd r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · rcases hd with rfl | rfl <;> exact Lay.fr_sep (by decide) (by decide) (by decide)
    · rcases hd with rfl | rfl <;> exact ctW_slot h hg hT (by decide) (by decide) (by decide) r hr
  refine (ctHashT_vp h hg (nbm := nbS h P) hT (Nat.succ_pos _) (msg := Mp h P) (fun σ => by
      rw [Mp_length]; show _ ≤ ((P.sl + (8 + h.D) + h.L) / h.B + 1) * h.B; rw [Nat.mul_comm]; omega_using [q1])
    (Inv := Kh h P) (fun σ m m' hk hf' => ⟨hk.1.keep h hf' (away3_ctWT h hg hT), slot_keep hf'
      (dT sL (.inl rfl)) hk.2.1, slot_keep hf' (dT sNb (.inr rfl)) hk.2.2⟩)
    (fun σ m hk => hk.2.1) (fun σ m hk => hk.2.2) ⟨h.certs.digSp, h.certs.digCt⟩ (sg_arg h (j := 22) (by decide))
    hTab22_taint (fun σ m hk => hTH σ hk.1.1.tabTH) hi₀.tblH fne).mono
    (fun σ s ⟨⟨hc, hk, hy⟩, sy⟩ => ⟨⟨hc, hk, fun i hi => hy i (by omega_using [hT, hi])⟩, sy⟩)
    fun σ s ⟨⟨hc, hk, hd⟩, sy⟩ => ⟨⟨⟨hc, hk.1⟩, hd⟩, sy⟩

end VG.Proof.RsaPss.X86.Sg

end

end


/-!
# RSASSA-PSS signing on x86: `EM`

`EM` cleared (`clr_vp`), then `0x01` and the salt at the end of
`DB = EM[lo..lo + dbLen)` (`one_vp`, `cpS_vp`), `H` after it (`putH_vp`)
and `0xbc` last (`bc_vp`), as on ARMv7.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Sg

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes

variable (h : PssHash)

theorem add_ofNat_sub {x : BitVec 32} {a b : Nat} (hb : b ≤ a) :
    x + BitVec.ofNat 32 a - BitVec.ofNat 32 b = x + BitVec.ofNat 32 (a - b) := by
  have : BitVec.ofNat 32 a = BitVec.ofNat 32 (a - b) + BitVec.ofNat 32 b := by
    rw [BitVec.ofNat_add_ofNat, Nat.sub_add_cancel hb]
  rw [this, ← BitVec.add_assoc, BitVec.add_sub_cancel]

/-- `H`. -/
abbrev Hs (P : EP) (σ : State) : List Byte := h.ok.hH.SH.H.hash (Mp h P σ)

/-- What the rest of the encoding keeps. -/
abbrev Ke (P : EP) (σ : State) (m : Mem) : Prop := Kp h P σ m ∧ Dg h P.scr (Mp h P σ) m

/-- After `H`. -/
abbrev E4 (P : EP) (σ s : State) : Prop := E0 h P σ s ∧ Dg h P.scr (Mp h P σ) s.mem

/-- `EM`'s `k` bytes. -/
abbrev EMv (P : EP) (m : Mem) (f : Nat → Byte) : Prop := ∀ i < P.K, m (sa P.scr (oEm + i)) = f i

/-- `DB`'s byte `j`: zeros, `0x01`, then the salt. -/
abbrev dbv (P : EP) (σ : State) (j : Nat) : Byte :=
  if j < dbN h P - P.sl - 1 then 0 else if j = dbN h P - P.sl - 1 then 1 else (saltB P σ).getD (j - (dbN h P - P.sl)) 0

/-- `EM` after `0x01`, after the salt, after `H` and after `0xbc`. -/
abbrev emP (P : EP) (i : Nat) : Byte := if i = lo P + dbN h P - P.sl - 1 then 1 else 0
abbrev emA (P : EP) (σ : State) (i : Nat) : Byte :=
  if i < lo P then 0 else if i < lo P + dbN h P then dbv h P σ (i - lo P) else 0
abbrev emB (P : EP) (σ : State) (i : Nat) : Byte :=
  if i < lo P + dbN h P then emA h P σ i else if i < lo P + dbN h P + h.D then (Hs h P σ).getD (i - lo P - dbN h P) 0
    else 0
abbrev emC (P : EP) (σ : State) (i : Nat) : Byte := if i = P.K - 1 then 0xbc else emB h P σ i

theorem Ke.keep {P : EP} {σ : State} {m m' : Mem} {o n : Nat} (hg : Geo (P.lay h.D) P.scr) (hk : Ke h P σ m)
    (hf : Frame [sR P.scr o n] m m') (ho : oEm ≤ o) (hn : o + n ≤ oY) : Ke h P σ m' := by
  have := h.D_le
  have := h.N_le
  exact ⟨hk.1.keep h hf fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact away3_scr hg (by pomega_arith),
    sbytes_keep hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Geo.sep (by pomega_arith) (by pomega_arith) (by pomega_arith))
      (by pomega_arith) hk.2⟩

/-- `EM` cleared. -/
theorem clr_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (E4 h P) (.seq (.block clrEm) zeroLoop)
      (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧ EMv P s.mem fun _ => 0) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  have hK := hi₀.k1024
  have hK0 := hi₀.k64
  refine VP.seq (G := fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧
      s.gpr .esi = P.scr + BitVec.ofNat 32 oEm ∧ s.gpr .ecx = BitVec.ofNat 32 P.K ∧ s.gpr .eax = 0)
    (VP.taint [.esp, .ebp] clrEm_taint (sp_bp fun _ _ h => h.1.1) fun σ s ⟨⟨hc, hk⟩, hd⟩ => ?_)
    ((zero_vp (hg.wbuf (o := oEm) (n := P.K) (by pomega_arith) (by omega_using [hK0])) (by omega_using [hK0]) (Inv := Ke h P)
      fun σ m m' hk hf => hk.keep h hg (by rwa [hg.scrA (by pomega_arith)] at hf) (Nat.le_refl _) (by pomega_arith)).mono
      (fun _ _ h => h) fun σ s ⟨hc, hk, hz⟩ => ⟨hc, hk, fun i hi => by rw [← hg.byteAt_scr (by pomega_arith)]; exact hz i hi⟩)
  simp only [clrEm, atS, ld, mi, addi, List.cons_append, List.nil_append]
  refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
  refine ((hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)).wp_arg hg
    (sg_arg h (j := 3) (by decide)) (by decide) (by decide) fun t3 c3 u3 => wp_movi fun t4 u4 => WP.block_nil ?_
  refine ⟨c3.upd u4 (by decide) (by decide), by rw [u4.mem, u3.mem, u2.mem, u1.mem]; exact ⟨hk, hd⟩, ?_, ?_, ?_⟩
  · simp (disch := decide) only [u4.other, u3.other, u2.gpr, u1.gpr, hc.ebp]
  · rw [u4.other _ (by decide), u3.gpr]; rfl
  · rw [u4.gpr]; rfl

/-- `0x01` before the salt's place at the end of `DB`. -/
theorem one_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧ EMv P s.mem fun _ => 0)
      (.seq (.block oneSet) (.block put1))
      (fun σ s => (Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧ EMv P s.mem (emP h P)) ∧
        s.gpr .ebx = P.scr + BitVec.ofNat 32 (oEm + lo P + dbN h P - P.sl) ∧ s.gpr .esi = P.salt ∧
        s.gpr .ecx = BitVec.ofNat 32 P.sl ∧ s.zf = some (decide (P.sl = 0))) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.2.1.1.2.1
  obtain hsl2 : P.sl + h.D + 2 ≤ P.K := by have := hf.2; omega_using [this]
  have hK := hi₀.k1024
  obtain hlo : lo P ≤ 1 := by unfold lo; split <;> omega_using []
  obtain hdb : P.sl + 1 ≤ dbN h P := by unfold dbN; omega
  obtain hsum : lo P + dbN h P + h.D + 1 = P.K := by unfold dbN; omega_using [hsl2, hlo]
  obtain hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega_arith
  have e1 : oEm = 1024 := rfl
  have e2 : oRsa = 8192 := rfl
  have e3 : oY = 2048 := rfl
  have fit := hg.fit
  refine VP.seq (G := fun σ s => (Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧ EMv P s.mem fun _ => 0) ∧
      s.gpr .ebx = P.scr + BitVec.ofNat 32 (oEm + lo P + dbN h P - P.sl - 1))
    (VP.taint [.esp, .ebp] oneSet_taint (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hk, he⟩ => ?_)
    (VP.taint _ put1_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s ⟨⟨hc, hk, he⟩, bx⟩ => ?_)
  · simp only [oneSet, atDb, atS, addSlot, addi, Impl.RsaPkcs1Sig.X86.stk, List.cons_append, List.nil_append]
    refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
    obtain c2 : Ctx (P.lay h.D) P.scr σ t2 := (hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)
    refine wp_addm (B := (P.lay h.D).B) (by rw [c2.st.sp]) (by rw [hg.aFr ok sLo (by decide)]; exact c2.rFr hg sLo (by decide)) fun t3 u3 => ?_
    obtain c3 : Ctx (P.lay h.D) P.scr σ t3 := c2.upd u3 (by decide) (by decide)
    refine wp_addm (B := (P.lay h.D).B) (by rw [c3.st.sp]) (by rw [hg.aFr ok sDb (by decide)]; exact c3.rFr hg sDb (by decide)) fun t4 u4 => ?_
    obtain c4 : Ctx (P.lay h.D) P.scr σ t4 := c3.upd u4 (by decide) (by decide)
    refine wp_subm (B := (P.lay h.D).B) (by rw [c4.st.sp]) (by rw [hg.aArg ok 19 (by simp)]; exact
      (by rw [c4.st.rd, c4.st.wr]; exact c4.st.ok.arg_read (sg_arg h (by decide)))) fun t5 u5 => ?_
    refine wp_subi fun t6 u6 _ _ => WP.block_nil ?_
    obtain m6 : t6.mem = s.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    refine ⟨⟨((c4.upd u5 (by decide) (by decide)).upd u6 (by decide) (by decide)), m6 ▸ hk, m6 ▸ he⟩, ?_⟩
    obtain a18 : t4.mem.readW (addr (P.lay h.D).B (Impl.RsaPkcs1Sig.X86.argOff frameBytes 19)) 32 =
        BitVec.ofNat 32 P.sl := by
      rw [hg.aArg ok 19 (by simp), u4.mem, u3.mem, u2.mem, u1.mem, hc.st.arg (sg_arg h (by decide))]; rfl
    rw [u6.gpr, u5.gpr, a18, u4.gpr, u3.gpr, u2.gpr, u1.gpr, u3.mem, u2.mem, u1.mem, hc.ebp,
      hg.aFr ok sLo (by decide), hg.aFr ok sDb (by decide), hk.1.2.2.2.1, hk.1.2.2.2.2, BitVec.add_assoc,
      BitVec.add_assoc, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat, ← Nat.add_assoc,
      add_ofNat_sub (by omega_using [hdb]), show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, add_ofNat_sub (by omega_using [hdb])]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.1.1.st.sp, h₂.1.1.st.sp]
    · rw [h₁.2, h₂.2]
  · have ad : addr (P.scr + BitVec.ofNat 32 (oEm + lo P + dbN h P - P.sl - 1)) 0 =
        sa P.scr (oEm + lo P + dbN h P - P.sl - 1) := by rw [hg.addrD (by omega_using [hK, hsum, e1, e2]), Nat.add_zero]
    obtain wd : InRegions s.wr (sa P.scr (oEm + lo P + dbN h P - P.sl - 1)) 1 := hg.wr hc.st (by omega_using [hK, hsum,
        e1, e2])
    simp only [put1, mi, ld, addi, Impl.RsaPkcs1Sig.X86.at_]
    refine wp_movi fun t1 u1 => wp_store8 (a := sa P.scr (oEm + lo P + dbN h P - P.sl - 1))
      (by rw [ea_at, u1.other _ (by decide), bx]; exact ad) (by rw [u1.wr]; exact wd) fun t2 u2 => ?_
    obtain m2 : t2.mem = s.mem.writeW (sa P.scr (oEm + lo P + dbN h P - P.sl - 1)) (1 : Byte) := by
      rw [u2.mem, Reg8.reg, u1.gpr, u1.mem]; rfl
    obtain fr : Frame [sR P.scr (oEm + lo P + dbN h P - P.sl - 1) 1] s.mem t2.mem := by
      rw [m2]; exact frame_byte P.scr _ _ (Nat.le_refl _) (by omega_using []) (by omega_using [hK, hsum, e1])
    obtain c2 : Ctx (P.lay h.D) P.scr σ t2 := (hc.upd u1 (by decide) (by decide)).write
      (by rw [u1.mem]; exact fr) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hg.inW (by omega_using [hK, hsum, e1, e2]))
      u2.rd u2.wr (by rw [u2.gpr]) (by rw [u2.gpr])
    refine wp_addi fun t3 u3 => ?_
    obtain c3 : Ctx (P.lay h.D) P.scr σ t3 := c2.upd u3 (by decide) (by decide)
    refine c3.wp_arg hg (sg_arg h (j := 18) (by decide)) (by decide) (by decide) fun t4 c4 u4 =>
      c4.wp_arg hg (sg_arg h (j := 19) (by decide)) (by decide) (by decide) fun t5 c5 u5 =>
        wp_test fun t6 u6 z6 => WP.block_nil ?_
    obtain m6 : t6.mem = t2.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem]
    refine ⟨⟨c5.fupd u6, ?_, fun i hi => ?_⟩, ?_, ?_, ?_, ?_⟩
    · rw [m6]; exact hk.keep h hg fr (by omega_using [hdb]) (by omega_using [hK, hsum, e1, e3])
    · rw [m6, m2, sa_write P.scr _ _ (by omega_using [hK, hsum, e1]) (by omega_using [hK, e1, hi]), he i hi]
      by_cases e : i = lo P + dbN h P - P.sl - 1
      · rw [ite_eq_left (by omega_using [hdb, e])]; exact (ite_eq_left e).symm
      · rw [ite_eq_right (by omega_using [e1, e])]; exact (ite_eq_right e).symm
    · rw [u6.gpr]
      simp (disch := decide) only [u5.other, u4.other, u3.gpr, u2.gpr, u1.other, bx]
      rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, show oEm + lo P + dbN h P - P.sl - 1 + 1 =
        oEm + lo P + dbN h P - P.sl by omega_using [hdb]]
    · rw [u6.gpr]; simp (disch := decide) only [u5.other, u4.gpr]; rfl
    · rw [u6.gpr, u5.gpr]; rfl
    · rw [z6, u5.gpr, BitVec.and_self]
      exact congrArg some (ofNat_beq_zero hi₀.sl32)

/-- `EM` after the salt, from `EM` after `0x01`. -/
theorem emA_eq {P : EP} {σ : State} (hlo : lo P ≤ 1) (hdb : P.sl + 1 ≤ dbN h P) (i : Nat) :
    emA h P σ i = if lo P + dbN h P - P.sl ≤ i ∧ i < lo P + dbN h P then
      (saltB P σ).getD (i - (lo P + dbN h P - P.sl)) 0 else emP h P i := by
  unfold emA dbv emP
  by_cases h1 : i < lo P
  · rw [ite_eq_left h1, ite_eq_right (by omega_arith), ite_eq_right (by omega_arith)]
  rw [ite_eq_right h1]
  by_cases h2 : i < lo P + dbN h P
  · rw [ite_eq_left h2]
    by_cases h3 : i - lo P < dbN h P - P.sl - 1
    · rw [ite_eq_left h3, ite_eq_right (by omega_arith), ite_eq_right (by omega_arith)]
    rw [ite_eq_right h3]
    by_cases h4 : i - lo P = dbN h P - P.sl - 1
    · rw [ite_eq_left h4, ite_eq_right (by omega_arith), ite_eq_left (by omega_arith)]
    · rw [ite_eq_right h4, ite_eq_left (by omega_arith), show i - lo P - (dbN h P - P.sl) = i - (lo P + dbN h P - P.sl) by omega_arith]
  · rw [ite_eq_right h2, ite_eq_right (by omega_arith), ite_eq_right (by omega_arith)]

/-- The salt at the end of `DB`. -/
theorem cpS_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun σ s => (Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧ EMv P s.mem (emP h P)) ∧
        s.gpr .ebx = P.scr + BitVec.ofNat 32 (oEm + lo P + dbN h P - P.sl) ∧ s.gpr .esi = P.salt ∧
        s.gpr .ecx = BitVec.ofNat 32 P.sl ∧ s.zf = some (decide (P.sl = 0)))
      (.ite .e (.block []) Impl.Bignum.X86.copyBytes)
      (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧ EMv P s.mem (emA h P σ)) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.1.2.1.1.2.1
  have hK := hi₀.k1024
  obtain hlo : lo P ≤ 1 := by unfold lo; split <;> omega_using []
  obtain hdb : P.sl + 1 ≤ dbN h P := by unfold dbN; have := hf.2; omega_using [this]
  obtain hsum : lo P + dbN h P + h.D + 1 = P.K := by unfold dbN; have := hf.2; omega_using [this]
  have e1 : oEm = 1024 := rfl
  have e2 : oRsa = 8192 := rfl
  have e3 : oY = 2048 := rfl
  have fit := hg.fit
  refine VP.ite (fun σ s h' => ⟨_, h'.2.2.2.2⟩) (fun _ _ _ _ h₁ h₂ => by simp only [eval, h₁.2.2.2.2, h₂.2.2.2.2])
    (VP.block_nil fun σ s ⟨⟨⟨hc, hk, he⟩, _, _, _, z⟩, e⟩ => ⟨hc, hk, fun i hi => ?_⟩) ?_
  · have h0 : P.sl = 0 := by simp only [eval, z, Option.some.injEq, decide_eq_true_eq] at e; exact e
    rw [he i hi, emA_eq h hlo hdb, ite_eq_right (by omega_using [h0])]
  by_cases h0 : P.sl = 0
  · exact VP.empty fun σ s ⟨⟨_, _, _, _, z⟩, e⟩ => by
      simp only [eval, z, decide_eq_true h0] at e; exact absurd e (by decide)
  refine (copy_vp (hg.wbuf (o := oEm + lo P + dbN h P - P.sl) (n := P.sl) (by omega_using [hK, hdb, hsum, e1,
      e2]) (by omega_using [h0]))
    (salt_buf h ⟨σ₀, hi₀⟩) (by rw [hg.scrA (by omega_using [hK, hsum, e1, e2])]; exact (hg.ro ok (by omega_using [hK,
        hdb, hsum, e1, e2]) (R := P.SALT) (by simp)).symm)
    (by omega_using [h0]) (f := fun σ i => (saltB P σ).getD i 0)
    (Inv := fun σ m => Ke h P σ m ∧ ∀ i < P.K, (i < lo P + dbN h P - P.sl ∨ lo P + dbN h P ≤ i) →
      m (sa P.scr (oEm + i)) = emP h P i) fun σ m m' ⟨hk, ho⟩ hf' => ?_).mono
    (fun σ s ⟨⟨⟨hc, hk, he⟩, bx, si, cx, _⟩, _⟩ => ⟨hc, ⟨hk, fun i hi _ => he i hi⟩, bx, si, cx,
      fun i hi => salt_at h hc hi⟩) fun σ s ⟨hc, ⟨hk, ho⟩, hs⟩ => ⟨hc, hk, fun i hi => ?_⟩
  · rw [hg.scrA (by omega_using [hK, hsum, e1, e2])] at hf'
    refine ⟨hk.keep h hg hf' (by omega_using [hdb]) (by omega_using [hK, hdb, hsum, e1, e3]), fun i hi hr => ?_⟩
    rw [← ho i hi hr]
    exact hf' _ fun r hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact Geo.sep (scr := P.scr) (o := oEm + i) (n := 1) (by omega_using [hdb, hr]) (by omega_using [hK, e1, e2,
          hi]) (by omega_using [hK, hdb, hsum, e1, e2]) _ (Region.contains_self _ _)
  · rw [emA_eq h hlo hdb]
    by_cases hr : lo P + dbN h P - P.sl ≤ i ∧ i < lo P + dbN h P
    · rw [ite_eq_left hr, ← hs (i - (lo P + dbN h P - P.sl)) (by omega_using [hr]), hg.byteAt_scr (by omega_using [hK,
        hsum, e1, e2, hi]),
        show oEm + lo P + dbN h P - P.sl + (i - (lo P + dbN h P - P.sl)) = oEm + i by omega_using [hdb, hr]]
    · rw [ite_eq_right hr]; exact ho i hi (by omega_using [hr])

/-- `H` after `DB`. -/
theorem putH_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧ EMv P s.mem (emA h P σ))
      (.seq (.block (putH h.H)) Impl.Bignum.X86.copyBytes)
      (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧ EMv P s.mem (emB h P σ)) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.2.1.1.2.1
  have hK := hi₀.k1024
  obtain hlo : lo P ≤ 1 := by unfold lo; split <;> omega_using []
  obtain hdb : P.sl + 1 ≤ dbN h P := by unfold dbN; have := hf.2; omega_using [this]
  obtain hsum : lo P + dbN h P + h.D + 1 = P.K := by unfold dbN; have := hf.2; omega_using [this]
  obtain hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega_arith
  have hD0 := h.D_pos
  have e1 : oEm = 1024 := rfl
  have e2 : oRsa = 8192 := rfl
  have e3 : oY = 2048 := rfl
  have e4 : oDig = 832 := rfl
  have fit := hg.fit
  refine VP.seq (G := fun σ s => (Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧ EMv P s.mem (emA h P σ)) ∧
      s.gpr .ebx = P.scr + BitVec.ofNat 32 (oEm + lo P + dbN h P) ∧ s.gpr .esi = P.scr + BitVec.ofNat 32 oDig ∧
      s.gpr .ecx = BitVec.ofNat 32 h.D)
    (VP.taint [.esp, .ebp] h.certs.putH (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hk, he⟩ => ?_)
    ((copy_vp (hg.wbuf (o := oEm + lo P + dbN h P) (n := h.D) (by omega_using [hK, hsum, e1, e2]) hD0)
      (hg.rbuf (o := oDig) (n := h.D) (by omega_using [hK, hsum, e2, e4]) hD0)
      (by rw [hg.scrA (by omega_using [e2, e4]), hg.scrA (by omega_using [hK, hsum, e1,
          e2])]; exact Geo.sep (by omega_using [hD, e1, e4]) (by omega_using [hK, hsum, e2, e4]) (by omega_using [hK,
          hsum, e1, e2])) hD0
      (f := fun σ i => (Hs h P σ).getD i 0)
      (Inv := fun σ m => Ke h P σ m ∧ ∀ i < P.K, (i < lo P + dbN h P ∨ lo P + dbN h P + h.D ≤ i) →
        m (sa P.scr (oEm + i)) = emA h P σ i) fun σ m m' ⟨hk, ho⟩ hf' => ?_).mono
      (fun σ s ⟨⟨hc, hk, he⟩, bx, si, cx⟩ => ⟨hc, ⟨hk, fun i hi _ => he i hi⟩, bx, si, cx, fun i hi => by
        rw [hg.byteAt_scr (by omega_using [hK, hsum, e2, e4,
            hi])]; exact hk.2 i hi⟩) fun σ s ⟨hc, ⟨hk, ho⟩, hs⟩ => ⟨hc, hk, fun i hi => ?_⟩)
  · simp only [putH, atDb, atS, addSlot, addi, mi, Impl.RsaPkcs1Sig.X86.stk, List.cons_append, List.nil_append]
    refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => wp_mov fun t3 u3 => wp_addi fun t4 u4 => ?_
    obtain c4 : Ctx (P.lay h.D) P.scr σ t4 := (((hc.upd u1 (by decide) (by decide)).upd u2 (by decide)
      (by decide)).upd u3 (by decide) (by decide)).upd u4 (by decide) (by decide)
    refine wp_addm (B := (P.lay h.D).B) (by rw [c4.st.sp]) (by rw [hg.aFr ok sLo (by decide)]; exact c4.rFr hg sLo (by decide)) fun t5 u5 => ?_
    obtain c5 : Ctx (P.lay h.D) P.scr σ t5 := c4.upd u5 (by decide) (by decide)
    refine wp_addm (B := (P.lay h.D).B) (by rw [c5.st.sp]) (by rw [hg.aFr ok sDb (by decide)]; exact c5.rFr hg sDb (by decide)) fun t6 u6 => wp_movi fun t7 u7 => WP.block_nil ?_
    obtain m7 : t7.mem = s.mem := by rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    refine ⟨⟨(c5.upd u6 (by decide) (by decide)).upd u7 (by decide) (by decide), m7 ▸ hk, m7 ▸ he⟩, ?_, ?_, ?_⟩
    · rw [u7.other _ (by decide), u6.gpr, u5.gpr, u4.gpr, u3.gpr, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem,
        u2.other _ (by decide), u1.other _ (by decide), hc.ebp, hg.aFr ok sLo (by decide), hg.aFr ok sDb (by decide),
        hk.1.2.2.2.1, hk.1.2.2.2.2, BitVec.add_assoc, BitVec.add_assoc, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat,
        ← Nat.add_assoc]
    · simp (disch := decide) only [u7.other, u6.other, u5.other, u4.other, u3.other, u2.gpr, u1.gpr, hc.ebp]
    · rw [u7.gpr]
  · rw [hg.scrA (by omega_using [hK, hsum, e1, e2])] at hf'
    refine ⟨hk.keep h hg hf' (by omega_using []) (by omega_using [hK, hsum, e1, e3]), fun i hi hr => ?_⟩
    rw [← ho i hi hr]
    exact hf' _ fun r hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact Geo.sep (scr := P.scr) (o := oEm + i) (n := 1) (by omega_using [hr]) (by omega_using [hK, e1, e2,
          hi]) (by omega_using [hK, hsum, e1, e2]) _ (Region.contains_self _ _)
  · unfold emB
    by_cases h1 : i < lo P + dbN h P
    · rw [ite_eq_left h1]; exact ho i hi (.inl h1)
    rw [ite_eq_right h1]
    by_cases h2 : i < lo P + dbN h P + h.D
    · rw [ite_eq_left h2, ← hs (i - lo P - dbN h P) (by omega_using [hD0, h2]), hg.byteAt_scr (by omega_using [hK, hsum,
        e1, e2, hi]),
        show oEm + lo P + dbN h P + (i - lo P - dbN h P) = oEm + i by omega_using [h1]]
    · rw [ite_eq_right h2, ho i hi (.inr (by omega_using [h2]))]
      unfold emA
      rw [ite_eq_right (by omega_using [h1]), ite_eq_right (by omega_using [h1])]

/-- `0xbc` last. -/
theorem bc_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧ EMv P s.mem (emB h P σ))
      (.seq (.block bcSet) (.block putBc))
      (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧ EMv P s.mem (emC h P σ)) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have hK := hi₀.k1024
  have hK0 := hi₀.k64
  have e1 : oEm = 1024 := rfl
  have e2 : oRsa = 8192 := rfl
  have e3 : oY = 2048 := rfl
  have fit := hg.fit
  refine VP.seq (G := fun σ s => (Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧ EMv P s.mem (emB h P σ)) ∧
      s.gpr .esi = P.scr + BitVec.ofNat 32 (oEm + P.K - 1))
    (VP.taint [.esp, .ebp] bcSet_taint (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hk, he⟩ => ?_)
    (VP.taint _ putBc_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s ⟨⟨hc, hk, he⟩, si⟩ => ?_)
  · simp only [bcSet, atS, addSlot, addi, Impl.RsaPkcs1Sig.X86.stk, List.cons_append, List.nil_append]
    refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
    obtain c2 : Ctx (P.lay h.D) P.scr σ t2 := (hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)
    refine wp_addm (B := (P.lay h.D).B) (by rw [c2.st.sp]) (by rw [hg.aArg ok 3 (by simp)]; exact
      (by rw [c2.st.rd, c2.st.wr]; exact c2.st.ok.arg_read (sg_arg h (by decide)))) fun t3 u3 => ?_
    refine wp_subi fun t4 u4 _ _ => WP.block_nil ?_
    obtain m4 : t4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
    refine ⟨⟨(c2.upd u3 (by decide) (by decide)).upd u4 (by decide) (by decide), m4 ▸ hk, m4 ▸ he⟩, ?_⟩
    rw [u4.gpr, u3.gpr, u2.gpr, u1.gpr, u2.mem, u1.mem, hc.ebp, hg.aArg ok 3 (by simp),
      hc.st.arg (sg_arg h (by decide)), show (P.lay h.D).argv.getD 3 0 = BitVec.ofNat 32 P.K from rfl,
      BitVec.add_assoc, BitVec.ofNat_add_ofNat, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      add_ofNat_sub (by omega_using [hK0])]
  · simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2]
  · have ad : addr (P.scr + BitVec.ofNat 32 (oEm + P.K - 1)) 0 = sa P.scr (oEm + P.K - 1) := by
      rw [hg.addrD (by omega_using [hK, e1, e2]), Nat.add_zero]
    obtain wd : InRegions s.wr (sa P.scr (oEm + P.K - 1)) 1 := hg.wr hc.st (by omega_using [hK, e1, e2])
    simp only [putBc, mi, Impl.RsaPkcs1Sig.X86.at_]
    refine wp_movi fun t1 u1 => wp_store8 (a := sa P.scr (oEm + P.K - 1))
      (by rw [ea_at, u1.other _ (by decide), si]; exact ad) (by rw [u1.wr]; exact wd) fun t2 u2 => WP.block_nil ?_
    obtain m2 : t2.mem = s.mem.writeW (sa P.scr (oEm + P.K - 1)) (0xbc : Byte) := by
      rw [u2.mem, Reg8.reg, u1.gpr, u1.mem]; rfl
    obtain fr : Frame [sR P.scr (oEm + P.K - 1) 1] s.mem t2.mem := by
      rw [m2]; exact frame_byte P.scr _ _ (Nat.le_refl _) (by omega_using []) (by omega_using [hK, e1])
    refine ⟨(hc.upd u1 (by decide) (by decide)).write (by rw [u1.mem]; exact fr) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hg.inW (by omega_using [hK, e1,
            e2])) u2.rd u2.wr (by rw [u2.gpr])
        (by rw [u2.gpr]), hk.keep h hg fr (by omega_using [hK0]) (by omega_using [hK, e1, e3]), fun i hi => ?_⟩
    rw [m2, sa_write P.scr _ _ (by omega_using [hK, e1]) (by omega_using [hK, e1, hi]), he i hi]
    by_cases e : i = P.K - 1
    · rw [ite_eq_left (by omega_using [hK0, e])]; exact (ite_eq_left e).symm
    · rw [ite_eq_right (by omega_using [e])]; exact (ite_eq_right e).symm

end VG.Proof.RsaPss.X86.Sg

end

end


/-!
# RSASSA-PSS signing on x86: `maskedDB`

`DB ⊕= MGF1(H, dbLen)` (`mask_vp`): MGF1's slots (`margs_vp`), then
RSAES-OAEP's MGF1 with the hash function `g` of the table `mgf1`
(`Proof.RsaOaep.X86.mgf_vp`); and `maskedDB`'s first byte ANDed with the
mask `c` (`top_vp`): `EM` is `emT` of the specification's encoding
(`EncBytes.lean`), and so is the whole encoding (`enc_vp`), whose stages
keep the addresses of the statics (`VP.syms`) for the indirect calls.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Sg

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes
open VG.Impl.RsaOaep.X86 (Fns sSrc sSrcLen sDst sDstLen sTab sHl)
open VG.Proof.RsaOaep.X86 (OHash TabFacts MP mpOf Sl VP.syms)

theorem slots4 {L : Lay} {scr : BitVec 32} {σ s t : State} (hc : Ctx L scr σ s) (hg : Geo L scr)
    {v1 v2 v3 v4 : BitVec 32}
    (m : t.mem = (((s.mem.writeW (L.fr sDst) v1).writeW (L.fr sDstLen) v2).writeW (L.fr sSrc) v3).writeW
      (L.fr sSrcLen) v4)
    (rd : t.rd = s.rd) (wr : t.wr = s.wr) (sp : t.gpr .esp = s.gpr .esp) (bp : t.gpr .ebp = s.gpr .ebp) :
    Ctx L scr σ t ∧ Frame [slotR L sDst, slotR L sDstLen, slotR L sSrc, slotR L sSrcLen] s.mem t.mem ∧
      t.mem.readW (L.fr sSrc) 32 = v3 ∧ t.mem.readW (L.fr sSrcLen) 32 = v4 ∧
      t.mem.readW (L.fr sDst) 32 = v1 ∧ t.mem.readW (L.fr sDstLen) 32 = v2 := by
  obtain fr : Frame [slotR L sDst, slotR L sDstLen, slotR L sSrc, slotR L sSrcLen] s.mem t.mem := by
    rw [m]
    exact (((slot_frame _ _ _ _).mono (by simp)).trans ((slot_frame _ _ _ _).mono (by simp))).trans
      ((slot_frame _ _ _ _).mono (by simp)) |>.trans ((slot_frame _ _ _ _).mono (by simp))
  refine ⟨hc.write fr (fun r hr => ?_) rd wr sp bp, fr, ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact slotW hg (by decide)
  · rw [m, Lay.readW_fr_other (d := sSrc) (e := sSrcLen) _ _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]
  · rw [m, Mem.readW_writeW_self32]
  · rw [m, Lay.readW_fr_other (d := sDst) (e := sSrcLen) _ _ _ (by decide) (by decide) (by decide),
      Lay.readW_fr_other (d := sDst) (e := sSrc) _ _ _ (by decide) (by decide) (by decide),
      Lay.readW_fr_other (d := sDst) (e := sDstLen) _ _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]
  · rw [m, Lay.readW_fr_other (d := sDstLen) (e := sSrcLen) _ _ _ (by decide) (by decide) (by decide),
      Lay.readW_fr_other (d := sDstLen) (e := sSrc) _ _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]

/-- The slots' frame misses our part of `scratch`. -/
theorem slots4_dis {L : Lay} {scr : BitVec 32} (hg : Geo L scr) :
    ∀ o n, o + n ≤ oRsa → ∀ r ∈ [slotR L sDst, slotR L sDstLen, slotR L sSrc, slotR L sSrcLen],
      (sR scr o n).Disjoint r := by
  obtain ⟨σ', ok⟩ := hg.ok
  intro o n hon r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact (hg.slot ok hon (by rw [hg.F]; decide)).symm

variable (h : PssHash)

/-- `EM`'s bytes outside `DB` and `H`: the leading zero and `0xbc`. -/
abbrev Ko (P : EP) (σ : State) (m : Mem) : Prop :=
  Kp h P σ m ∧ (∀ i < lo P, m (sa P.scr (oEm + i)) = 0) ∧ m (sa P.scr (oEm + (P.K - 1))) = 0xbc

/-- The mask, with MGF1's hash function `G`. -/
abbrev mkS (G : Spec.Mgf1.Hash) (P : EP) (σ : State) : List Byte := Spec.Mgf1.mgf1 G (Hs h P σ) (dbN h P)

theorem Hs_length (P : EP) (σ : State) : (Hs h P σ).length = h.D := by
  rw [Hs, ← h.hash]; have := (PssHash.valid h).2 (Mp h P σ); rw [this, h.glen]

/-- MGF1's slots: `H` its source, `DB` its destination. -/
abbrev Ms (P : EP) (m : Mem) : Prop :=
  Sl (P.lay h.D) P.scr (oEm + lo P + dbN h P) h.D (oEm + lo P) (dbN h P) m

/-- MGF1's slots, from those of the parameters; `DB` and `H` from `EM`. -/
theorem margs_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧ EMv P s.mem (emC h P σ)) (.block (mgfArgsT h.H))
      (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ (Ko h P σ s.mem ∧ Ms h P s.mem) ∧
        (∀ i < dbN h P, s.mem (sa P.scr (oEm + lo P + i)) = dbv h P σ i) ∧
        ∀ i < h.D, s.mem (sa P.scr (oEm + lo P + dbN h P + i)) = (Hs h P σ).getD i 0) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.2.1.1.2.1
  have hK := hi₀.k1024
  obtain hlo : lo P ≤ 1 := by unfold lo; split <;> omega_using []
  obtain hdb : P.sl + 1 ≤ dbN h P := by unfold dbN; have := hf.2; omega_using [this]
  obtain hsum : lo P + dbN h P + h.D + 1 = P.K := by unfold dbN; have := hf.2; omega_using [this]
  obtain hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega_arith
  have e1 : oEm = 1024 := rfl
  have e2 : oRsa = 8192 := rfl
  have fit := hg.fit
  refine VP.taint [.esp, .ebp] h.certs.mgfArgs (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hk, he⟩ => ?_
  simp only [mgfArgsT, atDb, atS, addSlot, addi, ld, st, mi, Impl.RsaPkcs1Sig.X86.stk, List.cons_append,
    List.nil_append]
  refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
  obtain c2 : Ctx (P.lay h.D) P.scr σ t2 := (hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)
  refine wp_addm (B := (P.lay h.D).B) (by rw [c2.st.sp])
    (by rw [hg.aFr ok sLo (by decide)]; exact c2.rFr hg sLo (by decide)) fun t3 u3 => ?_
  refine (c2.upd u3 (by decide) (by decide)).wp_st hg (by decide) fun t4 c4 m4 => ?_
  refine c4.wp_slot hg (by decide) (by decide) (by decide) fun t5 c5 u5 => ?_
  refine c5.wp_st hg (by decide) fun t6 c6 m6 => wp_add fun t7 u7 _ => ?_
  refine (c6.upd u7 (by decide) (by decide)).wp_st hg (by decide) fun t8 c8 m8 => wp_movi fun t9 u9 => ?_
  refine (c8.upd u9 (by decide) (by decide)).wp_st hg (by decide) fun t10 c10 m10 => WP.block_nil ?_
  obtain e3 : t3.gpr .eax = P.scr + BitVec.ofNat 32 (oEm + lo P) := by
    rw [u3.gpr, u2.gpr, u1.gpr, u2.mem, u1.mem, hc.ebp, hg.aFr ok sLo (by decide), hk.1.2.2.2.1, BitVec.add_assoc,
      BitVec.ofNat_add_ofNat]
  obtain e5 : t5.gpr .ecx = BitVec.ofNat 32 (dbN h P) := by
    rw [u5.gpr, m4.mem, Lay.readW_fr_other (d := sDb) (e := sDst) _ _ _ (by decide) (by decide) (by decide), u3.mem,
      u2.mem, u1.mem, hk.1.2.2.2.2]
  obtain e7 : t7.gpr .eax = P.scr + BitVec.ofNat 32 (oEm + lo P + dbN h P) := by
    rw [u7.gpr, m6.gpr, u5.other _ (by decide), m4.gpr, e3, e5, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  obtain m10 : t10.mem = (((s.mem.writeW ((P.lay h.D).fr sDst) (P.scr + BitVec.ofNat 32 (oEm + lo P))).writeW
      ((P.lay h.D).fr sDstLen) (BitVec.ofNat 32 (dbN h P))).writeW ((P.lay h.D).fr sSrc)
        (P.scr + BitVec.ofNat 32 (oEm + lo P + dbN h P))).writeW ((P.lay h.D).fr sSrcLen) (BitVec.ofNat 32 h.D) := by
    rw [m10.mem, u9.gpr, u9.mem, m8.mem, e7, u7.mem, m6.mem, e5, u5.mem, m4.mem, e3, u3.mem, u2.mem, u1.mem]
  obtain ⟨c, fr, r1, r2, r3, r4⟩ := slots4 hc hg m10 (by rw [c10.st.rd, hc.st.rd]) (by rw [c10.st.wr, hc.st.wr])
    (by rw [c10.st.sp, hc.st.sp]) (by rw [c10.ebp, hc.ebp])
  obtain dis := slots4_dis hg
  obtain kp := hk.1.keep h fr fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact away3_slot (by decide) (.inr (by decide))
  obtain he' : ∀ i < P.K, t10.mem (sa P.scr (oEm + i)) = emC h P σ i := fun i hi =>
    by rw [sbytes_keep (o := oEm) (n := P.K) fr (dis _ _ (by omega_using [hK, e1, e2])) (by omega_using [hK, e1]) he i hi]
  refine ⟨c, ⟨⟨kp, fun i hi => ?_, ?_⟩, r1, r2, r3, r4⟩, fun i hi => ?_, fun i hi => ?_⟩
  · rw [he' i (by omega_using [hsum, hi])]
    unfold emC emB emA
    rw [ite_eq_right (by omega_using [hsum, hi]), ite_eq_left (by omega_using [hi]), ite_eq_left hi]
  · rw [he' _ (by omega_using [hsum])]
    exact ite_eq_left rfl
  · rw [Nat.add_assoc, he' _ (by omega_using [hsum, hi])]
    unfold emC emB emA
    rw [ite_eq_right (by omega_using [hsum, hi]), ite_eq_left (by omega_using [hi]), ite_eq_right (by omega_using []), ite_eq_left (by omega_using [hi]),
      Nat.add_sub_cancel_left]
  · rw [Nat.add_assoc, Nat.add_assoc, he' _ (by omega_using [hsum, hi])]
    unfold emC emB
    rw [ite_eq_right (by omega_using [hsum, hi]), ite_eq_right (by omega_using []), ite_eq_left (by omega_using [hi])]
    congr 1; omega_using []

/-- `maskedDB`, before its first byte's top bits are cleared: MGF1 with the
hash function `g` of the table at the argument 23. -/
theorem mask_vp (P : EP) (hP : ∃ σ, In h.D P σ) (g : OHash) {fG : Fns}
    (hT : ∀ σ, P.T σ → TabFacts g.H fG P.tab P.ai P.au P.af σ)
    (fne : fG.init ≠ [] ∧ fG.upd ≠ [] ∧ fG.fin ≠ []) :
    VP (fun σ s => (Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧ EMv P s.mem (emC h P σ)) ∧ s.syms = σ.syms)
      (.seq (.block (mgfArgsT h.H)) (Impl.RsaOaep.X86.mgfXor fG 23))
      (fun σ s => (Ctx (P.lay h.D) P.scr σ s ∧ Ko h P σ s.mem ∧
        (∀ i < dbN h P, s.mem (sa P.scr (oEm + lo P + i)) = dbv h P σ i ^^^ (mkS h g.G P σ).getD i 0) ∧
        ∀ i < h.D, s.mem (sa P.scr (oEm + lo P + dbN h P + i)) = (Hs h P σ).getD i 0) ∧ s.syms = σ.syms) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.1.2.1.1.2.1
  have hK := hi₀.k1024
  obtain hlo : lo P ≤ 1 := by unfold lo; split <;> omega_using []
  obtain hdb : P.sl + 1 ≤ dbN h P := by unfold dbN; have := hf.2; omega_using [this]
  obtain hsum : lo P + dbN h P + h.D + 1 = P.K := by unfold dbN; have := hf.2; omega_using [this]
  obtain hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega_arith
  have hD0 : 0 < h.D := h.D_pos
  have hS := g.S_le
  have hW := g.Wb_le
  have hF := g.F_le
  have e1 : oEm = 1024 := rfl
  have e2 : oRsa = 8192 := rfl
  have fit := hg.fit
  obtain hC : (P.lay h.D).C ≤ 2 ^ 32 := by have := ok.BC; have := (P.lay h.D).B.isLt; omega_arith
  have e4 : Impl.RsaOaep.X86.oCtr = 768 := rfl
  have e5 : Impl.RsaOaep.X86.oBuf = 2048 := rfl
  -- What `mgfXor` writes misses the parameters and the bytes of `EM` outside `DB` and `H`.
  obtain away : ∀ r ∈ Proof.RsaOaep.X86.mgfW g (P.lay h.D) P.scr (oEm + lo P) (dbN h P), Away3 (P.lay h.D) r ∧
      ∀ i, (i < lo P ∨ i = P.K - 1) → ¬ r.Contains (sa P.scr (oEm + i)) 1 := by
    intro r hr
    simp only [Proof.RsaOaep.X86.mgfW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨away3_scr hg (by pomega_arith), fun i hi => Geo.sep (scr := P.scr) (o := oEm + i) (n := 1) (by pomega_arith)
        (by pomega_arith) (by pomega_arith) _ (Region.contains_self _ _)⟩
    · exact ⟨away3_scr hg (by pomega_arith), fun i hi => Geo.sep (scr := P.scr) (o := oEm + i) (n := 1) (by pomega_arith)
        (by pomega_arith) (by pomega_arith) _ (Region.contains_self _ _)⟩
    · exact ⟨away3_scr hg (by pomega_arith), fun i hi => Geo.sep (scr := P.scr) (o := oEm + i) (n := 1) (by pomega_arith)
        (by pomega_arith) (by pomega_arith) _ (Region.contains_self _ _)⟩
    · exact ⟨away3_scr hg (by pomega_arith), fun i hi => Geo.sep (scr := P.scr) (o := oEm + i) (n := 1) (by pomega_arith)
        (by pomega_arith) (by pomega_arith) _ (Region.contains_self _ _)⟩
    · exact ⟨⟨Lay.fr_low (by decide) hC, Lay.fr_low (by decide) hC, Lay.fr_low (by decide) hC⟩,
        fun i hi => hg.low ok (o := oEm + i) (n := 1) (by pomega_arith) _ (Region.contains_self _ _)⟩
    · exact ⟨away3_scr hg (by pomega_arith), fun i hi => Geo.sep (scr := P.scr) (o := oEm + i) (n := 1) (by pomega_arith)
        (by pomega_arith) (by pomega_arith) _ (Region.contains_self _ _)⟩
    all_goals exact ⟨away3_slot (by decide) (.inr (by decide)), fun i hi => (hg.slot ok (o := oEm + i) (n := 1)
      (by pomega_arith) (by rw [hg.F]; decide)).symm _ (Region.contains_self _ _)⟩
  obtain hX : ∀ σ m m', Ko h P σ m → Frame (Proof.RsaOaep.X86.mgfW g (P.lay h.D) P.scr (oEm + lo P) (dbN h P)) m m' → Ko h P σ m' :=
    fun σ m m' ⟨hk, h0, hbc⟩ hf' => ⟨hk.keep h hf' fun r hr => (away r hr).1, fun i hi => by
      rw [← h0 i hi]; exact hf' _ fun r hr => (away r hr).2 i (.inl hi),
      by rw [← hbc]; exact hf' _ fun r hr => (away r hr).2 _ (.inr rfl)⟩
  obtain mp := mpOf g hg (so := oEm + lo P + dbN h P) (sl := h.D) (dOff := oEm + lo P) (dl := dbN h P) hD0
    (by omega_using [hdb]) (by omega_using []) (by omega_using []) (by pomega_arith) (by pomega_arith) (.inr (Nat.le_refl _)) (seed := Hs h P)
    (fun σ => Hs_length h P σ) hX (sg_arg h (j := 23) (by decide)) hi₀.tbl Proof.RsaOaep.X86.tabArg23_taint
    (fun σ m hk => hT σ hk.1.1.tabT) fne
  exact VP.seq (VP.syms (margs_vp h P ⟨σ₀, hi₀⟩)) ((Proof.RsaOaep.X86.mgf_vp g mp (dstv := dbv h P)).mono (fun _ _ h => h)
    fun σ s ⟨⟨hc, ⟨hk, _⟩, hd, hh⟩, sy⟩ => ⟨⟨hc, hk, hd, hh⟩, sy⟩)

/-- `EM`, as the specification encodes it (`RsaPss.emT`). -/
abbrev emF (G : Spec.Mgf1.Hash) (P : EP) (σ : State) (i : Nat) : Byte :=
  RsaPss.emT (lo P) (dbN h P) P.sl (saltB P σ) (Hs h P σ) (mkS h G P σ) ((cW (xB P)).setWidth 8) i

theorem andByte (b : Byte) (w : BitVec 32) : (b.setWidth 32 &&& w).setWidth 8 = b &&& w.setWidth 8 := by
  obtain e1 : (b.setWidth 32).setWidth 8 = b := by simp
  rw [BitVec.setWidth_and, e1]

/-- `maskedDB`'s first byte ANDed with the mask: `EM`. -/
theorem top_vp (G : Spec.Mgf1.Hash) (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Ko h P σ s.mem ∧
        (∀ i < dbN h P, s.mem (sa P.scr (oEm + lo P + i)) = dbv h P σ i ^^^ (mkS h G P σ).getD i 0) ∧
        ∀ i < h.D, s.mem (sa P.scr (oEm + lo P + dbN h P + i)) = (Hs h P σ).getD i 0)
      (.seq (.block topSet) (.block topAnd))
      (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Kp h P σ s.mem ∧ EMv P s.mem (emF h G P σ)) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.2.1.1.2.1
  have hK := hi₀.k1024
  obtain hlo : lo P ≤ 1 := by unfold lo; split <;> omega_using []
  obtain hdb : P.sl + 1 ≤ dbN h P := by unfold dbN; have := hf.2; omega_using [this]
  obtain hsum : lo P + dbN h P + h.D + 1 = P.K := by unfold dbN; have := hf.2; omega_using [this]
  have e1 : oEm = 1024 := rfl
  have e2 : oRsa = 8192 := rfl
  have e3 : oY = 2048 := rfl
  have fit := hg.fit
  refine VP.seq (G := fun σ s => (Ctx (P.lay h.D) P.scr σ s ∧ Ko h P σ s.mem ∧
        (∀ i < dbN h P, s.mem (sa P.scr (oEm + lo P + i)) = dbv h P σ i ^^^ (mkS h G P σ).getD i 0) ∧
        ∀ i < h.D, s.mem (sa P.scr (oEm + lo P + dbN h P + i)) = (Hs h P σ).getD i 0) ∧
      s.gpr .esi = P.scr + BitVec.ofNat 32 (oEm + lo P))
    (VP.taint [.esp, .ebp] topSet_taint (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hk, hd, hh⟩ => ?_)
    (VP.taint _ topAnd_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s ⟨⟨hc, hk, hd, hh⟩, si⟩ => ?_)
  · simp only [topSet, atDb, atS, addSlot, addi, Impl.RsaPkcs1Sig.X86.stk, List.cons_append, List.nil_append]
    refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
    obtain c2 : Ctx (P.lay h.D) P.scr σ t2 := (hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)
    refine wp_addm (B := (P.lay h.D).B) (by rw [c2.st.sp])
      (by rw [hg.aFr ok sLo (by decide)]; exact c2.rFr hg sLo (by decide)) fun t3 u3 => WP.block_nil ?_
    obtain m3 : t3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
    refine ⟨⟨c2.upd u3 (by decide) (by decide), m3 ▸ hk, m3 ▸ hd, m3 ▸ hh⟩, ?_⟩
    rw [u3.gpr, u2.gpr, u1.gpr, u2.mem, u1.mem, hc.ebp, hg.aFr ok sLo (by decide), hk.1.2.2.2.1, BitVec.add_assoc,
      BitVec.ofNat_add_ofNat]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.1.1.st.sp, h₂.1.1.st.sp]
    · rw [h₁.2, h₂.2]
  · have ad : addr (P.scr + BitVec.ofNat 32 (oEm + lo P)) 0 = sa P.scr (oEm + lo P) := by
      rw [hg.addrD (by omega_using [hlo, e1, e2]), Nat.add_zero]
    obtain rd : InRegions (s.rd ++ s.wr) (sa P.scr (oEm + lo P)) 1 := hg.rd hc.st (by omega_using [hlo, e1, e2])
    obtain wd : InRegions s.wr (sa P.scr (oEm + lo P)) 1 := hg.wr hc.st (by omega_using [hlo, e1, e2])
    simp only [topAnd, Impl.RsaPkcs1Sig.X86.at_, Impl.RsaPkcs1Sig.X86.stk]
    refine wp_movzx8 (a := sa P.scr (oEm + lo P)) (by rw [ea_at, si]; exact ad) rd fun t1 u1 => ?_
    obtain c1 : Ctx (P.lay h.D) P.scr σ t1 := hc.upd u1 (by decide) (by decide)
    obtain rC := c1.rFr hg sC (by decide)
    refine wp_andS (readSrc_mem (B := (P.lay h.D).B) (by rw [c1.st.sp]) (by rw [hg.aFr ok sC (by decide)]; exact rC))
      fun t2 u2 => ?_
    obtain a2 : t2.ea ⟨.esi, 0⟩ = sa P.scr (oEm + lo P) := by
      rw [ea_at, u2.other .esi (by decide), u1.other .esi (by decide), si]; exact ad
    refine wp_store8 (a := sa P.scr (oEm + lo P)) a2 (by rw [u2.wr, u1.wr]; exact wd) fun t3 u3 => WP.block_nil ?_
    obtain m3 : t3.mem = s.mem.writeW (sa P.scr (oEm + lo P)) (s.mem (sa P.scr (oEm + lo P)) &&& (cW (xB P)).setWidth 8) := by
      rw [u3.mem, Reg8.reg, u2.gpr, u2.mem, u1.gpr, u1.mem, hg.aFr ok sC (by decide), hk.1.2.2.1, andByte]
    obtain fr : Frame [sR P.scr (oEm + lo P) 1] s.mem t3.mem := by
      rw [m3]; exact frame_byte P.scr _ _ (Nat.le_refl _) (by omega_using []) (by omega_using [hlo, e1])
    refine ⟨(c1.upd u2 (by decide) (by decide)).write (by rw [u2.mem, u1.mem]; exact fr) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hg.inW (by omega_using [hlo, e1, e2])) u3.rd u3.wr (by rw [u3.gpr])
        (by rw [u3.gpr]), hk.1.keep h fr fun r hr => ?_, fun i hi => ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact away3_scr hg (by omega_using [hlo, e1, e2])
    rw [m3, sa_write P.scr _ _ (by omega_using [hlo, e1]) (by omega_using [hK, e1, hi])]
    obtain hl := Hs_length h P σ
    unfold emF RsaPss.emT
    by_cases h1 : i < lo P
    · rw [ite_eq_right (by omega_using [h1]), ite_eq_left h1]; exact hk.2.1 i h1
    rw [ite_eq_right h1]
    by_cases h2 : i - lo P < dbN h P
    · rw [ite_eq_left h2]
      by_cases h3 : i - lo P = 0
      · rw [ite_eq_left (by omega_using [h1, h3]), ite_eq_left h3, show oEm + lo P = oEm + lo P + 0 from rfl, hd 0 (by omega_using [hdb]), h3]
      · rw [ite_eq_right (by omega_using [h3]), ite_eq_right h3, show oEm + i = oEm + lo P + (i - lo P) by omega_using [h1], hd _ h2]
    rw [ite_eq_right h2, ite_eq_right (by omega_using [hdb, h2])]
    by_cases h4 : i - lo P < dbN h P + (Hs h P σ).length
    · rw [ite_eq_left h4, show oEm + i = oEm + lo P + dbN h P + (i - lo P - dbN h P) by omega_using [hdb, h2], hh _ (by omega_using [hl, h2, h4])]
    · rw [ite_eq_right h4, show oEm + i = oEm + (P.K - 1) by omega_using [hdb, hsum, hi, hl, h4]]; exact hk.2.2

/-- The encoding, when everything fits, with the hash function of the table
of `MdHash` at the argument 22 and MGF1's of the table of `MdHash` at 23. -/
theorem enc_vp (P : EP) (hP : ∃ σ, In h.D P σ) {dn : String} {f : MdFns}
    (hTH : ∀ σ, P.TH σ → HFacts h dn f P.tabH P.hai P.hac P.had σ)
    (fneH : f.init ≠ [] ∧ f.comp ≠ [] ∧ f.dig ≠ []) (g : OHash) {fG : Fns}
    (hT : ∀ σ, P.T σ → TabFacts g.H fG P.tab P.ai P.au P.af σ)
    (fne : fG.init ≠ [] ∧ fG.upd ≠ [] ∧ fG.fin ≠ []) :
    VP (fun σ s => E0 h P σ s ∧ s.syms = σ.syms) (signEncT f h.H fG)
      (fun σ s => (Ctx (P.lay h.D) P.scr σ s ∧ Kp h P σ s.mem ∧ EMv P s.mem (emF h g.G P σ)) ∧ s.syms = σ.syms) := by
  show VP _ (.seq (yDig h.H 16) (.seq (.block (cpSalt h.H)) (.seq (.ite .e (.block []) Impl.Bignum.X86.copyBytes)
    (.seq (.block (lenArgs h.H 19)) (.seq (ctHashT f h.H 22) (.seq (.block clrEm) (.seq zeroLoop
    (.seq (.block oneSet) (.seq (.block put1) (.seq (.ite .e (.block []) Impl.Bignum.X86.copyBytes)
    (.seq (.block (putH h.H)) (.seq Impl.Bignum.X86.copyBytes (.seq (.block bcSet) (.seq (.block putBc)
    (.seq (.block (mgfArgsT h.H)) (.seq (Impl.RsaOaep.X86.mgfXor fG 23) (.seq (.block topSet) (.block topAnd)))))))))))))))))) _
  exact (VP.syms (yDig_sg h P hP)).seq (vpAssoc ((VP.syms (salt_vp h P hP)).seq ((VP.syms (lenSet_vp h P)).seq
    ((hash_vp h P hP hTH fneH).seq (vpAssoc ((VP.syms (clr_vp h P hP)).seq (vpAssoc ((VP.syms (one_vp h P hP)).seq
    ((VP.syms (cpS_vp h P hP)).seq (vpAssoc ((VP.syms (putH_vp h P hP)).seq (vpAssoc ((VP.syms (bc_vp h P hP)).seq
    (vpAssoc ((mask_vp h P hP g hT fne).seq (VP.syms (top_vp h g.G P hP)))))))))))))))))

end VG.Proof.RsaPss.X86.Sg
