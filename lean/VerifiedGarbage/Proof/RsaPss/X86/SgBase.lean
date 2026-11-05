module

public import VerifiedGarbage.Impl.RsaPss.X86
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Entry
public import VerifiedGarbage.Spec.RsaPss.Contract
public import VerifiedGarbage.Spec.RsaPss.Table
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.RsaPss.X86.Base
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.Exec

/-!
# RSASSA-PSS signing on x86: where everything is

As on ARMv7 (`Proof/RsaPss/Arm/SgBase.lean`): `EP`, what two runs share
(the frame's base `B`, the pointers, the lengths, the public key's bytes
`nB` and `eB`, and the tables: the hash function's of `MdHash` at `tabH`,
whose functions are at `hai`, `hac` and `had`, and MGF1's of `Hash` at
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
abbrev TAB : Region := Sig.tableRegion 32 (P.tab.setWidth 64) 5

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
  have hf := h.ok.fits (P.SCR) (by simp)
  simp only [BitVec.toNat_setWidth] at hf
  rw [Nat.mod_eq_of_lt (by have := P.scr.isLt; omega)] at hf
  unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at hs
  exact ⟨rfl, by unfold oRsa; omega, ⟨P.scl * 8, by unfold oRsa; omega, by simp⟩, ⟨σ, h.ok⟩,
    by show 48 ≤ 3448; decide⟩

/-- The table of `MdHash`, in a buffer only read: its words 0 to 4. -/
theorem tblH : ∀ k, k < 5 → ∃ R ∈ (P.lay D).ro, R.Contains (VG.X86.addr P.tabH (4 * k)) 4 := by
  have hf := h.ok.fits P.TABH (by simp)
  simp only [Sig.tableRegion, BitVec.toNat_setWidth] at hf
  rw [Nat.mod_eq_of_lt (by have := P.tabH.isLt; omega)] at hf
  intro k hk
  refine ⟨P.TABH, by simp, ?_⟩
  show (⟨P.tabH.setWidth 64, 11 * (32 / 8)⟩ : Region).Contains (VG.X86.addr P.tabH (4 * k)) 4
  rw [addr_eq (by omega)]
  exact Offset.contains_base _ (by omega) (by omega)

/-- Its word 5, the hash function's index. -/
theorem tblH5 : ∃ R ∈ (P.lay D).ro, R.Contains (VG.X86.addr P.tabH 20) 4 := by
  have hf := h.ok.fits P.TABH (by simp)
  simp only [Sig.tableRegion, BitVec.toNat_setWidth] at hf
  rw [Nat.mod_eq_of_lt (by have := P.tabH.isLt; omega)] at hf
  refine ⟨P.TABH, by simp, ?_⟩
  show (⟨P.tabH.setWidth 64, 11 * (32 / 8)⟩ : Region).Contains (VG.X86.addr P.tabH 20) 4
  rw [addr_eq (by omega)]
  exact Offset.contains_base _ (by omega) (by omega)

/-- The table of `Hash`, in a buffer only read. -/
theorem tbl : ∃ R ∈ (P.lay D).ro, ∀ o, o + 4 ≤ 20 → R.Contains (VG.X86.addr P.tab o) 4 := by
  have hf := h.ok.fits P.TAB (by simp)
  simp only [Sig.tableRegion, BitVec.toNat_setWidth] at hf
  rw [Nat.mod_eq_of_lt (by have := P.tab.isLt; omega)] at hf
  refine ⟨P.TAB, by simp, fun o ho => ?_⟩
  show (⟨P.tab.setWidth 64, 5 * (32 / 8)⟩ : Region).Contains (VG.X86.addr P.tab o) 4
  rw [addr_eq (by omega)]
  exact Offset.contains_base _ (by omega) (by omega)

end In

/-! ## The entry -/

/-- The stack the function uses: the push, the inner frame and the calls'. -/
abbrev stackBytes : Nat := 16 + frameBytes + 3448

/-- The shared contract, with the hash function's table one of `tsH` and
MGF1's one of `ts`, and that stack. -/
abbrev spec (tsH ts : List FnTable) : Contract isa :=
  Spec.RsaPss.signTableContract (abi.withTables Spec.RsaPss.signTableSig [("hash", tsH), ("mgf1", ts)]) stackBytes

/-- Unfolds the contract's precondition at `h`. -/
macro "sign_pre" " at " h:ident : tactic => `(tactic| (
  sig_pre [Spec.RsaPss.signTableContract, Spec.RsaPss.signTableSig, Spec.MdHashTable.param,
      Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Spec.HashTable.param,
      Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes,
      stackBelow] at $h:ident
  sig_pre [Spec.RsaPss.signTableContract, Spec.RsaPss.signTableSig, Spec.MdHashTable.param,
      Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Spec.HashTable.param,
      Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes,
      stackBelow] at $h:ident
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
      (arg s 22).toNat + 44 ≤ 2 ^ 32 ∧ (arg s 23).toNat + 20 ≤ 2 ^ 32 ∧
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
  have a1 : arg s 1 = arg s 3 := BitVec.eq_of_toNat_eq olk
  have a11 : arg s 11 = arg s 7 := BitVec.eq_of_toNat_eq dpl
  have a15 : arg s 15 = arg s 7 := BitVec.eq_of_toNat_eq qil
  have a13 : arg s 13 = arg s 9 := BitVec.eq_of_toNat_eq dql
  rw [olk] at hwr oN oE oP oQ oDP oDQ oQI oD oSl oS oTH oT oA rO kO fO
  rw [dpl] at hrd oDP dpS dpA rDP kDP fDP
  rw [qil] at hrd oQI qiS qiA rQI kQI fQI
  rw [dql] at hrd oDQ dqS dqA rDQ kDQ fDQ
  have h16 : 4 * Impl.RsaPkcs1Sig.X86.savedRegs.length ≤ (s.gpr .esp).toNat := by
    simp only [Impl.RsaPkcs1Sig.X86.savedRegs, List.length_cons, List.length_nil]; omega_arith
  have hpush : Frame [below (s.gpr .esp) (4 * Impl.RsaPkcs1Sig.X86.savedRegs.length)] s.mem
      (entered frameBytes s).mem :=
    pushed_frame (by decide) h16
  have below16 : Region.Sub (below (s.gpr .esp) (4 * Impl.RsaPkcs1Sig.X86.savedRegs.length))
      ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 3608, 3608⟩ := by
    simp only [below, Impl.RsaPkcs1Sig.X86.savedRegs, List.length_cons, List.length_nil]
    rw [Taint.sub_setWidth (by omega_arith)]
    exact Offset.sub_below _ (by omega_arith) (by omega_arith)
  refine
    { ok := ?_
      kv := kv, el1 := el1, elK := elK, pl1 := pl1, plK := plK, ql1 := ql1, qlK := qlK, slK := slK
      sl32 := (arg s 19).isLt
      scl32 := (arg s 21).isLt
      nB := Proof.RsaPkcs1Sig.bytesAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kN.sub_left below16).symm)
        (by show (arg s 3).toNat ≤ 2 ^ 64; omega_arith)
      eB := Proof.RsaPkcs1Sig.bytesAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kE.sub_left below16).symm)
        (by show (arg s 5).toNat ≤ 2 ^ 64; omega_arith)
      tabTH := hTH
      tabT := hT }
  rw [ep_lay]
  refine ok_entered (S := 3608) rfl (by decide) hsp (by simp) (by simp; omega_arith) hrd
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
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 2).isLt; omega_arith)]; omega_arith)
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
    rcases (by omega_using [this] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨
        j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨
        j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl <;> simp [ep, a1, a11, a13, a15]

end VG.Proof.RsaPss.X86.Sg
