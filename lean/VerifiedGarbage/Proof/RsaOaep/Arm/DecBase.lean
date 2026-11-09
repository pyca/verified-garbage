module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Entry
public import VerifiedGarbage.Spec.RsaOaep.Contract
public import VerifiedGarbage.Spec.RsaOaep.Tables
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.RsaOaep.Arm.Mgf
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSAES-OAEP decryption on ARMv7: where everything is

`EP`: what two runs share (the frame's base `B`, the pointers, the lengths
and the public key's bytes `nB` and `eB`), and its layout (`EP.lay`), with
the 3440 bytes below the frame that the call of `vg_rsa_private_checked`
uses, and MGF1's table, the argument 23 (`EP.TAB`). `In P σ`: the state `σ`
the body starts from (`in_of_pre`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm.Dec

open VG VG.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm VG.Proof.RsaOaep.Arm
open VG.Impl.RsaPss.Arm (frameBytes oRsa arg)

/-- What two runs share: MGF1's table (`tab`) among them, its hash
function's functions at `ai`, `au` and `af`, and what each run's entry
state holds of it (`T`). -/
structure EP where
  B : BitVec 32
  out : BitVec 32
  ml : BitVec 32
  n : BitVec 32
  e : BitVec 32
  p : BitVec 32
  q : BitVec 32
  dp : BitVec 32
  dq : BitVec 32
  qinv : BitVec 32
  lab : BitVec 32
  ct : BitVec 32
  scr : BitVec 32
  K : Nat
  el : Nat
  pl : Nat
  ql : Nat
  ll : Nat
  scl : Nat
  nB : List Byte
  eB : List Byte
  tab : BitVec 32
  ai : BitVec 32
  au : BitVec 32
  af : BitVec 32
  T : State → Prop
  tabL : BitVec 32
  aiL : BitVec 32
  auL : BitVec 32
  afL : BitVec 32
  TL : State → Prop

namespace EP

variable (P : EP)

abbrev OUT : Region := ⟨State.addr P.out, P.K⟩
abbrev ML : Region := ⟨State.addr P.ml, 8⟩
abbrev N : Region := ⟨State.addr P.n, P.K⟩
abbrev E : Region := ⟨State.addr P.e, P.el⟩
abbrev PP : Region := ⟨State.addr P.p, P.pl⟩
abbrev QQ : Region := ⟨State.addr P.q, P.ql⟩
abbrev DP : Region := ⟨State.addr P.dp, P.pl⟩
abbrev DQ : Region := ⟨State.addr P.dq, P.ql⟩
abbrev QI : Region := ⟨State.addr P.qinv, P.pl⟩
abbrev LAB : Region := ⟨State.addr P.lab, P.ll⟩
abbrev CT : Region := ⟨State.addr P.ct, P.K⟩
abbrev SCR : Region := ⟨State.addr P.scr, P.scl * 8⟩
abbrev TAB : Region := Sig.tableRegion 32 (State.addr P.tab) 5
abbrev TABL : Region := Sig.tableRegion 32 (State.addr P.tabL) 5

/-- The arguments, in order. -/
abbrev argv : List (BitVec 32) :=
  [P.out, BitVec.ofNat 32 P.K, P.ml, P.n, BitVec.ofNat 32 P.K, P.e, BitVec.ofNat 32 P.el, P.p, BitVec.ofNat 32 P.pl,
    P.q, BitVec.ofNat 32 P.ql, P.dp, BitVec.ofNat 32 P.pl, P.dq, BitVec.ofNat 32 P.ql, P.qinv,
    BitVec.ofNat 32 P.pl, P.lab, BitVec.ofNat 32 P.ll, P.ct, BitVec.ofNat 32 P.K, P.scr, BitVec.ofNat 32 P.scl,
    P.tabL, P.tab]

abbrev lay : Lay where
  B := P.B
  F := frameBytes
  A := 84
  argv := P.argv
  ro := [P.N, P.E, P.PP, P.QQ, P.DP, P.DQ, P.QI, P.LAB, P.CT, P.TABL, P.TAB]
  rw := [P.OUT, P.ML, P.SCR]
  C := 3440

end EP

/-- The state the body starts from. -/
structure In (P : EP) (σ : State) : Prop where
  ok : P.lay.Ok σ
  kv : Spec.Rsa.lenValid P.K
  el1 : 1 ≤ P.el
  elK : P.el ≤ P.K
  pl1 : 1 ≤ P.pl
  plK : P.pl < P.K
  ql1 : 1 ≤ P.ql
  qlK : P.ql < P.K
  slK : Spec.RsaPss.scratchWords P.K ≤ P.scl
  ll32 : P.ll < 2 ^ 32
  scl32 : P.scl < 2 ^ 32
  nB : Spec.Rsa.bytesAt σ.mem (State.addr P.n) P.K = P.nB
  eB : Spec.Rsa.bytesAt σ.mem (State.addr P.e) P.el = P.eB
  tabT : P.T σ
  tabTL : P.TL σ

namespace In

variable {P : EP} {σ : State} (h : In P σ)
include h

theorem k64 : 64 ≤ P.K := h.kv.1
theorem k1024 : P.K ≤ 1024 := h.kv.2

/-- Our part of `scratch`. -/
theorem geo : Geo P.lay P.scr := by
  have hs := h.slK
  have hK := h.k1024
  have hf := h.ok.fits (P.SCR) (by simp)
  simp only [Proof.X25519.Arm.addr_toNat] at hf
  unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at hs
  exact ⟨rfl, by unfold oRsa; omega, ⟨P.scl * 8, by unfold oRsa; omega, by simp⟩, ⟨σ, h.ok⟩, by show 16 ≤ 3440; decide⟩

end In

/-! ## The entry -/

/-- The stack the function uses: the push, the inner frame and the call's. -/
abbrev stackBytes : Nat := 56 + frameBytes + 3440

/-- The shared contract, with MGF1's hash function one of the tables `ts` and
that stack. -/
abbrev spec (ts : List FnTable) : Contract isa :=
  Spec.RsaOaep.decryptTablesContract
    (abi.withTables Spec.RsaOaep.decryptTablesSig [("hash", ts), ("mgf1", ts)]) stackBytes

/-- Unfolds the contract's precondition at `h`. -/
macro "dec_pre" " at " h:ident : tactic => `(tactic| (
  sig_pre [Spec.RsaOaep.decryptTablesContract, Spec.RsaOaep.decryptTablesSig, Spec.RsaOaep.decryptSig,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argRegs, reduceClassify, Loc.val] at $h:ident
  sig_pre [Spec.RsaOaep.decryptTablesContract, Spec.RsaOaep.decryptTablesSig, Spec.RsaOaep.decryptSig,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argRegs, reduceClassify, Loc.val] at $h:ident
  simp only [Option.map_some, Nat.reduceAdd, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq,
    exists_eq_left'] at $h:ident))

/-- The public parameters of an entry state, with MGF1's hash function's
functions at `ai`, `au` and `af`, and `T` of the entry. -/
def ep (s : State) (ai au af : BitVec 32) (T : State → Prop) (aiL auL afL : BitVec 32) (TL : State → Prop) : EP where
  B := s.sp - BitVec.ofNat 32 56 - BitVec.ofNat 32 frameBytes
  out := s.gpr .r0
  ml := s.gpr .r2
  n := s.gpr .r3
  e := stackArg s 1
  p := stackArg s 3
  q := stackArg s 5
  dp := stackArg s 7
  dq := stackArg s 9
  qinv := stackArg s 11
  lab := stackArg s 13
  ct := stackArg s 15
  scr := stackArg s 17
  K := (stackArg s 0).toNat
  el := (stackArg s 2).toNat
  pl := (stackArg s 4).toNat
  ql := (stackArg s 6).toNat
  ll := (stackArg s 14).toNat
  scl := (stackArg s 18).toNat
  nB := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat
  eB := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 1)) (stackArg s 2).toNat
  tab := stackArg s 20
  ai := ai
  au := au
  af := af
  T := T
  tabL := stackArg s 19
  aiL := aiL
  auL := auL
  afL := afL
  TL := TL

variable {ai au af : BitVec 32} {T : State → Prop} {aiL auL afL : BitVec 32} {TL : State → Prop}

theorem ep_lay (s : State) :
    (ep s ai au af T aiL auL afL TL).lay = layOf frameBytes 84 (ep s ai au af T aiL auL afL TL).argv
      [(ep s ai au af T aiL auL afL TL).N, (ep s ai au af T aiL auL afL TL).E, (ep s ai au af T aiL auL afL TL).PP,
        (ep s ai au af T aiL auL afL TL).QQ, (ep s ai au af T aiL auL afL TL).DP,
        (ep s ai au af T aiL auL afL TL).DQ, (ep s ai au af T aiL auL afL TL).QI,
        (ep s ai au af T aiL auL afL TL).LAB, (ep s ai au af T aiL auL afL TL).CT,
        (ep s ai au af T aiL auL afL TL).TABL, (ep s ai au af T aiL auL afL TL).TAB]
      [(ep s ai au af T aiL auL afL TL).OUT, (ep s ai au af T aiL auL afL TL).ML,
        (ep s ai au af T aiL auL afL TL).SCR] s 3440 := rfl

/-- The tables, as the contract gives them: each one of `ts`, the label's
hash function's at the stack argument 19 and MGF1's at 20, with the
functions of distinct names at distinct addresses. -/
theorem spec_tab {ts : List FnTable} {s : State} (h : (spec ts).pre s) :
    (∃ T ∈ ts, Abi.tableHeld 32 s.mem (State.addr (stackArg s 19)) (FnTable.words isa s T)) ∧
      (∃ T ∈ ts, Abi.tableHeld 32 s.mem (State.addr (stackArg s 20)) (FnTable.words isa s T)) ∧
      ((ts.map (fun T : FnTable => T.fns)).flatten ++ ((ts.map (fun T : FnTable => T.fns)).flatten ++ [])).Pairwise
        (fun f g => f ≠ g → (s.syms f).setWidth 64 ≠ (s.syms g).setWidth 64) ∧
      (stackArg s 19).toNat + 20 ≤ 2 ^ 32 ∧ (stackArg s 20).toNat + 20 ≤ 2 ^ 32 := by
  dec_pre at h
  sig_split h
  rename_i hsp hsa hheld hheld2 hpw hrd hwr oM oN oE oP oQ oDP oDQ oQI oL oC oS oTL oT oA mN mE mP mQ mDP mDQ mQI mL
    mC mS mTL mT mA nS eS pS qS dpS dqS qiS lS cS sTL sT sA kO kM kN kE kP kQ kDP kDQ kQI kL kC kS kTL kT kA fO fM fN
    fE fP fQ fDP fDQ fQI fL fC fS fTL fT kv olk clk el1 elK pl1 plK ql1 qlK dpl qil dql
  exact ⟨hheld, hheld2, hpw, fTL, fT⟩

theorem in_of_pre {ts : List FnTable} {s : State} (h : (spec ts).pre s)
    (hT : T (entered frameBytes s)) (hTL : TL (entered frameBytes s)) :
    In (ep s ai au af T aiL auL afL TL) (entered frameBytes s) := by
  dec_pre at h
  sig_split h
  rename_i hsp hsa hheld hheld2 hpw hrd hwr oM oN oE oP oQ oDP oDQ oQI oL oC oS oTL oT oA mN mE mP mQ mDP mDQ mQI mL
    mC mS mTL mT mA nS eS pS qS dpS dqS qiS lS cS sTL sT sA kO kM kN kE kP kQ kDP kDQ kQI kL kC kS kTL kT kA fO fM fN
    fE fP fQ fDP fDQ fQI fL fC fS fTL fT kv olk clk el1 elK pl1 plK ql1 qlK dpl qil dql
  have slK := h
  have h3624 : 3624 ≤ s.sp.toNat := hsp
  have r1 : s.gpr .r1 = stackArg s 0 := BitVec.eq_of_toNat_eq olk
  have a16 : stackArg s 16 = stackArg s 0 := BitVec.eq_of_toNat_eq clk
  have a8 : stackArg s 8 = stackArg s 4 := BitVec.eq_of_toNat_eq dpl
  have a12 : stackArg s 12 = stackArg s 4 := BitVec.eq_of_toNat_eq qil
  have a10 : stackArg s 10 = stackArg s 6 := BitVec.eq_of_toNat_eq dql
  rw [olk] at hwr oM oN oE oP oQ oDP oDQ oQI oL oC oS oTL oT oA kO fO
  rw [clk] at oC mC cS kC fC hrd
  rw [dpl] at oDP mDP dpS kDP fDP hrd
  rw [qil] at oQI mQI qiS kQI fQI hrd
  rw [dql] at oDQ mDQ dqS kDQ fDQ hrd
  have hpush : Frame [FrameStack.belowA s.sp 56] s.mem (entered frameBytes s).mem :=
    FrameStack.pushed_frameA (rs := Impl.RsaPkcs1Sig.Arm.pushRegs) (by show 56 ≤ s.sp.toNat; omega_arith)
  have below : Region.Sub (FrameStack.belowA s.sp 56)
      ⟨State.addr s.sp - BitVec.ofNat 64 stackBytes, stackBytes⟩ := by
    show Region.Sub ⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩ _
    rw [FrameStack.addr_sub' (by omega_arith)]
    exact Offset.sub_below _ (show 56 ≤ stackBytes by decide) (show stackBytes - 56 + 56 ≤ stackBytes by decide)
  refine
    { ok := ?_
      kv := kv, el1 := el1, elK := elK, pl1 := pl1, plK := plK, ql1 := ql1, qlK := qlK, slK := slK
      ll32 := (stackArg s 14).isLt
      scl32 := (stackArg s 18).isLt
      nB := bytesAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kN.sub_left below).symm)
        (by show (stackArg s 0).toNat ≤ 2 ^ 64; omega_arith)
      eB := bytesAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kE.sub_left below).symm)
        (by show (stackArg s 2).toNat ≤ 2 ^ 64; omega_arith)
      tabT := hT
      tabTL := hTL }
  rw [ep_lay]
  refine ok_entered (by decide) (by decide) rfl hsp hsa hrd hwr ?_ ?_ ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [kN, kE, kP, kQ, kDP, kDQ, kQI, kL, kC, kTL, kT, kO, kM, kS, kA]
  · intro w hw r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hw with rfl | rfl | rfl <;>
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [oN, oE, oP, oQ, oDP, oDQ, oQI, oL, oC, oTL, oT, oA, mN, mE, mP, mQ, mDP, mDQ, mQI, mL, mC, mTL, mT, mA,
      nS.symm, eS.symm, pS.symm, qS.symm, dpS.symm, dqS.symm, qiS.symm, lS.symm, cS.symm, sTL, sT, sA]
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨⟨oM, oS⟩, mS, fun _ h => h.elim⟩
  · intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [fN, fE, fP, fQ, fDP, fDQ, fQI, fL, fC, fTL, fT, fO, fM, fS]
  · intro j hj
    rcases (by omega_arith : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    · rfl
    · simp [regArg, ep, r1]
    · rfl
    · simp [regArg, ep]
  · intro i hi
    have : i < 21 := hi
    rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
        i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;>
      simp [ep, a8, a10, a12, a16]

end VG.Proof.RsaOaep.Arm.Dec
