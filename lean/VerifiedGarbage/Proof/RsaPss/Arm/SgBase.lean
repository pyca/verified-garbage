module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Entry
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
public import VerifiedGarbage.Spec.RsaPss
public import VerifiedGarbage.Spec.RsaPss.Contract
public import VerifiedGarbage.Spec.RsaPss.Table
public import VerifiedGarbage.Proof.RsaPss.Arm.TabCall
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.RsaPss.Arm.Step
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-!
# RSASSA-PSS signing on ARMv7: where everything is

`EP`: what two runs share (the frame's base `B`, the pointers, the lengths,
the public key's bytes `nB` and `eB`, and the tables: the hash function's of
`MdHash`, `hd`, with what each run's entry state holds of it, `HT`, and
MGF1's of `Hash`, `tab`, its functions at `ai`, `au` and `af`, and `T`), and
its layout (`EP.lay`), with the 3440 bytes below the frame that the call of
`vg_rsa_private_checked` uses. `In P σ`: the state `σ` the body starts
from. The shared contract, with the tables one of those it lists and the
stack of the frames and of the call, gives `In (ep s …) (entered frameBytes
s)` (`in_of_pre`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Sg

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm

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
  hd : BitVec 32
  hi : BitVec 32
  hc : BitVec 32
  hdg : BitVec 32
  HT : State → Prop
  tab : BitVec 32
  ai : BitVec 32
  au : BitVec 32
  af : BitVec 32
  T : State → Prop

namespace EP

variable (D : Nat) (P : EP)

abbrev OUT : Region := ⟨State.addr P.out, P.K⟩
abbrev N : Region := ⟨State.addr P.n, P.K⟩
abbrev E : Region := ⟨State.addr P.e, P.el⟩
abbrev PP : Region := ⟨State.addr P.p, P.pl⟩
abbrev QQ : Region := ⟨State.addr P.q, P.ql⟩
abbrev DP : Region := ⟨State.addr P.dp, P.pl⟩
abbrev DQ : Region := ⟨State.addr P.dq, P.ql⟩
abbrev QI : Region := ⟨State.addr P.qinv, P.pl⟩
abbrev DIG : Region := ⟨State.addr P.dig, D⟩
abbrev SALT : Region := ⟨State.addr P.salt, P.sl⟩
abbrev SCR : Region := ⟨State.addr P.scr, P.scl * 8⟩
abbrev HTAB : Region := Sig.tableRegion 32 (State.addr P.hd) 11
abbrev TAB : Region := Sig.tableRegion 32 (State.addr P.tab) 5

/-- The arguments, in order. -/
abbrev argv : List (BitVec 32) :=
  [P.out, BitVec.ofNat 32 P.K, P.n, BitVec.ofNat 32 P.K, P.e, BitVec.ofNat 32 P.el, P.p, BitVec.ofNat 32 P.pl,
    P.q, BitVec.ofNat 32 P.ql, P.dp, BitVec.ofNat 32 P.pl, P.dq, BitVec.ofNat 32 P.ql, P.qinv,
    BitVec.ofNat 32 P.pl, P.dig, BitVec.ofNat 32 D, P.salt, BitVec.ofNat 32 P.sl, P.scr, BitVec.ofNat 32 P.scl,
    P.hd, P.tab]

abbrev lay : Lay where
  B := P.B
  F := frameBytes
  A := 80
  argv := P.argv D
  ro := [P.N, P.E, P.PP, P.QQ, P.DP, P.DQ, P.QI, P.DIG D, P.SALT, P.HTAB, P.TAB]
  rw := [P.OUT, P.SCR]
  C := 3440

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
  nB : Spec.Rsa.bytesAt σ.mem (State.addr P.n) P.K = P.nB
  eB : Spec.Rsa.bytesAt σ.mem (State.addr P.e) P.el = P.eB
  htabT : P.HT σ
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
  simp only [Proof.X25519.Arm.addr_toNat] at hf
  unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at hs
  exact ⟨rfl, by unfold oRsa; omega_arith, ⟨P.scl * 8, by unfold oRsa; omega_arith, by simp⟩, ⟨σ, h.ok⟩, by show 16 ≤ 3440; decide⟩

/-- The table of `MdHash`, in a buffer only read. -/
theorem htbl : ∃ R ∈ (P.lay D).ro, ∀ o, o + 4 ≤ 44 → R.Contains (RsaOaep.Arm.tA P.hd o) 4 := by
  have hf := h.ok.fits P.HTAB (by simp)
  simp only [Sig.tableRegion, Proof.X25519.Arm.addr_toNat] at hf
  refine ⟨P.HTAB, by simp, fun o ho => ?_⟩
  show (⟨State.addr P.hd, 11 * (32 / 8)⟩ : Region).Contains (State.addr (P.hd + BitVec.ofNat 32 o)) 4
  rw [VG.Arm.addr_add (by omega_arith)]
  exact Offset.contains_base _ (by omega_arith) (by omega_arith)

/-- The table of `Hash`, in a buffer only read. -/
theorem tbl : ∃ R ∈ (P.lay D).ro, ∀ o, o + 4 ≤ 20 → R.Contains (RsaOaep.Arm.tA P.tab o) 4 := by
  have hf := h.ok.fits P.TAB (by simp)
  simp only [Sig.tableRegion, Proof.X25519.Arm.addr_toNat] at hf
  refine ⟨P.TAB, by simp, fun o ho => ?_⟩
  show (⟨State.addr P.tab, 5 * (32 / 8)⟩ : Region).Contains (State.addr (P.tab + BitVec.ofNat 32 o)) 4
  rw [VG.Arm.addr_add (by omega_arith)]
  exact Offset.contains_base _ (by omega_arith) (by omega_arith)

end In

/-! ## The entry -/

/-- The stack the function uses: the push, the inner frame and the call's. -/
abbrev stackBytes : Nat := 56 + frameBytes + 3440

/-- The shared contract, with the hash function one of the tables `hs`,
MGF1's one of `ts`, and that stack. -/
abbrev spec (hs ts : List FnTable) : Contract isa :=
  Spec.RsaPss.signTableContract (abi.withTables Spec.RsaPss.signTableSig [("hash", hs), ("mgf1", ts)]) stackBytes

/-- Unfolds the contract's precondition at `h`. -/
macro "sign_pre" " at " h:ident : tactic => `(tactic| (
  sig_pre [Spec.RsaPss.signTableContract, Spec.RsaPss.signTableSig, Spec.MdHashTable.param,
      Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Spec.HashTable.param,
      Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argRegs, reduceClassify, Loc.val] at $h:ident
  sig_pre [Spec.RsaPss.signTableContract, Spec.RsaPss.signTableSig, Spec.MdHashTable.param,
      Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Spec.HashTable.param,
      Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argRegs, reduceClassify, Loc.val] at $h:ident
  simp only [Option.map_some, Nat.reduceAdd, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq,
    exists_eq_left'] at $h:ident))

/-- The public parameters of an entry state, with what `HT` and `T` say of
the tables. -/
def ep (s : State) (hi hc hdg : BitVec 32) (HT : State → Prop) (ai au af : BitVec 32) (T : State → Prop) : EP where
  B := s.sp - BitVec.ofNat 32 56 - BitVec.ofNat 32 frameBytes
  out := s.gpr .r0
  n := s.gpr .r2
  e := stackArg s 0
  p := stackArg s 2
  q := stackArg s 4
  dp := stackArg s 6
  dq := stackArg s 8
  qinv := stackArg s 10
  dig := stackArg s 12
  salt := stackArg s 14
  scr := stackArg s 16
  K := (s.gpr .r3).toNat
  el := (stackArg s 1).toNat
  pl := (stackArg s 3).toNat
  ql := (stackArg s 5).toNat
  sl := (stackArg s 15).toNat
  scl := (stackArg s 17).toNat
  nB := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat
  eB := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat
  hd := stackArg s 18
  hi := hi
  hc := hc
  hdg := hdg
  HT := HT
  tab := stackArg s 19
  ai := ai
  au := au
  af := af
  T := T

variable {hi hc hdg : BitVec 32} {HT : State → Prop} {ai au af : BitVec 32} {T : State → Prop}

theorem ep_lay (D : Nat) (s : State) :
    (ep s hi hc hdg HT ai au af T).lay D = layOf frameBytes 80 ((ep s hi hc hdg HT ai au af T).argv D)
      [(ep s hi hc hdg HT ai au af T).N, (ep s hi hc hdg HT ai au af T).E, (ep s hi hc hdg HT ai au af T).PP, (ep s hi hc hdg HT ai au af T).QQ,
        (ep s hi hc hdg HT ai au af T).DP, (ep s hi hc hdg HT ai au af T).DQ, (ep s hi hc hdg HT ai au af T).QI, (ep s hi hc hdg HT ai au af T).DIG D,
        (ep s hi hc hdg HT ai au af T).SALT, (ep s hi hc hdg HT ai au af T).HTAB, (ep s hi hc hdg HT ai au af T).TAB]
      [(ep s hi hc hdg HT ai au af T).OUT, (ep s hi hc hdg HT ai au af T).SCR] s 3440 := rfl

theorem in_of_pre {hs ts : List FnTable} {s : State} (h : (spec hs ts).pre s) {D : Nat}
    (hD : (stackArg s 13).toNat = D) (hHT : HT (entered frameBytes s)) (hT : T (entered frameBytes s)) :
    In D (ep s hi hc hdg HT ai au af T) (entered frameBytes s) := by
  sign_pre at h
  sig_split h
  rename_i hsp hsa hheld hheld2 hpw hrd hwr oN oE oP oQ oDP oDQ oQI oD oSl oS oTH oT oA nS eS pS qS dpS dqS qiS dS
    slS sTH sT sA kO kN kE kP kQ kDP kDQ kQI kD kSl kS kTH kT kA fO fN fE fP fQ fDP fDQ fQI fD fSl fS fTH fT kv olk
    el1 elK pl1 plK ql1 qlK dpl qil dql slK
  have h3624 : 3624 ≤ s.sp.toNat := hsp
  have r1 : s.gpr .r1 = s.gpr .r3 := BitVec.eq_of_toNat_eq olk
  have a7 : stackArg s 7 = stackArg s 3 := BitVec.eq_of_toNat_eq dpl
  have a11 : stackArg s 11 = stackArg s 3 := BitVec.eq_of_toNat_eq qil
  have a9 : stackArg s 9 = stackArg s 5 := BitVec.eq_of_toNat_eq dql
  have a13 : stackArg s 13 = BitVec.ofNat 32 D := by
    apply BitVec.eq_of_toNat_eq; rw [hD, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [← hD]; exact (stackArg s 13).isLt)]
  rw [olk] at hwr oN oE oP oQ oDP oDQ oQI oD oSl oS oTH oT oA kO fO
  rw [dpl] at oDP dpS kDP fDP hrd
  rw [qil] at oQI qiS kQI fQI hrd
  rw [dql] at oDQ dqS kDQ fDQ hrd
  rw [hD] at oD dS kD fD hrd
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
      sl32 := (stackArg s 15).isLt
      scl32 := (stackArg s 17).isLt
      nB := bytesAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kN.sub_left below).symm)
        (by show (s.gpr .r3).toNat ≤ 2 ^ 64; omega_arith)
      eB := bytesAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kE.sub_left below).symm)
        (by show (stackArg s 1).toNat ≤ 2 ^ 64; omega_arith)
      htabT := hHT
      tabT := hT }
  rw [ep_lay]
  refine ok_entered (by decide) (by decide) rfl hsp hsa hrd hwr ?_ ?_ ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [kN, kE, kP, kQ, kDP, kDQ, kQI, kD, kSl, kTH, kT, kO, kS, kA]
  · intro w hw r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hw with rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [oN, oE, oP, oQ, oDP, oDQ, oQI, oD, oSl, oTH, oT, oA, nS.symm, eS.symm, pS.symm, qS.symm, dpS.symm,
      dqS.symm, qiS.symm, dS.symm, slS.symm, sTH, sT, sA]
  · exact List.pairwise_pair.mpr oS
  · intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [fN, fE, fP, fQ, fDP, fDQ, fQI, fD, fSl, fTH, fT, fO, fS]
  · intro j hj
    rcases (by omega_arith : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    · rfl
    · simp [regArg, ep, r1]
    · rfl
    · simp [regArg, ep]
  · intro i hi
    have : i < 20 := hi
    rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
        i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl <;>
      simp [ep, a7, a9, a11, a13]

/-- What the proofs need of the tables, for the hash function `h`, whose
digest is named `dn`, and MGF1's `g`: an indirect call of `f`'s and `fg`'s
functions (not empty) through the table reaches theirs, in every run. -/
structure TF (h : PssHash) (g : RsaOaep.Arm.OHash) (f : MdFns) (fg : Impl.RsaOaep.Arm.Fns) (dn : String) (P : EP) :
    Prop where
  ht : ∀ σ, P.HT σ → HTab h dn f P.hd P.hi P.hc P.hdg σ
  t : ∀ σ, P.T σ → RsaOaep.Arm.TabFacts g.H fg P.tab P.ai P.au P.af σ
  fne : f.init ≠ [] ∧ f.comp ≠ [] ∧ f.dig ≠ []
  gne : fg.init ≠ [] ∧ fg.upd ≠ [] ∧ fg.fin ≠ []

end VG.Proof.RsaPss.Arm.Sg
