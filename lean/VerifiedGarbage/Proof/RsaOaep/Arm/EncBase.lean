module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Entry
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
public import VerifiedGarbage.Spec.RsaOaep.Precomputed
public import VerifiedGarbage.Spec.RsaOaep.Tables
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.RsaPss.Arm.Step
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSAES-OAEP encryption with a precomputed public key on ARMv7: where everything is

`EP`: what two runs share (the frame's base `B`, the pointers, the lengths,
and the public key's bytes and precomputed words), its layout (`EP.lay`,
with the seed's `D` bytes), with the 56 bytes below the frame that the call
of `vg_rsa_public_precomputed_checked` and the frames of `update` and
`finalize` use, and the tables of the label's hash function and of MGF1's,
the arguments 16 and 17 (`EP.TABL`, `EP.TAB`). `In D P σ`:
the state `σ` the body starts from (`in_of_pre`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm.Enc

open VG VG.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm VG.Proof.RsaOaep.Arm
open VG.Impl.RsaPss.Arm (frameBytes oRsa arg)

/-- What two runs share: MGF1's table (`tab`) among them, its hash
function's functions at `ai`, `au` and `af`, and what each run's entry
state holds of it (`T`), and the same of the label's hash function's table
(`tabL`, `aiL`, `auL`, `afL`, `TL`). -/
structure EP where
  B : BitVec 32
  out : BitVec 32
  n : BitVec 32
  e : BitVec 32
  lab : BitVec 32
  msg : BitVec 32
  seed : BitVec 32
  sl : BitVec 32
  scr : BitVec 32
  pre : BitVec 32
  K : Nat
  el : Nat
  ll : Nat
  ml : Nat
  scl : Nat
  rl : Nat
  nB : List Byte
  eB : List Byte
  pw : List (BitVec 64)
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

variable (D : Nat) (P : EP)

abbrev OUT : Region := ⟨State.addr P.out, P.K⟩
abbrev N : Region := ⟨State.addr P.n, P.K⟩
abbrev E : Region := ⟨State.addr P.e, P.el⟩
abbrev LAB : Region := ⟨State.addr P.lab, P.ll⟩
abbrev MSG : Region := ⟨State.addr P.msg, P.ml⟩
abbrev SEED : Region := ⟨State.addr P.seed, D⟩
abbrev SCR : Region := ⟨State.addr P.scr, P.scl * 8⟩
abbrev PRE : Region := ⟨State.addr P.pre, P.rl * 8⟩
abbrev TAB : Region := Sig.tableRegion 32 (State.addr P.tab) 5
abbrev TABL : Region := Sig.tableRegion 32 (State.addr P.tabL) 5

/-- The arguments, in order. -/
abbrev argv : List (BitVec 32) :=
  [P.out, BitVec.ofNat 32 P.K, P.n, BitVec.ofNat 32 P.K, P.e, BitVec.ofNat 32 P.el, P.lab, BitVec.ofNat 32 P.ll,
    P.msg, BitVec.ofNat 32 P.ml, P.seed, P.sl, P.scr, BitVec.ofNat 32 P.scl, P.pre, BitVec.ofNat 32 P.rl, P.tabL,
    P.tab]

abbrev lay : Lay where
  B := P.B
  F := frameBytes
  A := 56
  argv := P.argv
  ro := [P.N, P.E, P.LAB, P.MSG, P.SEED D, P.PRE, P.TABL, P.TAB]
  rw := [P.OUT, P.SCR]

end EP

/-- The state the body starts from. -/
structure In (D : Nat) (P : EP) (σ : State) : Prop where
  ok : (P.lay D).Ok σ
  kv : Spec.Rsa.lenValid P.K
  el1 : 1 ≤ P.el
  elK : P.el ≤ P.K
  scrK : Spec.RsaPss.publicScratchWords P.K ≤ P.scl
  rlK : P.rl = Spec.Rsa.precomputedWords P.K
  ll32 : P.ll < 2 ^ 32
  ml32 : P.ml < 2 ^ 32
  scl32 : P.scl < 2 ^ 32
  nB : Spec.Rsa.bytesAt σ.mem (State.addr P.n) P.K = P.nB
  eB : Spec.Rsa.bytesAt σ.mem (State.addr P.e) P.el = P.eB
  pw : Spec.Rsa.wordsAt σ.mem (State.addr P.pre) P.rl = P.pw
  tabT : P.T σ
  tabTL : P.TL σ

namespace In

variable {D : Nat} {P : EP} {σ : State} (h : In D P σ)
include h

theorem k64 : 64 ≤ P.K := h.kv.1
theorem k1024 : P.K ≤ 1024 := h.kv.2

/-- The working space: ours, and the public operation's after it. -/
theorem pubScr : Spec.Rsa.publicScratchWords P.K ≤ P.scl - 1024 ∧ 1025 ≤ P.scl := by
  have := h.scrK
  unfold Spec.RsaPss.publicScratchWords Spec.Rsa.publicScratchWords at this
  unfold Spec.Rsa.publicScratchWords
  omega

/-- Our part of `scratch`. -/
theorem geo : Geo (P.lay D) P.scr := by
  have hs := h.pubScr.2
  have hf := h.ok.fits (P.SCR) (by simp)
  simp only [Proof.X25519.Arm.addr_toNat] at hf
  exact ⟨rfl, by unfold oRsa; omega, ⟨P.scl * 8, by unfold oRsa; omega, by simp⟩, ⟨σ, h.ok⟩,
    by show 16 ≤ 56; decide⟩

end In

/-! ## The entry -/

/-- The stack the function uses: the push, the inner frame and the call's. -/
abbrev stackBytes : Nat := 56 + frameBytes + 56

/-- The shared contract, with both hash functions each one of the tables
`ts`, and that stack. -/
abbrev spec (ts : List FnTable) : Contract isa :=
  Spec.RsaOaep.encryptTablesContract (abi.withTables Spec.RsaOaep.encryptTablesSig [("hash", ts), ("mgf1", ts)])
    stackBytes

/-- Unfolds the contract's precondition at `h`. -/
macro "enc_pre" " at " h:ident : tactic => `(tactic| (
  sig_pre [Spec.RsaOaep.encryptTablesContract, Spec.RsaOaep.encryptTablesSig, Spec.RsaOaep.seedLenOk,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argRegs, reduceClassify, Loc.val] at $h:ident
  sig_pre [Spec.RsaOaep.encryptTablesContract, Spec.RsaOaep.encryptTablesSig, Spec.RsaOaep.seedLenOk,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argRegs, reduceClassify, Loc.val] at $h:ident
  simp only [Option.map_some, Nat.reduceAdd, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq,
    exists_eq_left'] at $h:ident))

/-- The public parameters of an entry state, with MGF1's hash function's
functions at `ai`, `au` and `af`, and `T` of the entry. -/
def ep (s : State) (ai au af : BitVec 32) (T : State → Prop) (aiL auL afL : BitVec 32) (TL : State → Prop) : EP where
  B := s.sp - BitVec.ofNat 32 56 - BitVec.ofNat 32 frameBytes
  out := s.gpr .r0
  n := s.gpr .r2
  e := stackArg s 0
  lab := stackArg s 2
  msg := stackArg s 4
  seed := stackArg s 6
  sl := stackArg s 7
  scr := stackArg s 8
  pre := stackArg s 10
  K := (s.gpr .r3).toNat
  el := (stackArg s 1).toNat
  ll := (stackArg s 3).toNat
  ml := (stackArg s 5).toNat
  scl := (stackArg s 9).toNat
  rl := (stackArg s 11).toNat
  nB := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat
  eB := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat
  pw := Spec.Rsa.wordsAt s.mem (State.addr (stackArg s 10)) (stackArg s 11).toNat
  tab := stackArg s 13
  ai := ai
  au := au
  af := af
  T := T
  tabL := stackArg s 12
  aiL := aiL
  auL := auL
  afL := afL
  TL := TL

variable {ai au af : BitVec 32} {T : State → Prop} {aiL auL afL : BitVec 32} {TL : State → Prop}

theorem ep_lay (D : Nat) (s : State) :
    (ep s ai au af T aiL auL afL TL).lay D = layOf frameBytes 56 (ep s ai au af T aiL auL afL TL).argv
      [(ep s ai au af T aiL auL afL TL).N, (ep s ai au af T aiL auL afL TL).E,
        (ep s ai au af T aiL auL afL TL).LAB, (ep s ai au af T aiL auL afL TL).MSG,
        (ep s ai au af T aiL auL afL TL).SEED D, (ep s ai au af T aiL auL afL TL).PRE,
        (ep s ai au af T aiL auL afL TL).TABL, (ep s ai au af T aiL auL afL TL).TAB]
      [(ep s ai au af T aiL auL afL TL).OUT, (ep s ai au af T aiL auL afL TL).SCR] s := rfl

/-- The tables, as the contract gives them: each one of `ts`, the label's
hash function's at the stack argument 12 and MGF1's at 13, with the
functions of distinct names at distinct addresses. -/
theorem spec_tab {ts : List FnTable} {s : State} (h : (spec ts).pre s) :
    (∃ T ∈ ts, Abi.tableHeld 32 s.mem (State.addr (stackArg s 12)) (FnTable.words isa s T)) ∧
      (∃ T ∈ ts, Abi.tableHeld 32 s.mem (State.addr (stackArg s 13)) (FnTable.words isa s T)) ∧
      ((ts.map (fun T : FnTable => T.fns)).flatten ++ ((ts.map (fun T : FnTable => T.fns)).flatten ++ [])).Pairwise
        (fun f g => f ≠ g → (s.syms f).setWidth 64 ≠ (s.syms g).setWidth 64) ∧
      (stackArg s 12).toNat + 20 ≤ 2 ^ 32 ∧ (stackArg s 13).toNat + 20 ≤ 2 ^ 32 := by
  enc_pre at h
  sig_split h
  rename_i hsp hsa hheld hheld2 hpw hrd hwr oN oE oL oM oS oC oP oTL oT oA nC eC lC mC sC cP cTL cT cA kO kN kE kL
    kM kS kC kP kTL kT kA fO fN fE fL fM fS fC fP fTL fT kv olk el1 elK scrK rlK
  exact ⟨hheld, hheld2, hpw, fTL, fT⟩

theorem in_of_pre {H : Spec.Mgf1.Hash} {ts : List FnTable} {s : State} (h : (spec ts).pre s)
    (hH : Spec.HashTable.hashAt 32 s.mem (State.addr (stackArg s 12)) = some H)
    (hT : T (entered frameBytes s)) (hTL : TL (entered frameBytes s)) :
    In H.len (ep s ai au af T aiL auL afL TL) (entered frameBytes s) := by
  enc_pre at h
  sig_split h
  rename_i hsp hsa hheld hheld2 hpw hrd hwr oN oE oL oM oS oC oP oTL oT oA nC eC lC mC sC cP cTL cT cA kO kN kE kL
    kM kS kC kP kTL kT kA fO fN fE fL fM fS fC fP fTL fT kv olk el1 elK scrK rlK
  have hl := h H hH
  rw [hl] at hrd oS sC kS fS
  have h240 : 240 ≤ s.sp.toNat := hsp
  have r1 : s.gpr .r1 = s.gpr .r3 := BitVec.eq_of_toNat_eq olk
  rw [olk] at hwr oN oE oL oM oS oC oP oTL oT oA kO fO
  have hpush : Frame [FrameStack.belowA s.sp 56] s.mem (entered frameBytes s).mem :=
    FrameStack.pushed_frameA (rs := Impl.RsaPkcs1Sig.Arm.pushRegs) (by show 56 ≤ s.sp.toNat; omega_arith)
  have below : Region.Sub (FrameStack.belowA s.sp 56) ⟨State.addr s.sp - BitVec.ofNat 64 240, 240⟩ := by
    show Region.Sub ⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩ _
    rw [FrameStack.addr_sub' (by omega_arith)]
    exact Offset.sub_below _ (by omega_arith) (by omega_arith)
  refine
    { ok := ?_
      kv := kv, el1 := el1, elK := elK, scrK := scrK, rlK := rlK
      ll32 := (stackArg s 3).isLt
      ml32 := (stackArg s 5).isLt
      scl32 := (stackArg s 9).isLt
      nB := bytesAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kN.sub_left below).symm)
        (by show (s.gpr .r3).toNat ≤ 2 ^ 64; omega_arith)
      eB := bytesAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kE.sub_left below).symm)
        (by show (stackArg s 1).toNat ≤ 2 ^ 64; omega_arith)
      pw := wordsAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kP.sub_left below).symm)
        (by show (stackArg s 11).toNat * 8 ≤ 2 ^ 64; omega_arith)
      tabT := hT
      tabTL := hTL }
  rw [ep_lay]
  refine ok_entered (by decide) (by decide) rfl hsp hsa hrd hwr ?_ ?_ ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [kN, kE, kL, kM, kS, kP, kTL, kT, kO, kC, kA]
  · intro w hw r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hw with rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [oN, oE, oL, oM, oS, oP, oTL, oT, oA, nC.symm, eC.symm, lC.symm, mC.symm, sC.symm, cP, cTL, cT, cA]
  · exact List.pairwise_pair.mpr oC
  · intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [fN, fE, fL, fM, fS, fP, fTL, fT, fO, fC]
  · intro j hj
    rcases (by omega_arith : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    · rfl
    · simp [regArg, ep, r1]
    · rfl
    · simp [regArg, ep]
  · intro i hi
    have : i < 14 := hi
    rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨
        i = 11 ∨ i = 12 ∨ i = 13) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [ep]

end VG.Proof.RsaOaep.Arm.Enc
