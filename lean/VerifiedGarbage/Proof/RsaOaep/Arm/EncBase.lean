module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Entry
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
public import VerifiedGarbage.Spec.RsaOaep.Precomputed
public import VerifiedGarbage.Spec.RsaOaep.Table
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
`finalize` use, and MGF1's table, the argument 15 (`EP.TAB`). `In D P σ`:
the state `σ` the body starts from (`in_of_pre`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm.Enc

open VG VG.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm VG.Proof.RsaOaep.Arm
open VG.Impl.RsaPss.Arm (frameBytes oRsa arg)

/-- What two runs share: MGF1's table (`tab`) among them, its hash
function's functions at `ai`, `au` and `af`, and what each run's entry
state holds of it (`T`). -/
structure EP where
  B : BitVec 32
  out : BitVec 32
  n : BitVec 32
  e : BitVec 32
  lab : BitVec 32
  msg : BitVec 32
  seed : BitVec 32
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

/-- The arguments, in order. -/
abbrev argv : List (BitVec 32) :=
  [P.out, BitVec.ofNat 32 P.K, P.n, BitVec.ofNat 32 P.K, P.e, BitVec.ofNat 32 P.el, P.lab, BitVec.ofNat 32 P.ll,
    P.msg, BitVec.ofNat 32 P.ml, P.seed, P.scr, BitVec.ofNat 32 P.scl, P.pre, BitVec.ofNat 32 P.rl, P.tab]

abbrev lay : Lay where
  B := P.B
  F := frameBytes
  A := 48
  argv := P.argv
  ro := [P.N, P.E, P.LAB, P.MSG, P.SEED D, P.PRE, P.TAB]
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

/-- The shared contract, with MGF1's hash function one of the tables `ts` and
that stack. -/
abbrev spec (H : Spec.Mgf1.Hash) (ts : List FnTable) : Contract isa :=
  Spec.RsaOaep.encryptTableContract H (abi.withTables (Spec.RsaOaep.encryptTableSig H) [("mgf1", ts)]) stackBytes

/-- Unfolds the contract's precondition at `h`. -/
macro "enc_pre" " at " h:ident : tactic => `(tactic| (
  sig_pre [Spec.RsaOaep.encryptTableContract, Spec.RsaOaep.encryptTableSig, Spec.RsaOaep.encryptPrecomputedSig,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argRegs, reduceClassify, Loc.val] at $h:ident
  sig_pre [Spec.RsaOaep.encryptTableContract, Spec.RsaOaep.encryptTableSig, Spec.RsaOaep.encryptPrecomputedSig,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argRegs, reduceClassify, Loc.val] at $h:ident
  simp only [Option.map_some, Nat.reduceAdd, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq,
    exists_eq_left'] at $h:ident))

/-- The public parameters of an entry state, with MGF1's hash function's
functions at `ai`, `au` and `af`, and `T` of the entry. -/
def ep (s : State) (ai au af : BitVec 32) (T : State → Prop) : EP where
  B := s.sp - BitVec.ofNat 32 56 - BitVec.ofNat 32 frameBytes
  out := s.gpr .r0
  n := s.gpr .r2
  e := stackArg s 0
  lab := stackArg s 2
  msg := stackArg s 4
  seed := stackArg s 6
  scr := stackArg s 7
  pre := stackArg s 9
  K := (s.gpr .r3).toNat
  el := (stackArg s 1).toNat
  ll := (stackArg s 3).toNat
  ml := (stackArg s 5).toNat
  scl := (stackArg s 8).toNat
  rl := (stackArg s 10).toNat
  nB := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat
  eB := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat
  pw := Spec.Rsa.wordsAt s.mem (State.addr (stackArg s 9)) (stackArg s 10).toNat
  tab := stackArg s 11
  ai := ai
  au := au
  af := af
  T := T

variable {ai au af : BitVec 32} {T : State → Prop}

theorem ep_lay (D : Nat) (s : State) :
    (ep s ai au af T).lay D = layOf frameBytes 48 (ep s ai au af T).argv [(ep s ai au af T).N, (ep s ai au af T).E,
      (ep s ai au af T).LAB, (ep s ai au af T).MSG, (ep s ai au af T).SEED D, (ep s ai au af T).PRE,
      (ep s ai au af T).TAB] [(ep s ai au af T).OUT, (ep s ai au af T).SCR] s := rfl

/-- MGF1's table, as the contract gives it: one of `ts`, at the argument 15,
with the functions of distinct names at distinct addresses. -/
theorem spec_tab {H : Spec.Mgf1.Hash} {ts : List FnTable} {s : State} (h : (spec H ts).pre s) :
    (∃ T ∈ ts, Abi.tableHeld 32 s.mem (State.addr (stackArg s 11)) (FnTable.words isa s T)) ∧
      ((ts.map (fun T : FnTable => T.fns)).flatten ++ []).Pairwise
        (fun f g => f ≠ g → (s.syms f).setWidth 64 ≠ (s.syms g).setWidth 64) ∧
      (stackArg s 11).toNat + 20 ≤ 2 ^ 32 := by
  enc_pre at h
  sig_split h
  rename_i hsp hsa hheld hpw hrd hwr oN oE oL oM oS oC oP oT oA nC eC lC mC sC cP cT cA kO kN kE kL kM kS kC kP
    kT kA fO fN fE fL fM fS fC fP fT kv olk el1 elK scrK
  exact ⟨hheld, hpw, fT⟩

theorem in_of_pre {H : Spec.Mgf1.Hash} {ts : List FnTable} {s : State} (h : (spec H ts).pre s)
    (hT : T (entered frameBytes s)) : In H.len (ep s ai au af T) (entered frameBytes s) := by
  enc_pre at h
  sig_split h
  rename_i hsp hsa hheld hpw hrd hwr oN oE oL oM oS oC oP oT oA nC eC lC mC sC cP cT cA kO kN kE kL kM kS kC kP
    kT kA fO fN fE fL fM fS fC fP fT kv olk el1 elK scrK
  have rlK := h
  have h240 : 240 ≤ s.sp.toNat := hsp
  have r1 : s.gpr .r1 = s.gpr .r3 := BitVec.eq_of_toNat_eq olk
  rw [olk] at hwr oN oE oL oM oS oC oP oT oA kO fO
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
      scl32 := (stackArg s 8).isLt
      nB := bytesAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kN.sub_left below).symm)
        (by show (s.gpr .r3).toNat ≤ 2 ^ 64; omega_arith)
      eB := bytesAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kE.sub_left below).symm)
        (by show (stackArg s 1).toNat ≤ 2 ^ 64; omega_arith)
      pw := wordsAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kP.sub_left below).symm)
        (by show (stackArg s 10).toNat * 8 ≤ 2 ^ 64; omega_arith)
      tabT := hT }
  rw [ep_lay]
  refine ok_entered (by decide) (by decide) rfl hsp hsa hrd hwr ?_ ?_ ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [kN, kE, kL, kM, kS, kP, kT, kO, kC, kA]
  · intro w hw r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hw with rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [oN, oE, oL, oM, oS, oP, oT, oA, nC.symm, eC.symm, lC.symm, mC.symm, sC.symm, cP, cT, cA]
  · exact List.pairwise_pair.mpr oC
  · intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [fN, fE, fL, fM, fS, fP, fT, fO, fC]
  · intro j hj
    rcases (by omega_arith : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    · rfl
    · simp [regArg, ep, r1]
    · rfl
    · simp [regArg, ep]
  · intro i hi
    have : i < 12 := hi
    rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨
        i = 11) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [ep]

end VG.Proof.RsaOaep.Arm.Enc
