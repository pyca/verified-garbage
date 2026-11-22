module

public import VerifiedGarbage.Proof.RsaOaep.Encode
public import VerifiedGarbage.Proof.RsaPss.Arm.Step
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.RsaOaep.Arm.LabelT
import VerifiedGarbage.Proof.RsaPss.Arm.CtSel
import VerifiedGarbage.Proof.RsaPss.Arm.CtBase
import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Aes.KeyExp
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.RsaOaep.Encode
meta import Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.RsaOaep.Arm.LabelT
meta import VerifiedGarbage.Proof.RsaPss.Arm.CtSel
meta import VerifiedGarbage.Proof.RsaPss.Arm.CtBase
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
meta import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Common
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Aes.KeyExp
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.RsaOaep.Arm.Mgf
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.RsaOaep.Arm.Mgf
meta import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.RsaOaep.Arm.Calls
meta import VerifiedGarbage.Proof.RsaOaep.Arm.Calls
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Entry
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
public import VerifiedGarbage.Spec.RsaOaep.MdTables
public import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Entry
meta import VerifiedGarbage.Spec.RsaOaep.MdTables
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.RsaPss.Arm.Step

/-! ### `RsaOaep.Arm.EncChk`, which this module and modules that import it used -/

section

/-! ### `RsaOaep.Arm.EncBase`, which this module and modules that import it used -/

section

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
abbrev TAB : Region := Sig.tableRegion 32 (State.addr P.tab) 11
abbrev TABL : Region := Sig.tableRegion 32 (State.addr P.tabL) 11

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
  C := 104

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
  omega_using [this]

/-- Our part of `scratch`. -/
theorem geo : Geo (P.lay D) P.scr := by
  have hs := h.pubScr.2
  have hf := h.ok.fits (P.SCR) (by simp)
  simp only [Proof.X25519.Arm.addr_toNat] at hf
  exact ⟨rfl, by unfold oRsa; omega_using [hs, hf], ⟨P.scl * 8, by unfold oRsa; omega_using [hs], by simp⟩, ⟨σ, h.ok⟩,
    by show 16 ≤ 104; decide⟩

end In

/-! ## The entry -/

/-- The stack the function uses: the push, the inner frame and the call's. -/
abbrev stackBytes : Nat := 56 + frameBytes + 104

/-- The shared contract, with both hash functions each one of the tables
`ts`, and that stack. -/
abbrev spec (ts : List FnTable) : Contract isa :=
  Spec.RsaOaep.encryptMdTablesContract (abi.withTables Spec.RsaOaep.encryptMdTablesSig [("hash", ts), ("mgf1", ts)])
    stackBytes

/-- Unfolds the contract's precondition at `h`. -/
macro "enc_pre" " at " h:ident : tactic => `(tactic| (
  sig_pre [Spec.RsaOaep.encryptMdTablesContract, Spec.RsaOaep.encryptMdTablesSig, Spec.RsaOaep.seedLenMdOk,
      Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argRegs, reduceClassify, Loc.val] at $h:ident
  sig_pre [Spec.RsaOaep.encryptMdTablesContract, Spec.RsaOaep.encryptMdTablesSig, Spec.RsaOaep.seedLenMdOk,
      Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables, Sig.wordIndex,
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
      [(ep s ai au af T aiL auL afL TL).OUT, (ep s ai au af T aiL auL afL TL).SCR] s 104 := rfl

/-- The tables, as the contract gives them: each one of `ts`, the label's
hash function's at the stack argument 12 and MGF1's at 13, with the
functions of distinct names at distinct addresses. -/
theorem spec_tab {ts : List FnTable} {s : State} (h : (spec ts).pre s) :
    (∃ T ∈ ts, Abi.tableHeld 32 s.mem (State.addr (stackArg s 12)) (FnTable.words isa s T)) ∧
      (∃ T ∈ ts, Abi.tableHeld 32 s.mem (State.addr (stackArg s 13)) (FnTable.words isa s T)) ∧
      ((ts.map (fun T : FnTable => T.fns)).flatten ++ ((ts.map (fun T : FnTable => T.fns)).flatten ++ [])).Pairwise
        (fun f g => f ≠ g → (s.syms f).setWidth 64 ≠ (s.syms g).setWidth 64) ∧
      (stackArg s 12).toNat + 44 ≤ 2 ^ 32 ∧ (stackArg s 13).toNat + 44 ≤ 2 ^ 32 := by
  enc_pre at h
  sig_split h
  rename_i hsp hsa hheld hheld2 hpw hrd hwr oN oE oL oM oS oC oP oTL oT oA nC eC lC mC sC cP cTL cT cA kO kN kE kL
    kM kS kC kP kTL kT kA fO fN fE fL fM fS fC fP fTL fT kv olk el1 elK scrK rlK
  exact ⟨hheld, hheld2, hpw, fTL, fT⟩

theorem in_of_pre {H : Spec.Mgf1.Hash} {ts : List FnTable} {s : State} (h : (spec ts).pre s)
    (hH : Spec.MdHashTable.hashAt 32 s.mem (State.addr (stackArg s 12)) = some H)
    (hT : T (entered frameBytes s)) (hTL : TL (entered frameBytes s)) :
    In H.len (ep s ai au af T aiL auL afL TL) (entered frameBytes s) := by
  enc_pre at h
  sig_split h
  rename_i hsp hsa hheld hheld2 hpw hrd hwr oN oE oL oM oS oC oP oTL oT oA nC eC lC mC sC cP cTL cT cA kO kN kE kL
    kM kS kC kP kTL kT kA fO fN fE fL fM fS fC fP fTL fT kv olk el1 elK scrK rlK
  have hl := h H hH
  rw [hl] at hrd oS sC kS fS
  have h288 : 288 ≤ s.sp.toNat := hsp
  have r1 : s.gpr .r1 = s.gpr .r3 := BitVec.eq_of_toNat_eq olk
  rw [olk] at hwr oN oE oL oM oS oC oP oTL oT oA kO fO
  have hpush : Frame [FrameStack.belowA s.sp 56] s.mem (entered frameBytes s).mem :=
    FrameStack.pushed_frameA (rs := Impl.RsaPkcs1Sig.Arm.pushRegs) (by show 56 ≤ s.sp.toNat; omega_arith)
  have below : Region.Sub (FrameStack.belowA s.sp 56) ⟨State.addr s.sp - BitVec.ofNat 64 288, 288⟩ := by
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

end

end

/-!
# RSAES-OAEP encryption with a precomputed public key on ARMv7: the checks

`chk_vp`: `scratch` to its slot, and the flags of whether the message fits
(`fits`), from the lengths alone. `fail_vp`: when it does not, zeros to
`out` and 0 returned, as `encrypt` (`Proof.RsaOaep.encrypt_none`) says.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm.Enc

open VG VG.Arm VG.Impl.RsaOaep.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm VG.Proof.RsaOaep.Arm
open VG.Impl.RsaPss.Arm (sp0 ld st mw atS frameBytes sS oRsa arg)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)

variable (h g : OHash)

/-- A state of the body. -/
abbrev S (P : EP) (σ s : State) : Prop := In h.H.D P σ ∧ (P.lay h.H.D).St σ s

/-- The label, the message and the seed, as they are in the run from `σ`. -/
abbrev labB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.lab) P.ll
abbrev msgB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.msg) P.ml
abbrev seedB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.seed) h.H.D

/-- Whether the message fits. -/
abbrev fits (P : EP) : Prop := 2 * h.H.D + 2 + P.ml ≤ P.K

/-- What the function writes to `out` and returns. -/
abbrev Res (P : EP) (σ : State) (m : Mem) (r : BitVec 32) : Prop :=
  Spec.Rsa.publicPrecompute P.nB = some P.pw →
    Spec.Rsa.written m (State.addr P.out) P.K r (Spec.RsaOaep.encrypt h.G g.G P.nB P.eB (labB P σ) (msgB P σ)
      (seedB h P σ))

/-- The end of the body. -/
abbrev Fin (P : EP) (σ s : State) : Prop := S h P σ s ∧ Res h g P σ s.mem (s.gpr .r0)

theorem arg_lt {j : Nat} (hj : j < 18) : arg j < 4096 := by
  unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes; split <;> omega_arith

/-- An argument: its place, readable, and its value. -/
theorem argAt {D : Nat} {P : EP} {σ s : State} (hi : In D P σ) (hs : (P.lay D).St σ s) {j : Nat} (hj : j < 18) :
    State.addr (P.B + BitVec.ofNat 32 (arg j)) = (P.lay D).fr (arg j) ∧
    InRegions (s.rd ++ s.wr) ((P.lay D).fr (arg j)) 4 ∧
    s.mem.readW ((P.lay D).fr (arg j)) 32 = P.argv.getD j 0 := by
  have hl : j < (P.lay D).argv.length := by simp only [EP.argv, List.length_cons, List.length_nil]; omega_arith
  exact ⟨hi.ok.addrB (by
      show arg j < frameBytes + 56 + 56; unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes; split <;> omega_arith),
    by rw [hs.rd, hs.wr]; exact hi.ok.arg_read hl, hs.arg hl⟩

/-- A slot, written with `r12 = sp`. -/
theorem slotAt {D : Nat} {P : EP} {σ : State} (hi : In D P σ) {d : Nat} (hd : d + 4 ≤ frameBytes) :
    State.addr (P.B + BitVec.ofNat 32 d) = (P.lay D).fr d :=
  hi.ok.addrB (by show d < frameBytes + 56 + 56; unfold frameBytes at hd ⊢; omega_arith)

/-- The flags of the checks: zero exactly when `c + ml ≤ K`. -/
theorem chk_z {K c ml : Nat} (hK : K ≤ 1024) (hc1 : 1 ≤ c) (hc : c ≤ 1024) (hml : ml < 2 ^ 32) :
    (((BitVec.ofNat 32 K - BitVec.ofNat 32 c) >>> 31 ||| BitVec.ofNat 32 ml >>> 10 |||
      (BitVec.ofNat 32 K - BitVec.ofNat 32 c - BitVec.ofNat 32 ml) >>> 31) - 0 == 0) = decide (c + ml ≤ K) := by
  simp only [BitVec.ofNat_eq_ofNat, BitVec.sub_zero]
  by_cases hcK : c ≤ K
  · rw [Offset.ofNat_sub_ofNat (w := 32) hcK]
    have z1 : BitVec.ofNat 32 (K - c) >>> 31 = 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; simp; omega_arith
    by_cases hm : ml < 1024
    · have z2 : BitVec.ofNat 32 ml >>> 10 = 0 := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; simp; omega_arith
      rw [z1, z2, ltBit (a := K - c) (b := ml) (by omega_arith) (by omega_arith)]
      by_cases e : K - c < ml
      · simp [e]; omega_arith
      · simp [e]; omega_arith
    · have hne : BitVec.ofNat 32 ml >>> 10 ≠ 0 := fun e => by
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow] at this; simp at this; omega_arith
      rw [decide_eq_false (by omega_arith)]
      exact beq_false_of_ne fun e => hne ((or_eq_zero32 _ _).1 ((or_eq_zero32 _ _).1 e).1).2
  · have hne : (BitVec.ofNat 32 K - BitVec.ofNat 32 c) >>> 31 ≠ 0 := fun e => by
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (a := K) (by omega_arith), Nat.mod_eq_of_lt (a := c) (by omega_arith)] at this
      simp at this; omega_arith
    rw [decide_eq_false (by omega_arith)]
    exact beq_false_of_ne fun e => hne ((or_eq_zero32 _ _).1 ((or_eq_zero32 _ _).1 e).1).1

/-! ## The checks -/

/-- After `encChk`. -/
abbrev C0 (P : EP) (σ s : State) : Prop :=
  Ctx (P.lay h.H.D) P.scr σ s ∧ In h.H.D P σ ∧ s.z = decide (fits h P)

theorem chk_vp (P : EP) : VP (S h P) (.block (encChk h.H)) (C0 h P) := by
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.2.sp.trans h₂.2.sp.symm) fun σ s ⟨hi, hs⟩ => ?_
  have hD := h.D_le
  have hK := hi.k1024
  obtain ⟨a12, r12, v12⟩ := argAt hi hs (j := 12) (by decide)
  obtain ⟨a3, r3, v3⟩ := argAt hi hs (j := 3) (by decide)
  obtain ⟨a9, r9, v9⟩ := argAt hi hs (j := 9) (by decide)
  replace v12 : s.mem.readW ((P.lay h.H.D).fr (arg 12)) 32 = P.scr := v12
  replace v3 : s.mem.readW ((P.lay h.H.D).fr (arg 3)) 32 = BitVec.ofNat 32 P.K := v3
  replace v9 : s.mem.readW ((P.lay h.H.D).fr (arg 9)) 32 = BitVec.ofNat 32 P.ml := v9
  have k : ∀ (j : Nat) (v : BitVec 32), j < 18 →
      (s.mem.writeW ((P.lay h.H.D).fr sS) v).readW ((P.lay h.H.D).fr (arg j)) 32 =
        s.mem.readW ((P.lay h.H.D).fr (arg j)) 32 :=
    fun j v hj => Lay.readW_fr_other _ _ _ (by
      unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes sS; split <;> omega_arith) (by
      unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes; split <;> omega_arith) (by decide)
  have hw : WP isa (.block (encChk h.H)) s fun t => t.mem = s.mem.writeW ((P.lay h.H.D).fr sS) P.scr ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.z = decide (fits h P) := by
    prun [encChk, sp0, ld, st, mw, hs.sp, a12, r12, v12, a3, r3, v3, a9, r9, v9, k 3 _ (by decide),
      k 9 _ (by decide), slotAt hi (d := sS) (by decide), hs.inFr (d := sS) (n := 4) (by show sS + 4 ≤ frameBytes; decide),
      arg_lt, movw_val (show 2 * h.H.D + 2 < 2 ^ 16 by omega_arith), dpVal, chk_z hK (show 1 ≤ 2 * h.H.D + 2 by omega_arith) (show 2 * h.H.D + 2 ≤ 1024 by omega_arith) hi.ml32]
  refine WP.mono hw fun t ⟨m, rd, wr, sp, z⟩ => ⟨⟨?_, ?_⟩, hi, z⟩
  · exact hs.frameW (d := sS) (n := 4) (by show sS + 4 ≤ frameBytes; decide) (by
      rw [m]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)) rd wr sp
  · rw [m, Mem.readW_writeW_self32]

/-! ## A message that does not fit -/

theorem out_wbuf {P : EP} {σ : State} (hi : In h.H.D P σ) : WBuf (P.lay h.H.D) P.out P.K := by
  have hK := hi.k1024
  have hf := hi.ok.fits P.OUT (by simp)
  simp only [Proof.X25519.Arm.addr_toNat] at hf
  exact ⟨hf, by omega_arith, ⟨P.OUT, by simp, Region.contains_self _ _⟩,
    hi.ok.stk_fr (R := P.OUT) (.inr (by simp)) (d := sS) (n := 4) (by show sS + 4 ≤ frameBytes + 56; decide)⟩

theorem nB_length {D : Nat} {P : EP} {σ : State} (hi : In D P σ) : P.nB.length = P.K := by
  rw [← hi.nB]; simp [Spec.Rsa.bytesAt]

theorem msgB_length (P : EP) (σ : State) : (msgB P σ).length = P.ml := by simp [Spec.Rsa.bytesAt]

theorem fail_vp (P : EP) :
    VP (fun σ s => C0 h P σ s ∧ isa.eval .ne s = some true) (encFail) (Fin h g P) := by
  by_cases hP : ∃ σ, In h.H.D P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1.2.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  have hb := out_wbuf h hi₀
  have hK := hi₀.k64
  show VP _ (.seq (.block [sp0, ld .r0 (arg 0), ld .lr (arg 3), mw .r2 0]) (.seq Impl.Bignum.Arm.maskBytes
    (.block [mw .r0 0]))) _
  refine VP.seq (G := fun σ s => (Ctx (P.lay h.H.D) P.scr σ s ∧ (In h.H.D P σ ∧ ¬ fits h P)) ∧ s.gpr .r0 = P.out ∧
      s.gpr .r2 = 0 ∧ s.gpr .lr = BitVec.ofNat 32 P.K)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.1.st.sp.trans h₂.1.1.st.sp.symm)
      fun σ s ⟨⟨hc, hi, z⟩, e⟩ => ?_) ?_
  · have nf : ¬ fits h P := by
      intro hf
      rw [VG.Proof.X25519.Arm.eval_ne, z, decide_eq_true hf] at e
      cases e
    obtain ⟨a0, r0, v0⟩ := argAt hi hc.st (j := 0) (by decide)
    obtain ⟨a3, r3, v3⟩ := argAt hi hc.st (j := 3) (by decide)
    replace v0 : s.mem.readW ((P.lay h.H.D).fr (arg 0)) 32 = P.out := v0
    replace v3 : s.mem.readW ((P.lay h.H.D).fr (arg 3)) 32 = BitVec.ofNat 32 P.K := v3
    have hw : WP isa (.block [sp0, ld .r0 (arg 0), ld .lr (arg 3), mw .r2 0]) s fun t => t.mem = s.mem ∧
        t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.gpr .r0 = P.out ∧ t.gpr .r2 = 0 ∧
        t.gpr .lr = BitVec.ofNat 32 P.K := by
      prun [sp0, ld, mw, hc.st.sp, a0, r0, v0, a3, r3, v3, arg_lt]
    exact WP.mono hw fun t ⟨m, rd, wr, sp, t0, t2, tl⟩ => ⟨⟨hc.regs rd wr sp m, hi, nf⟩, t0, t2, tl⟩
  refine VP.seq ((zero_vp hb (by omega_arith) (Inv := fun σ _ => In h.H.D P σ ∧ ¬ fits h P)
    fun σ m m' hm _ => hm).mono (fun σ s ⟨⟨hc, hm⟩, r0, r2, lr⟩ => ⟨hc, hm, r0, r2, lr⟩) fun _ _ h => h) ?_
  refine VP.taint [] ⟨_, by taint_decide⟩ (fun _ _ _ _ _ _ r hr => by simp at hr)
    fun σ s ⟨hc, ⟨hi, nf⟩, hz⟩ => ?_
  apply WP.of_runBlock
  simp only [mw, runBlock_cons, runStep_some, runBlock_nil, exec]
  refine ⟨_, rfl, ⟨hi, hc.st.regs rfl rfl rfl rfl⟩, fun _ => ?_⟩
  have en : Spec.RsaOaep.encrypt h.G g.G P.nB P.eB (labB P σ) (msgB P σ) (seedB h P σ) = none :=
    Proof.RsaOaep.encrypt_none (by rw [nB_length hi, msgB_length, h.glen]; simp only [fits] at nf; omega_arith)
  rw [en]
  refine ⟨by simp [VG.Arm.RegUpd.gpr_setReg], ?_⟩
  apply List.ext_getElem (by simp [Spec.Rsa.bytesAt])
  intro i h1 _
  simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at h1
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
  exact hz i h1

end VG.Proof.RsaOaep.Arm.Enc

end

end

/-!
# RSAES-OAEP encryption with a precomputed public key on ARMv7: `EM` before masking

When the message fits: `EM`'s `k` bytes at `scratch + oEm` cleared, the
seed after its first byte, the label's hash, through its table (`em3_vp`),
after the seed, `0x01` before the message and the message at its end:
`EM = 0x00 ‖ seed ‖ lHash ‖ 0… ‖ 0x01 ‖ M` (`Proof.RsaOaep.EmAt`, `em_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm.Enc

open VG VG.Arm VG.Impl.RsaOaep.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm VG.Proof.RsaOaep.Arm
open VG.Impl.RsaPss.Arm (sp0 ld st mw atS frameBytes sS oRsa arg put1)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)

variable (h : OHash)

/-- A state of the body when the message fits. -/
abbrev E0 (P : EP) (σ s : State) : Prop := Ctx (P.lay h.H.D) P.scr σ s ∧ In h.H.D P σ ∧ fits h P

/-- `EM`'s bytes, from the memory. -/
abbrev emV (scr : BitVec 32) (m : Mem) (o : Nat) : Byte := m (sa scr (oEm + o))

/-- The label's hash. -/
abbrev lhB (P : EP) (σ : State) : List Byte := h.G.hash (labB P σ)

/-- The facts that do not change in the body. -/
abbrev K0 (P : EP) (σ : State) : Prop := In h.H.D P σ ∧ fits h P

/-- The arguments read in this file. -/
theorem argV {P : EP} {σ s : State} (hi : In h.H.D P σ) (hs : (P.lay h.H.D).St σ s) :
    (State.addr (P.B + BitVec.ofNat 32 (arg 3)) = (P.lay h.H.D).fr (arg 3) ∧
      InRegions (s.rd ++ s.wr) ((P.lay h.H.D).fr (arg 3)) 4 ∧
      s.mem.readW ((P.lay h.H.D).fr (arg 3)) 32 = BitVec.ofNat 32 P.K) ∧
    (State.addr (P.B + BitVec.ofNat 32 (arg 8)) = (P.lay h.H.D).fr (arg 8) ∧
      InRegions (s.rd ++ s.wr) ((P.lay h.H.D).fr (arg 8)) 4 ∧ s.mem.readW ((P.lay h.H.D).fr (arg 8)) 32 = P.msg) ∧
    (State.addr (P.B + BitVec.ofNat 32 (arg 9)) = (P.lay h.H.D).fr (arg 9) ∧
      InRegions (s.rd ++ s.wr) ((P.lay h.H.D).fr (arg 9)) 4 ∧
      s.mem.readW ((P.lay h.H.D).fr (arg 9)) 32 = BitVec.ofNat 32 P.ml) ∧
    (State.addr (P.B + BitVec.ofNat 32 (arg 10)) = (P.lay h.H.D).fr (arg 10) ∧
      InRegions (s.rd ++ s.wr) ((P.lay h.H.D).fr (arg 10)) 4 ∧
      s.mem.readW ((P.lay h.H.D).fr (arg 10)) 32 = P.seed) :=
  ⟨argAt hi hs (by decide), argAt hi hs (by decide), argAt hi hs (by decide), argAt hi hs (by decide)⟩

/-! ## The pieces -/

/-- `EM` cleared. -/
abbrev Z1 (P : EP) (m : Mem) : Prop := ∀ i < P.K, emV P.scr m i = 0

theorem em1_vp (P : EP) :
    VP (E0 h P) (.seq (.block clrEm) Impl.Bignum.Arm.maskBytes) (fun σ s => E0 h P σ s ∧ Z1 P s.mem) := by
  by_cases hP : ∃ σ, In h.H.D P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.2.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  have hK := hi₀.k1024
  have hK0 := hi₀.k64
  refine VP.seq (G := fun σ s => (Ctx (P.lay h.H.D) P.scr σ s ∧ K0 h P σ) ∧ s.gpr .r0 = P.scr + BitVec.ofNat 32 oEm ∧
      s.gpr .r2 = 0 ∧ s.gpr .lr = BitVec.ofNat 32 P.K)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hi, hf⟩ => ?_)
    ((zero_vp (hg.wbuf (o := oEm) (n := P.K) (by oomega) (by omega_using [hK0])) (by omega_using [hK0]) (Inv := fun σ _ => K0 h P σ)
      fun σ m m' hm _ => hm).mono (fun σ s ⟨⟨hc, hm⟩, r0, r2, lr⟩ => ⟨hc, hm, r0, r2, lr⟩)
      fun σ s ⟨hc, hm, hz⟩ => ⟨⟨hc, hm⟩, fun i hi => by rw [emV, ← hg.byteAt_scr (by oomega)]; exact hz i hi⟩)
  obtain ⟨⟨a3, r3, v3⟩, -⟩ := argV h hi hc.st
  have hw : WP isa (.block clrEm) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.gpr .r0 = P.scr + BitVec.ofNat 32 oEm ∧ t.gpr .r2 = 0 ∧ t.gpr .lr = BitVec.ofNat 32 P.K := by
    prun [clrEm, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, a3, r3, v3, arg_lt,
      movw_val (show oEm < 2 ^ 16 by decide)]
  exact WP.mono hw fun t ⟨m, rd, wr, sp, r0, r2, lr⟩ => ⟨⟨hc.regs rd wr sp m, hi, hf⟩, r0, r2, lr⟩

/-- The seed after `EM`'s first byte, zeros elsewhere. -/
abbrev Z2 (P : EP) (sd : List Byte) (m : Mem) : Prop :=
  emV P.scr m 0 = 0 ∧ (∀ i < h.H.D, emV P.scr m (1 + i) = sd.getD i 0) ∧
    ∀ i, 1 + h.H.D ≤ i → i < P.K → emV P.scr m i = 0

/-- The seed's bytes, in a state of the body. -/
theorem seed_bytes {P : EP} {σ s : State} (hs : (P.lay h.H.D).St σ s) :
    ∀ i < h.H.D, s.mem (byteAt P.seed i) = (seedB h P σ).getD i 0 := by
  intro i hi
  have e := hs.ro (R := P.SEED h.H.D) (by simp)
  have e2 := congrArg (fun l => l.getD i 0) e
  simp only [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some] at e2
  simp only [seedB, Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some, byteAt]
  exact e2

theorem em2_vp (P : EP) :
    VP (fun σ s => E0 h P σ s ∧ Z1 P s.mem) (.seq (.block (seedSet h.H)) Impl.Bignum.Arm.copyBytes)
      (fun σ s => E0 h P σ s ∧ Z2 h P (seedB h P σ) s.mem) := by
  by_cases hP : ∃ σ, In h.H.D P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1.2.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  have hK := hi₀.k1024
  have hD := h.D_le
  have hD0 := h.D_pos
  obtain ⟨σ', ok⟩ := hg.ok
  have hsd : RBuf (P.lay h.H.D) P.seed h.H.D := by
    have hf := hi₀.ok.fits (P.SEED h.H.D) (by simp)
    simp only [Proof.X25519.Arm.addr_toNat] at hf
    exact ⟨hf, by omega_using [hD], ⟨P.SEED h.H.D, by simp, Region.contains_self _ _⟩⟩
  have sep : Region.Disjoint ⟨State.addr P.seed, h.H.D⟩ ⟨State.addr (P.scr + BitVec.ofNat 32 (oEm + 1)), h.H.D⟩ := by
    rw [hg.addr (by oomega)]
    exact (ok.rw_ro (w := P.SCR) (r := P.SEED h.H.D) (by simp) (by simp)).symm.sub_right
      (Offset.sub_base _ (by have := hi₀.pubScr.2; oomega))
  -- What the copy keeps: `EM`'s other bytes, zero.
  let X : State → Mem → Prop := fun σ m => K0 h P σ ∧ emV P.scr m 0 = 0 ∧
    ∀ i, 1 + h.H.D ≤ i → i < P.K → emV P.scr m i = 0
  refine VP.seq (G := fun σ s => (Ctx (P.lay h.H.D) P.scr σ s ∧ X σ s.mem) ∧
      s.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + 1) ∧ s.gpr .r1 = P.seed ∧ s.gpr .lr = BitVec.ofNat 32 h.H.D ∧
      ∀ i < h.H.D, s.mem (byteAt P.seed i) = (seedB h P σ).getD i 0)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.1.st.sp.trans h₂.1.1.st.sp.symm)
      fun σ s ⟨⟨hc, hi, hf⟩, hz⟩ => ?_)
    ((copy_vp (hg.wbuf (o := oEm + 1) (n := h.H.D) (by oomega) hD0) hsd sep hD0 (Inv := X)
      (f := fun σ i => (seedB h P σ).getD i 0) fun σ m m' ⟨k, z0, zr⟩ hf => ?_).mono
      (fun σ s ⟨⟨hc, hm⟩, r0, r1, lr, hb⟩ => ⟨hc, hm, r0, r1, lr, hb⟩)
      fun σ s ⟨hc, ⟨k, z0, zr⟩, hb⟩ => ⟨⟨hc, k⟩, z0, fun i hi => ?_, zr⟩)
  · obtain ⟨-, -, -, ⟨a10, r10, v10⟩⟩ := argV h hi hc.st
    have hw : WP isa (.block (seedSet h.H)) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + 1) ∧ t.gpr .r1 = P.seed ∧ t.gpr .lr = BitVec.ofNat 32 h.H.D := by
      prun [seedSet, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, a10, r10, v10, arg_lt,
        movw_val (show oEm + 1 < 2 ^ 16 by decide), movw_val (show h.H.D < 2 ^ 16 by omega_using [hD])]
    refine WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1, lr⟩ => ⟨⟨hc.regs rd wr sp m, ⟨hi, hf⟩, ?_, fun i h1 h2 => ?_⟩,
      r0, r1, lr, ?_⟩
    · rw [emV, m]; exact hz 0 (by omega)
    · rw [emV, m]; exact hz i h2
    · rw [m]; exact seed_bytes h hc.st
  · rw [hg.addr (by oomega)] at hf
    refine ⟨k, ?_, fun i h1 h2 => ?_⟩
    · rw [emV, ← z0]
      exact hf _ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Geo.sep (scr := P.scr) (o := oEm + 0) (n := 1) (by oomega) (by oomega) (by oomega) _
          (Region.contains_self _ _)
    · rw [emV, ← zr i h1 h2]
      exact hf _ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Geo.sep (scr := P.scr) (o := oEm + i) (n := 1) (by oomega) (by oomega) (by oomega) _
          (Region.contains_self _ _)
  · rw [emV, show oEm + (1 + i) = oEm + 1 + i by oomega, ← hg.byteAt_scr (by oomega)]
    exact hb i hi

/-! ## `EM`'s bytes as functions -/

/-- `EM`'s first `k` bytes are `f`. -/
abbrev EMv (P : EP) (m : Mem) (f : Nat → Byte) : Prop := ∀ i < P.K, emV P.scr m i = f i

/-- `EM` with the seed. -/
abbrev e2 (P : EP) (σ : State) (i : Nat) : Byte :=
  if 1 ≤ i ∧ i < 1 + h.H.D then (seedB h P σ).getD (i - 1) 0 else 0

/-- `EM` with the seed and `lHash`. -/
abbrev e3 (P : EP) (σ : State) (i : Nat) : Byte :=
  if 1 + h.H.D ≤ i ∧ i < 1 + 2 * h.H.D then (lhB h P σ).getD (i - (1 + h.H.D)) 0 else e2 h P σ i

/-- `EM` with `0x01`. -/
abbrev e4 (P : EP) (σ : State) (i : Nat) : Byte := if i = P.K - P.ml - 1 then 1 else e3 h P σ i

/-- `EM` before masking. -/
abbrev e5 (P : EP) (σ : State) (i : Nat) : Byte :=
  if P.K - P.ml ≤ i ∧ i < P.K then (msgB P σ).getD (i - (P.K - P.ml)) 0 else e4 h P σ i

theorem z2_emv {P : EP} {σ : State} {m : Mem} (hz : Z2 h P (seedB h P σ) m) : EMv P m (e2 h P σ) := by
  intro i hi
  obtain ⟨z0, sd, zr⟩ := hz
  simp only [e2]
  by_cases h1 : 1 ≤ i ∧ i < 1 + h.H.D
  · rw [ite_eq_left h1, show i = 1 + (i - 1) by omega_using [h1], sd _ (by omega_using [h1]), Nat.add_sub_cancel_left]
  · rw [ite_eq_right h1]
    by_cases h0 : i = 0
    · subst h0; exact z0
    · exact zr i (by omega_using [h1, h0]) hi

theorem add_ofNat_sub {x : BitVec 32} {a b : Nat} (hb : b ≤ a) :
    x + BitVec.ofNat 32 a - BitVec.ofNat 32 b = x + BitVec.ofNat 32 (a - b) := by
  have : BitVec.ofNat 32 a = BitVec.ofNat 32 (a - b) + BitVec.ofNat 32 b := by
    rw [BitVec.ofNat_add_ofNat, Nat.sub_add_cancel hb]
  rw [this, ← BitVec.add_assoc, BitVec.add_sub_cancel]

theorem add_ofNat_sub_one {x : BitVec 32} {a : Nat} (ha : 1 ≤ a) :
    x + BitVec.ofNat 32 a - 1 = x + BitVec.ofNat 32 (a - 1) := add_ofNat_sub ha

/-- `EM`'s bytes, kept by a write elsewhere in our part of `scratch`. -/
theorem emv_keep {P : EP} (hg : Geo (P.lay h.H.D) P.scr) (hK : P.K ≤ 1024) {m m' : Mem} {f : Nat → Byte}
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, (∃ o n, oBuf ≤ o ∧ o + n ≤ oRsa ∧ r = sR P.scr o n) ∨
      r = (P.lay h.H.D).LOW) (he : EMv P m f) : EMv P m' f := by
  obtain ⟨σ', ok⟩ := hg.ok
  intro i hi
  rw [emV, ← he i hi]
  refine hf _ fun r hr => ?_
  rcases hd r hr with ⟨o, n, h1, h2, rfl⟩ | rfl
  · exact Geo.sep (scr := P.scr) (o := oEm + i) (n := 1) (by oomega) (by oomega) h2 _ (Region.contains_self _ _)
  · exact hg.low ok (o := oEm + i) (n := 1) (by oomega) _ (Region.contains_self _ _)

/-- The label's hash function's table, the argument 16, in a buffer only
read. -/
theorem tblL_of {D : Nat} {P : EP} {σ : State} (hi : In D P σ) :
    ∃ R ∈ (P.lay D).ro, ∀ o, o + 4 ≤ 44 → R.Contains (tA P.tabL o) 4 := by
  have hf := hi.ok.fits P.TABL (by simp)
  simp only [Sig.tableRegion, Proof.X25519.Arm.addr_toNat] at hf
  refine ⟨P.TABL, by simp, fun o ho => ?_⟩
  show (⟨State.addr P.tabL, 11 * (32 / 8)⟩ : Region).Contains (State.addr (P.tabL + BitVec.ofNat 32 o)) 4
  rw [VG.Arm.addr_add (by omega_using [hf, ho])]
  exact Offset.contains_base _ (by omega_using [ho]) (by omega_using [ho])

/-- What the label's hash keeps, with its table's address in its slot. -/
abbrev L0 (P : EP) (σ : State) (m : Mem) : Prop :=
  (K0 h P σ ∧ EMv P m (e2 h P σ)) ∧ m.readW ((P.lay h.H.D).fr sTab) 32 = P.tabL

/-- The label's hash function's table's address to its slot, and the label's
hash at `oDig`, with that table's hash function `h`. -/
theorem em3_vp (P : EP) {f : Fns} (hTL : ∀ σ, P.TL σ → TabFacts h.H f P.tabL P.aiL P.auL P.afL σ)
    (fne : f.init ≠ [] ∧ f.upd ≠ [] ∧ f.fin ≠ []) :
    VP (fun σ s => (E0 h P σ s ∧ Z2 h P (seedB h P σ) s.mem) ∧ s.syms = σ.syms)
      (.seq (.block (tabSlot 16)) (hashLabelT f 6 oDig))
      (fun σ s => (E0 h P σ s ∧ EMv P s.mem (e2 h P σ) ∧
        ∀ i < h.H.D, s.mem (sa P.scr (oDig + i)) = (lhB h P σ).getD i 0) ∧ s.syms = σ.syms) := by
  by_cases hP : ∃ σ, In h.H.D P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1.1.2.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  have hK := hi₀.k1024
  have := h.S_le; have := h.Wb_le; have := h.F_le; have := h.D_le
  obtain ⟨σ', ok⟩ := hg.ok
  have hl := hi₀.ok.fits P.LAB (by simp)
  simp only [Proof.X25519.Arm.addr_toNat] at hl
  have hlab : RBuf (P.lay h.H.D) P.lab P.ll := ⟨hl, hi₀.ll32, ⟨P.LAB, by simp, Region.contains_self _ _⟩⟩
  have dS : ∀ {o n : Nat}, o + n ≤ oRsa → Region.Disjoint ⟨State.addr P.lab, P.ll⟩ (sR P.scr o n) :=
    fun hon => (hg.ro ok hon (R := P.LAB) (by simp)).symm
  -- The table's address to its slot.
  refine VP.seq (G := fun σ s => (Ctx (P.lay h.H.D) P.scr σ s ∧ L0 h P σ s.mem) ∧ s.syms = σ.syms)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.1.1.st.sp.trans h₂.1.1.1.st.sp.symm)
      fun σ s ⟨⟨⟨hc, hi, hf⟩, hz⟩, sy⟩ => ?_) ?_
  · refine WP.mono (tabA_wp hg hc (j := 16) (by simp) (arg_lt (by decide))) fun t ⟨m, rd, wr, sp, _, _, ty⟩ => ?_
    have fr : Frame [slotR (P.lay h.H.D) sTab] s.mem t.mem := by rw [m]; exact slot_frame _ _ _ _
    refine ⟨⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp, ⟨⟨hi, hf⟩, fun i hi' => ?_⟩, ?_⟩,
      ty.trans sy⟩
    · rw [List.mem_singleton.mp hr]; exact slotW hg (by decide)
    · rw [List.mem_singleton.mp hr]; exact slotSep (by decide) (by decide) (by decide)
    · rw [emV, ← z2_emv h hz i hi']
      refine fr _ fun r hr => ?_
      rw [List.mem_singleton.mp hr]
      exact (hg.slot ok (o := oEm + i) (n := 1) (by oomega) (by rw [hg.F]; decide)).symm _
        (Region.contains_self _ _)
    · rw [m, Mem.readW_writeW_self32]; rfl
  -- The label's hash.
  refine (labelT_vp hg h (f := f) (p := P.tabL) (ai := P.aiL) (au := P.auL) (af := P.afL) (tblL_of hi₀) fne
    (j := 6) (o := oDig) (ll := P.ll) (lab := P.lab) (by simp) (arg_lt (by decide))
    (arg_lt (by decide)) rfl rfl hlab (dS (by oomega)) (dS (by oomega))
    (ok.low_buf (R := P.LAB) (.inl (by simp))).symm (by oomega) (by oomega) (labB := labB P)
    (fun σ s hc => hc.st.ro (R := P.LAB) (by simp))
    (Inv := L0 h P) ?_ (fun _ _ hm => hm.2) (fun σ _ hm => hTL σ hm.1.1.1.tabTL)).mono
    (fun _ _ h => h) fun σ s ⟨⟨hc, ⟨⟨⟨hi, hf⟩, he⟩, _⟩, hd⟩, sy⟩ => ⟨⟨⟨hc, hi, hf⟩, he, hd⟩, sy⟩
  intro σ m m' ⟨⟨k, he⟩, hs⟩ hf
  refine ⟨⟨k, emv_keep h hg hK hf (fun r hr => ?_) he⟩, slot_keep hf (fun r hr => ?_) hs⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact .inl ⟨oSt, h.H.S, by oomega, by oomega, rfl⟩
    · exact .inl ⟨oW, h.ok.Wb, by oomega, by oomega, rfl⟩
    · exact .inr rfl
    · exact .inl ⟨oDig, h.H.F, by oomega, by oomega, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hg.slot ok (by oomega) (by rw [hg.F]; decide)
    · exact hg.slot ok (by oomega) (by rw [hg.F]; decide)
    · exact Lay.fr_low (by decide)
    · exact hg.slot ok (by oomega) (by rw [hg.F]; decide)

/-- `lHash` after the seed. -/
theorem em4_vp (P : EP) :
    VP (fun σ s => E0 h P σ s ∧ EMv P s.mem (e2 h P σ) ∧
        ∀ i < h.H.D, s.mem (sa P.scr (oDig + i)) = (lhB h P σ).getD i 0)
      (.seq (.block (lhSet h.H)) Impl.Bignum.Arm.copyBytes)
      (fun σ s => E0 h P σ s ∧ EMv P s.mem (e3 h P σ)) := by
  by_cases hP : ∃ σ, In h.H.D P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1.2.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  have hK := hi₀.k1024
  have hD := h.D_le
  have hD0 := h.D_pos
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s hs => hf hs.1.2.2
  have hfit : 2 * h.H.D + 2 + P.ml ≤ P.K := hf
  let X : State → Mem → Prop := fun σ m => K0 h P σ ∧
    ∀ i < P.K, (i < 1 + h.H.D ∨ 1 + 2 * h.H.D ≤ i) → emV P.scr m i = e2 h P σ i
  have sp4 : Region.Disjoint ⟨State.addr (P.scr + BitVec.ofNat 32 oDig), h.H.D⟩
      ⟨State.addr (P.scr + BitVec.ofNat 32 (oEm + 1 + h.H.D)), h.H.D⟩ := by
    rw [hg.addr (by oomega), hg.addr (by oomega)]
    exact Geo.sep (by oomega) (by oomega) (by oomega)
  refine VP.seq (G := fun σ s => (Ctx (P.lay h.H.D) P.scr σ s ∧ X σ s.mem) ∧
      s.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + 1 + h.H.D) ∧ s.gpr .r1 = P.scr + BitVec.ofNat 32 oDig ∧
      s.gpr .lr = BitVec.ofNat 32 h.H.D ∧
      ∀ i < h.H.D, s.mem (byteAt (P.scr + BitVec.ofNat 32 oDig) i) = (lhB h P σ).getD i 0)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.1.st.sp.trans h₂.1.1.st.sp.symm)
      fun σ s ⟨⟨hc, hi, _⟩, he, hd⟩ => ?_)
    ((copy_vp (hg.wbuf (o := oEm + 1 + h.H.D) (n := h.H.D) (by oomega) hD0) (hg.rbuf (o := oDig) (n := h.H.D)
      (by oomega) hD0) sp4 hD0 (Inv := X) (f := fun σ i => (lhB h P σ).getD i 0) fun σ m m' ⟨k, ho⟩ hf' => ?_).mono
      (fun σ s ⟨⟨hc, hm⟩, r0, r1, lr, hb⟩ => ⟨hc, hm, r0, r1, lr, hb⟩)
      fun σ s ⟨hc, ⟨k, ho⟩, hb⟩ => ⟨⟨hc, k⟩, fun i hi => ?_⟩)
  · have hw : WP isa (.block (lhSet h.H)) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + 1 + h.H.D) ∧ t.gpr .r1 = P.scr + BitVec.ofNat 32 oDig ∧
        t.gpr .lr = BitVec.ofNat 32 h.H.D := by
      prun [lhSet, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS,
        movw_val (show oEm + 1 + h.H.D < 2 ^ 16 by oomega), movw_val (show oDig < 2 ^ 16 by decide),
        movw_val (show h.H.D < 2 ^ 16 by omega_using [hD])]
    refine WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1, lr⟩ => ⟨⟨hc.regs rd wr sp m, ⟨hi, hf⟩, fun i hi _ => ?_⟩,
      r0, r1, lr, fun i hi => ?_⟩
    · rw [m]; exact he i hi
    · rw [m, hg.byteAt_scr (by oomega)]; exact hd i hi
  · rw [hg.addr (by oomega)] at hf'
    refine ⟨k, fun i hi hr => ?_⟩
    rw [emV, ← ho i hi hr]
    exact hf' _ fun r hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact Geo.sep (scr := P.scr) (o := oEm + i) (n := 1) (by oomega) (by oomega) (by oomega) _
        (Region.contains_self _ _)
  · simp only [e3]
    by_cases hr : 1 + h.H.D ≤ i ∧ i < 1 + 2 * h.H.D
    · rw [ite_eq_left hr, emV, show oEm + i = oEm + 1 + h.H.D + (i - (1 + h.H.D)) by oomega,
        ← hg.byteAt_scr (by oomega)]
      exact hb _ (by omega_using [hr])
    · rw [ite_eq_right hr]; exact ho i hi (by omega_using [hr])

theorem put1_cert : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0, .lr])
    (.block put1) hc).isSome = true := ⟨_, by taint_decide⟩

/-- `0x01` before the message's place at the end of `EM`. -/
theorem em5_vp (P : EP) :
    VP (fun σ s => E0 h P σ s ∧ EMv P s.mem (e3 h P σ)) (.seq (.block msgPos) (.block put1))
      (fun σ s => (E0 h P σ s ∧ EMv P s.mem (e4 h P σ)) ∧
        s.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + (P.K - P.ml)) ∧ s.gpr .r1 = P.msg ∧
        s.gpr .lr = BitVec.ofNat 32 P.ml ∧ s.z = decide (P.ml = 0)) := by
  by_cases hP : ∃ σ, In h.H.D P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1.2.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  have hK := hi₀.k1024
  have hD := h.D_le
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s hs => hf hs.1.2.2
  have hfit : 2 * h.H.D + 2 + P.ml ≤ P.K := hf
  refine VP.seq (G := fun σ s => (E0 h P σ s ∧ EMv P s.mem (e3 h P σ)) ∧
      s.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + (P.K - P.ml - 1)) ∧ s.gpr .r1 = P.msg ∧
      s.gpr .lr = BitVec.ofNat 32 P.ml)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.1.st.sp.trans h₂.1.1.st.sp.symm)
      fun σ s ⟨⟨hc, hi, hf'⟩, he⟩ => ?_)
    (VP.taint _ put1_cert (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s ⟨⟨⟨hc, hi, hf'⟩, he⟩, r0, r1, lr⟩ => ?_)
  · obtain ⟨⟨a3, r3, v3⟩, ⟨a8, r8, v8⟩, ⟨a9, r9, v9⟩, -⟩ := argV h hi hc.st
    have hw : WP isa (.block msgPos) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + (P.K - P.ml - 1)) ∧ t.gpr .r1 = P.msg ∧
        t.gpr .lr = BitVec.ofNat 32 P.ml := by
      prun [msgPos, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, a3, r3, v3, a8, r8, v8, a9, r9, v9,
        arg_lt, movw_val (show oEm < 2 ^ 16 by decide), BitVec.add_assoc, BitVec.ofNat_add_ofNat,
        add_ofNat_sub (x := P.scr) (a := oEm + P.K) (b := P.ml) (by omega_using [hfit]),
        add_ofNat_sub_one (x := P.scr) (a := oEm + P.K - P.ml) (by oomega)]
      rw [show oEm + P.K - P.ml - 1 = oEm + (P.K - P.ml - 1) by oomega]
    exact WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1, lr⟩ => ⟨⟨⟨hc.regs rd wr sp m, hi, hf'⟩, m ▸ he⟩, r0, r1, lr⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2.2, h₂.2.2.2]
  · have ad : State.addr (P.scr + BitVec.ofNat 32 (oEm + (P.K - P.ml - 1))) = sa P.scr (oEm + (P.K - P.ml - 1)) :=
      hg.addr (by oomega)
    have wd : InRegions s.wr (sa P.scr (oEm + (P.K - P.ml - 1))) 1 := hg.wr hc.st (by oomega)
    have hz0 : ∀ y : BitVec 32, y - 0 = y := fun y => BitVec.sub_zero y
    have hw : WP isa (.block put1) s fun t =>
        t.mem = s.mem.writeW (sa P.scr (oEm + (P.K - P.ml - 1))) (1 : Byte) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        t.sp = s.sp ∧ t.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + (P.K - P.ml - 1) + 1) ∧
        t.gpr .r1 = P.msg ∧ t.gpr .lr = BitVec.ofNat 32 P.ml ∧ t.z = decide (P.ml = 0) := by
      prun [put1, mw, r0, r1, lr, ad, wd, movw_val (show 1 < 2 ^ 16 by decide), dpVal, hz0,
        VG.Proof.X25519.Arm.ofNat_beq_zero hi.ml32, BitVec.add_assoc, VG.Proof.Pbkdf2.Stream.Arm.ofNat_succ32]
      rfl
    refine WP.mono hw fun t ⟨m, rd, wr, sp, t0, t1, tl, z⟩ => ?_
    have fr : Frame [sR P.scr (oEm + (P.K - P.ml - 1)) 1] s.mem t.mem := by
      rw [m]; exact frame_byte P.scr _ _ (Nat.le_refl _) (by omega_using []) (by oomega)
    refine ⟨⟨⟨ctxW hg hc fr (fun r hr => .inl ⟨oEm + (P.K - P.ml - 1), 1, by oomega,
      by simpa using hr⟩) rd wr sp, hi, hf'⟩,
      fun i hi' => ?_⟩, by rw [t0, show oEm + (P.K - P.ml - 1) + 1 = oEm + (P.K - P.ml) by oomega], t1, tl, z⟩
    rw [emV, m, sa_write P.scr _ _ (by oomega) (by oomega)]
    by_cases e : i = P.K - P.ml - 1
    · rw [ite_eq_left (by omega_using [e])]; exact (ite_eq_left e).symm
    · rw [ite_eq_right (by omega_using [e])]; exact (he i hi').trans (ite_eq_right e).symm

/-- The message at the end of `EM`, if it is not empty. -/
theorem em6_vp (P : EP) :
    VP (fun σ s => (E0 h P σ s ∧ EMv P s.mem (e4 h P σ)) ∧
        s.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + (P.K - P.ml)) ∧ s.gpr .r1 = P.msg ∧
        s.gpr .lr = BitVec.ofNat 32 P.ml ∧ s.z = decide (P.ml = 0))
      (.ite .eq (.block []) Impl.Bignum.Arm.copyBytes)
      (fun σ s => E0 h P σ s ∧ EMv P s.mem (e5 h P σ)) := by
  by_cases hP : ∃ σ, In h.H.D P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1.1.2.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have hK := hi₀.k1024
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s hs => hf hs.1.1.2.2
  have hfit : 2 * h.H.D + 2 + P.ml ≤ P.K := hf
  refine VP.ite (fun _ _ _ _ h₁ h₂ => by rw [VG.Proof.X25519.Arm.eval_eq, VG.Proof.X25519.Arm.eval_eq, h₁.2.2.2.2,
      h₂.2.2.2.2]) (VP.block_nil fun σ s ⟨⟨⟨hc, he⟩, _, _, _, z⟩, e⟩ => ⟨hc, fun i hi => ?_⟩) ?_
  · have h0 : P.ml = 0 := by rw [VG.Proof.X25519.Arm.eval_eq, z] at e; simpa using e
    rw [he i hi]; exact (ite_eq_right (by omega_using [h0])).symm
  by_cases h0 : P.ml = 0
  · exact VP.empty fun σ s ⟨⟨_, _, _, _, z⟩, e⟩ => by
      rw [VG.Proof.X25519.Arm.eval_eq, z, decide_eq_true h0] at e; exact absurd e (by decide)
  have hm := hi₀.ok.fits P.MSG (by simp)
  simp only [Proof.X25519.Arm.addr_toNat] at hm
  have hmsg : RBuf (P.lay h.H.D) P.msg P.ml := ⟨hm, hi₀.ml32, ⟨P.MSG, by simp, Region.contains_self _ _⟩⟩
  refine (copy_vp (hg.wbuf (o := oEm + (P.K - P.ml)) (n := P.ml) (by oomega) (by omega_using [h0])) hmsg
    (by rw [hg.addr (by oomega)]; exact (hg.ro ok (by oomega) (R := P.MSG) (by simp)).symm)
    (by omega_using [h0]) (f := fun σ i => (msgB P σ).getD i 0)
    (Inv := fun σ m => K0 h P σ ∧ ∀ i < P.K, i < P.K - P.ml → emV P.scr m i = e4 h P σ i)
    fun σ m m' ⟨k, ho⟩ hf' => ?_).mono
    (fun σ s ⟨⟨⟨⟨hc, hi, hf'⟩, he⟩, r0, r1, lr, _⟩, _⟩ => ⟨hc, ⟨⟨hi, hf'⟩, fun i hi _ => he i hi⟩, r0, r1, lr,
      fun i hi => ?_⟩) fun σ s ⟨hc, ⟨k, ho⟩, hs⟩ => ⟨⟨hc, k⟩, fun i hi => ?_⟩
  · rw [hg.addr (by oomega)] at hf'
    refine ⟨k, fun i hi hr => ?_⟩
    rw [emV, ← ho i hi hr]
    exact hf' _ fun r hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact Geo.sep (scr := P.scr) (o := oEm + i) (n := 1) (by oomega) (by oomega) (by oomega) _
        (Region.contains_self _ _)
  · have e := (hc.st.ro (R := P.MSG) (by simp))
    have e2 := congrArg (fun l => l.getD i 0) e
    simp only [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
      Option.map_some, Option.getD_some] at e2
    simp only [msgB, Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
      Option.map_some, Option.getD_some, byteAt]
    exact e2
  · simp only [e5]
    by_cases hr : P.K - P.ml ≤ i ∧ i < P.K
    · rw [ite_eq_left hr, emV, show oEm + i = oEm + (P.K - P.ml) + (i - (P.K - P.ml)) by oomega,
        ← hg.byteAt_scr (by oomega)]
      exact hs _ (by omega_using [h0, hi])
    · rw [ite_eq_right hr]; exact ho i hi (by omega_using [hi, hr])

/-! ## `EM` -/

theorem e5_emAt {P : EP} {σ : State} (hf : fits h P) {m : Mem} (he : EMv P m (e5 h P σ)) :
    Proof.RsaOaep.EmAt (emV P.scr m) P.K h.H.D (seedB h P σ) (lhB h P σ) (msgB P σ) P.ml := by
  have hfit : 2 * h.H.D + 2 + P.ml ≤ P.K := hf
  refine ⟨?_, fun i hi => ?_, fun i hi => ?_, fun i h1 h2 => ?_, ?_, fun i hi => ?_⟩
  · rw [he 0 (by omega_using [hfit])]; simp only [e5, e4, e3, e2]
    rw [ite_eq_right (by omega_using [hfit]), ite_eq_right (by omega_using [hfit]), ite_eq_right (by omega_using []), ite_eq_right (by omega_using [])]
  · rw [he _ (by omega_using [hfit, hi])]; simp only [e5, e4, e3, e2]
    rw [ite_eq_right (by omega_using [hfit, hi]), ite_eq_right (by omega_using [hfit, hi]), ite_eq_right (by omega_using [hi]), ite_eq_left (by omega_using [hi]),
      Nat.add_sub_cancel_left]
  · rw [he _ (by omega_using [hfit, hi])]; simp only [e5, e4, e3]
    rw [ite_eq_right (by omega_using [hfit, hi]), ite_eq_right (by omega_using [hfit, hi]), ite_eq_left (by omega_using [hi]),
      show 1 + h.H.D + i - (1 + h.H.D) = i by omega_using []]
  · rw [he _ (by omega_using [h2])]; simp only [e5, e4, e3, e2]
    rw [ite_eq_right (by omega_using [h2]), ite_eq_right (by omega_using [h2]), ite_eq_right (by omega_using [h1]), ite_eq_right (by omega_using [h1])]
  · rw [he _ (by omega_using [hfit])]; simp only [e5, e4]
    rw [ite_eq_right (by omega_using [hfit])]; exact ite_eq_left trivial
  · rw [he _ (by omega_using [hfit, hi])]; simp only [e5]
    rw [ite_eq_left (by omega_using [hfit, hi]), show P.K - P.ml + i - (P.K - P.ml) = i by omega_using []]

/-- `EM` before masking, from the checks' state when the message fits. -/
theorem em_vp (P : EP) {f : Fns} (hTL : ∀ σ, P.TL σ → TabFacts h.H f P.tabL P.aiL P.auL P.afL σ)
    (fne : f.init ≠ [] ∧ f.upd ≠ [] ∧ f.fin ≠ []) :
    VP (fun σ s => E0 h P σ s ∧ s.syms = σ.syms) (encEm h.H f)
      (fun σ s => (E0 h P σ s ∧ Proof.RsaOaep.EmAt (emV P.scr s.mem) P.K h.H.D (seedB h P σ) (lhB h P σ)
        (msgB P σ) P.ml) ∧ s.syms = σ.syms) := by
  show VP _ (.seq (.block clrEm) (.seq Impl.Bignum.Arm.maskBytes (.seq (.block (seedSet h.H))
    (.seq Impl.Bignum.Arm.copyBytes (.seq (.block (tabSlot 16)) (.seq (hashLabelT f 6 oDig)
      (.seq (.block (lhSet h.H)) (.seq Impl.Bignum.Arm.copyBytes (.seq (.block msgPos) (.seq (.block put1)
        (.ite .eq (.block []) Impl.Bignum.Arm.copyBytes))))))))))) _
  exact VP.assoc (VP.seq (VP.syms (em1_vp h P)) (VP.assoc (VP.seq (VP.syms (em2_vp h P))
    (VP.assoc (VP.seq (em3_vp h P hTL fne)
    (VP.assoc (VP.seq (VP.syms (em4_vp h P)) (VP.assoc (VP.seq (VP.syms (em5_vp h P)) ((VP.syms (em6_vp h P)).mono
      (fun _ _ h => h) fun σ s ⟨⟨he0, he⟩, sy⟩ => ⟨⟨he0, e5_emAt h he0.2.2 he⟩, sy⟩))))))))))

/-! ## `EM` masked -/

/-- `EM` masked, as the specification has it. -/
abbrev emB (g : OHash) (P : EP) (σ : State) : List Byte :=
  Proof.RsaOaep.emOf g.G h.H.D P.K P.ml (seedB h P σ) (lhB h P σ) (msgB P σ)

/-- A state of the body with `EM` masked at `scratch + oEm`. -/
abbrev E1 (g : OHash) (P : EP) (σ s : State) : Prop :=
  E0 h P σ s ∧ ∀ i < P.K, emV P.scr s.mem i = (emB h g P σ).getD i 0

end VG.Proof.RsaOaep.Arm.Enc
