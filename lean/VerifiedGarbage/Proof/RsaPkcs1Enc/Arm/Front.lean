module

public import VerifiedGarbage.Impl.RsaPkcs1Enc.Arm.Front
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecPrecomputed
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Entry
public import VerifiedGarbage.Proof.RsaPss.Arm.Step
public import VerifiedGarbage.Proof.RsaPss.Arm.CtBase
public import VerifiedGarbage.Spec.RsaPkcs1Enc.Contract
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.RsaPss.Arm.CtSel
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.Fn
public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Proof.Rsa.Arm.ScrubOut
public import VerifiedGarbage.Proof.Rsa.Arm.ScrubCode
import VerifiedGarbage.Proof.RsaOaep.Arm.Calls
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Vp
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Callees
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Rsa.Arm.PrivImpl
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.RsaPss.Arm.VfPass
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Common
import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.RsaPkcs1Enc.Arm.Front

/-!
# RSAES-PKCS1-v1_5 decryption with the message first, on ARMv7

`Front.code` (`Impl/RsaPkcs1Enc/Arm/Front.lean`) against
`Spec.RsaPkcs1Enc.decryptPrecomputedFrontContract` with 3824 bytes of stack
(`front_verified`), for any callee verified against
`Spec.RsaPkcs1Enc.decryptPrecomputedContract` with 3640: its proof is used
only through that contract (`call_vp`).

**The layout.** `EP`: what two runs share (the frame's base `B`, the
pointers, the lengths, the public key's bytes and what of `pre` it may
leak), and its layout (`EP.lay`, `Proof/RsaPkcs1Sig/Arm/Lay.lean`):
RSAES-OAEP's frame of 128 bytes in the push of every register, the 84 bytes
of stack arguments above them, and below the frame the 3640 bytes
`vg_rsa_pkcs1_decrypt_precomputed` uses. `In P σ`: the state `σ` the body
starts from, which the contract's precondition gives (`in_of_pre`).

**The call.** `setup` copies the stack arguments to the bottom of the frame
and loads the argument registers back from the push (`setup_vp`); the call
is used only through the callee's contract: its precondition from the
layout (`call_pre`), the same public data in two runs (`call_pub`), and what
it writes (`R2`). `after` keeps its result in the slot `sRes` and puts
`scratch` in the slot `sS` (`after_vp`).

**After the call**, in RSAES-OAEP's frame and layout of `scratch` (`Ctx`,
`Geo`, `Proof/RsaPss/Arm/Step.lean`), with the call's result in `sRes` and
`*msg_len` as it wrote them (`Kp`): the buffer cleared (`clr_vp`), `out`'s
`k` bytes copied to it (`in_vp`), shifted left by `k - L` in eleven passes
(`shift_vp`, with RSAES-OAEP's passes, as `Proof/RsaOaep/Arm/DecOut.lean`
proves its ten), which leaves the message and zeros, and copied back
(`out_vp`), with the result back in `r0` (`ret_vp`): what `writtenMsgFront`
states.

**As emitted** (`front_scrubbed`): the code calling
`vg_rsa_pkcs1_decrypt_precomputed`'s code before its cleanup, an internal
function of its own (`bodyName`), then the cleanup of the 3824 bytes of
stack it and its callee use.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.Arm.Front

open VG VG.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Impl.RsaPss.Arm (frameBytes sp0 ld st copyArg arg sS oRsa)
open VG.Impl.RsaOaep.Arm (sRes)
open VG.Impl.RsaPkcs1Enc.Arm.Front (setup after)
open VG.Proof.Rsa.Arm.Recover (VP)

/-- What two runs share. -/
structure EP where
  B : BitVec 32
  out : BitVec 32
  ml : BitVec 32
  n : BitVec 32
  e : BitVec 32
  d : BitVec 32
  inp : BitVec 32
  p : BitVec 32
  q : BitVec 32
  dp : BitVec 32
  dq : BitVec 32
  qinv : BitVec 32
  scr : BitVec 32
  pre : BitVec 32
  K : Nat
  el : Nat
  dl : Nat
  pl : Nat
  ql : Nat
  sl : Nat
  prl : Nat
  nB : List Byte
  eB : List Byte
  preL : List Nat

/-- The stack the callee uses. -/
abbrev calleeStack : Nat := Proof.RsaPkcs1Enc.Arm.Dec.stackBytes

/-- The stack the function uses: the push, the inner frame and the call's. -/
abbrev stackBytes : Nat := 56 + frameBytes + calleeStack

namespace EP

variable (P : EP)

abbrev OUT : Region := ⟨State.addr P.out, P.K⟩
abbrev ML : Region := ⟨State.addr P.ml, 8⟩
abbrev N : Region := ⟨State.addr P.n, P.K⟩
abbrev E : Region := ⟨State.addr P.e, P.el⟩
abbrev D : Region := ⟨State.addr P.d, P.dl⟩
abbrev INP : Region := ⟨State.addr P.inp, P.K⟩
abbrev PP : Region := ⟨State.addr P.p, P.pl⟩
abbrev QQ : Region := ⟨State.addr P.q, P.ql⟩
abbrev DP : Region := ⟨State.addr P.dp, P.pl⟩
abbrev DQ : Region := ⟨State.addr P.dq, P.ql⟩
abbrev QI : Region := ⟨State.addr P.qinv, P.pl⟩
abbrev SCR : Region := ⟨State.addr P.scr, P.sl * 8⟩
abbrev PRE : Region := ⟨State.addr P.pre, P.prl * 8⟩

/-- The arguments, in order. -/
abbrev argv : List (BitVec 32) :=
  [P.out, BitVec.ofNat 32 P.K, P.ml, P.n, BitVec.ofNat 32 P.K, P.e, BitVec.ofNat 32 P.el, P.d,
    BitVec.ofNat 32 P.dl, P.inp, BitVec.ofNat 32 P.K, P.p, BitVec.ofNat 32 P.pl, P.q, BitVec.ofNat 32 P.ql,
    P.dp, BitVec.ofNat 32 P.pl, P.dq, BitVec.ofNat 32 P.ql, P.qinv, BitVec.ofNat 32 P.pl, P.scr,
    BitVec.ofNat 32 P.sl, P.pre, BitVec.ofNat 32 P.prl]

/-- The buffers it reads. -/
abbrev ro : List Region := [P.N, P.E, P.D, P.INP, P.PP, P.QQ, P.DP, P.DQ, P.QI, P.PRE]

/-- The buffers it writes. -/
abbrev rw : List Region := [P.OUT, P.ML, P.SCR]

abbrev lay : Lay where
  B := P.B
  F := frameBytes
  A := 84
  argv := P.argv
  ro := P.ro
  rw := P.rw
  C := calleeStack

end EP

/-- The state the body starts from. -/
structure In (P : EP) (σ : State) : Prop where
  ok : P.lay.Ok σ
  kv : Spec.Rsa.lenValid P.K
  el1 : 1 ≤ P.el
  elK : P.el ≤ P.K
  dl1 : 1 ≤ P.dl
  dlK : P.dl ≤ P.K
  pl1 : 1 ≤ P.pl
  plK : P.pl < P.K
  ql1 : 1 ≤ P.ql
  qlK : P.ql < P.K
  slK : Spec.Rsa.scratchWords P.K ≤ P.sl
  nB : Spec.Rsa.bytesAt σ.mem (State.addr P.n) P.K = P.nB
  eB : Spec.Rsa.bytesAt σ.mem (State.addr P.e) P.el = P.eB
  prl : P.prl = Spec.Rsa.privatePrecomputedWords P.K P.pl P.ql
  pre : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt σ.mem (State.addr P.n) P.K)
    (Spec.Rsa.bytesAt σ.mem (State.addr P.p) P.pl) (Spec.Rsa.bytesAt σ.mem (State.addr P.q) P.ql) =
      some (Spec.Rsa.wordsAt σ.mem (State.addr P.pre) P.prl)
  preL : Spec.Rsa.privatePrecomputedLeak σ.mem (State.addr P.pre) P.K = P.preL

/-- A state of the body. -/
abbrev S (P : EP) (σ s : State) : Prop := In P σ ∧ P.lay.St σ s

namespace In

variable {P : EP} {σ : State} (h : In P σ)
include h

theorem k64 : 64 ≤ P.K := h.kv.1
theorem k1024 : P.K ≤ 1024 := h.kv.2

theorem sl32 : P.sl < 2 ^ 32 := by
  have := h.ok.fits P.SCR (by simp)
  simp only [Proof.X25519.Arm.addr_toNat] at this
  omega_using [this]

theorem prl32 : P.prl < 2 ^ 32 := by
  have := h.ok.fits P.PRE (by simp)
  simp only [Proof.X25519.Arm.addr_toNat] at this
  omega_using [this]

theorem out_fit : P.out.toNat + P.K ≤ 2 ^ 32 := by
  have := h.ok.fits P.OUT (by simp); simpa [Proof.X25519.Arm.addr_toNat] using this

theorem ml_fit : P.ml.toNat + 8 ≤ 2 ^ 32 := by
  have := h.ok.fits P.ML (by simp); simpa [Proof.X25519.Arm.addr_toNat] using this

/-- Our part of `scratch`. -/
theorem geo : Geo P.lay P.scr := by
  have hs := h.slK
  have hK := h.k64
  have hf := h.ok.fits (P.SCR) (by simp)
  simp only [Proof.X25519.Arm.addr_toNat] at hf
  unfold Spec.Rsa.scratchWords at hs
  exact ⟨rfl, by unfold oRsa; omega_using [hs, hf, hK],
    ⟨P.sl * 8, by unfold oRsa; omega_using [hs, hK], by simp⟩, ⟨σ, h.ok⟩, by show 16 ≤ 3640; decide⟩

end In

/-- The arguments' places are immediates. -/
theorem arg_lt {j : Nat} (hj : j < 25) : arg j < 4096 := by
  unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes; split <;> omega_using [hj]

/-- An argument: its place, readable, and its value. -/
theorem argAt {P : EP} {σ s : State} (hi : In P σ) (hs : P.lay.St σ s) {j : Nat} (hj : j < 25) :
    State.addr (P.B + BitVec.ofNat 32 (arg j)) = P.lay.fr (arg j) ∧
    InRegions (s.rd ++ s.wr) (P.lay.fr (arg j)) 4 ∧
    s.mem.readW (P.lay.fr (arg j)) 32 = P.argv.getD j 0 := by
  obtain hl : j < P.lay.argv.length := by simp only [EP.argv, List.length_cons, List.length_nil]; omega_using [hj]
  exact ⟨hi.ok.addrB (by
      show arg j < frameBytes + 56 + 84; unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes; split <;> omega_using [hj]),
    by rw [hs.rd, hs.wr]; exact hi.ok.arg_read hl, hs.arg hl⟩

/-- A slot, written with `r12 = sp`. -/
theorem slotAt {P : EP} {σ : State} (hi : In P σ) {d : Nat} (hd : d + 4 ≤ frameBytes) :
    State.addr (P.B + BitVec.ofNat 32 d) = P.lay.fr d :=
  hi.ok.addrB (by show d < frameBytes + 56 + 84; unfold frameBytes at hd ⊢; omega_using [hd])

theorem nB_at {P : EP} {σ s : State} (hi : In P σ) (hs : P.lay.St σ s) :
    Spec.Rsa.bytesAt s.mem (State.addr P.n) P.K = P.nB := (hs.ro (R := P.N) (by simp)).trans hi.nB

theorem eB_at {P : EP} {σ s : State} (hi : In P σ) (hs : P.lay.St σ s) :
    Spec.Rsa.bytesAt s.mem (State.addr P.e) P.el = P.eB := (hs.ro (R := P.E) (by simp)).trans hi.eB

theorem leak_at {P : EP} {σ s : State} (hi : In P σ) (hs : P.lay.St σ s) :
    Spec.Rsa.privatePrecomputedLeak s.mem (State.addr P.pre) P.K = P.preL := by
  obtain le : Spec.Rsa.precomputedWords P.K ≤ P.prl := by
    rw [hi.prl, Spec.Rsa.privatePrecomputedWords]; omega_using []
  obtain rw := hs.ro_words (R := P.PRE) (by simp) (n := P.prl) rfl
  dsimp only at rw
  rw [← hi.preL]
  unfold Spec.Rsa.privatePrecomputedLeak
  rw [Proof.Rsa.Arm.wordsAt_take le, Proof.Rsa.Arm.wordsAt_take (m := σ.mem) le, rw]

theorem key_at {P : EP} {σ s : State} (hi : In P σ) (hs : P.lay.St σ s) :
    Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem (State.addr P.n) P.K)
      (Spec.Rsa.bytesAt s.mem (State.addr P.p) P.pl) (Spec.Rsa.bytesAt s.mem (State.addr P.q) P.ql) =
    some (Spec.Rsa.wordsAt s.mem (State.addr P.pre) P.prl) := by
  obtain rw := hs.ro_words (R := P.PRE) (by simp) (n := P.prl) rfl
  dsimp only at rw
  rw [hs.ro (R := P.N) (by simp), hs.ro (R := P.PP) (by simp), hs.ro (R := P.QQ) (by simp), rw]
  exact hi.pre

/-! ## The entry -/

/-- The shared contract, with the stack of the frames and of the call. -/
abbrev spec : Contract isa := Spec.RsaPkcs1Enc.decryptPrecomputedFrontContract abi stackBytes

/-- The public parameters of an entry state. -/
def ep (s : State) : EP where
  B := s.sp - BitVec.ofNat 32 56 - BitVec.ofNat 32 frameBytes
  out := s.gpr .r0
  ml := s.gpr .r2
  n := s.gpr .r3
  e := stackArg s 1
  d := stackArg s 3
  inp := stackArg s 5
  p := stackArg s 7
  q := stackArg s 9
  dp := stackArg s 11
  dq := stackArg s 13
  qinv := stackArg s 15
  scr := stackArg s 17
  pre := stackArg s 19
  K := (stackArg s 0).toNat
  el := (stackArg s 2).toNat
  dl := (stackArg s 4).toNat
  pl := (stackArg s 8).toNat
  ql := (stackArg s 10).toNat
  sl := (stackArg s 18).toNat
  prl := (stackArg s 20).toNat
  nB := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat
  eB := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 1)) (stackArg s 2).toNat
  preL := Spec.Rsa.privatePrecomputedLeak s.mem (State.addr (stackArg s 19)) (stackArg s 0).toNat

/-- The elements of a list that is a function's values at `0 … n - 1`. -/
private theorem getD_of_eq_map_range {α : Type} (f : Nat → α) (d : α) {l : List α} {n : Nat}
    (h : l = (List.range n).map f) {i : Nat} (hi : i < n) : f i = l.getD i d := by
  subst h
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]; rfl

theorem in_of_pre {s : State} (h : spec.pre s) : In (ep s) (entered frameBytes s) := by
  sig_pre [Spec.RsaPkcs1Enc.decryptPrecomputedFrontContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
    Spec.RsaPkcs1Enc.decryptSig, abi, argRegs, reduceClassify, Loc.val] at h
  sig_split h
  rename_i hsp hsa hrd hwr oM oN oE oD oI oP oQ oDP oDQ oQI oS oPre oA mN mE mD mI mP mQ mDP mDQ mQI mS mPre mA
    nS eS dS iS pS qS dpS dqS qiS sPre sA kO kM kN kE kD kI kP kQ kDP kDQ kQI kS kPre kA fO fM fN fE fD fI fP fQ
    fDP fDQ fQI fS fPre kv olk ilk el1 elK dl1 dlK pl1 plK ql1 qlK dpl qil dql slK prl
  have key := h
  have h3824 : 3824 ≤ s.sp.toNat := hsp
  have r1 : s.gpr .r1 = stackArg s 0 := BitVec.eq_of_toNat_eq olk
  have a6 : stackArg s 6 = stackArg s 0 := BitVec.eq_of_toNat_eq ilk
  have a12 : stackArg s 12 = stackArg s 8 := BitVec.eq_of_toNat_eq dpl
  have a16 : stackArg s 16 = stackArg s 8 := BitVec.eq_of_toNat_eq qil
  have a14 : stackArg s 14 = stackArg s 10 := BitVec.eq_of_toNat_eq dql
  rw [olk] at hwr oM oN oE oD oI oP oQ oDP oDQ oQI oS oPre oA kO fO
  rw [ilk] at hrd oI mI iS kI fI
  rw [dpl] at hrd oDP mDP dpS kDP fDP
  rw [qil] at hrd oQI mQI qiS kQI fQI
  rw [dql] at hrd oDQ mDQ dqS kDQ fDQ
  have hpush : Frame [FrameStack.belowA s.sp 56] s.mem (entered frameBytes s).mem :=
    FrameStack.pushed_frameA (rs := Impl.RsaPkcs1Sig.Arm.pushRegs) (by show 56 ≤ s.sp.toNat; omega_arith)
  have below : Region.Sub (FrameStack.belowA s.sp 56)
      ⟨State.addr s.sp - BitVec.ofNat 64 3824, 3824⟩ := by
    show Region.Sub ⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩ _
    rw [FrameStack.addr_sub' (by omega_arith)]
    exact Offset.sub_below _ (by omega_arith) (by omega_arith)
  have bytesE {R : Region} (hR : (⟨State.addr s.sp - BitVec.ofNat 64 3824, 3824⟩ : Region).Disjoint R)
      (hl : R.len ≤ 2 ^ 64) : Spec.Rsa.bytesAt (entered frameBytes s).mem R.base R.len =
        Spec.Rsa.bytesAt s.mem R.base R.len :=
    bytesAt_frame hpush (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hR.sub_left below).symm) hl
  have kPre' : (⟨State.addr s.sp - BitVec.ofNat 64 3824, 3824⟩ : Region).Disjoint
      ⟨State.addr (stackArg s 19), 8 * (stackArg s 20).toNat⟩ := by rw [Nat.mul_comm]; exact kPre
  have hn : Spec.Rsa.bytesAt (entered frameBytes s).mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat =
      Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat :=
    bytesE (R := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩) kN (by show (stackArg s 0).toNat ≤ 2 ^ 64; omega_arith)
  have he : Spec.Rsa.bytesAt (entered frameBytes s).mem (State.addr (stackArg s 1)) (stackArg s 2).toNat =
      Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 1)) (stackArg s 2).toNat :=
    bytesE (R := ⟨State.addr (stackArg s 1), (stackArg s 2).toNat⟩) kE (by show (stackArg s 2).toNat ≤ 2 ^ 64; omega_arith)
  have hp : Spec.Rsa.bytesAt (entered frameBytes s).mem (State.addr (stackArg s 7)) (stackArg s 8).toNat =
      Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 7)) (stackArg s 8).toNat :=
    bytesE (R := ⟨State.addr (stackArg s 7), (stackArg s 8).toNat⟩) kP (by show (stackArg s 8).toNat ≤ 2 ^ 64; omega_arith)
  have hq : Spec.Rsa.bytesAt (entered frameBytes s).mem (State.addr (stackArg s 9)) (stackArg s 10).toNat =
      Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 9)) (stackArg s 10).toNat :=
    bytesE (R := ⟨State.addr (stackArg s 9), (stackArg s 10).toNat⟩) kQ (by show (stackArg s 10).toNat ≤ 2 ^ 64; omega_arith)
  have hw : Spec.Rsa.wordsAt (entered frameBytes s).mem (State.addr (stackArg s 19)) (stackArg s 20).toNat =
      Spec.Rsa.wordsAt s.mem (State.addr (stackArg s 19)) (stackArg s 20).toNat :=
    VG.Proof.Rsa.wordsAt_frame hpush (by omega_arith) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (kPre'.sub_left below).symm)
  have le : Spec.Rsa.precomputedWords (stackArg s 0).toNat ≤ (stackArg s 20).toNat := by
    rw [prl, Spec.Rsa.privatePrecomputedWords]; omega_using []
  constructor
  rotate_left
  · exact kv
  · exact el1
  · exact elK
  · exact dl1
  · exact dlK
  · exact pl1
  · exact plK
  · exact ql1
  · exact qlK
  · exact slK
  · exact hn
  · exact he
  · exact prl
  · change Spec.Rsa.privatePrecompute
      (Spec.Rsa.bytesAt (entered frameBytes s).mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat)
      (Spec.Rsa.bytesAt (entered frameBytes s).mem (State.addr (stackArg s 7)) (stackArg s 8).toNat)
      (Spec.Rsa.bytesAt (entered frameBytes s).mem (State.addr (stackArg s 9)) (stackArg s 10).toNat) =
        some (Spec.Rsa.wordsAt (entered frameBytes s).mem (State.addr (stackArg s 19)) (stackArg s 20).toNat)
    rw [hn, hp, hq, hw]
    exact key
  · change Spec.Rsa.privatePrecomputedLeak (entered frameBytes s).mem (State.addr (stackArg s 19))
      (stackArg s 0).toNat = Spec.Rsa.privatePrecomputedLeak s.mem (State.addr (stackArg s 19)) (stackArg s 0).toNat
    unfold Spec.Rsa.privatePrecomputedLeak
    rw [Proof.Rsa.Arm.wordsAt_take le, Proof.Rsa.Arm.wordsAt_take (m := s.mem) le, hw]
  have lay : (ep s).lay = layOf frameBytes 84 (ep s).argv [(ep s).N, (ep s).E, (ep s).D,
      (ep s).INP, (ep s).PP, (ep s).QQ, (ep s).DP, (ep s).DQ, (ep s).QI,
      (ep s).PRE] [(ep s).OUT, (ep s).ML, (ep s).SCR] s calleeStack := by
    simp [ep, EP.lay, EP.argv, EP.ro, EP.rw, layOf]
  rw [lay]
  refine ok_entered (by decide) (by decide) rfl hsp hsa hrd hwr ?_ ?_ ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [kN, kE, kD, kI, kP, kQ, kDP, kDQ, kQI, kPre, kO, kM, kS, kA]
  · intro w hw r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hw with rfl | rfl | rfl <;>
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [oN, oE, oD, oI, oP, oQ, oDP, oDQ, oQI, oPre, oA, mN, mE, mD, mI, mP, mQ, mDP, mDQ, mQI, mPre, mA,
      nS.symm, eS.symm, dS.symm, iS.symm, pS.symm, qS.symm, dpS.symm, dqS.symm, qiS.symm, sPre, sA]
  · refine List.Pairwise.cons ?_ (List.pairwise_pair.mpr mS)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [oM, oS]
  · intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [fN, fE, fD, fI, fP, fQ, fDP, fDQ, fQI, fPre, fO, fM, fS]
  · intro j hj
    rcases (by omega_arith : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    · rfl
    · simp [regArg, ep, r1]
    · rfl
    · rfl
  · intro i hi
    simp only [ep, EP.argv, BitVec.ofNat_eq_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq, List.getD_cons_succ]
    refine getD_of_eq_map_range (stackArg s) 0 ?_ (show i < 21 from hi)
    simp only [List.range, List.range.loop, List.map_cons, List.map_nil, a6, a12, a14, a16]

theorem spec_sp {s : State} (h : spec.pre s) : stackBytes ≤ s.sp.toNat := by
  sig_pre [Spec.RsaPkcs1Enc.decryptPrecomputedFrontContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
    Spec.RsaPkcs1Enc.decryptSig, abi, argRegs, reduceClassify, Loc.val] at h
  exact h.1

theorem entered_state {s : State} (h : spec.pre s) : S (ep s) (entered frameBytes s) (entered frameBytes s) :=
  ⟨in_of_pre h, ⟨(in_of_pre h).ok, (in_of_pre h).ok.sp, rfl, rfl, Frame.refl _ _⟩⟩

theorem ep_eq {s₁ s₂ : State} (hp : spec.pub s₁ s₂) : ep s₁ = ep s₂ := by
  sig_pub [Spec.RsaPkcs1Enc.decryptPrecomputedFrontContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
    Spec.RsaPkcs1Enc.decryptSig, abi, argRegs, reduceClassify, Loc.val] at hp
  obtain ⟨hsp, hl, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17,
    a18, a19, a20⟩ := hp
  obtain ⟨hl1, hleak⟩ := List.append_inj hl (by simp [bytesAt_length, a0, a2])
  obtain ⟨hn, he⟩ := List.append_inj (Proof.RsaPkcs1Enc.Arm.Dec.map_toNat_inj hl1) (by simp [bytesAt_length, a0])
  simp only [ep]
  rw [hsp, h0, h2, h3, a0, a1, a2, a3, a4, a5, a7, a8, a9, a10, a11, a13, a15, a17, a18, a19, a20]
  rw [h3, a0] at hn
  rw [a1, a2] at he
  rw [a19, a0] at hleak
  rw [show State.addr (s₂.gpr .r3) = BitVec.setWidth 64 (s₂.gpr .r3) from rfl, hn,
    show State.addr (stackArg s₂ 1) = BitVec.setWidth 64 (stackArg s₂ 1) from rfl, he,
    show State.addr (stackArg s₂ 19) = BitVec.setWidth 64 (stackArg s₂ 19) from rfl, hleak]

/-! ## The call's arguments -/

theorem rdArg {L : Lay} (m : Mem) (v : BitVec 32) {d j : Nat} (hd : d + 4 ≤ frameBytes) (hj : j < 25) :
    (m.writeW (L.fr d) v).readW (L.fr (arg j)) 32 = m.readW (L.fr (arg j)) 32 :=
  Lay.readW_fr_other L m v (by unfold arg Impl.RsaPkcs1Sig.Arm.argOff; unfold frameBytes at hd ⊢; split <;> omega_using [hd])
    (by unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes; split <;> omega_using [hj])
    (by unfold frameBytes at hd; omega_using [hd])

/-- Words written to the frame from slot `k` on. -/
def wl (L : Lay) : Mem → Nat → List (BitVec 32) → Mem
  | m, _, [] => m
  | m, k, v :: vs => wl L (m.writeW (L.fr (4 * k)) v) (k + 1) vs

theorem wl_nil (L : Lay) (m : Mem) (k : Nat) : wl L m k [] = m := rfl
theorem wl_cons (L : Lay) (m : Mem) (k : Nat) (v : BitVec 32) (vs : List (BitVec 32)) :
    wl L m k (v :: vs) = wl L (m.writeW (L.fr (4 * k)) v) (k + 1) vs := rfl

theorem wl_other (L : Lay) : ∀ (vs : List (BitVec 32)) (m : Mem) (k j : Nat), j < k → k + vs.length ≤ 21 →
    (wl L m k vs).readW (L.fr (4 * j)) 32 = m.readW (L.fr (4 * j)) 32
  | [], _, _, _, _, _ => rfl
  | v :: vs, m, k, j, hj, hl => by
    rw [wl_cons, wl_other L vs _ (k + 1) j (by omega_using [hj]) (by simp at hl; omega_using [hl]),
      Lay.readW_fr_other _ _ _ (by omega_using [hj]) (by omega_using [hj, hl]) (by simp at hl; omega_using [hl])]

theorem wl_read (L : Lay) : ∀ (vs : List (BitVec 32)) (m : Mem) (k i : Nat), k ≤ i → i < k + vs.length →
    k + vs.length ≤ 21 → (wl L m k vs).readW (L.fr (4 * i)) 32 = vs.getD (i - k) 0
  | [], _, _, _, h₁, h₂, _ => by simp at h₂; omega
  | v :: vs, m, k, i, h₁, h₂, hl => by
    rw [wl_cons]
    simp only [List.length_cons] at h₂ hl
    by_cases e : i = k
    · subst e
      rw [wl_other L vs _ (i + 1) i (by omega_using []) (by omega_using [hl]), Mem.readW_writeW_self32, Nat.sub_self]; rfl
    · rw [wl_read L vs _ (k + 1) i (by omega_using [h₁, e]) (by omega_using [h₂]) (by omega_using [hl]),
        show i - k = (i - (k + 1)) + 1 by omega_using [h₁, e]]; rfl

theorem wl_frame (L : Lay) : ∀ (vs : List (BitVec 32)) (m : Mem) (k : Nat), k + vs.length ≤ 21 →
    Frame [⟨L.fr 0, 84⟩] m (wl L m k vs)
  | [], _, _, _ => Frame.refl _ _
  | v :: vs, m, k, hl => by
    rw [wl_cons]
    simp only [List.length_cons] at hl
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (Nat.zero_le _) (by omega_using [hl]) (by omega_using []))).trans
      (wl_frame L vs _ (k + 1) (by omega_using [hl]))

/-- The call's stack arguments: our arguments 4 … 24. -/
abbrev sargs (P : EP) : List (BitVec 32) := P.argv.drop 4

theorem setup_wp (P : EP) {σ s : State} (hi : In P σ) (hs : P.lay.St σ s) :
    WP isa (.block setup) s fun t =>
      t.mem = wl P.lay s.mem 0 (sargs P) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.gpr .r0 = P.out ∧
      t.gpr .r1 = BitVec.ofNat 32 P.K ∧ t.gpr .r2 = P.ml ∧ t.gpr .r3 = P.n := by
  obtain ⟨a0, r0, v0⟩ := argAt hi hs (j := 0) (by decide)
  obtain ⟨a1, r1, v1⟩ := argAt hi hs (j := 1) (by decide)
  obtain ⟨a2, r2, v2⟩ := argAt hi hs (j := 2) (by decide)
  obtain ⟨a3, r3, v3⟩ := argAt hi hs (j := 3) (by decide)
  obtain ⟨a4, r4, v4⟩ := argAt hi hs (j := 4) (by decide)
  obtain ⟨a5, r5, v5⟩ := argAt hi hs (j := 5) (by decide)
  obtain ⟨a6, r6, v6⟩ := argAt hi hs (j := 6) (by decide)
  obtain ⟨a7, r7, v7⟩ := argAt hi hs (j := 7) (by decide)
  obtain ⟨a8, r8, v8⟩ := argAt hi hs (j := 8) (by decide)
  obtain ⟨a9, r9, v9⟩ := argAt hi hs (j := 9) (by decide)
  obtain ⟨a10, r10, v10⟩ := argAt hi hs (j := 10) (by decide)
  obtain ⟨a11, r11, v11⟩ := argAt hi hs (j := 11) (by decide)
  obtain ⟨a12, r12, v12⟩ := argAt hi hs (j := 12) (by decide)
  obtain ⟨a13, r13, v13⟩ := argAt hi hs (j := 13) (by decide)
  obtain ⟨a14, r14, v14⟩ := argAt hi hs (j := 14) (by decide)
  obtain ⟨a15, r15, v15⟩ := argAt hi hs (j := 15) (by decide)
  obtain ⟨a16, r16, v16⟩ := argAt hi hs (j := 16) (by decide)
  obtain ⟨a17, r17, v17⟩ := argAt hi hs (j := 17) (by decide)
  obtain ⟨a18, r18, v18⟩ := argAt hi hs (j := 18) (by decide)
  obtain ⟨a19, r19, v19⟩ := argAt hi hs (j := 19) (by decide)
  obtain ⟨a20, r20, v20⟩ := argAt hi hs (j := 20) (by decide)
  obtain ⟨a21, r21, v21⟩ := argAt hi hs (j := 21) (by decide)
  obtain ⟨a22, r22, v22⟩ := argAt hi hs (j := 22) (by decide)
  obtain ⟨a23, r23, v23⟩ := argAt hi hs (j := 23) (by decide)
  obtain ⟨a24, r24, v24⟩ := argAt hi hs (j := 24) (by decide)
  obtain wF : ∀ d, d + 4 ≤ frameBytes → InRegions s.wr (P.lay.fr d) 4 := fun d hd => hs.inFr hd
  obtain aF : ∀ d, d + 4 ≤ frameBytes → State.addr (P.B + BitVec.ofNat 32 d) = P.lay.fr d :=
    fun d hd => slotAt hi hd
  obtain q0 : State.addr P.B = P.lay.fr 0 := by simp
  obtain w0 : InRegions s.wr (State.addr P.B) 4 := by rw [q0]; exact wF 0 (by decide)
  obtain rdA0 : ∀ (m : Mem) (v : BitVec 32) (j : Nat), j < 25 →
      (m.writeW (State.addr P.B) v).readW (P.lay.fr (arg j)) 32 = m.readW (P.lay.fr (arg j)) 32 :=
    fun m v j hj => by rw [q0]; exact rdArg m v (by decide) hj
  prun [setup, copyArg, sp0, ld, st, hs.sp, aF, wF, arg_lt,
    a0, r0, v0, a1, r1, v1, a2, r2, v2, a3, r3, v3, a4, r4, v4, a5, r5, v5, a6, r6, v6, a7, r7, v7, a8, r8, v8,
    a9, r9, v9, a10, r10, v10, a11, r11, v11, a12, r12, v12, a13, r13, v13, a14, r14, v14, a15, r15, v15,
    a16, r16, v16, a17, r17, v17, a18, r18, v18, a19, r19, v19, a20, r20, v20, a21, r21, v21, a22, r22, v22,
    a23, r23, v23, a24, r24, v24, rdArg, w0, rdA0, Nat.reduceMul, Nat.reduceAdd]
  simp only [sargs, EP.argv, List.drop_succ_cons, List.drop_zero, wl_cons, wl_nil, List.getD_cons_succ,
    List.getD_cons_zero, Nat.reduceMul, Nat.reduceAdd, q0, and_self]

/-- Before the call. -/
abbrev R1 (P : EP) (σ s : State) : Prop :=
  S P σ s ∧ s.gpr .r0 = P.out ∧ s.gpr .r1 = BitVec.ofNat 32 P.K ∧ s.gpr .r2 = P.ml ∧ s.gpr .r3 = P.n ∧
    ∀ i < 21, stackArg s i = (sargs P).getD i 0

theorem setup_vp (P : EP) : VP (S P) (.block setup) (R1 P) := by
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.2.sp.trans h₂.2.sp.symm) fun σ s ⟨hi, hs⟩ => ?_
  refine WP.mono (setup_wp P hi hs) fun t ⟨m, rd, wr, sp, t0, t1, t2, t3⟩ => ?_
  obtain fr : Frame [⟨P.lay.fr 0, 84⟩] s.mem t.mem := by rw [m]; exact wl_frame _ _ _ 0 (by simp)
  refine ⟨⟨hi, hs.write fr (fun r hr => ?_) rd wr sp⟩, t0, t1, t2, t3, fun i hi' => ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨P.lay.FR, List.mem_cons_self, Offset.sub_base _ (show 0 + 84 ≤ frameBytes by decide)⟩
  · simp only [stackArg, stackArgAddr, sp, hs.sp]
    rw [slotAt hi (d := 4 * i) (by unfold frameBytes; omega_using [hi']), m,
      wl_read _ _ _ 0 i (Nat.zero_le _) (by simp; omega_using [hi']) (by simp), Nat.sub_zero]

/-! ## The call -/

/-- The callee's buffers: those it reads, with its stack arguments, and
those it writes. -/
abbrev cRd (P : EP) : List Region := P.ro ++ [⟨State.addr P.B, 84⟩]
abbrev cWr (P : EP) : List Region := P.rw

/-- The callee's contract. -/
abbrev cK : Contract isa := Spec.RsaPkcs1Enc.decryptPrecomputedContract abi calleeStack

/-- The callee's stack arguments' region, the bottom of our frame. -/
abbrev AR (P : EP) : Region := ⟨State.addr P.B, 84⟩

section
variable {P : EP} {σ : State} (hi : In P σ)
include hi

theorem rw_ro' {w r : Region} (hw : w ∈ P.rw) (hr : r ∈ P.ro) : w.Disjoint r := hi.ok.rw_ro hw hr

theorem rw_ar {w : Region} (hw : w ∈ P.rw) : w.Disjoint (AR P) := by
  obtain q0 : State.addr P.B = P.lay.fr 0 := by simp
  rw [AR, q0]; exact (hi.ok.stk_fr (.inr hw) (d := 0) (n := 84) (by show 0 + 84 ≤ frameBytes + 56; decide)).symm

theorem low_ro {r : Region} (hr : r ∈ P.ro ∨ r ∈ P.rw) :
    (⟨State.addr P.B - BitVec.ofNat 64 calleeStack, calleeStack⟩ : Region).Disjoint r := hi.ok.low_buf hr

omit hi in
theorem low_ar : (⟨State.addr P.B - BitVec.ofNat 64 calleeStack, calleeStack⟩ : Region).Disjoint (AR P) := by
  obtain q0 : State.addr P.B = P.lay.fr 0 := by simp
  have := (Lay.fr_low (L := P.lay) (d := 0) (n := 84) (by decide) (by show calleeStack ≤ 2 ^ 32; decide)).symm
  rw [← q0] at this
  exact this

theorem rw_pair : P.OUT.Disjoint P.ML ∧ P.OUT.Disjoint P.SCR ∧ P.ML.Disjoint P.SCR := by
  have h := hi.ok.wrw
  simp only [EP.rw, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, List.Pairwise.nil, and_true] at h
  exact ⟨h.1.1, h.1.2, h.2.1⟩

end

theorem call_pre {P : EP} {σ s : State} (h : R1 P σ s) : cK.pre (s.callEntry.withRegions (cRd P) (cWr P)) := by
  obtain ⟨⟨hi, hs⟩, r0, r1, r2, r3, a⟩ := h
  have ok := hi.ok
  have k32 : P.K < 2 ^ 32 := by have := hi.k1024; omega_using [this]
  have el32 : P.el < 2 ^ 32 := by have := hi.elK; omega_using [k32, this]
  have dl32 : P.dl < 2 ^ 32 := by have := hi.dlK; omega_using [k32, this]
  have pl32 : P.pl < 2 ^ 32 := by have := hi.plK; omega_using [k32, this]
  have ql32 : P.ql < 2 ^ 32 := by have := hi.qlK; omega_using [k32, this]
  have sl32 := hi.sl32
  have prl32 := hi.prl32
  have a0 : stackArg s 0 = BitVec.ofNat 32 P.K := a 0 (by decide)
  have a1 : stackArg s 1 = P.e := a 1 (by decide)
  have a2 : stackArg s 2 = BitVec.ofNat 32 P.el := a 2 (by decide)
  have a3 : stackArg s 3 = P.d := a 3 (by decide)
  have a4 : stackArg s 4 = BitVec.ofNat 32 P.dl := a 4 (by decide)
  have a5 : stackArg s 5 = P.inp := a 5 (by decide)
  have a6 : stackArg s 6 = BitVec.ofNat 32 P.K := a 6 (by decide)
  have a7 : stackArg s 7 = P.p := a 7 (by decide)
  have a8 : stackArg s 8 = BitVec.ofNat 32 P.pl := a 8 (by decide)
  have a9 : stackArg s 9 = P.q := a 9 (by decide)
  have a10 : stackArg s 10 = BitVec.ofNat 32 P.ql := a 10 (by decide)
  have a11 : stackArg s 11 = P.dp := a 11 (by decide)
  have a12 : stackArg s 12 = BitVec.ofNat 32 P.pl := a 12 (by decide)
  have a13 : stackArg s 13 = P.dq := a 13 (by decide)
  have a14 : stackArg s 14 = BitVec.ofNat 32 P.ql := a 14 (by decide)
  have a15 : stackArg s 15 = P.qinv := a 15 (by decide)
  have a16 : stackArg s 16 = BitVec.ofNat 32 P.pl := a 16 (by decide)
  have a17 : stackArg s 17 = P.scr := a 17 (by decide)
  have a18 : stackArg s 18 = BitVec.ofNat 32 P.sl := a 18 (by decide)
  have a19 : stackArg s 19 = P.pre := a 19 (by decide)
  have a20 : stackArg s 20 = BitVec.ofNat 32 P.prl := a 20 (by decide)
  have sa0 : stackArgAddr s 0 = State.addr P.B := by simp [stackArgAddr, hs.sp]
  obtain ⟨oM, oS, mS⟩ := rw_pair hi
  sig_pre [Spec.RsaPkcs1Enc.decryptPrecomputedContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
    Spec.RsaPkcs1Enc.decryptSig, abi, argRegs, reduceClassify, Loc.val]
  simp only [stackArg_call, stackArgAddr_call, r0, r1, r2, r3, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11,
    a12, a13, a14, a15, a16, a17, a18, a19, a20, sa0, hs.sp, BitVec.toNat_ofNat, Nat.mod_eq_of_lt k32,
    Nat.mod_eq_of_lt el32, Nat.mod_eq_of_lt dl32, Nat.mod_eq_of_lt pl32, Nat.mod_eq_of_lt ql32,
    Nat.mod_eq_of_lt sl32, Nat.mod_eq_of_lt prl32]
  have fit : P.B.toNat + 128 + 56 + 84 ≤ 2 ^ 32 := ok.fit
  obtain rr : ∀ {w r : Region}, w ∈ P.rw → r ∈ P.ro → w.Disjoint r := fun hw hr => rw_ro' hi hw hr
  obtain ra : ∀ {w : Region}, w ∈ P.rw → w.Disjoint (AR P) := fun hw => rw_ar hi hw
  obtain lo : ∀ {r : Region}, r ∈ P.ro ∨ r ∈ P.rw →
      (⟨State.addr P.B - BitVec.ofNat 64 calleeStack, calleeStack⟩ : Region).Disjoint r := fun hr => low_ro hi hr
  obtain fi : ∀ {r : Region}, r ∈ P.ro ++ P.rw → r.base.toNat + r.len ≤ 2 ^ 32 := fun hr => ok.fits _ hr
  refine ⟨ok.B56, by omega_using [fit], rfl, rfl, oM,
    rr (w := P.OUT) (r := P.N) (by simp) (by simp), rr (w := P.OUT) (r := P.E) (by simp) (by simp),
    rr (w := P.OUT) (r := P.D) (by simp) (by simp), rr (w := P.OUT) (r := P.INP) (by simp) (by simp),
    rr (w := P.OUT) (r := P.PP) (by simp) (by simp), rr (w := P.OUT) (r := P.QQ) (by simp) (by simp),
    rr (w := P.OUT) (r := P.DP) (by simp) (by simp), rr (w := P.OUT) (r := P.DQ) (by simp) (by simp),
    rr (w := P.OUT) (r := P.QI) (by simp) (by simp), oS, rr (w := P.OUT) (r := P.PRE) (by simp) (by simp),
    ra (w := P.OUT) (by simp),
    rr (w := P.ML) (r := P.N) (by simp) (by simp), rr (w := P.ML) (r := P.E) (by simp) (by simp),
    rr (w := P.ML) (r := P.D) (by simp) (by simp), rr (w := P.ML) (r := P.INP) (by simp) (by simp),
    rr (w := P.ML) (r := P.PP) (by simp) (by simp), rr (w := P.ML) (r := P.QQ) (by simp) (by simp),
    rr (w := P.ML) (r := P.DP) (by simp) (by simp), rr (w := P.ML) (r := P.DQ) (by simp) (by simp),
    rr (w := P.ML) (r := P.QI) (by simp) (by simp), mS, rr (w := P.ML) (r := P.PRE) (by simp) (by simp),
    ra (w := P.ML) (by simp),
    (rr (w := P.SCR) (r := P.N) (by simp) (by simp)).symm, (rr (w := P.SCR) (r := P.E) (by simp) (by simp)).symm,
    (rr (w := P.SCR) (r := P.D) (by simp) (by simp)).symm, (rr (w := P.SCR) (r := P.INP) (by simp) (by simp)).symm,
    (rr (w := P.SCR) (r := P.PP) (by simp) (by simp)).symm, (rr (w := P.SCR) (r := P.QQ) (by simp) (by simp)).symm,
    (rr (w := P.SCR) (r := P.DP) (by simp) (by simp)).symm, (rr (w := P.SCR) (r := P.DQ) (by simp) (by simp)).symm,
    (rr (w := P.SCR) (r := P.QI) (by simp) (by simp)).symm, rr (w := P.SCR) (r := P.PRE) (by simp) (by simp),
    ra (w := P.SCR) (by simp),
    lo (r := P.OUT) (.inr (by simp)), lo (r := P.ML) (.inr (by simp)), lo (r := P.N) (.inl (by simp)),
    lo (r := P.E) (.inl (by simp)), lo (r := P.D) (.inl (by simp)), lo (r := P.INP) (.inl (by simp)),
    lo (r := P.PP) (.inl (by simp)), lo (r := P.QQ) (.inl (by simp)), lo (r := P.DP) (.inl (by simp)),
    lo (r := P.DQ) (.inl (by simp)), lo (r := P.QI) (.inl (by simp)), lo (r := P.SCR) (.inr (by simp)),
    lo (r := P.PRE) (.inl (by simp)), low_ar (P := P),
    fi (r := P.OUT) (by simp), fi (r := P.ML) (by simp), fi (r := P.N) (by simp), fi (r := P.E) (by simp),
    fi (r := P.D) (by simp), fi (r := P.INP) (by simp), fi (r := P.PP) (by simp), fi (r := P.QQ) (by simp),
    fi (r := P.DP) (by simp), fi (r := P.DQ) (by simp), fi (r := P.QI) (by simp), fi (r := P.SCR) (by simp),
    fi (r := P.PRE) (by simp), hi.kv, trivial, trivial, hi.el1, hi.elK, hi.dl1, hi.dlK, hi.pl1, hi.plK, hi.ql1,
    hi.qlK, trivial, trivial, trivial, hi.slK, hi.prl, key_at hi hs⟩


theorem call_pub {P : EP} {σ₁ σ₂ s₁ s₂ : State} (h₁ : R1 P σ₁ s₁) (h₂ : R1 P σ₂ s₂) :
    cK.pub (s₁.callEntry.withRegions (cRd P) (cWr P)) (s₂.callEntry.withRegions (cRd P) (cWr P)) := by
  obtain ⟨⟨hi₁, hs₁⟩, p0, p1, p2, p3, pa⟩ := h₁
  obtain ⟨⟨hi₂, hs₂⟩, q0, q1, q2, q3, qa⟩ := h₂
  have pa0 : stackArg s₁ 0 = BitVec.ofNat 32 P.K := pa 0 (by decide)
  have pa1 : stackArg s₁ 1 = P.e := pa 1 (by decide)
  have pa2 : stackArg s₁ 2 = BitVec.ofNat 32 P.el := pa 2 (by decide)
  have pa19 : stackArg s₁ 19 = P.pre := pa 19 (by decide)
  have qa0 : stackArg s₂ 0 = BitVec.ofNat 32 P.K := qa 0 (by decide)
  have qa1 : stackArg s₂ 1 = P.e := qa 1 (by decide)
  have qa2 : stackArg s₂ 2 = BitVec.ofNat 32 P.el := qa 2 (by decide)
  have qa19 : stackArg s₂ 19 = P.pre := qa 19 (by decide)
  have k32 : P.K < 2 ^ 32 := by have := hi₁.k1024; omega_using [this]
  have el32 : P.el < 2 ^ 32 := by have := hi₁.elK; omega_using [k32, this]
  sig_pub [Spec.RsaPkcs1Enc.decryptPrecomputedContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
    Spec.RsaPkcs1Enc.decryptSig, abi, argRegs, reduceClassify, Loc.val]
  simp only [stackArg_call, p0, p1, p2, p3, q0, q1, q2, q3, pa0, pa1, pa2, pa19, qa0, qa1, qa2, qa19,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt k32, Nat.mod_eq_of_lt el32]
  obtain e : ∀ i < 21, stackArg s₁ i = stackArg s₂ i := fun i hi => (pa i hi).trans (qa i hi).symm
  obtain nb : Spec.Rsa.bytesAt s₁.mem (BitVec.setWidth 64 P.n) P.K =
      Spec.Rsa.bytesAt s₂.mem (BitVec.setWidth 64 P.n) P.K := (nB_at hi₁ hs₁).trans (nB_at hi₂ hs₂).symm
  obtain eb : Spec.Rsa.bytesAt s₁.mem (BitVec.setWidth 64 P.e) P.el =
      Spec.Rsa.bytesAt s₂.mem (BitVec.setWidth 64 P.e) P.el := (eB_at hi₁ hs₁).trans (eB_at hi₂ hs₂).symm
  obtain lb : Spec.Rsa.privatePrecomputedLeak s₁.mem (BitVec.setWidth 64 P.pre) P.K =
      Spec.Rsa.privatePrecomputedLeak s₂.mem (BitVec.setWidth 64 P.pre) P.K :=
    (leak_at hi₁ hs₁).trans (leak_at hi₂ hs₂).symm
  rw [nb, eb, lb]
  exact ⟨by rw [hs₁.sp, hs₂.sp], rfl, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
    e 3 (by decide), e 4 (by decide), e 5 (by decide), e 6 (by decide), e 7 (by decide), e 8 (by decide),
    e 9 (by decide), e 10 (by decide), e 11 (by decide), e 12 (by decide), e 13 (by decide), e 14 (by decide),
    e 15 (by decide), e 16 (by decide), e 17 (by decide), e 18 (by decide), trivial, e 20 (by decide)⟩

/-- The buffers the body only reads, in the run from `σ`. -/
abbrev dB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.d) P.dl
abbrev pB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.p) P.pl
abbrev qB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.q) P.ql
abbrev dpB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.dp) P.pl
abbrev dqB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.dq) P.ql
abbrev qiB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.qinv) P.pl
abbrev cB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.inp) P.K

/-- The decryption's outcome, in the run from `σ`. -/
abbrev oc (P : EP) (σ : State) : Spec.Rsa.Outcome :=
  Spec.RsaPkcs1Enc.decrypt P.nB P.eB (dB P σ) (pB P σ) (qB P σ) (dpB P σ) (dqB P σ) (qiB P σ) (cB P σ)

/-- After the call: what it writes, and its result. -/
abbrev R2 (P : EP) (σ s : State) : Prop :=
  S P σ s ∧ Spec.RsaPkcs1Enc.writtenMsg s.mem (State.addr P.out) (State.addr P.ml) P.K (s.gpr .r0) (oc P σ)

theorem call_post {P : EP} {σ s t : State} (h : R1 P σ s)
    (po : cK.post (s.callEntry.withRegions (cRd P) (cWr P)) (t.withRegions (cRd P) (cWr P))) :
    Spec.RsaPkcs1Enc.writtenMsg t.mem (State.addr P.out) (State.addr P.ml) P.K (t.gpr .r0)
      (Spec.RsaPkcs1Enc.decrypt (Spec.Rsa.bytesAt s.mem (State.addr P.n) P.K)
        (Spec.Rsa.bytesAt s.mem (State.addr P.e) P.el) (Spec.Rsa.bytesAt s.mem (State.addr P.d) P.dl)
        (Spec.Rsa.bytesAt s.mem (State.addr P.p) P.pl) (Spec.Rsa.bytesAt s.mem (State.addr P.q) P.ql)
        (Spec.Rsa.bytesAt s.mem (State.addr P.dp) P.pl) (Spec.Rsa.bytesAt s.mem (State.addr P.dq) P.ql)
        (Spec.Rsa.bytesAt s.mem (State.addr P.qinv) P.pl) (Spec.Rsa.bytesAt s.mem (State.addr P.inp) P.K)) := by
  obtain ⟨⟨hi, hs⟩, r0, r1, r2, r3, a⟩ := h
  have k32 : P.K < 2 ^ 32 := by have := hi.k1024; omega_using [this]
  have el32 : P.el < 2 ^ 32 := by have := hi.elK; omega_using [k32, this]
  have dl32 : P.dl < 2 ^ 32 := by have := hi.dlK; omega_using [k32, this]
  have pl32 : P.pl < 2 ^ 32 := by have := hi.plK; omega_using [k32, this]
  have ql32 : P.ql < 2 ^ 32 := by have := hi.qlK; omega_using [k32, this]
  have a0 : stackArg s 0 = BitVec.ofNat 32 P.K := a 0 (by decide)
  have a1 : stackArg s 1 = P.e := a 1 (by decide)
  have a2 : stackArg s 2 = BitVec.ofNat 32 P.el := a 2 (by decide)
  have a3 : stackArg s 3 = P.d := a 3 (by decide)
  have a4 : stackArg s 4 = BitVec.ofNat 32 P.dl := a 4 (by decide)
  have a5 : stackArg s 5 = P.inp := a 5 (by decide)
  have a7 : stackArg s 7 = P.p := a 7 (by decide)
  have a8 : stackArg s 8 = BitVec.ofNat 32 P.pl := a 8 (by decide)
  have a9 : stackArg s 9 = P.q := a 9 (by decide)
  have a10 : stackArg s 10 = BitVec.ofNat 32 P.ql := a 10 (by decide)
  have a11 : stackArg s 11 = P.dp := a 11 (by decide)
  have a13 : stackArg s 13 = P.dq := a 13 (by decide)
  have a15 : stackArg s 15 = P.qinv := a 15 (by decide)
  sig_post [Spec.RsaPkcs1Enc.decryptPrecomputedContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
    Spec.RsaPkcs1Enc.decryptSig, abi, argRegs, reduceClassify, Loc.val] at po
  simp only [stackArg_call, r0, r2, r3, a0, a1, a2, a3, a4, a5, a7, a8, a9, a10, a11, a13, a15,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt k32, Nat.mod_eq_of_lt el32, Nat.mod_eq_of_lt dl32,
    Nat.mod_eq_of_lt pl32, Nat.mod_eq_of_lt ql32] at po
  rw [BitVec.setWidth_append_eq_right] at po
  exact po

/-- The call of `vg_rsa_pkcs1_decrypt_precomputed`'s code `c`, by its
contract. -/
theorem call_vp {c : Prog isa} (hv : Verified target c cK) (hst : FrameStack.armStack c ≤ calleeStack)
    (name : String) (P : EP) : VP (R1 P) (.call name c) (R2 P) := by
  refine VG.Proof.RsaPkcs1Sig.Arm.VP.callF hv hst (cRd P) (cWr P) (fun _ _ h => call_pre h)
    (fun σ s h => ?_) (fun σ s h => ?_) (fun _ _ _ _ h₁ h₂ => call_pub h₁ h₂)
    (fun σ s s' h rd wr sp fr _ po => ?_)
  · obtain ⟨⟨hi, hs⟩, -⟩ := h
    have ok := hi.ok
    obtain q0 : State.addr P.B = P.lay.fr 0 := by simp
    obtain hro : ∀ R ∈ P.ro, Covers [R] (s.rd ++ s.wr) := fun R hR =>
      Covers.left (Covers.of_mem fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hs.rd, ok.rd]; exact List.mem_append_left _ hR)
    obtain hrw : Covers (cWr P) s.wr :=
      Covers.of_mem fun r hr => by rw [hs.wr, ok.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)
    refine ⟨Covers.append_left (Covers.append_left (Covers.of_forall hro) ?_) hrw.right, hrw⟩
    refine Covers.cons ?_ Covers.nil
    rw [q0]; exact (Covers.one (hs.inFr (by show 0 + 84 ≤ frameBytes; decide))).right
  · rw [h.1.2.sp]; exact h.1.1.ok.B56
  · have hi := h.1.1
    have hs := h.1.2
    have ok := hi.ok
    obtain low : FrameStack.belowA s.sp calleeStack = P.lay.LOW := by rw [hs.sp]; exact ok.low_eq
    rw [low] at fr
    obtain st : P.lay.St σ s' := hs.write fr (fun r hr => by
      simp only [cWr, EP.rw, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨P.OUT, List.mem_cons_of_mem _ (List.mem_append_left _ List.mem_cons_self), fun _ h => h⟩
      · exact ⟨P.ML, List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)),
          fun _ h => h⟩
      · exact ⟨P.SCR, List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ List.mem_cons_self))), fun _ h => h⟩
      · exact ⟨P.lay.LOW, List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _)),
          fun _ h => h⟩) rd wr sp
    have := call_post h po
    rw [nB_at hi hs, eB_at hi hs, hs.ro (R := P.D) (by simp), hs.ro (R := P.PP) (by simp),
      hs.ro (R := P.QQ) (by simp), hs.ro (R := P.DP) (by simp), hs.ro (R := P.DQ) (by simp),
      hs.ro (R := P.QI) (by simp), hs.ro (R := P.INP) (by simp)] at this
    exact ⟨⟨hi, st⟩, this⟩

/-! ## After the call -/

/-- The message, or nothing. -/
def msgOf : Spec.Rsa.Outcome → List Byte
  | .ok M => M
  | _ => []

/-- The result. -/
def rOf : Spec.Rsa.Outcome → BitVec 32
  | .ok _ => 1
  | .invalid => 0
  | .fault => 2

/-- What `writtenMsg` states, the same way for every outcome. -/
theorem written_of {m : Mem} {o ml : Addr} {K : Nat} {r : BitVec 32} {v : Spec.Rsa.Outcome}
    (h : Spec.RsaPkcs1Enc.writtenMsg m o ml K r v) :
    r = rOf v ∧ Spec.Rsa.bytesAt m o K = List.replicate (K - (msgOf v).length) 0 ++ msgOf v ∧
      Spec.Rsa.wordsAt m ml 1 = [BitVec.ofNat 64 (msgOf v).length] := by
  cases v with
  | ok M => exact h
  | invalid =>
    obtain ⟨a, b, c⟩ := h
    exact ⟨a, by simp only [b, msgOf, List.length_nil, Nat.sub_zero, List.append_nil], by rw [c]; rfl⟩
  | fault =>
    obtain ⟨a, b, c⟩ := h
    exact ⟨a, by simp only [b, msgOf, List.length_nil, Nat.sub_zero, List.append_nil], by rw [c]; rfl⟩

/-- `writtenMsgFront`, the same way for every outcome. -/
theorem front_of {m : Mem} {o ml : Addr} {K : Nat} {r : BitVec 32} {v : Spec.Rsa.Outcome} (hr : r = rOf v)
    (hb : Spec.Rsa.bytesAt m o K = msgOf v ++ List.replicate (K - (msgOf v).length) 0)
    (hw : Spec.Rsa.wordsAt m ml 1 = [BitVec.ofNat 64 (msgOf v).length]) :
    Spec.RsaPkcs1Enc.writtenMsgFront m o ml K r v := by
  cases v with
  | ok M => exact ⟨hr, hb, hw⟩
  | invalid =>
    exact ⟨hr, by simp only [hb, msgOf, List.length_nil, Nat.sub_zero, List.nil_append], by rw [hw]; rfl⟩
  | fault =>
    exact ⟨hr, by simp only [hb, msgOf, List.length_nil, Nat.sub_zero, List.nil_append], by rw [hw]; rfl⟩

/-- The message and its length, in the run from `σ`. -/
abbrev Mv (P : EP) (σ : State) : List Byte := msgOf (oc P σ)
abbrev Lv (P : EP) (σ : State) : Nat := (Mv P σ).length

/-- What the call leaves in `out`. -/
abbrev Ob (P : EP) (σ : State) : List Byte := List.replicate (P.K - Lv P σ) 0 ++ Mv P σ

/-- What the rest keeps: the result in `sRes`, `*msg_len`, and the
message's length, at most `k`. -/
abbrev Kp (P : EP) (σ : State) (m : Mem) : Prop :=
  m.readW (P.lay.fr sRes) 32 = rOf (oc P σ) ∧
    Spec.Rsa.wordsAt m (State.addr P.ml) 1 = [BitVec.ofNat 64 (Lv P σ)] ∧ Lv P σ ≤ P.K

/-- After `after`. -/
abbrev R3 (P : EP) (σ s : State) : Prop :=
  (Ctx P.lay P.scr σ s ∧ In P σ) ∧ Kp P σ s.mem ∧ ∀ i < P.K, s.mem (byteAt P.out i) = (Ob P σ).getD i 0

theorem after_vp (P : EP) : VP (R2 P) (.block after) (R3 P) := by
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.2.sp.trans h₂.1.2.sp.symm) fun σ s ⟨⟨hi, hs⟩, hw⟩ => ?_
  have hg := hi.geo
  have ok := hi.ok
  obtain ⟨r0, hb, hm⟩ := written_of hw
  obtain ⟨a21, r21, v21⟩ := argAt hi hs (j := 21) (by decide)
  replace v21 : s.mem.readW (P.lay.fr (arg 21)) 32 = P.scr := v21
  obtain hwp : WP isa (.block after) s fun t =>
      t.mem = (s.mem.writeW (P.lay.fr sRes) (s.gpr .r0)).writeW (P.lay.fr sS) P.scr ∧
        t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
    prun [after, sp0, ld, st, hs.sp, a21, r21, v21, slotAt hi (d := sRes) (by decide),
      slotAt hi (d := sS) (by decide), hs.inFr (d := sRes) (n := 4) (by show sRes + 4 ≤ frameBytes; decide),
      hs.inFr (d := sS) (n := 4) (by show sS + 4 ≤ frameBytes; decide), arg_lt, Proof.RsaOaep.Arm.sRes_lt, rdArg]
  refine WP.mono hwp fun t ⟨m, rd, wr, sp⟩ => ?_
  obtain fr : Frame [slotR P.lay sRes, slotR P.lay sS] s.mem t.mem := by
    rw [m]
    exact ((slot_frame _ _ _ _).mono (by simp)).trans ((slot_frame _ _ _ _).mono (by simp))
  obtain apart : ∀ {R : Region}, R ∈ P.rw → ∀ r ∈ [slotR P.lay sRes, slotR P.lay sS], R.Disjoint r :=
    fun hR r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (ok.stk_fr (.inr hR) (by show sRes + 4 ≤ frameBytes + 56; decide)).symm
      · exact (ok.stk_fr (.inr hR) (by show sS + 4 ≤ frameBytes + 56; decide)).symm
  obtain hK : P.K ≤ 2 ^ 64 := by have := hi.k1024; omega_using [this]
  obtain hl : Lv P σ ≤ P.K := by
    have e := congrArg List.length hb
    simp only [bytesAt_length, List.length_append, List.length_replicate] at e
    show (msgOf (oc P σ)).length ≤ P.K
    omega_using [e]
  refine ⟨⟨⟨hs.write fr (fun r hr => ?_) rd wr sp, ?_⟩, hi⟩, ⟨?_, ?_, hl⟩, fun i hi' => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Proof.RsaPss.Arm.slotW hg (by decide)
  · rw [m, Mem.readW_writeW_self32]
  · rw [m, Proof.RsaPss.Arm.slot_ww _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32, r0]
  · rw [wordsAt_frame fr (n := 1) (apart (R := P.ML) (by simp)) (by decide)]; exact hm
  · rw [← bytesAt_frame fr (apart (R := P.OUT) (by simp)) hK] at hb
    rw [byteAt, ← bytesAt_getD (m := t.mem) hi' 0, hb]

open VG.Impl.RsaPss.Arm (mw atS sA sD sPc countLoop passBody passNext)
open VG.Impl.RsaOaep.Arm (oBuf clrBuf passSet passOne outSet)
open VG.Impl.RsaPkcs1Enc.Arm.Front (inSet mlArg mlLoad shInit shift ret tail)
open VG.Proof.X25519.Arm (dpVal)

/-! ## What the rest keeps -/

/-- What misses `Kp`'s memory. -/
abbrev Away (P : EP) (r : Region) : Prop := (slotR P.lay sRes).Disjoint r ∧ P.ML.Disjoint r

theorem Kp.keep {P : EP} {σ : State} {rs : List Region} {m m' : Mem} (hk : Kp P σ m) (hf : Frame rs m m')
    (ha : ∀ r ∈ rs, Away P r) : Kp P σ m' :=
  ⟨slot_keep hf (fun r hr => (ha r hr).1) hk.1,
    by rw [wordsAt_frame hf (n := 1) (fun r hr => (ha r hr).2) (by decide)]; exact hk.2.1, hk.2.2⟩

section
variable {P : EP} {σ : State} (hi : In P σ)
include hi

/-- Our part of `scratch` is in `scratch`. -/
theorem scr_sub {o n : Nat} (h : o + n ≤ oRsa) : Region.Sub (sR P.scr o n) P.SCR := by
  have hs := hi.slK
  have hK := hi.k64
  unfold Spec.Rsa.scratchWords at hs
  exact Offset.sub_base _ (by unfold oRsa at h; omega_using [h, hs, hK])

theorem away_buf {o n : Nat} (h : o + n ≤ oRsa) : Away P (sR P.scr o n) :=
  ⟨hi.geo.slot hi.ok h (by rw [hi.geo.F]; decide), (rw_pair hi).2.2.sub_right (scr_sub hi h)⟩

/-- `out` misses our part of `scratch`. -/
theorem out_buf {o n : Nat} (h : o + n ≤ oRsa) : P.OUT.Disjoint (sR P.scr o n) :=
  (rw_pair hi).2.1.sub_right (scr_sub hi h)

theorem away_out : Away P P.OUT :=
  ⟨(hi.ok.stk_fr (.inr (by simp)) (by show sRes + 4 ≤ frameBytes + 56; decide)), (rw_pair hi).1.symm⟩

theorem away_slot {d : Nat} (hd : d + 4 ≤ frameBytes) (h : d + 4 ≤ sRes ∨ sRes + 4 ≤ d) : Away P (slotR P.lay d) :=
  ⟨slotSep (by decide) hd (by omega_using [h]),
    (hi.ok.stk_fr (.inr (by simp)) (by show d + 4 ≤ frameBytes + 56; unfold frameBytes at hd ⊢; omega_using [hd])).symm⟩

/-- `out` as a buffer the body reads and writes. -/
theorem out_w : WBuf P.lay P.out P.K := by
  have ok := hi.ok
  exact ⟨hi.out_fit, by have := hi.k1024; omega_using [this], ⟨P.OUT, by simp, Region.contains_self _ _⟩,
    ok.stk_fr (.inr (by simp)) (by show sS + 4 ≤ frameBytes + 56; decide)⟩

end

/-! ## The buffer cleared -/

/-- What stays until `out` is copied. -/
abbrev Iv (P : EP) (σ : State) (m : Mem) : Prop :=
  In P σ ∧ Kp P σ m ∧ ∀ i < P.K, m (byteAt P.out i) = (Ob P σ).getD i 0

/-- After the buffer is cleared. -/
abbrev A1 (P : EP) (σ s : State) : Prop :=
  Ctx P.lay P.scr σ s ∧ Iv P σ s.mem ∧ ∀ j < 2048, s.mem (Proof.RsaPss.Arm.sa P.scr (oBuf + j)) = 0

theorem clr_vp (P : EP) : VP (R3 P) (.seq (.block clrBuf) Impl.Bignum.Arm.maskBytes) (A1 P) := by
  by_cases hP : ∃ σ, In P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1.2⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  refine VP.seq (G := fun σ s => (Ctx P.lay P.scr σ s ∧ Iv P σ s.mem) ∧ s.gpr .r0 = P.scr + BitVec.ofNat 32 oBuf ∧
      s.gpr .r2 = 0 ∧ s.gpr .lr = BitVec.ofNat 32 2048)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.1.st.sp.trans h₂.1.1.st.sp.symm)
      fun σ s ⟨⟨hc, hi⟩, hk, ho⟩ => ?_) ?_
  · have hw : WP isa (.block clrBuf) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r0 = P.scr + BitVec.ofNat 32 oBuf ∧ t.gpr .r2 = 0 ∧ t.gpr .lr = BitVec.ofNat 32 2048 := by
      prun [clrBuf, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS,
        movw_val (show oBuf < 2 ^ 16 by decide), movw_val (show 2048 < 2 ^ 16 by decide)]
    exact WP.mono hw fun t ⟨m, rd, wr, sp, r0, r2, lr⟩ =>
      ⟨⟨hc.regs rd wr sp m, m ▸ ⟨hi, hk, ho⟩⟩, r0, r2, lr⟩
  obtain aB : State.addr (P.scr + BitVec.ofNat 32 oBuf) = Proof.RsaPss.Arm.sa P.scr oBuf := hg.addr (by decide)
  refine (zero_vp (hg.wbuf (o := oBuf) (n := 2048) (by decide) (by decide)) (by decide)
    (Inv := Iv P) fun σ m m' ⟨hi, hk, ho⟩ hf => by
      rw [aB] at hf
      obtain ad : ∀ r ∈ [sR P.scr oBuf 2048], Region.Disjoint P.OUT r := fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact out_buf hi (by decide)
      refine ⟨hi, hk.keep hf fun r hr => ?_, fun i hi' => ?_⟩
      · simp only [List.mem_singleton] at hr; subst hr; exact away_buf hi (by decide)
      · rw [← ho i hi']
        exact hf _ fun r hr hc => ad r hr _ (contains_byte (Region.contains_self _ _) hi.out_fit hi') hc).mono
    (fun σ s ⟨⟨hc, hm⟩, r0, r2, lr⟩ => ⟨hc, hm, r0, r2, lr⟩)
    fun σ s ⟨hc, hm, hz⟩ => ⟨hc, hm, fun j hj => by rw [← hg.byteAt_scr (by unfold oBuf oRsa; omega_using [hj])]; exact hz j hj⟩

/-! ## `out` to the buffer -/

theorem Ob_length {P : EP} {σ : State} (h : Lv P σ ≤ P.K) : (Ob P σ).length = P.K := by
  have h' : (Mv P σ).length ≤ P.K := h
  simp only [Ob, Lv, List.length_append, List.length_replicate]; omega_using [h']

/-- After `out` is copied to the buffer: the buffer holds `out`, zeros after
it. -/
abbrev A2 (P : EP) (σ s : State) : Prop :=
  Ctx P.lay P.scr σ s ∧ (In P σ ∧ Kp P σ s.mem) ∧
    ∀ j < 2048, s.mem (Proof.RsaPss.Arm.sa P.scr (oBuf + j)) = (Ob P σ).getD j 0

theorem in_vp (P : EP) : VP (A1 P) (.seq (.block inSet) Impl.Bignum.Arm.copyBytes) (A2 P) := by
  by_cases hP : ∃ σ, In P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.2.1.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  have hK := hi₀.k1024
  have hK64 := hi₀.k64
  refine VP.seq (G := fun σ s => (Ctx P.lay P.scr σ s ∧ (In P σ ∧ Kp P σ s.mem ∧
      ∀ j < 2048, P.K ≤ j → s.mem (Proof.RsaPss.Arm.sa P.scr (oBuf + j)) = 0)) ∧
      s.gpr .r0 = P.scr + BitVec.ofNat 32 oBuf ∧ s.gpr .r1 = P.out ∧ s.gpr .lr = BitVec.ofNat 32 P.K ∧
      ∀ i < P.K, s.mem (byteAt P.out i) = (Ob P σ).getD i 0)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm)
      fun σ s ⟨hc, ⟨hi, hk, ho⟩, hz⟩ => ?_) ?_
  · obtain ⟨a0, r0, v0⟩ := argAt hi hc.st (j := 0) (by decide)
    obtain ⟨a4, r4, v4⟩ := argAt hi hc.st (j := 4) (by decide)
    replace v0 : s.mem.readW (P.lay.fr (arg 0)) 32 = P.out := v0
    replace v4 : s.mem.readW (P.lay.fr (arg 4)) 32 = BitVec.ofNat 32 P.K := v4
    have hw : WP isa (.block inSet) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r0 = P.scr + BitVec.ofNat 32 oBuf ∧ t.gpr .r1 = P.out ∧ t.gpr .lr = BitVec.ofNat 32 P.K := by
      prun [inSet, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, a0, r0, v0, a4, r4, v4, arg_lt,
        movw_val (show oBuf < 2 ^ 16 by decide)]
    exact WP.mono hw fun t ⟨m, rd, wr, sp, t0, t1, tl⟩ =>
      ⟨⟨hc.regs rd wr sp m, m ▸ ⟨hi, hk, fun j hj _ => hz j hj⟩⟩, t0, t1, tl, m ▸ ho⟩
  obtain aB : State.addr (P.scr + BitVec.ofNat 32 oBuf) = Proof.RsaPss.Arm.sa P.scr oBuf := hg.addr (by decide)
  refine (copy_vp (hg.wbuf (o := oBuf) (n := P.K) (by unfold oBuf oRsa; omega_using [hK]) (by omega_using [hK64]))
    (out_w hi₀).rbuf (by rw [aB]; exact out_buf hi₀ (by unfold oBuf oRsa; omega_using [hK]))
    (by omega_using [hK64]) (Inv := fun σ m => In P σ ∧ Kp P σ m ∧
      ∀ j < 2048, P.K ≤ j → m (Proof.RsaPss.Arm.sa P.scr (oBuf + j)) = 0)
    (f := fun σ i => (Ob P σ).getD i 0) fun σ m m' ⟨hi, hk, hz⟩ hf => by
      rw [aB] at hf
      refine ⟨hi, hk.keep hf fun r hr => ?_, fun j hj hj' => ?_⟩
      · simp only [List.mem_singleton] at hr; subst hr
        exact away_buf hi (by unfold oBuf oRsa; omega_using [hK])
      · rw [← hz j hj hj']
        exact hf _ fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Geo.sep (scr := P.scr) (o := oBuf + j) (n := 1) (by omega_using [hj']) (by unfold oBuf oRsa; omega_using [hj])
            (by unfold oBuf oRsa; omega_using [hK]) _ (Region.contains_self _ _)).mono
    (fun σ s ⟨⟨hc, hm⟩, r0, r1, lr, hf⟩ => ⟨hc, hm, r0, r1, lr, hf⟩)
    fun σ s ⟨hc, ⟨hi, hk, hz⟩, hb⟩ => ⟨hc, ⟨hi, hk⟩, fun j hj => ?_⟩
  by_cases e : j < P.K
  · rw [← hb j e, hg.byteAt_scr (by unfold oBuf oRsa; omega_using [hj])]
  · rw [hz j hj (by omega_using [e]), List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by rw [Ob_length hk.2.2]; omega_using [e])]; rfl

/-! ## The shift -/

theorem readW_lo32 (m : Mem) (a : Addr) : m.readW a 32 = (m.readW a 64).setWidth 32 := by
  obtain e := Mem.read_eq_of_bytes (m := m) (a := a) (n := 4) (v := (m.readW a 64).setWidth 32) fun i hi => by
    rw [BitVec.extractLsb'_setWidth_of_le (by omega_using [hi])]
    show _ = ((m.read a 8).setWidth 64).extractLsb' (8 * i) 8
    rw [BitVec.extractLsb'_setWidth_of_le (by omega_using [hi]), Mem.extractLsb'_read m a (by omega_using [hi] : i < 8)]
  show (m.read a 4).setWidth 32 = _
  rw [e]; exact BitVec.setWidth_eq _

/-- `*msg_len`'s low word. -/
theorem ml_low {m : Mem} {a : Addr} {L : Nat} (h : Spec.Rsa.wordsAt m a 1 = [BitVec.ofNat 64 L]) :
    m.readW a 32 = BitVec.ofNat 32 L := by
  obtain h64 : m.readW a 64 = BitVec.ofNat 64 L := by
    simpa [Spec.Rsa.wordsAt] using h
  rw [readW_lo32, h64]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  exact Nat.mod_mod_of_dvd _ (by decide)

/-- The shift's distance: `k - L`. -/
abbrev sv (P : EP) (σ : State) : Nat := P.K - Lv P σ

/-- `msg_len` in `r1`. -/
abbrev B1 (P : EP) (σ s : State) : Prop := A2 P σ s ∧ s.gpr .r1 = P.ml

theorem mlArg_vp (P : EP) : VP (A2 P) (.block mlArg) (B1 P) := by
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, ⟨hi, hk⟩, hb⟩ => ?_
  have hg := hi.geo
  obtain ⟨a2, r2, v2⟩ := argAt hi hc.st (j := 2) (by decide)
  replace v2 : s.mem.readW (P.lay.fr (arg 2)) 32 = P.ml := v2
  have hw : WP isa (.block mlArg) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.gpr .r1 = P.ml := by
    prun [mlArg, sp0, ld, hc.st.sp, a2, r2, v2, arg_lt]
  exact WP.mono hw fun t ⟨m, rd, wr, sp, t1⟩ => ⟨⟨hc.regs rd wr sp m, ⟨hi, m ▸ hk⟩, m ▸ hb⟩, t1⟩

theorem mlLoad_cert : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r1]) (.block mlLoad) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- `*msg_len`'s low word, `L`, in `r1`. -/
abbrev B2 (P : EP) (σ s : State) : Prop := A2 P σ s ∧ s.gpr .r1 = BitVec.ofNat 32 (Lv P σ)

theorem mlLoad_vp (P : EP) : VP (B1 P) (.block mlLoad) (B2 P) := by
  refine VP.taint _ mlLoad_cert (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s ⟨⟨hc, ⟨hi, hk⟩, hb⟩, r1⟩ => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
    rw [h₁.2, h₂.2]
  have fit := hi.ml_fit
  obtain a0 : State.addr (P.ml + BitVec.ofNat 32 0) = State.addr P.ml := by rw [BitVec.add_zero]
  obtain rm : InRegions (s.rd ++ s.wr) (State.addr P.ml) 4 :=
    ⟨P.ML, List.mem_append_right _ (by rw [hc.st.wr, hi.ok.wr]; simp),
      by have := Offset.contains_base (State.addr P.ml) (d := 0) (n := 4) (k := 8) (by decide) (by decide)
         rwa [BitVec.add_zero] at this⟩
  have hw : WP isa (.block mlLoad) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.gpr .r1 = s.mem.readW (State.addr P.ml) 32 := by
    prun [mlLoad, r1, a0, rm]
  exact WP.mono hw fun t ⟨m, rd, wr, sp, t1⟩ =>
    ⟨⟨hc.regs rd wr sp m, ⟨hi, m ▸ hk⟩, m ▸ hb⟩, t1.trans (ml_low hk.2.1)⟩

/-- What the shift keeps. -/
abbrev Zk (P : EP) (σ : State) (m : Mem) : Prop := In P σ ∧ Kp P σ m

theorem Zk.keep {P : EP} {σ : State} {rs : List Region} {m m' : Mem} (hz : Zk P σ m) (hf : Frame rs m m')
    (ha : ∀ r ∈ rs, Away P r) : Zk P σ m' := ⟨hz.1, hz.2.keep hf ha⟩

/-- `out`'s bytes are zeros from `k` on. -/
theorem Ob_getD_ge {P : EP} {σ : State} (hl : Lv P σ ≤ P.K) {x : Nat} (hx : P.K ≤ x) : (Ob P σ).getD x 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [Ob_length hl]; exact hx)]; rfl

/-- The bounds a pass needs. -/
theorem shB {P : EP} {σ : State} {m : Mem} (hk : Zk P σ m) : 64 ≤ P.K ∧ P.K ≤ 1024 ∧ sv P σ < 2048 := by
  have hK := hk.1.k1024
  exact ⟨hk.1.k64, hK, by show P.K - Lv P σ < 2048; omega_using [hK]⟩

/-- After `p` passes. -/
abbrev SH (P : EP) (σ : State) (p : Nat) (m : Mem) : Prop :=
  m.readW (P.lay.fr sA) 32 = BitVec.ofNat 32 (sv P σ / 2 ^ p) ∧
    m.readW (P.lay.fr sD) 32 = BitVec.ofNat 32 (2 ^ p) ∧
    m.readW (P.lay.fr sPc) 32 = BitVec.ofNat 32 (11 - p) ∧
    ∀ j < 2048, m (Proof.RsaPss.Arm.sa P.scr (oBuf + j)) = (Ob P σ).getD (j + sv P σ % 2 ^ p) 0

/-- The shift's distance, its first pass's, and its passes. -/
theorem shInit_vp (P : EP) :
    VP (B2 P) (.block shInit) (fun σ s => Ctx P.lay P.scr σ s ∧ Zk P σ s.mem ∧ SH P σ 0 s.mem) := by
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.1.st.sp.trans h₂.1.1.st.sp.symm)
    fun σ s ⟨⟨hc, ⟨hi, hk⟩, hb⟩, r1⟩ => ?_
  have hg := hi.geo
  obtain ⟨σ', ok⟩ := hg.ok
  obtain ⟨a4, r4, v4⟩ := argAt hi hc.st (j := 4) (by decide)
  replace v4 : s.mem.readW (P.lay.fr (arg 4)) 32 = BitVec.ofNat 32 P.K := v4
  obtain hw : WP isa (.block shInit) s fun t =>
      t.mem = ((s.mem.writeW (P.lay.fr sA) (BitVec.ofNat 32 (sv P σ))).writeW
        (P.lay.fr sD) (BitVec.ofNat 32 1)).writeW (P.lay.fr sPc) (BitVec.ofNat 32 11) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
    prun [shInit, sp0, ld, st, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, a4, r4, v4, r1, arg_lt,
      slotAt hi (d := sA) (by decide), slotAt hi (d := sD) (by decide), slotAt hi (d := sPc) (by decide),
      hc.st.inFr (d := sA) (n := 4) (by show sA + 4 ≤ frameBytes; decide),
      hc.st.inFr (d := sD) (n := 4) (by show sD + 4 ≤ frameBytes; decide),
      hc.st.inFr (d := sPc) (n := 4) (by show sPc + 4 ≤ frameBytes; decide),
      movw_val (show 1 < 2 ^ 16 by decide), movw_val (show 11 < 2 ^ 16 by decide),
      Offset.ofNat_sub_ofNat (w := 32) hk.2.2, dpVal]
  refine WP.mono hw fun t ⟨m, rd, wr, sp⟩ => ?_
  obtain fr : Frame [slotR P.lay sA, slotR P.lay sD, slotR P.lay sPc] s.mem t.mem := by
    rw [m]
    exact ((slot_frame _ _ _ _).mono (by simp) |>.trans ((slot_frame _ _ _ _).mono (by simp))).trans
      ((slot_frame _ _ _ _).mono (by simp))
  obtain aw : ∀ r ∈ [slotR P.lay sA, slotR P.lay sD, slotR P.lay sPc], Away P r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact away_slot hi (by decide) (by decide)
  refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp, ⟨hi, hk.keep fr aw⟩, ?_, ?_, ?_, fun j hj => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact slotW hg (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact slotSep (by decide) (by decide) (by decide)
  · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), slot_ww _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32, Nat.pow_zero, Nat.div_one]
  · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [m, Mem.readW_writeW_self32]
  · rw [Nat.pow_zero, Nat.mod_one, Nat.add_zero]
    refine (sbytes_keep fr (fun r hr => ?_) (by unfold oBuf; omega_using []) hb) j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact (hg.slot ok (by decide) (by rw [hg.F]; decide)).symm

/-- A pass's registers. -/
theorem passSet_vp (P : EP) {p : Nat} :
    VP (fun σ s => Ctx P.lay P.scr σ s ∧ Zk P σ s.mem ∧ SH P σ p s.mem) (.block passSet)
      (fun σ s => (Ctx P.lay P.scr σ s ∧ Zk P σ s.mem ∧ SH P σ p s.mem) ∧
        s.gpr .r0 = P.scr + BitVec.ofNat 32 oBuf ∧
        s.gpr .r1 = P.scr + BitVec.ofNat 32 (oBuf + 2 ^ p) ∧ s.gpr .lr = BitVec.ofNat 32 1024 ∧
        s.gpr .r2 = maskOf (sv P σ / 2 ^ p % 2 = 1)) := by
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hk, hs⟩ => ?_
  have hg := hk.1.geo
  obtain ⟨-, -, hsv⟩ := shB hk
  have hav : sv P σ / 2 ^ p < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega_using [hsv])
  have hw : WP isa (.block passSet) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.gpr .r0 = P.scr + BitVec.ofNat 32 oBuf ∧
      t.gpr .r1 = P.scr + BitVec.ofNat 32 (oBuf + 2 ^ p) ∧ t.gpr .lr = BitVec.ofNat 32 1024 ∧
      t.gpr .r2 = 0 - (BitVec.ofNat 32 (sv P σ / 2 ^ p) &&& 1) := by
    prun [passSet, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, hs.1, hs.2.1,
      movw_val (show oBuf < 2 ^ 16 by decide), movw_val (show 1024 < 2 ^ 16 by decide),
      movw_val (show 0 < 2 ^ 16 by decide), BitVec.add_assoc, BitVec.ofNat_add_ofNat, dpVal]
    rfl
  exact WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1, lr, r2⟩ =>
    ⟨⟨hc.regs rd wr sp m, m ▸ hk, m ▸ hs⟩, r0, r1, lr, by rw [r2, Vf.mask_bit hav]⟩

/-- Between a pass's bytes and its next stage. -/
abbrev SM (P : EP) (σ : State) (p : Nat) (m : Mem) : Prop :=
  m.readW (P.lay.fr sA) 32 = BitVec.ofNat 32 (sv P σ / 2 ^ p) ∧
    m.readW (P.lay.fr sD) 32 = BitVec.ofNat 32 (2 ^ p) ∧
    m.readW (P.lay.fr sPc) 32 = BitVec.ofNat 32 (11 - p) ∧
    ∀ j < 2048, m (Proof.RsaPss.Arm.sa P.scr (oBuf + j)) = (Ob P σ).getD (j + sv P σ % 2 ^ (p + 1)) 0

/-- A pass's bytes. -/
theorem passMid_vp (P : EP) (hP : ∃ σ, In P σ) {p : Nat} (hp : p < 11) :
    VP (fun σ s => (Ctx P.lay P.scr σ s ∧ Zk P σ s.mem ∧ SH P σ p s.mem) ∧
        s.gpr .r0 = P.scr + BitVec.ofNat 32 oBuf ∧
        s.gpr .r1 = P.scr + BitVec.ofNat 32 (oBuf + 2 ^ p) ∧ s.gpr .lr = BitVec.ofNat 32 1024 ∧
        s.gpr .r2 = maskOf (sv P σ / 2 ^ p % 2 = 1))
      (countLoop passBody)
      (fun σ s => Ctx P.lay P.scr σ s ∧ Zk P σ s.mem ∧ SM P σ p s.mem) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  obtain hp9 : 2 ^ p ≤ 2 ^ 10 := Nat.pow_le_pow_right (by decide) (by omega_using [hp])
  obtain hp0 : 0 < 2 ^ p := Nat.two_pow_pos p
  refine (pass_vp hg (o := oBuf) (d := 2 ^ p) (n := 1024) (by decide) hp0
    (by unfold oBuf oRsa; omega_using [hp9])
    (c := fun σ => sv P σ / 2 ^ p % 2 = 1) (X := fun σ m => Zk P σ m ∧ SH P σ p m)).mono
    (fun σ s ⟨⟨hc, hk, hs⟩, r0, r1, lr, r2⟩ => ⟨hc, ⟨hk, hs⟩, r0, r1, lr, r2⟩)
    fun σ s ⟨hc, m₀, ⟨hk, hs⟩, fr, hsel⟩ => ?_
  obtain ⟨-, hK, hsv⟩ := shB hk
  obtain hl := hk.2.2.2
  obtain ks : ∀ d, d + 4 ≤ frameBytes → s.mem.readW (P.lay.fr d) 32 = m₀.readW (P.lay.fr d) 32 :=
    fun d hd => slot_keep (v := m₀.readW (P.lay.fr d) 32) fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hg.slot ok (by unfold oBuf oRsa; omega_using []) (by rw [hg.F]; unfold frameBytes at hd ⊢; omega_using [hd])) rfl
  refine ⟨hc, hk.keep fr fun r hr => ?_, by rw [ks _ (by decide)]; exact hs.1,
    by rw [ks _ (by decide)]; exact hs.2.1, by rw [ks _ (by decide)]; exact hs.2.2.1, fun j hj => ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact away_buf hk.1 (by unfold oBuf oRsa; omega_using [])
  obtain ms := Vf.mod_succ (sv P σ) p
  by_cases e : j < 1024
  · rw [hsel j e]
    by_cases hc' : sv P σ / 2 ^ p % 2 = 1
    · rw [ite_eq_left hc', show oBuf + 2 ^ p + j = oBuf + (2 ^ p + j) by omega_using [],
        hs.2.2.2 _ (by omega_using [hp9, e])]
      congr 1; rw [ms, hc']; omega_using []
    · rw [ite_eq_right hc', hs.2.2.2 _ hj]
      congr 1; rw [ms, show sv P σ / 2 ^ p % 2 = 0 by omega_using [hc']]; omega_using []
  · have hm : s.mem (Proof.RsaPss.Arm.sa P.scr (oBuf + j)) = m₀ (Proof.RsaPss.Arm.sa P.scr (oBuf + j)) :=
      fr _ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Geo.sep (scr := P.scr) (o := oBuf + j) (n := 1) (by omega_using [e])
          (by unfold oBuf oRsa; omega_using [hj]) (by unfold oBuf oRsa; omega_using []) _ (Region.contains_self _ _)
    rw [hm, hs.2.2.2 j hj, Ob_getD_ge hl (by omega_using [e, hK]), Ob_getD_ge hl (by omega_using [e, hK])]

/-- The next pass's slots, and the flags of whether it was the last. -/
theorem passNext_vp (P : EP) {p : Nat} (hp : p < 11) :
    VP (fun σ s => Ctx P.lay P.scr σ s ∧ Zk P σ s.mem ∧ SM P σ p s.mem) (.block passNext)
      (fun σ s => (Ctx P.lay P.scr σ s ∧ Zk P σ s.mem ∧ SH P σ (p + 1) s.mem) ∧
        s.z = decide (11 - (p + 1) = 0)) := by
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hk, hs⟩ => ?_
  have hi := hk.1
  have hg := hi.geo
  obtain ⟨σ', ok⟩ := hg.ok
  obtain ⟨-, -, hsv⟩ := shB hk
  obtain hp9 : 2 ^ p ≤ 2 ^ 10 := Nat.pow_le_pow_right (by decide) (by omega_using [hp])
  obtain ea : BitVec.ofNat 32 (sv P σ / 2 ^ p) >>> 1 = BitVec.ofNat 32 (sv P σ / 2 ^ (p + 1)) := by
    rw [VG.Proof.MdStream.Arm.ofNat_shr (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega_using [hsv])),
      Nat.div_div_eq_div_mul, Nat.pow_one, ← Nat.pow_succ]
  obtain ed : BitVec.ofNat 32 (2 ^ p) + BitVec.ofNat 32 (2 ^ p) = BitVec.ofNat 32 (2 ^ (p + 1)) := by
    rw [BitVec.ofNat_add_ofNat, Nat.pow_succ]; congr 1; omega_using []
  obtain ec : BitVec.ofNat 32 (11 - p) - 1 = BitVec.ofNat 32 (11 - (p + 1)) := by
    rw [show 11 - p = (11 - (p + 1)) + 1 by omega_using [hp]]; exact sub_one_ofNat (by omega_using [])
  obtain hz0 : ∀ y : BitVec 32, y - 0 = y := fun y => BitVec.sub_zero y
  obtain w1 : ∀ v, (s.mem.writeW (P.lay.fr sA) v).readW (P.lay.fr sD) 32 = BitVec.ofNat 32 (2 ^ p) :=
    fun v => by rw [slot_ww _ _ (by decide) (by decide) (by decide)]; exact hs.2.1
  obtain w2 : ∀ v v', ((s.mem.writeW (P.lay.fr sA) v).writeW (P.lay.fr sD) v').readW
      (P.lay.fr sPc) 32 = BitVec.ofNat 32 (11 - p) := fun v v' => by
    rw [slot_ww _ _ (by decide) (by decide) (by decide), slot_ww _ _ (by decide) (by decide) (by decide)]
    exact hs.2.2.1
  obtain hw : WP isa (.block passNext) s fun t =>
      t.mem = ((s.mem.writeW (P.lay.fr sA) (BitVec.ofNat 32 (sv P σ / 2 ^ (p + 1)))).writeW
        (P.lay.fr sD) (BitVec.ofNat 32 (2 ^ (p + 1)))).writeW (P.lay.fr sPc)
          (BitVec.ofNat 32 (11 - (p + 1))) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.z = decide (11 - (p + 1) = 0) := by
    prun [passNext, sp0, ld, st, hc.st.sp, hc.aFr hg, hc.rFr hg, hs.1, hs.2.1, hs.2.2.1,
      slotAt hi (d := sA) (by decide), slotAt hi (d := sD) (by decide), slotAt hi (d := sPc) (by decide),
      hc.st.inFr (d := sA) (n := 4) (by show sA + 4 ≤ frameBytes; decide),
      hc.st.inFr (d := sD) (n := 4) (by show sD + 4 ≤ frameBytes; decide),
      hc.st.inFr (d := sPc) (n := 4) (by show sPc + 4 ≤ frameBytes; decide), ea, ed, ec, hz0, w1, w2,
      VG.Proof.X25519.Arm.ofNat_beq_zero (show 11 - (p + 1) < 2 ^ 32 by omega_using []), dpVal]
  refine WP.mono hw fun t ⟨m, rd, wr, sp, z⟩ => ?_
  obtain fr : Frame [slotR P.lay sA, slotR P.lay sD, slotR P.lay sPc] s.mem t.mem := by
    rw [m]
    exact ((slot_frame _ _ _ _).mono (by simp) |>.trans ((slot_frame _ _ _ _).mono (by simp))).trans
      ((slot_frame _ _ _ _).mono (by simp))
  obtain aw : ∀ r ∈ [slotR P.lay sA, slotR P.lay sD, slotR P.lay sPc], Away P r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact away_slot hi (by decide) (by decide)
  refine ⟨⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp, hk.keep fr aw, ?_, ?_, ?_,
    sbytes_keep fr (fun r hr => ?_) (by unfold oBuf; omega_using []) hs.2.2.2⟩, z⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact slotW hg (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact slotSep (by decide) (by decide) (by decide)
  · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), slot_ww _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]
  · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [m, Mem.readW_writeW_self32]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact (hg.slot ok (by decide) (by rw [hg.F]; decide)).symm

/-- A pass. -/
theorem onePass_vp (P : EP) (hP : ∃ σ, In P σ) {p : Nat} (hp : p < 11) :
    VP (fun σ s => Ctx P.lay P.scr σ s ∧ Zk P σ s.mem ∧ SH P σ p s.mem) passOne
      (fun σ s => (Ctx P.lay P.scr σ s ∧ Zk P σ s.mem ∧ SH P σ (p + 1) s.mem) ∧
        s.z = decide (11 - (p + 1) = 0)) :=
  (passSet_vp P).seq ((passMid_vp P hP hp).seq (passNext_vp P hp))

/-- After the shift: the buffer holds `out` from byte `k - L` on, zeros
after it. -/
abbrev SF (P : EP) (σ s : State) : Prop :=
  Ctx P.lay P.scr σ s ∧ Zk P σ s.mem ∧
    ∀ j < 2048, s.mem (Proof.RsaPss.Arm.sa P.scr (oBuf + j)) = (Ob P σ).getD (j + sv P σ) 0

/-- `out` shifted left by `k - L` bytes. -/
theorem shift_vp (P : EP) : VP (A2 P) shift (SF P) := by
  by_cases hP : ∃ σ, In P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.2.1.1⟩
  refine (mlArg_vp P).seq ((mlLoad_vp P).seq ((shInit_vp P).seq ?_))
  let I : Nat → State → State → Prop := fun k σ s => k ≤ 11 ∧ Ctx P.lay P.scr σ s ∧ Zk P σ s.mem ∧
    SH P σ (11 - k) s.mem
  refine (VP.loop (I := I) (fun k => ?_) 10).mono (fun σ s ⟨hc, hk, hs⟩ => ⟨by omega_using [], hc, hk, hs⟩)
    fun _ _ h => h
  by_cases hk : k ≤ 10
  swap
  · exact VP.empty fun σ s h' => hk (by have := h'.1; omega_using [this])
  refine (onePass_vp P hP (p := 10 - k) (by omega_using [hk])).mono
    (fun σ s ⟨_, hc, hq, hs⟩ => ⟨hc, hq, by rw [show 10 - k = 11 - (k + 1) by omega_using [hk]]; exact hs⟩)
    fun σ s ⟨⟨hc, hq, hs⟩, z⟩ => ⟨?_, fun h0 => ⟨hc, hq, fun j hj => ?_⟩,
      fun hpos => ⟨by omega_using [hk], hc, hq, ?_⟩⟩
  · rw [VG.Proof.X25519.Arm.eval_ne, z, show 11 - (10 - k + 1) = k by omega_using [hk]]; cases k <;> simp
  · subst h0
    obtain ⟨-, -, hsv⟩ := shB hq
    rw [hs.2.2.2 j hj, Nat.mod_eq_of_lt (show sv P σ < 2 ^ (10 - 0 + 1) by
      show sv P σ < 2048; omega_using [hsv])]
  · rw [show 11 - k = 10 - k + 1 by omega_using [hk]]; exact hs

/-! ## The buffer back to `out` -/

/-- After the copy back: `out` holds the buffer's first `k` bytes. -/
abbrev O1 (P : EP) (σ s : State) : Prop :=
  Ctx P.lay P.scr σ s ∧ Zk P σ s.mem ∧ ∀ i < P.K, s.mem (byteAt P.out i) = (Ob P σ).getD (i + sv P σ) 0

theorem out_vp (P : EP) : VP (SF P) (.seq (.block outSet) Impl.Bignum.Arm.copyBytes) (O1 P) := by
  by_cases hP : ∃ σ, In P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.2.1.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  have hK := hi₀.k1024
  have hK64 := hi₀.k64
  refine VP.seq (G := fun σ s => (Ctx P.lay P.scr σ s ∧ Zk P σ s.mem) ∧ s.gpr .r0 = P.out ∧
      s.gpr .r1 = P.scr + BitVec.ofNat 32 oBuf ∧ s.gpr .lr = BitVec.ofNat 32 P.K ∧
      ∀ i < P.K, s.mem (byteAt (P.scr + BitVec.ofNat 32 oBuf) i) = (Ob P σ).getD (i + sv P σ) 0)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm)
      fun σ s ⟨hc, hk, hb⟩ => ?_) ?_
  · have hi := hk.1
    obtain ⟨a0, r0, v0⟩ := argAt hi hc.st (j := 0) (by decide)
    obtain ⟨a4, r4, v4⟩ := argAt hi hc.st (j := 4) (by decide)
    replace v0 : s.mem.readW (P.lay.fr (arg 0)) 32 = P.out := v0
    replace v4 : s.mem.readW (P.lay.fr (arg 4)) 32 = BitVec.ofNat 32 P.K := v4
    have hw : WP isa (.block outSet) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r0 = P.out ∧ t.gpr .r1 = P.scr + BitVec.ofNat 32 oBuf ∧ t.gpr .lr = BitVec.ofNat 32 P.K := by
      prun [outSet, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, a0, r0, v0, a4, r4, v4, arg_lt,
        movw_val (show oBuf < 2 ^ 16 by decide)]
    refine WP.mono hw fun t ⟨m, rd, wr, sp, t0, t1, tl⟩ =>
      ⟨⟨hc.regs rd wr sp m, m ▸ hk⟩, t0, t1, tl, fun i hi' => ?_⟩
    rw [m, hg.byteAt_scr (by unfold oBuf oRsa; omega_using [hi', hK])]
    exact hb i (by omega_using [hi', hK])
  obtain aB : State.addr (P.scr + BitVec.ofNat 32 oBuf) = Proof.RsaPss.Arm.sa P.scr oBuf := hg.addr (by decide)
  exact (copy_vp (out_w hi₀) (hg.rbuf (o := oBuf) (n := P.K) (by unfold oBuf oRsa; omega_using [hK])
    (by omega_using [hK64])) (by rw [aB]; exact (out_buf hi₀ (by unfold oBuf oRsa; omega_using [hK])).symm)
    (by omega_using [hK64]) (Inv := Zk P) (f := fun σ i => (Ob P σ).getD (i + sv P σ) 0)
    fun σ m m' hz hf => hz.keep hf fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact away_out hz.1).mono
    (fun σ s ⟨⟨hc, hm⟩, r0, r1, lr, hf⟩ => ⟨hc, hm, r0, r1, lr, hf⟩) fun _ _ h => h

/-! ## The result -/

/-- What the shared contract states of the result `r` and the memory `m`. -/
def Res (P : EP) (σ : State) (m : Mem) (r : BitVec 32) : Prop :=
  Spec.RsaPkcs1Enc.writtenMsgFront m (State.addr P.out) (State.addr P.ml) P.K r (oc P σ)

/-- The end of the body. -/
def Fin (P : EP) (σ s : State) : Prop := S P σ s ∧ Res P σ s.mem (s.gpr .r0)

theorem Res_frame {P : EP} {σ : State} {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (ho : ∀ r ∈ rs, P.OUT.Disjoint r) (hm : ∀ r ∈ rs, P.ML.Disjoint r) (hK : P.K ≤ 2 ^ 64)
    {r : BitVec 32} (h : Res P σ m r) : Res P σ m' r := by
  unfold Res at h ⊢
  obtain eb := bytesAt_frame hf ho hK
  obtain ew := wordsAt_frame hf (n := 1) hm (by decide)
  revert h
  generalize oc P σ = o
  intro h
  cases o <;> exact ⟨h.1, eb.trans h.2.1, ew.trans h.2.2⟩

/-- The message, then zeros. -/
theorem front_bytes {P : EP} {σ : State} (hl : Lv P σ ≤ P.K) (i : Nat) :
    (Ob P σ).getD (i + sv P σ) 0 = (Mv P σ ++ List.replicate (P.K - Lv P σ) 0).getD i 0 := by
  have hl' : (Mv P σ).length ≤ P.K := hl
  have eL : Lv P σ = (Mv P σ).length := rfl
  by_cases e : i < Lv P σ
  · rw [Ob, getD_append_right _ _ _ (by simp only [List.length_replicate, sv]; omega_using []),
      getD_append_left _ _ _ e]
    simp only [List.length_replicate, sv]
    congr 1; omega_using [hl']
  · rw [Ob_getD_ge hl (by show P.K ≤ i + (P.K - Lv P σ); omega_using [e]), getD_append_right _ _ _ (by omega_using [e, eL]),
      List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split <;> rfl

theorem ret_vp (P : EP) : VP (O1 P) (.block ret) (Fin P) := by
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, ⟨hi, hk⟩, ho⟩ => ?_
  have hg := hi.geo
  have hw : WP isa (.block ret) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.gpr .r0 = s.mem.readW (P.lay.fr sRes) 32 := by
    prun [Impl.RsaPkcs1Enc.Arm.Front.ret, sp0, ld, hc.st.sp, hc.aFr hg, hc.rFr hg, Proof.RsaOaep.Arm.sRes_lt]
  refine WP.mono hw fun t ⟨m, rd, wr, sp, t0⟩ => ⟨⟨hi, (hc.regs rd wr sp m).st⟩, ?_⟩
  obtain hl := hk.2.2
  have hl' : (Mv P σ).length ≤ P.K := hl
  refine front_of (t0.trans (m ▸ hk.1)) ?_ (m ▸ hk.2.1)
  rw [m]
  have eL : Lv P σ = (Mv P σ).length := rfl
  obtain e : (Mv P σ ++ List.replicate (P.K - Lv P σ) 0).length = P.K := by
    simp only [List.length_append, List.length_replicate]; omega_using [hl', eL]
  have hb := bytesAt_eq (m := s.mem) (p := State.addr P.out) (xs := Mv P σ ++ List.replicate (P.K - Lv P σ) 0)
    fun i hi' => by
      rw [e] at hi'
      rw [← front_bytes hl i, ← ho i hi']
  rw [e] at hb
  exact hb

/-! ## The body -/

/-- After the call. -/
theorem tail_vp (P : EP) : VP (R3 P) tail (Fin P) :=
  VP.assoc ((clr_vp P).seq (VP.assoc ((in_vp P).seq ((shift_vp P).seq (VP.assoc ((out_vp P).seq (ret_vp P)))))))

/-- The body, calling `vg_rsa_pkcs1_decrypt_precomputed`'s code `c` by its
contract. -/
theorem body_vp {c : Prog isa} (hv : Verified target c cK) (hst : FrameStack.armStack c ≤ calleeStack)
    (name : String) (P : EP) : VP (S P) (Impl.RsaPkcs1Enc.Arm.Front.body name c) (Fin P) :=
  (setup_vp P).seq ((call_vp hv hst name P).seq ((after_vp P).seq (tail_vp P)))

/-! ## The function -/

theorem satisfiable : ∃ s, spec.pre s := by
  open Proof.RsaPkcs1Enc.Arm.Dec in
  have p11 : BitVec.setWidth 64 (stackArg preState 7) = 0x4200 := by decide
  have p13 : BitVec.setWidth 64 (stackArg preState 9) = 0x4300 := by decide
  have p23 : BitVec.setWidth 64 (stackArg preState 19) = 0x4800 := by decide
  have l4 : (stackArg preState 0).toNat = 64 := by decide
  have l12 : (stackArg preState 8).toNat = 32 := by decide
  have l14 : (stackArg preState 10).toNat = 32 := by decide
  have l24 : (stackArg preState 20).toNat = 24 := by decide
  refine ⟨preState, ?_⟩
  sig_pre [Spec.RsaPkcs1Enc.decryptPrecomputedFrontContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
    Spec.RsaPkcs1Enc.decryptSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  sig_and_intros
  rotate_right
  · rw [show BitVec.setWidth 64 (8192 : BitVec 32) = (0x2000 : Addr) by decide, p11, p13, p23, l4, l12, l14, l24]
    exact preState_key
  all_goals first
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (simp only [Spec.Rsa.lenValid]; decide)

section

variable {c : Prog isa} (hv : Verified target c cK) (hst : FrameStack.armStack c ≤ calleeStack) (name : String)
include hv hst

theorem code_ok {s : State} (h : spec.pre s) :
    WP isa (Impl.RsaPkcs1Enc.Arm.Front.code name c) s fun t => abiPreserved s t ∧ spec.post s t := by
  have hs := spec_sp h
  have hin := in_of_pre h
  have st := entered_state h
  have hsp : 56 + frameBytes ≤ s.sp.toNat := Nat.le_trans (Nat.le_add_right _ _) hs
  have hF : FrameOk frameBytes := by decide
  have hb := (body_vp hv hst name (ep s)).wp _ _ st
  refine WP.mono (wrap_ok hF (by rw [Nat.add_comm]; exact hsp) (W := (ep s).lay.W)
    (Q := fun r m => Res (ep s) (entered frameBytes s) m r) (fun r hr => ?_)
    (WP.mono hb fun u hu => ⟨hu.1.2.frame, hu.2⟩)
    (hQ := fun _ m₁ m₂ hf hres => by
      have ap := fun {R : Region} (hR : R ∈ (ep s).rw) =>
        released_apart (F := frameBytes) (A := 84) (C := calleeStack) (argv := (ep s).argv)
          (ro := (ep s).ro) hin.ok hsp (Or.inr hR)
      exact Res_frame hf (ap (by simp)) (ap (by simp))
        (by have := hin.out_fit; omega_using [this]) hres)) fun t ⟨abi, res⟩ => ⟨abi, ?_⟩
  · rw [pushRegion_eq (F := frameBytes) (A := 84) (C := calleeStack) (argv := (ep s).argv)
      (ro := (ep s).ro) (rw := (ep s).rw) hsp]
    exact hin.ok.push_apart r hr
  · sig_post [Spec.RsaPkcs1Enc.decryptPrecomputedFrontContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
      Spec.RsaPkcs1Enc.decryptSig, abi, argRegs, reduceClassify, Loc.val]
    rw [BitVec.setWidth_append_eq_right]
    have ro := fun {R : Region} (hR : R ∈ (ep s).ro) =>
      entered_ro (F := frameBytes) (A := 84) (C := calleeStack) (argv := (ep s).argv)
        (rw := (ep s).rw) hin.ok hsp hR
    have hD : dB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 3))
        (stackArg s 4).toNat := ro (R := (ep s).D) (by simp)
    have hI : cB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 5))
        (stackArg s 0).toNat := ro (R := (ep s).INP) (by simp)
    have hP : pB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 7))
        (stackArg s 8).toNat := ro (R := (ep s).PP) (by simp)
    have hQ : qB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 9))
        (stackArg s 10).toNat := ro (R := (ep s).QQ) (by simp)
    have hDP : dpB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 11))
        (stackArg s 8).toNat := ro (R := (ep s).DP) (by simp)
    have hDQ : dqB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 13))
        (stackArg s 10).toNat := ro (R := (ep s).DQ) (by simp)
    have hQI : qiB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 15))
        (stackArg s 8).toNat := ro (R := (ep s).QI) (by simp)
    unfold Res oc at res
    rw [hD, hI, hP, hQ, hDP, hDQ, hQI] at res
    exact res

theorem code_ct : ConstantTime isa spec.pre spec.pub (Impl.RsaPkcs1Enc.Arm.Front.code name c) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  have hep := ep_eq hp
  have hsp : s₁.sp = s₂.sp := by
    sig_pub [Spec.RsaPkcs1Enc.decryptPrecomputedFrontContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
      Spec.RsaPkcs1Enc.decryptSig, abi, argRegs, reduceClassify, Loc.val] at hp
    exact hp.1
  refine (wrap_ct (F := frameBytes) (by decide) (P := fun a b => a = s₁ ∧ b = s₂)
    (fun a b h => by rw [h.1, h.2]; exact hsp)
    (fun a b h => by rw [h.1]; exact Nat.le_trans (Nat.le_add_right _ _) (spec_sp h₁)) ?_
    s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  refine (body_vp hv hst name (ep s₁)).ct.mono ?_ fun _ _ _ => trivial
  rintro a b ⟨_, _, ⟨rfl, rfl⟩, rfl, rfl⟩
  exact ⟨_, _, entered_state h₁, by rw [hep]; exact entered_state h₂⟩

/-- `vg_rsa_pkcs1_decrypt_precomputed_front`, calling the code `c` of
`vg_rsa_pkcs1_decrypt_precomputed` by `name`. -/
theorem front_verified : Verified target (Impl.RsaPkcs1Enc.Arm.Front.code name c) spec :=
  ⟨fun _ h => let ⟨t, s', he, hq⟩ := code_ok hv hst name h; ⟨t, s', he, hq.1, hq.2⟩, code_ct hv hst name,
    satisfiable⟩

end

/-! ## As emitted -/

section

open VG.Arm.Scrub VG.Proof.Rsa.Arm.Scrub
open VG.Proof.Rsa.Arm (CrtImpl privCodeP)

/-- The name of `vg_rsa_pkcs1_decrypt_precomputed`'s code before its
cleanup, over `v`: an internal function. -/
def bodyName (v : CrtImpl) : String := "vg_rsa_pkcs1_decrypt_precomputed_body" ++ v.suffix

theorem writtenMsgFront_of {m₁ m₂ : Mem} {o l : Addr} {n : Nat} {r : BitVec 32} {v : Spec.Rsa.Outcome}
    (e : Spec.Rsa.bytesAt m₂ o n = Spec.Rsa.bytesAt m₁ o n) (el : Spec.Rsa.wordsAt m₂ l 1 = Spec.Rsa.wordsAt m₁ l 1)
    (h : Spec.RsaPkcs1Enc.writtenMsgFront m₁ o l n r v) : Spec.RsaPkcs1Enc.writtenMsgFront m₂ o l n r v := by
  cases v <;> simpa only [Spec.RsaPkcs1Enc.writtenMsgFront, e, el] using h

/-- The postcondition reads the memory on return only within `out` and
`msg_len`. -/
theorem frontOut (stack : Nat) :
    PostOut (Spec.RsaPkcs1Enc.decryptPrecomputedFrontContract abi stack)
      (Spec.RsaPkcs1Enc.decryptPrecomputedSig.retBits 32) :=
  postOut_of_local_pre (leak := some _) ScrubAbi.plain fun
    | [out, outLen, ml, _, nLen, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hp, hb, h => by
      simp only [Spec.RsaPkcs1Enc.decryptPrecomputedSig, Spec.RsaPkcs1Enc.decryptSig, List.cons_append,
        List.nil_append, Sig.bufs, List.mem_cons, forall_eq_or_imp, Elem.size] at hb
      change @Curry.apply (Mem → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ m at hp
      change @Curry.apply (Mem → Mem → BitVec _ → Prop)
        [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop)
        [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at hp h ⊢
      exact writtenMsgFront_of (bytesAt_of hb.1 (hp.2.1 ▸ toNat_sw_le abi ScrubAbi.plain outLen))
        (wordsAt_of hb.2.1) h

/-- What the cleanup needs of `vg_rsa_pkcs1_decrypt_precomputed`'s code
over `v`, with the stack its contract states. -/
theorem dec_ok (v : CrtImpl) : CodeOk (Proof.RsaPkcs1Enc.Arm.Dec.decryptCodeP v) calleeStack :=
  (wrap_codeOk (n := 3488) (F := 96) (CodeOk.seq (CodeOk.zero (CodeOk.block _))
    (CodeOk.seq (CodeOk.call (privCodeP_ok v)) Proof.RsaPkcs1Enc.Arm.Scrub.decRest_ok))).mono (by decide)

theorem rest_ok : CodeOk (.seq (.block Impl.RsaPkcs1Enc.Arm.Front.after) Impl.RsaPkcs1Enc.Arm.Front.tail) 0 := by
  lit_decide

/-- And of ours, calling it. -/
theorem front_ok {name : String} {c : Prog isa} (h : CodeOk c calleeStack) :
    CodeOk (Impl.RsaPkcs1Enc.Arm.Front.code name c) stackBytes :=
  (wrap_codeOk (n := calleeStack) (F := Impl.RsaPss.Arm.frameBytes)
    (CodeOk.seq (CodeOk.zero (CodeOk.block _)) (CodeOk.seq (CodeOk.call h) (CodeOk.zero rest_ok)))).mono (by decide)

theorem frameOk_3824 : VG.Arm.Scrub.FrameOk stackBytes := by decide

/-- `Spec.RsaPkcs1Enc.decryptPrecomputedFrontApi`'s function as emitted,
calling `vg_rsa_pkcs1_decrypt_precomputed`'s code over `v`: it meets its
contract in constant time and returns without secret residue. -/
theorem front_scrubbed (v : CrtImpl) :
    VerifiedScrubbed target
      (Impl.RsaPkcs1Enc.Arm.Fn.decryptPrecomputedFront (bodyName v) (Proof.RsaPkcs1Enc.Arm.Dec.decryptCodeP v))
      (Spec.RsaPkcs1Enc.decryptPrecomputedFrontContract abi 3824) 32 :=
  verifiedScrubbedAll (api := Spec.RsaPkcs1Enc.decryptPrecomputedFrontApi)
    { code := Impl.RsaPkcs1Enc.Arm.Front.code (bodyName v) (Proof.RsaPkcs1Enc.Arm.Dec.decryptCodeP v)
      verified := front_verified (Proof.RsaPkcs1Enc.Arm.Dec.decryptPrecomputed_verified v) (dec_ok v).1 (bodyName v) }
    (frontOut _) (scrubSideF_of (front_ok (dec_ok v)) frameOk_3824 _)

end

end VG.Proof.RsaPkcs1Enc.Arm.Front
