module

import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Bignum.Arm.MaskBuffer
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.SgTaint
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.EncodeTaint
import VerifiedGarbage.Proof.Bignum.Arm.MaskBytesCT
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Vp
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.PrivCall
import VerifiedGarbage.Proof.Rsa.Arm.PrivVerified
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Rsa.Contract
public import VerifiedGarbage.Impl.RsaPkcs1Sig.Arm.Sign
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Entry
public import VerifiedGarbage.Spec.RsaPkcs1Sig.Contract
public import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `RsaPkcs1Sig.Arm.SgCall`, which this module and modules that import it used -/

section

/-! ### `RsaPkcs1Sig.Arm.SgBase`, which this module and modules that import it used -/

section

/-!
# RSASSA-PKCS1-v1_5 signing on ARMv7: where everything is

`EP`: what two runs share (the frame's base `B`, the pointers, the lengths,
the hash function's number, and the public key's bytes `nB` and `eB`), and
its layout (`EP.lay`, `Proof/RsaPkcs1Sig/Arm/Lay.lean`), with the 3440
bytes below the frame that the call uses. `In P σ`: the state `σ` the body
starts from; `S P σ s`: a state of the body. The shared contract, with the
stack of the frames and of the call, gives `In (ep s) (entered frameBytes s)`
(`in_of_pre`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.Arm.Sg

open VG VG.Arm VG.Impl.RsaPkcs1Sig.Arm.Sign VG.Proof.RsaPkcs1Sig.Arm

/-- What two runs share. -/
structure EP where
  B : BitVec 32
  out : BitVec 32
  n : BitVec 32
  e : BitVec 32
  hash : BitVec 32
  dig : BitVec 32
  p : BitVec 32
  q : BitVec 32
  dp : BitVec 32
  dq : BitVec 32
  qinv : BitVec 32
  scr : BitVec 32
  K : Nat
  el : Nat
  dl : Nat
  pl : Nat
  ql : Nat
  sl : Nat
  nB : List Byte
  eB : List Byte
  /-- `vg_rsa_pkcs1_sign_precomputed`, given the key's precomputed values
  `pre` (`prl` words), of which it may leak `preL`. -/
  pc : Bool
  pre : BitVec 32
  prl : Nat
  preL : List Nat

namespace EP

variable (P : EP)

abbrev OUT : Region := ⟨State.addr P.out, P.K⟩
abbrev N : Region := ⟨State.addr P.n, P.K⟩
abbrev E : Region := ⟨State.addr P.e, P.el⟩
abbrev DIG : Region := ⟨State.addr P.dig, P.dl⟩
abbrev PP : Region := ⟨State.addr P.p, P.pl⟩
abbrev QQ : Region := ⟨State.addr P.q, P.ql⟩
abbrev DP : Region := ⟨State.addr P.dp, P.pl⟩
abbrev DQ : Region := ⟨State.addr P.dq, P.ql⟩
abbrev QI : Region := ⟨State.addr P.qinv, P.pl⟩
abbrev SCR : Region := ⟨State.addr P.scr, P.sl * 8⟩
abbrev PRE : Region := ⟨State.addr P.pre, P.prl * 8⟩

/-- The arguments, in order. -/
abbrev argv : List (BitVec 32) :=
  [P.out, BitVec.ofNat 32 P.K, P.n, BitVec.ofNat 32 P.K, P.e, BitVec.ofNat 32 P.el, P.hash, P.dig,
    BitVec.ofNat 32 P.dl, P.p, BitVec.ofNat 32 P.pl, P.q, BitVec.ofNat 32 P.ql, P.dp, BitVec.ofNat 32 P.pl,
    P.dq, BitVec.ofNat 32 P.ql, P.qinv, BitVec.ofNat 32 P.pl, P.scr, BitVec.ofNat 32 P.sl] ++
    if P.pc then [P.pre, BitVec.ofNat 32 P.prl] else []

/-- The buffers it reads. -/
abbrev ro : List Region := [P.N, P.E, P.DIG, P.PP, P.QQ, P.DP, P.DQ, P.QI] ++ if P.pc then [P.PRE] else []

abbrev lay : Lay where
  B := P.B
  F := frameBytes
  A := if P.pc then 76 else 68
  argv := P.argv
  ro := P.ro
  rw := [P.OUT, P.SCR]
  C := 3440

theorem lt_lay {d : Nat} (h : d < frameBytes + 56 + 68) : d < P.lay.F + 56 + P.lay.A := by
  show d < frameBytes + 56 + (if P.pc then 76 else 68); split <;> omega_using [h]

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
  slK : Spec.Rsa.scratchWords P.K ≤ P.sl
  dl32 : P.dl < 2 ^ 32
  nB : Spec.Rsa.bytesAt σ.mem (State.addr P.n) P.K = P.nB
  eB : Spec.Rsa.bytesAt σ.mem (State.addr P.e) P.el = P.eB
  prl : P.pc → P.prl = Spec.Rsa.privatePrecomputedWords P.K P.pl P.ql
  pre : P.pc → Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt σ.mem (State.addr P.n) P.K)
    (Spec.Rsa.bytesAt σ.mem (State.addr P.p) P.pl) (Spec.Rsa.bytesAt σ.mem (State.addr P.q) P.ql) =
      some (Spec.Rsa.wordsAt σ.mem (State.addr P.pre) P.prl)
  preL : P.pc → Spec.Rsa.privatePrecomputedLeak σ.mem (State.addr P.pre) P.K = P.preL

/-- A state of the body. -/
abbrev S (P : EP) (σ s : State) : Prop := In P σ ∧ P.lay.St σ s

namespace In

variable {P : EP} {σ : State} (h : In P σ)
include h

theorem k64 : 64 ≤ P.K := h.kv.1
theorem k1024 : P.K ≤ 1024 := h.kv.2

end In

/-! ## The entry -/

/-- The stack the function uses: the push, the inner frame and the call's. -/
abbrev stackBytes : Nat := 56 + frameBytes + 3440

/-- The shared contract, with that stack. -/
abbrev spec : Contract isa := Spec.RsaPkcs1Sig.signContract abi stackBytes

/-- The public parameters of an entry state (with `pc`, of
`vg_rsa_pkcs1_sign_precomputed`). -/
def ep (s : State) (pc : Bool := false) : EP where
  B := s.sp - BitVec.ofNat 32 56 - BitVec.ofNat 32 frameBytes
  out := s.gpr .r0
  n := s.gpr .r2
  e := stackArg s 0
  hash := stackArg s 2
  dig := stackArg s 3
  p := stackArg s 5
  q := stackArg s 7
  dp := stackArg s 9
  dq := stackArg s 11
  qinv := stackArg s 13
  scr := stackArg s 15
  K := (s.gpr .r3).toNat
  el := (stackArg s 1).toNat
  dl := (stackArg s 4).toNat
  pl := (stackArg s 6).toNat
  ql := (stackArg s 8).toNat
  sl := (stackArg s 16).toNat
  nB := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat
  eB := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat
  pc := pc
  pre := if pc then stackArg s 17 else 0
  prl := if pc then (stackArg s 18).toNat else 0
  preL := if pc then Spec.Rsa.privatePrecomputedLeak s.mem (State.addr (stackArg s 17)) (s.gpr .r3).toNat else []

theorem ep_lay (s : State) :
    (ep s).lay = layOf frameBytes 68 (ep s).argv [(ep s).N, (ep s).E, (ep s).DIG, (ep s).PP, (ep s).QQ,
      (ep s).DP, (ep s).DQ, (ep s).QI] [(ep s).OUT, (ep s).SCR] s 3440 := by
  simp [ep, EP.lay, EP.argv, EP.ro, layOf]

theorem in_of_pre {s : State} (h : spec.pre s) : In (ep s) (entered frameBytes s) := by
  sig_pre [Spec.RsaPkcs1Sig.signContract, Spec.RsaPkcs1Sig.signSig, abi,
    argRegs, reduceClassify, Loc.val] at h
  sig_split h
  rename_i hsp hsa hrd hwr oN oE oD oP oQ oDP oDQ oQI oS oA nS eS dS pS qS dpS dqS qiS sA kO kN kE kD kP kQ
    kDP kDQ kQI kS kA fO fN fE fD fP fQ fDP fDQ fQI fS kv olk el1 elK pl1 plK ql1 qlK dpl qil dql
  have slK := h
  have h4616 : 4616 ≤ s.sp.toNat := hsp
  have r1 : s.gpr .r1 = s.gpr .r3 := BitVec.eq_of_toNat_eq olk
  have a10 : stackArg s 10 = stackArg s 6 := BitVec.eq_of_toNat_eq dpl
  have a14 : stackArg s 14 = stackArg s 6 := BitVec.eq_of_toNat_eq qil
  have a12 : stackArg s 12 = stackArg s 8 := BitVec.eq_of_toNat_eq dql
  rw [olk] at hwr oN oE oD oP oQ oDP oDQ oQI oS oA kO fO
  rw [dpl] at oDP dpS kDP fDP hrd
  rw [qil] at oQI qiS kQI fQI hrd
  rw [dql] at oDQ dqS kDQ fDQ hrd
  have hpush : Frame [FrameStack.belowA s.sp 56] s.mem (entered frameBytes s).mem :=
    FrameStack.pushed_frameA (rs := Impl.RsaPkcs1Sig.Arm.pushRegs) (by show 56 ≤ s.sp.toNat; omega_arith)
  have below : Region.Sub (FrameStack.belowA s.sp 56)
      ⟨State.addr s.sp - BitVec.ofNat 64 4616, 4616⟩ := by
    show Region.Sub ⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩ _
    rw [FrameStack.addr_sub' (by omega_arith)]
    exact Offset.sub_below _ (by omega_arith) (by omega_arith)
  refine
    { ok := ?_
      kv := kv, el1 := el1, elK := elK, pl1 := pl1, plK := plK, ql1 := ql1, qlK := qlK, slK := slK
      dl32 := (stackArg s 4).isLt
      nB := bytesAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kN.sub_left below).symm)
        (by show (s.gpr .r3).toNat ≤ 2 ^ 64; omega_arith)
      eB := bytesAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kE.sub_left below).symm)
        (by show (stackArg s 1).toNat ≤ 2 ^ 64; omega_arith)
      prl := fun h => by cases h
      pre := fun h => by cases h
      preL := fun h => by cases h }
  rw [ep_lay]
  refine ok_entered (by decide) (by decide) rfl hsp hsa hrd hwr ?_ ?_ ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [kN, kE, kD, kP, kQ, kDP, kDQ, kQI, kO, kS, kA]
  · intro w hw r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hw with rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [oN, oE, oD, oP, oQ, oDP, oDQ, oQI, oA, nS.symm, eS.symm, dS.symm, pS.symm, qS.symm, dpS.symm,
      dqS.symm, qiS.symm, sA]
  · exact List.pairwise_pair.mpr oS
  · intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [fN, fE, fD, fP, fQ, fDP, fDQ, fQI, fO, fS]
  · intro j hj
    rcases (by omega_arith : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    · rfl
    · simp [regArg, ep, r1]
    · rfl
    · simp [regArg, ep]
  · intro i hi
    have : i < 17 := hi
    rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
        i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [ep, a10, a12, a14]

end VG.Proof.RsaPkcs1Sig.Arm.Sg

end

end

/-! ### `RsaPkcs1Sig.Arm.SgPieces`, which only this module used -/

section

/-!
# RSASSA-PKCS1-v1_5 signing on ARMv7: the encoding

The encoding of the hash value to `EM` (`encArgs_wp`, `encode_wp`), the
test of its success (`cmp_wp`), which depends only on public data
(`encOut_isNone`), and zeros and 0 when it fails (`zeroArgs_wp`, `zero_wp`,
`ret0_wp`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.Arm.Sg

open VG VG.Arm VG.Impl.RsaPkcs1Sig.Arm.Sign VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.RsaPkcs1Sig.Arm.Vf (EncR)
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_dp wp_cmp op2_imm op2_reg dpVal)

variable {P : EP}

/-- The hash value and the private key. -/
abbrev digB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.dig) P.dl
abbrev pB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.p) P.pl
abbrev qB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.q) P.ql
abbrev dpB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.dp) P.pl
abbrev dqB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.dq) P.ql
abbrev qiB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.qinv) P.pl

/-- The encoding, if any. -/
abbrev enc (P : EP) (σ : State) : Option (List Byte) := encOut P.hash.toNat (digB P σ) P.K

/-- What the function writes to `out` and returns. -/
def Res (P : EP) (σ : State) (m : Mem) (r : BitVec 32) : Prop :=
  Spec.Rsa.writtenOutcome m (State.addr P.out) P.K r
    (Spec.RsaPkcs1Sig.signId P.nB P.eB (pB P σ) (qB P σ) (dpB P σ) (dqB P σ) (qiB P σ) P.hash.toNat (digB P σ))

/-- Before `encode`. -/
def E1 (P : EP) (σ s : State) : Prop :=
  S P σ s ∧ s.gpr .r0 = P.B + BitVec.ofNat 32 oEM ∧ s.gpr .r1 = P.dig ∧ s.gpr .r2 = P.hash ∧
    s.gpr .r3 = BitVec.ofNat 32 P.K ∧ s.gpr .lr = BitVec.ofNat 32 P.dl

/-- After `encode`. -/
def E2 (P : EP) (σ s : State) : Prop := S P σ s ∧ EncR P.hash.toNat (digB P σ) P.K s.mem (P.lay.fr oEM) (s.gpr .r3)

/-- After the test of its success. -/
def E3 (P : EP) (σ s : State) : Prop := E2 P σ s ∧ s.z = (enc P σ).isNone

/-- Before the zeros. -/
def F1 (P : EP) (σ s : State) : Prop :=
  S P σ s ∧ enc P σ = none ∧ s.gpr .r0 = P.out ∧ s.gpr .lr = BitVec.ofNat 32 P.K ∧ s.gpr .r2 = 0

/-- `out` zeros. -/
def F2 (P : EP) (σ s : State) : Prop :=
  S P σ s ∧ enc P σ = none ∧ Spec.Rsa.bytesAt s.mem (State.addr P.out) P.K = List.replicate P.K 0

/-- The end of the body. -/
def Fin (P : EP) (σ s : State) : Prop := S P σ s ∧ Res P σ s.mem (s.gpr .r0)

/-- The encoding written. -/
def R0 (P : EP) (σ s : State) : Prop :=
  S P σ s ∧ ∃ em, enc P σ = some em ∧ Spec.Rsa.bytesAt s.mem (P.lay.fr oEM) P.K = em

/-! ## Whether the encoding succeeds -/

theorem encOut_isNone {id K : Nat} {D D' : List Byte} (h : D.length = D'.length) :
    (encOut id D K).isNone = (encOut id D' K).isNone := by
  unfold encOut
  cases Spec.RsaPkcs1Sig.Hash.ofId id with
  | none => rfl
  | some hh => simp only [encode_eq, h]; split <;> rfl

theorem enc_isNone (P : EP) (σ₁ σ₂ : State) : (enc P σ₁).isNone = (enc P σ₂).isNone :=
  encOut_isNone (by simp only [bytesAt_length])

theorem encR_r3 {id K : Nat} {D : List Byte} {m : Mem} {a : Addr} {ok : BitVec 32} (h : EncR id D K m a ok) :
    ok = if (encOut id D K).isNone then 0 else 1 := by
  unfold EncR at h
  split at h <;> simp_all

/-! ## The pieces -/

theorem encArgs_wp {σ s : State} (hs : S P σ s) : WP isa (.block encArgs) s (E1 P σ) := by
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  refine wp_dp (op2_imm (by decide)) fun t2 u2 => ?_
  obtain s2 : P.lay.St σ t2 := (hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem).of_rest
    (u2.rest (ws := [.r0]) (by simp)) u2.mem
  refine s2.wp_arg (j := 7) (by simp) (by dsimp only; decide) fun t3 s3 u3 => ?_
  refine s3.wp_arg (j := 6) (by simp) (by dsimp only; decide) fun t4 s4 u4 => ?_
  refine s4.wp_arg (j := 3) (by simp) (by dsimp only; decide) fun t5 s5 u5 => ?_
  refine s5.wp_arg (j := 8) (by simp) (by dsimp only; decide) fun t6 s6 u6 => WP.block_nil
    ⟨⟨hs.1, s6⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.gpr,
      dpVal, u1.gpr, hs.2.sp, BitVec.add_zero]
  · rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.gpr]; rfl
  · rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr]; rfl
  · rw [u6.other _ (by decide), u5.gpr]; rfl
  · rw [u6.gpr]; rfl

theorem encode_wp {σ s : State} (h : E1 P σ s) : WP isa Impl.RsaPkcs1Sig.Arm.encode s (E2 P σ) := by
  obtain ⟨hs, r0, r1, r2, r3, lr⟩ := h
  have ok := hs.1.ok
  have hK := hs.1.k1024
  have fit := ok.fit
  obtain e : State.addr (P.B + BitVec.ofNat 32 oEM) = P.lay.fr oEM :=
    ok.addrB (P.lt_lay (by decide))
  obtain hfd := ok.fits P.DIG (by simp)
  simp only [Proof.X25519.Arm.addr_toNat] at hfd
  obtain hin : EncIn s (P.B + BitVec.ofNat 32 oEM) P.dig P.hash P.K P.dl :=
    { r0 := r0, r1 := r1, r2 := r2, r3 := r3, lr := lr
      k64 := hs.1.k64, k1024 := hK, dl32 := hs.1.dl32
      dstFit := by
        rw [Proof.X25519.Arm.toNat_add_lt (by rw [BitVec.toNat_ofNat]; simp only [oEM, frameBytes] at fit ⊢; omega_using [fit]),
          BitVec.toNat_ofNat]
        simp only [oEM, frameBytes] at fit ⊢; omega_using [hK, fit]
      srcFit := hfd
      write := by rw [e]; exact hs.2.inFr (by show oEM + P.K ≤ frameBytes; simp only [oEM, frameBytes]; omega_using [hK])
      read := ⟨P.DIG, List.mem_append_left _ (by rw [hs.2.rd, ok.rd]; simp), Region.contains_self _ _⟩
      sep := by
        rw [e]
        exact (ok.stk_fr (R := P.DIG) (.inl (by simp)) (by simp only [oEM, frameBytes]; omega_using [hK])).symm }
  refine WP.mono (encode_ok hin) fun t ⟨fr, rest, res⟩ => ?_
  rw [e] at fr
  obtain st' : P.lay.St σ t := hs.2.frameW (by show oEM + P.K ≤ frameBytes; simp only [oEM, frameBytes]; omega_using [hK])
    fr rest.rd rest.wr rest.sp
  refine ⟨⟨hs.1, st'⟩, ?_⟩
  obtain hd : Spec.Rsa.bytesAt s.mem (State.addr P.dig) P.dl = digB P σ := hs.2.ro (R := P.DIG) (by simp)
  rw [hd, e] at res
  unfold EncR
  revert res
  cases encOut P.hash.toNat (digB P σ) P.K with
  | some em => exact fun r => r
  | none => exact fun r => r

theorem cmp_wp {σ s : State} (h : E2 P σ s) : WP isa (.block [.cmp .r3 (.imm 0)]) s (E3 P σ) := by
  obtain ⟨hs, er⟩ := h
  refine wp_cmp (op2_imm (by decide)) fun t1 u1 z1 => WP.block_nil
    ⟨⟨⟨hs.1, hs.2.of_rest (u1.rest []) u1.mem⟩, by rw [u1.mem, u1.gpr]; exact er⟩, ?_⟩
  rw [z1, encR_r3 er]
  show _ = (encOut P.hash.toNat (digB P σ) P.K).isNone
  cases encOut P.hash.toNat (digB P σ) P.K <;> simp

theorem zeroArgs_wp {σ s : State} (h : E3 P σ s ∧ isa.eval .eq s = some true) :
    WP isa (.block zeroArgs) s (F1 P σ) := by
  obtain ⟨⟨⟨hs, -⟩, z⟩, e⟩ := h
  obtain hn : enc P σ = none := by
    rw [Proof.X25519.Arm.eval_eq, z] at e; simpa using e
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  obtain s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  refine s1.wp_arg (j := 0) (by simp) (by dsimp only; decide) fun t2 s2 u2 => ?_
  refine s2.wp_arg (j := 3) (by simp) (by dsimp only; decide) fun t3 s3 u3 => ?_
  refine wp_mov (op2_imm (by decide)) fun t4 u4 => WP.block_nil
    ⟨⟨hs.1, s3.of_rest (u4.rest (ws := [.r2]) (by simp)) u4.mem⟩, hn, ?_, ?_, u4.gpr⟩
  · rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr]; rfl
  · rw [u4.other _ (by decide), u3.gpr]; rfl

theorem zero_wp {σ s : State} (h : F1 P σ s) : WP isa Impl.Bignum.Arm.maskBytes s (F2 P σ) := by
  obtain ⟨hs, hn, r0, lr, r2⟩ := h
  have ok := hs.1.ok
  obtain hfo := ok.fits P.OUT (by simp)
  simp only [Proof.X25519.Arm.addr_toNat] at hfo
  have hK := hs.1.k1024
  refine WP.mono (Bignum.Arm.maskBuffer_ok s (dst := P.out) (n := P.K) (by have := hs.1.k64; omega_using [this]) (by omega_using [hK])
    hfo ⟨P.OUT, by rw [hs.2.wr, ok.wr]; simp, Region.contains_self _ _⟩ r0 lr) fun t ⟨hb, fr, rst⟩ => ?_
  obtain st : P.lay.St σ t := hs.2.write fr (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨P.OUT, by simp, fun _ h => h⟩) rst.rd rst.wr rst.sp
  refine ⟨⟨hs.1, st⟩, hn, ?_⟩
  rw [hb, r2]
  apply List.ext_getElem (by simp [bytesAt_length])
  intro i h₁ h₂
  simp

theorem S.nB {σ s : State} (hs : S P σ s) : Spec.Rsa.bytesAt s.mem (State.addr P.n) P.K = P.nB :=
  (hs.2.ro (R := P.N) (by simp)).trans hs.1.nB

theorem S.eB {σ s : State} (hs : S P σ s) : Spec.Rsa.bytesAt s.mem (State.addr P.e) P.el = P.eB :=
  (hs.2.ro (R := P.E) (by simp)).trans hs.1.eB

theorem nB_length {σ : State} (h : In P σ) : P.nB.length = P.K := by rw [← h.nB, bytesAt_length]

/-- `signId` when the encoding fails. -/
theorem signId_none {σ : State} (h : In P σ) (hn : enc P σ = none) :
    Spec.RsaPkcs1Sig.signId P.nB P.eB (pB P σ) (qB P σ) (dpB P σ) (dqB P σ) (qiB P σ) P.hash.toNat (digB P σ) =
      .invalid := by
  unfold Spec.RsaPkcs1Sig.signId
  unfold enc encOut at hn
  split
  · rename_i hh e
    rw [e] at hn
    simp only at hn
    rw [Spec.RsaPkcs1Sig.sign, nB_length h, hn]
  · rfl

/-- `signId` when the encoding is `em`. -/
theorem signId_some {σ : State} (h : In P σ) {em : List Byte} (hs : enc P σ = some em) :
    Spec.RsaPkcs1Sig.signId P.nB P.eB (pB P σ) (qB P σ) (dpB P σ) (dqB P σ) (qiB P σ) P.hash.toNat (digB P σ) =
      Spec.Rsa.privateChecked P.nB P.eB em (pB P σ) (qB P σ) (dpB P σ) (dqB P σ) (qiB P σ) := by
  unfold Spec.RsaPkcs1Sig.signId
  unfold enc encOut at hs
  split
  · rename_i hh e
    rw [e] at hs
    simp only at hs
    rw [Spec.RsaPkcs1Sig.sign, nB_length h, hs]
  · rename_i e
    rw [e] at hs
    cases hs

theorem ret0_wp {σ s : State} (h : F2 P σ s) : WP isa (.block ret0) s (Fin P σ) := by
  obtain ⟨hs, hn, hz⟩ := h
  refine wp_mov (op2_imm (by decide)) fun t1 u1 => WP.block_nil
    ⟨⟨hs.1, hs.2.of_rest (u1.rest (ws := [.r0]) (by simp)) u1.mem⟩, ?_⟩
  rw [Res, signId_none hs.1 hn, u1.gpr, u1.mem]
  exact ⟨rfl, hz⟩

theorem r0_of {σ s : State} (h : E3 P σ s ∧ isa.eval .eq s = some false) : R0 P σ s := by
  obtain ⟨⟨⟨hs, er⟩, z⟩, e⟩ := h
  obtain hn : (enc P σ).isNone = false := by
    rw [Proof.X25519.Arm.eval_eq, z] at e; simpa using e
  refine ⟨hs, ?_⟩
  unfold EncR at er
  cases he : encOut P.hash.toNat (digB P σ) P.K with
  | none => have he' : enc P σ = none := he; rw [he'] at hn; cases hn
  | some em => rw [he] at er; exact ⟨em, he, er.2⟩

end VG.Proof.RsaPkcs1Sig.Arm.Sg

end

end


/-!
# RSASSA-PKCS1-v1_5 signing on ARMv7: the call

The call's sixteen stack arguments, one word of the frame at a time
(`Slots`, `copySlot`, `callArgs_wp`), and the call of
`vg_rsa_private_checked` (`call_vp`, correct and constant time: its
arguments and the public key it reads are the same in two runs), which
writes the signature of `EM` (`R2`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.Arm.Sg

open VG VG.Arm VG.Impl.RsaPkcs1Sig.Arm.Sign VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_dp op2_imm op2_reg dpVal)
open VG.Proof.Rsa.Arm.Recover (VP)

variable {P : EP}

/-- The call's stack arguments. -/
abbrev outv (P : EP) : List (BitVec 32) :=
  [P.e, BitVec.ofNat 32 P.el, P.B + BitVec.ofNat 32 oEM, BitVec.ofNat 32 P.K, P.p, BitVec.ofNat 32 P.pl, P.q,
    BitVec.ofNat 32 P.ql, P.dp, BitVec.ofNat 32 P.pl, P.dq, BitVec.ofNat 32 P.ql, P.qinv, BitVec.ofNat 32 P.pl,
    P.scr, BitVec.ofNat 32 P.sl] ++ if P.pc then [P.pre, BitVec.ofNat 32 P.prl] else []

/-- Their number. -/
abbrev ncall (P : EP) : Nat := if P.pc then 18 else 16

/-- The first `k` of them in the frame. -/
def Slots (P : EP) (m : Mem) (k : Nat) : Prop :=
  ∀ i < k, m.readW (P.lay.fr (4 * i)) 32 = (outv P).getD i 0

/-- Before the call. -/
def R1 (P : EP) (σ s : State) : Prop :=
  R0 P σ s ∧ Slots P s.mem (ncall P) ∧ s.gpr .r0 = P.out ∧ s.gpr .r1 = BitVec.ofNat 32 P.K ∧ s.gpr .r2 = P.n ∧
    s.gpr .r3 = BitVec.ofNat 32 P.K

/-- After the call. -/
def R2 (P : EP) (σ s : State) : Prop :=
  S P σ s ∧ ∃ em, enc P σ = some em ∧ Spec.Rsa.writtenOutcome s.mem (State.addr P.out) P.K (s.gpr .r0)
    (Spec.Rsa.privateChecked P.nB P.eB em (pB P σ) (qB P σ) (dpB P σ) (dqB P σ) (qiB P σ))

theorem R0.of_st {σ s t : State} (h : R0 P σ s) (st : P.lay.St σ t) (hm : t.mem = s.mem) : R0 P σ t :=
  let ⟨hS, em, he, hb⟩ := h
  ⟨⟨hS.1, st⟩, em, he, by rw [hm]; exact hb⟩

theorem arg_lt {j : Nat} (hj : j < 23) : Impl.RsaPkcs1Sig.Arm.argOff frameBytes j < 4096 := by
  unfold Impl.RsaPkcs1Sig.Arm.argOff
  split <;> simp only [frameBytes] <;> omega_using [hj]

/-- `str r0, [r12, #4k]` of the stack argument `k`. -/
theorem strSlot {σ s : State} {k : Nat} (h : R0 P σ s) (hs : Slots P s.mem k) (hk : k < 18)
    (h12 : s.gpr .r12 = P.B) (hv : s.gpr .r0 = (outv P).getD k 0) {is : List Instr} {Q : State → Prop}
    (kk : ∀ t, R0 P σ t → Slots P t.mem (k + 1) → t.gpr = s.gpr → WP isa (.block is) t Q) :
    WP isa (.block (.str .r0 .r12 (4 * k) :: is)) s Q := by
  obtain ⟨hS, em, he, hb⟩ := h
  have hK := hS.1.k1024
  refine hS.2.wp_strFr (d := 4 * k) (by show 4 * k + 4 ≤ frameBytes; simp only [frameBytes]; omega_using [hk]) (by omega_using [hk]) h12
    fun t st m => kk t ⟨⟨hS.1, st⟩, em, he, ?_⟩ ?_ m.gpr
  · rw [m.mem, bytesAt_frame frame1' (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx
      exact Lay.fr_sep (by simp only [oEM]; omega_using [hk]) (by simp only [oEM]; omega_using [hK]) (by omega_using [hk])) (by omega_using [hK])]
    exact hb
  · intro i hi
    rw [m.mem]
    rcases (by omega_using [hi] : i = k ∨ i < k) with rfl | hik
    · rw [Mem.readW_writeW_self32, hv]
    · rw [Lay.readW_fr_other _ _ _ (by omega_using [hik]) (by omega_using [hk, hi]) (by omega_using [hk])]
      exact hs i hik
where
  frame1' {m : Mem} {d : Nat} {v : BitVec 32} : Frame [⟨P.lay.fr d, 4⟩] m (m.writeW (P.lay.fr d) v) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

/-- Argument `j` to the call's stack argument `k`. -/
theorem argv21 (P : EP) : 21 ≤ P.argv.length := by
  simp only [EP.argv, List.length_append, List.length_cons, List.length_nil]; omega_using []

theorem copySlot {σ s : State} {k j : Nat} (h : R0 P σ s) (hs : Slots P s.mem k) (hk : k < 18)
    (h12 : s.gpr .r12 = P.B) (hj : j < 23) (hjl : j < P.argv.length) (hv : P.argv.getD j 0 = (outv P).getD k 0)
    {is : List Instr}
    {Q : State → Prop} (kk : ∀ t, R0 P σ t → Slots P t.mem (k + 1) → t.gpr .r12 = P.B → WP isa (.block is) t Q) :
    WP isa (.block (copyArg j k ++ is)) s Q :=
  h.1.2.wp_arg (j := j) hjl (arg_lt hj)
    fun t1 s1 u1 => strSlot (h.of_st s1 u1.mem) (by rw [u1.mem]; exact hs)
      hk (by rw [u1.other _ (by decide), h12]) (by rw [u1.gpr, hv])
      fun t st sl g => kk t st sl (by rw [g, u1.other _ (by decide), h12])

theorem callStack_wp {σ s : State} (h : R0 P σ s) :
    WP isa (.block callStack) s fun t => R0 P σ t ∧ Slots P t.mem 16 ∧ t.gpr .r12 = P.B := by
  simp only [callStack, List.append_assoc, List.cons_append, List.nil_append]
  refine Bignum.Arm.wp_stackAddr (by decide) fun t0 u0 => ?_
  obtain h0 : R0 P σ t0 := h.of_st (h.1.2.of_rest (u0.rest (ws := [.r12]) (by simp)) u0.mem) u0.mem
  obtain r12 : t0.gpr .r12 = P.B := by rw [u0.gpr, h.1.2.sp, BitVec.add_zero]
  obtain z : Slots P t0.mem 0 := fun _ hi => absurd hi (Nat.not_lt_zero _)
  refine copySlot h0 z (by decide) r12 (j := 4) (by decide) (Nat.lt_of_lt_of_le (by decide) (argv21 P)) rfl fun t1 h1 z1 r1 => ?_
  refine copySlot h1 z1 (by decide) r1 (j := 5) (by decide) (Nat.lt_of_lt_of_le (by decide) (argv21 P)) rfl fun t2 h2 z2 r2 => ?_
  refine wp_dp (op2_imm (by decide)) fun t3 u3 => ?_
  obtain h3 : R0 P σ t3 := h2.of_st (h2.1.2.of_rest (u3.rest (ws := [.r0]) (by simp)) u3.mem) u3.mem
  obtain r3 : t3.gpr .r12 = P.B := by rw [u3.other _ (by decide), r2]
  refine strSlot (k := 2) h3 (by rw [u3.mem]; exact z2) (by decide) r3 (by rw [u3.gpr, dpVal, r2]; rfl)
    fun t4 h4 z4 g4 => ?_
  obtain r4 : t4.gpr .r12 = P.B := by rw [g4, r3]
  refine copySlot h4 z4 (by decide) r4 (j := 3) (by decide) (Nat.lt_of_lt_of_le (by decide) (argv21 P)) rfl fun t5 h5 z5 r5 => ?_
  refine copySlot h5 z5 (by decide) r5 (j := 9) (by decide) (Nat.lt_of_lt_of_le (by decide) (argv21 P)) rfl fun t6 h6 z6 r6 => ?_
  refine copySlot h6 z6 (by decide) r6 (j := 10) (by decide) (Nat.lt_of_lt_of_le (by decide) (argv21 P)) rfl fun t7 h7 z7 r7 => ?_
  refine copySlot h7 z7 (by decide) r7 (j := 11) (by decide) (Nat.lt_of_lt_of_le (by decide) (argv21 P)) rfl fun t8 h8 z8 r8 => ?_
  refine copySlot h8 z8 (by decide) r8 (j := 12) (by decide) (Nat.lt_of_lt_of_le (by decide) (argv21 P)) rfl fun t9 h9 z9 r9 => ?_
  refine copySlot h9 z9 (by decide) r9 (j := 13) (by decide) (Nat.lt_of_lt_of_le (by decide) (argv21 P)) rfl fun t10 h10 z10 r10 => ?_
  refine copySlot h10 z10 (by decide) r10 (j := 14) (by decide) (Nat.lt_of_lt_of_le (by decide) (argv21 P)) rfl fun t11 h11 z11 r11 => ?_
  refine copySlot h11 z11 (by decide) r11 (j := 15) (by decide) (Nat.lt_of_lt_of_le (by decide) (argv21 P)) rfl fun t12 h12 z12 r12 => ?_
  refine copySlot h12 z12 (by decide) r12 (j := 16) (by decide) (Nat.lt_of_lt_of_le (by decide) (argv21 P)) rfl fun t13 h13 z13 r13 => ?_
  refine copySlot h13 z13 (by decide) r13 (j := 17) (by decide) (Nat.lt_of_lt_of_le (by decide) (argv21 P)) rfl fun t14 h14 z14 r14 => ?_
  refine copySlot h14 z14 (by decide) r14 (j := 18) (by decide) (Nat.lt_of_lt_of_le (by decide) (argv21 P)) rfl fun t15 h15 z15 r15 => ?_
  refine copySlot h15 z15 (by decide) r15 (j := 19) (by decide) (Nat.lt_of_lt_of_le (by decide) (argv21 P)) rfl fun t16 h16 z16 r16 => ?_
  refine copySlot h16 z16 (by decide) r16 (j := 20) (by decide) (Nat.lt_of_lt_of_le (by decide) (argv21 P)) rfl fun t17 h17 z17 r17 => ?_
  exact WP.block_nil ⟨h17, z17, r17⟩

theorem callPre_wp {σ s : State} (h : R0 P σ s) (z : Slots P s.mem 16) (r12 : s.gpr .r12 = P.B) :
    WP isa (.block (callPre P.pc)) s fun t => R0 P σ t ∧ Slots P t.mem (ncall P) := by
  unfold callPre ncall
  cases hpc : P.pc
  · exact WP.block_nil ⟨h, z⟩
  · have len : P.argv.length = 23 := by simp [EP.argv, hpc]
    rw [← List.append_nil (copyArg 22 17)]
    refine copySlot h z (by decide) r12 (j := 21) (by decide) (by omega_using [len]) (by simp [EP.argv, outv, hpc])
      fun t1 h1 z1 r1 => ?_
    refine copySlot h1 z1 (by decide) r1 (j := 22) (by decide) (by omega_using [len]) (by simp [EP.argv, outv, hpc])
      fun t2 h2 z2 _ => WP.block_nil ⟨h2, z2⟩

theorem callRegs_wp {σ s : State} (h : R0 P σ s) (z : Slots P s.mem (ncall P)) :
    WP isa (.block callRegs) s (R1 P σ) := by
  have s17 := h.1.2
  refine s17.wp_arg (j := 0) (Nat.lt_of_lt_of_le (by decide) (argv21 P)) (by dsimp only; decide) fun t18 s18 u18 => ?_
  refine s18.wp_arg (j := 3) (Nat.lt_of_lt_of_le (by decide) (argv21 P)) (by dsimp only; decide) fun t19 s19 u19 => ?_
  refine s19.wp_arg (j := 2) (Nat.lt_of_lt_of_le (by decide) (argv21 P)) (by dsimp only; decide) fun t20 s20 u20 => ?_
  refine s20.wp_arg (j := 3) (Nat.lt_of_lt_of_le (by decide) (argv21 P)) (by dsimp only; decide) fun t21 s21 u21 => WP.block_nil ?_
  obtain mm : t21.mem = s.mem := by rw [u21.mem, u20.mem, u19.mem, u18.mem]
  refine ⟨h.of_st s21 mm, by rw [mm]; exact z, ?_, ?_, ?_, ?_⟩
  · rw [u21.other _ (by decide), u20.other _ (by decide), u19.other _ (by decide), u18.gpr]; rfl
  · rw [u21.other _ (by decide), u20.other _ (by decide), u19.gpr]; rfl
  · rw [u21.other _ (by decide), u20.gpr]; rfl
  · rw [u21.gpr]; rfl

theorem callArgs_wp {σ s : State} (h : R0 P σ s) : WP isa (.block (callArgs P.pc)) s (R1 P σ) := by
  rw [callArgs, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (callStack_wp h) fun t ⟨ht, z, r12⟩ => ?_
  exact WP.mono (callPre_wp ht z r12) fun u ⟨hu, zu⟩ => callRegs_wp hu zu

theorem R1.privArgs {σ s : State} (h : R1 P σ s) :
    PrivArgs s P.out P.n P.e (P.B + BitVec.ofNat 32 oEM) P.p P.q P.dp P.dq P.qinv P.scr P.K P.el P.pl P.ql P.sl := by
  obtain ⟨⟨hs, -⟩, oa, r0, r1, r2, r3⟩ := h
  obtain a : ∀ i < 16, stackArg s i = (outv P).getD i 0 := fun i hi => by
    rw [← oa i (by unfold ncall; split <;> omega_using [hi])]
    simp only [stackArg, stackArgAddr, hs.2.sp]
    rw [hs.2.ok.addrB (P.lt_lay (by simp only [frameBytes]; omega_using [hi]))]
  have h1 := hs.1
  exact ⟨r0, r1, r2, r3, a 0 (by decide), a 1 (by decide), a 2 (by decide), a 3 (by decide), a 4 (by decide),
    a 5 (by decide), a 6 (by decide), a 7 (by decide), a 8 (by decide), a 9 (by decide), a 10 (by decide),
    a 11 (by decide), a 12 (by decide), a 13 (by decide), a 14 (by decide), a 15 (by decide), h1.kv, h1.el1,
    h1.elK, h1.pl1, h1.plK, h1.ql1, h1.qlK, h1.slK,
    by have := hs.1.ok.fits P.SCR (by simp); simp only [Proof.X25519.Arm.addr_toNat] at this; omega_using [this]⟩

/-- `EM`, as the call reads it. -/
theorem inpA (P : EP) {σ : State} (h : In P σ) : State.addr (P.B + BitVec.ofNat 32 oEM) = P.lay.fr oEM :=
  h.ok.addrB (P.lt_lay (by decide))

theorem call_pre {σ s : State} (h : R1 P σ s) :
    (Proof.Rsa.privateCheckedContract abi Proof.Rsa.Arm.stackBytes).pre
      (s.callEntry.withRegions (privRd P.B P.n P.e (P.B + BitVec.ofNat 32 oEM) P.p P.q P.dp P.dq P.qinv P.K P.el
        P.pl P.ql) (privWr P.out P.scr P.K P.sl)) := by
  have hs := h.1.1
  have ok := hs.1.ok
  have hK := hs.1.k1024
  have fit := ok.fit
  have hB := ok.B56
  obtain e := inpA P hs.1
  obtain q0 : State.addr P.B = P.lay.fr 0 := by simp
  refine priv_pre h.privArgs hs.2.sp hB (by simp only [frameBytes] at fit; omega_using [fit]) ?_ (List.pairwise_pair.mp ok.wrw)
    ?_ ?_
  · intro w hw r hr
    have hw' : w ∈ P.lay.rw := hw
    simp only [privRd, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ok.rw_ro hw' (by simp)
    · exact ok.rw_ro hw' (by simp)
    · rw [e]; exact (ok.stk_fr (.inr hw') (by simp only [oEM, frameBytes]; omega_using [hK])).symm
    · exact ok.rw_ro hw' (by simp)
    · exact ok.rw_ro hw' (by simp)
    · exact ok.rw_ro hw' (by simp)
    · exact ok.rw_ro hw' (by simp)
    · exact ok.rw_ro hw' (by simp)
    · rw [q0]; exact (ok.stk_fr (d := 0) (n := 64) (.inr hw') (by simp only [frameBytes]; omega_using [])).symm
  · intro r hr
    have low : (⟨State.addr P.B - BitVec.ofNat 64 3440, 3440⟩ : Region) = P.lay.LOW := rfl
    rw [low]
    simp only [privRd, privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ok.low_buf (R := P.OUT) (.inr (by simp))
    · exact ok.low_buf (R := P.SCR) (.inr (by simp))
    · exact ok.low_buf (R := P.N) (.inl (by simp))
    · exact ok.low_buf (R := P.E) (.inl (by simp))
    · rw [e]; exact (Lay.fr_low (by simp only [oEM]; omega_using [hK])).symm
    · exact ok.low_buf (R := P.PP) (.inl (by simp))
    · exact ok.low_buf (R := P.QQ) (.inl (by simp))
    · exact ok.low_buf (R := P.DP) (.inl (by simp))
    · exact ok.low_buf (R := P.DQ) (.inl (by simp))
    · exact ok.low_buf (R := P.QI) (.inl (by simp))
    · rw [q0]; exact (Lay.fr_low (by decide)).symm
  · intro r hr
    simp only [privBufs, List.mem_cons, List.not_mem_nil, or_false] at hr
    obtain fs := fun {R : Region} (hR : R ∈ P.lay.ro ++ P.lay.rw) => ok.fits R hR
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · rw [Proof.X25519.Arm.addr_toNat, Proof.X25519.Arm.toNat_add_lt (by
        simp only [oEM, frameBytes] at fit ⊢; rw [BitVec.toNat_ofNat]; omega_using [fit]), BitVec.toNat_ofNat]
      simp only [oEM, frameBytes] at fit ⊢; omega_using [hK, fit]
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)

theorem call_vp (v : Proof.Rsa.Arm.CrtImpl) :
    VP (R1 P) (.call (Proof.Rsa.Arm.privName v) (Proof.Rsa.Arm.privCode v)) (R2 P) := by
  refine VP.callF (Proof.Rsa.Arm.code_verified v) (privCode_stack v)
    (privRd P.B P.n P.e (P.B + BitVec.ofNat 32 oEM) P.p P.q P.dp P.dq P.qinv P.K P.el P.pl P.ql)
    (privWr P.out P.scr P.K P.sl) (fun _ _ h => call_pre h) (fun σ s h => ?_) (fun σ s h => ?_)
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) (fun σ s s' h rd wr sp fr _ po => ?_)
  · have hs := h.1.1
    have ok := hs.1.ok
    have hK := hs.1.k1024
    obtain e := inpA P hs.1
    obtain q0 : State.addr P.B = P.lay.fr 0 := by simp
    obtain hro : ∀ R ∈ P.lay.ro, Covers [R] (s.rd ++ s.wr) := fun R hR =>
      Covers.left (Covers.of_mem fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hs.2.rd, ok.rd]; exact List.mem_append_left _ hR)
    obtain hrw : ∀ R ∈ P.lay.rw, Covers [R] s.wr := fun R hR =>
      Covers.of_mem fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hs.2.wr, ok.wr]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hR)
    obtain wr : Covers (privWr P.out P.scr P.K P.sl) s.wr := (hrw P.OUT (by simp)).cons (hrw P.SCR (by simp))
    refine ⟨Covers.append_left ((hro P.N (by simp)).cons ((hro P.E (by simp)).cons ?_)) wr.right, wr⟩
    refine Covers.cons ?_ ((hro P.PP (by simp)).cons ((hro P.QQ (by simp)).cons ((hro P.DP (by simp)).cons
      ((hro P.DQ (by simp)).cons ((hro P.QI (by simp)).cons (Covers.cons ?_ Covers.nil))))))
    · rw [e]; exact (Covers.one (hs.2.inFr (by show oEM + P.K ≤ frameBytes; simp only [oEM, frameBytes]; omega_using [hK]))).right
    · rw [q0]; exact (Covers.one (hs.2.inFr (by show 0 + 64 ≤ frameBytes; decide))).right
  · rw [h.1.1.2.sp]; exact h.1.1.1.ok.B56
  · exact priv_pub h₁.privArgs h₂.privArgs (by rw [h₁.1.1.2.sp, h₂.1.1.2.sp]) (by rw [h₁.1.1.nB, h₂.1.1.nB])
      (by rw [h₁.1.1.eB, h₂.1.1.eB]) _ _
  · have hh := h
    obtain ⟨⟨hs, em, he, hb⟩, -, -⟩ := h
    have ok := hs.1.ok
    have hK := hs.1.k1024
    obtain low : FrameStack.belowA s.sp Proof.Rsa.Arm.stackBytes = P.lay.LOW := by rw [hs.2.sp]; exact ok.low_eq
    rw [low] at fr
    have fr' : Frame [P.OUT, P.SCR, P.lay.LOW] s.mem s'.mem := fr
    obtain st : P.lay.St σ s' := hs.2.write fr' (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨P.OUT, by simp, fun _ h => h⟩
      · exact ⟨P.SCR, by simp, fun _ h => h⟩
      · exact ⟨P.lay.LOW, by simp, fun _ h => h⟩) rd wr sp
    refine ⟨⟨hs.1, st⟩, em, he, ?_⟩
    have := priv_post hh.privArgs po
    rw [hs.nB, hs.eB, inpA P hs.1, hb, hs.2.ro (R := P.PP) (by simp), hs.2.ro (R := P.QQ) (by simp),
      hs.2.ro (R := P.DP) (by simp), hs.2.ro (R := P.DQ) (by simp), hs.2.ro (R := P.QI) (by simp)] at this
    exact this

/-! ## `vg_rsa_private_checked_precomputed` -/

theorem R1.preArgs {σ s : State} (hpc : P.pc = true) (h : R1 P σ s) :
    stackArg s 16 = P.pre ∧ stackArg s 17 = BitVec.ofNat 32 P.prl := by
  obtain ⟨⟨hs, -⟩, oa, -⟩ := h
  obtain a : ∀ i < 18, stackArg s i = (outv P).getD i 0 := fun i hi => by
    rw [← oa i (by unfold ncall; rw [hpc]; exact hi)]
    simp only [stackArg, stackArgAddr, hs.2.sp]
    rw [hs.2.ok.addrB (P.lt_lay (by simp only [frameBytes]; omega_using [hi]))]
  refine ⟨(a 16 (by decide)).trans ?_, (a 17 (by decide)).trans ?_⟩ <;> simp [outv, hpc]

theorem In.prl32 {σ : State} (hpc : P.pc = true) (h : In P σ) : P.prl < 2 ^ 32 := by
  have := h.ok.fits P.PRE (List.mem_append_left _ (by simp [EP.ro, hpc]))
  simp only [Proof.X25519.Arm.addr_toNat] at this
  omega_using [this]

theorem call_preP {σ s : State} (hpc : P.pc = true) (h : R1 P σ s) :
    (Proof.Rsa.privateCheckedPrecomputedContract abi Proof.Rsa.Arm.stackBytes).pre
      (s.callEntry.withRegions (privRdP P.B P.n P.e (P.B + BitVec.ofNat 32 oEM) P.p P.q P.dp P.dq P.qinv P.pre
        P.K P.el P.pl P.ql P.prl) (privWr P.out P.scr P.K P.sl)) := by
  have hs := h.1.1
  have ok := hs.1.ok
  have hK := hs.1.k1024
  have fit := ok.fit
  have hB := ok.B56
  obtain e := inpA P hs.1
  obtain q0 : State.addr P.B = P.lay.fr 0 := by simp
  obtain preRo : P.PRE ∈ P.lay.ro := by simp [EP.ro, hpc]
  obtain hA : P.lay.A = 76 := by simp [hpc]
  rw [hA] at fit
  obtain ⟨a16, a17⟩ := h.preArgs hpc
  refine priv_preP h.privArgs a16 a17 (hs.1.prl32 hpc) hs.2.sp hB (by simp only [frameBytes] at fit; omega_using [fit]) ?_
    (List.pairwise_pair.mp ok.wrw) ?_ ?_ (hs.1.prl hpc) ?_
  · intro w hw r hr
    have hw' : w ∈ P.lay.rw := hw
    simp only [privRdP, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ok.rw_ro hw' (by simp)
    · exact ok.rw_ro hw' (by simp)
    · rw [e]; exact (ok.stk_fr (.inr hw') (by simp only [oEM, frameBytes]; omega_using [hK])).symm
    · exact ok.rw_ro hw' (by simp)
    · exact ok.rw_ro hw' (by simp)
    · exact ok.rw_ro hw' (by simp)
    · exact ok.rw_ro hw' (by simp)
    · exact ok.rw_ro hw' (by simp)
    · exact ok.rw_ro hw' preRo
    · rw [q0]; exact (ok.stk_fr (d := 0) (n := 72) (.inr hw') (by simp only [frameBytes]; omega_using [])).symm
  · intro r hr
    have low : (⟨State.addr P.B - BitVec.ofNat 64 3440, 3440⟩ : Region) = P.lay.LOW := rfl
    rw [low]
    simp only [privRdP, privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ok.low_buf (R := P.OUT) (.inr (by simp))
    · exact ok.low_buf (R := P.SCR) (.inr (by simp))
    · exact ok.low_buf (R := P.N) (.inl (by simp))
    · exact ok.low_buf (R := P.E) (.inl (by simp))
    · rw [e]; exact (Lay.fr_low (by simp only [oEM]; omega_using [hK])).symm
    · exact ok.low_buf (R := P.PP) (.inl (by simp))
    · exact ok.low_buf (R := P.QQ) (.inl (by simp))
    · exact ok.low_buf (R := P.DP) (.inl (by simp))
    · exact ok.low_buf (R := P.DQ) (.inl (by simp))
    · exact ok.low_buf (R := P.QI) (.inl (by simp))
    · exact ok.low_buf (R := P.PRE) (.inl preRo)
    · rw [q0]; exact (Lay.fr_low (by decide)).symm
  · intro r hr
    simp only [privBufs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    obtain fs := fun {R : Region} (hR : R ∈ P.lay.ro ++ P.lay.rw) => ok.fits R hR
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · rw [Proof.X25519.Arm.addr_toNat, Proof.X25519.Arm.toNat_add_lt (by
        simp only [oEM, frameBytes] at fit ⊢; rw [BitVec.toNat_ofNat]; omega_using [fit]), BitVec.toNat_ofNat]
      simp only [oEM, frameBytes] at fit ⊢; omega_using [hK, fit]
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (List.mem_append_left _ preRo)
  · have rn := hs.2.ro (R := P.N) (by simp)
    obtain rp := hs.2.ro (R := P.PP) (by simp)
    obtain rq := hs.2.ro (R := P.QQ) (by simp)
    obtain rw := hs.2.ro_words (R := P.PRE) preRo (n := P.prl) rfl
    dsimp only at rn rp rq rw
    rw [rn, rp, rq, rw]
    exact hs.1.pre hpc

theorem leak_st {σ s : State} (hpc : P.pc = true) (hs : S P σ s) :
    Spec.Rsa.privatePrecomputedLeak s.mem (State.addr P.pre) P.K = P.preL := by
  obtain preRo : P.PRE ∈ P.lay.ro := by simp [EP.ro, hpc]
  obtain le : Spec.Rsa.precomputedWords P.K ≤ P.prl := by
    rw [hs.1.prl hpc, Spec.Rsa.privatePrecomputedWords]; omega_using []
  obtain rw := hs.2.ro_words (R := P.PRE) preRo (n := P.prl) rfl
  dsimp only at rw
  rw [← hs.1.preL hpc]
  unfold Spec.Rsa.privatePrecomputedLeak
  rw [Proof.Rsa.Arm.wordsAt_take le, Proof.Rsa.Arm.wordsAt_take (m := σ.mem) le, rw]

theorem call_vpP (v : Proof.Rsa.Arm.CrtImpl) (hpc : P.pc = true) :
    VP (R1 P) (.call (Proof.Rsa.Arm.privNameP v) (Proof.Rsa.Arm.privCodeP v)) (R2 P) := by
  refine VP.callC (fun s h => Proof.Rsa.Arm.private_contract_correctP v s h) (Proof.Rsa.Arm.private_contract_ctP v)
    (privCodeP_stack v)
    (privRdP P.B P.n P.e (P.B + BitVec.ofNat 32 oEM) P.p P.q P.dp P.dq P.qinv P.pre P.K P.el P.pl P.ql P.prl)
    (privWr P.out P.scr P.K P.sl) (fun _ _ h => call_preP hpc h) (fun σ s h => ?_) (fun σ s h => ?_)
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) (fun σ s s' h rd wr sp fr _ po => ?_)
  · have hs := h.1.1
    have ok := hs.1.ok
    have hK := hs.1.k1024
    obtain e := inpA P hs.1
    obtain q0 : State.addr P.B = P.lay.fr 0 := by simp
    obtain hro : ∀ R ∈ P.lay.ro, Covers [R] (s.rd ++ s.wr) := fun R hR =>
      Covers.left (Covers.of_mem fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hs.2.rd, ok.rd]; exact List.mem_append_left _ hR)
    obtain hrw : ∀ R ∈ P.lay.rw, Covers [R] s.wr := fun R hR =>
      Covers.of_mem fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hs.2.wr, ok.wr]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hR)
    obtain wr : Covers (privWr P.out P.scr P.K P.sl) s.wr := (hrw P.OUT (by simp)).cons (hrw P.SCR (by simp))
    refine ⟨Covers.append_left ((hro P.N (by simp)).cons ((hro P.E (by simp)).cons ?_)) wr.right, wr⟩
    refine Covers.cons ?_ ((hro P.PP (by simp)).cons ((hro P.QQ (by simp)).cons ((hro P.DP (by simp)).cons
      ((hro P.DQ (by simp)).cons ((hro P.QI (by simp)).cons ((hro P.PRE (by simp [EP.ro, hpc])).cons
        (Covers.cons ?_ Covers.nil)))))))
    · rw [e]; exact (Covers.one (hs.2.inFr (by show oEM + P.K ≤ frameBytes; simp only [oEM, frameBytes]; omega_using [hK]))).right
    · rw [q0]; exact (Covers.one (hs.2.inFr (by show 0 + 72 ≤ frameBytes; decide))).right
  · rw [h.1.1.2.sp]; exact h.1.1.1.ok.B56
  · obtain ⟨p16, p17⟩ := h₁.preArgs hpc
    obtain ⟨q16, q17⟩ := h₂.preArgs hpc
    exact priv_pubP h₁.privArgs h₂.privArgs (by rw [h₁.1.1.2.sp, h₂.1.1.2.sp]) p16 q16 p17 q17
      (by rw [h₁.1.1.nB, h₂.1.1.nB]) (by rw [h₁.1.1.eB, h₂.1.1.eB])
      (by rw [leak_st hpc h₁.1.1, leak_st hpc h₂.1.1]) _ _
  · have hh := h
    obtain ⟨⟨hs, em, he, hb⟩, -, -⟩ := h
    have ok := hs.1.ok
    have hK := hs.1.k1024
    obtain low : FrameStack.belowA s.sp Proof.Rsa.Arm.stackBytes = P.lay.LOW := by rw [hs.2.sp]; exact ok.low_eq
    rw [low] at fr
    have fr' : Frame [P.OUT, P.SCR, P.lay.LOW] s.mem s'.mem := fr
    obtain st : P.lay.St σ s' := hs.2.write fr' (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨P.OUT, by simp, fun _ h => h⟩
      · exact ⟨P.SCR, by simp, fun _ h => h⟩
      · exact ⟨P.lay.LOW, by simp, fun _ h => h⟩) rd wr sp
    refine ⟨⟨hs.1, st⟩, em, he, ?_⟩
    have := priv_postP hh.privArgs po
    rw [hs.nB, hs.eB, inpA P hs.1, hb, hs.2.ro (R := P.PP) (by simp), hs.2.ro (R := P.QQ) (by simp),
      hs.2.ro (R := P.DP) (by simp), hs.2.ro (R := P.DQ) (by simp), hs.2.ro (R := P.QI) (by simp)] at this
    exact this

/-- The checked private operation the code calls: with `pc`,
`vg_rsa_private_checked_precomputed`. -/
def privN (pc : Bool) (v : Proof.Rsa.Arm.CrtImpl) : String :=
  if pc then Proof.Rsa.Arm.privNameP v else Proof.Rsa.Arm.privName v
def privC (pc : Bool) (v : Proof.Rsa.Arm.CrtImpl) : Prog isa :=
  if pc then Proof.Rsa.Arm.privCodeP v else Proof.Rsa.Arm.privCode v

theorem call_vpG (v : Proof.Rsa.Arm.CrtImpl) : VP (R1 P) (.call (privN P.pc v) (privC P.pc v)) (R2 P) := by
  cases hpc : P.pc
  · exact call_vp v
  · exact call_vpP v hpc

end VG.Proof.RsaPkcs1Sig.Arm.Sg

end

end

/-! ### `RsaPkcs1Sig.Arm.SgTail`, which only this module used -/

section

/-!
# RSASSA-PKCS1-v1_5 signing on ARMv7: after the call

The result kept in `r3` while `EM` is overwritten with zeros (`wipeArgs_wp`,
`wipe_wp`), and returned (`fin_wp`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.Arm.Sg

open VG VG.Arm VG.Impl.RsaPkcs1Sig.Arm.Sign VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_dp op2_imm op2_reg dpVal)

variable {P : EP}

/-- The signature, and the result in `r`. -/
def SR (P : EP) (σ : State) (m : Mem) (r : BitVec 32) : Prop :=
  ∃ em, enc P σ = some em ∧ Spec.Rsa.writtenOutcome m (State.addr P.out) P.K r
    (Spec.Rsa.privateChecked P.nB P.eB em (pB P σ) (qB P σ) (dpB P σ) (dqB P σ) (qiB P σ))

/-- Before the wipe of `EM`. -/
def R3 (P : EP) (σ s : State) : Prop :=
  S P σ s ∧ SR P σ s.mem (s.gpr .r3) ∧ s.gpr .r0 = P.B + BitVec.ofNat 32 oEM ∧
    s.gpr .lr = BitVec.ofNat 32 P.K ∧ s.gpr .r2 = 0

/-- `EM` wiped. -/
def R4 (P : EP) (σ s : State) : Prop := S P σ s ∧ SR P σ s.mem (s.gpr .r3)

theorem writtenOutcome_congr {m m' : Mem} {a : Addr} {K : Nat} {r : BitVec 32} {o : Spec.Rsa.Outcome}
    (hb : Spec.Rsa.bytesAt m' a K = Spec.Rsa.bytesAt m a K) (h : Spec.Rsa.writtenOutcome m a K r o) :
    Spec.Rsa.writtenOutcome m' a K r o := by
  cases o with
  | ok y => exact ⟨h.1, hb.trans h.2⟩
  | invalid => exact ⟨h.1, hb.trans h.2⟩
  | fault => exact ⟨h.1, hb.trans h.2⟩

theorem wipeArgs_wp {σ s : State} (h : R2 P σ s) : WP isa (.block wipeArgs) s (R3 P σ) := by
  obtain ⟨hs, sr⟩ := h
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  refine wp_mov (op2_reg _ _) fun t2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun t3 u3 => ?_
  have s3 : P.lay.St σ t3 := ((hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem).of_rest
    (u2.rest (ws := [.r3]) (by simp)) u2.mem).of_rest (u3.rest (ws := [.r0]) (by simp)) u3.mem
  refine s3.wp_arg (j := 3) (by simp) (by dsimp only; decide) fun t4 s4 u4 => ?_
  refine wp_mov (op2_imm (by decide)) fun t5 u5 => WP.block_nil ⟨⟨hs.1, s4.of_rest (u5.rest (ws := [.r2])
    (by simp)) u5.mem⟩, ?_, ?_, ?_, u5.gpr⟩
  · rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, u5.other _ (by decide), u4.other _ (by decide),
      u3.other _ (by decide), u2.gpr, u1.other _ (by decide)]
    exact sr
  · rw [u5.other _ (by decide), u4.other _ (by decide), u3.gpr, dpVal, u2.other _ (by decide), u1.gpr, hs.2.sp,
      BitVec.add_zero]
  · rw [u5.other _ (by decide), u4.gpr]; rfl

theorem wipe_wp {σ s : State} (h : R3 P σ s) : WP isa Impl.Bignum.Arm.maskBytes s (R4 P σ) := by
  obtain ⟨hs, sr, r0, lr, -⟩ := h
  have ok := hs.1.ok
  have hK := hs.1.k1024
  have e := inpA P hs.1
  have fit := ok.fit
  refine WP.mono (Bignum.Arm.maskBuffer_ok s (dst := P.B + BitVec.ofNat 32 oEM) (n := P.K)
    (by have := hs.1.k64; omega_using [this]) (by omega_using [hK]) (by
      rw [Proof.X25519.Arm.toNat_add_lt (by rw [BitVec.toNat_ofNat]; simp only [oEM, frameBytes] at fit ⊢; omega_using [fit]),
        BitVec.toNat_ofNat]
      simp only [oEM, frameBytes] at fit ⊢; omega_using [hK, fit])
    (by rw [e]; exact hs.2.inFr (by show oEM + P.K ≤ frameBytes; simp only [oEM, frameBytes]; omega_using [hK])) r0 lr)
    fun t ⟨_, fr, rest⟩ => ?_
  rw [e] at fr
  have st : P.lay.St σ t := hs.2.frameW (by show oEM + P.K ≤ frameBytes; simp only [oEM, frameBytes]; omega_using [hK]) fr
    rest.rd rest.wr rest.sp
  refine ⟨⟨hs.1, st⟩, ?_⟩
  have hb : Spec.Rsa.bytesAt t.mem (State.addr P.out) P.K = Spec.Rsa.bytesAt s.mem (State.addr P.out) P.K :=
    bytesAt_frame fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (ok.stk_fr (.inr (by simp)) (by show _ ≤ frameBytes + 56; simp only [oEM, frameBytes]; omega_using [hK])).symm)
      (by omega_using [hK])
  obtain ⟨em, he, w⟩ := sr
  rw [rest.gpr .r3 (by decide)]
  exact ⟨em, he, writtenOutcome_congr hb w⟩

theorem fin_wp {σ s : State} (h : R4 P σ s) : WP isa (.block [.mov .r0 (.reg .r3)]) s (Fin P σ) :=
  wp_mov (op2_reg _ _) fun t u => WP.block_nil ⟨⟨h.1.1, h.1.2.of_rest (u.rest (ws := [.r0]) (by simp)) u.mem⟩, by
    obtain ⟨em, he, w⟩ := h.2
    rw [Res, signId_some h.1.1 he, u.mem, u.gpr]
    exact w⟩

end VG.Proof.RsaPkcs1Sig.Arm.Sg

end

end


/-!
# RSASSA-PKCS1-v1_5 signing on ARMv7: the body

The pieces as `VP`s, correct and constant time at once, put together
(`body_vp`): from the state the body starts from, it ends with the result
(`Fin`), and two runs with the same public data leak the same trace. The
branch on the encoding's success agrees in two runs: it depends only on the
hash function's number and the lengths (`enc_isNone`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.Arm.Sg

open VG VG.Arm VG.Impl.RsaPkcs1Sig.Arm.Sign VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.Rsa.Arm.Recover (VP)

variable {P : EP}

theorem S_sp {σ₁ σ₂ s₁ s₂ : State} (h₁ : S P σ₁ s₁) (h₂ : S P σ₂ s₂) : s₁.sp = s₂.sp := by
  rw [h₁.2.sp, h₂.2.sp]

theorem encArgs_vp : VP (S P) (.block encArgs) (E1 P) :=
  VP.stk (code := [_, _, _, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁ h₂) fun _ _ h => encArgs_wp h

theorem encode_vp : VP (E1 P) Impl.RsaPkcs1Sig.Arm.encode (E2 P) :=
  VP.taint [.r0, .r1, .r2, .r3, .lr] encode_taint (fun _ _ _ _ h₁ h₂ r hr => by
    obtain ⟨-, a0, a1, a2, a3, a4⟩ := h₁
    obtain ⟨-, b0, b1, b2, b3, b4⟩ := h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [a0, b0]
    · rw [a1, b1]
    · rw [a2, b2]
    · rw [a3, b3]
    · rw [a4, b4]) fun _ _ h => encode_wp h

theorem cmp_vp : VP (E2 P) (.block [.cmp .r3 (.imm 0)]) (E3 P) :=
  VP.taint [.r3] cmp_taint (fun σ₁ σ₂ _ _ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [encR_r3 h₁.2, encR_r3 h₂.2]
    exact congrArg (fun b : Bool => if b = true then (0 : BitVec 32) else 1) (enc_isNone P σ₁ σ₂))
    fun _ _ h => cmp_wp h

theorem fail_vp : VP (fun σ s => E3 P σ s ∧ isa.eval .eq s = some true)
    (.seq (.block zeroArgs) (.seq Impl.Bignum.Arm.maskBytes (.block ret0))) (Fin P) :=
  (VP.stk (code := [_, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1.1.1 h₂.1.1.1)
    fun _ _ h => zeroArgs_wp h).seq
  ((VP.ct Bignum.Arm.maskBytes_ct (fun _ _ _ _ h₁ h₂ => ⟨by rw [h₁.2.2.1, h₂.2.2.1], by rw [h₁.2.2.2.1, h₂.2.2.2.1]⟩)
    fun _ _ h => zero_wp h).seq
  (VP.taint [] ret0_taint (fun _ _ _ _ _ _ _ h => absurd h List.not_mem_nil) fun _ _ h => ret0_wp h))

theorem callArgs_vp : VP (fun σ s => E3 P σ s ∧ isa.eval .eq s = some false) (.block (callArgs P.pc)) (R1 P) :=
  VP.stk (code := (callArgs P.pc).tail) (by generalize P.pc = b; cases b <;> decide)
    (by generalize P.pc = b; cases b <;> decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1.1.1 h₂.1.1.1)
    fun _ _ h => callArgs_wp (r0_of h)

theorem wipeArgs_vp : VP (R2 P) (.block wipeArgs) (R3 P) :=
  VP.stk (code := [_, _, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1 h₂.1)
    fun _ _ h => wipeArgs_wp h

theorem wipe_vp : VP (R3 P) Impl.Bignum.Arm.maskBytes (R4 P) :=
  VP.ct Bignum.Arm.maskBytes_ct (fun _ _ _ _ h₁ h₂ => ⟨by rw [h₁.2.2.1, h₂.2.2.1], by rw [h₁.2.2.2.1, h₂.2.2.2.1]⟩)
    fun _ _ h => wipe_wp h

theorem fin_vp : VP (R4 P) (.block [.mov .r0 (.reg .r3)]) (Fin P) :=
  VP.taint [] fin_taint (fun _ _ _ _ _ _ _ h => absurd h List.not_mem_nil) fun _ _ h => fin_wp h

theorem rest_vp (v : Proof.Rsa.Arm.CrtImpl) :
    VP (fun σ s => E3 P σ s ∧ isa.eval .eq s = some false)
      (rest P.pc (privN P.pc v) (privC P.pc v)) (Fin P) :=
  callArgs_vp.seq ((call_vpG v).seq (wipeArgs_vp.seq (wipe_vp.seq fin_vp)))

theorem body_vp (v : Proof.Rsa.Arm.CrtImpl) :
    VP (S P) (body P.pc (privN P.pc v) (privC P.pc v)) (Fin P) :=
  encArgs_vp.seq (encode_vp.seq (cmp_vp.seq (VP.ite (fun σ₁ σ₂ _ _ h₁ h₂ => by
    rw [Proof.X25519.Arm.eval_eq, Proof.X25519.Arm.eval_eq, h₁.2, h₂.2, enc_isNone P σ₁ σ₂]) fail_vp (rest_vp v))))

end VG.Proof.RsaPkcs1Sig.Arm.Sg
