module

public import VerifiedGarbage.Impl.RsaPkcs1Enc.Arm.Decrypt
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Entry
public import VerifiedGarbage.Spec.RsaPkcs1Enc.Contract
public import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSAES-PKCS1-v1_5 decryption on ARMv7: where everything is

`EP`: what two runs share (the frame's base `B`, the pointers, the lengths,
and the public key's bytes `nB` and `eB`), and its layout (`EP.lay`,
`Proof/RsaPkcs1Sig/Arm/Lay.lean`), with the 3440 bytes below the frame that
the private-key operation uses. `In P σ`: the state `σ` the body starts
from; `S P σ s`: a state of the body. The shared contract, with the stack of
the frames and of the calls, gives `In (ep s) (entered frameBytes s)`
(`in_of_pre`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.Arm.Dec

open VG VG.Arm VG.Impl.RsaPkcs1Enc.Arm.Decrypt VG.Proof.RsaPkcs1Sig.Arm

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
  K : Nat
  el : Nat
  dl : Nat
  pl : Nat
  ql : Nat
  sl : Nat
  nB : List Byte
  eB : List Byte

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

/-- The arguments, in order. -/
abbrev argv : List (BitVec 32) :=
  [P.out, BitVec.ofNat 32 P.K, P.ml, P.n, BitVec.ofNat 32 P.K, P.e, BitVec.ofNat 32 P.el, P.d,
    BitVec.ofNat 32 P.dl, P.inp, BitVec.ofNat 32 P.K, P.p, BitVec.ofNat 32 P.pl, P.q, BitVec.ofNat 32 P.ql,
    P.dp, BitVec.ofNat 32 P.pl, P.dq, BitVec.ofNat 32 P.ql, P.qinv, BitVec.ofNat 32 P.pl, P.scr,
    BitVec.ofNat 32 P.sl]

abbrev lay : Lay where
  B := P.B
  F := frameBytes
  A := 76
  argv := P.argv
  ro := [P.N, P.E, P.D, P.INP, P.PP, P.QQ, P.DP, P.DQ, P.QI]
  rw := [P.OUT, P.ML, P.SCR]
  C := 3440

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

/-- A state of the body. -/
abbrev S (P : EP) (σ s : State) : Prop := In P σ ∧ P.lay.St σ s

namespace In

variable {P : EP} {σ : State} (h : In P σ)
include h

theorem k64 : 64 ≤ P.K := h.kv.1
theorem k1024 : P.K ≤ 1024 := h.kv.2

end In

/-! ## The entry -/

/-- The stack the function uses: the push, the inner frame and the calls'. -/
abbrev stackBytes : Nat := 56 + frameBytes + 3440

/-- The shared contract, with that stack. -/
abbrev spec : Contract isa := Spec.RsaPkcs1Enc.decryptContract abi stackBytes

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
  K := (stackArg s 0).toNat
  el := (stackArg s 2).toNat
  dl := (stackArg s 4).toNat
  pl := (stackArg s 8).toNat
  ql := (stackArg s 10).toNat
  sl := (stackArg s 18).toNat
  nB := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat
  eB := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 1)) (stackArg s 2).toNat

theorem ep_lay (s : State) :
    (ep s).lay = layOf frameBytes 76 (ep s).argv [(ep s).N, (ep s).E, (ep s).D, (ep s).INP, (ep s).PP,
      (ep s).QQ, (ep s).DP, (ep s).DQ, (ep s).QI] [(ep s).OUT, (ep s).ML, (ep s).SCR] s 3440 := rfl

theorem in_of_pre {s : State} (h : spec.pre s) : In (ep s) (entered frameBytes s) := by
  sig_pre [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, abi,
    argRegs, reduceClassify, Loc.val] at h
  obtain ⟨hsp, hsa, hrd, hwr, oM, oN, oE, oD, oI, oP, oQ, oDP, oDQ, oQI, oS, oA,
    mN, mE, mD, mI, mP, mQ, mDP, mDQ, mQI, mS, mA, nS, eS, dS, iS, pS, qS, dpS, dqS, qiS, sA,
    kO, kM, kN, kE, kD, kI, kP, kQ, kDP, kDQ, kQI, kS, kA, fO, fM, fN, fE, fD, fI, fP, fQ, fDP, fDQ, fQI, fS,
    kv, olk, ilk, el1, elK, dl1, dlK, pl1, plK, ql1, qlK, dpl, qil, dql, slK⟩ := h
  have h3584 : 3584 ≤ s.sp.toNat := hsp
  have r1 : s.gpr .r1 = stackArg s 0 := BitVec.eq_of_toNat_eq olk
  have a6 : stackArg s 6 = stackArg s 0 := BitVec.eq_of_toNat_eq ilk
  have a12 : stackArg s 12 = stackArg s 8 := BitVec.eq_of_toNat_eq dpl
  have a16 : stackArg s 16 = stackArg s 8 := BitVec.eq_of_toNat_eq qil
  have a14 : stackArg s 14 = stackArg s 10 := BitVec.eq_of_toNat_eq dql
  rw [olk] at hwr oM oN oE oD oI oP oQ oDP oDQ oQI oS oA kO fO
  rw [ilk] at hrd oI mI iS kI fI
  rw [dpl] at hrd oDP mDP dpS kDP fDP
  rw [qil] at hrd oQI mQI qiS kQI fQI
  rw [dql] at hrd oDQ mDQ dqS kDQ fDQ
  have hpush : Frame [FrameStack.belowA s.sp 56] s.mem (entered frameBytes s).mem :=
    FrameStack.pushed_frameA (rs := Impl.RsaPkcs1Sig.Arm.pushRegs) (by show 56 ≤ s.sp.toNat; omega_arith)
  have below : Region.Sub (FrameStack.belowA s.sp 56)
      ⟨State.addr s.sp - BitVec.ofNat 64 3584, 3584⟩ := by
    show Region.Sub ⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩ _
    rw [FrameStack.addr_sub' (by omega_arith)]
    exact Offset.sub_below _ (by omega_arith) (by omega_arith)
  refine
    { ok := ?_
      kv := kv, el1 := el1, elK := elK, dl1 := dl1, dlK := dlK, pl1 := pl1, plK := plK, ql1 := ql1, qlK := qlK
      slK := slK
      nB := bytesAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kN.sub_left below).symm)
        (by show (stackArg s 0).toNat ≤ 2 ^ 64; omega_arith)
      eB := bytesAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kE.sub_left below).symm)
        (by show (stackArg s 2).toNat ≤ 2 ^ 64; omega_arith) }
  rw [ep_lay]
  refine ok_entered (by decide) (by decide) rfl hsp hsa hrd hwr ?_ ?_ ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [kN, kE, kD, kI, kP, kQ, kDP, kDQ, kQI, kO, kM, kS, kA]
  · intro w hw r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hw with rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [oN, oE, oD, oI, oP, oQ, oDP, oDQ, oQI, oA, mN, mE, mD, mI, mP, mQ, mDP, mDQ, mQI, mA,
      nS.symm, eS.symm, dS.symm, iS.symm, pS.symm, qS.symm, dpS.symm, dqS.symm, qiS.symm, sA]
  · refine List.Pairwise.cons ?_ (List.pairwise_pair.mpr mS)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [oM, oS]
  · intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [fN, fE, fD, fI, fP, fQ, fDP, fDQ, fQI, fO, fM, fS]
  · intro j hj
    rcases (by omega_arith : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    · rfl
    · simp [regArg, ep, r1]
    · rfl
    · rfl
  · intro i hi
    have : i < 19 := hi
    rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
        i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl <;> simp [ep, a6, a12, a14, a16]

end VG.Proof.RsaPkcs1Enc.Arm.Dec
