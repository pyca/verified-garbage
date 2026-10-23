module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.Arm.Sign
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Entry
public import VerifiedGarbage.Spec.RsaPkcs1Sig.Contract
public import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Framework.Offset

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

/-- The arguments, in order. -/
abbrev argv : List (BitVec 32) :=
  [P.out, BitVec.ofNat 32 P.K, P.n, BitVec.ofNat 32 P.K, P.e, BitVec.ofNat 32 P.el, P.hash, P.dig,
    BitVec.ofNat 32 P.dl, P.p, BitVec.ofNat 32 P.pl, P.q, BitVec.ofNat 32 P.ql, P.dp, BitVec.ofNat 32 P.pl,
    P.dq, BitVec.ofNat 32 P.ql, P.qinv, BitVec.ofNat 32 P.pl, P.scr, BitVec.ofNat 32 P.sl]

abbrev lay : Lay where
  B := P.B
  F := frameBytes
  A := 68
  argv := P.argv
  ro := [P.N, P.E, P.DIG, P.PP, P.QQ, P.DP, P.DQ, P.QI]
  rw := [P.OUT, P.SCR]
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
  slK : Spec.Rsa.scratchWords P.K ≤ P.sl
  dl32 : P.dl < 2 ^ 32
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

/-- The stack the function uses: the push, the inner frame and the call's. -/
abbrev stackBytes : Nat := 56 + frameBytes + 3440

/-- The shared contract, with that stack. -/
abbrev spec : Contract isa := Spec.RsaPkcs1Sig.signContract abi stackBytes

/-- The public parameters of an entry state. -/
def ep (s : State) : EP where
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

theorem ep_lay (s : State) :
    (ep s).lay = layOf frameBytes 68 (ep s).argv [(ep s).N, (ep s).E, (ep s).DIG, (ep s).PP, (ep s).QQ,
      (ep s).DP, (ep s).DQ, (ep s).QI] [(ep s).OUT, (ep s).SCR] s 3440 := rfl

theorem in_of_pre {s : State} (h : spec.pre s) : In (ep s) (entered frameBytes s) := by
  sig_pre [Spec.RsaPkcs1Sig.signContract, Spec.RsaPkcs1Sig.signSig, abi,
    argRegs, reduceClassify, Loc.val] at h
  obtain ⟨hsp, hsa, hrd, hwr, oN, oE, oD, oP, oQ, oDP, oDQ, oQI, oS, oA, nS, eS, dS, pS, qS, dpS, dqS, qiS, sA,
    kO, kN, kE, kD, kP, kQ, kDP, kDQ, kQI, kS, kA, fO, fN, fE, fD, fP, fQ, fDP, fDQ, fQI, fS,
    kv, olk, el1, elK, pl1, plK, ql1, qlK, dpl, qil, dql, slK⟩ := h
  have h4584 : 4584 ≤ s.sp.toNat := hsp
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
      ⟨State.addr s.sp - BitVec.ofNat 64 4584, 4584⟩ := by
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
        (by show (stackArg s 1).toNat ≤ 2 ^ 64; omega_arith) }
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
