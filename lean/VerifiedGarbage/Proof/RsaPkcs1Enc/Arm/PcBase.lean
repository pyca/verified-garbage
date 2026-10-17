module

public import VerifiedGarbage.Impl.RsaPkcs1Enc.Arm.Precomputed
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Entry
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Vp
public import VerifiedGarbage.Spec.RsaPkcs1Enc.Precomputed
public import VerifiedGarbage.Proof.Framework.Sig
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# RSAES-PKCS1-v1_5 encryption with a precomputed public key on ARMv7: where everything is

`EP`: what two runs share (the frame's base `B`, the pointers, the lengths,
`e` and the words of `pre`), and its layout (`EP.lay`, `Proof/RsaPkcs1Sig/Arm/Lay.lean`).
`In P σ`: the state `σ` the body starts from; `S P σ s`: a state of the body.
The shared contract, with the stack of the frames and of the call, gives
`In (ep s) (entered frameBytes s)` (`in_of_pre`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.Arm.Pc

open VG VG.Arm VG.Impl.RsaPkcs1Enc.Arm.Precomputed VG.Proof.RsaPkcs1Sig.Arm

/-- What two runs share. -/
structure EP where
  B : BitVec 32
  out : BitVec 32
  n : BitVec 32
  e : BitVec 32
  msg : BitVec 32
  ps : BitVec 32
  scr : BitVec 32
  pre : BitVec 32
  K : Nat
  el : Nat
  ml : Nat
  pl : Nat
  sl : Nat
  rl : Nat
  eB : List Byte
  pw : List (BitVec 64)

namespace EP

variable (P : EP)

abbrev OUT : Region := ⟨State.addr P.out, P.K⟩
abbrev N : Region := ⟨State.addr P.n, P.K⟩
abbrev E : Region := ⟨State.addr P.e, P.el⟩
abbrev MSG : Region := ⟨State.addr P.msg, P.ml⟩
abbrev PS : Region := ⟨State.addr P.ps, P.pl⟩
abbrev SCR : Region := ⟨State.addr P.scr, P.sl * 8⟩
abbrev PRE : Region := ⟨State.addr P.pre, P.rl * 8⟩

/-- The arguments, in order. -/
abbrev argv : List (BitVec 32) :=
  [P.out, BitVec.ofNat 32 P.K, P.n, BitVec.ofNat 32 P.K, P.e, BitVec.ofNat 32 P.el, P.msg,
    BitVec.ofNat 32 P.ml, P.ps, BitVec.ofNat 32 P.pl, P.scr, BitVec.ofNat 32 P.sl, P.pre,
    BitVec.ofNat 32 P.rl]

abbrev lay : Lay where
  B := P.B
  F := frameBytes
  A := 40
  argv := P.argv
  ro := [P.N, P.E, P.MSG, P.PS, P.PRE]
  rw := [P.OUT, P.SCR]

/-- `EM`. -/
abbrev EM : Region := ⟨P.lay.fr oEM, P.K⟩

end EP

/-- The state the body starts from. -/
structure In (P : EP) (σ : State) : Prop where
  ok : P.lay.Ok σ
  kv : Spec.Rsa.lenValid P.K
  el1 : 1 ≤ P.el
  elK : P.el ≤ P.K
  mlK : P.ml + 11 ≤ P.K
  plK : P.pl = P.K - P.ml - 3
  slK : Spec.Rsa.scratchWords P.K ≤ P.sl
  rlK : P.rl = Spec.Rsa.precomputedWords P.K
  eB : Spec.Rsa.bytesAt σ.mem (State.addr P.e) P.el = P.eB
  pw : Spec.Rsa.wordsAt σ.mem (State.addr P.pre) P.rl = P.pw

/-- A state of the body. -/
abbrev S (P : EP) (σ s : State) : Prop := In P σ ∧ P.lay.St σ s

namespace In

variable {P : EP} {σ : State} (h : In P σ)
include h

theorem k64 : 64 ≤ P.K := h.kv.1
theorem k1024 : P.K ≤ 1024 := h.kv.2
theorem pl8 : 8 ≤ P.pl := by have := h.plK; have := h.mlK; omega
theorem em_len : P.pl + P.ml + 3 = P.K := by have := h.plK; have := h.mlK; omega

end In

/-! ## The entry -/

/-- The stack the function uses: the push, the inner frame and the call's. -/
abbrev stackBytes : Nat := 56 + frameBytes + 56

/-- The shared contract, with that stack. -/
abbrev spec : Contract isa := Spec.RsaPkcs1Enc.encryptPrecomputedContract abi stackBytes

/-- The public parameters of an entry state. -/
def ep (s : State) : EP where
  B := s.sp - BitVec.ofNat 32 56 - BitVec.ofNat 32 frameBytes
  out := s.gpr .r0
  n := s.gpr .r2
  e := stackArg s 0
  msg := stackArg s 2
  ps := stackArg s 4
  scr := stackArg s 6
  pre := stackArg s 8
  K := (s.gpr .r3).toNat
  el := (stackArg s 1).toNat
  ml := (stackArg s 3).toNat
  pl := (stackArg s 5).toNat
  sl := (stackArg s 7).toNat
  rl := (stackArg s 9).toNat
  eB := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat
  pw := Spec.Rsa.wordsAt s.mem (State.addr (stackArg s 8)) (stackArg s 9).toNat

theorem ep_lay (s : State) :
    (ep s).lay = layOf frameBytes 40 (ep s).argv [(ep s).N, (ep s).E, (ep s).MSG, (ep s).PS, (ep s).PRE]
      [(ep s).OUT, (ep s).SCR] s := rfl

theorem in_of_pre {s : State} (h : spec.pre s) : In (ep s) (entered frameBytes s) := by
  sig_pre [Spec.RsaPkcs1Enc.encryptPrecomputedContract, Spec.RsaPkcs1Enc.encryptPrecomputedSig, abi,
    argRegs, reduceClassify, Loc.val] at h
  obtain ⟨hsp, hsa, hrd, hwr, oN, oE, oM, oP, oS, oR, oA, nS, eS, mS, pS, sR, sA, kO, kN, kE, kM, kP, kS,
    kR, kA, fO, fN, fE, fM, fP, fS, fR, kv, olk, el1, elK, mlK, plK, slK, rlK⟩ := h
  have h1168 : 1168 ≤ s.sp.toNat := hsp
  have r1 : s.gpr .r1 = s.gpr .r3 := BitVec.eq_of_toNat_eq olk
  rw [olk] at hwr oN oE oM oP oS oR oA kO fO
  have hpush : Frame [FrameStack.belowA s.sp 56] s.mem (entered frameBytes s).mem :=
    FrameStack.pushed_frameA (rs := Impl.RsaPkcs1Sig.Arm.pushRegs) (by show 56 ≤ s.sp.toNat; omega)
  have below : Region.Sub (FrameStack.belowA s.sp 56)
      ⟨State.addr s.sp - BitVec.ofNat 64 1168, 1168⟩ := by
    show Region.Sub ⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩ _
    rw [FrameStack.addr_sub' (by omega)]
    exact Offset.sub_below _ (by omega) (by omega)
  refine
    { ok := ?_
      kv := kv, el1 := el1, elK := elK, mlK := mlK, plK := plK, slK := slK, rlK := rlK
      eB := bytesAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kE.sub_left below).symm)
        (by show (stackArg s 1).toNat ≤ 2 ^ 64; omega)
      pw := wordsAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kR.sub_left below).symm)
        (by show (stackArg s 9).toNat * 8 ≤ 2 ^ 64; omega) }
  rw [ep_lay]
  refine ok_entered (by decide) (by decide) rfl hsp hsa hrd hwr ?_ ?_ ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [kN, kE, kM, kP, kR, kO, kS, kA]
  · intro w hw r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hw with rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [oN, oE, oM, oP, oR, oA, nS.symm, eS.symm, mS.symm, pS.symm, sR, sA]
  · exact List.pairwise_pair.mpr oS
  · intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [fN, fE, fM, fP, fR, fO, fS]
  · intro j hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    · rfl
    · simp [regArg, ep, r1]
    · rfl
    · simp [regArg, ep]
  · intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [ep]

end VG.Proof.RsaPkcs1Enc.Arm.Pc
