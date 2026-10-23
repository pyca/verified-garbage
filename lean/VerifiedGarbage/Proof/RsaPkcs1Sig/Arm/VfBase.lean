module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.Arm.Precomputed
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Entry
public import VerifiedGarbage.Spec.RsaPkcs1Sig.Precomputed
public import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSASSA-PKCS1-v1_5 verification with a precomputed public key on ARMv7: where everything is

`EP`: what two runs share (the frame's base `B`, the pointers, the lengths,
the hash function's number, `e` and the words of `pre`), and its layout
(`EP.lay`, `Proof/RsaPkcs1Sig/Arm/Lay.lean`). `In P σ`: the state `σ` the
body starts from; `S P σ s`: a state of the body. The shared contract, with
the stack of the frames and of the call, gives `In (ep s) (entered frameBytes s)`
(`in_of_pre`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.Arm.Vf

open VG VG.Arm VG.Impl.RsaPkcs1Sig.Arm.Precomputed VG.Proof.RsaPkcs1Sig.Arm

/-- What two runs share. -/
structure EP where
  B : BitVec 32
  n : BitVec 32
  e : BitVec 32
  hash : BitVec 32
  dig : BitVec 32
  sig : BitVec 32
  scr : BitVec 32
  pre : BitVec 32
  K : Nat
  el : Nat
  dl : Nat
  gl : Nat
  sl : Nat
  rl : Nat
  eB : List Byte
  pw : List (BitVec 64)

namespace EP

variable (P : EP)

abbrev N : Region := ⟨State.addr P.n, P.K⟩
abbrev E : Region := ⟨State.addr P.e, P.el⟩
abbrev DIG : Region := ⟨State.addr P.dig, P.dl⟩
abbrev SIG : Region := ⟨State.addr P.sig, P.gl⟩
abbrev SCR : Region := ⟨State.addr P.scr, P.sl * 8⟩
abbrev PRE : Region := ⟨State.addr P.pre, P.rl * 8⟩

/-- The arguments, in order. -/
abbrev argv : List (BitVec 32) :=
  [P.n, BitVec.ofNat 32 P.K, P.e, BitVec.ofNat 32 P.el, P.hash, P.dig, BitVec.ofNat 32 P.dl, P.sig,
    BitVec.ofNat 32 P.gl, P.scr, BitVec.ofNat 32 P.sl, P.pre, BitVec.ofNat 32 P.rl]

abbrev lay : Lay where
  B := P.B
  F := frameBytes
  A := 36
  argv := P.argv
  ro := [P.N, P.E, P.DIG, P.SIG, P.PRE]
  rw := [P.SCR]

end EP

/-- The state the body starts from. -/
structure In (P : EP) (σ : State) : Prop where
  ok : P.lay.Ok σ
  kv : Spec.Rsa.lenValid P.K
  el1 : 1 ≤ P.el
  elK : P.el ≤ P.K
  slK : Spec.Rsa.publicScratchWords P.K ≤ P.sl
  rlK : P.rl = Spec.Rsa.precomputedWords P.K
  eB : Spec.Rsa.bytesAt σ.mem (State.addr P.e) P.el = P.eB
  pw : Spec.Rsa.wordsAt σ.mem (State.addr P.pre) P.rl = P.pw
  dl32 : P.dl < 2 ^ 32
  gl32 : P.gl < 2 ^ 32

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
abbrev stackBytes : Nat := 56 + frameBytes + 56

/-- The shared contract, with that stack. -/
abbrev spec : Contract isa := Spec.RsaPkcs1Sig.verifyPrecomputedContract abi stackBytes

/-- The public parameters of an entry state. -/
def ep (s : State) : EP where
  B := s.sp - BitVec.ofNat 32 56 - BitVec.ofNat 32 frameBytes
  n := s.gpr .r0
  e := s.gpr .r2
  hash := stackArg s 0
  dig := stackArg s 1
  sig := stackArg s 3
  scr := stackArg s 5
  pre := stackArg s 7
  K := (s.gpr .r1).toNat
  el := (s.gpr .r3).toNat
  dl := (stackArg s 2).toNat
  gl := (stackArg s 4).toNat
  sl := (stackArg s 6).toNat
  rl := (stackArg s 8).toNat
  eB := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat
  pw := Spec.Rsa.wordsAt s.mem (State.addr (stackArg s 7)) (stackArg s 8).toNat

theorem ep_lay (s : State) :
    (ep s).lay = layOf frameBytes 36 (ep s).argv [(ep s).N, (ep s).E, (ep s).DIG, (ep s).SIG, (ep s).PRE]
      [(ep s).SCR] s := rfl

theorem in_of_pre {s : State} (h : spec.pre s) : In (ep s) (entered frameBytes s) := by
  sig_pre [Spec.RsaPkcs1Sig.verifyPrecomputedContract, Spec.RsaPkcs1Sig.verifyPrecomputedSig, abi,
    argRegs, reduceClassify, Loc.val] at h
  obtain ⟨hsp, hsa, hrd, hwr, nS, eS, dS, gS, sR, sA, kN, kE, kD, kG, kS, kR, kA, fN, fE, fD, fG, fS, fR,
    kv, el1, elK, slK, rlK⟩ := h
  have h2192 : 2192 ≤ s.sp.toNat := hsp
  have hpush : Frame [FrameStack.belowA s.sp 56] s.mem (entered frameBytes s).mem :=
    FrameStack.pushed_frameA (rs := Impl.RsaPkcs1Sig.Arm.pushRegs) (by show 56 ≤ s.sp.toNat; omega_arith)
  have below : Region.Sub (FrameStack.belowA s.sp 56)
      ⟨State.addr s.sp - BitVec.ofNat 64 2192, 2192⟩ := by
    show Region.Sub ⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩ _
    rw [FrameStack.addr_sub' (by omega_arith)]
    exact Offset.sub_below _ (by omega_arith) (by omega_arith)
  refine
    { ok := ?_
      kv := kv, el1 := el1, elK := elK, slK := slK, rlK := rlK
      eB := bytesAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kE.sub_left below).symm)
        (by show (s.gpr .r3).toNat ≤ 2 ^ 64; omega_arith)
      pw := wordsAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kR.sub_left below).symm)
        (by show (stackArg s 8).toNat * 8 ≤ 2 ^ 64; omega_arith)
      dl32 := (stackArg s 2).isLt
      gl32 := (stackArg s 4).isLt }
  rw [ep_lay]
  refine ok_entered (by decide) (by decide) rfl hsp hsa hrd hwr ?_ ?_ ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [kN, kE, kD, kG, kR, kS, kA]
  · intro w hw r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hw
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [nS.symm, eS.symm, dS.symm, gS.symm, sR, sA]
  · exact List.pairwise_singleton _ _
  · intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [fN, fE, fD, fG, fR, fS]
  · intro j hj
    rcases (by omega_arith : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    · rfl
    · simp [regArg, ep]
    · rfl
    · simp [regArg, ep]
  · intro i hi
    rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [ep]

end VG.Proof.RsaPkcs1Sig.Arm.Vf
