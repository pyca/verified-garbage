module

public import VerifiedGarbage.Impl.RsaPkcs1Enc.X86.Precomputed
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Entry
public import VerifiedGarbage.Spec.RsaPkcs1Enc.Precomputed
public import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSAES-PKCS1-v1_5 encryption with a precomputed public key on x86: where everything is

As on ARMv7 (`Proof/RsaPkcs1Enc/Arm/PcBase.lean`): `EP`, what two runs
share (the frame's base `B`, the pointers, the lengths, `e`'s bytes and
`pre`'s words), and its layout (`EP.lay`), with the 100 bytes below the frame
that `vg_rsa_public_precomputed_checked` and its return address use.
`In P σ`: the state `σ` the body starts from; `S P σ s`: a state of the
body. The shared contract, with the stack of the frames and of the call,
gives `In (ep s) (entered frameBytes s)` (`in_of_pre`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Pc

open VG VG.Impl.RsaPkcs1Enc.X86.Precomputed VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes

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

abbrev OUT : Region := ⟨P.out.setWidth 64, P.K⟩
abbrev N : Region := ⟨P.n.setWidth 64, P.K⟩
abbrev E : Region := ⟨P.e.setWidth 64, P.el⟩
abbrev MSG : Region := ⟨P.msg.setWidth 64, P.ml⟩
abbrev PS : Region := ⟨P.ps.setWidth 64, P.pl⟩
abbrev SCR : Region := ⟨P.scr.setWidth 64, P.sl * 8⟩
abbrev PRE : Region := ⟨P.pre.setWidth 64, P.rl * 8⟩

/-- The arguments, in order. -/
abbrev argv : List (BitVec 32) :=
  [P.out, BitVec.ofNat 32 P.K, P.n, BitVec.ofNat 32 P.K, P.e, BitVec.ofNat 32 P.el, P.msg,
    BitVec.ofNat 32 P.ml, P.ps, BitVec.ofNat 32 P.pl, P.scr, BitVec.ofNat 32 P.sl, P.pre,
    BitVec.ofNat 32 P.rl]

abbrev ro : List Region := [P.N, P.E, P.MSG, P.PS, P.PRE]
abbrev rw : List Region := [P.OUT, P.SCR]

abbrev lay : Lay where
  B := P.B
  F := frameBytes
  argv := P.argv
  ro := P.ro
  rw := P.rw
  C := 100

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
  slK : Spec.Rsa.publicScratchWords P.K ≤ P.sl
  sl32 : P.sl < 2 ^ 32
  rlK : P.rl = Spec.Rsa.precomputedWords P.K
  eB : Spec.Rsa.bytesAt σ.mem (P.e.setWidth 64) P.el = P.eB
  pw : Spec.Rsa.wordsAt σ.mem (P.pre.setWidth 64) P.rl = P.pw

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
abbrev stackBytes : Nat := 16 + frameBytes + 100

/-- The shared contract, with that stack. -/
abbrev spec : Contract isa := Spec.RsaPkcs1Enc.encryptPrecomputedContract abi stackBytes

/-- The public parameters of an entry state. -/
def ep (s : State) : EP where
  B := s.gpr .esp - BitVec.ofNat 32 16 - BitVec.ofNat 32 frameBytes
  out := arg s 0
  n := arg s 2
  e := arg s 4
  msg := arg s 6
  ps := arg s 8
  scr := arg s 10
  pre := arg s 12
  K := (arg s 3).toNat
  el := (arg s 5).toNat
  ml := (arg s 7).toNat
  pl := (arg s 9).toNat
  sl := (arg s 11).toNat
  rl := (arg s 13).toNat
  eB := Spec.Rsa.bytesAt s.mem ((arg s 4).setWidth 64) (arg s 5).toNat
  pw := Spec.Rsa.wordsAt s.mem ((arg s 12).setWidth 64) (arg s 13).toNat

theorem ep_lay (s : State) :
    (ep s).lay = layOf frameBytes (ep s).argv (ep s).ro (ep s).rw s 100 := rfl

theorem in_of_pre {s : State} (h : spec.pre s) : In (ep s) (entered frameBytes s) := by
  sig_pre [Spec.RsaPkcs1Enc.encryptPrecomputedContract, Spec.RsaPkcs1Enc.encryptPrecomputedSig, abi, argSlots,
    argVal, argBytes, stackBelow] at h
  obtain ⟨hsp, hsa, hrd, hwr, oN, oE, oM, oP, oS, oR, oA, nS, nA, eS, eA, mS, mA, pS, pA, sR, sA, rA,
    rO, rN, rE, rM, rP, rS, rR, rAr, kO, kN, kE, kM, kP, kS, kR, kA, fO, fN, fE, fM, fP, fS, fR,
    kv, olk, el1, elK, mlK, plK, slK, rlK⟩ := h
  simp only [stackBytes, frameBytes, Nat.reduceAdd] at hsp kO kN kE kM kP kS kR kA
  have a1 : arg s 1 = arg s 3 := BitVec.eq_of_toNat_eq olk
  rw [olk] at hwr oN oE oM oP oS oR oA rO kO fO
  have h16 : 4 * Impl.RsaPkcs1Sig.X86.savedRegs.length ≤ (s.gpr .esp).toNat := by
    simp only [Impl.RsaPkcs1Sig.X86.savedRegs, List.length_cons, List.length_nil]; omega_arith
  have hpush : Frame [below (s.gpr .esp) (4 * Impl.RsaPkcs1Sig.X86.savedRegs.length)] s.mem
      (entered frameBytes s).mem :=
    pushed_frame (by decide) h16
  have below16 : Region.Sub (below (s.gpr .esp) (4 * Impl.RsaPkcs1Sig.X86.savedRegs.length))
      ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 1188, 1188⟩ := by
    simp only [below, Impl.RsaPkcs1Sig.X86.savedRegs, List.length_cons, List.length_nil]
    rw [Taint.sub_setWidth (by omega_arith)]
    exact Offset.sub_below _ (by omega_arith) (by omega_arith)
  have sl32 : (arg s 11).toNat < 2 ^ 32 := (arg s 11).isLt
  refine
    { ok := ?_
      kv := kv, el1 := el1, elK := elK, mlK := mlK, plK := plK, slK := slK, sl32 := sl32, rlK := rlK
      eB := Proof.RsaPkcs1Sig.bytesAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kE.sub_left below16).symm)
        (by show (arg s 5).toNat ≤ 2 ^ 64; omega_arith)
      pw := Proof.RsaPkcs1Sig.wordsAt_frame' hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kR.sub_left below16).symm)
        (by show (arg s 13).toNat * 8 ≤ 2 ^ 64; have := (arg s 13).isLt; omega_arith) }
  rw [ep_lay]
  refine ok_entered (S := 1188) rfl (by decide) hsp (by simp) (by simp; omega_arith) hrd
    (by rw [hwr]; rfl) ?_ ?_ ?_ ?_ ?_ ?_
  · intro r hr
    simp only [EP.ro, EP.rw, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [kN, kE, kM, kP, kR, kO, kS]
  · intro r hr
    simp only [EP.rw, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [rO, rS]
  · intro w hw r hr
    simp only [EP.rw, List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [EP.ro, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hw with rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [oN, oE, oM, oP, oR, oA, nS.symm, eS.symm, mS.symm, pS.symm, sR, sA]
  · exact List.pairwise_pair.mpr oS
  · intro r hr
    simp only [EP.ro, EP.rw, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [ep, BitVec.toNat_setWidth]
    all_goals first
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 2).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 4).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 6).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 8).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 12).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 0).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 10).isLt; omega_arith)]; omega_arith)
  · intro j hj
    have : j < 14 := hj
    rcases (by omega_arith : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨
        j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [ep, a1]

end VG.Proof.RsaPkcs1Enc.X86.Pc
