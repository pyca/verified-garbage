module

-- separate module: the `sig_pre` unfolding of the shared contract builds in parallel with `RndCount`, `RndTaint` and `RndEnc`, and is not rebuilt with the scan's proofs

public import VerifiedGarbage.Impl.RsaPkcs1Enc.X86.Random
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Entry
public import VerifiedGarbage.Spec.RsaPkcs1Enc.Random
public import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on x86: where everything is

`RP`, what two runs share (the frame's base `B`, the pointers, the lengths,
`n`'s and `e`'s bytes, `pre`'s words and which octets of the tape are zero,
`mask`), and its layout (`RP.lay`), with the bytes below the frame that
`vg_rsa_pkcs1_encrypt_precomputed` and its return address use. `In P σ`:
the state `σ` the body starts from; `S P σ s`: a state of the body. The
shared contract gives `In (ep s) (entered frameBytes s)` (`in_of_pre`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Rnd

open VG VG.Impl.RsaPkcs1Enc.X86.Random VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes

/-- What two runs share. -/
structure RP where
  B : BitVec 32
  out : BitVec 32
  tape : BitVec 32
  n : BitVec 32
  e : BitVec 32
  msg : BitVec 32
  rnd : BitVec 32
  scr : BitVec 32
  pre : BitVec 32
  K : Nat
  el : Nat
  ml : Nat
  len : Nat
  sl : Nat
  rl : Nat
  nB : List Byte
  eB : List Byte
  pw : List (BitVec 64)
  mask : List Nat

/-- The room below the frame: the callee's stack and its return address. -/
abbrev roomC : Nat := 1192

namespace RP

variable (P : RP)

abbrev pl : Nat := P.K - P.ml - 3

abbrev OUT : Region := ⟨P.out.setWidth 64, P.K⟩
abbrev TAPE : Region := ⟨P.tape.setWidth 64, 16⟩
abbrev N : Region := ⟨P.n.setWidth 64, P.K⟩
abbrev E : Region := ⟨P.e.setWidth 64, P.el⟩
abbrev MSG : Region := ⟨P.msg.setWidth 64, P.ml⟩
abbrev RAND : Region := ⟨P.rnd.setWidth 64, P.len⟩
abbrev SCR : Region := ⟨P.scr.setWidth 64, P.sl * 8⟩
abbrev PRE : Region := ⟨P.pre.setWidth 64, P.rl * 8⟩

/-- The arguments, in order. -/
abbrev argv : List (BitVec 32) :=
  [P.out, BitVec.ofNat 32 P.K, P.tape, P.n, BitVec.ofNat 32 P.K, P.e, BitVec.ofNat 32 P.el, P.msg,
    BitVec.ofNat 32 P.ml, P.rnd, BitVec.ofNat 32 P.len, P.scr, BitVec.ofNat 32 P.sl, P.pre,
    BitVec.ofNat 32 P.rl]

abbrev ro : List Region := [P.N, P.E, P.MSG, P.RAND, P.PRE]
abbrev rw : List Region := [P.OUT, P.TAPE, P.SCR]

abbrev lay : Lay where
  B := P.B
  F := frameBytes
  argv := P.argv
  ro := P.ro
  rw := P.rw
  C := roomC

/-- `PS`'s place. -/
abbrev BUF : Region := ⟨P.lay.fr oBuf, P.pl⟩

end RP

/-- The tape's octets. -/
abbrev rB (P : RP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (P.rnd.setWidth 64) P.len

/-- The state the body starts from. -/
structure In (P : RP) (σ : State) : Prop where
  ok : P.lay.Ok σ
  kv : Spec.Rsa.lenValid P.K
  el1 : 1 ≤ P.el
  elK : P.el ≤ P.K
  mlK : P.ml + 11 ≤ P.K
  lenC : P.len ≤ Spec.RsaPkcs1Enc.padEntropy P.pl
  slK : Spec.Rsa.publicScratchWords P.K ≤ P.sl
  sl32 : P.sl < 2 ^ 32
  rlK : P.rl = Spec.Rsa.precomputedWords P.K
  nB : Spec.Rsa.bytesAt σ.mem (P.n.setWidth 64) P.K = P.nB
  eB : Spec.Rsa.bytesAt σ.mem (P.e.setWidth 64) P.el = P.eB
  pw : Spec.Rsa.wordsAt σ.mem (P.pre.setWidth 64) P.rl = P.pw
  mask : (Spec.RsaPkcs1Enc.padSearch P.pl (rB P σ)).trace = P.mask

/-- A state of the body. -/
abbrev S (P : RP) (σ s : State) : Prop := In P σ ∧ P.lay.St σ s

namespace In

variable {P : RP} {σ : State} (h : In P σ)
include h

theorem k64 : 64 ≤ P.K := h.kv.1
theorem k1024 : P.K ≤ 1024 := h.kv.2
theorem pl8 : 8 ≤ P.pl := by have := h.mlK; simp only [RP.pl]; omega
theorem pl1021 : P.pl ≤ 1021 := by have := h.kv.2; simp only [RP.pl]; omega

end In

/-! ## The entry -/

/-- The stack the function uses: the push, the inner frame and the call's. -/
abbrev stackBytes : Nat := 16 + frameBytes + roomC

/-- The shared contract, with that stack. -/
abbrev spec : Contract isa := Spec.RsaPkcs1Enc.encryptRandomContract abi stackBytes

/-- The public parameters of an entry state. -/
def ep (s : State) : RP where
  B := s.gpr .esp - BitVec.ofNat 32 16 - BitVec.ofNat 32 frameBytes
  out := arg s 0
  tape := arg s 2
  n := arg s 3
  e := arg s 5
  msg := arg s 7
  rnd := arg s 9
  scr := arg s 11
  pre := arg s 13
  K := (arg s 4).toNat
  el := (arg s 6).toNat
  ml := (arg s 8).toNat
  len := (arg s 10).toNat
  sl := (arg s 12).toNat
  rl := (arg s 14).toNat
  nB := Spec.Rsa.bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat
  eB := Spec.Rsa.bytesAt s.mem ((arg s 5).setWidth 64) (arg s 6).toNat
  pw := Spec.Rsa.wordsAt s.mem ((arg s 13).setWidth 64) (arg s 14).toNat
  mask := (Spec.RsaPkcs1Enc.padSearch ((arg s 4).toNat - (arg s 8).toNat - 3)
    (Spec.Rsa.bytesAt s.mem ((arg s 9).setWidth 64) (arg s 10).toNat)).trace

theorem ep_lay (s : State) :
    (ep s).lay = layOf frameBytes (ep s).argv (ep s).ro (ep s).rw s roomC := rfl

theorem in_of_pre {s : State} (h : spec.pre s) : In (ep s) (entered frameBytes s) := by
  sig_pre [Spec.RsaPkcs1Enc.encryptRandomContract, Spec.RsaPkcs1Enc.encryptRandomSig, abi, argSlots,
    argVal, argBytes, stackBelow] at h
  obtain ⟨hsp, hsa, hrd, hwr, oT, oN, oE, oM, oR, oS, oQ, oA, tN, tE, tM, tR, tS, tQ, tA,
    nS, nA, eS, eA, mS, mA, rS, rA, sQ, sA, qA,
    xO, xT, xN, xE, xM, xR, xS, xQ, xA, kO, kT, kN, kE, kM, kR, kS, kQ, kA,
    fO, fT, fN, fE, fM, fR, fS, fQ,
    kv, olk, el1, elK, mlK, lenC, slK, rlK⟩ := h
  simp only [stackBytes, frameBytes, roomC, Nat.reduceAdd] at hsp kO kT kN kE kM kR kS kQ kA
  have a1 : arg s 1 = arg s 4 := BitVec.eq_of_toNat_eq olk
  rw [olk] at hwr oT oN oE oM oR oS oQ oA xO kO fO
  have h16 : 4 * Impl.RsaPkcs1Sig.X86.savedRegs.length ≤ (s.gpr .esp).toNat := by
    simp only [Impl.RsaPkcs1Sig.X86.savedRegs, List.length_cons, List.length_nil]; omega
  have hpush : Frame [below (s.gpr .esp) (4 * Impl.RsaPkcs1Sig.X86.savedRegs.length)] s.mem
      (entered frameBytes s).mem :=
    pushed_frame (by decide) h16
  have below16 : Region.Sub (below (s.gpr .esp) (4 * Impl.RsaPkcs1Sig.X86.savedRegs.length))
      ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 2296, 2296⟩ := by
    simp only [below, Impl.RsaPkcs1Sig.X86.savedRegs, List.length_cons, List.length_nil]
    rw [Taint.sub_setWidth (by omega)]
    exact Offset.sub_below _ (by omega) (by omega)
  have sl32 : (arg s 12).toNat < 2 ^ 32 := (arg s 12).isLt
  refine
    { ok := ?_
      kv := kv, el1 := el1, elK := elK, mlK := mlK, lenC := lenC, slK := slK, sl32 := sl32, rlK := rlK
      nB := Proof.RsaPkcs1Sig.bytesAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kN.sub_left below16).symm)
        (by show (arg s 4).toNat ≤ 2 ^ 64; omega)
      eB := Proof.RsaPkcs1Sig.bytesAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kE.sub_left below16).symm)
        (by show (arg s 6).toNat ≤ 2 ^ 64; omega)
      pw := Proof.RsaPkcs1Sig.wordsAt_frame' hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kQ.sub_left below16).symm)
        (by show (arg s 14).toNat * 8 ≤ 2 ^ 64; have := (arg s 14).isLt; omega)
      mask := by
        show (Spec.RsaPkcs1Enc.padSearch _ (Spec.Rsa.bytesAt (entered frameBytes s).mem _ _)).trace = _
        rw [Proof.RsaPkcs1Sig.bytesAt_frame hpush (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact (kR.sub_left below16).symm)
          (by show (arg s 10).toNat ≤ 2 ^ 64; omega)]
        rfl }
  rw [ep_lay]
  refine ok_entered (S := 2296) rfl (by decide) hsp (by simp) (by simp; omega) hrd
    (by rw [hwr]; rfl) ?_ ?_ ?_ ?_ ?_ ?_
  · intro r hr
    simp only [RP.ro, RP.rw, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [kN, kE, kM, kR, kQ, kO, kT, kS]
  · intro r hr
    simp only [RP.rw, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [xO, xT, xS]
  · intro w hw r hr
    simp only [RP.rw, List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [RP.ro, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hw with rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [oN, oE, oM, oR, oQ, oA, tN, tE, tM, tR, tQ, tA, nS.symm, eS.symm, mS.symm, rS.symm, sQ, sA]
  · simp only [RP.rw, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨⟨oT, oS⟩, tS, fun _ h => h.elim⟩
  · intro r hr
    simp only [RP.ro, RP.rw, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [ep, BitVec.toNat_setWidth]
    all_goals first
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 3).isLt; omega)]; omega)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 5).isLt; omega)]; omega)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 7).isLt; omega)]; omega)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 9).isLt; omega)]; omega)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 13).isLt; omega)]; omega)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 0).isLt; omega)]; omega)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 2).isLt; omega)]; omega)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 11).isLt; omega)]; omega)
  · intro j hj
    have : j < 15 := hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨
        j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [ep, a1]

end VG.Proof.RsaPkcs1Enc.X86.Rnd
