module

import VerifiedGarbage.Impl.RsaOaep.X86
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Entry
public import VerifiedGarbage.Spec.RsaOaep.Precomputed
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.RsaPss.X86.Base
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.RsaPss.X86

/-!
# RSAES-OAEP encryption with a precomputed public key on x86: where everything is

As on ARMv7 (`Proof/RsaOaep/Arm/EncBase.lean`): `EP`, what two runs share
(the frame's base `B`, the pointers, the lengths, and the public key's bytes
and precomputed words), and its layout (`EP.lay`, with the seed's `D`
bytes), with the 100 bytes below the frame that the call of
`vg_rsa_public_precomputed_checked` (100) and the frames of the streaming
functions (48) use. `In D P σ`: the state `σ` the body starts from
(`in_of_pre`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86.Enc

open VG VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes

/-- What two runs share. -/
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

namespace EP

variable (D : Nat) (P : EP)

abbrev OUT : Region := ⟨P.out.setWidth 64, P.K⟩
abbrev N : Region := ⟨P.n.setWidth 64, P.K⟩
abbrev E : Region := ⟨P.e.setWidth 64, P.el⟩
abbrev LAB : Region := ⟨P.lab.setWidth 64, P.ll⟩
abbrev MSG : Region := ⟨P.msg.setWidth 64, P.ml⟩
abbrev SEED : Region := ⟨P.seed.setWidth 64, D⟩
abbrev SCR : Region := ⟨P.scr.setWidth 64, P.scl * 8⟩
abbrev PRE : Region := ⟨P.pre.setWidth 64, P.rl * 8⟩

/-- The arguments, in order. -/
abbrev argv : List (BitVec 32) :=
  [P.out, BitVec.ofNat 32 P.K, P.n, BitVec.ofNat 32 P.K, P.e, BitVec.ofNat 32 P.el, P.lab, BitVec.ofNat 32 P.ll,
    P.msg, BitVec.ofNat 32 P.ml, P.seed, P.scr, BitVec.ofNat 32 P.scl, P.pre, BitVec.ofNat 32 P.rl]

abbrev ro : List Region := [P.N, P.E, P.LAB, P.MSG, P.SEED D, P.PRE]
abbrev rw : List Region := [P.OUT, P.SCR]

abbrev lay : Lay where
  B := P.B
  F := frameBytes
  argv := P.argv
  ro := P.ro D
  rw := P.rw
  C := 100

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
  nB : Spec.Rsa.bytesAt σ.mem (P.n.setWidth 64) P.K = P.nB
  eB : Spec.Rsa.bytesAt σ.mem (P.e.setWidth 64) P.el = P.eB
  pw : Spec.Rsa.wordsAt σ.mem (P.pre.setWidth 64) P.rl = P.pw

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
  simp only [BitVec.toNat_setWidth] at hf
  rw [Nat.mod_eq_of_lt (by have := P.scr.isLt; omega)] at hf
  exact ⟨rfl, by unfold oRsa; omega, ⟨P.scl * 8, by unfold oRsa; omega, by simp⟩, ⟨σ, h.ok⟩,
    by show 48 ≤ 100; decide⟩

end In

/-! ## The entry -/

/-- The stack the function uses: the push, the inner frame and the calls'. -/
abbrev stackBytes : Nat := 16 + frameBytes + 100

/-- The shared contract, with that stack. -/
abbrev spec (H G : Spec.Mgf1.Hash) : Contract isa := Spec.RsaOaep.encryptPrecomputedContract H G abi stackBytes

/-- The public parameters of an entry state. -/
def ep (s : State) : EP where
  B := s.gpr .esp - BitVec.ofNat 32 16 - BitVec.ofNat 32 frameBytes
  out := arg s 0
  n := arg s 2
  e := arg s 4
  lab := arg s 6
  msg := arg s 8
  seed := arg s 10
  scr := arg s 11
  pre := arg s 13
  K := (arg s 3).toNat
  el := (arg s 5).toNat
  ll := (arg s 7).toNat
  ml := (arg s 9).toNat
  scl := (arg s 12).toNat
  rl := (arg s 14).toNat
  nB := Spec.Rsa.bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat
  eB := Spec.Rsa.bytesAt s.mem ((arg s 4).setWidth 64) (arg s 5).toNat
  pw := Spec.Rsa.wordsAt s.mem ((arg s 13).setWidth 64) (arg s 14).toNat

theorem ep_lay (D : Nat) (s : State) :
    (ep s).lay D = layOf frameBytes (ep s).argv ((ep s).ro D) (ep s).rw s 100 := rfl

theorem in_of_pre {H G : Spec.Mgf1.Hash} {s : State} (h : (spec H G).pre s) :
    In H.len (ep s) (entered frameBytes s) := by
  sig_pre [Spec.RsaOaep.encryptPrecomputedContract, Spec.RsaOaep.encryptPrecomputedSig, abi, argSlots, argVal,
    argBytes, stackBelow] at h
  obtain ⟨hsp, hsa, hrd, hwr, oN, oE, oL, oM, oS, oC, oP, oA, nC, nA, eC, eA, lC, lA, mC, mA, sC, sA, cP, cA, pA,
    rO, rN, rE, rL, rM, rS, rC, rP, rA, kO, kN, kE, kL, kM, kS, kC, kP, kA, fO, fN, fE, fL, fM, fS, fC, fP,
    kv, olk, el1, elK, scrK, rlK⟩ := h
  simp only [stackBytes, frameBytes, Nat.reduceAdd] at hsp kO kN kE kL kM kS kC kP kA
  have a1 : arg s 1 = BitVec.ofNat 32 (arg s 3).toNat := by
    apply BitVec.eq_of_toNat_eq; rw [olk, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (arg s 3).isLt]
  rw [olk] at hwr oN oE oL oM oS oC oP oA rO kO fO
  have h16 : 4 * Impl.RsaPkcs1Sig.X86.savedRegs.length ≤ (s.gpr .esp).toNat := by
    simp only [Impl.RsaPkcs1Sig.X86.savedRegs, List.length_cons, List.length_nil]; omega
  have hpush : Frame [below (s.gpr .esp) (4 * Impl.RsaPkcs1Sig.X86.savedRegs.length)] s.mem
      (entered frameBytes s).mem :=
    pushed_frame (by decide) h16
  have below16 : Region.Sub (below (s.gpr .esp) (4 * Impl.RsaPkcs1Sig.X86.savedRegs.length))
      ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 260, 260⟩ := by
    simp only [below, Impl.RsaPkcs1Sig.X86.savedRegs, List.length_cons, List.length_nil]
    rw [Taint.sub_setWidth (by omega)]
    exact Offset.sub_below _ (by omega) (by omega)
  refine
    { ok := ?_
      kv := kv, el1 := el1, elK := elK, scrK := scrK, rlK := rlK
      ll32 := (arg s 7).isLt
      ml32 := (arg s 9).isLt
      scl32 := (arg s 12).isLt
      nB := Proof.RsaPkcs1Sig.bytesAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kN.sub_left below16).symm)
        (by show (arg s 3).toNat ≤ 2 ^ 64; omega)
      eB := Proof.RsaPkcs1Sig.bytesAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kE.sub_left below16).symm)
        (by show (arg s 5).toNat ≤ 2 ^ 64; omega)
      pw := Proof.RsaPkcs1Sig.wordsAt_frame' hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kP.sub_left below16).symm)
        (by show (arg s 14).toNat * 8 ≤ 2 ^ 64; have := (arg s 14).isLt; omega) }
  rw [ep_lay]
  refine ok_entered (S := 260) rfl (by decide) hsp (by simp) (by simp; omega) hrd
    (by rw [hwr]; rfl) ?_ ?_ ?_ ?_ ?_ ?_
  · intro r hr
    simp only [EP.ro, EP.rw, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [kN, kE, kL, kM, kS, kP, kO, kC]
  · intro r hr
    simp only [EP.rw, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [rO, rC]
  · intro w hw r hr
    simp only [EP.rw, List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [EP.ro, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hw with rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [oN, oE, oL, oM, oS, oP, oA, nC.symm, eC.symm, lC.symm, mC.symm, sC.symm, cP, cA]
  · exact List.pairwise_pair.mpr oC
  · intro r hr
    simp only [EP.ro, EP.rw, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [ep, BitVec.toNat_setWidth]
    all_goals first
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 0).isLt; omega)]; omega)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 2).isLt; omega)]; omega)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 4).isLt; omega)]; omega)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 6).isLt; omega)]; omega)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 8).isLt; omega)]; omega)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 10).isLt; omega)]; omega)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 11).isLt; omega)]; omega)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 13).isLt; omega)]; omega)
  · intro j hj
    have : j < 15 := hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨
        j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [ep, a1]

end VG.Proof.RsaOaep.X86.Enc
