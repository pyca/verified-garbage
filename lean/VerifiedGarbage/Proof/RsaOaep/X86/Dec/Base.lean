module

import VerifiedGarbage.Impl.RsaOaep.X86
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Entry
public import VerifiedGarbage.Spec.RsaOaep.Contract
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.RsaPss.X86.Base
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.RsaPss.X86

/-!
# RSAES-OAEP decryption on x86: where everything is

As on ARMv7 (`Proof/RsaOaep/Arm/DecBase.lean`): `EP`, what two runs share
(the frame's base `B`, the pointers, the lengths and the public key's bytes
`nB` and `eB`), and its layout (`EP.lay`), with the 3448 bytes below the
frame that the call of `vg_rsa_private_checked` uses (the streaming
functions' frames use less). `In P σ`: the state `σ` the body starts from
(`in_of_pre`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86.Dec

open VG VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes

/-- What two runs share. -/
structure EP where
  B : BitVec 32
  out : BitVec 32
  ml : BitVec 32
  n : BitVec 32
  e : BitVec 32
  p : BitVec 32
  q : BitVec 32
  dp : BitVec 32
  dq : BitVec 32
  qinv : BitVec 32
  lab : BitVec 32
  ct : BitVec 32
  scr : BitVec 32
  K : Nat
  el : Nat
  pl : Nat
  ql : Nat
  ll : Nat
  scl : Nat
  nB : List Byte
  eB : List Byte

namespace EP

variable (P : EP)

abbrev OUT : Region := ⟨P.out.setWidth 64, P.K⟩
abbrev ML : Region := ⟨P.ml.setWidth 64, 8⟩
abbrev N : Region := ⟨P.n.setWidth 64, P.K⟩
abbrev E : Region := ⟨P.e.setWidth 64, P.el⟩
abbrev PP : Region := ⟨P.p.setWidth 64, P.pl⟩
abbrev QQ : Region := ⟨P.q.setWidth 64, P.ql⟩
abbrev DP : Region := ⟨P.dp.setWidth 64, P.pl⟩
abbrev DQ : Region := ⟨P.dq.setWidth 64, P.ql⟩
abbrev QI : Region := ⟨P.qinv.setWidth 64, P.pl⟩
abbrev LAB : Region := ⟨P.lab.setWidth 64, P.ll⟩
abbrev CT : Region := ⟨P.ct.setWidth 64, P.K⟩
abbrev SCR : Region := ⟨P.scr.setWidth 64, P.scl * 8⟩

/-- The arguments, in order. -/
abbrev argv : List (BitVec 32) :=
  [P.out, BitVec.ofNat 32 P.K, P.ml, P.n, BitVec.ofNat 32 P.K, P.e, BitVec.ofNat 32 P.el, P.p, BitVec.ofNat 32 P.pl,
    P.q, BitVec.ofNat 32 P.ql, P.dp, BitVec.ofNat 32 P.pl, P.dq, BitVec.ofNat 32 P.ql, P.qinv,
    BitVec.ofNat 32 P.pl, P.lab, BitVec.ofNat 32 P.ll, P.ct, BitVec.ofNat 32 P.K, P.scr, BitVec.ofNat 32 P.scl]

abbrev ro : List Region := [P.N, P.E, P.PP, P.QQ, P.DP, P.DQ, P.QI, P.LAB, P.CT]
abbrev rw : List Region := [P.OUT, P.ML, P.SCR]

abbrev lay : Lay where
  B := P.B
  F := frameBytes
  argv := P.argv
  ro := P.ro
  rw := P.rw
  C := 3448

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
  slK : Spec.RsaPss.scratchWords P.K ≤ P.scl
  ll32 : P.ll < 2 ^ 32
  scl32 : P.scl < 2 ^ 32
  nB : Spec.Rsa.bytesAt σ.mem (P.n.setWidth 64) P.K = P.nB
  eB : Spec.Rsa.bytesAt σ.mem (P.e.setWidth 64) P.el = P.eB

namespace In

variable {P : EP} {σ : State} (h : In P σ)
include h

theorem k64 : 64 ≤ P.K := h.kv.1
theorem k1024 : P.K ≤ 1024 := h.kv.2

/-- Our part of `scratch`. -/
theorem geo : Geo P.lay P.scr := by
  have hs := h.slK
  have hK := h.k1024
  have hf := h.ok.fits (P.SCR) (by simp)
  simp only [BitVec.toNat_setWidth] at hf
  rw [Nat.mod_eq_of_lt (by have := P.scr.isLt; omega_arith)] at hf
  unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at hs
  exact ⟨rfl, by unfold oRsa; omega_arith, ⟨P.scl * 8, by unfold oRsa; omega_arith, by simp⟩, ⟨σ, h.ok⟩,
    by show 48 ≤ 3448; decide⟩

end In

/-! ## The entry -/

/-- The stack the function uses: the push, the inner frame and the call's. -/
abbrev stackBytes : Nat := 16 + frameBytes + 3448

/-- The shared contract, with that stack. -/
abbrev spec (H G : Spec.Mgf1.Hash) : Contract isa := Spec.RsaOaep.decryptContract H G abi stackBytes

/-- The public parameters of an entry state. -/
def ep (s : State) : EP where
  B := s.gpr .esp - BitVec.ofNat 32 16 - BitVec.ofNat 32 frameBytes
  out := arg s 0
  ml := arg s 2
  n := arg s 3
  e := arg s 5
  p := arg s 7
  q := arg s 9
  dp := arg s 11
  dq := arg s 13
  qinv := arg s 15
  lab := arg s 17
  ct := arg s 19
  scr := arg s 21
  K := (arg s 4).toNat
  el := (arg s 6).toNat
  pl := (arg s 8).toNat
  ql := (arg s 10).toNat
  ll := (arg s 18).toNat
  scl := (arg s 22).toNat
  nB := Spec.Rsa.bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat
  eB := Spec.Rsa.bytesAt s.mem ((arg s 5).setWidth 64) (arg s 6).toNat

theorem ep_lay (s : State) :
    (ep s).lay = layOf frameBytes (ep s).argv (ep s).ro (ep s).rw s 3448 := rfl

theorem in_of_pre {H G : Spec.Mgf1.Hash} {s : State} (h : (spec H G).pre s) :
    In (ep s) (entered frameBytes s) := by
  sig_pre [Spec.RsaOaep.decryptContract, Spec.RsaOaep.decryptSig, abi, argSlots, argVal,
    argBytes, stackBelow] at h
  obtain ⟨hsp, hsa, hrd, hwr, oM, oN, oE, oP, oQ, oDP, oDQ, oQI, oL, oC, oS, oA, mN, mE, mP, mQ, mDP, mDQ, mQI, mL,
    mC, mS, mA, nS, nA, eS, eA, pS, pA, qS, qA, dpS, dpA, dqS, dqA, qiS, qiA, lS, lA, cS, cA, sA,
    rO, rM, rN, rE, rP, rQ, rDP, rDQ, rQI, rL, rC, rS, rA, kO, kM, kN, kE, kP, kQ, kDP, kDQ, kQI, kL, kC, kS, kA,
    fO, fM, fN, fE, fP, fQ, fDP, fDQ, fQI, fL, fC, fS,
    kv, olk, clk, el1, elK, pl1, plK, ql1, qlK, dpl, qil, dql, slK⟩ := h
  simp only [stackBytes, frameBytes, Nat.reduceAdd] at hsp kO kM kN kE kP kQ kDP kDQ kQI kL kC kS kA
  have a1 : arg s 1 = arg s 4 := BitVec.eq_of_toNat_eq olk
  have a20 : arg s 20 = arg s 4 := BitVec.eq_of_toNat_eq clk
  have a12 : arg s 12 = arg s 8 := BitVec.eq_of_toNat_eq dpl
  have a16 : arg s 16 = arg s 8 := BitVec.eq_of_toNat_eq qil
  have a14 : arg s 14 = arg s 10 := BitVec.eq_of_toNat_eq dql
  rw [olk] at hwr oM oN oE oP oQ oDP oDQ oQI oL oC oS oA rO kO fO
  rw [clk] at hrd oC mC cS cA rC kC fC
  rw [dpl] at hrd oDP mDP dpS dpA rDP kDP fDP
  rw [qil] at hrd oQI mQI qiS qiA rQI kQI fQI
  rw [dql] at hrd oDQ mDQ dqS dqA rDQ kDQ fDQ
  have h16 : 4 * Impl.RsaPkcs1Sig.X86.savedRegs.length ≤ (s.gpr .esp).toNat := by
    simp only [Impl.RsaPkcs1Sig.X86.savedRegs, List.length_cons, List.length_nil]; omega_arith
  have hpush : Frame [below (s.gpr .esp) (4 * Impl.RsaPkcs1Sig.X86.savedRegs.length)] s.mem
      (entered frameBytes s).mem :=
    pushed_frame (by decide) h16
  have below16 : Region.Sub (below (s.gpr .esp) (4 * Impl.RsaPkcs1Sig.X86.savedRegs.length))
      ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 3608, 3608⟩ := by
    simp only [below, Impl.RsaPkcs1Sig.X86.savedRegs, List.length_cons, List.length_nil]
    rw [Taint.sub_setWidth (by omega_arith)]
    exact Offset.sub_below _ (by omega_arith) (by omega_arith)
  refine
    { ok := ?_
      kv := kv, el1 := el1, elK := elK, pl1 := pl1, plK := plK, ql1 := ql1, qlK := qlK, slK := slK
      ll32 := (arg s 18).isLt
      scl32 := (arg s 22).isLt
      nB := Proof.RsaPkcs1Sig.bytesAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kN.sub_left below16).symm)
        (by show (arg s 4).toNat ≤ 2 ^ 64; omega_arith)
      eB := Proof.RsaPkcs1Sig.bytesAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kE.sub_left below16).symm)
        (by show (arg s 6).toNat ≤ 2 ^ 64; omega_arith) }
  rw [ep_lay]
  refine ok_entered (S := 3608) rfl (by decide) hsp (by simp) (by simp; omega_arith) hrd
    (by rw [hwr]; rfl) ?_ ?_ ?_ ?_ ?_ ?_
  · intro r hr
    simp only [EP.ro, EP.rw, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [kN, kE, kP, kQ, kDP, kDQ, kQI, kL, kC, kO, kM, kS]
  · intro r hr
    simp only [EP.rw, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [rO, rM, rS]
  · intro w hw r hr
    simp only [EP.rw, List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [EP.ro, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hw with rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [oN, oE, oP, oQ, oDP, oDQ, oQI, oL, oC, oA, mN, mE, mP, mQ, mDP, mDQ, mQI, mL, mC, mA,
      nS.symm, eS.symm, pS.symm, qS.symm, dpS.symm, dqS.symm, qiS.symm, lS.symm, cS.symm, sA]
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨⟨oM, oS⟩, mS, fun _ h => h.elim⟩
  · intro r hr
    simp only [EP.ro, EP.rw, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [ep, BitVec.toNat_setWidth]
    all_goals first
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 0).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 2).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 3).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 5).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 7).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 9).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 11).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 13).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 15).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 17).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 19).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 21).isLt; omega_arith)]; omega_arith)
  · intro j hj
    have : j < 23 := hj
    rcases (by omega_using [this] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨
        j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨
        j = 20 ∨ j = 21 ∨ j = 22) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl <;> simp [ep, a1, a12, a14, a16, a20]

end VG.Proof.RsaOaep.X86.Dec
