module

public import VerifiedGarbage.Impl.RsaPss.X86
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Entry
public import VerifiedGarbage.Spec.RsaPss.Contract
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.RsaPss.X86.Base
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSASSA-PSS signing on x86: where everything is

As on ARMv7 (`Proof/RsaPss/Arm/SgBase.lean`): `EP`, what two runs share
(the frame's base `B`, the pointers, the lengths, and the public key's bytes
`nB` and `eB`), and its layout (`EP.lay`), with the 3392 bytes below the
frame that the hash function's calls and the private-key operation use.
`In D P σ`: the state `σ` the body starts from, for digests of `D` bytes.
The shared contract, with the stack of the frames and of the calls, gives
`In (ep s) (entered frameBytes s)` (`in_of_pre`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Sg

open VG VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes

/-- What two runs share. -/
structure EP where
  B : BitVec 32
  out : BitVec 32
  n : BitVec 32
  e : BitVec 32
  p : BitVec 32
  q : BitVec 32
  dp : BitVec 32
  dq : BitVec 32
  qinv : BitVec 32
  dig : BitVec 32
  salt : BitVec 32
  scr : BitVec 32
  K : Nat
  el : Nat
  pl : Nat
  ql : Nat
  sl : Nat
  scl : Nat
  nB : List Byte
  eB : List Byte

namespace EP

variable (D : Nat) (P : EP)

abbrev OUT : Region := ⟨P.out.setWidth 64, P.K⟩
abbrev N : Region := ⟨P.n.setWidth 64, P.K⟩
abbrev E : Region := ⟨P.e.setWidth 64, P.el⟩
abbrev PP : Region := ⟨P.p.setWidth 64, P.pl⟩
abbrev QQ : Region := ⟨P.q.setWidth 64, P.ql⟩
abbrev DP : Region := ⟨P.dp.setWidth 64, P.pl⟩
abbrev DQ : Region := ⟨P.dq.setWidth 64, P.ql⟩
abbrev QI : Region := ⟨P.qinv.setWidth 64, P.pl⟩
abbrev DIG : Region := ⟨P.dig.setWidth 64, D⟩
abbrev SALT : Region := ⟨P.salt.setWidth 64, P.sl⟩
abbrev SCR : Region := ⟨P.scr.setWidth 64, P.scl * 8⟩

/-- The arguments, in order. -/
abbrev argv : List (BitVec 32) :=
  [P.out, BitVec.ofNat 32 P.K, P.n, BitVec.ofNat 32 P.K, P.e, BitVec.ofNat 32 P.el, P.p, BitVec.ofNat 32 P.pl,
    P.q, BitVec.ofNat 32 P.ql, P.dp, BitVec.ofNat 32 P.pl, P.dq, BitVec.ofNat 32 P.ql, P.qinv,
    BitVec.ofNat 32 P.pl, P.dig, P.salt, BitVec.ofNat 32 P.sl, P.scr, BitVec.ofNat 32 P.scl]

abbrev ro : List Region := [P.N, P.E, P.PP, P.QQ, P.DP, P.DQ, P.QI, P.DIG D, P.SALT]
abbrev rw : List Region := [P.OUT, P.SCR]

abbrev lay : Lay where
  B := P.B
  F := frameBytes
  argv := P.argv
  ro := P.ro D
  rw := P.rw
  C := 3392

end EP

/-- The state the body starts from. -/
structure In (D : Nat) (P : EP) (σ : State) : Prop where
  ok : (P.lay D).Ok σ
  kv : Spec.Rsa.lenValid P.K
  el1 : 1 ≤ P.el
  elK : P.el ≤ P.K
  pl1 : 1 ≤ P.pl
  plK : P.pl < P.K
  ql1 : 1 ≤ P.ql
  qlK : P.ql < P.K
  slK : Spec.RsaPss.scratchWords P.K ≤ P.scl
  sl32 : P.sl < 2 ^ 32
  scl32 : P.scl < 2 ^ 32
  nB : Spec.Rsa.bytesAt σ.mem (P.n.setWidth 64) P.K = P.nB
  eB : Spec.Rsa.bytesAt σ.mem (P.e.setWidth 64) P.el = P.eB

namespace In

variable {D : Nat} {P : EP} {σ : State} (h : In D P σ)
include h

theorem k64 : 64 ≤ P.K := h.kv.1
theorem k1024 : P.K ≤ 1024 := h.kv.2

/-- Our part of `scratch`. -/
theorem geo : Geo (P.lay D) P.scr := by
  have hs := h.slK
  have hK := h.k1024
  have hf := h.ok.fits (P.SCR) (by simp)
  simp only [BitVec.toNat_setWidth] at hf
  rw [Nat.mod_eq_of_lt (by have := P.scr.isLt; omega)] at hf
  unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at hs
  exact ⟨rfl, by unfold oRsa; omega, ⟨P.scl * 8, by unfold oRsa; omega, by simp⟩, ⟨σ, h.ok⟩,
    by show 48 ≤ 3392; decide⟩

end In

/-! ## The entry -/

/-- The stack the function uses: the push, the inner frame and the calls'. -/
abbrev stackBytes : Nat := 16 + frameBytes + 3392

/-- The shared contract, with that stack. -/
abbrev spec (G : Spec.Mgf1.Hash) : Contract isa := Spec.RsaPss.signContract G G abi stackBytes

/-- The public parameters of an entry state. -/
def ep (s : State) : EP where
  B := s.gpr .esp - BitVec.ofNat 32 16 - BitVec.ofNat 32 frameBytes
  out := arg s 0
  n := arg s 2
  e := arg s 4
  p := arg s 6
  q := arg s 8
  dp := arg s 10
  dq := arg s 12
  qinv := arg s 14
  dig := arg s 16
  salt := arg s 17
  scr := arg s 19
  K := (arg s 3).toNat
  el := (arg s 5).toNat
  pl := (arg s 7).toNat
  ql := (arg s 9).toNat
  sl := (arg s 18).toNat
  scl := (arg s 20).toNat
  nB := Spec.Rsa.bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat
  eB := Spec.Rsa.bytesAt s.mem ((arg s 4).setWidth 64) (arg s 5).toNat

theorem ep_lay (D : Nat) (s : State) :
    (ep s).lay D = layOf frameBytes (ep s).argv ((ep s).ro D) (ep s).rw s 3392 := rfl

theorem in_of_pre {G : Spec.Mgf1.Hash} {s : State} (h : (spec G).pre s) : In G.len (ep s) (entered frameBytes s) := by
  sig_pre [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argSlots, argVal, argBytes, stackBelow] at h
  obtain ⟨hsp, hsa, hrd, hwr, oN, oE, oP, oQ, oDP, oDQ, oQI, oD, oSl, oS, oA, nS, nA, eS, eA, pS, pA, qS, qA,
    dpS, dpA, dqS, dqA, qiS, qiA, dS, dA, slS, slA, sA, rO, rN, rE, rP, rQ, rDP, rDQ, rQI, rD, rSl, rS, rA,
    kO, kN, kE, kP, kQ, kDP, kDQ, kQI, kD, kSl, kS, kA, fO, fN, fE, fP, fQ, fDP, fDQ, fQI, fD, fSl, fS,
    kv, olk, el1, elK, pl1, plK, ql1, qlK, dpl, qil, dql, slK⟩ := h
  simp only [stackBytes, frameBytes, Nat.reduceAdd] at hsp kO kN kE kP kQ kDP kDQ kQI kD kSl kS kA
  have a1 : arg s 1 = arg s 3 := BitVec.eq_of_toNat_eq olk
  have a11 : arg s 11 = arg s 7 := BitVec.eq_of_toNat_eq dpl
  have a15 : arg s 15 = arg s 7 := BitVec.eq_of_toNat_eq qil
  have a13 : arg s 13 = arg s 9 := BitVec.eq_of_toNat_eq dql
  rw [olk] at hwr oN oE oP oQ oDP oDQ oQI oD oSl oS oA rO kO fO
  rw [dpl] at hrd oDP dpS dpA rDP kDP fDP
  rw [qil] at hrd oQI qiS qiA rQI kQI fQI
  rw [dql] at hrd oDQ dqS dqA rDQ kDQ fDQ
  have h16 : 4 * Impl.RsaPkcs1Sig.X86.savedRegs.length ≤ (s.gpr .esp).toNat := by
    simp only [Impl.RsaPkcs1Sig.X86.savedRegs, List.length_cons, List.length_nil]; omega
  have hpush : Frame [below (s.gpr .esp) (4 * Impl.RsaPkcs1Sig.X86.savedRegs.length)] s.mem
      (entered frameBytes s).mem :=
    pushed_frame (by decide) h16
  have below16 : Region.Sub (below (s.gpr .esp) (4 * Impl.RsaPkcs1Sig.X86.savedRegs.length))
      ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 3552, 3552⟩ := by
    simp only [below, Impl.RsaPkcs1Sig.X86.savedRegs, List.length_cons, List.length_nil]
    rw [Taint.sub_setWidth (by omega)]
    exact Offset.sub_below _ (by omega) (by omega)
  refine
    { ok := ?_
      kv := kv, el1 := el1, elK := elK, pl1 := pl1, plK := plK, ql1 := ql1, qlK := qlK, slK := slK
      sl32 := (arg s 18).isLt
      scl32 := (arg s 20).isLt
      nB := Proof.RsaPkcs1Sig.bytesAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kN.sub_left below16).symm)
        (by show (arg s 3).toNat ≤ 2 ^ 64; omega)
      eB := Proof.RsaPkcs1Sig.bytesAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kE.sub_left below16).symm)
        (by show (arg s 5).toNat ≤ 2 ^ 64; omega) }
  rw [ep_lay]
  refine ok_entered (S := 3552) rfl (by decide) hsp (by simp) (by simp; omega) hrd
    (by rw [hwr]; rfl) ?_ ?_ ?_ ?_ ?_ ?_
  · intro r hr
    simp only [EP.ro, EP.rw, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [kN, kE, kP, kQ, kDP, kDQ, kQI, kD, kSl, kO, kS]
  · intro r hr
    simp only [EP.rw, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [rO, rS]
  · intro w hw r hr
    simp only [EP.rw, List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [EP.ro, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hw with rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [oN, oE, oP, oQ, oDP, oDQ, oQI, oD, oSl, oA, nS.symm, eS.symm, pS.symm, qS.symm, dpS.symm,
      dqS.symm, qiS.symm, dS.symm, slS.symm, sA]
  · exact List.pairwise_pair.mpr oS
  · intro r hr
    simp only [EP.ro, EP.rw, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [ep, BitVec.toNat_setWidth]
    all_goals first
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 2).isLt; omega)]; omega)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 4).isLt; omega)]; omega)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 6).isLt; omega)]; omega)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 8).isLt; omega)]; omega)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 10).isLt; omega)]; omega)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 12).isLt; omega)]; omega)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 14).isLt; omega)]; omega)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 16).isLt; omega)]; omega)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 17).isLt; omega)]; omega)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 0).isLt; omega)]; omega)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 19).isLt; omega)]; omega)
  · intro j hj
    have : j < 21 := hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨
        j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨
        j = 20) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> simp [ep, a1, a11, a13, a15]

end VG.Proof.RsaPss.X86.Sg
