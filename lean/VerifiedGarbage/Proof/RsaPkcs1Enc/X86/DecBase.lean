module

public import VerifiedGarbage.Impl.RsaPkcs1Enc.X86.Decrypt
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Entry
public import VerifiedGarbage.Spec.RsaPkcs1Enc.Contract
public import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSAES-PKCS1-v1_5 decryption on x86: where everything is

As on ARMv7 (`Proof/RsaPkcs1Enc/Arm/DecBase.lean`): `EP`, what two runs
share (the frame's base `B`, the pointers, the lengths, and the public key's
bytes `nB` and `eB`), and its layout (`EP.lay`,
`Proof/RsaPkcs1Sig/X86/Lay.lean`), with the 3448 bytes below the frame that
the private-key operation and its return address use. `In P σ`: the state
`σ` the body starts from; `S P σ s`: a state of the body. The shared
contract, with the stack of the frames and of the calls, gives
`In (ep s) (entered frameBytes s)` (`in_of_pre`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Dec

open VG VG.Impl.RsaPkcs1Enc.X86.Decrypt VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes

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

abbrev OUT : Region := ⟨P.out.setWidth 64, P.K⟩
abbrev ML : Region := ⟨P.ml.setWidth 64, 8⟩
abbrev N : Region := ⟨P.n.setWidth 64, P.K⟩
abbrev E : Region := ⟨P.e.setWidth 64, P.el⟩
abbrev D : Region := ⟨P.d.setWidth 64, P.dl⟩
abbrev INP : Region := ⟨P.inp.setWidth 64, P.K⟩
abbrev PP : Region := ⟨P.p.setWidth 64, P.pl⟩
abbrev QQ : Region := ⟨P.q.setWidth 64, P.ql⟩
abbrev DP : Region := ⟨P.dp.setWidth 64, P.pl⟩
abbrev DQ : Region := ⟨P.dq.setWidth 64, P.ql⟩
abbrev QI : Region := ⟨P.qinv.setWidth 64, P.pl⟩
abbrev SCR : Region := ⟨P.scr.setWidth 64, P.sl * 8⟩

/-- The arguments, in order. -/
abbrev argv : List (BitVec 32) :=
  [P.out, BitVec.ofNat 32 P.K, P.ml, P.n, BitVec.ofNat 32 P.K, P.e, BitVec.ofNat 32 P.el, P.d,
    BitVec.ofNat 32 P.dl, P.inp, BitVec.ofNat 32 P.K, P.p, BitVec.ofNat 32 P.pl, P.q, BitVec.ofNat 32 P.ql,
    P.dp, BitVec.ofNat 32 P.pl, P.dq, BitVec.ofNat 32 P.ql, P.qinv, BitVec.ofNat 32 P.pl, P.scr,
    BitVec.ofNat 32 P.sl]

abbrev ro : List Region := [P.N, P.E, P.D, P.INP, P.PP, P.QQ, P.DP, P.DQ, P.QI]
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
  dl1 : 1 ≤ P.dl
  dlK : P.dl ≤ P.K
  pl1 : 1 ≤ P.pl
  plK : P.pl < P.K
  ql1 : 1 ≤ P.ql
  qlK : P.ql < P.K
  slK : Spec.Rsa.scratchWords P.K ≤ P.sl
  sl32 : P.sl < 2 ^ 32
  nB : Spec.Rsa.bytesAt σ.mem (P.n.setWidth 64) P.K = P.nB
  eB : Spec.Rsa.bytesAt σ.mem (P.e.setWidth 64) P.el = P.eB

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
abbrev stackBytes : Nat := 16 + frameBytes + 3448

/-- The shared contract, with that stack. -/
abbrev spec : Contract isa := Spec.RsaPkcs1Enc.decryptContract abi stackBytes

/-- The public parameters of an entry state. -/
def ep (s : State) : EP where
  B := s.gpr .esp - BitVec.ofNat 32 16 - BitVec.ofNat 32 frameBytes
  out := arg s 0
  ml := arg s 2
  n := arg s 3
  e := arg s 5
  d := arg s 7
  inp := arg s 9
  p := arg s 11
  q := arg s 13
  dp := arg s 15
  dq := arg s 17
  qinv := arg s 19
  scr := arg s 21
  K := (arg s 4).toNat
  el := (arg s 6).toNat
  dl := (arg s 8).toNat
  pl := (arg s 12).toNat
  ql := (arg s 14).toNat
  sl := (arg s 22).toNat
  nB := Spec.Rsa.bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat
  eB := Spec.Rsa.bytesAt s.mem ((arg s 5).setWidth 64) (arg s 6).toNat

theorem ep_lay (s : State) :
    (ep s).lay = layOf frameBytes (ep s).argv (ep s).ro (ep s).rw s 3448 := rfl

theorem in_of_pre {s : State} (h : spec.pre s) : In (ep s) (entered frameBytes s) := by
  sig_pre [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, abi, argSlots, argVal, argBytes,
    stackBelow] at h
  obtain ⟨hsp, hsa, hrd, hwr, oM, oN, oE, oD, oI, oP, oQ, oDP, oDQ, oQI, oS, oA, mN, mE, mD, mI, mP, mQ, mDP,
    mDQ, mQI, mS, mA, nS, nA, eS, eA, dS, dA, iS, iA, pS, pA, qS, qA, dpS, dpA, dqS, dqA, qiS, qiA, sA, rO, rM,
    rN, rE, rD, rI, rP, rQ, rDP, rDQ, rQI, rS, rA, kO, kM, kN, kE, kD, kI, kP, kQ, kDP, kDQ, kQI, kS, kA, fO,
    fM, fN, fE, fD, fI, fP, fQ, fDP, fDQ, fQI, fS, kv, olk, ilk, el1, elK, dl1, dlK, pl1, plK, ql1, qlK, dpl,
    qil, dql, slK⟩ := h
  simp only [stackBytes, frameBytes, Nat.reduceAdd] at hsp kO kM kN kE kD kI kP kQ kDP kDQ kQI kS kA
  have a1 : arg s 1 = arg s 4 := BitVec.eq_of_toNat_eq olk
  have a10 : arg s 10 = arg s 4 := BitVec.eq_of_toNat_eq ilk
  have a16 : arg s 16 = arg s 12 := BitVec.eq_of_toNat_eq dpl
  have a20 : arg s 20 = arg s 12 := BitVec.eq_of_toNat_eq qil
  have a18 : arg s 18 = arg s 14 := BitVec.eq_of_toNat_eq dql
  rw [olk] at hwr oM oN oE oD oI oP oQ oDP oDQ oQI oS oA rO kO fO
  rw [ilk] at hrd oI mI iS iA rI kI fI
  rw [dpl] at hrd oDP mDP dpS dpA rDP kDP fDP
  rw [qil] at hrd oQI mQI qiS qiA rQI kQI fQI
  rw [dql] at hrd oDQ mDQ dqS dqA rDQ kDQ fDQ
  have h16 : 4 * Impl.RsaPkcs1Sig.X86.savedRegs.length ≤ (s.gpr .esp).toNat := by
    simp only [Impl.RsaPkcs1Sig.X86.savedRegs, List.length_cons, List.length_nil]; omega
  have hpush : Frame [below (s.gpr .esp) (4 * Impl.RsaPkcs1Sig.X86.savedRegs.length)] s.mem
      (entered frameBytes s).mem :=
    pushed_frame (by decide) h16
  have below16 : Region.Sub (below (s.gpr .esp) (4 * Impl.RsaPkcs1Sig.X86.savedRegs.length))
      ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 3568, 3568⟩ := by
    simp only [below, Impl.RsaPkcs1Sig.X86.savedRegs, List.length_cons, List.length_nil]
    rw [Taint.sub_setWidth (by omega)]
    exact Offset.sub_below _ (by omega) (by omega)
  have sl32 : (arg s 22).toNat < 2 ^ 32 := (arg s 22).isLt
  refine
    { ok := ?_
      kv := kv, el1 := el1, elK := elK, dl1 := dl1, dlK := dlK, pl1 := pl1, plK := plK, ql1 := ql1,
      qlK := qlK, slK := slK, sl32 := sl32
      nB := Proof.RsaPkcs1Sig.bytesAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kN.sub_left below16).symm)
        (by show (arg s 4).toNat ≤ 2 ^ 64; omega)
      eB := Proof.RsaPkcs1Sig.bytesAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kE.sub_left below16).symm)
        (by show (arg s 6).toNat ≤ 2 ^ 64; omega) }
  rw [ep_lay]
  refine ok_entered (S := 3568) rfl (by decide) hsp (by simp) (by simp; omega) hrd
    (by rw [hwr]; rfl) ?_ ?_ ?_ ?_ ?_ ?_
  · intro r hr
    simp only [EP.ro, EP.rw, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [kN, kE, kD, kI, kP, kQ, kDP, kDQ, kQI, kO, kM, kS]
  · intro r hr
    simp only [EP.rw, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [rO, rM, rS]
  · intro w hw r hr
    simp only [EP.rw, List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [EP.ro, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hw with rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [oN, oE, oD, oI, oP, oQ, oDP, oDQ, oQI, oA, mN, mE, mD, mI, mP, mQ, mDP, mDQ, mQI, mA,
      nS.symm, eS.symm, dS.symm, iS.symm, pS.symm, qS.symm, dpS.symm, dqS.symm, qiS.symm, sA]
  · refine List.Pairwise.cons ?_ (List.pairwise_pair.mpr mS)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [oM, oS]
  · intro r hr
    simp only [EP.ro, EP.rw, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [ep, BitVec.toNat_setWidth]
    all_goals first
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 3).isLt; omega)]; omega)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 5).isLt; omega)]; omega)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 7).isLt; omega)]; omega)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 9).isLt; omega)]; omega)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 11).isLt; omega)]; omega)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 13).isLt; omega)]; omega)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 15).isLt; omega)]; omega)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 17).isLt; omega)]; omega)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 19).isLt; omega)]; omega)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 0).isLt; omega)]; omega)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 2).isLt; omega)]; omega)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 21).isLt; omega)]; omega)
  · intro j hj
    have : j < 23 := hj
    rcases (by omega_using [this] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨
        j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨
        j = 20 ∨ j = 21 ∨ j = 22) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl <;> simp [ep, a1, a10, a16, a18, a20]

end VG.Proof.RsaPkcs1Enc.X86.Dec
