module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Entry
public import VerifiedGarbage.Spec.RsaOaep.Contract
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.RsaOaep.Arm.Mgf
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSAES-OAEP decryption on ARMv7: where everything is

`EP`: what two runs share (the frame's base `B`, the pointers, the lengths
and the public key's bytes `nB` and `eB`), and its layout (`EP.lay`), with
the 3440 bytes below the frame that the call of `vg_rsa_private_checked`
uses. `In P σ`: the state `σ` the body starts from (`in_of_pre`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm.Dec

open VG VG.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm VG.Proof.RsaOaep.Arm
open VG.Impl.RsaPss.Arm (frameBytes oRsa arg)

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

abbrev OUT : Region := ⟨State.addr P.out, P.K⟩
abbrev ML : Region := ⟨State.addr P.ml, 8⟩
abbrev N : Region := ⟨State.addr P.n, P.K⟩
abbrev E : Region := ⟨State.addr P.e, P.el⟩
abbrev PP : Region := ⟨State.addr P.p, P.pl⟩
abbrev QQ : Region := ⟨State.addr P.q, P.ql⟩
abbrev DP : Region := ⟨State.addr P.dp, P.pl⟩
abbrev DQ : Region := ⟨State.addr P.dq, P.ql⟩
abbrev QI : Region := ⟨State.addr P.qinv, P.pl⟩
abbrev LAB : Region := ⟨State.addr P.lab, P.ll⟩
abbrev CT : Region := ⟨State.addr P.ct, P.K⟩
abbrev SCR : Region := ⟨State.addr P.scr, P.scl * 8⟩

/-- The arguments, in order. -/
abbrev argv : List (BitVec 32) :=
  [P.out, BitVec.ofNat 32 P.K, P.ml, P.n, BitVec.ofNat 32 P.K, P.e, BitVec.ofNat 32 P.el, P.p, BitVec.ofNat 32 P.pl,
    P.q, BitVec.ofNat 32 P.ql, P.dp, BitVec.ofNat 32 P.pl, P.dq, BitVec.ofNat 32 P.ql, P.qinv,
    BitVec.ofNat 32 P.pl, P.lab, BitVec.ofNat 32 P.ll, P.ct, BitVec.ofNat 32 P.K, P.scr, BitVec.ofNat 32 P.scl]

abbrev lay : Lay where
  B := P.B
  F := frameBytes
  A := 76
  argv := P.argv
  ro := [P.N, P.E, P.PP, P.QQ, P.DP, P.DQ, P.QI, P.LAB, P.CT]
  rw := [P.OUT, P.ML, P.SCR]
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
  slK : Spec.RsaPss.scratchWords P.K ≤ P.scl
  ll32 : P.ll < 2 ^ 32
  scl32 : P.scl < 2 ^ 32
  nB : Spec.Rsa.bytesAt σ.mem (State.addr P.n) P.K = P.nB
  eB : Spec.Rsa.bytesAt σ.mem (State.addr P.e) P.el = P.eB

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
  simp only [Proof.X25519.Arm.addr_toNat] at hf
  unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at hs
  exact ⟨rfl, by unfold oRsa; omega, ⟨P.scl * 8, by unfold oRsa; omega, by simp⟩, ⟨σ, h.ok⟩, by show 16 ≤ 3440; decide⟩

end In

/-! ## The entry -/

/-- The stack the function uses: the push, the inner frame and the call's. -/
abbrev stackBytes : Nat := 56 + frameBytes + 3440

/-- The shared contract, with that stack. -/
abbrev spec (h g : OHash) : Contract isa := Spec.RsaOaep.decryptContract h.G g.G abi stackBytes

/-- The public parameters of an entry state. -/
def ep (s : State) : EP where
  B := s.sp - BitVec.ofNat 32 56 - BitVec.ofNat 32 frameBytes
  out := s.gpr .r0
  ml := s.gpr .r2
  n := s.gpr .r3
  e := stackArg s 1
  p := stackArg s 3
  q := stackArg s 5
  dp := stackArg s 7
  dq := stackArg s 9
  qinv := stackArg s 11
  lab := stackArg s 13
  ct := stackArg s 15
  scr := stackArg s 17
  K := (stackArg s 0).toNat
  el := (stackArg s 2).toNat
  pl := (stackArg s 4).toNat
  ql := (stackArg s 6).toNat
  ll := (stackArg s 14).toNat
  scl := (stackArg s 18).toNat
  nB := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat
  eB := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 1)) (stackArg s 2).toNat

theorem ep_lay (s : State) :
    (ep s).lay = layOf frameBytes 76 (ep s).argv [(ep s).N, (ep s).E, (ep s).PP, (ep s).QQ, (ep s).DP,
      (ep s).DQ, (ep s).QI, (ep s).LAB, (ep s).CT] [(ep s).OUT, (ep s).ML, (ep s).SCR] s 3440 := rfl

theorem in_of_pre {h' g : OHash} {s : State} (h : (spec h' g).pre s) : In (ep s) (entered frameBytes s) := by
  sig_pre [Spec.RsaOaep.decryptContract, Spec.RsaOaep.decryptSig, abi, argRegs, reduceClassify, Loc.val] at h
  obtain ⟨hsp, hsa, hrd, hwr, oM, oN, oE, oP, oQ, oDP, oDQ, oQI, oL, oC, oS, oA, mN, mE, mP, mQ, mDP, mDQ, mQI, mL,
    mC, mS, mA, nS, eS, pS, qS, dpS, dqS, qiS, lS, cS, sA, kO, kM, kN, kE, kP, kQ, kDP, kDQ, kQI, kL, kC, kS, kA, fO,
    fM, fN, fE, fP, fQ, fDP, fDQ, fQI, fL, fC, fS, kv, olk, clk, el1, elK, pl1, plK, ql1, qlK, dpl, qil, dql,
    slK⟩ := h
  have h3624 : 3624 ≤ s.sp.toNat := hsp
  have r1 : s.gpr .r1 = stackArg s 0 := BitVec.eq_of_toNat_eq olk
  have a16 : stackArg s 16 = stackArg s 0 := BitVec.eq_of_toNat_eq clk
  have a8 : stackArg s 8 = stackArg s 4 := BitVec.eq_of_toNat_eq dpl
  have a12 : stackArg s 12 = stackArg s 4 := BitVec.eq_of_toNat_eq qil
  have a10 : stackArg s 10 = stackArg s 6 := BitVec.eq_of_toNat_eq dql
  rw [olk] at hwr oM oN oE oP oQ oDP oDQ oQI oL oC oS oA kO fO
  rw [clk] at oC mC cS kC fC hrd
  rw [dpl] at oDP mDP dpS kDP fDP hrd
  rw [qil] at oQI mQI qiS kQI fQI hrd
  rw [dql] at oDQ mDQ dqS kDQ fDQ hrd
  have hpush : Frame [FrameStack.belowA s.sp 56] s.mem (entered frameBytes s).mem :=
    FrameStack.pushed_frameA (rs := Impl.RsaPkcs1Sig.Arm.pushRegs) (by show 56 ≤ s.sp.toNat; omega)
  have below : Region.Sub (FrameStack.belowA s.sp 56)
      ⟨State.addr s.sp - BitVec.ofNat 64 stackBytes, stackBytes⟩ := by
    show Region.Sub ⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩ _
    rw [FrameStack.addr_sub' (by omega)]
    exact Offset.sub_below _ (show 56 ≤ stackBytes by decide) (show stackBytes - 56 + 56 ≤ stackBytes by decide)
  refine
    { ok := ?_
      kv := kv, el1 := el1, elK := elK, pl1 := pl1, plK := plK, ql1 := ql1, qlK := qlK, slK := slK
      ll32 := (stackArg s 14).isLt
      scl32 := (stackArg s 18).isLt
      nB := bytesAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kN.sub_left below).symm)
        (by show (stackArg s 0).toNat ≤ 2 ^ 64; omega)
      eB := bytesAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kE.sub_left below).symm)
        (by show (stackArg s 2).toNat ≤ 2 ^ 64; omega) }
  rw [ep_lay]
  refine ok_entered (by decide) (by decide) rfl hsp hsa hrd hwr ?_ ?_ ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [kN, kE, kP, kQ, kDP, kDQ, kQI, kL, kC, kO, kM, kS, kA]
  · intro w hw r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hw with rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [oN, oE, oP, oQ, oDP, oDQ, oQI, oL, oC, oA, mN, mE, mP, mQ, mDP, mDQ, mQI, mL, mC, mA,
      nS.symm, eS.symm, pS.symm, qS.symm, dpS.symm, dqS.symm, qiS.symm, lS.symm, cS.symm, sA]
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨⟨oM, oS⟩, mS, fun _ h => h.elim⟩
  · intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [fN, fE, fP, fQ, fDP, fDQ, fQI, fL, fC, fO, fM, fS]
  · intro j hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    · rfl
    · simp [regArg, ep, r1]
    · rfl
    · simp [regArg, ep]
  · intro i hi
    have : i < 19 := hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
        i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [ep, a8, a10, a12, a16]

end VG.Proof.RsaOaep.Arm.Dec
