module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Entry
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
public import VerifiedGarbage.Spec.RsaPss.Contract
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.RsaPss.Arm.Step
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSASSA-PSS signing on ARMv7: where everything is

`EP`: what two runs share (the frame's base `B`, the pointers, the lengths
and the public key's bytes `nB` and `eB`), and its layout (`EP.lay`), with
the 3440 bytes below the frame that the call of `vg_rsa_private_checked`
uses. `In P σ`: the state `σ` the body starts from. The shared contract,
with the stack of the frames and of the call, gives
`In (ep s) (entered frameBytes s)` (`in_of_pre`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Sg

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm

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

abbrev OUT : Region := ⟨State.addr P.out, P.K⟩
abbrev N : Region := ⟨State.addr P.n, P.K⟩
abbrev E : Region := ⟨State.addr P.e, P.el⟩
abbrev PP : Region := ⟨State.addr P.p, P.pl⟩
abbrev QQ : Region := ⟨State.addr P.q, P.ql⟩
abbrev DP : Region := ⟨State.addr P.dp, P.pl⟩
abbrev DQ : Region := ⟨State.addr P.dq, P.ql⟩
abbrev QI : Region := ⟨State.addr P.qinv, P.pl⟩
abbrev DIG : Region := ⟨State.addr P.dig, D⟩
abbrev SALT : Region := ⟨State.addr P.salt, P.sl⟩
abbrev SCR : Region := ⟨State.addr P.scr, P.scl * 8⟩

/-- The arguments, in order. -/
abbrev argv : List (BitVec 32) :=
  [P.out, BitVec.ofNat 32 P.K, P.n, BitVec.ofNat 32 P.K, P.e, BitVec.ofNat 32 P.el, P.p, BitVec.ofNat 32 P.pl,
    P.q, BitVec.ofNat 32 P.ql, P.dp, BitVec.ofNat 32 P.pl, P.dq, BitVec.ofNat 32 P.ql, P.qinv,
    BitVec.ofNat 32 P.pl, P.dig, P.salt, BitVec.ofNat 32 P.sl, P.scr, BitVec.ofNat 32 P.scl]

abbrev lay : Lay where
  B := P.B
  F := frameBytes
  A := 68
  argv := P.argv
  ro := [P.N, P.E, P.PP, P.QQ, P.DP, P.DQ, P.QI, P.DIG D, P.SALT]
  rw := [P.OUT, P.SCR]
  C := 3440

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
  nB : Spec.Rsa.bytesAt σ.mem (State.addr P.n) P.K = P.nB
  eB : Spec.Rsa.bytesAt σ.mem (State.addr P.e) P.el = P.eB

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
  simp only [Proof.X25519.Arm.addr_toNat] at hf
  unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at hs
  exact ⟨rfl, by unfold oRsa; omega_arith, ⟨P.scl * 8, by unfold oRsa; omega_arith, by simp⟩, ⟨σ, h.ok⟩, by show 16 ≤ 3440; decide⟩

end In

/-! ## The entry -/

/-- The stack the function uses: the push, the inner frame and the call's. -/
abbrev stackBytes : Nat := 56 + frameBytes + 3440

/-- The shared contract, with that stack. -/
abbrev spec (G : Spec.Mgf1.Hash) : Contract isa := Spec.RsaPss.signContract G G abi stackBytes

/-- The public parameters of an entry state. -/
def ep (s : State) : EP where
  B := s.sp - BitVec.ofNat 32 56 - BitVec.ofNat 32 frameBytes
  out := s.gpr .r0
  n := s.gpr .r2
  e := stackArg s 0
  p := stackArg s 2
  q := stackArg s 4
  dp := stackArg s 6
  dq := stackArg s 8
  qinv := stackArg s 10
  dig := stackArg s 12
  salt := stackArg s 13
  scr := stackArg s 15
  K := (s.gpr .r3).toNat
  el := (stackArg s 1).toNat
  pl := (stackArg s 3).toNat
  ql := (stackArg s 5).toNat
  sl := (stackArg s 14).toNat
  scl := (stackArg s 16).toNat
  nB := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat
  eB := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat

theorem ep_lay (D : Nat) (s : State) :
    (ep s).lay D = layOf frameBytes 68 (ep s).argv [(ep s).N, (ep s).E, (ep s).PP, (ep s).QQ, (ep s).DP,
      (ep s).DQ, (ep s).QI, (ep s).DIG D, (ep s).SALT] [(ep s).OUT, (ep s).SCR] s 3440 := rfl

theorem in_of_pre {G : Spec.Mgf1.Hash} {s : State} (h : (spec G).pre s) : In G.len (ep s) (entered frameBytes s) := by
  sig_pre [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argRegs, reduceClassify, Loc.val] at h
  sig_split h
  rename_i hsp hsa hrd hwr oN oE oP oQ oDP oDQ oQI oD oSl oS oA nS eS pS qS dpS dqS qiS dS slS sA kO kN kE
    kP kQ kDP kDQ kQI kD kSl kS kA fO fN fE fP fQ fDP fDQ fQI fD fSl fS kv olk el1 elK pl1 plK ql1 qlK dpl
    qil dql
  have slK := h
  have h3624 : 3624 ≤ s.sp.toNat := hsp
  have r1 : s.gpr .r1 = s.gpr .r3 := BitVec.eq_of_toNat_eq olk
  have a7 : stackArg s 7 = stackArg s 3 := BitVec.eq_of_toNat_eq dpl
  have a11 : stackArg s 11 = stackArg s 3 := BitVec.eq_of_toNat_eq qil
  have a9 : stackArg s 9 = stackArg s 5 := BitVec.eq_of_toNat_eq dql
  rw [olk] at hwr oN oE oP oQ oDP oDQ oQI oD oSl oS oA kO fO
  rw [dpl] at oDP dpS kDP fDP hrd
  rw [qil] at oQI qiS kQI fQI hrd
  rw [dql] at oDQ dqS kDQ fDQ hrd
  have hpush : Frame [FrameStack.belowA s.sp 56] s.mem (entered frameBytes s).mem :=
    FrameStack.pushed_frameA (rs := Impl.RsaPkcs1Sig.Arm.pushRegs) (by show 56 ≤ s.sp.toNat; omega_arith)
  have below : Region.Sub (FrameStack.belowA s.sp 56)
      ⟨State.addr s.sp - BitVec.ofNat 64 stackBytes, stackBytes⟩ := by
    show Region.Sub ⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩ _
    rw [FrameStack.addr_sub' (by omega_arith)]
    exact Offset.sub_below _ (show 56 ≤ stackBytes by decide) (show stackBytes - 56 + 56 ≤ stackBytes by decide)
  refine
    { ok := ?_
      kv := kv, el1 := el1, elK := elK, pl1 := pl1, plK := plK, ql1 := ql1, qlK := qlK, slK := slK
      sl32 := (stackArg s 14).isLt
      scl32 := (stackArg s 16).isLt
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
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [kN, kE, kP, kQ, kDP, kDQ, kQI, kD, kSl, kO, kS, kA]
  · intro w hw r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hw with rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [oN, oE, oP, oQ, oDP, oDQ, oQI, oD, oSl, oA, nS.symm, eS.symm, pS.symm, qS.symm, dpS.symm,
      dqS.symm, qiS.symm, dS.symm, slS.symm, sA]
  · exact List.pairwise_pair.mpr oS
  · intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [fN, fE, fP, fQ, fDP, fDQ, fQI, fD, fSl, fO, fS]
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
      simp [ep, a7, a9, a11]

end VG.Proof.RsaPss.Arm.Sg
