module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.SgVerified
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.SgBody
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Rsa.Arm.PrivPrecomputed
public import VerifiedGarbage.Proof.Rsa.PreKey
import VerifiedGarbage.Proof.Framework.Contract

/-! # `vg_rsa_pkcs1_sign_precomputed` on ARMv7

`vg_rsa_pkcs1_sign`'s code calling `vg_rsa_private_checked_precomputed`
with the key's precomputed values `pre` (`code true`, `signCodeP`), proven
with `vg_rsa_pkcs1_sign`'s (`body_vp` of `ep s true`): its precondition gives
the body's start (`in_of_preP`), its public data the same public parameters
(`ep_eqP`), and a state that meets it holds a real key (`satisfiablePre`,
`Proof/Rsa/PreKey.lean`).
-/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.Arm.Sg
open VG VG.Arm VG.Impl.RsaPkcs1Sig.Arm.Sign VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.Rsa.PreKey (keyIn keyMem key_pre_of)

/-! ## A state that meets the contract -/

/-- The stack arguments of `preState`; the key (`keyMem`) has `n` at
`0x2000`, `p` at `0x4200`, `q` at `0x4300` and `pre` at `0x4800`. -/
def preArgs : List Nat := [0x2100, 1, 0, 0x3000, 0, 0x4200, 32, 0x4300, 32, 0x4400, 32, 0x4500, 32, 0x4600, 32, 0xa000, 0x420, 0x4800, 24]

/-- The memory of `preState`: the stack arguments from `0x8000`, and the
key. -/
def preMem (a : Addr) : Byte :=
  let i := a.toNat
  bif Nat.ble 0x8000 i && Nat.blt i 0x804c then
    BitVec.ofNat 8 (preArgs.getD ((i - 0x8000) / 4) 0 / 256 ^ ((i - 0x8000) % 4))
  else bif keyIn i then keyMem a else 0

def preState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 64 | .r2 => 0x2000 | .r3 => 64 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem := preMem
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x3000, 0⟩, ⟨0x4200, 32⟩, ⟨0x4300, 32⟩, ⟨0x4400, 32⟩, ⟨0x4500, 32⟩,
    ⟨0x4600, 32⟩, ⟨0x4800, 192⟩, ⟨0x8000, 76⟩]
  wr := [⟨0x1000, 64⟩, ⟨0xA000, 8448⟩]

theorem preState_key : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt preState.mem 0x2000 64)
    (Spec.Rsa.bytesAt preState.mem 0x4200 32) (Spec.Rsa.bytesAt preState.mem 0x4300 32) =
      some (Spec.Rsa.wordsAt preState.mem 0x4800 24) :=
  key_pre_of fun a ha => by
    have hs : (Nat.ble 0x8000 a.toNat && Nat.blt a.toNat 0x804c) = false := by
      simp only [keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at ha
      refine Bool.eq_false_iff.mpr fun h => ?_
      simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
      omega
    show (bif _ then _ else _) = _
    rw [hs, Bool.cond_false, ha, Bool.cond_true]

theorem satisfiablePre : ∃ s, (Spec.RsaPkcs1Sig.signPrecomputedContract abi stackBytes).pre s := by
  have p5 : BitVec.setWidth 64 (stackArg preState 5) = 0x4200 := by decide
  have p7 : BitVec.setWidth 64 (stackArg preState 7) = 0x4300 := by decide
  have p17 : BitVec.setWidth 64 (stackArg preState 17) = 0x4800 := by decide
  have l6 : (stackArg preState 6).toNat = 32 := by decide
  have l8 : (stackArg preState 8).toNat = 32 := by decide
  have l18 : (stackArg preState 18).toNat = 24 := by decide
  refine ⟨preState, ?_⟩
  sig_pre [Spec.RsaPkcs1Sig.signPrecomputedContract, Spec.RsaPkcs1Sig.signPrecomputedSig,
    Spec.RsaPkcs1Sig.signSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  sig_and_intros
  rotate_right
  · rw [p5, p7, p17, l6, l8, l18, show BitVec.setWidth 64 (8192 : BitVec 32) = (0x2000 : Addr) by decide,
      show BitVec.toNat (64 : BitVec 32) = 64 by decide]
    exact preState_key
  all_goals first
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (simp only [Spec.Rsa.lenValid]; decide)


/-! ## The entry of `vg_rsa_pkcs1_sign_precomputed` -/

abbrev specP : Contract isa := Spec.RsaPkcs1Sig.signPrecomputedContract abi stackBytes

theorem in_of_preP {s : State} (h : specP.pre s) : In (ep s true) (entered frameBytes s) := by
  sig_pre [Spec.RsaPkcs1Sig.signPrecomputedContract, Spec.RsaPkcs1Sig.signPrecomputedSig,
    Spec.RsaPkcs1Sig.signSig, abi, argRegs, reduceClassify, Loc.val] at h
  sig_split h
  rename_i hsp hsa hrd hwr oN oE oD oP oQ oDP oDQ oQI oS oPre oA nS eS dS pS qS dpS dqS qiS sPre sA kO kN kE kD kP
    kQ kDP kDQ kQI kS kPre kA fO fN fE fD fP fQ fDP fDQ fQI fS fPre kv olk el1 elK pl1 plK ql1 qlK dpl qil dql slK
    prl
  have key := h
  have h4616 : 4616 ≤ s.sp.toNat := hsp
  have r1 : s.gpr .r1 = s.gpr .r3 := BitVec.eq_of_toNat_eq olk
  have a10 : stackArg s 10 = stackArg s 6 := BitVec.eq_of_toNat_eq dpl
  have a14 : stackArg s 14 = stackArg s 6 := BitVec.eq_of_toNat_eq qil
  have a12 : stackArg s 12 = stackArg s 8 := BitVec.eq_of_toNat_eq dql
  rw [olk] at hwr oN oE oD oP oQ oDP oDQ oQI oS oPre oA kO fO
  rw [dpl] at oDP dpS kDP fDP hrd
  rw [qil] at oQI qiS kQI fQI hrd
  rw [dql] at oDQ dqS kDQ fDQ hrd
  have hpush : Frame [FrameStack.belowA s.sp 56] s.mem (entered frameBytes s).mem :=
    FrameStack.pushed_frameA (rs := Impl.RsaPkcs1Sig.Arm.pushRegs) (by show 56 ≤ s.sp.toNat; omega_arith)
  have below : Region.Sub (FrameStack.belowA s.sp 56)
      ⟨State.addr s.sp - BitVec.ofNat 64 4616, 4616⟩ := by
    show Region.Sub ⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩ _
    rw [FrameStack.addr_sub' (by omega_arith)]
    exact Offset.sub_below _ (by omega_arith) (by omega_arith)
  have bytesE {R : Region} (hR : (⟨State.addr s.sp - BitVec.ofNat 64 4616, 4616⟩ : Region).Disjoint R)
      (hl : R.len ≤ 2 ^ 64) : Spec.Rsa.bytesAt (entered frameBytes s).mem R.base R.len =
        Spec.Rsa.bytesAt s.mem R.base R.len :=
    bytesAt_frame hpush (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hR.sub_left below).symm) hl
  have wordsE {n : Nat} (hR : (⟨State.addr s.sp - BitVec.ofNat 64 4616, 4616⟩ : Region).Disjoint
      ⟨State.addr (stackArg s 17), 8 * n⟩) (hl : 8 * n < 2 ^ 64) :
      Spec.Rsa.wordsAt (entered frameBytes s).mem (State.addr (stackArg s 17)) n =
        Spec.Rsa.wordsAt s.mem (State.addr (stackArg s 17)) n :=
    VG.Proof.Rsa.wordsAt_frame hpush hl (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hR.sub_left below).symm)
  have kPre' : (⟨State.addr s.sp - BitVec.ofNat 64 4616, 4616⟩ : Region).Disjoint
      ⟨State.addr (stackArg s 17), 8 * (stackArg s 18).toNat⟩ := by rw [Nat.mul_comm]; exact kPre
  have hn := bytesE (R := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩) kN (by show (s.gpr .r3).toNat ≤ 2 ^ 64; omega_arith)
  have hp := bytesE (R := ⟨State.addr (stackArg s 5), (stackArg s 6).toNat⟩) kP (by show (stackArg s 6).toNat ≤ 2 ^ 64; omega_arith)
  have hq := bytesE (R := ⟨State.addr (stackArg s 7), (stackArg s 8).toNat⟩) kQ (by show (stackArg s 8).toNat ≤ 2 ^ 64; omega_arith)
  have hw := wordsE kPre' (by omega_arith)
  have le : Spec.Rsa.precomputedWords (s.gpr .r3).toNat ≤ (stackArg s 18).toNat := by
    rw [prl, Spec.Rsa.privatePrecomputedWords]; omega_using []
  constructor
  rotate_left
  · exact kv
  · exact el1
  · exact elK
  · exact pl1
  · exact plK
  · exact ql1
  · exact qlK
  · exact slK
  · exact (stackArg s 4).isLt
  · exact hn
  · have he : Spec.Rsa.bytesAt (entered frameBytes s).mem (State.addr (stackArg s 0)) (stackArg s 1).toNat =
        Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat :=
      bytesE (R := ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩) kE (by show (stackArg s 1).toNat ≤ 2 ^ 64; omega_arith)
    exact he
  · exact fun _ => prl
  · intro _
    change Spec.Rsa.privatePrecompute
      (Spec.Rsa.bytesAt (entered frameBytes s).mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
      (Spec.Rsa.bytesAt (entered frameBytes s).mem (State.addr (stackArg s 5)) (stackArg s 6).toNat)
      (Spec.Rsa.bytesAt (entered frameBytes s).mem (State.addr (stackArg s 7)) (stackArg s 8).toNat) =
        some (Spec.Rsa.wordsAt (entered frameBytes s).mem (State.addr (stackArg s 17)) (stackArg s 18).toNat)
    rw [hn, hp, hq, hw]
    exact key
  · intro _
    change Spec.Rsa.privatePrecomputedLeak (entered frameBytes s).mem (State.addr (stackArg s 17))
      (s.gpr .r3).toNat = Spec.Rsa.privatePrecomputedLeak s.mem (State.addr (stackArg s 17)) (s.gpr .r3).toNat
    unfold Spec.Rsa.privatePrecomputedLeak
    rw [Proof.Rsa.Arm.wordsAt_take le, Proof.Rsa.Arm.wordsAt_take (m := s.mem) le, hw]
  have lay : (ep s true).lay = layOf frameBytes 76 (ep s true).argv [(ep s true).N, (ep s true).E, (ep s true).DIG,
      (ep s true).PP, (ep s true).QQ, (ep s true).DP, (ep s true).DQ, (ep s true).QI, (ep s true).PRE]
      [(ep s true).OUT, (ep s true).SCR] s 3440 := by
    simp [ep, EP.lay, EP.argv, EP.ro, layOf]
  rw [lay]
  refine ok_entered (by decide) (by decide) rfl hsp hsa hrd hwr ?_ ?_ ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [kN, kE, kD, kP, kQ, kDP, kDQ, kQI, kPre, kO, kS, kA]
  · intro w hw r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hw with rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [oN, oE, oD, oP, oQ, oDP, oDQ, oQI, oPre, oA, nS.symm, eS.symm, dS.symm, pS.symm, qS.symm, dpS.symm,
      dqS.symm, qiS.symm, sPre, sA]
  · exact List.pairwise_pair.mpr oS
  · intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [fN, fE, fD, fP, fQ, fDP, fDQ, fQI, fPre, fO, fS]
  · intro j hj
    rcases (by omega_arith : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    · rfl
    · simp [regArg, ep, r1]
    · rfl
    · simp [regArg, ep]
  · intro i hi
    have : i < 19 := hi
    rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
        i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [ep, a10, a12, a14]


/-! ## The code -/

/-- The code, calling `vg_rsa_private_checked_precomputed` over `v`. -/
abbrev signCodeP (v : Proof.Rsa.Arm.CrtImpl) : Prog isa :=
  code true (privN true v) (privC true v)

theorem specP_sp {s : State} (h : specP.pre s) : stackBytes ≤ s.sp.toNat := by
  sig_pre [Spec.RsaPkcs1Sig.signPrecomputedContract, Spec.RsaPkcs1Sig.signPrecomputedSig,
    Spec.RsaPkcs1Sig.signSig, abi, argRegs, reduceClassify, Loc.val] at h
  exact h.1

theorem entered_stateP {s : State} (h : specP.pre s) :
    S (ep s true) (entered frameBytes s) (entered frameBytes s) :=
  ⟨in_of_preP h, ⟨(in_of_preP h).ok, (in_of_preP h).ok.sp, rfl, rfl, Frame.refl _ _⟩⟩

theorem code_okP (v : Proof.Rsa.Arm.CrtImpl) {s : State} (h : specP.pre s) :
    WP isa (signCodeP v) s fun t => abiPreserved s t ∧ specP.post s t := by
  have hs := specP_sp h
  have hin := in_of_preP h
  have st := entered_stateP h
  have hsp : 56 + frameBytes ≤ s.sp.toNat := Nat.le_trans (Nat.le_add_right _ _) hs
  have hF : FrameOk frameBytes := by decide
  have hb := (body_vp (P := ep s true) v).wp _ _ st
  refine WP.mono (wrap_ok hF (by rw [Nat.add_comm]; exact hsp) (W := (ep s true).lay.W)
    (Q := fun r m => Res (ep s true) (entered frameBytes s) m r) (fun r hr => ?_)
    (WP.mono hb fun u hu => ⟨hu.1.2.frame, hu.2⟩)) fun t ⟨abi, res⟩ => ⟨abi, ?_⟩
  · rw [pushRegion_eq (F := frameBytes) (A := 76) (C := 3440) (argv := (ep s true).argv)
      (ro := (ep s true).ro) (rw := [(ep s true).OUT, (ep s true).SCR]) hsp]
    exact hin.ok.push_apart r hr
  · sig_post [Spec.RsaPkcs1Sig.signPrecomputedContract, Spec.RsaPkcs1Sig.signPrecomputedSig,
      Spec.RsaPkcs1Sig.signSig, abi, argRegs, reduceClassify, Loc.val]
    rw [BitVec.setWidth_append_eq_right]
    have ro := fun {R : Region} (hR : R ∈ (ep s true).ro) =>
      entered_ro (F := frameBytes) (A := 76) (C := 3440) (argv := (ep s true).argv)
        (rw := [(ep s true).OUT, (ep s true).SCR]) hin.ok hsp hR
    have hD : digB (ep s true) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 3))
        (stackArg s 4).toNat := ro (R := (ep s true).DIG) (by simp)
    have hP : pB (ep s true) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 5))
        (stackArg s 6).toNat := ro (R := (ep s true).PP) (by simp)
    have hQ : qB (ep s true) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 7))
        (stackArg s 8).toNat := ro (R := (ep s true).QQ) (by simp)
    have hDP : dpB (ep s true) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 9))
        (stackArg s 6).toNat := ro (R := (ep s true).DP) (by simp)
    have hDQ : dqB (ep s true) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 11))
        (stackArg s 8).toNat := ro (R := (ep s true).DQ) (by simp)
    have hQI : qiB (ep s true) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 13))
        (stackArg s 6).toNat := ro (R := (ep s true).QI) (by simp)
    unfold Res at res
    rw [hD, hP, hQ, hDP, hDQ, hQI] at res
    exact res

theorem ep_eqP {s₁ s₂ : State} (hp : specP.pub s₁ s₂) : ep s₁ true = ep s₂ true := by
  sig_pub [Spec.RsaPkcs1Sig.signPrecomputedContract, Spec.RsaPkcs1Sig.signPrecomputedSig,
    Spec.RsaPkcs1Sig.signSig, abi, argRegs, reduceClassify, Loc.val] at hp
  obtain ⟨hsp, hl, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17,
    a18⟩ := hp
  obtain ⟨hl1, hleak⟩ := List.append_inj hl (by simp [bytesAt_length, h3, a1])
  obtain ⟨hn, he⟩ := List.append_inj (map_toNat_inj hl1) (by simp [bytesAt_length, h3])
  simp only [ep, ↓reduceIte]
  rw [hsp, h0, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a11, a13, a15, a16, a17, a18]
  rw [h2, h3] at hn
  rw [a0, a1] at he
  rw [a17, h3] at hleak
  rw [show State.addr (s₂.gpr .r2) = BitVec.setWidth 64 (s₂.gpr .r2) from rfl, hn,
    show State.addr (stackArg s₂ 0) = BitVec.setWidth 64 (stackArg s₂ 0) from rfl, he,
    show State.addr (stackArg s₂ 17) = BitVec.setWidth 64 (stackArg s₂ 17) from rfl, hleak]

theorem code_ctP (v : Proof.Rsa.Arm.CrtImpl) : ConstantTime isa specP.pre specP.pub (signCodeP v) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  have hep := ep_eqP hp
  have hsp : s₁.sp = s₂.sp := by
    sig_pub [Spec.RsaPkcs1Sig.signPrecomputedContract, Spec.RsaPkcs1Sig.signPrecomputedSig,
      Spec.RsaPkcs1Sig.signSig, abi, argRegs, reduceClassify, Loc.val] at hp
    exact hp.1
  refine (wrap_ct (F := frameBytes) (by decide) (P := fun a b => a = s₁ ∧ b = s₂)
    (fun a b h => by rw [h.1, h.2]; exact hsp)
    (fun a b h => by rw [h.1]; exact Nat.le_trans (Nat.le_add_right _ _) (specP_sp h₁)) ?_
    s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  refine (body_vp (P := ep s₁ true) v).ct.mono ?_ fun _ _ _ => trivial
  rintro a b ⟨_, _, ⟨rfl, rfl⟩, rfl, rfl⟩
  exact ⟨_, _, entered_stateP h₁, by rw [hep]; exact entered_stateP h₂⟩

/-- `vg_rsa_pkcs1_sign_precomputed`, calling `vg_rsa_private_checked_precomputed` over `v`. -/
theorem signPrecomputed_verified (v : Proof.Rsa.Arm.CrtImpl) :
    Verified target (signCodeP v) (Spec.RsaPkcs1Sig.signPrecomputedContract abi stackBytes) :=
  ⟨fun _ h => let ⟨t, s', he, hq⟩ := code_okP v h; ⟨t, s', he, hq.1, hq.2⟩, code_ctP v, satisfiablePre⟩

end VG.Proof.RsaPkcs1Sig.Arm.Sg
