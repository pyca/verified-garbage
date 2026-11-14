module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.SignVerified
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.SignCT
public import VerifiedGarbage.Proof.Rsa.PreKey
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.SignVerified
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.SignCT
meta import VerifiedGarbage.Proof.Rsa.PreKey
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # `vg_rsa_pkcs1_sign_precomputed` on AArch64

`vg_rsa_pkcs1_sign`'s code, passing on the key's precomputed values `pre`
to `vg_rsa_private_checked_precomputed` (`codeP`): the proofs of
`vg_rsa_pkcs1_sign` (`codeN_ok`, `codeN_ct`) with that call, given what the
contract says of `pre` (`PreX`), proven against
`vg_rsa_pkcs1_sign_precomputed`'s contract, with a state that meets it
(`satisfiablePre`), which holds a real key (`Proof/Rsa/PreKey.lean`).
-/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.AArch64.Sgn
open VG VG.AArch64 VG.Impl.RsaPkcs1Sig.AArch64.Sign
open VG.Proof.Rsa.PreKey (keyIn keyMem key_pre_of)
open VG.Proof.RsaPkcs1Sig.AArch64 (Two Pins clob)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

/-! ## A state that meets the contract -/

/-- The stack arguments of `preState`; the key (`keyMem`) has `n` at
`0x2000`, `p` at `0x4200`, `q` at `0x4300` and `pre` at `0x4800`. -/
def preArgs : List Nat := [1, 0x4200, 32, 0x4300, 32, 0x4400, 32, 0x4500, 32, 0x4600, 32, 0x10000, 0x420, 0x4800, 24]

/-- The memory of `preState`: the stack arguments from `2^40`, and the key. -/
def preMem (a : Addr) : Byte :=
  let i := a.toNat
  bif Nat.ble 0x10000000000 i && Nat.blt i 0x10000000078 then
    BitVec.ofNat 8 (preArgs.getD ((i - 0x10000000000) / 8) 0 / 256 ^ ((i - 0x10000000000) % 8))
  else bif keyIn i then keyMem a else 0

/-- `satState` with the key and its precomputed values. -/
def preState : State where
  gpr r := match r with
    | .x0 => 0x5000 | .x1 => 64 | .x2 => 0x2000 | .x3 => 64 | .x4 => 0x2100 | .x5 => 1 | .x7 => 0x3000
    | _ => 0
  sp := 0x10000000000
  mem := preMem
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x3000, 1⟩, ⟨0x4200, 32⟩, ⟨0x4300, 32⟩, ⟨0x4400, 32⟩, ⟨0x4500, 32⟩,
    ⟨0x4600, 32⟩, ⟨0x4800, 192⟩, ⟨0x10000000000, 120⟩]
  wr := [⟨0x5000, 64⟩, ⟨0x10000, 8448⟩]

theorem preState_key : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt preState.mem 0x2000 64)
    (Spec.Rsa.bytesAt preState.mem 0x4200 32) (Spec.Rsa.bytesAt preState.mem 0x4300 32) =
      some (Spec.Rsa.wordsAt preState.mem 0x4800 24) :=
  key_pre_of fun a ha => by
    have hs : (Nat.ble 0x10000000000 a.toNat && Nat.blt a.toNat 0x10000000078) = false := by
      simp only [keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at ha
      refine Bool.eq_false_iff.mpr fun h => ?_
      simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
      omega
    show (bif _ then _ else _) = _
    rw [hs, Bool.cond_false, ha, Bool.cond_true]

theorem pre_args : stackArg preState 0 = 1 ∧ stackArg preState 1 = 0x4200 ∧ stackArg preState 2 = 32 ∧ stackArg preState 3 = 0x4300 ∧ stackArg preState 4 = 32 ∧ stackArg preState 5 = 0x4400 ∧ stackArg preState 6 = 32 ∧ stackArg preState 7 = 0x4500 ∧ stackArg preState 8 = 32 ∧ stackArg preState 9 = 0x4600 ∧ stackArg preState 10 = 32 ∧ stackArg preState 11 = 0x10000 ∧ stackArg preState 12 = 0x420 ∧ stackArg preState 13 = 0x4800 ∧ stackArg preState 14 = 24 := by
  decide

theorem stackArgs_fifteen (s : State) :
    List.map (stackArg s) (List.range 15) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10, stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14] := rfl

theorem satisfiablePre (K : Nat) (hK : K ≤ 2 ^ 20) :
    ∃ s, (Spec.RsaPkcs1Sig.signPrecomputedContract abi (stk K)).pre s := by
  refine ⟨preState, ?_⟩
  have e : stk K = (frameBytes + K - 1) + 1 := by unfold stk frameBytes; omega_using []
  rw [e]
  sig_pre [Spec.RsaPkcs1Sig.signPrecomputedContract, Spec.RsaPkcs1Sig.signPrecomputedSig, Spec.RsaPkcs1Sig.signSig,
    abi, argRegs, stackArgs_fifteen, List.append_eq]
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩ := pre_args
  have hS : frameBytes + K - 1 + 1 = 1152 + K := by unfold frameBytes; omega_using []
  have hsp : (0x10000000000 : BitVec 64).toNat = 2 ^ 40 := by decide
  have hkb : ((0x10000000000 : BitVec 64) - BitVec.ofNat 64 (1152 + K)).toNat = 2 ^ 40 - (1152 + K) := by
    rw [BitVec.toNat_sub, hsp, BitVec.toNat_ofNat]; omega_using [hK]
  have ha : stackArgAddr preState 0 = 0x10000000000 := by decide
  simp only [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, hS, ha]
  have kd : ∀ (b : BitVec 64) (n : Nat), b.toNat + n ≤ 2 ^ 20 →
      Region.Disjoint ⟨0x10000000000 - BitVec.ofNat 64 (1152 + K), 1152 + K⟩ ⟨b, n⟩ := fun b n h =>
    Region.disjoint_of_le (.inr (by dsimp only; rw [hkb]; omega_using [hK, h])) (by dsimp only; rw [hkb]; omega_using [hK])
      (by dsimp only; omega_using [h])
  have kt : Region.Disjoint ⟨0x10000000000 - BitVec.ofNat 64 (1152 + K), 1152 + K⟩ ⟨0x10000000000, 120⟩ :=
    Region.disjoint_of_le (.inl (by dsimp only; rw [hkb, hsp]; omega_using [hK]))
      (by dsimp only; rw [hkb]; omega_using [hK]) (by dsimp only; rw [hsp]; omega_using [])
  sig_and_intros
  rotate_right
  · exact preState_key
  all_goals first
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact kd _ _ (by decide)
    | exact kt
    | (rw [hsp]; omega_using [hK])
    | (simp only [Spec.Rsa.lenValid]; decide)

/-! ## What the contract says of `pre` -/

/-- `pre`, our stack arguments 13 and 14, and our 15 stack arguments. -/
abbrev preRs (s : State) : Region := ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
abbrev aRP (s : State) : Region := ⟨stackArgAddr s 0, 120⟩

/-- What the call of `vg_rsa_private_checked_precomputed` needs besides
`PreS`. -/
structure PreX (K : Nat) (s : State) : Prop where
  sp3 : s.sp.toNat + 120 ≤ 2 ^ 64
  hrd : Covers [preRs s, aRP s] s.rd
  oa : (oR s).Disjoint (aRP s)
  sa : (sR s).Disjoint (aRP s)
  ka : (kR K s).Disjoint (aRP s)
  opr : (oR s).Disjoint (preRs s)
  spr : (sR s).Disjoint (preRs s)
  kpr : (kR K s).Disjoint (preRs s)
  wpr : (stackArg s 13).toNat + (stackArg s 14).toNat * 8 ≤ 2 ^ 64
  prl : (stackArg s 14).toNat =
    Spec.Rsa.privatePrecomputedWords (s.gpr .x3).toNat (stackArg s 2).toNat (stackArg s 4).toNat
  key : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat) =
    some (Spec.Rsa.wordsAt s.mem (stackArg s 13) (stackArg s 14).toNat)

theorem a104_sub (s : State) : Region.Sub (aR s) (aRP s) := by
  simpa using Offset.sub_base (stackArgAddr s 0) (d := 0) (n := 104) (k := 120) (by decide)

theorem preSP_of {K : Nat} {s : State}
    (h : (Spec.RsaPkcs1Sig.signPrecomputedContract abi (stk K)).pre s) : PreS K s ∧ PreX K s := by
  have e : stk K = (frameBytes + K - 1) + 1 := by unfold stk frameBytes; omega_using []
  rw [e] at h
  sig_pre [Spec.RsaPkcs1Sig.signPrecomputedContract, Spec.RsaPkcs1Sig.signPrecomputedSig,
    Spec.RsaPkcs1Sig.signSig, abi, argRegs, stackArgs_fifteen, List.append_eq, List.range, List.range.loop] at h
  sig_pre [Spec.RsaPkcs1Sig.signPrecomputedContract, Spec.RsaPkcs1Sig.signPrecomputedSig,
    Spec.RsaPkcs1Sig.signSig, abi, argRegs, stackArgs_fifteen, List.append_eq, List.range, List.range.loop] at h
  sig_split h
  rename_i sp1 sp2 hrd hwr on oe od op oq odp odq oqi os opr oa ns es ds ps qs dps dqs qis spr sa ko kn ke kd
    kp kq kdp kdq kqi ks kpr ka wo wn we wd wp wq wdp wdq wqi ws wpr hsplit1 ol e1 e2 p1 p2 q1 q2 hdp hqi hdq hs
    prl
  obtain ⟨k1, k2⟩ := hsplit1
  rw [← e] at sp1 ko kn ke kd kp kq kdp kdq kqi ks kpr ka
  have s104 := a104_sub s
  have hc : Covers [nR s, eR s, dR s, pR s, qR s, dpR s, dqR s, qiR s, aR s] s.rd := by
    rw [hrd]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    iterate 8 exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    exact ⟨⟨stackArgAddr s 0, 120⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  exact ⟨⟨sp1, by omega_using [sp2], hc, by rw [hwr]; simp, by rw [hwr]; simp, on, oe, od, op, oq, odp, odq, oqi, os,
    oa.sub_right s104, ns, es, ds, ps, qs, dps, dqs, qis, sa.sub_right s104, ko, kn, ke, kd, kp, kq, kdp, kdq,
    kqi, ks, ka.sub_right s104, wo, wn, we, wd, wp, wq, wdp, wdq, wqi, ws, k1, k2, ol, e1, e2, p1, p2, q1, q2,
    hdp, hqi, hdq, by unfold Spec.Rsa.scratchWords at hs; omega_using [hs]⟩,
    ⟨sp2, by
      rw [hrd]
      refine Covers.of_mem fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp, oa, sa, ka, opr, spr, kpr, wpr,
      prl, h⟩⟩

theorem argsOkP {K : Nat} {s : State} (hx : PreX K s) : ArgsOk K s 15 :=
  ⟨fun j hj => hx.hrd _ _ ⟨aRP s, by simp, by
      rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])⟩,
    fun j hj => hx.ka.sub_right (by rw [stackArgAddr_eq s j]; exact Offset.sub_base _ (by omega_using [hj]))⟩

/-- Words of the caller's, in memory changed only in the frame. -/
theorem words_frame {K : Nat} {s : State} {m : Mem} (hf : Frame [⟨fb s, frameBytes⟩] s.mem m) {p : Addr}
    {n : Nat} (hk : (kR K s).Disjoint ⟨p, n * 8⟩) (hl : p.toNat + n * 8 ≤ 2 ^ 64) :
    Spec.Rsa.wordsAt m p n = Spec.Rsa.wordsAt s.mem p n := by
  simp only [Spec.Rsa.wordsAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  exact hf.readW (r := ⟨p, n * 8⟩) (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hl, hi])) (keep_of_frame hk) (by decide)

theorem a112_sub (K : Nat) (s : State) : Region.Sub ⟨fb s, 112⟩ (kR K s) :=
  fun a h => frame_sub0 K s a (Region.sub_prefix (by decide) a h)

theorem privPOk_of (c : PrivPChecked) {s t : State} (hp : PreS c.stack s) (hx : PreX c.stack s)
    {em : List Byte} (ha : AtCall s em t) (he : ∀ i < 14, stackArg t i = stackArg s (i + 1)) :
    PrivPOk c.stack t := by
  have hfb := fb_toNat hp
  have hkb := kb_toNat hp
  have hcl := c.le
  have hfK : fb s - BitVec.ofNat 64 c.stack = kb c.stack s := by rw [fb_eq c.stack, BitVec.add_sub_cancel]
  have hkK : Region.Sub ⟨kb c.stack s, c.stack⟩ (kR c.stack s) := Region.sub_prefix (by unfold stk; omega_arith)
  have h112 : (⟨fb s, 112⟩ : Region) = ⟨kb c.stack s + BitVec.ofNat 64 c.stack, 112⟩ := by rw [fb_eq c.stack]
  have a10 := he 10 (by decide); have a11 := he 11 (by decide)
  have a12 := he 12 (by decide); have a13 := he 13 (by decide)
  have b1 := he 0 (by decide); have b3 := he 2 (by decide)
  have c1 := he 1 (by decide); have c3 := he 3 (by decide)
  simp only [Nat.reduceAdd, Nat.zero_add] at a10 a11 a12 a13 b1 b3 c1 c3
  have hpw := hx.wpr
  have hpr : VG.Proof.RsaPkcs1Sig.AArch64.preR t = preRs s := by
    simp only [VG.Proof.RsaPkcs1Sig.AArch64.preR, preRs, a12, a13]
  refine ⟨privOk_ofK c.pos c.le hp ha, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ha.sp]; unfold frameBytes at hfb; omega_arith
  · rw [ha.x0, ha.x1, ha.sp]; exact (hp.ko.sub_left (a112_sub c.stack s)).symm
  · rw [a10, a11, ha.sp]; exact (hp.ks.sub_left (a112_sub c.stack s)).symm
  · rw [ha.sp, hfK, h112]
    exact Offset.base_disjoint _ (by omega_arith) (by unfold stk at *; omega_arith)
  · rw [ha.x0, ha.x1, hpr]; exact hx.opr
  · rw [a10, a11, hpr]; exact hx.spr
  · rw [ha.sp, hfK, hpr]; exact hx.kpr.sub_left hkK
  · rw [a12, a13]; exact hpw
  · rw [ha.rd, ha.wr, hpr, ha.sp]
    refine Covers.cons (Covers.left (Covers.trans (Covers.of_mem fun r hr => by
      rw [List.mem_singleton.mp hr]; simp) hx.hrd)) (Covers.right (Covers.one ?_))
    simpa using in_frame s s.wr (d := 0) (n := 112) (by decide)
  · rw [a13, ha.x3, c1, c3]; exact hx.prl
  · have hl : ∀ {p : Addr} {len : Nat}, p.toNat + len ≤ 2 ^ 64 → len ≤ 2 ^ 64 := fun h => by omega_arith
    rw [ha.x2, ha.x3, b1, b3, c1, c3, a12, a13,
      bytes_frame ha.mem hp.kn (hl hp.wn), bytes_frame ha.mem hp.kp (hl hp.wp),
      bytes_frame ha.mem hp.kq (hl hp.wq), words_frame ha.mem hx.kpr hpw]
    exact hx.key

theorem callP_ok (c : PrivPChecked) {s t : State} (hp : PreS c.stack s) (hx : PreX c.stack s)
    {em : List Byte} (ha : AtCall s em t) (he : ∀ i < 14, stackArg t i = stackArg s (i + 1)) :
    WP isa (.call c.name c.code) t (AfterCall s em) :=
  privPCall c (privPOk_of c hp hx ha he) fun _ hrd' hwr' hsp' hf hpres hvs hpost =>
    afterCall_of c.le c.depth hp ha hrd' hwr' hsp' hf hpres hvs hpost

theorem codeP_correct (c : PrivPChecked) (s : State)
    (h : (Spec.RsaPkcs1Sig.signPrecomputedContract abi (stk c.stack)).pre s) :
    ∃ t s', Exec isa (codeP c.name c.code) s t s' ∧ abiPreserved s s' ∧
      (Spec.RsaPkcs1Sig.signPrecomputedContract abi (stk c.stack)).post s s' := by
  obtain ⟨hp, hx⟩ := preSP_of h
  obtain ⟨t, s', he, habi, hr⟩ := codeN_ok hp (argsOkP hx) (by decide) (by decide)
    fun _ _ ht he => callP_ok c hp hx ht he
  refine ⟨t, s', he, habi, ?_⟩
  sig_post [Spec.RsaPkcs1Sig.signPrecomputedContract, Spec.RsaPkcs1Sig.signPrecomputedSig,
    Spec.RsaPkcs1Sig.signSig, abi, argRegs, stackArgs_fifteen, List.append_eq]
  rw [← sigOut_eq]
  exact hr

/-! ## Constant time -/

/-- The public data of `pre`: its place and length, and `n`'s values. -/
def PubX (a s : State) : Prop :=
  stackArg s 13 = stackArg a 13 ∧ stackArg s 14 = stackArg a 14 ∧
    Spec.Rsa.wordsAt s.mem (stackArg s 13) (Spec.Rsa.precomputedWords (s.gpr .x3).toNat) =
      Spec.Rsa.wordsAt a.mem (stackArg a 13) (Spec.Rsa.precomputedWords (a.gpr .x3).toNat)

/-- What the precomputed call needs besides `PreS` and `PubS`. -/
def XP (K : Nat) (a s : State) : Prop := PreX K s ∧ PubX a s

theorem pubSP_of {S : Nat} {s₁ s₂ : State} (h : (Spec.RsaPkcs1Sig.signPrecomputedContract abi S).pub s₁ s₂) :
    PubS s₁ s₂ ∧ PubX s₁ s₂ := by
  sig_pub [Spec.RsaPkcs1Sig.signPrecomputedContract, Spec.RsaPkcs1Sig.signPrecomputedSig,
    Spec.RsaPkcs1Sig.signSig, abi, argRegs, stackArgs_fifteen, List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13,
    a14⟩ := h
  obtain ⟨hl₁, hl₂⟩ := List.append_inj hl (by simp [bytesAt_length, h3, h5])
  obtain ⟨hn, he⟩ := leak_eq2 (by rw [bytesAt_length, bytesAt_length, h3]) hl₁
  have hw := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hl₂
  refine ⟨⟨hsp.symm, fun r hr => ?_, h6.symm, fun i hi => ?_, hn.symm, he.symm⟩, a13.symm, a14.symm, hw.symm⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h0.symm, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h7.symm]
  · rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
      i = 10 ∨ i = 11 ∨ i = 12) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a0.symm, a1.symm, a2.symm, a3.symm, a4.symm, a5.symm, a6.symm, a7.symm, a8.symm, a9.symm,
      a10.symm, a11.symm, a12.symm]

/-- `n`'s values in `pre`, at the call, are the entry state's. -/
theorem preWords_call {K : Nat} {s t : State} (hx : PreX K s) {em : List Byte}
    (ha : AtCall s em t) (he : ∀ i < 14, stackArg t i = stackArg s (i + 1)) :
    Spec.Rsa.wordsAt t.mem (stackArg t 12) (Spec.Rsa.precomputedWords (t.gpr .x3).toNat) =
      Spec.Rsa.wordsAt s.mem (stackArg s 13) (Spec.Rsa.precomputedWords (s.gpr .x3).toNat) := by
  have hle : Spec.Rsa.precomputedWords (s.gpr .x3).toNat ≤ (stackArg s 14).toNat := by
    rw [hx.prl]; unfold Spec.Rsa.privatePrecomputedWords; omega_using []
  have hpw := hx.wpr
  have h12 := he 12 (by decide)
  simp only [Nat.reduceAdd] at h12
  rw [h12, ha.x3]
  exact words_frame ha.mem (hx.kpr.sub_right (by
    simpa using Offset.sub_base (stackArg s 13) (d := 0) (n := Spec.Rsa.precomputedWords (s.gpr .x3).toNat * 8)
      (k := (stackArg s 14).toNat * 8) (by omega_using [hle]))) (by omega_using [hle, hpw])

theorem callP_ct (c : PrivPChecked) :
    RelCT isa (Two (At c.stack (XP c.stack) (JC 14))) (.call c.name c.code) fun _ _ => True := by
  refine privPCallCT c fun t₁ t₂ ⟨a, ⟨s₁, h₁, em₁, c₁, x₁⟩, ⟨s₂, h₂, em₂, c₂, x₂⟩⟩ => ?_
  refine ⟨privPOk_of c h₁.1 h₁.2.2.1 c₁ x₁, privPOk_of c h₂.1 h₂.2.2.1 c₂ x₂,
    ⟨?_, fun r hr => ?_, fun i hi => ?_⟩, ?_, ?_, ?_⟩
  · rw [c₁.sp, c₂.sp, h₁.fb, h₂.fb]
  · have e : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x7], s₁.gpr r = s₂.gpr r :=
      fun r hr => (h₁.gpr hr).trans (h₂.gpr hr).symm
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [c₁.x0, c₂.x0, e .x0 (by decide)]
    · rw [c₁.x1, c₂.x1, e .x1 (by decide)]
    · rw [c₁.x2, c₂.x2, e .x2 (by decide)]
    · rw [c₁.x3, c₂.x3, e .x3 (by decide)]
    · rw [c₁.x4, c₂.x4, e .x4 (by decide)]
    · rw [c₁.x5, c₂.x5, e .x5 (by decide)]
    · rw [c₁.x6, c₂.x6, h₁.fb, h₂.fb]
    · rw [c₁.x7, c₂.x7, e .x3 (by decide)]
  · rw [x₁ i hi, x₂ i hi]
    rcases (by omega_using [hi] : i + 1 < 13 ∨ i = 12 ∨ i = 13) with h | rfl | rfl
    · rw [h₁.2.1.args (i + 1) h, h₂.2.1.args (i + 1) h]
    · exact h₁.2.2.2.1.trans h₂.2.2.2.1.symm
    · exact h₁.2.2.2.2.1.trans h₂.2.2.2.2.1.symm
  · rw [c₁.x2, c₁.x3, c₂.x2, c₂.x3, bytes_frame c₁.mem h₁.1.kn (by have := h₁.1.wn; omega_using []),
      bytes_frame c₂.mem h₂.1.kn (by have := h₂.1.wn; omega_using []), h₁.2.1.bn, h₂.2.1.bn]
  · rw [c₁.x4, c₁.x5, c₂.x4, c₂.x5, bytes_frame c₁.mem h₁.1.ke (by have := h₁.1.we; omega_using []),
      bytes_frame c₂.mem h₂.1.ke (by have := h₂.1.we; omega_using []), h₁.2.1.be, h₂.2.1.be]
  · rw [preWords_call h₁.2.2.1 c₁ x₁, preWords_call h₂.2.2.1 c₂ x₂]
    exact h₁.2.2.2.2.2.trans h₂.2.2.2.2.2.symm

theorem codeP_constantTime (c : PrivPChecked) :
    ConstantTime isa (Spec.RsaPkcs1Sig.signPrecomputedContract abi (stk c.stack)).pre
      (Spec.RsaPkcs1Sig.signPrecomputedContract abi (stk c.stack)).pub (codeP c.name c.code) :=
  RelCT.constantTime ((codeN_ct (X := XP c.stack) (fun _ _ h => argsOkP h.2.2.1) (by decide) (by decide)
    (fun _ _ h _ _ ht he => callP_ok c h.1 h.2.2.1 ht he) callArgsP_taint (callP_ct c)).mono
    (fun s₁ _ ⟨h₁, h₂, hp⟩ =>
      ⟨s₁, ⟨(preSP_of h₁).1, PubS.refl s₁, (preSP_of h₁).2, rfl, rfl, rfl⟩,
        (preSP_of h₂).1, (pubSP_of hp).1, (preSP_of h₂).2, (pubSP_of hp).2⟩) fun _ _ h => h)

theorem signPrecomputed_verified (c : PrivPChecked) :
    Verified AArch64.target (codeP c.name c.code) (Spec.RsaPkcs1Sig.signPrecomputedContract abi (stk c.stack)) :=
  ⟨codeP_correct c, codeP_constantTime c, satisfiablePre c.stack c.le⟩

end VG.Proof.RsaPkcs1Sig.AArch64.Sgn
