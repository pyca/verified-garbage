module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.Contract
public import VerifiedGarbage.Impl.RsaPkcs1Enc.X86.Front
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecP.Verified
public import VerifiedGarbage.Proof.RsaPss.X86.VfPass
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.RsaOaep.X86.Dec.Verified
import VerifiedGarbage.Proof.Framework.ReadHalves
meta import VerifiedGarbage.Impl.RsaPkcs1Enc.X86.Front
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.Contract

/-!
# `vg_rsa_pkcs1_decrypt_precomputed_front` on x86 (32-bit)

`Front.code` (`Impl/RsaPkcs1Enc/X86/Front.lean`) against
`Spec.RsaPkcs1Enc.decryptPrecomputedFrontContract` with 3732 bytes of stack
(`front_verified`), for any callee verified against
`Proof.RsaPkcs1Enc.decryptPrecomputedContract` with 3568 (`specP`) that never
writes `esp` and uses at most that stack: its proof is used only through
that contract.

The body runs in the frames of the x86 RSA padding functions (`wrap`,
`wrap_ok`, `wrap_ct`), with the layout `layF`: x86 PKCS#1 decryption's
public parameters (`EP`, `fp`), with our frame of 144 bytes and the 3572
bytes below it that the call uses. Its pieces are proven correct and
constant time at once (`VP`, `Proof/RsaPkcs1Sig/X86/Vp.lean`).

**The call.** `setup` copies our 25 arguments to the frame's first 25 words
(`copies_wp`), which the callee, entered 4 bytes below the frame, finds as
its own: its precondition (`dec_pre`), with the buffers' regions and the
copies, and its stack within the 3572 bytes below the frame; its public data
(`dec_pub`), `n`, `e` and the first words of `pre` (the modulus' values,
`preModulus`), the same in two runs; and its postcondition (`dec_post`),
`writtenMsg` of the decryption of the entry's bytes (`Res`, `call_vp`).

**After the call.** In RSAES-OAEP's frame and layout of `scratch` (`Geo`,
`Ctx`, `Proof/RsaPss/X86/`): the result to `sRet` and `scratch` to `ebp`
(`after_vp`), the buffer cleared (`clear_vp`), `out` copied to it
(`copyIn_vp`), shifted by `k - L` in eleven passes (`shift_vp`, with
RSASSA-PSS's `pass_vp`), which leaves the message and zeros, and copied back
(`copyOut_vp`, `ret_vp`), each keeping the result's slot, `out` and
`*msg_len` while it does not write them (`Kp`, `Kq`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Front

open VG VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPkcs1Enc.X86.Dec
open VG.X86 hiding frameBytes
open VG.X86.Wp
open VG.Impl.RsaPss.X86 (frameBytes copyArg)
open VG.Impl.RsaPkcs1Enc.X86.Front (setup)

/-! ## The entry -/

/-- The stack the function uses: the push, the frame, the call's return
address and the callee's. -/
abbrev stackF : Nat := 16 + frameBytes + 3572

/-- The contract, with that stack. -/
abbrev specF : Contract isa := Spec.RsaPkcs1Enc.decryptPrecomputedFrontContract abi stackF

/-- The public parameters of an entry state, with our frame's base. -/
def fp (s : State) : EP := { ep s with B := s.gpr .esp - BitVec.ofNat 32 16 - BitVec.ofNat 32 frameBytes }

/-- Our layout: the frame of `frameBytes` bytes, and the 3572 bytes below it
that the call's return address and the callee use. -/
abbrev layF (P : EP) (pre : BitVec 32) (L : Nat) : Lay where
  B := P.B
  F := frameBytes
  argv := P.argvP pre L
  ro := P.roP pre L
  rw := P.rw
  C := 3572

theorem fp_layF (s : State) (pre : BitVec 32) (L : Nat) :
    layF (fp s) pre L = layOf frameBytes ((fp s).argvP pre L) ((fp s).roP pre L) (fp s).rw s 3572 := rfl

variable {P : EP} {pre : BitVec 32} {L : Nat}

/-- The state the body starts from. -/
structure InF (P : EP) (pre : BitVec 32) (L : Nat) (σ : State) : Prop where
  ok : (layF P pre L).Ok σ
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
  lenEq : L = Spec.Rsa.privatePrecomputedWords P.K P.pl P.ql
  key : Spec.Rsa.privatePrecompute P.nB (pB P σ) (qB P σ) = some (Spec.Rsa.wordsAt σ.mem (pre.setWidth 64) L)

/-- A state of the body. -/
abbrev SF (P : EP) (pre : BitVec 32) (L : Nat) (σ s : State) : Prop := InF P pre L σ ∧ (layF P pre L).St σ s

theorem in_of_preF {s : State} (h : specF.pre s) :
    InF (fp s) (arg s 23) (arg s 24).toNat (entered frameBytes s) := by
  sig_pre [Spec.RsaPkcs1Enc.decryptPrecomputedFrontContract, Spec.RsaPkcs1Enc.decryptPrecomputedFrontSig,
    abi, argSlots, argVal, argBytes, stackBelow] at h
  obtain ⟨olk, ilk, dpl, qil, dql⟩ : (arg s 1).toNat = (arg s 4).toNat ∧ (arg s 10).toNat = (arg s 4).toNat ∧
      (arg s 16).toNat = (arg s 12).toNat ∧ (arg s 20).toNat = (arg s 12).toNat ∧
      (arg s 18).toNat = (arg s 14).toNat := by
    sig_split h
    rename_i hsp hsa hrd hwr oM oN oE oD oI oP oQ oDP oDQ oQI oS oPre oA mN mE mD mI mP mQ mDP mDQ mQI mS mPre mA
      nS nA eS eA dS dA iS iA pS pA qS qA dpS dpA dqS dqA qiS qiA sPre sA preA
      rO rM rN rE rD rI rP rQ rDP rDQ rQI rS rPre rA kO kM kN kE kD kI kP kQ kDP kDQ kQI kS kPre kA
      fO fM fN fE fD fI fP fQ fDP fDQ fQI fS fPre kv olk ilk el1 elK dl1 dlK
      pl1 plK ql1 qlK dpl qil dql slK plen
    exact ⟨olk, ilk, dpl, qil, dql⟩
  have a1 : arg s 1 = arg s 4 := BitVec.eq_of_toNat_eq olk
  have a10 : arg s 10 = arg s 4 := BitVec.eq_of_toNat_eq ilk
  have a16 : arg s 16 = arg s 12 := BitVec.eq_of_toNat_eq dpl
  have a20 : arg s 20 = arg s 12 := BitVec.eq_of_toNat_eq qil
  have a18 : arg s 18 = arg s 14 := BitVec.eq_of_toNat_eq dql
  rw [olk, ilk, dpl, qil, dql] at h
  simp only [stackF, frameBytes, Nat.reduceAdd] at h
  sig_split h
  rename_i hsp hsa hrd hwr oM oN oE oD oI oP oQ oDP oDQ oQI oS oPre oA mN mE mD mI mP mQ mDP mDQ mQI mS mPre mA
    nS nA eS eA dS dA iS iA pS pA qS qA dpS dpA dqS dqA qiS qiA sPre sA preA
    rO rM rN rE rD rI rP rQ rDP rDQ rQI rS rPre rA kO kM kN kE kD kI kP kQ kDP kDQ kQI kS kPre kA
    fO fM fN fE fD fI fP fQ fDP fDQ fQI fS fPre kv _ _ el1 elK dl1 dlK
    pl1 plK ql1 qlK _ _ _ slK plen
  have h16 : 4 * Impl.RsaPkcs1Sig.X86.savedRegs.length ≤ (s.gpr .esp).toNat := by
    simp only [Impl.RsaPkcs1Sig.X86.savedRegs, List.length_cons, List.length_nil]; omega_arith
  have hpush : Frame [below (s.gpr .esp) (4 * Impl.RsaPkcs1Sig.X86.savedRegs.length)] s.mem
      (entered frameBytes s).mem :=
    pushed_frame (by decide) h16
  have below16 : Region.Sub (below (s.gpr .esp) (4 * Impl.RsaPkcs1Sig.X86.savedRegs.length))
      ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 3732, 3732⟩ := by
    simp only [below, Impl.RsaPkcs1Sig.X86.savedRegs, List.length_cons, List.length_nil]
    rw [Taint.sub_setWidth (by omega_arith)]
    exact Offset.sub_below _ (by omega_arith) (by omega_arith)
  have sl32 : (arg s 22).toNat < 2 ^ 32 := (arg s 22).isLt
  have bytesE := fun {x : BitVec 32} {k : Nat}
      (hk : (⟨(s.gpr .esp).setWidth 64 - 3732#64, 3732⟩ : Region).Disjoint ⟨x.setWidth 64, k⟩) (hl : k ≤ 2 ^ 64) =>
    Proof.RsaPkcs1Sig.bytesAt_frame hpush (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hk.sub_left below16).symm) hl
  have ok : (layF (fp s) (arg s 23) (arg s 24).toNat).Ok (entered frameBytes s) := by
    rw [fp_layF]
    refine ok_entered (S := 3732) rfl (by decide) hsp (by simp) (by simp; omega_arith) hrd
      (by rw [hwr]; rfl) ?_ ?_ ?_ ?_ ?_ ?_
    · intro r hr
      simp only [EP.roP, EP.rw, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [kN, kE, kD, kI, kP, kQ, kDP, kDQ, kQI, kPre, kO, kM, kS]
    · intro r hr
      simp only [EP.rw, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [rO, rM, rS]
    · intro w hw r hr
      simp only [EP.rw, List.mem_cons, List.not_mem_nil, or_false] at hw
      simp only [EP.roP, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hw with rfl | rfl | rfl <;>
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [oN, oE, oD, oI, oP, oQ, oDP, oDQ, oQI, oPre, oA, mN, mE, mD, mI, mP, mQ, mDP, mDQ, mQI, mPre, mA,
        nS.symm, eS.symm, dS.symm, iS.symm, pS.symm, qS.symm, dpS.symm, dqS.symm, qiS.symm, sPre, sA]
    · refine List.Pairwise.cons ?_ (List.pairwise_pair.mpr mS)
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [oM, oS]
    · intro r hr
      simp only [EP.roP, EP.rw, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp only [fp, ep, BitVec.toNat_setWidth]
      all_goals first
        | (rw [Nat.mod_eq_of_lt (by have := (arg s 3).isLt; omega_arith)]; omega_arith)
        | (rw [Nat.mod_eq_of_lt (by have := (arg s 5).isLt; omega_arith)]; omega_arith)
        | (rw [Nat.mod_eq_of_lt (by have := (arg s 7).isLt; omega_arith)]; omega_arith)
        | (rw [Nat.mod_eq_of_lt (by have := (arg s 9).isLt; omega_arith)]; omega_arith)
        | (rw [Nat.mod_eq_of_lt (by have := (arg s 11).isLt; omega_arith)]; omega_arith)
        | (rw [Nat.mod_eq_of_lt (by have := (arg s 13).isLt; omega_arith)]; omega_arith)
        | (rw [Nat.mod_eq_of_lt (by have := (arg s 15).isLt; omega_arith)]; omega_arith)
        | (rw [Nat.mod_eq_of_lt (by have := (arg s 17).isLt; omega_arith)]; omega_arith)
        | (rw [Nat.mod_eq_of_lt (by have := (arg s 19).isLt; omega_arith)]; omega_arith)
        | (rw [Nat.mod_eq_of_lt (by have := (arg s 23).isLt; omega_arith)]; omega_arith)
        | (rw [Nat.mod_eq_of_lt (by have := (arg s 0).isLt; omega_arith)]; omega_arith)
        | (rw [Nat.mod_eq_of_lt (by have := (arg s 2).isLt; omega_arith)]; omega_arith)
        | (rw [Nat.mod_eq_of_lt (by have := (arg s 21).isLt; omega_arith)]; omega_arith)
    · simp only [fp, ep, EP.argvP, List.length_cons, List.length_nil, Nat.zero_add,
        Nat.reduceAdd, Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, implies_true,
        List.getD_cons_zero, List.getD_cons_succ, BitVec.ofNat_toNat, BitVec.setWidth_eq, a1, a10, a16, a18, a20,
        and_self]
  have hn := bytesE kN (by have := (arg s 4).isLt; omega_using [])
  have hp := bytesE kP (by have := (arg s 12).isLt; omega_using [])
  have hq := bytesE kQ (by have := (arg s 14).isLt; omega_using [])
  have he := bytesE kE (by have := (arg s 6).isLt; omega_using [])
  have hw : Spec.Rsa.wordsAt (entered frameBytes s).mem ((arg s 23).setWidth 64) (arg s 24).toNat =
      Spec.Rsa.wordsAt s.mem ((arg s 23).setWidth 64) (arg s 24).toNat :=
    Proof.Rsa.wordsAt_frame hpush (by omega_arith) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [show 8 * (arg s 24).toNat = (arg s 24).toNat * 8 from Nat.mul_comm _ _]
      exact (kPre.sub_left below16).symm)
  refine ⟨ok, kv, el1, elK, dl1, dlK, pl1, plK, ql1, qlK, slK, sl32, hn, he, plen, ?_⟩
  change Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat)
    (Spec.Rsa.bytesAt (entered frameBytes s).mem ((arg s 11).setWidth 64) (arg s 12).toNat)
    (Spec.Rsa.bytesAt (entered frameBytes s).mem ((arg s 13).setWidth 64) (arg s 14).toNat) =
    some (Spec.Rsa.wordsAt (entered frameBytes s).mem ((arg s 23).setWidth 64) (arg s 24).toNat)
  rw [hp, hq, hw]
  exact h

/-! ## The call's arguments -/

/-- The first `k` of our arguments copied to the frame. -/
def Slots (P : EP) (pre : BitVec 32) (L : Nat) (m : Mem) (k : Nat) : Prop :=
  ∀ i < k, m.readW ((layF P pre L).fr (4 * i)) 32 = (P.argvP pre L).getD i 0

/-- Before the call. -/
def R1 (P : EP) (pre : BitVec 32) (L : Nat) (σ s : State) : Prop := SF P pre L σ s ∧ Slots P pre L s.mem 25

theorem copy_step {σ s : State} {i : Nat} (h : SF P pre L σ s) (hs : Slots P pre L s.mem i) (hi : i < 25)
    {is : List Instr} {Q : State → Prop}
    (kk : ∀ t, SF P pre L σ t → Slots P pre L t.mem (i + 1) → WP isa (.block is) t Q) :
    WP isa (.block (copyArg i i ++ is)) s Q := by
  refine h.2.wp_arg (j := i) (by simp only [EP.argvP, List.length_cons, List.length_nil]; omega_using [hi])
    (by decide) fun t1 s1 u1 => ?_
  refine s1.wp_strFr (d := 4 * i) (by show 4 * i + 4 ≤ frameBytes; simp only [frameBytes]; omega_using [hi])
    fun t2 s2 m2 => kk t2 ⟨h.1, s2⟩ ?_
  intro k hk
  rw [m2.mem]
  rcases (by omega_using [hk] : k = i ∨ k < i) with rfl | hki
  · rw [Mem.readW_writeW_self32, u1.gpr]
  · rw [Lay.readW_fr_other _ _ _ (by omega_using [hki]) (by omega_using [hi, hk]) (by omega_using [hi]), u1.mem]
    exact hs k hki

theorem copies_wp {σ : State} : ∀ k ≤ 25, ∀ s, SF P pre L σ s →
    WP isa (.block ((List.range k).flatMap fun j => copyArg j j)) s
      (fun t => SF P pre L σ t ∧ Slots P pre L t.mem k)
  | 0, _, s, h => WP.block_nil ⟨h, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  | k + 1, hk, s, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (copies_wp k (by omega_using [hk]) s h) fun t ⟨ht, z⟩ => ?_)
    rw [← List.append_nil (copyArg k k)]
    exact copy_step ht z (by omega_using [hk]) fun u hu zu => WP.block_nil ⟨hu, zu⟩

theorem setup_taint : TaintOk [.esp] (.block setup) := ⟨_, by taint_decide⟩

theorem setup_vp : VP (SF P pre L) (.block setup) (R1 P pre L) :=
  VP.taint [.esp] setup_taint (fun _ _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    rw [h₁.2.sp, h₂.2.sp]) fun _ s h => copies_wp 25 (Nat.le_refl _) s h

/-! ## The call -/

/-- The buffers the callee writes, and the copies of its arguments. -/
abbrev decWr (P : EP) : List Region := [P.OUT, P.ML, P.SCR, ⟨P.B.setWidth 64, 100⟩]

theorem InF.fit {σ : State} (h : InF P pre L σ) : P.B.toNat + 264 ≤ 2 ^ 32 := by
  have := h.ok.fit
  simp only [Lay.A, EP.argvP, List.length_cons, List.length_nil, frameBytes] at this
  omega_using [this]

theorem InF.BC {σ : State} (h : InF P pre L σ) : 3572 ≤ P.B.toNat := h.ok.BC

theorem R1.arg {σ s : State} (h : R1 P pre L σ s) (rd wr : List Region) {i : Nat} (hi : i < 25) :
    VG.X86.arg (s.callEntry.withRegions rd wr) i = (P.argvP pre L).getD i 0 := by
  have fit := h.1.1.fit
  have bc := h.1.1.BC
  have hsp : s.gpr .esp = P.B := h.1.2.sp
  rw [arg_withRegions, arg_callEntry (by rw [hsp]; omega_using [bc]) (by rw [hsp]; omega_using [fit, hi])]
  have hd : 4 * i < (layF P pre L).F + 20 + (layF P pre L).A := by
    simp only [Lay.A, EP.argvP, List.length_cons, List.length_nil, frameBytes]; omega_using [hi]
  rw [show (s.gpr .esp + BitVec.ofNat 32 (4 * i)).setWidth 64 = addr (s.gpr .esp) (4 * i) from rfl, hsp,
    h.1.1.ok.addrB hd]
  exact h.2 i hi

theorem SF.callWords {σ s : State} (hs : SF P pre L σ s) :
    Spec.Rsa.wordsAt s.callEntry.mem (pre.setWidth 64) L = Spec.Rsa.wordsAt σ.mem (pre.setWidth 64) L := by
  have fit : (pre.setWidth 64).toNat + 8 * L ≤ 2 ^ 32 := by
    have := hs.1.ok.fits (preR pre L) (List.mem_append_left _ (by simp))
    simp only at this; omega_using [this]
  have sep : ∀ r ∈ (layF P pre L).W, (⟨pre.setWidth 64, 8 * L⟩ : Region).Disjoint r := by
    rw [show 8 * L = L * 8 from Nat.mul_comm _ _]
    exact lay_ro_apart hs.1.ok (R := preR pre L) (by simp)
  rw [Proof.Rsa.wordsAt_frame (hs.2.callEntry_frame (by show (4 : Nat) ≤ 3572; decide)) (by omega_using [fit]) (by
      intro r hr; obtain rfl := List.mem_singleton.mp hr
      exact sep _ (by simp [Lay.W])),
    Proof.Rsa.wordsAt_frame hs.2.frame (by omega_using [fit]) sep]

theorem SF.callRo {σ s : State} (hs : SF P pre L σ s) {R : Region} (hR : R ∈ (layF P pre L).ro) :
    Spec.Rsa.bytesAt s.callEntry.mem R.base R.len = Spec.Rsa.bytesAt σ.mem R.base R.len :=
  hs.2.callEntry_ro (by show (4 : Nat) ≤ 3572; decide) hR

/-- The callee's precondition. -/
theorem dec_pre {σ s : State} (h : R1 P pre L σ s) :
    specP.pre (s.callEntry.withRegions (P.roP pre L) (decWr P)) := by
  have hin := h.1.1
  have ok := hin.ok
  have hsp : s.gpr .esp = P.B := h.1.2.sp
  have fit := hin.fit
  have bc := hin.BC
  have k32 : P.K < 2 ^ 32 := by have := hin.kv.2; omega_using [this]
  have el32 : P.el < 2 ^ 32 := by have := hin.elK; omega_using [k32, this]
  have dl32 : P.dl < 2 ^ 32 := by have := hin.dlK; omega_using [k32, this]
  have pl32 : P.pl < 2 ^ 32 := by have := hin.plK; omega_using [k32, this]
  have ql32 : P.ql < 2 ^ 32 := by have := hin.qlK; omega_using [k32, this]
  have L32 : L < 2 ^ 32 := by
    have e := hin.lenEq
    have := hin.plK; have := hin.qlK; have := hin.kv.2
    simp only [Spec.Rsa.privatePrecomputedWords, Spec.Rsa.precomputedWords, Spec.Rsa.primeWords,
      Spec.Rsa.modulusWords] at e
    omega_arith
  have sl32 := hin.sl32
  have a := fun {i} (hi : i < 25) => h.arg (P.roP pre L) (decWr P) hi
  have e4 : (P.B - 4).toNat = P.B.toNat - 4 := sub_toNat (k := 4) (by omega_using [bc])
  have key : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.callEntry.mem (P.n.setWidth 64) P.K)
      (Spec.Rsa.bytesAt s.callEntry.mem (P.p.setWidth 64) P.pl)
      (Spec.Rsa.bytesAt s.callEntry.mem (P.q.setWidth 64) P.ql) =
      some (Spec.Rsa.wordsAt s.callEntry.mem (pre.setWidth 64) L) := by
    rw [h.1.callWords, h.1.callRo (R := P.N) (by simp), h.1.callRo (R := P.PP) (by simp),
      h.1.callRo (R := P.QQ) (by simp)]
    have k := hin.key
    rw [← hin.nB] at k
    exact k
  rw [State.callEntry_mem, hsp] at key
  have lenEq := hin.lenEq
  have args0 : (⟨P.B.setWidth 64, 100⟩ : Region) = ⟨(layF P pre L).fr 0, 100⟩ := by simp
  have fA : ∀ R, R ∈ (layF P pre L).ro ∨ R ∈ (layF P pre L).rw →
      (⟨P.B.setWidth 64, 100⟩ : Region).Disjoint R := fun R hR => by
    rw [args0]; exact ok.stk_fr hR (by simp only [frameBytes]; omega_using [])
  have dW : ∀ w ∈ decWr P, ∀ r ∈ P.roP pre L, w.Disjoint r := by
    intro w hw r hr
    have hr' : r ∈ (layF P pre L).ro := hr
    simp only [decWr, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact ok.rw_ro (w := P.OUT) (by simp) hr'
    · exact ok.rw_ro (w := P.ML) (by simp) hr'
    · exact ok.rw_ro (w := P.SCR) (by simp) hr'
    · exact fA r (.inl hr')
  have dWW : (decWr P).Pairwise Region.Disjoint := by
    have ww := ok.wrw
    simp only [EP.rw, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true] at ww
    simp only [decWr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨⟨ww.1.1, ww.1.2, (fA P.OUT (.inr (by simp))).symm⟩, ⟨ww.2.1, (fA P.ML (.inr (by simp))).symm⟩,
      (fA P.SCR (.inr (by simp))).symm, fun _ h => h.elim⟩
  have dLow : ∀ r ∈ decWr P ++ P.roP pre L, Region.Disjoint (below P.B 3572) r := by
    intro r hr
    rw [show P.B = (layF P pre L).B from rfl, ok.low_eq]
    rcases List.mem_append.mp hr with hr | hr
    · simp only [decWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ok.low_buf (R := P.OUT) (.inr (by simp))
      · exact ok.low_buf (R := P.ML) (.inr (by simp))
      · exact ok.low_buf (R := P.SCR) (.inr (by simp))
      · rw [args0]; exact (Lay.fr_low (by omega_using []) (by show (3572 : Nat) ≤ 2 ^ 32; decide)).symm
    · exact ok.low_buf (.inl hr)
  have fits : ∀ r ∈ decWr P ++ P.roP pre L, r.base.toNat + r.len ≤ 2 ^ 32 := by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · simp only [decWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ok.fits P.OUT (by simp)
      · exact ok.fits P.ML (by simp)
      · exact ok.fits P.SCR (by simp)
      · show (P.B.setWidth 64).toNat + 100 ≤ 2 ^ 32
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := P.B.isLt; omega_using [])]
        omega_using [fit]
    · exact ok.fits _ (List.mem_append_left _ hr)
  have ret : Region.Sub ⟨(P.B - 4).setWidth 64, 4⟩ (below P.B 3572) := below_sub (by decide) bc
  have low : Region.Sub ⟨(P.B - 4).setWidth 64 - BitVec.ofNat 64 3568, 3568⟩ (below P.B 3572) := by
    rw [← Taint.sub_setWidth (by omega_using [bc, e4])]
    exact below_inner (by decide) bc
  have dWs := fun (w : Region) hw (r : Region) hr => (dW w hw r hr).symm
  have loR := fun (r : Region) hr => (dLow r hr).sub_left ret
  have loL := fun (r : Region) hr => (dLow r hr).sub_left low
  sig_pre [Proof.RsaPkcs1Enc.decryptPrecomputedContract, Proof.RsaPkcs1Enc.decryptPrecomputedSig,
    Proof.RsaPkcs1Enc.decryptSig, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [a (by decide : 0 < 25), a (by decide : 1 < 25), a (by decide : 2 < 25), a (by decide : 3 < 25),
    a (by decide : 4 < 25), a (by decide : 5 < 25), a (by decide : 6 < 25), a (by decide : 7 < 25),
    a (by decide : 8 < 25), a (by decide : 9 < 25), a (by decide : 10 < 25), a (by decide : 11 < 25),
    a (by decide : 12 < 25), a (by decide : 13 < 25), a (by decide : 14 < 25), a (by decide : 15 < 25),
    a (by decide : 16 < 25), a (by decide : 17 < 25), a (by decide : 18 < 25), a (by decide : 19 < 25),
    a (by decide : 20 < 25), a (by decide : 21 < 25), a (by decide : 22 < 25), a (by decide : 23 < 25),
    a (by decide : 24 < 25),
    EP.argvP, List.getD_cons_zero, List.getD_cons_succ,
    BitVec.toNat_ofNat, Nat.reducePow,
    Nat.mod_eq_of_lt (show P.K < 4294967296 by omega_using [k32]),
    Nat.mod_eq_of_lt (show P.el < 4294967296 by omega_using [el32]),
    Nat.mod_eq_of_lt (show P.dl < 4294967296 by omega_using [dl32]),
    Nat.mod_eq_of_lt (show P.pl < 4294967296 by omega_using [pl32]),
    Nat.mod_eq_of_lt (show P.ql < 4294967296 by omega_using [ql32]),
    Nat.mod_eq_of_lt (show P.sl < 4294967296 by omega_using [sl32]),
    Nat.mod_eq_of_lt (show L < 4294967296 by omega_using [L32]),
    argAddr_withRegions, argAddr_callEntry, Nat.mul_zero, BitVec.add_zero, hsp, e4, stackBytes,
    Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes, Nat.reduceAdd]
  simp only [decWr, EP.roP, preR, List.cons_append, List.nil_append, List.pairwise_cons, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, forall_false,
    implies_true, BitVec.toNat_setWidth_32_64, Nat.reducePow] at dW dWs dWW loR loL fits
  simp only [dW, dWs, dWW, loR, loL, fits, key, hin.kv, hin.el1, hin.elK, hin.dl1, hin.dlK, hin.pl1, hin.plK,
    hin.ql1, hin.qlK, hin.slK, ← lenEq, and_true]
  exact ⟨by omega_using [bc], by omega_using [fit]⟩

theorem SF.callWordsN {σ s : State} (hs : SF P pre L σ s) {n : Nat} (hn : n ≤ L) :
    Spec.Rsa.wordsAt s.callEntry.mem (pre.setWidth 64) n = Spec.Rsa.wordsAt σ.mem (pre.setWidth 64) n := by
  have fit : (pre.setWidth 64).toNat + 8 * L ≤ 2 ^ 32 := by
    have := hs.1.ok.fits (preR pre L) (List.mem_append_left _ (by simp))
    simp only at this; omega_using [this]
  have sep : ∀ r ∈ (layF P pre L).W, (⟨pre.setWidth 64, 8 * n⟩ : Region).Disjoint r := fun r hr =>
    ((lay_ro_apart hs.1.ok (R := preR pre L) (by simp) r hr).sub_left (Region.sub_prefix (by omega_using [hn])))
  rw [Proof.Rsa.wordsAt_frame (hs.2.callEntry_frame (by show (4 : Nat) ≤ 3572; decide))
      (by omega_using [fit, hn]) (by
      intro r hr; obtain rfl := List.mem_singleton.mp hr
      exact sep _ (by simp [Lay.W])),
    Proof.Rsa.wordsAt_frame hs.2.frame (by omega_using [fit, hn]) sep]

/-- The callee's public data. -/
theorem dec_pub {σ₁ σ₂ s₁ s₂ : State} (h₁ : R1 P pre L σ₁ s₁) (h₂ : R1 P pre L σ₂ s₂) (rd wr : List Region) :
    specP.pub (s₁.callEntry.withRegions rd wr) (s₂.callEntry.withRegions rd wr) := by
  have hin₁ := h₁.1.1
  have k32 : P.K < 2 ^ 32 := by have := hin₁.kv.2; omega_using [this]
  have a₁ := fun {i} (hi : i < 25) => h₁.arg rd wr hi
  have a₂ := fun {i} (hi : i < 25) => h₂.arg rd wr hi
  have hsp : s₁.gpr .esp = s₂.gpr .esp := by rw [h₁.1.2.sp, h₂.1.2.sp]
  -- `pre`'s first words, which the callee leaks, are the modulus' values in both runs.
  have lw : ∀ {σ s : State}, R1 P pre L σ s →
      some (Spec.Rsa.wordsAt s.callEntry.mem (pre.setWidth 64) (Spec.Rsa.precomputedWords P.K)) =
        Spec.Rsa.publicPrecompute P.nB := by
    intro σ s h
    have k := preModulus h.1.1.key
    have hl : P.nB.length = P.K := by rw [← h.1.1.nB, Proof.RsaPkcs1Sig.bytesAt_len]
    rw [hl] at k
    have hle : Spec.Rsa.precomputedWords P.K ≤ L := by
      rw [h.1.1.lenEq]; unfold Spec.Rsa.privatePrecomputedWords; omega_using []
    rw [h.1.callWordsN hle]
    exact k
  have hw := Option.some.inj ((lw h₁).trans (lw h₂).symm)
  have hn₁ : Spec.Rsa.bytesAt s₁.callEntry.mem (P.n.setWidth 64) P.K = P.nB :=
    (h₁.1.callRo (R := P.N) (by simp)).trans hin₁.nB
  have hn₂ : Spec.Rsa.bytesAt s₂.callEntry.mem (P.n.setWidth 64) P.K = P.nB :=
    (h₂.1.callRo (R := P.N) (by simp)).trans h₂.1.1.nB
  have he₁ : Spec.Rsa.bytesAt s₁.callEntry.mem (P.e.setWidth 64) P.el = P.eB :=
    (h₁.1.callRo (R := P.E) (by simp)).trans hin₁.eB
  have he₂ : Spec.Rsa.bytesAt s₂.callEntry.mem (P.e.setWidth 64) P.el = P.eB :=
    (h₂.1.callRo (R := P.E) (by simp)).trans h₂.1.1.eB
  sig_pub [Proof.RsaPkcs1Enc.decryptPrecomputedContract, Proof.RsaPkcs1Enc.decryptPrecomputedSig,
    Proof.RsaPkcs1Enc.decryptSig, abi, argSlots, argVal, argBytes]
  simp only [a₁ (by decide : 0 < 25), a₂ (by decide : 0 < 25), a₁ (by decide : 1 < 25), a₂ (by decide : 1 < 25),
    a₁ (by decide : 2 < 25), a₂ (by decide : 2 < 25), a₁ (by decide : 3 < 25), a₂ (by decide : 3 < 25),
    a₁ (by decide : 4 < 25), a₂ (by decide : 4 < 25), a₁ (by decide : 5 < 25), a₂ (by decide : 5 < 25),
    a₁ (by decide : 6 < 25), a₂ (by decide : 6 < 25), a₁ (by decide : 7 < 25), a₂ (by decide : 7 < 25),
    a₁ (by decide : 8 < 25), a₂ (by decide : 8 < 25), a₁ (by decide : 9 < 25), a₂ (by decide : 9 < 25),
    a₁ (by decide : 10 < 25), a₂ (by decide : 10 < 25), a₁ (by decide : 11 < 25), a₂ (by decide : 11 < 25),
    a₁ (by decide : 12 < 25), a₂ (by decide : 12 < 25), a₁ (by decide : 13 < 25), a₂ (by decide : 13 < 25),
    a₁ (by decide : 14 < 25), a₂ (by decide : 14 < 25), a₁ (by decide : 15 < 25), a₂ (by decide : 15 < 25),
    a₁ (by decide : 16 < 25), a₂ (by decide : 16 < 25), a₁ (by decide : 17 < 25), a₂ (by decide : 17 < 25),
    a₁ (by decide : 18 < 25), a₂ (by decide : 18 < 25), a₁ (by decide : 19 < 25), a₂ (by decide : 19 < 25),
    a₁ (by decide : 20 < 25), a₂ (by decide : 20 < 25), a₁ (by decide : 21 < 25), a₂ (by decide : 21 < 25),
    a₁ (by decide : 22 < 25), a₂ (by decide : 22 < 25), a₁ (by decide : 23 < 25), a₂ (by decide : 23 < 25),
    a₁ (by decide : 24 < 25), a₂ (by decide : 24 < 25),
    EP.argvP, List.getD_cons_zero, List.getD_cons_succ, and_true]
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt k32,
    Nat.mod_eq_of_lt (show P.el < 2 ^ 32 by have := hin₁.elK; omega_using [k32, this]),
    ← State.callEntry_mem s₁, ← State.callEntry_mem s₂]
  simp only [Spec.Rsa.privatePrecomputedLeak, hn₁, hn₂, he₁, he₂, hw, hsp, and_true]

/-- The callee's result: what it writes to `out` and `*msg_len`, and returns. -/
theorem dec_post {σ s t : State} (h : R1 P pre L σ s) {rd wr : List Region}
    (hp : specP.post (s.callEntry.withRegions rd wr) t) : Res P σ t.mem (t.gpr .eax) := by
  have hin := h.1.1
  have k32 : P.K < 2 ^ 32 := by have := hin.kv.2; omega_using [this]
  have a := fun {i} (hi : i < 25) => h.arg rd wr hi
  sig_post [Proof.RsaPkcs1Enc.decryptPrecomputedContract, Proof.RsaPkcs1Enc.decryptPrecomputedSig,
    Proof.RsaPkcs1Enc.decryptSig, abi, argSlots, argVal, argBytes] at hp
  simp only [a (by decide : 0 < 25), a (by decide : 2 < 25), a (by decide : 3 < 25), a (by decide : 4 < 25),
    a (by decide : 5 < 25), a (by decide : 6 < 25), a (by decide : 7 < 25), a (by decide : 8 < 25),
    a (by decide : 9 < 25), a (by decide : 11 < 25), a (by decide : 12 < 25), a (by decide : 13 < 25),
    a (by decide : 14 < 25), a (by decide : 15 < 25), a (by decide : 17 < 25), a (by decide : 19 < 25),
    EP.argvP, List.getD_cons_zero, List.getD_cons_succ, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.mod_eq_of_lt (show P.K < 4294967296 by omega_using [k32]),
    Nat.mod_eq_of_lt (show P.el < 4294967296 by have := hin.elK; omega_using [k32, this]),
    Nat.mod_eq_of_lt (show P.dl < 4294967296 by have := hin.dlK; omega_using [k32, this]),
    Nat.mod_eq_of_lt (show P.pl < 4294967296 by have := hin.plK; omega_using [k32, this]),
    Nat.mod_eq_of_lt (show P.ql < 4294967296 by have := hin.qlK; omega_using [k32, this])] at hp
  rw [BitVec.setWidth_append_eq_right, ← State.callEntry_mem] at hp
  have ro := fun {R : Region} (hR : R ∈ (layF P pre L).ro) => h.1.callRo hR
  rw [ro (R := P.N) (by simp), show Spec.Rsa.bytesAt σ.mem P.N.base P.N.len = P.nB from hin.nB,
    ro (R := P.E) (by simp), show Spec.Rsa.bytesAt σ.mem P.E.base P.E.len = P.eB from hin.eB,
    ro (R := P.D) (by simp), ro (R := P.INP) (by simp), ro (R := P.PP) (by simp), ro (R := P.QQ) (by simp),
    ro (R := P.DP) (by simp), ro (R := P.DQ) (by simp), ro (R := P.QI) (by simp)] at hp
  exact hp

/-- After the call. -/
def R2 (P : EP) (pre : BitVec 32) (L : Nat) (σ s : State) : Prop := SF P pre L σ s ∧ Res P σ s.mem (s.gpr .eax)

theorem call_vp {name : String} {c : Prog isa} (hv : Verified target c specP) (hns : NoSp c)
    (hst : stackUse c ≤ 3568) : VP (R1 P pre L) (.call name c) (R2 P pre L) := by
  refine VP.call hv.1 hv.2.1 hns (P.roP pre L) (decWr P) (fun σ s h => dec_pre h) (fun σ s h => ?_)
    (fun σ s h => ?_) (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.1.2.sp, h₂.1.2.sp])
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => dec_pub h₁ h₂ _ _) (fun σ s s' h rd wr cs fr po => ?_)
  · -- What the callee is given is ours.
    have hs := h.1
    have hro : ∀ R ∈ (layF P pre L).ro, Covers [R] (s.rd ++ s.wr) := fun R hR =>
      Covers.of_mem fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hs.2.inRo hR
    have hrw : ∀ R ∈ (layF P pre L).rw, Covers [R] s.wr := fun R hR =>
      Covers.of_mem fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hs.2.inRw hR
    have hA : Covers [⟨P.B.setWidth 64, 100⟩] s.wr := by
      have := hs.2.inFr (d := 0) (n := 100) (by simp only [frameBytes]; omega_using [])
      simp only [Lay.fr, BitVec.add_zero] at this
      exact Covers.one this
    have wr : Covers (decWr P) s.wr :=
      (hrw P.OUT (by simp)).cons ((hrw P.ML (by simp)).cons ((hrw P.SCR (by simp)).cons (hA.cons Covers.nil)))
    refine ⟨Covers.append_left ?_ wr.right, wr⟩
    refine (hro P.N (by simp)).cons ((hro P.E (by simp)).cons ((hro P.D (by simp)).cons
      ((hro P.INP (by simp)).cons ((hro P.PP (by simp)).cons ((hro P.QQ (by simp)).cons
      ((hro P.DP (by simp)).cons ((hro P.DQ (by simp)).cons ((hro P.QI (by simp)).cons
      ((hro (preR pre L) (by simp)).cons Covers.nil)))))))))
  · rw [show s.gpr .esp = P.B from h.1.2.sp]
    have := h.1.1.BC
    omega_using [hst, this]
  · -- After the call.
    have hh := h
    obtain ⟨hs, -⟩ := h
    have ok := hs.1.ok
    have hsp : s.gpr .esp = P.B := hs.2.sp
    have low : Region.Sub (below (s.gpr .esp) (stackUse c + 4)) (layF P pre L).LOW := by
      rw [hsp, ← show (layF P pre L).B = P.B from rfl, ← ok.low_eq]
      exact below_sub (by simp only; omega_using [hst]) ok.BC
    have st : (layF P pre L).St σ s' := hs.2.write fr (fun r hr => by
      simp only [decWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact ⟨P.OUT, by simp, fun _ h => h⟩
      · exact ⟨P.ML, by simp, fun _ h => h⟩
      · exact ⟨P.SCR, by simp, fun _ h => h⟩
      · refine ⟨(layF P pre L).FR, by simp, ?_⟩
        have : (⟨P.B.setWidth 64, 100⟩ : Region) = ⟨(layF P pre L).fr 0, 100⟩ := by simp
        rw [this]; exact Offset.sub_base _ (by simp only [frameBytes]; omega_using [])
      · exact ⟨(layF P pre L).LOW, by simp, low⟩) rd wr (cs .esp (by simp [calleeSaved]))
    refine ⟨⟨hs.1, st⟩, ?_⟩
    obtain ⟨s₂, m₂, g₂, po⟩ := po
    have := dec_post hh po
    rw [m₂, g₂ .eax (by decide)] at this
    exact this

/-! ## After the call -/

open VG.Proof.RsaPss.X86 (Geo Ctx sa slotR WBuf RBuf byteAt zero_vp copy_vp pass_vp slot_keep sbytes_keep sp_bp
  slot_frame slotSep maskOf contains_byte)
open VG.Impl.RsaPss.X86 (sA sD sPc oRsa ld st mi atS addi addSlot countLoop zeroLoop clrArgs arg passNext passBody)
open VG.Impl.RsaOaep.X86 (oBuf passOne passSet)
open VG.Impl.RsaPkcs1Enc.X86.Front (sRet after clearBuf inSet copyIn shInit shift outSet copyOut tail)
open VG.Proof.RsaOaep.X86.Dec (mask_bit mod_succ fr3 rd3)

/-- The callee's outcome. -/
abbrev oc (P : EP) (σ : State) : Spec.Rsa.Outcome :=
  Spec.RsaPkcs1Enc.decrypt P.nB P.eB (dB P σ) (pB P σ) (qB P σ) (dpB P σ) (dqB P σ) (qiB P σ) (cB P σ)

/-- An outcome's message, empty for an error. -/
def msgOf : Spec.Rsa.Outcome → List Byte
  | .ok M => M
  | _ => []

/-- An outcome's result. -/
def rOf : Spec.Rsa.Outcome → BitVec 32
  | .ok _ => 1
  | .invalid => 0
  | .fault => 2

/-- The message's length. -/
abbrev mlen (P : EP) (σ : State) : Nat := (msgOf (oc P σ)).length

/-- The distance the buffer is shifted by: the zeros before the message. -/
abbrev aV (P : EP) (σ : State) : Nat := P.K - mlen P σ

/-- `out`'s bytes after the call. -/
abbrev outB (P : EP) (σ : State) : List Byte := List.replicate (aV P σ) 0 ++ msgOf (oc P σ)

/-- Byte `j` of the buffer after the copy: `out`'s, zeros after it. -/
abbrev Bp (P : EP) (σ : State) (j : Nat) : Byte := if j < P.K then (outB P σ).getD j 0 else 0

theorem writtenMsg_parts {m : Mem} {out ml : Addr} {K : Nat} {r : BitVec 32} {o : Spec.Rsa.Outcome}
    (h : Proof.RsaPkcs1Enc.writtenMsg m out ml K r o) :
    r = rOf o ∧ Spec.Rsa.bytesAt m out K = List.replicate (K - (msgOf o).length) 0 ++ msgOf o ∧
      Spec.Rsa.wordsAt m ml 1 = [BitVec.ofNat 64 (msgOf o).length] := by
  cases o <;> simpa [Proof.RsaPkcs1Enc.writtenMsg, msgOf, rOf] using h

theorem writtenMsgFront_of {m : Mem} {out ml : Addr} {K : Nat} {r : BitVec 32} {o : Spec.Rsa.Outcome}
    (hr : r = rOf o) (hb : Spec.Rsa.bytesAt m out K = msgOf o ++ List.replicate (K - (msgOf o).length) 0)
    (hw : Spec.Rsa.wordsAt m ml 1 = [BitVec.ofNat 64 (msgOf o).length]) :
    Spec.RsaPkcs1Enc.writtenMsgFront m out ml K r o := by
  cases o <;> simp only [Spec.RsaPkcs1Enc.writtenMsgFront, msgOf, rOf, List.length_nil, Nat.sub_zero,
    List.nil_append, BitVec.ofNat_eq_ofNat] at hr hb hw ⊢ <;> exact ⟨hr, hb, hw⟩

theorem mlen_le {m : Mem} {out : Addr} {K : Nat} {l : List Byte}
    (h : Spec.Rsa.bytesAt m out K = List.replicate (K - l.length) 0 ++ l) : l.length ≤ K := by
  have := congrArg List.length h
  simp only [Proof.RsaPkcs1Sig.bytesAt_len, List.length_append, List.length_replicate] at this
  omega_arith

/-- What the code after the call keeps: the call's result in its slot,
`out` and `*msg_len` as the call left them. -/
structure Kp (P : EP) (pre : BitVec 32) (L : Nat) (σ : State) (m : Mem) : Prop where
  r : m.readW ((layF P pre L).fr sRet) 32 = rOf (oc P σ)
  out : Spec.Rsa.bytesAt m (P.out.setWidth 64) P.K = outB P σ
  ml : Spec.Rsa.wordsAt m (P.ml.setWidth 64) 1 = [BitVec.ofNat 64 (mlen P σ)]
  le : mlen P σ ≤ P.K

/-- What misses those. -/
abbrev Away (P : EP) (pre : BitVec 32) (L : Nat) (r : Region) : Prop :=
  (slotR (layF P pre L) sRet).Disjoint r ∧ P.OUT.Disjoint r ∧ P.ML.Disjoint r

theorem Kp.keep {σ : State} {m m' : Mem} {rs : List Region} (hk : Kp P pre L σ m) (hf : Frame rs m m')
    (ha : ∀ r ∈ rs, Away P pre L r) (hK : P.K ≤ 2 ^ 64) : Kp P pre L σ m' := by
  refine ⟨slot_keep hf (fun r hr => (ha r hr).1) hk.r, ?_, ?_, hk.le⟩
  · rw [Proof.RsaPkcs1Sig.bytesAt_frame hf (fun r hr => (ha r hr).2.1) hK]; exact hk.out
  · rw [Proof.Rsa.wordsAt_frame hf (by decide) (fun r hr => (ha r hr).2.2)]; exact hk.ml

theorem InF.geo {σ : State} (h : InF P pre L σ) : Geo (layF P pre L) P.scr := by
  have f := h.ok.fits P.SCR (by simp)
  have sw := h.slK
  have k64 := h.kv.1
  simp only [Spec.Rsa.scratchWords] at sw
  simp only [BitVec.toNat_setWidth] at f
  rw [Nat.mod_eq_of_lt (by have := P.scr.isLt; omega_arith)] at f
  exact ⟨rfl, by unfold oRsa; omega_arith, ⟨P.sl * 8, by unfold oRsa; omega_arith, by simp⟩, ⟨σ, h.ok⟩,
    by show 48 ≤ 3572; decide⟩

/-- A range of our part of `scratch` misses the slot, `out` and `*msg_len`. -/
theorem away_scr {σ : State} (h : InF P pre L σ) {o n : Nat} (hn : o + n ≤ oRsa) :
    Away P pre L (VG.Proof.RsaPss.X86.sR P.scr o n) := by
  have hg := h.geo
  have ok := h.ok
  have sub : Region.Sub (VG.Proof.RsaPss.X86.sR P.scr o n) P.SCR := by
    have sw := h.slK
    have k64 := h.kv.1
    simp only [Spec.Rsa.scratchWords] at sw
    have f := h.ok.fits P.SCR (by simp)
    simp only [BitVec.toNat_setWidth] at f
    rw [Nat.mod_eq_of_lt (by have := P.scr.isLt; omega_arith)] at f
    exact Offset.sub_base _ (by unfold oRsa at hn; omega_arith)
  have ww := ok.wrw
  simp only [EP.rw, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true] at ww
  exact ⟨hg.slot ok hn (by show sRet + 4 ≤ frameBytes + 16; decide), (ww.1.2.sub_right sub),
    (ww.2.1.sub_right sub)⟩

/-- A slot other than `sRet` misses the slot, `out` and `*msg_len`. -/
theorem away_slot {σ : State} (h : InF P pre L σ) {d : Nat} (hd : d + 4 ≤ frameBytes)
    (h₁ : d + 4 ≤ sRet ∨ sRet + 4 ≤ d) : Away P pre L (slotR (layF P pre L) d) :=
  ⟨slotSep (by decide) hd (by rcases h₁ with h₁ | h₁ <;> [exact .inr h₁; exact .inl h₁]),
    (h.ok.stk_fr (R := P.OUT) (.inr (by simp)) (by show d + 4 ≤ frameBytes + 16; unfold frameBytes at hd ⊢; omega_arith)).symm,
    (h.ok.stk_fr (R := P.ML) (.inr (by simp)) (by show d + 4 ≤ frameBytes + 16; unfold frameBytes at hd ⊢; omega_arith)).symm⟩

/-- After `after`: `scratch` in `ebp`, and what the call left. -/
abbrev T0 (P : EP) (pre : BitVec 32) (L : Nat) (σ s : State) : Prop :=
  Ctx (layF P pre L) P.scr σ s ∧ InF P pre L σ ∧ Kp P pre L σ s.mem

theorem after_taint : TaintOk [.esp] (.block after) := ⟨_, by taint_decide⟩

theorem after_vp : VP (R2 P pre L) (.block after) (T0 P pre L) := by
  refine VP.taint [.esp] after_taint (fun _ _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    rw [h₁.1.2.sp, h₂.1.2.sp]) fun σ s ⟨⟨hin, hst⟩, res⟩ => ?_
  obtain ⟨hr, hb, hw⟩ := writtenMsg_parts res
  simp only [after, st, ld]
  refine hst.wp_strFr (d := sRet) (by show sRet + 4 ≤ frameBytes; decide) fun t1 s1 m1 => ?_
  refine s1.wp_arg (j := 21) (by simp) (by decide) fun t2 s2 u2 => WP.block_nil ?_
  have fr : Frame [slotR (layF P pre L) sRet] s.mem t2.mem := by
    rw [u2.mem, m1.mem]; exact slot_frame _ _ _ _
  have d : ∀ R, R ∈ (layF P pre L).rw → ∀ r ∈ [slotR (layF P pre L) sRet], R.Disjoint r := by
    intro R hR r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact (hin.ok.stk_fr (.inr hR) (by show sRet + 4 ≤ frameBytes + 16; decide)).symm
  have k32 : P.K < 2 ^ 32 := by have := hin.kv.2; omega_arith
  refine ⟨⟨s2, by rw [u2.gpr]; rfl⟩, hin, ⟨?_, ?_, ?_, mlen_le hb⟩⟩
  · rw [u2.mem, m1.mem, Mem.readW_writeW_self32, hr]
  · rw [Proof.RsaPkcs1Sig.bytesAt_frame fr (d P.OUT (by simp)) (by omega_arith)]; exact hb
  · rw [Proof.Rsa.wordsAt_frame fr (by decide) (d P.ML (by simp))]; exact hw

/-! ## The buffer -/

theorem InF.k32 {σ : State} (h : InF P pre L σ) : P.K ≤ 1024 := h.kv.2

theorem InF.outFit {σ : State} (h : InF P pre L σ) : P.out.toNat + P.K ≤ 2 ^ 32 := by
  have f := h.ok.fits P.OUT (by simp)
  simp only [BitVec.toNat_setWidth] at f
  rwa [Nat.mod_eq_of_lt (by have := P.out.isLt; omega_arith)] at f

/-- After the buffer is cleared. -/
abbrev T1 (P : EP) (pre : BitVec 32) (L : Nat) (σ s : State) : Prop :=
  Ctx (layF P pre L) P.scr σ s ∧ (InF P pre L σ ∧ Kp P pre L σ s.mem) ∧
    ∀ i < 2048, s.mem (byteAt (P.scr + BitVec.ofNat 32 oBuf) i) = 0

theorem clr_taint : TaintOk [.esp, .ebp] (.block (clrArgs oBuf 2048)) := ⟨_, by taint_decide⟩

theorem InF.kp_keep_scr {σ : State} (hin : InF P pre L σ) {m m' : Mem} {o n : Nat} (hn : o + n ≤ oRsa)
    (hk : Kp P pre L σ m) (hf : Frame [VG.Proof.RsaPss.X86.sR P.scr o n] m m') : Kp P pre L σ m' :=
  hk.keep hf (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact away_scr hin hn) (by have := hin.k32; omega_arith)

theorem clear_vp {σ₀ : State} (h₀ : InF P pre L σ₀) : VP (T0 P pre L) clearBuf (T1 P pre L) := by
  have hg := h₀.geo
  refine VP.seq (G := fun σ s => (Ctx (layF P pre L) P.scr σ s ∧ (InF P pre L σ ∧ Kp P pre L σ s.mem)) ∧
      s.gpr .esi = P.scr + BitVec.ofNat 32 oBuf ∧ s.gpr .ecx = BitVec.ofNat 32 2048 ∧ s.gpr .eax = 0)
    (VP.taint [.esp, .ebp] clr_taint (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hin, hk⟩ => ?_) ?_
  · simp only [clrArgs, atS, addi, mi, List.cons_append, List.nil_append]
    refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => wp_movi fun t3 u3 => wp_movi fun t4 u4 => WP.block_nil ?_
    obtain m4 : t4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
    refine ⟨⟨(((hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)).upd u3 (by decide)
      (by decide)).upd u4 (by decide) (by decide), hin, m4 ▸ hk⟩, ?_, ?_, ?_⟩
    · simp (disch := decide) only [u4.other, u3.other, u2.gpr, u1.gpr, hc.ebp]
    · rw [u4.other _ (by decide), u3.gpr]
    · rw [u4.gpr]; rfl
  · exact (zero_vp (hg.wbuf (o := oBuf) (n := 2048) (by decide) (by decide)) (by decide)
      (Inv := fun σ m => InF P pre L σ ∧ Kp P pre L σ m) fun σ m m' ⟨hin, hk⟩ hf =>
        ⟨hin, hin.kp_keep_scr (o := oBuf) (n := 2048) (by decide) hk (by rwa [hg.scrA (by decide)] at hf)⟩).mono
      (fun σ s ⟨⟨hc, hm⟩, si, cx, ax⟩ => ⟨hc, hm, si, cx, ax⟩) fun _ _ h => h

/-- After `out` is copied to the buffer. -/
abbrev T2 (P : EP) (pre : BitVec 32) (L : Nat) (σ s : State) : Prop :=
  Ctx (layF P pre L) P.scr σ s ∧ (InF P pre L σ ∧ Kp P pre L σ s.mem) ∧
    ∀ j < 2048, s.mem (sa P.scr (oBuf + j)) = Bp P σ j

theorem inSet_taint : TaintOk [.esp, .ebp] (.block inSet) := ⟨_, by taint_decide⟩

theorem copyIn_vp {σ₀ : State} (h₀ : InF P pre L σ₀) : VP (T1 P pre L) copyIn (T2 P pre L) := by
  have hg := h₀.geo
  have hK := h₀.k32
  have k64 := h₀.kv.1
  have eB : oBuf = 2048 := rfl
  have eR : oRsa = 8192 := rfl
  refine VP.seq (G := fun σ s => (Ctx (layF P pre L) P.scr σ s ∧ ((InF P pre L σ ∧ Kp P pre L σ s.mem) ∧
      ∀ j < 2048, P.K ≤ j → s.mem (byteAt (P.scr + BitVec.ofNat 32 oBuf) j) = 0)) ∧
      s.gpr .ebx = P.scr + BitVec.ofNat 32 oBuf ∧ s.gpr .esi = P.out ∧ s.gpr .ecx = BitVec.ofNat 32 P.K ∧
      ∀ i < P.K, s.mem (byteAt P.out i) = (outB P σ).getD i 0)
    (VP.taint [.esp, .ebp] inSet_taint (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, ⟨hin, hk⟩, hz⟩ => ?_) ?_
  · simp only [inSet, atS, addi, ld, List.cons_append, List.nil_append]
    refine hc.wp_arg hg (j := 0) (by simp) (by decide) (by decide) fun t1 c1 u1 => ?_
    refine wp_mov fun t2 u2 => wp_addi fun t3 u3 => ?_
    have c3 := (c1.upd u2 (by decide) (by decide)).upd u3 (by decide) (by decide)
    refine c3.wp_arg hg (j := 4) (by simp) (by decide) (by decide) fun t4 c4 u4 => WP.block_nil ?_
    obtain m4 : t4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
    refine ⟨⟨c4, ⟨hin, m4 ▸ hk⟩, fun j hj _ => m4 ▸ hz j hj⟩, ?_, ?_, ?_, fun i hi => ?_⟩
    · simp (disch := decide) only [u4.other, u3.gpr, u2.gpr, c1.ebp]
    · rw [u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u1.gpr]; rfl
    · rw [u4.gpr]; rfl
    · rw [m4, ← Proof.RsaPkcs1Sig.bytesAt_getD (m := s.mem) (p := P.out.setWidth 64) hi 0, hk.out]
  have aB : (P.scr + BitVec.ofNat 32 oBuf).setWidth 64 = sa P.scr oBuf := hg.scrA (by decide)
  refine VP.mono (copy_vp (hg.wbuf (o := oBuf) (n := P.K) (by omega_arith) (by omega_arith))
    ⟨h₀.outFit, by omega_arith, ⟨P.OUT, List.mem_append_right _ (List.mem_cons_of_mem _ (by simp)),
      Region.contains_self _ _⟩⟩
    (by rw [aB]; exact (away_scr h₀ (o := oBuf) (n := P.K) (by omega_arith)).2.1)
    (by omega_arith)
    (Inv := fun σ m => (InF P pre L σ ∧ Kp P pre L σ m) ∧
      ∀ j < 2048, P.K ≤ j → m (byteAt (P.scr + BitVec.ofNat 32 oBuf) j) = 0)
    (f := fun σ i => (outB P σ).getD i 0) fun σ m m' ⟨⟨hin, hk⟩, hz⟩ hf => by
      rw [aB] at hf
      refine ⟨⟨hin, hin.kp_keep_scr (o := oBuf) (n := P.K) (by omega_arith) hk hf⟩,
        fun j hj hj' => ?_⟩
      rw [← hz j hj hj']
      refine hf _ fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      rw [hg.byteAt_scr (by omega_arith)]
      exact VG.Proof.RsaPss.X86.Geo.sep (scr := P.scr) (o := oBuf + j) (n := 1) (by omega_arith)
        (by omega_arith) (by omega_arith) _ (Region.contains_self _ _))
    (fun σ s ⟨⟨hc, hm⟩, bx, si, cx, hf⟩ => ⟨hc, hm, bx, si, cx, hf⟩)
    fun σ s ⟨hc, ⟨hm, hz⟩, ht⟩ => ⟨hc, hm, fun j hj => ?_⟩
  rw [← hg.byteAt_scr (by omega_arith)]
  by_cases e : j < P.K
  · rw [Bp, ite_eq_left e, ht j e]
  · rw [Bp, ite_eq_right e]; exact hz j hj (by omega_arith)


/-! ## The shift -/

/-- After `p` passes. -/
abbrev SH (P : EP) (pre : BitVec 32) (L : Nat) (σ : State) (p : Nat) (m : Mem) : Prop :=
  m.readW ((layF P pre L).fr sA) 32 = BitVec.ofNat 32 (aV P σ / 2 ^ p) ∧
    m.readW ((layF P pre L).fr sD) 32 = BitVec.ofNat 32 (2 ^ p) ∧
    m.readW ((layF P pre L).fr sPc) 32 = BitVec.ofNat 32 (11 - p) ∧
    ∀ j < 2048, m (sa P.scr (oBuf + j)) = Bp P σ (j + aV P σ % 2 ^ p)

/-- A state of the shift, after `p` passes. -/
abbrev S0 (P : EP) (pre : BitVec 32) (L : Nat) (p : Nat) (σ s : State) : Prop :=
  Ctx (layF P pre L) P.scr σ s ∧ (InF P pre L σ ∧ Kp P pre L σ s.mem) ∧ SH P pre L σ p s.mem

theorem Bp_high {σ : State} (h : InF P pre L σ) {j : Nat} (hj : 1024 ≤ j) : Bp P σ j = 0 := by
  have := h.k32
  rw [Bp, ite_eq_right (by omega_arith)]

theorem shA_taint : TaintOk [.esp] (.block ([ld .eax (arg 4), ld .edx (arg 2)] : List Instr)) :=
  ⟨_, by taint_decide⟩

theorem shB_taint : TaintOk [.esp, .edx] (.block (shInit.drop 2)) := ⟨_, by taint_decide⟩

/-- What the shift's slots keep. -/
theorem keep3 {σ₀ σ : State} (h₀ : InF P pre L σ₀) {m m' : Mem}
    (hf : Frame [slotR (layF P pre L) sA, slotR (layF P pre L) sD, slotR (layF P pre L) sPc] m m')
    (hk : Kp P pre L σ m) {f : Nat → Byte} (hy : ∀ j < 2048, m (sa P.scr (oBuf + j)) = f j) :
    Kp P pre L σ m' ∧ ∀ j < 2048, m' (sa P.scr (oBuf + j)) = f j := by
  have hg := h₀.geo
  have ok := h₀.ok
  refine ⟨hk.keep hf (fun r hr => ?_) (by have := h₀.k32; omega_arith),
    sbytes_keep hf (fun r hr => ?_) (by decide) hy⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact away_slot h₀ (by decide) (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      exact (hg.slot ok (by decide) (by show _ + 4 ≤ frameBytes + 16; decide)).symm

/-- The distance, the first pass's, and the passes. -/
theorem shInit_vp {σ₀ : State} (h₀ : InF P pre L σ₀) : VP (T2 P pre L) (.block shInit) (S0 P pre L 0) := by
  have hg := h₀.geo
  rw [show shInit = ([ld .eax (arg 4), ld .edx (arg 2)] : List Instr) ++ shInit.drop 2 from rfl]
  refine VP.block_append (G := fun σ s => T2 P pre L σ s ∧ s.gpr .eax = BitVec.ofNat 32 P.K ∧ s.gpr .edx = P.ml)
    (VP.taint [.esp] shA_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      rw [h₁.1.st.sp, h₂.1.st.sp]) fun σ s ⟨hc, hm, hy⟩ => ?_)
    (VP.taint [.esp, .edx] shB_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.1.1.st.sp, h₂.1.1.st.sp]
      · rw [h₁.2.2, h₂.2.2]) fun σ s ⟨⟨hc, ⟨hin, hk⟩, hy⟩, ax, dx⟩ => ?_)
  · simp only [ld]
    refine hc.wp_arg hg (j := 4) (by simp) (by decide) (by decide) fun t1 c1 u1 => ?_
    refine c1.wp_arg hg (j := 2) (by simp) (by decide) (by decide) fun t2 c2 u2 => WP.block_nil ?_
    obtain m2 : t2.mem = s.mem := by rw [u2.mem, u1.mem]
    exact ⟨⟨c2, m2 ▸ hm, m2 ▸ hy⟩, by rw [u2.other _ (by decide), u1.gpr]; rfl, by rw [u2.gpr]; rfl⟩
  have hK := hin.k32
  have le := hk.le
  have fitM : P.ml.toNat + 8 ≤ 2 ^ 32 := by
    have f := hin.ok.fits P.ML (by simp)
    simp only [BitVec.toNat_setWidth] at f
    rwa [Nat.mod_eq_of_lt (by have := P.ml.isLt; omega_arith)] at f
  have rd64 : s.mem.readW (P.ml.setWidth 64) 64 = BitVec.ofNat 64 (mlen P σ) := by
    have := hk.ml
    simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero,
      BitVec.add_zero, List.cons.injEq, and_true] at this
    simpa using this
  have rd32 : s.mem.readW (P.ml.setWidth 64) 32 = BitVec.ofNat 32 (mlen P σ) := by
    rw [Mem.readW_lo32 rd64]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_arith
  have aM : addr P.ml 0 = P.ml.setWidth 64 := by simp [addr]
  simp only [shInit, ld, st, mi, List.drop_succ_cons, List.drop_zero, Impl.RsaPkcs1Sig.X86.at_]
  refine wp_ldm (B := P.ml) (o := 0) dx (by
      rw [aM]; exact ⟨P.ML, List.mem_append_right _ (hc.st.inRw (by simp)), by simp [Region.Contains]⟩)
    fun t1 u1 => ?_
  have c1 := hc.upd u1 (by decide) (by decide)
  refine wp_sub fun t2 u2 _ => ?_
  have c2 := c1.upd u2 (by decide) (by decide)
  refine c2.wp_st hg (d := sA) (by decide) fun t3 c3 m3 => ?_
  refine wp_movi fun t4 u4 => (c3.upd u4 (by decide) (by decide)).wp_st hg (d := sD) (by decide)
    fun t5 c5 m5 => ?_
  refine wp_movi fun t6 u6 => (c5.upd u6 (by decide) (by decide)).wp_st hg (d := sPc) (by decide)
    fun t7 c7 m7 => WP.block_nil ?_
  obtain va : t2.gpr .eax = BitVec.ofNat 32 (aV P σ) := by
    rw [u2.gpr, u1.other _ (by decide), u1.gpr, ax, aM, rd32, sub_ofNat le]
  obtain mm : t7.mem = ((s.mem.writeW ((layF P pre L).fr sA) (BitVec.ofNat 32 (aV P σ))).writeW
      ((layF P pre L).fr sD) (BitVec.ofNat 32 1)).writeW ((layF P pre L).fr sPc) (BitVec.ofNat 32 11) := by
    rw [m7.mem, u6.gpr, u6.mem, m5.mem, u4.gpr, u4.mem, m3.mem, va, u2.mem, u1.mem]
  obtain ⟨hk', hy'⟩ := keep3 hin (mm ▸ fr3 _ _ _ _ _) hk hy
  obtain ⟨r1, r2, r3⟩ := rd3 (layF P pre L) s.mem (BitVec.ofNat 32 (aV P σ)) (BitVec.ofNat 32 1)
    (BitVec.ofNat 32 11)
  rw [← mm] at r1 r2 r3
  refine ⟨c7, ⟨hin, hk'⟩, ?_, ?_, ?_, fun j hj => ?_⟩
  · rw [r1, Nat.pow_zero, Nat.div_one]
  · rw [r2]
  · rw [r3]
  · rw [hy' j hj, Nat.pow_zero, Nat.mod_one, Nat.add_zero]

theorem passSet_taint : TaintOk [.esp, .ebp] (.block passSet) := ⟨_, by taint_decide⟩
theorem passNext_taint : TaintOk [.esp, .ebp] (.block passNext) := ⟨_, by taint_decide⟩

/-- A pass's registers. -/
theorem passSet_vp {σ₀ : State} (h₀ : InF P pre L σ₀) {p : Nat} :
    VP (S0 P pre L p) (.block passSet)
      (fun σ s => S0 P pre L p σ s ∧ s.gpr .esi = P.scr + BitVec.ofNat 32 oBuf ∧
        s.gpr .edi = P.scr + BitVec.ofNat 32 (oBuf + 2 ^ p) ∧ s.gpr .ecx = BitVec.ofNat 32 1024 ∧
        s.gpr .edx = maskOf (aV P σ / 2 ^ p % 2 = 1)) := by
  have hg := h₀.geo
  refine VP.taint [.esp, .ebp] passSet_taint (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, ⟨hin, hk⟩, hs⟩ => ?_
  obtain ⟨σ', ok⟩ := hg.ok
  have hK := hin.k32
  have haV : aV P σ ≤ P.K := Nat.sub_le _ _
  have hav : aV P σ / 2 ^ p < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega_arith)
  simp only [passSet, atS, addSlot, addi, ld, mi, Impl.RsaPkcs1Sig.X86.stk, List.cons_append, List.nil_append]
  refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => wp_mov fun t3 u3 => ?_
  have c3 : Ctx (layF P pre L) P.scr σ t3 :=
    ((hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)).upd u3 (by decide) (by decide)
  refine wp_addm (B := (layF P pre L).B) (by rw [c3.st.sp])
    (by rw [hg.aFr ok sD (by decide)]; exact c3.rFr hg sD (by decide)) fun t4 u4 => ?_
  have c4 : Ctx (layF P pre L) P.scr σ t4 := c3.upd u4 (by decide) (by decide)
  refine c4.wp_slot hg (d := sA) (by decide) (by decide) (by decide) fun t5 c5 u5 => ?_
  refine wp_andi fun t6 u6 => wp_movi fun t7 u7 => wp_sub fun t8 u8 _ => wp_movi fun t9 u9 => WP.block_nil ?_
  have c9 : Ctx (layF P pre L) P.scr σ t9 :=
    (((c5.upd u6 (by decide) (by decide)).upd u7 (by decide) (by decide)).upd u8 (by decide) (by decide)).upd u9
      (by decide) (by decide)
  have m9 : t9.mem = s.mem := by
    rw [u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have esi2 : t2.gpr .esi = P.scr + BitVec.ofNat 32 oBuf := by rw [u2.gpr, u1.gpr, hc.ebp]
  refine ⟨⟨c9, ⟨hin, m9 ▸ hk⟩, m9 ▸ hs⟩, ?_, ?_, ?_, ?_⟩
  · simp (disch := decide) only [u9.other, u8.other, u7.other, u6.other, u5.other, u4.other, u3.other, esi2]
  · simp (disch := decide) only [u9.other, u8.other, u7.other, u6.other, u5.other, u4.gpr, u3.gpr, esi2]
    rw [u3.mem, u2.mem, u1.mem, hg.aFr ok sD (by decide), hs.2.1, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  · rw [u9.gpr]
  · simp (disch := decide) only [u9.other, u8.gpr, u7.gpr, u7.other, u6.gpr, u5.gpr]
    rw [u4.mem, u3.mem, u2.mem, u1.mem, hs.1]
    exact mask_bit hav

/-- Between a pass's bytes and its next stage. -/
abbrev SM (P : EP) (pre : BitVec 32) (L : Nat) (σ : State) (p : Nat) (m : Mem) : Prop :=
  m.readW ((layF P pre L).fr sA) 32 = BitVec.ofNat 32 (aV P σ / 2 ^ p) ∧
    m.readW ((layF P pre L).fr sD) 32 = BitVec.ofNat 32 (2 ^ p) ∧
    m.readW ((layF P pre L).fr sPc) 32 = BitVec.ofNat 32 (11 - p) ∧
    ∀ j < 2048, m (sa P.scr (oBuf + j)) = Bp P σ (j + aV P σ % 2 ^ (p + 1))

/-- A pass's bytes. -/
theorem passMid_vp {σ₀ : State} (h₀ : InF P pre L σ₀) {p : Nat} (hp : p < 11) :
    VP (fun σ s => S0 P pre L p σ s ∧ s.gpr .esi = P.scr + BitVec.ofNat 32 oBuf ∧
        s.gpr .edi = P.scr + BitVec.ofNat 32 (oBuf + 2 ^ p) ∧ s.gpr .ecx = BitVec.ofNat 32 1024 ∧
        s.gpr .edx = maskOf (aV P σ / 2 ^ p % 2 = 1))
      (countLoop passBody)
      (fun σ s => Ctx (layF P pre L) P.scr σ s ∧ (InF P pre L σ ∧ Kp P pre L σ s.mem) ∧ SM P pre L σ p s.mem) := by
  have hg := h₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have eB : oBuf = 2048 := rfl
  have eR : oRsa = 8192 := rfl
  obtain hp10 : 2 ^ p ≤ 2 ^ 10 := Nat.pow_le_pow_right (by decide) (by omega_arith)
  obtain hp0 : 0 < 2 ^ p := Nat.two_pow_pos p
  refine (pass_vp hg (o := oBuf) (d := 2 ^ p) (n := 1024) (by decide) hp0 (by omega_arith)
    (c := fun σ => aV P σ / 2 ^ p % 2 = 1)
    (X := fun σ m => (InF P pre L σ ∧ Kp P pre L σ m) ∧ SH P pre L σ p m)).mono
    (fun σ s ⟨⟨hc, hk, hs⟩, si, di, cx, dx⟩ => ⟨hc, ⟨hk, hs⟩, si, di, cx, dx⟩)
    fun σ s ⟨hc, m₀, ⟨⟨hin, hk⟩, hs⟩, fr, hsel⟩ => ?_
  have hK := hin.k32
  obtain ks : ∀ d, d + 4 ≤ frameBytes → s.mem.readW ((layF P pre L).fr d) 32 = m₀.readW ((layF P pre L).fr d) 32 :=
    fun d hd => slot_keep (v := m₀.readW ((layF P pre L).fr d) 32) fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hg.slot ok (by omega_arith) (by show d + 4 ≤ frameBytes + 16; unfold frameBytes at hd ⊢; omega_arith)) rfl
  refine ⟨hc, ⟨hin, hin.kp_keep_scr (o := oBuf) (n := 1024) (by omega_arith) hk fr⟩,
    by rw [ks _ (by decide)]; exact hs.1, by rw [ks _ (by decide)]; exact hs.2.1,
    by rw [ks _ (by decide)]; exact hs.2.2.1, fun j hj => ?_⟩
  obtain ms := mod_succ (aV P σ) p
  by_cases e : j < 1024
  · rw [hsel j e]
    by_cases hc' : aV P σ / 2 ^ p % 2 = 1
    · rw [ite_eq_left hc', show oBuf + 2 ^ p + j = oBuf + (2 ^ p + j) by omega_arith,
        hs.2.2.2 _ (by omega_arith)]
      congr 1; rw [ms, hc']; omega_arith
    · rw [ite_eq_right hc', hs.2.2.2 _ hj]
      congr 1; rw [ms, show aV P σ / 2 ^ p % 2 = 0 by omega_arith]; omega_arith
  · have hm : s.mem (sa P.scr (oBuf + j)) = m₀ (sa P.scr (oBuf + j)) :=
      fr _ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact VG.Proof.RsaPss.X86.Geo.sep (scr := P.scr) (o := oBuf + j) (n := 1) (by omega_arith)
          (by omega_arith) (by omega_arith) _ (Region.contains_self _ _)
    rw [hm, hs.2.2.2 j hj, Bp_high hin (by omega_arith), Bp_high hin (by omega_arith)]

/-- The next pass's slots, and the flags of whether it was the last. -/
theorem passNext_vp {σ₀ : State} (h₀ : InF P pre L σ₀) {p : Nat} (hp : p < 11) :
    VP (fun σ s => Ctx (layF P pre L) P.scr σ s ∧ (InF P pre L σ ∧ Kp P pre L σ s.mem) ∧ SM P pre L σ p s.mem)
      (.block passNext)
      (fun σ s => S0 P pre L (p + 1) σ s ∧ s.zf = some (decide (11 - (p + 1) = 0))) := by
  have hg := h₀.geo
  refine VP.taint [.esp, .ebp] passNext_taint (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, ⟨hin, hk⟩, hs⟩ => ?_
  have hK := hin.k32
  have haV : aV P σ ≤ P.K := Nat.sub_le _ _
  obtain hp10 : 2 ^ p ≤ 2 ^ 10 := Nat.pow_le_pow_right (by decide) (by omega_arith)
  obtain ea : BitVec.ofNat 32 (aV P σ / 2 ^ p) >>> 1 = BitVec.ofNat 32 (aV P σ / 2 ^ (p + 1)) := by
    rw [VG.Proof.RsaPss.X86.ofNat_shr (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega_arith)),
      Nat.div_div_eq_div_mul, Nat.pow_one, ← Nat.pow_succ]
  obtain ed : BitVec.ofNat 32 (2 ^ p) + BitVec.ofNat 32 (2 ^ p) = BitVec.ofNat 32 (2 ^ (p + 1)) := by
    rw [BitVec.ofNat_add_ofNat, Nat.pow_succ]; congr 1; omega_arith
  obtain ec : BitVec.ofNat 32 (11 - p) - 1 = BitVec.ofNat 32 (11 - (p + 1)) := by
    rw [ofNat_pred (by omega_arith), Nat.sub_sub]
  simp only [passNext, ld, st]
  refine hc.wp_slot hg (d := sA) (by decide) (by decide) (by decide) fun t1 c1 u1 => ?_
  refine wp_shr (by decide) fun t2 u2 _ => ?_
  refine (c1.upd u2 (by decide) (by decide)).wp_st hg (d := sA) (by decide) fun t3 c3 m3 => ?_
  refine c3.wp_slot hg (d := sD) (by decide) (by decide) (by decide) fun t4 c4 u4 => ?_
  refine wp_add fun t5 u5 _ => (c4.upd u5 (by decide) (by decide)).wp_st hg (d := sD) (by decide)
    fun t6 c6 m6 => ?_
  refine c6.wp_slot hg (d := sPc) (by decide) (by decide) (by decide) fun t7 c7 u7 => ?_
  refine wp_subi fun t8 u8 _ z8 => (c7.upd u8 (by decide) (by decide)).wp_st hg (d := sPc) (by decide)
    fun t9 c9 m9 => WP.block_nil ?_
  obtain va : t2.gpr .eax = BitVec.ofNat 32 (aV P σ / 2 ^ (p + 1)) := by rw [u2.gpr, u1.gpr, hs.1, ea]
  obtain m3' : t3.mem = s.mem.writeW ((layF P pre L).fr sA) (BitVec.ofNat 32 (aV P σ / 2 ^ (p + 1))) := by
    rw [m3.mem, va, u2.mem, u1.mem]
  obtain vd : t5.gpr .eax = BitVec.ofNat 32 (2 ^ (p + 1)) := by
    rw [u5.gpr, u4.gpr, m3', Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide), hs.2.1, ed]
  obtain vc : t8.gpr .eax = BitVec.ofNat 32 (11 - (p + 1)) := by
    rw [u8.gpr, u7.gpr, m6.mem, u5.mem, u4.mem, m3', Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide),
      Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide), hs.2.2.1, ec]
  obtain mm : t9.mem = ((s.mem.writeW ((layF P pre L).fr sA) (BitVec.ofNat 32 (aV P σ / 2 ^ (p + 1)))).writeW
      ((layF P pre L).fr sD) (BitVec.ofNat 32 (2 ^ (p + 1)))).writeW ((layF P pre L).fr sPc)
        (BitVec.ofNat 32 (11 - (p + 1))) := by
    rw [m9.mem, vc, u8.mem, u7.mem, m6.mem, vd, u5.mem, u4.mem, m3']
  obtain ⟨hk', hy'⟩ := keep3 hin (mm ▸ fr3 _ _ _ _ _) hk hs.2.2.2
  obtain ⟨r1, r2, r3⟩ := rd3 (layF P pre L) s.mem (BitVec.ofNat 32 (aV P σ / 2 ^ (p + 1)))
    (BitVec.ofNat 32 (2 ^ (p + 1))) (BitVec.ofNat 32 (11 - (p + 1)))
  rw [← mm] at r1 r2 r3
  refine ⟨⟨c9, ⟨hin, hk'⟩, r1, r2, r3, hy'⟩, ?_⟩
  rw [m9.zf, z8, u7.gpr, m6.mem, u5.mem, u4.mem, m3', Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide),
    Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide), hs.2.2.1, ec, VG.X86.Wp.ofNat_beq_zero (by omega_arith)]

/-- A pass. -/
theorem onePass_vp {σ₀ : State} (h₀ : InF P pre L σ₀) {p : Nat} (hp : p < 11) :
    VP (S0 P pre L p) passOne (fun σ s => S0 P pre L (p + 1) σ s ∧ s.zf = some (decide (11 - (p + 1) = 0))) :=
  (passSet_vp h₀).seq ((passMid_vp h₀ hp).seq (passNext_vp h₀ hp))

/-- After the shift: the buffer holds `out`'s bytes from the zeros' end on. -/
abbrev T3 (P : EP) (pre : BitVec 32) (L : Nat) (σ s : State) : Prop :=
  Ctx (layF P pre L) P.scr σ s ∧ (InF P pre L σ ∧ Kp P pre L σ s.mem) ∧
    ∀ j < 2048, s.mem (sa P.scr (oBuf + j)) = Bp P σ (j + aV P σ)

/-- `out`'s bytes shifted left by `k - *msg_len` bytes. -/
theorem shift_vp {σ₀ : State} (h₀ : InF P pre L σ₀) : VP (T2 P pre L) shift (T3 P pre L) := by
  refine (shInit_vp h₀).seq ?_
  let I : Nat → State → State → Prop := fun k σ s => k ≤ 11 ∧ S0 P pre L (11 - k) σ s
  refine (VP.loop (I := I) (fun k => ?_) 10).mono (fun σ s h => ⟨by omega_arith, h⟩) fun _ _ h => h
  by_cases hk : k ≤ 10
  swap
  · exact VG.Proof.RsaPss.X86.VP.empty fun σ s h' => hk (by have := h'.1; omega_arith)
  refine (onePass_vp h₀ (p := 10 - k) (by omega_arith)).mono
    (fun σ s ⟨_, hs⟩ => by rw [show 10 - k = 11 - (k + 1) by omega_arith]; exact hs)
    fun σ s ⟨⟨hc, hq, hs⟩, z⟩ => ⟨?_, fun h0 => ⟨hc, hq, fun j hj => ?_⟩, fun hpos => ⟨by omega_arith, ?_⟩⟩
  · show eval .ne s = _
    simp only [eval, z, show 11 - (10 - k + 1) = k by omega_arith]
    by_cases h0 : k = 0 <;> simp [h0] <;> omega_arith
  · subst h0
    have hK := hq.1.k32
    have := hq.2.le
    rw [hs.2.2.2 j hj, Nat.mod_eq_of_lt (show aV P σ < 2 ^ (10 - 0 + 1) by
      show P.K - mlen P σ < 2048; omega_arith)]
  · rw [show 11 - k = 10 - k + 1 by omega_arith]; exact ⟨hc, hq, hs⟩

/-! ## The buffer back to `out` -/

/-- What `copyOut` keeps: the result's slot and `*msg_len`. -/
structure Kq (P : EP) (pre : BitVec 32) (L : Nat) (σ : State) (m : Mem) : Prop where
  r : m.readW ((layF P pre L).fr sRet) 32 = rOf (oc P σ)
  ml : Spec.Rsa.wordsAt m (P.ml.setWidth 64) 1 = [BitVec.ofNat 64 (mlen P σ)]
  le : mlen P σ ≤ P.K

/-- After the copy back. -/
abbrev T4 (P : EP) (pre : BitVec 32) (L : Nat) (σ s : State) : Prop :=
  Ctx (layF P pre L) P.scr σ s ∧ (InF P pre L σ ∧ Kq P pre L σ s.mem) ∧
    ∀ i < P.K, s.mem (byteAt P.out i) = Bp P σ (i + aV P σ)

theorem outSet_taint : TaintOk [.esp, .ebp] (.block outSet) := ⟨_, by taint_decide⟩

theorem copyOut_vp {σ₀ : State} (h₀ : InF P pre L σ₀) : VP (T3 P pre L) copyOut (T4 P pre L) := by
  have hg := h₀.geo
  have hK := h₀.k32
  have k64 := h₀.kv.1
  have eB : oBuf = 2048 := rfl
  have eR : oRsa = 8192 := rfl
  refine VP.seq (G := fun σ s => (Ctx (layF P pre L) P.scr σ s ∧ (InF P pre L σ ∧ Kq P pre L σ s.mem)) ∧
      s.gpr .ebx = P.out ∧ s.gpr .esi = P.scr + BitVec.ofNat 32 oBuf ∧ s.gpr .ecx = BitVec.ofNat 32 P.K ∧
      ∀ i < P.K, s.mem (byteAt (P.scr + BitVec.ofNat 32 oBuf) i) = Bp P σ (i + aV P σ))
    (VP.taint [.esp, .ebp] outSet_taint (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, ⟨hin, hk⟩, hy⟩ => ?_) ?_
  · simp only [outSet, atS, addi, ld, List.cons_append, List.nil_append]
    refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
    have c2 := (hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)
    refine c2.wp_arg hg (j := 0) (by simp) (by decide) (by decide) fun t3 c3 u3 => ?_
    refine c3.wp_arg hg (j := 4) (by simp) (by decide) (by decide) fun t4 c4 u4 => WP.block_nil ?_
    obtain m4 : t4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
    refine ⟨⟨c4, hin, m4 ▸ ⟨hk.r, hk.ml, hk.le⟩⟩, ?_, ?_, ?_, fun i hi => ?_⟩
    · rw [u4.other _ (by decide), u3.gpr]; rfl
    · simp (disch := decide) only [u4.other, u3.other, u2.gpr, u1.gpr, hc.ebp]
    · rw [u4.gpr]; rfl
    · rw [m4, hg.byteAt_scr (by omega_arith)]; exact hy i (by omega_arith)
  have aB : (P.scr + BitVec.ofNat 32 oBuf).setWidth 64 = sa P.scr oBuf := hg.scrA (by decide)
  refine VP.mono (copy_vp (src := P.scr + BitVec.ofNat 32 oBuf) (dst := P.out)
    ⟨h₀.outFit, by omega_arith, ⟨P.OUT, List.mem_cons_of_mem _ (by simp), Region.contains_self _ _⟩⟩
    (hg.rbuf (o := oBuf) (n := P.K) (by omega_arith) (by omega_arith))
    (by rw [aB]; exact (away_scr h₀ (o := oBuf) (n := P.K) (by omega_arith)).2.1.symm)
    (by omega_arith)
    (Inv := fun σ m => InF P pre L σ ∧ Kq P pre L σ m)
    (f := fun σ i => Bp P σ (i + aV P σ)) fun σ m m' ⟨hin, hk⟩ hf => by
      have ww := hin.ok.wrw
      simp only [EP.rw, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true] at ww
      refine ⟨hin, slot_keep hf (fun r hr => ?_) hk.r, ?_, hk.le⟩
      · simp only [List.mem_singleton] at hr; subst hr
        exact hin.ok.stk_fr (R := P.OUT) (.inr (by simp)) (by show sRet + 4 ≤ frameBytes + 16; decide)
      · rw [Proof.Rsa.wordsAt_frame hf (by decide) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact ww.1.1.symm)]
        exact hk.ml)
    (fun σ s ⟨⟨hc, hm⟩, bx, si, cx, hf⟩ => ⟨hc, hm, bx, si, cx, hf⟩)
    fun σ s ⟨hc, hm, ht⟩ => ⟨hc, hm, ht⟩

/-- What the contract states of the result `r` and the memory `m`. -/
def FRes (P : EP) (σ : State) (m : Mem) (r : BitVec 32) : Prop :=
  Spec.RsaPkcs1Enc.writtenMsgFront m (P.out.setWidth 64) (P.ml.setWidth 64) P.K r (oc P σ)

/-- The end of the body. -/
def FinF (P : EP) (pre : BitVec 32) (L : Nat) (σ s : State) : Prop := SF P pre L σ s ∧ FRes P σ s.mem (s.gpr .eax)

theorem getD_append_zeros (l : List Byte) (n i : Nat) : (l ++ List.replicate n 0).getD i 0 = l.getD i 0 := by
  by_cases h : i < l.length
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_of_not_lt h),
      List.getElem?_replicate]
    rw [List.getElem?_eq_none (Nat.le_of_not_lt h)]
    split <;> rfl

theorem Bp_shift (P : EP) (σ : State) (hle : mlen P σ ≤ P.K) (i : Nat) :
    Bp P σ (i + aV P σ) = (msgOf (oc P σ)).getD i 0 := by
  have e : aV P σ = P.K - mlen P σ := rfl
  have e2 : mlen P σ = (msgOf (oc P σ)).length := rfl
  unfold Bp
  split
  · rw [outB, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by simp), List.length_replicate, Nat.add_sub_cancel]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega_arith)]; rfl

theorem ret_taint : TaintOk [.esp] (.block Impl.RsaPkcs1Enc.X86.Front.ret) := ⟨_, by taint_decide⟩

theorem ret_vp {σ₀ : State} (h₀ : InF P pre L σ₀) :
    VP (T4 P pre L) (.block Impl.RsaPkcs1Enc.X86.Front.ret) (FinF P pre L) := by
  have hg := h₀.geo
  refine VP.taint [.esp] ret_taint (fun _ _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    rw [h₁.1.st.sp, h₂.1.st.sp]) fun σ s ⟨hc, ⟨hin, hk⟩, ho⟩ => ?_
  simp only [Impl.RsaPkcs1Enc.X86.Front.ret]
  refine hc.wp_slot hg (d := sRet) (by decide) (by decide) (by decide) fun t c u => WP.block_nil ?_
  refine ⟨⟨hin, c.st⟩, writtenMsgFront_of (by rw [u.gpr, hk.r]) ?_ (by rw [u.mem]; exact hk.ml)⟩
  have hl : (msgOf (oc P σ) ++ List.replicate (P.K - mlen P σ) 0).length = P.K := by
    rw [List.length_append, List.length_replicate]; exact Nat.add_sub_cancel' hk.le
  have := Proof.RsaPkcs1Sig.bytesAt_eq (m := t.mem) (p := P.out.setWidth 64)
    (xs := msgOf (oc P σ) ++ List.replicate (P.K - mlen P σ) 0) fun i hi => by
      rw [hl] at hi
      rw [getD_append_zeros, ← Bp_shift P σ hk.le, u.mem]
      exact ho i hi
  rw [hl] at this
  exact this

/-- After the call: the message moved to the start of `out`. -/
theorem tail_vp : VP (R2 P pre L) tail (FinF P pre L) := by
  by_cases h : ∃ σ, InF P pre L σ
  swap
  · exact VG.Proof.RsaPss.X86.VP.empty fun σ s hs => h ⟨σ, hs.1.1⟩
  obtain ⟨σ₀, h₀⟩ := h
  exact after_vp.seq ((clear_vp h₀).seq ((copyIn_vp h₀).seq ((shift_vp h₀).seq ((copyOut_vp h₀).seq
    (ret_vp h₀)))))

/-! ## The function -/

theorem body_vp {name : String} {c : Prog isa} (hv : Verified target c specP) (hns : NoSp c)
    (hst : stackUse c ≤ 3568) :
    VP (SF P pre L) (Impl.RsaPkcs1Enc.X86.Front.body name c) (FinF P pre L) :=
  setup_vp.seq ((call_vp hv hns hst).seq tail_vp)

theorem tail_noSp : NoSp tail := NoSp.of_all (by decide)

theorem body_noSp {name : String} {c : Prog isa} (hns : NoSp c) : NoSp (Impl.RsaPkcs1Enc.X86.Front.body name c) :=
  noSp_seq (.of_all (by decide)) (noSp_seq (noSp_call hns) tail_noSp)

theorem code_noSp {name : String} {c : Prog isa} (hns : NoSp c) : NoSp (Impl.RsaPkcs1Enc.X86.Front.code name c) :=
  noSp_frame rfl rfl (noSp_seq (noSp_frame rfl rfl (body_noSp hns)) restore_noSp)

theorem entered_stateF {s : State} (h : specF.pre s) :
    SF (fp s) (arg s 23) (arg s 24).toNat (entered frameBytes s) (entered frameBytes s) :=
  ⟨in_of_preF h, ⟨(in_of_preF h).ok, (in_of_preF h).ok.sp, rfl, rfl, Frame.refl _ _⟩⟩

theorem specF_sp {s : State} (h : specF.pre s) :
    stackF ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 4 ≤ 2 ^ 32 := by
  sig_pre [Spec.RsaPkcs1Enc.decryptPrecomputedFrontContract, Spec.RsaPkcs1Enc.decryptPrecomputedFrontSig,
    abi, argSlots, argVal, argBytes, stackBelow] at h
  obtain ⟨hsp, hsa, -⟩ := h
  exact ⟨hsp, by omega_using [hsa]⟩

theorem code_ok {name : String} {c : Prog isa} (hv : Verified target c specP) (hns : NoSp c)
    (hst : stackUse c ≤ 3568) {s : State} (h : specF.pre s) :
    WP isa (Impl.RsaPkcs1Enc.X86.Front.code name c) s fun t => abiPreserved s t ∧ specF.post s t := by
  have hin := in_of_preF h
  obtain ⟨hs, hfit⟩ := specF_sp h
  have hsp : 16 + frameBytes ≤ (s.gpr .esp).toNat := by simp only [stackF, frameBytes] at hs ⊢; omega_using [hs]
  have hb := (body_vp (P := fp s) (pre := arg s 23) (L := (arg s 24).toNat) (name := name) hv hns hst).wp _ _
    (entered_stateF h)
  have ok := hin.ok
  rw [fp_layF] at ok
  refine WP.mono (wrap_ok (F := frameBytes) (by decide) (body_noSp hns) hsp hfit
    (W := (layF (fp s) (arg s 23) (arg s 24).toNat).W)
    (Q := fun r m => FRes (fp s) (entered frameBytes s) m r) (fun r hr => ?_)
    (WP.mono hb fun u hu => ⟨hu.1.2.frame, hu.2⟩) (fun r m m' fl hres => ?_)) fun t ⟨abi, res⟩ => ⟨abi, ?_⟩
  · rw [save_eq (argv := (fp s).argvP (arg s 23) (arg s 24).toNat) (ro := (fp s).roP (arg s 23) (arg s 24).toNat)
      (rw := (fp s).rw) (C := 3572) hsp,
      ret_eq (argv := (fp s).argvP (arg s 23) (arg s 24).toNat) (ro := (fp s).roP (arg s 23) (arg s 24).toNat)
      (rw := (fp s).rw) (C := 3572) hsp]
    exact ⟨ok.save_apart r hr, ok.ret_apart r hr⟩
  · obtain F' := release_frame (argv := (fp s).argvP (arg s 23) (arg s 24).toNat)
      (ro := (fp s).roP (arg s 23) (arg s 24).toNat) (rw := (fp s).rw) (C := 3572) fl
    obtain hO := VG.Proof.Rsa.rsa_bytes_frame F' (src := ((fp s).out.setWidth 64)) (k := (fp s).K)
      (by show (arg s 4).toNat < 2 ^ 64; have := (arg s 4).isLt; omega_using [this])
      (fun q hq => by rw [List.mem_singleton.mp hq]; exact (ok.stk (fp s).OUT (by simp [layOf])).symm)
    obtain hM := VG.Proof.Rsa.wordsAt_frame F' (p := ((fp s).ml.setWidth 64)) (n := 1) (by decide)
      (fun q hq => by rw [List.mem_singleton.mp hq]; exact (ok.stk (fp s).ML (by simp [layOf])).symm)
    have key : ∀ o, Spec.RsaPkcs1Enc.writtenMsgFront m ((fp s).out.setWidth 64) ((fp s).ml.setWidth 64) (fp s).K r o →
        Spec.RsaPkcs1Enc.writtenMsgFront m' ((fp s).out.setWidth 64) ((fp s).ml.setWidth 64) (fp s).K r o :=
      fun o => by cases o <;> simp only [Spec.RsaPkcs1Enc.writtenMsgFront] <;> rw [hO, hM] <;> exact id
    unfold FRes at hres ⊢
    exact key _ hres
  · have ro := fun {R : Region} (hR : R ∈ (fp s).roP (arg s 23) (arg s 24).toNat) => entered_ro hsp ok hR
    sig_post [Spec.RsaPkcs1Enc.decryptPrecomputedFrontContract, Spec.RsaPkcs1Enc.decryptPrecomputedFrontSig,
      abi, argSlots, argVal, argBytes]
    unfold FRes oc at res
    rw [show dB (fp s) (entered frameBytes s) = _ from ro (R := (fp s).D) (by simp),
      show cB (fp s) (entered frameBytes s) = _ from ro (R := (fp s).INP) (by simp),
      show pB (fp s) (entered frameBytes s) = _ from ro (R := (fp s).PP) (by simp),
      show qB (fp s) (entered frameBytes s) = _ from ro (R := (fp s).QQ) (by simp),
      show dpB (fp s) (entered frameBytes s) = _ from ro (R := (fp s).DP) (by simp),
      show dqB (fp s) (entered frameBytes s) = _ from ro (R := (fp s).DQ) (by simp),
      show qiB (fp s) (entered frameBytes s) = _ from ro (R := (fp s).QI) (by simp)] at res
    rw [BitVec.setWidth_append_eq_right]
    exact res

theorem code_ct {name : String} {c : Prog isa} (hv : Verified target c specP) (hns : NoSp c)
    (hst : stackUse c ≤ 3568) :
    ConstantTime isa specF.pre specF.pub (Impl.RsaPkcs1Enc.X86.Front.code name c) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  obtain ⟨hep, h23, h24⟩ := ep_eqP (s₁ := s₁) (s₂ := s₂) hp
  have hsp : s₁.gpr .esp = s₂.gpr .esp := by
    sig_pub [Spec.RsaPkcs1Enc.decryptPrecomputedFrontContract, Spec.RsaPkcs1Enc.decryptPrecomputedFrontSig,
      abi, argSlots, argVal, argBytes] at hp
    exact hp.1
  have hfp : fp s₁ = fp s₂ := by simp only [fp]; rw [hep, hsp]
  refine (wrap_ct (F := frameBytes) (body_noSp hns) (P := fun a b => a = s₁ ∧ b = s₂)
    (fun a b h => by rw [h.1, h.2]; exact hsp) ?_ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  refine (body_vp (P := fp s₁) (pre := arg s₁ 23) (L := (arg s₁ 24).toNat) (name := name) hv hns hst).ct.mono ?_
    fun _ _ _ => trivial
  rintro a b ⟨_, _, ⟨rfl, rfl⟩, rfl, rfl⟩
  exact ⟨_, _, entered_stateF h₁, by rw [hfp, h23, h24]; exact entered_stateF h₂⟩

theorem satisfiableF : ∃ s, specF.pre s := by
  have a3 : arg preState 3 = 0x2000 := by decide
  have p3 : BitVec.setWidth 64 (arg preState 3) = 0x2000 := by rw [a3]; decide
  have a11 : arg preState 11 = 0x4200 := by decide
  have p11 : BitVec.setWidth 64 (arg preState 11) = 0x4200 := by rw [a11]; decide
  have a13 : arg preState 13 = 0x4300 := by decide
  have p13 : BitVec.setWidth 64 (arg preState 13) = 0x4300 := by rw [a13]; decide
  have a23 : arg preState 23 = 0x4800 := by decide
  have p23 : BitVec.setWidth 64 (arg preState 23) = 0x4800 := by rw [a23]; decide
  have a4 : arg preState 4 = 64 := by decide
  have l4 : (arg preState 4).toNat = 64 := by rw [a4]; decide
  have a12 : arg preState 12 = 32 := by decide
  have l12 : (arg preState 12).toNat = 32 := by rw [a12]; decide
  have a14 : arg preState 14 = 32 := by decide
  have l14 : (arg preState 14).toNat = 32 := by rw [a14]; decide
  have a24 : arg preState 24 = 24 := by decide
  have l24 : (arg preState 24).toNat = 24 := by rw [a24]; decide
  have e : argAddr preState 0 = 0x20004 := by decide
  have esp : preState.gpr .esp = 0x20000 := rfl
  refine ⟨preState, ?_⟩
  sig_pre [Spec.RsaPkcs1Enc.decryptPrecomputedFrontContract, Spec.RsaPkcs1Enc.decryptPrecomputedFrontSig,
    abi, argSlots, argVal, argBytes, stackBelow, e, esp,
    stackF, frameBytes, Spec.Rsa.lenValid, Spec.Rsa.scratchWords, Spec.Rsa.privatePrecomputedWords]
  sig_and_intros
  rotate_right
  · rw [p3, p11, p13, p23, l4, l12, l14, l24]; exact preState_key
  all_goals first
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (intro a h₁ h₂
       sig_simp_only [Region.Contains, preState] at h₁ h₂
       bv_omega)

/-- `vg_rsa_pkcs1_decrypt_precomputed_front`, calling a callee verified
against `vg_rsa_pkcs1_decrypt_precomputed`'s contract, with 3568 bytes of
stack. -/
theorem front_verified {name : String} {c : Prog isa} (hv : Verified target c specP) (hns : NoSp c)
    (hst : stackUse c ≤ 3568) : Verified target (Impl.RsaPkcs1Enc.X86.Front.code name c) specF :=
  ⟨fun _ h => let ⟨t, s', he, hq⟩ := code_ok hv hns hst h; ⟨t, s', he, hq.1, hq.2⟩, code_ct hv hns hst,
    satisfiableF⟩

end VG.Proof.RsaPkcs1Enc.X86.Front
