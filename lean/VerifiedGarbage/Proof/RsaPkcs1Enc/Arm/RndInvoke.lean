module

-- separate module: its proofs (the call by its contract) build in parallel with `RndTail`'s, which `RndVerified` also imports

public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.RndScan
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Vp
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on ARMv7: the call

The call of `vg_rsa_pkcs1_encrypt_precomputed` (`call_vp`) by its contract,
`Pc.spec`, with `PS` the frame's: its precondition (`call_pre`), the same
public data in two runs (`call_pub`) and what it leaves (`C3`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.Arm.Rnd

open VG VG.Arm VG.Impl.RsaPkcs1Enc.Arm.Random VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.Rsa.Arm.Recover (VP)

variable {P : EP}

/-- The callee's stack. -/
theorem pcStack (c : PdImpl) :
    FrameStack.armStack (Impl.RsaPkcs1Enc.Arm.Precomputed.code c.name c.code) ≤ callStack := by
  have := c.stack
  simp only [Impl.RsaPkcs1Enc.Arm.Precomputed.code, Impl.RsaPkcs1Sig.Arm.wrap, Impl.RsaPkcs1Enc.Arm.Precomputed.body,
    Impl.RsaPkcs1Enc.Arm.Precomputed.psLoop, Impl.RsaPkcs1Enc.Arm.Precomputed.msgCopy, Impl.Bignum.Arm.copyBytes,
    Impl.Bignum.Arm.maskBytes, FrameStack.armStack, Impl.RsaPkcs1Sig.Arm.pushRegs, List.length_cons,
    List.length_nil, Impl.RsaPkcs1Enc.Arm.Precomputed.frameBytes, callStack]
  omega

/-- The callee's buffers. -/
abbrev cRd (P : EP) : List Region := [P.N, P.E, P.MSG, ⟨P.lay.fr oBuf, P.pl⟩, P.PRE, ⟨P.lay.Q, 40⟩]
abbrev cWr (P : EP) : List Region := [P.OUT, P.SCR]

section

variable {σ s : State}

theorem C2.args (h : C2 P σ s) : ∀ i < 10, stackArg s i = (outv P).getD i 0 := fun i hi => by
  rw [← h.2.1 i hi]
  simp only [stackArg, stackArgAddr, h.1.1.2.sp]
  rw [h.1.1.2.ok.addrB (by show 4 * i < frameBytes + 56 + 44; simp only [frameBytes]; omega)]

theorem call_pre (h : C2 P σ s) : Pc.spec.pre (s.callEntry.withRegions (cRd P) (cWr P)) := by
  have a := h.args
  obtain ⟨⟨hs, -, -, -⟩, -, r0, r1, r2, r3⟩ := h
  have ok := hs.1.ok
  have hK := hs.1.k1024
  have hml := hs.1.mlK
  have hel := hs.1.elK
  have hsl := hs.1.slK
  have hql := hs.1.qlK
  have fit := ok.fit
  have fS := ok.fits P.SCR (by simp)
  simp only [Proof.X25519.Arm.addr_toNat] at fS
  have k32 : P.K < 2 ^ 32 := by omega
  have el32 : P.el < 2 ^ 32 := by omega
  have ml32 : P.ml < 2 ^ 32 := by omega
  have pl32 : P.pl < 2 ^ 32 := by have := hs.1.pl_le; omega
  have sl32 : P.sl < 2 ^ 32 := by omega
  have ql32 : P.ql < 2 ^ 32 := by
    rw [hql]; simp only [Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords]; omega
  have a0 : stackArg s 0 = P.e := a 0 (by decide)
  have a1 : stackArg s 1 = BitVec.ofNat 32 P.el := a 1 (by decide)
  have a2 : stackArg s 2 = P.msg := a 2 (by decide)
  have a3 : stackArg s 3 = BitVec.ofNat 32 P.ml := a 3 (by decide)
  have a4 : stackArg s 4 = P.B + BitVec.ofNat 32 oBuf := a 4 (by decide)
  have a5 : stackArg s 5 = BitVec.ofNat 32 P.pl := a 5 (by decide)
  have a6 : stackArg s 6 = P.scr := a 6 (by decide)
  have a7 : stackArg s 7 = BitVec.ofNat 32 P.sl := a 7 (by decide)
  have a8 : stackArg s 8 = P.pre := a 8 (by decide)
  have a9 : stackArg s 9 = BitVec.ofNat 32 P.ql := a 9 (by decide)
  have sa : stackArgAddr s 0 = State.addr P.B := by simp [stackArgAddr, hs.2.sp]
  have e40 : BitVec.setWidth 64 (P.B + BitVec.ofNat 32 oBuf) = P.lay.fr oBuf :=
    ok.addrB (by show oBuf < frameBytes + 56 + 44; decide)
  have q0 : State.addr P.B = P.lay.fr 0 := by simp
  have hps : oBuf + P.pl ≤ frameBytes + 56 := by simp only [oBuf, frameBytes]; have := hs.1.pl_le; omega
  sig_pre [Pc.spec, Pc.stackBytes, Impl.RsaPkcs1Enc.Arm.Precomputed.frameBytes,
    Proof.RsaPkcs1Enc.encryptPrecomputedContract, Proof.RsaPkcs1Enc.encryptPrecomputedSig, abi, argRegs,
    reduceClassify, Loc.val]
  simp only [stackArg_call, stackArgAddr_call, r0, r1, r2, r3, a0, a1, a2, a3,
    a4, a5, a6, a7, a8, a9, sa, hs.2.sp, BitVec.toNat_ofNat, Nat.mod_eq_of_lt k32, Nat.mod_eq_of_lt el32,
    Nat.mod_eq_of_lt ml32, Nat.mod_eq_of_lt pl32, Nat.mod_eq_of_lt sl32, Nat.mod_eq_of_lt ql32, e40]
  have hfr : ∀ {R : Region}, R ∈ P.lay.ro ∨ R ∈ P.lay.rw → ∀ {d n : Nat}, d + n ≤ frameBytes + 56 →
      Region.Disjoint ⟨P.lay.fr d, n⟩ R := fun hR _ _ hd => ok.stk_fr hR hd
  have fs : ∀ {R : Region}, R ∈ P.lay.ro ++ P.lay.rw → R.base.toNat + R.len ≤ 2 ^ 32 := fun hR => ok.fits _ hR
  have hB := ok.B56
  have hpsF : (P.B + BitVec.ofNat 32 oBuf).toNat = P.B.toNat + oBuf := by
    rw [Proof.X25519.Arm.toNat_add_lt (by simp only [oBuf, frameBytes] at fit ⊢; rw [BitVec.toNat_ofNat]; omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide)]
  have kA : P.lay.LOW.Disjoint ⟨State.addr P.B, 40⟩ := by
    have := (Lay.fr_low (L := P.lay) (d := 0) (n := 40) (by decide) (show 1168 ≤ 2 ^ 32 by decide)).symm
    rwa [← q0] at this
  have kP : P.lay.LOW.Disjoint ⟨P.lay.fr oBuf, P.pl⟩ :=
    (Lay.fr_low (L := P.lay) (by simp only [oBuf, frameBytes] at hps ⊢; omega) (show 1168 ≤ 2 ^ 32 by decide)).symm
  refine ⟨hB, by simp only [frameBytes] at fit; omega, rfl, rfl,
    ok.rw_ro (w := P.OUT) (r := P.N) (by simp) (by simp), ok.rw_ro (w := P.OUT) (r := P.E) (by simp) (by simp),
    ok.rw_ro (w := P.OUT) (r := P.MSG) (by simp) (by simp),
    (hfr (R := P.OUT) (.inr (by simp)) hps).symm, hs.1.dOS, ok.rw_ro (w := P.OUT) (r := P.PRE) (by simp) (by simp),
    by rw [q0]; exact (hfr (R := P.OUT) (.inr (by simp)) (by decide)).symm,
    (ok.rw_ro (w := P.SCR) (r := P.N) (by simp) (by simp)).symm,
    (ok.rw_ro (w := P.SCR) (r := P.E) (by simp) (by simp)).symm,
    (ok.rw_ro (w := P.SCR) (r := P.MSG) (by simp) (by simp)).symm,
    hfr (R := P.SCR) (.inr (by simp)) hps, ok.rw_ro (w := P.SCR) (r := P.PRE) (by simp) (by simp),
    by rw [q0]; exact (hfr (R := P.SCR) (.inr (by simp)) (by decide)).symm,
    ?_⟩
  refine ⟨ok.low_buf (R := P.OUT) (.inr (by simp)), ok.low_buf (R := P.N) (.inl (by simp)),
    ok.low_buf (R := P.E) (.inl (by simp)), ok.low_buf (R := P.MSG) (.inl (by simp)),
    kP, ok.low_buf (R := P.SCR) (.inr (by simp)), ok.low_buf (R := P.PRE) (.inl (by simp)),
    kA, by have := fs (R := P.OUT) (by simp); simpa [Proof.X25519.Arm.addr_toNat] using this,
    by have := fs (R := P.N) (by simp); simpa [Proof.X25519.Arm.addr_toNat] using this,
    by have := fs (R := P.E) (by simp); simpa [Proof.X25519.Arm.addr_toNat] using this,
    by have := fs (R := P.MSG) (by simp); simpa [Proof.X25519.Arm.addr_toNat] using this,
    by rw [hpsF]; simp only [oBuf, frameBytes] at fit hps ⊢; omega,
    fS,
    by have := fs (R := P.PRE) (by simp); simpa [Proof.X25519.Arm.addr_toNat] using this,
    hs.1.kv, trivial, hs.1.el1, hel, hml, trivial, hsl, hql⟩

theorem S.nB {s : State} (hs : S P σ s) : Spec.Rsa.bytesAt s.mem (BitVec.setWidth 64 P.n) P.K = P.nB :=
  (hs.2.ro (R := P.N) (by simp)).trans hs.1.nB

theorem S.eB {s : State} (hs : S P σ s) : Spec.Rsa.bytesAt s.mem (BitVec.setWidth 64 P.e) P.el = P.eB :=
  (hs.2.ro (R := P.E) (by simp)).trans hs.1.eB

theorem S.pw {s : State} (hs : S P σ s) : Spec.Rsa.wordsAt s.mem (BitVec.setWidth 64 P.pre) P.ql = P.pw :=
  (hs.2.ro_words (R := P.PRE) (by simp) rfl).trans hs.1.pw

theorem S.msg {s : State} (hs : S P σ s) : Spec.Rsa.bytesAt s.mem (BitVec.setWidth 64 P.msg) P.ml = msgB P σ :=
  hs.2.ro (R := P.MSG) (by simp)

theorem K1.ps (h : K1 P σ s) :
    Spec.Rsa.bytesAt s.mem (BitVec.setWidth 64 (P.B + BitVec.ofNat 32 oBuf)) P.pl = kept P σ (N P) := by
  obtain ⟨hs, hf, buf, -⟩ := h
  have e40 : BitVec.setWidth 64 (P.B + BitVec.ofNat 32 oBuf) = P.lay.fr oBuf :=
    hs.2.ok.addrB (by show oBuf < frameBytes + 56 + 44; decide)
  rw [e40, ← hf]
  exact bytesAt_eq fun i hi => by rw [Offset.add_ofNat_add_ofNat]; exact buf i hi

theorem call_pub {σ₁ σ₂ s₁ s₂ : State} (h₁ : C2 P σ₁ s₁) (h₂ : C2 P σ₂ s₂) (rd wr : List Region) :
    Pc.spec.pub (s₁.callEntry.withRegions rd wr) (s₂.callEntry.withRegions rd wr) := by
  have a₁ := h₁.args
  have a₂ := h₂.args
  have hs₁ := h₁.1.1
  have hs₂ := h₂.1.1
  have hK := hs₁.1.k1024
  have k32 : P.K < 2 ^ 32 := by omega
  have el32 : P.el < 2 ^ 32 := by have := hs₁.1.elK; omega
  have ql32 : P.ql < 2 ^ 32 := by
    rw [hs₁.1.qlK]; simp only [Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords]; omega
  sig_pub [Pc.spec, Pc.stackBytes, Impl.RsaPkcs1Enc.Arm.Precomputed.frameBytes,
    Proof.RsaPkcs1Enc.encryptPrecomputedContract, Proof.RsaPkcs1Enc.encryptPrecomputedSig, abi, argRegs,
    reduceClassify, Loc.val]
  simp only [stackArg_call, h₁.2.2.1, h₁.2.2.2.1, h₁.2.2.2.2.1, h₁.2.2.2.2.2, h₂.2.2.1, h₂.2.2.2.1, h₂.2.2.2.2.1,
    h₂.2.2.2.2.2, a₁ 0 (by decide), a₁ 1 (by decide), a₁ 2 (by decide), a₁ 3 (by decide), a₁ 4 (by decide),
    a₁ 5 (by decide), a₁ 6 (by decide), a₁ 7 (by decide), a₁ 8 (by decide), a₁ 9 (by decide),
    a₂ 0 (by decide), a₂ 1 (by decide), a₂ 2 (by decide), a₂ 3 (by decide), a₂ 4 (by decide),
    a₂ 5 (by decide), a₂ 6 (by decide), a₂ 7 (by decide), a₂ 8 (by decide), a₂ 9 (by decide),
    List.getD_cons_zero, List.getD_cons_succ, hs₁.2.sp, hs₂.2.sp, BitVec.toNat_ofNat, Nat.mod_eq_of_lt k32,
    Nat.mod_eq_of_lt el32, Nat.mod_eq_of_lt ql32, and_true, true_and]
  rw [hs₁.nB, hs₂.nB, hs₁.eB, hs₂.eB, hs₁.pw, hs₂.pw]

theorem call_post {s' : State} (h : C2 P σ s) (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) (sp : s'.sp = s.sp)
    (fr : Frame (cWr P ++ [FrameStack.belowA s.sp callStack]) s.mem s'.mem)
    (po : Pc.spec.post (s.callEntry.withRegions (cRd P) (cWr P)) (s'.withRegions (cRd P) (cWr P))) :
    C3 P σ s' := by
  have a := h.args
  have k1 := h.1
  obtain ⟨⟨hs, hf, buf, tw⟩, -, r0, r1, r2, r3⟩ := h
  have ok := hs.1.ok
  have hK := hs.1.k1024
  have hpl := hs.1.pl_le
  have k32 : P.K < 2 ^ 32 := by omega
  have el32 : P.el < 2 ^ 32 := by have := hs.1.elK; omega
  have ml32 : P.ml < 2 ^ 32 := by have := hs.1.mlK; omega
  have pl32 : P.pl < 2 ^ 32 := by omega
  have ql32 : P.ql < 2 ^ 32 := by
    rw [hs.1.qlK]; simp only [Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords]; omega
  have low : FrameStack.belowA s.sp callStack = P.lay.LOW := by rw [hs.2.sp]; exact ok.low_eq
  rw [low] at fr
  have fr' : Frame [P.OUT, P.SCR, P.lay.LOW] s.mem s'.mem := fr
  have st : P.lay.St σ s' := hs.2.write fr' (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨P.OUT, by simp, fun _ h => h⟩
    · exact ⟨P.SCR, by simp, fun _ h => h⟩
    · exact ⟨P.lay.LOW, by simp, fun _ h => h⟩) rd wr sp
  have hps : oBuf + P.pl ≤ frameBytes + 56 := by simp only [oBuf, frameBytes]; omega
  refine ⟨⟨⟨hs.1, st⟩, hf, buf.frame fr' fun r hr => ?_, tw.frame fr' fun r hr => ?_⟩, fun hq => ?_⟩
  · have hl : (kept P σ (N P)).length = P.pl := hf
    rw [hl]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ok.stk_fr (.inr (by simp)) hps
    · exact ok.stk_fr (.inr (by simp)) hps
    · exact Lay.fr_low (L := P.lay) (by simp only [oBuf, frameBytes] at hps ⊢; omega) (show 1168 ≤ 2 ^ 32 by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hs.1.dOT.symm
    · exact hs.1.dTS
    · exact hs.1.tapeLow
  · sig_post [Pc.spec, Pc.stackBytes, Impl.RsaPkcs1Enc.Arm.Precomputed.frameBytes,
      Proof.RsaPkcs1Enc.encryptPrecomputedContract, Proof.RsaPkcs1Enc.encryptPrecomputedSig, abi, argRegs,
      reduceClassify, Loc.val] at po
    simp only [stackArg_call, r0, r2, r3, a 0 (by decide), a 1 (by decide), a 2 (by decide), a 3 (by decide),
      a 4 (by decide), a 5 (by decide), a 8 (by decide), a 9 (by decide), List.getD_cons_zero, List.getD_cons_succ,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt k32, Nat.mod_eq_of_lt el32, Nat.mod_eq_of_lt ml32,
      Nat.mod_eq_of_lt pl32, Nat.mod_eq_of_lt ql32] at po
    rw [BitVec.setWidth_append_eq_right, hs.nB, hs.eB, hs.pw, hs.msg, k1.ps] at po
    exact po hq

theorem call_vp (encName : String) (c : PdImpl) :
    VP (C2 P) (.call encName (Impl.RsaPkcs1Enc.Arm.Precomputed.code c.name c.code)) (C3 P) := by
  refine VP.callF (Pc.code_verified c) (pcStack c) (cRd P) (cWr P) (fun _ _ h => call_pre h) (fun σ s h => ?_)
    (fun σ s h => ?_) (fun _ _ _ _ h₁ h₂ => call_pub h₁ h₂ _ _) (fun σ s s' h rd wr sp fr _ po =>
      call_post h rd wr sp fr po)
  · have hs := h.1.1
    have ok := hs.1.ok
    have hK := hs.1.k1024
    have hpl := hs.1.pl_le
    have hro : ∀ R ∈ P.lay.ro, Covers [R] (s.rd ++ s.wr) := fun R hR =>
      Covers.left (Covers.of_mem fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hs.2.rd, ok.rd]; exact List.mem_append_left _ hR)
    have hrw : ∀ R ∈ P.lay.rw, Covers [R] s.wr := fun R hR =>
      Covers.of_mem fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hs.2.wr, ok.wr]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hR)
    have wr : Covers (cWr P) s.wr := (hrw P.OUT (by simp)).cons (hrw P.SCR (by simp))
    have q : P.lay.Q = P.lay.fr 0 := by simp
    refine ⟨Covers.append_left ((hro P.N (by simp)).cons ((hro P.E (by simp)).cons ((hro P.MSG (by simp)).cons
      (Covers.cons ?_ ((hro P.PRE (by simp)).cons (Covers.cons ?_ Covers.nil)))))) wr.right, wr⟩
    · exact (Covers.one (hs.2.inFr (by show oBuf + P.pl ≤ frameBytes; simp only [oBuf, frameBytes]; omega))).right
    · rw [q]; exact (Covers.one (hs.2.inFr (by show 0 + 40 ≤ frameBytes; decide))).right
  · rw [h.1.1.2.sp]; exact h.1.1.1.ok.B56

end

end VG.Proof.RsaPkcs1Enc.Arm.Rnd
