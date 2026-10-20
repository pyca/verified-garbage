module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.SgBase
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.VfPost
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Bignum.Arm.MaskBuffer
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem

/-!
# RSASSA-PKCS1-v1_5 signing on ARMv7: the encoding

The encoding of the hash value to `EM` (`encArgs_wp`, `encode_wp`), the
test of its success (`cmp_wp`), which depends only on public data
(`encOut_isNone`), and zeros and 0 when it fails (`zeroArgs_wp`, `zero_wp`,
`ret0_wp`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.Arm.Sg

open VG VG.Arm VG.Impl.RsaPkcs1Sig.Arm.Sign VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.RsaPkcs1Sig.Arm.Vf (EncR)
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_dp wp_cmp op2_imm op2_reg dpVal)

variable {P : EP}

/-- The hash value and the private key. -/
abbrev digB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.dig) P.dl
abbrev pB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.p) P.pl
abbrev qB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.q) P.ql
abbrev dpB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.dp) P.pl
abbrev dqB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.dq) P.ql
abbrev qiB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.qinv) P.pl

/-- The encoding, if any. -/
abbrev enc (P : EP) (σ : State) : Option (List Byte) := encOut P.hash.toNat (digB P σ) P.K

/-- What the function writes to `out` and returns. -/
def Res (P : EP) (σ : State) (m : Mem) (r : BitVec 32) : Prop :=
  Spec.Rsa.writtenOutcome m (State.addr P.out) P.K r
    (Spec.RsaPkcs1Sig.signId P.nB P.eB (pB P σ) (qB P σ) (dpB P σ) (dqB P σ) (qiB P σ) P.hash.toNat (digB P σ))

/-- Before `encode`. -/
def E1 (P : EP) (σ s : State) : Prop :=
  S P σ s ∧ s.gpr .r0 = P.B + BitVec.ofNat 32 oEM ∧ s.gpr .r1 = P.dig ∧ s.gpr .r2 = P.hash ∧
    s.gpr .r3 = BitVec.ofNat 32 P.K ∧ s.gpr .lr = BitVec.ofNat 32 P.dl

/-- After `encode`. -/
def E2 (P : EP) (σ s : State) : Prop := S P σ s ∧ EncR P.hash.toNat (digB P σ) P.K s.mem (P.lay.fr oEM) (s.gpr .r3)

/-- After the test of its success. -/
def E3 (P : EP) (σ s : State) : Prop := E2 P σ s ∧ s.z = (enc P σ).isNone

/-- Before the zeros. -/
def F1 (P : EP) (σ s : State) : Prop :=
  S P σ s ∧ enc P σ = none ∧ s.gpr .r0 = P.out ∧ s.gpr .lr = BitVec.ofNat 32 P.K ∧ s.gpr .r2 = 0

/-- `out` zeros. -/
def F2 (P : EP) (σ s : State) : Prop :=
  S P σ s ∧ enc P σ = none ∧ Spec.Rsa.bytesAt s.mem (State.addr P.out) P.K = List.replicate P.K 0

/-- The end of the body. -/
def Fin (P : EP) (σ s : State) : Prop := S P σ s ∧ Res P σ s.mem (s.gpr .r0)

/-- The encoding written. -/
def R0 (P : EP) (σ s : State) : Prop :=
  S P σ s ∧ ∃ em, enc P σ = some em ∧ Spec.Rsa.bytesAt s.mem (P.lay.fr oEM) P.K = em

/-! ## Whether the encoding succeeds -/

theorem encOut_isNone {id K : Nat} {D D' : List Byte} (h : D.length = D'.length) :
    (encOut id D K).isNone = (encOut id D' K).isNone := by
  unfold encOut
  cases Spec.RsaPkcs1Sig.Hash.ofId id with
  | none => rfl
  | some hh => simp only [encode_eq, h]; split <;> rfl

theorem enc_isNone (P : EP) (σ₁ σ₂ : State) : (enc P σ₁).isNone = (enc P σ₂).isNone :=
  encOut_isNone (by simp only [bytesAt_length])

theorem encR_r3 {id K : Nat} {D : List Byte} {m : Mem} {a : Addr} {ok : BitVec 32} (h : EncR id D K m a ok) :
    ok = if (encOut id D K).isNone then 0 else 1 := by
  unfold EncR at h
  split at h <;> simp_all

/-! ## The pieces -/

theorem encArgs_wp {σ s : State} (hs : S P σ s) : WP isa (.block encArgs) s (E1 P σ) := by
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  refine wp_dp (op2_imm (by decide)) fun t2 u2 => ?_
  have s2 : P.lay.St σ t2 := (hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem).of_rest
    (u2.rest (ws := [.r0]) (by simp)) u2.mem
  refine s2.wp_arg (j := 7) (by simp) (by dsimp only; decide) fun t3 s3 u3 => ?_
  refine s3.wp_arg (j := 6) (by simp) (by dsimp only; decide) fun t4 s4 u4 => ?_
  refine s4.wp_arg (j := 3) (by simp) (by dsimp only; decide) fun t5 s5 u5 => ?_
  refine s5.wp_arg (j := 8) (by simp) (by dsimp only; decide) fun t6 s6 u6 => WP.block_nil
    ⟨⟨hs.1, s6⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.gpr,
      dpVal, u1.gpr, hs.2.sp, BitVec.add_zero]
  · rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.gpr]; rfl
  · rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr]; rfl
  · rw [u6.other _ (by decide), u5.gpr]; rfl
  · rw [u6.gpr]; rfl

theorem encode_wp {σ s : State} (h : E1 P σ s) : WP isa Impl.RsaPkcs1Sig.Arm.encode s (E2 P σ) := by
  obtain ⟨hs, r0, r1, r2, r3, lr⟩ := h
  have ok := hs.1.ok
  have hK := hs.1.k1024
  have fit := ok.fit
  have e : State.addr (P.B + BitVec.ofNat 32 oEM) = P.lay.fr oEM :=
    ok.addrB (by show oEM < frameBytes + 56 + 68; decide)
  have hfd := ok.fits P.DIG (by simp)
  simp only [Proof.X25519.Arm.addr_toNat] at hfd
  have hin : EncIn s (P.B + BitVec.ofNat 32 oEM) P.dig P.hash P.K P.dl :=
    { r0 := r0, r1 := r1, r2 := r2, r3 := r3, lr := lr
      k64 := hs.1.k64, k1024 := hK, dl32 := hs.1.dl32
      dstFit := by
        rw [Proof.X25519.Arm.toNat_add_lt (by rw [BitVec.toNat_ofNat]; simp only [oEM, frameBytes] at fit ⊢; omega),
          BitVec.toNat_ofNat]
        simp only [oEM, frameBytes] at fit ⊢; omega
      srcFit := hfd
      write := by rw [e]; exact hs.2.inFr (by show oEM + P.K ≤ frameBytes; simp only [oEM, frameBytes]; omega)
      read := ⟨P.DIG, List.mem_append_left _ (by rw [hs.2.rd, ok.rd]; simp), Region.contains_self _ _⟩
      sep := by
        rw [e]
        exact (ok.stk_fr (R := P.DIG) (.inl (by simp)) (by simp only [oEM, frameBytes]; omega)).symm }
  refine WP.mono (encode_ok hin) fun t ⟨fr, rest, res⟩ => ?_
  rw [e] at fr
  have st' : P.lay.St σ t := hs.2.frameW (by show oEM + P.K ≤ frameBytes; simp only [oEM, frameBytes]; omega)
    fr rest.rd rest.wr rest.sp
  refine ⟨⟨hs.1, st'⟩, ?_⟩
  have hd : Spec.Rsa.bytesAt s.mem (State.addr P.dig) P.dl = digB P σ := hs.2.ro (R := P.DIG) (by simp)
  rw [hd, e] at res
  unfold EncR
  revert res
  cases encOut P.hash.toNat (digB P σ) P.K with
  | some em => exact fun r => r
  | none => exact fun r => r

theorem cmp_wp {σ s : State} (h : E2 P σ s) : WP isa (.block [.cmp .r3 (.imm 0)]) s (E3 P σ) := by
  obtain ⟨hs, er⟩ := h
  refine wp_cmp (op2_imm (by decide)) fun t1 u1 z1 => WP.block_nil
    ⟨⟨⟨hs.1, hs.2.of_rest (u1.rest []) u1.mem⟩, by rw [u1.mem, u1.gpr]; exact er⟩, ?_⟩
  rw [z1, encR_r3 er]
  show _ = (encOut P.hash.toNat (digB P σ) P.K).isNone
  cases encOut P.hash.toNat (digB P σ) P.K <;> simp

theorem zeroArgs_wp {σ s : State} (h : E3 P σ s ∧ isa.eval .eq s = some true) :
    WP isa (.block zeroArgs) s (F1 P σ) := by
  obtain ⟨⟨⟨hs, -⟩, z⟩, e⟩ := h
  have hn : enc P σ = none := by
    rw [Proof.X25519.Arm.eval_eq, z] at e; simpa using e
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  have s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  refine s1.wp_arg (j := 0) (by simp) (by dsimp only; decide) fun t2 s2 u2 => ?_
  refine s2.wp_arg (j := 3) (by simp) (by dsimp only; decide) fun t3 s3 u3 => ?_
  refine wp_mov (op2_imm (by decide)) fun t4 u4 => WP.block_nil
    ⟨⟨hs.1, s3.of_rest (u4.rest (ws := [.r2]) (by simp)) u4.mem⟩, hn, ?_, ?_, u4.gpr⟩
  · rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr]; rfl
  · rw [u4.other _ (by decide), u3.gpr]; rfl

theorem zero_wp {σ s : State} (h : F1 P σ s) : WP isa Impl.Bignum.Arm.maskBytes s (F2 P σ) := by
  obtain ⟨hs, hn, r0, lr, r2⟩ := h
  have ok := hs.1.ok
  have hfo := ok.fits P.OUT (by simp)
  simp only [Proof.X25519.Arm.addr_toNat] at hfo
  have hK := hs.1.k1024
  refine WP.mono (Bignum.Arm.maskBuffer_ok s (dst := P.out) (n := P.K) (by have := hs.1.k64; omega) (by omega)
    hfo ⟨P.OUT, by rw [hs.2.wr, ok.wr]; simp, Region.contains_self _ _⟩ r0 lr) fun t ⟨hb, fr, rst⟩ => ?_
  have st : P.lay.St σ t := hs.2.write fr (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨P.OUT, by simp, fun _ h => h⟩) rst.rd rst.wr rst.sp
  refine ⟨⟨hs.1, st⟩, hn, ?_⟩
  rw [hb, r2]
  apply List.ext_getElem (by simp [bytesAt_length])
  intro i h₁ h₂
  simp

theorem S.nB {σ s : State} (hs : S P σ s) : Spec.Rsa.bytesAt s.mem (State.addr P.n) P.K = P.nB :=
  (hs.2.ro (R := P.N) (by simp)).trans hs.1.nB

theorem S.eB {σ s : State} (hs : S P σ s) : Spec.Rsa.bytesAt s.mem (State.addr P.e) P.el = P.eB :=
  (hs.2.ro (R := P.E) (by simp)).trans hs.1.eB

theorem nB_length {σ : State} (h : In P σ) : P.nB.length = P.K := by rw [← h.nB, bytesAt_length]

/-- `signId` when the encoding fails. -/
theorem signId_none {σ : State} (h : In P σ) (hn : enc P σ = none) :
    Spec.RsaPkcs1Sig.signId P.nB P.eB (pB P σ) (qB P σ) (dpB P σ) (dqB P σ) (qiB P σ) P.hash.toNat (digB P σ) =
      .invalid := by
  unfold Spec.RsaPkcs1Sig.signId
  unfold enc encOut at hn
  split
  · rename_i hh e
    rw [e] at hn
    simp only at hn
    rw [Spec.RsaPkcs1Sig.sign, nB_length h, hn]
  · rfl

/-- `signId` when the encoding is `em`. -/
theorem signId_some {σ : State} (h : In P σ) {em : List Byte} (hs : enc P σ = some em) :
    Spec.RsaPkcs1Sig.signId P.nB P.eB (pB P σ) (qB P σ) (dpB P σ) (dqB P σ) (qiB P σ) P.hash.toNat (digB P σ) =
      Spec.Rsa.privateChecked P.nB P.eB em (pB P σ) (qB P σ) (dpB P σ) (dqB P σ) (qiB P σ) := by
  unfold Spec.RsaPkcs1Sig.signId
  unfold enc encOut at hs
  split
  · rename_i hh e
    rw [e] at hs
    simp only at hs
    rw [Spec.RsaPkcs1Sig.sign, nB_length h, hs]
  · rename_i e
    rw [e] at hs
    cases hs

theorem ret0_wp {σ s : State} (h : F2 P σ s) : WP isa (.block ret0) s (Fin P σ) := by
  obtain ⟨hs, hn, hz⟩ := h
  refine wp_mov (op2_imm (by decide)) fun t1 u1 => WP.block_nil
    ⟨⟨hs.1, hs.2.of_rest (u1.rest (ws := [.r0]) (by simp)) u1.mem⟩, ?_⟩
  rw [Res, signId_none hs.1 hn, u1.gpr, u1.mem]
  exact ⟨rfl, hz⟩

theorem r0_of {σ s : State} (h : E3 P σ s ∧ isa.eval .eq s = some false) : R0 P σ s := by
  obtain ⟨⟨⟨hs, er⟩, z⟩, e⟩ := h
  have hn : (enc P σ).isNone = false := by
    rw [Proof.X25519.Arm.eval_eq, z] at e; simpa using e
  refine ⟨hs, ?_⟩
  unfold EncR at er
  cases he : encOut P.hash.toNat (digB P σ) P.K with
  | none => have he' : enc P σ = none := he; rw [he'] at hn; cases hn
  | some em => rw [he] at er; exact ⟨em, he, er.2⟩

end VG.Proof.RsaPkcs1Sig.Arm.Sg
