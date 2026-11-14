module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.VfBase
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Encode
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Callees
public import VerifiedGarbage.Proof.Rsa.Arm.Stage.VP
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Vp
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.Arm.CompareBuffer
import VerifiedGarbage.Proof.Rsa.Arm.PrivMask
import VerifiedGarbage.Proof.RsaPkcs1Sig.Verify
import VerifiedGarbage.Proof.Rsa.ZeroTest32

/-! ### `RsaPkcs1Sig.Arm.VfCall`, which only this module used -/

section

/-! ### `RsaPkcs1Sig.Arm.VfPieces`, which only this module used -/

section

/-!
# RSASSA-PKCS1-v1_5 verification with a precomputed public key on ARMv7: up to the call

The stages up to the call and the correctness of the pieces between them:
the check of the lengths (`lenCheck_wp`, `cmp_wp`), the result 0 when they
differ (`ret0_wp`), and the call's arguments (`callArgs_wp`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.Arm.Vf

open VG VG.Arm VG.Impl.RsaPkcs1Sig.Arm.Precomputed VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_dp wp_cmp op2_imm op2_reg dpVal)

variable {P : EP}

/-- The hash value and the signature. -/
abbrev digB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.dig) P.dl
abbrev sigB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.sig) P.gl

/-- What the function returns, for every modulus whose precomputed values
are `pre`'s. -/
def Res (P : EP) (σ : State) (r : BitVec 32) : Prop :=
  ∀ nB : List Byte, nB.length = P.K → Spec.Rsa.publicPrecompute nB = some P.pw →
    r = if Spec.RsaPkcs1Sig.verifyId nB P.eB P.hash.toNat (digB P σ) (sigB P σ) then 1 else 0

/-- After `lenCheck`. -/
def H1 (P : EP) (σ s : State) : Prop := S P σ s ∧ s.gpr .r0 = BitVec.ofNat 32 P.gl - BitVec.ofNat 32 P.K

/-- After the comparison of the lengths. -/
def H2 (P : EP) (σ s : State) : Prop := S P σ s ∧ s.z = decide (P.gl = P.K)

/-- The end of the body. -/
def Fin (P : EP) (σ s : State) : Prop := S P σ s ∧ Res P σ (s.gpr .r0)

/-- Once the lengths are equal. -/
def C0 (P : EP) (σ s : State) : Prop := S P σ s ∧ P.gl = P.K

/-- The call's stack arguments. -/
abbrev outv (P : EP) : List (BitVec 32) :=
  [P.e, BitVec.ofNat 32 P.el, P.sig, BitVec.ofNat 32 P.K, P.scr, BitVec.ofNat 32 P.sl]

def OutA (P : EP) (s : State) : Prop := ∀ i < 6, s.mem.readW (P.lay.fr (4 * i)) 32 = (outv P).getD i 0

/-- Before the call. -/
def C1 (P : EP) (σ s : State) : Prop :=
  C0 P σ s ∧ OutA P s ∧ s.gpr .r0 = P.B + BitVec.ofNat 32 oEM1 ∧ s.gpr .r1 = BitVec.ofNat 32 P.K ∧
    s.gpr .r2 = P.pre ∧ s.gpr .r3 = BitVec.ofNat 32 P.rl

theorem lenCheck_wp {σ s : State} (hs : S P σ s) : WP isa (.block lenCheck) s (H1 P σ) := by
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  have s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  refine s1.wp_arg (j := 8) (by simp) (by dsimp only; decide) fun t2 s2 u2 => ?_
  refine s2.wp_arg (j := 1) (by simp) (by dsimp only; decide) fun t3 s3 u3 => ?_
  refine wp_dp (op2_reg _ _) fun t4 u4 => WP.block_nil
    ⟨⟨hs.1, s3.of_rest (u4.rest (ws := [.r0]) (by simp)) u4.mem⟩, ?_⟩
  rw [u4.gpr, dpVal, u3.other _ (by decide), u2.gpr, u3.gpr]; rfl

theorem cmp_wp {σ s : State} (h : H1 P σ s) : WP isa (.block [.cmp .r0 (.imm 0)]) s (H2 P σ) := by
  obtain ⟨hs, r0⟩ := h
  have hK := hs.1.k1024
  refine wp_cmp (op2_imm (by decide)) fun t1 u1 z1 => WP.block_nil
    ⟨⟨hs.1, hs.2.of_rest (u1.rest []) u1.mem⟩, ?_⟩
  have e : ∀ x : BitVec 32, x - 0 = x := fun x => by simp
  rw [z1, r0, e, cmp_eq hs.1.gl32 (by omega_using [hK])]

theorem verifyId_len {nB eB D sig : List Byte} {id : Nat} (h : sig.length ≠ nB.length) :
    Spec.RsaPkcs1Sig.verifyId nB eB id D sig = false := by
  unfold Spec.RsaPkcs1Sig.verifyId
  split
  · rw [Spec.RsaPkcs1Sig.verify, ite_eq_right h]
  · rfl

theorem ret0_wp {σ s : State} (h : H2 P σ s ∧ isa.eval .ne s = some true) :
    WP isa (.block ret0) s (Fin P σ) := by
  obtain ⟨⟨hs, z⟩, e⟩ := h
  have hne : P.gl ≠ P.K := by
    rw [Proof.X25519.Arm.eval_ne, z] at e; simpa using e
  refine wp_mov (op2_imm (by decide)) fun t1 u1 => WP.block_nil
    ⟨⟨hs.1, hs.2.of_rest (u1.rest (ws := [.r0]) (by simp)) u1.mem⟩, fun nB hn _ => ?_⟩
  rw [u1.gpr, verifyId_len (by rw [bytesAt_length, hn]; exact hne)]
  rfl

theorem c0_of {σ s : State} (h : H2 P σ s ∧ isa.eval .ne s = some false) : C0 P σ s := by
  obtain ⟨⟨hs, z⟩, e⟩ := h
  refine ⟨hs, ?_⟩
  rw [Proof.X25519.Arm.eval_ne, z] at e; simpa using e

theorem callArgs_wp {σ s : State} (h : C0 P σ s) : WP isa (.block callArgs) s (C1 P σ) := by
  obtain ⟨hs, hgl⟩ := h
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t0 u0 => ?_
  have s0 : P.lay.St σ t0 := hs.2.of_rest (u0.rest (ws := [.r12]) (by simp)) u0.mem
  have r12 : t0.gpr .r12 = P.B := by rw [u0.gpr, hs.2.sp, BitVec.add_zero]
  refine s0.wp_copyArg (j := 2) (d := 0) r12 (by simp) (by dsimp only; decide) (by dsimp only; decide)
    (by decide) (by decide) fun t1 s1 v1 g1 m1 => ?_
  refine s1.wp_copyArg (j := 3) (d := 4) (by rw [g1 _ (by decide), r12]) (by simp) (by dsimp only; decide)
    (by dsimp only; decide) (by decide) (by decide) fun t2 s2 v2 g2 m2 => ?_
  refine s2.wp_copyArg (j := 7) (d := 8) (by rw [g2 _ (by decide), g1 _ (by decide), r12]) (by simp)
    (by dsimp only; decide) (by dsimp only; decide) (by decide) (by decide) fun t3 s3 v3 g3 m3 => ?_
  refine s3.wp_copyArg (j := 1) (d := 12) (by rw [g3 _ (by decide), g2 _ (by decide), g1 _ (by decide), r12])
    (by simp) (by dsimp only; decide) (by dsimp only; decide) (by decide) (by decide) fun t4 s4 v4 g4 m4 => ?_
  have r12' : t4.gpr .r12 = P.B := by
    rw [g4 _ (by decide), g3 _ (by decide), g2 _ (by decide), g1 _ (by decide), r12]
  refine s4.wp_copyArg (j := 9) (d := 16) r12' (by simp) (by dsimp only; decide) (by dsimp only; decide)
    (by decide) (by decide) fun t5 s5 v5 g5 m5 => ?_
  refine s5.wp_copyArg (j := 10) (d := 20) (by rw [g5 _ (by decide), r12']) (by simp) (by dsimp only; decide)
    (by dsimp only; decide) (by decide) (by decide) fun t6 s6 v6 g6 m6 => ?_
  refine wp_dp (op2_imm (by decide)) fun t7 u7 => ?_
  have s7 : P.lay.St σ t7 := s6.of_rest (u7.rest (ws := [.r0]) (by simp)) u7.mem
  refine s7.wp_arg (j := 1) (by simp) (by dsimp only; decide) fun t8 s8 u8 => ?_
  refine s8.wp_arg (j := 11) (by simp) (by dsimp only; decide) fun t9 s9 u9 => ?_
  refine s9.wp_arg (j := 12) (by simp) (by dsimp only; decide) fun t10 s10 u10 => WP.block_nil ?_
  have mm : t10.mem = t6.mem := by rw [u10.mem, u9.mem, u8.mem, u7.mem]
  refine ⟨⟨⟨hs.1, s10⟩, hgl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [mm, m6]
    have w : ∀ (m : Mem) (d e : Nat) (v : BitVec 32), d + 4 ≤ e ∨ e + 4 ≤ d → d + 4 ≤ 24 → e + 4 ≤ 24 →
        (m.writeW (P.lay.fr e) v).readW (P.lay.fr d) 32 = m.readW (P.lay.fr d) 32 :=
      fun m d e v h hd he => Lay.readW_fr_other _ _ _ h (by omega_using [hd]) (by omega_using [he])
    rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [w _ _ _ _ (by decide) (by decide) (by decide), m5, w _ _ _ _ (by decide) (by decide) (by decide), m4,
        w _ _ _ _ (by decide) (by decide) (by decide), m3, w _ _ _ _ (by decide) (by decide) (by decide), m2,
        w _ _ _ _ (by decide) (by decide) (by decide), m1]
      exact Mem.readW_writeW_self32 _ _ _
    · rw [w _ _ _ _ (by decide) (by decide) (by decide), m5, w _ _ _ _ (by decide) (by decide) (by decide), m4,
        w _ _ _ _ (by decide) (by decide) (by decide), m3, w _ _ _ _ (by decide) (by decide) (by decide), m2]
      exact Mem.readW_writeW_self32 _ _ _
    · rw [w _ _ _ _ (by decide) (by decide) (by decide), m5, w _ _ _ _ (by decide) (by decide) (by decide), m4,
        w _ _ _ _ (by decide) (by decide) (by decide), m3]
      exact Mem.readW_writeW_self32 _ _ _
    · rw [w _ _ _ _ (by decide) (by decide) (by decide), m5, w _ _ _ _ (by decide) (by decide) (by decide), m4]
      exact Mem.readW_writeW_self32 _ _ _
    · rw [w _ _ _ _ (by decide) (by decide) (by decide), m5]
      exact Mem.readW_writeW_self32 _ _ _
    · exact Mem.readW_writeW_self32 _ _ _
  · rw [u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide), u7.gpr, dpVal,
      g6 _ (by decide), g5 _ (by decide), r12']
  · rw [u10.other _ (by decide), u9.other _ (by decide), u8.gpr]; rfl
  · rw [u10.other _ (by decide), u9.gpr]; rfl
  · rw [u10.gpr]; rfl

end VG.Proof.RsaPkcs1Sig.Arm.Vf

end

end


/-!
# RSASSA-PKCS1-v1_5 verification with a precomputed public key on ARMv7: the call

The call of `vg_rsa_public_precomputed_checked` (`call_vp`, correct and
constant time: its arguments and the public data it reads are the same in
two runs), which writes `EM₁` and returns its status (`CR`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.Arm.Vf

open VG VG.Arm VG.Impl.RsaPkcs1Sig.Arm.Precomputed VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.Rsa.Arm.Recover (VP)

variable {P : EP}

/-- What the call writes to `EM₁` and returns. -/
def CR (P : EP) (σ : State) (m : Mem) (r : BitVec 32) : Prop :=
  ∀ nB : List Byte, nB.length = P.K → Spec.Rsa.publicPrecompute nB = some P.pw →
    Spec.Rsa.written m (P.lay.fr oEM1) P.K r (Spec.Rsa.publicOpChecked nB P.eB (sigB P σ))

/-- After the call. -/
def C2 (P : EP) (σ s : State) : Prop := C0 P σ s ∧ CR P σ s.mem (s.gpr .r0)

theorem C1.pdArgs {σ s : State} (h : C1 P σ s) :
    PdArgs s (P.B + BitVec.ofNat 32 oEM1) P.pre P.e P.sig P.scr P.K P.el P.rl P.sl := by
  obtain ⟨⟨hs, -⟩, oa, r0, r1, r2, r3⟩ := h
  have a : ∀ i < 6, stackArg s i = (outv P).getD i 0 := fun i hi => by
    rw [← oa i hi]
    simp only [stackArg, stackArgAddr, hs.2.sp]
    rw [hs.2.ok.addrB (by show 4 * i < frameBytes + 56 + 36; simp only [frameBytes]; omega_using [hi])]
  have h1 := hs.1
  exact ⟨r0, r1, r2, r3, a 0 (by decide), a 1 (by decide), a 2 (by decide), a 3 (by decide), a 4 (by decide),
    a 5 (by decide), h1.kv, h1.rlK, h1.el1, h1.elK, h1.slK,
    by have := hs.1.ok.fits P.SCR (by simp); simp only [Proof.X25519.Arm.addr_toNat] at this; omega_using [this]⟩

/-- `EM₁`, as the call writes it. -/
theorem outA (P : EP) {σ : State} (h : In P σ) : State.addr (P.B + BitVec.ofNat 32 oEM1) = P.lay.fr oEM1 :=
  h.ok.addrB (by show oEM1 < frameBytes + 56 + 36; decide)

theorem call_pre {σ s : State} (h : C1 P σ s) :
    (Proof.Rsa.publicPrecomputedCheckedContract abi 56).pre
      (s.callEntry.withRegions (pdRd P.B P.pre P.e P.sig P.K P.el P.rl)
        (pdWr (P.B + BitVec.ofNat 32 oEM1) P.scr P.K P.sl)) := by
  have hs := h.1.1
  have hgl := h.1.2
  have ok := hs.1.ok
  have hK := hs.1.k1024
  have fit := ok.fit
  have hB := ok.B56
  have e := outA P hs.1
  have hfr : ∀ {R : Region}, R ∈ P.lay.ro ∨ R ∈ P.lay.rw → ∀ {d n : Nat}, d + n ≤ frameBytes + 56 →
      Region.Disjoint ⟨P.lay.fr d, n⟩ R := fun hR _ _ hd => ok.stk_fr hR hd
  have fs := fun {R : Region} (hR : R ∈ P.lay.ro ++ P.lay.rw) => ok.fits R hR
  have q0 : State.addr P.B = P.lay.fr 0 := by simp
  have sigR : (⟨State.addr P.sig, P.K⟩ : Region) = P.SIG := by rw [← hgl]
  refine pd_pre h.pdArgs hs.2.sp (by omega) (by simp only [frameBytes] at fit; omega_using [fit])
    (by rw [show (P.B + BitVec.ofNat 32 oEM1).toNat = P.B.toNat + oEM1 from
          Proof.X25519.Arm.toNat_add_lt (by simp only [oEM1, frameBytes] at fit ⊢; rw [BitVec.toNat_ofNat]; omega_using [fit]) |>.trans
          (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide)])]
        simp only [oEM1, frameBytes] at fit ⊢; omega_using [hK, fit])
    (by have := fs (R := P.PRE) (by simp); simpa [Proof.X25519.Arm.addr_toNat] using this)
    (by have := fs (R := P.E) (by simp); simpa [Proof.X25519.Arm.addr_toNat] using this)
    (by have := fs (R := P.SIG) (by simp); simp only [Proof.X25519.Arm.addr_toNat] at this; omega_using [hgl, this])
    (by have := fs (R := P.SCR) (by simp); simpa [Proof.X25519.Arm.addr_toNat] using this)
    (by rw [e]; exact hfr (R := P.PRE) (.inl (by simp)) (by simp only [oEM1, frameBytes]; omega_using [hK]))
    (by rw [e]; exact hfr (R := P.E) (.inl (by simp)) (by simp only [oEM1, frameBytes]; omega_using [hK]))
    (by rw [e, sigR]; exact hfr (R := P.SIG) (.inl (by simp)) (by simp only [oEM1, frameBytes]; omega_using [hK]))
    (by rw [e]; exact hfr (R := P.SCR) (.inr (by simp)) (by simp only [oEM1, frameBytes]; omega_using [hK]))
    (by rw [e, q0]; exact Lay.fr_sep (by simp only [oEM1]; omega_using []) (by simp only [oEM1]; omega_using [hK]) (by decide))
    (ok.rw_ro (by simp) (by simp)).symm (ok.rw_ro (by simp) (by simp)).symm
    (by rw [sigR]; exact (ok.rw_ro (by simp) (by simp)).symm)
    (by rw [q0]; exact (hfr (R := P.SCR) (.inr (by simp)) (by decide)).symm) ?_
  intro r hr
  have low : (⟨State.addr P.B - BitVec.ofNat 64 56, 56⟩ : Region) = P.lay.LOW := rfl
  rw [low]
  simp only [pdRd, pdWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ok.low_buf (R := P.PRE) (.inl (by simp))
  · exact ok.low_buf (R := P.E) (.inl (by simp))
  · rw [sigR]; exact ok.low_buf (R := P.SIG) (.inl (by simp))
  · rw [q0]; exact (Lay.fr_low (by decide)).symm
  · rw [e]; exact (Lay.fr_low (by simp only [oEM1]; omega_using [hK])).symm
  · exact ok.low_buf (R := P.SCR) (.inr (by simp))

theorem S.eB {σ s : State} (hs : S P σ s) : Spec.Rsa.bytesAt s.mem (State.addr P.e) P.el = P.eB :=
  (hs.2.ro (R := P.E) (by simp)).trans hs.1.eB

theorem S.pw {σ s : State} (hs : S P σ s) : Spec.Rsa.wordsAt s.mem (State.addr P.pre) P.rl = P.pw :=
  (hs.2.ro_words (R := P.PRE) (by simp) rfl).trans hs.1.pw

theorem call_vp (c : PdImpl) : VP (C1 P) (.call c.name c.code) (C2 P) := by
  refine VP.callF c.verified c.stack (pdRd P.B P.pre P.e P.sig P.K P.el P.rl)
    (pdWr (P.B + BitVec.ofNat 32 oEM1) P.scr P.K P.sl) (fun _ _ h => call_pre h) (fun σ s h => ?_)
    (fun σ s h => ?_) (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) (fun σ s s' h rd wr sp fr _ po => ?_)
  · have hs := h.1.1
    have hgl := h.1.2
    have ok := hs.1.ok
    have hK := hs.1.k1024
    have e := outA P hs.1
    have q0 : State.addr P.B = P.lay.fr 0 := by simp
    have hro : ∀ R ∈ P.lay.ro, Covers [R] (s.rd ++ s.wr) := fun R hR =>
      Covers.left (Covers.of_mem fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hs.2.rd, ok.rd]; exact List.mem_append_left _ hR)
    have hrw : ∀ R ∈ P.lay.rw, Covers [R] s.wr := fun R hR =>
      Covers.of_mem fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hs.2.wr, ok.wr]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hR)
    have wr : Covers (pdWr (P.B + BitVec.ofNat 32 oEM1) P.scr P.K P.sl) s.wr := by
      refine Covers.cons ?_ (hrw P.SCR (by simp))
      rw [e]; exact Covers.one (hs.2.inFr (by show oEM1 + P.K ≤ frameBytes; simp only [oEM1, frameBytes]; omega_using [hK]))
    have sigR : (⟨State.addr P.sig, P.K⟩ : Region) = P.SIG := by rw [← hgl]
    refine ⟨Covers.append_left ((hro P.PRE (by simp)).cons ((hro P.E (by simp)).cons ?_)) wr.right, wr⟩
    refine Covers.cons ?_ (Covers.cons ?_ Covers.nil)
    · rw [sigR]; exact hro P.SIG (by simp)
    · rw [q0]; exact (Covers.one (hs.2.inFr (by show 0 + 24 ≤ frameBytes; decide))).right
  · rw [h.1.1.2.sp]; exact h.1.1.1.ok.B56
  · exact pd_pub h₁.pdArgs h₂.pdArgs (by rw [h₁.1.1.2.sp, h₂.1.1.2.sp]) (by rw [h₁.1.1.pw, h₂.1.1.pw])
      (by rw [h₁.1.1.eB, h₂.1.1.eB]) _ _
  · have hh := h
    obtain ⟨⟨hs, hgl⟩, -, -⟩ := h
    have ok := hs.1.ok
    have hK := hs.1.k1024
    have e := outA P hs.1
    have low : FrameStack.belowA s.sp 56 = P.lay.LOW := by rw [hs.2.sp]; exact ok.low_eq
    rw [low] at fr
    have fr' : Frame [⟨State.addr (P.B + BitVec.ofNat 32 oEM1), P.K⟩, P.SCR, P.lay.LOW] s.mem s'.mem := fr
    have st : P.lay.St σ s' := hs.2.write fr' (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [e]; exact ⟨P.lay.FR, by simp, Offset.sub_base _ (by simp only [oEM1, frameBytes]; omega_using [hK])⟩
      · exact ⟨P.SCR, by simp, fun _ h => h⟩
      · exact ⟨P.lay.LOW, by simp, fun _ h => h⟩) rd wr sp
    refine ⟨⟨⟨hs.1, st⟩, hgl⟩, fun nB hn hp => ?_⟩
    have := pd_post hh.pdArgs po nB hn (by rw [hs.pw]; exact hp)
    rw [hs.eB, e, show P.K = P.gl from hgl.symm, hs.2.ro (R := P.SIG) (by simp)] at this
    rw [← hgl]
    exact this

end VG.Proof.RsaPkcs1Sig.Arm.Vf

end

end


/-!
# RSASSA-PKCS1-v1_5 verification with a precomputed public key on ARMv7: after the call

The status to its word and the encoding of the hash value to `EM₂`
(`encArgs_wp`, `encode_wp`, `ER`), the comparison of `EM₁` and `EM₂`
(`cmpArgs_wp`, `compare_wp`) and the result (`result_wp`, from
`verify_result`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.Arm.Vf

open VG VG.Arm VG.Impl.RsaPkcs1Sig.Arm.Precomputed VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_dp op2_imm op2_reg op2_lsr dpVal)

variable {P : EP}

/-! ## The result -/

theorem written_congr {m m' : Mem} {a : Addr} {K : Nat} {r : BitVec 32} {o : Option (List Byte)}
    (hb : Spec.Rsa.bytesAt m' a K = Spec.Rsa.bytesAt m a K) (h : Spec.Rsa.written m a K r o) :
    Spec.Rsa.written m' a K r o := by
  cases o with
  | some y => exact ⟨h.1, hb.trans h.2⟩
  | none => exact ⟨h.1, hb.trans h.2⟩

/-- What `encode` wrote to the bytes at `a` and returned (`ok`). -/
def EncR (id : Nat) (D : List Byte) (K : Nat) (m : Mem) (a : Addr) (ok : BitVec 32) : Prop :=
  match encOut id D K with
  | some em => ok = 1 ∧ Spec.Rsa.bytesAt m a K = em
  | none => ok = 0

theorem EncR.congr {id : Nat} {D : List Byte} {K : Nat} {m m' : Mem} {a : Addr} {ok : BitVec 32}
    (hb : Spec.Rsa.bytesAt m' a K = Spec.Rsa.bytesAt m a K) (h : EncR id D K m a ok) : EncR id D K m' a ok := by
  unfold EncR at h ⊢
  split at h
  · exact ⟨h.1, hb.trans h.2⟩
  · exact h

theorem and_zero' (x : BitVec 32) : x &&& 0 = 0 := by simp
theorem zero_and' (x : BitVec 32) : 0 &&& x = 0 := by simp

/-- The result: the status, masked with the encoding's success and with
whether `EM₁` and `EM₂` are equal. -/
theorem verify_result {nB eB D sig : List Byte} {id K : Nat} {m : Mem} {a₁ a₂ : Addr} {rc ok : BitVec 32}
    {eq : Bool} (hn : nB.length = K) (hs : sig.length = K)
    (w : Spec.Rsa.written m a₁ K rc (Spec.Rsa.publicOpChecked nB eB sig)) (e : EncR id D K m a₂ ok)
    (he : eq = true ↔ Spec.Rsa.bytesAt m a₁ K = Spec.Rsa.bytesAt m a₂ K) :
    rc &&& ok &&& BitVec.ofNat 32 eq.toNat =
      if Spec.RsaPkcs1Sig.verifyId nB eB id D sig then 1 else 0 := by
  unfold Spec.RsaPkcs1Sig.verifyId
  unfold EncR encOut at e
  cases hh : Spec.RsaPkcs1Sig.Hash.ofId id with
  | none =>
    simp only [hh] at e
    rw [e, and_zero', zero_and']; rfl
  | some h =>
    simp only [hh] at e ⊢
    have hv := VG.Proof.RsaPkcs1Sig.verify_iff_publicOpChecked nB eB h D sig
    cases hp : Spec.Rsa.publicOpChecked nB eB sig with
    | none =>
      rw [hp] at w
      have hf : Spec.RsaPkcs1Sig.verify nB eB h D sig = false := by
        rw [← Bool.not_eq_true, hv]; simp [hp]
      simp only [hf, Bool.false_eq_true, ↓reduceIte]
      rw [w.1, zero_and', zero_and']
    | some y =>
      rw [hp] at w
      cases hE : Spec.RsaPkcs1Sig.encode h D nB.length with
      | none =>
        rw [hn] at hE
        simp only [hE] at e
        have hf : Spec.RsaPkcs1Sig.verify nB eB h D sig = false := by
          rw [← Bool.not_eq_true, hv, hn]; simp [hE]
        simp only [hf, Bool.false_eq_true, ↓reduceIte]
        rw [e, and_zero', zero_and']
      | some em =>
        rw [hn] at hE
        simp only [hE] at e
        rw [w.1, e.1]
        have h11 : (1 : BitVec 32) &&& 1 = 1 := by decide
        rw [h11]
        by_cases hy : y = em
        · subst hy
          have ht : Spec.RsaPkcs1Sig.verify nB eB h D sig = true := by
            rw [hv, hn]; exact ⟨hs.trans hn.symm |>.trans hn, y, hE, hp⟩
          have heq : eq = true := he.2 (w.2.trans e.2.symm)
          simp only [ht, ↓reduceIte]
          rw [heq]; rfl
        · have hf : Spec.RsaPkcs1Sig.verify nB eB h D sig = false := by
            rw [← Bool.not_eq_true, hv, hn]
            rintro ⟨-, em', h1, h2⟩
            rw [hE] at h1
            rw [hp] at h2
            exact hy ((Option.some.inj h2).trans (Option.some.inj h1).symm)
          have heq : eq = false := by
            cases eq
            · rfl
            · exact absurd (w.2.symm.trans ((he.1 rfl).trans e.2)) hy
          simp only [hf, Bool.false_eq_true, ↓reduceIte]
          rw [heq]; rfl

/-! ## The stages -/

/-- A word of the frame kept. -/
abbrev Slot (P : EP) (m : Mem) (d : Nat) (v : BitVec 32) : Prop := m.readW (P.lay.fr d) 32 = v

/-- The encoding of the hash value. -/
abbrev ER (P : EP) (σ : State) (m : Mem) (ok : BitVec 32) : Prop :=
  EncR P.hash.toNat (digB P σ) P.K m (P.lay.fr oEM2) ok

/-- The status in its word. -/
def St1 (P : EP) (σ : State) (m : Mem) : Prop := ∃ rc, CR P σ m rc ∧ Slot P m oSt rc

/-- The encoding's success in its word. -/
def Ok1 (P : EP) (σ : State) (m : Mem) : Prop := ∃ ok, ER P σ m ok ∧ Slot P m oOk ok

/-- Before `encode`. -/
def C3 (P : EP) (σ s : State) : Prop :=
  C0 P σ s ∧ St1 P σ s.mem ∧ s.gpr .r0 = P.B + BitVec.ofNat 32 oEM2 ∧ s.gpr .r1 = P.dig ∧
    s.gpr .r2 = P.hash ∧ s.gpr .r3 = BitVec.ofNat 32 P.K ∧ s.gpr .lr = BitVec.ofNat 32 P.dl

/-- After `encode`. -/
def C4 (P : EP) (σ s : State) : Prop := C0 P σ s ∧ St1 P σ s.mem ∧ ER P σ s.mem (s.gpr .r3)

/-- Before the comparison. -/
def C5 (P : EP) (σ s : State) : Prop :=
  C0 P σ s ∧ St1 P σ s.mem ∧ Ok1 P σ s.mem ∧ s.gpr .r0 = P.B + BitVec.ofNat 32 oEM1 ∧
    s.gpr .r1 = P.B + BitVec.ofNat 32 oEM2 ∧ s.gpr .lr = BitVec.ofNat 32 P.K ∧ s.gpr .r2 = 0

/-- After the comparison. -/
def C6 (P : EP) (σ s : State) : Prop :=
  C0 P σ s ∧ St1 P σ s.mem ∧ Ok1 P σ s.mem ∧
    (s.gpr .r2 = 0 ↔ Spec.Rsa.bytesAt s.mem (P.lay.fr oEM1) P.K = Spec.Rsa.bytesAt s.mem (P.lay.fr oEM2) P.K)

/-! ## Memory kept -/

theorem slot_frame {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {d : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨P.lay.fr d, 4⟩ r) : m'.readW (P.lay.fr d) 32 = m.readW (P.lay.fr d) 32 :=
  hf.readW (Region.contains_self _ _) hd (by decide)

theorem CR.frame {σ : State} {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {r : BitVec 32}
    (hd : ∀ x ∈ rs, Region.Disjoint ⟨P.lay.fr oEM1, P.K⟩ x) (hK : P.K ≤ 1024) (h : CR P σ m r) : CR P σ m' r :=
  fun nB hn hp => written_congr (bytesAt_frame hf hd (by omega_arith)) (h nB hn hp)

theorem ER.frame {σ : State} {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {ok : BitVec 32}
    (hd : ∀ x ∈ rs, Region.Disjoint ⟨P.lay.fr oEM2, P.K⟩ x) (hK : P.K ≤ 1024) (h : ER P σ m ok) : ER P σ m' ok :=
  EncR.congr (bytesAt_frame hf hd (by omega_arith)) h

/-- A store to a word of the frame below `EM₁`. -/
theorem St1.frame {σ : State} {m m' : Mem} {rs : List Region} (hf : Frame rs m m') (hK : P.K ≤ 1024)
    (hd : ∀ x ∈ rs, Region.Disjoint ⟨P.lay.fr oEM1, P.K⟩ x ∧ Region.Disjoint ⟨P.lay.fr oSt, 4⟩ x)
    (h : St1 P σ m) : St1 P σ m' :=
  let ⟨rc, cr, sl⟩ := h
  ⟨rc, cr.frame hf (fun x hx => (hd x hx).1) hK, (slot_frame hf fun x hx => (hd x hx).2).trans sl⟩

theorem frame1 {m : Mem} {d : Nat} {v : BitVec 32} :
    Frame [⟨P.lay.fr d, 4⟩] m (m.writeW (P.lay.fr d) v) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

/-! ## The pieces -/

theorem encArgs_wp {σ s : State} (h : C2 P σ s) : WP isa (.block encArgs) s (C3 P σ) := by
  obtain ⟨⟨hs, hgl⟩, cr⟩ := h
  have hK := hs.1.k1024
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  have s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  refine s1.wp_strFr (d := oSt) (by show oSt + 4 ≤ frameBytes; decide) (by decide)
    (by rw [u1.gpr, hs.2.sp, BitVec.add_zero]) fun t2 s2 m2 => ?_
  refine wp_dp (op2_imm (by decide)) fun t3 u3 => ?_
  have s3 : P.lay.St σ t3 := s2.of_rest (u3.rest (ws := [.r0]) (by simp)) u3.mem
  refine s3.wp_arg (j := 5) (by simp) (by dsimp only; decide) fun t4 s4 u4 => ?_
  refine s4.wp_arg (j := 4) (by simp) (by dsimp only; decide) fun t5 s5 u5 => ?_
  refine s5.wp_arg (j := 1) (by simp) (by dsimp only; decide) fun t6 s6 u6 => ?_
  refine s6.wp_arg (j := 6) (by simp) (by dsimp only; decide) fun t7 s7 u7 => WP.block_nil ?_
  have mm : t7.mem = t1.mem.writeW (P.lay.fr oSt) (t1.gpr .r0) := by
    rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, m2.mem]
  refine ⟨⟨⟨hs.1, s7⟩, hgl⟩, ⟨s.gpr .r0, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mm, u1.mem]
    refine cr.frame frame1 (fun x hx => ?_) hK
    simp only [List.mem_singleton] at hx; subst hx
    exact Lay.fr_sep (by simp only [oEM1, oSt]; omega_arith) (by simp only [oEM1]; omega_arith) (by simp only [oSt]; omega_arith)
  · rw [Slot, mm, Mem.readW_writeW_self32, u1.other _ (by decide)]
  · rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.gpr,
      dpVal, m2.gpr, u1.gpr, hs.2.sp, BitVec.add_zero]
  · rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.gpr]; rfl
  · rw [u7.other _ (by decide), u6.other _ (by decide), u5.gpr]; rfl
  · rw [u7.other _ (by decide), u6.gpr]; rfl
  · rw [u7.gpr]; rfl

theorem encode_wp {σ s : State} (h : C3 P σ s) : WP isa Impl.RsaPkcs1Sig.Arm.encode s (C4 P σ) := by
  obtain ⟨⟨hs, hgl⟩, st, r0, r1, r2, r3, lr⟩ := h
  have ok := hs.1.ok
  have hK := hs.1.k1024
  have fit := ok.fit
  have e2 : State.addr (P.B + BitVec.ofNat 32 oEM2) = P.lay.fr oEM2 :=
    ok.addrB (by show oEM2 < frameBytes + 56 + 36; decide)
  have hfd := ok.fits P.DIG (by simp)
  simp only [Proof.X25519.Arm.addr_toNat] at hfd
  have hin : EncIn s (P.B + BitVec.ofNat 32 oEM2) P.dig P.hash P.K P.dl :=
    { r0 := r0, r1 := r1, r2 := r2, r3 := r3, lr := lr
      k64 := hs.1.k64, k1024 := hK, dl32 := hs.1.dl32
      dstFit := by
        rw [Proof.X25519.Arm.toNat_add_lt (by rw [BitVec.toNat_ofNat]; simp only [oEM2, frameBytes] at fit ⊢; omega_arith),
          BitVec.toNat_ofNat]
        simp only [oEM2, frameBytes] at fit ⊢; omega_arith
      srcFit := hfd
      write := by rw [e2]; exact hs.2.inFr (by show oEM2 + P.K ≤ frameBytes; simp only [oEM2, frameBytes]; omega_arith)
      read := ⟨P.DIG, List.mem_append_left _ (by rw [hs.2.rd, ok.rd]; simp), Region.contains_self _ _⟩
      sep := by
        rw [e2]
        exact (ok.stk_fr (R := P.DIG) (.inl (by simp)) (by simp only [oEM2, frameBytes]; omega_arith)).symm }
  refine WP.mono (encode_ok hin) fun t ⟨fr, rest, res⟩ => ?_
  rw [e2] at fr
  have st' : P.lay.St σ t := hs.2.frameW (by show oEM2 + P.K ≤ frameBytes; simp only [oEM2, frameBytes]; omega_arith)
    fr rest.rd rest.wr rest.sp
  refine ⟨⟨⟨hs.1, st'⟩, hgl⟩, st.frame fr hK fun x hx => ?_, ?_⟩
  · simp only [List.mem_singleton] at hx; subst hx
    exact ⟨Lay.fr_sep (by simp only [oEM1, oEM2]; omega_arith) (by simp only [oEM1]; omega_arith) (by simp only [oEM2]; omega_arith),
      Lay.fr_sep (by simp only [oSt, oEM2]; omega_arith) (by simp only [oSt]; omega_arith) (by simp only [oEM2]; omega_arith)⟩
  · have hd : Spec.Rsa.bytesAt s.mem (State.addr P.dig) P.dl = digB P σ := hs.2.ro (R := P.DIG) (by simp)
    rw [hd, e2] at res
    unfold ER EncR
    revert res
    cases encOut P.hash.toNat (digB P σ) P.K with
    | some em => exact fun r => r
    | none => exact fun r => r

theorem cmpArgs_wp {σ s : State} (h : C4 P σ s) : WP isa (.block cmpArgs) s (C5 P σ) := by
  obtain ⟨⟨hs, hgl⟩, st, er⟩ := h
  have hK := hs.1.k1024
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  have s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  refine s1.wp_strFr (d := oOk) (by show oOk + 4 ≤ frameBytes; decide) (by decide)
    (by rw [u1.gpr, hs.2.sp, BitVec.add_zero]) fun t2 s2 m2 => ?_
  refine wp_dp (op2_imm (by decide)) fun t3 u3 => ?_
  refine wp_dp (op2_imm (by decide)) fun t4 u4 => ?_
  have s4 : P.lay.St σ t4 := (s2.of_rest (u3.rest (ws := [.r0]) (by simp)) u3.mem).of_rest
    (u4.rest (ws := [.r1]) (by simp)) u4.mem
  refine s4.wp_arg (j := 1) (by simp) (by dsimp only; decide) fun t5 s5 u5 => ?_
  refine wp_mov (op2_imm (by decide)) fun t6 u6 => WP.block_nil ?_
  have mm : t6.mem = t1.mem.writeW (P.lay.fr oOk) (t1.gpr .r3) := by
    rw [u6.mem, u5.mem, u4.mem, u3.mem, m2.mem]
  have r12 : t2.gpr .r12 = P.B := by rw [m2.gpr, u1.gpr, hs.2.sp, BitVec.add_zero]
  refine ⟨⟨⟨hs.1, s5.of_rest (u6.rest (ws := [.r2]) (by simp)) u6.mem⟩, hgl⟩, ?_, ⟨s.gpr .r3, ?_, ?_⟩, ?_, ?_, ?_,
    u6.gpr⟩
  · rw [mm, u1.mem]
    refine st.frame frame1 hK fun x hx => ?_
    simp only [List.mem_singleton] at hx; subst hx
    exact ⟨Lay.fr_sep (by simp only [oEM1, oOk]; omega_arith) (by simp only [oEM1]; omega_arith) (by simp only [oOk]; omega_arith),
      Lay.fr_sep (by simp only [oSt, oOk]; omega_arith) (by simp only [oSt]; omega_arith) (by simp only [oOk]; omega_arith)⟩
  · rw [mm, u1.mem]
    refine er.frame frame1 (fun x hx => ?_) hK
    simp only [List.mem_singleton] at hx; subst hx
    exact Lay.fr_sep (by simp only [oEM2, oOk]; omega_arith) (by simp only [oEM2]; omega_arith) (by simp only [oOk]; omega_arith)
  · rw [Slot, mm, Mem.readW_writeW_self32, u1.other _ (by decide)]
  · rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.gpr, dpVal, r12]
  · rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr, dpVal, u3.other _ (by decide), r12]
  · rw [u6.other _ (by decide), u5.gpr]; rfl

theorem compare_wp {σ s : State} (h : C5 P σ s) : WP isa Impl.Bignum.Arm.compareBytes s (C6 P σ) := by
  obtain ⟨⟨hs, hgl⟩, st, ok1, r0, r1, lr, r2⟩ := h
  have ok := hs.1.ok
  have hK := hs.1.k1024
  have fit := ok.fit
  have e1 : State.addr (P.B + BitVec.ofNat 32 oEM1) = P.lay.fr oEM1 :=
    ok.addrB (by show oEM1 < frameBytes + 56 + 36; decide)
  have e2 : State.addr (P.B + BitVec.ofNat 32 oEM2) = P.lay.fr oEM2 :=
    ok.addrB (by show oEM2 < frameBytes + 56 + 36; decide)
  have f : ∀ d, d < 2 ^ 32 → d + P.K ≤ frameBytes → (P.B + BitVec.ofNat 32 d).toNat + P.K ≤ 2 ^ 32 := by
    intro d hd hdK
    rw [Proof.X25519.Arm.toNat_add_lt (by rw [BitVec.toNat_ofNat]; simp only [frameBytes] at fit hdK ⊢; omega_arith),
      BitVec.toNat_ofNat]
    simp only [frameBytes] at fit hdK ⊢; omega_arith
  refine WP.mono (Bignum.Arm.compareBuffer_ok s (a := P.B + BitVec.ofNat 32 oEM1) (b := P.B + BitVec.ofNat 32 oEM2)
    (n := P.K) (by have := hs.1.k64; omega_arith) (by omega_arith) (f _ (by decide) (by simp only [oEM1, frameBytes]; omega_arith))
    (f _ (by decide) (by simp only [oEM2, frameBytes]; omega_arith))
    (by rw [e1]; exact hs.2.inFrR (by show oEM1 + P.K ≤ frameBytes; simp only [oEM1, frameBytes]; omega_arith))
    (by rw [e2]; exact hs.2.inFrR (by show oEM2 + P.K ≤ frameBytes; simp only [oEM2, frameBytes]; omega_arith))
    r0 r1 lr r2) fun t ⟨eq, mem, rest⟩ => ?_
  refine ⟨⟨⟨hs.1, hs.2.of_rest rest mem⟩, hgl⟩, by rw [mem]; exact st, by rw [mem]; exact ok1, ?_⟩
  rw [mem, ← e1, ← e2]
  exact eq

theorem result_wp {σ s : State} (h : C6 P σ s) : WP isa (.block result) s (Fin P σ) := by
  obtain ⟨⟨hs, hgl⟩, ⟨rc, cr, slR⟩, ⟨okv, er, slO⟩, eq⟩ := h
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  have s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  refine s1.wp_slot (d := oSt) (by show oSt + 4 ≤ frameBytes; decide) (by decide) fun t2 s2 u2 => ?_
  refine s2.wp_slot (d := oOk) (by show oOk + 4 ≤ frameBytes; decide) (by decide) fun t3 s3 u3 => ?_
  refine wp_mov (op2_imm (by decide)) fun t4 u4 => ?_
  refine wp_dp (op2_reg _ _) fun t5 u5 => ?_
  refine wp_dp (op2_reg _ _) fun t6 u6 => ?_
  refine wp_mov (op2_lsr (by decide)) fun t7 u7 => ?_
  refine wp_mov (op2_imm (by decide)) fun t8 u8 => ?_
  refine wp_dp (op2_reg _ _) fun t9 u9 => ?_
  refine wp_dp (op2_reg _ _) fun t10 u10 => ?_
  refine wp_dp (op2_reg _ _) fun t11 u11 => WP.block_nil ?_
  have s11 : P.lay.St σ t11 := (((((((s3.of_rest (u4.rest (ws := [.r1]) (by simp)) u4.mem).of_rest
    (u5.rest (ws := [.r1]) (by simp)) u5.mem).of_rest (u6.rest (ws := [.r1]) (by simp)) u6.mem).of_rest
    (u7.rest (ws := [.r1]) (by simp)) u7.mem).of_rest (u8.rest (ws := [.r2]) (by simp)) u8.mem).of_rest
    (u9.rest (ws := [.r1]) (by simp)) u9.mem).of_rest (u10.rest (ws := [.r0]) (by simp)) u10.mem).of_rest
    (u11.rest (ws := [.r0]) (by simp)) u11.mem
  refine ⟨⟨hs.1, s11⟩, fun nB hn hp => ?_⟩
  have r2_3 : t3.gpr .r2 = s.gpr .r2 := by
    rw [u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide)]
  have eqb : t9.gpr .r1 = BitVec.ofNat 32 (decide (s.gpr .r2 = 0#32)).toNat := by
    rw [u9.gpr, dpVal, u8.gpr, u8.other _ (by decide), u7.gpr, u6.gpr, dpVal, u5.gpr, dpVal, u4.gpr,
      u4.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), r2_3]
    exact VG.Proof.Rsa.Arm.zero_test32 _
  have mm : t3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  have r0_10 : t10.gpr .r0 = rc &&& okv := by
    rw [u10.gpr, dpVal, u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide),
      u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.gpr,
      u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide),
      u5.other _ (by decide), u4.other _ (by decide), u3.gpr, u2.mem, u1.mem, slR, slO]
  rw [u11.gpr, dpVal, r0_10, u10.other _ (by decide), eqb]
  have hsg : (sigB P σ).length = P.K := by rw [bytesAt_length, hgl]
  have hd : Spec.Rsa.bytesAt s.mem (State.addr P.dig) P.dl = digB P σ := hs.2.ro (R := P.DIG) (by simp)
  refine verify_result hn hsg (cr nB hn hp) er ?_
  rw [decide_eq_true_iff]
  exact eq

end VG.Proof.RsaPkcs1Sig.Arm.Vf
