module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.RcBase
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Encode
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Recover
public import VerifiedGarbage.Impl.RsaPkcs1Sig.Arm.RecoverPrecomputed
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Bignum.Arm.MaskBuffer
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Callees
public import VerifiedGarbage.Proof.Rsa.Arm.Stage.VP
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Vp
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Rsa.Contract
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.VfPost
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Bignum.Arm.CompareBuffer
import VerifiedGarbage.Proof.Rsa.Arm.PrivMask
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Rsa.ZeroTest32
import VerifiedGarbage.Proof.Bignum.Arm.CopyRegion
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.RcTaint
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.VfTaint
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.EncodeTaint
import VerifiedGarbage.Proof.Bignum.Arm.CompareBytesCT
import VerifiedGarbage.Proof.Bignum.Arm.CopyBytesCT
import VerifiedGarbage.Proof.Bignum.Arm.MaskBytesCT
public import VerifiedGarbage.Proof.Framework.Contract

/-! ### `RsaPkcs1Sig.Arm.RcBody`, which only this module used -/

section

/-! ### `RsaPkcs1Sig.Arm.RcOut`, which only this module used -/

section

/-! ### `RsaPkcs1Sig.Arm.RcPost`, which only this module used -/

section

/-! ### `RsaPkcs1Sig.Arm.RcCall`, which only this module used -/

section

/-! ### `RsaPkcs1Sig.Arm.RcPieces`, which only this module used -/

section

/-!
# RSASSA-PKCS1-v1_5 recovery with a precomputed public key on ARMv7: up to the call

The stages up to the call and the correctness of the pieces between them:
the check of the lengths (`lenCheck_wp`, `cmp_wp`), zeros and 0 when they
differ (`zeroArgs_wp`, `zero_wp`, `ret0_wp`), and the call's arguments
(`callArgs_wp`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.Arm.Rc

open VG VG.Arm VG.Impl.RsaPkcs1Sig.Arm.RecoverPrecomputed
open VG.Impl.RsaPkcs1Sig.Arm.Precomputed (frameBytes oSt oOk oEM1 oEM2 ret0)
open VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_dp wp_cmp op2_imm op2_reg dpVal)

variable {P : EP}

namespace In

variable {σ : State} (h : In P σ)
include h

theorem ol_pos : 0 < P.ol := by obtain ⟨hh, -, e⟩ := h.hh; rw [e]; exact len_pos hh
theorem ol64 : P.ol ≤ 64 := by obtain ⟨hh, -, e⟩ := h.hh; rw [e]; exact len_le hh

end In

/-- The signature. -/
abbrev sigB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.sig) P.gl

/-- What the function writes to `out` and returns, for every modulus whose
precomputed values are `pre`'s and the hash function `hash` names. -/
def Res (P : EP) (σ : State) (m : Mem) (r : BitVec 32) : Prop :=
  ∀ nB : List Byte, nB.length = P.K → Spec.Rsa.publicPrecompute nB = some P.pw →
    ∀ h, Spec.RsaPkcs1Sig.Hash.ofId P.hash.toNat = some h →
      Spec.Rsa.written m (State.addr P.out) P.ol r (recoverEnc nB P.eB h (sigB P σ))

/-- After `lenCheck`. -/
def H1 (P : EP) (σ s : State) : Prop := S P σ s ∧ s.gpr .r0 = BitVec.ofNat 32 P.gl - BitVec.ofNat 32 P.K

/-- After the comparison of the lengths. -/
def H2 (P : EP) (σ s : State) : Prop := S P σ s ∧ s.z = decide (P.gl = P.K)

/-- Before the zeros. -/
def Z1 (P : EP) (σ s : State) : Prop :=
  S P σ s ∧ P.gl ≠ P.K ∧ s.gpr .r0 = P.out ∧ s.gpr .lr = BitVec.ofNat 32 P.ol ∧ s.gpr .r2 = 0

/-- `out` zeros. -/
def Z2 (P : EP) (σ s : State) : Prop :=
  S P σ s ∧ P.gl ≠ P.K ∧ Spec.Rsa.bytesAt s.mem (State.addr P.out) P.ol = List.replicate P.ol 0

/-- The end of the body. -/
def Fin (P : EP) (σ s : State) : Prop := S P σ s ∧ Res P σ s.mem (s.gpr .r0)

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
  obtain s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  refine s1.wp_arg (j := 8) (by simp) (by dsimp only; decide) fun t2 s2 u2 => ?_
  refine s2.wp_arg (j := 3) (by simp) (by dsimp only; decide) fun t3 s3 u3 => ?_
  refine wp_dp (op2_reg _ _) fun t4 u4 => WP.block_nil
    ⟨⟨hs.1, s3.of_rest (u4.rest (ws := [.r0]) (by simp)) u4.mem⟩, ?_⟩
  rw [u4.gpr, dpVal, u3.other _ (by decide), u2.gpr, u3.gpr]; rfl

theorem cmp_wp {σ s : State} (h : H1 P σ s) : WP isa (.block [.cmp .r0 (.imm 0)]) s (H2 P σ) := by
  obtain ⟨hs, r0⟩ := h
  have hK := hs.1.k1024
  refine wp_cmp (op2_imm (by decide)) fun t1 u1 z1 => WP.block_nil
    ⟨⟨hs.1, hs.2.of_rest (u1.rest []) u1.mem⟩, ?_⟩
  obtain e : ∀ x : BitVec 32, x - 0 = x := fun x => by simp
  rw [z1, r0, e, cmp_eq hs.1.gl32 (by omega_using [hK])]

theorem zeroArgs_wp {σ s : State} (h : H2 P σ s ∧ isa.eval .ne s = some true) :
    WP isa (.block zeroArgs) s (Z1 P σ) := by
  obtain ⟨⟨hs, z⟩, e⟩ := h
  obtain hne : P.gl ≠ P.K := by
    rw [Proof.X25519.Arm.eval_ne, z] at e; simpa using e
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  obtain s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  refine s1.wp_arg (j := 0) (by simp) (by dsimp only; decide) fun t2 s2 u2 => ?_
  refine s2.wp_arg (j := 1) (by simp) (by dsimp only; decide) fun t3 s3 u3 => ?_
  refine wp_mov (op2_imm (by decide)) fun t4 u4 => WP.block_nil
    ⟨⟨hs.1, s3.of_rest (u4.rest (ws := [.r2]) (by simp)) u4.mem⟩, hne, ?_, ?_, u4.gpr⟩
  · rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr]; rfl
  · rw [u4.other _ (by decide), u3.gpr]; rfl

theorem zero_wp {σ s : State} (h : Z1 P σ s) : WP isa Impl.Bignum.Arm.maskBytes s (Z2 P σ) := by
  obtain ⟨hs, hne, r0, lr, r2⟩ := h
  have ok := hs.1.ok
  obtain hfo := ok.fits P.OUT (by simp)
  simp only [Proof.X25519.Arm.addr_toNat] at hfo
  have h64 := hs.1.ol64
  refine WP.mono (Bignum.Arm.maskBuffer_ok s (dst := P.out) (n := P.ol) hs.1.ol_pos (by omega_using [h64])
    hfo ⟨P.OUT, by rw [hs.2.wr, ok.wr]; simp, Region.contains_self _ _⟩ r0 lr) fun t ⟨hb, fr, rst⟩ => ?_
  obtain st : P.lay.St σ t := hs.2.write fr (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨P.OUT, by simp, fun _ h => h⟩) rst.rd rst.wr rst.sp
  refine ⟨⟨hs.1, st⟩, hne, ?_⟩
  rw [hb, r2]
  apply List.ext_getElem (by simp [bytesAt_length])
  intro i h₁ h₂
  simp

theorem ret0_wp {σ s : State} (h : Z2 P σ s) : WP isa (.block ret0) s (Fin P σ) := by
  obtain ⟨hs, hne, hz⟩ := h
  refine wp_mov (op2_imm (by decide)) fun t1 u1 => WP.block_nil
    ⟨⟨hs.1, hs.2.of_rest (u1.rest (ws := [.r0]) (by simp)) u1.mem⟩, fun nB hn _ h _ => ?_⟩
  obtain hr : recoverEnc nB P.eB h (sigB P σ) = none := by
    rw [recoverEnc, ite_eq_right (by rw [bytesAt_length, hn]; exact hne)]
  rw [hr, u1.gpr, u1.mem]
  exact ⟨rfl, hz⟩

theorem c0_of {σ s : State} (h : H2 P σ s ∧ isa.eval .ne s = some false) : C0 P σ s := by
  obtain ⟨⟨hs, z⟩, e⟩ := h
  refine ⟨hs, ?_⟩
  rw [Proof.X25519.Arm.eval_ne, z] at e; simpa using e

theorem callArgs_wp {σ s : State} (h : C0 P σ s) : WP isa (.block callArgs) s (C1 P σ) := by
  obtain ⟨hs, hgl⟩ := h
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t0 u0 => ?_
  obtain s0 : P.lay.St σ t0 := hs.2.of_rest (u0.rest (ws := [.r12]) (by simp)) u0.mem
  obtain r12 : t0.gpr .r12 = P.B := by rw [u0.gpr, hs.2.sp, BitVec.add_zero]
  refine s0.wp_copyArg (j := 4) (d := 0) r12 (by simp) (by dsimp only; decide) (by dsimp only; decide)
    (by decide) (by decide) fun t1 s1 v1 g1 m1 => ?_
  refine s1.wp_copyArg (j := 5) (d := 4) (by rw [g1 _ (by decide), r12]) (by simp) (by dsimp only; decide)
    (by dsimp only; decide) (by decide) (by decide) fun t2 s2 v2 g2 m2 => ?_
  refine s2.wp_copyArg (j := 7) (d := 8) (by rw [g2 _ (by decide), g1 _ (by decide), r12]) (by simp)
    (by dsimp only; decide) (by dsimp only; decide) (by decide) (by decide) fun t3 s3 v3 g3 m3 => ?_
  refine s3.wp_copyArg (j := 3) (d := 12) (by rw [g3 _ (by decide), g2 _ (by decide), g1 _ (by decide), r12])
    (by simp) (by dsimp only; decide) (by dsimp only; decide) (by decide) (by decide) fun t4 s4 v4 g4 m4 => ?_
  obtain r12' : t4.gpr .r12 = P.B := by
    rw [g4 _ (by decide), g3 _ (by decide), g2 _ (by decide), g1 _ (by decide), r12]
  refine s4.wp_copyArg (j := 9) (d := 16) r12' (by simp) (by dsimp only; decide) (by dsimp only; decide)
    (by decide) (by decide) fun t5 s5 v5 g5 m5 => ?_
  refine s5.wp_copyArg (j := 10) (d := 20) (by rw [g5 _ (by decide), r12']) (by simp) (by dsimp only; decide)
    (by dsimp only; decide) (by decide) (by decide) fun t6 s6 v6 g6 m6 => ?_
  refine wp_dp (op2_imm (by decide)) fun t7 u7 => ?_
  obtain s7 : P.lay.St σ t7 := s6.of_rest (u7.rest (ws := [.r0]) (by simp)) u7.mem
  refine s7.wp_arg (j := 3) (by simp) (by dsimp only; decide) fun t8 s8 u8 => ?_
  refine s8.wp_arg (j := 11) (by simp) (by dsimp only; decide) fun t9 s9 u9 => ?_
  refine s9.wp_arg (j := 12) (by simp) (by dsimp only; decide) fun t10 s10 u10 => WP.block_nil ?_
  obtain mm : t10.mem = t6.mem := by rw [u10.mem, u9.mem, u8.mem, u7.mem]
  refine ⟨⟨⟨hs.1, s10⟩, hgl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [mm, m6]
    obtain w : ∀ (m : Mem) (d e : Nat) (v : BitVec 32), d + 4 ≤ e ∨ e + 4 ≤ d → d + 4 ≤ 24 → e + 4 ≤ 24 →
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

end VG.Proof.RsaPkcs1Sig.Arm.Rc

end

end


/-!
# RSASSA-PKCS1-v1_5 recovery with a precomputed public key on ARMv7: the call

The call of `vg_rsa_public_precomputed_checked` (`call_vp`, correct and
constant time: its arguments and the public data it reads are the same in
two runs), which writes `EM₁` and returns its status (`CR`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.Arm.Rc

open VG VG.Arm VG.Impl.RsaPkcs1Sig.Arm.RecoverPrecomputed
open VG.Impl.RsaPkcs1Sig.Arm.Precomputed (frameBytes oSt oOk oEM1 oEM2 ret0)
open VG.Proof.RsaPkcs1Sig.Arm
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
  obtain a : ∀ i < 6, stackArg s i = (outv P).getD i 0 := fun i hi => by
    rw [← oa i hi]
    simp only [stackArg, stackArgAddr, hs.2.sp]
    rw [hs.2.ok.addrB (by show 4 * i < frameBytes + 56 + 36; simp only [frameBytes]; omega_arith)]
  have h1 := hs.1
  exact ⟨r0, r1, r2, r3, a 0 (by decide), a 1 (by decide), a 2 (by decide), a 3 (by decide), a 4 (by decide),
    a 5 (by decide), h1.kv, h1.rlK, h1.el1, h1.elK, h1.slK,
    by have := hs.1.ok.fits P.SCR (by simp); simp only [Proof.X25519.Arm.addr_toNat] at this; omega_arith⟩

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
  obtain e := outA P hs.1
  obtain hfr : ∀ {R : Region}, R ∈ P.lay.ro ∨ R ∈ P.lay.rw → ∀ {d n : Nat}, d + n ≤ frameBytes + 56 →
      Region.Disjoint ⟨P.lay.fr d, n⟩ R := fun hR _ _ hd => ok.stk_fr hR hd
  obtain fs := fun {R : Region} (hR : R ∈ P.lay.ro ++ P.lay.rw) => ok.fits R hR
  obtain q0 : State.addr P.B = P.lay.fr 0 := by simp
  obtain sigR : (⟨State.addr P.sig, P.K⟩ : Region) = P.SIG := by rw [← hgl]
  refine pd_pre h.pdArgs hs.2.sp (by omega_arith) (by simp only [frameBytes] at fit; omega_arith)
    (by rw [show (P.B + BitVec.ofNat 32 oEM1).toNat = P.B.toNat + oEM1 from
          Proof.X25519.Arm.toNat_add_lt (by simp only [oEM1, frameBytes] at fit ⊢; rw [BitVec.toNat_ofNat]; omega_arith) |>.trans
          (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide)])]
        simp only [oEM1, frameBytes] at fit ⊢; omega_arith)
    (by have := fs (R := P.PRE) (by simp); simpa [Proof.X25519.Arm.addr_toNat] using this)
    (by have := fs (R := P.E) (by simp); simpa [Proof.X25519.Arm.addr_toNat] using this)
    (by have := fs (R := P.SIG) (by simp); simp only [Proof.X25519.Arm.addr_toNat] at this; omega_arith)
    (by have := fs (R := P.SCR) (by simp); simpa [Proof.X25519.Arm.addr_toNat] using this)
    (by rw [e]; exact hfr (R := P.PRE) (.inl (by simp)) (by simp only [oEM1, frameBytes]; omega_arith))
    (by rw [e]; exact hfr (R := P.E) (.inl (by simp)) (by simp only [oEM1, frameBytes]; omega_arith))
    (by rw [e, sigR]; exact hfr (R := P.SIG) (.inl (by simp)) (by simp only [oEM1, frameBytes]; omega_arith))
    (by rw [e]; exact hfr (R := P.SCR) (.inr (by simp)) (by simp only [oEM1, frameBytes]; omega_arith))
    (by rw [e, q0]; exact Lay.fr_sep (by simp only [oEM1]; omega_arith) (by simp only [oEM1]; omega_arith) (by decide))
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
  · rw [e]; exact (Lay.fr_low (by simp only [oEM1]; omega_arith)).symm
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
    obtain e := outA P hs.1
    obtain q0 : State.addr P.B = P.lay.fr 0 := by simp
    obtain hro : ∀ R ∈ P.lay.ro, Covers [R] (s.rd ++ s.wr) := fun R hR =>
      Covers.left (Covers.of_mem fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hs.2.rd, ok.rd]; exact List.mem_append_left _ hR)
    obtain hrw : ∀ R ∈ P.lay.rw, Covers [R] s.wr := fun R hR =>
      Covers.of_mem fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hs.2.wr, ok.wr]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hR)
    obtain wr : Covers (pdWr (P.B + BitVec.ofNat 32 oEM1) P.scr P.K P.sl) s.wr := by
      refine Covers.cons ?_ (hrw P.SCR (by simp))
      rw [e]; exact Covers.one (hs.2.inFr (by show oEM1 + P.K ≤ frameBytes; simp only [oEM1, frameBytes]; omega_arith))
    obtain sigR : (⟨State.addr P.sig, P.K⟩ : Region) = P.SIG := by rw [← hgl]
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
    obtain e := outA P hs.1
    obtain low : FrameStack.belowA s.sp 56 = P.lay.LOW := by rw [hs.2.sp]; exact ok.low_eq
    rw [low] at fr
    have fr' : Frame [⟨State.addr (P.B + BitVec.ofNat 32 oEM1), P.K⟩, P.SCR, P.lay.LOW] s.mem s'.mem := fr
    obtain st : P.lay.St σ s' := hs.2.write fr' (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [e]; exact ⟨P.lay.FR, by simp, Offset.sub_base _ (by simp only [oEM1, frameBytes]; omega_arith)⟩
      · exact ⟨P.SCR, by simp, fun _ h => h⟩
      · exact ⟨P.lay.LOW, by simp, fun _ h => h⟩) rd wr sp
    refine ⟨⟨⟨hs.1, st⟩, hgl⟩, fun nB hn hp => ?_⟩
    have := pd_post hh.pdArgs po nB hn (by rw [hs.pw]; exact hp)
    rw [hs.eB, e, show P.K = P.gl from hgl.symm, hs.2.ro (R := P.SIG) (by simp)] at this
    rw [← hgl]
    exact this

end VG.Proof.RsaPkcs1Sig.Arm.Rc

end

end

/-!
# RSASSA-PKCS1-v1_5 recovery with a precomputed public key on ARMv7: the encoding and the comparison

The status to its word and the encoding of the last `out_len` bytes of
`EM₁` to `EM₂` (`encArgs_wp`, `encode_wp`), the comparison of `EM₁` and
`EM₂` (`cmpArgs_wp`, `compare_wp`) and the result (`result_wp`, from
`recover_result`), as in verification (`Proof/RsaPkcs1Sig/Arm/VfPost.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.Arm.Rc

open VG VG.Arm VG.Impl.RsaPkcs1Sig.Arm.RecoverPrecomputed
open VG.Impl.RsaPkcs1Sig.Arm.Precomputed (frameBytes oSt oOk oEM1 oEM2 ret0)
open VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.RsaPkcs1Sig.Arm.Vf (EncR EncR.congr written_congr and_zero' zero_and')
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_dp op2_imm op2_reg op2_lsr dpVal)

variable {P : EP}

/-! ## The result -/

/-- What the result and the value are: the value is the last `out_len`
bytes of `EM₁`, and the result is 1 exactly when there is one. -/
def Rv (o : Option (List Byte)) (r : BitVec 32) (v : List Byte) : Prop :=
  match o with
  | some y => r = 1 ∧ v = y
  | none => r = 0

theorem recover_result {nB eB sig : List Byte} {h : Spec.RsaPkcs1Sig.Hash} {id K ol : Nat} {m : Mem}
    {a₁ a₂ : Addr} {rc ok : BitVec 32} {eq : Bool} (hn : nB.length = K) (hs : sig.length = K)
    (hh : Spec.RsaPkcs1Sig.Hash.ofId id = some h) (hol : ol = h.len)
    (w : Spec.Rsa.written m a₁ K rc (Spec.Rsa.publicOpChecked nB eB sig))
    (e : EncR id ((Spec.Rsa.bytesAt m a₁ K).drop (K - ol)) K m a₂ ok)
    (he : eq = true ↔ Spec.Rsa.bytesAt m a₁ K = Spec.Rsa.bytesAt m a₂ K) :
    Rv (recoverEnc nB eB h sig) (rc &&& ok &&& BitVec.ofNat 32 eq.toNat)
      ((Spec.Rsa.bytesAt m a₁ K).drop (K - ol)) := by
  unfold recoverEnc
  rw [ite_eq_left (hs.trans hn.symm), hn, ← hol]
  unfold EncR encOut at e
  simp only [hh] at e
  cases hp : Spec.Rsa.publicOpChecked nB eB sig with
  | none =>
    rw [hp] at w
    show _ = _
    rw [w.1, zero_and', zero_and']
  | some y =>
    rw [hp] at w
    simp only
    rw [w.2] at e ⊢
    cases hE : Spec.RsaPkcs1Sig.encode h (y.drop (K - ol)) K with
    | none =>
      simp only [hE] at e
      simp only [reduceCtorEq, ↓reduceIte]
      show _ = _
      rw [e, and_zero', zero_and']
    | some em =>
      simp only [hE] at e
      rw [w.1, e.1]
      obtain h11 : (1 : BitVec 32) &&& 1 = 1 := by decide
      rw [h11]
      by_cases hy : em = y
      · subst hy
        obtain heq : eq = true := he.2 (w.2.trans e.2.symm)
        simp only [↓reduceIte]
        rw [heq]
        exact ⟨rfl, rfl⟩
      · have heq : eq = false := by
          cases eq
          · rfl
          · exact absurd (((he.1 rfl).symm.trans w.2).symm.trans e.2).symm hy
        simp only [Option.some.injEq, hy, ↓reduceIte]
        show _ = _
        rw [heq]; rfl

/-! ## The stages -/

/-- A word of the frame kept. -/
abbrev Slot (P : EP) (m : Mem) (d : Nat) (v : BitVec 32) : Prop := m.readW (P.lay.fr d) 32 = v

/-- The last `out_len` bytes of `EM₁`. -/
abbrev Tail (P : EP) (m : Mem) : List Byte := (Spec.Rsa.bytesAt m (P.lay.fr oEM1) P.K).drop (P.K - P.ol)

/-- The encoding of the last `out_len` bytes of `EM₁`. -/
abbrev ER (P : EP) (m : Mem) (ok : BitVec 32) : Prop := EncR P.hash.toNat (Tail P m) P.K m (P.lay.fr oEM2) ok

/-- The status in its word. -/
def St1 (P : EP) (σ : State) (m : Mem) : Prop := ∃ rc, CR P σ m rc ∧ Slot P m oSt rc

/-- The encoding's success in its word. -/
def Ok1 (P : EP) (m : Mem) : Prop := ∃ ok, ER P m ok ∧ Slot P m oOk ok

/-- Before `encode`. -/
def C3 (P : EP) (σ s : State) : Prop :=
  C0 P σ s ∧ St1 P σ s.mem ∧ s.gpr .r0 = P.B + BitVec.ofNat 32 oEM2 ∧
    s.gpr .r1 = P.B + BitVec.ofNat 32 (oEM1 + (P.K - P.ol)) ∧ s.gpr .r2 = P.hash ∧
    s.gpr .r3 = BitVec.ofNat 32 P.K ∧ s.gpr .lr = BitVec.ofNat 32 P.ol

/-- After `encode`. -/
def C4 (P : EP) (σ s : State) : Prop := C0 P σ s ∧ St1 P σ s.mem ∧ ER P s.mem (s.gpr .r3)

/-- Before the comparison. -/
def C5 (P : EP) (σ s : State) : Prop :=
  C0 P σ s ∧ St1 P σ s.mem ∧ Ok1 P s.mem ∧ s.gpr .r0 = P.B + BitVec.ofNat 32 oEM1 ∧
    s.gpr .r1 = P.B + BitVec.ofNat 32 oEM2 ∧ s.gpr .lr = BitVec.ofNat 32 P.K ∧ s.gpr .r2 = 0

/-- After the comparison. -/
def C6 (P : EP) (σ s : State) : Prop :=
  C0 P σ s ∧ St1 P σ s.mem ∧ Ok1 P s.mem ∧
    (s.gpr .r2 = 0 ↔ Spec.Rsa.bytesAt s.mem (P.lay.fr oEM1) P.K = Spec.Rsa.bytesAt s.mem (P.lay.fr oEM2) P.K)

/-- The result and the value, for every modulus whose precomputed values are
`pre`'s and the hash function `hash` names. -/
def RR (P : EP) (σ : State) (r : BitVec 32) (v : List Byte) : Prop :=
  ∀ nB : List Byte, nB.length = P.K → Spec.Rsa.publicPrecompute nB = some P.pw →
    ∀ h, Spec.RsaPkcs1Sig.Hash.ofId P.hash.toNat = some h → Rv (recoverEnc nB P.eB h (sigB P σ)) r v

/-- After the result. -/
def C7 (P : EP) (σ s : State) : Prop := C0 P σ s ∧ RR P σ (s.gpr .r3) (Tail P s.mem)

/-! ## Memory kept -/

theorem slot_frame {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {d : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨P.lay.fr d, 4⟩ r) : m'.readW (P.lay.fr d) 32 = m.readW (P.lay.fr d) 32 :=
  hf.readW (Region.contains_self _ _) hd (by decide)

theorem CR.frame {σ : State} {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {r : BitVec 32}
    (hd : ∀ x ∈ rs, Region.Disjoint ⟨P.lay.fr oEM1, P.K⟩ x) (hK : P.K ≤ 1024) (h : CR P σ m r) : CR P σ m' r :=
  fun nB hn hp => written_congr (bytesAt_frame hf hd (by omega_arith)) (h nB hn hp)

theorem ER.frame {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {ok : BitVec 32}
    (hd : ∀ x ∈ rs, Region.Disjoint ⟨P.lay.fr oEM1, P.K⟩ x ∧ Region.Disjoint ⟨P.lay.fr oEM2, P.K⟩ x)
    (hK : P.K ≤ 1024) (h : ER P m ok) : ER P m' ok := by
  obtain e1 : Tail P m' = Tail P m := by
    simp only [Tail]; rw [bytesAt_frame hf (fun x hx => (hd x hx).1) (by omega_arith)]
  simp only [ER] at h ⊢
  rw [e1]
  exact EncR.congr (bytesAt_frame hf (fun x hx => (hd x hx).2) (by omega_arith)) h

theorem St1.frame {σ : State} {m m' : Mem} {rs : List Region} (hf : Frame rs m m') (hK : P.K ≤ 1024)
    (hd : ∀ x ∈ rs, Region.Disjoint ⟨P.lay.fr oEM1, P.K⟩ x ∧ Region.Disjoint ⟨P.lay.fr oSt, 4⟩ x)
    (h : St1 P σ m) : St1 P σ m' :=
  let ⟨rc, cr, sl⟩ := h
  ⟨rc, cr.frame hf (fun x hx => (hd x hx).1) hK, (slot_frame hf fun x hx => (hd x hx).2).trans sl⟩

theorem frame1 {m : Mem} {d : Nat} {v : BitVec 32} :
    Frame [⟨P.lay.fr d, 4⟩] m (m.writeW (P.lay.fr d) v) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

theorem add_sub_ofNat (x : BitVec 32) {a b : Nat} (h : b ≤ a) :
    x + BitVec.ofNat 32 a - BitVec.ofNat 32 b = x + BitVec.ofNat 32 (a - b) := by
  conv => lhs; rw [show a = (a - b) + b by omega_arith, ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc, BitVec.add_sub_cancel]

/-! ## The pieces -/

theorem encArgs_wp {σ s : State} (h : C2 P σ s) : WP isa (.block encArgs) s (C3 P σ) := by
  obtain ⟨⟨hs, hgl⟩, cr⟩ := h
  have hK := hs.1.k1024
  obtain hol : P.ol ≤ P.K := by have := hs.1.ol64; have := hs.1.k64; omega_arith
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  obtain s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  obtain r12 : t1.gpr .r12 = P.B := by rw [u1.gpr, hs.2.sp, BitVec.add_zero]
  refine s1.wp_strFr (d := oSt) (by show oSt + 4 ≤ frameBytes; decide) (by decide) r12 fun t2 s2 m2 => ?_
  refine wp_dp (op2_imm (by decide)) fun t3 u3 => ?_
  obtain s3 : P.lay.St σ t3 := s2.of_rest (u3.rest (ws := [.r0]) (by simp)) u3.mem
  refine s3.wp_arg (j := 3) (by simp) (by dsimp only; decide) fun t4 s4 u4 => ?_
  refine s4.wp_arg (j := 1) (by simp) (by dsimp only; decide) fun t5 s5 u5 => ?_
  refine wp_dp (op2_imm (by decide)) fun t6 u6 => ?_
  refine wp_dp (op2_reg _ _) fun t7 u7 => ?_
  refine wp_dp (op2_reg _ _) fun t8 u8 => ?_
  obtain s8 : P.lay.St σ t8 := ((s5.of_rest (u6.rest (ws := [.r1]) (by simp)) u6.mem).of_rest
    (u7.rest (ws := [.r1]) (by simp)) u7.mem).of_rest (u8.rest (ws := [.r1]) (by simp)) u8.mem
  refine s8.wp_arg (j := 6) (by simp) (by dsimp only; decide) fun t9 s9 u9 => WP.block_nil ?_
  obtain mm : t9.mem = t1.mem.writeW (P.lay.fr oSt) (t1.gpr .r0) := by
    rw [u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, m2.mem]
  obtain r12' : t5.gpr .r12 = P.B := by
    rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), m2.gpr, r12]
  refine ⟨⟨⟨hs.1, s9⟩, hgl⟩, ⟨s.gpr .r0, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mm, u1.mem]
    refine cr.frame frame1 (fun x hx => ?_) hK
    simp only [List.mem_singleton] at hx; subst hx
    exact Lay.fr_sep (by simp only [oEM1, oSt]; omega_arith) (by simp only [oEM1]; omega_arith) (by simp only [oSt]; omega_arith)
  · rw [Slot, mm, Mem.readW_writeW_self32, u1.other _ (by decide)]
  · rw [u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide),
      u5.other _ (by decide), u4.other _ (by decide), u3.gpr, dpVal, m2.gpr, r12]
  · rw [u9.other _ (by decide), u8.gpr, dpVal, u7.gpr, dpVal, u6.gpr, dpVal, r12', u7.other .lr (by decide),
      u6.other .r3 (by decide), u6.other .lr (by decide), u5.gpr, u5.other .r3 (by decide), u4.gpr]
    change P.B + BitVec.ofNat 32 oEM1 + BitVec.ofNat 32 P.K - BitVec.ofNat 32 P.ol = _
    rw [add_sub_ofNat _ hol, Offset.add_ofNat_add_ofNat]
  · rw [u9.gpr]; rfl
  · rw [u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide),
      u5.other _ (by decide), u4.gpr]; rfl
  · rw [u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide), u5.gpr]
    rfl

theorem encode_wp {σ s : State} (h : C3 P σ s) : WP isa Impl.RsaPkcs1Sig.Arm.encode s (C4 P σ) := by
  obtain ⟨⟨hs, hgl⟩, st, r0, r1, r2, r3, lr⟩ := h
  have ok := hs.1.ok
  have hK := hs.1.k1024
  have h64 := hs.1.ol64
  obtain hol : P.ol ≤ P.K := by have := hs.1.k64; omega_arith
  have fit := ok.fit
  obtain e2 : State.addr (P.B + BitVec.ofNat 32 oEM2) = P.lay.fr oEM2 :=
    ok.addrB (by show oEM2 < frameBytes + 56 + 36; decide)
  obtain e1 : State.addr (P.B + BitVec.ofNat 32 (oEM1 + (P.K - P.ol))) = P.lay.fr (oEM1 + (P.K - P.ol)) :=
    ok.addrB (by show _ < frameBytes + 56 + 36; simp only [oEM1, frameBytes]; omega_arith)
  obtain f : ∀ d, d < 2 ^ 32 → d + P.K ≤ frameBytes → (P.B + BitVec.ofNat 32 d).toNat + P.K ≤ 2 ^ 32 := by
    intro d hd hdK
    rw [Proof.X25519.Arm.toNat_add_lt (by rw [BitVec.toNat_ofNat]; simp only [frameBytes] at fit hdK ⊢; omega_arith),
      BitVec.toNat_ofNat]
    simp only [frameBytes] at fit hdK ⊢; omega_arith
  obtain hin : EncIn s (P.B + BitVec.ofNat 32 oEM2) (P.B + BitVec.ofNat 32 (oEM1 + (P.K - P.ol))) P.hash P.K P.ol :=
    { r0 := r0, r1 := r1, r2 := r2, r3 := r3, lr := lr
      k64 := hs.1.k64, k1024 := hK, dl32 := by omega_arith
      dstFit := f _ (by decide) (by simp only [oEM2, frameBytes]; omega_arith)
      srcFit := by
        have := f (oEM1 + (P.K - P.ol)) (by simp only [oEM1]; omega_arith) (by simp only [oEM1, frameBytes]; omega_arith)
        omega_arith
      write := by rw [e2]; exact hs.2.inFr (by show oEM2 + P.K ≤ frameBytes; simp only [oEM2, frameBytes]; omega_arith)
      read := by
        rw [e1]
        exact hs.2.inFrR (by show oEM1 + (P.K - P.ol) + P.ol ≤ frameBytes; simp only [oEM1, frameBytes]; omega_arith)
      sep := by
        rw [e1, e2]
        exact Lay.fr_sep (by simp only [oEM1, oEM2]; omega_arith) (by simp only [oEM1]; omega_arith) (by simp only [oEM2]; omega_arith) }
  refine WP.mono (encode_ok hin) fun t ⟨fr, rest, res⟩ => ?_
  rw [e2] at fr
  obtain st' : P.lay.St σ t := hs.2.frameW (by show oEM2 + P.K ≤ frameBytes; simp only [oEM2, frameBytes]; omega_arith)
    fr rest.rd rest.wr rest.sp
  obtain d1 : Region.Disjoint ⟨P.lay.fr oEM1, P.K⟩ ⟨P.lay.fr oEM2, P.K⟩ :=
    Lay.fr_sep (by simp only [oEM1, oEM2]; omega_arith) (by simp only [oEM1]; omega_arith) (by simp only [oEM2]; omega_arith)
  refine ⟨⟨⟨hs.1, st'⟩, hgl⟩, st.frame fr hK fun x hx => ?_, ?_⟩
  · simp only [List.mem_singleton] at hx; subst hx
    exact ⟨d1, Lay.fr_sep (by simp only [oSt, oEM2]; omega_arith) (by simp only [oSt]; omega_arith) (by simp only [oEM2]; omega_arith)⟩
  · have ht : Tail P t.mem = Spec.Rsa.bytesAt s.mem (P.lay.fr (oEM1 + (P.K - P.ol))) P.ol := by
      simp only [Tail]
      obtain hd := VG.Proof.RsaPkcs1Sig.bytesAt_drop s.mem (P.lay.fr oEM1) (P.K - P.ol) P.ol
      rw [show P.K - P.ol + P.ol = P.K by omega_arith, Offset.add_ofNat_add_ofNat] at hd
      rw [bytesAt_frame fr (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact d1) (by omega_arith), hd]
    rw [e1, e2, ← ht] at res
    simp only [ER, EncR]
    revert res
    cases encOut P.hash.toNat (Tail P t.mem) P.K with
    | some em => exact fun r => r
    | none => exact fun r => r

theorem cmpArgs_wp {σ s : State} (h : C4 P σ s) : WP isa (.block cmpArgs) s (C5 P σ) := by
  obtain ⟨⟨hs, hgl⟩, st, er⟩ := h
  have hK := hs.1.k1024
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  obtain s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  refine s1.wp_strFr (d := oOk) (by show oOk + 4 ≤ frameBytes; decide) (by decide)
    (by rw [u1.gpr, hs.2.sp, BitVec.add_zero]) fun t2 s2 m2 => ?_
  refine wp_dp (op2_imm (by decide)) fun t3 u3 => ?_
  refine wp_dp (op2_imm (by decide)) fun t4 u4 => ?_
  obtain s4 : P.lay.St σ t4 := (s2.of_rest (u3.rest (ws := [.r0]) (by simp)) u3.mem).of_rest
    (u4.rest (ws := [.r1]) (by simp)) u4.mem
  refine s4.wp_arg (j := 3) (by simp) (by dsimp only; decide) fun t5 s5 u5 => ?_
  refine wp_mov (op2_imm (by decide)) fun t6 u6 => WP.block_nil ?_
  obtain mm : t6.mem = t1.mem.writeW (P.lay.fr oOk) (t1.gpr .r3) := by
    rw [u6.mem, u5.mem, u4.mem, u3.mem, m2.mem]
  obtain r12 : t2.gpr .r12 = P.B := by rw [m2.gpr, u1.gpr, hs.2.sp, BitVec.add_zero]
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
    exact ⟨Lay.fr_sep (by simp only [oEM1, oOk]; omega_arith) (by simp only [oEM1]; omega_arith) (by simp only [oOk]; omega_arith),
      Lay.fr_sep (by simp only [oEM2, oOk]; omega_arith) (by simp only [oEM2]; omega_arith) (by simp only [oOk]; omega_arith)⟩
  · rw [Slot, mm, Mem.readW_writeW_self32, u1.other _ (by decide)]
  · rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.gpr, dpVal, r12]
  · rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr, dpVal, u3.other _ (by decide), r12]
  · rw [u6.other _ (by decide), u5.gpr]; rfl

theorem compare_wp {σ s : State} (h : C5 P σ s) : WP isa Impl.Bignum.Arm.compareBytes s (C6 P σ) := by
  obtain ⟨⟨hs, hgl⟩, st, ok1, r0, r1, lr, r2⟩ := h
  have ok := hs.1.ok
  have hK := hs.1.k1024
  have fit := ok.fit
  obtain e1 : State.addr (P.B + BitVec.ofNat 32 oEM1) = P.lay.fr oEM1 :=
    ok.addrB (by show oEM1 < frameBytes + 56 + 36; decide)
  obtain e2 : State.addr (P.B + BitVec.ofNat 32 oEM2) = P.lay.fr oEM2 :=
    ok.addrB (by show oEM2 < frameBytes + 56 + 36; decide)
  obtain f : ∀ d, d < 2 ^ 32 → d + P.K ≤ frameBytes → (P.B + BitVec.ofNat 32 d).toNat + P.K ≤ 2 ^ 32 := by
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

theorem result_wp {σ s : State} (h : C6 P σ s) : WP isa (.block result) s (C7 P σ) := by
  obtain ⟨⟨hs, hgl⟩, ⟨rc, cr, slR⟩, ⟨okv, er, slO⟩, eq⟩ := h
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  obtain s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
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
  obtain s11 : P.lay.St σ t11 := (((((((s3.of_rest (u4.rest (ws := [.r1]) (by simp)) u4.mem).of_rest
    (u5.rest (ws := [.r1]) (by simp)) u5.mem).of_rest (u6.rest (ws := [.r1]) (by simp)) u6.mem).of_rest
    (u7.rest (ws := [.r1]) (by simp)) u7.mem).of_rest (u8.rest (ws := [.r2]) (by simp)) u8.mem).of_rest
    (u9.rest (ws := [.r1]) (by simp)) u9.mem).of_rest (u10.rest (ws := [.r0]) (by simp)) u10.mem).of_rest
    (u11.rest (ws := [.r3]) (by simp)) u11.mem
  obtain mm : t11.mem = s.mem := by
    rw [u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  refine ⟨⟨⟨hs.1, s11⟩, hgl⟩, fun nB hn hp h hh => ?_⟩
  obtain r2_3 : t3.gpr .r2 = s.gpr .r2 := by
    rw [u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide)]
  obtain eqb : t9.gpr .r1 = BitVec.ofNat 32 (decide (s.gpr .r2 = 0#32)).toNat := by
    rw [u9.gpr, dpVal, u8.gpr, u8.other _ (by decide), u7.gpr, u6.gpr, dpVal, u5.gpr, dpVal, u4.gpr,
      u4.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), r2_3]
    exact VG.Proof.Rsa.Arm.zero_test32 _
  obtain r0_10 : t10.gpr .r0 = rc &&& okv := by
    rw [u10.gpr, dpVal, u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide),
      u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.gpr,
      u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide),
      u5.other _ (by decide), u4.other _ (by decide), u3.gpr, u2.mem, u1.mem, slR, slO]
  rw [u11.gpr, dpVal, r0_10, u10.other _ (by decide), eqb, mm]
  obtain hsg : (sigB P σ).length = P.K := by rw [bytesAt_length, hgl]
  obtain ⟨h', hh', hol⟩ := hs.1.hh
  rw [hh] at hh'
  cases hh'
  refine recover_result hn hsg hh hol (cr nB hn hp) er ?_
  rw [decide_eq_true_iff]
  exact eq

end VG.Proof.RsaPkcs1Sig.Arm.Rc

end

end


/-!
# RSASSA-PKCS1-v1_5 recovery with a precomputed public key on ARMv7: the value

The last `out_len` bytes of `EM₁` copied to `out` (`copyArgs_wp`,
`copy_wp`), and `out` masked with `0 - r` for the result `r`
(`maskArgs_wp`, `mask_wp`, `masked`), which is returned (`fin_wp`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.Arm.Rc

open VG VG.Arm VG.Impl.RsaPkcs1Sig.Arm.RecoverPrecomputed
open VG.Impl.RsaPkcs1Sig.Arm.Precomputed (frameBytes oSt oOk oEM1 oEM2 ret0)
open VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_dp op2_imm op2_reg dpVal)

variable {P : EP}

/-- The result and `out`. -/
def RO (P : EP) (σ : State) (m : Mem) (r : BitVec 32) : Prop :=
  RR P σ r (Spec.Rsa.bytesAt m (State.addr P.out) P.ol)

/-- Before the copy. -/
def C8 (P : EP) (σ s : State) : Prop :=
  C0 P σ s ∧ RR P σ (s.gpr .r3) (Tail P s.mem) ∧ s.gpr .r0 = P.out ∧
    s.gpr .r1 = P.B + BitVec.ofNat 32 (oEM1 + (P.K - P.ol)) ∧ s.gpr .lr = BitVec.ofNat 32 P.ol

/-- After the copy. -/
def C9 (P : EP) (σ s : State) : Prop := C0 P σ s ∧ RO P σ s.mem (s.gpr .r3)

/-- Before the mask. -/
def C10 (P : EP) (σ s : State) : Prop :=
  C0 P σ s ∧ RO P σ s.mem (s.gpr .r3) ∧ s.gpr .r2 = 0 - s.gpr .r3 ∧ s.gpr .r0 = P.out ∧
    s.gpr .lr = BitVec.ofNat 32 P.ol

/-- After the mask. -/
def C11 (P : EP) (σ s : State) : Prop := C0 P σ s ∧ Res P σ s.mem (s.gpr .r3)

theorem copyArgs_wp {σ s : State} (h : C7 P σ s) : WP isa (.block copyArgs) s (C8 P σ) := by
  obtain ⟨⟨hs, hgl⟩, rr⟩ := h
  obtain hol : P.ol ≤ P.K := by have := hs.1.ol64; have := hs.1.k64; omega_arith
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  obtain s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  refine s1.wp_arg (j := 0) (by simp) (by dsimp only; decide) fun t2 s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun t3 u3 => ?_
  obtain s3 : P.lay.St σ t3 := s2.of_rest (u3.rest (ws := [.r1]) (by simp)) u3.mem
  refine s3.wp_arg (j := 3) (by simp) (by dsimp only; decide) fun t4 s4 u4 => ?_
  refine wp_dp (op2_reg _ _) fun t5 u5 => ?_
  obtain s5 : P.lay.St σ t5 := s4.of_rest (u5.rest (ws := [.r1]) (by simp)) u5.mem
  refine s5.wp_arg (j := 1) (by simp) (by dsimp only; decide) fun t6 s6 u6 => ?_
  refine wp_dp (op2_reg _ _) fun t7 u7 => WP.block_nil ?_
  obtain mm : t7.mem = s.mem := by rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  obtain r3 : t7.gpr .r3 = s.gpr .r3 := by
    rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide)]
  refine ⟨⟨⟨hs.1, s6.of_rest (u7.rest (ws := [.r1]) (by simp)) u7.mem⟩, hgl⟩, by rw [r3, mm]; exact rr, ?_, ?_, ?_⟩
  · rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.other _ (by decide), u2.gpr]; rfl
  · rw [u7.gpr, dpVal, u6.other .r1 (by decide), u6.gpr, u5.gpr, dpVal, u4.other .r1 (by decide), u4.gpr,
      u3.gpr, dpVal, u2.other .r12 (by decide), u1.gpr, hs.2.sp, BitVec.add_zero]
    change P.B + BitVec.ofNat 32 oEM1 + BitVec.ofNat 32 P.K - BitVec.ofNat 32 P.ol = _
    rw [add_sub_ofNat _ hol, Offset.add_ofNat_add_ofNat]
  · rw [u7.other _ (by decide), u6.gpr]; rfl

theorem copy_wp {σ s : State} (h : C8 P σ s) : WP isa Impl.Bignum.Arm.copyBytes s (C9 P σ) := by
  obtain ⟨⟨hs, hgl⟩, rr, r0, r1, lr⟩ := h
  have ok := hs.1.ok
  have hK := hs.1.k1024
  have h64 := hs.1.ol64
  obtain hol : P.ol ≤ P.K := by have := hs.1.k64; omega_using [h64, this]
  have fit := ok.fit
  obtain hfo := ok.fits P.OUT (by simp)
  simp only [Proof.X25519.Arm.addr_toNat] at hfo
  obtain e1 : State.addr (P.B + BitVec.ofNat 32 (oEM1 + (P.K - P.ol))) = P.lay.fr (oEM1 + (P.K - P.ol)) :=
    ok.addrB (by show _ < frameBytes + 56 + 36; simp only [oEM1, frameBytes]; omega_using [hK])
  obtain hsrc : (P.B + BitVec.ofNat 32 (oEM1 + (P.K - P.ol))).toNat + P.ol ≤ 2 ^ 32 := by
    rw [Proof.X25519.Arm.toNat_add_lt (by rw [BitVec.toNat_ofNat]; simp only [oEM1, frameBytes] at fit ⊢; omega_using [hK, fit]),
      BitVec.toNat_ofNat]
    simp only [oEM1, frameBytes] at fit ⊢; omega_using [hK, h64, fit]
  obtain ctx := Bignum.Arm.copyCtx_of_regions s (P.B + BitVec.ofNat 32 (oEM1 + (P.K - P.ol))) P.out (n := P.ol)
    (by omega_using [h64]) hsrc hfo
    (by rw [e1]; exact hs.2.inFrR (by show oEM1 + (P.K - P.ol) + P.ol ≤ frameBytes; simp only [oEM1, frameBytes]; omega_using [hK, h64]))
    ⟨P.OUT, by rw [hs.2.wr, ok.wr]; simp, Region.contains_self _ _⟩
    (by rw [e1]; exact ok.stk_fr (R := P.OUT) (.inr (by simp)) (by simp only [oEM1, frameBytes]; omega_using [hK, h64]))
  refine WP.mono (Bignum.Arm.copyBytes_ok s ctx hs.1.ol_pos r1 r0 lr) fun t ht => ?_
  obtain fr := ht.frame hfo
  obtain st : P.lay.St σ t := hs.2.write fr (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨P.OUT, by simp, fun _ h => h⟩)
    ht.rest.rd ht.rest.wr ht.rest.sp
  refine ⟨⟨⟨hs.1, st⟩, hgl⟩, ?_⟩
  obtain hb : Spec.Rsa.bytesAt t.mem (State.addr P.out) P.ol = Tail P s.mem := by
    rw [bytesAt_of_read (ht.read hsrc hfo), e1]
    obtain hd := VG.Proof.RsaPkcs1Sig.bytesAt_drop s.mem (P.lay.fr oEM1) (P.K - P.ol) P.ol
    rw [show P.K - P.ol + P.ol = P.K by omega_using [hol], Offset.add_ofNat_add_ofNat] at hd
    exact hd.symm
  rw [RO, hb, ht.rest.gpr .r3 (by decide)]
  exact rr

theorem maskArgs_wp {σ s : State} (h : C9 P σ s) : WP isa (.block maskArgs) s (C10 P σ) := by
  obtain ⟨⟨hs, hgl⟩, ro⟩ := h
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  refine wp_mov (op2_imm (by decide)) fun t2 u2 => ?_
  refine wp_dp (op2_reg _ _) fun t3 u3 => ?_
  obtain s3 : P.lay.St σ t3 := ((hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem).of_rest
    (u2.rest (ws := [.r2]) (by simp)) u2.mem).of_rest (u3.rest (ws := [.r2]) (by simp)) u3.mem
  refine s3.wp_arg (j := 0) (by simp) (by dsimp only; decide) fun t4 s4 u4 => ?_
  refine s4.wp_arg (j := 1) (by simp) (by dsimp only; decide) fun t5 s5 u5 => WP.block_nil ?_
  obtain mm : t5.mem = s.mem := by rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  obtain r3 : t5.gpr .r3 = s.gpr .r3 := by
    rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide),
      u1.other _ (by decide)]
  refine ⟨⟨⟨hs.1, s5⟩, hgl⟩, by rw [mm, r3]; exact ro, ?_, ?_, ?_⟩
  · rw [u5.other _ (by decide), u4.other _ (by decide), u3.gpr, dpVal, u2.gpr, u2.other _ (by decide), r3,
      u1.other _ (by decide)]
  · rw [u5.other _ (by decide), u4.gpr]; rfl
  · rw [u5.gpr]; rfl

/-- `out` masked with `0 - r`. -/
theorem masked {o : Option (List Byte)} {r : BitVec 32} {v : List Byte} {m' : Mem} {a : Addr} {n : Nat}
    (h : Rv o r v) (hl : v.length = n)
    (hb : Spec.Rsa.bytesAt m' a n = v.map (· &&& (0 - r).setWidth 8)) : Spec.Rsa.written m' a n r o := by
  unfold Rv at h
  cases o with
  | some y =>
    obtain ⟨rfl, rfl⟩ := h
    obtain e : ((0 : BitVec 32) - 1).setWidth 8 = BitVec.allOnes 8 := by decide
    rw [e] at hb
    refine ⟨rfl, hb.trans ?_⟩
    exact (List.map_congr_left (g := id) fun x _ => BitVec.and_allOnes).trans (List.map_id _)
  | none =>
    subst h
    obtain e : ((0 : BitVec 32) - 0).setWidth 8 = 0 := by decide
    rw [e] at hb
    refine ⟨rfl, hb.trans ?_⟩
    apply List.ext_getElem (by simp [hl])
    intro i h₁ h₂
    simp

theorem mask_wp {σ s : State} (h : C10 P σ s) : WP isa Impl.Bignum.Arm.maskBytes s (C11 P σ) := by
  obtain ⟨⟨hs, hgl⟩, ro, r2, r0, lr⟩ := h
  have ok := hs.1.ok
  obtain hfo := ok.fits P.OUT (by simp)
  simp only [Proof.X25519.Arm.addr_toNat] at hfo
  have h64 := hs.1.ol64
  refine WP.mono (Bignum.Arm.maskBuffer_ok s (dst := P.out) (n := P.ol) hs.1.ol_pos (by omega_using [h64])
    hfo ⟨P.OUT, by rw [hs.2.wr, ok.wr]; simp, Region.contains_self _ _⟩ r0 lr) fun t ⟨hb, fr, rst⟩ => ?_
  obtain st : P.lay.St σ t := hs.2.write fr (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨P.OUT, by simp, fun _ h => h⟩) rst.rd rst.wr rst.sp
  refine ⟨⟨⟨hs.1, st⟩, hgl⟩, fun nB hn hp h hh => ?_⟩
  rw [rst.gpr .r3 (by decide)]
  rw [r2] at hb
  exact masked (ro nB hn hp h hh) (bytesAt_length _ _ _) hb

theorem fin_wp {σ s : State} (h : C11 P σ s) : WP isa (.block [.mov .r0 (.reg .r3)]) s (Fin P σ) :=
  wp_mov (op2_reg _ _) fun t u => WP.block_nil ⟨⟨h.1.1.1, h.1.1.2.of_rest (u.rest (ws := [.r0]) (by simp)) u.mem⟩,
    by rw [u.mem, u.gpr]; exact h.2⟩

end VG.Proof.RsaPkcs1Sig.Arm.Rc

end

end


/-!
# RSASSA-PKCS1-v1_5 recovery with a precomputed public key on ARMv7: the body

The pieces as `VP`s, correct and constant time at once, put together
(`body_vp`): from the state the body starts from, it ends with the result
(`Fin`), and two runs with the same public data leak the same trace.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.Arm.Rc

open VG VG.Arm VG.Impl.RsaPkcs1Sig.Arm.RecoverPrecomputed
open VG.Impl.RsaPkcs1Sig.Arm.Precomputed (frameBytes oSt oOk oEM1 oEM2 ret0)
open VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.Rsa.Arm.Recover (VP)

variable {P : EP}

theorem S_sp {σ₁ σ₂ s₁ s₂ : State} (h₁ : S P σ₁ s₁) (h₂ : S P σ₂ s₂) : s₁.sp = s₂.sp := by
  rw [h₁.2.sp, h₂.2.sp]

theorem lenCheck_vp : VP (S P) (.block lenCheck) (H1 P) :=
  VP.stk (code := [_, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁ h₂) fun _ _ h => lenCheck_wp h

theorem cmp_vp : VP (H1 P) (.block [.cmp .r0 (.imm 0)]) (H2 P) :=
  VP.taint [.r0] Vf.cmp_taint (fun _ _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2]) fun _ _ h => cmp_wp h

theorem fail_vp : VP (fun σ s => H2 P σ s ∧ isa.eval .ne s = some true)
    (.seq (.block zeroArgs) (.seq Impl.Bignum.Arm.maskBytes (.block ret0))) (Fin P) :=
  (VP.stk (code := [_, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1.1 h₂.1.1)
    fun _ _ h => zeroArgs_wp h).seq
  ((VP.ct Bignum.Arm.maskBytes_ct (fun _ _ _ _ h₁ h₂ => ⟨by rw [h₁.2.2.1, h₂.2.2.1], by rw [h₁.2.2.2.1, h₂.2.2.2.1]⟩)
    fun _ _ h => zero_wp h).seq
  (VP.taint [] Vf.ret0_taint (fun _ _ _ _ _ _ _ h => absurd h List.not_mem_nil) fun _ _ h => ret0_wp h))

theorem callArgs_vp : VP (fun σ s => H2 P σ s ∧ isa.eval .ne s = some false) (.block callArgs) (C1 P) :=
  VP.stk (code := [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _]) (by decide) (by decide)
    (fun _ _ _ _ h₁ h₂ => S_sp h₁.1.1 h₂.1.1) fun _ _ h => callArgs_wp (c0_of h)

theorem encArgs_vp : VP (C2 P) (.block encArgs) (C3 P) :=
  VP.stk (code := [_, _, _, _, _, _, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1.1 h₂.1.1)
    fun _ _ h => encArgs_wp h

theorem encode_vp : VP (C3 P) Impl.RsaPkcs1Sig.Arm.encode (C4 P) :=
  VP.taint [.r0, .r1, .r2, .r3, .lr] encode_taint (fun _ _ _ _ h₁ h₂ r hr => by
    obtain ⟨-, -, a0, a1, a2, a3, a4⟩ := h₁
    obtain ⟨-, -, b0, b1, b2, b3, b4⟩ := h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [a0, b0]
    · rw [a1, b1]
    · rw [a2, b2]
    · rw [a3, b3]
    · rw [a4, b4]) fun _ _ h => encode_wp h

theorem cmpArgs_vp : VP (C4 P) (.block cmpArgs) (C5 P) :=
  VP.stk (code := [_, _, _, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1.1 h₂.1.1)
    fun _ _ h => cmpArgs_wp h

theorem compare_vp : VP (C5 P) Impl.Bignum.Arm.compareBytes (C6 P) :=
  VP.ct Bignum.Arm.compareBytes_ct (fun _ _ _ _ h₁ h₂ => by
    obtain ⟨-, -, -, a0, a1, a2, -⟩ := h₁
    obtain ⟨-, -, -, b0, b1, b2, -⟩ := h₂
    exact ⟨by rw [a0, b0], by rw [a1, b1], by rw [a2, b2]⟩) fun _ _ h => compare_wp h

theorem result_vp : VP (C6 P) (.block result) (C7 P) :=
  VP.stk (code := [_, _, _, _, _, _, _, _, _, _]) (by decide) (by decide)
    (fun _ _ _ _ h₁ h₂ => S_sp h₁.1.1 h₂.1.1) fun _ _ h => result_wp h

theorem copyArgs_vp : VP (C7 P) (.block copyArgs) (C8 P) :=
  VP.stk (code := [_, _, _, _, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1.1 h₂.1.1)
    fun _ _ h => copyArgs_wp h

theorem copy_vp : VP (C8 P) Impl.Bignum.Arm.copyBytes (C9 P) :=
  VP.ct Bignum.Arm.copyBytes_ct (fun _ _ _ _ h₁ h₂ => by
    obtain ⟨-, -, a0, a1, a2⟩ := h₁
    obtain ⟨-, -, b0, b1, b2⟩ := h₂
    exact ⟨by rw [a0, b0], by rw [a1, b1], by rw [a2, b2]⟩) fun _ _ h => copy_wp h

theorem maskArgs_vp : VP (C9 P) (.block maskArgs) (C10 P) :=
  VP.stk (code := [_, _, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1.1 h₂.1.1)
    fun _ _ h => maskArgs_wp h

theorem mask_vp : VP (C10 P) Impl.Bignum.Arm.maskBytes (C11 P) :=
  VP.ct Bignum.Arm.maskBytes_ct (fun _ _ _ _ h₁ h₂ => by
    obtain ⟨-, -, -, a0, a1⟩ := h₁
    obtain ⟨-, -, -, b0, b1⟩ := h₂
    exact ⟨by rw [a0, b0], by rw [a1, b1]⟩) fun _ _ h => mask_wp h

theorem fin_vp : VP (C11 P) (.block [.mov .r0 (.reg .r3)]) (Fin P) :=
  VP.taint [] fin_taint (fun _ _ _ _ _ _ _ h => absurd h List.not_mem_nil) fun _ _ h => fin_wp h

theorem rest_vp (c : PdImpl) :
    VP (fun σ s => H2 P σ s ∧ isa.eval .ne s = some false) (rest c.name c.code) (Fin P) :=
  callArgs_vp.seq ((call_vp c).seq (encArgs_vp.seq (encode_vp.seq (cmpArgs_vp.seq (compare_vp.seq
    (result_vp.seq (copyArgs_vp.seq (copy_vp.seq (maskArgs_vp.seq (mask_vp.seq fin_vp))))))))))

theorem body_vp (c : PdImpl) : VP (S P) (body c.name c.code) (Fin P) :=
  lenCheck_vp.seq (cmp_vp.seq (VP.ite (fun _ _ _ _ h₁ h₂ => by
    rw [Proof.X25519.Arm.eval_ne, Proof.X25519.Arm.eval_ne, h₁.2, h₂.2]) fail_vp (rest_vp c)))

end VG.Proof.RsaPkcs1Sig.Arm.Rc

end

end


/-!
# RSASSA-PKCS1-v1_5 recovery with a precomputed public key on ARMv7: verified

The frames around the body (`wrap_ok`, `wrap_ct`), the result as the shared
contract states it, and a state that meets it (`sat`):
`vg_rsa_pkcs1_recover_precomputed`, calling any implementation `c` of
`vg_rsa_public_precomputed_checked`, is verified (`code_verified`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.Arm.Rc

open VG VG.Arm VG.Impl.RsaPkcs1Sig.Arm.RecoverPrecomputed
open VG.Impl.RsaPkcs1Sig.Arm.Precomputed (frameBytes oSt oOk oEM1 oEM2 ret0)
open VG.Proof.RsaPkcs1Sig.Arm

theorem entered_state {s : State} (h : spec.pre s) :
    S (ep s) (entered frameBytes s) (entered frameBytes s) :=
  ⟨in_of_pre h, ⟨(in_of_pre h).ok, (in_of_pre h).ok.sp, rfl, rfl, Frame.refl _ _⟩⟩

theorem spec_sp {s : State} (h : spec.pre s) : stackBytes ≤ s.sp.toNat := by
  sig_pre [Spec.RsaPkcs1Sig.recoverPrecomputedContract, Spec.RsaPkcs1Sig.recoverPrecomputedSig, abi,
    argRegs, reduceClassify, Loc.val] at h
  exact h.1

theorem code_ok (c : PdImpl) {s : State} (h : spec.pre s) :
    WP isa (code c.name c.code) s fun t => abiPreserved s t ∧ spec.post s t := by
  obtain hs := spec_sp h
  obtain hin := in_of_pre h
  obtain st := entered_state h
  obtain hsp : 56 + frameBytes ≤ s.sp.toNat := by simp only [stackBytes] at hs; omega_using [hs]
  refine WP.mono (wrap_ok (by decide) (by omega_using [hsp]) (W := (ep s).lay.W)
    (Q := fun r m => Res (ep s) (entered frameBytes s) m r) (fun r hr => ?_)
    (WP.mono ((body_vp c).wp _ _ st) fun u hu => ⟨hu.1.2.frame, hu.2⟩)) fun t ⟨abi, res⟩ => ⟨abi, ?_⟩
  · rw [pushRegion_eq (F := frameBytes) (A := 36) (argv := (ep s).argv)
      (ro := [(ep s).N, (ep s).E, (ep s).SIG, (ep s).PRE]) (rw := [(ep s).OUT, (ep s).SCR]) hsp]
    exact hin.ok.push_apart r hr
  · sig_post [Spec.RsaPkcs1Sig.recoverPrecomputedContract, Spec.RsaPkcs1Sig.recoverPrecomputedSig, abi,
      argRegs, reduceClassify, Loc.val]
    rw [BitVec.setWidth_append_eq_right]
    intro hp hh hid
    obtain hn : (Spec.Rsa.bytesAt s.mem (BitVec.setWidth 64 (s.gpr .r2)) (s.gpr .r3).toNat).length =
        (s.gpr .r3).toNat := bytesAt_length _ _ _
    obtain w := res _ hn hp hh hid
    obtain ro := fun {R : Region} (hR : R ∈ [(ep s).N, (ep s).E, (ep s).SIG, (ep s).PRE]) =>
      entered_ro (F := frameBytes) (A := 36) (argv := (ep s).argv) (rw := [(ep s).OUT, (ep s).SCR]) hin.ok hsp hR
    obtain hG : sigB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 3))
        (stackArg s 4).toNat := ro (R := (ep s).SIG) (by simp)
    rw [hG, ← VG.Proof.RsaPkcs1Sig.recover_eq_recoverEnc] at w
    exact w

theorem map_toNat_inj {w : Nat} {a b : List (BitVec w)} (h : a.map (·.toNat) = b.map (·.toNat)) : a = b :=
  (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h

/-- Two entry states with the same public data have the same public parameters. -/
theorem ep_eq {s₁ s₂ : State} (hp : spec.pub s₁ s₂) : ep s₁ = ep s₂ := by
  sig_pub [Spec.RsaPkcs1Sig.recoverPrecomputedContract, Spec.RsaPkcs1Sig.recoverPrecomputedSig, abi,
    argRegs, reduceClassify, Loc.val] at hp
  obtain ⟨hsp, hl, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := hp
  obtain ⟨hab, hw⟩ := List.append_inj hl (by simp [bytesAt_length, h3, a1, a4])
  obtain hx := map_toNat_inj hab
  obtain ⟨hx, -⟩ := List.append_inj hx (by simp [bytesAt_length, h3, a1])
  obtain ⟨-, he⟩ := List.append_inj hx (by simp [bytesAt_length, h3])
  obtain hw' := map_toNat_inj hw
  simp only [ep]
  rw [hsp, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, a8]
  rw [a0, a1] at he
  rw [a7, a8] at hw'
  rw [show State.addr (stackArg s₂ 0) = BitVec.setWidth 64 (stackArg s₂ 0) from rfl, he,
    show State.addr (stackArg s₂ 7) = BitVec.setWidth 64 (stackArg s₂ 7) from rfl, hw']

theorem code_ct (c : PdImpl) : ConstantTime isa spec.pre spec.pub (code c.name c.code) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  obtain hep := ep_eq hp
  obtain hsp : s₁.sp = s₂.sp := by
    sig_pub [Spec.RsaPkcs1Sig.recoverPrecomputedContract, Spec.RsaPkcs1Sig.recoverPrecomputedSig, abi,
      argRegs, reduceClassify, Loc.val] at hp
    exact hp.1
  refine (wrap_ct (F := frameBytes) (by decide) (P := fun a b => a = s₁ ∧ b = s₂)
    (fun a b h => by rw [h.1, h.2]; exact hsp)
    (fun a b h => by rw [h.1]; have := spec_sp h₁; simp only [stackBytes] at this; omega_using [this]) ?_
    s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  refine (body_vp (P := ep s₁) c).ct.mono ?_ fun _ _ _ => trivial
  rintro a b ⟨_, _, ⟨rfl, rfl⟩, rfl, rfl⟩
  exact ⟨_, _, entered_state h₁, by rw [hep]; exact entered_state h₂⟩

/-- A state that meets the shared contract: a modulus of 64 bytes, `e` of one
byte, SHA-256 (`out` of 32 bytes), an empty signature, and the stack
arguments at `0x8000`. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 32 | .r2 => 0x2000 | .r3 => 64 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x21 else
    if a = 0x8004 then 1 else
    if a = 0x8008 then 3 else
    if a = 0x800d then 0x31 else
    if a = 0x8015 then 0x40 else
    if a = 0x8018 then 0x20 else
    if a = 0x8019 then 4 else
    if a = 0x801d then 0x70 else
    if a = 0x8020 then 0x10 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x3100, 0⟩, ⟨0x7000, 128⟩, ⟨0x8000, 36⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 8448⟩]

theorem sat : ∃ s, spec.pre s := by
  sig_implies_sat [Spec.RsaPkcs1Sig.recoverPrecomputedContract, Spec.RsaPkcs1Sig.recoverPrecomputedSig, abi,
    argRegs, reduceClassify, Loc.val, State.addr]
    [satState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid, Spec.Rsa.scratchWords,
      Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords, Spec.RsaPkcs1Sig.Hash.ofId,
      Spec.RsaPkcs1Sig.Hash.len] using satState

/-- `vg_rsa_pkcs1_recover_precomputed`, calling `c`, meets the shared contract. -/
theorem code_verified (c : PdImpl) : Verified target (code c.name c.code) spec :=
  ⟨fun _ h => let ⟨t, s', he, hq⟩ := code_ok c h; ⟨t, s', he, hq.1, hq.2⟩, code_ct c, sat⟩

end VG.Proof.RsaPkcs1Sig.Arm.Rc
