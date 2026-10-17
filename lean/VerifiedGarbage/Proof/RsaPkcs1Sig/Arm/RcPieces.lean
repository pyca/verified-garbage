module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.RcBase
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Encode
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Recover
public import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
public import VerifiedGarbage.Proof.Bignum.Arm.MaskBuffer
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

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
  have s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
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
  have e : ∀ x : BitVec 32, x - 0 = x := fun x => by simp
  rw [z1, r0, e, cmp_eq hs.1.gl32 (by omega)]

theorem zeroArgs_wp {σ s : State} (h : H2 P σ s ∧ isa.eval .ne s = some true) :
    WP isa (.block zeroArgs) s (Z1 P σ) := by
  obtain ⟨⟨hs, z⟩, e⟩ := h
  have hne : P.gl ≠ P.K := by
    rw [Proof.X25519.Arm.eval_ne, z] at e; simpa using e
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  have s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  refine s1.wp_arg (j := 0) (by simp) (by dsimp only; decide) fun t2 s2 u2 => ?_
  refine s2.wp_arg (j := 1) (by simp) (by dsimp only; decide) fun t3 s3 u3 => ?_
  refine wp_mov (op2_imm (by decide)) fun t4 u4 => WP.block_nil
    ⟨⟨hs.1, s3.of_rest (u4.rest (ws := [.r2]) (by simp)) u4.mem⟩, hne, ?_, ?_, u4.gpr⟩
  · rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr]; rfl
  · rw [u4.other _ (by decide), u3.gpr]; rfl

theorem zero_wp {σ s : State} (h : Z1 P σ s) : WP isa Impl.Bignum.Arm.maskBytes s (Z2 P σ) := by
  obtain ⟨hs, hne, r0, lr, r2⟩ := h
  have ok := hs.1.ok
  have hfo := ok.fits P.OUT (by simp)
  simp only [Proof.X25519.Arm.addr_toNat] at hfo
  have h64 := hs.1.ol64
  refine WP.mono (Bignum.Arm.maskBuffer_ok s (dst := P.out) (n := P.ol) hs.1.ol_pos (by omega)
    hfo ⟨P.OUT, by rw [hs.2.wr, ok.wr]; simp, Region.contains_self _ _⟩ r0 lr) fun t ⟨hb, fr, rst⟩ => ?_
  have st : P.lay.St σ t := hs.2.write fr (fun r hr => by
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
  have hr : recoverEnc nB P.eB h (sigB P σ) = none := by
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
  have s0 : P.lay.St σ t0 := hs.2.of_rest (u0.rest (ws := [.r12]) (by simp)) u0.mem
  have r12 : t0.gpr .r12 = P.B := by rw [u0.gpr, hs.2.sp, BitVec.add_zero]
  refine s0.wp_copyArg (j := 4) (d := 0) r12 (by simp) (by dsimp only; decide) (by dsimp only; decide)
    (by decide) (by decide) fun t1 s1 v1 g1 m1 => ?_
  refine s1.wp_copyArg (j := 5) (d := 4) (by rw [g1 _ (by decide), r12]) (by simp) (by dsimp only; decide)
    (by dsimp only; decide) (by decide) (by decide) fun t2 s2 v2 g2 m2 => ?_
  refine s2.wp_copyArg (j := 7) (d := 8) (by rw [g2 _ (by decide), g1 _ (by decide), r12]) (by simp)
    (by dsimp only; decide) (by dsimp only; decide) (by decide) (by decide) fun t3 s3 v3 g3 m3 => ?_
  refine s3.wp_copyArg (j := 3) (d := 12) (by rw [g3 _ (by decide), g2 _ (by decide), g1 _ (by decide), r12])
    (by simp) (by dsimp only; decide) (by dsimp only; decide) (by decide) (by decide) fun t4 s4 v4 g4 m4 => ?_
  have r12' : t4.gpr .r12 = P.B := by
    rw [g4 _ (by decide), g3 _ (by decide), g2 _ (by decide), g1 _ (by decide), r12]
  refine s4.wp_copyArg (j := 9) (d := 16) r12' (by simp) (by dsimp only; decide) (by dsimp only; decide)
    (by decide) (by decide) fun t5 s5 v5 g5 m5 => ?_
  refine s5.wp_copyArg (j := 10) (d := 20) (by rw [g5 _ (by decide), r12']) (by simp) (by dsimp only; decide)
    (by dsimp only; decide) (by decide) (by decide) fun t6 s6 v6 g6 m6 => ?_
  refine wp_dp (op2_imm (by decide)) fun t7 u7 => ?_
  have s7 : P.lay.St σ t7 := s6.of_rest (u7.rest (ws := [.r0]) (by simp)) u7.mem
  refine s7.wp_arg (j := 3) (by simp) (by dsimp only; decide) fun t8 s8 u8 => ?_
  refine s8.wp_arg (j := 11) (by simp) (by dsimp only; decide) fun t9 s9 u9 => ?_
  refine s9.wp_arg (j := 12) (by simp) (by dsimp only; decide) fun t10 s10 u10 => WP.block_nil ?_
  have mm : t10.mem = t6.mem := by rw [u10.mem, u9.mem, u8.mem, u7.mem]
  refine ⟨⟨⟨hs.1, s10⟩, hgl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [mm, m6]
    have w : ∀ (m : Mem) (d e : Nat) (v : BitVec 32), d + 4 ≤ e ∨ e + 4 ≤ d → d + 4 ≤ 24 → e + 4 ≤ 24 →
        (m.writeW (P.lay.fr e) v).readW (P.lay.fr d) 32 = m.readW (P.lay.fr d) 32 :=
      fun m d e v h hd he => Lay.readW_fr_other _ _ _ h (by omega) (by omega)
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl | rfl
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
