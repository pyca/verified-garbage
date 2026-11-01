module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Mr5
public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Mr4
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Mont5
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Taint6
import VerifiedGarbage.Proof.RsaKeyGen.MrMont
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MillerRabin.Arm.Win
import VerifiedGarbage.Proof.Rsa.Arm.RvCand1

/-! # A candidate on ARMv7: the round on the witness (`mrCall_vp`)

The witness in Montgomery form into Montgomery multiplication's array 5,
the round on it (`round_vp`, as a piece: correct and leaking only the
public parameters), the context, and its result into the header word `sF`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Operand)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa (b2n)
open VG.Proof.MillerRabin.Arm (KeepsLite roundPost roundPub RoundImpl)

/-- The stage after the witness. -/
abbrev AF (P : CP) (k : Nat) (σ : State) : Nat → Nat := upd (AW P k σ) aH1 (wf P σ k).1
abbrev VF (P : CP) (k : Nat) (σ : State) : Nat → Nat := upd (VW P k σ) sU (b2n (wf P σ k).2)
abbrev LF : List Nat := aH1 :: aX :: LB2
abbrev LSF : List Nat := sU :: LSW

/-- The round's result on the witness of iteration `k`. -/
abbrev rv (P : CP) (σ : State) (k : Nat) : Nat := b2n (Proof.MillerRabin.Round.round (cv P σ) (wf P σ k).1)

/-- The witness in Montgomery form from its product with `R² mod c`. -/
theorem x5_val {c R n a : Nat} (hR : Nat.Coprime R c) (hn : n < c) (hc : 0 < c)
    (h : n * R % c = a * (R * R % c) % c) : n = a % c * R % c := by
  refine VG.Proof.RsaKeyGen.mont_inj hR hn (Nat.mod_lt _ hc) ?_
  rw [h, Nat.mul_mod_mod, Nat.mod_mul_mod, Nat.mul_assoc, Nat.mod_mul_mod]

section
variable {P : CP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat}
  {LS : List Nat}

theorem wit_facts {σ : State} (pre : In P σ) (k : Nat) :
    Spec.RsaKeyGen.bitLength (cv P σ - 1) = 64 * P.w ∧ xw P σ k < 2 ^ (64 * P.w) := by
  have lE := pre.L_eq; have w4 := pre.w4
  have sh : VG.Proof.RsaKeyGen.PrimeShape (64 * P.w) (cv P σ) := by
    have := cv_shape (σ := σ) pre; rwa [show 8 * P.L = 64 * P.w by omega] at this
  refine ⟨(VG.Proof.RsaKeyGen.cand_bits (by omega) sh).2.1, ?_⟩
  have := xw_lt P σ k; rwa [show 8 * P.L = 64 * P.w by omega] at this

theorem wf_lt {σ : State} (pre : In P σ) (k : Nat) : (wf P σ k).1 < 2 ^ (64 * P.w) := by
  obtain ⟨hb, hx⟩ := wit_facts pre k
  have w4 := pre.w4
  rw [show wf P σ k = Spec.RsaKeyGen.witness (cv P σ - 1) (xw P σ k) from rfl, witness_arm hb hx]
  dsimp only
  split
  · exact hx
  · exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_le_pow_right (by decide) (by omega))

/-- The working space's context, keeping `X`. -/
theorem VP.ctx {X : State → State → Prop}
    (hX : ∀ σ s t, X σ s → t.mem = s.mem → Rest [.r7, .r8, .r9] s t → X σ t) :
    VP (fun σ s => (E σ ∧ KS P σ (A σ) L (V σ) LS s) ∧ X σ s) (.block ctx)
      (fun σ s => St P E A L V LS σ s ∧ X σ s) := by
  rw [show VG.Impl.RsaKeyGen.Arm.Candidate.ctx = [.ldrSp .r8 aoS] ++ ctxW from rfl]
  refine VP.block_append (G := fun σ s => ((E σ ∧ KS P σ (A σ) L (V σ) LS s) ∧ X σ s) ∧ s.gpr .r8 = P.B) ?_ ?_
  · show VP _ (.block ([(Reg.r8, aoS)].map fun p => Instr.ldrSp p.1 p.2)) _
    refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨⟨e, k⟩, x⟩ => ?_
    · rw [h₁.1.2.sp, h₁.1.2.pre.sp, h₂.1.2.sp, h₂.1.2.pre.sp]
    refine k.ldrSp (o := aoS) (by decide) fun t u => WP.block_nil ⟨⟨⟨e, k.of_rest (u.rest (ws := [.r8])
      (by simp)) u.mem⟩, hX σ s t x u.mem (u.rest (by simp))⟩, by rw [u.gpr, k.pre.aS]⟩
  · refine VP.taint [.r8] ctxW_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ s ⟨⟨⟨e, k⟩, x⟩, r8⟩ => ?_
    · simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2]
    have pre := k.pre
    have hz := pre.hdr_Z
    have hf := pre.fS
    have ea : State.addr (s.gpr .r8 + BitVec.ofNat 32 16) = off (State.addr P.B) 16 := by
      rw [r8]; exact addr_add (by simp only [hdr] at hz; omega)
    have rd : InRegions (s.rd ++ s.wr) (off (State.addr P.B) 16) 4 :=
      ⟨P.rS, List.mem_append_right _ (by rw [k.wr]; exact pre.rS_mem),
        Offset.contains_base _ (by simp only [hdr] at hz; omega) (by omega)⟩
    simp only [ctxW, stride, List.cons_append, List.nil_append]
    refine wp_ldr (by decide) ea rd fun s2 u2 => ?_
    refine wp_dp (op2_imm (by decide)) fun s3 u3 => wp_mov (op2_lsl (by decide)) fun s4 u4 => WP.block_nil ?_
    have m4 : s4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem]
    have r4 : Rest [.r7, .r9] s s4 := (u2.rest (by simp)).trans ((u3.rest (by simp)).trans (u4.rest (by simp)))
    have wl := pre.wle
    have e9 : s4.gpr .r9 = BitVec.ofNat 32 P.W := by
      rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr]
      apply BitVec.eq_of_toNat_eq
      have := k.cnt
      simp only [slot, w32] at this
      rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have e7 : s4.gpr .r7 = BitVec.ofNat 32 (S P.W) := by
      rw [u4.gpr, u3.gpr, dpVal, u2.gpr]
      apply BitVec.eq_of_toNat_eq
      have := k.cnt
      simp only [slot, w32] at this
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_add, this, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      simp only [show (2 : BitVec 32).toNat = 2 from rfl, S]
      omega
    have e8 : s4.gpr .r8 = P.B := by rw [r4.gpr _ (by decide), r8]
    have k4 := k.of_rest r4 m4
    exact ⟨⟨e, k4, k4.ws e7 e8 e9⟩, hX σ s s4 x m4 (r4.mono (by simp))⟩

/-- The round on Montgomery multiplication's array 5, the witness `b σ` in
Montgomery form. -/
theorem round_vp (v : RoundImpl) {b : State → Nat} (h9 : mBase + 9 ∈ L) (h10 : mBase + 10 ∈ L)
    (h27 : mBase + 27 ∈ L) (hL : ∀ j ∈ L, j ∉ rJs) (a9 : ∀ σ, E σ → A σ (mBase + 9) = Rm P σ)
    (a10 : ∀ σ, E σ → A σ (mBase + 10) = cv P σ - Rm P σ) (a27 : ∀ σ, E σ → A σ (mBase + 27) = EX P σ) :
    VP (fun σ s => ((E σ ∧ KS P σ (A σ) L (V σ) LS s) ∧ MS P σ s ∧
        numAt s.mem (State.addr P.M0) P.w 5 < cv P σ ∧
        numAt s.mem (State.addr P.M0) P.w 5 = b σ % cv P σ * 2 ^ (64 * P.w) % cv P σ) ∧
        s.gpr .r0 = P.M0 ∧ s.gpr .r1 = BitVec.ofNat 32 P.lenR)
      (.call v.name v.code)
      (fun σ s => (E σ ∧ KS P σ (A σ) L (V σ) LS s) ∧ MS P σ s ∧
        (s.gpr .r0).toNat = if Proof.MillerRabin.Round.round (cv P σ) (b σ) then 1 else 0) := by
  have nums : ∀ σ s, E σ → KS P σ (A σ) L (V σ) LS s →
      numAt s.mem (State.addr P.M0) P.w 9 = Rm P σ ∧
        numAt s.mem (State.addr P.M0) P.w 10 = cv P σ - Rm P σ := by
    intro σ s e h
    have pre := h.pre
    have lt := Rm_lt pre
    have cl := cv_lt pre
    refine ⟨?_, ?_⟩
    · rw [pre.numAt_eq (by rw [h.arrs _ h9, a9 σ e]; omega), h.arrs _ h9, a9 σ e]
    · rw [pre.numAt_eq (by rw [h.arrs _ h10, a10 σ e]; omega), h.arrs _ h10, a10 σ e]
  have cov : ∀ σ s, KS P σ (A σ) L (V σ) LS s → Covers [⟨State.addr P.M0, 8 * P.lenR⟩] s.wr := by
    intro σ s h
    have pre := h.pre
    refine Covers.of_sub fun r hr => ⟨P.rS, by rw [h.wr]; exact pre.rS_mem, P.oM, ?_, ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact pre.M0_addr
    · simp only [List.mem_singleton] at hr; subst hr; dsimp only; rw [pre.lenR_fit]
  have e0 : ∀ s : State, s.gpr .r0 = P.M0 →
      (s.callEntry.withRegions [] [⟨State.addr P.M0, 8 * P.lenR⟩]).gpr .r0 = P.M0 := fun s r0 => by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), r0]
  have e1 : ∀ s : State, s.gpr .r1 = BitVec.ofNat 32 P.lenR →
      (s.callEntry.withRegions [] [⟨State.addr P.M0, 8 * P.lenR⟩]).gpr .r1 = BitVec.ofNat 32 P.lenR := fun s r1 => by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), r1]
  refine VP.of_ct (fun σ₁ σ₂ => RelCT.call v.verified.1 v.verified.2.1 [] [⟨State.addr P.M0, 8 * P.lenR⟩]
    fun s₁ s₂ ⟨⟨⟨⟨e₁, h₁⟩, m₁, x₁, _⟩, r0₁, r1₁⟩, ⟨⟨⟨e₂, h₂⟩, m₂, x₂, _⟩, r0₂, r1₂⟩⟩ =>
      ⟨round_pre h₁ m₁ r0₁ r1₁ x₁ (nums σ₁ s₁ e₁ h₁).1 (nums σ₁ s₁ e₁ h₁).2 ((h₁.arrs _ h27).trans (a27 σ₁ e₁)),
        round_pre h₂ m₂ r0₂ r1₂ x₂ (nums σ₂ s₂ e₂ h₂).1 (nums σ₂ s₂ e₂ h₂).2 ((h₂.arrs _ h27).trans (a27 σ₂ e₂)), ?_,
        (cov σ₁ s₁ h₁).right, cov σ₁ s₁ h₁, (cov σ₂ s₂ h₂).right, cov σ₂ s₂ h₂⟩)
    fun σ s ⟨⟨⟨e, h⟩, m, x5, xv⟩, r0, r1⟩ => ?_
  · refine ⟨?_, by rw [e0 _ r0₁, e0 _ r0₂], by rw [e1 _ r1₁, e1 _ r1₂], ?_⟩
    · simp only [State.withRegions_sp, State.callEntry_sp]
      rw [h₁.sp, h₁.pre.sp, h₂.sp, h₂.pre.sp]
    · rw [e0 _ r0₁, e0 _ r0₂]
      simp only [State.withRegions_mem, State.callEntry_mem]
      rw [m₁.width, m₂.width]
  have pre := h.pre
  have spw : s.sp = P.sp := h.sp.trans pre.sp
  have lt : P.lenR < 2 ^ 32 := by have := pre.lenR_fit; have := pre.Z_le; omega
  refine FrameStack.WP.callF v.verified.1
    (round_pre h m r0 r1 x5 (nums σ s e h).1 (nums σ s e h).2 ((h.arrs _ h27).trans (a27 σ e)))
    (cov σ s h).right (cov σ s h) (by rw [spw]; have := v.stack; have := pre.spLo; omega)
    fun s' hrd hwr hsp hf _ hpost => ?_
  have fr : Frame [⟨State.addr P.M0, 8 * P.lenR⟩, P.rC] s.mem s'.mem := hf.sub fun r hr => by
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · refine ⟨P.rC, by simp, ?_⟩
      have := FrameStack.belowA_sub (sp := s.sp) (a := FrameStack.armStack v.code) (b := 56) v.stack
        (by rw [spw]; exact pre.spLo)
      rw [spw] at this ⊢; exact this
  change roundPost _ _ at hpost
  dsimp only [roundPost] at hpost
  rw [e0 _ r0, e1 _ r1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt lt] at hpost
  simp only [State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr] at hpost
  simp only [m.width, m.n0] at hpost
  obtain ⟨hr, keeps⟩ := hpost
  obtain ⟨k', m'⟩ := round_after h m hL keeps fr hsp hrd hwr
  exact ⟨⟨e, k'⟩, m', hr (b σ) xv⟩

end

end VG.Proof.RsaKeyGen.Arm.Cand
