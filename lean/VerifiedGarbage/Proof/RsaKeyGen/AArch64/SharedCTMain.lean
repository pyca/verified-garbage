module

import VerifiedGarbage.Proof.RsaKeyGen.AArch64.SharedCTRound
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.SharedMain
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.SharedCTRound
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.SharedMain
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMr
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # Constant time of RSA witness policy with a shared prepared round -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY)
open VG.Proof.RsaKeyGen (shapeOf itersOf passS checksW)

/-- At the head of iteration `j`. -/
def SharedLoopI (q : FPub) (j : Nat) (s : State) : Prop :=
  4 ≤ q.w ∧ q.w ≤ 128 ∧ slot q.w aE + 8 * (q.w + 2) ≤ q.Z ∧ q.rl < 2 ^ 64 ∧ ∃ (c : Nat) (r : List Byte) (s₀ : State) (res : Option (Bool × List Byte))
    (uni : Nat), SharedMrSt q.B q.Z q.w c (checksW q.w) q.rP r s₀ res (j + 1) uni (uOf q j) s ∧ shapeOf res = q.sch.mr ∧
    r.length = q.rl ∧ 1 < c ∧ VG.Proof.RsaKeyGen.PrimeShape (64 * q.w) c ∧ EndW q s₀ ∧
    itersOf (8 * q.w) q.rl q.sch.mr (uOf q j) = Nq q - j

/-- `SharedMrSt` survives changes to registers Montgomery multiplication may
change, and none to memory. -/
theorem SharedMrSt.congr {B : Addr} {Z w c ch : Nat} {rp : Addr} {r : List Byte} {s₀ : State}
    {res : Option (Bool × List Byte)} {i uni used : Nat} {s t : State} {rs : List Reg}
    (h : SharedMrSt B Z w c ch rp r s₀ res i uni used s) (hm : t.mem = s.mem) (k : Keep rs s t)
    (hrs : ∀ r ∈ rs, r ∈ mmRegs) : SharedMrSt B Z w c ch rp r s₀ res i uni used t := by
  obtain ⟨⟨bm, hc⟩, hE, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  refine ⟨⟨bm, hc.of_frm (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k
    (fun h => by have := hrs _ h; simp [mmRegs] at this) (by simp) (by simp) (by simp) (by simp) (by simp)⟩,
    by rw [hm]; exact hE, by rw [hm]; exact h1, by rw [hm]; exact h2, by rw [hm]; exact h3, by rw [hm]; exact h4, by rw [hm]; exact h5,
    h6.congrK (by rw [hm]; exact InScr.refl _ _ _) k, by rw [hm]; exact h7, by rw [hm]; exact h8,
    by rw [hm]; exact h9, h10, h11, h12, h13, h14, by rw [hm]; exact h15, (h16.trans k).mono fun r hr => ?_⟩
  rcases List.mem_append.mp hr with hr | hr
  · exact hr
  · exact hrs r hr

theorem sharedLoopI_ws {q : FPub} {j : Nat} {s : State} (h : SharedLoopI q j s) : Ws s q.B q.Z q.w := by
  obtain ⟨-, -, -, -, c, r, s₀, res, uni, hI, -⟩ := h
  obtain ⟨bm, hc⟩ := hI.ctx
  exact hc.ws

/-- Before the branch on `rand`'s length. -/
def SharedAvI (p : FPub × Nat) (s : State) : Prop :=
  SharedLoopI p.1 p.2 s ∧ isa.eval (.zero .x .x5) s = some (decide (p.1.rl < uOf p.1 p.2 + 8 * p.1.w))

theorem sharedAvI_r0 {p : FPub × Nat} {s : State} (h : SharedAvI p s) (hb : isa.eval (.zero .x .x5) s = some false) :
    R0 ⟨p.1.L, p.1.rP, uOf p.1 p.2, passS (8 * p.1.w) p.1.rl p.1.sch.mr (uOf p.1 p.2)⟩ s := by
  obtain ⟨⟨h4, h128, hEZ, hrl, c, r, s₀, res, uni, hI, hS, hrlen, hc1, hsh, -⟩, hcf⟩ := h
  rw [hcf] at hb
  simp only [Option.some.injEq, decide_eq_false_iff_not, Nat.not_lt] at hb
  obtain ⟨bm, hc⟩ := hI.ctx
  obtain ⟨_, _, hwb⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega_using [h4]) hsh
  have hiu := hI.iu
  have hul := hI.ul
  have hi : 32 * (p.2 + 1) ≤ 8 * p.1.w * (p.2 + 1) := Nat.mul_le_mul_right _ (by omega_using [h4])
  have hun := hI.unii
  refine ⟨h4, h128, hEZ, c, bm, r, p.2 + 1, uni, checksW p.1.w, hc, hI.ex, hI.r2, hc1, hsh, hI.rand, hI.kused, hI.len, hI.src,
    by rw [hrlen]; exact hb, hI.ki, hI.kuni, hI.chk, by omega_using [hrl, hb, hiu, hi], by omega_using [hrl, hb, hiu, hi, hun], checksW_lt _, ?_⟩
  rw [← hS, ← hI.rest, ← hrlen]
  exact (VG.Proof.RsaKeyGen.mr_pass hI.go hwb (by omega_using [h4]) (by rw [hrlen]; exact hb)).symm

/-- Where the loop ends. -/
def SharedLoopEnd (q : FPub) (s : State) : Prop :=
  4 ≤ q.w ∧ q.w ≤ 128 ∧ ∃ (c : Nat) (r : List Byte) (s₀ : State) (res : Option (Bool × List Byte)),
    SharedMrEnd q.B q.Z q.w c r s₀ res s ∧ shapeOf res = q.sch.mr ∧ r.length = q.rl ∧ EndW q s₀

/-- An iteration of the loop. -/
theorem sharedIterB_ct (M : Mont) (R : VG.Proof.MillerRabin.AArch64.Kernel) : RelCT isa (Two fun (p : FPub × Nat) s => p.2 < Nq p.1 ∧ SharedLoopI p.1 p.2 s)
    (seqs [
      .block ([ldh .x3 kRandLen, ldh .x4 kUsed, .sub .x .x3 .x3 .x4, ldh .x4 kLen] ++ geFlag),
      .ite (.zero .x .x5) (.block [movi .x3 0, sth .x3 kStat]) (seqs (mrRoundWith M.mm R.run)),
      .block [ldh .x3 kStat, .subImm .x .x3 .x3 4]]) fun _ _ => True := by
  have pw : ∀ {Φ : FPub × Nat → State → Prop}, (∀ p s, Φ p s → Ws s p.1.B p.1.Z p.1.w) → Pins Φ [.x0] :=
    fun h => pins_ws' (fun p : FPub × Nat => p.1.B) (fun p : FPub × Nat => p.1.Z) (fun p : FPub × Nat => p.1.w) h
  refine RelCT.seq (two_piece (Ψ := SharedAvI) [.x0] (pw fun _ _ h => sharedLoopI_ws h.2) (by taint_decide) ?_)
    (RelCT.seq (R := Two fun (p : FPub × Nat) t => Ws t p.1.B p.1.Z p.1.w)
      (two_ite (fun _ _ _ h₁ h₂ => by rw [h₁.2, h₂.2])
        (two_piece [.x0] (pw fun _ _ h => sharedLoopI_ws h.1.1) (by taint_decide) fun _ _ h => kStat0_ok (sharedLoopI_ws h.1.1))
        (two_post (two_map (fun p : FPub × Nat =>
            (⟨p.1.L, p.1.rP, uOf p.1 p.2, passS (8 * p.1.w) p.1.rl p.1.sch.mr (uOf p.1 p.2)⟩ : RP))
          (fun _ _ h => sharedAvI_r0 h.1 h.2) (sharedRound_ct M R)) ?_))
      (two_taint [.x0] (pw fun _ _ h => h) (by taint_decide)))
  · rintro ⟨q, j⟩ s ⟨hj, h⟩
    have h' := h
    obtain ⟨h4, h128, hEZ, hrl, c, r, s₀, res, uni, hI, hS, hrlen, hc1, hsh, hE, hit⟩ := h'
    obtain ⟨bm, hc⟩ := hI.ctx
    exact WP.mono (iterHead_ok (r := r) hc.ws h128 (by rw [hrlen]; exact hrl) hI.ul hI.len hI.rlen hI.kused)
      fun t ⟨hz, hm, k⟩ => ⟨⟨h4, h128, hEZ, hrl, c, r, s₀, res, uni, hI.congr hm k (by decide), hS, hrlen, hc1,
        hsh, hE, hit⟩, by rw [hz, hrlen]⟩
  · intro p s h
    have hr := sharedAvI_r0 h.1 h.2
    obtain ⟨h4, h128, hEZ, c, bm, r, i, uni, ch, hc, hE, hR2, hc1, hsh, hR, hU, hK, hsrc, hlen, hI, hN, hC, hi, huni,
      hch, -⟩ := hr
    exact WP.mono (sharedRound_ok M R h4 h128 hEZ hc hE hR2 hc1 hsh hR hU hK hsrc hlen hI hN hC hi huni hch)
      fun t ⟨⟨_, hc'⟩, _⟩ => hc'.ws

/-- Miller–Rabin's loop leaks the same in runs that agree on the public data. -/
theorem sharedLoop_ct (M : Mont) (R : VG.Proof.MillerRabin.AArch64.Kernel) : RelCT isa (Two fun (q : FPub) s => 0 < Nq q ∧ SharedLoopI q 0 s)
    (.loop (seqs [
      .block ([ldh .x3 kRandLen, ldh .x4 kUsed, .sub .x .x3 .x3 .x4, ldh .x4 kLen] ++ geFlag),
      .ite (.zero .x .x5) (.block [movi .x3 0, sth .x3 kStat]) (seqs (mrRoundWith M.mm R.run)),
      .block [ldh .x3 kStat, .subImm .x .x3 .x3 4]]) (.zero .x .x3)) (Two SharedLoopEnd) := by
  refine two_loop (Φ := SharedLoopI) Nq (sharedIterB_ct M R) ?_
  rintro q j s hj ⟨h4, h128, hEZ, hrl, c, r, s₀, res, uni, hI, hS, hrlen, hc1, hsh, hE, hit⟩
  obtain ⟨_, _, hwb⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega_using [h4]) hsh
  refine WP.mono (sharedIter_ok M R h4 h128 hEZ hc1 hsh (by omega_using [hrl, hrlen]) (checksW_lt _) s hI) fun t ht => ?_
  rcases ht with ⟨he, hend, hnone, hsome⟩ | ⟨he, uni', hI'⟩
  · have h1 : itersOf (8 * q.w) q.rl q.sch.mr (uOf q j) = 1 := by
      rcases hres : res with _ | ⟨b, rest⟩
      · rw [← hS, hres]; exact VG.Proof.RsaKeyGen.iters_end_none (by omega_using [h4]) (by rw [← hrlen]; exact hnone hres)
      · rw [← hS, hres]
        exact VG.Proof.RsaKeyGen.iters_end_some (by omega_using [h4]) (by rw [← hrlen]; exact hsome b rest hres)
    refine ⟨by rw [he]; exact congrArg some (decide_eq_false (by omega_using [hit, h1])).symm, fun h => absurd h (by omega_using [hit, h1]),
      fun _ => ⟨h4, h128, c, r, s₀, res, hend, hS, hrlen, hE⟩⟩
  · have hu' : uOf q (j + 1) = uOf q j + 8 * q.w := by simp only [uOf]; rw [Nat.mul_add, Nat.mul_one, Nat.add_assoc]
    have hc := VG.Proof.RsaKeyGen.iters_cont (L := 8 * q.w) (r := r) (a := (Spec.Rsa.splitTwos (c - 1)).1)
      (m := (Spec.Rsa.splitTwos (c - 1)).2) hI'.go hwb (by omega_using [h4]) (by omega_using []) hI'.ul
    have hr' : Spec.RsaKeyGen.loop (Spec.RsaKeyGen.mrStep c (checksW q.w) (Spec.Rsa.splitTwos (c - 1)).1
        (Spec.Rsa.splitTwos (c - 1)).2) (j + 1 + 1, uni') (List.drop (uOf q j + 8 * q.w) r) = res := hI'.rest
    rw [show uOf q j + 8 * q.w - 8 * q.w = uOf q j by omega_using [], hr', hS, hrlen] at hc
    refine ⟨by rw [he]; exact congrArg some (decide_eq_true (by omega_using [hit, hc])).symm, fun _ => ?_,
      fun h => absurd h (by omega_using [hit, hc])⟩
    rw [← hu'] at hI'
    exact ⟨h4, h128, hEZ, hrl, c, r, s₀, res, uni', hI', hS, hrlen, hc1, hsh, hE, by rw [hu']; omega_using [hit, hc]⟩

/-- `millerRabin` leaks the same in runs that agree on the public data. -/
theorem sharedMillerRabin_ct (M : Mont) (R : VG.Proof.MillerRabin.AArch64.Kernel) : RelCT isa (Two MrPre) (seqs (millerRabinWith M.mm R.run)) (Two SharedLoopEnd) := by
  unfold millerRabinWith
  refine RelCT.seq (two_piece [.x0] (pins_ws' (fun q : FPub => q.B) (fun q : FPub => q.Z) (fun q : FPub => q.w)
    fun _ _ ⟨_, _, _, _, _, _, _, hc, _⟩ => hc.ws) (by taint_decide) ?_) (sharedLoop_ct M R)
  rintro q s ⟨h4, h128, hEZ, hrl, c, bm, r, hc, hEc, hr2, hc1, hsh, hR, hRL, hrlen, hC, hsrc, hU, hu1, hS, hE⟩
  obtain ⟨_, _, hwb⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega_using [h4]) hsh
  have hN : 1 ≤ Nq q := by
    have := (VG.Proof.RsaKeyGen.iters_cont (L := 8 * q.w) (r := r) (a := (Spec.Rsa.splitTwos (c - 1)).1)
      (m := (Spec.Rsa.splitTwos (c - 1)).2) (ch := checksW q.w) (i := 1) (uni := 0) (Or.inl (by decide)) hwb
      (by omega_using [h4]) (Nat.le_refl _) hu1).2
    have hr' : Spec.RsaKeyGen.loop (Spec.RsaKeyGen.mrStep c (checksW q.w) (Spec.Rsa.splitTwos (c - 1)).1
        (Spec.Rsa.splitTwos (c - 1)).2) (1, 0) (List.drop (8 * q.w) r) = mrRest c (checksW q.w) r 1 0 (8 * q.w) :=
      rfl
    rwa [hr', hS, hrlen] at this
  have hK : word s.mem q.B (8 * kLen) = BitVec.ofNat 64 (8 * q.w) := hE.2.2.1
  exact WP.mono (sharedInit_ok hc hEc hEZ hr2 hR hK hRL hC hsrc hU (Nat.le_refl _) hu1) fun t hI =>
    ⟨hN, h4, h128, hEZ, hrl, c, r, s, _, 0, by simpa [uOf] using hI, hS, hrlen, hc1, hsh, hE, by simp [uOf]⟩

end VG.Proof.RsaKeyGen.AArch64
