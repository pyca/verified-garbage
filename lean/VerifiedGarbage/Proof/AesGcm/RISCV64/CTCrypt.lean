module

public import VerifiedGarbage.Proof.AesGcm.RISCV64.CTBase
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Crypt
import VerifiedGarbage.Proof.AesGcm.RISCV64.Absorb
import VerifiedGarbage.Proof.AesGcm.RISCV64.CryptOk
import VerifiedGarbage.Proof.Framework.RISCV64.Run
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Crypt
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Absorb
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CryptOk
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Run
meta import VerifiedGarbage.Impl.AesGcm.RISCV64
public import VerifiedGarbage.Impl.AesGcm.RISCV64

/-!
# AES-GCM on RISCV64: `crypt` is constant time

Untrusted: everything here is checked by Lean. As on ARMv7
(`Proof/AesGcm/Arm/CTCrypt.lean`): the invariants fix the context, the
state, `W`, the stack pointer, the number of rounds (in `r28`), the data's
address and length, and the length of the text so far modulo 16.
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64

/-- Before `crypt`. -/
def CrI (c st w sp : Addr) (R : Nat) (D : Addr) (n q : Nat) (s : State) : Prop :=
  ∃ V icb P, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧ P % 16 = q ∧ CrIn V sp R icb P D n s

/-- Part of the way: `j` bytes done. -/
def CrM (c st w sp : Addr) (R : Nat) (D : Addr) (n q j : Nat) (s : State) : Prop :=
  ∃ V icb P m₀, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧ P % 16 = q ∧ CrMid V sp R icb P D n m₀ j s

/-- Environments that agree on `r28` to `r31` agree in those registers. -/
theorem pinK {V₁ V₂ : Reg → BitVec 64} {sp : Addr} {s₁ s₂ : State} (e₁ : Env V₁ sp s₁) (e₂ : Env V₂ sp s₂)
    (h28 : V₁ .s3 = V₂ .s3) (h29 : V₁ .s2 = V₂ .s2) (h30 : V₁ .s1 = V₂ .s1) (h31 : V₁ .s0 = V₂ .s0)
    {r : Reg} (hr : r ∈ [Reg.s3, .s2, .s1, .s0]) : s₁.gpr r = s₂.gpr r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [e₁.s3, e₂.s3, h28]
  · rw [e₁.s2, e₂.s2, h29]
  · rw [e₁.s1, e₂.s1, h30]
  · rw [e₁.s0, e₂.s0, h31]

section
variable {c st w sp : Addr} (L : Lay c st w)
include L

theorem cryptWhole_ct {R : Nat} {D : Addr} {n q j : Nat} :
    CT (CrM c st w sp R D n q j) cryptWhole := by
  obtain ⟨nb, hnb⟩ : ∃ nb, nb = (n - j) / 16 := ⟨_, rfl⟩
  let J₁ : State → Prop := fun s => ∃ V : Reg → BitVec 64, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧
    V .s3 = BitVec.ofNat 64 R ∧ Env V sp s ∧ DataW (V .s2) (V .s1) (V .s0) s D n ∧ j ≤ n ∧
    (R = 10 ∨ R = 12 ∨ R = 14) ∧ s.gpr .a3 = D + BitVec.ofNat 64 j ∧ s.gpr .a4 = BitVec.ofNat 64 nb
  refine CT.seq (J := J₁) ?_ (fun s ⟨V, icb, P, m₀, h29, h30, h31, hP, hs⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s4, .s5]) (.block splitCtr)
        h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, _, _, _, h₁⟩ ⟨_, _, _, _, _, _, _, _, h₂⟩ =>
      ⟨h₁.env.sp.trans h₂.env.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.s4, h₂.s4]
    · rw [h₁.s5, h₂.s5]
  · refine WP.mono (splitCtr_ok hs.le hs.data.ok.lt hs.s4 hs.s5) fun s₁ ⟨h6, h7, _, _, hg₁, hk₁⟩ => ?_
    exact ⟨V, h29, h30, h31, hs.s3, hs.env.keep (fun r hr => hg₁ r (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
      (by revert r; decide)) hk₁.sp hk₁.rd hk₁.wr, hs.data.of_eq hk₁.rd hk₁.wr, hs.le, hs.rounds, h6,
      by rw [h7, hnb]⟩
  · refine CT.ite (decide (nb = 0)) (fun s ⟨_, _, _, _, _, _, hd, _, _, _, h7⟩ =>
      eval_zero h7 (by have := hd.ok.lt; omega_arith)) (fun _ => CT.skip) fun hb => ?_
    have h0 : nb ≠ 0 := by simpa using hb
    let J₂ : State → Prop := fun s => ∃ V : Reg → BitVec 64, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧
      Env V sp s ∧ DataW (V .s2) (V .s1) (V .s0) s D n ∧ j ≤ n ∧ (R = 10 ∨ R = 12 ∨ R = 14) ∧
      s.gpr .a0 = V .s2 ∧ s.gpr .a1 = BitVec.ofNat 64 R ∧ s.gpr .a2 = V .s1 + BitVec.ofNat 64 48 ∧
      s.gpr .a3 = D + BitVec.ofNat 64 j ∧ s.gpr .a4 = BitVec.ofNat 64 nb ∧
      s.gpr .a5 = V .s0 + BitVec.ofNat 64 512
    refine CT.seq (J := J₂) ?_ (fun s ⟨V, h29, h30, h31, h28, he, hd, hj, hR, h6, h7⟩ => ?_) ?_
    · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s3, .s2, .s1, .s0])
          (.block (ctrArgs 48)) h).isSome = true := ⟨_, by taint_decide⟩
      exact CT.taint _ (fun s₁ s₂ ⟨_, a29, a30, a31, a28, e₁, _⟩ ⟨_, b29, b30, b31, b28, e₂, _⟩ =>
        ⟨e₁.sp.trans e₂.sp.symm, fun r hr => pinK e₁ e₂ (a28.trans b28.symm) (a29.trans b29.symm)
          (a30.trans b30.symm) (a31.trans b31.symm) hr⟩) hc
    · refine WP.mono (ctrArgs_ok he h28) fun s₂ ⟨a3, a4, a5, a8, hg₂, hk₂⟩ => ?_
      exact ⟨V, h29, h30, h31, he.keep (fun r hr => hg₂ r (by revert r; decide) (by revert r; decide)
        (by revert r; decide) (by revert r; decide)) hk₂.sp hk₂.rd hk₂.wr, hd.of_eq hk₂.rd hk₂.wr, hj, hR,
        a3, a4, a5, by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide), h6],
        by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide), h7], a8⟩
    · refine CT.ctr fun s₁ s₂ ⟨V₁, a29, a30, a31, he₁, hd₁, hj₁, hR, a3, a4, a5, a6, a7, a8⟩
        ⟨V₂, b29, b30, b31, he₂, hd₂, _, _, b3, b4, b5, b6, b7, b8⟩ => ?_
      have hn₁ := hd₁.ok.lt
      have g₁ := ctrWhole_mk (L.v a29 a30 a31) he₁ a3 a4 a5 a6 a7 a8 hR (by omega_arith)
        (hd₁.sub (j := j) (k := 16 * nb) (by omega_arith) (by omega_arith))
      have g₂ := ctrWhole_mk (L.v b29 b30 b31) he₂ b3 b4 b5 b6 b7 b8 hR (by omega_arith)
        (hd₂.sub (j := j) (k := 16 * nb) (by omega_arith) (by omega_arith))
      rw [a29, a30, a31] at g₁
      rw [b29, b30, b31] at g₂
      exact ⟨_, _, _, _, _, _, g₁, g₂, he₁.sp.trans he₂.sp.symm⟩

theorem cryptTail_ct {R : Nat} {D : Addr} {n q j : Nat} :
    CT (CrM c st w sp R D n q j) cryptTail := by
  refine CT.ite (decide (n - j = 0)) (fun s ⟨_, _, _, _, _, _, _, _, hs⟩ =>
    eval_zero hs.s5 (by have := hs.data.ok.lt; omega_arith)) (fun _ => CT.skip) fun _ => ?_
  let J₁ : State → Prop := fun s => ∃ V : Reg → BitVec 64, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧
    Env V sp s ∧ (R = 10 ∨ R = 12 ∨ R = 14) ∧ s.gpr .a0 = V .s2 ∧ s.gpr .a1 = BitVec.ofNat 64 R ∧
    s.gpr .a2 = V .s1 + BitVec.ofNat 64 48 ∧ s.gpr .a3 = V .s1 + BitVec.ofNat 64 64 ∧
    s.gpr .a4 = BitVec.ofNat 64 1 ∧ s.gpr .a5 = V .s0 + BitVec.ofNat 64 512
  let J₂ : State → Prop := fun s => ∃ V icb P m₀ s₀, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧
    TailKs V sp R icb P D n m₀ j s₀ s
  refine CT.seq (J := J₂) (CT.seq (J := J₁) ?_ (fun s ⟨V, icb, P, m₀, h29, h30, h31, hP, hs⟩ => ?_) ?_)
    (fun s ⟨V, icb, P, m₀, h29, h30, h31, hP, hs⟩ =>
      WP.mono (tailKs_ok (L.v h29 h30 h31) hs (hs.ciph (L.v h29 h30 h31))) fun s' h =>
        ⟨V, icb, P, m₀, s, h29, h30, h31, h⟩) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s3, .s2, .s1, .s0])
        (.block tailArgs) h).isSome = true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, a29, a30, a31, _, h₁⟩ ⟨_, _, _, _, b29, b30, b31, _, h₂⟩ =>
      ⟨h₁.env.sp.trans h₂.env.sp.symm, fun r hr => pinK h₁.env h₂.env (h₁.s3.trans h₂.s3.symm)
        (a29.trans b29.symm) (a30.trans b30.symm) (a31.trans b31.symm) hr⟩) hc
  · refine WP.mono (tailArgs_ok hs.env hs.s3) fun s₂ ⟨_, a3, a4, a5, a6, a7, a8, hg₂, hk₂⟩ => ?_
    exact ⟨V, h29, h30, h31, hs.env.keep (fun r hr => hg₂ r (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
      (by revert r; decide)) hk₂.sp hk₂.rd hk₂.wr, hs.rounds, a3, a4, a5, a6, a7, a8⟩
  · exact CT.ctr fun s₁ s₂ ⟨V₁, a29, a30, a31, he₁, hR, a3, a4, a5, a6, a7, a8⟩
      ⟨V₂, b29, b30, b31, he₂, _, b3, b4, b5, b6, b7, b8⟩ => by
      have g₁ := ctrTail_mk (L.v a29 a30 a31) he₁ a3 a4 a5 a6 a7 a8 hR
      have g₂ := ctrTail_mk (L.v b29 b30 b31) he₂ b3 b4 b5 b6 b7 b8 hR
      rw [a29, a30, a31] at g₁
      rw [b29, b30, b31] at g₂
      exact ⟨_, _, _, _, _, _, g₁, g₂, he₁.sp.trans he₂.sp.symm⟩
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s4, .s5, .s1])
        (.seq (.block [.addi .a0 .s1 64, mov .a1 .s4, mov .a2 .s5]) xorLoop) h).isSome = true :=
      ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, _, a30, _, h₁⟩ ⟨_, _, _, _, _, _, b30, _, h₂⟩ =>
      ⟨h₁.env.sp.trans h₂.env.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.s4, h₂.s4]
    · rw [h₁.s5, h₂.s5]
    · rw [h₁.env.s1, h₂.env.s1, a30, b30]

theorem crypt_ct {R : Nat} {D : Addr} {n q : Nat} :
    CT (CrI c st w sp R D n q) crypt := by
  refine CT.ite (decide (n = 0)) (fun s ⟨_, _, _, _, _, _, _, hs⟩ => eval_zero hs.s5 hs.data.ok.lt)
    (fun _ => CT.skip) fun hb => ?_
  have h0 : n ≠ 0 := by simpa using hb
  let j₁ := if q = 0 then 0 else min (16 - q) n
  refine CT.seq (J := CrM c st w sp R D n q j₁) ?_
    (fun s ⟨V, icb, P, h29, h30, h31, hP, hs⟩ => WP.mono (cryptFill_ok hs h0) fun s' ⟨j, hj, hm⟩ =>
      ⟨V, icb, P, s.mem, h29, h30, h31, hP, by subst hj; rw [hP] at hm; exact hm⟩) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s4, .s5, .s6, .s1]) cryptFill
        h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, a30, _, hP₁, h₁⟩ ⟨_, _, _, _, b30, _, hP₂, h₂⟩ =>
      ⟨h₁.env.sp.trans h₂.env.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₁.s4, h₂.s4]
    · rw [h₁.s5, h₂.s5]
    · rw [h₁.s6, h₂.s6, hP₁, hP₂]
    · rw [h₁.env.s1, h₂.env.s1, a30, b30]
  refine CT.seq (J := CrM c st w sp R D n q (j₁ + 16 * ((n - j₁) / 16))) (cryptWhole_ct L)
    (fun s ⟨V, icb, P, m₀, h29, h30, h31, hP, hs⟩ =>
      WP.mono (cryptWhole_ok (L.v h29 h30 h31) hs (hs.ciph (L.v h29 h30 h31))) fun s' ⟨j, hj, hm, _⟩ =>
        ⟨V, icb, P, m₀, h29, h30, h31, hP, by subst hj; exact hm⟩) (cryptTail_ct L)

end

end VG.Proof.AesGcm.RISCV64
