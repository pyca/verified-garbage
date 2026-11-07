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
# AES-GCM on RISC-V: `crypt` is constant time

Untrusted: everything here is checked by Lean. As on ARMv7
(`Proof/AesGcm/Arm/CTCrypt.lean`): the invariants fix the context, the
state, `W`, the stack pointer, the number of rounds (in `s3`), the data's
address and length, and the length of the text so far modulo 16; out of
place, also the source's address and the distance to the destination in
`s9` (`CT.taintWith`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64

/-- Before `cryptWith o`. -/
def CrI (o : Bool) (c st w sp : Addr) (R : Nat) (S D : Addr) (n q : Nat) (s : State) : Prop :=
  ∃ V icb P, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧ P % 16 = q ∧ CrIn o V sp R icb P S D n s

/-- Part of the way: `j` bytes done. -/
def CrM (o : Bool) (c st w sp : Addr) (R : Nat) (S D : Addr) (n q j : Nat) (s : State) : Prop :=
  ∃ V icb P m₀, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧ P % 16 = q ∧ CrMid o V sp R icb P S D n m₀ j s

/-- Environments that agree on `s0` to `s3` agree in those registers. -/
theorem pinK {V₁ V₂ : Reg → BitVec 64} {sp : Addr} {s₁ s₂ : State} (e₁ : Env V₁ sp s₁) (e₂ : Env V₂ sp s₂)
    (h28 : V₁ .s3 = V₂ .s3) (h29 : V₁ .s2 = V₂ .s2) (h30 : V₁ .s1 = V₂ .s1) (h31 : V₁ .s0 = V₂ .s0)
    {r : Reg} (hr : r ∈ [Reg.s3, .s2, .s1, .s0]) : s₁.gpr r = s₂.gpr r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [e₁.s3, e₂.s3, h28]
  · rw [e₁.s2, e₂.s2, h29]
  · rw [e₁.s1, e₂.s1, h30]
  · rw [e₁.s0, e₂.s0, h31]

/-- A piece checked by the taint analysis in place and, with `s9` public too,
out of place. -/
theorem CT.taintWith {I : State → Prop} (c : Bool → Prog isa) (o : Bool) (rs : List Reg)
    (hp : ∀ s₁ s₂, I s₁ → I s₂ → s₁.sp = s₂.sp ∧ (∀ r ∈ rs, s₁.gpr r = s₂.gpr r) ∧
      (o = true → s₁.gpr .s9 = s₂.gpr .s9))
    (hf : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs rs) (c false) h).isSome = true)
    (ht : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs (rs ++ ([.s9] : List Reg))) (c true) h).isSome = true) :
    CT I (c o) := by
  cases o
  · obtain ⟨_, hc⟩ := hf
    exact CT.taint rs (fun s₁ s₂ h₁ h₂ => ⟨(hp s₁ s₂ h₁ h₂).1, (hp s₁ s₂ h₁ h₂).2.1⟩) hc
  · obtain ⟨_, hc⟩ := ht
    refine CT.taint _ (fun s₁ s₂ h₁ h₂ => ⟨(hp s₁ s₂ h₁ h₂).1, fun r hr => ?_⟩) hc
    rcases List.mem_append.mp hr with hr | hr
    · exact (hp s₁ s₂ h₁ h₂).2.1 r hr
    · simp only [List.mem_singleton] at hr; subst hr; exact (hp s₁ s₂ h₁ h₂).2.2 rfl

/-- Out of place, `s9` is the distance in both runs. -/
theorem s9_eq {o : Bool} {V₁ V₂ : Reg → BitVec 64} {sp : Addr} {s₁ s₂ : State} {S D : Addr}
    (e₁ : Env V₁ sp s₁) (e₂ : Env V₂ sp s₂) (d₁ : o = true → V₁ .s9 = D - S) (d₂ : o = true → V₂ .s9 = D - S) :
    o = true → s₁.gpr .s9 = s₂.gpr .s9 := fun ho => by
  rw [e₁.fr .s9 (by decide), e₂.fr .s9 (by decide), d₁ ho, d₂ ho]

section
variable {c st w sp : Addr} (L : Lay c st w)
include L

theorem cryptWhole_ct {o : Bool} {R : Nat} {S D : Addr} {n q j : Nat} :
    CT (CrM o c st w sp R S D n q j) (cryptWholeWith o) := by
  obtain ⟨nb, hnb⟩ : ∃ nb, nb = (n - j) / 16 := ⟨_, rfl⟩
  let J₁ : State → Prop := fun s => ∃ V : Reg → BitVec 64, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧
    V .s3 = BitVec.ofNat 64 R ∧ Env V sp s ∧ DataW (V .s2) (V .s1) (V .s0) s D n ∧
    DataOk (V .s1) (V .s0) s S n ∧ Alias o S D n ∧ j ≤ n ∧
    (R = 10 ∨ R = 12 ∨ R = 14) ∧ s.gpr .a3 = D + BitVec.ofNat 64 j ∧
    (o = true → s.gpr .a6 = S + BitVec.ofNat 64 j) ∧ s.gpr .a4 = BitVec.ofNat 64 nb
  refine CT.seq (J := J₁) ?_ (fun s ⟨V, icb, P, m₀, h29, h30, h31, hP, hs⟩ => ?_) ?_
  · refine CT.taintWith (fun o => .block (splitCtrWith o)) o [.s4, .s5]
      (fun s₁ s₂ ⟨_, _, _, _, _, _, _, _, h₁⟩ ⟨_, _, _, _, _, _, _, _, h₂⟩ =>
        ⟨h₁.env.sp.trans h₂.env.sp.symm, fun r hr => ?_, s9_eq h₁.env h₂.env h₁.dst h₂.dst⟩)
      ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.s4, h₂.s4]
    · rw [h₁.s5, h₂.s5]
  · refine WP.mono (splitCtrWith_ok hs.env hs.le hs.data.ok.lt (fun ho => by subst ho; exact hs.alias.eq) hs.dst
      hs.s4 hs.s5) fun s₁ ⟨h6, h6', h7, _, _, hg₁, hk₁⟩ => ?_
    exact ⟨V, h29, h30, h31, hs.s3, hs.env.keep (fun r hr => hg₁ r (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide)) hk₁.sp hk₁.rd hk₁.wr, hs.data.of_eq hk₁.rd hk₁.wr hk₁.sp,
      hs.src.of_eq hk₁.rd hk₁.wr hk₁.sp, hs.alias, hs.le, hs.rounds, h6, h6', by rw [h7, hnb]⟩
  · refine CT.ite (decide (nb = 0)) (fun s ⟨_, _, _, _, _, _, hd, _, _, _, _, _, _, h7⟩ =>
      eval_zero h7 (by have := hd.ok.lt; omega_arith)) (fun _ => CT.skip) fun hb => ?_
    have h0 : nb ≠ 0 := by simpa using hb
    let J₂ : State → Prop := fun s => ∃ V : Reg → BitVec 64, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧
      Env V sp s ∧ DataW (V .s2) (V .s1) (V .s0) s D n ∧ DataOk (V .s1) (V .s0) s S n ∧ Alias o S D n ∧
      j ≤ n ∧ (R = 10 ∨ R = 12 ∨ R = 14) ∧
      s.gpr .a0 = V .s2 ∧ s.gpr .a1 = BitVec.ofNat 64 R ∧ s.gpr .a2 = V .s1 + BitVec.ofNat 64 48 ∧
      s.gpr .a3 = D + BitVec.ofNat 64 j ∧ s.gpr .a4 = BitVec.ofNat 64 nb ∧
      s.gpr .a5 = V .s0 + BitVec.ofNat 64 512 ∧ (o = true → s.gpr .a6 = S + BitVec.ofNat 64 j)
    refine CT.seq (J := J₂) ?_ (fun s ⟨V, h29, h30, h31, h28, he, hd, hsr, ha, hj, hR, h6, h6', h7⟩ => ?_) ?_
    · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s3, .s2, .s1, .s0])
          (.block (ctrArgs 48)) h).isSome = true := ⟨_, by taint_decide⟩
      exact CT.taint _ (fun s₁ s₂ ⟨_, a29, a30, a31, a28, e₁, _⟩ ⟨_, b29, b30, b31, b28, e₂, _⟩ =>
        ⟨e₁.sp.trans e₂.sp.symm, fun r hr => pinK e₁ e₂ (a28.trans b28.symm) (a29.trans b29.symm)
          (a30.trans b30.symm) (a31.trans b31.symm) hr⟩) hc
    · refine WP.mono (ctrArgs_ok he h28) fun s₂ ⟨a3, a4, a5, a8, hg₂, hk₂⟩ => ?_
      exact ⟨V, h29, h30, h31, he.keep (fun r hr => hg₂ r (by revert r; decide) (by revert r; decide)
        (by revert r; decide) (by revert r; decide)) hk₂.sp hk₂.rd hk₂.wr, hd.of_eq hk₂.rd hk₂.wr hk₂.sp,
        hsr.of_eq hk₂.rd hk₂.wr hk₂.sp, ha, hj, hR,
        a3, a4, a5, by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide), h6],
        by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide), h7], a8,
        fun ho => by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide), h6' ho]⟩
    · cases o
      · refine CT.ctr fun s₁ s₂ ⟨V₁, a29, a30, a31, he₁, hd₁, _, _, hj₁, hR, a3, a4, a5, a6, a7, a8, _⟩
          ⟨V₂, b29, b30, b31, he₂, hd₂, _, _, _, _, b3, b4, b5, b6, b7, b8, _⟩ => ?_
        have hn₁ := hd₁.ok.lt
        have g₁ := ctrWhole_mk (L.v a29 a30 a31) he₁ a3 a4 a5 a6 a7 a8 hR (by omega_arith)
          (hd₁.sub (j := j) (k := 16 * nb) (by omega_arith) (by omega_arith))
        have g₂ := ctrWhole_mk (L.v b29 b30 b31) he₂ b3 b4 b5 b6 b7 b8 hR (by omega_arith)
          (hd₂.sub (j := j) (k := 16 * nb) (by omega_arith) (by omega_arith))
        rw [a29, a30, a31] at g₁
        rw [b29, b30, b31] at g₂
        exact ⟨_, _, _, _, _, _, g₁, g₂, he₁.sp.trans he₂.sp.symm⟩
      · refine ctrTo_rel fun s₁ s₂ ⟨⟨V₁, a29, a30, a31, he₁, hd₁, hs₁, ha₁, hj₁, hR, a3, a4, a5, a6, a7, a8, a9⟩,
          ⟨V₂, b29, b30, b31, he₂, hd₂, hs₂, ha₂, _, _, b3, b4, b5, b6, b7, b8, b9⟩⟩ => ?_
        have hn₁ := hd₁.ok.lt
        have g₁ := ctrWholeTo_mk (L.v a29 a30 a31) he₁ a3 a4 a5 a6 a7 a8 (a9 rfl) hR (by omega_arith)
          (hd₁.sub (j := j) (k := 16 * nb) (by omega_arith) (by omega_arith))
          (hs₁.sub (j := j) (k := 16 * nb) (by omega_arith) (by omega_arith)) (ha₁.drop (by omega_arith))
        have g₂ := ctrWholeTo_mk (L.v b29 b30 b31) he₂ b3 b4 b5 b6 b7 b8 (b9 rfl) hR (by omega_arith)
          (hd₂.sub (j := j) (k := 16 * nb) (by omega_arith) (by omega_arith))
          (hs₂.sub (j := j) (k := 16 * nb) (by omega_arith) (by omega_arith)) (ha₂.drop (by omega_arith))
        rw [a29, a30, a31] at g₁
        rw [b29, b30, b31] at g₂
        exact ⟨_, _, _, _, _, _, _, g₁, g₂, he₁.sp.trans he₂.sp.symm⟩

theorem cryptTail_ct {o : Bool} {R : Nat} {S D : Addr} {n q j : Nat} :
    CT (CrM o c st w sp R S D n q j) (cryptTailWith o) := by
  refine CT.ite (decide (n - j = 0)) (fun s ⟨_, _, _, _, _, _, _, _, hs⟩ =>
    eval_zero hs.s5 (by have := hs.data.ok.lt; omega_arith)) (fun _ => CT.skip) fun _ => ?_
  let J₁ : State → Prop := fun s => ∃ V : Reg → BitVec 64, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧
    Env V sp s ∧ (R = 10 ∨ R = 12 ∨ R = 14) ∧ s.gpr .a0 = V .s2 ∧ s.gpr .a1 = BitVec.ofNat 64 R ∧
    s.gpr .a2 = V .s1 + BitVec.ofNat 64 48 ∧ s.gpr .a3 = V .s1 + BitVec.ofNat 64 64 ∧
    s.gpr .a4 = BitVec.ofNat 64 1 ∧ s.gpr .a5 = V .s0 + BitVec.ofNat 64 512
  let J₂ : State → Prop := fun s => ∃ V icb P m₀ s₀, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧
    TailKs o V sp R icb P S D n m₀ j s₀ s
  refine CT.seq (J := J₂) (CT.seq (J := J₁) ?_ (fun s ⟨V, icb, P, m₀, h29, h30, h31, hP, hs⟩ => ?_) ?_)
    (fun s ⟨V, icb, P, m₀, h29, h30, h31, hP, hs⟩ =>
      WP.mono (tailKs_ok (L.v h29 h30 h31) hs (hs.ciph (L.v h29 h30 h31))) fun s' h =>
        ⟨V, icb, P, m₀, s, h29, h30, h31, h⟩) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s3, .s2, .s1, .s0])
        (.block tailArgs) h).isSome = true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, a29, a30, a31, _, h₁⟩ ⟨_, _, _, _, b29, b30, b31, _, h₂⟩ =>
      ⟨h₁.env.sp.trans h₂.env.sp.symm, fun r hr => pinK h₁.env h₂.env (h₁.s3.trans h₂.s3.symm)
        (a29.trans b29.symm) (a30.trans b30.symm) (a31.trans b31.symm) hr⟩) hc
  · refine WP.mono (tailArgs_ok (L.v h29 h30 h31) hs.env hs.s3) fun s₂ ⟨_, a3, a4, a5, a6, a7, a8, hg₂, hk₂⟩ => ?_
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
  · refine CT.taintWith (fun o => .seq (.block ([.addi .a0 .s1 64, mov .a1 .s4] ++ toDst o .a4 ++ [mov .a2 .s5]))
      (xorLoopWith o)) o [.s4, .s5, .s1]
      (fun s₁ s₂ ⟨_, _, _, _, _, _, a30, _, h₁⟩ ⟨_, _, _, _, _, _, b30, _, h₂⟩ =>
        ⟨h₁.env.sp.trans h₂.env.sp.symm, fun r hr => ?_, s9_eq h₁.env h₂.env h₁.mid.dst h₂.mid.dst⟩)
      ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.s4, h₂.s4]
    · rw [h₁.s5, h₂.s5]
    · rw [h₁.env.s1, h₂.env.s1, a30, b30]

theorem crypt_ct {o : Bool} {R : Nat} {S D : Addr} {n q : Nat} :
    CT (CrI o c st w sp R S D n q) (cryptWith o) := by
  refine CT.ite (decide (n = 0)) (fun s ⟨_, _, _, _, _, _, _, hs⟩ => eval_zero hs.s5 hs.data.ok.lt)
    (fun _ => CT.skip) fun hb => ?_
  have h0 : n ≠ 0 := by simpa using hb
  let j₁ := if q = 0 then 0 else min (16 - q) n
  refine CT.seq (J := CrM o c st w sp R S D n q j₁) ?_
    (fun s ⟨V, icb, P, h29, h30, h31, hP, hs⟩ => WP.mono (cryptFill_ok hs h0)
      fun s' ⟨j, hj, hm⟩ => ⟨V, icb, P, s.mem, h29, h30, h31, hP, by subst hj; rw [hP] at hm; exact hm⟩) ?_
  · refine CT.taintWith cryptFillWith o [.s4, .s5, .s6, .s1]
      (fun s₁ s₂ ⟨_, _, _, _, a30, _, hP₁, h₁⟩ ⟨_, _, _, _, b30, _, hP₂, h₂⟩ =>
        ⟨h₁.env.sp.trans h₂.env.sp.symm, fun r hr => ?_, s9_eq h₁.env h₂.env h₁.dst h₂.dst⟩)
      ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₁.s4, h₂.s4]
    · rw [h₁.s5, h₂.s5]
    · rw [h₁.s6, h₂.s6, hP₁, hP₂]
    · rw [h₁.env.s1, h₂.env.s1, a30, b30]
  refine CT.seq (J := CrM o c st w sp R S D n q (j₁ + 16 * ((n - j₁) / 16))) (cryptWhole_ct L)
    (fun s ⟨V, icb, P, m₀, h29, h30, h31, hP, hs⟩ =>
      WP.mono (cryptWhole_ok (L.v h29 h30 h31) hs (hs.ciph (L.v h29 h30 h31))) fun s' ⟨j, hj, hm, _⟩ =>
        ⟨V, icb, P, m₀, h29, h30, h31, hP, by subst hj; exact hm⟩) (cryptTail_ct L)

end

end VG.Proof.AesGcm.RISCV64
