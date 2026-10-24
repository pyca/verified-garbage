module

public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Crypt
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTBase
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Crypt
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTBase
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Run
public import VerifiedGarbage.Impl.Sm4Gcm.PPC64LE
meta import VerifiedGarbage.Impl.Sm4Gcm.PPC64LE
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Ghash1
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Ghash1

/-!
# SM4-GCM on PPC64LE: `crypt` is constant time

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/PPC64LE/CTCrypt.lean`): the invariants fix the context, the
state, `W`, the stack pointer, the data's address and length, and the length
of the text so far modulo 16; SM4's counter mode is constant time by its own
proof (`CT.ctr`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.PPC64LE

open VG VG.PPC64LE VG.Impl.Sm4Gcm.PPC64LE
open VG.Impl.AesGcm.PPC64LE (mov cryptFill splitWhole xorLoop)
open VG.Proof.AesGcm.PPC64LE (CT Env Lay DataW eval_zero split_ok)

/-- Before `crypt`. -/
def CrI (c st w x sp : Addr) (D : Addr) (n q : Nat) (s : State) : Prop :=
  ∃ V icb P, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧ V .r28 = x ∧ P % 16 = q ∧ CrIn V sp icb P D n s

/-- Part of the way: `j` bytes done. -/
def CrM (c st w x sp : Addr) (D : Addr) (n q j : Nat) (s : State) : Prop :=
  ∃ V icb P m₀, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧ V .r28 = x ∧ P % 16 = q ∧ CrMid V sp icb P D n m₀ j s

/-- Environments that agree on `r28` to `r31` agree in those registers. -/
theorem pinK {V₁ V₂ : Reg → BitVec 64} {sp : Addr} {s₁ s₂ : State} (e₁ : Env V₁ sp s₁) (e₂ : Env V₂ sp s₂)
    (h29 : V₁ .r29 = V₂ .r29) (h30 : V₁ .r30 = V₂ .r30) (h31 : V₁ .r31 = V₂ .r31) (h28 : V₁ .r28 = V₂ .r28)
    {r : Reg} (hr : r ∈ [Reg.r28, .r29, .r30, .r31]) : s₁.gpr r = s₂.gpr r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [e₁.fr _ (by decide), e₂.fr _ (by decide), h28]
  · rw [e₁.r29, e₂.r29, h29]
  · rw [e₁.r30, e₂.r30, h30]
  · rw [e₁.r31, e₂.r31, h31]

section
variable {c st w x sp : Addr} (L : Lay c st w) (X : XOk c st w x)
include L X

theorem cryptWhole_ct {D : Addr} {n q j : Nat} :
    CT (CrM c st w x sp D n q j) cryptWhole := by
  obtain ⟨nb, hnb⟩ : ∃ nb, nb = (n - j) / 16 := ⟨_, rfl⟩
  let J₁ : State → Prop := fun s => ∃ V : Reg → BitVec 64, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧ V .r28 = x ∧
    Env V sp s ∧ DataW (V .r29) (V .r30) (V .r31) s D n ∧ j ≤ n ∧ Covers [xR (V .r28)] s.wr ∧
    (⟨D, n⟩ : Region).Disjoint (xR (V .r28)) ∧
    s.gpr .r5 = D + BitVec.ofNat 64 j ∧ s.gpr .r6 = BitVec.ofNat 64 nb
  refine CT.seq (J := J₁) ?_ (fun s ⟨V, icb, P, m₀, h29, h30, h31, h28, hP, hs⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r24, .r25]) (.block splitWhole)
        h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, _, _, _, _, h₁⟩ ⟨_, _, _, _, _, _, _, _, _, h₂⟩ =>
      ⟨h₁.env.sp.trans h₂.env.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.r24, h₂.r24]
    · rw [h₁.r25, h₂.r25]
  · refine WP.mono (split_ok hs.le hs.data.ok.lt hs.r24 hs.r25) fun s₁ ⟨h5, h6, _, _, hg₁, hk₁⟩ => ?_
    exact ⟨V, h29, h30, h31, h28, hs.env.keep (fun r hr => hg₁ r (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
      (by revert r; decide)) hk₁.sp hk₁.rd hk₁.wr, hs.data.of_eq hk₁.rd hk₁.wr, hs.le,
      by rw [hk₁.wr]; exact hs.xw, hs.dx, h5, by rw [h6, hnb]⟩
  · refine CT.ite (decide (nb = 0)) (fun s ⟨_, _, _, _, _, _, hd, _, _, _, _, h6⟩ =>
      eval_zero h6 (by have := hd.ok.lt; omega)) (fun _ => CT.skip) fun hb => ?_
    have h0 : nb ≠ 0 := by simpa using hb
    let J₂ : State → Prop := fun s => ∃ V : Reg → BitVec 64, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧ V .r28 = x ∧
      Env V sp s ∧ DataW (V .r29) (V .r30) (V .r31) s D n ∧ j ≤ n ∧ Covers [xR (V .r28)] s.wr ∧
      (⟨D, n⟩ : Region).Disjoint (xR (V .r28)) ∧
      s.gpr .r3 = V .r29 ∧ s.gpr .r4 = V .r30 + BitVec.ofNat 64 48 ∧
      s.gpr .r5 = D + BitVec.ofNat 64 j ∧ s.gpr .r6 = BitVec.ofNat 64 nb ∧
      s.gpr .r7 = V .r28
    refine CT.seq (J := J₂) ?_ (fun s ⟨V, h29, h30, h31, h28, he, hd, hj, hxw, hdx, h5, h6⟩ => ?_) ?_
    · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r28, .r29, .r30, .r31])
          (.block (ctrArgs 48)) h).isSome = true := ⟨_, by taint_decide⟩
      exact CT.taint _ (fun s₁ s₂ ⟨_, a29, a30, a31, a28, e₁, _⟩ ⟨_, b29, b30, b31, b28, e₂, _⟩ =>
        ⟨e₁.sp.trans e₂.sp.symm, fun r hr => pinK e₁ e₂ (a29.trans b29.symm)
          (a30.trans b30.symm) (a31.trans b31.symm) (a28.trans b28.symm) hr⟩) hc
    · refine WP.mono (ctrArgs_ok he) fun s₂ ⟨a3, a4, a7, hg₂, hk₂⟩ => ?_
      exact ⟨V, h29, h30, h31, h28, he.keep (fun r hr => hg₂ r (by revert r; decide) (by revert r; decide)
        (by revert r; decide)) hk₂.sp hk₂.rd hk₂.wr, hd.of_eq hk₂.rd hk₂.wr, hj, by rw [hk₂.wr]; exact hxw, hdx,
        a3, a4, by rw [hg₂ _ (by decide) (by decide) (by decide), h5],
        by rw [hg₂ _ (by decide) (by decide) (by decide), h6], a7⟩
    · refine CT.ctr fun s₁ s₂ ⟨V₁, a29, a30, a31, a28, he₁, hd₁, hj₁, ax, adx, a3, a4, a5, a6, a7⟩
        ⟨V₂, b29, b30, b31, b28, he₂, hd₂, _, bx, bdx, b3, b4, b5, b6, b7⟩ => ?_
      have hn₁ := hd₁.ok.lt
      have g₁ := ctrWhole_mk (L.v a29 a30 a31) (by rw [a29, a30, a31, a28]; exact X) he₁ a3 a4 a5 a6 a7 (by omega)
        (hd₁.sub (j := j) (k := 16 * nb) (by omega) (by omega)) ax (adx.sub_left (VG.Offset.sub_base _ (by omega)))
      have g₂ := ctrWhole_mk (L.v b29 b30 b31) (by rw [b29, b30, b31, b28]; exact X) he₂ b3 b4 b5 b6 b7 (by omega)
        (hd₂.sub (j := j) (k := 16 * nb) (by omega) (by omega)) bx (bdx.sub_left (VG.Offset.sub_base _ (by omega)))
      rw [a29, a30, a28] at g₁
      rw [b29, b30, b28] at g₂
      exact ⟨_, _, _, _, _, g₁, g₂, he₁.sp.trans he₂.sp.symm⟩

theorem cryptTail_ct {D : Addr} {n q j : Nat} :
    CT (CrM c st w x sp D n q j) cryptTail := by
  refine CT.ite (decide (n - j = 0)) (fun s ⟨_, _, _, _, _, _, _, _, _, hs⟩ =>
    eval_zero hs.r25 (by have := hs.data.ok.lt; omega)) (fun _ => CT.skip) fun _ => ?_
  let J₁ : State → Prop := fun s => ∃ V : Reg → BitVec 64, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧ V .r28 = x ∧
    Env V sp s ∧ Covers [xR (V .r28)] s.wr ∧ s.gpr .r3 = V .r29 ∧
    s.gpr .r4 = V .r30 + BitVec.ofNat 64 48 ∧ s.gpr .r5 = V .r30 + BitVec.ofNat 64 64 ∧
    s.gpr .r6 = BitVec.ofNat 64 1 ∧ s.gpr .r7 = V .r28
  let J₂ : State → Prop := fun s => ∃ V icb P m₀ s₀, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧ V .r28 = x ∧
    TailKs V sp icb P D n m₀ j s₀ s
  refine CT.seq (J := J₂) (CT.seq (J := J₁) ?_ (fun s ⟨V, icb, P, m₀, h29, h30, h31, h28, hP, hs⟩ => ?_) ?_)
    (fun s ⟨V, icb, P, m₀, h29, h30, h31, h28, hP, hs⟩ =>
      WP.mono (tailKs_ok (L.v h29 h30 h31) (by rw [h29, h30, h31, h28]; exact X) hs) fun s' h =>
        ⟨V, icb, P, m₀, s, h29, h30, h31, h28, h⟩) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r28, .r29, .r30, .r31])
        (.block tailArgs) h).isSome = true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, a29, a30, a31, a28, _, h₁⟩ ⟨_, _, _, _, b29, b30, b31, b28, _, h₂⟩ =>
      ⟨h₁.env.sp.trans h₂.env.sp.symm, fun r hr => pinK h₁.env h₂.env
        (a29.trans b29.symm) (a30.trans b30.symm) (a31.trans b31.symm) (a28.trans b28.symm) hr⟩) hc
  · refine WP.mono (tailArgs_ok hs.env) fun s₂ ⟨_, a3, a4, a5, a6, a7, hg₂, hk₂⟩ => ?_
    exact ⟨V, h29, h30, h31, h28, hs.env.keep (fun r hr => hg₂ r (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)) hk₂.sp hk₂.rd
      hk₂.wr, by rw [hk₂.wr]; exact hs.xw, a3, a4, a5, a6, a7⟩
  · exact CT.ctr fun s₁ s₂ ⟨V₁, a29, a30, a31, a28, he₁, ax, a3, a4, a5, a6, a7⟩
      ⟨V₂, b29, b30, b31, b28, he₂, bx, b3, b4, b5, b6, b7⟩ => by
      have g₁ := ctrTail_mk (L.v a29 a30 a31) (by rw [a29, a30, a31, a28]; exact X) he₁ a3 a4 a5 a6 a7 ax
      have g₂ := ctrTail_mk (L.v b29 b30 b31) (by rw [b29, b30, b31, b28]; exact X) he₂ b3 b4 b5 b6 b7 bx
      rw [a29, a30, a28] at g₁
      rw [b29, b30, b28] at g₂
      exact ⟨_, _, _, _, _, g₁, g₂, he₁.sp.trans he₂.sp.symm⟩
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r24, .r25, .r30])
        (.seq (.block [.addi .r3 .r30 64, mov .r4 .r24, mov .r5 .r25]) xorLoop) h).isSome = true :=
      ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, _, a30, _, _, h₁⟩ ⟨_, _, _, _, _, _, b30, _, _, h₂⟩ =>
      ⟨h₁.env.sp.trans h₂.env.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.r24, h₂.r24]
    · rw [h₁.r25, h₂.r25]
    · rw [h₁.env.r30, h₂.env.r30, a30, b30]

theorem crypt_ct {D : Addr} {n q : Nat} :
    CT (CrI c st w x sp D n q) crypt := by
  refine CT.ite (decide (n = 0)) (fun s ⟨_, _, _, _, _, _, _, _, hs⟩ => eval_zero hs.r25 hs.data.ok.lt)
    (fun _ => CT.skip) fun hb => ?_
  have h0 : n ≠ 0 := by simpa using hb
  let j₁ := if q = 0 then 0 else min (16 - q) n
  refine CT.seq (J := CrM c st w x sp D n q j₁) ?_
    (fun s ⟨V, icb, P, h29, h30, h31, h28, hP, hs⟩ => WP.mono (cryptFill_ok hs h0) fun s' ⟨j, hj, hm⟩ =>
      ⟨V, icb, P, s.mem, h29, h30, h31, h28, hP, by subst hj; rw [hP] at hm; exact hm⟩) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r24, .r25, .r26, .r30]) cryptFill
        h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, a30, _, _, hP₁, h₁⟩ ⟨_, _, _, _, b30, _, _, hP₂, h₂⟩ =>
      ⟨h₁.env.sp.trans h₂.env.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₁.r24, h₂.r24]
    · rw [h₁.r25, h₂.r25]
    · rw [h₁.r26, h₂.r26, hP₁, hP₂]
    · rw [h₁.env.r30, h₂.env.r30, a30, b30]
  refine CT.seq (J := CrM c st w x sp D n q (j₁ + 16 * ((n - j₁) / 16))) (cryptWhole_ct L X)
    (fun s ⟨V, icb, P, m₀, h29, h30, h31, h28, hP, hs⟩ =>
      WP.mono (cryptWhole_ok (L.v h29 h30 h31) (by rw [h29, h30, h31, h28]; exact X) hs) fun s' ⟨j, hj, hm, _⟩ =>
        ⟨V, icb, P, m₀, h29, h30, h31, h28, hP, by subst hj; exact hm⟩) (cryptTail_ct L X)

end

end VG.Proof.Sm4Gcm.PPC64LE
