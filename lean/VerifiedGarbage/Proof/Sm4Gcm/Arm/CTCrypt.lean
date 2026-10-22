module
public import VerifiedGarbage.Proof.Sm4Gcm.Arm.CTBase
public import VerifiedGarbage.Proof.Sm4Gcm.Arm.Crypt

import VerifiedGarbage.Proof.Sm4Gcm.Arm.CTAbsorb
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.CTAbsorb
import VerifiedGarbage.Proof.Sm4Gcm.Arm.Tag
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.Tag
import VerifiedGarbage.Proof.Sm4Gcm.Arm.CryptOk
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.CryptOk
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.Entry
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.Ghash1
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.Loops
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.Open
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.Seal
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Mem
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Bytes
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sha256.Stream

/-!
# SM4-GCM on ARMv7: `crypt` and `tag` are constant time

Untrusted: everything here is checked by Lean. The invariants fix the
context, the state, `W`, the stack pointer, the value of `r8`, the data's
address and length, and the length of the text so far modulo 16.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Sm4Gcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- Before `crypt`. -/
def CrI (c st w sp k8 : BitVec 32) (D : BitVec 32) (n q : Nat) (s : State) : Prop :=
  ∃ k7 icb P, P % 16 = q ∧ CrIn c st w sp k7 k8 icb P D n s

/-- Part of the way: `j` bytes done. -/
def CrM (c st w sp k8 : BitVec 32) (D : BitVec 32) (n q j : Nat) (s : State) : Prop :=
  ∃ k7 icb P m₀, P % 16 = q ∧ CrMid c st w sp k7 k8 icb P D n m₀ j s

section
variable {c st w sp : BitVec 32} (L : Lay c st w sp)
include L

theorem cryptWhole_ct {k8 : BitVec 32} {D : BitVec 32} {n q j : Nat} :
    CT (CrM c st w sp k8 D n q j) cryptWhole := by
  let nb := (n - j) / 16
  let J₁ : State → Prop := fun s => ∃ k7, Env c st w sp k7 k8 s ∧ DataW c st w sp k7 k8 s D n ∧ j ≤ n ∧
    s.gpr .r3 = D + BitVec.ofNat 32 j ∧ s.gpr .r12 = BitVec.ofNat 32 nb ∧ s.z = decide (nb = 0)
  refine CT.seq (J := J₁) ?_ (fun s ⟨k7, icb, P, m₀, hP, hs⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r4, .r5]) (.block splitCtr) h).isSome =
        true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, h₁⟩ ⟨_, _, _, _, _, h₂⟩ r hr => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.r4, h₂.r4]
    · rw [h₁.r5, h₂.r5]
  · obtain ⟨s₁, run₁, h3, h12, -, -, hz, hg₁, hk₁⟩ := splitCtr_ok hs.le hs.data.ok.lt32 hs.r4 hs.r5
    refine WP.of_runBlock ⟨s₁, run₁, k7, hs.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)) hk₁.sp hk₁.rd hk₁.wr, hs.data.of_eq hk₁.rd hk₁.wr, hs.le, h3, h12, hz⟩
  · refine CT.ite (decide (nb = 0)) (fun s h => by obtain ⟨_, _, _, _, _, _, hz⟩ := h; exact hz)
      (fun _ => CT.skip) fun hb => ?_
    have h0 : nb ≠ 0 := by simpa using hb
    let J₂ : State → Prop := fun s => ∃ k7, Env c st w sp k7 k8 s ∧ DataW c st w sp k7 k8 s D n ∧ j ≤ n ∧
      s.gpr .r0 = c ∧ s.gpr .r2 = st + BitVec.ofNat 32 48 ∧ s.gpr .r3 = D + BitVec.ofNat 32 j ∧
      s.gpr .r12 = BitVec.ofNat 32 nb
    refine CT.seq (J := J₂) ?_ (fun s ⟨k7, he, hd, hj, h3, h12, _⟩ => ?_) ?_
    · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r9, .r10, .r11])
          (.block [.mov .r0 (.reg .r9), addI .r2 .r10 48]) h).isSome = true := ⟨_, by taint_decide⟩
      exact CT.taint _ (fun s₁ s₂ ⟨_, h₁, _⟩ ⟨_, h₂, _⟩ r hr => h₁.pin h₂ (by simpa using hr)) hc
    · obtain ⟨s₂, run₂, h0', h2', hg₂, hk₂⟩ := wholeArgs_ok he
      refine WP.of_runBlock ⟨s₂, run₂, k7, he.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide))
        hk₂.sp hk₂.rd hk₂.wr, hd.of_eq hk₂.rd hk₂.wr, hj, h0', h2',
        by rw [hg₂ _ (by decide) (by decide), h3], by rw [hg₂ _ (by decide) (by decide), h12]⟩
    · refine CT.ctr fun s₁ s₂ ⟨_, he₁, hd₁, hj₁, a0, a2, a3, a12⟩ ⟨_, he₂, hd₂, _, b0, b2, b3, b12⟩ => ?_
      exact ⟨_, _, _, _, ctrWhole_mk L he₁ a0 a2 a3 a12 (hd₁.sub (by omega) (by omega)),
        ctrWhole_mk L he₂ b0 b2 b3 b12 (hd₂.sub (by omega) (by omega)), he₁.sp.trans he₂.sp.symm⟩

theorem cryptTail_ct {k8 : BitVec 32} {D : BitVec 32} {n q j : Nat} :
    CT (CrM c st w sp k8 D n q j) cryptTail := by
  refine CT.seq (J := fun s => CrM c st w sp k8 D n q j s ∧ s.z = decide (n - j = 0)) ?_
    (fun s ⟨k7, icb, P, m₀, hP, hs⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r5]) (.block [.cmp .r5 (imm 0)]) h).isSome =
        true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, h₁⟩ ⟨_, _, _, _, _, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r5, h₂.r5]) hc
  · obtain ⟨s₁, run₁, hz, hg₁, hm₁, hrd₁, hwr₁, hsp₁⟩ := cmp0_ok s .r5 hs.r5 (by have := hs.data.ok.lt32; omega)
    refine WP.of_runBlock ⟨s₁, run₁, ⟨k7, icb, P, m₀, hP, ?_⟩, hz⟩
    exact ⟨hs.env.keep (fun r _ => by rw [hg₁]) hsp₁ hrd₁ hwr₁, hs.le, by rw [hg₁, hs.r4], by rw [hg₁, hs.r5],
      hs.data.of_eq hrd₁ hwr₁, fun h => by rw [hm₁]; exact hs.ctr h,
      fun h => by rw [hm₁]; exact hs.done h, by rw [hm₁]; exact hs.rest, hs.whole, by rw [hm₁]; exact hs.frame⟩
  refine CT.ite (decide (n - j = 0)) (fun s h => h.2) (fun _ => CT.skip) fun _ => ?_
  let J₁ : State → Prop := fun s => ∃ k7, Env c st w sp k7 k8 s ∧ s.gpr .r0 = c ∧
    s.gpr .r2 = st + BitVec.ofNat 32 48 ∧ s.gpr .r3 = st + BitVec.ofNat 32 64 ∧ s.gpr .r12 = BitVec.ofNat 32 1
  let J₂ : State → Prop := fun s => ∃ k7 icb P m₀ s₀, TailKs c st w sp k7 k8 icb P D n m₀ j s₀ s
  refine CT.seq (J := J₂) (CT.seq (J := J₁) ?_ (fun s ⟨⟨k7, icb, P, m₀, hP, hs⟩, _⟩ => ?_) ?_)
    (fun s ⟨⟨k7, icb, P, m₀, hP, hs⟩, _⟩ => WP.mono (tailKs_ok L hs (hs.ciph L)) fun s' h => ⟨k7, icb, P, m₀, s, h⟩) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r9, .r10, .r11]) (.block tailArgs)
        h).isSome = true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨⟨_, _, _, _, _, h₁⟩, _⟩ ⟨⟨_, _, _, _, _, h₂⟩, _⟩ r hr =>
      h₁.env.pin h₂.env (by simpa using hr)) hc
  · obtain ⟨s₂, run₂, -, h0, h2, h3, h12, hg₂, hrd₂, hwr₂, hsp₂⟩ := tailArgs_ok L hs.env
    exact WP.of_runBlock ⟨s₂, run₂, k7, hs.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        exact hg₂ _ (by decide) (by decide) (by decide) (by decide)) hsp₂ hrd₂ hwr₂,
      h0, h2, h3, h12⟩
  · exact CT.ctr fun s₁ s₂ ⟨_, he₁, a0, a2, a3, a12⟩ ⟨_, he₂, b0, b2, b3, b12⟩ =>
      ⟨_, _, _, _, ctrTail_mk L he₁ a0 a2 a3 a12, ctrTail_mk L he₂ b0 b2 b3 b12, he₁.sp.trans he₂.sp.symm⟩
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r4, .r5, .r10])
        (.seq (.block [addI .r1 .r10 64, .mov .r2 (.reg .r4), .mov .r3 (.reg .r5)]) xorLoop) h).isSome = true :=
      ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, h₁⟩ ⟨_, _, _, _, _, h₂⟩ r hr => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.r4, h₂.r4]
    · rw [h₁.r5, h₂.r5]
    · exact h₁.env.pin h₂.env (by simp)

theorem crypt_ct {k8 : BitVec 32} {D : BitVec 32} {n q : Nat} :
    CT (CrI c st w sp k8 D n q) crypt := by
  refine CT.seq (J := fun s => CrI c st w sp k8 D n q s ∧ s.z = decide (n = 0)) ?_
    (fun s ⟨k7, icb, P, hP, hs⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r5]) (.block [.cmp .r5 (imm 0)]) h).isSome =
        true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, h₁⟩ ⟨_, _, _, _, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r5, h₂.r5]) hc
  · obtain ⟨s₁, run₁, hz, hg₁, hm₁, hrd₁, hwr₁, hsp₁⟩ := cmp0_ok s .r5 hs.r5 hs.data.ok.lt32
    exact WP.of_runBlock ⟨s₁, run₁, ⟨k7, icb, P, hP, hs.keep hg₁ ⟨hm₁, hrd₁, hwr₁, hsp₁⟩⟩, hz⟩
  refine CT.ite (decide (n = 0)) (fun s h => h.2) (fun _ => CT.skip) fun hb => ?_
  have h0 : n ≠ 0 := by simpa using hb
  let j₁ := if q = 0 then 0 else min (16 - q) n
  refine CT.seq (J := CrM c st w sp k8 D n q j₁) ?_
    (fun s ⟨⟨k7, icb, P, hP, hs⟩, _⟩ => WP.mono (cryptFill_ok L hs h0) fun s' ⟨j, hj, hm⟩ =>
      ⟨k7, icb, P, s.mem, hP, by rw [hj, hP] at hm; exact hm⟩) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r4, .r5, .r6, .r10]) cryptFill h).isSome =
        true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨⟨_, _, _, hP₁, h₁⟩, _⟩ ⟨⟨_, _, _, hP₂, h₂⟩, _⟩ r hr => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₁.r4, h₂.r4]
    · rw [h₁.r5, h₂.r5]
    · rw [h₁.r6, h₂.r6, hP₁, hP₂]
    · exact h₁.env.pin h₂.env (by simp)
  refine CT.seq (J := CrM c st w sp k8 D n q (j₁ + 16 * ((n - j₁) / 16))) (cryptWhole_ct L)
    (fun s ⟨k7, icb, P, m₀, hP, hs⟩ => WP.mono (cryptWhole_ok L hs (hs.ciph L)) fun s' ⟨j, hj, hm, _⟩ =>
      ⟨k7, icb, P, m₀, hP, by rw [hj] at hm; exact hm⟩) (cryptTail_ct L)

/-- `tag o`. -/
theorem tag_ct {o : Nat} (ho : o = 0 ∨ o = 112) {k8 : BitVec 32} :
    CT (fun s => ∃ k7, Env c st w sp k7 k8 s) (tag o) := by
  refine CT.seq (J := fun s => ∃ k7, Env c st w sp k7 k8 s)
    ((lens_ct L (yo := 16) (.inr rfl)).mono fun s ⟨k7, he⟩ => ⟨k7, _, he⟩)
    (fun s ⟨k7, he⟩ => WP.mono (lens_ok L (yo := 16) (.inr rfl) (H := blockAt s.mem (State.addr c + BitVec.ofNat 64 128))
      he rfl) fun s' h => ⟨k7, h.1⟩) ?_
  let J : State → Prop := fun s => ∃ k7, Env c st w sp k7 k8 s ∧ s.gpr .r0 = c ∧
    s.gpr .r2 = st ∧ s.gpr .r3 = w + BitVec.ofNat 32 o ∧ s.gpr .r12 = BitVec.ofNat 32 1
  refine CT.seq (J := J) ?_ (fun s ⟨k7, he⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r9, .r10, .r11]) (.block (tagArgs o))
        h).isSome = true := by rcases ho with rfl | rfl <;> exact ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨_, h₁⟩ ⟨_, h₂⟩ r hr => h₁.pin h₂ (by simpa using hr)) hc
  · obtain ⟨s₂, run₂, -, h0, h2, h3, h12, hg₂, hrd₂, hwr₂, hsp₂⟩ := tagArgs_ok L ho he
    exact WP.of_runBlock ⟨s₂, run₂, k7, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        exact hg₂ _ (by decide) (by decide) (by decide) (by decide)) hsp₂ hrd₂ hwr₂,
      h0, h2, h3, h12⟩
  · exact CT.ctr fun s₁ s₂ ⟨_, he₁, a0, a2, a3, a12⟩ ⟨_, he₂, b0, b2, b3, b12⟩ =>
      ⟨_, _, _, _, ctrTag_mk L ho he₁ a0 a2 a3 a12, ctrTag_mk L ho he₂ b0 b2 b3 b12, he₁.sp.trans he₂.sp.symm⟩

end

end VG.Proof.Sm4Gcm.Arm
