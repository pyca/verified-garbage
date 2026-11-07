module
public import VerifiedGarbage.Proof.AesGcm.Arm.CTBase
public import VerifiedGarbage.Proof.AesGcm.Arm.Crypt

import VerifiedGarbage.Proof.AesGcm.Arm.CTAbsorb
meta import VerifiedGarbage.Proof.AesGcm.Arm.CTAbsorb
import VerifiedGarbage.Proof.AesGcm.Arm.Tag
meta import VerifiedGarbage.Proof.AesGcm.Arm.Tag
import VerifiedGarbage.Proof.AesGcm.Arm.CryptOk
meta import VerifiedGarbage.Proof.AesGcm.Arm.CryptOk
import VerifiedGarbage.Proof.AesGcm.Arm.Entry
import VerifiedGarbage.Proof.AesGcm.Arm.Ghash1
import VerifiedGarbage.Proof.AesGcm.Arm.Loops
import VerifiedGarbage.Proof.AesGcm.Arm.Open
import VerifiedGarbage.Proof.AesGcm.Arm.Seal
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Bytes
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Impl.Aes.Arm.Alloc
meta import VerifiedGarbage.Proof.AesGcm.Arm.Entry
meta import VerifiedGarbage.Proof.AesGcm.Arm.Ghash1
meta import VerifiedGarbage.Proof.AesGcm.Arm.Loops
meta import VerifiedGarbage.Proof.AesGcm.Arm.Open
meta import VerifiedGarbage.Proof.AesGcm.Arm.Seal
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
# AES-GCM on ARMv7: `crypt` and `tag` are constant time

Untrusted: everything here is checked by Lean. The invariants fix the
context, the state, `W`, the stack pointer, the number of rounds (in `r8`),
the data's address and length, and the length of the text so far modulo 16.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- Before `crypt`. -/
def CrI (c st w sp k8 : BitVec 32) (R : Nat) (D : BitVec 32) (n q : Nat) (s : State) : Prop :=
  ∃ k7 icb P, P % 16 = q ∧ CrIn c st w sp k7 k8 R icb P D n s

/-- Part of the way: `j` bytes done, from `S` to `T`. -/
def CrMG (to : Bool) (c st w sp k8 : BitVec 32) (R : Nat) (S T : BitVec 32) (n q j : Nat) (s : State) : Prop :=
  ∃ k7 icb P m₀, P % 16 = q ∧ CrMidG to c st w sp k7 k8 R icb P S T n m₀ j s

/-- In place. -/
abbrev CrM (c st w sp k8 : BitVec 32) (R : Nat) (D : BitVec 32) (n q j : Nat) (s : State) : Prop :=
  CrMG false c st w sp k8 R D D n q j s

theorem pin8 {c st w sp a b a' b' : BitVec 32} {s₁ s₂ : State} (h₁ : Env c st w sp a b s₁)
    (h₂ : Env c st w sp a' b' s₂) {R : Nat} (e₁ : s₁.gpr .r8 = BitVec.ofNat 32 R) (e₂ : s₂.gpr .r8 = BitVec.ofNat 32 R)
    {r : Reg} (hr : r = .r8 ∨ r = .r9 ∨ r = .r10 ∨ r = .r11) : s₁.gpr r = s₂.gpr r := by
  rcases hr with rfl | hr
  · rw [e₁, e₂]
  · exact h₁.pin h₂ hr

section
variable {c st w sp : BitVec 32} (L : Lay c st w sp)
include L

theorem cryptWhole_ct {to : Bool} {k8 : BitVec 32} {R : Nat} {S T : BitVec 32} {n q j : Nat} :
    CT (CrMG to c st w sp k8 R S T n q j) (cryptWholeG to) := by
  let nb := (n - j) / 16
  let J₁ : State → Prop := fun s => ∃ k7, Env c st w sp k7 k8 s ∧ DataW c st w sp k7 k8 s T n ∧
    DataOk st w sp s S n ∧ CrMode to c st w sp S T n ∧ j ≤ n ∧
    s.gpr .r8 = BitVec.ofNat 32 R ∧ (R = 10 ∨ R = 12 ∨ R = 14) ∧
    s.gpr .r3 = S + BitVec.ofNat 32 j ∧ s.gpr .r12 = BitVec.ofNat 32 nb ∧ s.z = decide (nb = 0) ∧
    (to = true → s.gpr .r6 = T + BitVec.ofNat 32 j)
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
        (by decide) (by decide)) hk₁.sp hk₁.rd hk₁.wr, hs.data.of_eq hk₁.rd hk₁.wr, hs.src.of_eq hk₁.rd hk₁.wr,
      hs.mode, hs.le,
      by rw [hg₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hs.r8], hs.rounds,
      h3, h12, hz, fun ht => by
        rw [hg₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hs.r6 ht]⟩
  · refine CT.ite (decide (nb = 0)) (fun s h => by obtain ⟨_, _, _, _, _, _, _, _, _, _, hz, _⟩ := h; exact hz)
      (fun _ => CT.skip) fun hb => ?_
    have h0 : nb ≠ 0 := by simpa using hb
    cases to
    · let J₂ : State → Prop := fun s => ∃ k7, Env c st w sp k7 k8 s ∧ DataW c st w sp k7 k8 s T n ∧ j ≤ n ∧
        (R = 10 ∨ R = 12 ∨ R = 14) ∧ s.gpr .r0 = c ∧ s.gpr .r1 = BitVec.ofNat 32 R ∧
        s.gpr .r2 = st + BitVec.ofNat 32 48 ∧ s.gpr .r3 = S + BitVec.ofNat 32 j ∧
        s.gpr .r12 = BitVec.ofNat 32 nb ∧ s.gpr .lr = w + BitVec.ofNat 32 512 ∧ S = T
      refine CT.seq (J := J₂) ?_ (fun s ⟨k7, he, hd, _, hm, hj, h8, hR, h3, h12, _⟩ => ?_) ?_
      · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r8, .r9, .r10, .r11])
            (.block [.mov .r0 (.reg .r9), .mov .r1 (.reg .r8), addI .r2 .r10 48, addI .lr .r11 scrO]) h).isSome =
            true := ⟨_, by taint_decide⟩
        exact CT.taint _ (fun s₁ s₂ ⟨_, h₁, _, _, _, _, e₁, _⟩ ⟨_, h₂, _, _, _, _, e₂, _⟩ r hr =>
          pin8 h₁ h₂ e₁ e₂ (by simpa using hr)) hc
      · obtain ⟨s₂, run₂, h0', h1', h2', hlr', hg₂, hk₂⟩ := wholeArgs_ok he
        refine WP.of_runBlock ⟨s₂, run₂, k7, he.keep (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide) (by decide))
          hk₂.sp hk₂.rd hk₂.wr, hd.of_eq hk₂.rd hk₂.wr, hj, hR, h0', by rw [h1', h8], h2',
          by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide), h3],
          by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide), h12], hlr', hm⟩
      · refine CT.ctr fun s₁ s₂ ⟨_, he₁, hd₁, hj₁, hR, a0, a1, a2, a3, a12, alr, e⟩
          ⟨_, he₂, hd₂, _, _, b0, b1, b2, b3, b12, blr, _⟩ => ?_
        subst e
        exact ⟨_, _, _, _, _, _, ctrWhole_mk L he₁ a0 a1 a2 a3 a12 alr hR (hd₁.sub (by omega) (by omega)),
          ctrWhole_mk L he₂ b0 b1 b2 b3 b12 blr hR (hd₂.sub (by omega) (by omega)), he₁.sp.trans he₂.sp.symm⟩
    · -- Out of place: the destination and the count to the stack arguments, the call, and the
      -- destination advanced.
      let J₂ : State → Prop := fun s => ∃ k7, Env c st w sp k7 k8 s ∧ DataW c st w sp k7 k8 s T n ∧
        DataOk st w sp s S n ∧ CrMode true c st w sp S T n ∧ j ≤ n ∧ (R = 10 ∨ R = 12 ∨ R = 14) ∧
        s.gpr .r0 = BitVec.ofNat 32 nb ∧ s.gpr .r1 = w + BitVec.ofNat 32 512 ∧
        s.gpr .r2 = T + BitVec.ofNat 32 j ∧ s.gpr .r3 = S + BitVec.ofNat 32 j ∧
        s.gpr .r8 = BitVec.ofNat 32 R ∧ s.gpr .r6 = T + BitVec.ofNat 32 j
      let J₃ : State → Prop := fun s => s.gpr .r6 = T + BitVec.ofNat 32 j ∧ s.gpr .r12 = BitVec.ofNat 32 nb
      refine CT.seq (J := J₂) ?_ (fun s ⟨k7, he, hd, hsr, hm, hj, h8, hR, h3, h12, _, h6⟩ => ?_) ?_
      · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r6, .r11, .r12])
            (.block [.mov .r2 (.reg .r6), .mov .r0 (.reg .r12), addI .r1 .r11 scrO]) h).isSome =
            true := ⟨_, by taint_decide⟩
        refine CT.taint _ (fun s₁ s₂ ⟨_, h₁, _, _, _, _, _, _, _, a12, _, a6⟩ ⟨_, h₂, _, _, _, _, _, _, _, b12, _, b6⟩
          r hr => ?_) hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [a6 rfl, b6 rfl]
        · exact h₁.pin h₂ (by simp)
        · rw [a12, b12]
      · obtain ⟨s₂, run₂, h0', h1', h2', hg₂, hk₂⟩ : ∃ s₂, runBlock isa
            [.mov .r2 (.reg .r6), .mov .r0 (.reg .r12), addI .r1 .r11 scrO] s = some s₂ ∧
            s₂.gpr .r0 = BitVec.ofNat 32 nb ∧ s₂.gpr .r1 = w + BitVec.ofNat 32 512 ∧
            s₂.gpr .r2 = T + BitVec.ofNat 32 j ∧
            (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → s₂.gpr r = s.gpr r) ∧ Keeps s s₂ := by
          refine ⟨_, by arun [], ?_, ?_, ?_, ?_, ?_⟩
          · simp [gpr_setReg, h12]
          · simp [gpr_setReg, he.r11]
          · simp [gpr_setReg, h6 rfl]
          · intro r a b d; simp [gpr_setReg, a, b, d]
          · exact ⟨rfl, rfl, rfl, rfl⟩
        exact WP.of_runBlock ⟨s₂, run₂, k7, he.keep (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide))
          hk₂.sp hk₂.rd hk₂.wr, hd.of_eq hk₂.rd hk₂.wr, hsr.of_eq hk₂.rd hk₂.wr, hm, hj, hR, h0', h1', h2',
          by rw [hg₂ _ (by decide) (by decide) (by decide), h3], by rw [hg₂ _ (by decide) (by decide) (by decide), h8],
          by rw [hg₂ _ (by decide) (by decide) (by decide), h6 rfl]⟩
      have mk : ∀ s, J₂ s → CtrToCall s c (st + BitVec.ofNat 32 48) (S + BitVec.ofNat 32 j) (T + BitVec.ofNat 32 j)
          (w + BitVec.ofNat 32 512) R nb := by
        intro s ⟨k7, he, hd, hsr, hm, hj, hR, a0, a1, a2, a3, a8, _⟩
        obtain ⟨dST, sp12, bc, bst, bw, bS, bT⟩ := hm
        have hdj := hd.sub (j := j) (k := 16 * nb) (by omega) (by omega)
        have hsj := hsr.sub (j := j) (k := 16 * nb) (by omega) (by omega)
        have eD := hd.ok.addr (j := j) (by omega)
        have eS := hsr.addr (j := j) (by omega)
        have eC := L.stA (d := 48) (by decide)
        have eW := L.wA (d := 512) (by decide)
        have hk := he.sp
        refine ⟨he.r9, a8, by rw [he.r10], a3, a0, a1, a2, hR, by rw [hk]; exact sp12,
          by have := L.cw; omega, by rw [L.stN (by decide)]; have := L.sw; omega, hsj.fit, hdj.ok.fit,
          by rw [L.wN (by decide)]; have := L.ww; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals try simp only [eC, eW]
        · exact (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (by decide))
        · exact hdj.ctx.sub_left (Region.sub_prefix (by decide))
        · exact (L.cw'.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide))
        · exact (hdj.ok.st.sub_right (Lay.stSub (by decide))).symm
        · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
        · exact hdj.ok.w.sub_right (Lay.wSub (by decide))
        · exact hsj.st.sub_right (Lay.stSub (by decide))
        · rw [eS, eD]
          exact (dST.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by omega))
        · exact hsj.w.sub_right (Lay.wSub (by decide))
        · rw [hk]; exact bc.sub_right (Region.sub_prefix (by decide))
        · rw [hk]; exact bst.sub_right (Lay.stSub (by decide))
        · rw [hk, eS]; exact bS.sub_right (Offset.sub_base _ (by omega))
        · rw [hk, eD]; exact bT.sub_right (Offset.sub_base _ (by omega))
        · rw [hk]; exact bw.sub_right (Lay.wSub (by decide))
        · exact covers_cons (covers_prefix he.perm.ctx (by decide)) hsj.rd
        · exact covers_cons (he.perm.stC (by decide)) (covers_cons hdj.wr (he.perm.wC (by decide)))
      have spJ : ∀ s, J₂ s → s.sp = sp := fun s ⟨_, he, _⟩ => he.sp
      refine CT.seq (J := J₃) (CT.ctrTo fun s₁ s₂ h₁ h₂ => ⟨_, _, _, _, _, _, _, mk s₁ h₁, mk s₂ h₂,
        (spJ s₁ h₁).trans (spJ s₂ h₂).symm⟩) (fun s hs => WP.mono (ctrTo_call (mk s hs)) fun s' g => ⟨?_, ?_⟩) ?_
      · obtain ⟨_, he, _, _, _, _, _, _, _, _, _, _, h6⟩ := hs
        rw [g.saved _ (by decide) (by decide), h6]
      · obtain ⟨_, _, _, _, _, _, _, a0, _⟩ := hs
        rw [g.r12, a0]
      · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r6, .r12])
            (.block [.dp .add .r6 .r6 (.shifted .r12 .lsl 4)]) h).isSome = true := ⟨_, by taint_decide⟩
        refine CT.taint _ (fun s₁ s₂ ⟨a6, a12⟩ ⟨b6, b12⟩ r hr => ?_) hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [a6, b6]
        · rw [a12, b12]

theorem cryptTail_ct {to : Bool} {k8 : BitVec 32} {R : Nat} {S T : BitVec 32} {n q j : Nat} :
    CT (CrMG to c st w sp k8 R S T n q j) (cryptTailG to) := by
  refine CT.seq (J := fun s => CrMG to c st w sp k8 R S T n q j s ∧ s.z = decide (n - j = 0)) ?_
    (fun s ⟨k7, icb, P, m₀, hP, hs⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r5]) (.block [.cmp .r5 (imm 0)]) h).isSome =
        true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, h₁⟩ ⟨_, _, _, _, _, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r5, h₂.r5]) hc
  · obtain ⟨s₁, run₁, hz, hg₁, hm₁, hrd₁, hwr₁, hsp₁⟩ := cmp0_ok s .r5 hs.r5 (by have := hs.data.ok.lt32; omega)
    refine WP.of_runBlock ⟨s₁, run₁, ⟨k7, icb, P, m₀, hP, ?_⟩, hz⟩
    exact ⟨hs.env.keep (fun r _ => by rw [hg₁]) hsp₁ hrd₁ hwr₁, hs.le, by rw [hg₁, hs.r4], by rw [hg₁, hs.r5],
      by rw [hg₁, hs.r8], hs.rounds, hs.data.of_eq hrd₁ hwr₁, fun h => by rw [hm₁]; exact hs.ctr h,
      fun h => by rw [hm₁]; exact hs.done h, by rw [hm₁]; exact hs.rest, hs.whole, by rw [hm₁]; exact hs.frame,
      fun h => by rw [hg₁]; exact hs.r6 h, hs.src.of_eq hrd₁ hwr₁, hs.mode⟩
  refine CT.ite (decide (n - j = 0)) (fun s h => h.2) (fun _ => CT.skip) fun _ => ?_
  let J₁ : State → Prop := fun s => ∃ k7, Env c st w sp k7 k8 s ∧ (R = 10 ∨ R = 12 ∨ R = 14) ∧ s.gpr .r0 = c ∧
    s.gpr .r1 = BitVec.ofNat 32 R ∧ s.gpr .r2 = st + BitVec.ofNat 32 48 ∧ s.gpr .r3 = st + BitVec.ofNat 32 64 ∧
    s.gpr .r12 = BitVec.ofNat 32 1 ∧ s.gpr .lr = w + BitVec.ofNat 32 512
  let J₂ : State → Prop := fun s => ∃ k7 icb P m₀ s₀, TailKs to c st w sp k7 k8 R icb P S T n m₀ j s₀ s
  refine CT.seq (J := J₂) (CT.seq (J := J₁) ?_ (fun s ⟨⟨k7, icb, P, m₀, hP, hs⟩, _⟩ => ?_) ?_)
    (fun s ⟨⟨k7, icb, P, m₀, hP, hs⟩, _⟩ => WP.mono (tailKs_ok L hs (CrMidG.ciph L hs)) fun s' h =>
      ⟨k7, icb, P, m₀, s, h⟩) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r8, .r9, .r10, .r11]) (.block tailArgs)
        h).isSome = true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨⟨_, _, _, _, _, h₁⟩, _⟩ ⟨⟨_, _, _, _, _, h₂⟩, _⟩ r hr =>
      pin8 h₁.env h₂.env h₁.r8 h₂.r8 (by simpa using hr)) hc
  · obtain ⟨s₂, run₂, -, h0, h1, h2, h3, h12, hlr, hg₂, hrd₂, hwr₂, hsp₂⟩ := tailArgs_ok L hs.env
    exact WP.of_runBlock ⟨s₂, run₂, k7, hs.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        exact hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hsp₂ hrd₂ hwr₂,
      hs.rounds, h0, by rw [h1, hs.r8], h2, h3, h12, hlr⟩
  · exact CT.ctr fun s₁ s₂ ⟨_, he₁, hR, a0, a1, a2, a3, a12, alr⟩ ⟨_, he₂, _, b0, b1, b2, b3, b12, blr⟩ =>
      ⟨_, _, _, _, _, _, ctrTail_mk L he₁ a0 a1 a2 a3 a12 alr hR, ctrTail_mk L he₂ b0 b1 b2 b3 b12 blr hR,
        he₁.sp.trans he₂.sp.symm⟩
  · cases to
    · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r4, .r5, .r10]) (tailOut false)
          h).isSome = true := ⟨_, by taint_decide⟩
      refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, h₁⟩ ⟨_, _, _, _, _, h₂⟩ r hr => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h₁.r4, h₂.r4]
      · rw [h₁.r5, h₂.r5]
      · exact h₁.env.pin h₂.env (by simp)
    · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r4, .r5, .r6, .r10]) (tailOut true)
          h).isSome = true := ⟨_, by taint_decide⟩
      refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, h₁⟩ ⟨_, _, _, _, _, h₂⟩ r hr => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h₁.r4, h₂.r4]
      · rw [h₁.r5, h₂.r5]
      · rw [h₁.r6 rfl, h₂.r6 rfl]
      · exact h₁.env.pin h₂.env (by simp)

/-- `cryptTo`, from the start of a whole block. -/
theorem cryptTo_ct {k8 : BitVec 32} {R : Nat} {S T : BitVec 32} {n : Nat} :
    CT (CrMG true c st w sp k8 R S T n 0 0) cryptTo := by
  refine CT.seq (J := fun s => CrMG true c st w sp k8 R S T n 0 0 s ∧ s.z = decide (n - 0 = 0)) ?_
    (fun s ⟨k7, icb, P, m₀, hP, hs⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r5]) (.block [.cmp .r5 (imm 0)]) h).isSome =
        true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, h₁⟩ ⟨_, _, _, _, _, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r5, h₂.r5]) hc
  · obtain ⟨s₁, run₁, hz, hg₁, hm₁, hrd₁, hwr₁, hsp₁⟩ := cmp0_ok s .r5 hs.r5 (by have := hs.data.ok.lt32; omega)
    refine WP.of_runBlock ⟨s₁, run₁, ⟨k7, icb, P, m₀, hP, ?_⟩, hz⟩
    exact ⟨hs.env.keep (fun r _ => by rw [hg₁]) hsp₁ hrd₁ hwr₁, hs.le, by rw [hg₁, hs.r4], by rw [hg₁, hs.r5],
      by rw [hg₁, hs.r8], hs.rounds, hs.data.of_eq hrd₁ hwr₁, fun h => by rw [hm₁]; exact hs.ctr h,
      fun h => by rw [hm₁]; exact hs.done h, by rw [hm₁]; exact hs.rest, hs.whole, by rw [hm₁]; exact hs.frame,
      fun h => by rw [hg₁]; exact hs.r6 h, hs.src.of_eq hrd₁ hwr₁, hs.mode⟩
  refine CT.ite (decide (n - 0 = 0)) (fun s h => h.2) (fun _ => CT.skip) fun _ => ?_
  refine CT.seq (J := CrMG true c st w sp k8 R S T n 0 (0 + 16 * ((n - 0) / 16)))
    (CT.mono (cryptWhole_ct L) fun _ h => h.1)
    (fun s ⟨⟨k7, icb, P, m₀, hP, hs⟩, _⟩ => WP.mono (cryptWholeG_ok L hs (CrMidG.ciph L hs)) fun s' ⟨j, hj, hm, _⟩ =>
      ⟨k7, icb, P, m₀, hP, by rw [hj] at hm; exact hm⟩) (cryptTail_ct L)

theorem crypt_ct {k8 : BitVec 32} {R : Nat} {D : BitVec 32} {n q : Nat} :
    CT (CrI c st w sp k8 R D n q) crypt := by
  refine CT.seq (J := fun s => CrI c st w sp k8 R D n q s ∧ s.z = decide (n = 0)) ?_
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
  refine CT.seq (J := CrM c st w sp k8 R D n q j₁) ?_
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
  refine CT.seq (J := CrM c st w sp k8 R D n q (j₁ + 16 * ((n - j₁) / 16))) (cryptWhole_ct L)
    (fun s ⟨k7, icb, P, m₀, hP, hs⟩ => WP.mono (cryptWholeG_ok L hs (CrMidG.ciph L hs)) fun s' ⟨j, hj, hm, _⟩ =>
      ⟨k7, icb, P, m₀, hP, by rw [hj] at hm; exact hm⟩) (cryptTail_ct L)

/-- `tag o`, from an environment with the number of rounds in `r8`. -/
theorem tag_ct {o R : Nat} (ho : o = 0 ∨ o = 112) (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    CT (fun s => ∃ k7, Env c st w sp k7 (BitVec.ofNat 32 R) s) (tag o) := by
  refine CT.seq (J := fun s => ∃ k7, Env c st w sp k7 (BitVec.ofNat 32 R) s)
    ((lens_ct L (yo := 16) (.inr rfl)).mono fun s ⟨k7, he⟩ => ⟨k7, _, he⟩)
    (fun s ⟨k7, he⟩ => WP.mono (lens_ok L (yo := 16) (.inr rfl) (H := blockAt s.mem (State.addr c + BitVec.ofNat 64 240))
      he rfl) fun s' h => ⟨k7, h.1⟩) ?_
  let J : State → Prop := fun s => ∃ k7, Env c st w sp k7 (BitVec.ofNat 32 R) s ∧ s.gpr .r0 = c ∧
    s.gpr .r1 = BitVec.ofNat 32 R ∧ s.gpr .r2 = st ∧ s.gpr .r3 = w + BitVec.ofNat 32 o ∧
    s.gpr .r12 = BitVec.ofNat 32 1 ∧ s.gpr .lr = w + BitVec.ofNat 32 512
  refine CT.seq (J := J) ?_ (fun s ⟨k7, he⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r8, .r9, .r10, .r11]) (.block (tagArgs o))
        h).isSome = true := by rcases ho with rfl | rfl <;> exact ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨_, h₁⟩ ⟨_, h₂⟩ r hr => pin8 h₁ h₂ h₁.r8 h₂.r8 (by simpa using hr)) hc
  · obtain ⟨s₂, run₂, -, h0, h1, h2, h3, h12, hlr, hg₂, hrd₂, hwr₂, hsp₂⟩ := tagArgs_ok L ho he
    exact WP.of_runBlock ⟨s₂, run₂, k7, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        exact hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hsp₂ hrd₂ hwr₂,
      h0, h1, h2, h3, h12, hlr⟩
  · exact CT.ctr fun s₁ s₂ ⟨_, he₁, a0, a1, a2, a3, a12, alr⟩ ⟨_, he₂, b0, b1, b2, b3, b12, blr⟩ =>
      ⟨_, _, _, _, _, _, ctrTag_mk L ho he₁ a0 a1 a2 a3 a12 alr hR, ctrTag_mk L ho he₂ b0 b1 b2 b3 b12 blr hR,
        he₁.sp.trans he₂.sp.symm⟩

end

end VG.Proof.AesGcm.Arm
