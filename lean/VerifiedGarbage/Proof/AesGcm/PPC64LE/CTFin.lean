module

public import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTBase
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Fn
import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTAbsorb
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
import VerifiedGarbage.Proof.AesGcm.PPC64LE.FinTag
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Flush
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamFinish
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Tag
import VerifiedGarbage.Proof.AesGcm.PPC64LE.TextAbsorb
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Proof.Framework.PPC64LE.Run
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTBase
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Fn
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTAbsorb
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.FinTag
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Flush
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamFinish
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Tag
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.TextAbsorb
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Run
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Env
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Spec.TripleDes
public import VerifiedGarbage.Impl.AesGcm.PPC64LE
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Init
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Init
public import VerifiedGarbage.Proof.Aes.SboxSpec
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.PPC64LE.StraightK
public import VerifiedGarbage.Spec.Aes
meta import VerifiedGarbage.Impl.AesGcm.PPC64LE
meta import VerifiedGarbage.Proof.Aes.SboxSpec
meta import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
meta import VerifiedGarbage.Proof.Framework.Inline
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Call
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StraightK
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Spec.Aes
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Crypt
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.CryptOk
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Crypt
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CryptOk

/-! ### `AesGcm.PPC64LE.CTCrypt`, which this module and modules that import it used -/

section

/-!
# AES-GCM on PPC64LE: `crypt` is constant time

Untrusted: everything here is checked by Lean. As on ARMv7
(`Proof/AesGcm/Arm/CTCrypt.lean`): the invariants fix the context, the
state, `W`, the stack pointer, the number of rounds (in `r28`), the data's
address and length, and the length of the text so far modulo 16.
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE

/-- Before `crypt`. -/
def CrI (c st w sp : Addr) (R : Nat) (D : Addr) (n q : Nat) (s : State) : Prop :=
  ∃ V icb P, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧ P % 16 = q ∧ CrIn V sp R icb P D n s

/-- Part of the way: `j` bytes done. -/
def CrM (c st w sp : Addr) (R : Nat) (D : Addr) (n q j : Nat) (s : State) : Prop :=
  ∃ V icb P m₀, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧ P % 16 = q ∧ CrMid V sp R icb P D n m₀ j s

/-- Environments that agree on `r28` to `r31` agree in those registers. -/
theorem pinK {V₁ V₂ : Reg → BitVec 64} {sp : Addr} {s₁ s₂ : State} (e₁ : Env V₁ sp s₁) (e₂ : Env V₂ sp s₂)
    (h28 : V₁ .r28 = V₂ .r28) (h29 : V₁ .r29 = V₂ .r29) (h30 : V₁ .r30 = V₂ .r30) (h31 : V₁ .r31 = V₂ .r31)
    {r : Reg} (hr : r ∈ [Reg.r28, .r29, .r30, .r31]) : s₁.gpr r = s₂.gpr r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [e₁.r28, e₂.r28, h28]
  · rw [e₁.r29, e₂.r29, h29]
  · rw [e₁.r30, e₂.r30, h30]
  · rw [e₁.r31, e₂.r31, h31]

/-- `wholeWith split args call` is constant time from `I`: `split`, then
`args` and `call` once `r7` holds the same number of whole blocks `nb` in
both runs. -/
theorem wholeWith_ct {split args : List Instr} {call : Prog isa} {nb : Nat} {I J₁ J₂ : State → Prop}
    (hs : CT I (.block split)) (hsw : ∀ s, I s → WP isa (.block split) s J₁)
    (h7 : ∀ s, J₁ s → s.gpr .r7 = BitVec.ofNat 64 nb ∧ nb < 2 ^ 64) (ha : CT J₁ (.block args))
    (haw : ∀ s, J₁ s → WP isa (.block args) s J₂) (hc : nb ≠ 0 → CT J₂ call) :
    CT I (wholeWith split args call) :=
  CT.seq (J := J₁) hs hsw (CT.ite (decide (nb = 0)) (fun s hs => eval_zero (h7 s hs).1 (h7 s hs).2)
    (fun _ => CT.skip) fun hb => CT.seq (J := J₂) ha haw (hc (by simpa using hb)))

/-- Before `cryptTailWith to`, the source `S`, the destination `E` and the
number of bytes `k` being the same in both runs. -/
def TailI (to : Bool) (c st w sp : Addr) (R : Nat) (S E : Addr) (k : Nat) (s : State) : Prop :=
  ∃ V icb Q cph X, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧ TailIn to V sp R icb Q S E k cph X s

section
variable {c st w sp : Addr} (L : Lay c st w)
include L

theorem cryptWhole_ct {R : Nat} {D : Addr} {n q j : Nat} :
    CT (CrM c st w sp R D n q j) cryptWhole := by
  obtain ⟨nb, hnb⟩ : ∃ nb, nb = (n - j) / 16 := ⟨_, rfl⟩
  let J₁ : State → Prop := fun s => ∃ V : Reg → BitVec 64, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧
    V .r28 = BitVec.ofNat 64 R ∧ Env V sp s ∧ DataW (V .r29) (V .r30) (V .r31) s D n ∧ j ≤ n ∧
    (R = 10 ∨ R = 12 ∨ R = 14) ∧ s.gpr .r6 = D + BitVec.ofNat 64 j ∧ s.gpr .r7 = BitVec.ofNat 64 nb
  let J₂ : State → Prop := fun s => ∃ V : Reg → BitVec 64, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧
    Env V sp s ∧ DataW (V .r29) (V .r30) (V .r31) s D n ∧ j ≤ n ∧ (R = 10 ∨ R = 12 ∨ R = 14) ∧
    s.gpr .r3 = V .r29 ∧ s.gpr .r4 = BitVec.ofNat 64 R ∧ s.gpr .r5 = V .r30 + BitVec.ofNat 64 48 ∧
    s.gpr .r6 = D + BitVec.ofNat 64 j ∧ s.gpr .r7 = BitVec.ofNat 64 nb ∧
    s.gpr .r8 = V .r31 + BitVec.ofNat 64 512
  refine wholeWith_ct (J₁ := J₁) (J₂ := J₂) ?_ (fun s ⟨V, icb, P, m₀, h29, h30, h31, hP, hs⟩ => ?_)
    (fun s ⟨_, _, _, _, _, _, hd, _, _, _, h7⟩ => ⟨h7, by have := hd.ok.lt; omega_arith⟩) ?_
    (fun s ⟨V, h29, h30, h31, h28, he, hd, hj, hR, h6, h7⟩ => ?_) fun h0 => ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r24, .r25]) (.block splitCtr)
        h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, _, _, _, h₁⟩ ⟨_, _, _, _, _, _, _, _, h₂⟩ =>
      ⟨h₁.env.sp.trans h₂.env.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.r24, h₂.r24]
    · rw [h₁.r25, h₂.r25]
  · refine WP.mono (splitCtr_ok hs.le hs.data.ok.lt hs.r24 hs.r25) fun s₁ ⟨h6, h7, _, _, _, hg₁, hk₁⟩ => ?_
    exact ⟨V, h29, h30, h31, hs.r28, hs.env.keep (fun r hr => hg₁ r (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
      (by revert r; decide)) hk₁.sp hk₁.rd hk₁.wr, hs.data.of_eq hk₁.rd hk₁.wr, hs.le, hs.rounds, h6,
      by rw [h7, hnb]⟩
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r28, .r29, .r30, .r31])
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

theorem cryptTailWith_ct {to : Bool} {R : Nat} {S E : Addr} {k : Nat} :
    CT (TailI to c st w sp R S E k) (cryptTailWith to) := by
  refine CT.ite (decide (k = 0)) (fun s ⟨_, _, _, _, _, _, _, _, hs⟩ => eval_zero hs.r25 hs.src.lt)
    (fun _ => CT.skip) fun _ => ?_
  let J₁ : State → Prop := fun s => ∃ V : Reg → BitVec 64, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧
    Env V sp s ∧ (R = 10 ∨ R = 12 ∨ R = 14) ∧ s.gpr .r3 = V .r29 ∧ s.gpr .r4 = BitVec.ofNat 64 R ∧
    s.gpr .r5 = V .r30 + BitVec.ofNat 64 48 ∧ s.gpr .r6 = V .r30 + BitVec.ofNat 64 64 ∧
    s.gpr .r7 = BitVec.ofNat 64 1 ∧ s.gpr .r8 = V .r31 + BitVec.ofNat 64 512
  let J₂ : State → Prop := fun s => ∃ V s₀ cph, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧
    (to → s₀.gpr .r26 = E) ∧ TailKs V sp S k cph s₀ s
  refine CT.seq (J := J₂) (CT.seq (J := J₁) ?_ (fun s ⟨V, icb, Q, cph, X, h29, h30, h31, hs⟩ => ?_) ?_)
    (fun s ⟨V, icb, Q, cph, X, h29, h30, h31, hs⟩ =>
      WP.mono (tailKs_ok (L.v h29 h30 h31) hs) fun s' h => ⟨V, s, cph, h29, h30, h31, hs.r26, h⟩) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r28, .r29, .r30, .r31])
        (.block tailArgs) h).isSome = true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, a29, a30, a31, h₁⟩ ⟨_, _, _, _, _, b29, b30, b31, h₂⟩ =>
      ⟨h₁.env.sp.trans h₂.env.sp.symm, fun r hr => pinK h₁.env h₂.env (h₁.r28.trans h₂.r28.symm)
        (a29.trans b29.symm) (a30.trans b30.symm) (a31.trans b31.symm) hr⟩) hc
  · refine WP.mono (tailArgs_ok hs.env hs.r28) fun s₂ ⟨_, a3, a4, a5, a6, a7, a8, hg₂, hk₂⟩ => ?_
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
  · cases to
    · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r24, .r25, .r30])
          (.seq (.block (xorArgs false)) (xorLoopWith false)) h).isSome = true := ⟨_, by taint_decide⟩
      refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, a30, _, _, h₁⟩ ⟨_, _, _, _, b30, _, _, h₂⟩ =>
        ⟨h₁.env.sp.trans h₂.env.sp.symm, fun r hr => ?_⟩) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h₁.r24, h₂.r24]
      · rw [h₁.r25, h₂.r25]
      · rw [h₁.env.r30, h₂.env.r30, a30, b30]
    · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r24, .r25, .r26, .r30])
          (.seq (.block (xorArgs true)) (xorLoopWith true)) h).isSome = true := ⟨_, by taint_decide⟩
      refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, a30, _, e₁, h₁⟩ ⟨_, _, _, _, b30, _, e₂, h₂⟩ =>
        ⟨h₁.env.sp.trans h₂.env.sp.symm, fun r hr => ?_⟩) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h₁.r24, h₂.r24]
      · rw [h₁.r25, h₂.r25]
      · rw [h₁.r26, h₂.r26, e₁ rfl, e₂ rfl]
      · rw [h₁.env.r30, h₂.env.r30, a30, b30]

theorem cryptTail_ct {R : Nat} {D : Addr} {n q j : Nat} :
    CT (CrM c st w sp R D n q j) cryptTail :=
  (cryptTailWith_ct L (to := false) (S := D + BitVec.ofNat 64 j) (E := D + BitVec.ofNat 64 j) (k := n - j)).mono
    fun _ ⟨V, icb, _, _, h29, h30, h31, _, hs⟩ =>
      ⟨V, icb, _, _, _, h29, h30, h31, hs.tailIn (hs.ciph (L.v h29 h30 h31))⟩

theorem crypt_ct {R : Nat} {D : Addr} {n q : Nat} :
    CT (CrI c st w sp R D n q) crypt := by
  refine CT.ite (decide (n = 0)) (fun s ⟨_, _, _, _, _, _, _, hs⟩ => eval_zero hs.r25 hs.data.ok.lt)
    (fun _ => CT.skip) fun hb => ?_
  have h0 : n ≠ 0 := by simpa using hb
  let j₁ := if q = 0 then 0 else min (16 - q) n
  refine CT.seq (J := CrM c st w sp R D n q j₁) ?_
    (fun s ⟨V, icb, P, h29, h30, h31, hP, hs⟩ => WP.mono (cryptFill_ok hs h0) fun s' ⟨j, hj, hm⟩ =>
      ⟨V, icb, P, s.mem, h29, h30, h31, hP, by subst hj; rw [hP] at hm; exact hm⟩) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r24, .r25, .r26, .r30]) cryptFill
        h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, a30, _, hP₁, h₁⟩ ⟨_, _, _, _, b30, _, hP₂, h₂⟩ =>
      ⟨h₁.env.sp.trans h₂.env.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₁.r24, h₂.r24]
    · rw [h₁.r25, h₂.r25]
    · rw [h₁.r26, h₂.r26, hP₁, hP₂]
    · rw [h₁.env.r30, h₂.env.r30, a30, b30]
  refine CT.seq (J := CrM c st w sp R D n q (j₁ + 16 * ((n - j₁) / 16))) (cryptWhole_ct L)
    (fun s ⟨V, icb, P, m₀, h29, h30, h31, hP, hs⟩ =>
      WP.mono (cryptWhole_ok (L.v h29 h30 h31) hs (hs.ciph (L.v h29 h30 h31))) fun s' ⟨j, hj, hm, _⟩ =>
        ⟨V, icb, P, m₀, h29, h30, h31, hP, by subst hj; exact hm⟩) (cryptTail_ct L)

end

end VG.Proof.AesGcm.PPC64LE

end

end

/-! ### `AesGcm.PPC64LE.InitCT`, which this module and modules that import it used -/

section

/-!
# AES-GCM on PPC64LE: `vg_aes_gcm_init` is constant time

Untrusted: everything here is checked by Lean. The code around the calls by
the taint analysis, from the public arguments and the registers the
correctness proof pins; the calls by their callees' proofs, with the
arguments those proofs give.
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE

theorem initPre_taint : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (.block initPre) h).isSome = true := ⟨_, by taint_decide⟩

theorem initArgs_taint : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r28, .r29, .r31])
    (.block initArgs) h).isSome = true := ⟨_, by taint_decide⟩

theorem restore_taint : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r31])
    (.block restore) h).isSome = true := ⟨_, by taint_decide⟩

theorem init_ct : ConstantTime isa initPPC64LE.pre initPPC64LE.pub init := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q3, q4, q5, q6, qsp⟩ := hq
  have hpre₁ := h₁
  obtain ⟨-, -, -, -, dcs, fc, -, hlen⟩ := hpre₁
  generalize hK : σ₁.gpr .r3 = K at *
  generalize hL : σ₁.gpr .r4 = KL at *
  generalize hC : σ₁.gpr .r5 = C at *
  generalize hW : σ₁.gpr .r6 = W at *
  generalize hSP : σ₁.sp = SP at *
  have hR := rounds_ok hlen
  let R := Spec.Aes.rounds (KL.toNat / 4)
  let I₀ : State → Prop := fun s => initPPC64LE.pre s ∧ s.gpr .r3 = K ∧ s.gpr .r4 = KL ∧ s.gpr .r5 = C ∧
    s.gpr .r6 = W ∧ s.sp = SP
  let I₁ : State → Prop := fun s => KeyCall s K KL.toNat C (W + BitVec.ofNat 64 512) ∧
    s.gpr .r28 = BitVec.ofNat 64 R ∧ s.gpr .r29 = C ∧ s.gpr .r31 = W ∧ s.sp = SP ∧
    s.wr = [⟨C, 256⟩, ⟨W, 2560⟩]
  let I₂ : State → Prop := fun s => s.gpr .r28 = BitVec.ofNat 64 R ∧ s.gpr .r29 = C ∧ s.gpr .r31 = W ∧
    s.sp = SP ∧ s.wr = [⟨C, 256⟩, ⟨W, 2560⟩]
  let I₃ : State → Prop := fun s => CtrCall s C (W + BitVec.ofNat 64 96) (C + BitVec.ofNat 64 240)
    (W + BitVec.ofNat 64 512) R 1 ∧ s.gpr .r31 = W ∧ s.sp = SP
  let I₄ : State → Prop := fun s => s.gpr .r31 = W ∧ s.sp = SP
  refine ⟨I₀, ⟨h₁, hK, hL, hC, hW, hSP⟩, ⟨h₂, q3.symm, q4.symm, q5.symm, q6.symm, qsp.symm⟩, ?_⟩
  refine CT.seq (J := I₁) ?_ (fun s ⟨hs, e3, e4, e5, e6, esp⟩ => WP.mono (is1_wp hs) fun s₁ h1 => ?_) ?_
  · obtain ⟨_, hc⟩ := initPre_taint
    exact CT.taintEq (I := I₀) _ (fun r => if r = .r3 then K else if r = .r4 then KL else
      if r = .r5 then C else W) SP (fun s ⟨_, e3, e4, e5, e6, esp⟩ => ⟨esp, by simp [e3, e4, e5, e6]⟩) hc
  · have kc := init_kc hs h1
    rw [e3, e4, e5, e6] at kc
    obtain ⟨-, hwr, -⟩ := hs
    refine ⟨kc, by rw [h1.r28, initR, e4], by rw [h1.r29, e5], by rw [h1.r31, e6],
      by rw [h1.keeps.sp, esp], by rw [h1.keeps.wr, hwr, e5, e6]⟩
  refine CT.seq (J := I₂) ?_ (fun s ⟨kc, e28, e29, e31, esp, ewr⟩ => WP.mono (key_call kc) fun s₂ kp =>
    ⟨by rw [kp.saved _ (by decide), e28], by rw [kp.saved _ (by decide), e29],
      by rw [kp.saved _ (by decide), e31], by rw [kp.sp, esp], by rw [kp.wr, ewr]⟩) ?_
  · exact CT.key fun s₁ s₂ h₁ h₂ => ⟨_, _, _, _, h₁.1, h₂.1, h₁.2.2.2.2.1.trans h₂.2.2.2.2.1.symm⟩
  refine CT.seq (J := I₃) ?_ (fun s ⟨e28, e29, e31, esp, ewr⟩ =>
    WP.mono (initArgs_ok e29 e31 e28 (by rw [ewr]; exact covers_mem (by simp))
      (by rw [ewr]; exact covers_mem (by simp))) fun s₃ ⟨_, a3, a4, a5, a6, a7, a8, hg₃, hk₃⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := initArgs_taint
    exact CT.taintEq (I := I₂) _ (fun r => if r = .r28 then BitVec.ofNat 64 R else if r = .r29 then C else W)
      SP (fun s ⟨e28, e29, e31, esp, _⟩ => ⟨esp, by simp [e28, e29, e31]⟩) hc
  · have hW₃ : Covers [⟨W, 2560⟩] s₃.wr := by rw [hk₃.wr, ewr]; exact covers_mem (by simp)
    have hC₃ : Covers [⟨C, 256⟩] s₃.wr := by rw [hk₃.wr, ewr]; exact covers_mem (by simp)
    exact ⟨init_cc dcs fc hR hW₃ hC₃ a3 a4 a5 a6 a7 a8,
      by rw [hg₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), e31],
      by rw [hk₃.sp, esp]⟩
  refine CT.seq (J := I₄) ?_ (fun s ⟨cc, e31, esp⟩ => WP.mono (ctr_call cc) fun s₄ cp =>
    ⟨by rw [cp.saved _ (by decide), e31], by rw [cp.sp, esp]⟩) ?_
  · exact CT.ctr fun s₁ s₂ h₁ h₂ => ⟨_, _, _, _, _, _, h₁.1, h₂.1, h₁.2.2.trans h₂.2.2.symm⟩
  · obtain ⟨_, hc⟩ := restore_taint
    exact CT.taintEq (I := I₄) _ (fun _ => W) SP (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

end VG.Proof.AesGcm.PPC64LE

end

end

/-!
# AES-GCM on PPC64LE: `tag`, `finTag` and `vg_aes_gcm_stream_finish` are constant time

Untrusted: everything here is checked by Lean. As on ARMv7
(`Proof/AesGcm/Arm/CTOpen.lean`): the invariants fix the context, the state,
`W`, the stack pointer, the number of rounds (`r28`), the lengths of the
additional data (`r22`) and of the text (`r23`), and the tag's address
(`r20`), all held in registers the environment pins.
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- An environment with `R` rounds in `r28`. -/
def EnvR (c st w sp : Addr) (R : Nat) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧ V .r28 = BitVec.ofNat 64 R ∧ Env V sp s

/-- Before `finTag`: also `aad_len` (`A`) and `text_len` (`T`) in `r22` and `r23`. -/
def FTI (c st w sp : Addr) (R : Nat) (A T : BitVec 64) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧ V .r28 = BitVec.ofNat 64 R ∧ V .r22 = A ∧
    V .r23 = T ∧ Env V sp s

section
variable {c st w sp : Addr} (L : Lay c st w)
include L

theorem tag_ct [VG.Proof.Gcm.PPC64LE.GhashLaw] {o R : Nat} (ho : o = 0 ∨ o = 112) (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    CT (EnvR c st w sp R) (tag o) := by
  refine CT.seq (J := EnvR c st w sp R)
    ((lens_ct L (yo := 16) (.inr rfl)).mono fun s ⟨V, a, b, d, _, he⟩ => ⟨V, a, b, d, he⟩)
    (fun s ⟨V, a, b, d, e, he⟩ => WP.mono (lens_ok (L.v a b d) (.inr rfl) he rfl) fun s' h =>
      ⟨V, a, b, d, e, h.1⟩) ?_
  let J : State → Prop := fun s => ∃ V : Reg → BitVec 64, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧
    Env V sp s ∧ s.gpr .r3 = V .r29 ∧ s.gpr .r4 = BitVec.ofNat 64 R ∧ s.gpr .r5 = V .r30 ∧
    s.gpr .r6 = V .r31 + BitVec.ofNat 64 o ∧ s.gpr .r7 = BitVec.ofNat 64 1 ∧
    s.gpr .r8 = V .r31 + BitVec.ofNat 64 512
  refine CT.seq (J := J) ?_ (fun s ⟨V, a, b, d, e, he⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r28, .r29, .r30, .r31])
        (.block (tagArgs o)) h).isSome = true := by rcases ho with rfl | rfl <;> exact ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨_, a₁, b₁, d₁, e₁, h₁⟩ ⟨_, a₂, b₂, d₂, e₂, h₂⟩ =>
      ⟨h₁.sp.trans h₂.sp.symm, fun r hr => pinK h₁ h₂ (e₁.trans e₂.symm) (a₁.trans a₂.symm)
        (b₁.trans b₂.symm) (d₁.trans d₂.symm) hr⟩) hc
  · refine WP.mono (tagArgs_ok (o := o) (by omega_using [ho]) (by omega_using [ho]) he)
      fun s' ⟨_, a3, a4, a5, a6, a7, a8, hg, hk⟩ => ⟨V, a, b, d, he.keep (fun r hr => hg r (by revert r; decide)
        (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
        (by revert r; decide)) hk.sp hk.rd hk.wr, a3, by rw [a4, e], a5, a6, a7, a8⟩
  · exact CT.ctr fun s₁ s₂ ⟨V₁, a₁, b₁, d₁, e₁, a3, a4, a5, a6, a7, a8⟩
      ⟨V₂, a₂, b₂, d₂, e₂, b3, b4, b5, b6, b7, b8⟩ => by
      have g₁ := ctrTag_mk (L.v a₁ b₁ d₁) ho e₁ a3 a4 a5 a6 a7 a8 hR
      have g₂ := ctrTag_mk (L.v a₂ b₂ d₂) ho e₂ b3 b4 b5 b6 b7 b8 hR
      rw [a₁, b₁, d₁] at g₁
      rw [a₂, b₂, d₂] at g₂
      exact ⟨_, _, _, _, _, _, g₁, g₂, e₁.sp.trans e₂.sp.symm⟩

/-- The number of buffered bytes `finTag` pads: of the text if there is any,
else of the additional data. -/
abbrev finQ (A T : BitVec 64) : Nat := if T.toNat = 0 then A.toNat % 16 else T.toNat % 16

theorem finTag_ct [VG.Proof.Gcm.PPC64LE.GhashLaw] {o R : Nat} (ho : o = 0 ∨ o = 112) (hR : R = 10 ∨ R = 12 ∨ R = 14) {A T : BitVec 64} :
    CT (FTI c st w sp R A T) (finTag o) := by
  have hq : finQ A T < 16 := by simp only [finQ]; split <;> exact Nat.mod_lt _ (by decide)
  let J : State → Prop := fun s => FTI c st w sp R A T s ∧ s.gpr .r26 = BitVec.ofNat 64 (finQ A T)
  refine CT.seq (J := J) ?_ (fun s ⟨V, a, b, d, e, f, g, he⟩ => ?_) ?_
  · refine CT.ite (decide (T.toNat = 0)) (fun s ⟨_, _, _, _, _, _, g, he⟩ =>
      eval_zero (by rw [he.ofNat (r := .r23) (by decide), g]) T.isLt) (fun _ => ?_) (fun _ => ?_)
    · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r22])
          (.block [.li .r0 15, .logic .and .r26 .r22 .r0]) h).isSome = true := ⟨_, by taint_decide⟩
      refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, f₁, _, h₁⟩ ⟨_, _, _, _, _, f₂, _, h₂⟩ =>
        ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
      simp only [List.mem_singleton] at hr; subst hr
      rw [h₁.fr _ (by decide), h₂.fr _ (by decide), f₁, f₂]
    · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r23])
          (.block [.li .r0 15, .logic .and .r26 .r23 .r0]) h).isSome = true := ⟨_, by taint_decide⟩
      refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, _, g₁, h₁⟩ ⟨_, _, _, _, _, _, g₂, h₂⟩ =>
        ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
      simp only [List.mem_singleton] at hr; subst hr
      rw [h₁.fr _ (by decide), h₂.fr _ (by decide), g₁, g₂]
  · have h22 := he.fr .r22 (by decide)
    have h23 := he.fr .r23 (by decide)
    refine WP.ite (decide (T.toNat = 0)) (eval_zero (by rw [he.ofNat (r := .r23) (by decide), g]) T.isLt)
      (fun ht => ?_) (fun hf => ?_)
    · have hand := and15 (V .r22)
      have hQ : finQ A T = (V .r22).toNat % 16 := by simp only [finQ, f]; simp at ht; simp [ht]
      have h₃ : WP isa (.block [.li .r0 15, .logic .and .r26 .r22 .r0]) s fun s₃ =>
          s₃.gpr .r26 = BitVec.ofNat 64 ((V .r22).toNat % 16) ∧
            (∀ r, r ≠ .r0 → r ≠ .r26 → s₃.gpr r = s.gpr r) ∧ Keeps s s₃ := by
        crun [h22, hand]
        exact ⟨fun r a b => by simp [a, b], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
      exact WP.mono h₃ fun s₃ ⟨h26, hg, hk⟩ => ⟨⟨V, a, b, d, e, f, g, he.keep (fun r hr => hg r
        (by revert r; decide) (by revert r; decide)) hk.sp hk.rd hk.wr⟩, by rw [h26, hQ]⟩
    · have hand := and15 (V .r23)
      have hQ : finQ A T = (V .r23).toNat % 16 := by simp only [finQ, g]; simp at hf; simp [hf]
      have h₃ : WP isa (.block [.li .r0 15, .logic .and .r26 .r23 .r0]) s fun s₃ =>
          s₃.gpr .r26 = BitVec.ofNat 64 ((V .r23).toNat % 16) ∧
            (∀ r, r ≠ .r0 → r ≠ .r26 → s₃.gpr r = s.gpr r) ∧ Keeps s s₃ := by
        crun [h23, hand]
        exact ⟨fun r a b => by simp [a, b], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
      exact WP.mono h₃ fun s₃ ⟨h26, hg, hk⟩ => ⟨⟨V, a, b, d, e, f, g, he.keep (fun r hr => hg r
        (by revert r; decide) (by revert r; decide)) hk.sp hk.rd hk.wr⟩, by rw [h26, hQ]⟩
  refine CT.seq (J := FTI c st w sp R A T)
    ((flush_ct L (yo := 16) (.inr rfl) hq).mono fun s ⟨⟨V, a, b, d, _, _, _, he⟩, h26⟩ => ⟨⟨V, a, b, d, he⟩, h26⟩)
    (fun s ⟨⟨V, a, b, d, e, f, g, he⟩, h26⟩ => WP.mono (flush_ok (L.v a b d) (yo := 16) (.inr rfl)
      (x := List.replicate (finQ A T) 0) ⟨he, rfl⟩ (by simp [h26, Nat.mod_eq_of_lt hq])) fun s' fl =>
        ⟨V, a, b, d, e, f, g, fl.env⟩) ?_
  refine CT.seq (J := EnvR c st w sp R) ?_ (fun s ⟨V, a, b, d, e, f, g, he⟩ => ?_)
    ((tag_ct L ho hR).mono fun _ h => h)
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r22, .r23])
        (.block [mov .r24 .r22, mov .r26 .r23]) h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, f₁, g₁, h₁⟩ ⟨_, _, _, _, _, f₂, g₂, h₂⟩ =>
      ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), f₁, f₂]
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), g₁, g₂]
  · have h₅ : WP isa (.block [mov .r24 .r22, mov .r26 .r23]) s fun s₅ =>
        (∀ r, r ≠ .r24 → r ≠ .r26 → s₅.gpr r = s.gpr r) ∧ Keeps s s₅ := by
      crun [mov, BitVec.or_self]
      exact ⟨fun r a b => by simp [a, b], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
    exact WP.mono h₅ fun s₅ ⟨hg, hk⟩ => ⟨V, a, b, d, e, he.keep (fun r hr => hg r (by revert r; decide)
      (by revert r; decide)) hk.sp hk.rd hk.wr⟩

end

/-- In `finish`, after the entry: also the tag's address `Tp` in `r20`, which
the state may write. -/
def FinI (c st w sp : Addr) (R : Nat) (A T Tp : BitVec 64) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧ V .r28 = BitVec.ofNat 64 R ∧ V .r22 = A ∧
    V .r23 = T ∧ V .r20 = Tp ∧ Env V sp s ∧ Covers [⟨Tp, 16⟩] s.wr

theorem finEntry_taint : ∃ h, (VG.Taint.check VG.PPC64LE.taint
    (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8, .r9]) (.block finEntry) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem tagOut_taint : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r20, .r31]) (.block tagOut)
    h).isSome = true := ⟨_, by taint_decide⟩

theorem streamFinish_ct [VG.Proof.Gcm.PPC64LE.GhashLaw] : ConstantTime isa streamFinishPPC64LE.pre streamFinishPPC64LE.pub streamFinish := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q3, q4, q5, q6, q7, q8, q9, qsp⟩ := hq
  have h₁' : finPre σ₁ := h₁
  have L := finLay h₁'
  have hR : (σ₁.gpr .r4).toNat = 10 ∨ (σ₁.gpr .r4).toNat = 12 ∨ (σ₁.gpr .r4).toNat = 14 :=
    h₁'.2.2.2.2.2.2.2.2.2.2.2.2
  have dtw : (⟨σ₁.gpr .r8, 16⟩ : Region).Disjoint ⟨σ₁.gpr .r9, 16⟩ :=
    h₁'.2.2.2.2.2.2.2.1.sub_right (Region.sub_prefix (by decide))
  let I₀ : State → Prop := fun s => finPre s ∧ s.gpr .r3 = σ₁.gpr .r3 ∧ s.gpr .r4 = σ₁.gpr .r4 ∧
    s.gpr .r5 = σ₁.gpr .r5 ∧ s.gpr .r6 = σ₁.gpr .r6 ∧ s.gpr .r7 = σ₁.gpr .r7 ∧ s.gpr .r8 = σ₁.gpr .r8 ∧
    s.gpr .r9 = σ₁.gpr .r9 ∧ s.sp = σ₁.sp
  refine ⟨I₀, ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨h₂, q3.symm, q4.symm, q5.symm, q6.symm, q7.symm,
    q8.symm, q9.symm, qsp.symm⟩, ?_⟩
  let FI := FinI (σ₁.gpr .r3) (σ₁.gpr .r5) (σ₁.gpr .r9) σ₁.sp (σ₁.gpr .r4).toNat (σ₁.gpr .r6) (σ₁.gpr .r7)
    (σ₁.gpr .r8)
  refine CT.seq (J := FI) ?_ (fun s ⟨hs, e3, e4, e5, e6, e7, e8, e9, esp⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := finEntry_taint
    exact CT.taintEq (I := I₀) _ σ₁.gpr σ₁.sp (fun s ⟨_, e3, e4, e5, e6, e7, e8, e9, esp⟩ =>
      ⟨esp, by simp [e3, e4, e5, e6, e7, e8, e9]⟩) hc
  · refine WP.mono (fin1_wp (fin_W hs)) fun s₁ h1 => ?_
    have hT : Covers [⟨s.gpr .r8, 16⟩] s₁.wr := by
      rw [h1.en.keeps.wr, hs.2.1]; exact covers_mem (by simp)
    refine ⟨s₁.gpr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h1.r29, e3]
    · rw [h1.r30, e5]
    · rw [h1.r31, e9]
    · rw [h1.r28, e4, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [h1.r22, e6]
    · rw [h1.r23, e7]
    · rw [h1.r20, e8]
    · rw [← esp]; exact fin_env hs h1
    · rw [← e8]; exact hT
  refine CT.seq (J := FI)
    ((finTag_ct L (o := 0) (.inl rfl) hR).mono fun s ⟨V, a, b, d, e, f, g, _, he, _⟩ => ⟨V, a, b, d, e, f, g, he⟩)
    (fun s ⟨V, a, b, d, e, f, g, i, he, hT⟩ => WP.mono (WP.with_rdwr (finTag_ok (L.v a b d) (o := 0) (.inl rfl)
      (a := List.replicate ((σ₁.gpr .r6).toNat % 16) 0) (ct := List.replicate (σ₁.gpr .r7).toNat 0) he e hR rfl
      (by simp [f]) (by simp [g]))) fun s' ⟨fo, _, wr, _⟩ =>
        ⟨V, a, b, d, e, f, g, i, fo.env, by rw [wr]; exact hT⟩) ?_
  refine CT.seq (J := fun s => s.gpr .r31 = σ₁.gpr .r9 ∧ s.sp = σ₁.sp) ?_
    (fun s ⟨V, a, b, d, e, f, g, i, he, hT⟩ => WP.mono (tagOut_ok he (by rw [i]; exact hT)
      (by rw [i, d]; exact dtw)) fun s' ⟨_, _, hg, hk⟩ =>
        ⟨by rw [hg _ (by decide), he.r31, d], by rw [hk.sp, he.sp]⟩) ?_
  · obtain ⟨_, hc⟩ := tagOut_taint
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, d₁, _, _, _, i₁, h₁, _⟩ ⟨_, _, _, d₂, _, _, _, i₂, h₂, _⟩ =>
      ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), i₁, i₂]
    · rw [h₁.r31, h₂.r31, d₁, d₂]
  obtain ⟨_, hc⟩ := restore_taint
  exact CT.taintEq _ (fun _ => σ₁.gpr .r9) σ₁.sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

end VG.Proof.AesGcm.PPC64LE
