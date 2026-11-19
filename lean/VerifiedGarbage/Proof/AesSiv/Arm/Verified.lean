module

public import VerifiedGarbage.Proof.AesSiv.Scratch
import VerifiedGarbage.Proof.AesSiv.Arm.CTInit
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Impl.StackScratch.Arm
import VerifiedGarbage.Proof.Framework.Arm.RegScratch
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.AesSiv.Arm.Ctr
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.AesSiv.Arm.FinishLong
meta import VerifiedGarbage.Proof.AesSiv.Arm.Ctr
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.AesSiv.Arm.FinishLong
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Spec.Ccm
import VerifiedGarbage.Proof.AesCcm.Arm.Seal
import VerifiedGarbage.Proof.AesGcm.Arm.Compare
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Proof.AesGcm.Arm.Fn
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Spec.Ccm
meta import VerifiedGarbage.Proof.AesCcm.Arm.Seal
meta import VerifiedGarbage.Proof.AesGcm.Arm.Compare
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.AesGcm.Arm.Fn
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.AesSiv.Arm
public import VerifiedGarbage.Proof.AesGcm.Arm.CTBase
public import VerifiedGarbage.Proof.AesSiv.Arm.CmacOf
meta import VerifiedGarbage.Impl.AesSiv.Arm
meta import VerifiedGarbage.Proof.AesGcm.Arm.CTBase
meta import VerifiedGarbage.Proof.AesSiv.Arm.CmacOf
import VerifiedGarbage.Proof.AesGcm.Arm.Run
meta import VerifiedGarbage.Proof.AesGcm.Arm.Run
public import VerifiedGarbage.Proof.AesSiv.Long
meta import VerifiedGarbage.Proof.AesSiv.Long
import Batteries.Logic
import VerifiedGarbage.Proof.AesGcm.Arm.Env
import VerifiedGarbage.Proof.AesGcm.Arm.Loops
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Arm.Bytes
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Sha256.Stream
meta import Batteries.Logic
meta import VerifiedGarbage.Proof.AesGcm.Arm.Env
meta import VerifiedGarbage.Proof.AesGcm.Arm.Loops
meta import VerifiedGarbage.Proof.Cmac.Mem
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Bytes
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Gcm.Stream
meta import VerifiedGarbage.Proof.Sha256.Stream

/-! ### `AesSiv.Arm.CTEnc`, which only this module used -/

section

/-! ### `AesSiv.Arm.CTCtr`, which only this module used -/

section

/-! ### `AesSiv.Arm.CTFinish`, which this module and modules that import it used -/

section

/-! ### `AesSiv.Arm.CTMac`, which this module and modules that import it used -/

section

/-!
# AES-SIV on ARMv7: the CMAC of a string is constant time

Untrusted: everything here is checked by Lean. Two runs of `cmacOf` on
strings at the same address and of the same length (`MPre`) leak the same:
the blocks between the calls the taint analysis checks from the registers
that hold the string's address and length, the context, the rounds and `W`;
the calls get the same arguments in both runs (`upd_rel`, `fin_rel`), which
the correctness lemmas give.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm VG.Impl.AesSiv.Arm
open VG.Proof.AesGcm.Arm (CT)
open VG.Proof.AesCcm.Arm (UArgs upd_call upd_rel)
open VG.Impl.AesGcm.Arm (imm)

/-- The registers an environment fixes. -/
theorem env_eq {c w sp : BitVec 32} {R : Nat} {s₁ s₂ : State} (h₁ : Env c w sp R s₁) (h₂ : Env c w sp R s₂)
    {r : Reg} (hr : r = .r9 ∨ r = .r10 ∨ r = .r11) : s₁.gpr r = s₂.gpr r := by
  rcases hr with rfl | rfl | rfl
  · rw [h₁.r9, h₂.r9]
  · rw [h₁.r10, h₂.r10]
  · rw [h₁.r11, h₂.r11]

/-- Before `cmacOf`: the string, `n` bytes at `P`, in `r6` and `r5`. -/
structure MPre (c w sp : BitVec 32) (R : Nat) (P : BitVec 32) (n : Nat) (s : State) : Prop where
  env : Env c w sp R s
  buf : Buf w sp s P n
  r6 : s.gpr .r6 = P
  r5 : s.gpr .r5 = BitVec.ofNat 32 n

/-- What the bytes after the chained ones are, as a buffer. -/
theorem Buf.rest {w sp P : BitVec 32} {n : Nat} {s : State} (hP : Buf w sp s P n) :
    Buf w sp s (P + BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 n)) (n - Spec.Cmac.chainedLen 16 n) := by
  have hcl := chainedLen_le n
  by_cases h0 : n - Spec.Cmac.chainedLen 16 n = 0
  · have : n = 0 := by
      by_contra hne; have := chainedLen_ne hne; omega_using [h0, this]
    subst this
    rw [chainedLen_zero, show P + BitVec.ofNat 32 0 = P from BitVec.add_zero P]
    exact hP
  · exact hP.sub (j := Spec.Cmac.chainedLen 16 n) (k := n - Spec.Cmac.chainedLen 16 n) (by omega_using [hcl]) (by omega_using [h0])

section
variable {c w sp : BitVec 32} {R : Nat} (L : Lay c w sp) (hR : R = 10 ∨ R = 12 ∨ R = 14)
include L hR

/-- Between the calls of `cmacOf`. -/
structure MMid (c w sp : BitVec 32) (R : Nat) (P : BitVec 32) (n : Nat) (s : State) : Prop where
  pre : MPre c w sp R P n s
  r4 : s.gpr .r4 = BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 n)

theorem cmacOf_ct {P : BitVec 32} {n : Nat} (hn : n < 2 ^ 32) : CT (MPre c w sp R P n) (cmacOf stOff) := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r5, .r6, .r9, .r10, .r11])
      (cmacPre stOff) h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r4, .r5, .r6, .r9, .r10, .r11])
      (.block (cmacMid stOff)) h).isSome = true := ⟨_, by taint_decide⟩
  refine CT.seq (J := fun s => MMid c w sp R P n s ∧
      UArgs s c (w + BitVec.ofNat 32 stOff) P (w + BitVec.ofNat 32 256) R (Spec.Cmac.chainedLen 16 n / 16))
    (CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h₁.r5, h₂.r5]
      · rw [h₁.r6, h₂.r6]
      all_goals exact env_eq h₁.env h₂.env (by simp)) hA)
    (fun s h => WP.mono (cmacPre_ok L h.env hR h.buf hn h.r6 h.r5) fun s' ⟨he, rd, wr, g, h4, U, _⟩ =>
      ⟨⟨⟨he, h.buf.of_eq rd wr, by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), h.r6], by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), h.r5]⟩, h4⟩, U⟩) ?_
  refine CT.seq (J := MMid c w sp R P n)
    (upd_rel fun s₁ s₂ hh => ⟨hh.1.2, hh.2.2, hh.1.1.pre.env.sp, hh.2.1.pre.env.sp⟩)
    (fun s h => WP.mono (upd_call h.2) fun s' h' => by
      have g : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r := h'.saved
      exact ⟨⟨h.1.pre.env.of_saved h'.saved h'.sp h'.rd h'.wr, h.1.pre.buf.of_eq h'.rd h'.wr,
        by rw [g _ (by decide) (by decide), h.1.pre.r6], by rw [g _ (by decide) (by decide), h.1.pre.r5]⟩,
        by rw [g _ (by decide) (by decide), h.1.r4]⟩) ?_
  refine CT.seq (J := fun s => Env c w sp R s ∧ FArgs s c (w + BitVec.ofNat 32 stOff)
      (P + BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 n)) (w + BitVec.ofNat 32 256) (n - Spec.Cmac.chainedLen 16 n) R)
    (CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [h₁.r4, h₂.r4]
      · rw [h₁.pre.r5, h₂.pre.r5]
      · rw [h₁.pre.r6, h₂.pre.r6]
      all_goals exact env_eq h₁.pre.env h₂.pre.env (by simp)) hB)
    (fun s h => by
      obtain ⟨s', run, he, _, _, F⟩ := cmacMid_ok L h.pre.env hR hn h.pre.buf.rest h.r4 h.pre.r5 h.pre.r6
      exact WP.of_runBlock ⟨s', run, he, F⟩) ?_
  exact fin_rel fun s₁ s₂ hh => ⟨hh.1.2, hh.2.2, hh.1.1.sp, hh.2.1.sp⟩

/-! ## S2V over the components -/

/-- The descriptors' words in `m` are `dsc`, the same in both runs. -/
def DescEq (m : Mem) (a : BitVec 32) (N : Nat) (dsc : Nat → Nat → BitVec 32) : Prop :=
  ∀ i < N, ∀ j < 2, descW m a i j = dsc i j

/-- Before component `i` (and, for `i = N`, after the last), in one run. -/
def AI (c w sp a : BitVec 32) (R N : Nat) (dsc : Nat → Nat → BitVec 32) (i : Nat) (s : State) : Prop :=
  ∃ m₀ σ, AInv c w sp a R N m₀ σ i s ∧ DescEq m₀ a N dsc

/-- One component. -/
theorem adBody_ct {a : BitVec 32} {N : Nat} {dsc : Nat → Nat → BitVec 32} {i : Nat} (hi : i < N) :
    CT (AI c w sp a R N dsc i) (.seq (.block adNext) (.seq (cmacOf stOff) (.block adStep))) := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r8]) (.block adNext) h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r7, .r8, .r9, .r10, .r11])
      (.block adStep) h).isSome = true := ⟨_, by taint_decide⟩
  refine CT.seq (J := fun s => MPre c w sp R (dsc i 0) (dsc i 1).toNat s ∧
      s.gpr .r8 = a + BitVec.ofNat 32 (8 * i) ∧ s.gpr .r7 = BitVec.ofNat 32 (N - i))
    (CT.taint _ (fun s₁ s₂ ⟨_, _, h₁, _⟩ ⟨_, _, h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r8, h₂.r8]) hA)
    (fun s ⟨m₀, σ, h, hd⟩ => WP.mono (adNext_ok h.ads hi h.frame h.r8) fun s₁ ⟨h6, h5, g, k⟩ => by
      have hb := (h.ads.comp i hi).of_eq k.rd k.wr
      rw [hd i hi 0 (by decide), hd i hi 1 (by decide)] at hb
      exact ⟨⟨h.env.keep (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> exact g _ (by decide) (by decide)) k.sp k.rd k.wr, hb,
        by rw [h6, hd i hi 0 (by decide)],
        by rw [h5, hd i hi 1 (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩,
        by rw [g _ (by decide) (by decide), h.r8], by rw [g _ (by decide) (by decide), h.r7]⟩) ?_
  refine CT.seq (J := fun s => Env c w sp R s ∧ s.gpr .r8 = a + BitVec.ofNat 32 (8 * i) ∧
      s.gpr .r7 = BitVec.ofNat 32 (N - i))
    ((cmacOf_ct L hR (BitVec.isLt _)).mono fun s h => h.1)
    (fun s h => WP.mono (cmacOf_ok L h.1.env hR h.1.buf (BitVec.isLt _) h.1.r6 h.1.r5)
      fun s' ⟨he, _, _, g, _, _⟩ => ⟨he, by rw [g _ (by decide) (by decide) (by decide), h.2.1],
        by rw [g _ (by decide) (by decide) (by decide), h.2.2]⟩) ?_
  exact CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [h₁.2.2, h₂.2.2]
    · rw [h₁.2.1, h₂.2.1]
    all_goals exact env_eq h₁.1 h₂.1 (by simp)) hC

/-- One component, as `aStep_ok` but with the descriptors. -/
theorem adBody_wp {a : BitVec 32} {N : Nat} {dsc : Nat → Nat → BitVec 32} {i : Nat} (hi : i < N) {s : State}
    (h : AI c w sp a R N dsc i s) :
    WP isa (.seq (.block adNext) (.seq (cmacOf stOff) (.block adStep))) s fun s' =>
      AI c w sp a R N dsc (i + 1) s' ∧ s'.z = decide (N - (i + 1) = 0) := by
  obtain ⟨m₀, σ, h, hd⟩ := h
  exact WP.mono (aStep_ok L hR h hi) fun s' ⟨h', hz⟩ => ⟨⟨m₀, σ, h', hd⟩, hz⟩

/-- S2V over the components. -/
theorem s2vAds_ct {a : BitVec 32} {N : Nat} {dsc : Nat → Nat → BitVec 32} (hN : N < 2 ^ 32) :
    CT (AI c w sp a R N dsc 0) s2vAds := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r7]) (.block [.cmp .r7 (imm 0)])
      h).isSome = true := ⟨_, by taint_decide⟩
  refine CT.seq (J := fun s => AI c w sp a R N dsc 0 s ∧ s.z = decide (N = 0))
    (CT.taint _ (fun s₁ s₂ ⟨_, _, h₁, _⟩ ⟨_, _, h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r7, h₂.r7]) hA)
    (fun s ⟨m₀, σ, h, hd⟩ => by
      refine WP.of_runBlock ⟨_, by arun [], ⟨m₀, σ, ?_, hd⟩, ?_⟩
      · exact ⟨h.env.keep (fun r _ => rfl) rfl rfl rfl, h.ads.of_eq rfl rfl, h.r8, h.r7, h.rd, h.wr, h.frame,
          h.acc⟩
      · simp only [Proof.AesGcm.Arm.z_subFlags, h.r7, Nat.sub_zero]; exact Proof.AesGcm.Arm.z_cmp hN (by decide))
    ?_
  refine CT.ite (decide (N = 0)) (fun s h => h.2) (fun _ => CT.skip) fun hN0 => ?_
  have hN0' : N ≠ 0 := by simpa using hN0
  refine (RelCT.loop (M := isa) (c := .ne)
    (fun (k : Nat) (x y : State) => ∃ i, k = N - i ∧ i < N ∧ AI c w sp a R N dsc i x ∧ AI c w sp a R N dsc i y)
    (fun k => ?_) (N - 0)).mono (fun x y hxy => ⟨0, rfl, Nat.pos_of_ne_zero hN0', hxy.1.1, hxy.2.1⟩)
    fun _ _ p => p
  refine RelCT.exists_ fun i => ?_
  by_cases hc : k = N - i ∧ i < N
  swap
  · exact RelCT.of_false fun _ _ p => hc ⟨p.1, p.2.1⟩
  obtain ⟨rfl, hiN⟩ := hc
  refine (((adBody_ct L hR hiN).wp
    (F₁ := fun (s : State) => AI c w sp a R N dsc (i + 1) s ∧ s.z = decide (N - (i + 1) = 0))
    (F₂ := fun (s : State) => AI c w sp a R N dsc (i + 1) s ∧ s.z = decide (N - (i + 1) = 0))
    fun x y hxy => ⟨adBody_wp L hR hiN hxy.1, adBody_wp L hR hiN hxy.2⟩).mono
    (fun x y p => ⟨p.2.2.1, p.2.2.2⟩) fun x y p => ?_)
  have ea := Proof.AesGcm.Arm.eval_ne' p.2.1.2
  have eb := Proof.AesGcm.Arm.eval_ne' p.2.2.2
  refine ⟨by rw [ea, eb], fun e => trivial, fun e => ?_⟩
  have he : N - (i + 1) ≠ 0 := by rw [ea] at e; simpa using e
  exact ⟨N - (i + 1), by omega_using [hiN], i + 1, rfl, by omega_using [he], p.2.1.1, p.2.2.1⟩

end

end VG.Proof.AesSiv.Arm

end

end

/-!
# AES-SIV on ARMv7: S2V's end is constant time

Untrusted: everything here is checked by Lean. Two runs of `finish` on
strings at the same address and of the same length (`FI`) leak the same:
the branch is on the length, and so are the tails' copies and `j`, which
the taint analysis checks with the blocks between the calls; the calls get
the same arguments in both runs, which the correctness lemmas give
(`shortArgs_ok`, `longArgs₁_ok`, `longArgs₂_ok`, `longArgs₃_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm VG.Impl.AesSiv.Arm
open VG.Proof.AesGcm.Arm (CT)
open VG.Proof.AesCcm.Arm (UArgs upd_call upd_rel)
open VG.Impl.AesGcm.Arm (imm)

/-- Before `finish`: the string, `n` bytes at `P`, in `r6` and `r5`. -/
abbrev FI (c w sp : BitVec 32) (R : Nat) (P : BitVec 32) (n : Nat) : State → Prop := MPre c w sp R P n

section
variable {c w sp : BitVec 32} {R : Nat} (L : Lay c w sp) (hR : R = 10 ∨ R = 12 ∨ R = 14)
include L hR

omit L hR in
theorem env_regs {s₁ s₂ : State} (h₁ : Env c w sp R s₁) (h₂ : Env c w sp R s₂) :
    ∀ r ∈ ([.r9, .r10, .r11] : List Reg), s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact env_eq h₁ h₂ (by simp)

/-- The short case's call. -/
theorem shortMac_ct {out : Nat} (hout : out = 0 ∨ out = tOff) : CT (Env c w sp R) (shortMac out) := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r9, .r10, .r11])
      (.block (shortArgs out)) h).isSome = true := by
    rcases hout with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  exact CT.seq (J := fun s => Env c w sp R s ∧
      FArgs s c (w + BitVec.ofNat 32 out) (w + BitVec.ofNat 32 tailOff) (w + BitVec.ofNat 32 256) 16 R)
    (CT.taint _ (fun s₁ s₂ h₁ h₂ => env_regs h₁ h₂) hA)
    (fun s h => WP.mono (shortArgs_ok L h hR hout) fun s' h' => ⟨h'.1, h'.2.2.2.2.2⟩)
    (fin_rel fun s₁ s₂ hh => ⟨hh.1.2, hh.2.2, hh.1.1.sp, hh.2.1.sp⟩)

/-- Before the long case's calls: the string and `16 k`. -/
structure LI (c w sp : BitVec 32) (R : Nat) (P : BitVec 32) (n : Nat) (s : State) : Prop where
  pre : MPre c w sp R P n s
  r4 : s.gpr .r4 = BitVec.ofNat 32 (16 * kOf n)

/-- The long case's calls. -/
theorem longMac_ct {P : BitVec 32} {n : Nat} (h16 : 16 ≤ n) (hn : n < 2 ^ 32) {out : Nat}
    (hout : out = 0 ∨ out = tOff) : CT (LI c w sp R P n) (longMac out) := by
  have hT := kOf_tail h16
  have hJ := jOf_rest h16
  have hj1 := jOf_le n
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r4, .r6, .r9, .r10, .r11])
      (.block (longArgs₁ out)) h).isSome = true := by
    rcases hout with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r5]) jBlock h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r7, .r9, .r10, .r11])
      (.block (longArgs₂ out)) h).isSome = true := by
    rcases hout with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  obtain ⟨_, hD⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r4, .r5, .r7, .r9, .r10, .r11])
      (.block (longArgs₃ out)) h).isSome = true := by
    rcases hout with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  -- The registers the pieces keep.
  let K := 16 * kOf n
  let j := jOf n
  let Rg (s : State) : Prop := Env c w sp R s ∧ s.gpr .r4 = BitVec.ofNat 32 K ∧ s.gpr .r5 = BitVec.ofNat 32 n
  have keep : ∀ {s s' : State}, Rg s → (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) → s'.sp = s.sp →
      s'.rd = s.rd → s'.wr = s.wr → Rg s' := fun h g hsp hrd hwr =>
    ⟨h.1.of_saved g hsp hrd hwr, by rw [g _ (by decide) (by decide), h.2.1],
      by rw [g _ (by decide) (by decide), h.2.2]⟩
  refine CT.seq (J := fun s => Rg s ∧ UArgs s c (w + BitVec.ofNat 32 out) P (w + BitVec.ofNat 32 256) R (K / 16))
    (CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h₁.r4, h₂.r4]
      · rw [h₁.pre.r6, h₂.pre.r6]
      all_goals exact env_eq h₁.pre.env h₂.pre.env (by simp)) hA)
    (fun s h => WP.mono (longArgs₁_ok L h.pre.env hR h.pre.buf (K := K) (by omega_using [hT]) (by omega_using []) hn h.pre.r6 h.r4 hout)
      fun s' ⟨he, g, _, _, _, U⟩ => ⟨⟨he, by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), h.r4], by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        h.pre.r5]⟩, U⟩) ?_
  refine CT.seq (J := Rg) (upd_rel fun s₁ s₂ hh => ⟨hh.1.2, hh.2.2, hh.1.1.1.sp, hh.2.1.1.sp⟩)
    (fun s h => WP.mono (upd_call h.2) fun s' h' => keep h.1 h'.saved h'.sp h'.rd h'.wr) ?_
  refine CT.seq (J := fun s => Rg s ∧ s.gpr .r7 = BitVec.ofNat 32 j)
    (CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.2, h₂.2.2]) hB)
    (fun s h => WP.mono (jBlock_ok h16 hn h.2.2) fun s' ⟨h7, g, k⟩ =>
      ⟨⟨h.1.keep (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> exact g _ (by decide) (by decide)) k.sp k.rd k.wr,
        by rw [g _ (by decide) (by decide), h.2.1], by rw [g _ (by decide) (by decide), h.2.2]⟩, h7⟩) ?_
  refine CT.seq (J := fun s => (Rg s ∧ s.gpr .r7 = BitVec.ofNat 32 j) ∧
      UArgs s c (w + BitVec.ofNat 32 out) (w + BitVec.ofNat 32 tailOff) (w + BitVec.ofNat 32 256) R j)
    (CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h₁.2, h₂.2]
      all_goals exact env_eq h₁.1.1 h₂.1.1 (by simp)) hC)
    (fun s h => by
      obtain ⟨s', run, he, g, k, U⟩ := longArgs₂_ok L h.1.1 hR hout hj1 h.2
      refine WP.of_runBlock ⟨s', run, ⟨⟨he, ?_, ?_⟩, ?_⟩, U⟩
      · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.1.2.1]
      · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.1.2.2]
      · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.2]) ?_
  refine CT.seq (J := fun s => Rg s ∧ s.gpr .r7 = BitVec.ofNat 32 j)
    (upd_rel fun s₁ s₂ hh => ⟨hh.1.2, hh.2.2, hh.1.1.1.1.sp, hh.2.1.1.1.sp⟩)
    (fun s h => WP.mono (upd_call h.2) fun s' h' => ⟨keep h.1.1 h'.saved h'.sp h'.rd h'.wr,
      by rw [h'.saved _ (by decide) (by decide), h.1.2]⟩) ?_
  refine CT.seq (J := fun s => Env c w sp R s ∧ FArgs s c (w + BitVec.ofNat 32 out)
      (w + BitVec.ofNat 32 (tailOff + 16 * j)) (w + BitVec.ofNat 32 256) (n - K - 16 * j) R)
    (CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [h₁.1.2.1, h₂.1.2.1]
      · rw [h₁.1.2.2, h₂.1.2.2]
      · rw [h₁.2, h₂.2]
      all_goals exact env_eq h₁.1.1 h₂.1.1 (by simp)) hD)
    (fun s h => by
      obtain ⟨s', run, he, _, _, F⟩ := longArgs₃_ok L h.1.1 hR hout hn hT hJ hj1 h.2 h.1.2.2 h.1.2.1
      exact WP.of_runBlock ⟨s', run, he, F⟩) ?_
  exact fin_rel fun s₁ s₂ hh => ⟨hh.1.2, hh.2.2, hh.1.1.sp, hh.2.1.sp⟩

/-- S2V's end with the string, into `W + out`. -/
theorem finish_ct {P : BitVec 32} {n : Nat} (hn : n < 2 ^ 32) {out : Nat} (hout : out = 0 ∨ out = tOff) :
    CT (FI c w sp R P n) (finish out) := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r5])
      (.block [.mov .r12 (.shifted .r5 .lsr 4), .cmp .r12 (imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hS⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r5, .r6, .r9, .r10, .r11])
      shortTail h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hL⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r5, .r6, .r9, .r10, .r11])
      longTail h).isSome = true := ⟨_, by taint_decide⟩
  have regs : ∀ s₁ s₂, FI c w sp R P n s₁ → FI c w sp R P n s₂ →
      ∀ r ∈ ([.r5, .r6, .r9, .r10, .r11] : List Reg), s₁.gpr r = s₂.gpr r := fun s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [h₁.r5, h₂.r5]
    · rw [h₁.r6, h₂.r6]
    all_goals exact env_eq h₁.env h₂.env (by simp)
  refine CT.seq (J := fun s => FI c w sp R P n s ∧ s.z = decide (n / 16 = 0))
    (CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r5, h₂.r5]) hA)
    (fun s h => by
      obtain ⟨s', run, hz, g, k⟩ := finishPre_ok hn h.r5
      exact WP.of_runBlock ⟨s', run, ⟨h.env.keep (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> exact g _ (by decide)) k.sp k.rd k.wr, h.buf.of_eq k.rd k.wr,
        by rw [g _ (by decide), h.r6], by rw [g _ (by decide), h.r5]⟩, hz⟩) ?_
  refine CT.ite (decide (n / 16 = 0)) (fun s h => h.2) (fun ht => ?_) fun hf => ?_
  · have h16 : n < 16 := by have := of_decide_eq_true ht; omega_using [this]
    exact (CT.seq (J := Env c w sp R) (CT.taint _ regs hS)
      (fun s h => WP.mono (shortTail_ok L h.env h.buf h16 h.r6 h.r5) fun s' h' => h'.1)
      (shortMac_ct L hR hout)).mono fun s h => h.1
  · have h16 : 16 ≤ n := by have := of_decide_eq_false hf; omega_using [this]
    exact (CT.seq (J := LI c w sp R P n) (CT.taint _ regs hL)
      (fun s h => WP.mono (longTail_ok L h.env h.buf h16 hn h.r6 h.r5) fun s' ⟨he, rd, wr, g, h4, _⟩ =>
        ⟨⟨he, h.buf.of_eq rd wr, by rw [g _ (by decide) (by decide) (by decide), h.r6],
          by rw [g _ (by decide) (by decide) (by decide), h.r5]⟩, h4⟩)
      (longMac_ct L hR h16 hn hout)).mono fun s h => h.1

end

end VG.Proof.AesSiv.Arm

end

end

/-!
# AES-SIV on ARMv7: CTR is constant time

Untrusted: everything here is checked by Lean. Two runs of `ctr 0` on data
at the same address and of the same length (`CtrI`) leak the same: the
first block loads the data's address and length from the stack arguments,
the same in both runs; the branches are on the length, and so are the
numbers of blocks and bytes; the calls of `vg_aes_ctr32` get the same
arguments in both runs (`ctrWholeArgs_ok`, `ctrTailArgs_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm VG.Impl.AesSiv.Arm
open VG.Proof.AesGcm.Arm (CT CtrCall ctr_call)
open VG.Impl.AesGcm.Arm (imm addI xorLoop)
open VG.Impl.CmacAes.Arm (mov)

/-- Before CTR's pieces: the data, `n` bytes at `D`, in `r6` and `r5`. -/
structure CI (c w sp : BitVec 32) (R : Nat) (D : BitVec 32) (n : Nat) (s : State) : Prop where
  env : Env c w sp R s
  dat : Dat c w sp s D n
  r6 : s.gpr .r6 = D
  r5 : s.gpr .r5 = BitVec.ofNat 32 n

/-- After code that keeps the callee-saved registers. -/
theorem CI.keep {c w sp D : BitVec 32} {R n : Nat} {s s' : State} (h : CI c w sp R D n s)
    (hg : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : CI c w sp R D n s' :=
  ⟨h.env.of_saved hg hsp hrd hwr, h.dat.of_eq hrd hwr, by rw [hg _ (by decide) (by decide), h.r6],
    by rw [hg _ (by decide) (by decide), h.r5]⟩

/-- Before CTR: the data's address and length as the stack arguments, which
the regions the code may write are apart from. -/
structure CtrI (c w sp : BitVec 32) (R : Nat) (D : BitVec 32) (n : Nat) (s : State) : Prop where
  env : Env c w sp R s
  dat : Dat c w sp s D n
  wa : ∀ r ∈ s.wr, (⟨State.addr sp, 16⟩ : Region).Disjoint r
  afit : sp.toNat + 16 ≤ 2 ^ 32
  args : Covers [⟨State.addr sp, 16⟩] (s.rd ++ s.wr)
  args_w : (⟨State.addr sp, 16⟩ : Region).Disjoint ⟨State.addr w, 2576⟩
  args_d : (⟨State.addr sp, 16⟩ : Region).Disjoint ⟨State.addr D, n⟩
  m0 : s.mem.readW (State.addr sp) 32 = D
  m1 : s.mem.readW (State.addr sp + BitVec.ofNat 64 4) 32 = BitVec.ofNat 32 n
  n32 : n < 2 ^ 32

/-- The first two stack arguments: the data's address and length. -/
theorem CtrI.arg {c w sp D : BitVec 32} {R n : Nat} {s : State} (h : CtrI c w sp R D n s) :
    stackArg s 0 = D ∧ stackArg s 1 = BitVec.ofNat 32 n := by
  have hsp := h.env.sp
  refine ⟨?_, ?_⟩
  · rw [stackArg, stackArgAddr, hsp, show 4 * 0 = 0 from rfl, BitVec.add_zero, h.m0]
  · rw [stackArg, stackArgAddr, hsp, addr_add (by have := h.afit; omega_using [this]), h.m1]

section
variable {c w sp : BitVec 32} {R : Nat} (L : Lay c w sp) (hR : R = 10 ∨ R = 12 ∨ R = 14)
include L hR

/-- The whole blocks. -/
theorem ctrWhole_ct {D : BitVec 32} {n : Nat} (hn : n < 2 ^ 32) : CT (CI c w sp R D n) ctrWhole := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r5])
      (.block [.mov .r12 (.shifted .r5 .lsr 4), .cmp .r12 (imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r6, .r9, .r10, .r11])
      (.block (ctrArgs ++ [mov .r3 .r6])) h).isSome = true := ⟨_, by taint_decide⟩
  refine CT.seq (J := fun s => CI c w sp R D n s ∧ s.z = decide (n / 16 = 0) ∧
      s.gpr .r12 = BitVec.ofNat 32 (n / 16))
    (CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r5, h₂.r5]) hA)
    (fun s h => by
      obtain ⟨s', run, h12, hz, g, k⟩ := split16_ok hn h.r5
      exact WP.of_runBlock ⟨s', run, ⟨h.env.keep (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> exact g _ (by decide)) k.sp k.rd k.wr, h.dat.of_eq k.rd k.wr,
        by rw [g _ (by decide), h.r6], by rw [g _ (by decide), h.r5]⟩, hz, h12⟩) ?_
  refine CT.ite (decide (n / 16 = 0)) (fun s h => h.2.1) (fun _ => CT.skip) fun _ => ?_
  refine CT.seq (J := fun s => Env c w sp R s ∧
      CtrCall s (c + BitVec.ofNat 32 272) (w + BitVec.ofNat 32 cbOff) D (w + BitVec.ofNat 32 256) R (n / 16))
    (CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h₁.1.r6, h₂.1.r6]
      all_goals exact env_eq h₁.1.env h₂.1.env (by simp)) hB)
    (fun s h => by
      obtain ⟨s', run, he, _, _, C⟩ := ctrWholeArgs_ok L h.1.env hR h.1.dat h.1.r6 rfl h.2.2
      exact WP.of_runBlock ⟨s', run, he, C⟩) ?_
  exact CT.ctr fun s₁ s₂ h₁ h₂ => ⟨_, _, _, _, _, _, h₁.2, h₂.2, by rw [h₁.1.sp, h₂.1.sp]⟩

/-- What the whole blocks keep. -/
theorem ctrWhole_keeps {D : BitVec 32} {n : Nat} (hn : n < 2 ^ 32) {s : State} (h : CI c w sp R D n s) :
    WP isa ctrWhole s (CI c w sp R D n) := by
  obtain ⟨s₁, run₁, h12, hz, g, k⟩ := split16_ok hn h.r5
  have h₁ : CI c w sp R D n s₁ := ⟨h.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact g _ (by decide)) k.sp k.rd k.wr, h.dat.of_eq k.rd k.wr,
    by rw [g _ (by decide), h.r6], by rw [g _ (by decide), h.r5]⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  by_cases h0 : n / 16 = 0
  · exact WP.ite true (Proof.AesGcm.Arm.eval_eq' (by rw [hz]; simp [h0])) (fun _ => WP.block_nil h₁)
      (fun h => by cases h)
  refine WP.ite false (Proof.AesGcm.Arm.eval_eq' (by rw [hz]; simp [h0])) (fun h => by cases h) fun _ => ?_
  obtain ⟨s₂, run₂, _, g₂, k₂, C⟩ := ctrWholeArgs_ok L h₁.env hR h₁.dat h₁.r6 rfl h12
  have h₂ : CI c w sp R D n s₂ := h₁.keep (fun r hr hlr => by
      have a : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact g₂ r a.1 a.2.1 a.2.2.1 a.2.2.2 hlr) k₂.sp k₂.rd k₂.wr
  exact WP.seq (WP.of_runBlock ⟨s₂, run₂, WP.mono (ctr_call C) fun s₃ p => h₂.keep p.saved p.sp p.rd p.wr⟩)

/-- The last bytes. -/
theorem ctrTail_ct {D : BitVec 32} {n : Nat} (hn : n < 2 ^ 32) : CT (CI c w sp R D n) ctrTail := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r5])
      (.block [.dp .and .r4 .r5 (imm 15), .cmp .r4 (imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r9, .r10, .r11])
      (.block (zero16 ksOff ++ ctrArgs ++ [addI .r3 .r11 ksOff, .mov .r12 (imm 1)])) h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r4, .r5, .r6, .r11])
      (.seq (.block [addI .r1 .r11 ksOff, .dp .sub .r2 .r5 (.reg .r4), .dp .add .r2 .r2 (.reg .r6), mov .r3 .r4])
        xorLoop) h).isSome = true := ⟨_, by taint_decide⟩
  let J (s : State) : Prop := CI c w sp R D n s ∧ s.gpr .r4 = BitVec.ofNat 32 (n % 16)
  refine CT.seq (J := fun s => J s ∧ s.z = decide (n % 16 = 0))
    (CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r5, h₂.r5]) hA)
    (fun s h => by
      obtain ⟨s', run, h4, hz, g, k⟩ := tailPre_ok hn h.r5
      exact WP.of_runBlock ⟨s', run, ⟨⟨h.env.keep (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> exact g _ (by decide)) k.sp k.rd k.wr, h.dat.of_eq k.rd k.wr,
        by rw [g _ (by decide), h.r6], by rw [g _ (by decide), h.r5]⟩, h4⟩, hz⟩) ?_
  refine CT.ite (decide (n % 16 = 0)) (fun s h => h.2) (fun _ => CT.skip) fun _ => ?_
  refine CT.seq (J := fun s => J s ∧ CtrCall s (c + BitVec.ofNat 32 272) (w + BitVec.ofNat 32 cbOff)
      (w + BitVec.ofNat 32 ksOff) (w + BitVec.ofNat 32 256) R 1)
    (CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact env_eq h₁.1.1.env h₂.1.1.env (by simp)) hB)
    (fun s h => WP.mono (ctrTailArgs_ok L h.1.1.env hR) fun s' ⟨he, g, rd, wr, _, _, C⟩ =>
      ⟨⟨⟨he, h.1.1.dat.of_eq rd wr,
        by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.1.1.r6],
        by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.1.1.r5]⟩,
        by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.1.2]⟩, C⟩) ?_
  refine CT.seq (J := J)
    (CT.ctr fun s₁ s₂ h₁ h₂ => ⟨_, _, _, _, _, _, h₁.2, h₂.2, by rw [h₁.1.1.env.sp, h₂.1.1.env.sp]⟩)
    (fun s h => WP.mono (ctr_call h.2) fun s' p =>
      ⟨h.1.1.keep p.saved p.sp p.rd p.wr, by rw [p.saved _ (by decide) (by decide), h.1.2]⟩) ?_
  exact CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₁.2, h₂.2]
    · rw [h₁.1.r5, h₂.1.r5]
    · rw [h₁.1.r6, h₂.1.r6]
    · exact env_eq h₁.1.env h₂.1.env (by simp)) hC

/-- CTR from the IV at `W`. -/
theorem ctr_ct {D : BitVec 32} {n : Nat} (hn : n < 2 ^ 32) : CT (CtrI c w sp R D n) (ctr 0) := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (argTaint [.r9, .r10, .r11] (4 * 2))
      (.block (counter 0 ++ [.ldrSp .r6 0, .ldrSp .r5 4])) h).isSome = true := ⟨_, by taint_decide⟩
  refine CT.seq (J := CI c w sp R D n)
    (CT.argTaint _ _ (fun s₁ s₂ h₁ h₂ => env_regs h₁.env h₂.env)
      (fun s₁ s₂ h₁ h₂ => by rw [h₁.env.sp, h₂.env.sp])
      (fun s h => ⟨by rw [h.env.sp]; have := h.afit; omega_using [this], fun r hr => by
        rw [h.env.sp]; exact (h.wa r hr).sub_left (Region.sub_prefix (by decide))⟩)
      (fun s₁ s₂ h₁ h₂ => argMem_of (by rw [h₁.env.sp, h₂.env.sp]) (by rw [h₁.env.sp]; have := h₁.afit; omega_using [this])
        fun i hi => by
          rcases (show i = 0 ∨ i = 1 by omega_using [hi]) with rfl | rfl
          · rw [h₁.arg.1, h₂.arg.1]
          · rw [h₁.arg.2, h₂.arg.2]) hA)
    (fun s h => WP.mono (ctrPre_ok L h.env h.dat h.afit h.args h.args_w h.m0 h.m1)
      fun s' ⟨he, hD, h6, h5, _⟩ => ⟨he, hD, h6, h5⟩) ?_
  exact CT.seq (ctrWhole_ct L hR hn) (fun s h => ctrWhole_keeps L hR hn h) (ctrTail_ct L hR hn)

end

end VG.Proof.AesSiv.Arm

end

end

/-! ### `AesSiv.Arm.Open`, which this module and modules that import it used -/

section

/-! ### `AesSiv.Arm.Seal`, which this module and modules that import it used -/

section

/-! ### `AesSiv.Arm.Start`, which this module and modules that import it used -/

section

/-!
# AES-SIV on ARMv7: the entry, and S2V's first state

Untrusted: everything here is checked by Lean. `encrypt` and `decrypt` take
the key context in `r0`, the rounds in `r1`, the descriptors in `r2` and
their number in `r3`, and the data, its length, `siv` and `W` on the stack
(`EPre`). They save our caller's registers in `W` where AES-GCM does
(`Proof.AesGcm.Arm.save_ok`), keep their arguments in registers, zero the
block at `W + 16` and `D`, and finalize the zero block into `D`:
`D = AES-CMAC(K1, <zero>)` (`start_ok`), S2V's first state.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesSiv.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.Arm (imm addI save)
open VG.Impl.CmacAes.Arm (mov)
open VG.Proof.AesCcm.Arm (blw)
open VG.Proof.AesGcm.Arm (bytesAt_frame SavedAt savedR save_ok covers_left covers_prefix in_off)
open VG.Proof.MdStream.Arm (wp_ldrSp)

/-- What `encrypt` and `decrypt` need of their arguments: the key context
`c`, the rounds `R`, the `N` descriptors at `a`, the data (`n` bytes at `D`),
`siv` (16 bytes at `T`, which they may at least read) and `W`, the last four
on the stack at `sp`. -/
structure EPre (c w sp a D T : BitVec 32) (R N n : Nat) (s : State) : Prop where
  lay : Lay c w sp
  perm : Perm c w s
  r0 : s.gpr .r0 = c
  r1 : s.gpr .r1 = BitVec.ofNat 32 R
  r2 : s.gpr .r2 = a
  r3 : s.gpr .r3 = BitVec.ofNat 32 N
  hsp : s.sp = sp
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  afit : sp.toNat + 16 ≤ 2 ^ 32
  args : Covers [⟨State.addr sp, 16⟩] (s.rd ++ s.wr)
  args_w : (⟨State.addr sp, 16⟩ : Region).Disjoint ⟨State.addr w, 2576⟩
  args_d : (⟨State.addr sp, 16⟩ : Region).Disjoint ⟨State.addr D, n⟩
  a0 : s.mem.readW (State.addr sp) 32 = D
  a1 : s.mem.readW (State.addr sp + BitVec.ofNat 64 4) 32 = BitVec.ofNat 32 n
  a2 : s.mem.readW (State.addr sp + BitVec.ofNat 64 8) 32 = T
  a3 : s.mem.readW (State.addr sp + BitVec.ofNat 64 12) 32 = w
  ads : Ads w sp a N s.mem s
  data : Dat c w sp s D n
  n32 : n < 2 ^ 32
  tfit : T.toNat + 16 ≤ 2 ^ 32
  t_rd : Covers [⟨State.addr T, 16⟩] (s.rd ++ s.wr)
  t_w : (⟨State.addr T, 16⟩ : Region).Disjoint ⟨State.addr w, 2576⟩
  t_stk : (blw sp).Disjoint ⟨State.addr T, 16⟩

/-- The descriptors as they were, after writes apart from them. -/
theorem Ads.of_frame {w sp a : BitVec 32} {N : Nat} {m m' : Mem} {s : State} (h : Ads w sp a N m s)
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, (⟨State.addr a, 8 * N⟩ : Region).Disjoint r) :
    Ads w sp a N m' s := by
  have e : ∀ i < N, ∀ j < 2, descW m' a i j = descW m a i j := fun i hi j hj =>
    hf.readW (r := ⟨State.addr a + BitVec.ofNat 64 (8 * i + 4 * j), 4⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (Offset.sub_base _ (by omega_using [hi, hj]))) (by decide)
  exact { h with comp := fun i hi => by rw [e i hi 0 (by decide), e i hi 1 (by decide)]; exact h.comp i hi }

/-- The components as they were, after writes apart from them. -/
theorem components_frame {a : BitVec 32} {N : Nat} {m m' : Mem}
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, (⟨State.addr a, 8 * N⟩ : Region).Disjoint r)
    (hc : ∀ i < N, ∀ r ∈ rs, (⟨State.addr (descW m a i 0), (descW m a i 1).toNat⟩ : Region).Disjoint r) :
    Spec.Siv.components 32 m' (State.addr a) N = Spec.Siv.components 32 m (State.addr a) N := by
  have e : ∀ i < N, ∀ j < 2, descW m' a i j = descW m a i j := fun i hi j hj =>
    hf.readW (r := ⟨State.addr a + BitVec.ofNat 64 (8 * i + 4 * j), 4⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (Offset.sub_base _ (by omega_using [hi, hj]))) (by decide)
  apply List.ext_getElem (by rw [length_components, length_components])
  intro i h₁ h₂
  rw [length_components] at h₂
  rw [components_getElem m' a h₂, components_getElem m a h₂, e i h₂ 0 (by decide), e i h₂ 1 (by decide)]
  exact bytesAt_frame hf (hc i h₂) (by have := (descW m a i 1).isLt; omega_using [])

section
variable {c w sp : BitVec 32} {R : Nat} (L : Lay c w sp)
include L

theorem saved_wR : ∀ r ∈ wR w sp, (savedR w).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact L.w_w (a := 128) (n := 36) (d := 16) (m := 112) (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w' (by decide)).symm

omit L in
/-- What the entry leaves, before the call of `vg_cmac_aes_finalize` that
computes S2V's first state: the registers saved in the memory `mₛ`, the
zero block at `W + 16` and `D` zeroed, and the arguments of the call. -/
structure Started (c w sp a : BitVec 32) (R N : Nat) (s : State) (mₛ : Mem) (s' : State) : Prop where
  fs : Frame [savedR w] s.mem mₛ
  sv : SavedAt mₛ w s
  env : Env c w sp R s'
  r8 : s'.gpr .r8 = a
  r7 : s'.gpr .r7 = BitVec.ofNat 32 N
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame (wR w sp) mₛ s'.mem
  zD : bytesAt s'.mem (State.addr w + BitVec.ofNat 64 dOff) 16 = Spec.Cmac.zeros 16
  zZ : bytesAt s'.mem (State.addr w + BitVec.ofNat 64 zOff) 16 = Spec.Cmac.zeros 16
  args : FArgs s' c (w + BitVec.ofNat 32 dOff) (w + BitVec.ofNat 32 zOff) (w + BitVec.ofNat 32 256) 16 R

/-- The entry, up to the call. -/
theorem startBlock_ok {a D T : BitVec 32} {N n : Nat} {s : State} (h : EPre c w sp a D T R N n s) :
    WP isa (.block (encPre ++ startPre)) s fun s' => ∃ mₛ, Started c w sp a R N s mₛ s' := by
  have ww := L.ww
  have hR := h.rounds
  rw [encPre, List.cons_append]
  refine wp_ldrSp (a := State.addr sp + BitVec.ofNat 64 12) (by decide)
    (by rw [h.hsp]; exact addr_add (by have := h.afit; omega_using [this])) (in_off h.args (by decide) (by decide))
    fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = w := by rw [u₁.gpr, h.a3]
  simp only [List.append_eq, List.append_assoc]
  refine save_ok h12 (by omega_using [ww]) (by rw [u₁.wr]; exact covers_prefix h.perm.w (by decide))
    fun s₂ g₂ rd₂ wr₂ sp₂ sv₂ f₂ => ?_
  have hrd₂ : s₂.rd = s.rd := by rw [rd₂, u₁.rd]
  have hwr₂ : s₂.wr = s.wr := by rw [wr₂, u₁.wr]
  have hsp₂ : s₂.sp = sp := by rw [sp₂, u₁.sp, h.hsp]
  have gg : ∀ r, r ≠ .r12 → s₂.gpr r = s.gpr r := fun r hr => by rw [g₂, u₁.other r hr]
  obtain ⟨s₃, run₃, he₃, h8₃, h7₃, k₃⟩ : ∃ s₃, runBlock isa [mov .r11 .r12, mov .r10 .r0, mov .r9 .r1,
      mov .r8 .r2, mov .r7 .r3] s₂ = some s₃ ∧ Env c w sp R s₃ ∧ s₃.gpr .r8 = a ∧ s₃.gpr .r7 = BitVec.ofNat 32 N ∧
      Proof.AesGcm.Arm.Keeps s₂ s₃ := by
    have e0 : s₂.gpr .r0 = c := by rw [gg _ (by decide), h.r0]
    have e1 : s₂.gpr .r1 = BitVec.ofNat 32 R := by rw [gg _ (by decide), h.r1]
    have e2 : s₂.gpr .r2 = a := by rw [gg _ (by decide), h.r2]
    have e3 : s₂.gpr .r3 = BitVec.ofNat 32 N := by rw [gg _ (by decide), h.r3]
    have e12 : s₂.gpr .r12 = w := by rw [g₂, h12]
    refine ⟨_, by simp only [mov]; arun [], ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · simp [gpr_setReg, e1]
    · simp [gpr_setReg, e0]
    · simp [gpr_setReg, e12]
    · simp [sp_setReg, hsp₂]
    · exact h.perm.of_eq (by simp [rd_setReg, hrd₂]) (by simp [wr_setReg, hwr₂])
    · simp [gpr_setReg, e2]
    · simp [gpr_setReg, e3]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  simp only [startPre, List.append_assoc]
  refine zero16_ok L he₃ (d := zOff) (by decide) fun s₄ g₄ m₄ rd₄ wr₄ sp₄ => ?_
  have he₄ : Env c w sp R s₄ := he₃.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₄ _ (by decide)) sp₄ rd₄ wr₄
  refine zero16_ok L he₄ (d := dOff) (by decide) fun s₅ g₅ m₅ rd₅ wr₅ sp₅ => ?_
  have he₅ : Env c w sp R s₅ := he₄.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₅ _ (by decide)) sp₅ rd₅ wr₅
  have eZ := L.wA (d := zOff) (by decide)
  have eD := L.wA (d := dOff) (by decide)
  obtain ⟨s₆, run₆, he₆, g₆, k₆, F⟩ : ∃ s₆, runBlock isa (macArgs dOff ++ [addI .r3 .r11 zOff, .mov .r12 (imm 16)])
      s₅ = some s₆ ∧ Env c w sp R s₆ ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₆.gpr r = s₅.gpr r) ∧
      Proof.AesGcm.Arm.Keeps s₅ s₆ ∧
      FArgs s₆ c (w + BitVec.ofNat 32 dOff) (w + BitVec.ofNat 32 zOff) (w + BitVec.ofNat 32 256) 16 R := by
    refine ⟨_, by simp only [macArgs, csOff, zOff, dOff]; arun [he₅.r9, he₅.r10, he₅.r11], ?_⟩
    refine ⟨he₅.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl,
      fun r a b c' d e f => by simp [gpr_setReg, a, b, c', d, e, f], ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
    refine fargs_of L ?_ hR (st := dOff) (.inr ⟨by decide, by decide⟩) (n := 16) (by decide)
      (by rw [L.wN (by decide)]; simp only [zOff]; omega_using [ww]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact he₅.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl
    · rw [eZ]; exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · rw [eZ]; exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · rw [eZ]; exact L.stk_w' (by decide)
    · rw [eZ]; exact covers_left (he₅.perm.wC (by decide))
    · simp [gpr_setReg, he₅.r10]
    · simp [gpr_setReg, he₅.r9]
    · simp [gpr_setReg, he₅.r11]
    · simp [gpr_setReg, he₅.r11]
    · simp [gpr_setReg]
    · simp [gpr_setReg, he₅.r11]
  -- What was written after the save.
  have fZ : Frame (wR w sp) s₂.mem s₆.mem := by
    rw [k₆.mem, m₅, m₄, k₃.mem]
    refine ((Proof.Cmac.frame_store4 _ _ _ _ _).sub fun r hr => ?_).trans
      ((Proof.Cmac.frame_store4 _ _ _ _ _).sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨State.addr w + BitVec.ofNat 64 16, 112⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨State.addr w + BitVec.ofNat 64 176, 2400⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  have hgg : ∀ r ∈ [Reg.r7, .r8], s₆.gpr r = s₃.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;>
      rw [g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g₅ _ (by decide),
        g₄ _ (by decide)]
  have f₂' : Frame [savedR w] s.mem s₂.mem := by rw [← u₁.mem]; exact f₂
  refine WP.of_runBlock ⟨s₆, run₆, s₂.mem, f₂', fun p hp => ?_, he₆, by rw [hgg _ (by simp), h8₃],
    by rw [hgg _ (by simp), h7₃], by rw [k₆.rd, rd₅, rd₄, k₃.rd, hrd₂], by rw [k₆.wr, wr₅, wr₄, k₃.wr, hwr₂], fZ,
    ?_, ?_, F⟩
  · have hp' : p.1 ≠ .r12 := by
      simp only [Impl.AesGcm.Arm.saved, List.mem_cons, List.not_mem_nil,
        or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [sv₂ p hp, u₁.other _ hp']
  · rw [k₆.mem, m₅, Proof.Cmac.zero4_bytes]
  · rw [k₆.mem, m₅, Proof.Cmac.zero4, bytesAt_frame (Proof.Cmac.frame_store4 _ _ _ _ _)
      (p := State.addr w + BitVec.ofNat 64 zOff)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide))
      (by decide), m₄, Proof.Cmac.zero4_bytes]

/-- The entry and S2V's first state: from the memory `mₛ` after the save,
`D = AES-CMAC(K1, <zero>)`, before the first component. -/
theorem start_ok {a D T : BitVec 32} {N n : Nat} {s : State} (h : EPre c w sp a D T R N n s) :
    WP isa (.seq (.block (encPre ++ startPre)) finFrame) s fun s' =>
      ∃ mₛ : Mem, Frame [savedR w] s.mem mₛ ∧ SavedAt mₛ w s ∧ AInv c w sp a R N mₛ s 0 s' := by
  have hR := h.rounds
  refine WP.seq (WP.mono (startBlock_ok L h) fun s₆ ⟨mₛ, St⟩ => ?_)
  have he₆ := St.env
  have eD := L.wA (d := dOff) (by decide)
  have eZ := L.wA (d := zOff) (by decide)
  refine WP.mono (fin_call St.args) fun s₇ h₇ => ?_
  have hb₆ := blw16_eq (s := s₆) he₆.sp
  have f₇ := h₇.frame
  rw [eD, L.wA (d := 256) (by decide), hb₆] at f₇
  have f₆₇ : Frame (wR w sp) s₆.mem s₇.mem := f₇.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨State.addr w + BitVec.ofNat 64 176, 2400⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨⟨State.addr w + BitVec.ofNat 64 176, 2400⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨blw sp, by simp, fun _ h => h⟩
  have rd₇ : s₇.rd = s.rd := by rw [h₇.rd, St.rd]
  have wr₇ : s₇.wr = s.wr := by rw [h₇.wr, St.wr]
  refine ⟨mₛ, St.fs, St.sv, ⟨he₆.of_saved h₇.saved h₇.sp h₇.rd h₇.wr, ?_, ?_, ?_, rd₇, wr₇,
    St.frame.trans f₆₇, ?_⟩⟩
  · refine (h.ads.of_frame St.fs (fun r hr => ?_)).of_eq (by rw [rd₇]) (by rw [wr₇])
    simp only [List.mem_singleton] at hr; subst hr
    exact (h.ads.dw.sub_right (Lay.wSub (by decide)))
  · rw [h₇.saved _ (by decide) (by decide), St.r8]; simp
  · rw [h₇.saved _ (by decide) (by decide), St.r7, Nat.sub_zero]
  · have hRb := rounds_le hR
    have dcw : ∀ r ∈ wR w sp, (⟨State.addr c, 512⟩ : Region).Disjoint r := dis_wR L.c_w L.stk_c
    have cK {d k : Nat} (hd : d + k ≤ 512) :
        bytesAt s₆.mem (State.addr c + BitVec.ofNat 64 d) k = bytesAt mₛ (State.addr c + BitVec.ofNat 64 d) k :=
      bytesAt_frame St.frame (fun r hr => (dcw r hr).sub_left (Lay.cSub hd)) (by omega_using [hd])
    have sch := cK (d := 0) (k := 16 * (R + 1)) (by omega_using [hR])
    rw [BitVec.add_zero] at sch
    have o₇ := h₇.out
    rw [eD, eZ, sch, cK (d := 240) (k := 16) (by decide), cK (d := 256) (k := 16) (by decide), St.zZ, St.zD] at o₇
    rw [o₇, List.take_zero, Spec.Siv.s2vAcc, List.foldl_nil, Spec.Siv.s2vStart, Spec.Siv.ctxMac,
      Spec.Siv.schedCiph, macWith_one _ _ _ _ (by rfl)]
    rfl

end

end VG.Proof.AesSiv.Arm

end

end

/-!
# AES-SIV on ARMv7: `vg_aes_siv_encrypt`

Untrusted: everything here is checked by Lean. `encS2v` saves the
registers, sets S2V's first state (`start_ok`), absorbs the components of
associated data (`s2vAds_ok`) and loads the data's address and length
(`s2v_ok`); `encrypt` then finishes S2V with the plaintext into the IV at
`W` (`finish_ok`), encrypts the plaintext with CTR from it (`ctr_ok`), copies
the IV to `siv` (`sivOut_ok`) and restores the registers (`encrypt_wp`):
`encryptWith` of the context's PRF and cipher (`Spec.Siv.encryptWith_eq`).
`decrypt` copies the received IV from `siv` to `W` the same way
(`sivIn_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCcm.Arm (blw)
open VG.Proof.AesGcm.Arm (bytesAt_frame SavedAt savedR restore_ok covers_left covers_prefix in_off sepW
  bytesAt_copy4 store4_eq mem_store add_ofNat_assoc add_ofNat_zero)
open VG.Proof.Cmac (store4)
open VG.Proof.MdStream.Arm (wp_ldrSp)

section
variable {c w sp : BitVec 32} {R : Nat} (L : Lay c w sp)
include L

/-- What `encS2v` leaves: `D` is S2V's state of the components, from the
memory `mₛ` after the save, and the data's address and length in `r6` and
`r5`. -/
structure S2vOut (c w sp a D : BitVec 32) (R N n : Nat) (s : State) (mₛ : Mem) (s' : State) : Prop where
  fs : Frame [savedR w] s.mem mₛ
  sv : SavedAt mₛ w s
  env : Env c w sp R s'
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  r6 : s'.gpr .r6 = D
  r5 : s'.gpr .r5 = BitVec.ofNat 32 n
  frame : Frame (wR w sp) mₛ s'.mem
  acc : bytesAt s'.mem (State.addr w + BitVec.ofNat 64 dOff) 16 =
    Spec.Siv.s2vAcc (Spec.Siv.ctxMac s.mem (State.addr c) R) (Spec.Siv.components 32 s.mem (State.addr a) N)

theorem s2v_ok {a D T : BitVec 32} {N n : Nat} {s : State} (h : EPre c w sp a D T R N n s) :
    WP isa encS2v s fun s' => ∃ mₛ, S2vOut c w sp a D R N n s mₛ s' := by
  have hR := h.rounds
  obtain hRb := rounds_le hR
  obtain hN : N < 2 ^ 32 := by have := h.ads.fit; omega_arith
  obtain st := WP.seq_iff.mp (start_ok L h)
  refine WP.seq (WP.mono st fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono h₁ fun s₂ ⟨mₛ, fs, sv, I₀⟩ => ?_)
  refine WP.seq (WP.mono (s2vAds_ok L hR I₀ hN) fun s₃ I => ?_)
  -- The data's address and length.
  obtain dA : ∀ r ∈ savedR w :: wR w sp, (⟨State.addr sp, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.args_w.sub_right (Lay.wSub (by decide))
    · exact h.args_w.sub_right (Lay.wSub (by decide))
    · exact h.args_w.sub_right (Lay.wSub (by decide))
    · exact Offset.base_disjoint_below (State.addr sp) (n := 16) (k := 16) (by decide)
  obtain fT : Frame (savedR w :: wR w sp) s.mem s₃.mem :=
    (fs.mono (by simp)).trans (I.frame.mono fun r hr => List.mem_cons_of_mem _ hr)
  obtain v0 : s₃.mem.readW (State.addr sp + BitVec.ofNat 64 0) 32 = D := by
    rw [fT.readW (r := ⟨State.addr sp + BitVec.ofNat 64 0, 4⟩) (Region.contains_self _ _)
      (fun r hr => (dA r hr).sub_left (Offset.sub_base _ (by decide))) (by decide), BitVec.add_zero, h.a0]
  obtain v4 : s₃.mem.readW (State.addr sp + BitVec.ofNat 64 4) 32 = BitVec.ofNat 32 n := by
    rw [fT.readW (r := ⟨State.addr sp + BitVec.ofNat 64 4, 4⟩) (Region.contains_self _ _)
      (fun r hr => (dA r hr).sub_left (Offset.sub_base _ (by decide))) (by decide), h.a1]
  have hsp₃ : s₃.sp = sp := I.env.sp
  refine wp_ldrSp (a := State.addr sp + BitVec.ofNat 64 0) (by decide)
    (by rw [hsp₃]; exact addr_add (by have := h.afit; omega_arith))
    (by rw [I.rd, I.wr]; exact in_off h.args (by decide) (by decide)) fun s₄ u₄ => ?_
  refine wp_ldrSp (a := State.addr sp + BitVec.ofNat 64 4) (by decide)
    (by rw [u₄.sp, hsp₃]; exact addr_add (by have := h.afit; omega_arith))
    (by rw [u₄.rd, u₄.wr, I.rd, I.wr]; exact in_off h.args (by decide) (by decide)) fun s₅ u₅ => WP.block_nil ?_
  obtain dc : ∀ r ∈ [savedR w], (⟨State.addr c, 512⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact L.c0_w' (by decide) (by decide)
  refine ⟨mₛ, fs, sv, I.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> rw [u₅.other _ (by decide), u₄.other _ (by decide)])
      (by rw [u₅.sp, u₄.sp]) (by rw [u₅.rd, u₄.rd]) (by rw [u₅.wr, u₄.wr]),
    by rw [u₅.rd, u₄.rd, I.rd], by rw [u₅.wr, u₄.wr, I.wr], by rw [u₅.other _ (by decide), u₄.gpr, v0],
    by rw [u₅.gpr, u₄.mem, v4], by rw [u₅.mem, u₄.mem]; exact I.frame, ?_⟩
  rw [u₅.mem, u₄.mem, I.acc, List.take_of_length_le (by rw [length_components]), ctxMac_frame fs dc hRb,
    components_frame fs (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.ads.dw.sub_right (Lay.wSub (by decide)))
      (fun i hi r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (h.ads.comp i hi).w.sub_right (Lay.wSub (by decide)))]

/-- `sivOut`: the IV at `W` copied to `T`, the stack argument at `[sp + 8]`. -/
theorem sivOut_ok {s : State} (he : Env c w sp R s) {T : BitVec 32}
    (hTi : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 8)) 4)
    (hTv : s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 8)) 32 = T)
    (hTw : Covers [⟨State.addr T, 16⟩] s.wr) (hTf : T.toNat + 16 ≤ 2 ^ 32)
    (hTd : (⟨State.addr T, 16⟩ : Region).Disjoint ⟨State.addr w, 16⟩) :
    ∃ s', runBlock isa sivOut s = some s' ∧ bytesAt s'.mem (State.addr T) 16 = bytesAt s.mem (State.addr w) 16 ∧
      Frame [⟨State.addr T, 16⟩] s.mem s'.mem ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have h11 := he.r11
  obtain eW : ∀ d, d < 2576 → State.addr (w + BitVec.ofNat 32 d) = State.addr w + BitVec.ofNat 64 d :=
    fun d hd => L.wA hd
  obtain eT : ∀ d, d < 16 → State.addr (T + BitVec.ofNat 32 d) = State.addr T + BitVec.ofNat 64 d :=
    fun d hd => addr_add (by omega_arith)
  obtain r₀ := he.perm.wR (show 0 + 4 ≤ 2576 by decide)
  obtain r₁ := he.perm.wR (show 4 + 4 ≤ 2576 by decide)
  obtain r₂ := he.perm.wR (show 8 + 4 ≤ 2576 by decide)
  obtain r₃ := he.perm.wR (show 12 + 4 ≤ 2576 by decide)
  obtain w₀ := in_off hTw (show 0 + 4 ≤ 16 by decide) (by decide)
  obtain w₁ := in_off hTw (show 4 + 4 ≤ 16 by decide) (by decide)
  obtain w₂ := in_off hTw (show 8 + 4 ≤ 16 by decide) (by decide)
  obtain w₃ := in_off hTw (show 12 + 4 ≤ 16 by decide) (by decide)
  obtain q : ∀ (m : Mem) (a b : Nat) (v : BitVec 32), a + 4 ≤ 16 → b + 4 ≤ 16 →
      (m.writeW (State.addr T + BitVec.ofNat 64 b) v).readW (State.addr w + BitVec.ofNat 64 a) 32 =
        m.readW (State.addr w + BitVec.ofNat 64 a) 32 := fun m a b v ha hb =>
    sepW (m := m) ((hTd.symm.sub_left (Offset.sub_base _ ha)).sub_right (Offset.sub_base _ hb))
  obtain p₁ := fun m v => q m 4 0 v (by decide) (by decide)
  obtain p₂ := fun m v => q m 8 0 v (by decide) (by decide)
  obtain p₃ := fun m v => q m 8 4 v (by decide) (by decide)
  obtain p₄ := fun m v => q m 12 0 v (by decide) (by decide)
  obtain p₅ := fun m v => q m 12 4 v (by decide) (by decide)
  obtain p₆ := fun m v => q m 12 8 v (by decide) (by decide)
  obtain ⟨s', run, hm, hg, hk⟩ : ∃ s', runBlock isa sivOut s = some s' ∧
      s'.mem = store4 s.mem (State.addr T + BitVec.ofNat 64 0) (s.mem.readW (State.addr w + BitVec.ofNat 64 0) 32)
        (s.mem.readW (State.addr w + BitVec.ofNat 64 4) 32) (s.mem.readW (State.addr w + BitVec.ofNat 64 8) 32)
        (s.mem.readW (State.addr w + BitVec.ofNat 64 12) 32) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
    refine ⟨_, by simp only [sivOut]; arun [hTi, hTv, h11, eW, eT, r₀, r₁, r₂, r₃, w₀, w₁, w₂, w₃, p₁, p₂, p₃, p₄,
      p₅, p₆], ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_store, store4_eq, add_ofNat_assoc]
    · intro r a b; simp [gpr_setReg, a, b]
    · exact ⟨rfl, rfl, rfl⟩
  simp only [add_ofNat_zero] at hm
  refine ⟨s', run, by rw [hm]; exact bytesAt_copy4 _ _ _, by rw [hm]; exact Proof.Cmac.frame_store4 _ _ _ _ _, hg,
    hk.1, hk.2.1, hk.2.2⟩

/-- `sivIn`: the IV at `T`, the stack argument at `[sp + 8]`, copied to `W`. -/
theorem sivIn_ok {s : State} (he : Env c w sp R s) {T : BitVec 32}
    (hTi : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 8)) 4)
    (hTv : s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 8)) 32 = T)
    (hTr : Covers [⟨State.addr T, 16⟩] (s.rd ++ s.wr)) (hTf : T.toNat + 16 ≤ 2 ^ 32)
    (hTd : (⟨State.addr T, 16⟩ : Region).Disjoint ⟨State.addr w, 16⟩) :
    ∃ s', runBlock isa sivIn s = some s' ∧ bytesAt s'.mem (State.addr w) 16 = bytesAt s.mem (State.addr T) 16 ∧
      Frame [⟨State.addr w, 16⟩] s.mem s'.mem ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have h11 := he.r11
  obtain eW : ∀ d, d < 2576 → State.addr (w + BitVec.ofNat 32 d) = State.addr w + BitVec.ofNat 64 d :=
    fun d hd => L.wA hd
  obtain eT : ∀ d, d < 16 → State.addr (T + BitVec.ofNat 32 d) = State.addr T + BitVec.ofNat 64 d :=
    fun d hd => addr_add (by omega_arith)
  obtain r₀ := in_off hTr (show 0 + 4 ≤ 16 by decide) (by decide)
  obtain r₁ := in_off hTr (show 4 + 4 ≤ 16 by decide) (by decide)
  obtain r₂ := in_off hTr (show 8 + 4 ≤ 16 by decide) (by decide)
  obtain r₃ := in_off hTr (show 12 + 4 ≤ 16 by decide) (by decide)
  obtain w₀ := he.perm.wW (show 0 + 4 ≤ 2576 by decide)
  obtain w₁ := he.perm.wW (show 4 + 4 ≤ 2576 by decide)
  obtain w₂ := he.perm.wW (show 8 + 4 ≤ 2576 by decide)
  obtain w₃ := he.perm.wW (show 12 + 4 ≤ 2576 by decide)
  obtain q : ∀ (m : Mem) (a b : Nat) (v : BitVec 32), a + 4 ≤ 16 → b + 4 ≤ 16 →
      (m.writeW (State.addr w + BitVec.ofNat 64 b) v).readW (State.addr T + BitVec.ofNat 64 a) 32 =
        m.readW (State.addr T + BitVec.ofNat 64 a) 32 := fun m a b v ha hb =>
    sepW (m := m) ((hTd.sub_left (Offset.sub_base _ ha)).sub_right (Offset.sub_base _ hb))
  obtain p₁ := fun m v => q m 4 0 v (by decide) (by decide)
  obtain p₂ := fun m v => q m 8 0 v (by decide) (by decide)
  obtain p₃ := fun m v => q m 8 4 v (by decide) (by decide)
  obtain p₄ := fun m v => q m 12 0 v (by decide) (by decide)
  obtain p₅ := fun m v => q m 12 4 v (by decide) (by decide)
  obtain p₆ := fun m v => q m 12 8 v (by decide) (by decide)
  obtain ⟨s', run, hm, hg, hk⟩ : ∃ s', runBlock isa sivIn s = some s' ∧
      s'.mem = store4 s.mem (State.addr w + BitVec.ofNat 64 0) (s.mem.readW (State.addr T + BitVec.ofNat 64 0) 32)
        (s.mem.readW (State.addr T + BitVec.ofNat 64 4) 32) (s.mem.readW (State.addr T + BitVec.ofNat 64 8) 32)
        (s.mem.readW (State.addr T + BitVec.ofNat 64 12) 32) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
    refine ⟨_, by simp only [sivIn]; arun [hTi, hTv, h11, eW, eT, r₀, r₁, r₂, r₃, w₀, w₁, w₂, w₃, p₁, p₂, p₃, p₄,
      p₅, p₆], ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_store, store4_eq, add_ofNat_assoc]
    · intro r a b; simp [gpr_setReg, a, b]
    · exact ⟨rfl, rfl, rfl⟩
  simp only [add_ofNat_zero] at hm
  refine ⟨s', run, by rw [hm]; exact bytesAt_copy4 _ _ _, by rw [hm]; exact Proof.Cmac.frame_store4 _ _ _ _ _, hg,
    hk.1, hk.2.1, hk.2.2⟩

/-- `vg_aes_siv_encrypt`: the synthetic IV at `T` and the ciphertext in place. -/
theorem encrypt_wp {a D T : BitVec 32} {N n : Nat} {s : State} (h : EPre c w sp a D T R N n s)
    (hTw : Covers [⟨State.addr T, 16⟩] s.wr) (hTd : (⟨State.addr T, 16⟩ : Region).Disjoint ⟨State.addr D, n⟩) :
    WP isa encrypt s fun s' => abiPreserved s s' ∧
      Spec.Siv.encryptWith (Spec.Siv.ctxMac s.mem (State.addr c) R) (Spec.Siv.ctxCiph s.mem (State.addr c) R)
          (Spec.Siv.components 32 s.mem (State.addr a) N) (bytesAt s.mem (State.addr D) n) =
        (bytesAt s'.mem (State.addr T) 16, bytesAt s'.mem (State.addr D) n) := by
  have hR := h.rounds
  obtain hRb := rounds_le hR
  have ww := L.ww
  refine WP.seq (WP.mono (s2v_ok L h) fun s₁ ⟨mₛ, O⟩ => ?_)
  obtain hD₁ : Dat c w sp s₁ D n := h.data.of_eq O.rd O.wr
  refine WP.seq (WP.mono (finish_ok L O.env hR hD₁.buf h.n32 O.r6 O.r5 (out := 0) (.inl rfl))
    fun s₂ ⟨he₂, rd₂, wr₂, g₂, f₂, o₂⟩ => ?_)
  -- The memory before CTR.
  obtain f₀₁ : Frame (savedR w :: oR w sp 0) s.mem s₁.mem :=
    (O.fs.mono (by simp)).trans ((frame_oR 0 O.frame).mono fun r hr => List.mem_cons_of_mem _ hr)
  obtain f₀₂ : Frame (savedR w :: oR w sp 0) s.mem s₂.mem :=
    (O.fs.mono (by simp)).trans (((frame_oR 0 O.frame).trans f₂).mono fun r hr => List.mem_cons_of_mem _ hr)
  obtain dA : ∀ r ∈ savedR w :: oR w sp 0, (⟨State.addr sp, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact h.args_w.sub_right (Lay.wSub (by decide))
    · exact h.args_w.sub_right (Lay.wSub (by decide))
    · exact h.args_w.sub_right (Lay.wSub (by decide))
    · exact h.args_w.sub_right (Lay.wSub (by decide))
    · exact Offset.base_disjoint_below (State.addr sp) (n := 16) (k := 16) (by decide)
  obtain dD : ∀ r ∈ savedR w :: oR w sp 0, (⟨State.addr D, n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact h.data.buf.w.sub_right (Lay.wSub (by decide))
    · exact h.data.buf.w.sub_right (Lay.wSub (by decide))
    · exact h.data.buf.w.sub_right (Lay.wSub (by decide))
    · exact h.data.buf.w.sub_right (Lay.wSub (by decide))
    · exact h.data.buf.stk.symm
  obtain dc : ∀ r ∈ savedR w :: oR w sp 0, (⟨State.addr c, 512⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact L.c0_w' (by decide) (by decide)
    · exact L.c0_w' (by decide) (by decide)
    · exact L.c0_w' (by decide) (by decide)
    · exact L.c0_w' (by decide) (by decide)
    · exact L.stk_c.symm
  obtain hm0 : s₂.mem.readW (State.addr sp) 32 = D := by
    rw [f₀₂.readW (r := ⟨State.addr sp, 4⟩) (Region.contains_self _ _)
      (fun r hr => (dA r hr).sub_left (Region.sub_prefix (by decide))) (by decide), h.a0]
  obtain hm1 : s₂.mem.readW (State.addr sp + BitVec.ofNat 64 4) 32 = BitVec.ofNat 32 n := by
    rw [f₀₂.readW (r := ⟨State.addr sp + BitVec.ofNat 64 4, 4⟩) (Region.contains_self _ _)
      (fun r hr => (dA r hr).sub_left (Offset.sub_base _ (by decide))) (by decide), h.a1]
  obtain hD₂ : Dat c w sp s₂ D n := hD₁.of_eq rd₂ wr₂
  refine WP.seq (WP.mono (ctr_ok L he₂ hR hD₂ h.n32 h.afit (by rw [rd₂, wr₂, O.rd, O.wr]; exact h.args) h.args_w
    hm0 hm1) fun s₃ ⟨he₃, rd₃, wr₃, g₃, h6₃, h5₃, f₃, d₃⟩ => ?_)
  -- The saved registers are where the save put them.
  obtain dS : ∀ r ∈ ctrR w sp D n, (savedR w).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w' (by decide)).symm
    · exact (h.data.buf.w.sub_right (Lay.wSub (by decide))).symm
  obtain sv₃ : SavedAt s₃.mem w s := (O.sv.frame ((frame_oR 0 O.frame).trans f₂) fun r hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact saved_wR L r hr).frame f₃ dS
  -- The IV copied to `siv`.
  obtain eA : ∀ r ∈ ctrR w sp D n, (⟨State.addr sp, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.args_w.sub_right (Lay.wSub (by decide))
    · exact h.args_w.sub_right (Lay.wSub (by decide))
    · exact Offset.base_disjoint_below (State.addr sp) (n := 16) (k := 16) (by decide)
    · exact h.args_d
  obtain a8 : State.addr (s₃.sp + BitVec.ofNat 32 8) = State.addr sp + BitVec.ofNat 64 8 := by
    rw [he₃.sp]; exact addr_add (by have := h.afit; omega_arith)
  obtain v8 : s₃.mem.readW (State.addr (s₃.sp + BitVec.ofNat 32 8)) 32 = T := by
    rw [a8, f₃.readW (r := ⟨State.addr sp + BitVec.ofNat 64 8, 4⟩) (Region.contains_self _ _)
      (fun r hr => (eA r hr).sub_left (Offset.sub_base _ (by decide))) (by decide),
      f₀₂.readW (r := ⟨State.addr sp + BitVec.ofNat 64 8, 4⟩) (Region.contains_self _ _)
      (fun r hr => (dA r hr).sub_left (Offset.sub_base _ (by decide))) (by decide), h.a2]
  obtain i8 : InRegions (s₃.rd ++ s₃.wr) (State.addr (s₃.sp + BitVec.ofNat 32 8)) 4 := by
    rw [a8, rd₃, wr₃, rd₂, wr₂, O.rd, O.wr]
    exact in_off h.args (by decide) (by decide)
  obtain ⟨s₄, run₄, iv₄, fo₄, g₄, rd₄, wr₄, sp₄⟩ := sivOut_ok L he₃ i8 v8
    (by rw [wr₃, wr₂, O.wr]; exact hTw) h.tfit (h.t_w.sub_right (Region.sub_prefix (by decide)))
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  obtain he₄ : Env c w sp R s₄ := he₃.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₄ _ (by decide) (by decide)) sp₄ rd₄ wr₄
  obtain sv₄ : SavedAt s₄.mem w s := sv₃.frame fo₄ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (h.t_w.sub_right (Lay.wSub (by decide))).symm
  refine WP.mono (restore_ok (s₀ := s) he₄.r11 (by omega_arith)
    (by rw [rd₄, wr₄, rd₃, wr₃, rd₂, wr₂, O.rd, O.wr]; exact covers_left (covers_prefix h.perm.w (by decide)))
    sv₄ (by rw [he₄.sp, h.hsp])) fun s₅ ⟨ab, m₅, _, _, _⟩ => ⟨ab, ?_⟩
  obtain pD : bytesAt s₄.mem (State.addr D) n = bytesAt s₃.mem (State.addr D) n :=
    bytesAt_frame fo₄ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hTd.symm)
      (by have := h.data.buf.lt; omega_arith)
  -- The values.
  obtain dW : ∀ r ∈ ctrR w sp D n, (⟨State.addr w, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa using L.w_w (a := 0) (n := 16) (.inl (by decide)) (by decide) (by decide)
    · simpa using L.w_w (a := 0) (n := 16) (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w.sub_right (Region.sub_prefix (by decide))).symm
    · exact (h.data.buf.w.sub_right (Region.sub_prefix (by decide))).symm
  obtain iv : bytesAt s₃.mem (State.addr w) 16 = bytesAt s₂.mem (State.addr w) 16 :=
    bytesAt_frame f₃ dW (by decide)
  obtain mac₁ : Spec.Siv.ctxMac s₁.mem (State.addr c) R = Spec.Siv.ctxMac s.mem (State.addr c) R :=
    ctxMac_frame f₀₁ dc hRb
  obtain ciph₂ : Spec.Siv.ctxCiph s₂.mem (State.addr c) R = Spec.Siv.ctxCiph s.mem (State.addr c) R :=
    ctxCiph_frame f₀₂ dc hRb
  obtain p₁ : bytesAt s₁.mem (State.addr D) n = bytesAt s.mem (State.addr D) n :=
    bytesAt_frame f₀₁ dD
      (by have := h.data.buf.lt; omega_arith)
  obtain p₂ : bytesAt s₂.mem (State.addr D) n = bytesAt s.mem (State.addr D) n :=
    bytesAt_frame f₀₂ dD (by have := h.data.buf.lt; omega_arith)
  rw [BitVec.add_zero] at o₂
  rw [m₅, iv₄, pD, Spec.Siv.encryptWith_eq, Spec.Siv.sealWith, d₃, iv, o₂, mac₁, O.acc, p₁, ciph₂, p₂]

end

end VG.Proof.AesSiv.Arm

end

end

/-!
# AES-SIV on ARMv7: `vg_aes_siv_decrypt`

Untrusted: everything here is checked by Lean. `decrypt` runs S2V over the
associated data (`s2v_ok`), copies the received IV from `siv` to `W`
(`sivIn_ok`), decrypts the data with CTR from it (`ctr_ok`), finishes S2V with the plaintext into `W + 112`
(`finish_ok`), sets `r0` to 1 if the two IVs are equal and 0 if not,
without a branch (`compare_ok`), ANDs every byte of the plaintext with
`0 − r0` (`maskData_ok`) and restores the registers (`decrypt_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesSiv.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.Arm (imm addI)
open VG.Proof.AesCcm.Arm (blw mask_byte length_mask mask_succ)
open VG.Proof.AesGcm.Arm (bytesAt_frame SavedAt savedR restore_ok covers_left covers_prefix in_off)
open VG.Proof.MdStream.Arm (wp_ldrSp)
open VG.Proof.AesGcm.Arm (Keeps z_subFlags gpr_subFlags z_cmp eval_eq' eval_ne' addr_i dec32 z_dec in_of_covers
  bytesAt_succ mem_store gpr_store add32_ofNat_assoc in_left add_ofNat_zero mem_subFlags bytes_words cmp_value
  words_eq_iff runBlock_app_of add_ofNat_assoc)

section
variable {c w sp : BitVec 32} {R : Nat} (L : Lay c w sp)
include L

/-- `compare`: `r0` is 1 iff the 16 bytes at `W` and `W + 112` are equal. -/
theorem compare_ok {s : State} (he : Env c w sp R s) :
    ∃ s', runBlock isa compare s = some s' ∧
      s'.gpr .r0 = (if bytesAt s.mem (State.addr w + BitVec.ofNat 64 0) 16 =
        bytesAt s.mem (State.addr w + BitVec.ofNat 64 tOff) 16 then 1 else 0) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  have h11 := he.r11
  obtain r₀ := he.perm.wR (show 0 + 4 ≤ 2576 by decide)
  obtain r₁ := he.perm.wR (show 4 + 4 ≤ 2576 by decide)
  obtain r₂ := he.perm.wR (show 8 + 4 ≤ 2576 by decide)
  obtain r₃ := he.perm.wR (show 12 + 4 ≤ 2576 by decide)
  obtain q₀ := he.perm.wR (show 112 + 4 ≤ 2576 by decide)
  obtain q₁ := he.perm.wR (show 116 + 4 ≤ 2576 by decide)
  obtain q₂ := he.perm.wR (show 120 + 4 ≤ 2576 by decide)
  obtain q₃ := he.perm.wR (show 124 + 4 ≤ 2576 by decide)
  let m := s.mem
  let a := fun k : Nat => m.readW (State.addr w + BitVec.ofNat 64 (4 * k)) 32
  let b := fun k : Nat => m.readW (State.addr w + BitVec.ofNat 64 (112 + 4 * k)) 32
  obtain ⟨s₁, run₁, g₁, h0₁, k₁⟩ : ∃ s₁, runBlock isa (xorW .r0 0 ++ xorW .r1 1 ++ [.dp .orr .r0 .r0 (.reg .r1)]) s =
      some s₁ ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → s₁.gpr r = s.gpr r) ∧
      s₁.gpr .r0 = (a 0 ^^^ b 0 ||| a 1 ^^^ b 1) ∧ Keeps s s₁ := by
    refine ⟨_, by simp only [xorW, tOff]; arun [h11, L.wA, r₀, r₁, q₀, q₁], ?_, ?_, ?_⟩
    · intro r x y z; simp [gpr_setReg, x, y, z]
    · simp [gpr_setReg, a, b, m]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  obtain h11₁ : s₁.gpr .r11 = w := by rw [g₁ _ (by decide) (by decide) (by decide), h11]
  have hm₁ := k₁.mem
  obtain ⟨s₂, run₂, g₂, h0₂, k₂⟩ : ∃ s₂, runBlock isa (xorW .r1 2 ++ [.dp .orr .r0 .r0 (.reg .r1)] ++ xorW .r1 3 ++
      [.dp .orr .r0 .r0 (.reg .r1)]) s₁ = some s₂ ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → s₂.gpr r = s₁.gpr r) ∧
      s₂.gpr .r0 = ((a 0 ^^^ b 0 ||| a 1 ^^^ b 1) ||| a 2 ^^^ b 2) ||| a 3 ^^^ b 3 ∧ Keeps s₁ s₂ := by
    rw [← k₁.rd, ← k₁.wr] at r₂ r₃ q₂ q₃
    refine ⟨_, by simp only [xorW, tOff]; arun [h11₁, L.wA, r₂, r₃, q₂, q₃, hm₁], ?_, ?_, ?_⟩
    · intro r x y z; simp [gpr_setReg, x, y, z]
    · simp [gpr_setReg, a, b, m, h0₁, hm₁]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨s₃, run₃, g₃, h0₃, k₃⟩ : ∃ s₃, runBlock isa [.mov .r1 (imm 0), .dp .sub .r1 .r1 (.reg .r0),
      .dp .orr .r0 .r0 (.reg .r1), .mov .r0 (.shifted .r0 .lsr 31), .mov .r1 (imm 1), .dp .sub .r0 .r1 (.reg .r0)] s₂ =
      some s₃ ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → s₃.gpr r = s₂.gpr r) ∧
      s₃.gpr .r0 = BitVec.ofNat 32 1 - ((s₂.gpr .r0 ||| (BitVec.ofNat 32 0 - s₂.gpr .r0)) >>> 31) ∧ Keeps s₂ s₃ := by
    refine ⟨_, by arun [], ?_, ?_, ?_⟩
    · intro r x y; simp [gpr_setReg, x, y]
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, Op2.eval]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine ⟨s₃, ?_, ?_, ?_, k₁.trans (k₂.trans k₃)⟩
  · rw [show compare = (xorW .r0 0 ++ xorW .r1 1 ++ [.dp .orr .r0 .r0 (.reg .r1)]) ++
      ((xorW .r1 2 ++ [.dp .orr .r0 .r0 (.reg .r1)] ++ xorW .r1 3 ++ [.dp .orr .r0 .r0 (.reg .r1)]) ++
      [.mov .r1 (imm 0), .dp .sub .r1 .r1 (.reg .r0), .dp .orr .r0 .r0 (.reg .r1), .mov .r0 (.shifted .r0 .lsr 31),
        .mov .r1 (imm 1), .dp .sub .r0 .r1 (.reg .r0)]) from rfl]
    exact runBlock_app_of run₁ (runBlock_app_of run₂ run₃)
  · rw [h0₃, h0₂, cmp_value, bytes_words, bytes_words]
    simp only [add_ofNat_assoc]
    congr 1
    simp only [a, b, m, tOff, Nat.mul_zero, Nat.add_zero]
    exact propext (words_eq_iff _ _ _ _ _ _ _ _).symm
  · intro r x y z; rw [g₃ r x y, g₂ r x y z, g₁ r x y z]

omit L in
theorem maskStep_ok (s : State) {D : BitVec 32} {i n : Nat} {ok : Bool} (h6 : s.gpr .r6 = D + BitVec.ofNat 32 i)
    (h5 : s.gpr .r5 = BitVec.ofNat 32 (n - i)) (h1 : s.gpr .r1 = 0 - (if ok then 1 else 0))
    (r : InRegions (s.rd ++ s.wr) (State.addr (D + BitVec.ofNat 32 i)) 1)
    (w : InRegions s.wr (State.addr (D + BitVec.ofNat 32 i)) 1) :
    ∃ s', runBlock isa [.ldrb .r12 .r6 0, .dp .and .r12 .r12 (.reg .r1), .strb .r12 .r6 0, addI .r6 .r6 1,
        .subs .r5 .r5 (imm 1)] s = some s' ∧
      s'.mem = s.mem.writeW (State.addr (D + BitVec.ofNat 32 i))
        ((if ok then s.mem (State.addr (D + BitVec.ofNat 32 i)) else 0 : Byte)) ∧
      s'.gpr .r6 = D + BitVec.ofNat 32 (i + 1) ∧ s'.gpr .r5 = BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 ∧
      s'.z = (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) ∧
      (∀ r, r ≠ .r5 → r ≠ .r6 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine ⟨_, by arun [h6, h5, add_ofNat_zero, r, w], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_subFlags, mem_store, gpr_setReg, gpr_store, ite_true, ite_false, reduceCtorEq, h1,
      mask_byte]
  · simp [gpr_setReg, h6, add32_ofNat_assoc]
  · simp [gpr_setReg, h5]
  · simp [z_setReg, h5]
  · intro r a b d; simp [gpr_setReg, a, b, d]
  all_goals rfl

omit L in
/-- `maskData`: every byte of the data (`n` bytes at `D`, in `r6` and `r5`)
ANDed with `0 − ok`, for `ok ∈ {0, 1}` in `r0`: kept if `ok = 1`, zeroed if
`ok = 0`. -/
theorem maskData_ok {s : State} (he : Env c w sp R s) {D : BitVec 32} {n : Nat} (hD : Dat c w sp s D n)
    (hn32 : n < 2 ^ 32) (h6 : s.gpr .r6 = D) (h5 : s.gpr .r5 = BitVec.ofNat 32 n) {ok : Bool}
    (h0 : s.gpr .r0 = if ok then 1 else 0) :
    WP isa maskData s fun s' => Env c w sp R s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .r1 → r ≠ .r5 → r ≠ .r6 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.mem = writeBytes s.mem (State.addr D) (if ok then bytesAt s.mem (State.addr D) n else Spec.Ccm.zeros n) := by
  have hn := hD.buf.fit
  obtain ⟨s₁, run₁, h1₁, hz₁, g₁, k₁⟩ : ∃ s₁, runBlock isa [.mov .r1 (imm 0), .dp .sub .r1 .r1 (.reg .r0),
      .cmp .r5 (imm 0)] s = some s₁ ∧ s₁.gpr .r1 = 0 - (if ok then 1 else 0) ∧
      s₁.z = decide (n = 0) ∧ (∀ r, r ≠ .r1 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
    refine ⟨_, by arun [], ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h0, imm]
    · simp only [z_subFlags, gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, h5, imm]
      rw [z_cmp hn32 (by decide)]
    · intro r a; simp [gpr_setReg, a]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  have he₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₁ _ (by decide)) k₁.sp k₁.rd k₁.wr
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (n = 0)) (eval_eq' hz₁) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hn0 : n = 0 := by simpa using hb
    subst hn0
    refine ⟨he₁, k₁.rd, k₁.wr, fun r a _ _ _ => g₁ r a, ?_⟩
    rw [k₁.mem]; cases ok <;> simp [bytesAt, Spec.Ccm.zeros, writeBytes_nil]
  have hn0 : 0 < n := by have : n ≠ 0 := by simpa using hb
                         omega_arith
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ j, k = n - j ∧ j < n ∧ t.gpr .r6 = D + BitVec.ofNat 32 j ∧
      t.gpr .r5 = BitVec.ofNat 32 (n - j) ∧
      t.mem = writeBytes s.mem (State.addr D) (if ok then bytesAt s.mem (State.addr D) j else Spec.Ccm.zeros j) ∧
      (∀ r, r ≠ .r5 → r ≠ .r6 → r ≠ .r12 → t.gpr r = s₁.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp) ?_
    (n - 0) _
    ⟨0, rfl, hn0, by rw [g₁ _ (by decide), h6, add_ofNat_zero], by rw [g₁ _ (by decide), h5]; rfl,
      by rw [k₁.mem]; cases ok <;> simp [bytesAt, Spec.Ccm.zeros, writeBytes_nil], fun r _ _ _ => rfl, k₁.rd, k₁.wr,
      k₁.sp⟩
  rintro m t ⟨j, rfl, hj, r6, r5, mem, g, rd, wr, sp⟩
  have aD := addr_i hn hj
  obtain ⟨t', run', mem', r6', r5', z', g', rd', wr', sp'⟩ := maskStep_ok t (ok := ok) r6 r5
    (by rw [g _ (by decide) (by decide) (by decide), h1₁])
    (by rw [rd, wr, aD]; exact in_of_covers hD.buf.rd hj (by omega_arith))
    (by rw [wr, aD]; exact in_of_covers hD.wr hj (by omega_arith))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have fr : Frame [⟨State.addr D, j⟩] s.mem t.mem := by
    rw [mem]; exact writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)
  have hq : t.mem (State.addr D + BitVec.ofNat 64 j) = s.mem (State.addr D + BitVec.ofNat 64 j) :=
    fr _ fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains, Mem.sub_ofNat_toNat (State.addr D) (show j < 2 ^ 64 by omega_arith)] at hcon; omega_arith
  have hmem : t'.mem = writeBytes s.mem (State.addr D)
      (if ok then bytesAt s.mem (State.addr D) (j + 1) else Spec.Ccm.zeros (j + 1)) := by
    rw [mem', aD, hq, mem, mask_succ, writeBytes_snoc _ _ _ _ (by rw [length_mask]; omega_arith), length_mask]
  have hz : t'.z = decide (j + 1 = n) := by rw [z', dec32 hj hn32, z_dec hj hn32]
  have gg : ∀ r, r ≠ .r5 → r ≠ .r6 → r ≠ .r12 → t'.gpr r = s₁.gpr r := fun r a b d => by
    rw [g' r a b d, g r a b d]
  have ev : isa.eval .ne t' = some !decide (j + 1 = n) := eval_ne' hz
  by_cases hjn : j + 1 = n
  · left
    refine ⟨by rw [ev]; simp [hjn], he₁.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact gg _ (by decide) (by decide) (by decide))
      (by rw [sp', sp, ← k₁.sp]) (by rw [rd', rd, k₁.rd]) (by rw [wr', wr, k₁.wr]), by rw [rd', rd],
      by rw [wr', wr], fun r a b d e => by rw [gg r b d e, g₁ r a], by rw [hmem, hjn]⟩
  · right
    refine ⟨by rw [ev]; simp [hjn], n - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, r6',
      by rw [r5', dec32 hj hn32], hmem, gg, by rw [rd', rd], by rw [wr', wr], by rw [sp', sp]⟩

/-- Decryption before the comparison: the received IV at `W`, from `T`, the
plaintext `p` at `D` and S2V's result for it at `W + 112`, the saved
registers and the data's address and length where they were. -/
structure OMid (c w sp a D T : BitVec 32) (R N n : Nat) (s s' : State) : Prop where
  env : Env c w sp R s'
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sv : SavedAt s'.mem w s
  a0 : s'.mem.readW (State.addr sp) 32 = D
  a1 : s'.mem.readW (State.addr sp + BitVec.ofNat 64 4) 32 = BitVec.ofNat 32 n
  iv : bytesAt s'.mem (State.addr w + BitVec.ofNat 64 0) 16 = bytesAt s.mem (State.addr T) 16
  pt : bytesAt s'.mem (State.addr D) n = Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem (State.addr c) R)
    (Spec.Siv.counter (bytesAt s.mem (State.addr T) 16)) (bytesAt s.mem (State.addr D) n)
  tag : bytesAt s'.mem (State.addr w + BitVec.ofNat 64 tOff) 16 =
    Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem (State.addr c) R)
      (Spec.Siv.s2vAcc (Spec.Siv.ctxMac s.mem (State.addr c) R) (Spec.Siv.components 32 s.mem (State.addr a) N))
      (bytesAt s'.mem (State.addr D) n)

/-- S2V of the associated data, the received IV copied from `siv`, CTR from it
and S2V's end with the plaintext. -/
theorem front_ok {a D T : BitVec 32} {N n : Nat} {s : State} (h : EPre c w sp a D T R N n s) {rest : Prog isa}
    {Q : State → Prop} (k : ∀ s', OMid c w sp a D T R N n s s' → WP isa rest s' Q) :
    WP isa (.seq encS2v (.seq (.block sivIn) (.seq (ctr 0) (.seq (.block [.ldrSp .r6 0, .ldrSp .r5 4])
      (.seq (finish tOff) rest))))) s Q := by
  have hR := h.rounds
  obtain hRb := rounds_le hR
  have ww := L.ww
  refine WP.seq (WP.mono (s2v_ok L h) fun s₀ ⟨mₛ, O⟩ => ?_)
  obtain f₀₀ : Frame (savedR w :: wR w sp) s.mem s₀.mem :=
    (O.fs.mono (by simp)).trans (O.frame.mono fun r hr => List.mem_cons_of_mem _ hr)
  obtain dA₀ : ∀ r ∈ savedR w :: wR w sp, (⟨State.addr sp, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.args_w.sub_right (Lay.wSub (by decide))
    · exact h.args_w.sub_right (Lay.wSub (by decide))
    · exact h.args_w.sub_right (Lay.wSub (by decide))
    · exact Offset.base_disjoint_below (State.addr sp) (n := 16) (k := 16) (by decide)
  obtain dT₀ : ∀ r ∈ savedR w :: wR w sp, (⟨State.addr T, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.t_w.sub_right (Lay.wSub (by decide))
    · exact h.t_w.sub_right (Lay.wSub (by decide))
    · exact h.t_w.sub_right (Lay.wSub (by decide))
    · exact h.t_stk.symm
  -- The received IV copied from `siv`.
  obtain a8 : State.addr (s₀.sp + BitVec.ofNat 32 8) = State.addr sp + BitVec.ofNat 64 8 := by
    rw [O.env.sp]; exact addr_add (by have := h.afit; omega_arith)
  obtain v8 : s₀.mem.readW (State.addr (s₀.sp + BitVec.ofNat 32 8)) 32 = T := by
    rw [a8, f₀₀.readW (r := ⟨State.addr sp + BitVec.ofNat 64 8, 4⟩) (Region.contains_self _ _)
      (fun r hr => (dA₀ r hr).sub_left (Offset.sub_base _ (by decide))) (by decide), h.a2]
  obtain i8 : InRegions (s₀.rd ++ s₀.wr) (State.addr (s₀.sp + BitVec.ofNat 32 8)) 4 := by
    rw [a8, O.rd, O.wr]; exact in_off h.args (by decide) (by decide)
  obtain ⟨s₁, run₁, iv₀₁, fi, gi, rdi, wri, spi⟩ := sivIn_ok L O.env i8 v8 (by rw [O.rd, O.wr]; exact h.t_rd)
    h.tfit (h.t_w.sub_right (Region.sub_prefix (by decide)))
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain he₁ : Env c w sp R s₁ := O.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact gi _ (by decide) (by decide)) spi rdi wri
  obtain rd₁ : s₁.rd = s.rd := by rw [rdi, O.rd]
  obtain wr₁ : s₁.wr = s.wr := by rw [wri, O.wr]
  obtain hD₁ : Dat c w sp s₁ D n := h.data.of_eq rd₁ wr₁
  obtain w0 : ∀ {a k : Nat}, 16 ≤ a → a + k ≤ 2576 →
      (⟨State.addr w + BitVec.ofNat 64 a, k⟩ : Region).Disjoint ⟨State.addr w, 16⟩ := fun ha hk => by
    have := L.w_w (a := _) (n := _) (d := 0) (m := 16) (.inr ha) hk (by decide)
    rwa [add_ofNat_zero] at this
  obtain f₀₁ : Frame (⟨State.addr w, 16⟩ :: savedR w :: wR w sp) s.mem s₁.mem :=
    (f₀₀.mono fun r hr => List.mem_cons_of_mem _ hr).trans (fi.mono (by simp))
  obtain dA : ∀ r ∈ ⟨State.addr w, 16⟩ :: savedR w :: wR w sp, (⟨State.addr sp, 16⟩ : Region).Disjoint r := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact h.args_w.sub_right (Region.sub_prefix (by decide))
    · exact dA₀ r hr
  obtain dD : ∀ r ∈ ⟨State.addr w, 16⟩ :: savedR w :: wR w sp, (⟨State.addr D, n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact h.data.buf.w.sub_right (Region.sub_prefix (by decide))
    · exact h.data.buf.w.sub_right (Lay.wSub (by decide))
    · exact h.data.buf.w.sub_right (Lay.wSub (by decide))
    · exact h.data.buf.w.sub_right (Lay.wSub (by decide))
    · exact h.data.buf.stk.symm
  obtain dc : ∀ r ∈ ⟨State.addr w, 16⟩ :: savedR w :: wR w sp, (⟨State.addr c, 512⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact L.c_w.sub_right (Region.sub_prefix (by decide))
    · exact L.c0_w' (by decide) (by decide)
    · exact L.c0_w' (by decide) (by decide)
    · exact L.c0_w' (by decide) (by decide)
    · exact L.stk_c.symm
  obtain hm0 : s₁.mem.readW (State.addr sp) 32 = D := by
    rw [f₀₁.readW (r := ⟨State.addr sp, 4⟩) (Region.contains_self _ _)
      (fun r hr => (dA r hr).sub_left (Region.sub_prefix (by decide))) (by decide), h.a0]
  obtain hm1 : s₁.mem.readW (State.addr sp + BitVec.ofNat 64 4) 32 = BitVec.ofNat 32 n := by
    rw [f₀₁.readW (r := ⟨State.addr sp + BitVec.ofNat 64 4, 4⟩) (Region.contains_self _ _)
      (fun r hr => (dA r hr).sub_left (Offset.sub_base _ (by decide))) (by decide), h.a1]
  refine WP.seq (WP.mono (ctr_ok L he₁ hR hD₁ h.n32 h.afit (by rw [rd₁, wr₁]; exact h.args) h.args_w
    hm0 hm1) fun s₂ ⟨he₂, rd₂, wr₂, g₂, h6₂, h5₂, f₂, d₂⟩ => ?_)
  -- What CTR writes.
  obtain eA : ∀ r ∈ ctrR w sp D n, (⟨State.addr sp, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.args_w.sub_right (Lay.wSub (by decide))
    · exact h.args_w.sub_right (Lay.wSub (by decide))
    · exact Offset.base_disjoint_below (State.addr sp) (n := 16) (k := 16) (by decide)
    · exact h.args_d
  obtain eS : ∀ r ∈ ctrR w sp D n, (savedR w).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w' (by decide)).symm
    · exact (h.data.buf.w.sub_right (Lay.wSub (by decide))).symm
  obtain eW : ∀ {d : Nat}, d + 16 ≤ 80 ∨ 2432 ≤ d → d + 16 ≤ 2576 →
      ∀ r ∈ ctrR w sp D n, (⟨State.addr w + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := by
    intro d hd hd' r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.w_w (by simp only [ksOff]; omega_arith) hd' (by decide)
    · exact L.w_w (by omega_arith) hd' (by decide)
    · exact (L.stk_w' hd').symm
    · exact (h.data.buf.w.sub_right (Lay.wSub hd')).symm
  obtain ec : ∀ r ∈ ctrR w sp D n, (⟨State.addr c, 512⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.c0_w' (by decide) (by decide)
    · exact L.c0_w' (by decide) (by decide)
    · exact L.stk_c.symm
    · exact h.data.c
  obtain hm0₂ : s₂.mem.readW (State.addr sp + BitVec.ofNat 64 0) 32 = D := by
    rw [BitVec.add_zero, f₂.readW (r := ⟨State.addr sp, 4⟩) (Region.contains_self _ _)
      (fun r hr => (eA r hr).sub_left (Region.sub_prefix (by decide))) (by decide), hm0]
  obtain hm1₂ : s₂.mem.readW (State.addr sp + BitVec.ofNat 64 4) 32 = BitVec.ofNat 32 n := by
    rw [f₂.readW (r := ⟨State.addr sp + BitVec.ofNat 64 4, 4⟩) (Region.contains_self _ _)
      (fun r hr => (eA r hr).sub_left (Offset.sub_base _ (by decide))) (by decide), hm1]
  have hsp₂ : s₂.sp = sp := he₂.sp
  refine WP.seq ?_
  refine wp_ldrSp (a := State.addr sp + BitVec.ofNat 64 0) (by decide)
    (by rw [hsp₂]; exact addr_add (by have := h.afit; omega_arith))
    (by rw [rd₂, wr₂, rd₁, wr₁]; exact in_off h.args (by decide) (by decide)) fun s₃ u₃ => ?_
  refine wp_ldrSp (a := State.addr sp + BitVec.ofNat 64 4) (by decide)
    (by rw [u₃.sp, hsp₂]; exact addr_add (by have := h.afit; omega_arith))
    (by rw [u₃.rd, u₃.wr, rd₂, wr₂, rd₁, wr₁]; exact in_off h.args (by decide) (by decide))
    fun s₄ u₄ => WP.block_nil ?_
  obtain m₄ : s₄.mem = s₂.mem := by rw [u₄.mem, u₃.mem]
  obtain he₄ : Env c w sp R s₄ := he₂.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> rw [u₄.other _ (by decide), u₃.other _ (by decide)])
    (by rw [u₄.sp, u₃.sp]) (by rw [u₄.rd, u₃.rd]) (by rw [u₄.wr, u₃.wr])
  obtain rd₄ : s₄.rd = s.rd := by rw [u₄.rd, u₃.rd, rd₂, rd₁]
  obtain wr₄ : s₄.wr = s.wr := by rw [u₄.wr, u₃.wr, wr₂, wr₁]
  obtain hD₄ : Dat c w sp s₄ D n := h.data.of_eq rd₄ wr₄
  obtain h6₄ : s₄.gpr .r6 = D := by rw [u₄.other _ (by decide), u₃.gpr, hm0₂]
  obtain h5₄ : s₄.gpr .r5 = BitVec.ofNat 32 n := by rw [u₄.gpr, u₃.mem, hm1₂]
  refine WP.seq (WP.mono (finish_ok L he₄ hR hD₄.buf h.n32 h6₄ h5₄ (out := tOff) (.inr rfl))
    fun s₅ ⟨he₅, rd₅, wr₅, _, f₅, o₅⟩ => k s₅ ?_)
  obtain f₅' : Frame (wR w sp) s₄.mem s₅.mem := frame_oR_tOff f₅
  rw [m₄] at f₅' o₅
  -- The values.
  obtain ciph₁ : Spec.Siv.ctxCiph s₁.mem (State.addr c) R = Spec.Siv.ctxCiph s.mem (State.addr c) R :=
    ctxCiph_frame f₀₁ dc hRb
  obtain mac₂ : Spec.Siv.ctxMac s₂.mem (State.addr c) R = Spec.Siv.ctxMac s.mem (State.addr c) R := by
    rw [ctxMac_frame f₂ ec hRb, ctxMac_frame f₀₁ dc hRb]
  obtain iv₁ : bytesAt s₁.mem (State.addr w) 16 = bytesAt s.mem (State.addr T) 16 := by
    rw [iv₀₁, bytesAt_frame f₀₀ dT₀ (by decide)]
  obtain p₁ : bytesAt s₁.mem (State.addr D) n = bytesAt s.mem (State.addr D) n :=
    bytesAt_frame f₀₁ dD (by have := h.data.buf.lt; omega_arith)
  obtain p₅ : bytesAt s₅.mem (State.addr D) n = bytesAt s₂.mem (State.addr D) n :=
    bytesAt_frame f₅' (dis_wR h.data.buf.w h.data.buf.stk) (by have := h.data.buf.lt; omega_arith)
  obtain acc₂ : bytesAt s₂.mem (State.addr w + BitVec.ofNat 64 dOff) 16 =
      bytesAt s₀.mem (State.addr w + BitVec.ofNat 64 dOff) 16 := by
    rw [bytesAt_frame f₂ (eW (.inr (by decide)) (by decide)) (by decide),
      bytesAt_frame fi (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact w0 (by decide) (by decide)) (by decide)]
  obtain dWw : ∀ r ∈ wR w sp, (⟨State.addr w + BitVec.ofNat 64 0, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w' (by decide)).symm
  obtain dAw : ∀ r ∈ wR w sp, (⟨State.addr sp, 16⟩ : Region).Disjoint r :=
    fun r hr => dA₀ r (List.mem_cons_of_mem _ hr)
  refine ⟨he₅, by rw [rd₅, rd₄], by rw [wr₅, wr₄], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (((O.sv.frame O.frame (saved_wR L)).frame fi fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact w0 (by decide) (by decide)).frame f₂ eS).frame f₅'
      (saved_wR L)
  · rw [f₅'.readW (r := ⟨State.addr sp, 4⟩) (Region.contains_self _ _)
      (fun r hr => (dAw r hr).sub_left (Region.sub_prefix (by decide))) (by decide), ← hm0₂, BitVec.add_zero]
  · rw [f₅'.readW (r := ⟨State.addr sp + BitVec.ofNat 64 4, 4⟩) (Region.contains_self _ _)
      (fun r hr => (dAw r hr).sub_left (Offset.sub_base _ (by decide))) (by decide), hm1₂]
  · rw [bytesAt_frame f₅' dWw (by decide), bytesAt_frame f₂ (eW (.inl (by decide)) (by decide)) (by decide),
      BitVec.add_zero, iv₁]
  · rw [p₅, d₂, ciph₁, iv₁, p₁]
  · rw [o₅, mac₂, acc₂, O.acc, p₅]

/-- `vg_aes_siv_decrypt`: 1 and the plaintext in place if the received IV at
`T` is S2V's for it, and 0 and zeros if not. -/
theorem decrypt_wp {a D T : BitVec 32} {N n : Nat} {s : State} (h : EPre c w sp a D T R N n s) :
    WP isa decrypt s fun s' => abiPreserved s s' ∧
      match Spec.Siv.decryptWith (Spec.Siv.ctxMac s.mem (State.addr c) R) (Spec.Siv.ctxCiph s.mem (State.addr c) R)
          (Spec.Siv.components 32 s.mem (State.addr a) N) (bytesAt s.mem (State.addr T) 16)
          (bytesAt s.mem (State.addr D) n) with
      | some pt => s'.gpr .r0 = 1 ∧ bytesAt s'.mem (State.addr D) n = pt
      | none => s'.gpr .r0 = 0 ∧ bytesAt s'.mem (State.addr D) n = Spec.Siv.zeros n := by
  have ww := L.ww
  refine front_ok L h fun s₅ M => ?_
  obtain ⟨s₆, run₆, h0₆, g₆, k₆⟩ := compare_ok L M.env
  have hsp₅ : s₅.sp = sp := M.env.sp
  refine WP.seq (WP.block_append (WP.of_runBlock ⟨s₆, run₆, ?_⟩))
  refine wp_ldrSp (a := State.addr sp + BitVec.ofNat 64 0) (by decide)
    (by rw [k₆.sp, hsp₅]; exact addr_add (by have := h.afit; omega_arith))
    (by rw [k₆.rd, k₆.wr, M.rd, M.wr]; exact in_off h.args (by decide) (by decide)) fun s₇ u₇ => ?_
  refine wp_ldrSp (a := State.addr sp + BitVec.ofNat 64 4) (by decide)
    (by rw [u₇.sp, k₆.sp, hsp₅]; exact addr_add (by have := h.afit; omega_arith))
    (by rw [u₇.rd, u₇.wr, k₆.rd, k₆.wr, M.rd, M.wr]; exact in_off h.args (by decide) (by decide))
    fun s₈ u₈ => WP.block_nil ?_
  obtain m₈ : s₈.mem = s₅.mem := by rw [u₈.mem, u₇.mem, k₆.mem]
  obtain he₈ : Env c w sp R s₈ := M.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;>
        rw [u₈.other _ (by decide), u₇.other _ (by decide), g₆ _ (by decide) (by decide) (by decide)])
    (by rw [u₈.sp, u₇.sp, k₆.sp]) (by rw [u₈.rd, u₇.rd, k₆.rd]) (by rw [u₈.wr, u₇.wr, k₆.wr])
  obtain rd₈ : s₈.rd = s.rd := by rw [u₈.rd, u₇.rd, k₆.rd, M.rd]
  obtain wr₈ : s₈.wr = s.wr := by rw [u₈.wr, u₇.wr, k₆.wr, M.wr]
  obtain hD₈ : Dat c w sp s₈ D n := h.data.of_eq rd₈ wr₈
  obtain h6₈ : s₈.gpr .r6 = D := by
    rw [u₈.other _ (by decide), u₇.gpr, k₆.mem, BitVec.add_zero, M.a0]
  obtain h5₈ : s₈.gpr .r5 = BitVec.ofNat 32 n := by rw [u₈.gpr, u₇.mem, k₆.mem, M.a1]
  obtain h0₈ : s₈.gpr .r0 = if (decide (bytesAt s₅.mem (State.addr w + BitVec.ofNat 64 0) 16 =
      bytesAt s₅.mem (State.addr w + BitVec.ofNat 64 tOff) 16)) then 1 else 0 := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), h0₆]; simp only [decide_eq_true_eq]
  obtain ⟨ok, hok⟩ : ∃ ok, ok = decide (bytesAt s₅.mem (State.addr w + BitVec.ofNat 64 0) 16 =
      bytesAt s₅.mem (State.addr w + BitVec.ofNat 64 tOff) 16) := ⟨_, rfl⟩
  rw [← hok] at h0₈
  refine WP.seq (WP.mono (maskData_ok he₈ hD₈ h.n32 h6₈ h5₈ h0₈) fun s₉ ⟨he₉, rd₉, wr₉, g₉, m₉⟩ => ?_)
  obtain hlen := length_mask s₈.mem (State.addr D) ok n
  obtain sv₉ : SavedAt s₉.mem w s := by
    rw [m₉]
    refine (m₈ ▸ M.sv).frame (writeBytes_frame _ _ _ (R := ⟨State.addr D, n⟩)
      (by rw [hlen]; exact Region.contains_self _ _)) fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact (h.data.buf.w.sub_right (Lay.wSub (by decide))).symm
  refine WP.mono (restore_ok (s₀ := s) he₉.r11 (by omega_arith)
    (by rw [rd₉, wr₉, rd₈, wr₈]; exact covers_left (covers_prefix h.perm.w (by decide))) sv₉
    (by rw [he₉.sp, h.hsp])) fun s₁₀ ⟨ab, m₁₀, r0₁₀, _, _⟩ => ⟨ab, ?_⟩
  obtain hr0 : s₁₀.gpr .r0 = if ok then 1 else 0 := by
    rw [r0₁₀, g₉ _ (by decide) (by decide) (by decide) (by decide), h0₈]
  obtain hb : bytesAt s₁₀.mem (State.addr D) n =
      if ok then bytesAt s₅.mem (State.addr D) n else Spec.Ccm.zeros n := by
    obtain e := bytesAt_writeBytes_self s₈.mem (State.addr D)
      (if ok then bytesAt s₈.mem (State.addr D) n else Spec.Ccm.zeros n) (by rw [hlen]; have := h.n32; omega_arith)
    rw [hlen] at e
    rw [m₁₀, m₉, e, m₈]
  rw [M.iv, M.tag, M.pt] at hok
  rw [Spec.Siv.decryptWith_eq, Spec.Siv.openWith]
  by_cases e : Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem (State.addr c) R)
      (Spec.Siv.s2vAcc (Spec.Siv.ctxMac s.mem (State.addr c) R) (Spec.Siv.components 32 s.mem (State.addr a) N))
      (Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem (State.addr c) R) (Spec.Siv.counter (bytesAt s.mem (State.addr T) 16))
        (bytesAt s.mem (State.addr D) n)) = bytesAt s.mem (State.addr T) 16
  · have : ok = true := by rw [hok, e]; simp
    simp only [e, ite_true]
    rw [hr0, hb, this, M.pt]; exact ⟨rfl, rfl⟩
  · have : ok = false := by rw [hok]; simpa using Ne.symm e
    simp only [e, ite_false]
    rw [hr0, hb, this]; exact ⟨rfl, rfl⟩

end

end VG.Proof.AesSiv.Arm

end

end

/-!
# AES-SIV on ARMv7: `encrypt` and `decrypt` are constant time

Untrusted: everything here is checked by Lean. Two runs with the same
public arguments and the same descriptors of the components (`E0`) leak the
same. The blocks reading the stack arguments are checked by the taint
analysis with them public (`CT.argTaint`); between the pieces, the
correctness lemmas give each run the next piece's invariant (`CtrI` for the
pieces after S2V of the associated data, which keep the stack arguments);
`decrypt` compares the IVs and masks the data without a branch, so nothing
it does depends on the result.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm VG.Impl.AesSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCcm.Arm (blw)
open VG.Proof.AesGcm.Arm (CT savedR in_off bytesAt_frame Keeps)
open VG.Proof.MdStream.Arm (wp_ldrSp)

/-- The entry, with the regions the code may write apart from the stack
arguments, and the descriptors' words `dsc`. -/
structure E0 (c w sp a D T : BitVec 32) (R N n : Nat) (dsc : Nat → Nat → BitVec 32) (s : State) : Prop where
  pre : EPre c w sp a D T R N n s
  wa : ∀ r ∈ s.wr, (⟨State.addr sp, 16⟩ : Region).Disjoint r
  desc : DescEq s.mem a N dsc

/-- The descriptors' words, after writes apart from them. -/
theorem DescEq.frame {m m' : Mem} {a : BitVec 32} {N : Nat} {dsc : Nat → Nat → BitVec 32}
    (h : DescEq m a N dsc) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨State.addr a, 8 * N⟩ : Region).Disjoint r) : DescEq m' a N dsc := fun i hi j hj => by
  rw [← h i hi j hj]
  exact hf.readW (r := ⟨State.addr a + BitVec.ofNat 64 (8 * i + 4 * j), 4⟩) (Region.contains_self _ _)
    (fun r hr => (hd r hr).sub_left (Offset.sub_base _ (by omega_using [hi, hj]))) (by decide)

/-- After code that keeps the stack arguments: writes apart from them, the
same regions and an environment. -/
theorem CtrI.next {c w sp D : BitVec 32} {R n : Nat} {s s' : State} (h : CtrI c w sp R D n s)
    (he : Env c w sp R s') (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hd : ∀ r ∈ rs, (⟨State.addr sp, 16⟩ : Region).Disjoint r) :
    CtrI c w sp R D n s' where
  env := he
  dat := h.dat.of_eq hrd hwr
  wa := by rw [hwr]; exact h.wa
  afit := h.afit
  args := by rw [hrd, hwr]; exact h.args
  args_w := h.args_w
  args_d := h.args_d
  m0 := by
    rw [hf.readW (r := ⟨State.addr sp, 4⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (Region.sub_prefix (by decide))) (by decide), h.m0]
  m1 := by
    rw [hf.readW (r := ⟨State.addr sp + BitVec.ofNat 64 4, 4⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (Offset.sub_base _ (by decide))) (by decide), h.m1]
  n32 := h.n32

/-- `siv`, the third stack argument, at `T`: 16 bytes apart from `W` that the
code may read. -/
structure SivA (w sp T : BitVec 32) (s : State) : Prop where
  m2 : s.mem.readW (State.addr sp + BitVec.ofNat 64 8) 32 = T
  fit : T.toNat + 16 ≤ 2 ^ 32
  rd : Covers [⟨State.addr T, 16⟩] (s.rd ++ s.wr)
  t_w : (⟨State.addr T, 16⟩ : Region).Disjoint ⟨State.addr w, 2576⟩

theorem SivA.of_pre {c w sp a D T : BitVec 32} {R N n : Nat} {s : State} (h : EPre c w sp a D T R N n s) :
    SivA w sp T s :=
  ⟨h.a2, h.tfit, h.t_rd, h.t_w⟩

/-- `siv` where it was, after writes apart from the stack arguments. -/
theorem SivA.next {w sp T : BitVec 32} {s s' : State} (h : SivA w sp T s) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hd : ∀ r ∈ rs, (⟨State.addr sp, 16⟩ : Region).Disjoint r) : SivA w sp T s' where
  m2 := by
    rw [hf.readW (r := ⟨State.addr sp + BitVec.ofNat 64 8, 4⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (Offset.sub_base _ (by decide))) (by decide), h.m2]
  fit := h.fit
  rd := by rw [hrd, hwr]; exact h.rd
  t_w := h.t_w

/-- The third stack argument: `siv`'s address. -/
theorem SivA.arg {c w sp D T : BitVec 32} {R n : Nat} {s : State} (hc : CtrI c w sp R D n s)
    (h : SivA w sp T s) : stackArg s 2 = T := by
  rw [stackArg, stackArgAddr, hc.env.sp, addr_add (by have := hc.afit; omega_using [this]), h.m2]

section
variable {c w sp : BitVec 32} {R : Nat} (L : Lay c w sp) (hR : R = 10 ∨ R = 12 ∨ R = 14)
include L hR

omit L hR in
/-- A region of `W` but its first 16 bytes, or the stack below `sp`, is apart
from the stack arguments. -/
theorem args_dis (hw : (⟨State.addr sp, 16⟩ : Region).Disjoint ⟨State.addr w, 2576⟩) :
    ∀ r ∈ savedR w :: wR w sp, (⟨State.addr sp, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact Offset.base_disjoint_below (State.addr sp) (n := 16) (k := 16) (by decide)

omit L hR in
/-- What S2V's end writes, apart from the stack arguments. -/
theorem args_dis_oR (hw : (⟨State.addr sp, 16⟩ : Region).Disjoint ⟨State.addr w, 2576⟩) {out : Nat}
    (hout : out = 0 ∨ out = tOff) : ∀ r ∈ oR w sp out, (⟨State.addr sp, 16⟩ : Region).Disjoint r := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact hw.sub_right (Lay.wSub (by rcases hout with rfl | rfl <;> decide))
  · exact args_dis hw r (List.mem_cons_of_mem _ hr)

omit L hR in
/-- What CTR writes, apart from the stack arguments. -/
theorem args_dis_ctr {D : BitVec 32} {n : Nat}
    (hw : (⟨State.addr sp, 16⟩ : Region).Disjoint ⟨State.addr w, 2576⟩)
    (hd : (⟨State.addr sp, 16⟩ : Region).Disjoint ⟨State.addr D, n⟩) :
    ∀ r ∈ ctrR w sp D n, (⟨State.addr sp, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact Offset.base_disjoint_below (State.addr sp) (n := 16) (k := 16) (by decide)
  · exact hd

omit L hR in
/-- The pieces' invariant, from the entry, after writes that keep the stack
arguments. -/
theorem CtrI.of_entry {a D T : BitVec 32} {N n : Nat} {dsc : Nat → Nat → BitVec 32} {σ s : State}
    (h : E0 c w sp a D T R N n dsc σ) (he : Env c w sp R s) (hrd : s.rd = σ.rd) (hwr : s.wr = σ.wr)
    {rs : List Region} (hf : Frame rs σ.mem s.mem) (hd : ∀ r ∈ rs, (⟨State.addr sp, 16⟩ : Region).Disjoint r) :
    CtrI c w sp R D n s where
  env := he
  dat := h.pre.data.of_eq hrd hwr
  wa := by rw [hwr]; exact h.wa
  afit := h.pre.afit
  args := by rw [hrd, hwr]; exact h.pre.args
  args_w := h.pre.args_w
  args_d := h.pre.args_d
  m0 := by
    rw [hf.readW (r := ⟨State.addr sp, 4⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (Region.sub_prefix (by decide))) (by decide), h.pre.a0]
  m1 := by
    rw [hf.readW (r := ⟨State.addr sp + BitVec.ofNat 64 4, 4⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (Offset.sub_base _ (by decide))) (by decide), h.pre.a1]
  n32 := h.pre.n32

omit L hR in
/-- The data's address and length from the stack arguments. -/
theorem loadArgs_ct {D : BitVec 32} {n : Nat} :
    CT (CtrI c w sp R D n) (.block [.ldrSp .r6 0, .ldrSp .r5 4]) := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (argTaint [] (4 * 2))
      (.block [.ldrSp .r6 0, .ldrSp .r5 4]) h).isSome = true := ⟨_, by taint_decide⟩
  exact CT.argTaint _ _ (fun _ _ _ _ r hr => by simp at hr) (fun s₁ s₂ h₁ h₂ => by rw [h₁.env.sp, h₂.env.sp])
    (fun s h => ⟨by rw [h.env.sp]; have := h.afit; omega_using [this], fun r hr => by
      rw [h.env.sp]; exact (h.wa r hr).sub_left (Region.sub_prefix (by decide))⟩)
    (fun s₁ s₂ h₁ h₂ => argMem_of (by rw [h₁.env.sp, h₂.env.sp]) (by rw [h₁.env.sp]; have := h₁.afit; omega_using [this])
      fun i hi => by
        rcases (show i = 0 ∨ i = 1 by omega_using [hi]) with rfl | rfl
        · rw [h₁.arg.1, h₂.arg.1]
        · rw [h₁.arg.2, h₂.arg.2]) hA

omit L hR in
theorem loadArgs_wp {D : BitVec 32} {n : Nat} {s : State} (h : CtrI c w sp R D n s) :
    WP isa (.block [.ldrSp .r6 0, .ldrSp .r5 4]) s fun s' => (CtrI c w sp R D n s' ∧ s'.gpr .r6 = D ∧
      s'.gpr .r5 = BitVec.ofNat 32 n) ∧ s'.gpr .r0 = s.gpr .r0 := by
  have hsp := h.env.sp
  refine wp_ldrSp (a := State.addr sp + BitVec.ofNat 64 0) (by decide)
    (by rw [hsp]; exact addr_add (by have := h.afit; omega_using [])) (in_off h.args (by decide) (by decide))
    fun s₁ u₁ => ?_
  refine wp_ldrSp (a := State.addr sp + BitVec.ofNat 64 4) (by decide)
    (by rw [u₁.sp, hsp]; exact addr_add (by have := h.afit; omega_using [this]))
    (by rw [u₁.rd, u₁.wr]; exact in_off h.args (by decide) (by decide)) fun s₂ u₂ => WP.block_nil ?_
  have he : Env c w sp R s₂ := h.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> rw [u₂.other _ (by decide), u₁.other _ (by decide)])
    (by rw [u₂.sp, u₁.sp]) (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr])
  refine ⟨⟨h.next he (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr]) (rs := [])
      (by rw [u₂.mem, u₁.mem]; exact Frame.refl _ _) (fun _ hr => by simp at hr), ?_, ?_⟩,
    by rw [u₂.other _ (by decide), u₁.other _ (by decide)]⟩
  · rw [u₂.other _ (by decide), u₁.gpr, BitVec.add_zero, h.m0]
  · rw [u₂.gpr, u₁.mem, h.m1]

/-! ## S2V of the associated data -/

/-- Between S2V's pieces, in one run: from the entry `σ`, the memory `m₀`
after the save, before component `i`. -/
def SI (c w sp a D T : BitVec 32) (R N n : Nat) (dsc : Nat → Nat → BitVec 32) (i : Nat) (s : State) : Prop :=
  ∃ σ m₀, E0 c w sp a D T R N n dsc σ ∧ Frame [savedR w] σ.mem m₀ ∧ AInv c w sp a R N m₀ σ i s ∧
    DescEq m₀ a N dsc

theorem encS2v_ct {a D T : BitVec 32} {N n : Nat} {dsc : Nat → Nat → BitVec 32} (hN : N < 2 ^ 32) :
    CT (E0 c w sp a D T R N n dsc) encS2v := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (argTaint [.r0, .r1, .r2, .r3] (4 * 4))
      (.block (encPre ++ startPre)) h).isSome = true := ⟨_, by taint_decide⟩
  have ab : CT (E0 c w sp a D T R N n dsc) (.seq (.block (encPre ++ startPre)) finFrame) := by
    refine CT.seq (J := fun s => ∃ σ mₛ, Started c w sp a R N σ mₛ s)
      (CT.argTaint _ _ (fun s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [h₁.pre.r0, h₂.pre.r0]
        · rw [h₁.pre.r1, h₂.pre.r1]
        · rw [h₁.pre.r2, h₂.pre.r2]
        · rw [h₁.pre.r3, h₂.pre.r3]) (fun s₁ s₂ h₁ h₂ => by rw [h₁.pre.hsp, h₂.pre.hsp])
        (fun s h => ⟨by rw [h.pre.hsp]; exact h.pre.afit, fun r hr => by
          rw [h.pre.hsp]; exact h.wa r hr⟩)
        (fun s₁ s₂ h₁ h₂ => argMem_of (by rw [h₁.pre.hsp, h₂.pre.hsp]) (by rw [h₁.pre.hsp]; exact h₁.pre.afit)
          fun i hi => by
            have e : ∀ {s : State}, E0 c w sp a D T R N n dsc s → ∀ {k : Nat}, k < 4 →
                stackArg s k = s.mem.readW (State.addr sp + BitVec.ofNat 64 (4 * k)) 32 := fun h k hk => by
              rw [stackArg, stackArgAddr, h.pre.hsp, addr_add (by have := h.pre.afit; omega_using [hk, this])]
            rw [e h₁ hi, e h₂ hi]
            rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega_using [hi]) with rfl | rfl | rfl | rfl
            · rw [show 4 * 0 = 0 from rfl, BitVec.add_zero, h₁.pre.a0, h₂.pre.a0]
            · rw [h₁.pre.a1, h₂.pre.a1]
            · rw [h₁.pre.a2, h₂.pre.a2]
            · rw [h₁.pre.a3, h₂.pre.a3]) hA)
      (fun s h => WP.mono (startBlock_ok L h.pre) fun s' ⟨mₛ, St⟩ => ⟨s, mₛ, St⟩) ?_
    exact fin_rel fun s₁ s₂ hh => by
      obtain ⟨⟨_, _, h₁⟩, ⟨_, _, h₂⟩⟩ := hh
      exact ⟨h₁.args, h₂.args, h₁.env.sp, h₂.env.sp⟩
  refine RelCT.assoc (CT.seq ab (J := SI c w sp a D T R N n dsc 0) (fun s h => WP.mono (start_ok L h.pre)
    fun s' ⟨mₛ, fs, _, I⟩ => ⟨s, mₛ, h, fs, I, h.desc.frame fs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.pre.ads.dw.sub_right (Lay.wSub (by decide))⟩) ?_)
  refine CT.seq (J := SI c w sp a D T R N n dsc N)
    ((s2vAds_ct L hR hN).mono fun s ⟨σ, m₀, _, _, I, hd⟩ => ⟨m₀, σ, I, hd⟩)
    (fun s ⟨σ, m₀, h, fs, I, hd⟩ => WP.mono (s2vAds_ok L hR I hN) fun s' I' => ⟨σ, m₀, h, fs, I', hd⟩) ?_
  exact (loadArgs_ct (c := c) (w := w) (sp := sp) (R := R) (D := D) (n := n)).mono fun s ⟨σ, m₀, h, fs, I, _⟩ =>
    CtrI.of_entry h I.env I.rd I.wr ((fs.mono (by simp)).trans (I.frame.mono fun r hr =>
      List.mem_cons_of_mem _ hr)) (args_dis h.pre.args_w)

omit hR in
/-- After S2V of the associated data. -/
theorem encS2v_wp {a D T : BitVec 32} {N n : Nat} {dsc : Nat → Nat → BitVec 32} {s : State}
    (h : E0 c w sp a D T R N n dsc s) :
    WP isa encS2v s fun s' => (CtrI c w sp R D n s' ∧ s'.gpr .r6 = D ∧ s'.gpr .r5 = BitVec.ofNat 32 n) ∧
      SivA w sp T s' ∧ s'.wr = s.wr :=
  WP.mono (s2v_ok L h.pre) fun s' ⟨mₛ, O⟩ => by
    have F : Frame (savedR w :: wR w sp) s.mem s'.mem :=
      (O.fs.mono (by simp)).trans (O.frame.mono fun r hr => List.mem_cons_of_mem _ hr)
    exact ⟨⟨CtrI.of_entry h O.env O.rd O.wr F (args_dis h.pre.args_w), O.r6, O.r5⟩,
      (SivA.of_pre h.pre).next O.rd O.wr F (args_dis h.pre.args_w), O.wr⟩

/-! ## `siv` -/

omit hR in
/-- The IV copied to `siv`, which the code may write: what follows needs only
the environment. -/
theorem sivOut_wp {D T : BitVec 32} {n : Nat} {s : State}
    (h : CtrI c w sp R D n s ∧ SivA w sp T s ∧ Covers [⟨State.addr T, 16⟩] s.wr) :
    WP isa (.block sivOut) s (Env c w sp R) := by
  obtain ⟨hc, ht, hw⟩ := h
  have a8 : State.addr (s.sp + BitVec.ofNat 32 8) = State.addr sp + BitVec.ofNat 64 8 := by
    rw [hc.env.sp]; exact addr_add (by have := hc.afit; omega_using [this])
  obtain ⟨s', run, -, -, g, rd, wr, sp'⟩ := sivOut_ok L hc.env (T := T)
    (by rw [a8]; exact in_off hc.args (by decide) (by decide)) (by rw [a8]; exact ht.m2) hw ht.fit
    (ht.t_w.sub_right (Region.sub_prefix (by decide)))
  exact WP.of_runBlock ⟨s', run, hc.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g _ (by decide) (by decide)) sp' rd wr⟩

omit L hR in
theorem sivOut_ct {D T : BitVec 32} {n : Nat} :
    CT (fun s => CtrI c w sp R D n s ∧ SivA w sp T s ∧ Covers [⟨State.addr T, 16⟩] s.wr) (.block sivOut) := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (argTaint [.r11] (4 * 3)) (.block sivOut) h).isSome = true :=
    ⟨_, by taint_decide⟩
  exact CT.argTaint _ _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.env.r11, h₂.1.env.r11])
    (fun s₁ s₂ h₁ h₂ => by rw [h₁.1.env.sp, h₂.1.env.sp])
    (fun s h => ⟨by rw [h.1.env.sp]; have := h.1.afit; omega_using [this], fun r hr => by
      rw [h.1.env.sp]; exact (h.1.wa r hr).sub_left (Region.sub_prefix (by decide))⟩)
    (fun s₁ s₂ h₁ h₂ => argMem_of (by rw [h₁.1.env.sp, h₂.1.env.sp]) (by rw [h₁.1.env.sp]; have := h₁.1.afit; omega_using [this])
      fun i hi => by
        rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega_using [hi]) with rfl | rfl | rfl
        · rw [h₁.1.arg.1, h₂.1.arg.1]
        · rw [h₁.1.arg.2, h₂.1.arg.2]
        · rw [SivA.arg h₁.1 h₁.2.1, SivA.arg h₂.1 h₂.2.1]) hA

omit hR in
/-- The received IV copied from `siv` to `W`. -/
theorem sivIn_wp {D T : BitVec 32} {n : Nat} {s : State} (h : CtrI c w sp R D n s ∧ SivA w sp T s) :
    WP isa (.block sivIn) s (CtrI c w sp R D n) := by
  obtain ⟨hc, ht⟩ := h
  have a8 : State.addr (s.sp + BitVec.ofNat 32 8) = State.addr sp + BitVec.ofNat 64 8 := by
    rw [hc.env.sp]; exact addr_add (by have := hc.afit; omega_using [this])
  obtain ⟨s', run, -, f, g, rd, wr, sp'⟩ := sivIn_ok L hc.env (T := T)
    (by rw [a8]; exact in_off hc.args (by decide) (by decide)) (by rw [a8]; exact ht.m2) ht.rd ht.fit
    (ht.t_w.sub_right (Region.sub_prefix (by decide)))
  refine WP.of_runBlock ⟨s', run, hc.next (hc.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g _ (by decide) (by decide)) sp' rd wr) rd wr f fun r hr => ?_⟩
  simp only [List.mem_singleton] at hr; subst hr
  exact hc.args_w.sub_right (Region.sub_prefix (by decide))

omit L hR in
theorem sivIn_ct {D T : BitVec 32} {n : Nat} :
    CT (fun s => CtrI c w sp R D n s ∧ SivA w sp T s) (.block sivIn) := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (argTaint [.r11] (4 * 3)) (.block sivIn) h).isSome = true :=
    ⟨_, by taint_decide⟩
  exact CT.argTaint _ _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.env.r11, h₂.1.env.r11])
    (fun s₁ s₂ h₁ h₂ => by rw [h₁.1.env.sp, h₂.1.env.sp])
    (fun s h => ⟨by rw [h.1.env.sp]; have := h.1.afit; omega_using [this], fun r hr => by
      rw [h.1.env.sp]; exact (h.1.wa r hr).sub_left (Region.sub_prefix (by decide))⟩)
    (fun s₁ s₂ h₁ h₂ => argMem_of (by rw [h₁.1.env.sp, h₂.1.env.sp]) (by rw [h₁.1.env.sp]; have := h₁.1.afit; omega_using [this])
      fun i hi => by
        rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega_using [hi]) with rfl | rfl | rfl
        · rw [h₁.1.arg.1, h₂.1.arg.1]
        · rw [h₁.1.arg.2, h₂.1.arg.2]
        · rw [SivA.arg h₁.1 h₁.2, SivA.arg h₂.1 h₂.2]) hA

/-! ## The ends -/

omit L hR in
theorem restore_ct : CT (Env c w sp R) (.block Impl.AesGcm.Arm.restore) := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r11])
      (.block Impl.AesGcm.Arm.restore) h).isSome = true := ⟨_, by taint_decide⟩
  exact CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r11, h₂.r11]) hA

/-- S2V's end with the data into `W + out`, from the pieces' invariant with
the data in `r6` and `r5`. -/
theorem finish_next {D : BitVec 32} {n : Nat} {out : Nat} (hout : out = 0 ∨ out = tOff) {s : State}
    (h : CtrI c w sp R D n s ∧ s.gpr .r6 = D ∧ s.gpr .r5 = BitVec.ofNat 32 n)
    (hA : ∀ r ∈ oR w sp out, (⟨State.addr sp, 16⟩ : Region).Disjoint r) :
    WP isa (finish out) s (CtrI c w sp R D n) := by
  exact WP.mono (finish_ok L h.1.env hR h.1.dat.buf h.1.n32 h.2.1 h.2.2 hout) fun s' ⟨he, rd, wr, _, f, _⟩ =>
    h.1.next he rd wr f hA

omit L hR in
/-- The IVs compared, and the data's address and length loaded again. -/
theorem cmpLoad_ct {D : BitVec 32} {n : Nat} :
    CT (CtrI c w sp R D n) (.block (compare ++ ([.ldrSp .r6 0, .ldrSp .r5 4] : List Instr))) := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (argTaint [.r9, .r10, .r11] (4 * 2))
      (.block (compare ++ [.ldrSp .r6 0, .ldrSp .r5 4])) h).isSome = true := ⟨_, by taint_decide⟩
  exact CT.argTaint _ _ (fun s₁ s₂ h₁ h₂ => env_regs h₁.env h₂.env) (fun s₁ s₂ h₁ h₂ => by rw [h₁.env.sp, h₂.env.sp])
    (fun s h => ⟨by rw [h.env.sp]; have := h.afit; omega_using [this], fun r hr => by
      rw [h.env.sp]; exact (h.wa r hr).sub_left (Region.sub_prefix (by decide))⟩)
    (fun s₁ s₂ h₁ h₂ => argMem_of (by rw [h₁.env.sp, h₂.env.sp]) (by rw [h₁.env.sp]; have := h₁.afit; omega_using [this])
      fun i hi => by
        rcases (show i = 0 ∨ i = 1 by omega_using [hi]) with rfl | rfl
        · rw [h₁.arg.1, h₂.arg.1]
        · rw [h₁.arg.2, h₂.arg.2]) hA

omit hR in
theorem cmpLoad_wp {D : BitVec 32} {n : Nat} {s : State} (h : CtrI c w sp R D n s) :
    WP isa (.block (compare ++ ([.ldrSp .r6 0, .ldrSp .r5 4] : List Instr))) s fun s' =>
      (CtrI c w sp R D n s' ∧ s'.gpr .r6 = D ∧ s'.gpr .r5 = BitVec.ofNat 32 n) ∧
        ∃ ok : Bool, s'.gpr .r0 = if ok then 1 else 0 := by
  obtain ⟨s₁, run, h0, g, k⟩ := compare_ok L h.env
  refine WP.block_append_iff.mpr (WP.of_runBlock ⟨s₁, run, ?_⟩)
  have he : Env c w sp R s₁ := h.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g _ (by decide) (by decide) (by decide)) k.sp k.rd k.wr
  have h₁ : CtrI c w sp R D n s₁ := h.next he k.rd k.wr (rs := []) (by rw [k.mem]; exact Frame.refl _ _)
    (fun _ hr => by simp at hr)
  refine WP.mono (loadArgs_wp h₁) fun s' ⟨p, e0⟩ => ⟨p, decide (bytesAt s.mem (State.addr w + BitVec.ofNat 64 0) 16 =
    bytesAt s.mem (State.addr w + BitVec.ofNat 64 tOff) 16), ?_⟩
  rw [e0, h0]; simp only [decide_eq_true_eq]

omit L hR in
/-- The data masked with `0 − r0`. -/
theorem maskData_ct {D : BitVec 32} {n : Nat} :
    CT (fun s => CtrI c w sp R D n s ∧ s.gpr .r6 = D ∧ s.gpr .r5 = BitVec.ofNat 32 n) maskData := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r5, .r6]) maskData h).isSome = true :=
    ⟨_, by taint_decide⟩
  exact CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.2.2, h₂.2.2]
    · rw [h₁.2.1, h₂.2.1]) hA

/-- `vg_aes_siv_encrypt`, in two runs with the same public arguments and
descriptors, with `siv` writable. -/
theorem encrypt_ct {a D T : BitVec 32} {N n : Nat} {dsc : Nat → Nat → BitVec 32} (hN : N < 2 ^ 32)
    (hn : n < 2 ^ 32) :
    CT (fun s => E0 c w sp a D T R N n dsc s ∧ Covers [⟨State.addr T, 16⟩] s.wr) encrypt := by
  refine CT.seq ((encS2v_ct L hR hN).mono fun s h => h.1) (J := fun s =>
      (CtrI c w sp R D n s ∧ s.gpr .r6 = D ∧ s.gpr .r5 = BitVec.ofNat 32 n) ∧ SivA w sp T s ∧
        Covers [⟨State.addr T, 16⟩] s.wr)
    (fun s h => WP.mono (encS2v_wp L h.1) fun s' ⟨p, q, e⟩ => ⟨p, q, by rw [e]; exact h.2⟩) ?_
  refine CT.seq (J := fun s => CtrI c w sp R D n s ∧ SivA w sp T s ∧ Covers [⟨State.addr T, 16⟩] s.wr)
    ((finish_ct L hR hn (.inl rfl)).mono fun s h => ⟨h.1.1.env, h.1.1.dat.buf, h.1.2.1, h.1.2.2⟩)
    (fun s h => WP.mono (finish_ok L h.1.1.env hR h.1.1.dat.buf h.1.1.n32 h.1.2.1 h.1.2.2 (.inl rfl))
      fun s' ⟨he, rd, wr, _, f, _⟩ => ⟨h.1.1.next he rd wr f (args_dis_oR h.1.1.args_w (.inl rfl)),
        h.2.1.next rd wr f (args_dis_oR h.1.1.args_w (.inl rfl)), by rw [wr]; exact h.2.2⟩) ?_
  refine CT.seq (J := fun s => CtrI c w sp R D n s ∧ SivA w sp T s ∧ Covers [⟨State.addr T, 16⟩] s.wr)
    ((ctr_ct L hR hn).mono fun s h => h.1)
    (fun s h => WP.mono (ctr_ok L h.1.env hR h.1.dat hn h.1.afit h.1.args h.1.args_w h.1.m0 h.1.m1)
      fun s' ⟨he, rd, wr, _, _, _, f, _⟩ => ⟨h.1.next he rd wr f (args_dis_ctr h.1.args_w h.1.args_d),
        h.2.1.next rd wr f (args_dis_ctr h.1.args_w h.1.args_d), by rw [wr]; exact h.2.2⟩) ?_
  exact CT.seq (J := Env c w sp R) sivOut_ct (fun s h => sivOut_wp L h) restore_ct

/-- `vg_aes_siv_decrypt`, in two runs with the same public arguments and descriptors. -/
theorem decrypt_ct {a D T : BitVec 32} {N n : Nat} {dsc : Nat → Nat → BitVec 32} (hN : N < 2 ^ 32)
    (hn : n < 2 ^ 32) : CT (E0 c w sp a D T R N n dsc) decrypt := by
  refine CT.seq (encS2v_ct L hR hN) (J := fun s => CtrI c w sp R D n s ∧ SivA w sp T s)
    (fun s h => WP.mono (encS2v_wp L h) fun s' ⟨p, q, _⟩ => ⟨p.1, q⟩) ?_
  refine CT.seq sivIn_ct (fun s h => sivIn_wp L h) ?_
  refine CT.seq (J := CtrI c w sp R D n) (ctr_ct L hR hn)
    (fun s h => WP.mono (ctr_ok L h.env hR h.dat hn h.afit h.args h.args_w h.m0 h.m1)
      fun s' ⟨he, rd, wr, _, _, _, f, _⟩ => h.next he rd wr f (args_dis_ctr h.args_w h.args_d)) ?_
  refine CT.seq loadArgs_ct (fun s h => WP.mono (loadArgs_wp h) fun s' p => p.1) ?_
  refine CT.seq (J := CtrI c w sp R D n) ((finish_ct L hR hn (.inr rfl)).mono
      fun s h => ⟨h.1.env, h.1.dat.buf, h.2.1, h.2.2⟩)
    (fun s h => finish_next L hR (.inr rfl) h (args_dis_oR h.1.args_w (.inr rfl))) ?_
  refine CT.seq cmpLoad_ct (fun s h => cmpLoad_wp L h) ?_
  exact CT.seq (J := Env c w sp R) (maskData_ct.mono fun s h => h.1)
    (fun s ⟨⟨h, h6, h5⟩, ok, h0⟩ => WP.mono (maskData_ok h.env h.dat hn h6 h5 h0) fun s' p => p.1) restore_ct

end

end VG.Proof.AesSiv.Arm

end

end

/-!
# AES-SIV on ARMv7: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant
time, a state satisfying each precondition, and the shared contracts of
`Spec/Siv/Contract.lean`. `init` calls `vg_cmac_aes_subkeys`, which uses 8
bytes of stack, and keeps its 2560-byte working space in a frame of its own
(`init_framed`); `encrypt` and `decrypt` are proved against the shared
contracts with the working space as a last argument
(`Proof/AesSiv/Scratch.lean`), using 16 bytes of stack: each call pushes two
words, and `vg_cmac_aes_update` and `vg_cmac_aes_finalize` push two more for
their own calls. On ARMv7 the arguments on the stack are read-only, apart
from every region the code may write (`E0`): the data, `work` and, for
`encrypt`, `siv`.
-/

@[expose] public section

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm VG.Impl.AesSiv.Arm

/-- A state with the given registers, the stack pointer at `0x8000`, memory
of zeros (so stack arguments of 0) and the given regions. -/
def sivSat (g : Reg → BitVec 32) (rd wr : List Region) : State where
  gpr := g
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := rd
  wr := wr

/-! ## `vg_aes_siv_init` -/

/-- A state satisfying `vg_aes_siv_init`'s precondition. -/
def initSat : State :=
  sivSat (fun r => match r with | .r0 => 0x1000 | .r1 => 32 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0)
    [⟨0x1000, 32⟩] [⟨0x2000, 512⟩, ⟨0x3000, 2560⟩]

theorem init_verified : Verified Arm.target init (Proof.AesSiv.initScratchContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => init_wp hs) init_ct (by
    sig_implies [Proof.AesSiv.initScratchContract, Proof.AesSiv.initScratchSig, Spec.Siv.initPre,
      Spec.Siv.initPost, initArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [initSat, sivSat] using initSat)

/-- A state satisfying `vg_aes_siv_init`'s precondition, without the
working space. -/
def initFrameSat : State :=
  sivSat (fun r => match r with | .r0 => 0x1000 | .r1 => 32 | .r2 => 0x2000 | _ => 0)
    [⟨0x1000, 32⟩] [⟨0x2000, 512⟩]

theorem initFrameSat_pre : ∃ s, (Spec.Siv.initContract Arm.abi 2568).pre s := by
  implies_sat [Spec.Siv.initContract, Spec.Siv.initSig, Spec.Siv.initPre, Spec.Siv.initPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [initFrameSat, sivSat] using initFrameSat

/-- `init` with its working space in a frame of 2560 bytes. -/
theorem init_framed : Verified Arm.target (Impl.StackScratch.Arm.withRegScratch 2560 .r3 init)
    (Spec.Siv.initContract Arm.abi 2568) :=
  Arm.Verified.regScratch (sig := Spec.Siv.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Siv.initPre Arm.abi.ptrBits) (post := Spec.Siv.initPost Arm.abi.ptrBits)
    (wa := true) (stack := 8) init_verified (by decide) (by decide) (by decide)
    (fun vs mm m₁ m₂ r hl _ => Proof.AesSiv.initPostOut_local _ vs mm m₁ m₂ r hl) initFrameSat_pre

/-! ## `vg_aes_siv_encrypt` and `vg_aes_siv_decrypt` -/

theorem filter_true' (l : List Region) : l.filter (fun _ => true) = l := List.filter_eq_self.mpr (by simp)

theorem filter_false' (l : List Region) : l.filter (fun _ => false) = [] := List.filter_eq_nil_iff.mpr (by simp)

theorem filterMap_some' {β : Type} (f : Region → β) (l : List Region) :
    l.filterMap (fun x => some (f x)) = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem filterMap_none' {β : Type} (l : List Region) : l.filterMap (fun _ => (none : Option β)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem cov_mem {r : Region} {ts : List Region} (h : r ∈ ts) : Covers [r] ts := by
  intro a n ⟨x, hx, hc⟩
  simp only [List.mem_singleton] at hx; subst hx; exact ⟨x, h, hc⟩

/-- Component `i`'s region, as the descriptors list it. -/
theorem listed_mem (m : Mem) (a : BitVec 32) {N i : Nat} (hi : i < N) :
    (⟨State.addr (descW m a i 0), (descW m a i 1).toNat⟩ : Region) ∈ Sig.listed 32 m .u8 (State.addr a) N := by
  refine List.mem_map.mpr ⟨i, List.mem_range.mpr hi, ?_⟩
  simp only [descW, State.addr, Elem.size, Nat.mul_one]
  rw [show i * (2 * (32 / 8)) = 8 * i + 4 * 0 by omega_arith, show (32 / 8 : Nat) = 4 from rfl, BitVec.add_assoc,
    BitVec.ofNat_add_ofNat, show 8 * i + 4 * 0 + 4 = 8 * i + 4 * 1 by omega_arith]

theorem stackArgAddr0 (s : State) : stackArgAddr s 0 = State.addr s.sp := by
  simp [stackArgAddr]

/-- The entry invariant of the proofs, for the shared contracts' arguments:
`siv` is the third stack argument and `work` the fourth. -/
abbrev E0S (s : State) : Prop :=
  E0 (s.gpr .r0) (stackArg s 3) s.sp (s.gpr .r2) (stackArg s 0) (stackArg s 2) (s.gpr .r1).toNat
    (s.gpr .r3).toNat (stackArg s 1).toNat (fun i j => descW s.mem (s.gpr .r2) i j) s

set_option linter.unusedSimpArgs false in
/-- The precondition of `encrypt`'s shared contract gives the proofs' entry
invariant, with the descriptors' words in the entry memory, and `siv`
writable and apart from the data. -/
theorem encPre_of {s : State} (h : (Proof.AesSiv.encryptScratchContract Arm.abi 16).pre s) :
    E0S s ∧ Covers [⟨State.addr (stackArg s 2), 16⟩] s.wr ∧
      (⟨State.addr (stackArg s 2), 16⟩ : Region).Disjoint ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩ := by
  sig_pre [Proof.AesSiv.encryptScratchContract, Proof.AesSiv.encryptScratchSig, Spec.Siv.encryptPre, Arm.abi,
    Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, List.append_eq] at h
  sig_split h
  simp only [List.filter_map, List.map_map, List.filterMap_map, List.map_nil, Function.comp_def,
    Bool.not_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false,
    List.nil_append, Sig.conj, List.filter_append, List.filter_cons, List.map_append,
    List.filterMap_append, List.filterMap_cons, ite_true, Bool.false_eq_true, ite_false, List.filter_nil,
    List.filterMap_nil, List.map_cons] at *
  rename_i sp16 afit cd cT bc bd bT bw fc fd fT fw hrd hwr pw bl fl
  obtain ⟨cW, dT, dW, dA, ⟨dL, dArg⟩, tW, -, ⟨-, tArg⟩, wA, ⟨wL, wArg⟩, -⟩ := pw
  obtain ⟨bA, bL, -⟩ := bl
  obtain ⟨fA, fL⟩ := fl
  rw [stackArgAddr0] at hrd wArg dArg tArg
  have hA : (s.gpr .r2).toNat + 8 * (s.gpr .r3).toNat ≤ 2 ^ 32 := by omega_arith
  have inRd {r : Region} (hr : r ∈ s.rd) : r ∈ s.rd ++ s.wr := List.mem_append_left _ hr
  have inWr {r : Region} (hr : r ∈ s.wr) : r ∈ s.rd ++ s.wr := List.mem_append_right _ hr
  have e4 : State.addr (s.sp + BitVec.ofNat 32 4) = State.addr s.sp + BitVec.ofNat 64 4 := addr_add (by omega_arith)
  have e8 : State.addr (s.sp + BitVec.ofNat 32 8) = State.addr s.sp + BitVec.ofNat 64 8 := addr_add (by omega_arith)
  have e12 : State.addr (s.sp + BitVec.ofNat 32 12) = State.addr s.sp + BitVec.ofNat 64 12 := addr_add (by omega_arith)
  have mC : (⟨State.addr (s.gpr .r0), 512⟩ : Region) ∈ s.rd := by rw [hrd]; exact List.mem_cons_self
  have mA : (⟨State.addr (s.gpr .r2), 8 * (s.gpr .r3).toNat⟩ : Region) ∈ s.rd := by
    rw [hrd, Nat.mul_comm]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have mS : (⟨State.addr s.sp, 16⟩ : Region) ∈ s.rd := by
    rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self))
  have mD : (⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩ : Region) ∈ s.wr := by
    rw [hwr]; exact List.mem_cons_self
  have mT : (⟨State.addr (stackArg s 2), 16⟩ : Region) ∈ s.wr := by
    rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have mW : (⟨State.addr (stackArg s 3), 2576⟩ : Region) ∈ s.wr := by
    rw [hwr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have wa : ∀ r ∈ s.wr, (⟨State.addr s.sp, 16⟩ : Region).Disjoint r := by
    intro r hr
    rw [hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact dArg.symm
    · exact tArg.symm
    · exact wArg.symm
  refine ⟨⟨⟨⟨fc, fw, sp16, cW, bc, bw⟩, ⟨cov_mem (inRd mC), cov_mem mW⟩,
    rfl, by simp, rfl, by simp, rfl, h, afit, cov_mem (inRd mS), wArg.symm, dArg.symm, ?_, ?_, ?_, ?_,
    ⟨cov_mem (inRd mA), hA, by rw [Nat.mul_comm]; exact wA.symm, by rw [Nat.mul_comm]; exact bA, fun i hi => ?_⟩,
    ⟨⟨cov_mem (inWr mD), fd, dW, bd⟩, cov_mem mD, cd⟩, BitVec.isLt _, fT, cov_mem (inWr mT), tW, bT⟩, wa,
    fun _ _ _ _ => rfl⟩, cov_mem mT, dT.symm⟩
  · rw [stackArg, stackArgAddr0]
  · rw [stackArg, stackArgAddr, show 4 * 1 = 4 from rfl, e4, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [stackArg, stackArgAddr, show 4 * 2 = 8 from rfl, e8]
  · rw [stackArg, stackArgAddr, show 4 * 3 = 12 from rfl, e12]
  · have hm := listed_mem s.mem (s.gpr .r2) hi
    have f := fL _ hm
    have mP : (⟨State.addr (descW s.mem (s.gpr .r2) i 0), (descW s.mem (s.gpr .r2) i 1).toNat⟩ : Region) ∈
        s.rd := by
      rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ hm))
    exact ⟨cov_mem (inRd mP), f, (wL _ hm).symm, bL _ hm⟩

set_option linter.unusedSimpArgs false in
/-- The precondition of `decrypt`'s shared contract gives the proofs' entry
invariant, with the descriptors' words in the entry memory. -/
theorem decPre_of {s : State} (h : (Proof.AesSiv.decryptScratchContract Arm.abi 16).pre s) : E0S s := by
  sig_pre [Proof.AesSiv.decryptScratchContract, Proof.AesSiv.decryptScratchSig, Spec.Siv.decryptPre, Arm.abi,
    Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, List.append_eq] at h
  sig_split h
  simp only [List.filter_map, List.map_map, List.filterMap_map, List.map_nil, Function.comp_def,
    Bool.not_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false,
    List.nil_append, Sig.conj, List.filter_append, List.filter_cons, List.map_append,
    List.filterMap_append, List.filterMap_cons, ite_true, Bool.false_eq_true, ite_false, List.filter_nil,
    List.filterMap_nil, List.map_cons] at *
  rename_i sp16 afit cd bc bd bT bw fc fd fT fw hrd hwr pw bl fl
  obtain ⟨cW, -, dW, dA, ⟨dL, dArg⟩, tW, wA, ⟨wL, wArg⟩, -⟩ := pw
  obtain ⟨bA, bL, -⟩ := bl
  obtain ⟨fA, fL⟩ := fl
  rw [stackArgAddr0] at hrd wArg dArg
  have hA : (s.gpr .r2).toNat + 8 * (s.gpr .r3).toNat ≤ 2 ^ 32 := by omega_arith
  have inRd {r : Region} (hr : r ∈ s.rd) : r ∈ s.rd ++ s.wr := List.mem_append_left _ hr
  have inWr {r : Region} (hr : r ∈ s.wr) : r ∈ s.rd ++ s.wr := List.mem_append_right _ hr
  have e4 : State.addr (s.sp + BitVec.ofNat 32 4) = State.addr s.sp + BitVec.ofNat 64 4 := addr_add (by omega_arith)
  have e8 : State.addr (s.sp + BitVec.ofNat 32 8) = State.addr s.sp + BitVec.ofNat 64 8 := addr_add (by omega_arith)
  have e12 : State.addr (s.sp + BitVec.ofNat 32 12) = State.addr s.sp + BitVec.ofNat 64 12 := addr_add (by omega_arith)
  have mC : (⟨State.addr (s.gpr .r0), 512⟩ : Region) ∈ s.rd := by rw [hrd]; exact List.mem_cons_self
  have mT : (⟨State.addr (stackArg s 2), 16⟩ : Region) ∈ s.rd := by
    rw [hrd]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have mA : (⟨State.addr (s.gpr .r2), 8 * (s.gpr .r3).toNat⟩ : Region) ∈ s.rd := by
    rw [hrd, Nat.mul_comm]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have mS : (⟨State.addr s.sp, 16⟩ : Region) ∈ s.rd := by
    rw [hrd]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_append_right _ List.mem_cons_self)))
  have mD : (⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩ : Region) ∈ s.wr := by
    rw [hwr]; exact List.mem_cons_self
  have mW : (⟨State.addr (stackArg s 3), 2576⟩ : Region) ∈ s.wr := by
    rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have wa : ∀ r ∈ s.wr, (⟨State.addr s.sp, 16⟩ : Region).Disjoint r := by
    intro r hr
    rw [hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dArg.symm
    · exact wArg.symm
  refine ⟨⟨⟨fc, fw, sp16, cW, bc, bw⟩, ⟨cov_mem (inRd mC), cov_mem mW⟩,
    rfl, by simp, rfl, by simp, rfl, h, afit, cov_mem (inRd mS), wArg.symm, dArg.symm, ?_, ?_, ?_, ?_,
    ⟨cov_mem (inRd mA), hA, by rw [Nat.mul_comm]; exact wA.symm, by rw [Nat.mul_comm]; exact bA, fun i hi => ?_⟩,
    ⟨⟨cov_mem (inWr mD), fd, dW, bd⟩, cov_mem mD, cd⟩, BitVec.isLt _, fT, cov_mem (inRd mT), tW, bT⟩, wa,
    fun _ _ _ _ => rfl⟩
  · rw [stackArg, stackArgAddr0]
  · rw [stackArg, stackArgAddr, show 4 * 1 = 4 from rfl, e4, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [stackArg, stackArgAddr, show 4 * 2 = 8 from rfl, e8]
  · rw [stackArg, stackArgAddr, show 4 * 3 = 12 from rfl, e12]
  · have hm := listed_mem s.mem (s.gpr .r2) hi
    have f := fL _ hm
    have mP : (⟨State.addr (descW s.mem (s.gpr .r2) i 0), (descW s.mem (s.gpr .r2) i 1).toNat⟩ : Region) ∈
        s.rd := by
      rw [hrd]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ hm)))
    exact ⟨cov_mem (inRd mP), f, (wL _ hm).symm, bL _ hm⟩

/-- Descriptors whose bytes are the same in two memories have the same words. -/
theorem descW_eq {m m' : Mem} {a : BitVec 32} {N : Nat}
    (h : ∀ k < N * 8, m (State.addr a + BitVec.ofNat 64 k) = m' (State.addr a + BitVec.ofNat 64 k))
    {i j : Nat} (hi : i < N) (hj : j < 2) : descW m' a i j = descW m a i j := by
  have e := Mem.read_congr (m := m) (m' := m') (a := State.addr a + BitVec.ofNat 64 (8 * i + 4 * j))
    (n := 32 / 8) fun k hk => by rw [Offset.add_add]; exact h _ (by omega_arith)
  simp only [descW, Mem.readW, e]

/-- What two runs of `encrypt` or `decrypt` agree on: the stack pointer, the
arguments and the descriptors. -/
def EncPub (s₁ s₂ : State) : Prop :=
  (s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧
    stackArg s₁ 2 = stackArg s₂ 2 ∧ stackArg s₁ 3 = stackArg s₂ 3) ∧
  ∀ i < (s₁.gpr .r3).toNat * 8, s₁.mem (State.addr (s₁.gpr .r2) + BitVec.ofNat 64 i) =
    s₂.mem (State.addr (s₁.gpr .r2) + BitVec.ofNat 64 i)

/-- The second run's entry invariant, with the first run's public values. -/
theorem encPre_pub {X : BitVec 32 → State → Prop} {s₁ s₂ : State} (E : E0S s₂) (hX : X (stackArg s₂ 2) s₂)
    (hq : EncPub s₁ s₂) :
    E0 (s₁.gpr .r0) (stackArg s₁ 3) s₁.sp (s₁.gpr .r2) (stackArg s₁ 0) (stackArg s₁ 2) (s₁.gpr .r1).toNat
      (s₁.gpr .r3).toNat (stackArg s₁ 1).toNat (fun i j => descW s₁.mem (s₁.gpr .r2) i j) s₂ ∧
      X (stackArg s₁ 2) s₂ := by
  obtain ⟨⟨q0, q1, q2, q3, q4, q5, q6, q7, q8⟩, hd⟩ := hq
  have hd' : DescEq s₂.mem (s₁.gpr .r2) (s₁.gpr .r3).toNat (fun i j => descW s₁.mem (s₁.gpr .r2) i j) :=
    fun i hi j hj => descW_eq hd hi hj
  rw [q3, q4] at hd'
  rw [q0, q1, q2, q3, q4, q5, q6, q7, q8]
  exact ⟨⟨E.pre, E.wa, hd'⟩, hX⟩

/-- `vg_aes_siv_encrypt` and `vg_aes_siv_decrypt` are constant time, given
their constant time on the entry invariant and `X` of `siv`. -/
theorem enc_ct {c : Prog isa} {k : Contract isa} {X : BitVec 32 → State → Prop}
    (hk : ∀ s, k.pre s → E0S s ∧ X (stackArg s 2) s) (hpub : ∀ s₁ s₂, k.pub s₁ s₂ → EncPub s₁ s₂)
    (hc : ∀ {c' w sp a D T : BitVec 32} {R N n : Nat} {dsc : Nat → Nat → BitVec 32}, Lay c' w sp →
      (R = 10 ∨ R = 12 ∨ R = 14) → N < 2 ^ 32 → n < 2 ^ 32 →
      Proof.AesGcm.Arm.CT (fun s => E0 c' w sp a D T R N n dsc s ∧ X T s) c) :
    ConstantTime isa k.pre k.pub c := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂
  obtain ⟨E₁, X₁⟩ := hk _ h₁
  obtain ⟨E₂, X₂⟩ := hk _ h₂
  exact (hc E₁.pre.lay E₁.pre.rounds (BitVec.isLt _) (BitVec.isLt _) _ _ _ _ _ _
    ⟨⟨E₁, X₁⟩, encPre_pub E₂ X₂ (hpub _ _ hq)⟩ e₁ e₂).1

/-- A state satisfying the precondition of `vg_aes_siv_encrypt` and
`vg_aes_siv_decrypt`, with no associated data and no data, `siv` at
`0x5000` and `work` at `0x4000` (the stack arguments' words at `0x8008` and
`0x800c`). -/
def encSat (rd wr : List Region) : State :=
  { sivSat (fun r => match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | _ => 0) rd wr with
    mem := fun a => if a = 0x8009 then 0x50 else if a = 0x800d then 0x40 else 0 }

theorem encSat_pre : ∃ s, (Proof.AesSiv.encryptScratchContract Arm.abi 16).pre s := by
  sig_implies_sat [Proof.AesSiv.encryptScratchContract, Proof.AesSiv.encryptScratchSig, Spec.Siv.encryptPre,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [encSat, sivSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using encSat [⟨0x1000, 512⟩, ⟨0x2000, 0⟩, ⟨0x8000, 16⟩] [⟨0, 0⟩, ⟨0x5000, 16⟩, ⟨0x4000, 2576⟩]

theorem decSat_pre : ∃ s, (Proof.AesSiv.decryptScratchContract Arm.abi 16).pre s := by
  sig_implies_sat [Proof.AesSiv.decryptScratchContract, Proof.AesSiv.decryptScratchSig, Spec.Siv.decryptPre,
    Spec.Siv.decryptLeak, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [encSat, sivSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using encSat [⟨0x1000, 512⟩, ⟨0x5000, 16⟩, ⟨0x2000, 0⟩, ⟨0x8000, 16⟩] [⟨0, 0⟩, ⟨0x4000, 2576⟩]

theorem encrypt_verified : Verified Arm.target encrypt (Proof.AesSiv.encryptScratchContract Arm.abi 16) := by
  refine ⟨fun s hs => ?_, enc_ct (X := fun T s => Covers [⟨State.addr T, 16⟩] s.wr)
    (fun s h => ⟨(encPre_of h).1, (encPre_of h).2.1⟩) (fun s₁ s₂ hp => ?_)
    (fun L hR hN hn => encrypt_ct L hR hN hn), encSat_pre⟩
  · obtain ⟨E, hTw, hTd⟩ := encPre_of hs
    obtain ⟨t, s', he, hq⟩ := encrypt_wp E.pre.lay E.pre hTw hTd
    refine ⟨t, s', he, hq.1, ?_⟩
    sig_post [Proof.AesSiv.encryptScratchContract, Proof.AesSiv.encryptScratchSig, Proof.AesSiv.encryptRoundsPost,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    exact fun _ => hq.2
  · sig_pub [Proof.AesSiv.encryptScratchContract, Proof.AesSiv.encryptScratchSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] at hp
    sig_split hp
    rename_i q0 q1 q2 q3 q4 q5 q6 q7 q8
    exact ⟨⟨q0, q1, q2, q3, q4, q5, q6, q7, q8⟩, hp⟩

theorem decrypt_verified : Verified Arm.target decrypt (Proof.AesSiv.decryptScratchContract Arm.abi 16) := by
  refine ⟨fun s hs => ?_, enc_ct (X := fun _ _ => True) (fun s h => ⟨decPre_of h, trivial⟩)
    (fun s₁ s₂ hp => ?_) (fun L hR hN hn => (decrypt_ct L hR hN hn).mono fun s h => h.1), decSat_pre⟩
  · obtain ⟨t, s', he, hq⟩ := decrypt_wp (decPre_of hs).pre.lay (decPre_of hs).pre
    refine ⟨t, s', he, hq.1, ?_⟩
    sig_post [Proof.AesSiv.decryptScratchContract, Proof.AesSiv.decryptScratchSig, Proof.AesSiv.decryptRoundsPost,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    have e : ∀ x y : BitVec 32, (x ++ y).setWidth 32 = y := fun _ _ => BitVec.setWidth_append_eq_right
    rw [e]
    exact fun _ => hq.2
  · sig_pub [Proof.AesSiv.decryptScratchContract, Proof.AesSiv.decryptScratchSig, Spec.Siv.decryptLeak, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] at hp
    sig_split hp
    rename_i q0 _ q1 q2 q3 q4 q5 q6 q7 q8
    exact ⟨⟨q0, q1, q2, q3, q4, q5, q6, q7, q8⟩, hp⟩

end VG.Proof.AesSiv.Arm
