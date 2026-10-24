module
public import VerifiedGarbage.Proof.AesGcm.AArch64.CalleePw
public import VerifiedGarbage.Proof.AesGcm.AArch64.OneShot
public import VerifiedGarbage.Proof.AesGcm.AArch64.Verified
public import VerifiedGarbage.Proof.AesGcm.ScratchPowers8
public import VerifiedGarbage.Impl.StackScratch.AArch64
public import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Groups

import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenVerified
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenCT
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.Offset

/-!
# AES-GCM on AArch64: `vg_aes_gcm_open_with_powers`

Untrusted: everything here is checked by Lean. `vg_aes_gcm_open_with_powers`
is `open` with `pw` a stack argument after `tag_len` (so `work` one slot
further, `Fast.openWithPw`), its whole blocks on the path for TLS records
hashed by `vg_ghash_with_powers`, called with `pw` loaded from the stack
(`Fast.pwSel 16`), as `vg_aes_gcm_seal_with_powers` does (`SealPw.lean`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64.Fast

open VG VG.AArch64 VG.Impl.AesGcm.AArch64
open VG.Proof.AesGcm.AArch64

/-- The powers' buffer, the stack argument 2. -/
abbrev pwRO (s : State) : Region := ⟨stackArg s 2, 128⟩

/-- What `vg_aes_gcm_open_with_powers` needs, on the regions its proofs run
on: `openPreXW 3`, with `pw` readable, apart from the text and the working
space, and holding the powers of the hash subkey. -/
def openPwN (s : State) : Prop :=
  openPreXW 3 [pwRO s] s ∧ (pwRO s).Disjoint ⟨s.gpr .x6, (s.gpr .x7).toNat⟩ ∧
    (pwRO s).Disjoint ⟨stackArg s 3, 2560⟩ ∧
    Spec.Gcm.Powers8Repr s.mem (stackArg s 2) (Spec.Gcm.ctxH s.mem (s.gpr .x0))

/-- What `vg_aes_gcm_open_with_powers` needs: `openPreXW 3`, with `pw`
readable before the stack arguments, holding the powers. -/
def openPwW (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .x0, 256⟩
  let nonce : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  let aad : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
  let data : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
  let tag : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
  let pw : Region := pwRO s
  let work : Region := ⟨stackArg s 3, 2560⟩
  s.rd = [ctx, nonce, aad, tag, pw, args s 4] ∧ s.wr = [data, work] ∧
    ctx.Disjoint data ∧ ctx.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧ pw.Disjoint data ∧
    data.Disjoint work ∧ data.Disjoint (args s 4) ∧ tag.Disjoint work ∧ pw.Disjoint work ∧
    work.Disjoint (args s 4) ∧
    (s.gpr .x0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64 ∧
    (stackArg s 3).toNat + 2560 ≤ 2 ^ 64 ∧ s.sp.toNat + 8 * 4 ≤ 2 ^ 64 ∧ rounds (s.gpr .x1) ∧
    Spec.Gcm.Powers8Repr s.mem (stackArg s 2) (Spec.Gcm.ctxH s.mem (s.gpr .x0))

/-- `vg_aes_gcm_open_with_powers`. -/
def openPwAArch64 : Contract isa where
  pre := openPwW
  post := openAArch64.post
  pub s₁ s₂ := onePub 4 s₁ s₂ ∧ openLeakOf s₁ = openLeakOf s₂

/-! ## The call of `vg_ghash_with_powers` -/

/-- At the call, with memory changed since the entry only in the working
space and the text: `pw` is at `[sp + 16]`, readable, apart from the
accumulator and the working space of the call, and holds the powers. -/
theorem gwCallO_of {σ s : State} {Y S : Addr} (hs : openPwN σ) (sY : Region.Sub ⟨Y, 16⟩ (workR (stackArg σ 3)))
    (sS : Region.Sub ⟨S, 256⟩ (workR (stackArg σ 3))) (hrd : s.rd = σ.rd) (hwr : s.wr = σ.wr) (hsp : s.sp = σ.sp)
    (hf : Frame [workR (stackArg σ 3), ⟨σ.gpr .x6, (σ.gpr .x7).toNat⟩] σ.mem s.mem) :
    s.mem.readW (s.sp + BitVec.ofNat 64 16) 64 = stackArg σ 2 ∧
      InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 16) 8 ∧
      GhWCall s (σ.gpr .x0) Y S (stackArg σ 2) := by
  obtain ⟨hpx, pd, pw, rep⟩ := hs
  obtain ⟨ol, -, -⟩ := openLay hpx
  have hrd₀ := hpx.1
  have hp' := hpx
  simp only [openPreXW] at hp'
  obtain ⟨-, -, -, -, -, -, -, -, -, dda, -⟩ := hp'
  have hspA := ol.hsp 2 (by decide)
  have sA : Region.Sub ⟨σ.sp + BitVec.ofNat 64 16, 8⟩ (args σ 4) := by
    show Region.Sub ⟨σ.sp + BitVec.ofNat 64 16, 8⟩ ⟨σ.sp + BitVec.ofNat 64 (8 * 0), 8 * 4⟩
    rw [show σ.sp + BitVec.ofNat 64 (8 * 0) = σ.sp by rw [Nat.mul_zero, BitVec.add_zero]]
    exact Offset.sub_base _ (by decide)
  refine ⟨?_, by rw [hrd, hwr, hsp]; exact hspA, ⟨?_, (pw.sub_right sY).symm, (pw.sub_right sS).symm, ?_⟩⟩
  · rw [hsp, hf.readW (r := ⟨σ.sp + BitVec.ofNat 64 16, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ol.args.sub_left sA
      · exact (dda.sub_right sA).symm) (by decide)]
    rfl
  · refine Covers.left (Covers.of_mem fun r hr => ?_)
    simp only [List.mem_singleton] at hr
    subst hr
    rw [hrd, hrd₀]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  · have hH : Spec.Gcm.blockAt s.mem (σ.gpr .x0 + BitVec.ofNat 64 240) = Spec.Gcm.ctxH σ.mem (σ.gpr .x0) :=
      blockAt_frame hf fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ol.ctx.sub_left (Lay.ctxSub (d := 240) (n := 16) (by decide))
        · exact ol.cd.sub_left (Lay.ctxSub (d := 240) (n := 16) (by decide))
    rw [hH]
    exact Proof.AesGcm.powers8Repr_congr (fun i hi => hf.bytes (R := pwRO σ) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact pw
        · exact pd) (show 128 ≤ 2 ^ 64 by decide) hi) rep

/-! ## On the regions of the proofs -/

section
variable (v : GcmImpl) (g : GhashWithImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey)
include hMK

theorem openPw_correctN (s : State) (hs : openPwN s) :
    ∃ t s', Exec isa (Impl.AesGcm.AArch64.Fast.openWithPw v.callees g.fn) s t s' ∧ abiPreserved s s' ∧
      openAArch64.post s s' :=
  WP.withPreservedV (openWithE_wp (w := 3) _ v hMK (.inr rfl) hs.1 fun _ _ _ _ _ hc sY sS hrd hwr hsp hf =>
      have q := gwCallO_of hs sY sS hrd hwr hsp hf
      pwSel_call v g (k := 16) (by decide) q.1 q.2.1 hc q.2.2)
    (fastOpenWithE_keepsV v (.inr rfl) (pwSel_keepsV v g (.inr rfl)))

theorem openPw_ctN :
    ConstantTime isa openPwN (fun s₁ s₂ => onePub 4 s₁ s₂ ∧ openLeakOf s₁ = openLeakOf s₂)
      (Impl.AesGcm.AArch64.Fast.openWithPw v.callees g.fn) :=
  openWithE_ct (w := 3) v _ hMK (.inr rfl) (extra := fun s => [pwRO s]) (fun _ h => h.1)
    (fun p hc sY sS hrd hwr hsp hf =>
      have q := gwCallO_of p sY sS hrd hwr hsp hf
      pwSel_call v g (k := 16) (by decide) q.1 q.2.1 hc q.2.2)
    fun {σ₁ σ₂ s₁ s₂ _ _ _ _} p₁ p₂ hq c₁ c₂ sY sS sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂ => by
      obtain ⟨q0, -, -, -, -, -, q6, q7, qsp, qa⟩ := hq
      have e3 : stackArg σ₁ 3 = stackArg σ₂ 3 := qa 3 (by decide)
      have e2 : stackArg σ₁ 2 = stackArg σ₂ 2 := qa 2 (by decide)
      obtain ⟨hP₁, hs₁, k₁⟩ := gwCallO_of p₁ sY sS r₁ w₁ sp₁ f₁
      obtain ⟨hP₂, hs₂, k₂⟩ := gwCallO_of p₂ (by rw [← e3]; exact sY) (by rw [← e3]; exact sS) r₂ w₂
        (sp₂.trans qsp) (by rw [← e3, ← q6, ← q7]; exact f₂)
      rw [← e2] at hP₂ k₂
      rw [← q0] at k₂
      exact pwSel_rel v g (.inr rfl) hP₁ hs₁ hP₂ hs₂ c₁ k₁ c₂ k₂ (sp₁.trans sp₂.symm)

end

/-! ## On the shared contract's regions -/

/-- The readable regions of the proofs: `pw` after the stack arguments. -/
def narrowRdPO (s : State) : List Region :=
  [⟨s.gpr .x0, 256⟩, ⟨s.gpr .x2, (s.gpr .x3).toNat⟩, ⟨s.gpr .x4, (s.gpr .x5).toNat⟩,
    ⟨stackArg s 0, (stackArg s 1).toNat⟩, args s 4, pwRO s]

/-- `s` with the readable regions of the proofs. -/
def narrowPO (s : State) : State := s.withRegions (narrowRdPO s) s.wr

theorem narrowPO_pre {s : State} (h : openPwW s) : openPwN (narrowPO s) := by
  obtain ⟨-, hwr, cd, cw, nd, nw, ad, aw, pd, dw, da, tw, pw, wa, b0, b2, b4, b6, b1, bsp, hr, rep⟩ := h
  exact ⟨⟨rfl, hwr, cd, cw, nd, nw, ad, aw, dw, da, tw, wa, b0, b2, b4, b6, b1, bsp, hr⟩, pd, pw, rep⟩

theorem narrowPO_covers {s : State} (h : openPwW s) :
    Covers ((narrowPO s).rd ++ (narrowPO s).wr) (s.rd ++ s.wr) := by
  rw [show (narrowPO s).rd = narrowRdPO s from rfl, show (narrowPO s).wr = s.wr from rfl, h.1]
  refine Covers.append (Covers.of_mem fun r hr => ?_) (Covers.refl _)
  simp only [narrowRdPO, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem narrowPO_exec {c : Prog isa} {s s₁ : State} {t : List Leak} (h : openPwW s)
    (he : Exec isa c (narrowPO s) t s₁) : Exec isa c s t (s₁.withRegions s.rd s.wr) := by
  have := Exec.widen he (narrowPO_covers h) (Covers.refl _)
  rwa [show (narrowPO s).withRegions s.rd s.wr = s from rfl] at this

/-- A state satisfying `vg_aes_gcm_open_with_powers`'s precondition: `openSat`
with `pw` at `0x6000` (`[sp + 16]`) and `work` at `0x5000` (`[sp + 24]`). -/
def openSatPw : State :=
  { openSat with
    mem := fun a => if a = 0x8019 then 0x50 else if a = 0x8011 then 0x60 else 0
    rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0, 0⟩, ⟨0x6000, 128⟩, ⟨0x8000, 32⟩] }

/-- `pw`'s bytes in `openSatPw` are zero. -/
theorem openSatPw_zero : ∀ i < 16 * 8, openSatPw.mem (stackArg openSatPw 2 + BitVec.ofNat 64 i) = 0 := by
  intro i hi
  have hP : stackArg openSatPw 2 = 0x6000 := by decide
  rw [hP]
  show (if (0x6000 : BitVec 64) + BitVec.ofNat 64 i = 0x8019 then 0x50
    else if (0x6000 : BitVec 64) + BitVec.ofNat 64 i = 0x8011 then 0x60 else 0) = 0
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by bv_omega)), ite_eq_right_of_eq_false _ _ (eq_false (by bv_omega))]

section
variable (v : GcmImpl) (g : GhashWithImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey)
include hMK

theorem openPw_correct (s : State) (hs : openPwAArch64.pre s) :
    ∃ t s', Exec isa (Impl.AesGcm.AArch64.Fast.openWithPw v.callees g.fn) s t s' ∧ abiPreserved s s' ∧
      openPwAArch64.post s s' := by
  obtain ⟨t, s₁, he, ha, hp⟩ := openPw_correctN v g hMK _ (narrowPO_pre hs)
  exact ⟨t, _, narrowPO_exec hs he, ha, hp⟩

theorem openPw_ct :
    ConstantTime isa openPwAArch64.pre openPwAArch64.pub (Impl.AesGcm.AArch64.Fast.openWithPw v.callees g.fn) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂
  obtain ⟨u₁, r₁, f₁, -⟩ := openPw_correctN v g hMK _ (narrowPO_pre h₁)
  obtain ⟨u₂, r₂, f₂, -⟩ := openPw_correctN v g hMK _ (narrowPO_pre h₂)
  rw [(Exec.det e₁ (narrowPO_exec h₁ f₁)).1, (Exec.det e₂ (narrowPO_exec h₂ f₂)).1]
  exact openPw_ctN v g hMK _ _ _ _ _ _ (narrowPO_pre h₁) (narrowPO_pre h₂) hq f₁ f₂

theorem openPw_verified :
    Verified AArch64.target (Impl.AesGcm.AArch64.Fast.openWithPw v.callees g.fn)
      (Proof.AesGcm.openWithPowersScratchContract AArch64.abi) :=
  Verified.of_correct (openPw_correct v g hMK) (openPw_ct v g hMK)
    { pre := by
        sig_implies_pre [Proof.AesGcm.openWithPowersScratchContract, Proof.AesGcm.openWithPowersScratchSig,
          Spec.Gcm.openWithPowersPre, Spec.Gcm.openPre, Spec.Gcm.openWithPowersPost, Spec.Gcm.openPost,
          Spec.Gcm.openWithPowersLeak, Spec.Gcm.openLeak, openPwAArch64, openPwW, pwRO, openAArch64, onePub,
          openRes, openLeakOf, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr,
          List.getD, List.range, List.range.loop]
      post := by
        sig_implies_post [Proof.AesGcm.openWithPowersScratchContract, Proof.AesGcm.openWithPowersScratchSig,
          Spec.Gcm.openWithPowersPre, Spec.Gcm.openPre, Spec.Gcm.openWithPowersPost, Spec.Gcm.openPost,
          Spec.Gcm.openWithPowersLeak, Spec.Gcm.openLeak, openPwAArch64, openPwW, pwRO, openAArch64, onePub,
          openRes, openLeakOf, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr,
          List.getD, List.range, List.range.loop]
      pub := by
        sig_implies_pub [Proof.AesGcm.openWithPowersScratchContract, Proof.AesGcm.openWithPowersScratchSig,
          Spec.Gcm.openWithPowersPre, Spec.Gcm.openPre, Spec.Gcm.openWithPowersPost, Spec.Gcm.openPost,
          Spec.Gcm.openWithPowersLeak, Spec.Gcm.openLeak, openPwAArch64, openPwW, pwRO, openAArch64, onePub,
          openRes, openLeakOf, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr,
          List.getD, List.range, List.range.loop]
      sat := ⟨openSatPw, by
        sig_pre [Proof.AesGcm.openWithPowersScratchContract, Proof.AesGcm.openWithPowersScratchSig,
          Spec.Gcm.openWithPowersPre, Spec.Gcm.openPre, AArch64.abi, AArch64.argRegs,
          AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop, openSatPw, openSat,
          stackArg, stackArgAddr, Mem.readW, Mem.read]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | exact Proof.AesGcm.powers8Repr_of_zeroMem (by decide) openSatPw_zero⟩ }

end

/-! ## With its working space on the stack -/

/-- `openSatPw` with its stack arguments `tag`, `tag_len` and `pw` only. -/
def openFrameSatPw : State :=
  { openSatPw with rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0, 0⟩, ⟨0x6000, 128⟩, ⟨0x8000, 24⟩],
                   wr := [⟨0x4000, 0⟩] }

theorem openFrameSatPw_pre : ∃ s, (Spec.Gcm.openWithPowersContract AArch64.abi 2592).pre s := by
  refine ⟨openFrameSatPw, ?_⟩
  sig_pre [Spec.Gcm.openWithPowersContract, Spec.Gcm.openWithPowersSig, Spec.Gcm.openSig, Spec.Gcm.withPowersParam,
    Spec.Gcm.openWithPowersPre, Spec.Gcm.openPre, Spec.Gcm.openWithPowersPost, Spec.Gcm.openPost,
    Spec.Gcm.openWithPowersLeak, Spec.Gcm.openLeak, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
    AArch64.stackArgAddr, List.getD, List.range, List.range.loop, List.cons_append, List.nil_append,
    openFrameSatPw, openSatPw, openSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Proof.AesGcm.powers8Repr_of_zeroMem (by decide) openSatPw_zero

theorem openPw_framed (v : GcmImpl) (g : GhashWithImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackArgScratch 2592 3 (Impl.AesGcm.AArch64.Fast.openWithPw v.callees g.fn))
      (Spec.Gcm.openWithPowersContract AArch64.abi 2592) :=
  AArch64.Verified.stackArgScratch (sig := Spec.Gcm.openWithPowersSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.openWithPowersPre AArch64.abi.ptrBits)
    (post := Spec.Gcm.openWithPowersPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 2592)
    (leak := some (Spec.Gcm.openWithPowersLeak AArch64.abi.ptrBits))
    (openPw_verified v g hMK) (by decide) (by decide) (Proof.AesGcm.openWithPowersPre_local _)
    (Proof.AesGcm.openWithPowersPost_local _) openFrameSatPw_pre
    (hleak := Proof.AesGcm.openWithPowersLeak_local _)

end VG.Proof.AesGcm.AArch64.Fast
