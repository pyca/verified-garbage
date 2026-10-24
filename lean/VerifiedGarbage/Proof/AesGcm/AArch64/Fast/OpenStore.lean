module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenPw
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenVerified
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenCT
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.Offset

/-!
# AES-GCM on AArch64: `vg_aes_gcm_open_store_powers`

Untrusted: everything here is checked by Lean. `vg_aes_gcm_open_store_powers`
is `vg_aes_gcm_open_with_powers`'s code (`Fast.openStorePw`) with
`vg_ghash_store_powers` (`GhashStoreImpl`) as the call on the whole blocks:
on the path for TLS records with an allowed tag length, which its
precondition requires, the call hashes as `vg_ghash` and writes the powers
of the hash subkey to `pw` (`pwS_call`), whatever the tag. The proofs of
`open` hold for a call that also writes `pw` (`openWithEX_wp`,
`openWithEX_ct`), and the rest writes only the working space and the text,
apart from `pw`.

The shared contract lists `pw` before `work` among the writable regions; the
proofs list it after them (`narrowSO`), and the code runs as it does with
either order (`Exec.widen`), with the same trace.
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64.Fast

open VG VG.AArch64 VG.Impl.AesGcm.AArch64
open VG.Proof.AesGcm.AArch64

/-- What `vg_aes_gcm_open_store_powers` needs, on the regions its proofs run
on: `openPreXW 3` with `pw` writable after the working space, apart from the
text, the working space and the key context, a TLS record and an allowed tag
length. -/
def openStN (s : State) : Prop :=
  openPreXW 3 [] s [pwRO s] ∧ (pwRO s).Disjoint ⟨s.gpr .x6, (s.gpr .x7).toNat⟩ ∧
    (pwRO s).Disjoint ⟨stackArg s 3, 2560⟩ ∧ (pwRO s).Disjoint ⟨s.gpr .x0, 256⟩ ∧
    (s.gpr .x5).toNat ≤ 16 ∧ (s.gpr .x3).toNat = 12 ∧ Spec.Gcm.tagLenOk (stackArg s 1).toNat = true

/-- What `vg_aes_gcm_open_store_powers` needs: `openPreXW 3`'s regions with
`pw` writable before the working space, a TLS record and an allowed tag
length. -/
def openStW (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .x0, 256⟩
  let nonce : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  let aad : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
  let data : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
  let tag : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
  let pw : Region := pwRO s
  let work : Region := ⟨stackArg s 3, 2560⟩
  s.rd = [ctx, nonce, aad, tag, args s 4] ∧ s.wr = [data, pw, work] ∧
    ctx.Disjoint data ∧ ctx.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧ pw.Disjoint data ∧
    data.Disjoint work ∧ data.Disjoint (args s 4) ∧ tag.Disjoint work ∧ pw.Disjoint work ∧
    work.Disjoint (args s 4) ∧ pw.Disjoint ctx ∧
    (s.gpr .x0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64 ∧
    (stackArg s 3).toNat + 2560 ≤ 2 ^ 64 ∧ s.sp.toNat + 8 * 4 ≤ 2 ^ 64 ∧ rounds (s.gpr .x1) ∧
    (s.gpr .x3).toNat = 12 ∧ (s.gpr .x5).toNat ≤ 16 ∧ Spec.Gcm.tagLenOk (stackArg s 1).toNat = true

/-- `vg_aes_gcm_open_store_powers`. -/
def openStAArch64 : Contract isa where
  pre := openStW
  post s s' := openAArch64.post s s' ∧
    Spec.Gcm.Powers8Repr s'.mem (stackArg s 2) (Spec.Gcm.ctxH s.mem (s.gpr .x0))
  pub s₁ s₂ := onePub 4 s₁ s₂ ∧ openLeakOf s₁ = openLeakOf s₂

/-! ## The call of `vg_ghash_store_powers` -/

/-- At the call, with memory changed since the entry only in the working
space and the text: `pw` is at `[sp + 16]`, writable, apart from the
accumulator, the working space of the call and the blocks it hashes, and the
hash subkey is the entry's. -/
theorem gsCallO_of {σ s : State} {Y Dd S : Addr} {nb : Nat} (hs : openStN σ)
    (sY : Region.Sub ⟨Y, 16⟩ (workR (stackArg σ 3))) (sS : Region.Sub ⟨S, 256⟩ (workR (stackArg σ 3)))
    (hrd : s.rd = σ.rd) (hwr : s.wr = σ.wr) (hsp : s.sp = σ.sp)
    (hf : Frame [workR (stackArg σ 3), ⟨σ.gpr .x6, (σ.gpr .x7).toNat⟩] σ.mem s.mem)
    (hd : Region.Sub ⟨Dd, 16 * nb⟩ ⟨σ.gpr .x6, (σ.gpr .x7).toNat⟩) :
    s.mem.readW (s.sp + BitVec.ofNat 64 16) 64 = stackArg σ 2 ∧
      InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 16) 8 ∧
      GhSCall s (σ.gpr .x0) Y Dd S (stackArg σ 2) nb ∧
      Spec.Gcm.blockAt s.mem (σ.gpr .x0 + BitVec.ofNat 64 240) = Spec.Gcm.ctxH σ.mem (σ.gpr .x0) := by
  obtain ⟨hpx, pd, pw, pc, -, -, -⟩ := hs
  obtain ⟨ol, -, -⟩ := openLay hpx
  have hwr₀ := hpx.2.1
  have hp' := hpx
  simp only [openPreXW] at hp'
  obtain ⟨-, -, -, -, -, -, -, -, -, dda, -⟩ := hp'
  have hspA := ol.hsp 2 (by decide)
  have sA : Region.Sub ⟨σ.sp + BitVec.ofNat 64 16, 8⟩ (args σ 4) := by
    show Region.Sub ⟨σ.sp + BitVec.ofNat 64 16, 8⟩ ⟨σ.sp + BitVec.ofNat 64 (8 * 0), 8 * 4⟩
    rw [show σ.sp + BitVec.ofNat 64 (8 * 0) = σ.sp by rw [Nat.mul_zero, BitVec.add_zero]]
    exact Offset.sub_base _ (by decide)
  refine ⟨?_, by rw [hrd, hwr, hsp]; exact hspA, ⟨?_, (pc.sub_right (Lay.ctxSub (d := 240) (n := 16)
    (by decide))).symm, (pw.sub_right sY).symm, (pd.sub_right hd).symm, (pw.sub_right sS).symm⟩, ?_⟩
  · rw [hsp, hf.readW (r := ⟨σ.sp + BitVec.ofNat 64 16, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ol.args.sub_left sA
      · exact (dda.sub_right sA).symm) (by decide)]
    rfl
  · refine Covers.of_mem fun r hr => ?_
    simp only [List.mem_singleton] at hr
    subst hr
    rw [hwr, hwr₀]
    simp
  · exact blockAt_frame hf fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ol.ctx.sub_left (Lay.ctxSub (d := 240) (n := 16) (by decide))
      · exact ol.cd.sub_left (Lay.ctxSub (d := 240) (n := 16) (by decide))

/-- The powers at `pw` survive what the rest writes. -/
theorem powers_keepO {σ : State} (hs : openStN σ) {H : Spec.Gcm.Block} {m m' : Mem}
    (h : Spec.Gcm.Powers8Repr m (stackArg σ 2) H)
    (hf : Frame [workR (stackArg σ 3), ⟨σ.gpr .x6, (σ.gpr .x7).toNat⟩] m m') :
    Spec.Gcm.Powers8Repr m' (stackArg σ 2) H := by
  obtain ⟨-, pd, pw, -, -, -, -⟩ := hs
  exact Proof.AesGcm.powers8Repr_congr (fun i hi => hf.bytes (R := pwRO σ) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact pw
      · exact pd) (show 128 ≤ 2 ^ 64 by decide) hi) h

/-! ## On the regions of the proofs -/

theorem pwCallS16_keepsV (g : GhashStoreImpl) :
    (Impl.AesGcm.AArch64.Fast.pwCall 16 g.fn).allInstrs keepsV = true := by
  simp only [Impl.AesGcm.AArch64.Fast.pwCall, Code.allInstrs, g.keepsV, Bool.and_true]
  decide

section
variable (v : GcmImpl) (g : GhashStoreImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey)
include hMK

theorem openSt_correctN (s : State) (hs : openStN s) :
    ∃ t s', Exec isa (Impl.AesGcm.AArch64.Fast.openStorePw v.callees g.fn) s t s' ∧ abiPreserved s s' ∧
      openStAArch64.post s s' := by
  have hs' := hs
  obtain ⟨hpx, pd, pw, pc, h16, h12, htl⟩ := hs'
  exact WP.withPreservedV (WP.mono (openWithEX_wp (w := 3) _ v hMK (.inr rfl) (ex := [pwRO s]) hpx ⟨h16, h12⟩ htl
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact pw.symm)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact pd.symm)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact pc.symm)
      (fun hi hf => powers_keepO hs hi hf)
      fun s' _ _ _ _ hc sY sS hrd hwr hsp hf hd =>
        have q := gsCallO_of hs sY sS hrd hwr hsp hf hd
        WP.mono (pwS_call g (k := 16) (by decide) q.1 q.2.1 hc q.2.2.1) fun _ ⟨gp, pp⟩ =>
          ⟨gp, by rw [← q.2.2.2]; exact pp⟩) fun _ ⟨⟨ga, p⟩, q⟩ => ⟨ga, p, q⟩)
    (fastOpenWithE_keepsV v (.inr rfl) (pwCallS16_keepsV g))

theorem openSt_ctN :
    ConstantTime isa openStN (fun s₁ s₂ => onePub 4 s₁ s₂ ∧ openLeakOf s₁ = openLeakOf s₂)
      (Impl.AesGcm.AArch64.Fast.openStorePw v.callees g.fn) :=
  openWithEX_ct (w := 3) v _ hMK (.inr rfl) (extra := fun _ => []) (extraW := fun s => [pwRO s])
    (ex := fun s => [pwRO s]) (fun _ h => h.1)
    (fun h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.2.2.1.symm)
    (fun h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.2.1.symm)
    (fun h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.2.2.2.1.symm)
    (fun hq => by obtain ⟨-, -, -, -, -, -, -, -, -, qa⟩ := hq; simp only [pwRO, qa 2 (by decide)])
    (fun p hc sY sS hrd hwr hsp hf hd =>
      have q := gsCallO_of p sY sS hrd hwr hsp hf hd
      WP.mono (pwS_call g (k := 16) (by decide) q.1 q.2.1 hc q.2.2.1) fun _ q' => q'.1)
    fun {σ₁ σ₂ s₁ s₂ _ _ _ _} p₁ p₂ hq c₁ c₂ sY sS sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂ hd => by
      obtain ⟨q0, -, -, -, -, -, q6, q7, qsp, qa⟩ := hq
      have e3 : stackArg σ₁ 3 = stackArg σ₂ 3 := qa 3 (by decide)
      have e2 : stackArg σ₁ 2 = stackArg σ₂ 2 := qa 2 (by decide)
      obtain ⟨hP₁, hs₁, k₁, -⟩ := gsCallO_of p₁ sY sS r₁ w₁ sp₁ f₁ hd
      obtain ⟨hP₂, hs₂, k₂, -⟩ := gsCallO_of p₂ (by rw [← e3]; exact sY) (by rw [← e3]; exact sS) r₂ w₂
        (sp₂.trans qsp) (by rw [← e3, ← q6, ← q7]; exact f₂) (by rw [← q6, ← q7]; exact hd)
      rw [← e2] at hP₂ k₂
      rw [← q0] at k₂
      exact pwS_rel g (.inr rfl) hP₁ hs₁ hP₂ hs₂ c₁ k₁ c₂ k₂ (sp₁.trans sp₂.symm)

end

/-! ## On the shared contract's regions -/

/-- The writable regions of the proofs: `pw` after the working space. -/
def narrowWrSO (s : State) : List Region :=
  [⟨s.gpr .x6, (s.gpr .x7).toNat⟩, ⟨stackArg s 3, 2560⟩, pwRO s]

/-- `s` with the writable regions of the proofs. -/
def narrowSO (s : State) : State := s.withRegions s.rd (narrowWrSO s)

theorem narrowSO_pre {s : State} (h : openStW s) : openStN (narrowSO s) := by
  obtain ⟨hrd, -, cd, cw, nd, nw, ad, aw, pd, dw, da, tw, pw, wa, pc, b0, b2, b4, b6, b1, bsp, hr,
    h12, h16, htl⟩ := h
  exact ⟨⟨by rw [show (narrowSO s).rd = s.rd from rfl, hrd]; rfl, rfl, cd, cw, nd, nw, ad, aw, dw, da, tw, wa,
    b0, b2, b4, b6, b1, bsp, hr⟩, pd, pw, pc, h16, h12, htl⟩

theorem narrowSO_covers {s : State} (h : openStW s) :
    Covers ((narrowSO s).rd ++ (narrowSO s).wr) (s.rd ++ s.wr) ∧ Covers (narrowSO s).wr s.wr := by
  have w : Covers (narrowSO s).wr s.wr := by
    rw [show (narrowSO s).wr = narrowWrSO s from rfl, h.2.1]
    refine Covers.of_mem fun r hr => ?_
    simp only [narrowWrSO, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl <;> simp
  exact ⟨Covers.append (Covers.refl _) w, w⟩

theorem narrowSO_exec {c : Prog isa} {s s₁ : State} {t : List Leak} (h : openStW s)
    (he : Exec isa c (narrowSO s) t s₁) : Exec isa c s t (s₁.withRegions s.rd s.wr) := by
  have := Exec.widen he (narrowSO_covers h).1 (narrowSO_covers h).2
  rwa [show (narrowSO s).withRegions s.rd s.wr = s from rfl] at this

/-- A state satisfying `vg_aes_gcm_open_store_powers`'s precondition:
`openSat` with a 12-byte nonce, a 16-byte tag at 0, `pw` at `0x6000`
(`[sp + 16]`) and `work` at `0x5000` (`[sp + 24]`). -/
def openSatSt : State :=
  { openSat with
    gpr := fun r => match r with
      | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x2000 | .x3 => 12 | .x4 => 0x3000 | .x6 => 0x4000 | _ => 0
    mem := fun a => if a = 0x8019 then 0x50 else if a = 0x8011 then 0x60 else if a = 0x8008 then 0x10 else 0
    rd := [⟨0x1000, 256⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩, ⟨0, 16⟩, ⟨0x8000, 32⟩]
    wr := [⟨0x4000, 0⟩, ⟨0x6000, 128⟩, ⟨0x5000, 2560⟩] }

section
variable (v : GcmImpl) (g : GhashStoreImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey)
include hMK

theorem openSt_correct (s : State) (hs : openStAArch64.pre s) :
    ∃ t s', Exec isa (Impl.AesGcm.AArch64.Fast.openStorePw v.callees g.fn) s t s' ∧ abiPreserved s s' ∧
      openStAArch64.post s s' := by
  obtain ⟨t, s₁, he, ha, hp⟩ := openSt_correctN v g hMK _ (narrowSO_pre hs)
  exact ⟨t, _, narrowSO_exec hs he, ha, hp⟩

theorem openSt_ct :
    ConstantTime isa openStAArch64.pre openStAArch64.pub (Impl.AesGcm.AArch64.Fast.openStorePw v.callees g.fn) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂
  obtain ⟨u₁, r₁, f₁, -⟩ := openSt_correctN v g hMK _ (narrowSO_pre h₁)
  obtain ⟨u₂, r₂, f₂, -⟩ := openSt_correctN v g hMK _ (narrowSO_pre h₂)
  rw [(Exec.det e₁ (narrowSO_exec h₁ f₁)).1, (Exec.det e₂ (narrowSO_exec h₂ f₂)).1]
  exact openSt_ctN v g hMK _ _ _ _ _ _ (narrowSO_pre h₁) (narrowSO_pre h₂) hq f₁ f₂

theorem openSt_verified :
    Verified AArch64.target (Impl.AesGcm.AArch64.Fast.openStorePw v.callees g.fn)
      (Proof.AesGcm.openStorePowersScratchContract AArch64.abi) :=
  Verified.of_correct (openSt_correct v g hMK) (openSt_ct v g hMK)
    { pre := by
        sig_implies_pre [Proof.AesGcm.openStorePowersScratchContract, Proof.AesGcm.openStorePowersScratchSig,
          Proof.AesGcm.openStorePowersPreP, Spec.Gcm.openPre, Spec.Gcm.storePowersOk,
          Spec.Gcm.openStorePowersPost, Spec.Gcm.openPost, Proof.AesGcm.openStorePowersLeakP, Spec.Gcm.openLeak,
          openStAArch64, openStW, pwRO, openAArch64, onePub, openRes, openLeakOf, args, rounds, AArch64.abi,
          AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      post := by
        intro s s' _ h
        sig_post [Proof.AesGcm.openStorePowersScratchContract, Proof.AesGcm.openStorePowersScratchSig,
          Proof.AesGcm.openStorePowersPreP, Spec.Gcm.openPre, Spec.Gcm.storePowersOk,
          Spec.Gcm.openStorePowersPost, Spec.Gcm.openPost, Proof.AesGcm.openStorePowersLeakP, Spec.Gcm.openLeak,
          openStAArch64, openStW, pwRO, openAArch64, onePub, openRes, openLeakOf, args, rounds, AArch64.abi,
          AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
        sig_reduce [openStAArch64, openAArch64, openRes, AArch64.stackArg, AArch64.stackArgAddr] at h
        sig_simp [openStAArch64, openAArch64, openRes, AArch64.stackArg, AArch64.stackArgAddr] [] at h
        exact ⟨fun _ => h.1, h.2⟩
      pub := by
        sig_implies_pub [Proof.AesGcm.openStorePowersScratchContract, Proof.AesGcm.openStorePowersScratchSig,
          Proof.AesGcm.openStorePowersPreP, Spec.Gcm.openPre, Spec.Gcm.storePowersOk,
          Spec.Gcm.openStorePowersPost, Spec.Gcm.openPost, Proof.AesGcm.openStorePowersLeakP, Spec.Gcm.openLeak,
          openStAArch64, openStW, pwRO, openAArch64, onePub, openRes, openLeakOf, args, rounds, AArch64.abi,
          AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      sat := ⟨openSatSt, by
        sig_pre [Proof.AesGcm.openStorePowersScratchContract, Proof.AesGcm.openStorePowersScratchSig,
          Proof.AesGcm.openStorePowersPreP, Spec.Gcm.openPre, Spec.Gcm.storePowersOk, AArch64.abi,
          AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop,
          openSatSt, openSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)⟩ }

end

/-! ## With its working space on the stack -/

/-- `openSatSt` with its stack arguments `tag`, `tag_len` and `pw` only. -/
def openFrameSatSt : State :=
  { openSatSt with rd := [⟨0x1000, 256⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩, ⟨0, 16⟩, ⟨0x8000, 24⟩],
                   wr := [⟨0x4000, 0⟩, ⟨0x6000, 128⟩] }

theorem openFrameSatSt_pre : ∃ s, (Spec.Gcm.openStorePowersContract AArch64.abi 2592).pre s := by
  refine ⟨openFrameSatSt, ?_⟩
  sig_pre [Spec.Gcm.openStorePowersContract, Spec.Gcm.openStorePowersSig, Spec.Gcm.openSig,
    Spec.Gcm.storePowersParam, Spec.Gcm.openPre, Spec.Gcm.storePowersOk, Spec.Gcm.openStorePowersPost,
    Spec.Gcm.openPost, Spec.Gcm.openLeak, AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr,
    List.getD, List.range, List.range.loop, List.cons_append, List.nil_append, openFrameSatSt, openSatSt, openSat,
    stackArg, stackArgAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)

theorem openSt_framed (v : GcmImpl) (g : GhashStoreImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackArgScratch 2592 3 (Impl.AesGcm.AArch64.Fast.openStorePw v.callees g.fn))
      (Spec.Gcm.openStorePowersContract AArch64.abi 2592) :=
  AArch64.Verified.stackArgScratch (sig := Spec.Gcm.openStorePowersSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Proof.AesGcm.openStorePowersPreP AArch64.abi.ptrBits)
    (post := Spec.Gcm.openStorePowersPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 2592)
    (leak := some (Proof.AesGcm.openStorePowersLeakP AArch64.abi.ptrBits))
    (openSt_verified v g hMK) (by decide) (by decide) (Proof.AesGcm.openStorePowersPre_local _)
    (Proof.AesGcm.openStorePowersPost_local _) openFrameSatSt_pre
    (hleak := Proof.AesGcm.openStorePowersLeak_local _)

end VG.Proof.AesGcm.AArch64.Fast
