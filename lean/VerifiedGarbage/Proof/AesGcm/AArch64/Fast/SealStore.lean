module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.SealPw
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# AES-GCM on AArch64: `vg_aes_gcm_seal_store_powers`

Untrusted: everything here is checked by Lean. `vg_aes_gcm_seal_store_powers`
is `vg_aes_gcm_seal_with_powers`'s code (`Fast.sealWithPw`) with
`vg_ghash_store_powers` (`GhashStoreImpl`) as the call on the whole blocks:
on the path for TLS records, which its precondition requires (a 12-byte
nonce and at most 16 bytes of additional data), the call hashes as
`vg_ghash` and writes the powers of the hash subkey to `pw` (`pwS_call`).
The proofs of `seal` hold for a call that also writes `pw`
(`sealWithEX_wp`, `sealWithEX_ct`), and the rest of the path writes only
the working space, the text and the tag, apart from `pw`, so the powers are
there on return.

The shared contract lists `pw` before `work` among the writable regions; the
proofs list it after them (`narrowS`), and the code runs as it does with
either order (`Exec.widen`), with the same trace.
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64.Fast

open VG VG.AArch64 VG.Impl.AesGcm.AArch64
open VG.Proof.AesGcm.AArch64

/-- What `vg_aes_gcm_seal_store_powers` needs, on the regions its proofs run
on: `sealPreXW 2` with `pw` writable after the working space, apart from the
text, the working space, the key context and the tag, and a TLS record. -/
def sealStN (s : State) : Prop :=
  sealPreXW 2 [] s [pwR s] ∧ (pwR s).Disjoint ⟨s.gpr .x6, (s.gpr .x7).toNat⟩ ∧
    (pwR s).Disjoint ⟨stackArg s 2, 2560⟩ ∧ (pwR s).Disjoint ⟨s.gpr .x0, 256⟩ ∧
    (pwR s).Disjoint ⟨stackArg s 0, 16⟩ ∧ (s.gpr .x5).toNat ≤ 16 ∧ (s.gpr .x3).toNat = 12

/-- What `vg_aes_gcm_seal_store_powers` needs: `sealPreXW 2`'s regions with
`pw` writable before the working space, and a TLS record. -/
def sealStW (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .x0, 256⟩
  let nonce : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  let aad : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
  let data : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
  let tag : Region := ⟨stackArg s 0, 16⟩
  let pw : Region := pwR s
  let work : Region := ⟨stackArg s 2, 2560⟩
  s.rd = [ctx, nonce, aad, args s 3] ∧ s.wr = [data, tag, pw, work] ∧
    ctx.Disjoint data ∧ ctx.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧ data.Disjoint tag ∧ pw.Disjoint data ∧
    data.Disjoint work ∧ data.Disjoint (args s 3) ∧ tag.Disjoint work ∧ pw.Disjoint work ∧
    work.Disjoint (args s 3) ∧ pw.Disjoint ctx ∧ pw.Disjoint tag ∧
    (s.gpr .x0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64 ∧
    (stackArg s 2).toNat + 2560 ≤ 2 ^ 64 ∧ s.sp.toNat + 8 * 3 ≤ 2 ^ 64 ∧ rounds (s.gpr .x1) ∧
    (s.gpr .x3).toNat = 12 ∧ (s.gpr .x5).toNat ≤ 16

/-- `vg_aes_gcm_seal_store_powers`. -/
def sealStAArch64 : Contract isa where
  pre := sealStW
  post s s' := sealAArch64.post s s' ∧
    Spec.Gcm.Powers8Repr s'.mem (stackArg s 1) (Spec.Gcm.ctxH s.mem (s.gpr .x0))
  pub := onePub 3

/-! ## The call of `vg_ghash_store_powers` -/

/-- At the call, with memory changed since the entry only in the working
space and the text: `pw` is at `[sp + 8]`, writable, apart from the
accumulator, the working space of the call and the blocks it hashes, and the
hash subkey is the entry's. -/
theorem gsCall_of {σ s : State} {Y Dd S : Addr} {nb : Nat} (hs : sealStN σ)
    (sY : Region.Sub ⟨Y, 16⟩ (workR (stackArg σ 2))) (sS : Region.Sub ⟨S, 256⟩ (workR (stackArg σ 2)))
    (hrd : s.rd = σ.rd) (hwr : s.wr = σ.wr) (hsp : s.sp = σ.sp)
    (hf : Frame [workR (stackArg σ 2), ⟨σ.gpr .x6, (σ.gpr .x7).toNat⟩] σ.mem s.mem)
    (hd : Region.Sub ⟨Dd, 16 * nb⟩ ⟨σ.gpr .x6, (σ.gpr .x7).toNat⟩) :
    s.mem.readW (s.sp + BitVec.ofNat 64 8) 64 = stackArg σ 1 ∧
      InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 8) 8 ∧
      GhSCall s (σ.gpr .x0) Y Dd S (stackArg σ 1) nb ∧
      Spec.Gcm.blockAt s.mem (σ.gpr .x0 + BitVec.ofNat 64 240) = Spec.Gcm.ctxH σ.mem (σ.gpr .x0) := by
  obtain ⟨hpx, pd, pw, pc, pt, -, -⟩ := hs
  obtain ⟨ol, -, -, -⟩ := sealLay hpx
  have hwr₀ := hpx.2.1
  have hp' := hpx
  simp only [sealPreXW] at hp'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, dda, -⟩ := hp'
  have hspA := ol.hsp 1 (by decide)
  have sA : Region.Sub ⟨σ.sp + BitVec.ofNat 64 8, 8⟩ (args σ 3) := by
    show Region.Sub ⟨σ.sp + BitVec.ofNat 64 8, 8⟩ ⟨σ.sp + BitVec.ofNat 64 (8 * 0), 8 * 3⟩
    rw [show σ.sp + BitVec.ofNat 64 (8 * 0) = σ.sp by rw [Nat.mul_zero, BitVec.add_zero]]
    exact Offset.sub_base _ (by decide)
  refine ⟨?_, by rw [hrd, hwr, hsp]; exact hspA, ⟨?_, (pc.sub_right (Lay.ctxSub (d := 240) (n := 16)
    (by decide))).symm, (pw.sub_right sY).symm, (pd.sub_right hd).symm, (pw.sub_right sS).symm⟩, ?_⟩
  · rw [hsp, hf.readW (r := ⟨σ.sp + BitVec.ofNat 64 8, 8⟩) (Region.contains_self _ _) (fun r hr => by
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
theorem powers_keep {σ : State} (hs : sealStN σ) {H : Spec.Gcm.Block} {m m' : Mem}
    (h : Spec.Gcm.Powers8Repr m (stackArg σ 1) H)
    (hf : Frame [workR (stackArg σ 2), ⟨stackArg σ 0, 16⟩] m m') :
    Spec.Gcm.Powers8Repr m' (stackArg σ 1) H := by
  obtain ⟨-, -, pw, -, pt, -, -⟩ := hs
  exact Proof.AesGcm.powers8Repr_congr (fun i hi => hf.bytes (R := pwR σ) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact pw
      · exact pt) (show 128 ≤ 2 ^ 64 by decide) hi) h

/-! ## On the regions of the proofs -/

section
variable (v : GcmImpl) (g : GhashStoreImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey)
include hMK

omit hMK in
theorem pwCallS_keepsV : (Impl.AesGcm.AArch64.Fast.pwCall 8 g.fn).allInstrs keepsV = true := by
  simp only [Impl.AesGcm.AArch64.Fast.pwCall, Code.allInstrs, g.keepsV, Bool.and_true]
  decide

theorem sealSt_wp {s : State} (hs : sealStN s) :
    WP isa (Impl.AesGcm.AArch64.Fast.sealWithPw v.callees g.fn) s fun s' =>
      (GprAbi s s' ∧ sealAArch64.post s s') ∧
        Spec.Gcm.Powers8Repr s'.mem (stackArg s 1) (Spec.Gcm.ctxH s.mem (s.gpr .x0)) := by
  have hs' := hs
  obtain ⟨hpx, pd, pw, pc, -, h16, h12⟩ := hs'
  exact sealWithEX_wp (w := 2) v _ hMK (.inr rfl) (ex := [pwR s]) hpx ⟨h16, h12⟩
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact pw.symm)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact pd.symm)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact pc.symm)
    (fun hi hf => powers_keep hs hi hf)
    fun s' _ _ _ _ hc sY sS hrd hwr hsp hf hd =>
      have q := gsCall_of hs sY sS hrd hwr hsp hf hd
      WP.mono (pwS_call g (k := 8) (by decide) q.1 q.2.1 hc q.2.2.1) fun _ ⟨gp, pp⟩ =>
        ⟨gp, by rw [← q.2.2.2]; exact pp⟩

theorem sealSt_correctN (s : State) (hs : sealStN s) :
    ∃ t s', Exec isa (Impl.AesGcm.AArch64.Fast.sealWithPw v.callees g.fn) s t s' ∧ abiPreserved s s' ∧
      sealStAArch64.post s s' :=
  WP.withPreservedV (WP.mono (sealSt_wp v g hMK hs) fun _ ⟨⟨ga, p⟩, q⟩ => ⟨ga, p, q⟩)
    (fastSealWithE_keepsV v (.inr rfl) (pwCallS_keepsV g))

theorem sealSt_ctN :
    ConstantTime isa sealStN (onePub 3) (Impl.AesGcm.AArch64.Fast.sealWithPw v.callees g.fn) :=
  sealWithEX_ct (w := 2) v _ hMK (.inr rfl) (extra := fun _ => []) (extraW := fun s => [pwR s])
    (ex := fun s => [pwR s]) (fun _ h => h.1)
    (fun h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.2.2.1.symm)
    (fun h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.2.2.2.1.symm)
    (fun hq => by obtain ⟨-, -, -, -, -, -, -, -, -, qa⟩ := hq; simp only [pwR, qa 1 (by decide)])
    (fun p hc sY sS hrd hwr hsp hf hd =>
      have q := gsCall_of p sY sS hrd hwr hsp hf hd
      WP.mono (pwS_call g (k := 8) (by decide) q.1 q.2.1 hc q.2.2.1) fun _ q' => q'.1)
    fun {σ₁ σ₂ s₁ s₂ _ _ _ _} p₁ p₂ hq c₁ c₂ sY sS sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂ hd => by
      obtain ⟨q0, -, -, -, -, -, q6, q7, qsp, qa⟩ := hq
      have e2 : stackArg σ₁ 2 = stackArg σ₂ 2 := qa 2 (by decide)
      have e1 : stackArg σ₁ 1 = stackArg σ₂ 1 := qa 1 (by decide)
      obtain ⟨hP₁, hs₁, k₁, -⟩ := gsCall_of p₁ sY sS r₁ w₁ sp₁ f₁ hd
      obtain ⟨hP₂, hs₂, k₂, -⟩ := gsCall_of p₂ (by rw [← e2]; exact sY) (by rw [← e2]; exact sS) r₂ w₂
        (sp₂.trans qsp) (by rw [← e2, ← q6, ← q7]; exact f₂) (by rw [← q6, ← q7]; exact hd)
      rw [← e1] at hP₂ k₂
      rw [← q0] at k₂
      exact pwS_rel g (.inl rfl) hP₁ hs₁ hP₂ hs₂ c₁ k₁ c₂ k₂ (sp₁.trans sp₂.symm)

end

/-! ## On the shared contract's regions -/

/-- The writable regions of the proofs: `pw` after the working space. -/
def narrowWrS (s : State) : List Region :=
  [⟨s.gpr .x6, (s.gpr .x7).toNat⟩, ⟨stackArg s 0, 16⟩, ⟨stackArg s 2, 2560⟩, pwR s]

/-- `s` with the writable regions of the proofs. -/
def narrowS (s : State) : State := s.withRegions s.rd (narrowWrS s)

theorem narrowS_pre {s : State} (h : sealStW s) : sealStN (narrowS s) := by
  obtain ⟨hrd, -, cd, cw, nd, nw, ad, aw, dt, pd, dw, da, tw, pw, wa, pc, pt, b0, b2, b4, b6, b1, bsp, hr,
    h12, h16⟩ := h
  exact ⟨⟨by rw [show (narrowS s).rd = s.rd from rfl, hrd]; rfl, rfl, cd, cw, nd, nw, ad, aw, dt, dw, da, tw, wa,
    b0, b2, b4, b6, b1, bsp, hr⟩, pd, pw, pc, pt, h16, h12⟩

theorem narrowS_covers {s : State} (h : sealStW s) :
    Covers ((narrowS s).rd ++ (narrowS s).wr) (s.rd ++ s.wr) ∧ Covers (narrowS s).wr s.wr := by
  have w : Covers (narrowS s).wr s.wr := by
    rw [show (narrowS s).wr = narrowWrS s from rfl, h.2.1]
    refine Covers.of_mem fun r hr => ?_
    simp only [narrowWrS, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl <;> simp
  exact ⟨Covers.append (Covers.refl _) w, w⟩

theorem narrowS_exec {c : Prog isa} {s s₁ : State} {t : List Leak} (h : sealStW s)
    (he : Exec isa c (narrowS s) t s₁) : Exec isa c s t (s₁.withRegions s.rd s.wr) := by
  have := Exec.widen he (narrowS_covers h).1 (narrowS_covers h).2
  rwa [show (narrowS s).withRegions s.rd s.wr = s from rfl] at this

/-- A state satisfying `vg_aes_gcm_seal_store_powers`'s precondition:
`sealSat` with a 12-byte nonce, `pw` at `0x6000` (`[sp + 8]`) and `work` at
`0x5000` (`[sp + 16]`). -/
def sealSatSt : State :=
  { sealSat with
    gpr := fun r => match r with
      | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x2000 | .x3 => 12 | .x4 => 0x3000 | .x6 => 0x4000 | _ => 0
    mem := fun a => if a = 0x8011 then 0x50 else if a = 0x8009 then 0x60 else 0
    rd := [⟨0x1000, 256⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩, ⟨0x8000, 24⟩]
    wr := [⟨0x4000, 0⟩, ⟨0, 16⟩, ⟨0x6000, 128⟩, ⟨0x5000, 2560⟩] }

section
variable (v : GcmImpl) (g : GhashStoreImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey)
include hMK

theorem sealSt_correct (s : State) (hs : sealStAArch64.pre s) :
    ∃ t s', Exec isa (Impl.AesGcm.AArch64.Fast.sealWithPw v.callees g.fn) s t s' ∧ abiPreserved s s' ∧
      sealStAArch64.post s s' := by
  obtain ⟨t, s₁, he, ha, hp⟩ := sealSt_correctN v g hMK _ (narrowS_pre hs)
  exact ⟨t, _, narrowS_exec hs he, ha, hp⟩

theorem sealSt_ct :
    ConstantTime isa sealStAArch64.pre sealStAArch64.pub (Impl.AesGcm.AArch64.Fast.sealWithPw v.callees g.fn) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂
  obtain ⟨u₁, r₁, f₁, -⟩ := sealSt_correctN v g hMK _ (narrowS_pre h₁)
  obtain ⟨u₂, r₂, f₂, -⟩ := sealSt_correctN v g hMK _ (narrowS_pre h₂)
  rw [(Exec.det e₁ (narrowS_exec h₁ f₁)).1, (Exec.det e₂ (narrowS_exec h₂ f₂)).1]
  exact sealSt_ctN v g hMK _ _ _ _ _ _ (narrowS_pre h₁) (narrowS_pre h₂) hq f₁ f₂

theorem sealSt_verified :
    Verified AArch64.target (Impl.AesGcm.AArch64.Fast.sealWithPw v.callees g.fn)
      (Proof.AesGcm.sealStorePowersScratchContract AArch64.abi) :=
  Verified.of_correct (sealSt_correct v g hMK) (sealSt_ct v g hMK)
    { pre := by
        sig_implies_pre [Proof.AesGcm.sealStorePowersScratchContract, Proof.AesGcm.sealStorePowersScratchSig,
          Proof.AesGcm.sealStorePowersPreP, Spec.Gcm.sealPre, Spec.Gcm.storePowersOk,
          Spec.Gcm.sealStorePowersPost, Spec.Gcm.sealPost,
          sealStAArch64, sealStW, pwR, sealAArch64, onePub, args, rounds, AArch64.abi, AArch64.argRegs,
          AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      post := by
        intro s s' _ h
        sig_post [Proof.AesGcm.sealStorePowersScratchContract, Proof.AesGcm.sealStorePowersScratchSig,
          Proof.AesGcm.sealStorePowersPreP, Spec.Gcm.sealPre, Spec.Gcm.storePowersOk,
          Spec.Gcm.sealStorePowersPost, Spec.Gcm.sealPost,
          sealStAArch64, sealStW, pwR, sealAArch64, onePub, args, rounds, AArch64.abi, AArch64.argRegs,
          AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
        sig_reduce [sealStAArch64, sealAArch64, AArch64.stackArg, AArch64.stackArgAddr] at h
        sig_simp [sealStAArch64, sealAArch64, AArch64.stackArg, AArch64.stackArgAddr] [] at h
        exact ⟨fun _ => h.1, h.2⟩
      pub := by
        sig_implies_pub [Proof.AesGcm.sealStorePowersScratchContract, Proof.AesGcm.sealStorePowersScratchSig,
          Proof.AesGcm.sealStorePowersPreP, Spec.Gcm.sealPre, Spec.Gcm.storePowersOk,
          Spec.Gcm.sealStorePowersPost, Spec.Gcm.sealPost,
          sealStAArch64, sealStW, pwR, sealAArch64, onePub, args, rounds, AArch64.abi, AArch64.argRegs,
          AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      sat := ⟨sealSatSt, by
        sig_pre [Proof.AesGcm.sealStorePowersScratchContract, Proof.AesGcm.sealStorePowersScratchSig,
          Proof.AesGcm.sealStorePowersPreP, Spec.Gcm.sealPre, Spec.Gcm.storePowersOk, AArch64.abi,
          AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop,
          sealSatSt, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)⟩ }

end

/-! ## With its working space on the stack -/

/-- `sealSatSt` with its stack arguments `tag` and `pw` only. -/
def sealFrameSatSt : State :=
  { sealSatSt with rd := [⟨0x1000, 256⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩, ⟨0x8000, 16⟩],
                   wr := [⟨0x4000, 0⟩, ⟨0, 16⟩, ⟨0x6000, 128⟩] }

theorem sealFrameSatSt_pre : ∃ s, (Spec.Gcm.sealStorePowersContract AArch64.abi 2592).pre s := by
  refine ⟨sealFrameSatSt, ?_⟩
  sig_pre [Spec.Gcm.sealStorePowersContract, Spec.Gcm.sealStorePowersSig, Spec.Gcm.sealSig,
    Spec.Gcm.storePowersParam, Spec.Gcm.sealPre, Spec.Gcm.storePowersOk, Spec.Gcm.sealStorePowersPost,
    Spec.Gcm.sealPost, AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range,
    List.range.loop, List.cons_append, List.nil_append, sealFrameSatSt, sealSatSt, sealSat, stackArg, stackArgAddr,
    Mem.readW, Mem.read]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)

theorem sealSt_framed (v : GcmImpl) (g : GhashStoreImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackArgScratch 2592 2 (Impl.AesGcm.AArch64.Fast.sealWithPw v.callees g.fn))
      (Spec.Gcm.sealStorePowersContract AArch64.abi 2592) :=
  AArch64.Verified.stackArgScratch (sig := Spec.Gcm.sealStorePowersSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Proof.AesGcm.sealStorePowersPreP AArch64.abi.ptrBits)
    (post := Spec.Gcm.sealStorePowersPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 2592)
    (sealSt_verified v g hMK) (by decide) (by decide) (Proof.AesGcm.sealStorePowersPre_local _)
    (Proof.AesGcm.sealStorePowersPost_local _) sealFrameSatSt_pre

end VG.Proof.AesGcm.AArch64.Fast
