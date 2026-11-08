module

public import VerifiedGarbage.Proof.AesGcm.AArch64.OpenSplit.Run
public import VerifiedGarbage.Proof.AesGcm.AArch64.OpenSplit.Contract
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.OpenCT
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.SealPw
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Verified
import VerifiedGarbage.Proof.AesGcm.AArch64.OpenCT
import VerifiedGarbage.Proof.AesGcm.AArch64.SealCT
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
meta import VerifiedGarbage.Proof.AesGcm.AArch64.OpenSplit.Run
meta import VerifiedGarbage.Proof.AesGcm.AArch64.OpenSplit.Contract
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.OpenCT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.SealPw
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Verified
meta import VerifiedGarbage.Proof.AesGcm.AArch64.OpenCT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.SealCT
meta import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch

/-!
# AES-GCM on AArch64: `vg_aes_gcm_open_split_with_powers`, constant time and `Verified`

Untrusted: everything here is checked by Lean. Two runs from the same public
arguments take the same branches as long as their tags compare alike
(`openSp_ctN`): the entry and the pointer to `src`, loaded from the stack,
are public, and the rest is `open`'s path for TLS records out of place
(`openRunWithS_relX`). Then `Verified`, as `Stitch/OpenPw.lean` for
`vg_aes_gcm_open_with_powers`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64.OpenSplit

open VG VG.AArch64 VG.AArch64.Taint VG.Impl.AesGcm.AArch64
open VG.Proof.AesGcm.AArch64 VG.Proof.AesGcm.AArch64.Fast
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxH ctxCiph)
open VG.Proof.Gcm.AArch64.Pmull (MulKey)
open VG.Proof.Gcm.AArch64.Stitch (Gh8Ok)

/-- The table from `pw`, then the interleaved loop out of place, from the
registers it reads. -/
theorem pwRestDecTo_rel {u₁ u₂ : State} (hsp : u₁.sp = u₂.sp)
    (hr : ∀ r ∈ Reg.x5 :: Reg.x15 :: stRegs, u₁.gpr r = u₂.gpr r) :
    RelCT isa (Eq2 u₁ u₂) (.seq (.block pwRest) (Impl.Gcm.AArch64.Stitch.dec true)) TT :=
  rel_taint (.x5 :: .x15 :: stRegs) hsp hr ⟨_, by taint_decide⟩

/-- What it may leak: whether the tag is right. -/
def splitLeakOf (s : State) : List Nat :=
  if ¬rounds (s.gpr .x1) then [] else [if (splitRes s).isSome = true then 1 else 0]

section
variable (v : GcmImpl) (g : GhashWithImpl) (hMK : MulKey) (gh : Gh8Ok)
include hMK gh

theorem openSp_ctN :
    ConstantTime isa openSpN (fun s₁ s₂ => onePub 6 s₁ s₂ ∧ splitLeakOf s₁ = splitLeakOf s₂)
      (Impl.AesGcm.AArch64.Stitch.openSplitWithPw v.callees g.fn) := by
  refine ct_of fun σ₁ σ₂ p₁ p₂ hq => ?_
  have h₁ := p₁.1
  have h₂ := p₂.1
  obtain ⟨hq, hres⟩ := hq
  have hq₀ := hq
  have hR₁ : rounds (σ₁.gpr .x1) := (openLay h₁).1.rounds
  have hR₂ : rounds (σ₂.gpr .x1) := (openLay h₂).1.rounds
  obtain ⟨f₁, f₂⟩ := oneFacts (by decide : 5 < 6) (openCore h₁) (openCore h₂) hq
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp, qa⟩ := hq
  have qt : stackArg σ₁ 1 = stackArg σ₂ 1 := qa 1 (by decide)
  have qg : stackArg σ₁ 0 = stackArg σ₂ 0 := qa 0 (by decide)
  have e2 : stackArg σ₁ 2 = stackArg σ₂ 2 := qa 2 (by decide)
  have e3 : stackArg σ₁ 3 = stackArg σ₂ 3 := qa 3 (by decide)
  have e4 : stackArg σ₁ 4 = stackArg σ₂ 4 := qa 4 (by decide)
  have e5 : stackArg σ₁ 5 = stackArg σ₂ 5 := qa 5 (by decide)
  have hW₁ : σ₁.mem.readW (σ₁.sp + BitVec.ofNat 64 40) 64 = stackArg σ₁ 5 := rfl
  have hW₂ : σ₂.mem.readW (σ₂.sp + BitVec.ofNat 64 40) 64 = stackArg σ₁ 5 := f₂.hW
  have hk : 40 % 8 = 0 ∧ 40 < 32768 := by decide
  have hT₁ : σ₁.mem.readW (σ₁.sp + BitVec.ofNat 64 8) 64 = stackArg σ₁ 1 := rfl
  have hT₂ : σ₂.mem.readW (σ₂.sp + BitVec.ofNat 64 8) 64 = stackArg σ₁ 1 := qt.symm
  have t₁ : ∃ h, (taint.check (Taint.ofRegs []) (.block [.ldrSp .x12 0, .ldrSp .x6 24]) h).isSome = true :=
    ⟨_, by taint_decide⟩
  unfold Impl.AesGcm.AArch64.Stitch.openSplitWithPw
  refine rel_seq (RelCT.block_split (rel_seq (entryStash_rel (k := 40) (j := 8) (.inr (.inr (.inr rfl))) rfl
      (.inr rfl) f₁ f₂ (by decide) qsp (by agree_tac [q0, q1, q2, q3, q4, q5, q6, q7]))
      (entryStash_ok (V := stackArg σ₁ 1) hk (by decide) hW₁ (f₁.hsp 5 (by decide)) (f₁.hsp 1 (by decide))
        hT₁ (f₁.argW (by decide)) rfl f₁.perm)
      (entryStash_ok (V := stackArg σ₁ 1) hk (by decide) hW₂ (f₂.hsp 5 (by decide)) (f₂.hsp 1 (by decide))
        hT₂ (f₂.argW (by decide)) q0.symm f₂.perm)
      fun τ₁ τ₂ a₁ a₂ => rel_taint [] (by rw [a₁.1.sp, a₂.1.sp, qsp]) (by agree_tac []) t₁))
    (splitEntry_ok p₁) (splitEntry_ok p₂) fun s₁ s₂ ⟨o₁, x12₁, x6₁, k₁⟩ ⟨o₂, x12₂, x6₂, k₂⟩ => ?_
  -- The second run, in the first run's public values.
  rw [← e5, ← q0, ← q1, ← q2, ← q3, ← q4, ← q5, ← q6, ← q7, ← qsp, ← qt, ← qg] at o₂
  rw [← qg] at x12₂
  rw [← e3] at x6₂
  obtain ⟨-, -, -, -, sd, sw, -, h12, hal, h4n⟩ := id p₁
  have h4n₂ : (stackArg σ₂ 4).toNat = (σ₁.gpr .x7).toNat := by rw [← e4, h4n]
  have hb : (Spec.Gcm.openResult (ctxCiph σ₁.mem (σ₁.gpr .x0) (σ₁.gpr .x1).toNat) (ctxH σ₁.mem (σ₁.gpr .x0))
        (stackArg σ₁ 1).toNat (bytesAt σ₁.mem (σ₁.gpr .x2) (σ₁.gpr .x3).toNat)
        (bytesAt σ₁.mem (stackArg σ₁ 3) (σ₁.gpr .x7).toNat) (bytesAt σ₁.mem (σ₁.gpr .x4) (σ₁.gpr .x5).toNat)
        (bytesAt σ₁.mem (stackArg σ₁ 0) (stackArg σ₁ 1).toNat)).isSome =
      (Spec.Gcm.openResult (ctxCiph σ₂.mem (σ₁.gpr .x0) (σ₁.gpr .x1).toNat) (ctxH σ₂.mem (σ₁.gpr .x0))
        (stackArg σ₁ 1).toNat (bytesAt σ₂.mem (σ₁.gpr .x2) (σ₁.gpr .x3).toNat)
        (bytesAt σ₂.mem (stackArg σ₁ 3) (σ₁.gpr .x7).toNat) (bytesAt σ₂.mem (σ₁.gpr .x4) (σ₁.gpr .x5).toNat)
        (bytesAt σ₂.mem (stackArg σ₁ 0) (stackArg σ₁ 1).toNat)).isSome := by
    have hb' : (splitRes σ₁).isSome = (splitRes σ₂).isSome := by
      rw [splitLeakOf, splitLeakOf, ite_eq_right_of_eq_false _ _ (eq_false (not_not_intro hR₁)),
        ite_eq_right_of_eq_false _ _ (eq_false (not_not_intro hR₂))] at hres
      revert hres; cases (splitRes σ₁).isSome <;> cases (splitRes σ₂).isSome <;> simp
    unfold splitRes at hb'
    rw [h4n, h4n₂, ← q0, ← q1, ← q2, ← q3, ← q4, ← q5, ← qt, ← qg, ← e3] at hb'
    exact hb'
  -- The registers `open`'s path reads.
  have regs : ∀ {σ u t : State}, (∀ r ∈ [Reg.x4, .x5, .x7], u.gpr r = σ.gpr r) → u.gpr .x6 = stackArg σ₁ 3 →
      (∀ r ∈ [Reg.x4, .x5, .x6, .x7], t.gpr r = u.gpr r) → σ.gpr .x4 = σ₁.gpr .x4 → σ.gpr .x5 = σ₁.gpr .x5 →
      σ.gpr .x7 = σ₁.gpr .x7 →
      t.gpr .x4 = σ₁.gpr .x4 ∧ t.gpr .x5 = BitVec.ofNat 64 (σ₁.gpr .x5).toNat ∧ t.gpr .x6 = stackArg σ₁ 3 ∧
        t.gpr .x7 = BitVec.ofNat 64 (σ₁.gpr .x7).toNat := fun ku k6 kt a4 a5 a7 =>
    ⟨by rw [kt _ (by simp), ku _ (by simp), a4], by rw [kt _ (by simp), ku _ (by simp), a5, ofNat_toNat'],
      by rw [kt _ (by simp), k6], by rw [kt _ (by simp), ku _ (by simp), a7, ofNat_toNat']⟩
  -- The call of `vg_ghash_with_powers` and the table, in each run.
  have hgh₁ : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat},
      GhCall s' (σ₁.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR (stackArg σ₁ 5)) → Region.Sub ⟨S, 256⟩ (workR (stackArg σ₁ 5)) →
      s'.rd = σ₁.rd → s'.wr = σ₁.wr → s'.sp = σ₁.sp →
      Frame [workR (stackArg σ₁ 5), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ₁.mem s'.mem →
      Region.Sub ⟨Dd, 16 * nb⟩ (⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩ : Region) →
      WP isa (Impl.AesGcm.AArch64.Fast.pwSel v.callees 16 g.fn) s' fun u =>
        GhPost s' (σ₁.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb u [] :=
    fun s' _ _ _ _ hc sY sS hrd hwr hsp hf _ =>
      have q := gwCallS_of p₁ sY sS hrd hwr hsp hf
      pwSel_call v g (k := 16) (by decide) q.1 q.2.1 hc q.2.2
  have hgh₂ : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat},
      GhCall s' (σ₁.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR (stackArg σ₁ 5)) → Region.Sub ⟨S, 256⟩ (workR (stackArg σ₁ 5)) →
      s'.rd = σ₂.rd → s'.wr = σ₂.wr → s'.sp = σ₁.sp →
      Frame [workR (stackArg σ₁ 5), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ₂.mem s'.mem →
      Region.Sub ⟨Dd, 16 * nb⟩ (⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩ : Region) →
      WP isa (Impl.AesGcm.AArch64.Fast.pwSel v.callees 16 g.fn) s' fun u =>
        GhPost s' (σ₁.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb u [] :=
    fun s' _ _ _ _ hc sY sS hrd hwr hsp hf _ => by
      obtain ⟨hP, hsl, k⟩ := gwCallS_of p₂ (by rw [← e5]; exact sY) (by rw [← e5]; exact sS) hrd hwr
        (hsp.trans qsp) (by rw [← e5, ← q6, ← q7]; exact hf)
      rw [← e2, ← q0] at k
      rw [← e2] at hP
      exact pwSel_call v g (k := 16) (by decide) hP hsl hc k
  have htb₁ := (pwTbl_forS p₁).tbFor
  have htb₂ := (pwTbl_forS p₂).tbFor
  rw [← q0, ← e5, ← q6, ← q7, ← qsp] at htb₂
  unfold Impl.AesGcm.AArch64.Stitch.openFastS
  refine openRestWithG_rel (w := 5) (F₁ := fun _ => True) (F₂ := fun _ => True)
    (C₁ := bytesAt σ₁.mem (stackArg σ₁ 3) (σ₁.gpr .x7).toNat)
    (C₂ := bytesAt σ₂.mem (stackArg σ₁ 3) (σ₁.gpr .x7).toNat) o₁ o₂ x12₁ x12₂ trivial trivial
    (fun {t} o' hT hok hx => ?_) (fun {t} o' hT hok hx => ?_) fun {t₁ t₂} o₁' o₂' rt₁ rt₂ hok hx₁ hx₂ => ?_
  · obtain ⟨hsrc, hS⟩ := srcFacts p₁ o' rfl rfl
    have e := regs k₁ x6₁ hx rfl rfl rfl
    exact WP.mono (openRunWithS_postXT v _ hMK gh («to» := true) (ex := []) (I := fun _ => True) o' h12
      e.1 e.2.1 e.2.2.1 e.2.2.2 hal hT hok hsrc sw sd hS (by simp) (by simp) (by simp) (fun _ _ => trivial)
      (fun s' _ _ _ _ hc sY sS hrd hwr hsp hf hd =>
        WP.mono (hgh₁ s' hc sY sS hrd hwr hsp hf hd) fun _ g => ⟨g, trivial⟩) htb₁)
      fun _ q => OpenPostG.true q.1
  · obtain ⟨hsrc, hS⟩ := srcFacts p₂ o' e5 (by rw [q7])
    rw [← e3] at hsrc hS
    have e := regs k₂ x6₂ hx q4.symm q5.symm q7.symm
    exact WP.mono (openRunWithS_postXT v _ hMK gh («to» := true) (ex := []) (I := fun _ => True) o' h12
      e.1 e.2.1 e.2.2.1 e.2.2.2 hal hT hok hsrc sw sd hS (by simp) (by simp) (by simp) (fun _ _ => trivial)
      (fun s' _ _ _ _ hc sY sS hrd hwr hsp hf hd =>
        WP.mono (hgh₂ s' hc sY sS hrd hwr hsp hf hd) fun _ g => ⟨g, trivial⟩) htb₂)
      fun _ q => OpenPostG.true q.1
  · obtain ⟨hsrc₁, hS₁⟩ := srcFacts p₁ o₁' rfl rfl
    obtain ⟨hsrc₂, hS₂⟩ := srcFacts p₂ o₂' e5 (by rw [q7])
    rw [← e3] at hsrc₂ hS₂
    exact openRunWithS_relX v _ hMK gh («to» := true) (S := stackArg σ₁ 3) (ex := []) (by simp) (by simp)
      (by simp) o₁' o₂' h12 (regs k₁ x6₁ hx₁ rfl rfl rfl) (regs k₂ x6₂ hx₂ q4.symm q5.symm q7.symm) hal rt₁ rt₂
      hok hsrc₁ hsrc₂ sw sd hS₁ hS₂ hb hgh₁ hgh₂
      (fun {s₁ s₂ _ _ _ _} c₁ c₂ sY sS sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂ _ => by
        obtain ⟨hP₁, hs₁, k₁⟩ := gwCallS_of p₁ sY sS r₁ w₁ sp₁ f₁
        obtain ⟨hP₂, hs₂, k₂⟩ := gwCallS_of p₂ (by rw [← e5]; exact sY) (by rw [← e5]; exact sS) r₂ w₂
          (sp₂.trans qsp) (by rw [← e5, ← q6, ← q7]; exact f₂)
        rw [← e2] at hP₂ k₂
        rw [← q0] at k₂
        exact pwSel_rel v g (.inr (.inl rfl)) hP₁ hs₁ hP₂ hs₂ c₁ k₁ c₂ k₂ (sp₁.trans sp₂.symm))
      htb₁ htb₂
      fun v₁ v₂ sp₁ sp₂ hr h15 r₁ w₁ f₁ r₂ w₂ f₂ => by
        obtain ⟨hP₁, hs₁, -⟩ := gwCallS_of p₁ (Y := stackArg σ₁ 5 + BitVec.ofNat 64 512)
          (S := stackArg σ₁ 5 + BitVec.ofNat 64 512) (Lay.wSub (by decide)) (Lay.wSub (by decide)) r₁ w₁ sp₁ f₁
        obtain ⟨hP₂, hs₂, -⟩ := gwCallS_of p₂ (Y := stackArg σ₂ 5 + BitVec.ofNat 64 512)
          (S := stackArg σ₂ 5 + BitVec.ofNat 64 512) (Lay.wSub (by decide)) (Lay.wSub (by decide)) r₂ w₂
          (sp₂.trans qsp) (by rw [← e5, ← q6, ← q7]; exact f₂)
        rw [← e2] at hP₂
        exact pwTbl_relR (.x15 :: stRegs) (.inr rfl) (fun hsp hr => pwRestDecTo_rel hsp hr)
          (sp₁.trans sp₂.symm) (fun r hr' => by
            rcases List.mem_cons.mp hr' with rfl | hr'
            · exact h15 rfl
            · exact hr r hr') hP₁ hs₁ hP₂ hs₂

end

/-! ## On the contract's regions -/

/-- The source, the stack argument 3, of `src_len` bytes. -/
abbrev srcLR (s : State) : Region := ⟨stackArg s 3, (stackArg s 4).toNat⟩

/-- What `vg_aes_gcm_open_split_with_powers` needs, as its contract says:
`pw` and `src` readable before the stack arguments, `pw` holding the powers,
`src_len` equal to `len`, a 12-byte nonce and at most 16 bytes of additional
data. -/
def openSpW (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .x0, 256⟩
  let nonce : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  let aad : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
  let data : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
  let tag : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
  let pw : Region := pwRO s
  let src : Region := srcLR s
  let work : Region := ⟨stackArg s 5, 2560⟩
  s.rd = [ctx, nonce, aad, tag, pw, src, args s 6] ∧ s.wr = [data, work] ∧
    ctx.Disjoint data ∧ ctx.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧ pw.Disjoint data ∧ src.Disjoint data ∧
    data.Disjoint work ∧ data.Disjoint (args s 6) ∧ tag.Disjoint work ∧ pw.Disjoint work ∧ src.Disjoint work ∧
    work.Disjoint (args s 6) ∧
    (s.gpr .x0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64 ∧
    (stackArg s 3).toNat + (stackArg s 4).toNat ≤ 2 ^ 64 ∧
    (stackArg s 5).toNat + 2560 ≤ 2 ^ 64 ∧ s.sp.toNat + 8 * 6 ≤ 2 ^ 64 ∧ rounds (s.gpr .x1) ∧
    Spec.Gcm.Powers8Repr s.mem (stackArg s 2) (ctxH s.mem (s.gpr .x0)) ∧
    (stackArg s 4).toNat = (s.gpr .x7).toNat ∧ (s.gpr .x3).toNat = 12 ∧ (s.gpr .x5).toNat ≤ 16

/-- `vg_aes_gcm_open_split_with_powers`. -/
def openSpAArch64 : Contract isa where
  pre := openSpW
  post := splitPost
  pub s₁ s₂ := onePub 6 s₁ s₂ ∧ splitLeakOf s₁ = splitLeakOf s₂

/-- The readable regions of the proofs: `pw` and `src` after the stack arguments. -/
def narrowRdS (s : State) : List Region :=
  [⟨s.gpr .x0, 256⟩, ⟨s.gpr .x2, (s.gpr .x3).toNat⟩, ⟨s.gpr .x4, (s.gpr .x5).toNat⟩,
    ⟨stackArg s 0, (stackArg s 1).toNat⟩, args s 6, pwRO s, srcR s]

/-- `s` with the readable regions of the proofs. -/
def narrowS (s : State) : State := s.withRegions (narrowRdS s) s.wr

theorem narrowS_pre {s : State} (h : openSpW s) : openSpN (narrowS s) := by
  obtain ⟨-, hwr, cd, cw, nd, nw, ad, aw, pd, sd, dw, da, tw, pw, sw, wa, b0, b2, b4, b6, b3, b1, bsp, hr, rep,
    h4n, h12, hal⟩ := h
  have e : srcLR s = srcR s := by simp only [srcLR, srcR, h4n]
  rw [e] at sd sw
  exact ⟨⟨rfl, hwr, cd, cw, nd, nw, ad, aw, dw, da, tw, wa, b0, b2, b4, b6, b1, bsp, hr⟩, pd, pw, rep, sd, sw,
    by have := b3; rw [h4n] at this; exact this, h12, hal, h4n⟩

theorem narrowS_covers {s : State} (h : openSpW s) :
    Covers ((narrowS s).rd ++ (narrowS s).wr) (s.rd ++ s.wr) := by
  have e : srcR s = srcLR s := by simp only [srcLR, srcR, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  rw [show (narrowS s).rd = narrowRdS s from rfl, show (narrowS s).wr = s.wr from rfl, h.1]
  refine Covers.append (Covers.of_mem fun r hr => ?_) (Covers.refl _)
  simp only [narrowRdS, e, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem narrowS_exec {c : Prog isa} {s s₁ : State} {t : List Leak} (h : openSpW s)
    (he : Exec isa c (narrowS s) t s₁) : Exec isa c s t (s₁.withRegions s.rd s.wr) := by
  have := Exec.widen he (narrowS_covers h) (Covers.refl _)
  rwa [show (narrowS s).withRegions s.rd s.wr = s from rfl] at this

/-- A state satisfying the precondition: a 12-byte nonce at `0x2000`, `pw` at
`0x6000` (`[sp + 16]`), `src` at `0x7000` (`[sp + 24]`) and `work` at
`0x5000` (`[sp + 40]`). -/
def splitSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x2000 | .x3 => 12 | .x4 => 0x3000 | .x6 => 0x4000 | _ => 0
  sp := 0x8000
  mem a := if a = 0x8029 then 0x50 else if a = 0x8019 then 0x70 else if a = 0x8011 then 0x60 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩, ⟨0, 0⟩, ⟨0x6000, 128⟩, ⟨0x7000, 0⟩, ⟨0x8000, 48⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x5000, 2560⟩]

/-- `pw`'s bytes in `splitSat` are zero. -/
theorem splitSat_zero : ∀ i < 16 * 8, splitSat.mem (stackArg splitSat 2 + BitVec.ofNat 64 i) = 0 := by
  intro i hi
  have hP : stackArg splitSat 2 = 0x6000 := by decide
  rw [hP]
  show (if (0x6000 : BitVec 64) + BitVec.ofNat 64 i = 0x8029 then 0x50
    else if (0x6000 : BitVec 64) + BitVec.ofNat 64 i = 0x8019 then 0x70
    else if (0x6000 : BitVec 64) + BitVec.ofNat 64 i = 0x8011 then 0x60 else 0) = 0
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by bv_omega)), ite_eq_right_of_eq_false _ _ (eq_false (by bv_omega)),
    ite_eq_right_of_eq_false _ _ (eq_false (by bv_omega))]

section
variable (v : GcmImpl) (g : GhashWithImpl) (hMK : MulKey) (gh : Gh8Ok)
include hMK gh

theorem openSp_correctN (s : State) (hs : openSpN s) :
    ∃ t s', Exec isa (Impl.AesGcm.AArch64.Stitch.openSplitWithPw v.callees g.fn) s t s' ∧ abiPreserved s s' ∧
      splitPost s s' :=
  WP.withPreservedV (openSp_wp v g hMK gh s hs) (stitchOpenSplit_keepsV v (pwSel_keepsV v g (.inr (.inl rfl))))

theorem openSp_correct (s : State) (hs : openSpAArch64.pre s) :
    ∃ t s', Exec isa (Impl.AesGcm.AArch64.Stitch.openSplitWithPw v.callees g.fn) s t s' ∧ abiPreserved s s' ∧
      openSpAArch64.post s s' := by
  obtain ⟨t, s₁, he, ha, hp⟩ := openSp_correctN v g hMK gh _ (narrowS_pre hs)
  exact ⟨t, _, narrowS_exec hs he, ha, hp⟩

theorem openSp_ct :
    ConstantTime isa openSpAArch64.pre openSpAArch64.pub
      (Impl.AesGcm.AArch64.Stitch.openSplitWithPw v.callees g.fn) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂
  obtain ⟨u₁, r₁, f₁, -⟩ := openSp_correctN v g hMK gh _ (narrowS_pre h₁)
  obtain ⟨u₂, r₂, f₂, -⟩ := openSp_correctN v g hMK gh _ (narrowS_pre h₂)
  rw [(Exec.det e₁ (narrowS_exec h₁ f₁)).1, (Exec.det e₂ (narrowS_exec h₂ f₂)).1]
  exact openSp_ctN v g hMK gh _ _ _ _ _ _ (narrowS_pre h₁) (narrowS_pre h₂) hq f₁ f₂

theorem openSp_verified :
    Verified AArch64.target (Impl.AesGcm.AArch64.Stitch.openSplitWithPw v.callees g.fn)
      (OpenSplit.scratchContract AArch64.abi) :=
  Verified.of_correct (openSp_correct v g hMK gh) (openSp_ct v g hMK gh)
    { pre := by
        sig_implies_pre [OpenSplit.scratchContract, OpenSplit.scratchSig, OpenSplit.pre, OpenSplit.post, OpenSplit.leak,
          openSpAArch64, openSpW, pwRO, srcLR, splitPost, splitRes, splitLeakOf, onePub, args, rounds, AArch64.abi,
          AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      post := by
        sig_implies_post [OpenSplit.scratchContract, OpenSplit.scratchSig, OpenSplit.pre, OpenSplit.post, OpenSplit.leak,
          openSpAArch64, openSpW, pwRO, srcLR, splitPost, splitRes, splitLeakOf, onePub, args, rounds, AArch64.abi,
          AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      pub := by
        sig_implies_pub [OpenSplit.scratchContract, OpenSplit.scratchSig, OpenSplit.pre, OpenSplit.post, OpenSplit.leak,
          openSpAArch64, openSpW, pwRO, srcLR, splitPost, splitRes, splitLeakOf, onePub, args, rounds, AArch64.abi,
          AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      sat := ⟨splitSat, by
        sig_pre [OpenSplit.scratchContract, OpenSplit.scratchSig, OpenSplit.pre, AArch64.abi, AArch64.argRegs,
          AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop, splitSat,
          stackArg, stackArgAddr, Mem.readW, Mem.read]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | exact Proof.AesGcm.powers8Repr_of_zeroMem (by decide) splitSat_zero⟩ }

end

/-! ## With its working space on the stack -/

/-- `splitSat` with its stack arguments `tag`, `tag_len`, `pw`, `src` and `src_len` only. -/
def splitFrameSat : State :=
  { splitSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩, ⟨0, 0⟩, ⟨0x6000, 128⟩, ⟨0x7000, 0⟩, ⟨0x8000, 40⟩],
                  wr := [⟨0x4000, 0⟩] }

theorem splitFrameSat_pre : ∃ s, (OpenSplit.contract AArch64.abi 2608).pre s := by
  refine ⟨splitFrameSat, ?_⟩
  sig_pre [OpenSplit.contract, OpenSplit.sig, OpenSplit.pre, OpenSplit.post, OpenSplit.leak, AArch64.abi,
    AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop,
    List.cons_append, List.nil_append, splitFrameSat, splitSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Proof.AesGcm.powers8Repr_of_zeroMem (by decide) splitSat_zero

/-- `vg_aes_gcm_open_split_with_powers`, its working space on the stack. -/
theorem openSp_framed (v : GcmImpl) (g : GhashWithImpl) (hMK : MulKey) (gh : Gh8Ok) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackArgScratch 2608 5
        (Impl.AesGcm.AArch64.Stitch.openSplitWithPw v.callees g.fn))
      (OpenSplit.contract AArch64.abi 2608) :=
  AArch64.Verified.stackArgScratch (sig := OpenSplit.sig) (nm := "work") (e := .u64)
    (n := 320) (pre := OpenSplit.pre AArch64.abi.ptrBits) (post := OpenSplit.post AArch64.abi.ptrBits) (wa := true)
    (stack := 0) (bytes := 2608) (leak := some (OpenSplit.leak AArch64.abi.ptrBits))
    (openSp_verified v g hMK gh) (by decide) (by decide) (pre_local _) (post_local _) splitFrameSat_pre
    (hleak := leak_local _)

end VG.Proof.AesGcm.AArch64.OpenSplit
