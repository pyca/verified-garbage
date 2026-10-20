module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.CT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.CT
import VerifiedGarbage.Proof.AesGcm.AArch64.Env
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Mul
import VerifiedGarbage.Proof.AesGcm.AArch64.Fn
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Seal
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Entry
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.ShortCopy

/-!
# AES-GCM on AArch64, short records: `sealShort` is constant time

Untrusted: everything here is checked by Lean. `sealShort` keeps every length
and pointer it uses after the table in registers (`shortLen`), which both runs
agree on: so its head (`J₀`, the first counter block and `shortLen`) is
checked by the taint analysis, and the table with everything after it
(`shortRestZ`) by the caller's `tb` (`sealShort_rel`), which for `pwTbl` is
the taint analysis too. `sealWithShX_ct`: `sealWithS` with the short path, as
`sealWithSX_ct`, the lengths that choose the path being public.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64.Fast

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Taint VG.Impl.AesGcm.AArch64
open VG.Proof.AesGcm.AArch64
open VG.Proof.Gcm.AArch64.Pmull
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)
open VG.Proof.Gcm.AArch64.Stitch (Gh8Ok)

theorem RelCT.assoc' {P Q : State → State → Prop} {a b c : Prog isa}
    (h : RelCT isa P (.seq a (.seq b c)) Q) : RelCT isa P (.seq (.seq a b) c) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq e₁ c₁ =>
    cases e₁ with
    | seq a₁ b₁ =>
      cases e₂ with
      | seq e₂ c₂ =>
        cases e₂ with
        | seq a₂ b₂ =>
          obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq a₁ (.seq b₁ c₁)) (.seq a₂ (.seq b₂ c₂))
          simp only [List.append_assoc] at ht ⊢
          exact ⟨ht, hq⟩

/-- The registers `sealShort` reads after the table, which both runs agree on. -/
abbrev shRegs : List Reg := [.x4, .x19, .x20, .x21, .x22, .x24, .x25, .x26, .x27, .x28]

/-- `sealShort` after `zeroBufs`. -/
abbrev shortRest : Prog isa :=
  .seq Stitch.textIn
  (.seq (.block Stitch.shortCtr)
  (.seq (Impl.Gcm.AArch64.Stitch.byRounds Stitch.shortAes)
  (.seq Stitch.textOut
  (.seq Stitch.aadIn
    (.block (Stitch.lensB ++ Stitch.shortGh ++ Stitch.shortTag ++ restore))))))

/-- `sealShort` after the table. -/
abbrev shortRestZ : Prog isa := .seq (.block Stitch.zeroBufs) shortRest

section
variable {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W)
include L

/-- `J₀`, the first counter block and `shortLen`. -/
theorem shortHead_ok {k : Reg → BitVec 64} {H : Block} {Np A D : Addr} {al n : Nat} {s : State}
    (hJ : J0In Ctx (W + BitVec.ofNat 64 16) W SP k H Np 12 s) (h4 : s.gpr .x4 = A)
    (h5 : s.gpr .x5 = BitVec.ofNat 64 al) (h6 : s.gpr .x6 = D) (h7 : s.gpr .x7 = BitVec.ofNat 64 n)
    (hn : n < 2 ^ 60) :
    WP isa (.block (j012 ++ initState ++ Stitch.shortLen)) s fun t =>
      Env Ctx (W + BitVec.ofNat 64 16) W SP t ∧ t.gpr .x4 = A ∧ t.gpr .x24 = BitVec.ofNat 64 al ∧
      t.gpr .x25 = BitVec.ofNat 64 (16 * ((n + 15) / 16)) ∧ t.gpr .x26 = BitVec.ofNat 64 n ∧ t.gpr .x27 = D ∧
      t.gpr .x22 = s.gpr .x22 ∧ t.gpr .x28 = s.gpr .x28 ∧ Frame (j0Frame (W + BitVec.ofNat 64 16) W) s.mem t.mem ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.with_rdwr (WP.block_and (j012_ok L hJ) (j012_others hJ))) fun s₂ ⟨⟨h₂, o₂⟩, rd₂, wr₂⟩ => ?_
  refine WP.mono (WP.with_rdwr (WP.block_and (initState_ok L h₂) (initState_others h₂.env)))
    fun s₃ ⟨⟨h₃, o₃⟩, rd₃, wr₃⟩ => ?_
  have o : ∀ r ∉ [Reg.x9, .x10, .x11, .x12], s₃.gpr r = s.gpr r := fun r hr => by rw [o₃ r hr, o₂ r hr]
  refine WP.mono (Stitch.shortLen_ok (D := D) (al := al) s₃ (by rw [o _ (by decide), h7]) (by rw [o _ (by decide), h6])
    (by rw [o _ (by decide), h5]) hn) fun t ⟨x26, x27, x24, x25, g, m, _, sp, rd, wr⟩ => ?_
  refine ⟨h₃.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact g _ (by decide) (by decide) (by decide) (by decide)) sp rd wr,
    by rw [g _ (by decide) (by decide) (by decide) (by decide), o _ (by decide), h4], x24, x25, x26, x27,
    by rw [g _ (by decide) (by decide) (by decide) (by decide), o _ (by decide)],
    by rw [g _ (by decide) (by decide) (by decide) (by decide), o _ (by decide)], by rw [m]; exact h₃.frame,
    by rw [rd, rd₃, rd₂], by rw [wr, wr₃, wr₂]⟩

/-- `sealShort`, in two runs from the entry of `seal` that agree on the
arguments, given its table and what follows in two runs that agree on
`shRegs`. -/
theorem sealShort_rel {tb : List Instr} {k₁ k₂ : Reg → BitVec 64} {H₁ H₂ : Block} {Np A D : Addr} {al n : Nat}
    {ρ₁ ρ₂ σ₁ σ₂ : State}
    (hJ₁ : J0In Ctx (W + BitVec.ofNat 64 16) W SP k₁ H₁ Np 12 σ₁)
    (hJ₂ : J0In Ctx (W + BitVec.ofNat 64 16) W SP k₂ H₂ Np 12 σ₂)
    (hx₁ : σ₁.gpr .x4 = A ∧ σ₁.gpr .x5 = BitVec.ofNat 64 al ∧ σ₁.gpr .x6 = D ∧ σ₁.gpr .x7 = BitVec.ofNat 64 n)
    (hx₂ : σ₂.gpr .x4 = A ∧ σ₂.gpr .x5 = BitVec.ofNat 64 al ∧ σ₂.gpr .x6 = D ∧ σ₂.gpr .x7 = BitVec.ofNat 64 n)
    (hn : n < 2 ^ 60) (h22 : σ₁.gpr .x22 = σ₂.gpr .x22) (h28 : σ₁.gpr .x28 = σ₂.gpr .x28)
    (hf₁ : Frame [workR W, ⟨D, n⟩] ρ₁.mem σ₁.mem) (hrd₁ : σ₁.rd = ρ₁.rd) (hwr₁ : σ₁.wr = ρ₁.wr)
    (hf₂ : Frame [workR W, ⟨D, n⟩] ρ₂.mem σ₂.mem) (hrd₂ : σ₂.rd = ρ₂.rd) (hwr₂ : σ₂.wr = ρ₂.wr)
    (htbrel : ∀ v₁ v₂ : State, v₁.sp = SP → v₂.sp = SP → (∀ r ∈ shRegs, v₁.gpr r = v₂.gpr r) →
      v₁.rd = ρ₁.rd → v₁.wr = ρ₁.wr → Frame [workR W, ⟨D, n⟩] ρ₁.mem v₁.mem →
      v₂.rd = ρ₂.rd → v₂.wr = ρ₂.wr → Frame [workR W, ⟨D, n⟩] ρ₂.mem v₂.mem →
      RelCT isa (Eq2 v₁ v₂) (.seq (.block tb) shortRestZ) TT) :
    RelCT isa (Eq2 σ₁ σ₂) (Impl.AesGcm.AArch64.Stitch.sealShort tb) TT := by
  obtain ⟨x4₁, x5₁, x6₁, x7₁⟩ := hx₁
  obtain ⟨x4₂, x5₂, x6₂, x7₂⟩ := hx₂
  have j0W : ∀ r ∈ j0Frame (W + BitVec.ofNat 64 16) W, ∃ r' ∈ [workR W, (⟨D, n⟩ : Region)], Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  unfold Impl.AesGcm.AArch64.Stitch.sealShort Impl.AesGcm.AArch64.Stitch.shortPre
  refine RelCT.assoc' (rel_seq (rel_taint [.x4, .x5, .x6, .x7, .x19, .x20, .x21, .x23]
      (by rw [hJ₁.env.sp, hJ₂.env.sp])
      (by agree_tac [x4₁, x4₂, x5₁, x5₂, x6₁, x6₂, x7₁, x7₂, hJ₁.env.x19, hJ₂.env.x19, hJ₁.env.x20, hJ₂.env.x20,
        hJ₁.env.x21, hJ₂.env.x21, hJ₁.x23, hJ₂.x23]) ⟨_, by taint_decide⟩)
    (shortHead_ok L hJ₁ x4₁ x5₁ x6₁ x7₁ hn) (shortHead_ok L hJ₂ x4₂ x5₂ x6₂ x7₂ hn)
    fun τ₁ τ₂ ⟨e₁, a₁, l₁, c₁, n₁, d₁, r₁, t₁, f₁, rd₁, wr₁⟩ ⟨e₂, a₂, l₂, c₂, n₂, d₂, r₂, t₂, f₂, rd₂, wr₂⟩ => ?_)
  refine RelCT.assoc' (htbrel τ₁ τ₂ e₁.sp e₂.sp (fun r hr => ?_) (by rw [rd₁, hrd₁]) (by rw [wr₁, hwr₁])
    (hf₁.trans (f₁.sub j0W)) (by rw [rd₂, hrd₂]) (by rw [wr₂, hwr₂]) (hf₂.trans (f₂.sub j0W)))
  simp only [shRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a₁, a₂]
  · rw [e₁.x19, e₂.x19]
  · rw [e₁.x20, e₂.x20]
  · rw [e₁.x21, e₂.x21]
  · rw [r₁, r₂, h22]
  · rw [l₁, l₂]
  · rw [c₁, c₂]
  · rw [n₁, n₂]
  · rw [d₁, d₂]
  · rw [t₁, t₂, h28]

end

/-- `seal` with the path for TLS records, its whole blocks hashed by `gh`, is
constant time, for a `gh` that hashes as `vg_ghash` and leaks the same in two
runs, called with memory changed since the entry only in the working space and
the text. -/
theorem sealWithShX_ct (v : GcmImpl) (cl : Prog isa) (hMK : MulKey) (gh : Gh8Ok) {tb : List Instr} {w : Nat}
    (hw : w = 1 ∨ w = 2)
    {extra extraW : State → List Region} {pre : State → Prop}
    (hpre : ∀ s, pre s → sealPreXW w (extra s) s (extraW s))
    {ex : State → List Region}
    (hexW : ∀ {σ : State}, pre σ → ∀ r ∈ ex σ, (workR (stackArg σ w)).Disjoint r)
    (hexC : ∀ {σ : State}, pre σ → ∀ r ∈ ex σ, (⟨σ.gpr .x0, 256⟩ : Region).Disjoint r)
    (hexq : ∀ {σ₁ σ₂ : State}, onePub (w + 1) σ₁ σ₂ → ex σ₂ = ex σ₁)
    (hgh : ∀ {σ s : State} {Y Dd S : Addr} {nb : Nat}, pre σ →
      GhCall s (σ.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR (stackArg σ w)) → Region.Sub ⟨S, 256⟩ (workR (stackArg σ w)) →
      s.rd = σ.rd → s.wr = σ.wr → s.sp = σ.sp →
      Frame [workR (stackArg σ w), ⟨σ.gpr .x6, (σ.gpr .x7).toNat⟩] σ.mem s.mem →
      Region.Sub ⟨Dd, 16 * nb⟩ (⟨σ.gpr .x6, (σ.gpr .x7).toNat⟩ : Region) →
      WP isa cl s fun u => GhPost s (σ.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb u (ex σ))
    (hrel : ∀ {σ₁ σ₂ s₁ s₂ : State} {Y Dd S : Addr} {nb : Nat}, pre σ₁ → pre σ₂ → onePub (w + 1) σ₁ σ₂ →
      GhCall s₁ (σ₁.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      GhCall s₂ (σ₁.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR (stackArg σ₁ w)) → Region.Sub ⟨S, 256⟩ (workR (stackArg σ₁ w)) →
      s₁.sp = σ₁.sp → s₂.sp = σ₁.sp →
      s₁.rd = σ₁.rd → s₁.wr = σ₁.wr →
      Frame [workR (stackArg σ₁ w), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ₁.mem s₁.mem →
      s₂.rd = σ₂.rd → s₂.wr = σ₂.wr →
      Frame [workR (stackArg σ₁ w), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ₂.mem s₂.mem →
      Region.Sub ⟨Dd, 16 * nb⟩ (⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩ : Region) →
      RelCT isa (Eq2 s₁ s₂) cl TT)
    (htbP : ∀ {σ : State}, pre σ → TbForP tb w σ)
    (htbrel : ∀ {σ₁ σ₂ : State}, pre σ₁ → pre σ₂ → onePub (w + 1) σ₁ σ₂ → ∀ v₁ v₂ : State, v₁.sp = σ₁.sp →
      v₂.sp = σ₁.sp → (∀ r ∈ stRegs, v₁.gpr r = v₂.gpr r) →
      v₁.rd = σ₁.rd → v₁.wr = σ₁.wr →
      Frame [workR (stackArg σ₁ w), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ₁.mem v₁.mem →
      v₂.rd = σ₂.rd → v₂.wr = σ₂.wr →
      Frame [workR (stackArg σ₁ w), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ₂.mem v₂.mem →
      RelCT isa (Eq2 v₁ v₂) (.seq (.block tb) Impl.Gcm.AArch64.Stitch.enc) TT)
    (htbrelS : ∀ {σ₁ σ₂ : State}, pre σ₁ → pre σ₂ → onePub (w + 1) σ₁ σ₂ → ∀ v₁ v₂ : State, v₁.sp = σ₁.sp →
      v₂.sp = σ₁.sp → (∀ r ∈ shRegs, v₁.gpr r = v₂.gpr r) →
      v₁.rd = σ₁.rd → v₁.wr = σ₁.wr →
      Frame [workR (stackArg σ₁ w), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ₁.mem v₁.mem →
      v₂.rd = σ₂.rd → v₂.wr = σ₂.wr →
      Frame [workR (stackArg σ₁ w), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ₂.mem v₂.mem →
      RelCT isa (Eq2 v₁ v₂) (.seq (.block tb) shortRestZ) TT) :
    ConstantTime isa pre (onePub (w + 1)) (Impl.AesGcm.AArch64.Stitch.sealWithS v.callees (8 * w) tb cl true) := by
  refine ct_of fun σ₁ σ₂ p₁ p₂ hq => ?_
  have h₁ := hpre _ p₁
  have h₂ := hpre _ p₂
  have hq₀ := hq
  have exq := hexq hq
  obtain ⟨f₁, f₂⟩ := oneFacts (by omega : w < w + 1) (sealCore h₁) (sealCore h₂) hq
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp, qa⟩ := hq
  have qt : stackArg σ₁ 0 = stackArg σ₂ 0 := qa 0 (by omega)
  have L := f₁.ol.lay
  have hT₁ : σ₁.mem.readW (σ₁.sp + BitVec.ofNat 64 0) 64 = stackArg σ₁ 0 := rfl
  have hT₂ : σ₂.mem.readW (σ₂.sp + BitVec.ofNat 64 0) 64 = stackArg σ₁ 0 := qt.symm
  have hW₁ : σ₁.mem.readW (σ₁.sp + BitVec.ofNat 64 (8 * w)) 64 = stackArg σ₁ w := rfl
  have hW₂ : σ₂.mem.readW (σ₂.sp + BitVec.ofNat 64 (8 * w)) 64 = stackArg σ₁ w := f₂.hW
  have hk : 8 * w % 8 = 0 ∧ 8 * w < 32768 := by omega
  unfold Impl.AesGcm.AArch64.Stitch.sealWithS
  refine rel_seq (entryStash_rel (k := 8 * w) (j := 0) (by omega) rfl (.inl rfl) f₁ f₂ (by omega) qsp
      (by agree_tac [q0, q1, q2, q3, q4, q5, q6, q7]))
    (WP.block_and (entryStash_ok (V := stackArg σ₁ 0) hk (by decide) hW₁ (f₁.hsp w (by omega))
      (f₁.hsp 0 (by omega)) hT₁ (f₁.argW (by omega)) rfl f₁.perm)
      (entry_keeps hk (by decide) hW₁ (f₁.hsp w (by omega)) (f₁.hsp 0 (by omega)) f₁.perm.w))
    (WP.block_and (entryStash_ok (V := stackArg σ₁ 0) hk (by decide) hW₂ (f₂.hsp w (by omega))
      (f₂.hsp 0 (by omega)) hT₂ (f₂.argW (by omega)) q0.symm f₂.perm)
      (entry_keeps hk (by decide) hW₂ (f₂.hsp w (by omega)) (f₂.hsp 0 (by omega)) f₂.perm.w))
    fun τ₁ τ₂ ⟨a₁, k₁⟩ ⟨a₂, k₂⟩ => ?_
  have k5₁ : τ₁.gpr .x5 = BitVec.ofNat 64 (σ₁.gpr .x5).toNat := by rw [k₁ .x5 (by simp), ofNat_toNat']
  have k5₂ : τ₂.gpr .x5 = BitVec.ofNat 64 (σ₁.gpr .x5).toNat := by rw [k₂ .x5 (by simp), ← q5, ofNat_toNat']
  have k24₁ : τ₁.gpr .x24 = BitVec.ofNat 64 (σ₁.gpr .x3).toNat := by rw [a₁.2.2.2.1, ofNat_toNat']
  have k24₂ : τ₂.gpr .x24 = BitVec.ofNat 64 (σ₁.gpr .x3).toNat := by rw [a₂.2.2.2.1, ← q3, ofNat_toNat']
  refine rel_seq (rel_taint [.x5, .x24] (by rw [a₁.1.sp, a₂.1.sp, qsp]) (by agree_tac [k5₁, k5₂, k24₁, k24₂])
      ⟨_, by taint_decide⟩)
    (cond_ok k5₁ (σ₁.gpr .x5).isLt k24₁ (σ₁.gpr .x3).isLt) (cond_ok k5₂ (σ₁.gpr .x5).isLt k24₂ (σ₁.gpr .x3).isLt)
    fun u₁ u₂ ⟨c₁, r₁⟩ ⟨c₂, r₂⟩ => ?_
  have b₁ := SealEntered.of_regs a₁ r₁
  have b₂ := SealEntered.of_regs a₂ r₂
  refine rel_ite (eval_zero c₁ (by split <;> decide)) (eval_zero c₂ (by split <;> decide)) (fun ht => ?_)
    (fun _ => sealRest_rel v h₁ h₂ hq₀ b₁ b₂)
  have hc : (σ₁.gpr .x5).toNat ≤ 16 ∧ (σ₁.gpr .x3).toNat = 12 := by
    by_contra hc; simp [hc] at ht
  have gu₁ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], u₁.gpr r = σ₁.gpr r := fun r hr => by
    rw [r₁.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), k₁ r hr]
  have gu₂ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], u₂.gpr r = σ₁.gpr r := fun r hr => by
    rw [r₂.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), k₂ r hr]
    simp at hr; rcases hr with rfl | rfl | rfl | rfl
    · exact q4.symm
    · exact q5.symm
    · exact q6.symm
    · exact q7.symm
  -- What follows the choice of the path, from the states it leaves.
  have post : ∀ {v₁ v₂ : State}, SealEntered w σ₁ σ₁ v₁ → SealEntered w σ₂ σ₁ v₂ →
      (∀ r ∈ [Reg.x4, .x5, .x6, .x7], v₁.gpr r = σ₁.gpr r) → (∀ r ∈ [Reg.x4, .x5, .x6, .x7], v₂.gpr r = σ₁.gpr r) →
      RelCT isa (Eq2 v₁ v₂) (Impl.AesGcm.AArch64.Fast.runWithP v.callees cl) TT ∧
      RelCT isa (Eq2 v₁ v₂) (Impl.AesGcm.AArch64.Stitch.runWithS v.callees tb cl) TT ∧
      ((σ₁.gpr .x7).toNat ≤ 96 → RelCT isa (Eq2 v₁ v₂) (Impl.AesGcm.AArch64.Stitch.sealShort tb) TT) := by
    intro v₁ v₂ b₁ b₂ g₁ g₂
    have i₁ := frontIn_of f₁ rfl rfl rfl rfl rfl rfl b₁
    have i₂ := frontIn_of f₂ q3.symm q2.symm q4.symm q5.symm q6.symm q7.symm b₂
    rw [← qsp] at i₂
    rw [hc.2] at i₁ i₂
    have ol := f₁.ol
    have sub16 : Region.Sub ⟨stackArg σ₁ w + BitVec.ofNat 64 16, 80⟩ (workR (stackArg σ₁ w)) := Lay.wSub (by decide)
    have hn := (σ₁.gpr .x7).isLt
    have mkD : ∀ {σ u : State}, OneFacts σ σ₁ (w + 1) w → u.wr = σ.wr →
        DataW (σ₁.gpr .x0) (stackArg σ₁ w + BitVec.ofNat 64 16) (stackArg σ₁ w) u (σ₁.gpr .x6) (σ₁.gpr .x7).toNat :=
      fun f wr => ⟨⟨covers_left (by rw [wr]; exact f.dataW), hn, ol.dw, ol.data.sub_right sub16, ol.data⟩,
        by rw [wr]; exact f.dataW, ol.cd⟩
    have hf : ∀ {σ u : State}, Frame [entryR (stackArg σ₁ w)] σ.mem u.mem →
        Frame [workR (stackArg σ₁ w), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ.mem u.mem :=
      fun f => f.sub fun r hr => ⟨_, List.mem_cons_self .., entryR_work _ r hr⟩
    have hgh₂ := @hgh σ₂
    rw [f₂.hW, ← q0, ← q6, ← q7] at hgh₂
    have htb := fun {σ} (p : pre σ) => (htbP p).tbFor
    have htb₂ := htb p₂
    unfold TbFor at htb₂
    rw [f₂.hW, ← q0, ← q6, ← q7, ← qsp] at htb₂
    have e₁ := b₁
    have e₂ := b₂
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, bf₁, -, brd₁, bwr₁⟩ := e₁
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, bf₂, -, brd₂, bwr₂⟩ := e₂
    have hH₁ : blockAt v₁.mem (σ₁.gpr .x0 + BitVec.ofNat 64 240) = Spec.Gcm.ctxH σ₁.mem (σ₁.gpr .x0) :=
      blockAt_frame bf₁ (keep_of_sub (entryR_work _) (ol.ctx.sub_left (Lay.ctxSub (d := 240) (n := 16) (by decide))))
    have hH₂ : blockAt v₂.mem (σ₁.gpr .x0 + BitVec.ofNat 64 240) = Spec.Gcm.ctxH σ₂.mem (σ₁.gpr .x0) :=
      blockAt_frame bf₂ (keep_of_sub (entryR_work _) (ol.ctx.sub_left (Lay.ctxSub (d := 240) (n := 16) (by decide))))
    refine ⟨?_, ?_, ?_⟩
    · refine runWithPX_rel L v cl hMK (Tg := stackArg σ₁ 0) (R := (σ₁.gpr .x1).toNat) (hexW p₁) (hexC p₁)
        ⟨i₁.env, i₁.kept, i₁.x23, i₁.x24, i₁.x26, i₁.x27, i₁.non, rfl⟩
        ⟨i₂.env, i₂.kept, i₂.x23, i₂.x24, i₂.x26, i₂.x27, i₂.non, rfl⟩ i₁.aad i₂.aad hc.1
        ⟨g₁ .x4 (by simp), by rw [g₁ .x5 (by simp), ofNat_toNat'], g₁ .x6 (by simp), by rw [g₁ .x7 (by simp), ofNat_toNat']⟩
        ⟨g₂ .x4 (by simp), by rw [g₂ .x5 (by simp), ofNat_toNat'], g₂ .x6 (by simp), by rw [g₂ .x7 (by simp), ofNat_toNat']⟩
        (mkD f₁ b₁.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2) (mkD f₂ b₂.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
        (by rw [b₁.2.1, ofNat_toNat']) (by rw [b₂.2.1, ← q1, ofNat_toNat']) ol.rounds b₁.2.2.2.2.2.2.1 b₂.2.2.2.2.2.2.1
        (hf bf₁) brd₁ bwr₁ (hf bf₂) brd₂ bwr₂ ?_ ?_ ?_
      · intro s Y Dd S nb c y z r w' sp f hd
        exact hgh p₁ c y z r w' sp f hd
      · intro s Y Dd S nb c y z r w' sp f hd
        rw [← exq]
        exact hgh₂ p₂ c y z r w' (sp.trans qsp) f hd
      · intro s₁ s₂ Y Dd S nb c₁ c₂ y z sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂ hd
        exact hrel p₁ p₂ hq₀ c₁ c₂ y z sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂ hd
    · refine runWithSX_rel L v cl hMK gh (Tg := stackArg σ₁ 0) (R := (σ₁.gpr .x1).toNat) (hexW p₁) (hexC p₁)
        ⟨i₁.env, i₁.kept, i₁.x23, i₁.x24, i₁.x26, i₁.x27, i₁.non, rfl⟩
        ⟨i₂.env, i₂.kept, i₂.x23, i₂.x24, i₂.x26, i₂.x27, i₂.non, rfl⟩ i₁.aad i₂.aad hc.1
        ⟨g₁ .x4 (by simp), by rw [g₁ .x5 (by simp), ofNat_toNat'], g₁ .x6 (by simp), by rw [g₁ .x7 (by simp), ofNat_toNat']⟩
        ⟨g₂ .x4 (by simp), by rw [g₂ .x5 (by simp), ofNat_toNat'], g₂ .x6 (by simp), by rw [g₂ .x7 (by simp), ofNat_toNat']⟩
        (mkD f₁ b₁.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2) (mkD f₂ b₂.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
        (by rw [b₁.2.1, ofNat_toNat']) (by rw [b₂.2.1, ← q1, ofNat_toNat']) ol.rounds b₁.2.2.2.2.2.2.1 b₂.2.2.2.2.2.2.1
        (hf bf₁) brd₁ bwr₁ (hf bf₂) brd₂ bwr₂ ?_ ?_ ?_ ?_ ?_ ?_
      · intro s Y Dd S nb c y z r w' sp f hd
        exact hgh p₁ c y z r w' sp f hd
      · intro s Y Dd S nb c y z r w' sp f hd
        rw [← exq]
        exact hgh₂ p₂ c y z r w' (sp.trans qsp) f hd
      · intro s₁ s₂ Y Dd S nb c₁ c₂ y z sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂ hd
        exact hrel p₁ p₂ hq₀ c₁ c₂ y z sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂ hd
      · intro u he hrd hwr hf' key
        rw [hH₁] at key ⊢
        exact htb p₁ u he hrd hwr hf' key
      · intro u he hrd hwr hf' key
        rw [hH₂] at key ⊢
        exact htb₂ u he hrd hwr hf' key
      · intro v₁ v₂ sp₁ sp₂ hr r₁ w₁ f₁ r₂ w₂ f₂
        exact htbrel p₁ p₂ hq₀ v₁ v₂ sp₁ sp₂ hr r₁ w₁ f₁ r₂ w₂ f₂
    · intro h96
      exact sealShort_rel L
        ⟨i₁.env, i₁.kept, i₁.x23, i₁.x24, i₁.x26, i₁.x27, i₁.non, rfl⟩
        ⟨i₂.env, i₂.kept, i₂.x23, i₂.x24, i₂.x26, i₂.x27, i₂.non, rfl⟩
        ⟨g₁ .x4 (by simp), by rw [g₁ .x5 (by simp), ofNat_toNat'], g₁ .x6 (by simp), by rw [g₁ .x7 (by simp), ofNat_toNat']⟩
        ⟨g₂ .x4 (by simp), by rw [g₂ .x5 (by simp), ofNat_toNat'], g₂ .x6 (by simp), by rw [g₂ .x7 (by simp), ofNat_toNat']⟩
        (by omega) (by rw [b₁.2.1, b₂.2.1, q1]) (by rw [b₁.2.2.2.2.2.2.1, b₂.2.2.2.2.2.2.1])
        (hf bf₁) brd₁ bwr₁ (hf bf₂) brd₂ bwr₂
        fun v₁ v₂ sp₁ sp₂ hr r₁ w₁ f₁ r₂ w₂ f₂ => htbrelS p₁ p₂ hq₀ v₁ v₂ sp₁ sp₂ hr r₁ w₁ f₁ r₂ w₂ f₂
  simp only [↓reduceIte]
  have hnb : (σ₁.gpr .x7).toNat + 2560 ≤ 2 ^ 64 := len_of_disjoint f₁.ol.data f₁.ol.dw f₁.ol.lay.ww
  have x7u₁ : u₁.gpr .x7 = BitVec.ofNat 64 (σ₁.gpr .x7).toNat := by rw [gu₁ .x7 (by simp), ofNat_toNat']
  have x7u₂ : u₂.gpr .x7 = BitVec.ofNat 64 (σ₁.gpr .x7).toNat := by rw [gu₂ .x7 (by simp), ofNat_toNat']
  -- `shortThr`, on the length, which is public.
  refine rel_seq (rel_taint [.x7] (by rw [r₁.sp, r₂.sp, a₁.1.sp, a₂.1.sp, qsp])
      (by agree_tac [gu₁ .x7 (by simp), gu₂ .x7 (by simp)]) ⟨_, by taint_decide⟩)
    (shortThr_ok u₁ x7u₁ (by omega)) (shortThr_ok u₂ x7u₂ (by omega)) fun w₁ w₂ ⟨y9₁, s₁'⟩ ⟨y9₂, s₂'⟩ => ?_
  have c₁ := SealEntered.of_regs b₁ s₁'
  have c₂ := SealEntered.of_regs b₂ s₂'
  have gw₁ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], w₁.gpr r = σ₁.gpr r := fun r hr => by
    rw [s₁'.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), gu₁ r hr]
  have gw₂ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], w₂.gpr r = σ₁.gpr r := fun r hr => by
    rw [s₂'.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), gu₂ r hr]
  have x7w₁ : w₁.gpr .x7 = BitVec.ofNat 64 (σ₁.gpr .x7).toNat := by rw [gw₁ .x7 (by simp), ofNat_toNat']
  have x7w₂ : w₂.gpr .x7 = BitVec.ofNat 64 (σ₁.gpr .x7).toNat := by rw [gw₂ .x7 (by simp), ofNat_toNat']
  refine rel_ite (eval_zero y9₁ (by omega)) (eval_zero y9₂ (by omega)) (fun hz => ?_) (fun _ => ?_)
  · -- `shortMin`.
    refine rel_seq (rel_taint [.x7] (by rw [s₁'.sp, s₂'.sp, r₁.sp, r₂.sp, a₁.1.sp, a₂.1.sp, qsp])
        (by agree_tac [x7w₁, x7w₂]) ⟨_, by taint_decide⟩)
      (shortMin_ok w₁ x7w₁ (by omega)) (shortMin_ok w₂ x7w₂ (by omega)) fun z₁ z₂ ⟨m9₁, t₁⟩ ⟨m9₂, t₂⟩ => ?_
    have gz₁ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], z₁.gpr r = σ₁.gpr r := fun r hr => by
      rw [t₁.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), gw₁ r hr]
    have gz₂ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], z₂.gpr r = σ₁.gpr r := fun r hr => by
      rw [t₂.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), gw₂ r hr]
    have P := post (SealEntered.of_regs c₁ t₁) (SealEntered.of_regs c₂ t₂) gz₁ gz₂
    exact rel_ite (eval_zero m9₁ (by omega)) (eval_zero m9₂ (by omega)) (fun _ => P.1)
      (fun _ => P.2.2 (by have := of_decide_eq_true hz; omega))
  · -- `thr`.
    refine rel_seq (rel_taint [.x7] (by rw [s₁'.sp, s₂'.sp, r₁.sp, r₂.sp, a₁.1.sp, a₂.1.sp, qsp])
        (by agree_tac [x7w₁, x7w₂]) ⟨_, by taint_decide⟩)
      (Stitch.thr_ok w₁) (Stitch.thr_ok w₂) fun v₁ v₂ ⟨x9₁, t₁⟩ ⟨x9₂, t₂⟩ => ?_
    have e9 : v₂.gpr .x9 = BitVec.ofNat 64 (v₁.gpr .x9).toNat := by
      rw [ofNat_toNat', x9₁, x9₂, gw₁ .x7 (by simp), gw₂ .x7 (by simp)]
    have gv₁ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], v₁.gpr r = σ₁.gpr r := fun r hr => by
      rw [t₁.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), gw₁ r hr]
    have gv₂ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], v₂.gpr r = σ₁.gpr r := fun r hr => by
      rw [t₂.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), gw₂ r hr]
    have P := post (SealEntered.of_regs c₁ t₁) (SealEntered.of_regs c₂ t₂) gv₁ gv₂
    exact rel_ite (eval_zero (a := (v₁.gpr .x9).toNat) (by rw [ofNat_toNat']) (v₁.gpr .x9).isLt)
      (eval_zero e9 (v₁.gpr .x9).isLt) (fun _ => P.1) (fun _ => P.2.1)

/-- `sealWithShX_ct`, for a call that writes only what `vg_ghash` does. -/
theorem sealWithSh_ct (v : GcmImpl) (cl : Prog isa) (hMK : MulKey) (gh : Gh8Ok) {tb : List Instr} {w : Nat}
    (hw : w = 1 ∨ w = 2)
    {extra : State → List Region} {pre : State → Prop} (hpre : ∀ s, pre s → sealPreXW w (extra s) s)
    (hgh : ∀ {σ s : State} {Y Dd S : Addr} {nb : Nat}, pre σ →
      GhCall s (σ.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR (stackArg σ w)) → Region.Sub ⟨S, 256⟩ (workR (stackArg σ w)) →
      s.rd = σ.rd → s.wr = σ.wr → s.sp = σ.sp →
      Frame [workR (stackArg σ w), ⟨σ.gpr .x6, (σ.gpr .x7).toNat⟩] σ.mem s.mem →
      WP isa cl s (GhPost s (σ.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb))
    (hrel : ∀ {σ₁ σ₂ s₁ s₂ : State} {Y Dd S : Addr} {nb : Nat}, pre σ₁ → pre σ₂ → onePub (w + 1) σ₁ σ₂ →
      GhCall s₁ (σ₁.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      GhCall s₂ (σ₁.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR (stackArg σ₁ w)) → Region.Sub ⟨S, 256⟩ (workR (stackArg σ₁ w)) →
      s₁.sp = σ₁.sp → s₂.sp = σ₁.sp →
      s₁.rd = σ₁.rd → s₁.wr = σ₁.wr →
      Frame [workR (stackArg σ₁ w), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ₁.mem s₁.mem →
      s₂.rd = σ₂.rd → s₂.wr = σ₂.wr →
      Frame [workR (stackArg σ₁ w), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ₂.mem s₂.mem →
      RelCT isa (Eq2 s₁ s₂) cl TT)
    (htbP : ∀ {σ : State}, pre σ → TbForP tb w σ)
    (htbrel : ∀ {σ₁ σ₂ : State}, pre σ₁ → pre σ₂ → onePub (w + 1) σ₁ σ₂ → ∀ v₁ v₂ : State, v₁.sp = σ₁.sp →
      v₂.sp = σ₁.sp → (∀ r ∈ stRegs, v₁.gpr r = v₂.gpr r) →
      v₁.rd = σ₁.rd → v₁.wr = σ₁.wr →
      Frame [workR (stackArg σ₁ w), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ₁.mem v₁.mem →
      v₂.rd = σ₂.rd → v₂.wr = σ₂.wr →
      Frame [workR (stackArg σ₁ w), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ₂.mem v₂.mem →
      RelCT isa (Eq2 v₁ v₂) (.seq (.block tb) Impl.Gcm.AArch64.Stitch.enc) TT)
    (htbrelS : ∀ {σ₁ σ₂ : State}, pre σ₁ → pre σ₂ → onePub (w + 1) σ₁ σ₂ → ∀ v₁ v₂ : State, v₁.sp = σ₁.sp →
      v₂.sp = σ₁.sp → (∀ r ∈ shRegs, v₁.gpr r = v₂.gpr r) →
      v₁.rd = σ₁.rd → v₁.wr = σ₁.wr →
      Frame [workR (stackArg σ₁ w), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ₁.mem v₁.mem →
      v₂.rd = σ₂.rd → v₂.wr = σ₂.wr →
      Frame [workR (stackArg σ₁ w), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ₂.mem v₂.mem →
      RelCT isa (Eq2 v₁ v₂) (.seq (.block tb) shortRestZ) TT) :
    ConstantTime isa pre (onePub (w + 1)) (Impl.AesGcm.AArch64.Stitch.sealWithS v.callees (8 * w) tb cl true) :=
  sealWithShX_ct v cl hMK gh hw hpre (ex := fun _ => []) (fun _ => by simp) (fun _ => by simp) (fun _ => rfl)
    (fun p c y z r w sp f _ => hgh p c y z r w sp f)
    (fun p₁ p₂ hq c₁ c₂ y z sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂ _ => hrel p₁ p₂ hq c₁ c₂ y z sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂)
    htbP htbrel htbrelS

end VG.Proof.AesGcm.AArch64.Fast
