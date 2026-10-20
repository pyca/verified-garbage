module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.ShortCT
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.OpenSh
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.OpenCT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.ShortCT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.OpenSh
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.OpenCT
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
import VerifiedGarbage.Proof.AesGcm.AArch64.OpenCT
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Open
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenCT
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.ShortOpen

/-!
# AES-GCM on AArch64, short records: `openShort` is constant time

Untrusted: everything here is checked by Lean. As `ShortCT.lean` for
`sealShort`: the head of `openShortA` by the taint analysis, the table and
the rest of `openShortA` (`openRestZ`) by the caller's `tb`; then
`openShortB` by the taint analysis with the result bit public, which both
runs agree on when they agree on whether the record opens (`openShort_rel`).
`openWithShX_ct`: `openWithS` with the short path.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64.Fast

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Taint VG.Impl.AesGcm.AArch64
open VG.Proof.AesGcm.AArch64
open VG.Proof.Gcm.AArch64.Pmull
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ctxCiph)
open VG.Proof.Gcm.AArch64.Stitch (Gh8Ok)

/-- `openShortA` after the table. -/
abbrev openRestZ : Prog isa :=
  .seq (.block Stitch.zeroBufs)
  (.seq Stitch.textIn
  (.seq Stitch.ctToB2
  (.seq Stitch.aadIn
  (.seq (.block (Stitch.lensB ++ Stitch.shortGh ++ Stitch.shortCtr))
  (.seq (Impl.Gcm.AArch64.Stitch.byRounds Stitch.shortAes)
  (.seq (.block (Stitch.shortTagAt uO))
  (.seq cmp
    (.block [imm .x24 1, .sub .x .x24 .x24 .x10]))))))))

/-- The record opens exactly when the tags are equal. -/
theorem tagEqS_iff {Ctx Np A D Tg : Addr} {R al n tl : Nat} (hok : Spec.Gcm.tagLenOk tl = true) (s₀ : State) :
    (Spec.Gcm.openResult (ctxCiph s₀.mem Ctx R) (ctxH s₀.mem Ctx) tl (bytesAt s₀.mem Np 12) (bytesAt s₀.mem D n)
      (bytesAt s₀.mem A al) (bytesAt s₀.mem Tg tl)).isSome = decide (tagEqS Ctx Np A D Tg R al n tl s₀) := by
  rw [Spec.Gcm.openResult, ite_eq_left hok, Spec.Gcm.decryptWith]
  by_cases h : tagEqS Ctx Np A D Tg R al n tl s₀
  · rw [ite_eq_left h, decide_eq_true h]; rfl
  · rw [ite_eq_right h, decide_eq_false h]; rfl

/-- `openShort`, in two runs from the state `open` leaves once the received
tag is at `W`, that agree on the arguments and on whether the record opens,
given its table and the rest of `openShortA` in two runs that agree on
`shRegs`. -/
theorem openShort_rel (gh : Gh8Ok) {tb : List Instr} {Ctx W SP Np A D Tg : Addr} {R al n tl : Nat}
    {σ₁ σ₂ t₁ t₂ : State}
    (o₁ : OpenIn Ctx W SP Np A D Tg R 12 al n tl σ₁ t₁) (o₂ : OpenIn Ctx W SP Np A D Tg R 12 al n tl σ₂ t₂)
    (hx₁ : t₁.gpr .x4 = A ∧ t₁.gpr .x5 = BitVec.ofNat 64 al ∧ t₁.gpr .x6 = D ∧ t₁.gpr .x7 = BitVec.ofNat 64 n)
    (hx₂ : t₂.gpr .x4 = A ∧ t₂.gpr .x5 = BitVec.ofNat 64 al ∧ t₂.gpr .x6 = D ∧ t₂.gpr .x7 = BitVec.ofNat 64 n)
    (h16 : al ≤ 16) (hhi : n ≤ 96)
    (rt₁ : bytesAt t₁.mem W tl = bytesAt σ₁.mem Tg tl) (rt₂ : bytesAt t₂.mem W tl = bytesAt σ₂.mem Tg tl)
    (hok : Spec.Gcm.tagLenOk tl = true)
    (hb : decide (tagEqS Ctx Np A D Tg R al n tl σ₁) = decide (tagEqS Ctx Np A D Tg R al n tl σ₂))
    (htb₁ : ∀ u : State, Env Ctx (W + BitVec.ofNat 64 16) W SP u → u.rd = σ₁.rd → u.wr = σ₁.wr →
      Frame [workR W, ⟨D, n⟩] σ₁.mem u.mem → WP isa (.block tb) u (Stitch.TblPost W (ctxH σ₁.mem Ctx) u))
    (htb₂ : ∀ u : State, Env Ctx (W + BitVec.ofNat 64 16) W SP u → u.rd = σ₂.rd → u.wr = σ₂.wr →
      Frame [workR W, ⟨D, n⟩] σ₂.mem u.mem → WP isa (.block tb) u (Stitch.TblPost W (ctxH σ₂.mem Ctx) u))
    (htbrel : ∀ v₁ v₂ : State, v₁.sp = SP → v₂.sp = SP → (∀ r ∈ shRegs, v₁.gpr r = v₂.gpr r) →
      v₁.rd = σ₁.rd → v₁.wr = σ₁.wr → Frame [workR W, ⟨D, n⟩] σ₁.mem v₁.mem →
      v₂.rd = σ₂.rd → v₂.wr = σ₂.wr → Frame [workR W, ⟨D, n⟩] σ₂.mem v₂.mem →
      RelCT isa (Eq2 v₁ v₂) (.seq (.block tb) openRestZ) TT) :
    RelCT isa (Eq2 t₁ t₂) (Impl.AesGcm.AArch64.Stitch.openShort tb) TT := by
  have L := o₁.lay
  obtain ⟨x4₁, x5₁, x6₁, x7₁⟩ := hx₁
  obtain ⟨x4₂, x5₂, x6₂, x7₂⟩ := hx₂
  have hJ₁ : J0In Ctx (W + BitVec.ofNat 64 16) W SP t₁.gpr (ctxH σ₁.mem Ctx) Np 12 t₁ :=
    ⟨o₁.env, fun _ _ => rfl, o₁.x23, o₁.x24, o₁.x26, o₁.x27, o₁.non, o₁.vals.2.1⟩
  have hJ₂ : J0In Ctx (W + BitVec.ofNat 64 16) W SP t₂.gpr (ctxH σ₂.mem Ctx) Np 12 t₂ :=
    ⟨o₂.env, fun _ _ => rfl, o₂.x23, o₂.x24, o₂.x26, o₂.x27, o₂.non, o₂.vals.2.1⟩
  have j0W : ∀ r ∈ j0Frame (W + BitVec.ofNat 64 16) W, ∃ r' ∈ [workR W, (⟨D, n⟩ : Region)], Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  have F₁ : Frame [workR W, ⟨D, n⟩] σ₁.mem t₁.mem :=
    o₁.fr.sub fun r hr => ⟨_, List.mem_cons_self .., entry16_work W r hr⟩
  have F₂ : Frame [workR W, ⟨D, n⟩] σ₂.mem t₂.mem :=
    o₂.fr.sub fun r hr => ⟨_, List.mem_cons_self .., entry16_work W r hr⟩
  refine (openShort_split tb).symm.rel (rel_seq ?_ (openShortA_ok gh o₁ x4₁ x5₁ x6₁ x7₁ h16 hhi rt₁ hok htb₁)
    (openShortA_ok gh o₂ x4₂ x5₂ x6₂ x7₂ h16 hhi rt₂ hok htb₂) fun m₁ m₂ hm₁ hm₂ => ?_)
  · unfold openShortA Impl.AesGcm.AArch64.Stitch.shortPre
    refine RelCT.assoc' (rel_seq (rel_taint [.x4, .x5, .x6, .x7, .x19, .x20, .x21, .x23]
        (by rw [o₁.env.sp, o₂.env.sp])
        (by agree_tac [x4₁, x4₂, x5₁, x5₂, x6₁, x6₂, x7₁, x7₂, o₁.env.x19, o₂.env.x19, o₁.env.x20, o₂.env.x20,
          o₁.env.x21, o₂.env.x21, o₁.x23, o₂.x23]) ⟨_, by taint_decide⟩)
      (shortHead_ok L hJ₁ x4₁ x5₁ x6₁ x7₁ (by omega)) (shortHead_ok L hJ₂ x4₂ x5₂ x6₂ x7₂ (by omega))
      fun τ₁ τ₂ ⟨e₁, a₁, l₁, c₁, n₁, d₁, r₁, t₁', f₁, rd₁, wr₁⟩ ⟨e₂, a₂, l₂, c₂, n₂, d₂, r₂, t₂', f₂, rd₂, wr₂⟩ => ?_)
    refine RelCT.assoc' (htbrel τ₁ τ₂ e₁.sp e₂.sp (fun r hr => ?_) (by rw [rd₁, o₁.rd₀]) (by rw [wr₁, o₁.wr₀])
      (F₁.trans (f₁.sub j0W)) (by rw [rd₂, o₂.rd₀]) (by rw [wr₂, o₂.wr₀]) (F₂.trans (f₂.sub j0W)))
    simp only [shRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [a₁, a₂]
    · rw [e₁.x19, e₂.x19]
    · rw [e₁.x20, e₂.x20]
    · rw [e₁.x21, e₂.x21]
    · rw [r₁, r₂, o₁.x22, o₂.x22]
    · rw [l₁, l₂]
    · rw [c₁, c₂]
    · rw [n₁, n₂]
    · rw [d₁, d₂]
    · rw [t₁', t₂', o₁.x28, o₂.x28]
  · have x24₂ : m₂.gpr .x24 =
        BitVec.ofNat 64 (1 - if tagEqS Ctx Np A D Tg R al n tl σ₁ then 0 else 1) := by
      have hiff := decide_eq_decide.mp hb
      by_cases h : tagEqS Ctx Np A D Tg R al n tl σ₁
      · rw [hm₂.x24, ite_eq_left (hiff.mp h), ite_eq_left h]
      · rw [hm₂.x24, ite_eq_right (fun h' => h (hiff.mpr h')), ite_eq_right h]
    unfold openShortB
    exact rel_taint [.x19, .x24, .x25, .x26, .x27] (by rw [hm₁.env.sp, hm₂.env.sp])
      (by agree_tac [hm₁.env.x19, hm₂.env.x19, hm₁.x24, x24₂, hm₁.x25, hm₂.x25, hm₁.x26, hm₂.x26, hm₁.x27,
        hm₂.x27]) ⟨_, by taint_decide⟩

/-- `open` with the interleaved path for TLS records, its whole blocks hashed
by `gh`, is constant time, for a `gh` that hashes as `vg_ghash` and leaks the
same in two runs, called with memory changed since the entry only in the
working space and the text, and a `tb` that writes the table and leaks the
same in two runs. -/
theorem openWithShX_ct (v : GcmImpl) (cl : Prog isa) (hMK : MulKey) (gh : Gh8Ok) {tb : List Instr} {w : Nat}
    (hw : w = 2 ∨ w = 3)
    {pre : State → Prop} {extra extraW : State → List Region}
    (hpre : ∀ s, pre s → openPreXW w (extra s) s (extraW s))
    {ex : State → List Region}
    (hexW : ∀ {σ : State}, pre σ → ∀ r ∈ ex σ, (workR (stackArg σ w)).Disjoint r)
    (hexD : ∀ {σ : State}, pre σ → ∀ r ∈ ex σ, (⟨σ.gpr .x6, (σ.gpr .x7).toNat⟩ : Region).Disjoint r)
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
    (htbP : ∀ {σ : State}, pre σ → TbForOP tb (σ.gpr .x0) (stackArg σ w) σ.sp (σ.gpr .x6) (σ.gpr .x7).toNat σ)
    (htbrel : ∀ {σ₁ σ₂ : State}, pre σ₁ → pre σ₂ → onePub (w + 1) σ₁ σ₂ → ∀ v₁ v₂ : State, v₁.sp = σ₁.sp →
      v₂.sp = σ₁.sp → (∀ r ∈ stRegs, v₁.gpr r = v₂.gpr r) →
      v₁.rd = σ₁.rd → v₁.wr = σ₁.wr →
      Frame [workR (stackArg σ₁ w), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ₁.mem v₁.mem →
      v₂.rd = σ₂.rd → v₂.wr = σ₂.wr →
      Frame [workR (stackArg σ₁ w), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ₂.mem v₂.mem →
      RelCT isa (Eq2 v₁ v₂) (.seq (.block tb) Impl.Gcm.AArch64.Stitch.dec) TT)
    (htbrelS : ∀ {σ₁ σ₂ : State}, pre σ₁ → pre σ₂ → onePub (w + 1) σ₁ σ₂ → ∀ v₁ v₂ : State, v₁.sp = σ₁.sp →
      v₂.sp = σ₁.sp → (∀ r ∈ shRegs, v₁.gpr r = v₂.gpr r) →
      v₁.rd = σ₁.rd → v₁.wr = σ₁.wr →
      Frame [workR (stackArg σ₁ w), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ₁.mem v₁.mem →
      v₂.rd = σ₂.rd → v₂.wr = σ₂.wr →
      Frame [workR (stackArg σ₁ w), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ₂.mem v₂.mem →
      RelCT isa (Eq2 v₁ v₂) (.seq (.block tb) openRestZ) TT) :
    ConstantTime isa pre (fun s₁ s₂ => onePub (w + 1) s₁ s₂ ∧ openLeakOf s₁ = openLeakOf s₂)
      (Impl.AesGcm.AArch64.Stitch.openWithS v.callees (8 * w) tb cl true) := by
  have htb := fun {σ} (p : pre σ) => (htbP p).tbFor
  unfold Impl.AesGcm.AArch64.Stitch.openWithS
  refine open_ct_ofW hw hpre fun {σ₁ σ₂ s₁ s₂} p₁ p₂ hq o₁ o₂ x12₁ x12₂ k₁ k₂ hb => ?_
  have hq₀ := hq
  have exq := hexq hq
  obtain ⟨q0, -, -, -, -, -, q6, q7, qsp, qa⟩ := hq
  have k5₁ : s₁.gpr .x5 = BitVec.ofNat 64 (σ₁.gpr .x5).toNat := by rw [k₁ .x5 (by simp), ofNat_toNat']
  have k5₂ : s₂.gpr .x5 = BitVec.ofNat 64 (σ₁.gpr .x5).toNat := by rw [k₂ .x5 (by simp), ofNat_toNat']
  refine rel_seq (rel_taint [.x5, .x24] (by rw [o₁.env.sp, o₂.env.sp]) (by agree_tac [k5₁, k5₂, o₁.x24, o₂.x24])
      ⟨_, by taint_decide⟩)
    (cond_ok k5₁ (σ₁.gpr .x5).isLt o₁.x24 (σ₁.gpr .x3).isLt) (cond_ok k5₂ (σ₁.gpr .x5).isLt o₂.x24 (σ₁.gpr .x3).isLt)
    fun u₁ u₂ ⟨c₁, r₁⟩ ⟨c₂, r₂⟩ => ?_
  have v₁ := o₁.of_regs r₁
  have v₂ := o₂.of_regs r₂
  have y12₁ : u₁.gpr .x12 = stackArg σ₁ 0 := by rw [r₁.others _ (by decide), x12₁]
  have y12₂ : u₂.gpr .x12 = stackArg σ₁ 0 := by rw [r₂.others _ (by decide), x12₂]
  have kk₁ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], u₁.gpr r = σ₁.gpr r := fun r hr => by
    rw [r₁.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), k₁ r hr]
  have kk₂ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], u₂.gpr r = σ₁.gpr r := fun r hr => by
    rw [r₂.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), k₂ r hr]
  have hlt : ((if (σ₁.gpr .x5).toNat ≤ 16 ∧ (σ₁.gpr .x3).toNat = 12 then 0 else 1 : Nat)) < 2 ^ 64 := by
    split <;> decide
  refine rel_ite (eval_zero c₁ hlt) (eval_zero c₂ hlt) (fun ht => ?_) (fun _ => ?_)
  · have hc : (σ₁.gpr .x5).toNat ≤ 16 ∧ (σ₁.gpr .x3).toNat = 12 := by
      by_contra hc; simp [hc] at ht
    have hgh₂ := @hgh σ₂
    rw [exq, ← q0, ← qa w (by omega), ← q6, ← q7] at hgh₂
    have htb₂ := htb p₂
    rw [← q0, ← qa w (by omega), ← q6, ← q7, ← qsp] at htb₂
    have regs : ∀ {u t : State}, (∀ r ∈ [Reg.x4, .x5, .x6, .x7], u.gpr r = σ₁.gpr r) →
        (∀ r ∈ [Reg.x4, .x5, .x6, .x7], t.gpr r = u.gpr r) →
        t.gpr .x4 = σ₁.gpr .x4 ∧ t.gpr .x5 = BitVec.ofNat 64 (σ₁.gpr .x5).toNat ∧ t.gpr .x6 = σ₁.gpr .x6 ∧
          t.gpr .x7 = BitVec.ofNat 64 (σ₁.gpr .x7).toNat := fun ku kt =>
      ⟨by rw [kt _ (by simp), ku _ (by simp)], by rw [kt _ (by simp), ku _ (by simp), ofNat_toNat'],
        by rw [kt _ (by simp), ku _ (by simp)], by rw [kt _ (by simp), ku _ (by simp), ofNat_toNat']⟩
    simp only [↓reduceIte]
    obtain ⟨ol, -, -⟩ := openLay (hpre _ p₁)
    have hnb : (σ₁.gpr .x7).toNat + 2560 ≤ 2 ^ 64 := len_of_disjoint ol.data ol.dw ol.lay.ww
    have htbP₂ := htbP p₂
    rw [← q0, ← qa w (by omega), ← q6, ← q7, ← qsp] at htbP₂
    have x7u₁ : u₁.gpr .x7 = BitVec.ofNat 64 (σ₁.gpr .x7).toNat := by rw [kk₁ .x7 (by simp), ofNat_toNat']
    have x7u₂ : u₂.gpr .x7 = BitVec.ofNat 64 (σ₁.gpr .x7).toNat := by rw [kk₂ .x7 (by simp), ofNat_toNat']
    -- `shortThr`, on the length, which is public.
    refine rel_seq (rel_taint [.x7] (by rw [v₁.env.sp, v₂.env.sp])
        (by agree_tac [kk₁ .x7 (by simp), kk₂ .x7 (by simp)]) ⟨_, by taint_decide⟩)
      (shortThr_ok u₁ x7u₁ (by omega)) (shortThr_ok u₂ x7u₂ (by omega)) fun w₁ w₂ ⟨y9₁, s₁'⟩ ⟨y9₂, s₂'⟩ => ?_
    have v₁ := v₁.of_regs s₁'
    have v₂ := v₂.of_regs s₂'
    have y12₁ : w₁.gpr .x12 = stackArg σ₁ 0 := by rw [s₁'.others _ (by decide), y12₁]
    have y12₂ : w₂.gpr .x12 = stackArg σ₁ 0 := by rw [s₂'.others _ (by decide), y12₂]
    have kk₁ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], w₁.gpr r = σ₁.gpr r := fun r hr => by
      rw [s₁'.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), kk₁ r hr]
    have kk₂ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], w₂.gpr r = σ₁.gpr r := fun r hr => by
      rw [s₂'.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), kk₂ r hr]
    refine rel_ite (eval_zero y9₁ (by omega)) (eval_zero y9₂ (by omega)) (fun hz => ?_) (fun _ => ?_)
    · have h96 := of_decide_eq_true hz
      unfold Impl.AesGcm.AArch64.Stitch.openShortF
      refine openRestWith_rel v₁ v₂ y12₁ y12₂
        (fun o' hT hok hx => have e := regs kk₁ hx
          by rw [hc.2] at o' ⊢
             exact openShort_post gh o' e.1 e.2.1 e.2.2.1 e.2.2.2 hc.1 (by omega) hT hok
               fun u he hrd hwr hf => htbP p₁ u he hrd hwr hf)
        (fun o' hT hok hx => have e := regs kk₂ hx
          by rw [hc.2] at o' ⊢
             exact openShort_post gh o' e.1 e.2.1 e.2.2.1 e.2.2.2 hc.1 (by omega) hT hok
               fun u he hrd hwr hf => htbP₂ u he hrd hwr hf)
        fun p₁' p₂' rt₁ rt₂ hok hx₁ hx₂ => ?_
      rw [hc.2] at p₁' p₂' hb
      exact openShort_rel gh p₁' p₂' (regs kk₁ hx₁) (regs kk₂ hx₂) hc.1 (by omega) rt₁ rt₂ hok
        (by rw [← tagEqS_iff hok, ← tagEqS_iff hok]; exact hb)
        (fun u he hrd hwr hf => htbP p₁ u he hrd hwr hf) (fun u he hrd hwr hf => htbP₂ u he hrd hwr hf)
        fun v₁ v₂ sp₁ sp₂ hr r₁ w₁ f₁ r₂ w₂ f₂ => htbrelS p₁ p₂ hq₀ v₁ v₂ sp₁ sp₂ hr r₁ w₁ f₁ r₂ w₂ f₂
    -- `thr`, on the length, which is public.
    refine rel_seq (rel_taint [.x7] (by rw [v₁.env.sp, v₂.env.sp])
        (by agree_tac [kk₁ .x7 (by simp), kk₂ .x7 (by simp)]) ⟨_, by taint_decide⟩)
      (Stitch.thr_ok w₁) (Stitch.thr_ok w₂) fun z₁ z₂ ⟨x9₁, t₁⟩ ⟨x9₂, t₂⟩ => ?_
    have e9 : z₂.gpr .x9 = BitVec.ofNat 64 (z₁.gpr .x9).toNat := by
      rw [ofNat_toNat', x9₁, x9₂, kk₁ .x7 (by simp), kk₂ .x7 (by simp)]
    have v₁ := v₁.of_regs t₁
    have v₂ := v₂.of_regs t₂
    have y12₁ : z₁.gpr .x12 = stackArg σ₁ 0 := by rw [t₁.others _ (by decide), y12₁]
    have y12₂ : z₂.gpr .x12 = stackArg σ₁ 0 := by rw [t₂.others _ (by decide), y12₂]
    have kk₁ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], z₁.gpr r = σ₁.gpr r := fun r hr => by
      rw [t₁.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), kk₁ r hr]
    have kk₂ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], z₂.gpr r = σ₁.gpr r := fun r hr => by
      rw [t₂.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), kk₂ r hr]
    refine rel_ite (eval_zero (a := (z₁.gpr .x9).toNat) (by rw [ofNat_toNat']) (z₁.gpr .x9).isLt)
      (eval_zero e9 (z₁.gpr .x9).isLt) (fun _ => ?_) (fun _ => ?_)
    · unfold Impl.AesGcm.AArch64.Fast.openFastP
      refine openRestWith_rel v₁ v₂ y12₁ y12₂
        (fun o' hT hok hx => have e := regs kk₁ hx
          openRunWith_postE cl v hMK o' hc.2 e.1 e.2.1 e.2.2.1 e.2.2.2 hc.1 hT hok (hexW p₁) (hexD p₁) (hexC p₁)
            fun s' _ _ _ _ c sY sS hr hw hsp hf hd => hgh p₁ c sY sS hr hw hsp hf hd)
        (fun o' hT hok hx => have e := regs kk₂ hx
          openRunWith_postE cl v hMK o' hc.2 e.1 e.2.1 e.2.2.1 e.2.2.2 hc.1 hT hok (hexW p₁) (hexD p₁) (hexC p₁)
            fun s' _ _ _ _ c sY sS hr hw hsp hf hd => hgh₂ p₂ c sY sS hr hw (hsp.trans qsp) hf hd)
        fun p₁' p₂' rt₁ rt₂ hok hx₁ hx₂ => openRunWith_relX v cl hMK (hexW p₁) (hexD p₁) (hexC p₁) p₁' p₂' hc.2
          (regs kk₁ hx₁) (regs kk₂ hx₂)
          hc.1 rt₁ rt₂ hok hb (fun s' _ _ _ _ c sY sS hr hw hsp hf hd => hgh p₁ c sY sS hr hw hsp hf hd)
          (fun s' _ _ _ _ c sY sS hr hw hsp hf hd => hgh₂ p₂ c sY sS hr hw (hsp.trans qsp) hf hd)
          fun c₁ c₂ sY sS sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂ hd => hrel p₁ p₂ hq₀ c₁ c₂ sY sS sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂ hd
    · unfold Impl.AesGcm.AArch64.Stitch.openFastS
      refine openRestWith_rel v₁ v₂ y12₁ y12₂
        (fun o' hT hok hx => have e := regs kk₁ hx
          WP.mono (openRunWithS_postX v cl hMK gh (I := fun _ => True) o' hc.2 e.1 e.2.1 e.2.2.1 e.2.2.2 hc.1 hT hok
            (hexW p₁) (hexD p₁) (hexC p₁) (fun _ _ => trivial)
            (fun s' _ _ _ _ c sY sS hr hw hsp hf hd =>
              WP.mono (hgh p₁ c sY sS hr hw hsp hf hd) fun _ g => ⟨g, trivial⟩) (htb p₁)) fun _ q => q.1)
        (fun o' hT hok hx => have e := regs kk₂ hx
          WP.mono (openRunWithS_postX v cl hMK gh (I := fun _ => True) o' hc.2 e.1 e.2.1 e.2.2.1 e.2.2.2 hc.1 hT hok
            (hexW p₁) (hexD p₁) (hexC p₁) (fun _ _ => trivial)
            (fun s' _ _ _ _ c sY sS hr hw hsp hf hd =>
              WP.mono (hgh₂ p₂ c sY sS hr hw (hsp.trans qsp) hf hd) fun _ g => ⟨g, trivial⟩) htb₂) fun _ q => q.1)
        fun p₁' p₂' rt₁ rt₂ hok hx₁ hx₂ => openRunWithS_relX v cl hMK gh (hexW p₁) (hexD p₁) (hexC p₁) p₁' p₂' hc.2
          (regs kk₁ hx₁) (regs kk₂ hx₂) hc.1 rt₁ rt₂ hok hb
          (fun s' _ _ _ _ c sY sS hr hw hsp hf hd => hgh p₁ c sY sS hr hw hsp hf hd)
          (fun s' _ _ _ _ c sY sS hr hw hsp hf hd => hgh₂ p₂ c sY sS hr hw (hsp.trans qsp) hf hd)
          (fun c₁ c₂ sY sS sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂ hd => hrel p₁ p₂ hq₀ c₁ c₂ sY sS sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂ hd)
          (htb p₁) htb₂ (fun v₁ v₂ sp₁ sp₂ hr r₁ w₁ f₁ r₂ w₂ f₂ => htbrel p₁ p₂ hq₀ v₁ v₂ sp₁ sp₂ hr r₁ w₁ f₁ r₂ w₂ f₂)
  · exact openRestWith_rel v₁ v₂ y12₁ y12₂ (fun o' hT hok _ => openMain_post v o' hT hok)
      (fun o' hT hok _ => openMain_post v o' hT hok) fun p₁' p₂' rt₁ rt₂ hok _ _ =>
        openMain_rel v p₁' p₂' rt₁ rt₂ hok hb

/-- `openWithShX_ct`, for a call that writes only what `vg_ghash` does. -/
theorem openWithSh_ct (v : GcmImpl) (cl : Prog isa) (hMK : MulKey) (gh : Gh8Ok) {tb : List Instr} {w : Nat}
    (hw : w = 2 ∨ w = 3)
    {pre : State → Prop} {extra : State → List Region} (hpre : ∀ s, pre s → openPreXW w (extra s) s)
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
    (htbP : ∀ {σ : State}, pre σ → TbForOP tb (σ.gpr .x0) (stackArg σ w) σ.sp (σ.gpr .x6) (σ.gpr .x7).toNat σ)
    (htbrel : ∀ {σ₁ σ₂ : State}, pre σ₁ → pre σ₂ → onePub (w + 1) σ₁ σ₂ → ∀ v₁ v₂ : State, v₁.sp = σ₁.sp →
      v₂.sp = σ₁.sp → (∀ r ∈ stRegs, v₁.gpr r = v₂.gpr r) →
      v₁.rd = σ₁.rd → v₁.wr = σ₁.wr →
      Frame [workR (stackArg σ₁ w), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ₁.mem v₁.mem →
      v₂.rd = σ₂.rd → v₂.wr = σ₂.wr →
      Frame [workR (stackArg σ₁ w), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ₂.mem v₂.mem →
      RelCT isa (Eq2 v₁ v₂) (.seq (.block tb) Impl.Gcm.AArch64.Stitch.dec) TT)
    (htbrelS : ∀ {σ₁ σ₂ : State}, pre σ₁ → pre σ₂ → onePub (w + 1) σ₁ σ₂ → ∀ v₁ v₂ : State, v₁.sp = σ₁.sp →
      v₂.sp = σ₁.sp → (∀ r ∈ shRegs, v₁.gpr r = v₂.gpr r) →
      v₁.rd = σ₁.rd → v₁.wr = σ₁.wr →
      Frame [workR (stackArg σ₁ w), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ₁.mem v₁.mem →
      v₂.rd = σ₂.rd → v₂.wr = σ₂.wr →
      Frame [workR (stackArg σ₁ w), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ₂.mem v₂.mem →
      RelCT isa (Eq2 v₁ v₂) (.seq (.block tb) openRestZ) TT) :
    ConstantTime isa pre (fun s₁ s₂ => onePub (w + 1) s₁ s₂ ∧ openLeakOf s₁ = openLeakOf s₂)
      (Impl.AesGcm.AArch64.Stitch.openWithS v.callees (8 * w) tb cl true) :=
  openWithShX_ct v cl hMK gh hw hpre (ex := fun _ => []) (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)
    (fun _ => rfl) (fun p c y z r w sp f _ => hgh p c y z r w sp f)
    (fun p₁ p₂ hq c₁ c₂ y z sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂ _ => hrel p₁ p₂ hq c₁ c₂ y z sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂)
    htbP htbrel htbrelS

end VG.Proof.AesGcm.AArch64.Fast
