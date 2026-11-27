module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.CT
public import VerifiedGarbage.Impl.AesGcm.X86_64.Fast
import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.TailCT
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.SealCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Split.CT
meta import VerifiedGarbage.Impl.AesGcm.X86_64.Fast
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.TailCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.CT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.SealCT
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.AesGcm.X86_64.Cmp
import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Cmp
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.Run
import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.CT
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Short.CT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
public import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Split.Run
meta import VerifiedGarbage.Proof.Framework.Offset

/-! ### `AesGcm.X86_64.Fast.Mid`, which this module and modules that import it used -/

section

/-! ### `AesGcm.X86_64.Fast.Cond`, which only this module used -/

section

/-!
# AES-GCM `seal_split`'s path for TLS records: the condition

Untrusted: everything here is checked by Lean. `Fast.cond` leaves ZF clear
iff the path applies: a 12-byte nonce, at most 16 bytes of additional data
and at least 256 bytes of text, or any text with `any` (`cond_ok`), and takes
the same branches in two runs with the same lengths (`cond_rel`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Fast

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Fast
open VG.Proof.AesGcm.X86_64
open VG.Proof.AesGcm.X86_64.Short (CondS CondKeep condB1_ok eval_ne eval_ae rel_next)

/-- When the path applies. -/
abbrev IsFast (nl al n : Nat) (any : Bool := false) : Prop := nl = 12 ∧ al < 17 ∧ (any = true ∨ 256 ≤ n)

/-- A length in `W` at `d` compared with `k`. -/
theorem condLen_ok {W : Addr} {nl al n : Nat} {s : State} (h : CondS W nl al n s) {d v k : Nat}
    (hd : d = 184 ∨ d = 208) (hv : s.mem.readW (W + BitVec.ofNat 64 d) 64 = BitVec.ofNat 64 v) (hv' : v < 2 ^ 64)
    (hk : k < 2 ^ 31) :
    WP isa (.block [.mov .rcx (.mem (at_ .r15 d)), .alu .cmp .rcx (imm k)]) s fun t =>
      t.cf = some (decide (v < k)) ∧ t.gpr .rax = s.gpr .rax ∧ CondKeep s t := by
  have r₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) 8 :=
    in_left (in_off h.w (by rcases hd with rfl | rfl <;> decide) (by decide))
  have h15 := h.r15
  obtain ⟨s₃, run₃, cx₃, ax₃, k₃⟩ : ∃ s₃, runBlock isa [.mov .rcx (.mem (at_ .r15 d))] s = some s₃ ∧
      s₃.gpr .rcx = BitVec.ofNat 64 v ∧ s₃.gpr .rax = s.gpr .rax ∧ CondKeep s s₃ := by
    refine ⟨_, by xrun [h15, hv, r₁], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · simp [gpr_setReg]
    · intro r a b c; simp [gpr_setReg, b]
    all_goals rfl
  obtain ⟨s₄, run₄, -, cf₄, g₄, m₄, rd₄, wr₄⟩ := cmpImm_ok s₃ .rcx cx₃ hv' hk
  exact WP.block_append_iff.mpr (WP.of_runBlock ⟨s₃, run₃, WP.of_runBlock ⟨s₄, run₄, cf₄, by rw [g₄, ax₃],
    k₃.trans ⟨fun r _ _ _ => by rw [g₄], m₄, rd₄, wr₄⟩⟩⟩)

/-- `cond`: ZF clear iff the path applies, with `rbp` the nonce's length and
the lengths of the additional data and the text in `W`. -/
theorem cond_ok {s : State} {W : Addr} {nl al n : Nat} {any : Bool} (h : CondS W nl al n s) (hnl : nl < 2 ^ 64)
    (hal : al < 2 ^ 64) (hn : n < 2 ^ 64) :
    WP isa (cond any) s fun s' => s'.zf = some (decide ¬IsFast nl al n any) ∧ CondKeep s s' := by
  refine WP.seq (WP.mono (condB1_ok h hnl) fun s₂ ⟨zf₂, ax₂, k₂⟩ => ?_)
  -- `rax := 1` iff the path applies.
  refine WP.seq (WP.mono (Q := fun (s₃ : State) => s₃.gpr .rax = BitVec.ofNat 64 (if IsFast nl al n any then 1 else 0) ∧
      CondKeep s s₃) (WP.ite (!decide (nl = 12)) (eval_ne zf₂) (fun h12 => ?_) (fun h12 => ?_)) fun s₃ ⟨ax₃, k₃⟩ => ?_)
  · have h12 : nl ≠ 12 := by simpa using h12
    refine WP.block_nil ⟨?_, k₂⟩
    rw [ax₂]
    simp [IsFast, h12]
  · have h12 : nl = 12 := by simpa using h12
    refine WP.seq (WP.mono (condLen_ok (h.keep k₂) (.inl rfl) (by rw [k₂.mem]; exact h.alen) hal
      (show 17 < 2 ^ 31 by decide)) fun s₄ ⟨cf₄, ax₄, k₄⟩ => ?_)
    rw [ax₂] at ax₄
    refine WP.ite (!decide (al < 17)) (eval_ae cf₄) (fun h5 => ?_) (fun h5 => ?_)
    · have h5 : ¬al < 17 := by simpa using h5
      refine WP.block_nil ⟨?_, k₂.trans k₄⟩
      rw [ax₄]
      simp [IsFast, h5]
    · have h5 : al < 17 := by simpa using h5
      cases any
      · simp only [condLen, Bool.false_eq_true, ↓reduceIte]
        refine WP.seq (WP.mono (condLen_ok ((h.keep k₂).keep k₄) (.inr rfl)
          (by rw [k₄.mem, k₂.mem]; exact h.len) hn (show 256 < 2 ^ 31 by decide)) fun s₆ ⟨cf₆, ax₆, k₆⟩ => ?_)
        rw [ax₄] at ax₆
        refine WP.ite (decide (n < 256)) (eval_b cf₆) (fun h2 => ?_) (fun h2 => ?_)
        · have h2 : n < 256 := by simpa using h2
          exact WP.block_nil ⟨by simp [ax₆, IsFast, show ¬256 ≤ n by omega_using [h2]], k₂.trans (k₄.trans k₆)⟩
        · have h2 : ¬n < 256 := by simpa using h2
          have hs : IsFast nl al n false := ⟨h12, h5, .inr (by omega_using [h2])⟩
          refine WP.of_runBlock ⟨_, by xrun [], ?_, ?_⟩
          · have e : (if IsFast nl al n false then 1 else 0) = 1 := ite_eq_left_iff.mpr fun h => absurd hs h
            rw [e]
            simp [gpr_setReg]
          · exact k₂.trans (k₄.trans (k₆.trans ⟨fun r a _ _ => by simp [gpr_setReg, a], rfl, rfl, rfl⟩))
      · simp only [condLen, ↓reduceIte]
        have hs : IsFast nl al n true := ⟨h12, h5, .inl rfl⟩
        refine WP.of_runBlock ⟨_, by xrun [], ?_, ?_⟩
        · have e : (if IsFast nl al n true then 1 else 0) = 1 := ite_eq_left_iff.mpr fun h => absurd hs h
          rw [e]
          simp [gpr_setReg]
        · exact k₂.trans (k₄.trans ⟨fun r a _ _ => by simp [gpr_setReg, a], rfl, rfl, rfl⟩)
  -- `test rax, rax`.
  refine WP.of_runBlock ⟨_, by xrun [], ?_, ?_⟩
  · rw [zf_arithFlags, ax₃]
    split <;> rename_i h <;> simp [h]
  · exact k₃.trans ⟨fun r _ _ _ => by simp [gpr_arithFlags], rfl, rfl, rfl⟩

/-- `cond` in two runs with the same lengths: the same branches. -/
theorem cond_rel {W : Addr} {nl al n : Nat} {F₁ F₂ : State → Prop}
    (h₁ : ∀ s, F₁ s → CondS W nl al n s) (h₂ : ∀ s, F₂ s → CondS W nl al n s)
    (hnl : nl < 2 ^ 64) (hal : al < 2 ^ 64) (hn : n < 2 ^ 64) {any : Bool} :
    RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) (cond any) fun _ _ => True := by
  have w₁ : ∀ {F : State → Prop}, (∀ s, F s → CondS W nl al n s) → ∀ s, F s →
      WP isa (.block [.mov32 .rax (imm 0), .alu .cmp .rbp (imm 12)]) s fun t =>
        t.zf = some (decide (nl = 12)) ∧ CondS W nl al n t := fun hF s h =>
    WP.mono (condB1_ok (hF s h) hnl) fun _ ⟨z, _, k⟩ => ⟨z, (hF s h).keep k⟩
  have b1 := rel_next (rel_taint (P := fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) [.rbp] (fun _ _ h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [(h₁ _ h.1).rbp, (h₂ _ h.2).rbp]) ⟨_, by taint_decide⟩)
    (w₁ h₁) (w₁ h₂)
  have last := rel_taint (P := fun _ _ => True) (c := .block [.alu .test .rax (.reg .rax)]) []
    (fun _ _ _ _ hr => by cases hr) ⟨_, by taint_decide⟩
  have none := rel_taint (P := fun _ _ => True) (c := .block []) [] (fun _ _ _ _ hr => by cases hr) ⟨_, by taint_decide⟩
  have one := rel_taint (P := fun _ _ => True) (c := .block [.mov32 .rax (imm 1)]) []
    (fun _ _ _ _ hr => by cases hr) ⟨_, by taint_decide⟩
  refine RelCT.seq b1 (RelCT.seq (RelCT.ite (fun _ _ h => by
      rw [eval_ne h.1.1, eval_ne h.2.1]) (none.mono (fun _ _ _ => trivial) fun _ _ h => h) ?_)
    (last.mono (fun _ _ _ => trivial) fun _ _ h => h))
  -- The additional data's length compared with 17.
  have w₂ : ∀ s, (s.zf = some (decide (nl = 12)) ∧ CondS W nl al n s) →
      WP isa (.block [.mov .rcx (.mem (at_ .r15 alenO)), .alu .cmp .rcx (imm 17)]) s fun t =>
        t.cf = some (decide (al < 17)) ∧ CondS W nl al n t :=
    fun s h => WP.mono (condLen_ok h.2 (.inl rfl) h.2.alen hal (by decide)) fun _ ⟨c, _, k⟩ => ⟨c, h.2.keep k⟩
  have b2 := rel_next (rel_taint (P := fun s₁ s₂ =>
      (s₁.zf = some (decide (nl = 12)) ∧ CondS W nl al n s₁) ∧ (s₂.zf = some (decide (nl = 12)) ∧ CondS W nl al n s₂))
      [.r15] (fun _ _ h r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2.r15, h.2.2.r15]) ⟨_, by taint_decide⟩) w₂ w₂
  refine RelCT.seq (b2.mono (fun _ _ h => h.1) fun _ _ h => h)
    (RelCT.ite (fun _ _ h => (eval_ae h.1.1).trans (eval_ae h.2.1).symm)
      (none.mono (fun _ _ _ => trivial) fun _ _ h => h) ?_)
  cases any
  case true =>
    simp only [condLen, ↓reduceIte]
    exact one.mono (fun _ _ _ => trivial) fun _ _ h => h
  simp only [condLen, Bool.false_eq_true, ↓reduceIte]
  -- The text's length compared with 256.
  have w₃ : ∀ s, (s.cf = some (decide (al < 17)) ∧ CondS W nl al n s) →
      WP isa (.block [.mov .rcx (.mem (at_ .r15 lenO)), .alu .cmp .rcx (imm 256)]) s fun t =>
        t.cf = some (decide (n < 256)) :=
    fun s h => WP.mono (condLen_ok h.2 (.inr rfl) h.2.len hn (by decide)) fun _ ⟨c, _⟩ => c
  have b3 := rel_next (rel_taint (P := fun s₁ s₂ =>
      (s₁.cf = some (decide (al < 17)) ∧ CondS W nl al n s₁) ∧ (s₂.cf = some (decide (al < 17)) ∧ CondS W nl al n s₂))
      [.r15] (fun _ _ h r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2.r15, h.2.2.r15]) ⟨_, by taint_decide⟩) w₃ w₃
  refine RelCT.seq (b3.mono (fun _ _ h => h.1) fun _ _ h => h)
    (RelCT.ite (fun _ _ h => (eval_b h.1).trans (eval_b h.2).symm)
      (none.mono (fun _ _ _ => trivial) fun _ _ h => h) (one.mono (fun _ _ _ => trivial) fun _ _ h => h))

end VG.Proof.AesGcm.X86_64.Fast

end

end

/-!
# AES-GCM `seal_split`'s path for TLS records: after the entry

Untrusted: everything here is checked by Lean. With a prepared key context
(`CtxMode.prepared`), whose `H'` at `ctx + 272` multiplies as `H`
(`ShortFacts.pp1`), `Fast.aad` leaves what `oneAad` does (`aad_mid`), so
`Fast.run`, with `Fast.tail` for at most 16 bytes left (`fbody_ok`), meets
`MidOk` as `SealSplit.run` does (`splitRun_of_midB`), and
`Fast.sel` too, with `other` for the inputs `cond` turns away (`sel_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Fast

variable {np : Nat} {hpn : 8 ≤ np ∧ np ≤ 24}

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Proof.AesGcm.X86_64
open VG.Proof.AesGcm.X86_64.Split
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.StreamTo (BlkToFn)
open VG.Proof.AesGcm.X86_64.Short (ShortFacts KsOk CondKeep IsH1 condS_of)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (blockAt ctxH)

variable {any : Bool}

theorem fastCond_mx (any : Bool) :
    (Impl.AesGcm.X86_64.Fast.cond any : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true := by
  cases any <;> decide +kernel
theorem fastCond_spSafe (any : Bool) :
    (Impl.AesGcm.X86_64.Fast.cond any : Prog isa).all (fun i => !X86_64.isa.writesSp i) = true := by
  cases any <;> decide +kernel
theorem fastCond_xdepth (any : Bool) : (Impl.AesGcm.X86_64.Fast.cond any : Prog isa).x86_64Depth = 0 := by
  cases any <;> decide +kernel
theorem fastAad_mx : (Impl.AesGcm.X86_64.Fast.aad : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true := by
  decide +kernel
theorem fastAad_spSafe : (Impl.AesGcm.X86_64.Fast.aad : Prog isa).all (fun i => !X86_64.isa.writesSp i) = true := by
  decide +kernel
theorem fastAad_xdepth : (Impl.AesGcm.X86_64.Fast.aad : Prog isa).x86_64Depth = 0 := by decide +kernel

/-- `aad` after the entry, for a 12-byte nonce and at most 16 bytes of
additional data: what `oneAad` leaves. -/
theorem aad_mid (hF : ShortFacts) {k : Nat} {s s₁ : State} {Ctx W SP Np A D : Addr} {al n : Nat}
    (C : OneCtx s k Ctx W SP Np A D 12 al n) (X : CtxExt (CtxMode.preparedN np hpn) Ctx (W + BitVec.ofNat 64 16) W SP D n s)
    (E : OneEntry s Ctx W SP A D n s₁)
    (hNp : s.gpr .rdx = Np) (hnl : (s.gpr .rcx).toNat = 12) (hal : (s.gpr .r9).toNat = al) (h16 : al ≤ 16) :
    WP isa Impl.AesGcm.X86_64.Fast.aad s₁ (OneMid s Ctx W SP D n (ctxH s.mem Ctx) (bytesAt s.mem Np 12) (bytesAt s.mem A al) s₁.mem) := by
  have L := C.lay
  have dW : ∀ (p : Addr) (k : Nat), (⟨p, k⟩ : Region).Disjoint ⟨W, 2560⟩ → ∀ r ∈ [oneR W], (⟨p, k⟩ : Region).Disjoint r :=
    fun p k h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.sub_right (Lay.wSub (by decide))
  have hH₁ : blockAt s₁.mem (Ctx + BitVec.ofNat 64 240) = ctxH s.mem Ctx := by
    rw [ctxH_eq, blockAt_frame E.frame (dW _ _ (L.cw'.sub_left (Lay.ctxSub (by decide))))]
  have hiv : bytesAt s₁.mem Np 12 = bytesAt s.mem Np 12 := bytesAt_frame E.frame (dW _ _ C.nonce.w) (by decide)
  have haa : bytesAt s₁.mem A al = bytesAt s.mem A al := bytesAt_frame E.frame (dW _ _ C.aad.w) (by have := C.aad.lt; omega_using [hal])
  have hal' : s₁.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al := by
    rw [E.alen, ← hal, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  -- `H'`, kept from the prepared context.
  have s272 : Region.Sub ⟨Ctx + BitVec.ofNat 64 272, 16⟩ ⟨Ctx, (CtxMode.preparedN np hpn).len⟩ :=
    Offset.sub_base Ctx (show 272 + 16 ≤ 1024 by decide)
  have cw := X.cw.sub_left s272
  have ct : (below SP 8).Disjoint ⟨Ctx + BitVec.ofNat 64 272, 16⟩ :=
    (X.ct.sub_left (below_sub (by decide) (by decide))).sub_right s272
  have inH : InRegions (s₁.rd ++ s₁.wr) (Ctx + BitVec.ofNat 64 272) 16 := by
    rw [E.rd, E.wr]; exact in_off X.cov (show 272 + 16 ≤ 1024 by decide) (by exact (by decide : (1024 : Nat) < 2 ^ 64))
  have hP : IsH1 (ctxH s.mem Ctx) (s₁.mem.readW (Ctx + BitVec.ofNat 64 272) 128) := by
    have e := (X.ok 0 (by have := hpn.1; omega_using [hpn])).2
    simp only [Nat.mul_zero, Nat.add_zero] at e
    rw [E.frame.readW (r := ⟨Ctx + BitVec.ofNat 64 272, 16⟩) (Region.contains_self _ _) (dW _ _ cw) (by decide), e]
    exact hF.pp1 _
  refine WP.mono (WP.with_rdwr (fastAad_ok L E.env hH₁ (by rw [E.r12, hNp])
    (by rw [E.rbp, ← hnl, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (C.nonce.of_eq E.rd E.wr) (C.aad.of_eq E.rd E.wr)
    E.aad hal' h16 hP inH cw ct)) fun s₂ ⟨ao, hrd₂, hwr₂⟩ => ?_
  rw [hiv, haa] at ao
  have f₂ := wFrame_one (D := D) (n := n) (o := 0) (.inl rfl) (wFrame_cons ao.frame)
  have kp : ∀ d, (128 ≤ d ∧ d + 8 ≤ 216) ∨ (224 ≤ d ∧ d + 8 ≤ 240) →
      s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd => f₂.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (kept_oneFrame L C.dE hd)
      (by decide)
  refine ⟨ao.env, ao.hH, ⟨by rw [kp 176 (.inl ⟨by decide, by decide⟩)]; exact E.rounds.1, E.rounds.2⟩,
    by rw [kp 200 (.inl ⟨by decide, by decide⟩)]; exact E.dat, by rw [kp 208 (.inl ⟨by decide, by decide⟩)]; exact E.len,
    by rw [kp 184 (.inl ⟨by decide, by decide⟩)]; exact E.alen, ao.j0, ao.abs, ao.cb,
    E.saved.frame f₂ (saved_oneFrame L C.dE), ?_, ao.frame, hrd₂.trans E.rd, hwr₂.trans E.wr⟩
  exact (E.frame.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact oneR_w).trans
    (wFrame_w ao.frame)

/-- `cond` after the entry: ZF clear iff the path applies, and the entry
kept. -/
theorem condE_ok {k : Nat} {s₀ s₁ : State} {Ctx W SP Np A D : Addr} {nl al n : Nat}
    (C : OneCtx s₀ k Ctx W SP Np A D nl al n) (E : OneEntry s₀ Ctx W SP A D n s₁)
    (hnl : (s₀.gpr .rcx).toNat = nl) (hal : (s₀.gpr .r9).toNat = al) :
    WP isa (Impl.AesGcm.X86_64.Fast.cond any) s₁ fun s₂ => s₂.zf = some (decide ¬IsFast nl al n any) ∧
      OneEntry s₀ Ctx W SP A D n s₂ ∧ CondKeep s₁ s₂ := by
  have hlt := C.data.ok.lt
  refine WP.mono (cond_ok (condS_of E hnl hal) (by rw [← hnl]; exact BitVec.isLt _) (by rw [← hal]; exact BitVec.isLt _)
    (by omega_using [hlt])) fun s₂ ⟨hz, K⟩ => ⟨hz, ?_, K⟩
  exact E.keep C.lay (fun r hr => K.gpr r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) K.rd K.wr (by rw [K.mem]; exact Frame.refl _ _)

/-- `sel`: this path for the inputs it takes, `other` for the rest. -/
theorem sel_ok (hF : ShortFacts) (v : GcmImpl) (B : BlkFn (CtxMode.preparedN np hpn)) {pre : Prog isa}
    {qf : Nat → Nat → Nat} (hpre : PreOk (CtxMode.preparedN np hpn) pre qf)
    {ks : Prog isa} (hks : KsOk ks) {fin : Prog isa} (hfin : FinOk (CtxMode.preparedN np hpn) fin) {other : Prog isa}
    (ho : MidOk (CtxMode.preparedN np hpn) other) :
    MidOk (CtxMode.preparedN np hpn) (Impl.AesGcm.X86_64.Fast.sel (v.withBlk B) pre ks fin other any) := by
  intro s₀ s₁ Ctx W SP Np A D S T' nl al n sl C X kM E hNp hnl hal
  unfold Impl.AesGcm.X86_64.Fast.sel
  refine WP.seq (WP.mono (condE_ok C.toOneCtx E.toOneEntry hnl hal) fun s₂ ⟨hz, E₂, K⟩ => ?_)
  have S₂ : SEntry s₀ Ctx W SP A D S n sl s₂ := ⟨E₂, by rw [K.mem]; exact E.src, by rw [K.mem]; exact E.slen⟩
  refine WP.ite (decide ¬IsFast nl al n any) (eval_e hz) (fun _ => ho C X kM S₂ hNp hnl hal) fun h => ?_
  obtain ⟨h12, h17, -⟩ : IsFast nl al n any := Decidable.not_not.mp (of_decide_eq_false h)
  subst h12
  exact splitRun_of_pre hpre (fbody_ok hF hks B hfin) C X kM S₂ hal
    (aad_mid hF C.toOneCtx X S₂.toOneEntry hNp hnl hal (by omega_using [h17]))

end VG.Proof.AesGcm.X86_64.Fast

end

end

/-!
# AES-GCM `seal_split`'s path for TLS records, in two runs

Untrusted: everything here is checked by Lean. Two runs test the same public
lengths (`cond_rel`), so take the same path: `other`, or `Fast.run`, whose
additional data `aad` addresses memory from the environment's registers, the
nonce's pointer and, once they are loaded, the additional data's pointer and
length, which are public (`aad_rel`), and whose end takes the same branch in
both (`fbody_rel`): `sel_rel`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Fast

variable {np : Nat} {hpn : 8 ≤ np ∧ np ≤ 24}

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Impl.AesGcm.X86_64.Fast (aadPad aadMul aadReg aadFull aadMulR aadSome)
open VG.Proof.AesGcm.X86_64
open VG.Proof.AesGcm.X86_64.Split
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.StreamTo (BlkToFn)
open VG.Proof.AesGcm.X86_64.Short (ShortFacts KsOk KsRel condS_of rel_next rel_piece keepsEnv)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

variable {any : Bool}

/-- Before `aad`. -/
def A0 (M : CtxMode) (Ctx W SP : Addr) (R : Nat) (A : Addr) (al : Nat) (D : Addr) (n : Nat) (Np : Addr)
    (s : State) : Prop :=
  OneS M Ctx W SP R A al D n none s ∧ s.gpr .r12 = Np ∧ s.gpr .rbp = BitVec.ofNat 64 12 ∧
    DataOk (W + BitVec.ofNat 64 16) W SP s Np 12

/-- After `j012`. -/
def A1 (M : CtxMode) (Ctx W SP : Addr) (R : Nat) (A : Addr) (al : Nat) (D : Addr) (n : Nat) (s : State) : Prop :=
  ∃ (H : Block) (iv : List Byte) (σ : State), J0Mid Ctx (W + BitVec.ofNat 64 16) W SP H iv σ.mem s ∧
    OneS M Ctx W SP R A al D n none σ ∧ s.rd = σ.rd ∧ s.wr = σ.wr

/-- After the additional data's length is tested. -/
def A3 (M : CtxMode) (Ctx W SP : Addr) (R : Nat) (A : Addr) (al : Nat) (D : Addr) (n : Nat) (s : State) : Prop :=
  OneS M Ctx W SP R A al D n none s ∧ s.gpr .rcx = BitVec.ofNat 64 al ∧ s.zf = some (decide (al = 0))

/-- After the additional data's length is compared with 5. -/
def A5 (M : CtxMode) (Ctx W SP : Addr) (R : Nat) (A : Addr) (al : Nat) (D : Addr) (n : Nat) (s : State) : Prop :=
  OneS M Ctx W SP R A al D n none s ∧ s.gpr .rcx = BitVec.ofNat 64 al ∧ s.zf = some (decide (al = 5))

/-- After the additional data's length is compared with 16. -/
def A16 (M : CtxMode) (Ctx W SP : Addr) (R : Nat) (A : Addr) (al : Nat) (D : Addr) (n : Nat) (s : State) : Prop :=
  OneS M Ctx W SP R A al D n none s ∧ s.gpr .rcx = BitVec.ofNat 64 al ∧ s.zf = some (decide (al = 16))

theorem envRegs_mem {r : Reg} (hr : r ∈ [Reg.r12, .r13, .r14, .r15, .rsp]) : r = .r12 ∨ r ∈ [Reg.r13, .r14, .r15, .rsp] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp

section
variable {M : CtxMode} {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP) {R : Nat} {Np A D : Addr}
  {al n : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (h16 : al ≤ 16)
include L hDW h16

/-- `aad` in two runs: the same addresses and branches. -/
theorem aad_rel :
    RelCT isa (fun s₁ s₂ => A0 M Ctx W SP R A al D n Np s₁ ∧ A0 M Ctx W SP R A al D n Np s₂)
      Impl.AesGcm.X86_64.Fast.aad fun _ _ => True := by
  have empty := rel_taint (P := fun _ _ => True) (c := .block []) [] (fun _ _ _ _ hr => by cases hr) ⟨_, by taint_decide⟩
  -- `j012`.
  have w₁ : ∀ s, A0 M Ctx W SP R A al D n Np s → WP isa (.block j012) s (A1 M Ctx W SP R A al D n) := fun s h =>
    WP.mono (WP.with_rdwr (j012_ok L ⟨h.1.env, rfl, h.2.1, h.2.2.1, h.2.2.2⟩)) fun _ ⟨o, hrd, hwr⟩ =>
      ⟨_, _, s, o, h.1, hrd, hwr⟩
  have r₁ := rel_next (rel_taint (P := fun s₁ s₂ => A0 M Ctx W SP R A al D n Np s₁ ∧ A0 M Ctx W SP R A al D n Np s₂)
      [.r12, .r13, .r14, .r15, .rsp] (fun _ _ h r hr => by
        rcases envRegs_mem hr with rfl | hr
        · rw [h.1.2.1, h.2.2.1]
        · exact env_agree h.1.1.env h.2.1.env r hr) ⟨_, by taint_decide⟩) w₁ w₁
  -- `initState`.
  have w₂ : ∀ s, A1 M Ctx W SP R A al D n s → WP isa (.block initState) s (OneS M Ctx W SP R A al D n none) :=
    fun s ⟨_, _, σ, j, O, hrd, hwr⟩ => WP.mono (WP.with_rdwr (initState_ok L j)) fun _ ⟨o, hrd', hwr'⟩ =>
      O.frame L o.env (hrd'.trans hrd) (hwr'.trans hwr) hDW (w_one (j0Frame_one o.frame))
  have r₂ := rel_next (rel_taint (P := fun s₁ s₂ => A1 M Ctx W SP R A al D n s₁ ∧ A1 M Ctx W SP R A al D n s₂)
      [.r13, .r14, .r15, .rsp] (fun _ _ h => by
        obtain ⟨⟨_, _, _, j₁, -⟩, ⟨_, _, _, j₂, -⟩⟩ := h
        exact env_agree j₁.env j₂.env) ⟨_, by taint_decide⟩) w₂ w₂
  -- The additional data's length tested.
  have w₃ : ∀ s, OneS M Ctx W SP R A al D n none s →
      WP isa (.block [.mov .rcx (.mem (at_ .r15 alenO)), .alu .test .rcx (.reg .rcx)]) s
        (A3 M Ctx W SP R A al D n) := fun s O => by
    have he := O.env
    have h15 := he.r15
    have q₂ := he.perm.wR (show 184 + 8 ≤ 2560 by decide)
    have hal := O.alen
    have hlt := O.dA.lt
    obtain ⟨s₃, run₃, hcx₃, hzf₃, hg₃, hm₃, hrd₃, hwr₃⟩ : ∃ s₃, runBlock isa
        [.mov .rcx (.mem (at_ .r15 alenO)), .alu .test .rcx (.reg .rcx)] s = some s₃ ∧
        s₃.gpr .rcx = BitVec.ofNat 64 al ∧ s₃.zf = some (decide (al = 0)) ∧
        (∀ r, r ≠ .rcx → s₃.gpr r = s.gpr r) ∧ s₃.mem = s.mem ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr := by
      refine ⟨_, by xrun [h15, q₂], ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [gpr_setReg, hal]
      · simp only [zf_arithFlags, gpr_setReg, ite_true, hal]; rw [and_self_beq (by omega_using [h16])]
      · intro r h; simp [gpr_setReg, h]
      all_goals rfl
    have he₃ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₃ := he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₃ _ (by decide)) hrd₃ hwr₃
    exact WP.of_runBlock ⟨s₃, run₃, O.frame L he₃ hrd₃ hwr₃ hDW (by rw [hm₃]; exact Frame.refl _ _), hcx₃, hzf₃⟩
  have r₃ := rel_next (rel_taint (P := fun s₁ s₂ => OneS M Ctx W SP R A al D n none s₁ ∧
      OneS M Ctx W SP R A al D n none s₂) [.r13, .r14, .r15, .rsp] (fun _ _ h => env_agree h.1.env h.2.env)
      ⟨_, by simp only [alenO]; taint_decide⟩) w₃ w₃
  -- The additional data padded in `T`, and multiplied.
  have r₄ : RelCT isa (fun s₁ s₂ => A3 M Ctx W SP R A al D n s₁ ∧ A3 M Ctx W SP R A al D n s₂)
      (.ite .e (.block []) aadSome) fun _ _ => True := by
    refine rel_ite_e (fun _ _ h => by rw [h.1.2.2, h.2.2.2]) (empty.mono (fun _ _ _ => trivial) fun _ _ h => h)
      (StreamTo.RelCT.of_imp (1 ≤ al) (fun _ _ h => by
        have e := h.1.1.2.2.symm.trans h.2
        simp only [Option.some.injEq, decide_eq_false_iff_not] at e
        omega_using [e]) fun h1 => ?_)
    -- The length compared with 5.
    have w₅ : ∀ s, A3 M Ctx W SP R A al D n s →
        WP isa (.block [.alu .cmp .rcx (imm 5)]) s (A5 M Ctx W SP R A al D n) := fun s h => by
      obtain ⟨t, run, zf, -, g, m, rd, wr⟩ := cmpImm_ok s .rcx h.2.1 h.1.dA.lt (show 5 < 2 ^ 31 by decide)
      have he : Env Ctx (W + BitVec.ofNat 64 16) W SP t := h.1.env.keep (fun r _ => by rw [g]) rd wr
      exact WP.of_runBlock ⟨t, run, h.1.frame L he rd wr hDW (by rw [m]; exact Frame.refl _ _),
        by rw [g]; exact h.2.1, zf⟩
    have r₅ := rel_next (rel_taint (P := fun s₁ s₂ => A3 M Ctx W SP R A al D n s₁ ∧ A3 M Ctx W SP R A al D n s₂)
      [.rcx] (fun _ _ h r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2.1, h.2.2.1]) ⟨_, by taint_decide⟩) w₅ w₅
    -- Five bytes, from a register.
    have hr : ∀ s, A5 M Ctx W SP R A al D n s →
        WP isa (.block [.mov .rsi (.mem (at_ .r15 aadO))]) s fun t => t.gpr .rsi = A := fun s h => by
      have q := h.1.env.perm.wR (show 232 + 8 ≤ 2560 by decide)
      have h15 := h.1.env.r15
      have ha := h.1.aad
      obtain ⟨t, run, ht⟩ : ∃ t, runBlock isa [.mov .rsi (.mem (at_ .r15 aadO))] s = some t ∧ t.gpr .rsi = A := by
        refine ⟨_, by xrun [h15, q], ?_⟩
        simp [gpr_setReg, ha]
      exact WP.of_runBlock ⟨t, run, ht⟩
    have reg := rel_piece (F₁ := A5 M Ctx W SP R A al D n) (F₂ := A5 M Ctx W SP R A al D n)
      (c := .block (aadReg ++ aadMulR)) [.rsi] (fun _ h => h.1.env) (fun _ h => h.1.env) (keepsEnv (by decide +kernel))
      ⟨_, by simp only [aadO]; taint_decide⟩ hr hr (fun _ _ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁, h₂]) ⟨_, by taint_decide⟩
    -- The length compared with 16.
    have w₁₆ : ∀ s, A5 M Ctx W SP R A al D n s →
        WP isa (.block [.alu .cmp .rcx (imm 16)]) s (A16 M Ctx W SP R A al D n) := fun s h => by
      obtain ⟨t, run, zf, -, g, m, rd, wr⟩ := cmpImm_ok s .rcx h.2.1 h.1.dA.lt (show 16 < 2 ^ 31 by decide)
      have he : Env Ctx (W + BitVec.ofNat 64 16) W SP t := h.1.env.keep (fun r _ => by rw [g]) rd wr
      exact WP.of_runBlock ⟨t, run, h.1.frame L he rd wr hDW (by rw [m]; exact Frame.refl _ _),
        by rw [g]; exact h.2.1, zf⟩
    have r₁₆ := rel_next (rel_taint (P := fun s₁ s₂ => A5 M Ctx W SP R A al D n s₁ ∧ A5 M Ctx W SP R A al D n s₂)
      [.rcx] (fun _ _ h r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2.1, h.2.2.1]) ⟨_, by taint_decide⟩) w₁₆ w₁₆
    -- Sixteen bytes, loaded whole.
    have hr₁₆ : ∀ s, A16 M Ctx W SP R A al D n s →
        WP isa (.block [.mov .rsi (.mem (at_ .r15 aadO))]) s fun t => t.gpr .rsi = A := fun s h => by
      have q := h.1.env.perm.wR (show 232 + 8 ≤ 2560 by decide)
      have h15 := h.1.env.r15
      have ha := h.1.aad
      obtain ⟨t, run, ht⟩ : ∃ t, runBlock isa [.mov .rsi (.mem (at_ .r15 aadO))] s = some t ∧ t.gpr .rsi = A := by
        refine ⟨_, by xrun [h15, q], ?_⟩
        simp [gpr_setReg, ha]
      exact WP.of_runBlock ⟨t, run, ht⟩
    have full := rel_piece (F₁ := A16 M Ctx W SP R A al D n) (F₂ := A16 M Ctx W SP R A al D n)
      (c := .block (aadFull ++ aadMulR)) [.rsi] (fun _ h => h.1.env) (fun _ h => h.1.env) (keepsEnv (by decide +kernel))
      ⟨_, by simp only [aadO]; taint_decide⟩ hr₁₆ hr₁₆ (fun _ _ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁, h₂]) ⟨_, by taint_decide⟩
    -- Any other length, padded in `T`, and multiplied.
    have hw : ∀ s, A16 M Ctx W SP R A al D n s →
        WP isa (.block (([.mov32 .rax (imm 0), .store (at_ .r15 tO) .rax, .store (at_ .r15 (tO + 8)) .rax] :
          List Instr) ++ ptr .rdi .r15 tO ++ ([.mov .rsi (.mem (at_ .r15 aadO))] : List Instr))) s
          fun t => t.gpr .rsi = A ∧ t.gpr .rdi = W + BitVec.ofNat 64 96 ∧ t.gpr .rcx = BitVec.ofNat 64 al :=
      fun s h => WP.mono (aadPadHead_ok L h.1.env h.1.dA h1 h16 h.1.aad h.2.1) fun _ ⟨_, _, _, _, lp⟩ =>
        ⟨lp.rsi, lp.rdi, lp.rcx⟩
    have pad := rel_piece (F₁ := A16 M Ctx W SP R A al D n) (F₂ := A16 M Ctx W SP R A al D n) (c := copyLoop)
      [.rsi, .rdi, .rcx] (fun _ h => h.1.env) (fun _ h => h.1.env) (keepsEnv (by decide +kernel))
      ⟨_, by simp only [tO, aadO, ptr]; taint_decide⟩ hw hw (fun _ _ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2.1, h₂.2.1]
        · rw [h₁.2.2, h₂.2.2]) ⟨_, by taint_decide⟩
    have wp : ∀ s, A16 M Ctx W SP R A al D n s → WP isa aadPad s (Env Ctx (W + BitVec.ofNat 64 16) W SP) :=
      fun s h => WP.mono (aadPad_ok L h.1.env h.1.dA h1 h16 h.1.aad h.2.1) fun _ g => g.1
    have pad' := rel_next (c := aadPad) (by unfold aadPad; exact pad) wp wp
    have mul := rel_taint (P := fun s₁ s₂ => Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧
      Env Ctx (W + BitVec.ofNat 64 16) W SP s₂) (c := .block aadMul) [.r13, .r14, .r15, .rsp]
      (fun _ _ h => env_agree h.1 h.2) ⟨_, by taint_decide⟩
    have some := RelCT.seq r₅ (rel_ite_e (fun _ _ h => by rw [h.1.2.2, h.2.2.2])
      (reg.mono (fun _ _ h => h.1) fun _ _ h => h) ((RelCT.seq r₁₆ (rel_ite_e (fun _ _ h => by rw [h.1.2.2, h.2.2.2])
        (full.mono (fun _ _ h => h.1) fun _ _ h => h) ((RelCT.seq pad' mul).mono (fun _ _ h => h.1) fun _ _ h => h))).mono
        (fun _ _ h => h.1) fun _ _ h => h))
    unfold aadSome
    exact some.mono (fun _ _ h => h.1) fun _ _ h => h
  unfold Impl.AesGcm.X86_64.Fast.aad
  exact RelCT.seq r₁ (RelCT.seq r₂ (RelCT.seq r₃ r₄))

end

/-- `sel` in two runs: the same path, and on it the same addresses and
branches. -/
theorem sel_rel (v : GcmImpl) (B : BlkFn (CtxMode.preparedN np hpn)) {pre : Prog isa} {qf : Nat → Nat → Nat}
    (hpre : PreOk (CtxMode.preparedN np hpn) pre qf) (hrel : PreRel (CtxMode.preparedN np hpn) pre)
    (hq : ∀ n sl, sl ≤ n → 16 * qf n sl ≤ n) (hF : ShortFacts)
    {ks : Prog isa} (hks : KsOk ks) (hkr : KsRel ks) {fin : Prog isa} (hfr : FinRel (CtxMode.preparedN np hpn) fin)
    {other : Prog isa} (ho : MidRel (CtxMode.preparedN np hpn) other) :
    MidRel (CtxMode.preparedN np hpn) (Impl.AesGcm.X86_64.Fast.sel (v.withBlk B) pre ks fin other any) := by
  intro s₀ s₀' Ctx W SP Np A D S T' nl al n sl R C C' X X' kM hNp hnl hal hR hNp' hnl' hal' hR'
  have hlt := C.data.ok.lt
  unfold Impl.AesGcm.X86_64.Fast.sel
  have hw : ∀ {s₀ : State} (C : SplitCtx s₀ Ctx W SP Np A D S T' nl al n sl), (s₀.gpr .rcx).toNat = nl →
      (s₀.gpr .r9).toNat = al → ∀ s, SEntry s₀ Ctx W SP A D S n sl s →
      WP isa (Impl.AesGcm.X86_64.Fast.cond any) s fun u => u.zf = some (decide ¬IsFast nl al n any) ∧
        SEntry s₀ Ctx W SP A D S n sl u :=
    fun C hnl hal s h => WP.mono (condE_ok C.toOneCtx h.toOneEntry hnl hal) fun _ ⟨z, E, K⟩ =>
      ⟨z, E, by rw [K.mem]; exact h.src, by rw [K.mem]; exact h.slen⟩
  have c := rel_next (cond_rel (F₁ := SEntry s₀ Ctx W SP A D S n sl) (F₂ := SEntry s₀' Ctx W SP A D S n sl)
      (fun _ h => condS_of h.toOneEntry hnl hal) (fun _ h => condS_of h.toOneEntry hnl' hal')
      (by rw [← hnl]; exact BitVec.isLt _) (by rw [← hal]; exact BitVec.isLt _) (by omega_using [hlt]))
    (hw C hnl hal) (hw C' hnl' hal')
  refine RelCT.seq c (rel_ite_e (fun _ _ h => by rw [h.1.1, h.2.1])
    ((ho C C' X X' kM hNp hnl hal hR hNp' hnl' hal' hR').mono
      (fun _ _ h => ⟨h.1.1.2, h.1.2.2⟩) fun _ _ h => h) ?_)
  by_cases hs : IsFast nl al n any
  · obtain ⟨h12, h17, -⟩ := hs
    subst h12
    have L := C.lay
    have a := (aad_rel L C.dE (M := (CtxMode.preparedN np hpn)) (R := R) (Np := Np) (A := A) (al := al) (by omega_using [h17])).mono
      (P' := fun (s₁ s₂ : State) => SEntry s₀ Ctx W SP A D S n sl s₁ ∧ SEntry s₀' Ctx W SP A D S n sl s₂)
      (fun _ _ g => ⟨g.1.toOneEntry.aadPre C.toOneCtx X hNp hnl hal hR,
        g.2.toOneEntry.aadPre C'.toOneCtx X' hNp' hnl' hal' hR'⟩) fun _ _ _ => trivial
    exact (splitRun_rel_of_pre hpre hrel hq (fbody_rel hks hkr B hfr) C C' X X' kM hNp hnl hal hR hNp' hnl' hal' hR' a
      (fun s E => aad_mid hF C.toOneCtx X E.toOneEntry hNp hnl hal (by omega_using [h17]))
      (fun s E => aad_mid hF C'.toOneCtx X' E.toOneEntry hNp' hnl' hal' (by omega_using [h17]))).mono
      (fun _ _ h => ⟨h.1.1.2, h.1.2.2⟩) fun _ _ h => h
  · exact RelCT.of_false fun _ _ h => by have := h.1.1.1.symm.trans h.2; simp [hs] at this

end VG.Proof.AesGcm.X86_64.Fast
