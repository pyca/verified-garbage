module

import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.Aad
public import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.Cond
import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.Tail
public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.Run
public import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Context
import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks

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
    (C : OneCtx s k Ctx W SP Np A D 12 al n) (X : CtxExt CtxMode.prepared Ctx (W + BitVec.ofNat 64 16) W SP D n s)
    (E : OneEntry s Ctx W SP A D n s₁)
    (hNp : s.gpr .rdx = Np) (hnl : (s.gpr .rcx).toNat = 12) (hal : (s.gpr .r9).toNat = al) (h16 : al ≤ 16) :
    WP isa Impl.AesGcm.X86_64.Fast.aad s₁ (OneMid s Ctx W SP D n (ctxH s.mem Ctx) (bytesAt s.mem Np 12) (bytesAt s.mem A al) s₁.mem) := by
  have L := C.lay
  have dW : ∀ (p : Addr) (k : Nat), (⟨p, k⟩ : Region).Disjoint ⟨W, 2560⟩ → ∀ r ∈ [oneR W], (⟨p, k⟩ : Region).Disjoint r :=
    fun p k h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.sub_right (Lay.wSub (by decide))
  have hH₁ : blockAt s₁.mem (Ctx + BitVec.ofNat 64 240) = ctxH s.mem Ctx := by
    rw [ctxH_eq, blockAt_frame E.frame (dW _ _ (L.cw'.sub_left (Lay.ctxSub (by decide))))]
  have hiv : bytesAt s₁.mem Np 12 = bytesAt s.mem Np 12 := bytesAt_frame E.frame (dW _ _ C.nonce.w) (by decide)
  have haa : bytesAt s₁.mem A al = bytesAt s.mem A al := bytesAt_frame E.frame (dW _ _ C.aad.w) (by have := C.aad.lt; omega)
  have hal' : s₁.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al := by
    rw [E.alen, ← hal, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  -- `H'`, kept from the prepared context.
  have s272 : Region.Sub ⟨Ctx + BitVec.ofNat 64 272, 16⟩ ⟨Ctx, CtxMode.prepared.len⟩ :=
    Offset.sub_base Ctx (show 272 + 16 ≤ 1024 by decide)
  have cw := X.cw.sub_left s272
  have ct : (below SP 8).Disjoint ⟨Ctx + BitVec.ofNat 64 272, 16⟩ :=
    (X.ct.sub_left (below_sub (by decide) (by decide))).sub_right s272
  have inH : InRegions (s₁.rd ++ s₁.wr) (Ctx + BitVec.ofNat 64 272) 16 := by
    rw [E.rd, E.wr]; exact in_off X.cov (show 272 + 16 ≤ 1024 by decide) (by decide)
  have hP : IsH1 (ctxH s.mem Ctx) (s₁.mem.readW (Ctx + BitVec.ofNat 64 272) 128) := by
    have e := (X.ok 0 (by decide)).2
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
    (by omega)) fun s₂ ⟨hz, K⟩ => ⟨hz, ?_, K⟩
  exact E.keep C.lay (fun r hr => K.gpr r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) K.rd K.wr (by rw [K.mem]; exact Frame.refl _ _)

/-- `sel`: this path for the inputs it takes, `other` for the rest. -/
theorem sel_ok (hF : ShortFacts) (v : GcmImpl) (B : BlkFn CtxMode.prepared) (T : BlkToFn CtxMode.prepared)
    {ks : Prog isa} (hks : KsOk ks) {fin : Prog isa} (hfin : FinOk CtxMode.prepared fin) {other : Prog isa}
    (ho : MidOk CtxMode.prepared other) :
    MidOk CtxMode.prepared (Impl.AesGcm.X86_64.Fast.sel (v.withBlk B) T.fn ks fin other any) := by
  intro s₀ s₁ Ctx W SP Np A D S T' nl al n sl C X kM E hNp hnl hal
  unfold Impl.AesGcm.X86_64.Fast.sel
  refine WP.seq (WP.mono (condE_ok C.toOneCtx E.toOneEntry hnl hal) fun s₂ ⟨hz, E₂, K⟩ => ?_)
  have S₂ : SEntry s₀ Ctx W SP A D S n sl s₂ := ⟨E₂, by rw [K.mem]; exact E.src, by rw [K.mem]; exact E.slen⟩
  refine WP.ite (decide ¬IsFast nl al n any) (eval_e hz) (fun _ => ho C X kM S₂ hNp hnl hal) fun h => ?_
  obtain ⟨h12, h17, -⟩ : IsFast nl al n any := Decidable.not_not.mp (of_decide_eq_false h)
  subst h12
  exact splitRun_of_midB T (fbody_ok hF hks B hfin) C X kM S₂ hal
    (aad_mid hF C.toOneCtx X S₂.toOneEntry hNp hnl hal (by omega))

end VG.Proof.AesGcm.X86_64.Fast
