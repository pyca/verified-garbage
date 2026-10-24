module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
public import VerifiedGarbage.Proof.AesGcm.AArch64.Env
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Env
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
import VerifiedGarbage.Proof.AesGcm.AArch64.OneEntry
meta import VerifiedGarbage.Proof.AesGcm.AArch64.OneEntry
public import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
public import VerifiedGarbage.Impl.AesGcm.AArch64.Fast
meta import VerifiedGarbage.Impl.AesGcm.AArch64.Fast
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.AesGcm.AArch64.Body
import VerifiedGarbage.Proof.AesGcm.AArch64.FinTag
import VerifiedGarbage.Proof.AesGcm.AArch64.Fn
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Proof.AesGcm.AArch64.StreamFinish
import VerifiedGarbage.Proof.AesGcm.AArch64.StreamVerify
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Gcm.Bits
meta import VerifiedGarbage.Impl.Aes.AArch64.Alloc
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Body
meta import VerifiedGarbage.Proof.AesGcm.AArch64.FinTag
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Fn
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
meta import VerifiedGarbage.Proof.AesGcm.AArch64.StreamFinish
meta import VerifiedGarbage.Proof.AesGcm.AArch64.StreamVerify
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Gcm.Bits

/-!
# AES-GCM on AArch64: `vg_ghash_with_powers`, called with `pw` from the stack

Untrusted: everything here is checked by Lean. What the `*_with_powers`
functions need of an implementation of `vg_ghash_with_powers`
(`GhashWithImpl`), and its call `Fast.pwCall k`: `x5` loaded with the
stack argument `pw` at `sp + k`, then the call, which hashes as `vg_ghash`
(`GhPost`) when the powers of the hash subkey are at `pw` (`GhWCall`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.Impl.AesGcm.AArch64

/-- What a call of `vg_ghash_with_powers` needs besides `GhCall`: the powers
of the hash subkey at `Ctx + 240`, readable at `P`, apart from the
accumulator and the working space. -/
structure GhWCall (s : State) (Ctx Y S P : Addr) : Prop where
  reads : Covers [⟨P, 128⟩] (s.rd ++ s.wr)
  yp : (⟨Y, 16⟩ : Region).Disjoint ⟨P, 128⟩
  sp : (⟨S, 256⟩ : Region).Disjoint ⟨P, 128⟩
  repr : Spec.Gcm.Powers8Repr s.mem P (Spec.Gcm.blockAt s.mem (Ctx + BitVec.ofNat 64 240))

section
variable {s : State} {Ctx Y D S P : Addr} {n : Nat} (h : GhCall s (Ctx + BitVec.ofNat 64 240) Y D S n)
  (p : GhWCall s Ctx Y S P) (h5 : s.gpr .x5 = P)
include h p h5

theorem GhWCall.pre : Proof.Gcm.ghashWithAArch64.pre (s.callEntry.withRegions
    [⟨Ctx + BitVec.ofNat 64 240, 16⟩, ⟨D, 16 * n⟩, ⟨P, 128⟩] [⟨Y, 16⟩, ⟨S, 256⟩]) := by
  have hn := toNat_ofNat_lt (show n < 2 ^ 64 by have := h.n_lt; omega)
  simp only [Proof.Gcm.ghashWithAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_mem, State.callEntry_mem, callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3,
    callEntry_x4, callEntry_x5, h.x0, h.x1, h.x2, h.x3, h.x4, h5, hn]
  exact ⟨trivial, trivial, h.hy, h.hs, h.yd, h.ys, p.yp, h.ds, p.sp, p.repr⟩

omit h5 in
theorem GhWCall.covers : Covers ([⟨Ctx + BitVec.ofNat 64 240, 16⟩, ⟨D, 16 * n⟩, ⟨P, 128⟩] ++
    [⟨Y, 16⟩, ⟨S, 256⟩]) (s.rd ++ s.wr) := by
  have sub : Covers [⟨Ctx + BitVec.ofNat 64 240, 16⟩, ⟨D, 16 * n⟩, ⟨Y, 16⟩, ⟨S, 256⟩] (s.rd ++ s.wr) := h.reads
  refine Covers.cons ((Covers.of_mem fun _ hr => ?_).trans sub) (Covers.cons ((Covers.of_mem fun _ hr => ?_).trans sub)
    (Covers.cons p.reads ((Covers.of_mem fun _ hr => ?_).trans sub)))
  all_goals simp_all

theorem gw_call (g : GhashWithImpl) :
    WP isa (.call g.fn.name g.fn.code) s (GhPost s (Ctx + BitVec.ofNat 64 240) Y D S n) := by
  have hn := toNat_ofNat_lt (show n < 2 ^ 64 by have := h.n_lt; omega)
  refine WP.call (k := Proof.Gcm.ghashWithAArch64) g.ok
    (rd := [⟨Ctx + BitVec.ofNat 64 240, 16⟩, ⟨D, 16 * n⟩, ⟨P, 128⟩]) (wr := [⟨Y, 16⟩, ⟨S, 256⟩])
    (GhWCall.pre h p h5) (GhWCall.covers h p) h.writes ?_ g.noFrames
  intro s' hrd hwr hsp hf hsaved _ hpost
  refine ⟨hrd, hwr, hsp, hsaved, hf, ?_⟩
  simp only [Proof.Gcm.ghashWithAArch64, Proof.Gcm.ghashAArch64, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_mem, callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, h.x0, h.x1, h.x2, h.x3, hn]
    at hpost
  exact hpost

end

theorem gw_rel (g : GhashWithImpl) {σ₁ σ₂ : State} {Ctx Y D S P : Addr} {n : Nat}
    (h₁ : GhCall σ₁ (Ctx + BitVec.ofNat 64 240) Y D S n) (p₁ : GhWCall σ₁ Ctx Y S P) (q₁ : σ₁.gpr .x5 = P)
    (h₂ : GhCall σ₂ (Ctx + BitVec.ofNat 64 240) Y D S n) (p₂ : GhWCall σ₂ Ctx Y S P) (q₂ : σ₂.gpr .x5 = P)
    (hsp : σ₁.sp = σ₂.sp) :
    RelCT isa (fun a b => a = σ₁ ∧ b = σ₂) (.call g.fn.name g.fn.code) fun _ _ => True := by
  refine RelCT.call g.ok g.ct [⟨Ctx + BitVec.ofNat 64 240, 16⟩, ⟨D, 16 * n⟩, ⟨P, 128⟩] [⟨Y, 16⟩, ⟨S, 256⟩]
    fun a b hab => ?_
  obtain ⟨rfl, rfl⟩ := hab
  refine ⟨GhWCall.pre h₁ p₁ q₁, GhWCall.pre h₂ p₂ q₂, ?_, GhWCall.covers h₁ p₁, h₁.writes,
    GhWCall.covers h₂ p₂, h₂.writes⟩
  simp only [Proof.Gcm.ghashWithAArch64, Proof.Gcm.ghashAArch64, State.withRegions_gpr, State.withRegions_sp,
    State.callEntry_sp, callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, callEntry_x4, callEntry_x5,
    h₁.x0, h₁.x1, h₁.x2, h₁.x3, h₁.x4, h₂.x0, h₂.x1, h₂.x2, h₂.x3, h₂.x4, q₁, q₂, hsp]
  exact ⟨⟨trivial, trivial, trivial, trivial, trivial, trivial⟩, trivial⟩

/-! ## The call with `pw` from the stack -/

/-- `ldr x5, [sp, #k]` keeps a call's arguments and the facts about them. -/
theorem pwLoad_ok {s : State} {Ctx Y D S P : Addr} {n k : Nat} (hk : k % 8 = 0 ∧ k < 32768)
    (hP : s.mem.readW (s.sp + BitVec.ofNat 64 k) 64 = P) (hsp : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 k) 8)
    (h : GhCall s (Ctx + BitVec.ofNat 64 240) Y D S n) (p : GhWCall s Ctx Y S P) :
    ∃ s₁, runBlock isa [.ldrSp .x5 k] s = some s₁ ∧ s₁.gpr .x5 = P ∧
      GhCall s₁ (Ctx + BitVec.ofNat 64 240) Y D S n ∧ GhWCall s₁ Ctx Y S P ∧
      (∀ r, r ≠ .x5 → s₁.gpr r = s.gpr r) ∧ s₁.sp = s.sp ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  obtain ⟨s₁, run, x5, g, sp, m, rd, wr⟩ := ldrSp_ok (t := .x5) hk hP hsp
  refine ⟨s₁, run, x5, ⟨?_, ?_, ?_, ?_, ?_, h.n_lt, h.hy, h.hs, h.yd, h.ys, h.ds, ?_, ?_⟩,
    ⟨?_, p.yp, p.sp, ?_⟩, g, sp, m, rd, wr⟩
  · rw [g _ (by decide)]; exact h.x0
  · rw [g _ (by decide)]; exact h.x1
  · rw [g _ (by decide)]; exact h.x2
  · rw [g _ (by decide)]; exact h.x3
  · rw [g _ (by decide)]; exact h.x4
  · rw [rd, wr]; exact h.reads
  · rw [wr]; exact h.writes
  · rw [rd, wr]; exact p.reads
  · rw [m]; exact p.repr

/-- `Fast.pwCall k g`: `pw` loaded from `sp + k`, then the call, which hashes
as `vg_ghash`. -/
theorem pw_call (g : GhashWithImpl) {s : State} {Ctx Y D S P : Addr} {n k : Nat} (hk : k % 8 = 0 ∧ k < 32768)
    (hP : s.mem.readW (s.sp + BitVec.ofNat 64 k) 64 = P) (hsp : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 k) 8)
    (h : GhCall s (Ctx + BitVec.ofNat 64 240) Y D S n) (p : GhWCall s Ctx Y S P) :
    WP isa (Impl.AesGcm.AArch64.Fast.pwCall k g.fn) s (GhPost s (Ctx + BitVec.ofNat 64 240) Y D S n) := by
  obtain ⟨s₁, run, x5, h₁, p₁, g₁, sp, m, rd, wr⟩ := pwLoad_ok hk hP hsp h p
  refine WP.seq (WP.of_runBlock ⟨s₁, run, WP.mono (gw_call h₁ p₁ x5 g) fun s' q => ?_⟩)
  obtain ⟨qrd, qwr, qsp, qsv, qf, qout⟩ := q
  refine ⟨qrd.trans rd, qwr.trans wr, qsp.trans sp, fun r hr h30 => ?_, by rw [← m]; exact qf, ?_⟩
  · rw [qsv r hr h30, g₁ r (by intro e; subst e; simp [preserved] at hr)]
  · rw [qout, m]

/-- `Fast.pwCall k g` in two runs, with the same public arguments. -/
theorem pw_rel (g : GhashWithImpl) {σ₁ σ₂ : State} {Ctx Y D S P : Addr} {n k : Nat} (hk : k = 8 ∨ k = 16)
    (hP₁ : σ₁.mem.readW (σ₁.sp + BitVec.ofNat 64 k) 64 = P) (hsp₁ : InRegions (σ₁.rd ++ σ₁.wr) (σ₁.sp + BitVec.ofNat 64 k) 8)
    (hP₂ : σ₂.mem.readW (σ₂.sp + BitVec.ofNat 64 k) 64 = P) (hsp₂ : InRegions (σ₂.rd ++ σ₂.wr) (σ₂.sp + BitVec.ofNat 64 k) 8)
    (h₁ : GhCall σ₁ (Ctx + BitVec.ofNat 64 240) Y D S n) (p₁ : GhWCall σ₁ Ctx Y S P)
    (h₂ : GhCall σ₂ (Ctx + BitVec.ofNat 64 240) Y D S n) (p₂ : GhWCall σ₂ Ctx Y S P) (qsp : σ₁.sp = σ₂.sp) :
    RelCT isa (Eq2 σ₁ σ₂) (Impl.AesGcm.AArch64.Fast.pwCall k g.fn) TT := by
  have hk' : k % 8 = 0 ∧ k < 32768 := by rcases hk with rfl | rfl <;> decide
  have t : ∃ h, (taint.check (Taint.ofRegs []) (.block [.ldrSp .x5 k]) h).isSome = true := by
    rcases hk with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  obtain ⟨s₁, run₁, x5₁, c₁, w₁, -, sp₁, -, -, -⟩ := pwLoad_ok hk' hP₁ hsp₁ h₁ p₁
  obtain ⟨s₂, run₂, x5₂, c₂, w₂, -, sp₂, -, -, -⟩ := pwLoad_ok hk' hP₂ hsp₂ h₂ p₂
  refine rel_seq (rel_taint [] qsp (by agree_tac []) t) (F₁ := fun u => u = s₁) (F₂ := fun u => u = s₂)
    (WP.of_runBlock ⟨s₁, run₁, rfl⟩) (WP.of_runBlock ⟨s₂, run₂, rfl⟩) fun τ₁ τ₂ e₁ e₂ => ?_
  subst e₁ e₂
  exact gw_rel g c₁ w₁ x5₁ c₂ w₂ x5₂ (by rw [sp₁, sp₂, qsp])

/-! ## `vg_ghash` for at most one block, else the call with `pw` -/

/-- `lsr x9, x3, #1`, with `n` blocks in `x3`. -/
theorem selLsr_ok {s : State} {n : Nat} (h3 : s.gpr .x3 = BitVec.ofNat 64 n) (hn : n < 2 ^ 64) :
    ∃ s₁, runBlock isa [.lsr .x .x9 .x3 1] s = some s₁ ∧ s₁.gpr .x9 = BitVec.ofNat 64 (n / 2 ^ 1) ∧
      Others [.x9] s s₁ ∧ s₁.mem = s.mem ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  refine ⟨_, by arun [], ?_⟩
  exact ⟨by simp [RegUpd.gpr_write, h3, lsr_ofNat n 1 hn], by others_tac, rfl, rfl, rfl, rfl⟩

theorem GhCall.of_x9 {s s₁ : State} {H Y D S : Addr} {n : Nat} (h : GhCall s H Y D S n)
    (o : Others [.x9] s s₁) (rd : s₁.rd = s.rd) (wr : s₁.wr = s.wr) : GhCall s₁ H Y D S n :=
  ⟨(o _ (by decide)).trans h.x0, (o _ (by decide)).trans h.x1, (o _ (by decide)).trans h.x2,
    (o _ (by decide)).trans h.x3, (o _ (by decide)).trans h.x4, h.n_lt, h.hy, h.hs, h.yd, h.ys, h.ds,
    by rw [rd, wr]; exact h.reads, by rw [wr]; exact h.writes⟩

theorem GhWCall.of_x9 {s s₁ : State} {Ctx Y S P : Addr} (p : GhWCall s Ctx Y S P) (m : s₁.mem = s.mem)
    (rd : s₁.rd = s.rd) (wr : s₁.wr = s.wr) : GhWCall s₁ Ctx Y S P :=
  ⟨by rw [rd, wr]; exact p.reads, p.yp, p.sp, by rw [m]; exact p.repr⟩

theorem GhPost.of_x9 {s s₁ s' : State} {H Y D S : Addr} {n : Nat} (q : GhPost s₁ H Y D S n s')
    (o : Others [.x9] s s₁) (m : s₁.mem = s.mem) (sp : s₁.sp = s.sp) (rd : s₁.rd = s.rd) (wr : s₁.wr = s.wr) :
    GhPost s H Y D S n s' :=
  ⟨q.rd.trans rd, q.wr.trans wr, q.sp.trans sp, fun r hr h30 => by
    rw [q.saved r hr h30, o r (by simp only [List.mem_singleton]; rintro rfl; simp [preserved] at hr)],
    by rw [← m]; exact q.frame, by rw [q.out, m]⟩

/-- `Fast.pwSel k g`: `vg_ghash` for at most one block, else `pw` loaded
from `sp + k` and the call of `g`; either hashes as `vg_ghash`. -/
theorem pwSel_call (v : GcmImpl) (g : GhashWithImpl) {s : State} {Ctx Y D S P : Addr} {n k : Nat}
    (hk : k % 8 = 0 ∧ k < 32768) (hP : s.mem.readW (s.sp + BitVec.ofNat 64 k) 64 = P)
    (hsp : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 k) 8)
    (h : GhCall s (Ctx + BitVec.ofNat 64 240) Y D S n) (p : GhWCall s Ctx Y S P) :
    WP isa (Impl.AesGcm.AArch64.Fast.pwSel v.callees k g.fn) s (GhPost s (Ctx + BitVec.ofNat 64 240) Y D S n) := by
  have hn : n < 2 ^ 64 := by have := h.n_lt; omega
  obtain ⟨s₁, run, x9, o, m, sp, rd, wr⟩ := selLsr_ok h.x3 hn
  have h₁ := h.of_x9 o rd wr
  refine WP.seq (WP.of_runBlock ⟨s₁, run, ?_⟩)
  refine WP.ite _ (eval_zero x9 (by omega)) (fun _ => ?_) (fun _ => ?_)
  · exact WP.mono (gh_call v.gh h₁) fun _ q => q.of_x9 o m sp rd wr
  · exact WP.mono (pw_call g hk (by rw [sp, m]; exact hP) (by rw [rd, wr, sp]; exact hsp) h₁ (p.of_x9 m rd wr))
      fun _ q => q.of_x9 o m sp rd wr

/-- `Fast.pwSel k g` in two runs, with the same public arguments. -/
theorem pwSel_rel (v : GcmImpl) (g : GhashWithImpl) {σ₁ σ₂ : State} {Ctx Y D S P : Addr} {n k : Nat}
    (hk : k = 8 ∨ k = 16)
    (hP₁ : σ₁.mem.readW (σ₁.sp + BitVec.ofNat 64 k) 64 = P) (hsp₁ : InRegions (σ₁.rd ++ σ₁.wr) (σ₁.sp + BitVec.ofNat 64 k) 8)
    (hP₂ : σ₂.mem.readW (σ₂.sp + BitVec.ofNat 64 k) 64 = P) (hsp₂ : InRegions (σ₂.rd ++ σ₂.wr) (σ₂.sp + BitVec.ofNat 64 k) 8)
    (h₁ : GhCall σ₁ (Ctx + BitVec.ofNat 64 240) Y D S n) (p₁ : GhWCall σ₁ Ctx Y S P)
    (h₂ : GhCall σ₂ (Ctx + BitVec.ofNat 64 240) Y D S n) (p₂ : GhWCall σ₂ Ctx Y S P) (qsp : σ₁.sp = σ₂.sp) :
    RelCT isa (Eq2 σ₁ σ₂) (Impl.AesGcm.AArch64.Fast.pwSel v.callees k g.fn) TT := by
  have hn : n < 2 ^ 64 := by have := h₁.n_lt; omega
  obtain ⟨s₁, run₁, x9₁, o₁, m₁, sp₁, rd₁, wr₁⟩ := selLsr_ok h₁.x3 hn
  obtain ⟨s₂, run₂, x9₂, o₂, m₂, sp₂, rd₂, wr₂⟩ := selLsr_ok h₂.x3 hn
  have t : ∃ h, (taint.check (Taint.ofRegs [.x3]) (.block [.lsr .x .x9 .x3 1]) h).isSome = true :=
    ⟨_, by taint_decide⟩
  refine rel_seq (rel_taint [.x3] qsp (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.x3, h₂.x3]) t)
    (F₁ := fun u => u = s₁) (F₂ := fun u => u = s₂)
    (WP.of_runBlock ⟨s₁, run₁, rfl⟩) (WP.of_runBlock ⟨s₂, run₂, rfl⟩) fun τ₁ τ₂ e₁ e₂ => ?_
  subst e₁ e₂
  have c₁ := h₁.of_x9 o₁ rd₁ wr₁
  have c₂ := h₂.of_x9 o₂ rd₂ wr₂
  have q : τ₁.sp = τ₂.sp := by rw [sp₁, sp₂, qsp]
  refine rel_ite (eval_zero x9₁ (by omega)) (eval_zero x9₂ (by omega)) (fun _ => ?_) (fun _ => ?_)
  · exact gh_rel v.gh fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨_, Y, D, S, n, c₁, c₂, q⟩
  · exact pw_rel g hk (by rw [sp₁, m₁]; exact hP₁) (by rw [rd₁, wr₁, sp₁]; exact hsp₁)
      (by rw [sp₂, m₂]; exact hP₂) (by rw [rd₂, wr₂, sp₂]; exact hsp₂) c₁ (p₁.of_x9 m₁ rd₁ wr₁) c₂
      (p₂.of_x9 m₂ rd₂ wr₂) q

/-- Every instruction of `Fast.pwSel k g` keeps the vector registers the ABI
preserves, if `vg_ghash`'s and `g`'s do. -/
theorem pwSel_keepsV (v : GcmImpl) (g : GhashWithImpl) {k : Nat} (hk : k = 8 ∨ k = 16) :
    (Impl.AesGcm.AArch64.Fast.pwSel v.callees k g.fn).allInstrs keepsV = true := by
  rcases hk with rfl | rfl <;>
  simp only [Impl.AesGcm.AArch64.Fast.pwSel, Impl.AesGcm.AArch64.Fast.pwCall, Code.allInstrs, GcmImpl.callees,
    v.gh.keepsV, g.keepsV, Bool.and_true] <;> decide

/-! ## `vg_ghash_store_powers`, called with `pw` from the stack -/

/-- What a call of `vg_ghash_store_powers` needs besides `GhCall`: the
powers' buffer at `P`, writable, apart from the hash subkey, the
accumulator, the data and the working space. -/
structure GhSCall (s : State) (Ctx Y D S P : Addr) (n : Nat) : Prop where
  writes : Covers [⟨P, 128⟩] s.wr
  hp : (⟨Ctx + BitVec.ofNat 64 240, 16⟩ : Region).Disjoint ⟨P, 128⟩
  yp : (⟨Y, 16⟩ : Region).Disjoint ⟨P, 128⟩
  dp : (⟨D, 16 * n⟩ : Region).Disjoint ⟨P, 128⟩
  sp : (⟨S, 256⟩ : Region).Disjoint ⟨P, 128⟩

section
variable {s : State} {Ctx Y D S P : Addr} {n : Nat} (h : GhCall s (Ctx + BitVec.ofNat 64 240) Y D S n)
  (p : GhSCall s Ctx Y D S P n) (h5 : s.gpr .x5 = P)
include h p h5

theorem GhSCall.pre : Proof.Gcm.ghashStoreAArch64.pre (s.callEntry.withRegions
    [⟨Ctx + BitVec.ofNat 64 240, 16⟩, ⟨D, 16 * n⟩] [⟨Y, 16⟩, ⟨S, 256⟩, ⟨P, 128⟩]) := by
  have hn := toNat_ofNat_lt (show n < 2 ^ 64 by have := h.n_lt; omega)
  simp only [Proof.Gcm.ghashStoreAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, callEntry_x4, callEntry_x5, h.x0, h.x1, h.x2, h.x3,
    h.x4, h5, hn]
  exact ⟨trivial, trivial, h.hy, h.hs, p.hp, h.yd, h.ys, p.yp, h.ds, p.dp, p.sp⟩

omit h5 in
theorem GhSCall.covers : Covers ([⟨Ctx + BitVec.ofNat 64 240, 16⟩, ⟨D, 16 * n⟩] ++
    [⟨Y, 16⟩, ⟨S, 256⟩, ⟨P, 128⟩]) (s.rd ++ s.wr) := by
  have sub : Covers [⟨Ctx + BitVec.ofNat 64 240, 16⟩, ⟨D, 16 * n⟩, ⟨Y, 16⟩, ⟨S, 256⟩] (s.rd ++ s.wr) := h.reads
  refine Covers.cons ((Covers.of_mem fun _ hr => ?_).trans sub) (Covers.cons ((Covers.of_mem fun _ hr => ?_).trans sub)
    (Covers.cons ((Covers.of_mem fun _ hr => ?_).trans sub) (Covers.cons ((Covers.of_mem fun _ hr => ?_).trans sub)
      (Covers.right p.writes))))
  all_goals simp_all

omit h5 in
theorem GhSCall.writes' : Covers [⟨Y, 16⟩, ⟨S, 256⟩, ⟨P, 128⟩] s.wr := by
  have sub : Covers [⟨Y, 16⟩, ⟨S, 256⟩] s.wr := h.writes
  refine Covers.cons ((Covers.of_mem fun _ hr => ?_).trans sub) (Covers.cons ((Covers.of_mem fun _ hr => ?_).trans sub)
    p.writes)
  all_goals simp_all

theorem gs_call (g : GhashStoreImpl) :
    WP isa (.call g.fn.name g.fn.code) s fun t => GhPost s (Ctx + BitVec.ofNat 64 240) Y D S n t [⟨P, 128⟩] ∧
      Spec.Gcm.Powers8Repr t.mem P (Spec.Gcm.blockAt s.mem (Ctx + BitVec.ofNat 64 240)) := by
  have hn := toNat_ofNat_lt (show n < 2 ^ 64 by have := h.n_lt; omega)
  refine WP.call (k := Proof.Gcm.ghashStoreAArch64) g.ok
    (rd := [⟨Ctx + BitVec.ofNat 64 240, 16⟩, ⟨D, 16 * n⟩]) (wr := [⟨Y, 16⟩, ⟨S, 256⟩, ⟨P, 128⟩])
    (GhSCall.pre h p h5) (GhSCall.covers h p) (GhSCall.writes' h p) ?_ g.noFrames
  intro s' hrd hwr hsp hf hsaved _ hpost
  simp only [Proof.Gcm.ghashStoreAArch64, Proof.Gcm.ghashAArch64, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_mem, callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, callEntry_x5, h.x0, h.x1, h.x2,
    h.x3, h5, hn] at hpost
  exact ⟨⟨hrd, hwr, hsp, hsaved, hf, hpost.1⟩, hpost.2⟩

end

theorem gs_rel (g : GhashStoreImpl) {σ₁ σ₂ : State} {Ctx Y D S P : Addr} {n : Nat}
    (h₁ : GhCall σ₁ (Ctx + BitVec.ofNat 64 240) Y D S n) (p₁ : GhSCall σ₁ Ctx Y D S P n) (q₁ : σ₁.gpr .x5 = P)
    (h₂ : GhCall σ₂ (Ctx + BitVec.ofNat 64 240) Y D S n) (p₂ : GhSCall σ₂ Ctx Y D S P n) (q₂ : σ₂.gpr .x5 = P)
    (hsp : σ₁.sp = σ₂.sp) :
    RelCT isa (fun a b => a = σ₁ ∧ b = σ₂) (.call g.fn.name g.fn.code) fun _ _ => True := by
  refine RelCT.call g.ok g.ct [⟨Ctx + BitVec.ofNat 64 240, 16⟩, ⟨D, 16 * n⟩] [⟨Y, 16⟩, ⟨S, 256⟩, ⟨P, 128⟩]
    fun a b hab => ?_
  obtain ⟨rfl, rfl⟩ := hab
  refine ⟨GhSCall.pre h₁ p₁ q₁, GhSCall.pre h₂ p₂ q₂, ?_, GhSCall.covers h₁ p₁, GhSCall.writes' h₁ p₁,
    GhSCall.covers h₂ p₂, GhSCall.writes' h₂ p₂⟩
  simp only [Proof.Gcm.ghashStoreAArch64, Proof.Gcm.ghashAArch64, State.withRegions_gpr, State.withRegions_sp,
    State.callEntry_sp, callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, callEntry_x4, callEntry_x5,
    h₁.x0, h₁.x1, h₁.x2, h₁.x3, h₁.x4, h₂.x0, h₂.x1, h₂.x2, h₂.x3, h₂.x4, q₁, q₂, hsp]
  exact ⟨⟨trivial, trivial, trivial, trivial, trivial, trivial⟩, trivial⟩

/-- `ldr x5, [sp, #k]` keeps a store call's arguments and the facts about them. -/
theorem pwLoadS_ok {s : State} {Ctx Y D S P : Addr} {n k : Nat} (hk : k % 8 = 0 ∧ k < 32768)
    (hP : s.mem.readW (s.sp + BitVec.ofNat 64 k) 64 = P) (hsp : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 k) 8)
    (h : GhCall s (Ctx + BitVec.ofNat 64 240) Y D S n) (p : GhSCall s Ctx Y D S P n) :
    ∃ s₁, runBlock isa [.ldrSp .x5 k] s = some s₁ ∧ s₁.gpr .x5 = P ∧
      GhCall s₁ (Ctx + BitVec.ofNat 64 240) Y D S n ∧ GhSCall s₁ Ctx Y D S P n ∧
      (∀ r, r ≠ .x5 → s₁.gpr r = s.gpr r) ∧ s₁.sp = s.sp ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  obtain ⟨s₁, run, x5, g, sp, m, rd, wr⟩ := ldrSp_ok (t := .x5) hk hP hsp
  refine ⟨s₁, run, x5, ⟨?_, ?_, ?_, ?_, ?_, h.n_lt, h.hy, h.hs, h.yd, h.ys, h.ds, ?_, ?_⟩,
    ⟨?_, p.hp, p.yp, p.dp, p.sp⟩, g, sp, m, rd, wr⟩
  · rw [g _ (by decide)]; exact h.x0
  · rw [g _ (by decide)]; exact h.x1
  · rw [g _ (by decide)]; exact h.x2
  · rw [g _ (by decide)]; exact h.x3
  · rw [g _ (by decide)]; exact h.x4
  · rw [rd, wr]; exact h.reads
  · rw [wr]; exact h.writes
  · rw [wr]; exact p.writes

/-- `Fast.pwCall k g`, for `vg_ghash_store_powers`: `pw` loaded from
`sp + k`, then the call, which hashes as `vg_ghash` and stores the powers. -/
theorem pwS_call (g : GhashStoreImpl) {s : State} {Ctx Y D S P : Addr} {n k : Nat} (hk : k % 8 = 0 ∧ k < 32768)
    (hP : s.mem.readW (s.sp + BitVec.ofNat 64 k) 64 = P) (hsp : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 k) 8)
    (h : GhCall s (Ctx + BitVec.ofNat 64 240) Y D S n) (p : GhSCall s Ctx Y D S P n) :
    WP isa (Impl.AesGcm.AArch64.Fast.pwCall k g.fn) s fun t =>
      GhPost s (Ctx + BitVec.ofNat 64 240) Y D S n t [⟨P, 128⟩] ∧
        Spec.Gcm.Powers8Repr t.mem P (Spec.Gcm.blockAt s.mem (Ctx + BitVec.ofNat 64 240)) := by
  obtain ⟨s₁, run, x5, h₁, p₁, g₁, sp, m, rd, wr⟩ := pwLoadS_ok hk hP hsp h p
  refine WP.seq (WP.of_runBlock ⟨s₁, run, WP.mono (gs_call h₁ p₁ x5 g) fun s' ⟨q, pw⟩ => ?_⟩)
  obtain ⟨qrd, qwr, qsp, qsv, qf, qout⟩ := q
  refine ⟨⟨qrd.trans rd, qwr.trans wr, qsp.trans sp, fun r hr h30 => ?_, by rw [← m]; exact qf, ?_⟩, by rw [← m]; exact pw⟩
  · rw [qsv r hr h30, g₁ r (by intro e; subst e; simp [preserved] at hr)]
  · rw [qout, m]

/-- `Fast.pwCall k g`, for `vg_ghash_store_powers`, in two runs, with the
same public arguments. -/
theorem pwS_rel (g : GhashStoreImpl) {σ₁ σ₂ : State} {Ctx Y D S P : Addr} {n k : Nat} (hk : k = 8 ∨ k = 16)
    (hP₁ : σ₁.mem.readW (σ₁.sp + BitVec.ofNat 64 k) 64 = P) (hsp₁ : InRegions (σ₁.rd ++ σ₁.wr) (σ₁.sp + BitVec.ofNat 64 k) 8)
    (hP₂ : σ₂.mem.readW (σ₂.sp + BitVec.ofNat 64 k) 64 = P) (hsp₂ : InRegions (σ₂.rd ++ σ₂.wr) (σ₂.sp + BitVec.ofNat 64 k) 8)
    (h₁ : GhCall σ₁ (Ctx + BitVec.ofNat 64 240) Y D S n) (p₁ : GhSCall σ₁ Ctx Y D S P n)
    (h₂ : GhCall σ₂ (Ctx + BitVec.ofNat 64 240) Y D S n) (p₂ : GhSCall σ₂ Ctx Y D S P n) (qsp : σ₁.sp = σ₂.sp) :
    RelCT isa (Eq2 σ₁ σ₂) (Impl.AesGcm.AArch64.Fast.pwCall k g.fn) TT := by
  have hk' : k % 8 = 0 ∧ k < 32768 := by rcases hk with rfl | rfl <;> decide
  have t : ∃ h, (taint.check (Taint.ofRegs []) (.block [.ldrSp .x5 k]) h).isSome = true := by
    rcases hk with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  obtain ⟨s₁, run₁, x5₁, c₁, w₁, -, sp₁, -, -, -⟩ := pwLoadS_ok hk' hP₁ hsp₁ h₁ p₁
  obtain ⟨s₂, run₂, x5₂, c₂, w₂, -, sp₂, -, -, -⟩ := pwLoadS_ok hk' hP₂ hsp₂ h₂ p₂
  refine rel_seq (rel_taint [] qsp (by agree_tac []) t) (F₁ := fun u => u = s₁) (F₂ := fun u => u = s₂)
    (WP.of_runBlock ⟨s₁, run₁, rfl⟩) (WP.of_runBlock ⟨s₂, run₂, rfl⟩) fun τ₁ τ₂ e₁ e₂ => ?_
  subst e₁ e₂
  exact gs_rel g c₁ w₁ x5₁ c₂ w₂ x5₂ (by rw [sp₁, sp₂, qsp])

end VG.Proof.AesGcm.AArch64
