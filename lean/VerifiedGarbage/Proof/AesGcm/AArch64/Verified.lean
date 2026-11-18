module

public import VerifiedGarbage.Proof.AesGcm.Rounds
public import Mathlib.Data.List.Dedup
import VerifiedGarbage.Proof.AesGcm.AArch64.Init
import VerifiedGarbage.Proof.AesGcm.AArch64.StreamCryptCT
import VerifiedGarbage.Proof.AesGcm.AArch64.SealCT
import VerifiedGarbage.Proof.AesGcm.AArch64.OpenCT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.AesGcm.Scratch
public import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
public import VerifiedGarbage.Proof.AesGcm.AArch64.Contract
import VerifiedGarbage.Proof.AesGcm.AArch64.Seal
import VerifiedGarbage.Proof.AesGcm.AArch64.StreamVerify
import VerifiedGarbage.Proof.AesGcm.AArch64.StreamFinish
import VerifiedGarbage.Proof.AesGcm.AArch64.StreamInit
import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
import VerifiedGarbage.Proof.AesGcm.AArch64.Env
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Contract
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Init
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Env
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.AesGcm.AArch64.PieceCT
import VerifiedGarbage.Proof.AesGcm.AArch64.Fn
meta import VerifiedGarbage.Proof.AesGcm.AArch64.StreamInit
meta import VerifiedGarbage.Proof.AesGcm.AArch64.PieceCT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Fn
public import VerifiedGarbage.Proof.AesGcm.AArch64.Absorb
public import VerifiedGarbage.Proof.AesGcm.AArch64.Save
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Absorb
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Save

/-! ### `AesGcm.AArch64.StreamAadCT`, which only this module used -/

section

/-! ### `AesGcm.AArch64.StreamAad`, which this module and modules that import it used -/

section

/-!
# AES-GCM on AArch64: `vg_aes_gcm_stream_aad`

Untrusted: everything here is checked by Lean. The entry saves our caller's
registers and sets up `absorb`'s arguments, with `aad_len mod 16` bytes
buffered (`aadEntry_ok`); `absorb` takes the data into GHASH and touches
nothing else of the state (`aad_run`), for any additional data so far of
that length (`WP.forall_det`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom StreamRepr)
open VG.Proof.Gcm (Absorbed Ctr)

/-- After the entry: `absorb`'s arguments. -/
theorem aadEntry_ok {s : State} {Ctx St D W : Addr} {n : Nat} (hCtx : s.gpr .x0 = Ctx) (hSt : s.gpr .x1 = St)
    (hD : s.gpr .x3 = D) (hn : (s.gpr .x4).toNat = n) (hW : s.gpr .x5 = W) (hperm : Perm Ctx St W s) :
    WP isa (.block aadEntry) s fun s' => Env Ctx St W s.sp s' ∧ Kept s'.gpr s' ∧
      s'.gpr .x23 = D ∧ s'.gpr .x24 = BitVec.ofNat 64 n ∧
      s'.gpr .x25 = BitVec.ofNat 64 ((s.gpr .x2).toNat % 16) ∧ s'.mem = savedMem s.mem W s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, g₁, sp₁, rd₁, wr₁, m₁⟩ := save_ok s .x5 hW hperm.w
  have hn' : s.gpr .x4 = BitVec.ofNat 64 n := by rw [← hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain ⟨s₂, run₂, x19₂, x20₂, x21₂, x23₂, x24₂, x25₂, sp₂, m₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [mov .x19 .x5, mov .x20 .x1, mov .x21 .x0, mov .x23 .x3, mov .x24 .x4, imm .x9 15,
        .logic .and .x .x25 .x2 .x9] s₁ = some s₂ ∧
      s₂.gpr .x19 = W ∧ s₂.gpr .x20 = St ∧ s₂.gpr .x21 = Ctx ∧ s₂.gpr .x23 = D ∧
      s₂.gpr .x24 = BitVec.ofNat 64 n ∧ s₂.gpr .x25 = BitVec.ofNat 64 ((s.gpr .x2).toNat % 16) ∧
      s₂.sp = s₁.sp ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
    · simp [gpr_write, g₁, hW]
    · simp [gpr_write, g₁, hSt]
    · simp [gpr_write, g₁, hCtx]
    · simp [gpr_write, g₁, hD]
    · simp [gpr_write, g₁, hn']
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, g₁, BitVec.setWidth_eq]
      rw [show BitVec.setWidth 64 (15#16) <<< (16 * 0) = BitVec.ofNat 64 15 by decide, and15]
  refine WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩)
  exact ⟨⟨x19₂, x20₂, x21₂, by rw [sp₂, sp₁], hperm.of_eq (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])⟩,
    fun _ _ => rfl, x23₂, x24₂, x25₂, by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩

/-- The regions `stream_aad` writes. -/
abbrev aadFrame (St W : Addr) : List Region := savedR W :: absFrame St W 16

/-- One run of `stream_aad`, for additional data `x` so far of `o` bytes modulo 16. -/
theorem aad_run (v : GcmImpl) {s : State} (hs : streamAadAArch64.pre s) {x : List Byte}
    (hx : x.length % 16 = (s.gpr .x2).toNat % 16) :
    WP isa (streamAad v.callees) s fun s' => GprAbi s s' ∧
      (Absorbed s.mem (s.gpr .x1 + BitVec.ofNat 64 16) (s.gpr .x1 + BitVec.ofNat 64 32)
          (Spec.Gcm.ctxH s.mem (s.gpr .x0)) x →
        Absorbed s'.mem (s.gpr .x1 + BitVec.ofNat 64 16) (s.gpr .x1 + BitVec.ofNat 64 32)
          (Spec.Gcm.ctxH s.mem (s.gpr .x0)) (x ++ bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat)) ∧
      Frame (aadFrame (s.gpr .x1) (s.gpr .x5)) s.mem s'.mem := by
  simp only [streamAadAArch64] at hs
  obtain ⟨hrd, hwr, dcs, dcw, dds, ddw, dsw, wc, wd, ws, ww⟩ := hs
  generalize hCtx : s.gpr .x0 = Ctx at *
  generalize hSt : s.gpr .x1 = St at *
  generalize hD : s.gpr .x3 = D at *
  generalize hn : (s.gpr .x4).toNat = n at *
  generalize hW : s.gpr .x5 = W at *
  have L : Lay Ctx St W := Lay.of wc ws ww dcs dcw dsw
  have perm : Perm Ctx St W s :=
    ⟨covers_mem (by rw [hrd, hwr]; simp), covers_of_mem (by rw [hwr]; simp), covers_of_mem (by rw [hwr]; simp)⟩
  have hlt : n < 2 ^ 64 := hn ▸ (s.gpr .x4).isLt
  refine WP.seq (WP.mono (aadEntry_ok hCtx hSt hD hn hW perm)
    fun s₁ ⟨he₁, hk₁, x23₁, x24₁, x25₁, m₁, rd₁, wr₁⟩ => ?_)
  have fsv : Frame [savedR W] s.mem s₁.mem := by rw [m₁]; exact savedMem_frame _ _ _
  have sW : Region.Sub (savedR W) ⟨W, 2560⟩ := Lay.wSub (by decide)
  have hdat : bytesAt s₁.mem D n = bytesAt s.mem D n :=
    bytesAt_frame fsv (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ddw.sub_right sW) (by omega_using [hn])
  have hH : blockAt s₁.mem (Ctx + BitVec.ofNat 64 240) = Spec.Gcm.ctxH s.mem Ctx :=
    blockAt_frame fsv (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (dcw.sub_left (Lay.ctxSub (by decide))).sub_right sW)
  have dS : ∀ (d k : Nat), d + k ≤ 80 → (⟨St + BitVec.ofNat 64 d, k⟩ : Region).Disjoint (savedR W) :=
    fun d k h => L.st_w h (.inr ⟨by decide, by decide⟩)
  have hA : ∀ (m : Mem), Frame [savedR W] s.mem m →
      Absorbed s.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) (Spec.Gcm.ctxH s.mem Ctx) x →
      Absorbed m (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) (Spec.Gcm.ctxH s.mem Ctx) x :=
    fun m hf ha => ha.congr (blockAt_frame hf fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dS 16 16 (by decide))
      (bytesAt_frame hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (dS 32 16 (by decide)).sub_left (Region.sub_prefix (Nat.le_of_lt (Nat.mod_lt _ (by decide)))))
        (by omega_using []))
  have hIn : AbsIn Ctx St W s.sp s₁.gpr (Spec.Gcm.ctxH s.mem Ctx) x D n ((s.gpr .x2).toNat % 16) s₁ :=
    ⟨he₁, hk₁, x23₁, x24₁, x25₁, hx, ⟨covers_mem (by rw [rd₁, wr₁, hrd]; simp), hlt, wd, dds, ddw⟩, hH⟩
  refine WP.seq (WP.mono (absorb_ok L (.inr rfl) v hIn) fun s₂ h₂ => ?_)
  have hsv : SavedAt s₂.mem W s := by
    have := savedAt_save s.mem W s
    rw [← m₁] at this
    exact this.frame h₂.frame (saved_absFrame L (.inr rfl))
  refine WP.mono (exit_ok h₂.env.x19 h₂.env.sp (covers_left h₂.env.perm.w) hsv) fun s' ⟨ga, hm, _⟩ =>
    ⟨ga, fun ha => ?_, ?_⟩
  · rw [hm, ← hdat]; exact h₂.abs (hA _ fsv ha)
  · rw [hm]
    exact (fsv.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩).trans
      (h₂.frame.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)

theorem streamAad_wp (v : GcmImpl) {s : State} (hs : streamAadAArch64.pre s) :
    WP isa (streamAad v.callees) s fun s' => GprAbi s s' ∧ streamAadAArch64.post s s' := by
  have hz : (Spec.Gcm.zeros ((s.gpr .x2).toNat % 16)).length % 16 = (s.gpr .x2).toNat % 16 := by
    rw [Proof.Gcm.length_zeros, Nat.mod_mod]
  refine WP.mono (WP.forall_det (P := fun (i : (Block → Block) × List Byte × List Byte) =>
      StreamRepr s.mem (s.gpr .x1) i.1 (Spec.Gcm.ctxH s.mem (s.gpr .x0)) i.2.1 i.2.2 [] ∧
        s.gpr .x2 = BitVec.ofNat 64 i.2.2.length)
    (Q := fun i s' => StreamRepr s'.mem (s.gpr .x1) i.1 (Spec.Gcm.ctxH s.mem (s.gpr .x0)) i.2.1
      (i.2.2 ++ bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat) [])
    (aad_run v hs hz) fun ⟨ciph, iv, a⟩ ⟨hr, hl⟩ => ?_) fun s' ⟨⟨ga, _, _⟩, h⟩ =>
      ⟨ga, fun ciph iv a hr hl => h ⟨ciph, iv, a⟩ ⟨hr, hl⟩⟩
  have hx : a.length % 16 = (s.gpr .x2).toNat % 16 := by rw [hl, toNat_mod16]
  obtain ⟨hj, ha, hc⟩ := Proof.Gcm.streamRepr_iff.mp hr
  have hs' := hs
  simp only [streamAadAArch64] at hs'
  obtain ⟨-, -, -, -, -, -, dsw, -, -, ws, ww⟩ := hs'
  have dSt : ∀ r ∈ aadFrame (s.gpr .x1) (s.gpr .x5), ∀ d, d + 16 ≤ 80 → (d + 16 ≤ 16 ∨ 48 ≤ d) →
      (⟨s.gpr .x1 + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := by
    intro r hr d hd hd'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have st_off : ∀ e k, e + k ≤ 80 → (d + 16 ≤ e ∨ e + k ≤ d) →
        (⟨s.gpr .x1 + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint ⟨s.gpr .x1 + BitVec.ofNat 64 e, k⟩ :=
      fun e k he h => Offset.disjoint _ h (by omega_using [hd]) (by omega_using [he])
    rcases hr with rfl | rfl | rfl | rfl
    · exact (dsw.sub_left (Offset.sub_base _ (by omega_using [hd]))).sub_right (Lay.wSub (by decide))
    · exact st_off 16 16 (by decide) (by omega_using [hd'])
    · exact st_off 32 16 (by decide) (by omega_using [hd'])
    · exact (dsw.sub_left (Offset.sub_base _ (by omega_using [hd]))).sub_right (Lay.wSub (by decide))
  refine WP.mono (aad_run v hs hx) fun s' ⟨_, habs, hf⟩ => ?_
  refine Proof.Gcm.streamRepr_iff.mpr ⟨?_, ?_, ?_⟩
  · rw [← hj]
    have := blockAt_frame hf fun r hr => by simpa using dSt r hr 0 (by decide) (.inl (by decide))
    simpa using this
  · exact habs ha
  · refine hc.congr ?_ ?_
    · exact blockAt_frame hf fun r hr => dSt r hr 48 (by decide) (.inr (by decide))
    · exact blockAt_frame hf fun r hr => dSt r hr 64 (by decide) (.inr (by decide))

end VG.Proof.AesGcm.AArch64

end

end

/-!
# AES-GCM on AArch64: `vg_aes_gcm_stream_aad` is constant time

Untrusted: everything here is checked by Lean. The entry and the exit by the
taint analysis, from the public arguments and `W`; `absorb` by `absorb_rel`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

theorem streamAad_ct (v : GcmImpl) :
    ConstantTime isa streamAadAArch64.pre streamAadAArch64.pub (streamAad v.callees) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q0, q1, q2, q3, q4, q5, qsp⟩ := hq
  simp only [streamAadAArch64] at h₁ h₂
  rw [← q0, ← q1, ← q3, ← q4, ← q5] at h₂
  obtain ⟨hrd₁, hwr₁, dcs, dcw, dds, ddw, dsw, wc, wd, ws, ww⟩ := h₁
  obtain ⟨hrd₂, hwr₂, -⟩ := h₂
  generalize hCtx : σ₁.gpr .x0 = Ctx at *
  generalize hSt : σ₁.gpr .x1 = St at *
  generalize hD : σ₁.gpr .x3 = D at *
  generalize hn : (σ₁.gpr .x4).toNat = n at *
  generalize hW : σ₁.gpr .x5 = W at *
  generalize ho : (σ₁.gpr .x2).toNat % 16 = o at *
  have L : Lay Ctx St W := Lay.of wc ws ww dcs dcw dsw
  have hlt : n < 2 ^ 64 := hn ▸ (σ₁.gpr .x4).isLt
  have ho₂ : (σ₂.gpr .x2).toNat % 16 = o := by rw [← q2, ho]
  have perm (σ : State) (hrd : σ.rd = [⟨Ctx, 256⟩, ⟨D, n⟩]) (hwr : σ.wr = [⟨St, 80⟩, ⟨W, 2560⟩]) :
      Perm Ctx St W σ :=
    ⟨covers_mem (by rw [hrd, hwr]; simp), covers_of_mem (by rw [hwr]; simp), covers_of_mem (by rw [hwr]; simp)⟩
  have hz : (Spec.Gcm.zeros o).length % 16 = o := by
    rw [Proof.Gcm.length_zeros]; exact Nat.mod_eq_of_lt (ho ▸ Nat.mod_lt _ (by decide))
  have mk (σ σ' : State) (hrd : σ.rd = [⟨Ctx, 256⟩, ⟨D, n⟩]) (hσ : (σ.gpr .x2).toNat % 16 = o)
      (h : Env Ctx St W σ.sp σ' ∧ Kept σ'.gpr σ' ∧ σ'.gpr .x23 = D ∧ σ'.gpr .x24 = BitVec.ofNat 64 n ∧
        σ'.gpr .x25 = BitVec.ofNat 64 ((σ.gpr .x2).toNat % 16) ∧ σ'.mem = savedMem σ.mem W σ.gpr ∧
        σ'.rd = σ.rd ∧ σ'.wr = σ.wr) :
      AbsIn Ctx St W σ.sp σ'.gpr (blockAt σ'.mem (Ctx + BitVec.ofNat 64 240)) (Spec.Gcm.zeros o) D n o σ' := by
    obtain ⟨he, hk, x23, x24, x25, _, rd, wr⟩ := h
    exact ⟨he, hk, x23, x24, by rw [x25, hσ], hz, ⟨covers_mem (by rw [rd, wr, hrd]; simp), hlt, wd, dds, ddw⟩,
      rfl⟩
  refine rel_seq (rel_taint [.x0, .x1, .x2, .x3, .x4, .x5] qsp
      (by agree_tac [hCtx, hSt, hD, hW, ← q0, ← q1, q2, ← q3, q4, ← q5]) ⟨_, by taint_decide⟩)
    (aadEntry_ok hCtx hSt hD hn hW (perm σ₁ hrd₁ hwr₁))
    (aadEntry_ok q0.symm q1.symm q3.symm (by rw [← q4, hn]) q5.symm (perm σ₂ hrd₂ hwr₂))
    fun τ₁ τ₂ a₁ a₂ => ?_
  have j₁ := mk σ₁ τ₁ hrd₁ ho a₁
  have j₂ := mk σ₂ τ₂ hrd₂ ho₂ a₂
  rw [← qsp] at j₂
  refine rel_seq (absorb_rel L v (.inr rfl) j₁ j₂) (absorb_ok L (.inr rfl) v j₁) (absorb_ok L (.inr rfl) v j₂)
    fun τ₁ τ₂ b₁ b₂ => ?_
  exact rel_taint [.x19] (by rw [b₁.env.sp, b₂.env.sp]) (by agree_tac [b₁.env.x19, b₂.env.x19])
    ⟨_, by taint_decide⟩

end VG.Proof.AesGcm.AArch64

end

end

/-! ### `AesGcm.AArch64.StreamInitCT`, which only this module used -/

section

/-!
# AES-GCM on AArch64: `vg_aes_gcm_stream_init` is constant time

Untrusted: everything here is checked by Lean. The entry and the exit by the
taint analysis, from the public arguments and `W`; `j0` by `j0_rel`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

theorem streamInit_ct (v : GcmImpl) :
    ConstantTime isa streamInitAArch64.pre streamInitAArch64.pub (streamInit v.callees) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q0, q1, q2, q3, q4, qsp⟩ := hq
  simp only [streamInitAArch64] at h₁ h₂
  rw [← q0, ← q1, ← q2, ← q3, ← q4] at h₂
  obtain ⟨hrd₁, hwr₁, dcs, dcw, dns, dnw, dsw, wc, wn, ws, ww⟩ := h₁
  obtain ⟨hrd₂, hwr₂, -⟩ := h₂
  generalize hCtx : σ₁.gpr .x0 = Ctx at *
  generalize hNp : σ₁.gpr .x1 = Np at *
  generalize hn : (σ₁.gpr .x2).toNat = n at *
  generalize hSt : σ₁.gpr .x3 = St at *
  generalize hW : σ₁.gpr .x4 = W at *
  have L : Lay Ctx St W := Lay.of wc ws ww dcs dcw dsw
  have hlt : n < 2 ^ 64 := hn ▸ (σ₁.gpr .x2).isLt
  have perm (σ : State) (hrd : σ.rd = [⟨Ctx, 256⟩, ⟨Np, n⟩]) (hwr : σ.wr = [⟨St, 80⟩, ⟨W, 2560⟩]) :
      Perm Ctx St W σ :=
    ⟨covers_mem (by rw [hrd, hwr]; simp), covers_of_mem (by rw [hwr]; simp), covers_of_mem (by rw [hwr]; simp)⟩
  have mk (σ σ' : State) (hrd : σ.rd = [⟨Ctx, 256⟩, ⟨Np, n⟩])
      (h : Env Ctx St W σ.sp σ' ∧ Kept σ'.gpr σ' ∧ σ'.gpr .x23 = Np ∧ σ'.gpr .x24 = BitVec.ofNat 64 n ∧
        σ'.gpr .x26 = BitVec.ofNat 64 n ∧ σ'.gpr .x27 = 0 ∧ σ'.mem = savedMem σ.mem W σ.gpr ∧ σ'.rd = σ.rd ∧
        σ'.wr = σ.wr) :
      J0In Ctx St W σ.sp σ'.gpr (blockAt σ'.mem (Ctx + BitVec.ofNat 64 240)) Np n σ' := by
    obtain ⟨he, hk, x23, x24, x26, x27, _, rd, wr⟩ := h
    exact ⟨he, hk, x23, x24, x26, x27, ⟨covers_mem (by rw [rd, wr, hrd]; simp), hlt, wn, dns, dnw⟩, rfl⟩
  refine rel_seq (rel_taint [.x0, .x1, .x2, .x3, .x4] qsp
      (by agree_tac [hCtx, hNp, hSt, hW, ← q0, ← q1, q2, ← q3, ← q4]) ⟨_, by taint_decide⟩)
    (siEntry_ok hCtx hNp hn hSt hW (perm σ₁ hrd₁ hwr₁))
    (siEntry_ok q0.symm q1.symm (by rw [← q2, hn]) q3.symm q4.symm
      (perm σ₂ hrd₂ hwr₂))
    fun τ₁ τ₂ a₁ a₂ => ?_
  have j₁ := mk σ₁ τ₁ hrd₁ a₁
  have j₂ := mk σ₂ τ₂ hrd₂ a₂
  rw [← qsp] at j₂
  refine rel_seq (j0_rel L v j₁ j₂) (j0_ok L v j₁) (j0_ok L v j₂) fun τ₁ τ₂ b₁ b₂ => ?_
  exact rel_taint [.x19] (by rw [b₁.env.sp, b₂.env.sp]) (by agree_tac [b₁.env.x19, b₂.env.x19])
    ⟨_, by taint_decide⟩

end VG.Proof.AesGcm.AArch64

end

end

/-! ### `AesGcm.AArch64.InitCT`, which only this module used -/

section

/-!
# AES-GCM on AArch64: `vg_aes_gcm_init` is constant time

Untrusted: everything here is checked by Lean. The code around the calls by
the taint analysis, from the public arguments and the registers the
correctness proof pins (`init1_ok`, `init2_ok`); the calls by their callees'
proofs, with the arguments those proofs give.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- The block before the call of `vg_aes_expand_key_scratch`. -/
theorem init1_ok {cl : Nat} (hcl : 256 ≤ cl) {s : State} {K Ctx W : Addr} {L : Nat} (hK : s.gpr .x0 = K)
    (hLn : (s.gpr .x1).toNat = L) (hCtx : s.gpr .x2 = Ctx) (hW : s.gpr .x3 = W) (hrd : s.rd = [⟨K, L⟩])
    (hwr : s.wr = [⟨Ctx, cl⟩, ⟨W, 2560⟩]) (d_kc : (⟨K, L⟩ : Region).Disjoint ⟨Ctx, cl⟩)
    (d_ks : (⟨K, L⟩ : Region).Disjoint ⟨W, 2560⟩) (d_cs : (⟨Ctx, cl⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hL : L = 16 ∨ L = 24 ∨ L = 32) :
    WP isa (.block initSeg1) s fun s₂ => KeyCall s₂ K Ctx (W + BitVec.ofNat 64 512) L ∧ s₂.gpr .x19 = W ∧
      s₂.gpr .x21 = Ctx ∧ s₂.gpr .x22 = BitVec.ofNat 64 (Spec.Aes.rounds (L / 4)) ∧ s₂.sp = s.sp ∧
      s₂.rd = s.rd ∧ s₂.wr = s.wr := by
  have pW : Covers [⟨W, 2560⟩] s.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have pC : Covers [⟨Ctx, 256⟩] s.wr := by
    rw [hwr]; exact covers_prefix (covers_of_mem (by simp)) hcl
  replace d_kc : (⟨K, L⟩ : Region).Disjoint ⟨Ctx, 256⟩ := d_kc.sub_right (Region.sub_prefix hcl)
  replace d_cs : (⟨Ctx, 256⟩ : Region).Disjoint ⟨W, 2560⟩ := d_cs.sub_left (Region.sub_prefix hcl)
  obtain ⟨s₁, run₁, g₁, sp₁, rd₁, wr₁, m₁⟩ := save_ok s .x3 hW pW
  have hsi : s.gpr .x1 = BitVec.ofNat 64 L := by rw [← hLn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain ⟨s₂, run₂, x19₂, x21₂, x22₂, x3₂, x0₂, x1₂, x2₂, sp₂, m₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [mov .x19 .x3, mov .x21 .x2, .lsr .x .x22 .x1 2, .addImm .x .x22 .x22 6, ptr .x3 .x19 scrO] s₁ = some s₂ ∧
      s₂.gpr .x19 = W ∧ s₂.gpr .x21 = Ctx ∧ s₂.gpr .x22 = BitVec.ofNat 64 (Spec.Aes.rounds (L / 4)) ∧
      s₂.gpr .x3 = W + BitVec.ofNat 64 512 ∧ s₂.gpr .x0 = K ∧ s₂.gpr .x1 = BitVec.ofNat 64 L ∧
      s₂.gpr .x2 = Ctx ∧ s₂.sp = s₁.sp ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
    · simp [gpr_write, g₁, hW]
    · simp [gpr_write, g₁, hCtx]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, g₁, hsi, BitVec.setWidth_eq]
      exact rounds_of_len hL
    · simp [gpr_write, g₁, hW]
    · simp [gpr_write, g₁, hK]
    · simp [gpr_write, g₁, hsi]
    · simp [gpr_write, g₁, hCtx]
  refine WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩)
  have rd₂' : s₂.rd = s.rd := rd₂.trans rd₁
  have wr₂' : s₂.wr = s.wr := wr₂.trans wr₁
  have pS : Covers [⟨W + BitVec.ofNat 64 512, 512⟩] s.wr := covers_off pW (by decide) (by decide)
  refine ⟨⟨x0₂, x1₂, x2₂, x3₂, hL, d_kc.sub_right (Region.sub_prefix (by decide)),
      d_ks.sub_right (Lay.wSub (by decide)), (d_cs.sub_left (Region.sub_prefix (by decide))).sub_right
        (Lay.wSub (by decide)), ?_, ?_⟩, x19₂, x21₂, x22₂, by rw [sp₂, sp₁], rd₂', wr₂'⟩
  · rw [rd₂', wr₂', hrd]
    exact covers_cons (covers_of_mem (List.mem_append_left _ (List.mem_singleton_self _)))
      (covers_left (covers_cons (covers_prefix pC (by decide)) pS))
  · rw [wr₂']; exact covers_cons (covers_prefix pC (by decide)) pS

/-- The block before the call of `vg_aes_ctr32`. -/
theorem init2_ok {s : State} {Ctx W : Addr} {R : Nat} (h19 : s.gpr .x19 = W) (h21 : s.gpr .x21 = Ctx)
    (h22 : s.gpr .x22 = BitVec.ofNat 64 R) (hR' : R = 10 ∨ R = 12 ∨ R = 14)
    (pC : Covers [⟨Ctx, 256⟩] s.wr) (pW : Covers [⟨W, 2560⟩] s.wr) (d_cs : (⟨Ctx, 256⟩ : Region).Disjoint ⟨W, 2560⟩)
    (wc : Ctx.toNat + 256 ≤ 2 ^ 64) :
    WP isa (.block initSeg2) s fun s₄ =>
      CtrCall s₄ Ctx (W + BitVec.ofNat 64 96) (Ctx + BitVec.ofNat 64 240) (W + BitVec.ofNat 64 512) R 1 ∧
      s₄.gpr .x19 = W ∧ s₄.gpr .x21 = Ctx ∧ s₄.sp = s.sp := by
  have w₁ := in_off pC (show 240 + 8 ≤ 256 by decide) (by decide)
  have w₂ := in_off pC (show 248 + 8 ≤ 256 by decide) (by decide)
  have w₃ := in_off pW (show 96 + 8 ≤ 2560 by decide) (by decide)
  have w₄ := in_off pW (show 104 + 8 ≤ 2560 by decide) (by decide)
  obtain ⟨s₄, run₄, x0₄, x1₄, x2₄, x3₄, x4₄, x5₄, og₄, sp₄, rd₄, wr₄⟩ : ∃ s₄, runBlock isa initSeg2 s = some s₄ ∧
      s₄.gpr .x0 = Ctx ∧ s₄.gpr .x1 = BitVec.ofNat 64 R ∧ s₄.gpr .x2 = W + BitVec.ofNat 64 96 ∧
      s₄.gpr .x3 = Ctx + BitVec.ofNat 64 240 ∧ s₄.gpr .x4 = BitVec.ofNat 64 1 ∧
      s₄.gpr .x5 = W + BitVec.ofNat 64 512 ∧ Others [.x9, .x0, .x1, .x2, .x3, .x4, .x5] s s₄ ∧
      s₄.sp = s.sp ∧ s₄.rd = s.rd ∧ s₄.wr = s.wr := by
    refine ⟨_, by simp only [initSeg2]; arun [h19, h21, w₁, w₂, w₃, w₄], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by others_tac, rfl, rfl, rfl⟩
    · simp [gpr_write, h21]
    · simp [gpr_write, h22]
    · simp [gpr_write, h19]
    · simp [gpr_write, h21]
    · simp [gpr_write]
    · simp [gpr_write, h19]
  refine WP.of_runBlock ⟨s₄, run₄, ?_, by rw [og₄ _ (by decide), h19], by rw [og₄ _ (by decide), h21], sp₄⟩
  have dCW : ∀ d n, d + n ≤ 256 → ∀ e k, e + k ≤ 2560 →
      (⟨Ctx + BitVec.ofNat 64 d, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, k⟩ := fun d n hd e k he =>
    (d_cs.sub_left (Offset.sub_base _ hd)).sub_right (Lay.wSub he)
  have dK0 : (⟨Ctx, 240⟩ : Region).Disjoint ⟨Ctx + BitVec.ofNat 64 240, 16⟩ :=
    Offset.base_disjoint Ctx (by decide) (by omega_using [])
  have pC' : Covers [⟨Ctx, 256⟩] s₄.wr := by rw [wr₄]; exact pC
  have pW' : Covers [⟨W, 2560⟩] s₄.wr := by rw [wr₄]; exact pW
  refine ⟨x0₄, x1₄, x2₄, x3₄, x4₄, x5₄, hR', ?_, by decide, ?_, dK0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := Nat.mod_le (Ctx.toNat + 240 % 2 ^ 64) (2 ^ 64); omega_using [wc]
  · simpa using dCW 0 240 (by decide) 96 16 (by decide)
  · simpa using dCW 0 240 (by decide) 512 2048 (by decide)
  · exact (dCW 240 16 (by decide) 96 16 (by decide)).symm
  · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
  · exact dCW 240 16 (by decide) 512 2048 (by decide)
  · exact covers_cons (covers_left (covers_prefix pC' (by decide))) (covers_cons
      (covers_left (covers_off pW' (by decide) (by decide))) (covers_cons
      (covers_left (covers_off pC' (by decide) (by decide))) (covers_left (covers_off pW' (by decide) (by decide)))))
  · exact covers_cons (covers_off pW' (by decide) (by decide)) (covers_cons (covers_off pC' (by decide) (by decide))
      (covers_off pW' (by decide) (by decide)))

/-- Key setup up to the hash subkey, then `fin`, which the taint analysis
checks with `x19` (the working space) and `x21` (the context) public. -/
theorem initWith_ct (v : GcmImpl) (fin : Prog isa) {cl : Nat} (hcl : 256 ≤ cl) {pre : State → Prop}
    (hpre : ∀ s, pre s → s.rd = [⟨s.gpr .x0, (s.gpr .x1).toNat⟩] ∧ s.wr = [⟨s.gpr .x2, cl⟩, ⟨s.gpr .x3, 2560⟩] ∧
      (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨s.gpr .x2, cl⟩ ∧
      (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨s.gpr .x3, 2560⟩ ∧
      (⟨s.gpr .x2, cl⟩ : Region).Disjoint ⟨s.gpr .x3, 2560⟩ ∧ (s.gpr .x2).toNat + 256 ≤ 2 ^ 64 ∧
      ((s.gpr .x1).toNat = 16 ∨ (s.gpr .x1).toNat = 24 ∨ (s.gpr .x1).toNat = 32))
    (hT : ∃ h, (taint.check (Taint.ofRegs [.x19, .x21]) fin h).isSome = true) :
    ConstantTime isa pre initAArch64.pub (initWith v.callees fin) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q0, q1, q2, q3, qsp⟩ := hq
  replace h₁ := hpre _ h₁
  replace h₂ := hpre _ h₂
  rw [← q0, ← q1, ← q2, ← q3] at h₂
  obtain ⟨hrd₁, hwr₁, d_kc, d_ks, d_cs, wc, hL⟩ := h₁
  obtain ⟨hrd₂, hwr₂, -⟩ := h₂
  generalize hK : σ₁.gpr .x0 = K at *
  generalize hLn : (σ₁.gpr .x1).toNat = L at *
  generalize hCtx : σ₁.gpr .x2 = Ctx at *
  generalize hW : σ₁.gpr .x3 = W at *
  have hR' : Spec.Aes.rounds (L / 4) = 10 ∨ Spec.Aes.rounds (L / 4) = 12 ∨ Spec.Aes.rounds (L / 4) = 14 := by
    rcases hL with rfl | rfl | rfl <;> decide
  have d_cs' : (⟨Ctx, 256⟩ : Region).Disjoint ⟨W, 2560⟩ := d_cs.sub_left (Region.sub_prefix hcl)
  refine rel_seq (rel_taint [.x0, .x1, .x2, .x3] qsp (by agree_tac [hK, hCtx, hW, ← q0, q1, ← q2, ← q3])
      ⟨_, by taint_decide⟩)
    (init1_ok hcl hK hLn hCtx hW hrd₁ hwr₁ d_kc d_ks d_cs hL)
    (init1_ok hcl q0.symm (by rw [← q1, hLn]) q2.symm q3.symm hrd₂ hwr₂ d_kc d_ks d_cs hL)
    fun τ₁ τ₂ ⟨k₁, x19₁, x21₁, x22₁, sp₁, rd₁, wr₁⟩ ⟨k₂, x19₂, x21₂, x22₂, sp₂, rd₂, wr₂⟩ => ?_
  refine rel_seq (rel_key v.key k₁ k₂ (by rw [sp₁, sp₂, qsp])) (key_call v.key k₁) (key_call v.key k₂)
    fun τ₁' τ₂' g₁ g₂ => ?_
  have pv : ∀ {σ τ τ' : State}, σ.wr = [⟨Ctx, cl⟩, ⟨W, 2560⟩] → τ.wr = σ.wr →
      KeyPost τ K Ctx (W + BitVec.ofNat 64 512) L τ' → τ.gpr .x19 = W → τ.gpr .x21 = Ctx →
      τ.gpr .x22 = BitVec.ofNat 64 (Spec.Aes.rounds (L / 4)) →
      WP isa (.block initSeg2) τ' fun s₄ => CtrCall s₄ Ctx (W + BitVec.ofNat 64 96) (Ctx + BitVec.ofNat 64 240)
        (W + BitVec.ofNat 64 512) (Spec.Aes.rounds (L / 4)) 1 ∧ s₄.gpr .x19 = W ∧ s₄.gpr .x21 = Ctx ∧
        s₄.sp = τ'.sp :=
    fun hwr wr g h19 h21 h22 => init2_ok (by rw [g.saved .x19 (by decide) (by decide), h19])
      (by rw [g.saved .x21 (by decide) (by decide), h21]) (by rw [g.saved .x22 (by decide) (by decide), h22]) hR'
      (by rw [g.wr, wr, hwr]; exact covers_prefix (covers_of_mem (by simp)) hcl)
      (by rw [g.wr, wr, hwr]; exact covers_of_mem (by simp)) d_cs' wc
  refine rel_seq (rel_taint [.x19, .x21, .x22] (by rw [g₁.sp, g₂.sp, sp₁, sp₂, qsp])
      (by agree_tac [g₁.saved .x19 (by decide) (by decide), g₂.saved .x19 (by decide) (by decide),
        g₁.saved .x21 (by decide) (by decide), g₂.saved .x21 (by decide) (by decide),
        g₁.saved .x22 (by decide) (by decide), g₂.saved .x22 (by decide) (by decide), x19₁, x19₂, x21₁, x21₂,
        x22₁, x22₂]) ⟨_, by taint_decide⟩)
    (pv hwr₁ wr₁ g₁ x19₁ x21₁ x22₁) (pv hwr₂ wr₂ g₂ x19₂ x21₂ x22₂)
    fun τ₁ τ₂ ⟨c₁, y₁, z₁, s₁'⟩ ⟨c₂, y₂, z₂, s₂'⟩ => ?_
  refine rel_seq (rel_ctr v.ctr c₁ c₂ (by rw [s₁', s₂', g₁.sp, g₂.sp, sp₁, sp₂, qsp]))
    (ctr_call v.ctr c₁) (ctr_call v.ctr c₂) fun τ₁ τ₂ e₁ e₂ => ?_
  exact rel_taint [.x19, .x21] (by rw [e₁.sp, e₂.sp, s₁', s₂', g₁.sp, g₂.sp, sp₁, sp₂, qsp])
    (by agree_tac [e₁.saved .x19 (by decide) (by decide), e₂.saved .x19 (by decide) (by decide), y₁, y₂,
      e₁.saved .x21 (by decide) (by decide), e₂.saved .x21 (by decide) (by decide), z₁, z₂]) hT

theorem init_ct (v : GcmImpl) : ConstantTime isa initAArch64.pre initAArch64.pub (init v.callees) :=
  initWith_ct v _ (Nat.le_refl _) (fun s h => by
      simp only [initAArch64] at h
      obtain ⟨hrd, hwr, d_kc, d_ks, d_cs, wc, -, hL⟩ := h
      exact ⟨hrd, hwr, d_kc, d_ks, d_cs, wc, hL⟩)
    ⟨_, by taint_decide⟩

end VG.Proof.AesGcm.AArch64

end

end

/-!
# AES-GCM on AArch64: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time
(for any implementations `v` of `vg_aes_ctr32`, `vg_aes_expand_key_scratch` and
`vg_ghash`), a state satisfying each precondition, and the shared contracts of
`Spec/Gcm/Contract.lean` with the working space as a last argument
(`Proof/AesGcm/Scratch.lean`; with no stack: the calls keep the return
address in `x30`, which each function saves in the working space).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

/-- The CPU features of the functions calling `vg_aes_ctr32` and `vg_ghash`
(here, not in `Callee.lean`, to keep `List.dedup`'s imports out of the proofs). -/
def GcmImpl.features (v : GcmImpl) : List String := (v.ctr.features ++ v.gh.features).dedup

open VG VG.AArch64 VG.Impl.AesGcm.AArch64

/-! ## v8–v15 -/

theorem init_keepsV (v : GcmImpl) : (init v.callees).allInstrs keepsV = true := by
  simp only [init, initWith, ctrCall, GcmImpl.callees, Code.allInstrs, v.ctr.keepsV, v.key.keepsV, v.gh.keepsV]; decide +kernel

theorem streamInit_keepsV (v : GcmImpl) : (streamInit v.callees).allInstrs keepsV = true := by
  simp only [streamInit, j0, j0hash, ghCall, absorb, absSeg1, absTail, minK, copy, copyB, xorB, Impl.AesGcm.AArch64.xor, padSeg, flush, lens,
    GcmImpl.callees, Code.allInstrs, v.ctr.keepsV, v.key.keepsV, v.gh.keepsV]; decide +kernel

theorem streamAad_keepsV (v : GcmImpl) : (streamAad v.callees).allInstrs keepsV = true := by
  simp only [streamAad, ghCall, absorb, absSeg1, absTail, minK, copy, copyB, xorB, Impl.AesGcm.AArch64.xor, padSeg, flush, lens,
    GcmImpl.callees, Code.allInstrs, v.ctr.keepsV, v.key.keepsV, v.gh.keepsV]; decide +kernel

theorem streamEncrypt_keepsV (v : GcmImpl) : (streamEncrypt v.callees).allInstrs keepsV = true := by
  simp only [streamEncrypt, encBody, fo, textAbs, crypt, crSeg1, crSeg2, crTail, ctrCall, ghCall, absorb,
    absSeg1, absTail, minK, copy, copyB, xorB, Impl.AesGcm.AArch64.xor, padSeg, flush, lens, GcmImpl.callees, Code.allInstrs, v.ctr.keepsV,
    v.key.keepsV, v.gh.keepsV]; decide +kernel

theorem streamDecrypt_keepsV (v : GcmImpl) : (streamDecrypt v.callees).allInstrs keepsV = true := by
  simp only [streamDecrypt, decBody, decAbs, fo, textAbs, crypt, crSeg1, crSeg2, crTail, ctrCall, ghCall,
    absorb, absSeg1, absTail, minK, copy, copyB, xorB, Impl.AesGcm.AArch64.xor, padSeg, flush, lens, GcmImpl.callees, Code.allInstrs,
    v.ctr.keepsV, v.key.keepsV, v.gh.keepsV]; decide +kernel

theorem streamFinish_keepsV (v : GcmImpl) : (streamFinish v.callees).allInstrs keepsV = true := by
  simp only [streamFinish, finBody, tag, crypt, crSeg1, crSeg2, crTail, ctrCall, ghCall, absorb, absSeg1,
    absTail, minK, copy, copyB, xorB, Impl.AesGcm.AArch64.xor, padSeg, flush, lens, GcmImpl.callees, Code.allInstrs, v.ctr.keepsV,
    v.key.keepsV, v.gh.keepsV]; decide +kernel

theorem streamVerify_keepsV (v : GcmImpl) : (streamVerify v.callees).allInstrs keepsV = true := by
  simp only [streamVerify, tagLenOk, tagIn, cmpSeg, cmp, cmp16, finBody, tag, crypt, crSeg1, crSeg2, crTail, ctrCall,
    ghCall, absorb, absSeg1, absTail, minK, copy, copyB, xorB, Impl.AesGcm.AArch64.xor, padSeg, flush, lens, GcmImpl.callees, Code.allInstrs,
    v.ctr.keepsV, v.key.keepsV, v.gh.keepsV]; decide +kernel

theorem seal_keepsV (v : GcmImpl) : («seal» v.callees).allInstrs keepsV = true := by
  simp only [«seal», sealRest, j0, j0hash, oneAad, absorbAl, encBody, fo, textAbs, finBody, tag, crypt, crSeg1, crSeg2, crTail,
    ctrCall, ghCall, absorb, absSeg1, absTail, minK, copy, copyB, xorB, Impl.AesGcm.AArch64.xor, padSeg, flush, lens, GcmImpl.callees,
    Code.allInstrs, v.ctr.keepsV, v.key.keepsV, v.gh.keepsV]; decide +kernel

theorem open_keepsV (v : GcmImpl) : («open» v.callees).allInstrs keepsV = true := by
  simp only [«open», openEntry, openRest, openMain, oneCrypt, cryptAl, crArgs, tagLenOk, tagIn, cmpSeg, cmp, cmp16, j0, j0hash, oneAad, absorbAl, decAbs, fo, textAbs,
    finBody, tag, crypt, crSeg1, crSeg2, crTail, ctrCall, ghCall, absorb, absSeg1, absTail, minK, copy, copyB, xorB, Impl.AesGcm.AArch64.xor,
    padSeg, flush, lens, GcmImpl.callees, Code.allInstrs, v.ctr.keepsV, v.key.keepsV, v.gh.keepsV]
  decide +kernel

/-! ## Correctness -/

theorem init_correct (v : GcmImpl) (s : State) (hs : initAArch64.pre s) :
    ∃ t s', Exec isa (init v.callees) s t s' ∧ abiPreserved s s' ∧ initAArch64.post s s' :=
  WP.withPreservedV (init_wp v hs) (init_keepsV v)

theorem streamInit_correct (v : GcmImpl) (s : State) (hs : streamInitAArch64.pre s) :
    ∃ t s', Exec isa (streamInit v.callees) s t s' ∧ abiPreserved s s' ∧ streamInitAArch64.post s s' :=
  WP.withPreservedV (streamInit_wp v hs) (streamInit_keepsV v)

theorem streamAad_correct (v : GcmImpl) (s : State) (hs : streamAadAArch64.pre s) :
    ∃ t s', Exec isa (streamAad v.callees) s t s' ∧ abiPreserved s s' ∧ streamAadAArch64.post s s' :=
  WP.withPreservedV (streamAad_wp v hs) (streamAad_keepsV v)

theorem streamEncrypt_correct (v : GcmImpl) (s : State) (hs : streamEncryptAArch64.pre s) :
    ∃ t s', Exec isa (streamEncrypt v.callees) s t s' ∧ abiPreserved s s' ∧ streamEncryptAArch64.post s s' :=
  WP.withPreservedV (streamEncrypt_wp v hs) (streamEncrypt_keepsV v)

theorem streamDecrypt_correct (v : GcmImpl) (s : State) (hs : streamDecryptAArch64.pre s) :
    ∃ t s', Exec isa (streamDecrypt v.callees) s t s' ∧ abiPreserved s s' ∧ streamDecryptAArch64.post s s' :=
  WP.withPreservedV (streamDecrypt_wp v hs) (streamDecrypt_keepsV v)

theorem streamFinish_correct (v : GcmImpl) (s : State) (hs : streamFinishAArch64.pre s) :
    ∃ t s', Exec isa (streamFinish v.callees) s t s' ∧ abiPreserved s s' ∧ streamFinishAArch64.post s s' :=
  WP.withPreservedV (streamFinish_wp v hs) (streamFinish_keepsV v)

theorem streamVerify_correct (v : GcmImpl) (s : State) (hs : streamVerifyAArch64.pre s) :
    ∃ t s', Exec isa (streamVerify v.callees) s t s' ∧ abiPreserved s s' ∧ streamVerifyAArch64.post s s' :=
  WP.withPreservedV (streamVerify_wp v hs) (streamVerify_keepsV v)

theorem seal_correct (v : GcmImpl) (s : State) (hs : sealAArch64.pre s) :
    ∃ t s', Exec isa («seal» v.callees) s t s' ∧ abiPreserved s s' ∧ sealAArch64.post s s' :=
  WP.withPreservedV (seal_wp v hs) (seal_keepsV v)

theorem open_correct (v : GcmImpl) (s : State) (hs : openAArch64.pre s) :
    ∃ t s', Exec isa («open» v.callees) s t s' ∧ abiPreserved s s' ∧ openAArch64.post s s' :=
  WP.withPreservedV (open_wp v hs) (open_keepsV v)

/-! ## States satisfying the preconditions (with empty buffers) -/

def initSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 16 | .x2 => 0x2000 | .x3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 256⟩, ⟨0x4000, 2560⟩]

def streamInitSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x3 => 0x3000 | .x4 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩]

def streamAadSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x3000 | .x3 => 0x2000 | .x5 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩]

def streamCryptSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x3000 | .x5 => 0x2000 | .x7 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩, ⟨0x4000, 2560⟩]

def finSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x3000 | .x5 => 0x5000 | .x6 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x5000, 16⟩, ⟨0x4000, 2560⟩]

def verSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x3000 | .x5 => 0x5000 | .x7 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x5000, 0⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩]

/-- `tag` at 0 and `work` at `0x5000` (`[sp + 8]`). -/
def sealSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x2000 | .x4 => 0x3000 | .x6 => 0x4000 | _ => 0
  sp := 0x8000
  mem a := if a = 0x8009 then 0x50 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x8000, 16⟩]
  wr := [⟨0x4000, 0⟩, ⟨0, 16⟩, ⟨0x5000, 2560⟩]

/-- `tag` at 0, `tag_len` 0 and `work` at `0x5000` (`[sp + 16]`). -/
def openSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x2000 | .x4 => 0x3000 | .x6 => 0x4000 | _ => 0
  sp := 0x8000
  mem a := if a = 0x8011 then 0x50 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0, 0⟩, ⟨0x8000, 24⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x5000, 2560⟩]

/-! ## The shared contracts -/

theorem init_verified (v : GcmImpl) :
    Verified AArch64.target (init v.callees) (Proof.AesGcm.initScratchContract AArch64.abi) :=
  Verified.of_correct (init_correct v) (init_ct v) (by
    sig_implies [Proof.AesGcm.initScratchContract, Proof.AesGcm.initScratchSig, Spec.Gcm.initPre, Spec.Gcm.initPost, initAArch64, args, rounds, AArch64.abi,
      AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      [initSat] using initSat)

theorem streamInit_verified (v : GcmImpl) :
    Verified AArch64.target (streamInit v.callees) (Proof.AesGcm.streamInitScratchContract AArch64.abi) :=
  Verified.of_correct (streamInit_correct v) (streamInit_ct v) (by
    sig_implies [Proof.AesGcm.streamInitScratchContract, Proof.AesGcm.streamInitScratchSig, Spec.Gcm.streamInitPost, streamInitAArch64, args, rounds, AArch64.abi,
      AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      [streamInitSat] using streamInitSat)

theorem streamAad_verified (v : GcmImpl) :
    Verified AArch64.target (streamAad v.callees) (Proof.AesGcm.streamAadScratchContract AArch64.abi) :=
  Verified.of_correct (streamAad_correct v) (streamAad_ct v) (by
    sig_implies [Proof.AesGcm.streamAadScratchContract, Proof.AesGcm.streamAadScratchSig, Spec.Gcm.streamAadPost, streamAadAArch64, args, rounds, AArch64.abi,
      AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      [streamAadSat] using streamAadSat)

theorem streamEncrypt_verified (v : GcmImpl) :
    Verified AArch64.target (streamEncrypt v.callees) (Proof.AesGcm.streamEncryptScratchContract AArch64.abi) :=
  Verified.of_correct (streamEncrypt_correct v) (streamEncrypt_ct v) (by
    sig_implies [Proof.AesGcm.streamEncryptScratchContract, Proof.AesGcm.streamCryptScratchSig, Spec.Gcm.streamTextPre, Proof.AesGcm.streamEncryptRoundsPost, Proof.AesGcm.streamDecryptRoundsPost, streamEncryptAArch64, streamCryptPre, streamCryptPub, args, rounds, AArch64.abi,
      AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      [streamCryptSat] using streamCryptSat)

theorem streamDecrypt_verified (v : GcmImpl) :
    Verified AArch64.target (streamDecrypt v.callees) (Proof.AesGcm.streamDecryptScratchContract AArch64.abi) :=
  Verified.of_correct (streamDecrypt_correct v) (streamDecrypt_ct v) (by
    sig_implies [Proof.AesGcm.streamDecryptScratchContract, Proof.AesGcm.streamCryptScratchSig, Spec.Gcm.streamTextPre, Proof.AesGcm.streamEncryptRoundsPost, Proof.AesGcm.streamDecryptRoundsPost, streamDecryptAArch64, streamCryptPre, streamCryptPub, args, rounds, AArch64.abi,
      AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      [streamCryptSat] using streamCryptSat)

theorem streamFinish_verified (v : GcmImpl) :
    Verified AArch64.target (streamFinish v.callees) (Proof.AesGcm.streamFinishScratchContract AArch64.abi) :=
  Verified.of_correct (streamFinish_correct v) (streamFinish_ct v) (by
    sig_implies [Proof.AesGcm.streamFinishScratchContract, Proof.AesGcm.streamFinishScratchSig,
      Spec.Gcm.streamFinishPre, Proof.AesGcm.streamFinishRoundsPost, streamFinishAArch64, finPre, args, rounds, AArch64.abi,
      AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      [finSat] using finSat)

theorem streamVerify_verified (v : GcmImpl) :
    Verified AArch64.target (streamVerify v.callees) (Proof.AesGcm.streamVerifyScratchContract AArch64.abi) :=
  Verified.of_correct (streamVerify_correct v) (streamVerify_ct v) (by
    sig_implies [Proof.AesGcm.streamVerifyScratchContract, Proof.AesGcm.streamVerifyScratchSig,
      Spec.Gcm.streamVerifyPre, Proof.AesGcm.streamVerifyRoundsPost, streamVerifyAArch64, verPre, args, rounds, AArch64.abi,
      AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      [verSat] using verSat)

theorem seal_verified (v : GcmImpl) :
    Verified AArch64.target («seal» v.callees) (Proof.AesGcm.sealScratchContract AArch64.abi) :=
  Verified.of_correct (seal_correct v) (seal_ct v) (by
    sig_implies [Proof.AesGcm.sealScratchContract, Proof.AesGcm.sealScratchSig, Spec.Gcm.sealPre,
      Proof.AesGcm.sealRoundsPost, sealAArch64, sealPre, sealPreX, List.append_nil, onePub, args, rounds, AArch64.abi,
      AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      [sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealSat)

theorem open_verified (v : GcmImpl) :
    Verified AArch64.target («open» v.callees) (Proof.AesGcm.openScratchContract AArch64.abi) :=
  Verified.of_correct (open_correct v) (open_ct v) (by
    sig_implies [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openPre,
      Proof.AesGcm.openRoundsPost, Spec.Gcm.openLeak, openAArch64, openPre, openPreX, List.append_nil, onePub, openRes, openLeakOf, args, rounds,
      AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range,
      List.range.loop]
      [openSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using openSat)

end VG.Proof.AesGcm.AArch64
