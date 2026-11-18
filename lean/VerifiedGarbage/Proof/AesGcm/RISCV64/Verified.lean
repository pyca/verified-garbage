module

public import VerifiedGarbage.Proof.AesGcm.Rounds
public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contract
public import VerifiedGarbage.Proof.AesGcm.Scratch
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.AesGcm.RISCV64
public import VerifiedGarbage.Impl.StackScratch.RISCV64
public import VerifiedGarbage.Impl.StackScratch.RISCV64.Args
import VerifiedGarbage.Proof.AesGcm.RISCV64.Init
import VerifiedGarbage.Proof.AesGcm.RISCV64.InitCT
public import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamInit
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamCrypt
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamFinish
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamVerify
import VerifiedGarbage.Proof.AesGcm.RISCV64.CTFin
import VerifiedGarbage.Proof.AesGcm.RISCV64.CTOpen
import VerifiedGarbage.Proof.AesGcm.RISCV64.Seal
import VerifiedGarbage.Proof.AesGcm.RISCV64.CTSeal
import VerifiedGarbage.Proof.AesGcm.RISCV64.Open
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratchArgs
import VerifiedGarbage.Proof.AesGcm.RISCV64.CTBase
public import VerifiedGarbage.Proof.AesGcm.RISCV64.CTCrypt
public import VerifiedGarbage.Proof.AesGcm.RISCV64.CTText
import VerifiedGarbage.Proof.AesGcm.RISCV64.CryptOk
import VerifiedGarbage.Proof.AesGcm.RISCV64.TextAbsorb
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Contract
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTCrypt
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTText
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CryptOk
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.InitCT
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamCrypt
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.TextAbsorb
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Env
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.Proof.AesGcm.RISCV64.CTJ0
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTJ0
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamInit
public import VerifiedGarbage.Proof.Aes.SboxSpec
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Fn
import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.Gcm.Ctr
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Fn
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
meta import VerifiedGarbage.Proof.Gcm.Compose
meta import VerifiedGarbage.Proof.Gcm.Ctr
meta import VerifiedGarbage.Proof.Framework.RISCV64.Run
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Impl.AesGcm.RISCV64

/-! ### `AesGcm.RISCV64.StreamCT`, which only this module used -/

section

/-! ### `AesGcm.RISCV64.StreamAad`, which this module and modules that import it used -/

section

/-!
# AES-GCM on RISC-V: `vg_aes_gcm_stream_aad`

Untrusted: everything here is checked by Lean. The entry saves our caller's
registers and sets up `absorb`'s arguments (`aadEntry_ok`); `absorb 16`
absorbs the data into the accumulator (`aad_run`), which keeps the rest of
the state (`streamAad_wp`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom StreamRepr)
open VG.Proof.Gcm (Absorbed Ctr)

/-- The entry: `absorb`'s arguments. -/
theorem aadEntry_ok {s : State} (hW : Covers [⟨s.gpr .a5, 2560⟩] s.wr) (hal : (s.gpr .a5).toNat % 8 = 0) :
    WP isa (.block streamAadPre) s fun s' => Entered s (s.gpr .a5) s' ∧
      s'.gpr .s0 = s.gpr .a5 ∧ s'.gpr .s1 = s.gpr .a1 ∧ s'.gpr .s2 = s.gpr .a0 ∧
      s'.gpr .s4 = s.gpr .a3 ∧ s'.gpr .s5 = s.gpr .a4 ∧
      s'.gpr .s6 = BitVec.ofNat 64 ((s.gpr .a2).toNat % 16) := by
  refine WP.block_append (WP.mono (save_ok (b := .a5) hW hal) fun s₁ ⟨hg, h31, hk, hsv, hf⟩ => ?_)
  have e3 : s₁.gpr .a0 = s.gpr .a0 := hg _ (by decide)
  have e4 : s₁.gpr .a1 = s.gpr .a1 := hg _ (by decide)
  have e5 : s₁.gpr .a2 = s.gpr .a2 := hg _ (by decide)
  have e6 : s₁.gpr .a3 = s.gpr .a3 := hg _ (by decide)
  have e7 : s₁.gpr .a4 = s.gpr .a4 := hg _ (by decide)
  crun [Int.reduceNatCast', mov, e3, e4, e5, e6, e7, h31, and15]
  exact ⟨⟨hk.rd, hk.wr, hk.sp⟩, hsv, hf⟩

/-- The regions `stream_aad` writes. -/
abbrev aadFrame (St W sp : Addr) : List Region := savedR W :: absFrame St W 16 sp

/-- After the entry: `absorb`'s precondition, for additional data `x` so far
of `aad_len` bytes modulo 16. -/
theorem aad_entry {s : State} (hs : streamAadRISCV64.pre s) {x : List Byte}
    (hx : x.length % 16 = (s.gpr .a2).toNat % 16) :
    WP isa (.block streamAadPre) s fun s₁ => Entered s (s.gpr .a5) s₁ ∧ s₁.gpr .s2 = s.gpr .a0 ∧
      s₁.gpr .s1 = s.gpr .a1 ∧ s₁.gpr .s0 = s.gpr .a5 ∧
      AbsIn s₁.gpr s.sp 16 (Spec.Gcm.ctxH s.mem (s.gpr .a0)) x (s.gpr .a3) (s.gpr .a4).toNat s₁ ∧
      bytesAt s₁.mem (s.gpr .a3) (s.gpr .a4).toNat = bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat := by
  simp only [streamAadRISCV64] at hs
  obtain ⟨hrd, hwr, dcs, dcw, dds, ddw, dsw, wc, wd, ws, ww, hstk, -, -, hal⟩ := hs
  generalize hCtx : s.gpr .a0 = Ctx at *
  generalize hSt : s.gpr .a1 = St at *
  generalize hD : s.gpr .a3 = D at *
  generalize hn : (s.gpr .a4).toNat = n at *
  generalize hW : s.gpr .a5 = W at *
  have hlt : n < 2 ^ 64 := hn ▸ (s.gpr .a4).isLt
  have hn' : s.gpr .a4 = BitVec.ofNat 64 n := by rw [← hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hWc : Covers [⟨W, 2560⟩] s.wr := by rw [hwr]; exact covers_mem (by simp)
  refine WP.mono (aadEntry_ok (by rw [hW]; exact hWc) (by rw [hW]; exact hal)) fun s₁ ⟨en, h31, h30, h29, h24, h25, h26⟩ => ?_
  rw [hW] at en h31
  rw [hSt] at h30
  rw [hCtx] at h29
  rw [hD] at h24
  rw [hn'] at h25
  have perm : Perm Ctx St W s₁ :=
    (⟨covers_mem (by rw [hrd, hwr]; simp), covers_mem (by rw [hwr]; simp), hWc⟩ : Perm Ctx St W s).of_eq
      en.keeps.rd en.keeps.wr
  have hk : StkOk Ctx St W s.sp := hstk.stk (by simp) (by simp) (by simp)
  have he : Env s₁.gpr s.sp s₁ :=
    ⟨fun _ _ => rfl, en.keeps.sp, by rw [h29, h30, h31]; exact perm, by rw [h29, h30, h31, en.keeps.sp]; exact hk⟩
  have sW : Region.Sub (savedR W) ⟨W, 2560⟩ := Offset.sub_base _ (by decide)
  have hdat : bytesAt s₁.mem D n = bytesAt s.mem D n :=
    bytesAt_frame en.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ddw.sub_right sW) (by omega_using [hn])
  have hH : blockAt s₁.mem (s₁.gpr .s2 + BitVec.ofNat 64 240) = Spec.Gcm.ctxH s.mem Ctx := by
    rw [h29, ctxH_eq]
    exact blockAt_frame en.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (dcw.sub_left (Offset.sub_base _ (by decide))).sub_right sW)
  refine ⟨en, h29, h30, h31, ⟨he, h24, h25, by rw [h26, hx], ?_, hH⟩, hdat⟩
  rw [h30, h31]
  exact ⟨by rw [en.keeps.rd, en.keeps.wr, hrd]; exact covers_mem (by simp), hlt, wd, dds, ddw,
    by rw [en.keeps.sp]; exact hstk.buf (by simp)⟩

/-- One run of `stream_aad`, for additional data `x` so far of `aad_len` bytes
modulo 16. -/
theorem aad_run [VG.Proof.Gcm.RISCV64.GhashLaw] {s : State} (hs : streamAadRISCV64.pre s) {x : List Byte}
    (hx : x.length % 16 = (s.gpr .a2).toNat % 16) :
    WP isa streamAad s fun s' => abiPreserved s s' ∧
      (Absorbed s.mem (s.gpr .a1 + BitVec.ofNat 64 16) (s.gpr .a1 + BitVec.ofNat 64 32)
          (Spec.Gcm.ctxH s.mem (s.gpr .a0)) x →
        Absorbed s'.mem (s.gpr .a1 + BitVec.ofNat 64 16) (s.gpr .a1 + BitVec.ofNat 64 32)
          (Spec.Gcm.ctxH s.mem (s.gpr .a0)) (x ++ bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat)) ∧
      Frame (aadFrame (s.gpr .a1) (s.gpr .a5) s.sp) s.mem s'.mem := by
  have hs' := hs
  obtain ⟨-, -, dcs, dcw, -, -, dsw, wc, -, ws, ww, hstk, a0, a1, a5⟩ := hs'
  have L₀ : Lay (s.gpr .a0) (s.gpr .a1) (s.gpr .a5) := Lay.of wc ws ww dcs dcw dsw a0 a1 a5
  refine WP.seq (WP.mono (aad_entry hs hx) fun s₁ ⟨en, h29, h30, h31, hIn, hdat⟩ => ?_)
  have dS : ∀ (d k : Nat), d + k ≤ 80 →
      (⟨s.gpr .a1 + BitVec.ofNat 64 d, k⟩ : Region).Disjoint (savedR (s.gpr .a5)) :=
    fun d k h => L₀.st_w h (.inr ⟨by decide, by decide⟩)
  have hA : ∀ (m : Mem), Frame [savedR (s.gpr .a5)] s.mem m →
      Absorbed s.mem (s.gpr .a1 + BitVec.ofNat 64 16) (s.gpr .a1 + BitVec.ofNat 64 32)
        (Spec.Gcm.ctxH s.mem (s.gpr .a0)) x →
      Absorbed m (s.gpr .a1 + BitVec.ofNat 64 16) (s.gpr .a1 + BitVec.ofNat 64 32)
        (Spec.Gcm.ctxH s.mem (s.gpr .a0)) x :=
    fun m hf ha => ha.congr (blockAt_frame hf fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dS 16 16 (by decide))
      (bytesAt_frame hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (dS 32 16 (by decide)).sub_left (Region.sub_prefix (Nat.le_of_lt (Nat.mod_lt _ (by decide)))))
        (by omega_using []))
  refine WP.seq (WP.mono (absorb_ok (L₀.v h29 h30 h31) (.inr rfl) hIn) fun s₂ h₂ => ?_)
  have f₂ := h₂.frame
  rw [h30, h31] at f₂
  have hk := h₂.env.stk'
  rw [h29, h30, h31] at hk
  have hsv : SavedAt s₂.mem (s.gpr .a5) s := en.saved.frame f₂ (saved_absFrame L₀ (.inr rfl) hk)
  have e31 : s₂.gpr .s0 = s.gpr .a5 := (h₂.env.fr _ (by decide)).trans h31
  refine WP.mono (restore_ok e31 a5 (by
      have := h₂.env.perm.w; rw [h31] at this; exact Covers.right this) hsv h₂.env.sp)
    fun s' ⟨ga, hm, _⟩ => ⟨ga, fun ha => ?_, ?_⟩
  · have := h₂.abs
    rw [h30, hdat] at this
    rw [hm]; exact this (hA _ en.frame ha)
  · rw [hm]
    exact (en.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩).trans
      (f₂.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)

theorem streamAad_wp [VG.Proof.Gcm.RISCV64.GhashLaw] {s : State} (hs : streamAadRISCV64.pre s) :
    WP isa streamAad s fun s' => abiPreserved s s' ∧ streamAadRISCV64.post s s' := by
  have hz : (Spec.Gcm.zeros ((s.gpr .a2).toNat % 16)).length % 16 = (s.gpr .a2).toNat % 16 := by
    rw [Proof.Gcm.length_zeros, Nat.mod_mod]
  refine WP.mono (WP.forall_det (P := fun (i : (Block → Block) × List Byte × List Byte) =>
      StreamRepr s.mem (s.gpr .a1) i.1 (Spec.Gcm.ctxH s.mem (s.gpr .a0)) i.2.1 i.2.2 [] ∧
        s.gpr .a2 = BitVec.ofNat 64 i.2.2.length)
    (Q := fun i s' => StreamRepr s'.mem (s.gpr .a1) i.1 (Spec.Gcm.ctxH s.mem (s.gpr .a0)) i.2.1
      (i.2.2 ++ bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat) [])
    (aad_run hs hz) fun ⟨ciph, iv, a⟩ ⟨hr, hl⟩ => ?_) fun s' ⟨⟨ga, _, _⟩, h⟩ =>
      ⟨ga, fun ciph iv a hr hl => h ⟨ciph, iv, a⟩ ⟨hr, hl⟩⟩
  have hx : a.length % 16 = (s.gpr .a2).toNat % 16 := by rw [hl, toNat_mod16]
  obtain ⟨hj, ha, hc⟩ := Proof.Gcm.streamRepr_iff.mp hr
  have hs' := hs
  simp only [streamAadRISCV64] at hs'
  obtain ⟨-, -, -, -, -, -, dsw, -, -, ws, ww, hstk, -, -, -⟩ := hs'
  have dSt : ∀ r ∈ aadFrame (s.gpr .a1) (s.gpr .a5) s.sp, ∀ d, d + 16 ≤ 80 → (d + 16 ≤ 16 ∨ 48 ≤ d) →
      (⟨s.gpr .a1 + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := by
    intro r hr d hd hd'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have st_off : ∀ e k, e + k ≤ 80 → (d + 16 ≤ e ∨ e + k ≤ d) →
        (⟨s.gpr .a1 + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint ⟨s.gpr .a1 + BitVec.ofNat 64 e, k⟩ :=
      fun e k he h => Offset.disjoint _ h (by omega_using [hd]) (by omega_using [he])
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (dsw.sub_left (Offset.sub_base _ (by omega_using [hd]))).sub_right (Offset.sub_base _ (by decide))
    · exact st_off 16 16 (by decide) (by omega_using [hd'])
    · exact st_off 32 16 (by decide) (by omega_using [hd'])
    · exact (dsw.sub_left (Offset.sub_base _ (by omega_using [hd]))).sub_right (Offset.sub_base _ (by decide))
    · exact (hstk.buf (r := ⟨s.gpr .a1, 80⟩) (by simp)).sub_left (Offset.sub_base _ (by omega_using [hd]))
  refine WP.mono (aad_run hs hx) fun s' ⟨_, habs, hf⟩ => ?_
  refine Proof.Gcm.streamRepr_iff.mpr ⟨?_, ?_, ?_⟩
  · rw [← hj]
    have := blockAt_frame hf fun r hr => by simpa using dSt r hr 0 (by decide) (.inl (by decide))
    simpa using this
  · exact habs ha
  · refine hc.congr ?_ ?_
    · exact blockAt_frame hf fun r hr => dSt r hr 48 (by decide) (.inr (by decide))
    · exact blockAt_frame hf fun r hr => dSt r hr 64 (by decide) (.inr (by decide))

end VG.Proof.AesGcm.RISCV64

end

end

/-!
# AES-GCM on RISC-V: `vg_aes_gcm_stream_init` and `vg_aes_gcm_stream_aad` are constant time

Untrusted: everything here is checked by Lean. The entry by the taint
analysis from the public arguments; then `j0` (`j0_ct`) or `absorb 16`
(`absorb_ct`) from the invariants the entry's correctness gives; then the
exit from `W`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64

theorem streamInitPre_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint
    (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) (.block streamInitPre) h).isSome = true := ⟨_, by taint_decide⟩

theorem streamAadPre_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint
    (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5]) (.block streamAadPre) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem streamInit_ct [VG.Proof.Gcm.RISCV64.GhashLaw] : ConstantTime isa streamInitRISCV64.pre streamInitRISCV64.pub streamInit := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q3, q4, q5, q6, q7, qsp⟩ := hq
  have L : Lay (σ₁.gpr .a0) (σ₁.gpr .a3) (σ₁.gpr .a4) := by
    obtain ⟨-, -, dcs, dcw, -, -, dsw, wc, -, ws, ww, -, a0, a3, a4⟩ := h₁
    exact Lay.of wc ws ww dcs dcw dsw a0 a3 a4
  let I₀ : State → Prop := fun s => streamInitRISCV64.pre s ∧ s.gpr .a0 = σ₁.gpr .a0 ∧
    s.gpr .a1 = σ₁.gpr .a1 ∧ s.gpr .a2 = σ₁.gpr .a2 ∧ s.gpr .a3 = σ₁.gpr .a3 ∧ s.gpr .a4 = σ₁.gpr .a4 ∧
    s.sp = σ₁.sp
  refine ⟨I₀, ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨h₂, q3.symm, q4.symm, q5.symm, q6.symm, q7.symm,
    qsp.symm⟩, ?_⟩
  refine CT.seq (J := J0I (σ₁.gpr .a0) (σ₁.gpr .a3) (σ₁.gpr .a4) σ₁.sp (σ₁.gpr .a1) (σ₁.gpr .a2).toNat) ?_
    (fun s ⟨hs, e3, e4, e5, e6, e7, esp⟩ => WP.mono (si_entry hs) fun s₁ ⟨_, h29, h30, h31, hJ, _⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := streamInitPre_taint
    exact CT.taintEq (I := I₀) _ σ₁.gpr σ₁.sp (fun s ⟨_, e3, e4, e5, e6, e7, esp⟩ =>
      ⟨esp, by simp [e3, e4, e5, e6, e7]⟩) hc
  · rw [e3] at h29
    rw [e6] at h30
    rw [e7] at h31
    rw [e3, e4, e5, esp] at hJ
    exact ⟨s₁.gpr, _, h29, h30, h31, hJ⟩
  refine CT.seq (J := fun s => s.gpr .s0 = σ₁.gpr .a4 ∧ s.sp = σ₁.sp) (j0_ct L)
    (fun s ⟨V, H, h29, h30, h31, hJ⟩ => WP.mono (j0_ok (L.v h29 h30 h31) hJ) fun s₂ h₂ =>
      ⟨(h₂.env.fr _ (by decide)).trans h31, h₂.env.sp⟩) ?_
  obtain ⟨_, hc⟩ := restore_taint
  exact CT.taintEq _ (fun _ => σ₁.gpr .a4) σ₁.sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

theorem streamAad_ct [VG.Proof.Gcm.RISCV64.GhashLaw] : ConstantTime isa streamAadRISCV64.pre streamAadRISCV64.pub streamAad := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q3, q4, q5, q6, q7, q8, qsp⟩ := hq
  have L : Lay (σ₁.gpr .a0) (σ₁.gpr .a1) (σ₁.gpr .a5) := by
    obtain ⟨-, -, dcs, dcw, -, -, dsw, wc, -, ws, ww, -, a0, a1, a5⟩ := h₁
    exact Lay.of wc ws ww dcs dcw dsw a0 a1 a5
  let q := (σ₁.gpr .a2).toNat % 16
  have hq16 : q < 16 := Nat.mod_lt _ (by decide)
  let I₀ : State → Prop := fun s => streamAadRISCV64.pre s ∧ s.gpr .a0 = σ₁.gpr .a0 ∧
    s.gpr .a1 = σ₁.gpr .a1 ∧ s.gpr .a2 = σ₁.gpr .a2 ∧ s.gpr .a3 = σ₁.gpr .a3 ∧ s.gpr .a4 = σ₁.gpr .a4 ∧
    s.gpr .a5 = σ₁.gpr .a5 ∧ s.sp = σ₁.sp
  refine ⟨I₀, ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨h₂, q3.symm, q4.symm, q5.symm, q6.symm, q7.symm,
    q8.symm, qsp.symm⟩, ?_⟩
  refine CT.seq (J := AbsI (σ₁.gpr .a0) (σ₁.gpr .a1) (σ₁.gpr .a5) σ₁.sp 16 (σ₁.gpr .a3) (σ₁.gpr .a4).toNat q)
    ?_ (fun s ⟨hs, e3, e4, e5, e6, e7, e8, esp⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := streamAadPre_taint
    exact CT.taintEq (I := I₀) _ σ₁.gpr σ₁.sp (fun s ⟨_, e3, e4, e5, e6, e7, e8, esp⟩ =>
      ⟨esp, by simp [e3, e4, e5, e6, e7, e8]⟩) hc
  · have hx : (List.replicate q (0 : Byte)).length % 16 = (s.gpr .a2).toNat % 16 := by
      rw [List.length_replicate, e5, Nat.mod_mod]
    refine WP.mono (aad_entry hs hx) fun s₁ ⟨_, h29, h30, h31, hIn, _⟩ => ?_
    rw [e3] at h29 hIn
    rw [e4] at h30
    rw [e8] at h31
    rw [e6, e7, esp] at hIn
    exact ⟨s₁.gpr, _, _, h29, h30, h31, by rw [List.length_replicate, Nat.mod_mod], hIn⟩
  refine CT.seq (J := fun s => s.gpr .s0 = σ₁.gpr .a5 ∧ s.sp = σ₁.sp) (absorb_ct L (.inr rfl) hq16)
    (fun s ⟨V, H, x, h29, h30, h31, _, hs⟩ => WP.mono (absorb_ok (L.v h29 h30 h31) (.inr rfl) hs)
      fun s₂ h₂ => ⟨(h₂.env.fr _ (by decide)).trans h31, h₂.env.sp⟩) ?_
  obtain ⟨_, hc⟩ := restore_taint
  exact CT.taintEq _ (fun _ => σ₁.gpr .a5) σ₁.sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

end VG.Proof.AesGcm.RISCV64

end

end

/-! ### `AesGcm.RISCV64.CTCryptFn`, which only this module used -/

section

/-!
# AES-GCM on RISC-V: `vg_aes_gcm_stream_encrypt` and `vg_aes_gcm_stream_decrypt` are constant time

Untrusted: everything here is checked by Lean. The entry by the taint
analysis from the public arguments, which it keeps in registers the pieces
preserve (`DI`); then `crypt` (`crypt_ct`) and `textAbsorb`
(`textAbsorb_ct`), in either order, from the invariants their correctness
gives; then the exit from `W`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64

/-- After the entry: the arguments kept, `len` (`N`) bytes at `data` (`D`),
after `aad_len` (`A`) bytes of additional data and `text_len` (`T`) of
text, and `R` rounds. -/
def DI (c st w sp D : Addr) (R : Nat) (N A T : BitVec 64) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧ V .s9 = D ∧ V .s8 = N ∧ V .s10 = A ∧
    V .s11 = T ∧ V .s3 = BitVec.ofNat 64 R ∧ (R = 10 ∨ R = 12 ∨ R = 14) ∧ Env V sp s ∧ DataW c st w s D N.toNat

/-- Before `crypt`, with the arguments kept. -/
def CI (c st w sp D : Addr) (R : Nat) (N A T : BitVec 64) (s : State) : Prop :=
  ∃ V icb P, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧ V .s9 = D ∧ V .s8 = N ∧ V .s10 = A ∧ V .s11 = T ∧
    P % 16 = T.toNat % 16 ∧ CrIn false V sp R icb P D D N.toNat s

theorem cryptEntry_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint
    (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7]) (.block cryptEntry) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem cryptEntryArgs_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint
    (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7]) (.block (cryptEntry ++ textArgs)) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem textArgs_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s8, .s9, .s11])
    (.block textArgs) h).isSome = true := ⟨_, by taint_decide⟩

/-- The entry. -/
theorem sc_DI {s₀ : State} (h : streamCryptPre s₀) :
    WP isa (.block cryptEntry) s₀ (DI (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a7) s₀.sp (s₀.gpr .a5)
      (s₀.gpr .a1).toNat (s₀.gpr .a6) (s₀.gpr .a3) (s₀.gpr .a4)) :=
  WP.mono (sc1_wp (sc_W h) (sc_al h)) fun s₁ h1 => ⟨s₁.gpr, h1.s2, h1.s1, h1.s0, h1.s9, h1.s8, h1.s10, h1.s11,
    by rw [h1.s3, BitVec.ofNat_toNat, BitVec.setWidth_eq], sc_R h, sc_env h h1,
    sc_dataW h h1.en.keeps.wr h1.en.keeps.sp⟩

section
variable {c st w sp D : Addr} {R : Nat} {N A T : BitVec 64}

theorem di_ta {s : State} (h : DI c st w sp D R N A T s) : TA c st w sp D N A T s :=
  let ⟨V, h29, h30, h31, h20, h19, h22, h23, _, _, he, hd⟩ := h
  ⟨V, h29, h30, h31, h20, h19, h22, h23, he, hd.ok⟩

theorem ci_cr {s : State} (h : CI c st w sp D R N A T s) : CrI false c st w sp R D D N.toNat (T.toNat % 16) s :=
  let ⟨V, icb, P, h29, h30, h31, _, _, _, _, hP, ci⟩ := h
  ⟨V, icb, P, h29, h30, h31, hP, ci⟩

theorem ta_exit {s : State} (h : TA c st w sp D N A T s) : s.gpr .s0 = w ∧ s.sp = sp :=
  let ⟨_, _, _, h31, _, _, _, _, he, _⟩ := h
  ⟨(he.fr _ (by decide)).trans h31, he.sp⟩

/-- The arguments of `crypt`. -/
theorem di_textArgs {s : State} (h : DI c st w sp D R N A T s) :
    WP isa (.block textArgs) s (CI c st w sp D R N A T) := by
  obtain ⟨V, h29, h30, h31, h20, h19, h22, h23, h28, hR, he, hd⟩ := h
  refine WP.mono textArgs_ok fun s₂ ⟨h24, h25, h26, hg, hk⟩ => ?_
  have he₂ := he.keep (fun r hr => hg r (by revert r; decide) (by revert r; decide) (by revert r; decide))
    hk.sp hk.rd hk.wr
  exact ⟨V, 0, T.toNat, h29, h30, h31, h20, h19, h22, h23, rfl, he₂, by rw [h24, he.fr _ (by decide), h20],
    by rw [h25, he.fr _ (by decide), h19, BitVec.ofNat_toNat, BitVec.setWidth_eq],
    by rw [h26, he.fr _ (by decide), h23], h28, hR, by rw [h29, h30, h31]; exact hd.of_eq hk.rd hk.wr hk.sp,
    by rw [h30, h31]; exact (hd.of_eq hk.rd hk.wr hk.sp).ok, rfl, Bool.noConfusion⟩

variable (L : Lay c st w)
include L

theorem ci_crypt {s : State} (h : CI c st w sp D R N A T s) : WP isa crypt s (TA c st w sp D N A T) := by
  obtain ⟨V, icb, P, h29, h30, h31, h20, h19, h22, h23, _, ci⟩ := h
  refine WP.mono (WP.with_rdwr (crypt_ok (L.v h29 h30 h31) ci)) fun s' ⟨co, rd, wr, sp'⟩ =>
    ⟨V, h29, h30, h31, h20, h19, h22, h23, co.env, ?_⟩
  have := ci.data.ok.of_eq rd wr sp'
  rw [h30, h31] at this
  exact this

theorem di_textAbsorb [VG.Proof.Gcm.RISCV64.GhashLaw] {s : State} (h : DI c st w sp D R N A T s) :
    WP isa textAbsorb s (DI c st w sp D R N A T) := by
  obtain ⟨V, h29, h30, h31, h20, h19, h22, h23, h28, hR, he, hd⟩ := h
  refine WP.mono (WP.with_rdwr (textAbsorb_ok (L.v h29 h30 h31) (a := List.replicate (A.toNat % 16) 0)
    (ct := List.replicate T.toNat 0) he rfl (by rw [h20, h19, h30, h31]; exact hd.ok) (by simp [h22])
    (by simp [h23]))) fun s' ⟨ta, rd, wr, sp'⟩ => ⟨V, h29, h30, h31, h20, h19, h22, h23, h28, hR, ta.env,
      hd.of_eq rd wr sp'⟩

theorem ta_textAbsorb [VG.Proof.Gcm.RISCV64.GhashLaw] {s : State} (h : TA c st w sp D N A T s) :
    WP isa textAbsorb s fun s' => s'.gpr .s0 = w ∧ s'.sp = sp := by
  obtain ⟨V, h29, h30, h31, h20, h19, h22, h23, he, hd⟩ := h
  exact WP.mono (textAbsorb_ok (L.v h29 h30 h31) (a := List.replicate (A.toNat % 16) 0)
    (ct := List.replicate T.toNat 0) he rfl (by rw [h20, h19, h30, h31]; exact hd) (by simp [h22])
    (by simp [h23])) fun s' ta => ⟨(ta.env.fr _ (by decide)).trans h31, ta.env.sp⟩

end

/-- The invariant of the entry, from the public arguments of `σ`. -/
abbrev SCI (σ : State) (s : State) : Prop :=
  streamCryptPre s ∧ s.gpr .a0 = σ.gpr .a0 ∧ s.gpr .a1 = σ.gpr .a1 ∧ s.gpr .a2 = σ.gpr .a2 ∧
    s.gpr .a3 = σ.gpr .a3 ∧ s.gpr .a4 = σ.gpr .a4 ∧ s.gpr .a5 = σ.gpr .a5 ∧ s.gpr .a6 = σ.gpr .a6 ∧
    s.gpr .a7 = σ.gpr .a7 ∧ s.sp = σ.sp

theorem sci_of {σ₁ σ₂ : State} (h₁ : streamCryptPre σ₁) (h₂ : streamCryptPre σ₂) (hq : streamCryptPub σ₁ σ₂) :
    SCI σ₁ σ₁ ∧ SCI σ₁ σ₂ := by
  obtain ⟨q3, q4, q5, q6, q7, q8, q9, q10, qsp⟩ := hq
  exact ⟨⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨h₂, q3.symm, q4.symm, q5.symm, q6.symm, q7.symm, q8.symm, q9.symm, q10.symm, qsp.symm⟩⟩

theorem sci_DI {σ s : State} (h : SCI σ s) :
    WP isa (.block cryptEntry) s (DI (σ.gpr .a0) (σ.gpr .a2) (σ.gpr .a7) σ.sp (σ.gpr .a5)
      (σ.gpr .a1).toNat (σ.gpr .a6) (σ.gpr .a3) (σ.gpr .a4)) := by
  obtain ⟨hs, e3, e4, e5, e6, e7, e8, e9, e10, esp⟩ := h
  have := sc_DI hs
  rw [e3, e4, e5, e6, e7, e8, e9, e10, esp] at this
  exact this

theorem streamEncrypt_ct [VG.Proof.Gcm.RISCV64.GhashLaw] :
    ConstantTime isa streamEncryptRISCV64.pre streamEncryptRISCV64.pub streamEncrypt := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  have h₁' : streamCryptPre σ₁ := h₁
  have L := scLay h₁'
  obtain ⟨i₁, i₂⟩ := sci_of h₁' h₂ hq
  refine ⟨SCI σ₁, i₁, i₂, ?_⟩
  refine CT.seq (J := CI (σ₁.gpr .a0) (σ₁.gpr .a2) (σ₁.gpr .a7) σ₁.sp (σ₁.gpr .a5) (σ₁.gpr .a1).toNat
    (σ₁.gpr .a6) (σ₁.gpr .a3) (σ₁.gpr .a4)) ?_
    (fun s h => WP.block_append (WP.mono (sci_DI h) fun _ h' => di_textArgs h')) ?_
  · obtain ⟨_, hc⟩ := cryptEntryArgs_taint
    exact CT.taintEq _ σ₁.gpr σ₁.sp (fun s ⟨_, e3, e4, e5, e6, e7, e8, e9, e10, esp⟩ =>
      ⟨esp, by simp [e3, e4, e5, e6, e7, e8, e9, e10]⟩) hc
  refine CT.seq ((crypt_ct L).mono fun _ h => ci_cr h) (fun _ h => ci_crypt L h) ?_
  refine CT.seq (J := fun s => s.gpr .s0 = σ₁.gpr .a7 ∧ s.sp = σ₁.sp) (textAbsorb_ct L)
    (fun _ h => ta_textAbsorb L h) ?_
  obtain ⟨_, hc⟩ := restore_taint
  exact CT.taintEq _ (fun _ => σ₁.gpr .a7) σ₁.sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

theorem streamDecrypt_ct [VG.Proof.Gcm.RISCV64.GhashLaw] :
    ConstantTime isa streamDecryptRISCV64.pre streamDecryptRISCV64.pub streamDecrypt := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  have h₁' : streamCryptPre σ₁ := h₁
  have L := scLay h₁'
  obtain ⟨i₁, i₂⟩ := sci_of h₁' h₂ hq
  refine ⟨SCI σ₁, i₁, i₂, ?_⟩
  refine CT.seq (J := DI (σ₁.gpr .a0) (σ₁.gpr .a2) (σ₁.gpr .a7) σ₁.sp (σ₁.gpr .a5) (σ₁.gpr .a1).toNat
    (σ₁.gpr .a6) (σ₁.gpr .a3) (σ₁.gpr .a4)) ?_ (fun s h => sci_DI h) ?_
  · obtain ⟨_, hc⟩ := cryptEntry_taint
    exact CT.taintEq _ σ₁.gpr σ₁.sp (fun s ⟨_, e3, e4, e5, e6, e7, e8, e9, e10, esp⟩ =>
      ⟨esp, by simp [e3, e4, e5, e6, e7, e8, e9, e10]⟩) hc
  refine CT.seq ((textAbsorb_ct L).mono fun _ h => di_ta h) (fun _ h => di_textAbsorb L h) ?_
  refine CT.seq ?_ (fun _ h => di_textArgs h) ?_
  · obtain ⟨_, hc⟩ := textArgs_taint
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, a20, a19, _, a23, _, _, e₁, _⟩
      ⟨_, _, _, _, b20, b19, _, b23, _, _, e₂, _⟩ => ⟨e₁.sp.trans e₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [e₁.fr _ (by decide), e₂.fr _ (by decide), a19, b19]
    · rw [e₁.fr _ (by decide), e₂.fr _ (by decide), a20, b20]
    · rw [e₁.fr _ (by decide), e₂.fr _ (by decide), a23, b23]
  refine CT.seq ((crypt_ct L).mono fun _ h => ci_cr h) (fun _ h => ci_crypt L h) ?_
  obtain ⟨_, hc⟩ := restore_taint
  exact CT.taintEq _ (fun _ => σ₁.gpr .a7) σ₁.sp (fun s h => ⟨(ta_exit h).2, by simp [(ta_exit h).1]⟩) hc

end VG.Proof.AesGcm.RISCV64

end

end

/-!
# AES-GCM on RISC-V: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time,
a state satisfying each precondition, and the shared contracts of
`Spec/Gcm/Contract.lean` with the working space as a last argument
(`Proof/AesGcm/Scratch.lean`), with the 2048 bytes of stack `vg_ghash`'s
frame takes (but for `init`, which does not call it).
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64

theorem init_correct (s : State) (hs : initRISCV64.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ initRISCV64.post s s' :=
  init_wp hs

theorem streamInit_correct [VG.Proof.Gcm.RISCV64.GhashLaw] (s : State) (hs : streamInitRISCV64.pre s) :
    ∃ t s', Exec isa streamInit s t s' ∧ abiPreserved s s' ∧ streamInitRISCV64.post s s' :=
  streamInit_wp hs

theorem streamAad_correct [VG.Proof.Gcm.RISCV64.GhashLaw] (s : State) (hs : streamAadRISCV64.pre s) :
    ∃ t s', Exec isa streamAad s t s' ∧ abiPreserved s s' ∧ streamAadRISCV64.post s s' :=
  streamAad_wp hs

theorem streamEncrypt_correct [VG.Proof.Gcm.RISCV64.GhashLaw] (s : State) (hs : streamEncryptRISCV64.pre s) :
    ∃ t s', Exec isa streamEncrypt s t s' ∧ abiPreserved s s' ∧ streamEncryptRISCV64.post s s' :=
  streamEncrypt_wp hs

theorem streamDecrypt_correct [VG.Proof.Gcm.RISCV64.GhashLaw] (s : State) (hs : streamDecryptRISCV64.pre s) :
    ∃ t s', Exec isa streamDecrypt s t s' ∧ abiPreserved s s' ∧ streamDecryptRISCV64.post s s' :=
  streamDecrypt_wp hs

theorem streamFinish_correct [VG.Proof.Gcm.RISCV64.GhashLaw] (s : State) (hs : streamFinishRISCV64.pre s) :
    ∃ t s', Exec isa streamFinish s t s' ∧ abiPreserved s s' ∧ streamFinishRISCV64.post s s' :=
  streamFinish_wp hs

theorem streamVerify_correct [VG.Proof.Gcm.RISCV64.GhashLaw] (s : State) (hs : streamVerifyRISCV64.pre s) :
    ∃ t s', Exec isa streamVerify s t s' ∧ abiPreserved s s' ∧ streamVerifyRISCV64.post s s' :=
  streamVerify_wp hs

theorem seal_correct [VG.Proof.Gcm.RISCV64.GhashLaw] (s : State) (hs : sealRISCV64.pre s) :
    ∃ t s', Exec isa «seal» s t s' ∧ abiPreserved s s' ∧ sealRISCV64.post s s' :=
  seal_wp hs

theorem open_correct [VG.Proof.Gcm.RISCV64.GhashLaw] (s : State) (hs : openRISCV64.pre s) :
    ∃ t s', Exec isa «open» s t s' ∧ abiPreserved s s' ∧ openRISCV64.post s s' :=
  open_wp hs

/-! ## States satisfying the preconditions (with empty buffers) -/

def initSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 16 | .a2 => 0x2000 | .a3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 256⟩, ⟨0x4000, 2560⟩]

def streamInitSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a3 => 0x3000 | .a4 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩]

def streamAadSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x3000 | .a3 => 0x2000 | .a5 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩]

def streamCryptSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 10 | .a2 => 0x3000 | .a5 => 0x2000 | .a7 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩, ⟨0x4000, 2560⟩]

def finSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 10 | .a2 => 0x3000 | .a5 => 0x5000 | .a6 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x5000, 16⟩, ⟨0x4000, 2560⟩]

def verSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 10 | .a2 => 0x3000 | .a5 => 0x5000 | .a7 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x5000, 0⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩]

/-! ## The shared contracts -/

theorem init_verified :
    Verified RISCV64.target init (Proof.AesGcm.initScratchContract RISCV64.abi) :=
  Verified.of_correct init_correct init_ct (by
    sig_implies [Proof.AesGcm.initScratchContract, Proof.AesGcm.initScratchSig, Spec.Gcm.initPre,
      Spec.Gcm.initPost, initRISCV64, RISCV64.abi, RISCV64.argRegs, stackBelow, stkOk, stkAll, and_true] [initSat] using initSat)

theorem streamInit_verified [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target streamInit (Proof.AesGcm.streamInitScratchContract RISCV64.abi 2048) :=
  Verified.of_correct streamInit_correct streamInit_ct (by
    sig_implies [Proof.AesGcm.streamInitScratchContract, Proof.AesGcm.streamInitScratchSig,
      Spec.Gcm.streamInitPost, streamInitRISCV64, RISCV64.abi, RISCV64.argRegs, stackBelow, stkOk, stkAll, and_true]
      [streamInitSat] using streamInitSat)

theorem streamAad_verified [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target streamAad (Proof.AesGcm.streamAadScratchContract RISCV64.abi 2048) :=
  Verified.of_correct streamAad_correct streamAad_ct (by
    sig_implies [Proof.AesGcm.streamAadScratchContract, Proof.AesGcm.streamAadScratchSig,
      Spec.Gcm.streamAadPost, streamAadRISCV64, RISCV64.abi, RISCV64.argRegs, stackBelow, stkOk, stkAll, and_true]
      [streamAadSat] using streamAadSat)

theorem streamEncrypt_verified [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target streamEncrypt (Proof.AesGcm.streamEncryptScratchContract RISCV64.abi 2048) :=
  Verified.of_correct streamEncrypt_correct streamEncrypt_ct (by
    sig_implies [Proof.AesGcm.streamEncryptScratchContract, Proof.AesGcm.streamCryptScratchSig,
      Spec.Gcm.streamTextPre, Proof.AesGcm.streamEncryptRoundsPost, streamEncryptRISCV64, streamCryptPre,
      streamCryptPub, rounds, RISCV64.abi, RISCV64.argRegs, stackBelow, stkOk, stkAll, and_true] [streamCryptSat] using streamCryptSat)

theorem streamDecrypt_verified [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target streamDecrypt (Proof.AesGcm.streamDecryptScratchContract RISCV64.abi 2048) :=
  Verified.of_correct streamDecrypt_correct streamDecrypt_ct (by
    sig_implies [Proof.AesGcm.streamDecryptScratchContract, Proof.AesGcm.streamCryptScratchSig,
      Spec.Gcm.streamTextPre, Proof.AesGcm.streamDecryptRoundsPost, streamDecryptRISCV64, streamCryptPre,
      streamCryptPub, rounds, RISCV64.abi, RISCV64.argRegs, stackBelow, stkOk, stkAll, and_true] [streamCryptSat] using streamCryptSat)

theorem streamFinish_verified [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target streamFinish (Proof.AesGcm.streamFinishScratchContract RISCV64.abi 2048) :=
  Verified.of_correct streamFinish_correct streamFinish_ct (by
    sig_implies [Proof.AesGcm.streamFinishScratchContract, Proof.AesGcm.streamFinishScratchSig,
      Spec.Gcm.streamFinishPre, Proof.AesGcm.streamFinishRoundsPost, streamFinishRISCV64, finPre, rounds, RISCV64.abi,
      RISCV64.argRegs, stackBelow, stkOk, stkAll, and_true] [finSat] using finSat)

theorem streamVerify_verified [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target streamVerify (Proof.AesGcm.streamVerifyScratchContract RISCV64.abi 2048) :=
  Verified.of_correct streamVerify_correct streamVerify_ct (by
    sig_implies [Proof.AesGcm.streamVerifyScratchContract, Proof.AesGcm.streamVerifyScratchSig,
      Spec.Gcm.streamVerifyPre, Proof.AesGcm.streamVerifyRoundsPost, streamVerifyRISCV64, verPre, rounds, RISCV64.abi,
      RISCV64.argRegs, stackBelow, stkOk, stkAll, and_true] [verSat] using verSat)

/-- `tag` at `0x5000` and the working space at `0x6000`, the stack arguments. -/
def sealSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 10 | .a2 => 0x2000 | .a4 => 0x3000 | .a6 => 0x4000 | _ => 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9001 then 0x50 else bif Nat.beq a.toNat 0x9009 then 0x60 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x9000, 16⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x5000, 16⟩, ⟨0x6000, 2560⟩]

theorem seal_verified [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target «seal» (Proof.AesGcm.sealScratchContract RISCV64.abi 2048) :=
  Verified.of_correct seal_correct seal_ct (by
    sig_implies [Proof.AesGcm.sealScratchContract, Proof.AesGcm.sealScratchSig, Spec.Gcm.sealPre,
      Proof.AesGcm.sealRoundsPost, sealRISCV64, sealPre, onePub, args, rounds, RISCV64.abi, RISCV64.argRegs, stackBelow, stkOk, stkAll, and_true,
      stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
      [sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealSat)

/-- `tag` at `0x5000`, `tag_len` 0 and the working space at `0x6000`, the stack arguments. -/
def openSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 10 | .a2 => 0x2000 | .a4 => 0x3000 | .a6 => 0x4000 | _ => 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9001 then 0x50 else bif Nat.beq a.toNat 0x9011 then 0x60 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x5000, 0⟩, ⟨0x9000, 24⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x6000, 2560⟩]

/-- The leak `open` may have: whether it succeeds. -/
theorem leak_bool {a b : Bool} (h : [if a = true then 1 else 0] = [if b = true then 1 else 0]) : a = b := by
  cases a <;> cases b <;> simp_all

/-- The postconditions match on `openResult`; the result is the low 32 bits
of `a0`; and `open`'s public data include its leak, whether it succeeds (for
`rounds` of 10, 12 or 14). -/
theorem open_verified [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target «open» (Proof.AesGcm.openScratchContract RISCV64.abi 2048) :=
  Verified.of_correct open_correct open_ct
    { pre := by
        sig_implies_pre [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openPre,
          openRISCV64, openPre, onePub, args, rounds, RISCV64.abi, RISCV64.argRegs, stackBelow, stkOk, stkAll, and_true,
          stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
      post := by
        intro s s' _ h
        sig_eval [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Proof.AesGcm.openRoundsPost, RISCV64.abi,
          RISCV64.argRegs, stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
        simp only [openRISCV64] at h
        intro _
        exact h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openLeak, openRISCV64,
          openPre, onePub, args, rounds, RISCV64.abi, RISCV64.argRegs, stackBelow, stkOk, stkAll, and_true, stackArg, stackArgAddr, List.getD,
          List.range, List.range.loop] at h
        obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2⟩ := h
        refine ⟨⟨h3, h4, h5, h6, h7, h8, h9, h10, hsp, fun i hi => ?_⟩, fun hr => leak_bool ?_⟩
        · rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega_using [hi]) with rfl | rfl | rfl
          · exact a0
          · exact a1
          · exact a2
        · have e₁ : ¬((s₁.gpr .a1).toNat = 10 ∨ (s₁.gpr .a1).toNat = 12 ∨ (s₁.gpr .a1).toNat = 14) ↔ False :=
            ⟨fun x => x hr, False.elim⟩
          have e₂ : ¬((s₂.gpr .a1).toNat = 10 ∨ (s₂.gpr .a1).toNat = 12 ∨ (s₂.gpr .a1).toNat = 14) ↔ False :=
            ⟨fun x => x (h4 ▸ hr), False.elim⟩
          simp only [e₁, e₂, ↓reduceIte] at hl
          exact hl
      sat := by
        sig_implies_sat [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openPre,
          openRISCV64, openPre, onePub, args, rounds, RISCV64.abi, RISCV64.argRegs, stackBelow, stkOk, stkAll, and_true,
          stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
          [openSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using openSat }

end VG.Proof.AesGcm.RISCV64

/-! ## With the working space on the stack

Each function runs its code, proved with the working space as an argument
(`Verified.lean`), in a frame that allocates it: the functions whose
arguments all arrive in registers in a frame of 2560 bytes, the working
space in the next register (`Verified.stackScratchL`); `seal` and `open`,
whose last arguments arrive on the stack, in a frame that copies them and
then passes the working space's address (`Verified.stackScratchArgs`).
-/

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64

/-- A state satisfying `vg_aes_gcm_init`'s precondition, without the working
space. -/
def initFrameSat : State := { initSat with wr := [⟨0x2000, 256⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Gcm.initContract RISCV64.abi 2560).pre s := by
  implies_sat [Spec.Gcm.initContract, Spec.Gcm.initSig, Spec.Gcm.initPre, Spec.Gcm.initPost,
    RISCV64.abi, RISCV64.argRegs] [initFrameSat, initSat] using initFrameSat

theorem init_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2560 .a3 init)
      (Spec.Gcm.initContract RISCV64.abi 2560) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Gcm.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Gcm.initPre RISCV64.abi.ptrBits) (post := Spec.Gcm.initPost RISCV64.abi.ptrBits)
    (wa := true) (stack := 0) (bytes := 2560) init_verified (by decide) (by decide) (Proof.AesGcm.initPostOut_local _)
    initFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_init`'s precondition, without the
working space. -/
def streamInitFrameSat : State := { streamInitSat with wr := [⟨0x3000, 80⟩] }

theorem streamInitFrameSat_pre : ∃ s, (Spec.Gcm.streamInitContract RISCV64.abi 4608).pre s := by
  implies_sat [Spec.Gcm.streamInitContract, Spec.Gcm.streamInitSig, Spec.Gcm.streamInitPost,
    RISCV64.abi, RISCV64.argRegs] [streamInitFrameSat, streamInitSat] using streamInitFrameSat

theorem streamInit_framed [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2560 .a4 streamInit)
      (Spec.Gcm.streamInitContract RISCV64.abi 4608) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Gcm.streamInitSig) (nm := "scratch") (e := .u64)
    (n := 320) (post := Spec.Gcm.streamInitPost RISCV64.abi.ptrBits) (wa := true) (stack := 2048)
    (bytes := 2560) streamInit_verified (by decide) (by decide)
    (fun vs m m₁ m₂ r hl _ => Proof.AesGcm.streamInitPostOut_local _ vs m m₁ m₂ r hl)
    streamInitFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_aad`'s precondition, without the
working space. -/
def streamAadFrameSat : State := { streamAadSat with wr := [⟨0x3000, 80⟩] }

theorem streamAadFrameSat_pre : ∃ s, (Spec.Gcm.streamAadContract RISCV64.abi 4608).pre s := by
  implies_sat [Spec.Gcm.streamAadContract, Spec.Gcm.streamAadSig, Spec.Gcm.streamAadPost,
    RISCV64.abi, RISCV64.argRegs] [streamAadFrameSat, streamAadSat] using streamAadFrameSat

theorem streamAad_framed [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2560 .a5 streamAad)
      (Spec.Gcm.streamAadContract RISCV64.abi 4608) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Gcm.streamAadSig) (nm := "scratch") (e := .u64)
    (n := 320) (post := Spec.Gcm.streamAadPost RISCV64.abi.ptrBits) (wa := true) (stack := 2048)
    (bytes := 2560) streamAad_verified (by decide) (by decide)
    (fun vs m m₁ m₂ r hl _ => Proof.AesGcm.streamAadPostOut_local _ vs m m₁ m₂ r hl)
    streamAadFrameSat_pre

/-- A state satisfying the preconditions of `vg_aes_gcm_stream_encrypt` and
`vg_aes_gcm_stream_decrypt`, without the working space. -/
def streamCryptFrameSat : State := { streamCryptSat with wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩] }

theorem streamEncryptFrameSat_pre : ∃ s, (Proof.AesGcm.streamEncryptRoundsContract RISCV64.abi 4608).pre s := by
  implies_sat [Proof.AesGcm.streamEncryptRoundsContract, Spec.Gcm.streamCryptSig, Spec.Gcm.streamTextPre,
    Proof.AesGcm.streamEncryptRoundsPost, RISCV64.abi, RISCV64.argRegs] [streamCryptFrameSat, streamCryptSat]
    using streamCryptFrameSat

theorem streamEncrypt_framed [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2560 .a7 streamEncrypt)
      (Proof.AesGcm.streamEncryptRoundsContract RISCV64.abi 4608) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamTextPre RISCV64.abi.ptrBits)
    (post := Proof.AesGcm.streamEncryptRoundsPost RISCV64.abi.ptrBits) (wa := true) (stack := 2048)
    (bytes := 2560) streamEncrypt_verified (by decide) (by decide)
    (fun vs m m₁ m₂ r hl _ => Proof.AesGcm.streamEncryptPostOut_local _ vs m m₁ m₂ r hl)
    streamEncryptFrameSat_pre

theorem streamDecryptFrameSat_pre : ∃ s, (Proof.AesGcm.streamDecryptRoundsContract RISCV64.abi 4608).pre s := by
  implies_sat [Proof.AesGcm.streamDecryptRoundsContract, Spec.Gcm.streamCryptSig, Spec.Gcm.streamTextPre,
    Proof.AesGcm.streamDecryptRoundsPost, RISCV64.abi, RISCV64.argRegs] [streamCryptFrameSat, streamCryptSat]
    using streamCryptFrameSat

theorem streamDecrypt_framed [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2560 .a7 streamDecrypt)
      (Proof.AesGcm.streamDecryptRoundsContract RISCV64.abi 4608) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamTextPre RISCV64.abi.ptrBits)
    (post := Proof.AesGcm.streamDecryptRoundsPost RISCV64.abi.ptrBits) (wa := true) (stack := 2048)
    (bytes := 2560) streamDecrypt_verified (by decide) (by decide)
    (fun vs m m₁ m₂ r hl _ => Proof.AesGcm.streamDecryptPostOut_local _ vs m m₁ m₂ r hl)
    streamDecryptFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_finish`'s precondition, without
the working space. -/
def finFrameSat : State := { finSat with wr := [⟨0x3000, 80⟩, ⟨0x5000, 16⟩] }

theorem finFrameSat_pre : ∃ s, (Proof.AesGcm.streamFinishRoundsContract RISCV64.abi 4608).pre s := by
  implies_sat [Proof.AesGcm.streamFinishRoundsContract, Spec.Gcm.streamFinishSig, Spec.Gcm.streamFinishPre,
    Proof.AesGcm.streamFinishRoundsPost, RISCV64.abi, RISCV64.argRegs] [finFrameSat, finSat] using finFrameSat

theorem streamFinish_framed [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2560 .a6 streamFinish)
      (Proof.AesGcm.streamFinishRoundsContract RISCV64.abi 4608) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Gcm.streamFinishSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamFinishPre RISCV64.abi.ptrBits)
    (post := Proof.AesGcm.streamFinishRoundsPost RISCV64.abi.ptrBits) (wa := true) (stack := 2048)
    (bytes := 2560) streamFinish_verified (by decide) (by decide)
    (fun vs m m₁ m₂ r hl _ => Proof.AesGcm.streamFinishPostOut_local _ vs m m₁ m₂ r hl)
    finFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_verify`'s precondition, without
the working space. -/
def verFrameSat : State := { verSat with wr := [⟨0x3000, 80⟩] }

theorem verFrameSat_pre : ∃ s, (Proof.AesGcm.streamVerifyRoundsContract RISCV64.abi 4608).pre s := by
  implies_sat [Proof.AesGcm.streamVerifyRoundsContract, Spec.Gcm.streamVerifySig, Spec.Gcm.streamVerifyPre,
    Proof.AesGcm.streamVerifyRoundsPost, RISCV64.abi, RISCV64.argRegs] [verFrameSat, verSat] using verFrameSat

theorem streamVerify_framed [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2560 .a7 streamVerify)
      (Proof.AesGcm.streamVerifyRoundsContract RISCV64.abi 4608) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Gcm.streamVerifySig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamVerifyPre RISCV64.abi.ptrBits)
    (post := Proof.AesGcm.streamVerifyRoundsPost RISCV64.abi.ptrBits) (wa := true) (stack := 2048)
    (bytes := 2560) streamVerify_verified (by decide) (by decide)
    (fun vs m m₁ m₂ r hl _ => Proof.AesGcm.streamVerifyPostOut_local _ vs m m₁ m₂ r hl)
    verFrameSat_pre

/-- A state satisfying `vg_aes_gcm_seal`'s precondition, without the working
space: `tag` alone on the stack. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x9000, 8⟩],
                 wr := [⟨0x4000, 0⟩, ⟨0x5000, 16⟩] }

theorem sealFrameSat_pre : ∃ s, (Proof.AesGcm.sealRoundsContract RISCV64.abi 4624).pre s := by
  implies_sat [Proof.AesGcm.sealRoundsContract, Spec.Gcm.sealSig, Spec.Gcm.sealPre, Proof.AesGcm.sealRoundsPost, RISCV64.abi,
    RISCV64.argRegs, stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
    [sealFrameSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealFrameSat

/-- `seal`, whose `tag` arrives on the stack: the frame copies it, then the
working space's address, above its stack pointer (`Verified.stackScratchArgs`). -/
theorem seal_framed [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratchArgs 2576 1 «seal»)
      (Proof.AesGcm.sealRoundsContract RISCV64.abi 4624) :=
  RISCV64.Verified.stackScratchArgs (sig := Spec.Gcm.sealSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Spec.Gcm.sealPre RISCV64.abi.ptrBits) (post := Proof.AesGcm.sealRoundsPost RISCV64.abi.ptrBits)
    (wa := true) (stack := 2048) (bytes := 2576) (m := 1) seal_verified (by decide) (by decide)
    (Proof.AesGcm.sealPre_local _) (Proof.AesGcm.sealPost_local _)
    (fun vs m m₁ m₂ r hl _ => Proof.AesGcm.sealPostOut_local _ vs m m₁ m₂ r hl)
    sealFrameSat_pre

/-- A state satisfying `vg_aes_gcm_open`'s precondition, without the working
space: `tag` and `tag_len` alone on the stack. -/
def openFrameSat : State :=
  { openSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x5000, 0⟩, ⟨0x9000, 16⟩],
                 wr := [⟨0x4000, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Proof.AesGcm.openRoundsContract RISCV64.abi 4640).pre s := by
  implies_sat [Proof.AesGcm.openRoundsContract, Spec.Gcm.openSig, Spec.Gcm.openPre, Proof.AesGcm.openRoundsPost, Spec.Gcm.openLeak,
    RISCV64.abi, RISCV64.argRegs, stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
    [openFrameSat, openSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using openFrameSat

/-- `open`, whose `tag` and `tag_len` arrive on the stack, as `seal`'s `tag` does. -/
theorem open_framed [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratchArgs 2592 2 «open»)
      (Proof.AesGcm.openRoundsContract RISCV64.abi 4640) :=
  RISCV64.Verified.stackScratchArgs (sig := Spec.Gcm.openSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Spec.Gcm.openPre RISCV64.abi.ptrBits) (post := Proof.AesGcm.openRoundsPost RISCV64.abi.ptrBits)
    (wa := true) (stack := 2048) (bytes := 2592) (m := 2) (leak := some (Spec.Gcm.openLeak RISCV64.abi.ptrBits))
    open_verified (by decide) (by decide) (Proof.AesGcm.openPre_local _) (Proof.AesGcm.openPost_local _)
    (fun vs m m₁ m₂ r hl _ => Proof.AesGcm.openPostOut_local _ vs m m₁ m₂ r hl)
    openFrameSat_pre (hleak := Proof.AesGcm.openLeak_local _)

end VG.Proof.AesGcm.RISCV64
