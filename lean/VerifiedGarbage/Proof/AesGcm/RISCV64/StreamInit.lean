module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contract
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Fn
import VerifiedGarbage.Proof.AesGcm.RISCV64.Absorb
import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.Gcm.Ctr
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.AesGcm.RISCV64

/-!
# AES-GCM on RISCV64: `vg_aes_gcm_stream_init`

Untrusted: everything here is checked by Lean. The entry saves our caller's
registers and sets up `j0`'s arguments (`siEntry_ok`); `j0` writes `J₀`, a
zero accumulator and the first counter block, which is a state for the
nonce, no additional data and no text (`streamInit_wp`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom StreamRepr)

/-- After an entry that saved our caller's registers in `W`, from `s₀`. -/
structure Entered (s₀ : State) (W : Addr) (s : State) : Prop where
  keeps : Keeps' s₀ s
  saved : SavedAt s.mem W s₀
  frame : Frame [savedR W] s₀.mem s.mem

/-- The entry: `j0`'s arguments. -/
theorem siEntry_ok {s : State} (hW : Covers [⟨s.gpr .a4, 2560⟩] s.wr) (hal : (s.gpr .a4).toNat % 8 = 0) :
    WP isa (.block streamInitPre) s fun s' => Entered s (s.gpr .a4) s' ∧
      s'.gpr .s0 = s.gpr .a4 ∧ s'.gpr .s1 = s.gpr .a3 ∧ s'.gpr .s2 = s.gpr .a0 ∧
      s'.gpr .s4 = s.gpr .a1 ∧ s'.gpr .s5 = s.gpr .a2 ∧ s'.gpr .s7 = s.gpr .a2 := by
  refine WP.block_append (WP.mono (save_ok (b := .a4) hW hal) fun s₁ ⟨hg, h31, hk, hsv, hf⟩ => ?_)
  have e3 : s₁.gpr .a0 = s.gpr .a0 := hg _ (by decide)
  have e4 : s₁.gpr .a1 = s.gpr .a1 := hg _ (by decide)
  have e5 : s₁.gpr .a2 = s.gpr .a2 := hg _ (by decide)
  have e6 : s₁.gpr .a3 = s.gpr .a3 := hg _ (by decide)
  crun [Int.reduceNatCast', mov, e3, e4, e5, e6, h31]
  exact ⟨⟨hk.rd, hk.wr, hk.sp⟩, hsv, hf⟩

/-- After the entry: `j0`'s precondition, for the nonce and the hash subkey on entry. -/
theorem si_entry {s : State} (hs : streamInitRISCV64.pre s) :
    WP isa (.block streamInitPre) s fun s₁ => Entered s (s.gpr .a4) s₁ ∧ s₁.gpr .s2 = s.gpr .a0 ∧
      s₁.gpr .s1 = s.gpr .a3 ∧ s₁.gpr .s0 = s.gpr .a4 ∧
      J0In s₁.gpr s.sp (Spec.Gcm.ctxH s.mem (s.gpr .a0)) (s.gpr .a1) (s.gpr .a2).toNat s₁ ∧
      bytesAt s₁.mem (s.gpr .a1) (s.gpr .a2).toNat = bytesAt s.mem (s.gpr .a1) (s.gpr .a2).toNat := by
  simp only [streamInitRISCV64] at hs
  obtain ⟨hrd, hwr, dcs, dcw, dns, dnw, dsw, wc, wn, ws, ww, hstk, -, -, hal⟩ := hs
  generalize hCtx : s.gpr .a0 = Ctx at *
  generalize hNp : s.gpr .a1 = Np at *
  generalize hn : (s.gpr .a2).toNat = n at *
  generalize hSt : s.gpr .a3 = St at *
  generalize hW : s.gpr .a4 = W at *
  have hlt : n < 2 ^ 64 := hn ▸ (s.gpr .a2).isLt
  have hn' : s.gpr .a2 = BitVec.ofNat 64 n := by rw [← hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hWc : Covers [⟨W, 2560⟩] s.wr := by rw [hwr]; exact covers_mem (by simp)
  refine WP.mono (siEntry_ok (by rw [hW]; exact hWc) (by rw [hW]; exact hal)) fun s₁ ⟨en, h31, h30, h29, h24, h25, h18⟩ => ?_
  rw [hW] at en h31
  rw [hSt] at h30
  rw [hCtx] at h29
  rw [hNp] at h24
  rw [hn'] at h25 h18
  have perm : Perm Ctx St W s₁ :=
    (⟨covers_mem (by rw [hrd, hwr]; simp), covers_mem (by rw [hwr]; simp), hWc⟩ : Perm Ctx St W s).of_eq
      en.keeps.rd en.keeps.wr
  have hk : StkOk Ctx St W s.sp := hstk.stk (by simp) (by simp) (by simp)
  have he : Env s₁.gpr s.sp s₁ :=
    ⟨fun _ _ => rfl, en.keeps.sp, by rw [h29, h30, h31]; exact perm, by rw [h29, h30, h31, en.keeps.sp]; exact hk⟩
  have sW : Region.Sub (savedR W) ⟨W, 2560⟩ := Offset.sub_base _ (by decide)
  have hiv : bytesAt s₁.mem Np n = bytesAt s.mem Np n :=
    bytesAt_frame en.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dnw.sub_right sW) (by omega)
  have hH : blockAt s₁.mem (s₁.gpr .s2 + BitVec.ofNat 64 240) = Spec.Gcm.ctxH s.mem Ctx := by
    rw [h29, ctxH_eq]
    exact blockAt_frame en.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (dcw.sub_left (Offset.sub_base _ (by decide))).sub_right sW)
  refine ⟨en, h29, h30, h31, ⟨he, hH, h24, h25, h18, ?_⟩, hiv⟩
  rw [h30, h31]
  exact ⟨by rw [en.keeps.rd, en.keeps.wr, hrd]; exact covers_mem (by simp), hlt, wn, dns, dnw,
    by rw [en.keeps.sp]; exact hstk.buf (by simp)⟩

theorem streamInit_wp {s : State} (hs : streamInitRISCV64.pre s) :
    WP isa streamInit s fun s' => abiPreserved s s' ∧ streamInitRISCV64.post s s' := by
  have L₀ : Lay (s.gpr .a0) (s.gpr .a3) (s.gpr .a4) := by
    obtain ⟨-, -, dcs, dcw, -, -, dsw, wc, -, ws, ww, -, a0, a3, a4⟩ := hs
    exact Lay.of wc ws ww dcs dcw dsw a0 a3 a4
  refine WP.seq (WP.mono (si_entry hs) fun s₁ ⟨en, h29, h30, h31, hJ, hiv⟩ => ?_)
  refine WP.seq (WP.mono (j0_ok (L₀.v h29 h30 h31) hJ) fun s₂ h₂ => ?_)
  have hsv : SavedAt s₂.mem (s.gpr .a4) s := by
    have := h₂.frame
    rw [h30, h31] at this
    have hk := h₂.env.stk'
    rw [h29, h30, h31] at hk
    exact en.saved.frame this (saved_j0Frame L₀ hk)
  have e31 : s₂.gpr .s0 = s.gpr .a4 := (h₂.env.fr _ (by decide)).trans h31
  refine WP.mono (restore_ok e31 (by obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, a4⟩ := hs; exact a4)
      (by have := h₂.env.perm.w; rw [h31] at this; exact Covers.right this) hsv h₂.env.sp)
    fun s' ⟨ga, hm, _⟩ => ⟨ga, fun ciph => ?_⟩
  have hj := h₂.j0
  have hy := h₂.y
  have hcb := h₂.cb
  rw [h30, hiv] at hj hcb
  rw [h30] at hy
  rw [hm]
  exact Proof.Gcm.streamRepr_iff.mpr ⟨hj, Proof.Gcm.absorbed_nil _ hy, Proof.Gcm.ctr_zero _ _ _ _ hcb⟩

end VG.Proof.AesGcm.RISCV64
