module

public import VerifiedGarbage.Impl.Rsa.X86_64.Folded
public import VerifiedGarbage.Proof.Bignum.X86_64.PdCode
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Rsa.X86_64.Guarded
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
public import VerifiedGarbage.Proof.Rsa.Contract
public import VerifiedGarbage.Proof.Rsa.X86_64.PubChecked
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedMain
public import VerifiedGarbage.Proof.Bignum.X86_64.PubMain
public import VerifiedGarbage.Proof.Bignum.X86_64.FoldedIO
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.Octets
import Mathlib.Logic.Relator
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
meta import VerifiedGarbage.Proof.Rsa.X86_64.Guarded
meta import VerifiedGarbage.Impl.Rsa.X86_64.Folded
meta import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
meta import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.FoldedMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.FoldedExp
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Bignum.X86_64.PdCTExp
public import VerifiedGarbage.Proof.Bignum.X86_64.FoldedLoop
meta import VerifiedGarbage.Proof.Bignum.X86_64.PdCTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.FoldedLoop
import VerifiedGarbage.Proof.Bignum.X86_64.CTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTExp
import VerifiedGarbage.Proof.Bignum.X86_64.PcMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.FoldedIO
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.PcMain
meta import VerifiedGarbage.Proof.Framework.Omega

/-! ### `Bignum.X86_64.FoldedCTCode`, which this module and modules that import it used -/

section

/-! ### `Bignum.X86_64.FoldedCTMain`, which this module and modules that import it used -/

section

/-! ### `Bignum.X86_64.FoldedIOCT`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.Bignum.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open VG.Proof.MlKem.X86_64

theorem wordSetupRest_ct : RelCT isa (Two SR) (seqs (restStepsWith VG.Impl.Rsa.X86_64.Compare8.code)) fun _ _ => True := by
  unfold restStepsWith
  -- The comparison's registers.
  refine RelCT.seq (two_piece (Ψ := S5) [.rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1, h₂.2.1]) (by taint_decide) ?_) ?_
  · intro p s h
    have h' := h
    obtain ⟨hs, hdi, hZ, -, -, hW, hb, -⟩ := h'
    obtain ⟨g0, g8⟩ := slot0_ge p.w
    refine WP.mono (WP.keep [.r12, .rbx, .r10, .rbp] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 p.w ∧
        t.gpr .rbx = off p.B (slot p.w aX) ∧ t.gpr .r10 = off p.B (slot p.w aN) ∧ t.gpr .rbp = mask false ∧
        t.mem = s.mem) (by
      xrun [State.ea, hdr, hdi, hdrOff, hs.ld (d := 8 * sW) (by unfold sW; omega_arith),
        hs.ld (d := 8 * sArr aX) (by unfold sArr aX; omega_arith), hs.ld (d := 8 * sArr aN) (by unfold sArr aN; omega_arith),
        hW, hb aX (by decide), hb aN (by decide)]) rfl) fun t ⟨⟨h12, hbx, h10, hbp, hm⟩, k⟩ =>
      ⟨h.mem hm k (by decide), h12, hbx, h10, hbp⟩
  -- The comparison.
  refine RelCT.seq (two_piece (Ψ := S6) [.rbx, .r10, .r12] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2.1, h₂.2.2.2.1]
    · rw [h₁.2.1, h₂.2.1]) (by taint_decide) ?_) ?_
  · intro p s ⟨h, h12, hbx, h10, hbp⟩
    have h' := h
    obtain ⟨hs, -, hZ, hk, hk', -⟩ := h'
    refine WP.mono (Compare8.code_ok hs hbx h10 h12 hbp (by omega_arith) hk'
      (by have := slot_le (w := p.w) (show aX < 8 by decide); omega_arith)
      (by have := slot_le (w := p.w) (show aN < 8 by decide); omega_arith)) fun t ⟨_, hm, k⟩ =>
      ⟨h.mem hm k (by decide), (k.gpr (by decide)).trans h10, (k.gpr (by decide)).trans h12⟩
  -- `-m⁻¹`, and the number 1.
  refine RelCT.seq (two_piece (Ψ := S7) [.rdi, .r10] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.1.2.1, h₂.1.2.1]
    · rw [h₁.2.1, h₂.2.1]) (by taint_decide) ?_) ?_
  · intro p s ⟨h, h10, h12⟩
    obtain ⟨hs, hdi, hZ, hk, -, hW, hb, hodd₀⟩ := h
    exact WP.mono (blk7_ok hs hdi hZ (by omega_arith) hW hb h10 hodd₀) fun t ⟨mi, hH, hs', hdi', hcx, k⟩ =>
      ⟨mi, hH, hs', hdi', hZ, (k.gpr (by decide)).trans h12, hcx⟩
  -- The number 1.
  rw [setWord_eq]
  refine RelCT.seq (two_piece (Ψ := fun p s => S7 p s ∧ s.gpr .r8 = off p.B (slot p.w aOne)) [.rdi]
    (fun p s₁ s₂ ⟨_, _, _, h₁, _⟩ ⟨_, _, _, h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁, h₂]) (by taint_decide) ?_)
    (two_taint [.r8, .r12, .rcx] (fun p s₁ s₂ h₁ h₂ r hr => by
      obtain ⟨⟨_, _, _, _, _, a₁, b₁⟩, c₁⟩ := h₁
      obtain ⟨⟨_, _, _, _, _, a₂, b₂⟩, c₂⟩ := h₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [c₁, c₂]
      · rw [a₁, a₂]
      · rw [b₁, b₂]) (by taint_decide))
  rintro p s ⟨mi, hH, hs, hdi, hZ, h12, hcx⟩
  have hl : InRegions (s.rd ++ s.wr) (off p.B (8 * sArr aOne)) 8 :=
    hs.ld (by have := hdr_lt_slot p.w 8 (show sArr aOne < 32 by decide); omega_arith)
  refine WP.mono (WP.keep [.r8] (Q := fun t => t.gpr .r8 = off p.B (slot p.w aOne) ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hdi, hdrOff, hl, hH.harr aOne (by decide)]) rfl)
    fun t ⟨⟨h8, hm⟩, k⟩ => ⟨⟨mi, hm ▸ hH, hs.congr k.2.2, (k.gpr (by decide)).trans hdi, hZ,
      (k.gpr (by decide)).trans h12, (k.gpr (by decide)).trans hcx⟩, h8⟩

theorem wordIn_ct : RelCT isa (Two DRel) (seqs wordIn) (Two fun (p : DPub) s => SR ⟨p.B, p.Z, ((p.k + 7) / 8)⟩ s) := by
  unfold wordIn
  refine RelCT.seq (two_piece (Ψ := DIn) [.rdi] (fun p s₁ s₂ ⟨_, h₁⟩ ⟨_, h₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.rdi, h₂.rdi]) (by taint_decide) ?_) ?_
  · rintro p s ⟨xb, h⟩
    have hn := h.scr.nowrap
    have hZ : slot ((p.k + 7) / 8) 8 ≤ p.Z := h.z
    obtain ⟨g0, g8⟩ := slot0_ge ((p.k + 7) / 8)
    refine WP.mono (WP.keep [.rsi, .rcx, .rbx] (Q := fun t => t.gpr .rsi = p.ip ∧
        t.gpr .rcx = BitVec.ofNat 64 p.k ∧ t.gpr .rbx = off p.B (slot ((p.k + 7) / 8) aX) ∧ t.mem = s.mem) (by
      xrun [State.ea, hdr, h.rdi, hdrOff, h.scr.ld (d := 8 * sIn) (by unfold sIn sFn; omega_arith),
        h.scr.ld (d := 8 * sK) (by unfold sK sFn; omega_arith), h.scr.ld (d := 8 * sArr aX) (by unfold sArr aX; omega_arith),
        h.hIn, h.hK, h.hb aX (by decide)]) rfl)
      fun t ⟨⟨hsi, hcx, hbx, hm⟩, k⟩ => ⟨⟨xb, h.mem hm k (by decide)⟩, hsi, hcx, hbx⟩
  rw [seqs_one]
  refine two_piece [.rsi, .rcx, .rbx] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2, h₂.2.2.2]) (by taint_decide) ?_
  rintro p s ⟨⟨xb, h⟩, hsi, hcx, hbx⟩
  have hk1 := h.k1
  have hk2 := h.k2
  have hn := h.scr.nowrap
  have hZ : slot ((p.k + 7) / 8) 8 ≤ p.Z := h.z
  have hn' : p.B.toNat + slot ((p.k + 7) / 8) 8 ≤ 2 ^ 64 := by omega_arith
  have hw : 2 ≤ ((p.k + 7) / 8) := by show 2 ≤ (p.k + 7) / 8; omega_arith
  refine WP.mono (wordLoadArr_ok h.scr h.inSpan (by decide) h.z h.x h.xl (by omega_arith) (by omega_arith) hsi hcx hbx)
    fun t ⟨_, ha, k⟩ => ⟨h.scr.congr k.2.2, (k.gpr (by decide)).trans h.rdi, h.z,
      hw, show ((p.k + 7) / 8) < 2 ^ 31 by show (p.k + 7) / 8 < 2 ^ 31; omega_arith,
      by rw [ha.hslot (by decide)]; exact h.hW, fun j hj => by rw [ha.hslot (by unfold sArr; omega_arith)]; exact h.hb j hj, ?_⟩
  rw [ha.word0_of_not_mem (by decide) (by decide) hn' (by omega_arith),
    ← wv_mod64 _ _ _ (show 1 ≤ ((p.k + 7) / 8) by omega_arith), Nat.mod_mod_of_dvd _ (by decide), h.n, h.odd]

theorem wordSetup_ct : RelCT isa (Two DRel) (seqs (wordIn ++ restStepsWith VG.Impl.Rsa.X86_64.Compare8.code)) (Two DA) := by
  refine two_post (Ψ := fun p t => ∃ mi, DA (p, mi) t)
    (RelCT.seqs_append (by simp [wordIn]) (by simp [restStepsWith]) (RelCT.seq wordIn_ct (two_map (fun p : DPub => (⟨p.B, p.Z, ((p.k + 7) / 8)⟩ : RPub)) (fun _ _ h => h) wordSetupRest_ct))) ?_ |>.mono
      (fun _ _ h => h) fun _ _ h => two_bind (fun p t₁ t₂ H₁ H₂ => ?_) h
  · rintro p s ⟨xb, h⟩
    exact WP.mono (wordSetup_ok h) fun t ⟨mi, so, f, k, hR⟩ => ⟨mi, xb, s, ⟨h, f, k, so.mask⟩, so, hR⟩
  · obtain ⟨mi₁, h₁⟩ := H₁
    obtain ⟨mi₂, h₂⟩ := H₂
    have ⟨xb₁, σ₁, g₁, so₁, _⟩ := h₁
    have ⟨xb₂, σ₂, g₂, so₂, _⟩ := h₂
    have : 64 ≤ p.k := g₁.1.k1
    obtain rfl := so_minv so₁ so₂ g₁.1.odd (show 1 ≤ ((p.k + 7) / 8) by show 1 ≤ (p.k + 7) / 8; omega_arith)
    exact ⟨(p, mi₁), h₁, h₂⟩

theorem wordPdLoad_ct : RelCT isa (Two LH) (seqs (Precomputed.loadWith VG.Impl.Rsa.X86_64.Compare8.code)) fun _ _ => True := by
  unfold Precomputed.loadWith
  -- `w`, the bases, and the first copy's registers.
  refine RelCT.seq (two_piece (Ψ := fun p t => LW p t ∧ t.gpr .rsi = off p.pp (8 * 0) ∧
      t.gpr .rbx = off p.d.B (slot ((p.d.k + 7) / 8) aN) ∧ t.gpr .r12 = BitVec.ofNat 64 ((p.d.k + 7) / 8)) _
    pins_LH (by taint_decide) ?_) ?_
  · intro p t h
    have h' := h
    obtain ⟨hs, hdi, hZ, hk1, hk2, hK, hN, -⟩ := h'
    obtain ⟨g0, g8⟩ := slot0_ge ((p.d.k + 7) / 8)
    refine WP.mono (setupHead_ok hs hdi hZ (by omega_arith) hK hN) fun t' ⟨h12, _, hsi, hbx, hW, hb, hf, k⟩ =>
      ⟨⟨h.congr hf (fun r hr => ?_) k (by decide), hW, hb⟩, by rw [hsi]; simp [off], hbx, h12⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [sW, sArr] <;> omega_arith
  -- `m`.
  refine RelCT.seq (two_piece (Ψ := fun p t => LW p t ∧ t.gpr .rsi = off p.pp (8 * 0) ∧
      t.gpr .r12 = BitVec.ofNat 64 ((p.d.k + 7) / 8)) [.rsi, .rbx, .r12] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2, h₂.2.2.2]) (by taint_decide) ?_) ?_
  · rintro p t ⟨h, hsi, hbx, h12⟩
    exact WP.mono (ldCopy_ok h (Nat.zero_le _) (by decide) hsi hbx h12) fun t' ⟨h', k⟩ =>
      ⟨h', (k.gpr (by decide)).trans hsi, (k.gpr (by decide)).trans h12⟩
  -- `R² mod m`'s registers.
  refine RelCT.seq (two_piece (Ψ := fun p t => LW p t ∧ t.gpr .rsi = off p.pp (8 * ((p.d.k + 7) / 8)) ∧
      t.gpr .rbx = off p.d.B (slot ((p.d.k + 7) / 8) aR2) ∧ t.gpr .r12 = BitVec.ofNat 64 ((p.d.k + 7) / 8))
    [.rdi, .rsi, .r12] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.1.1.2.1, h₂.1.1.2.1]
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2, h₂.2.2]) (by taint_decide) ?_) ?_
  · rintro p t ⟨h, hsi, h12⟩
    have hs := h.1.1
    have hn := hs.nowrap
    have hZ := h.1.2.2.1
    obtain ⟨g0, g8⟩ := slot0_ge ((p.d.k + 7) / 8)
    have hax8 : ∀ r : BitVec 64, r = BitVec.ofNat 64 ((p.d.k + 7) / 8) → r + r + (r + r) + (r + r + (r + r)) =
        BitVec.ofNat 64 (8 * ((p.d.k + 7) / 8)) := by
      rintro r rfl; simp only [BitVec.ofNat_add_ofNat]; congr 1; omega_arith
    have hsi' : t.gpr .rsi = p.pp := by rw [hsi]; simp [off]
    refine WP.mono (WP.keep [.rax, .rsi, .rbx] (Q := fun t' => t'.gpr .rsi = off p.pp (8 * ((p.d.k + 7) / 8)) ∧
        t'.gpr .rbx = off p.d.B (slot ((p.d.k + 7) / 8) aR2) ∧ t'.mem = t.mem) (by
      unfold eightW
      simp only [List.cons_append, List.nil_append]
      xrun [State.ea, hdr, h.1.2.1, hdrOff, hs.ld (d := 8 * sArr aR2) (by unfold sArr aR2; omega_arith),
        h.2.2 aR2 (by decide), h12, hsi', hax8 _ rfl]) rfl)
      fun t' ⟨⟨hsi₁, hbx₁, hm⟩, k⟩ => ⟨⟨h.1.congr (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k
        (by decide), by rw [hm]; exact h.2.1, fun j hj => by rw [hm]; exact h.2.2 j hj⟩, hsi₁, hbx₁,
        (k.gpr (by decide)).trans h12⟩
  -- `R² mod m`.
  refine RelCT.seq (two_piece (Ψ := fun p t => LW p t ∧ t.gpr .rbx = off p.d.B (slot ((p.d.k + 7) / 8) aR2) ∧
      t.gpr .r12 = BitVec.ofNat 64 ((p.d.k + 7) / 8)) [.rsi, .rbx, .r12] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2, h₂.2.2.2]) (by taint_decide) ?_) ?_
  · rintro p t ⟨h, hsi, hbx, h12⟩
    exact WP.mono (ldCopy_ok h (Nat.le_refl _) (by decide) hsi hbx h12) fun t' ⟨h', k⟩ =>
      ⟨h', (k.gpr (by decide)).trans hbx, (k.gpr (by decide)).trans h12⟩
  -- The comparison's registers.
  refine RelCT.seq (two_piece (Ψ := fun p t => LH p t ∧ t.gpr .rbx = off p.d.B (slot ((p.d.k + 7) / 8) aR2) ∧
      t.gpr .r10 = off p.d.B (slot ((p.d.k + 7) / 8) aN) ∧ t.gpr .r12 = BitVec.ofNat 64 ((p.d.k + 7) / 8) ∧
      t.gpr .rbp = mask false) [.rdi] (fun p s₁ s₂ h₁ h₂ => pins_LH p s₁ s₂ h₁.1.1 h₂.1.1) (by taint_decide) ?_) ?_
  · rintro p t ⟨h, hbx, h12⟩
    have hs := h.1.1
    have hn := hs.nowrap
    have hZ := h.1.2.2.1
    obtain ⟨g0, g8⟩ := slot0_ge ((p.d.k + 7) / 8)
    refine WP.mono (WP.keep [.r10, .rbp] (Q := fun t' => t'.gpr .r10 = off p.d.B (slot ((p.d.k + 7) / 8) aN) ∧
        t'.gpr .rbp = mask false ∧ t'.mem = t.mem) (by
      xrun [State.ea, hdr, h.1.2.1, hdrOff, hs.ld (d := 8 * sArr aN) (by unfold sArr aN; omega_arith),
        h.2.2 aN (by decide)]) rfl)
      fun t' ⟨⟨h10, hbp, hm⟩, k⟩ => ⟨h.1.congr (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k
        (by decide), (k.gpr (by decide)).trans hbx, h10, (k.gpr (by decide)).trans h12, hbp⟩
  -- The comparison.
  refine RelCT.seq (two_piece (Ψ := fun (p : CPubD) t => t.gpr .r10 = off p.d.B (slot ((p.d.k + 7) / 8) aN) ∧
      t.gpr .r12 = BitVec.ofNat 64 ((p.d.k + 7) / 8)) [.rbx, .r10, .r12] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2.1, h₂.2.2.2.1]) (by taint_decide) ?_) ?_
  · rintro p t ⟨h, hbx, h10, h12, hbp⟩
    have hZ := h.2.2.1
    have hk1 := h.2.2.2.1
    have hk2 := h.2.2.2.2.1
    exact WP.mono (Compare8.code_ok h.1 hbx h10 h12 hbp (by omega_arith) (by omega_arith)
      (by have := slot_le (w := (p.d.k + 7) / 8) (show aR2 < 8 by decide); omega_arith)
      (by have := slot_le (w := (p.d.k + 7) / 8) (show aN < 8 by decide); omega_arith)) fun t' ⟨_, _, k⟩ =>
      ⟨(k.gpr (by decide)).trans h10, (k.gpr (by decide)).trans h12⟩
  -- The checks.
  exact two_taint [.r10, .r12] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.1, h₂.1]
    · rw [h₁.2, h₂.2]) (by taint_decide)

def WordOPre (p : OPub) (s : State) : Prop :=
  ∃ c : Bool, Good s p.L.B p.L.Z p.L.w p.L.minv ∧ p.L.w = (p.k + 7) / 8 ∧ slot p.L.w 8 ≤ p.L.Z ∧ 1 ≤ p.k ∧
    p.k < 2 ^ 31 ∧ word s.mem p.L.B (8 * sOut) = p.op ∧ word s.mem p.L.B (8 * sK) = BitVec.ofNat 64 p.k ∧
    word s.mem p.L.B (8 * sMask) = mask c ∧ InRegions s.wr p.op p.k ∧
    (∀ j < p.k, p.L.Z ≤ ofs p.L.B (p.op + BitVec.ofNat 64 j))

/-- Before `storeBE`. -/
def WordO1 (p : OPub) (s : State) : Prop :=
  ∃ c : Bool, Scr s p.L.B p.L.Z ∧ s.gpr .rdi = p.L.B ∧ p.L.w = (p.k + 7) / 8 ∧ slot p.L.w 8 ≤ p.L.Z ∧
    1 ≤ p.k ∧ p.k < 2 ^ 31 ∧ s.gpr .rbx = off p.L.B (slot p.L.w aY) ∧ s.gpr .rsi = p.op ∧
    s.gpr .rcx = BitVec.ofNat 64 p.k ∧ s.gpr .r15 = mask c ∧
    InRegions s.wr p.op p.k ∧
    (∀ j < p.k, p.L.Z ≤ ofs p.L.B (p.op + BitVec.ofNat 64 j))

/-- The result's store leaks the same in runs with the same working space,
length and `out`. -/
theorem wordOut_ct : RelCT isa (Two WordOPre) (seqs (wordOutStepsArr aY)) fun _ _ => True := by
  unfold wordOutStepsArr
  refine RelCT.seq (two_piece (Ψ := WordO1) [.rdi] (fun p s₁ s₂ ⟨_, h₁, _⟩ ⟨_, h₂, _⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.rdi, h₂.rdi]) (by taint_decide) ?_) ?_
  · rintro p s ⟨c, hg, hw, hZ, hk1, hk, hO, hK, hM, hout, hsep⟩
    have hn := hg.scr.nowrap
    obtain ⟨g0, g8⟩ := slot0_ge p.L.w
    have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.L.B (8 * i)) 8 := fun i hi => hg.scr.ld (by omega_arith)
    refine WP.mono (WP.keep [.rbx, .rsi, .rcx, .r15] (Q := fun t =>
        t.gpr .rbx = off p.L.B (slot p.L.w aY) ∧ t.gpr .rsi = p.op ∧ t.gpr .rcx = BitVec.ofNat 64 p.k ∧
        t.gpr .r15 = mask c ∧ t.mem = s.mem) (by
      xrun [State.ea, hdr, hg.rdi, hdrOff, hl (sArr aY) (by decide), hl sOut (by decide), hl sK (by decide),
        hl sMask (by decide), hg.hdr.harr aY (by decide), hO, hK, hM]) rfl)
      fun t ⟨⟨hbx, hsi, hcx, h15, hm⟩, k⟩ => ⟨c, hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi, hw, hZ,
        hk1, hk, hbx, hsi, hcx, h15, by rw [k.2.2]; exact hout, hsep⟩
  refine RelCT.seq (two_piece (Ψ := fun p s => s.gpr .rdi = p.L.B) [.rbx, .rsi, .rcx]
    (fun p s₁ s₂ ⟨_, _, _, _, _, _, _, a₁, b₁, c₁, _⟩ ⟨_, _, _, _, _, _, _, a₂, b₂, c₂, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [a₁, a₂]
      · rw [b₁, b₂]
      · rw [c₁, c₂]) (by taint_decide) ?_) ?_
  · rintro p s ⟨c, hs, hdi, hw, hZ, hk1, hk, hbx, hsi, hcx, h15, hout, hsep⟩
    exact WP.mono (WordIO.store_ok hs hbx hsi hcx h15 hk1 hk hw
      (by have := slot_le (w := p.L.w) (show aY < 8 by decide); omega_arith) hout hsep)
      fun t ⟨_, _, _, _, k⟩ => (k.gpr (by decide)).trans hdi
  exact two_taint [.rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁, h₂]) (by taint_decide)

theorem dd_wordOPre {q : DPub × BitVec 64} {t : State} (h : DD q t) : WordOPre ⟨DPub.L q, q.1.k, q.1.op⟩ t := by
  obtain ⟨xb, σ, g, hg⟩ := h
  have hk1 := g.1.k1
  have hk2 := g.1.k2
  exact ⟨_, hg, rfl, g.1.z, show 1 ≤ q.1.k by omega_arith, show q.1.k < 2 ^ 31 by omega_arith, by rw [g.fixed sOut (by decide)]; exact g.1.hO,
    by rw [g.fixed sK (by decide)]; exact g.1.hK, g.2.2.2, by rw [g.2.2.1.2.2]; exact g.1.outSpan,
    g.1.outSep⟩

theorem ce2_wordLoad {p : CPubD} {t : State} (h : CE2 p t) : WP isa (seqs (Precomputed.loadWith VG.Impl.Rsa.X86_64.Compare8.code)) t (CL p) := by
  obtain ⟨⟨B, Z, k, op, ep, ip, len, eb, N, R⟩, pp, rsp⟩ := p
  obtain ⟨s, hs, he⟩ := h
  have hs' := hs
  have he' := he
  obtain ⟨hdi, -, -, -, -, -, -, -, hN, hK, -, -, -, ho₁, k₁⟩ := he'
  obtain ⟨hpre, -, hB, hZ, hk, -, hpp, -, -, -, -, hNv, hRv, -⟩ := hs
  have c := pdCtx_of hpre
  have := c.hZ
  have := c.hk1
  have := c.hk2
  have hn := c.hs.nowrap
  have i₁ : InScr (stackArg s 2) ((stackArg s 3).toNat * 8) s.mem t.mem := InScr.of_outside ho₁ (by omega_arith)
  have hz : slot (((s.gpr .rsi).toNat + 7) / 8) 8 ≤ (stackArg s 3).toNat * 8 := by unfold slot hdrBytes; omega_arith
  refine WP.mono (pdLoadWith_ok VG.Impl.Rsa.X86_64.Compare8.code @Compare8.code_ok (c.hs.congr k₁.2.2) hdi hz (by omega_arith) (by omega_arith) (by rw [hK, ofNat_toNat64])
    hN (fun i hi => by rw [k₁.2.1, k₁.2.2]; exact c.hpr i hi) c.hps) fun t' ⟨hN₂, hR₂, hW₂, hb₂, hz₂, f₂, k₂⟩ => ?_
  rw [pre_wv_entry c i₁ (by omega_arith), hNv] at hN₂
  rw [pre_wv_entry c i₁ (by omega_arith), hRv] at hR₂
  rw [chk_eq (by omega_arith), hN₂, hR₂] at hz₂
  subst hB hZ hk hpp
  exact ⟨s, t, hs', he, hN₂, hR₂, hW₂, hb₂, hz₂, f₂, k₂⟩


end VG.Proof.Bignum.X86_64

end

end

/-! ### `Bignum.X86_64.FoldedCT`, which this module and modules that import it used -/

section

/-! ### `Bignum.X86_64.FoldedCTLoop`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.Bignum.X86_64.FoldedPublic
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum.X86_64

structure PublicData where
  L : Lay
  N : Nat

def Facts (p : PublicData) : Prop :=
  slot p.L.w 8 ≤ p.L.Z ∧ 2 ≤ p.L.w ∧ p.L.w < 2^31 ∧
  Nat.Coprime (2^(64*p.L.w)) p.N

def Inv (p : PublicData) (i : Nat) (s : State) : Prop :=
  ∃ s₀ X x, SquareInv s₀ p.L.B p.L.Z p.L.w p.N X x p.L.minv i s ∧ Facts p

theorem step_ct (M : Mont) :
    RelCT isa (Two fun (q : PublicData × Nat) s => q.2 < 16 ∧ Inv q.1 q.2 s)
      (Folded.squareStep M.mm) (fun _ _ => True) := by
  unfold Folded.squareStep
  refine RelCT.seq (two_post (Ψ := fun (q : PublicData × Nat) t => t.gpr .rdi = q.1.L.B)
    (two_map (fun (q : PublicData × Nat) => q.1.L)
      (fun _ _ ⟨_,_,_,_,h,hf⟩ => ⟨h.ctx.good,hf.1⟩)
      (M.ctL (o := aY) (a := aY) (b := aY) (by unfold MmUse; decide))) ?_)
    (two_taint [.rdi] (fun q s t hs ht r hr => by
      simp only [List.mem_singleton] at hr; subst r; exact hs.trans ht.symm) (by taint_decide))
  rintro q s ⟨_,s₀,X,x,h,hf⟩
  exact WP.mono (M.mm_ok h.ctx.good hf.1 hf.2.1 hf.2.2.1 (o := aY) (a := aY) (b := aY)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    h.ctx.inv (by rw [h.ctx.n]; exact h.reduced)) fun t ⟨hg,_⟩ => hg.rdi

theorem squares_ct (M : Mont) :
    RelCT isa (Two fun p s => 0 < 16 ∧ Inv p 0 s)
      (.loop (Folded.squareStep M.mm) .ne) (Two fun p s => Inv p 16 s) := by
  refine two_loop (Φ := Inv) (fun _ => 16) (step_ct M) ?_
  rintro p i s hi ⟨s₀,X,x,h,hf⟩
  exact WP.mono (loopStep_ok M hf.1 hf.2.1 hf.2.2.1 hf.2.2.2 hi h)
    fun t ⟨hz,ht⟩ => ⟨eval_ne_count hi hz, fun _ => ⟨s₀,X,x,ht,hf⟩,
      fun he => he ▸ ⟨s₀,X,x,ht,hf⟩⟩

end VG.Proof.Bignum.X86_64.FoldedPublic

end

end

@[expose] public section

namespace VG.Proof.Bignum.X86_64.FoldedPublic
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

def Pre (p : PublicData) (s : State) : Prop :=
  ∃ X x, ExpCtx s p.L.B p.L.Z p.L.w p.L.minv p.N X ∧ Facts p ∧ X < p.N ∧
    X % p.N = x * 2^(64*p.L.w) % p.N

def Ready (p : PublicData) (s : State) : Prop :=
  ∃ X x, ExpCtx s p.L.B p.L.Z p.L.w p.L.minv p.N X ∧ Facts p ∧
    wv s.mem p.L.B (slot p.L.w aY) p.L.w < p.N ∧
    wv s.mem p.L.B (slot p.L.w aY) p.L.w % p.N = x * 2^(64*p.L.w) % p.N

theorem start_fw (p : PublicData) (s : State) (h : Pre p s) :
    WP isa Precomputed.start s (Ready p) := by
  obtain ⟨X,x,hc,hf,hlt,hx⟩ := h
  exact WP.mono (start_ok hc hf.1 (by have := hf.2.1; omega_using [this]) hf.2.2.1)
    fun t ⟨ct,yt,_,_,_⟩ => ⟨X,x,ct,hf,by rw [yt]; exact hlt,by rw [yt]; exact hx⟩

theorem init_fw (p : PublicData) (s : State) (h : Ready p s) :
    WP isa (.block [.mov32 .rax (.imm 16), .store (hdr sI) .rax]) s (Inv p 0) := by
  obtain ⟨X,x,hc,hf,hlt,hx⟩ := h
  have hb : p.L.B.toNat + slot p.L.w 8 ≤ 2^64 := by
    have := hc.good.scr.nowrap; have := hf.1; omega_arith
  refine WP.mono (init_ok hc.good hf.1) fun t ⟨mt,kt⟩ => ?_
  have ct := ExpCtx.store hc hf.1 (i := sI) (by decide) (by decide) mt kt.2.2
    ((kt.gpr (by decide)).trans hc.good.rdi)
  have yt : wv t.mem p.L.B (slot p.L.w aY) p.L.w = wv s.mem p.L.B (slot p.L.w aY) p.L.w := by
    rw [mt,hdrStore_wv (i := sI) (j := aY) _ _ _ (by decide) (by decide) hb]
  exact ⟨t,X,x,⟨ct,by rw [yt]; exact hlt,by simpa only [yt,Nat.pow_zero,Nat.pow_one] using hx,
    by rw [mt,word_writeW_self]; rfl,Frm.refl _ _ _,Keep.refl _ _⟩,hf⟩

/-- `Y := X` and sixteen squares leak the same in runs with the same public
data. -/
theorem exp65536_ct (M : Mont) :
    RelCT isa (Two Pre) (Folded.exp65536 M.mm) (fun _ _ => True) := by
  unfold Folded.exp65536
  simp only [seqs]
  refine RelCT.seq (two_post (two_map (fun p : PublicData => p.L)
    (fun _ _ ⟨_,_,hc,hf,_⟩ => ⟨hc.good,hf.1⟩) VG.Proof.Bignum.X86_64.start_ct) start_fw) ?_
  refine RelCT.seq (two_piece [.rdi]
    (fun p s t ⟨_,_,hs,_⟩ ⟨_,_,ht,_⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst r; rw [hs.good.rdi,ht.good.rdi])
    (by taint_decide) init_fw) ?_
  exact (two_map id (fun _ _ h => ⟨by decide,h⟩) (squares_ct M)).mono (fun _ _ h => h) fun _ _ _ => trivial

end VG.Proof.Bignum.X86_64.FoldedPublic

end

end

@[expose] public section

namespace VG.Proof.Bignum.X86_64.FoldedPublic
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

def publicData (q : DPub × BitVec 64) : PublicData := ⟨DPub.L q,q.1.N⟩

theorem db_pre {q : DPub × BitVec 64} {s : State} (h : DB q s) : Pre (publicData q) s := by
  obtain ⟨X,x,hc,hf,_⟩ := VG.Proof.Bignum.X86_64.db_pre h
  exact ⟨X,x,hc,⟨hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1⟩,hf.2.2.2.2⟩

/-- `DB` after `is65537`, which writes registers only. -/
theorem db_is65537 {q : DPub × BitVec 64} {s t : State} (h : DB q s) (hm : t.mem = s.mem)
    (k : Keep [.rax, .r8, .r9, .r10, .r11] s t) : DB q t := by
  obtain ⟨xb,σ,g,hg,hn,hinv,hlt,hone⟩ := h
  exact ⟨xb,σ,g.step (by rw [hm]; exact Frm.refl _ _ _) (k.mono (by decide)) (by rw [hm]),
    ⟨hg.scr.congr k.2.2,(k.gpr (by decide)).trans hg.rdi,by rw [hm]; exact hg.hdr⟩,
    by rw [hm]; exact hn,by rw [hm]; exact hinv,by rw [hm]; exact hlt,by rw [hm]; exact hone⟩

/-- The exponentiation leaks the same in runs that agree on `e`: whether
`e` is 65537 is public. -/
theorem exp_ct (M : Mont) : RelCT isa (Two DB) (Folded.exp M.mm) (Two DC) := by
  unfold Folded.exp Folded.is65537
  refine RelCT.seq (RelCT.seq (two_piece (Ψ := fun q t => DB q t ∧ t.gpr .r8 = q.1.ep ∧
      t.gpr .r9 = BitVec.ofNat 64 q.1.len)
    [.rdi] (fun _ _ _ ⟨_,_,_,h₁,_⟩ ⟨_,_,_,h₂,_⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.rdi,h₂.rdi]) (by taint_decide) ?_)
    (two_piece (Ψ := fun q t => DB q t ∧ t.zf = some (decide (Spec.Rsa.os2ip q.1.eb = 65537)))
    [.r8, .r9] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.2.1,h₂.2.1]
      · rw [h₁.2.2,h₂.2.2]) (by taint_decide) ?_)) ?_
  · rintro q s h
    obtain ⟨X,x,hc,hf,he,hlen,_⟩ := VG.Proof.Bignum.X86_64.db_pre h
    exact WP.mono (is65537Load_ok hc.good hf.1 he hlen) fun a ⟨h8,h9,ma,ka⟩ =>
      ⟨db_is65537 h ma (ka.mono (by decide)),h8,h9⟩
  · rintro q s ⟨h,h8,h9⟩
    obtain ⟨_,_,_,_,_,_,hL1,_⟩ := VG.Proof.Bignum.X86_64.db_pre h
    have h' := h
    obtain ⟨xb,σ,g,_⟩ := h'
    have hs := g.1.e.congrK g.inScr g.2.2.1
    exact WP.mono (is65537Check_ok h8 h9 hs g.1.el hL1
      (by have := g.1.L2; have := g.1.k2; show q.1.len < 2^31; omega_arith)) fun a ⟨za,ma,ka⟩ =>
        ⟨db_is65537 h ma (ka.mono (by decide)),za⟩
  refine two_ite (fun _ _ _ h₁ h₂ => by simp only [eval,h₁.2,h₂.2]) ?_ ?_
  · refine two_post ((two_map publicData (fun _ _ h => db_pre h.1.1) (exp65536_ct M)).mono
      (fun _ _ h => h) fun _ _ _ => trivial) ?_
    rintro q s ⟨⟨h,hz⟩,hb⟩
    have h65 : Spec.Rsa.os2ip q.1.eb = 65537 := by simpa [eval,hz] using hb
    obtain ⟨X,x,hc,hf,_⟩ := VG.Proof.Bignum.X86_64.db_pre h
    obtain ⟨xb,σ,g,_⟩ := h
    have hE := os2ip_evenLast g.1.eodd
    refine WP.mono (exp65536_ok M hc hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2.1 hf.2.2.2.2.2)
      fun t ⟨ct,lt,vt,ft,kt⟩ => ⟨xb,σ,X,x,g.step (ft.mono (pExpRanges_pdAll _)) kt
        (ft.word_eq (pExpRanges_hdr _ (by decide) (by decide) (by decide) (by decide) (by decide))
          (by unfold sMask sFn; omega_using [])),ct,lt,?_⟩
    rw [← show Spec.Rsa.os2ip (evenLast q.1.eb) = 65536 by omega_using [h65, hE]] at vt; exact vt
  · exact two_map id (fun _ _ h => h.1.1) pdExp_ct

/-- The computation leaks the same in runs with the same public data, given
that the last multiplication does (`hfinal`). -/
theorem rest_ct (M : Mont)
    (hfinal : RelCT isa (Two GoodL) (M.mm aY aX aY) (fun _ _ => True)) :
    RelCT isa (Two DRel) (Folded.rest M.mm) (fun _ _ => True) := by
  rw [rest_eq]
  refine RelCT.seqs_append (by simp [wordIn]) (by simp [phases]) (RelCT.seq wordSetup_ct ?_)
  refine RelCT.seqs_append (by simp [phases]) (by simp [wordOutStepsArr])
    (RelCT.seq (R := Two DD) ?_ ?_)
  · exact RelCT.seq pdMm_ct (RelCT.seq (exp_ct M) (pdFinal_ct hfinal))
  · exact two_map (fun q => (⟨DPub.L q,q.1.k,q.1.op⟩ : OPub))
      (fun _ _ h => dd_wordOPre h) wordOut_ct

end VG.Proof.Bignum.X86_64.FoldedPublic

end

end

@[expose] public section

namespace VG.Proof.Bignum.X86_64.FoldedPublic
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- The code after the check of `e`, with any constant-time `rest`. -/
theorem codeWith_ct (rest : Prog isa) (hrest : RelCT isa (Two DRel) rest fun _ _ => True) :
    RelCT isa (Two CR) (.seq (.block Precomputed.entry) (.seq (seqs (Precomputed.loadWith Compare8.code))
      (.ite .e fail rest))) fun _ _ => True := by
  refine RelCT.seq (R := Two CE2) ?_ ?_
  · rw [pdEntry_split]
    refine RelCT.block_append (RelCT.seq (two_piece (Ψ := CE1) [.rsp] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1, h₂.2.1]) (by taint_decide) ?_)
      (two_piece [.r11, .rsp] (fun p s₁ s₂ ⟨_, _, a₁, b₁, _⟩ ⟨_, _, a₂, b₂, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [a₁, a₂]
        · rw [b₁, b₂]) (by taint_decide) fun p t ⟨s, hs, _, _, hw⟩ => WP.mono hw fun t' h => ⟨s, hs, h⟩))
    intro p s hs
    have c := pdCtx_of hs.1
    have hZ := c.hZ
    have hk1 := c.hk1
    have hw : ∀ i < 22, InRegions s.wr (off (stackArg s 2) (8 * i)) 8 := fun i hi => c.hs.st (by omega_using [hZ, hi])
    have hh : WP isa (.block (([.mov .r11 (.mem { base := .rsp, disp := 24 })] : List Instr) ++
        Precomputed.entry.drop 1)) s (PdEnt s) := by
      rw [← pdEntry_split]; exact pdEntry_ok rfl hw c.ha0 c.ha2 c.hsep
    have e2 : s.gpr .rsp + BitVec.ofInt 64 24 = stackArgAddr s 2 := rfl
    have hB' : s.mem.readW (stackArgAddr s 2) 64 = stackArg s 2 := rfl
    refine WP.mono (WP.and (WP.block_append_iff.mp hh) (WP.keep [.r11] (Q := fun t => t.gpr .r11 = stackArg s 2)
      (by xrun [State.ea, e2, c.ha2, hB']) rfl)) fun t ⟨hw', h11, k⟩ =>
        ⟨s, hs, h11.trans hs.2.2.1, (k.gpr (by decide)).trans hs.2.1, hw'⟩
  refine RelCT.seq (R := Two CL) (two_post (wordPdLoad_ct.mono (fun _ _ h => two_mono (fun _ _ h => ce2_lh h) h)
    fun _ _ h => h) fun p t h => ce2_wordLoad h) ?_
  refine two_ite (fun p s₁ s₂ ⟨_, _, _, _, _, _, _, _, z₁, _⟩ ⟨_, _, _, _, _, _, _, _, z₂, _⟩ => by
    simp only [eval, z₁, z₂]) ?_ ?_
  · -- `fail`.
    unfold fail
    refine RelCT.seq (two_piece (Ψ := fun (p : CPubD) t => t.gpr .rsi = p.d.op ∧
        t.gpr .rcx = BitVec.ofNat 64 p.d.k ∧ t.gpr .rdi = p.d.B) [.rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [(cl_fail h₁.1).2.1, (cl_fail h₂.1).2.1])
      (by taint_decide) ?_)
      (two_taint [.rsi, .rcx, .rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2.1, h₂.2.1]
        · rw [h₁.2.2, h₂.2.2]) (by taint_decide))
    rintro p t ⟨h, -⟩
    obtain ⟨hs, hdi, hZ, hk1, hk2, hO, hK⟩ := cl_fail h
    have hn := hs.nowrap
    have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off p.d.B (8 * i)) 8 := fun i hi => hs.ld (by omega_using [hZ, hi])
    refine WP.mono (WP.keep [.rsi, .rcx, .rax] (Q := fun t' => t'.gpr .rsi = p.d.op ∧
        t'.gpr .rcx = BitVec.ofNat 64 p.d.k) (by
      xrun [State.ea, hdr, hdi, hdrOff, hl sOut (by decide), hl sK (by decide), hO, hK]) rfl)
      fun t' ⟨⟨hsi, hcx⟩, k'⟩ => ⟨hsi, hcx, (k'.gpr (by decide)).trans hdi⟩
  · -- `rest`.
    exact two_map (fun p => p.d) (fun _ _ h => cl_rest h.1 h.2) hrest

/-- The code after the check of `e` is constant time, for valid `e`s, with any
constant-time `rest`. -/
theorem codeWith_constantTime (rest : Prog isa) (hrest : RelCT isa (Two DRel) rest fun _ _ => True) :
    ConstantTime isa (fun s => pdContract.pre s ∧ Rsa.X86_64.eValid s = true) pdContract.pub
      (.seq (.block Precomputed.entry) (.seq (seqs (Precomputed.loadWith Compare8.code)) (.ite .e fail rest))) := by
  refine RelCT.constantTime ((codeWith_ct rest hrest).mono (fun s₁ s₂ ⟨⟨h₁, v₁⟩, ⟨h₂, _⟩, hp⟩ => ⟨cpubOfD s₁, ?_, ?_⟩)
    fun _ _ h => h)
  · exact ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, v₁⟩
  · obtain ⟨hr, a0, -, a2, a3, hw, he⟩ := hp
    have r : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₂.gpr r = s₁.gpr r := fun r h => (hr r h).symm
    have c := pdCtx_of h₂
    have hpl := c.hpl
    rw [r .rcx (by decide), r .rsi (by decide)] at hpl
    rw [r .rdx (by decide), r .rcx (by decide)] at hw
    refine ⟨h₂, r .rsp (by decide), a2.symm, by rw [← a3]; rfl, by rw [r .rsi (by decide)]; rfl, r .rdi (by decide),
      r .rdx (by decide), r .r8 (by decide), a0.symm, by rw [r .r9 (by decide)]; rfl, he.symm, ?_, ?_, v₁⟩
    · rw [r .rdx (by decide), r .rsi (by decide), show (0 : Nat) = 8 * 0 from rfl]
      exact (wv_of_wordsAt hw (by omega_using [hpl])).symm
    · rw [r .rdx (by decide), r .rsi (by decide)]
      exact (wv_of_wordsAt hw (by omega_using [hpl])).symm

/-- The code after the check of `e` is constant time, for valid `e`s. -/
theorem code_constantTime (M : Mont)
    (hfinal : RelCT isa (Two GoodL) (M.mm aY aX aY) (fun _ _ => True)) :
    ConstantTime isa (fun s => pdContract.pre s ∧ Rsa.X86_64.eValid s = true) pdContract.pub (Folded.code M.mm) :=
  codeWith_constantTime (Folded.rest M.mm) (rest_ct M hfinal)

end VG.Proof.Bignum.X86_64.FoldedPublic

end

end

/-! ### `Bignum.X86_64.FoldedChecked`, which this module and modules that import it used -/

section

/-! ### `Bignum.X86_64.FoldedCode`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.Bignum.X86_64.FoldedPublic
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- The code after the check of `e`, for a valid `e`, with any `rest` that
`rest_ok` describes, MXCSR's control bits included. -/
theorem codeWith_correct (rest : Prog isa)
    (hrest : ∀ {t : State} {B : Addr} {Z k : Nat} {op ep ip : Addr} {L : Nat} {eb xb : List Byte} {N R : Nat},
      PdPre t B Z k op ep ip L eb xb N R → WP isa rest t fun t' => ∃ y : Nat,
        (R % N = 2^(64*((k+7)/8)) * 2^(64*((k+7)/8)) % N → y = Spec.Rsa.os2ip xb ^ Spec.Rsa.os2ip eb % N) ∧
        MainPost t t' B Z k op (if Spec.Rsa.os2ip xb < N then y else 0) (decide (Spec.Rsa.os2ip xb < N)) ∧
        t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10)
    (s : State) (h : pdContract.pre s)
    (hev : Spec.Rsa.exponentValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)) = true) :
    ∃ t s', Exec isa (.seq (.block Precomputed.entry) (.seq (seqs (Precomputed.loadWith Compare8.code))
      (.ite .e fail rest))) s t s' ∧ abiPreserved s s' ∧ pdContract.post s s' := by
  have c := pdCtx_of h
  have hZ' := c.hZ
  have hk1 := c.hk1
  have hk2 := c.hk2
  have hn := c.hs.nowrap
  suffices hwp : WP isa (.seq (.block Precomputed.entry) (.seq (seqs (Precomputed.loadWith Compare8.code))
      (.ite .e fail rest))) s fun s' => (gprPreserved s s' ∧ pdContract.post s s') ∧
        s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 by
    obtain ⟨t, s', he, ⟨hg, hp⟩, hx⟩ := hwp
    exact ⟨t, s', he, ⟨hg.1, hg.2, hx⟩, hp⟩
  have hw : ∀ i < 22, InRegions s.wr (off (stackArg s 2) (8 * i)) 8 := fun i hi => c.hs.st (by omega_using [hZ', hi])
  refine WP.seq (WP.mono_mx (by decide +kernel) (pdEntry_ok rfl hw c.ha0 c.ha2 c.hsep) fun t₁ ⟨hdi, h0, h1, h2, h3, h4, h5, hO, hN, hK,
    hE, hL, hIn, ho₁, k₁⟩ mx₁ => ?_)
  have i₁ : InScr (stackArg s 2) ((stackArg s 3).toNat * 8) s.mem t₁.mem := InScr.of_outside ho₁ (by omega_using [hZ'])
  have hz : slot (((s.gpr .rsi).toNat + 7) / 8) 8 ≤ (stackArg s 3).toNat * 8 := by unfold slot hdrBytes; omega_using [hZ']
  refine WP.seq (WP.mono_mx (by decide +kernel) (pdLoadWith_ok VG.Impl.Rsa.X86_64.Compare8.code @Compare8.code_ok (c.hs.congr k₁.2.2) hdi hz (by omega_using [hk1]) (by omega_using [hk2]) (by rw [hK, ofNat_toNat64])
    hN (fun i hi => by rw [k₁.2.1, k₁.2.2]; exact c.hpr i hi) c.hps)
    fun t₂ ⟨hN₂, hR₂, hW₂, hb₂, hz₂, f₂, k₂⟩ mx₂ => ?_)
  rw [pre_wv_entry c i₁ (by omega_using [])] at hN₂
  rw [pre_wv_entry c i₁ (by omega_using [])] at hR₂
  have x₂ := Fixed.of_frm f₂ (pdLoadRanges_fixed _)
  have i₂ : InScr (stackArg s 2) ((stackArg s 3).toNat * 8) s.mem t₂.mem :=
    i₁.trans (InScr.of_frm f₂ fun r hr => (pdLoadRanges_le _ r hr).trans hz)
  have kk := k₁.trans k₂
  have hs₂ := c.hs.congr kk.2.2
  have hdi₂ : t₂.gpr .rdi = stackArg s 2 := (k₂.gpr (by decide)).trans hdi
  have hO₂ : word t₂.mem (stackArg s 2) (8 * sOut) = s.gpr .rdi := by rw [x₂ sOut (by decide)]; exact hO
  have hK₂ : word t₂.mem (stackArg s 2) (8 * sK) = BitVec.ofNat 64 (s.gpr .rsi).toNat := by
    rw [x₂ sK (by decide), hK, ofNat_toNat64]
  have hout₂ : ∀ j < (s.gpr .rsi).toNat, InRegions t₂.wr (s.gpr .rdi + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [kk.2.2]; exact c.hout j hj
  -- What either branch leaves.
  have fin : ∀ t r (cb : Bool),
      MainPost t₂ t (stackArg s 2) ((stackArg s 3).toNat * 8) (s.gpr .rsi).toNat (s.gpr .rdi) r cb →
      (∀ nB : List Byte, nB.length = (s.gpr .rsi).toNat →
        Spec.Rsa.modulusValid (Spec.Rsa.os2ip nB) (s.gpr .rsi).toNat = true →
        wv s.mem (s.gpr .rdx) 0 (((s.gpr .rsi).toNat + 7) / 8) = Spec.Rsa.os2ip nB →
        wv s.mem (s.gpr .rdx) (8 * (((s.gpr .rsi).toNat + 7) / 8)) (((s.gpr .rsi).toNat + 7) / 8) =
          2 ^ (128 * (((s.gpr .rsi).toNat + 7) / 8)) % Spec.Rsa.os2ip nB →
        cb = decide (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rsi).toNat) < Spec.Rsa.os2ip nB) ∧
        r = if Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rsi).toNat) < Spec.Rsa.os2ip nB then
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rsi).toNat) ^
            Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) % Spec.Rsa.os2ip nB else 0) →
      gprPreserved s t ∧ pdContract.post s t := by
    intro t r cb hp H
    refine ⟨⟨fun reg hreg => ?_, Mem.readW_congr fun b hb => ?_⟩, fun nB hl hpp => ?_⟩
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hreg
      rcases hreg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (hp.saved 0 (by decide)).trans ((x₂ 0 (by decide)).trans h0)
      · exact (hp.saved 1 (by decide)).trans ((x₂ 1 (by decide)).trans h1)
      · exact (hp.keep.gpr (by decide)).trans (kk.gpr (by decide))
      · exact (hp.saved 2 (by decide)).trans ((x₂ 2 (by decide)).trans h2)
      · exact (hp.saved 3 (by decide)).trans ((x₂ 3 (by decide)).trans h3)
      · exact (hp.saved 4 (by decide)).trans ((x₂ 4 (by decide)).trans h4)
      · exact (hp.saved 5 (by decide)).trans ((x₂ 5 (by decide)).trans h5)
    · obtain ⟨hZx, hne⟩ := c.hret b hb
      rw [hp.frame _ hZx hne, i₂ _ hZx]
    · rw [c.hpl] at hpp
      obtain ⟨hv, hNv, hRv⟩ := pre_of_some hl hk1 hpp
      exact written_of hl hp.bytes hp.rax (fun _ => H nB hl hv hNv hRv) fun h => absurd h (by rw [hv]; decide)
  generalize hcb : (decide ((word t₂.mem (stackArg s 2) (slot (((s.gpr .rsi).toNat + 7) / 8) aN)).toNat % 2 = 1) &&
      decide (wv t₂.mem (stackArg s 2) (slot (((s.gpr .rsi).toNat + 7) / 8) aR2) (((s.gpr .rsi).toNat + 7) / 8) <
        wv t₂.mem (stackArg s 2) (slot (((s.gpr .rsi).toNat + 7) / 8) aN) (((s.gpr .rsi).toNat + 7) / 8)) &&
      decide (word t₂.mem (stackArg s 2) (slot (((s.gpr .rsi).toNat + 7) / 8) aN + 8 * ((((s.gpr .rsi).toNat + 7) / 8) - 1)) ≠ 0))
    = cb at hz₂
  refine WP.ite (!cb) (by simp [eval, hz₂]) (fun hb => ?_) (fun hb => ?_)
  · -- Values of no modulus.
    have hcf : cb = false := by simpa using hb
    refine WP.mono_mx (by decide +kernel) (fail_ok hs₂ hdi₂ (by omega_using [hZ']) (by omega_using [hk1]) (by omega_using [hk2]) hO₂ hK₂ hout₂ c.houts)
      fun t hp mxt => ⟨fin t 0 false hp fun nB hl hv hNv hRv => ?_, by rw [mxt, mx₂, mx₁]⟩
    obtain ⟨hodd, -, hlo⟩ := valid_facts hv hk1
    have := checks_true (by omega_using [hk1]) (hN₂.trans hNv) hodd hlo
      (by rw [hR₂, hRv]; exact Nat.mod_lt _ (by omega_using [hodd]))
    rw [hcb, hcf] at this
    exact absurd this (by decide)
  · have hct : cb = true := by simpa using hb
    rw [hct] at hcb
    obtain ⟨hodd, hN1, hRN⟩ := checks_facts (by omega_using [hk1]) hcb
    have hpre := pdPre_of c hdi hO hK hE hL hIn ho₁ k₁ hW₂ hb₂ f₂ k₂ hodd hN1 (checks_big (by omega_using [hk1]) hcb) hRN hev
    refine WP.mono (hrest hpre) fun t ⟨y, hy, hp, mxt⟩ => ⟨fin t _ _ hp fun nB hl hv hNv hRv => ?_,
      by rw [mxt, mx₂, mx₁]⟩
    rw [hN₂.trans hNv] at hy hp ⊢
    have hyX := hy (by
      rw [hR₂, hRv, Nat.mod_mod, ← Nat.pow_add, show 128 * (((s.gpr .rsi).toNat + 7) / 8) =
        64 * (((s.gpr .rsi).toNat + 7) / 8) + 64 * (((s.gpr .rsi).toNat + 7) / 8) by omega_using []])
    exact ⟨rfl, by rw [hyX]⟩

/-- The code after the check of `e`, for a valid `e`. -/
theorem code_correct (M : Mont)
    (hmx : (Folded.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true) (s : State) (h : pdContract.pre s)
    (hev : Spec.Rsa.exponentValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)) = true) :
    ∃ t s', Exec isa (Folded.code M.mm) s t s' ∧ abiPreserved s s' ∧ pdContract.post s s' := by
  have h' := hmx
  simp only [Folded.code, Code.allInstrs, Bool.and_eq_true] at h'
  have hr := h'.2.2.2
  have hmxp : (seqs (phases M)).allInstrs (fun i => !loadsMxcsr i) = true := by
    have h'' := hr
    rw [rest_eq, allInstrs_seqs_append _ (a := wordIn ++ restStepsWith VG.Impl.Rsa.X86_64.Compare8.code)
        (b := phases M ++ wordOutStepsArr aY) (by simp [wordIn]) (by simp [phases]),
      allInstrs_seqs_append _ (a := phases M) (b := wordOutStepsArr aY) (by simp [phases])
        (by simp [wordOutStepsArr]), Bool.and_eq_true, Bool.and_eq_true] at h''
    exact h''.2.1
  exact codeWith_correct (Folded.rest M.mm) (fun hp => WP.mono_mx hr (rest_ok M hp hmxp)
    fun t ⟨y, hy, hq⟩ mxt => ⟨y, hy, hq, by rw [mxt]⟩) s h hev

end VG.Proof.Bignum.X86_64.FoldedPublic

end

end

@[expose] public section

namespace VG.Proof.Bignum.X86_64.FoldedPublic
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Checked
open VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Proof.MlKem.X86_64

/-- `vg_rsa_public_precomputed_checked`: the code runs only for a valid `e`. -/
theorem checked_correct (M : Mont)
    (hmx : (Folded.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (h : pdContract.pre s) :
    ∃ tr t, Exec isa (Folded.checked M.mm) s tr t ∧ abiPreserved s t ∧ pdChkContract.post s t := by
  refine guarded_correct (fun s h hv => code_correct M hmx s h (by simpa only [eValid, eBytes] using hv))
    (fun _ h => pdGeom h) (fun s t hs h => (pdPre_same hs).symm ▸ h) ?_ ?_ s h
  · intro s t s' _ hs hv hp nB hl hpre
    simp only [pdContract, stackArg_same hs, hs.rdi, hs.rsi, hs.rdx, hs.rcx, hs.r8, hs.r9, hs.mem] at hp
    simp only [eValid, eBytes] at hv
    simp only [Spec.Rsa.publicOpChecked, hv, ↓reduceIte]
    exact hp nB hl hpre
  · intro s s' h hv hb hax nB _ _
    simp only [eValid, eBytes] at hv
    simp only [Spec.Rsa.publicOpChecked, hv, Bool.false_eq_true, ite_false, Spec.Rsa.written, hax]
    exact ⟨rfl, hb⟩

end VG.Proof.Bignum.X86_64.FoldedPublic

end

end

@[expose] public section

namespace VG.Proof.Bignum.X86_64.FoldedPublic
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Checked
open VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

/-- `Checked.guarded` of code that is constant time for valid `e`s. -/
theorem guardedPd_ct {code : Prog isa}
    (hcode : ConstantTime isa (fun s => pdContract.pre s ∧ Rsa.X86_64.eValid s = true) pdContract.pub code) :
    ConstantTime isa pdContract.pre pdContract.pub (Checked.guarded code) :=
  guarded_ct hcode (fun _ h => pdGeom h) (fun s t hs h => (pdPre_same hs).symm ▸ h)
    (fun _ _ _ _ hp => ⟨fun r hr => hp.1 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp), hp.2.2.2.2.2.2⟩)
    fun _ _ _ _ h₁ h₂ hp => pdPub_same h₁ h₂ hp

theorem checked_ct (M : Mont)
    (hfinal : RelCT isa (Two GoodL) (M.mm aY aX aY) (fun _ _ => True)) :
    ConstantTime isa pdContract.pre pdContract.pub (Folded.checked M.mm) :=
  guardedPd_ct (code_constantTime M hfinal)

end VG.Proof.Bignum.X86_64.FoldedPublic
