import VerifiedGarbage.Proof.Bignum.X86_64.FoldedIO
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT

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
      xrun [State.ea, hdr, hdi, hdrOff, hs.ld (d := 8 * sW) (by unfold sW; omega),
        hs.ld (d := 8 * sArr aX) (by unfold sArr aX; omega), hs.ld (d := 8 * sArr aN) (by unfold sArr aN; omega),
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
    refine WP.mono (Compare8.code_ok hs hbx h10 h12 hbp (by omega) hk'
      (by have := slot_le (w := p.w) (show aX < 8 by decide); omega)
      (by have := slot_le (w := p.w) (show aN < 8 by decide); omega)) fun t ⟨_, hm, k⟩ =>
      ⟨h.mem hm k (by decide), (k.gpr (by decide)).trans h10, (k.gpr (by decide)).trans h12⟩
  -- `-m⁻¹`, and the number 1.
  refine RelCT.seq (two_piece (Ψ := S7) [.rdi, .r10] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.1.2.1, h₂.1.2.1]
    · rw [h₁.2.1, h₂.2.1]) (by taint_decide) ?_) ?_
  · intro p s ⟨h, h10, h12⟩
    obtain ⟨hs, hdi, hZ, hk, -, hW, hb, hodd₀⟩ := h
    exact WP.mono (blk7_ok hs hdi hZ (by omega) hW hb h10 hodd₀) fun t ⟨mi, hH, hs', hdi', hcx, k⟩ =>
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
    hs.ld (by have := hdr_lt_slot p.w 8 (show sArr aOne < 32 by decide); omega)
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
      xrun [State.ea, hdr, h.rdi, hdrOff, h.scr.ld (d := 8 * sIn) (by unfold sIn sFn; omega),
        h.scr.ld (d := 8 * sK) (by unfold sK sFn; omega), h.scr.ld (d := 8 * sArr aX) (by unfold sArr aX; omega),
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
  have hn' : p.B.toNat + slot ((p.k + 7) / 8) 8 ≤ 2 ^ 64 := by omega
  have hw : 2 ≤ ((p.k + 7) / 8) := by show 2 ≤ (p.k + 7) / 8; omega
  refine WP.mono (wordLoadArr_ok h.scr h.inSpan (by decide) h.z h.x h.xl (by omega) (by omega) hsi hcx hbx)
    fun t ⟨_, ha, k⟩ => ⟨h.scr.congr k.2.2, (k.gpr (by decide)).trans h.rdi, h.z,
      hw, show ((p.k + 7) / 8) < 2 ^ 31 by show (p.k + 7) / 8 < 2 ^ 31; omega,
      by rw [ha.hslot (by decide)]; exact h.hW, fun j hj => by rw [ha.hslot (by unfold sArr; omega)]; exact h.hb j hj, ?_⟩
  rw [ha.word0_of_not_mem (by decide) (by decide) hn' (by omega),
    ← wv_mod64 _ _ _ (show 1 ≤ ((p.k + 7) / 8) by omega), Nat.mod_mod_of_dvd _ (by decide), h.n, h.odd]

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
    obtain rfl := so_minv so₁ so₂ g₁.1.odd (show 1 ≤ ((p.k + 7) / 8) by show 1 ≤ (p.k + 7) / 8; omega)
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
    refine WP.mono (setupHead_ok hs hdi hZ (by omega) hK hN) fun t' ⟨h12, _, hsi, hbx, hW, hb, hf, k⟩ =>
      ⟨⟨h.congr hf (fun r hr => ?_) k (by decide), hW, hb⟩, by rw [hsi]; simp [off], hbx, h12⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [sW, sArr] <;> omega
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
      rintro r rfl; simp only [BitVec.ofNat_add_ofNat]; congr 1; omega
    have hsi' : t.gpr .rsi = p.pp := by rw [hsi]; simp [off]
    refine WP.mono (WP.keep [.rax, .rsi, .rbx] (Q := fun t' => t'.gpr .rsi = off p.pp (8 * ((p.d.k + 7) / 8)) ∧
        t'.gpr .rbx = off p.d.B (slot ((p.d.k + 7) / 8) aR2) ∧ t'.mem = t.mem) (by
      unfold eightW
      simp only [List.cons_append, List.nil_append]
      xrun [State.ea, hdr, h.1.2.1, hdrOff, hs.ld (d := 8 * sArr aR2) (by unfold sArr aR2; omega),
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
      xrun [State.ea, hdr, h.1.2.1, hdrOff, hs.ld (d := 8 * sArr aN) (by unfold sArr aN; omega),
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
    exact WP.mono (Compare8.code_ok h.1 hbx h10 h12 hbp (by omega) (by omega)
      (by have := slot_le (w := (p.d.k + 7) / 8) (show aR2 < 8 by decide); omega)
      (by have := slot_le (w := (p.d.k + 7) / 8) (show aN < 8 by decide); omega)) fun t' ⟨_, _, k⟩ =>
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
    have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.L.B (8 * i)) 8 := fun i hi => hg.scr.ld (by omega)
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
      (by have := slot_le (w := p.L.w) (show aY < 8 by decide); omega) hout hsep)
      fun t ⟨_, _, _, _, k⟩ => (k.gpr (by decide)).trans hdi
  exact two_taint [.rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁, h₂]) (by taint_decide)

theorem dd_wordOPre {q : DPub × BitVec 64} {t : State} (h : DD q t) : WordOPre ⟨DPub.L q, q.1.k, q.1.op⟩ t := by
  obtain ⟨xb, σ, g, hg⟩ := h
  have hk1 := g.1.k1
  have hk2 := g.1.k2
  exact ⟨_, hg, rfl, g.1.z, show 1 ≤ q.1.k by omega, show q.1.k < 2 ^ 31 by omega, by rw [g.fixed sOut (by decide)]; exact g.1.hO,
    by rw [g.fixed sK (by decide)]; exact g.1.hK, g.2.2.2, by rw [g.2.2.1.2.2]; exact g.1.outSpan,
    g.1.outSep⟩

theorem ce2_wordLoad {p : CPubD} {t : State} (h : CE2 p t) : WP isa (seqs (Precomputed.loadWith VG.Impl.Rsa.X86_64.Compare8.code)) t (CL p) := by
  obtain ⟨⟨B, Z, k, op, ep, ip, len, eb, N, R⟩, pp, rsp⟩ := p
  obtain ⟨s, hs, he⟩ := h
  have hs' := hs
  have he' := he
  obtain ⟨hdi, -, -, -, -, -, -, -, hN, hK, -, -, -, ho₁, k₁⟩ := he'
  obtain ⟨hpre, -, hB, hZ, hk, -, hpp, -, -, -, -, hNv, hRv⟩ := hs
  have c := pdCtx_of hpre
  have := c.hZ
  have := c.hk1
  have := c.hk2
  have hn := c.hs.nowrap
  have i₁ : InScr (stackArg s 2) ((stackArg s 3).toNat * 8) s.mem t.mem := InScr.of_outside ho₁ (by omega)
  have hz : slot (((s.gpr .rsi).toNat + 7) / 8) 8 ≤ (stackArg s 3).toNat * 8 := by unfold slot hdrBytes; omega
  refine WP.mono (pdLoadWith_ok VG.Impl.Rsa.X86_64.Compare8.code @Compare8.code_ok (c.hs.congr k₁.2.2) hdi hz (by omega) (by omega) (by rw [hK, ofNat_toNat64])
    hN (fun i hi => by rw [k₁.2.1, k₁.2.2]; exact c.hpr i hi) c.hps) fun t' ⟨hN₂, hR₂, hW₂, hb₂, hz₂, f₂, k₂⟩ => ?_
  rw [pre_wv_entry c i₁ (by omega), hNv] at hN₂
  rw [pre_wv_entry c i₁ (by omega), hRv] at hR₂
  rw [chk_eq (by omega), hN₂, hR₂] at hz₂
  subst hB hZ hk hpp
  exact ⟨s, t, hs', he, hN₂, hR₂, hW₂, hb₂, hz₂, f₂, k₂⟩


end VG.Proof.Bignum.X86_64
