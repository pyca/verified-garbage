import VerifiedGarbage.Proof.AesGcmSiv.AArch64.KeysCT

/-!
# AES-GCM-SIV on AArch64: POLYVAL is constant time

Untrusted: everything here is checked by Lean. Both runs absorb the same
chunks of blocks: their number depends only on the lengths, which are
public; the code around each call of `vg_ghash` passes the taint analysis,
and each call has the same arguments in both runs.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcmSiv.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_gh rel_ite GcmImpl GhCall gh_call eval_zero eval_nonzero Others)

theorem chunkPre_check : ∃ h, (taint.check (Taint.ofRegs (pubRegs [.x27, .x28])) chunkPre h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem chunkEnd_check :
    ∃ h, (taint.check (Taint.ofRegs (pubRegs [.x28])) (.block [.lsr .x .x9 .x28 4]) h).isSome = true :=
  ⟨_, by taint_decide⟩

/-- A chunk, in two runs with the same public arguments, pointer and count. -/
theorem chunk_rel (v : GcmImpl) {p : Prm} (L : Lay p) {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂)
    {Q : Addr} {m : Nat} (hm : m < 2 ^ 64) (h16 : 16 ≤ m) (hQ₁ : Src p τ₁ Q (16 * (m / 16)))
    (hQ₂ : Src p τ₂ Q (16 * (m / 16))) (a27 : τ₁.gpr .x27 = Q) (b27 : τ₂.gpr .x27 = Q)
    (a28 : τ₁.gpr .x28 = BitVec.ofNat 64 m) (b28 : τ₂.gpr .x28 = BitVec.ofNat 64 m) :
    RelCT isa (Eq2 τ₁ τ₂) (chunk v.callees) TT := by
  refine rel_seq (rel_env E₁ E₂ [.x27, .x28] (by simp [a27, b27, a28, b28]) chunkPre_check)
    (chunkPre_ok L E₁ hm h16 hQ₁ a27 a28) (chunkPre_ok L E₂ hm h16 hQ₂ b27 b28) fun u₁ u₂ P₁ P₂ => ?_
  have wG : ∀ {u : State}, ChunkPre p Q m (min (m / 16) 64) τ₁ u ∨ ChunkPre p Q m (min (m / 16) 64) τ₂ u →
      WP isa (callGh v.callees) u fun w => Env p w ∧ w.gpr .x28 = BitVec.ofNat 64 (m - 16 * min (m / 16) 64) :=
    fun h => by
      rcases h with P | P <;>
      exact WP.mono (gh_call v.gh P.call) fun _ G =>
        ⟨P.env.of_saved G.saved G.sp G.rd G.wr, by rw [G.saved _ (by decide) (by decide), P.x28]⟩
  exact rel_seq (rel_gh v.gh P₁.call P₂.call (P₁.env.sp_eq P₂.env)) (wG (.inl P₁)) (wG (.inr P₂))
    fun w₁ w₂ G₁ G₂ => rel_env G₁.1 G₂.1 [.x28] (by simp [G₁.2, G₂.2]) chunkEnd_check

/-- The chunks, in two runs from `σ₁` and `σ₂` with the same public arguments. -/
theorem chunks_rel (v : GcmImpl) {p : Prm} (L : Lay p) {σ₁ σ₂ : State} {Q : Addr} {m : Nat} (hm : m < 2 ^ 64)
    (h16 : 16 ≤ m) (hQ₁ : Src p σ₁ Q (16 * (m / 16))) (hQ₂ : Src p σ₂ Q (16 * (m / 16))) {d : Nat}
    (hd : d < m / 16) {τ₁ τ₂ : State} (I₁ : CInv p σ₁ Q m d τ₁) (I₂ : CInv p σ₂ Q m d τ₂) :
    RelCT isa (Eq2 τ₁ τ₂) (.loop (chunk v.callees) (.nonzero .x .x9)) TT := by
  refine rel_loop (fun k t₁ t₂ => ∃ d, k = m / 16 - d ∧ d < m / 16 ∧ CInv p σ₁ Q m d t₁ ∧ CInv p σ₂ Q m d t₂)
    (fun k t₁ t₂ ⟨d, hk, hd, J₁, J₂⟩ => ?_) (m / 16 - d) ⟨d, rfl, hd, I₁, I₂⟩
  refine rel_wpQ (chunk_rel v L J₁.abs.env J₂.abs.env (by omega) (by omega) (J₁.src hQ₁ hd) (J₂.src hQ₂ hd)
      J₁.x27 J₂.x27 J₁.x28 J₂.x28)
    (chunk_ok v L J₁.abs.env (by omega) (by omega) (J₁.src hQ₁ hd) J₁.x27 J₁.x28)
    (chunk_ok v L J₂.abs.env (by omega) (by omega) (J₂.src hQ₂ hd) J₂.x27 J₂.x28) fun a b C₁ C₂ => ?_
  obtain ⟨K₁, x9₁⟩ := J₁.step L hm hQ₁ hd C₁
  obtain ⟨K₂, x9₂⟩ := J₂.step L hm hQ₂ hd C₂
  have ev₁ := eval_nonzero x9₁ (by omega)
  have ev₂ := eval_nonzero x9₂ (by omega)
  refine ⟨by rw [ev₁, ev₂], fun hc => ?_⟩
  rw [ev₁] at hc
  have he : d + min (m / 16 - d) 64 ≠ m / 16 := by simp at hc; omega
  exact ⟨m / 16 - (d + min (m / 16 - d) 64), by omega, d + min (m / 16 - d) 64, rfl, by omega, K₁, K₂⟩

theorem absHead_check :
    ∃ h, (taint.check (Taint.ofRegs (pubRegs [.x27, .x28])) (.block [.lsr .x .x9 .x28 4]) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem absTailPre_check : ∃ h, (taint.check (Taint.ofRegs (pubRegs [.x27, .x28])) absTailPre h).isSome = true :=
  ⟨_, by taint_decide⟩

/-- `chunk` on the block at `W + 224`. -/
theorem chunkB_rel (v : GcmImpl) {p : Prm} (L : Lay p) {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂)
    (a27 : τ₁.gpr .x27 = p.W + BitVec.ofNat 64 224) (b27 : τ₂.gpr .x27 = p.W + BitVec.ofNat 64 224)
    (a28 : τ₁.gpr .x28 = BitVec.ofNat 64 16) (b28 : τ₂.gpr .x28 = BitVec.ofNat 64 16) :
    RelCT isa (Eq2 τ₁ τ₂) (chunk v.callees) TT :=
  chunk_rel v L E₁ E₂ (m := 16) (by decide) (by decide) (srcB L E₁.perm) (srcB L E₂.perm) a27 b27 a28 b28

/-- `absorb`, in two runs with the same public arguments, pointer and count. -/
theorem absorb_rel (v : GcmImpl) {p : Prm} (L : Lay p) {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂)
    {Q : Addr} {m : Nat} (hm : m < 2 ^ 64) (hw : Q.toNat + m ≤ 2 ^ 64) (hd : (⟨Q, m⟩ : Region).Disjoint ⟨p.W, 3808⟩)
    (hc₁ : Covers [⟨Q, m⟩] (τ₁.rd ++ τ₁.wr)) (hc₂ : Covers [⟨Q, m⟩] (τ₂.rd ++ τ₂.wr))
    (a27 : τ₁.gpr .x27 = Q) (b27 : τ₂.gpr .x27 = Q) (a28 : τ₁.gpr .x28 = BitVec.ofNat 64 m)
    (b28 : τ₂.gpr .x28 = BitVec.ofNat 64 m) :
    RelCT isa (Eq2 τ₁ τ₂) (absorb v.callees) TT := by
  have hQ₁ : Src p τ₁ Q m := Src.ofW L hc₁ hm hw hd
  have hQ₂ : Src p τ₂ Q m := Src.ofW L hc₂ hm hw hd
  refine rel_seq (rel_env E₁ E₂ [.x27, .x28] (by simp [a27, b27, a28, b28]) absHead_check) (absHead_ok hm a28)
    (absHead_ok hm b28) fun u₁ u₂ ⟨x9₁, ho₁, m₁, sp₁, rd₁, wr₁⟩ ⟨x9₂, ho₂, m₂, sp₂, rd₂, wr₂⟩ => ?_
  have F₁ : Env p u₁ := E₁.keep (fun q hq => ho₁ q (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  have F₂ : Env p u₂ := E₂.keep (fun q hq => ho₂ q (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₂ rd₂ wr₂
  have u27₁ : u₁.gpr .x27 = Q := by rw [ho₁ _ (by decide), a27]
  have u27₂ : u₂.gpr .x27 = Q := by rw [ho₂ _ (by decide), b27]
  have u28₁ : u₁.gpr .x28 = BitVec.ofNat 64 m := by rw [ho₁ _ (by decide), a28]
  have u28₂ : u₂.gpr .x28 = BitVec.ofNat 64 m := by rw [ho₂ _ (by decide), b28]
  have hQ₁' := hQ₁.of_eq rd₁ wr₁
  have hQ₂' := hQ₂.of_eq rd₂ wr₂
  -- The whole blocks.
  refine rel_seq (rel_ite (eval_zero x9₁ (by omega)) (eval_zero x9₂ (by omega))
      (fun _ => RelCT.block_nil fun _ _ _ => trivial) (fun hf => ?_))
    (absMid_ok v L F₁ hm hQ₁' u27₁ u28₁ x9₁) (absMid_ok v L F₂ hm hQ₂' u27₂ u28₂ x9₂)
    fun w₁ w₂ ⟨A₁, x27₁, x28₁⟩ ⟨A₂, x27₂, x28₂⟩ => ?_
  · have h0 : m / 16 ≠ 0 := by simpa using hf
    exact chunks_rel v L hm (by omega) (hQ₁'.take (by omega)) (hQ₂'.take (by omega)) (d := 0) (by omega)
      (CInv.zero F₁ u27₁ u28₁) (CInv.zero F₂ u27₂ u28₂)
  -- The last bytes.
  refine rel_ite (eval_zero x28₁ (by omega)) (eval_zero x28₂ (by omega))
    (fun _ => RelCT.block_nil fun _ _ _ => trivial) (fun hf => ?_)
  have h0 : m % 16 ≠ 0 := by simpa using hf
  have dT : (⟨Q + BitVec.ofNat 64 (16 * (m / 16)), m % 16⟩ : Region).Disjoint ⟨p.W, 3808⟩ :=
    hd.sub_left (Offset.sub_base Q (by omega))
  have hs₁ := (hQ₁'.slice (a := 16 * (m / 16)) (k := m % 16) (by omega)).of_eq A₁.rd A₁.wr
  have hs₂ := (hQ₂'.slice (a := 16 * (m / 16)) (k := m % 16) (by omega)).of_eq A₂.rd A₂.wr
  refine rel_seq (rel_env A₁.env A₂.env [.x27, .x28] (by simp [x27₁, x27₂, x28₁, x28₂]) absTailPre_check)
    (absTailPre_ok L A₁.env (by omega) (by omega) hs₁.rd dT x27₁ x28₁)
    (absTailPre_ok L A₂.env (by omega) (by omega) hs₂.rd dT x27₂ x28₂) fun z₁ z₂ T₁ T₂ => ?_
  exact chunkB_rel v L T₁.env T₂.env T₁.x27 T₂.x27 T₁.x28 T₂.x28

theorem lensBlock_check : ∃ h, (taint.check (Taint.ofRegs (pubRegs [])) (.block lensBlock) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem tagIn_check : ∃ h, (taint.check (Taint.ofRegs (pubRegs [])) (.block tagIn) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem polyA_check : ∃ h, (taint.check (Taint.ofRegs (pubRegs []))
    (.block [Impl.AesGcm.AArch64.mov .x27 .x23, Impl.AesGcm.AArch64.mov .x28 .x24]) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem polyD_check : ∃ h, (taint.check (Taint.ofRegs (pubRegs []))
    (.block [Impl.AesGcm.AArch64.mov .x27 .x25, Impl.AesGcm.AArch64.mov .x28 .x26]) h).isSome = true :=
  ⟨_, by taint_decide⟩

/-- Two registers set to the arguments in `x19`–`x26`. -/
theorem mov2_ok {p : Prm} {t : State} (E : Env p t) {a b : Reg} (_ha : a ∈ envRegs) (hb : b ∈ envRegs) :
    WP isa (.block [Impl.AesGcm.AArch64.mov .x27 a, Impl.AesGcm.AArch64.mov .x28 b]) t fun t' =>
      Env p t' ∧ t'.gpr .x27 = t.gpr a ∧ t'.gpr .x28 = t.gpr b ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  refine WP.of_runBlock ⟨_, by grun [], ?_⟩
  have hb' : b ≠ .x27 := fun e => by subst e; revert hb; decide
  exact ⟨(E.write (by decide) _).write (by decide) _, by simp [gpr_write], by simp [gpr_write, hb'], rfl, rfl, rfl⟩

/-- `polyval`, in two runs with the same public arguments. -/
theorem polyval_rel (v : GcmImpl) {p : Prm} (L : Lay p) {σ₁ σ₂ : State} (E₁ : Env p σ₁) (E₂ : Env p σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) (polyval v.callees) TT := by
  refine rel_seq (rel_env E₁ E₂ [] (by simp) polyA_check) (mov2_ok E₁ (a := .x23) (b := .x24) (by decide) (by decide))
    (mov2_ok E₂ (a := .x23) (b := .x24) (by decide) (by decide)) fun a₁ a₂ ⟨G₁, a27₁, a28₁, _, rd₁, wr₁⟩
      ⟨G₂, a27₂, a28₂, _, rd₂, wr₂⟩ => ?_
  rw [E₁.x23] at a27₁; rw [E₁.x24] at a28₁; rw [E₂.x23] at a27₂; rw [E₂.x24] at a28₂
  have hc₁ : Covers [⟨p.A, p.al⟩] (a₁.rd ++ a₁.wr) := G₁.perm.aad
  have hc₂ : Covers [⟨p.A, p.al⟩] (a₂.rd ++ a₂.wr) := G₂.perm.aad
  refine rel_seq (absorb_rel v L G₁ G₂ L.al_lt L.aw L.a_w hc₁ hc₂ a27₁ a27₂ a28₁ a28₂)
    (absorb_ok v L G₁ hc₁ L.al_lt L.aw L.a_w a27₁ a28₁) (absorb_ok v L G₂ hc₂ L.al_lt L.aw L.a_w a27₂ a28₂)
    fun b₁ b₂ B₁ B₂ => ?_
  refine rel_seq (rel_env B₁.env B₂.env [] (by simp) polyD_check)
    (mov2_ok B₁.env (a := .x25) (b := .x26) (by decide) (by decide))
    (mov2_ok B₂.env (a := .x25) (b := .x26) (by decide) (by decide)) fun c₁ c₂ ⟨H₁, c27₁, c28₁, _, _, _⟩
      ⟨H₂, c27₂, c28₂, _, _, _⟩ => ?_
  rw [B₁.env.x25] at c27₁; rw [B₁.env.x26] at c28₁; rw [B₂.env.x25] at c27₂; rw [B₂.env.x26] at c28₂
  have dc₁ : Covers [⟨p.D, p.n⟩] (c₁.rd ++ c₁.wr) := Proof.AesGcm.AArch64.covers_left H₁.perm.d
  have dc₂ : Covers [⟨p.D, p.n⟩] (c₂.rd ++ c₂.wr) := Proof.AesGcm.AArch64.covers_left H₂.perm.d
  refine rel_seq (absorb_rel v L H₁ H₂ L.n_lt L.dw L.d_w dc₁ dc₂ c27₁ c27₂ c28₁ c28₂)
    (absorb_ok v L H₁ dc₁ L.n_lt L.dw L.d_w c27₁ c28₁) (absorb_ok v L H₂ dc₂ L.n_lt L.dw L.d_w c27₂ c28₂)
    fun d₁ d₂ D₁ D₂ => ?_
  refine rel_seq (c₁ := lens v.callees) ?_ (lens_ok v L D₁.env) (lens_ok v L D₂.env) fun e₁ e₂ F₁ F₂ =>
    rel_env F₁.env F₂.env [] (by simp) tagIn_check
  have wL : ∀ {d : State}, Env p d → WP isa (.block lensBlock) d fun t =>
      Env p t ∧ t.gpr .x27 = p.W + BitVec.ofNat 64 224 ∧ t.gpr .x28 = BitVec.ofNat 64 16 := fun E => by
    have w₀ := E.perm.wW (show 224 + 8 ≤ 3808 by decide)
    have w₈ := E.perm.wW (show 232 + 8 ≤ 3808 by decide)
    refine WP.run ⟨_, by simp only [lensBlock]; grun [E.x19, E.x24, E.x26, w₀, w₈], rfl⟩ fun t ht => ?_
    subst ht
    refine ⟨E.keep (fun q hq => by
        simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]) rfl rfl rfl,
      by simp [gpr_write, E.x19], by simp [gpr_write, movz_lit (show 16 < 2 ^ 16 by decide)]⟩
  exact rel_seq (rel_env D₁.env D₂.env [] (by simp) lensBlock_check) (wL D₁.env) (wL D₂.env)
    fun f₁ f₂ ⟨K₁, x27₁, x28₁⟩ ⟨K₂, x27₂, x28₂⟩ => chunkB_rel v L K₁ K₂ x27₁ x27₂ x28₁ x28₂

end VG.Proof.AesGcmSiv.AArch64
