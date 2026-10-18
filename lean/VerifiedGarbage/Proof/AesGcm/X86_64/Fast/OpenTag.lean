module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Open
public import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.Tail
public import VerifiedGarbage.Impl.AesGcm.X86_64.FastOpen
import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.AesGcm.X86_64.J0
import VerifiedGarbage.Proof.Aes.X86_64.Ctr32

/-!
# AES-GCM `open`'s path for TLS records: the tag

Untrusted: everything here is checked by Lean. `FastOpen.tagP` leaves what
`oneTag 112` does (`TagOk`, `oneTag_ok`), without calls: `H'` and `H'²` from
the prepared key context (`Fast.finPowP_ok`), the keystream of `J₀` and of the
counter block (`Short.finKs_ksOk`), the bytes left copied to `G[0]`
(`openTail_ok`, by `copyLoop`) or none (`openNoTail_ok`), `GHASH` continued
over `G`, the tag at `W + 112`, and `J₀` incremented (`incJ_ok`): `tagP_ok`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.FastOpen

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Short VG.WriteBytes
open VG.Impl.AesGcm.X86_64.FastOpen (incJ tagP)
open VG.Proof.AesGcm.X86_64
open VG.Proof.AesGcm.X86_64.Short (ShortFacts KsOk IsH1 IsH2 finTextArgs_ok finLens_ok finGh1_ok finGh2_ok finTest_ok
  tagK_ok finKs_ksOk writeW_zero128 ghash_snoc bytesAt_toBytes' add_ofNat_ofNat)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks inc32 zeros padLen toBytes ofBytes ctxH)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Gcm (Absorbed lensBlock)

/-! ## `J₀` incremented -/

/-- The last word of the block at `St`, big-endian, incremented in place:
`inc32` of the block. -/
theorem inc_block (m : Mem) (St : Addr) :
    blockAt (m.writeW (St + BitVec.ofNat 64 12)
      (X86_64.bswap32 (X86_64.bswap32 (m.readW (St + BitVec.ofNat 64 12) 32) + (BitVec.ofNat 64 1).setWidth 32))) St =
      inc32 (blockAt m St) := by
  refine VG.Proof.Aes.X86_64.ctr_after (n := 1) fun k hk => ?_
  rw [VG.Proof.Aes.X86_64.writeW_apply, Offset.sub_toNat' St (show 12 < 2 ^ 64 by decide) (by omega)]
  by_cases h : k < 12
  · rw [ite_eq_right (show ¬ 12 ≤ k by omega), ite_eq_right (show ¬ 2 ^ 64 + k - 12 < 32 / 8 by omega),
      ite_eq_left h]
  · rw [ite_eq_left (show 12 ≤ k by omega), ite_eq_left (show k - 12 < 32 / 8 by omega), ite_eq_right h,
      BitVec.setWidth_eq]

/-- `incJ`: `J₀`, at `St`, incremented. -/
theorem incJ_ok {Ctx St W SP : Addr} (s : State) (he : Env Ctx St W SP s) :
    ∃ t, runBlock isa incJ s = some t ∧ blockAt t.mem St = inc32 (blockAt s.mem St) ∧
      Frame [⟨St + BitVec.ofNat 64 12, 4⟩] s.mem t.mem ∧ (∀ g, g ≠ .rsi → t.gpr g = s.gpr g) ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ t.xmm = s.xmm := by
  have r₃ := he.perm.stR (show 12 + 4 ≤ 80 by decide)
  have w₃ := he.perm.stW (show 12 + 4 ≤ 80 by decide)
  refine ⟨_, by xrun [incJ, he.r14, r₃, w₃], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, ww32]
    exact inc_block _ _
  · simp only [mem_setReg, mem_arithFlags]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  · intro g hg; simp [gpr_setReg, gpr_arithFlags, hg]
  all_goals rfl

/-! ## The two ends of the tag -/

/-- What both ends of `tagP` start from: `FinPre` without the bytes left
writable, which `open` only reads. -/
structure TagPre (Ctx W SP : Addr) (H : Block) (al n r : Nat) (D : Addr) (s : State) : Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s
  x0 : s.xmm .xmm0 = revMask
  x1 : s.xmm .xmm1 = poly
  h1 : IsH1 H (s.xmm .xmm3)
  h2 : IsH2 H (s.xmm .xmm3) (s.xmm .xmm6)
  alen : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al
  tlen : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 n
  dat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D
  len : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 r
  r16 : r ≤ 16
  rd : Covers [⟨D, r⟩] (s.rd ++ s.wr)
  dW : (⟨D, r⟩ : Region).Disjoint ⟨W, 2560⟩

/-- Without bytes left: the tag of `GHASH` continued over the lengths block is
at `W + 112`. -/
theorem openNoTail_ok {Ctx W SP D : Addr} {H : Block} {al n r : Nat} {s : State} (P : TagPre Ctx W SP H al n r D s) :
    WP isa (.block (finLens ++ finGh1 ++ tagK uO)) s fun t =>
      Env Ctx (W + BitVec.ofNat 64 16) W SP t ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [⟨W + BitVec.ofNat 64 112, 16⟩, ⟨W + BitVec.ofNat 64 512, 32⟩] s.mem t.mem ∧
      blockAt t.mem (W + BitVec.ofNat 64 112) =
        ghashFrom H (blockAt s.mem (yA W)) [ofBytes (lensBlock al n)] ^^^ blockAt s.mem (W + BitVec.ofNat 64 1024) := by
  have he := P.env
  rw [List.append_assoc, WP.block_append_iff]
  obtain ⟨s₃, run₃, f₃, hL₃, g₃, rd₃, wr₃, x₃⟩ := finLens_ok s he P.alen P.tlen
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have he₃ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₃ := he.keep (fun g hg => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide)) rd₃ wr₃
  rw [WP.block_append_iff]
  refine WP.mono (finGh1_ok s₃ he₃ (H := H) (by rw [x₃]; exact P.x0) (by rw [x₃]; exact P.x1)
    (by rw [x₃]; exact P.h1)) fun s₄ ⟨y₄, o₄⟩ => ?_
  obtain ⟨s₅, run₅, tag₅, fW, g₅, rd₅, wr₅⟩ := tagK_ok (W := W) (o := 112) s₄
    ((o₄.gpr _ (by decide)).trans he₃.r15) (by rw [o₄.wr]; exact he₃.perm.w) (by decide)
    (by rw [o₄.xmm _ (by decide), x₃]; exact P.x0)
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  have m₄ := o₄.mem
  have bW : ∀ {d : Nat}, d + 16 ≤ 528 ∨ 544 ≤ d → d + 16 ≤ 2560 →
      blockAt s₃.mem (W + BitVec.ofNat 64 d) = blockAt s.mem (W + BitVec.ofNat 64 d) :=
    fun h h' => blockAt_frame f₃ fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact Offset.disjoint W (by omega) (by omega) (by decide)
  have hY : blockAt s₃.mem (yA W) = blockAt s.mem (yA W) := by
    simp only [yA, add_ofNat_ofNat]; exact bW (.inl (by decide)) (by decide)
  have hb₁ : blockAt s₃.mem (W + BitVec.ofNat 64 528) = ofBytes (lensBlock al n) := by
    rw [blockAt, hL₃]
  refine ⟨he₃.keep (fun g hg => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl <;> rw [g₅, o₄.gpr _ (by decide)]) (by rw [rd₅, o₄.rd]) (by rw [wr₅, o₄.wr]),
    by rw [rd₅, o₄.rd, rd₃], by rw [wr₅, o₄.wr, wr₃], ?_, ?_⟩
  · refine (f₃.sub fun q hq => ?_).trans ?_
    · simp only [List.mem_singleton] at hq; subst hq
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub _ (by decide) (by decide)⟩
    rw [← m₄]
    exact fW.sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · rw [tag₅, y₄, m₄, hY, hb₁, bW (d := 1024) (.inr (by decide)) (by decide)]

/-- With bytes left: they are copied to `G[0]`, and the tag of `GHASH`
continued over `G[0]` and the lengths block is at `W + 112`. -/
theorem openTail_ok {Ctx W SP D : Addr} {H : Block} {al n r : Nat} {s : State} (P : TagPre Ctx W SP H al n r D s)
    (h0 : r ≠ 0) :
    WP isa (.seq (.block finTextArgs) (.seq copyLoop (.block (finLens ++ finGh2 ++ tagK uO)))) s fun t =>
      Env Ctx (W + BitVec.ofNat 64 16) W SP t ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [⟨W + BitVec.ofNat 64 112, 16⟩, ⟨W + BitVec.ofNat 64 512, 32⟩] s.mem t.mem ∧
      blockAt t.mem (W + BitVec.ofNat 64 112) = ghashFrom H (blockAt s.mem (yA W))
          [ofBytes (bytesAt s.mem D r ++ zeros (16 - r)), ofBytes (lensBlock al n)] ^^^
        blockAt s.mem (W + BitVec.ofNat 64 1024) := by
  have he := P.env
  have hr := P.r16
  have dW : ∀ {d k : Nat}, d + k ≤ 2560 → (⟨D, r⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
    fun h => P.dW.sub_right (Lay.wSub h)
  have dWW : ∀ {d k e j : Nat}, d + k ≤ e ∨ e + j ≤ d → d + k ≤ 2560 → e + j ≤ 2560 →
      (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, j⟩ :=
    fun h _ _ => Offset.disjoint W h (by have := he.perm.w; omega) (by omega)
  -- `G[0]` zeroed, and the arguments.
  obtain ⟨s₁, run₁, m₁, di₁, si₁, -, cx₁, g₁, rd₁, wr₁, x₁⟩ := finTextArgs_ok s he P.dat P.len
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have lp : LoopPre s₁ D (W + BitVec.ofNat 64 512) r :=
    ⟨si₁, di₁, cx₁, by omega, by omega, by rw [rd₁, wr₁]; exact P.rd, by rw [wr₁]; exact he.perm.wC (by omega),
      dW (by omega)⟩
  -- The copy.
  refine WP.seq (WP.mono (copyLoopX_ok s₁ lp) fun s₂ ⟨m₂, g₂, rd₂, wr₂, x₂⟩ => ?_)
  have he₁ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ := he.keep (fun g hg => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide) (by decide) (by decide)) rd₁ wr₁
  have he₂ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := he₁.keep (fun g hg => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> exact g₂ _ (by decide) (by decide)) rd₂ wr₂
  have x₂' : ∀ q, q ≠ .xmm7 → s₂.xmm q = s.xmm q := fun q hq => by rw [x₂, x₁ q hq]
  generalize hc : bytesAt s₁.mem D r = c at m₂
  have hcl : c.length = r := by rw [← hc, length_bytesAt]
  have f₁ : Frame [⟨W + BitVec.ofNat 64 512, 16⟩] s.mem s₁.mem := by
    rw [m₁]; exact writeBytes_frame' _ (List.length_replicate ..)
  have f₂ : Frame [⟨W + BitVec.ofNat 64 512, r⟩] s₁.mem s₂.mem := by
    rw [m₂]; exact writeBytes_frame' _ hcl
  have F₂ : Frame [⟨W + BitVec.ofNat 64 512, 32⟩] s.mem s₂.mem := by
    refine (f₁.sub fun q hq => ?_).trans (f₂.sub fun q hq => ?_) <;>
      simp only [List.mem_singleton] at hq <;> subst hq <;>
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩
  have kW : ∀ {d k : Nat}, d + k ≤ 512 ∨ (544 ≤ d ∧ d + k ≤ 2560) →
      ∀ q ∈ [(⟨W + BitVec.ofNat 64 512, 32⟩ : Region)], (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint q :=
    fun h q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact dWW (by omega) (by omega) (by decide)
  have rW₂ : ∀ d, d + 8 ≤ 512 → s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d h => F₂.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (kW (.inl h)) (by decide)
  -- The lengths block.
  rw [List.append_assoc, WP.block_append_iff]
  obtain ⟨s₃, run₃, f₃, hL₃, g₃, rd₃, wr₃, x₃⟩ := finLens_ok s₂ he₂ (by rw [rW₂ 184 (by decide)]; exact P.alen)
    (by rw [rW₂ 192 (by decide)]; exact P.tlen)
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have he₃ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₃ := he₂.keep (fun g hg => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide)) rd₃ wr₃
  have x₃' : ∀ q, q ≠ .xmm7 → s₃.xmm q = s.xmm q := fun q a => by rw [x₃, x₂' q a]
  have F₃ : Frame [⟨W + BitVec.ofNat 64 512, 32⟩] s.mem s₃.mem :=
    F₂.trans (f₃.sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩)
  -- `GHASH`.
  rw [WP.block_append_iff]
  refine WP.mono (finGh2_ok s₃ he₃ (H := H) (by rw [x₃' _ (by decide)]; exact P.x0)
    (by rw [x₃' _ (by decide)]; exact P.x1)
    (by rw [x₃' .xmm3 (by decide), x₃' .xmm6 (by decide)]; exact P.h2)) fun s₄ ⟨y₄, o₄⟩ => ?_
  -- The tag.
  obtain ⟨s₅, run₅, tag₅, fW, g₅, rd₅, wr₅⟩ := tagK_ok (W := W) (o := 112) s₄
    ((o₄.gpr _ (by decide)).trans he₃.r15) (by rw [o₄.wr]; exact he₃.perm.w) (by decide)
    (by rw [o₄.xmm _ (by decide), x₃' _ (by decide)]; exact P.x0)
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  have m₄ := o₄.mem
  have hc' : c = bytesAt s.mem D r := by
    rw [← hc, bytesAt_frame f₁ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact dW (by decide)) (by omega)]
  -- `G[0]`: the ciphertext and zeros.
  have z₁ : bytesAt s₁.mem (W + BitVec.ofNat 64 512 + BitVec.ofNat 64 r) (16 - r) = zeros (16 - r) := by
    have e := bytesAt_add s₁.mem (W + BitVec.ofNat 64 512) r (16 - r)
    have e16 : bytesAt s₁.mem (W + BitVec.ofNat 64 512) 16 = List.replicate 16 0 := by
      rw [m₁]; exact bytesAt_writeBytes_self _ _ _ (by decide)
    rw [Nat.add_sub_cancel' (by omega), e16, show List.replicate 16 (0 : Byte) = List.replicate r 0 ++
      List.replicate (16 - r) 0 by rw [List.replicate_append_replicate, Nat.add_sub_cancel' (by omega)]] at e
    exact ((List.append_inj e (by rw [List.length_replicate, length_bytesAt])).2).symm
  have hG0 : bytesAt s₃.mem (W + BitVec.ofNat 64 512) 16 = c ++ zeros (16 - r) := by
    rw [bytesAt_frame f₃ (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact dWW (.inl (by decide)) (by decide) (by decide))
      (by decide), ← Nat.add_sub_cancel' (show r ≤ 16 by omega), bytesAt_add, Nat.add_sub_cancel' (by omega), m₂]
    have a₁ : bytesAt (writeBytes s₁.mem (W + BitVec.ofNat 64 512) c) (W + BitVec.ofNat 64 512) r = c := by
      rw [← hcl]; exact bytesAt_writeBytes_self _ _ _ (by omega)
    have a₂ : bytesAt (writeBytes s₁.mem (W + BitVec.ofNat 64 512) c) (W + BitVec.ofNat 64 512 + BitVec.ofNat 64 r)
        (16 - r) = bytesAt s₁.mem (W + BitVec.ofNat 64 512 + BitVec.ofNat 64 r) (16 - r) :=
      bytesAt_frame (writeBytes_frame' _ hcl) (fun q hq => by
          simp only [List.mem_singleton] at hq; subst hq
          exact Offset.disjoint_base (W + BitVec.ofNat 64 512) (Nat.le_refl r) (by omega)) (by omega)
    rw [a₁, a₂, z₁]
  have bW : ∀ {d : Nat}, d + 16 ≤ 512 ∨ (544 ≤ d ∧ d + 16 ≤ 2560) →
      blockAt s₃.mem (W + BitVec.ofNat 64 d) = blockAt s.mem (W + BitVec.ofNat 64 d) :=
    fun h => blockAt_frame F₃ (kW h)
  have hY : blockAt s₃.mem (yA W) = blockAt s.mem (yA W) := by
    simp only [yA, add_ofNat_ofNat]; exact bW (.inl (by decide))
  have hb₀ : blockAt s₃.mem (W + BitVec.ofNat 64 512) = ofBytes (c ++ zeros (16 - r)) := by
    rw [blockAt, hG0]
  have hb₁ : blockAt s₃.mem (W + BitVec.ofNat 64 528) = ofBytes (lensBlock al n) := by
    rw [blockAt, hL₃]
  refine ⟨he₃.keep (fun g hg => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl <;> rw [g₅, o₄.gpr _ (by decide)]) (by rw [rd₅, o₄.rd]) (by rw [wr₅, o₄.wr]),
    by rw [rd₅, o₄.rd, rd₃, rd₂, rd₁], by rw [wr₅, o₄.wr, wr₃, wr₂, wr₁], ?_, ?_⟩
  · refine (F₃.sub fun q hq => ⟨q, List.mem_cons_of_mem _ hq, fun _ h => h⟩).trans ?_
    rw [← m₄]
    exact fW.sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · rw [tag₅, y₄, m₄, hY, bW (d := 1024) (.inr ⟨by decide, by decide⟩), hb₀, hb₁, hc']

/-! ## The tag -/

/-- `tagP ks` with a prepared key context: what `oneTag 112` does. -/
theorem tagP_ok (hF : ShortFacts) {ks : Prog isa} (hks : KsOk ks) : TagOk CtxMode.prepared (tagP ks) := by
  intro Ctx W SP L R D n N al H x s hx he hH hR hdat hlen hn16 htl hN hal hd hDW hCD X
  -- `H'` and `H'²`.
  have hX : Spec.Gcm.PreparedPowersRepr s.mem Ctx := X.ok
  have p0 := hX 0 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] at p0
  rw [show ctxH s.mem Ctx = H by rw [ctxH_eq, hH]] at p0
  unfold tagP
  refine WP.seq (WP.mono (Fast.finPowP_ok hF s he.r13 (in_off X.cov (show 272 + 16 ≤ 1024 by decide) (by decide))
    (in_off X.cov (show 256 + 16 ≤ 1024 by decide) (by decide)) p0.2 p0.1) fun s₁ ⟨x0, x1, h1, h2, o₁⟩ => ?_)
  have he₁ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ := he.keep (fun g hg => o₁.gpr _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> decide)) o₁.rd o₁.wr
  have m₁ := o₁.mem
  -- The keystream of `J₀` and of the counter block.
  refine WP.seq (WP.mono (hks s₁ he₁ (by rw [m₁]; exact hR.1) hR.2)
    fun s₂ ⟨k₀, k₁, fK, g₂, rd₂, wr₂, x₂⟩ => ?_)
  have he₂ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := he₁.keep (fun g hg => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> exact g₂ _ (by decide) (by decide) (by decide)) rd₂ wr₂
  rw [m₁] at k₀ fK
  -- `J₀` incremented.
  obtain ⟨s₃, run₃, j₃, fJ, gJ, rdJ, wrJ, xJ⟩ := incJ_ok s₂ he₂
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have he₃ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₃ := he₂.keep (fun g hg => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> exact gJ _ (by decide)) rdJ wrJ
  have F₃ : Frame [⟨W + BitVec.ofNat 64 1024, 64⟩, ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 12, 4⟩] s.mem s₃.mem :=
    (fK.sub fun q hq => ⟨q, by simp only [List.mem_singleton] at hq; simp [hq], fun _ h => h⟩).trans
      (fJ.sub fun q hq => ⟨q, by simp only [List.mem_singleton] at hq; simp [hq], fun _ h => h⟩)
  have e28 : W + BitVec.ofNat 64 16 + BitVec.ofNat 64 12 = W + BitVec.ofNat 64 28 := add_ofNat_ofNat W 16 12
  have rK : ∀ d, 32 ≤ d → d + 8 ≤ 1024 →
      s₃.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => F₃.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact Offset.disjoint W (.inl (by omega)) (by omega) (by decide)
      · rw [e28]; exact Offset.disjoint W (.inr (by omega)) (by omega) (by decide))
      (by decide)
  -- The test.
  refine WP.seq (WP.mono (finTest_ok (r := n) (by omega) s₃ he₃ (by rw [rK 208 (by decide) (by decide)]; exact hlen))
    fun s₄ ⟨z₄, g₄, m₄, rd₄, wr₄, x₄⟩ => ?_)
  have he₄ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₄ := he₃.keep (fun g hg => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> exact g₄ _ (by decide)) rd₄ wr₄
  have xx : ∀ q, q ≠ .xmm5 → q ≠ .xmm7 → q ≠ .xmm8 → q ≠ .xmm13 → s₄.xmm q = s₁.xmm q := fun q a b c d => by
    rw [x₄, xJ, x₂ q a b c d]
  have TP : TagPre Ctx W SP H al N n D s₄ :=
    { env := he₄
      x0 := by rw [xx _ (by decide) (by decide) (by decide) (by decide)]; exact x0
      x1 := by rw [xx _ (by decide) (by decide) (by decide) (by decide)]; exact x1
      h1 := by rw [xx _ (by decide) (by decide) (by decide) (by decide)]; exact h1
      h2 := by
        rw [xx .xmm3 (by decide) (by decide) (by decide) (by decide),
          xx .xmm6 (by decide) (by decide) (by decide) (by decide)]; exact h2
      alen := by rw [m₄, rK 184 (by decide) (by decide)]; exact hal
      tlen := by rw [m₄, rK 192 (by decide) (by decide)]; exact htl
      dat := by rw [m₄, rK 200 (by decide) (by decide)]; exact hdat
      len := by rw [m₄, rK 208 (by decide) (by decide)]; exact hlen
      r16 := by omega
      rd := by rw [rd₄, wr₄, rdJ, wrJ, rd₂, wr₂, o₁.rd, o₁.wr]; exact hd.rd
      dW := hDW }
  -- What both ends share.
  have F₄ : Frame [⟨W + BitVec.ofNat 64 1024, 64⟩, ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 12, 4⟩] s.mem s₄.mem := by
    rw [m₄]; exact F₃
  have hK₀ : blockAt s₄.mem (W + BitVec.ofNat 64 1024) = ciphOf s.mem Ctx R (blockAt s.mem (W + BitVec.ofNat 64 16)) := by
    rw [m₄, blockAt_frame fJ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact (L.st_w (a := 12) (n := 4) (d := 1024) (k := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm), k₀]
  -- The regions of the state that the code keeps.
  have dS : ∀ {a k : Nat}, a + k ≤ 80 → a + k ≤ 12 ∨ 16 ≤ a →
      ∀ q ∈ [(⟨W + BitVec.ofNat 64 1024, 64⟩ : Region), ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 12, 4⟩] ++
        [⟨W + BitVec.ofNat 64 112, 16⟩, ⟨W + BitVec.ofNat 64 512, 32⟩],
      (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 a, k⟩ : Region).Disjoint q := fun ha h q hq => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact L.st_w ha (.inr ⟨by decide, by decide⟩)
    · exact L.st_st (by omega) ha (by decide)
    · exact L.st_w ha (.inr ⟨by decide, by decide⟩)
    · exact L.st_w ha (.inr ⟨by decide, by decide⟩)
  have hY : Absorbed s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H x →
      blockAt s₄.mem (yA W) = ghash H (blocks x) := fun hab => by
    rw [blockAt_frame F₄ (fun q hq => dS (a := 16) (k := 16) (by decide) (.inr (by decide)) q (List.mem_append_left _ hq)),
      hab.1, Proof.Gcm.whole_of_mod hx, List.take_length]
  have hD₄ : bytesAt s₄.mem D n = bytesAt s.mem D n :=
    bytesAt_frame F₄ (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact hDW.sub_right (Lay.wSub (by decide))
      · rw [e28]; exact hDW.sub_right (Lay.wSub (by decide))) (by omega)
  -- Either end leaves the post.
  have fin : ∀ t : State, Env Ctx (W + BitVec.ofNat 64 16) W SP t → t.rd = s₄.rd → t.wr = s₄.wr →
      Frame [⟨W + BitVec.ofNat 64 112, 16⟩, ⟨W + BitVec.ofNat 64 512, 32⟩] s₄.mem t.mem →
      (Absorbed s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H x →
        bytesAt t.mem (W + BitVec.ofNat 64 112) 16 =
          toBytes (ghashFrom H (ghash H (blocks (x ++ bytesAt s.mem D n ++
              zeros (padLen (x ++ bytesAt s.mem D n).length))))
            [ofBytes (lensBlock al N)] ^^^ ciphOf s.mem Ctx R (blockAt s.mem (W + BitVec.ofNat 64 16)))) →
      Env Ctx (W + BitVec.ofNat 64 16) W SP t ∧
        Frame (⟨W + BitVec.ofNat 64 112, 16⟩ :: wFrame W SP) s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        blockAt t.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
          blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) ∧
        blockAt t.mem (W + BitVec.ofNat 64 16) = inc32 (blockAt s.mem (W + BitVec.ofNat 64 16)) ∧
        (Absorbed s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H x →
          bytesAt t.mem (W + BitVec.ofNat 64 112) 16 =
            toBytes (ghashFrom H (ghash H (blocks (x ++ bytesAt s.mem D n ++
                zeros (padLen (x ++ bytesAt s.mem D n).length))))
              [ofBytes (lensBlock al N)] ^^^ ciphOf s.mem Ctx R (blockAt s.mem (W + BitVec.ofNat 64 16)))) := by
    intro t et rdt wrt ft tt
    have rd' : t.rd = s.rd := by rw [rdt, rd₄, rdJ, rd₂, o₁.rd]
    have wr' : t.wr = s.wr := by rw [wrt, wr₄, wrJ, wr₂, o₁.wr]
    refine ⟨et, ?_, rd', wr', ?_, ?_, tt⟩
    · refine (F₄.sub fun q hq => ?_).trans (ft.sub fun q hq => ?_)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact ⟨⟨W + BitVec.ofNat 64 240, 2320⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
        · exact ⟨⟨W + BitVec.ofNat 64 16, 112⟩, by simp, Offset.sub_base _ (by decide)⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
        · exact ⟨⟨W + BitVec.ofNat 64 240, 2320⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · rw [blockAt_frame ft (fun q hq => dS (by decide) (.inr (by decide)) q (List.mem_append_right _ hq)),
        blockAt_frame F₄ (fun q hq => dS (by decide) (.inr (by decide)) q (List.mem_append_left _ hq))]
    · have e : ∀ q ∈ [(⟨W + BitVec.ofNat 64 112, 16⟩ : Region), ⟨W + BitVec.ofNat 64 512, 32⟩],
          (⟨W + BitVec.ofNat 64 16, 16⟩ : Region).Disjoint q := fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · simpa using L.st_w (a := 0) (n := 16) (d := 112) (k := 16) (by decide) (.inr ⟨by decide, by decide⟩)
        · simpa using L.st_w (a := 0) (n := 16) (d := 512) (k := 32) (by decide) (.inr ⟨by decide, by decide⟩)
      rw [blockAt_frame ft e, m₄, j₃,
        blockAt_frame fK (fun q hq => by
          simp only [List.mem_singleton] at hq; subst hq
          simpa using L.st_w (a := 0) (n := 16) (d := 1024) (k := 64) (by decide) (.inr ⟨by decide, by decide⟩))]
  refine WP.ite (decide (n = 0)) (eval_e z₄) (fun h0 => ?_) (fun h0 => ?_)
  · -- No bytes left.
    have h0' : n = 0 := of_decide_eq_true h0
    subst h0'
    refine WP.mono (openNoTail_ok TP) fun t ⟨het, rdt, wrt, ft, tagt⟩ => fin t het rdt wrt ft fun hab => ?_
    rw [bytesAt_toBytes', tagt, hY hab, hK₀, show bytesAt s.mem D 0 = [] from rfl, List.append_nil,
      Proof.Gcm.padLen_of_mod hx, show zeros 0 = [] from rfl, List.append_nil]
  · -- Bytes left.
    have h0' : n ≠ 0 := of_decide_eq_false h0
    refine WP.mono (openTail_ok TP h0') fun t ⟨het, rdt, wrt, ft, tagt⟩ => fin t het rdt wrt ft fun hab => ?_
    have hpl : padLen (x ++ bytesAt s.mem D n).length = 16 - n := by
      simp only [padLen, List.length_append, length_bytesAt]; omega
    have bs := Proof.Gcm.blocks_single (bs := bytesAt s.mem D n ++ zeros (16 - n))
      (by rw [List.length_append, length_bytesAt, Proof.Gcm.length_zeros]; omega)
    rw [bytesAt_toBytes', tagt, hY hab, hK₀, hD₄, hpl, List.append_assoc, Proof.Gcm.blocks_append hx, bs, ghash_snoc,
      ← Proof.Gcm.ghashFrom_append]
    rfl

end VG.Proof.AesGcm.X86_64.FastOpen
