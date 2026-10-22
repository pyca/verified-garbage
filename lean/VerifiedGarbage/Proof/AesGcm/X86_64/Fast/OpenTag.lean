module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Open
import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.Tail
public import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.OpenTail
public import VerifiedGarbage.Impl.AesGcm.X86_64.FastOpen
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Finish
import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Seal
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith

/-!
# AES-GCM `open`'s path for TLS records: the tag

Untrusted: everything here is checked by Lean. `FastOpen.tagP` leaves what
`oneTag 112` does (`TagOk`, `oneTag_ok`), without calls: `H'` and `H'²` from
the prepared key context (`Fast.finPowP_ok`), the keystream of `J₀` and of the
counter block (`Short.finKs_ksOk`), the bytes left copied to `G[0]`
(`openTail_ok`, by `copyLoop`) or none (`openNoTail_ok`), `GHASH` continued
over `G`, the tag at `W + 112`, and `J₀` incremented (`incJ_ok`): `tagP_ok`.
It leaves `K[1]` too, the keystream of the counter block (`KOk`): `tagP_okP`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.FastOpen

variable {np : Nat} {hpn : 8 ≤ np ∧ np ≤ 24}

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

/-- After the blocks `GHASH` reads from memory are stored, from `s`: the
lengths block at `W + 528` and, with bytes left, them and zeros at
`W + 512`. -/
structure TagMid (Ctx W SP : Addr) (al n r : Nat) (D : Addr) (s t : State) : Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨W + BitVec.ofNat 64 512, 32⟩] s.mem t.mem
  xmm : ∀ q, q ≠ .xmm7 → t.xmm q = s.xmm q
  lens : blockAt t.mem (W + BitVec.ofNat 64 528) = ofBytes (lensBlock al n)
  tail : r ≠ 0 → blockAt t.mem (W + BitVec.ofNat 64 512) = ofBytes (bytesAt s.mem D r ++ zeros (16 - r))

/-- Without bytes left: the lengths block. -/
theorem prepNo_ok {Ctx W SP D : Addr} {H : Block} {al n r : Nat} {s : State} (P : TagPre Ctx W SP H al n r D s)
    (h0 : r = 0) : WP isa (.block finLens) s (TagMid Ctx W SP al n r D s) := by
  have he := P.env
  obtain ⟨s₃, run₃, f₃, hL₃, g₃, rd₃, wr₃, x₃⟩ := finLens_ok s he P.alen P.tlen
  refine WP.of_runBlock ⟨s₃, run₃, he.keep (fun g hg => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide)) rd₃ wr₃, rd₃, wr₃,
    f₃.sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩,
    fun q _ => by rw [x₃], by rw [blockAt, hL₃], fun h => absurd h0 h⟩

/-- With bytes left: they are copied to `G[0]`, padded with zeros, and the
lengths block. -/
theorem prepTail_ok {Ctx W SP D : Addr} {H : Block} {al n r : Nat} {s : State} (P : TagPre Ctx W SP H al n r D s)
    (h0 : r ≠ 0) :
    WP isa (.seq (.block finTextArgs) (.seq copyLoop (.block finLens))) s (TagMid Ctx W SP al n r D s) := by
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
  obtain ⟨s₃, run₃, f₃, hL₃, g₃, rd₃, wr₃, x₃⟩ := finLens_ok s₂ he₂ (by rw [rW₂ 184 (by decide)]; exact P.alen)
    (by rw [rW₂ 192 (by decide)]; exact P.tlen)
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have he₃ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₃ := he₂.keep (fun g hg => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide)) rd₃ wr₃
  have F₃ : Frame [⟨W + BitVec.ofNat 64 512, 32⟩] s.mem s₃.mem :=
    F₂.trans (f₃.sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩)
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
  exact ⟨he₃, by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁], F₃, fun q hq => by rw [x₃, x₂' q hq],
    by rw [blockAt, hL₃], fun _ => by rw [blockAt, hG0, hc']⟩

/-- Without bytes left: `GHASH` continued over the lengths block, and the tag
at `W + 112`. -/
theorem endNo_ok {Ctx W SP : Addr} {H : Block} {u : State} (he : Env Ctx (W + BitVec.ofNat 64 16) W SP u)
    (x0 : u.xmm .xmm0 = revMask) (x1 : u.xmm .xmm1 = poly) (h1 : IsH1 H (u.xmm .xmm3)) :
    WP isa (.block (finGh1 ++ tagK uO)) u fun t =>
      Env Ctx (W + BitVec.ofNat 64 16) W SP t ∧ t.rd = u.rd ∧ t.wr = u.wr ∧
      Frame [⟨W + BitVec.ofNat 64 112, 16⟩] u.mem t.mem ∧
      blockAt t.mem (W + BitVec.ofNat 64 112) =
        ghashFrom H (blockAt u.mem (yA W)) [blockAt u.mem (W + BitVec.ofNat 64 528)] ^^^
          blockAt u.mem (W + BitVec.ofNat 64 1024) := by
  rw [WP.block_append_iff]
  refine WP.mono (finGh1_ok u he (H := H) x0 x1 h1) fun s₄ ⟨y₄, o₄⟩ => ?_
  obtain ⟨s₅, run₅, tag₅, fW, g₅, rd₅, wr₅⟩ := tagK_ok (W := W) (o := 112) s₄
    ((o₄.gpr _ (by decide)).trans he.r15) (by rw [o₄.wr]; exact he.perm.w) (by decide)
    (by rw [o₄.xmm _ (by decide)]; exact x0)
  refine WP.of_runBlock ⟨s₅, run₅, he.keep (fun g hg => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl <;> rw [g₅, o₄.gpr _ (by decide)]) (by rw [rd₅, o₄.rd]) (by rw [wr₅, o₄.wr]),
    by rw [rd₅, o₄.rd], by rw [wr₅, o₄.wr], by rw [← o₄.mem]; exact fW, ?_⟩
  rw [tag₅, y₄, o₄.mem]

/-- With bytes left: `GHASH` continued over `G[0]` and the lengths block, and
the tag at `W + 112`. -/
theorem endTail_ok {Ctx W SP : Addr} {H : Block} {u : State} (he : Env Ctx (W + BitVec.ofNat 64 16) W SP u)
    (x0 : u.xmm .xmm0 = revMask) (x1 : u.xmm .xmm1 = poly) (h2 : IsH2 H (u.xmm .xmm3) (u.xmm .xmm6)) :
    WP isa (.block (finGh2 ++ tagK uO)) u fun t =>
      Env Ctx (W + BitVec.ofNat 64 16) W SP t ∧ t.rd = u.rd ∧ t.wr = u.wr ∧
      Frame [⟨W + BitVec.ofNat 64 112, 16⟩] u.mem t.mem ∧
      blockAt t.mem (W + BitVec.ofNat 64 112) =
        ghashFrom H (blockAt u.mem (yA W))
          [blockAt u.mem (W + BitVec.ofNat 64 512), blockAt u.mem (W + BitVec.ofNat 64 528)] ^^^
          blockAt u.mem (W + BitVec.ofNat 64 1024) := by
  rw [WP.block_append_iff]
  refine WP.mono (finGh2_ok u he (H := H) x0 x1 h2) fun s₄ ⟨y₄, o₄⟩ => ?_
  obtain ⟨s₅, run₅, tag₅, fW, g₅, rd₅, wr₅⟩ := tagK_ok (W := W) (o := 112) s₄
    ((o₄.gpr _ (by decide)).trans he.r15) (by rw [o₄.wr]; exact he.perm.w) (by decide)
    (by rw [o₄.xmm _ (by decide)]; exact x0)
  refine WP.of_runBlock ⟨s₅, run₅, he.keep (fun g hg => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl <;> rw [g₅, o₄.gpr _ (by decide)]) (by rw [rd₅, o₄.rd]) (by rw [wr₅, o₄.wr]),
    by rw [rd₅, o₄.rd], by rw [wr₅, o₄.wr], by rw [← o₄.mem]; exact fW, ?_⟩
  rw [tag₅, y₄, o₄.mem]

/-! ## The tag -/

/-- `tagP ks` with a prepared key context: what `oneTag 112` does, and `K[1]`
the keystream of the counter block. -/
theorem tagP_okP (hF : ShortFacts) {ks : Prog isa} (hks : KsOk ks) : TagOkP (CtxMode.preparedN np hpn) KOk (tagP ks) := by
  intro Ctx W SP L R D n N al H x s hx he hH hR hdat hlen hn16 htl hN hal hd hDW hCD X
  -- `H'` and `H'²`.
  have hX : VG.Proof.Gcm.X86_64.Stitch.PowersN np s.mem Ctx := X.ok
  have p0 := hX 0 (by have := hpn.1; omega)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] at p0
  rw [show ctxH s.mem Ctx = H by rw [ctxH_eq, hH]] at p0
  unfold tagP Impl.AesGcm.X86_64.FastOpen.lenTest
  refine WP.seq (WP.mono (Fast.finPowP_ok hF s he.r13 (in_off X.cov (show 272 + 16 ≤ 1024 by decide) (by exact (by decide : (1024 : Nat) < 2 ^ 64)))
    (in_off X.cov (show 256 + 16 ≤ 1024 by decide) (by exact (by decide : (1024 : Nat) < 2 ^ 64))) p0.2 p0.1) fun s₁ ⟨x0, x1, h1, h2, o₁⟩ => ?_)
  have he₁ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ := he.keep (fun g hg => o₁.gpr _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> decide)) o₁.rd o₁.wr
  have m₁ := o₁.mem
  -- The test.
  refine WP.seq (WP.mono (finTest_ok (r := n) (by omega) s₁ he₁ (by rw [m₁]; exact hlen))
    fun s₂ ⟨z₂, g₂, m₂, rd₂, wr₂, x₂⟩ => ?_)
  have he₂ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := he₁.keep (fun g hg => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> exact g₂ _ (by decide)) rd₂ wr₂
  have M₂ : s₂.mem = s.mem := by rw [m₂, m₁]
  have TP : TagPre Ctx W SP H al N n D s₂ :=
    { env := he₂
      x0 := by rw [x₂]; exact x0
      x1 := by rw [x₂]; exact x1
      h1 := by rw [x₂]; exact h1
      h2 := by rw [x₂]; exact h2
      alen := by rw [M₂]; exact hal
      tlen := by rw [M₂]; exact htl
      dat := by rw [M₂]; exact hdat
      len := by rw [M₂]; exact hlen
      r16 := by omega
      rd := by rw [rd₂, wr₂, o₁.rd, o₁.wr]; exact hd.rd
      dW := hDW }
  -- The blocks `GHASH` reads, stored before the keystream.
  refine WP.seq (WP.mono (Q := TagMid Ctx W SP al N n D s₂) (WP.ite (decide (n = 0)) (eval_e z₂)
    (fun h0 => prepNo_ok TP (of_decide_eq_true h0)) (fun h0 => prepTail_ok TP (of_decide_eq_false h0))) fun u U => ?_)
  have FU : Frame [⟨W + BitVec.ofNat 64 512, 32⟩] s.mem u.mem := by rw [← M₂]; exact U.frame
  have rU : ∀ d, d + 8 ≤ 512 → u.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d h => FU.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact Offset.disjoint W (.inl h) (by omega) (by decide))
      (by decide)
  -- The keystream of `J₀` and of the counter block.
  refine WP.seq (WP.mono (hks u U.env (by rw [rU 176 (by decide)]; exact hR.1) hR.2)
    fun s₃ ⟨k₀, k₁, fK, g₃, rd₃, wr₃, x₃⟩ => ?_)
  have he₃ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₃ := U.env.keep (fun g hg => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide) (by decide) (by decide)) rd₃ wr₃
  -- `J₀` incremented.
  obtain ⟨s₄, run₄, j₄, fJ, gJ, rdJ, wrJ, xJ⟩ := incJ_ok s₃ he₃
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  have he₄ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₄ := he₃.keep (fun g hg => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> exact gJ _ (by decide)) rdJ wrJ
  have e28 : W + BitVec.ofNat 64 16 + BitVec.ofNat 64 12 = W + BitVec.ofNat 64 28 := add_ofNat_ofNat W 16 12
  have FK : Frame [⟨W + BitVec.ofNat 64 1024, 64⟩, ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 12, 4⟩] u.mem s₄.mem :=
    (fK.sub fun q hq => ⟨q, by simp only [List.mem_singleton] at hq; simp [hq], fun _ h => h⟩).trans
      (fJ.sub fun q hq => ⟨q, by simp only [List.mem_singleton] at hq; simp [hq], fun _ h => h⟩)
  have rK : ∀ d, 32 ≤ d → d + 8 ≤ 512 →
      s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => by
      rw [← rU d h₂]
      exact FK.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact Offset.disjoint W (.inl (by omega)) (by omega) (by decide)
        · rw [e28]; exact Offset.disjoint W (.inr (by omega)) (by omega) (by decide))
        (by decide)
  -- The test again.
  refine WP.seq (WP.mono (finTest_ok (r := n) (by omega) s₄ he₄ (by rw [rK 208 (by decide) (by decide)]; exact hlen))
    fun s₅ ⟨z₅, g₅, m₅, rd₅, wr₅, x₅⟩ => ?_)
  have he₅ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₅ := he₄.keep (fun g hg => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> exact g₅ _ (by decide)) rd₅ wr₅
  have xx : ∀ q, q ≠ .xmm5 → q ≠ .xmm7 → q ≠ .xmm8 → q ≠ .xmm13 → s₅.xmm q = s₁.xmm q := fun q a b c d => by
    rw [x₅, xJ, x₃ q a b c d, U.xmm q b, x₂]
  -- The regions of the state and of `W` that the code writes.
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
  have F₅ : Frame ([⟨W + BitVec.ofNat 64 1024, 64⟩, ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 12, 4⟩] ++
      [⟨W + BitVec.ofNat 64 112, 16⟩, ⟨W + BitVec.ofNat 64 512, 32⟩]) s.mem s₅.mem := by
    rw [m₅]
    refine (FU.sub fun q hq => ?_).trans (FK.sub fun q hq => ?_)
    · simp only [List.mem_singleton] at hq; subst hq; exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨q, List.mem_append_left _ hq, fun _ h => h⟩
  -- The blocks `GHASH` reads, and the keystream of `J₀`, after the keystream.
  have bK : ∀ {d : Nat}, d = 512 ∨ d = 528 →
      blockAt s₅.mem (W + BitVec.ofNat 64 d) = blockAt u.mem (W + BitVec.ofNat 64 d) := fun h => by
    rw [m₅]
    refine blockAt_frame FK fun q hq => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact Offset.disjoint W (.inl (by omega)) (by omega) (by decide)
    · rw [e28]; exact Offset.disjoint W (.inr (by omega)) (by omega) (by omega)
  have hCtx : ciphOf u.mem Ctx R = ciphOf s.mem Ctx R := by
    simp only [ciphOf]
    rw [bytesAt_frame FU (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact L.cw'.sub_left (Region.sub_prefix (by rcases hR.2 with h | h | h <;> subst h <;> decide))
        |>.sub_right (Lay.wSub (by decide))) (by rcases hR.2 with h | h | h <;> subst h <;> decide)]
  have hK₀ : blockAt s₅.mem (W + BitVec.ofNat 64 1024) = ciphOf s.mem Ctx R (blockAt s.mem (W + BitVec.ofNat 64 16)) := by
    rw [m₅, blockAt_frame fJ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact (L.st_w (a := 12) (n := 4) (d := 1024) (k := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm), k₀,
      hCtx, blockAt_frame FU (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq
        simpa using L.st_w (a := 0) (n := 16) (d := 512) (k := 32) (by decide) (.inr ⟨by decide, by decide⟩))]
  have hY : Absorbed s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H x →
      blockAt s₅.mem (yA W) = ghash H (blocks x) := fun hab => by
    rw [blockAt_frame F₅ (fun q hq => dS (a := 16) (k := 16) (by decide) (.inr (by decide)) q hq),
      hab.1, Proof.Gcm.whole_of_mod hx, List.take_length]
  -- Either end leaves the post.
  have fin : ∀ t : State, Env Ctx (W + BitVec.ofNat 64 16) W SP t → t.rd = s₅.rd → t.wr = s₅.wr →
      Frame [⟨W + BitVec.ofNat 64 112, 16⟩] s₅.mem t.mem →
      (Absorbed s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H x →
        bytesAt t.mem (W + BitVec.ofNat 64 112) 16 =
          toBytes (ghashFrom H (ghash H (blocks (x ++ bytesAt s.mem D n ++
              zeros (padLen (x ++ bytesAt s.mem D n).length))))
            [ofBytes (lensBlock al N)] ^^^ ciphOf s.mem Ctx R (blockAt s.mem (W + BitVec.ofNat 64 16)))) →
      (Env Ctx (W + BitVec.ofNat 64 16) W SP t ∧
        Frame (⟨W + BitVec.ofNat 64 112, 16⟩ :: wFrame W SP) s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        blockAt t.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
          blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) ∧
        blockAt t.mem (W + BitVec.ofNat 64 16) = inc32 (blockAt s.mem (W + BitVec.ofNat 64 16)) ∧
        (Absorbed s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H x →
          bytesAt t.mem (W + BitVec.ofNat 64 112) 16 =
            toBytes (ghashFrom H (ghash H (blocks (x ++ bytesAt s.mem D n ++
                zeros (padLen (x ++ bytesAt s.mem D n).length))))
              [ofBytes (lensBlock al N)] ^^^ ciphOf s.mem Ctx R (blockAt s.mem (W + BitVec.ofNat 64 16))))) ∧
        KOk Ctx W R t := by
    intro t et rdt wrt ft tt
    have rd' : t.rd = s.rd := by rw [rdt, rd₅, rdJ, rd₃, U.rd, rd₂, o₁.rd]
    have wr' : t.wr = s.wr := by rw [wrt, wr₅, wrJ, wr₃, U.wr, wr₂, o₁.wr]
    have FT : Frame ([⟨W + BitVec.ofNat 64 1024, 64⟩, ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 12, 4⟩] ++
        [⟨W + BitVec.ofNat 64 112, 16⟩, ⟨W + BitVec.ofNat 64 512, 32⟩]) s.mem t.mem :=
      F₅.trans (ft.sub fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact ⟨_, by simp, fun _ h => h⟩)
    have cbT : blockAt t.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
        blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) :=
      blockAt_frame FT fun q hq => dS (by decide) (.inr (by decide)) q hq
    have e40 : W + BitVec.ofNat 64 1024 + BitVec.ofNat 64 16 = W + BitVec.ofNat 64 1040 := add_ofNat_ofNat W 1024 16
    have kT : KOk Ctx W R t := by
      unfold KOk
      have cU : blockAt u.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
          blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) :=
        blockAt_frame FU (fun q hq => by
          simp only [List.mem_singleton] at hq; subst hq
          exact L.st_w (a := 48) (n := 16) (d := 512) (k := 32) (by decide) (.inr ⟨by decide, by decide⟩))
      have kt : blockAt t.mem (W + BitVec.ofNat 64 1024 + BitVec.ofNat 64 16) =
          blockAt s₃.mem (W + BitVec.ofNat 64 1024 + BitVec.ofNat 64 16) := by
        rw [e40, blockAt_frame ft (fun q hq => by
            simp only [List.mem_singleton] at hq; subst hq
            exact Offset.disjoint W (.inr (by decide)) (by decide) (by decide)), m₅,
          blockAt_frame fJ (fun q hq => by
            simp only [List.mem_singleton] at hq; subst hq; rw [e28]
            exact Offset.disjoint W (.inr (by decide)) (by decide) (by decide))]
      have cT : ciphOf t.mem Ctx R = ciphOf s.mem Ctx R :=
        ciph_frame FT (fun q hq => by
          simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl | rfl | rfl
          · exact L.cw'.sub_right (Lay.wSub (by decide))
          · exact L.cs.sub_right (Lay.stSub (by decide))
          · exact L.cw'.sub_right (Lay.wSub (by decide))
          · exact L.cw'.sub_right (Lay.wSub (by decide))) hR.2
      rw [kt, k₁, hCtx, cU, cT, cbT]
    refine ⟨⟨et, ?_, rd', wr', ?_, ?_, tt⟩, kT⟩
    · refine FT.sub fun q hq => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact ⟨⟨W + BitVec.ofNat 64 240, 2320⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨⟨W + BitVec.ofNat 64 16, 112⟩, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · exact ⟨⟨W + BitVec.ofNat 64 240, 2320⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact cbT
    · have e : ∀ q ∈ [(⟨W + BitVec.ofNat 64 112, 16⟩ : Region)],
          (⟨W + BitVec.ofNat 64 16, 16⟩ : Region).Disjoint q := fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq
        simpa using L.st_w (a := 0) (n := 16) (d := 112) (k := 16) (by decide) (.inr ⟨by decide, by decide⟩)
      rw [blockAt_frame ft e, m₅, j₄,
        blockAt_frame fK (fun q hq => by
          simp only [List.mem_singleton] at hq; subst hq
          simpa using L.st_w (a := 0) (n := 16) (d := 1024) (k := 64) (by decide) (.inr ⟨by decide, by decide⟩)),
        blockAt_frame FU (fun q hq => by
          simp only [List.mem_singleton] at hq; subst hq
          simpa using L.st_w (a := 0) (n := 16) (d := 512) (k := 32) (by decide) (.inr ⟨by decide, by decide⟩))]
  have x0₅ : s₅.xmm .xmm0 = revMask := by rw [xx _ (by decide) (by decide) (by decide) (by decide)]; exact x0
  have x1₅ : s₅.xmm .xmm1 = poly := by rw [xx _ (by decide) (by decide) (by decide) (by decide)]; exact x1
  refine WP.ite (decide (n = 0)) (eval_e z₅) (fun h0 => ?_) (fun h0 => ?_)
  · -- No bytes left.
    have h0' : n = 0 := of_decide_eq_true h0
    subst h0'
    refine WP.mono (endNo_ok (H := H) he₅ x0₅ x1₅ (by rw [xx _ (by decide) (by decide) (by decide) (by decide)]; exact h1))
      fun t ⟨het, rdt, wrt, ft, tagt⟩ => fin t het rdt wrt ft fun hab => ?_
    rw [bytesAt_toBytes', tagt, hY hab, hK₀, bK (.inr rfl), U.lens, show bytesAt s.mem D 0 = [] from rfl,
      List.append_nil, Proof.Gcm.padLen_of_mod hx, show zeros 0 = [] from rfl, List.append_nil]
  · -- Bytes left.
    have h0' : n ≠ 0 := of_decide_eq_false h0
    refine WP.mono (endTail_ok (H := H) he₅ x0₅ x1₅ (by
        rw [xx .xmm3 (by decide) (by decide) (by decide) (by decide),
          xx .xmm6 (by decide) (by decide) (by decide) (by decide)]; exact h2))
      fun t ⟨het, rdt, wrt, ft, tagt⟩ => fin t het rdt wrt ft fun hab => ?_
    have hpl : padLen (x ++ bytesAt s.mem D n).length = 16 - n := by
      simp only [padLen, List.length_append, length_bytesAt]; omega
    have bs := Proof.Gcm.blocks_single (bs := bytesAt s.mem D n ++ zeros (16 - n))
      (by rw [List.length_append, length_bytesAt, Proof.Gcm.length_zeros]; omega)
    rw [bytesAt_toBytes', tagt, hY hab, hK₀, bK (.inl rfl), bK (.inr rfl), U.tail h0', U.lens, M₂, hpl,
      List.append_assoc, Proof.Gcm.blocks_append hx, bs, ghash_snoc, ← Proof.Gcm.ghashFrom_append]
    rfl

/-- `tagP ks` with a prepared key context: what `oneTag 112` does. -/
theorem tagP_ok (hF : ShortFacts) {ks : Prog isa} (hks : KsOk ks) : TagOk (CtxMode.preparedN np hpn) (tagP ks) :=
  TagOkP.tagOk (tagP_okP hF hks)

end VG.Proof.AesGcm.X86_64.FastOpen
