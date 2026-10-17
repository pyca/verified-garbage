module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Wide
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Copy

/-!
# Deterministic ECDSA on AArch64: the digest in the frame

The digest's copy for the hash function of `P` (`Cfg.digG`, chosen by the
dispatch on its number): nine zero words at `G` (`zero9_ok`), and, at an
offset in them, the digest's first `m` bytes (`copyF_ok`). Unless `wide`,
`G` is the digest's leftmost `Q` bytes, or the digest after `Q - D` zero
bytes if it is shorter (`digN_ok`); if `wide` (P-521, whose scalars are longer
than any hash), `h` is the digest after `Q - D` zero bytes, and `G` the
digest after `Q - D - 1` zero bytes and before one (`digW_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64

variable {P : RfcHash} {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} {L : Lay dn E} {g : Reg → BitVec 64} {m₀ : Mem}

/-! ## Zero words, and copies into the frame -/

theorem zeroK_ok {u : State} (hwr : u.wr = [L.FR, L.LR, L.OUT, L.SCR]) (h15 : u.gpr .x15 = L.B + BitVec.ofNat 64 16)
    {o : Nat} (ho : o % 8 = 0) (ho' : o + 72 ≤ 480) :
    ∀ k ≤ 9, WP isa (.block ((List.range k).map fun j => .str .x .x11 .x15 (o + 8 * j))) u fun u' =>
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧ u'.gpr = u.gpr ∧
      Frame [⟨L.B + BitVec.ofNat 64 (16 + o), 72⟩] u.mem u'.mem ∧
      ∀ j < k, u'.mem.readW (L.B + BitVec.ofNat 64 (16 + (o + 8 * j))) 64 = u.gpr .x11
  | 0, _ => WP.of_runBlock ⟨u, rfl, rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | k + 1, hk => by
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (zeroK_ok hwr h15 ho ho' k (by omega)) fun u₁ ⟨hrd, hwr₁, hsp, hg, hf, hv⟩ => ?_
    refine WP.mono (str15_ok (u := u₁) (hwr₁.trans hwr) (by rw [hg, h15]) (t := .x11) (o := o + 8 * k) (by omega)
      (by omega)) fun u₂ ⟨hrd₂, hwr₂, hsp₂, hg₂, hm₂⟩ => ⟨hrd₂.trans hrd, hwr₂.trans hwr₁, hsp₂.trans hsp,
        hg₂.trans hg, hf.trans ?_, fun j hj => ?_⟩
    · rw [hm₂]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))
    · rw [hm₂]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
        exact hv j hj
      · rw [Mem.readW_writeW_self64, hg]

/-- Nine zero words at `sp + o`, from `x11 = 0`, in a region the code may write. -/
theorem zero9_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (h15 : u.gpr .x15 = L.B + BitVec.ofNat 64 16)
    (h11 : u.gpr .x11 = 0) {o : Nat} (ho : o % 8 = 0) (ho' : o + 72 ≤ 480)
    (hs : Safe L ⟨L.B + BitVec.ofNat 64 (16 + o), 72⟩) :
    WP isa (.block (Cfg.zero9 o)) u fun u' => Ctx L g m₀ u' ∧ u'.gpr = u.gpr ∧
      Frame [⟨L.B + BitVec.ofNat 64 (16 + o), 72⟩] u.mem u'.mem ∧
      ∀ k ≤ 72, Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (16 + o)) k = List.replicate k 0 := by
  have h := Ctx.of_keep (Q := fun u' => u'.gpr = u.gpr ∧ ∀ j < 9,
      u'.mem.readW (L.B + BitVec.ofNat 64 (16 + o) + BitVec.ofNat 64 (8 * j)) 64 = 0) hL hc
    (is := Cfg.zero9 o) (ws := [⟨L.B + BitVec.ofNat 64 (16 + o), 72⟩])
    (WP.mono (zeroK_ok hc.wr h15 ho ho' 9 (Nat.le_refl _)) fun u' ⟨hrd, hwr, _, hg, hf, hv⟩ =>
      ⟨hrd, hwr, hf, hg, fun j hj => by
        rw [Offset.add_add, Nat.add_assoc]; exact (hv j hj).trans h11⟩) (by rfl)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hs)
  refine WP.mono h fun u' ⟨hc', hf, hg, hv⟩ => ⟨hc', hg, hf, fun k hk => ?_⟩
  rw [bytesAt_take _ _ (k := 8 * 9) hk, bytesAt_of_readW (k := 9) _ _ 0 hv,
    show (List.range (8 * 9)).map (fun i => (0 : BitVec 64).extractLsb' (8 * (i % 8)) 8) = List.replicate 72 0 by
      decide, replicate_take _ _ _ hk]

/-- The `m` bytes at `x1` copied to `sp + o`, through `x12`. -/
theorem copyF_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (h15 : u.gpr .x15 = L.B + BitVec.ofNat 64 16)
    {S : Addr} (h1 : u.gpr .x1 = S) {o m : Nat} (ho : o < 4096) (h8 : 8 ≤ m) (hom : o + m ≤ 480)
    (hs : Safe L ⟨L.B + BitVec.ofNat 64 (16 + o), m⟩)
    (hr : ∀ j, j + 8 ≤ m → InRegions (u.rd ++ u.wr) (S + BitVec.ofNat 64 j) 8)
    (hsep : Region.Disjoint ⟨S, m⟩ ⟨L.B + BitVec.ofNat 64 (16 + o), m⟩) :
    WP isa (.block (.addImm .x .x12 .x15 o :: Cfg.copyBytes m .x1 .x12)) u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → r ≠ .x14 → u'.gpr r = u.gpr r) ∧
      Frame [⟨L.B + BitVec.ofNat 64 (16 + o), m⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (16 + o)) m = Spec.Sha256.bytesAt u.mem S m := by
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (addImm_ok hL hc (d := .x12) (src := .x15) (by decide) h15 (k := o) ho) fun u₁ h₁ => ?_
  rw [Offset.add_add] at h₁
  refine WP.mono_syms (copyBytes_ok (src := .x1) (dst := .x12) (S := S) (D := L.B + BitVec.ofNat 64 (16 + o))
    (Q := m) (by decide) (by decide) (by decide) hsep h8 (by omega) (by rw [h₁.keep _ (by decide), h1]) h₁.val
    (fun j hj => by rw [h₁.ctx.rd, h₁.ctx.wr, ← hc.rd, ← hc.wr]; exact hr j hj)
    (fun j hj => by rw [Offset.add_add]; exact h₁.ctx.inFrW (by omega) (by omega)))
    fun u₂ ⟨hrd, hwr, hsp, hg, hf, hb⟩ hsy => ?_
  rw [h₁.mem] at hf hb
  exact ⟨h₁.ctx.keep hL hrd hwr hsp (fun r hr _ => hg r (ne_cs hr (by decide)) (ne_cs hr (by decide))
      (ne_cs hr (by decide))) (h₁.mem ▸ hf) (hsy := hsy)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hs),
    fun r h11 h12 h13 h14 => (hg r h11 h13 h14).trans (h₁.keep r h12), hf, hb⟩

/-- Bytes inside a range of zeros. -/
theorem zeros_at {m : Mem} {q : Addr} {n : Nat} (h : ∀ k ≤ n, Spec.Sha256.bytesAt m q k = List.replicate k 0)
    {a b : Nat} (hab : a + b ≤ n) : Spec.Sha256.bytesAt m (q + BitVec.ofNat 64 a) b = List.replicate b 0 := by
  have e := h (a + b) hab
  rw [Proof.Hmac.Common.bytesAt_add, h a (by omega), ← List.replicate_append_replicate] at e
  exact List.append_cancel_left e

/-- Nine zero words at `sp + o`, then `m` bytes of the digest (at `x1`) after
the first `p`: the `p + m + k` bytes there are `p` zeros, the digest's first
`m` bytes, and `k` zeros. -/
theorem zcopy_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (h15 : u.gpr .x15 = L.B + BitVec.ofNat 64 16)
    (h1 : u.gpr .x1 = L.dg) {o p m : Nat} (ho8 : o % 8 = 0) (ho : o + 72 ≤ 480) (hpm : p + m ≤ 72) (h8 : 8 ≤ m)
    (hm : m ≤ dn) (hs : Safe L ⟨L.B + BitVec.ofNat 64 (16 + o), 72⟩) :
    WP isa (.block (Cfg.zcopy o p m)) u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → r ≠ .x14 → u'.gpr r = u.gpr r) ∧
      Frame [⟨L.B + BitVec.ofNat 64 (16 + o), 72⟩] u.mem u'.mem ∧
      ∀ k, p + m + k ≤ 72 → Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (16 + o)) (p + m + k) =
        List.replicate p 0 ++ Spec.Sha256.bytesAt u.mem L.dg m ++ List.replicate k 0 := by
  have nB := hL.nB
  rw [Cfg.zcopy, WP.block_append_iff, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movz_ok hL hc (d := .x11) (by decide) (n := 0) (by decide)) fun u₁ h₁ => ?_
  refine WP.mono (zero9_ok hL h₁.ctx (by rw [h₁.keep _ (by decide), h15]) h₁.val ho8 ho hs)
    fun u₂ ⟨hc₂, hg₂, hf₂, hz₂⟩ => ?_
  have hdg : ∀ (m' : Mem), Frame [⟨L.B + BitVec.ofNat 64 (16 + o), 72⟩] u.mem m' →
      Spec.Sha256.bytesAt m' L.dg m = Spec.Sha256.bytesAt u.mem L.dg m := fun m' hf =>
    bytesAt_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hL.stk_DG (by omega)).symm.sub_left (Region.sub_prefix hm)) (by have := hL.ng; omega)
  refine WP.mono (copyF_ok hL hc₂ (by rw [congrFun hg₂, h₁.keep _ (by decide), h15]) (S := L.dg)
    (by rw [congrFun hg₂, h₁.keep _ (by decide), h1]) (o := o + p) (m := m) (by omega) h8 (by omega)
    (hs.of_sub (Offset.sub _ (by omega) (by omega)))
    (fun j hj => hc₂.inDg (by omega) (by omega))
    ((hL.stk_DG (by omega)).symm.sub_left (Region.sub_prefix hm))) fun u₃ ⟨hc₃, hg₃, hf₃, hb₃⟩ => ?_
  rw [← Nat.add_assoc] at hf₃ hb₃
  have hf₃' : Frame [⟨L.B + BitVec.ofNat 64 (16 + o), 72⟩] u₂.mem u₃.mem :=
    hf₃.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega) (by omega)⟩
  have hf : Frame [⟨L.B + BitVec.ofNat 64 (16 + o), 72⟩] u.mem u₃.mem := (h₁.mem ▸ hf₂).trans hf₃'
  refine ⟨hc₃, fun r h11 h12 h13 h14 => by rw [hg₃ r h11 h12 h13 h14, congrFun hg₂, h₁.keep r h11], hf,
    fun k hk => ?_⟩
  have z₂ : ∀ a b, a + b ≤ 72 → Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 (16 + o) + BitVec.ofNat 64 a) b =
      List.replicate b 0 := fun a b h => zeros_at hz₂ h
  rw [Proof.Hmac.Common.bytesAt_add, Proof.Hmac.Common.bytesAt_add, Offset.add_add, Offset.add_add, hb₃,
    hdg _ (h₁.mem ▸ hf₂)]
  have o₁ : Spec.Sha256.bytesAt u₃.mem (L.B + BitVec.ofNat 64 (16 + o)) p = List.replicate p 0 := by
    rw [bytesAt_frame hf₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)]
    have := z₂ 0 p (by omega)
    rwa [add_ofNat_zero] at this
  have o₂ : Spec.Sha256.bytesAt u₃.mem (L.B + BitVec.ofNat 64 (16 + o + (p + m))) k = List.replicate k 0 := by
    rw [bytesAt_frame hf₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)]
    have := z₂ (p + m) k (by omega)
    rwa [Offset.add_add] at this
  rw [o₁, o₂]

/-- `x15 ← sp`. -/
theorem sp15_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) :
    WP isa (.block [.addSp .x15 0]) u (Upd L g m₀ u .x15 (L.B + BitVec.ofNat 64 16)) :=
  WP.mono (fr_ok hL hc (d := .x15) (by decide) (o := 0) (by decide)) fun _ h => h

/-! ## The digest's copy -/

/-- Unless `wide`: `G`, the digest's leftmost `Q` bytes, or the digest after
`Q - D` zero bytes. -/
theorem digN_ok (hA : P.R.wide = false) (hL : L.Ok) {D : Nat} (hdn : D ≤ dn) (hD : 20 ≤ D) {t : State}
    (hc : Ctx L g m₀ t) (h1 : t.gpr .x1 = L.dg) :
    WP isa (.block ((cfgOf P).digG D)) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨gA L, 72⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (gA L) P.Q =
        List.replicate (P.Q - min D P.Q) 0 ++ Spec.Sha256.bytesAt t.mem L.dg (min D P.Q) := by
  have hs := P.wsizes
  have hQ64 : P.Q ≤ 64 := by have := P.sizesA hA; rcases this.1 with h | ⟨_, h | h⟩ <;> omega
  have hw : (cfgOf P).wide = false := hA
  simp only [Cfg.digG, hw, Bool.false_eq_true, ite_false]
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (sp15_ok hL hc) fun u₁ h₁ => ?_
  refine WP.mono (zcopy_ok hL h₁.ctx h₁.val (by rw [h₁.keep _ (by decide), h1]) (o := fG) (p := P.Q - min D P.Q)
    (m := min D P.Q) (by decide) (by decide) (by omega) (by omega) (by omega)
    (safe_high L (by decide) (by decide))) fun u₂ ⟨hc₂, _, hf₂, hb₂⟩ => ?_
  simp only [fG, Nat.reduceAdd] at hf₂ hb₂
  have hb := hb₂ 0 (by omega)
  rw [show P.Q - min D P.Q + min D P.Q + 0 = P.Q by omega, List.replicate_zero, List.append_nil, h₁.mem] at hb
  exact ⟨hc₂, h₁.mem ▸ hf₂, hb⟩

/-- If `wide`: `h`, the digest after `Q - D` zero bytes, and `G`, the digest
after `Q - D - 1` zero bytes and before one. -/
theorem digW_ok (hW : P.R.wide = true) (hL : L.Ok) {D : Nat} (hdn : D ≤ dn) (hD : 20 ≤ D) (hD' : D ≤ 64)
    {t : State} (hc : Ctx L g m₀ t) (h1 : t.gpr .x1 = L.dg) :
    WP isa (.block ((cfgOf P).digG D)) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 144, 72⟩, ⟨gA L, 72⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 144) P.Q =
        List.replicate (P.Q - D) 0 ++ Spec.Sha256.bytesAt t.mem L.dg D ∧
      Spec.Sha256.bytesAt t'.mem (gA L) P.Q =
        List.replicate (P.Q - D - 1) 0 ++ Spec.Sha256.bytesAt t.mem L.dg D ++ [0] := by
  obtain ⟨-, hQ66⟩ := P.sizesW hW
  have hw : (cfgOf P).wide = true := hW
  have e : (cfgOf P).len = P.Q := rfl
  simp only [Cfg.digG, hw, ite_true, e]
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (sp15_ok hL hc) fun u₁ h₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (zcopy_ok hL h₁.ctx h₁.val (by rw [h₁.keep _ (by decide), h1]) (o := fH) (p := P.Q - D)
    (m := D) (by decide) (by decide) (by omega) (by omega) hdn (safe_low L (by decide)))
    fun u₂ ⟨hc₂, hg₂, hf₂, hb₂⟩ => ?_
  refine WP.mono (zcopy_ok hL hc₂ (by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide), h₁.val])
    (by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide), h₁.keep _ (by decide), h1]) (o := fG)
    (p := P.Q - D - 1) (m := D) (by decide) (by decide) (by omega) (by omega) hdn (safe_high L (by decide) (by decide)))
    fun u₃ ⟨hc₃, _, hf₃, hb₃⟩ => ?_
  have hdg : Spec.Sha256.bytesAt u₂.mem L.dg D = Spec.Sha256.bytesAt u₁.mem L.dg D :=
    bytesAt_frame hf₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hL.stk_DG (by decide)).symm.sub_left (Region.sub_prefix hdn)) (by have := hL.ng; omega)
  simp only [fG, fH, Nat.reduceAdd] at hf₂ hb₂ hf₃ hb₃
  have hh := hb₂ 0 (by omega)
  have hg := hb₃ 1 (by omega)
  rw [show P.Q - D + D + 0 = P.Q by omega, List.replicate_zero, List.append_nil, h₁.mem] at hh
  rw [show P.Q - D - 1 + D + 1 = P.Q by omega, hdg, h₁.mem] at hg
  refine ⟨hc₃, ?_, ?_, hg⟩
  · rw [← h₁.mem]
    exact (hf₂.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩).trans (hf₃.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩)
  · rw [bytesAt_frame hf₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)]
    exact hh

/-! ## The run's digest, and step a -/

/-- The layout's facts for `P`: its scalars, and its hash function's number and block size. -/
def CoreOk (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) : Prop :=
  L.q = P.Q ∧ HashOk P L

/-- The digest, its integer `e`, and `bits2octets` of it. -/
abbrev hBOf (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) : List Byte := Spec.Sha256.bytesAt m₀ L.dg P.H.D
abbrev eOf (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) : Nat := Spec.Ecdsa.hashToInt P.R.E.C (hBOf P L m₀)
abbrev hSpec (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) : List Byte :=
  Spec.Ecdsa.Rfc6979.bits2octets P.R.E.C (hBOf P L m₀)

/-- `core`'s digest `G` is the digest's integer. -/
def DgOk (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ m : Mem) : Prop :=
  Spec.Ecdsa.hashToInt P.R.E.C (Spec.Sha256.bytesAt m (gA L) P.Q) = eOf P L m₀

theorem Ctx.dBytes (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {n : Nat} (hn : n ≤ L.q) :
    Spec.Sha256.bytesAt t.mem L.d n = Spec.Sha256.bytesAt m₀ L.d n := by
  simp only [Spec.Sha256.bytesAt]
  exact List.map_congr_left fun i hi => hc.d_byte hL (by have := List.mem_range.mp hi; omega)

theorem Ctx.dgBytes (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {n : Nat} (hn : n ≤ dn) :
    Spec.Sha256.bytesAt t.mem L.dg n = Spec.Sha256.bytesAt m₀ L.dg n := by
  simp only [Spec.Sha256.bytesAt]
  exact List.map_congr_left fun i hi => hc.dg_byte hL (by have := List.mem_range.mp hi; omega)

/-- After step c: `h`, `V = 0x01…`, `K = 0x00…` and `core`'s digest. -/
structure QB (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) (u : State) : Prop where
  h : hOf P L u.mem = hSpec P L m₀
  k : kOf P L u.mem = List.replicate P.H.D 0
  v : vOf P L u.mem = List.replicate P.H.D 1
  dg : DgOk P L m₀ u.mem

theorem length_bytesAt (m : Mem) (p : Addr) (n : Nat) : (Spec.Sha256.bytesAt m p n).length = n := by
  simp [Spec.Sha256.bytesAt]

/-- The digest's pointer and the hash function's number. -/
theorem dsel_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (Cfg.digestPtr ++ Cfg.selLd)) t fun u => Ctx L g m₀ u ∧ u.mem = t.mem ∧
      u.gpr .x1 = L.dg ∧ u.gpr .x9 = BitVec.ofNat 64 L.sel :=
  upd_append (digestPtr_ok hL hc) (fun u hu => ldSel_ok hL hu (d := .x9) (by decide))
    fun _ hc' hm hv _ h1 => ⟨hc', hm, h1 (by decide), hv⟩

variable {L : Lay P.I.hashLen P.R.E}

/-- Unless `wide`: `G`'s integer is the digest's `e`. -/
theorem gN_val (hA : P.R.wide = false) :
    Spec.Weierstrass.ofBytes (List.replicate (P.Q - min P.H.D P.Q) 0 ++
      Spec.Sha256.bytesAt m₀ L.dg (min P.H.D P.Q)) = eOf P L m₀ := by
  have hB : Spec.Ecdsa.nBits P.R.E.C = 8 * P.Q := by
    have h₁ := (P.R.sizesA hA).2.1; have h₂ := (P.R.sizesA hA).2.2.1; show _ = 8 * P.R.E.C.len; omega
  rw [ofBytes_zeros]
  by_cases hQD : P.Q ≤ P.H.D
  · rw [Nat.min_eq_right hQD, eOf, hashToInt_takeQ hB (by rw [hBOf, length_bytesAt]; exact hQD), hBOf,
      ← bytesAt_take _ _ hQD]
  · rw [Nat.min_eq_left (by omega), eOf, Spec.Ecdsa.hashToInt]
    simp only [hBOf, length_bytesAt, show 8 * P.H.D ≤ Spec.Ecdsa.nBits P.R.E.C by omega, ite_true]

/-- `G`, `h`, `V = 0x01…` and `K = 0x00…` (steps a–c). -/
theorem start_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).start t fun t' => Ctx L g m₀ t' ∧ QB P L m₀ t' := by
  have nB := hL.nB
  have hs := P.sizes
  refine WP.seq (WP.mono (dsel_ok hL hc) fun u ⟨hcu, hmu, h1, h9⟩ => ?_)
  refine WP.seq (disp_wp P (by rw [h9, hk.2.1]) fun w hw => ?_)
  have hcw := hcu.writesOnly hL (by decide) hw
  have h1w : w.gpr .x1 = L.dg := by rw [Dispatch.AArch64.WritesOnly.gpr hw (by decide), h1]
  have hmw : w.mem = t.mem := (WritesOnly.mem' hw).trans hmu
  cases hW : P.R.wide
  · have hw' : (cfgOf P).wide = false := hW
    simp only [hw', Bool.false_eq_true, ite_false]
    obtain ⟨hQ, h8⟩ := P.sizesA hW
    have hQ64 : P.Q ≤ 64 := by rcases hQ with h | ⟨_, h | h⟩ <;> omega
    refine WP.mono (digN_ok hW hL (D := P.H.D) (Nat.le_refl _) (by omega) hcw h1w) fun u₁ ⟨hc₁, hf₁, hg₁⟩ => ?_
    rw [WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (fr_ok hL hc₁ (d := .x1) (by decide) (o := fG) (by decide)) fun u₂ h₂ => ?_
    refine WP.mono (reduce_ok (P := P) hW hL h₂.ctx (by rw [h₂.val]; rfl)) fun u₃ ⟨hc₃, hf₃, hh₃⟩ => ?_
    refine WP.mono (initKV_ok hL hc₃) fun u₄ ⟨hc₄, hf₄, hv₄, hk₄⟩ => ⟨hc₄, ?_, hk₄ _ (by anums), hv₄ _ (by anums), ?_⟩
    · have e : hOf P L u₄.mem = hOf P L u₃.mem := bytesAt_frame hf₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega) (by omega) (by omega))
        (by omega)
      rw [e, hOf, hh₃, h₂.mem, hg₁, hmw, hc.dgBytes hL (by show min P.H.D P.Q ≤ P.H.D; omega), gN_val hW]
      simp only [hSpec, Spec.Ecdsa.Rfc6979.bits2octets, Spec.Ecdsa.Rfc6979.int2octets, Spec.Ecdsa.Rfc6979.bits2int,
        rlenQ (show Spec.Ecdsa.nBits P.R.E.C = 8 * P.Q by
          have h₁ := (P.R.sizesA hW).2.1; have h₂ := (P.R.sizesA hW).2.2.1; show _ = 8 * P.R.E.C.len; omega)]
    · have eG : Spec.Sha256.bytesAt u₄.mem (gA L) P.Q = Spec.Sha256.bytesAt u₁.mem (gA L) P.Q := by
        rw [bytesAt_frame hf₄ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega) (by omega) (by omega))
            (by omega),
          bytesAt_frame hf₃ (fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl
            · exact Offset.disjoint _ (by omega) (by omega) (by omega)
            · exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega), h₂.mem]
      unfold DgOk
      have hB : Spec.Ecdsa.nBits P.R.E.C = 8 * P.Q := by
        have h₁ := (P.R.sizesA hW).2.1; have h₂ := (P.R.sizesA hW).2.2.1; show _ = 8 * P.R.E.C.len; omega
      rw [eG, hg₁, hmw, hc.dgBytes hL (by show min P.H.D P.Q ≤ P.H.D; omega), Spec.Ecdsa.hashToInt]
      simp only [List.length_append, List.length_replicate, length_bytesAt,
        show 8 * (P.Q - min P.H.D P.Q + min P.H.D P.Q) ≤ Spec.Ecdsa.nBits P.R.E.C by omega, ite_true]
      exact gN_val hW
  · have hw' : (cfgOf P).wide = true := hW
    simp only [hw', ite_true]
    obtain ⟨hw9, hQ66⟩ := P.sizesW hW
    have hN := (P.R.sizesW hW).2.2
    have hsh := sh7 hW
    refine WP.mono (digW_ok hW hL (D := P.H.D) (Nat.le_refl _) (by omega) (by omega) hcw h1w)
      fun u₁ ⟨hc₁, hf₁, hh₁, hg₁⟩ => ?_
    have h81 : 8 - (cfgOf P).sh = 1 := by show 8 - P.R.sh = 1; omega
    rw [h81]
    refine WP.seq (WP.mono (conv_ok (P := P) hL hW hc₁ (o := fG) (s := 1) (by decide) (by decide) (by decide)
      (by decide) (by decide)) fun u₂ ⟨hc₂, hf₂, hb₂⟩ => ?_)
    simp only [fG, Nat.reduceAdd] at hf₂ hb₂
    refine WP.mono (initKV_ok hL hc₂) fun u₃ ⟨hc₃, hf₃, hv₃, hk₃⟩ => ⟨hc₃, ?_, hk₃ _ (by anums), hv₃ _ (by anums), ?_⟩
    · have e : hOf P L u₃.mem = hOf P L u₁.mem := by
        rw [hOf, bytesAt_frame hf₃ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega) (by omega) (by omega))
            (by omega),
          bytesAt_frame hf₂ (fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl
            · exact hL.stk_scr (by omega) (by omega)
            · exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)]
      have hl := P.R.nBits_len
      rw [e, hOf, hh₁, hmw, hc.dgBytes hL (Nat.le_refl _), hSpec,
        bits2octets_short (R := P.Q) (by show _ ≤ 8 * P.R.E.C.len; omega) (by show 8 * P.R.E.C.len < _; omega)
          (by rw [hBOf, length_bytesAt]; omega) P.R.n_ne, hBOf, length_bytesAt]
    · -- `G`: the digest's integer shifted left by `sh` bits.
      have hg₃ : Spec.Sha256.bytesAt u₃.mem (gA L) P.Q = Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg P.H.D) * 2 ^ 7) := by
        rw [bytesAt_frame hf₃ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega) (by omega) (by omega))
            (by omega)]
        rw [show gA L = L.B + BitVec.ofNat 64 288 from rfl, hb₂, ← show gA L = L.B + BitVec.ofNat 64 288 from rfl,
          hg₁, hmw, hc.dgBytes hL (Nat.le_refl _), List.append_assoc, ofBytes_zeros,
          show [(0 : Byte)] = List.replicate 1 0 from rfl, ofBytes_append_zeros, Nat.shiftRight_eq_div_pow,
          show 2 ^ (8 * 1) = 2 ^ 7 * 2 ^ 1 from rfl, ← Nat.mul_assoc, Nat.mul_div_cancel _ (by decide)]
      have hlt : Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg P.H.D) * 2 ^ 7 < 2 ^ (8 * P.Q) := by
        have := ofBytes_lt (Spec.Sha256.bytesAt m₀ L.dg P.H.D)
        rw [length_bytesAt] at this
        calc _ < 2 ^ (8 * P.H.D) * 2 ^ 7 := Nat.mul_lt_mul_of_pos_right this (Nat.two_pow_pos _)
          _ ≤ 2 ^ (8 * P.Q) := by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by omega) (by omega)
      have hl₁ : (Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg P.H.D) * 2 ^ 7)).length = P.Q := by
        simp [Spec.Weierstrass.toBytes]
      have hl := P.R.nBits_len
      unfold DgOk
      rw [hg₃, hashToInt_takeR (R := P.Q) (by show _ ≤ 8 * P.R.E.C.len; omega) (by rw [hl₁]),
        List.take_of_length_le (by rw [hl₁]), ofBytes_toBytes _ _ hlt,
        show 8 * P.Q - Spec.Ecdsa.nBits P.R.E.C = 7 by show 8 * P.R.E.C.len - _ = 7; omega,
        Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
      exact ((hashToInt_short (C := P.R.E.C) (h := Spec.Sha256.bytesAt m₀ L.dg P.H.D)
        (by rw [length_bytesAt]; omega) P.R.n_ne).1).symm

end VG.Proof.Ecdsa.Rfc6979.AArch64
