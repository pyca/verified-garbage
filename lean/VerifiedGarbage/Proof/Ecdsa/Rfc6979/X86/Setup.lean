module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Blocks
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Reduce
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Wide
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.X25519.X86.Column
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# Deterministic ECDSA on x86 (32-bit): what depends on the hash function

The case of the dispatch on `hash` that runs (`setup_ok`, by `calls_wp`):
the hash function's sizes stored in the frame (`stores_ok`), which makes
`Ctx` hold, and the digest for `core`, `X`, from the digest (`digestX_ok`):
its leftmost `Q` bytes, or, if the digest is shorter, after `Q - D` zero
bytes, whose number is in both cases `bits2int` of the digest (`XOk`); for
P-521 (`wide`), `h` (the digest after `Q - D` zero bytes) and `X` the digest
after `Q - D - 1` zero bytes and before one. Then `prep_ok`: `h = X mod n`
(`reduce_ok`), or, for P-521, `X` shifted right by one bit (`conv_ok`), the
digest's number shifted left by `sh` bits; and `K` and `V`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Ecdsa.Rfc6979.X86
open VG.Impl.Pbkdf2.Stream.X86 (at_)

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

/-! ## The sizes -/

theorem stores_ok (hL : L.Ok) {u : State} (hc : Ctx0 L g m₀ u) (v : Nat → Nat) : ∀ k ≤ 8,
    WP isa (.block ((List.range k).flatMap fun i =>
      [.mov .eax (.imm (BitVec.ofNat 32 (v i))), .store (stk (128 + 4 * i)) .eax])) u fun u' =>
      Ctx0 L g m₀ u' ∧ (∀ r, r ≠ .eax → u'.gpr r = u.gpr r) ∧
      Frame [⟨L.B + BitVec.ofNat 64 204, 32⟩] u.mem u'.mem ∧
      ∀ j < k, u'.mem.readW (L.B + BitVec.ofNat 64 (204 + 4 * j)) 32 = BitVec.ofNat 32 (v j)
  | 0, _ => by
    simp only [List.range_zero, List.flatMap_nil]
    exact WP.block_nil ⟨hc, fun _ _ => rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | k + 1, hk => by
    have nB := hL.nB
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (stores_ok hL hc v k (by omega_arith)) fun u₁ ⟨hc₁, hg₁, hf₁, hv₁⟩ => ?_
    have e : addr L.F (128 + 4 * k) = L.B + BitVec.ofNat 64 (204 + 4 * k) := by
      rw [hL.addrF (by omega_arith)]; congr 2; omega_arith
    refine wp_movi fun u₂ v₂ => wp_stm (B := L.F) (by rw [v₂.other _ (by decide), hc₁.esp])
      (by rw [e, v₂.wr]; exact hc₁.inFrW (by omega_arith) (by omega_arith) hL) fun u₃ v₃ => WP.block_nil ?_
    rw [e, v₂.gpr] at v₃
    have hm₃ : u₃.mem = u₁.mem.writeW (L.B + BitVec.ofNat 64 (204 + 4 * k)) (BitVec.ofNat 32 (v k)) := by
      rw [v₃.mem, v₂.mem]
    have hf₃ : Frame [⟨L.B + BitVec.ofNat 64 204, 32⟩] u₁.mem u₃.mem := by
      rw [hm₃]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))
    refine ⟨hc₁.keepP hL (by rw [v₃.rd, v₂.rd]) (by rw [v₃.wr, v₂.wr])
        (by rw [v₃.gpr, v₂.other _ (by decide)]) hf₃ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact sub_refl _) (by rw [v₃.syms, v₂.syms]),
      fun r hr => by rw [v₃.gpr, v₂.other _ hr, hg₁ r hr], hf₁.trans hf₃, fun j hj => ?_⟩
    rw [hm₃]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
      exact hv₁ j hj
    · rw [Mem.readW_writeW_self32]

/-- The value of size `i`, as `Cfg.sizes` lists them. -/
def sizeVal (P : RfcHash) (i : Nat) : Nat :=
  [P.F.H.D, P.F.H.B, P.F.H.D + 1, P.F.H.D + 1 + 2 * P.Q, P.F.H.B + P.F.H.D, P.F.H.B + P.F.H.D + 1,
    P.F.H.B + P.F.H.D + 1 + 2 * P.Q, P.nb].getD i 0

theorem storeSizes_eq (P : RfcHash) :
    (cfgOf P).storeSizes P.F = (List.range 8).flatMap fun i =>
      [.mov .eax (.imm (BitVec.ofNat 32 (sizeVal P i))), .store (stk (128 + 4 * i)) .eax] := rfl

theorem pv_sizeVal {L : Lay P.I.hashLen} (hk : Fits P L) : ∀ j < 8, BitVec.ofNat 32 (sizeVal P j) = L.pv j := by
  intro j hj
  have hq := hk.q; have hb := hk.bk; have hn := hk.nb
  match j, hj with
  | 0, _ => rfl
  | 1, _ => simp [sizeVal, Lay.pv, hb]
  | 2, _ => rfl
  | 3, _ => simp [sizeVal, Lay.pv, hq]
  | 4, _ => simp [sizeVal, Lay.pv, hb]
  | 5, _ => simp [sizeVal, Lay.pv, hb]
  | 6, _ => simp [sizeVal, Lay.pv, hb, hq]
  | 7, _ => simp [sizeVal, Lay.pv, hn]

/-! ## `X` -/

/-- 17 zero words at `esp + o`, in the frame's top words. -/
theorem zeros_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {o : Nat} (ho₁ : 196 ≤ o) (ho₂ : o + 68 ≤ 460) :
    WP isa (.block (zeroN 17 o)) u fun u' => Ctx L g m₀ u' ∧ (∀ r, r ≠ .eax → u'.gpr r = u.gpr r) ∧
      Frame [⟨L.B + BitVec.ofNat 64 (76 + o), 68⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (76 + o)) 68 = List.replicate 68 0 := by
  have nB := hL.nB
  refine wp_movi fun u₁ v₁ => ?_
  have hc₁ : Ctx L g m₀ u₁ := (Upd.of_wp hL hc (by decide) v₁).ctx
  -- The words, one at a time.
  have step : ∀ k ≤ 17, WP isa (.block ((List.range k).map fun j => .store (stk (o + 4 * j)) .eax)) u₁
      fun u' => u'.rd = u₁.rd ∧ u'.wr = u₁.wr ∧ u'.gpr = u₁.gpr ∧ u'.syms = u₁.syms ∧
        Frame [⟨L.B + BitVec.ofNat 64 (76 + o), 68⟩] u₁.mem u'.mem ∧
        ∀ j < k, u'.mem.readW (L.B + BitVec.ofNat 64 (76 + o + 4 * j)) 32 = 0 := by
    intro k hk
    induction k with
    | zero => exact WP.block_nil ⟨rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
    | succ k ih =>
      rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
      refine WP.mono (ih (by omega_arith)) fun u₂ ⟨hrd, hwr, hg, hsy, hf, hz⟩ => ?_
      have e : addr L.F (o + 4 * k) = L.B + BitVec.ofNat 64 (76 + o + 4 * k) := by
        rw [hL.addrF (by omega_arith)]; congr 2; omega_arith
      refine wp_stm (B := L.F) (by rw [hg, hc₁.esp]) (by rw [e, hwr]; exact hc₁.inFrW (by omega_arith) (by omega_arith) hL)
        fun u₃ v₃ => WP.block_nil ⟨by rw [v₃.rd, hrd], by rw [v₃.wr, hwr], by rw [v₃.gpr, hg], by rw [v₃.syms, hsy],
          hf.trans ?_, fun j hj => ?_⟩
      · rw [v₃.mem, e]
        exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
          (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))
      · rw [v₃.mem, e, hg, v₁.gpr]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
          exact hz j hj
        · rw [Mem.readW_writeW_self32]
  refine WP.mono (step 17 (Nat.le_refl _)) fun u' ⟨hrd, hwr, hg, hsy, hf, hz⟩ => ⟨?_, fun r hr => ?_, ?_, ?_⟩
  · exact hc₁.keep (hsy := hsy) hL hrd hwr (by rw [hg]) hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact safe_high L (by omega_arith) (by omega_arith))
  · rw [hg, v₁.other _ hr]
  · rw [← v₁.mem]; exact hf
  · rw [show (68 : Nat) = 4 * 17 from rfl, bytesAt_of_readW _ _ 0 fun j hj => by rw [Offset.add_add]; exact hz j hj]
    decide

/-- What `X` holds: unless `wide`, a number that is `bits2int` of the
digest; if `wide`, `h` and `X` as the digest after zero bytes. -/
def XOk (P : RfcHash) {dn : Nat} (L : Lay dn) (m₀ m : Mem) : Prop :=
  if P.R.wide then
    hOf P L m = List.replicate (P.Q - P.F.H.D) 0 ++ Spec.Sha256.bytesAt m₀ L.dg P.F.H.D ∧
      Spec.Sha256.bytesAt m (xA L) P.Q = List.replicate (P.Q - P.F.H.D - 1) 0 ++ Spec.Sha256.bytesAt m₀ L.dg P.F.H.D ++ [0]
  else Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m (xA L) P.Q) =
    Spec.Ecdsa.hashToInt P.R.E.C (Spec.Sha256.bytesAt m₀ L.dg P.F.H.D)

theorem Ctx0.dgBytes0 (hL : L.Ok) {t : State} (hc : Ctx0 L g m₀ t) {n : Nat} (hn : n ≤ dn) :
    Spec.Sha256.bytesAt t.mem L.dg n = Spec.Sha256.bytesAt m₀ L.dg n := by
  simp only [Spec.Sha256.bytesAt]
  exact List.map_congr_left fun i hi => hc.dg_byte hL (by have := List.mem_range.mp hi; omega)

/-- The digest's `D` bytes (`esi`) copied to `esp + o + z`, after 68 zero
bytes at `esp + o`. -/
theorem zcopy_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (hsi : u.gpr .esi = L.a2) {o z D : Nat}
    (ho₁ : 196 ≤ o) (ho₂ : o + 68 ≤ 460) (hz : z + D ≤ 68) (hD4 : D % 4 = 0) (hD : D ≤ dn) :
    WP isa (.block (zeroN 17 o ++ copyN (D / 4) .esi 0 .esp (o + z))) u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .eax → u'.gpr r = u.gpr r) ∧ Frame [⟨L.B + BitVec.ofNat 64 (76 + o), 68⟩] u.mem u'.mem ∧
      ∀ r, z + D + r ≤ 68 → Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (76 + o)) (z + D + r) =
        List.replicate z 0 ++ Spec.Sha256.bytesAt m₀ L.dg D ++ List.replicate r 0 := by
  have nB := hL.nB
  have ng := hL.ng
  have e4 : 4 * (D / 4) = D := by omega_arith
  rw [WP.block_append_iff]
  refine WP.mono (zeros_ok hL hc ho₁ ho₂) fun u₁ ⟨hc₁, hg₁, hf₁, hz₁⟩ => ?_
  have hdg₁ : Spec.Sha256.bytesAt u₁.mem L.dg D = Spec.Sha256.bytesAt m₀ L.dg D :=
    hc₁.toCtx0.dgBytes0 hL hD
  refine WP.mono (copyF_ok hL hc₁ (src := .esi) (S := L.a2) (SA := L.dg) ((hg₁ _ (by decide)).trans hsi)
    (by decide) (so := 0) (d := o + z) (K := D / 4) (by omega_arith) (by omega_arith)
    (fun j hj => by rw [Nat.zero_add]; exact addr_eq (by omega_arith))
    (fun j hj => hc₁.inDg (by omega_arith) (by omega_arith))
    ((hL.kg.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Region.sub_prefix (by omega_arith))).symm)
    fun u₂ ⟨hc₂, hg₂, hf₂, hb₂⟩ => ?_
  rw [e4] at hf₂ hb₂
  refine ⟨hc₂, fun r hr => by rw [hg₂ r hr, hg₁ r hr], hf₁.trans (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
    simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega_arith) (by omega_arith)⟩), fun r hr => ?_⟩
  -- The zeros before, the digest, the zeros after.
  have zs : ∀ a n, a + n ≤ 68 → Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 (76 + o + a)) n =
      List.replicate n 0 := fun a n h => by
    have := hz₁
    rw [show (68 : Nat) = a + (n + (68 - a - n)) by omega_arith, Proof.Hmac.Common.bytesAt_add,
      Proof.Hmac.Common.bytesAt_add, ← List.replicate_append_replicate, ← List.replicate_append_replicate,
      Offset.add_add, Offset.add_add] at this
    exact (List.append_inj (List.append_inj this (by simp [Spec.Sha256.bytesAt])).2.symm
      (by simp [Spec.Sha256.bytesAt])).1.symm
  rw [Proof.Hmac.Common.bytesAt_add, Proof.Hmac.Common.bytesAt_add, Offset.add_add, Offset.add_add,
    show 76 + o + z = 76 + (o + z) by omega_arith, hb₂, hdg₁]
  congr 1
  · congr 1
    rw [bytesAt_frame hf₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by omega_arith)]
    have := zs 0 z (by omega_arith)
    rwa [Nat.add_zero] at this
  · rw [bytesAt_frame hf₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by omega_arith)]
    exact zs _ _ (by omega_arith)

theorem length_bytesAt (m : Mem) (p : Addr) (n : Nat) : (Spec.Sha256.bytesAt m p n).length = n := by
  simp [Spec.Sha256.bytesAt]

/-- The digest for `core` (and, if `wide`, `h`), from the digest at `esi`. -/
theorem digestX_ok {L : Lay P.I.hashLen} (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (hsi : u.gpr .esi = L.a2) :
    WP isa (.block ((cfgOf P).digestX P.F.H.D)) u fun u' => Ctx L g m₀ u' ∧
      Frame [⟨L.B + BitVec.ofNat 64 272, 136⟩] u.mem u'.mem ∧ XOk P L m₀ u'.mem := by
  have hs := P.sizes
  have nB := hL.nB
  have ng := hL.ng
  have hl := P.R.nBits_len
  have hD4 : P.F.H.D % 4 = 0 := hs.2.2.2.2.2.2.1
  have hlen : P.I.hashLen = P.F.H.D := rfl
  have hQe : (cfgOf P).len = P.Q := rfl
  have hshe : (cfgOf P).sh = P.R.sh := rfl
  have sub : ∀ o, 272 ≤ 76 + o → 76 + o + 68 ≤ 408 →
      Region.Sub ⟨L.B + BitVec.ofNat 64 (76 + o), 68⟩ ⟨L.B + BitVec.ofNat 64 272, 136⟩ := fun o h₁ h₂ =>
    Offset.sub _ (by omega_arith) (by omega_arith)
  by_cases hQD : P.Q ≤ P.F.H.D
  · have hA : P.R.wide = false := by
      cases hW : P.R.wide
      · rfl
      · have := (P.sizesW hW).2.1; omega
    obtain ⟨hQ4, -⟩ := P.sizesA hA
    have hB : Spec.Ecdsa.nBits P.R.E.C = 8 * P.Q := by
      have := P.sh0 hA; show _ = 8 * P.R.E.C.len; omega
    simp only [Cfg.digestX, hQe, hQD, ite_true]
    refine WP.mono (copyF_ok hL hc (src := .esi) (S := L.a2) (SA := L.dg) hsi (by decide) (so := 0) (d := fX)
      (K := P.Q / 4) (by simp only [fX]; omega_arith) (by simp only [fX]; omega_arith)
      (fun j hj => by rw [Nat.zero_add]; exact addr_eq (by show _ < 2 ^ 32; omega_arith))
      (fun j hj => hc.inDg (by show _ ≤ P.F.H.D; omega_arith) (by omega_arith))
      ((hL.kg.sub_left (Offset.sub_base _ (by simp only [fX]; omega_arith))).sub_right
        (Region.sub_prefix (by show _ ≤ P.F.H.D; omega_arith))).symm)
      fun u' ⟨hc', _, hf', hb'⟩ => ⟨hc', hf'.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by simp only [fX]; omega_arith)
          (by simp only [fX]; omega_arith)⟩, ?_⟩
    simp only [XOk, hA, Bool.false_eq_true, ite_false, fX, show 4 * (P.Q / 4) = P.Q by omega,
      show 76 + 264 = 340 from rfl] at hb' ⊢
    rw [hb', hc.toCtx0.dgBytes0 hL (by show P.Q ≤ P.F.H.D; exact hQD),
      hashToInt_takeQ hB (by rw [length_bytesAt]; exact hQD), bytesAt_take _ _ hQD]
  · have hDQ : P.F.H.D < P.Q := Nat.lt_of_not_le hQD
    cases hW : P.R.wide
    · have h0 := P.sh0 hW
      have hQ64 := (P.sizesA hW)
      have hB : Spec.Ecdsa.nBits P.R.E.C = 8 * P.Q := by show _ = 8 * P.R.E.C.len; omega
      simp only [Cfg.digestX, hQe, hshe, hQD, h0, ite_true, ite_false,
        show fX + P.Q - P.F.H.D = fX + (P.Q - P.F.H.D) by omega]
      refine WP.mono (zcopy_ok hL hc hsi (o := fX) (z := P.Q - P.F.H.D) (D := P.F.H.D) (by simp only [fX]; omega)
        (by simp only [fX]; omega) (by omega) hD4 (Nat.le_refl _)) fun u' ⟨hc', _, hf', hb'⟩ =>
          ⟨hc', hf'.sub fun r hr => ⟨_, List.mem_singleton_self _, by
            simp only [List.mem_singleton] at hr; subst hr; exact sub _ (by simp only [fX]; omega)
              (by simp only [fX]; omega)⟩, ?_⟩
      have e := hb' 0 (by omega)
      rw [show P.Q - P.F.H.D + P.F.H.D + 0 = P.Q by omega, List.replicate_zero, List.append_nil] at e
      simp only [XOk, hW, Bool.false_eq_true, ite_false, xA]
      rw [show (340 : Nat) = 76 + fX from rfl, e, ofBytes_zeros,
        (hashToInt_short (h := Spec.Sha256.bytesAt m₀ L.dg P.F.H.D) (by rw [length_bytesAt, hB]; omega)
          P.R.n_ne).1]
    · obtain ⟨-, hQ66, h7⟩ := P.sizesW hW
      simp only [Cfg.digestX, hQe, hshe, hQD, h7, ite_false, show (7 : Nat) = 0 ↔ False by decide,
        show fH + P.Q - P.F.H.D = fH + (P.Q - P.F.H.D) by omega,
        show fX + P.Q - P.F.H.D - 1 = fX + (P.Q - P.F.H.D - 1) by omega, List.append_assoc]
      rw [← List.append_assoc, WP.block_append_iff]
      refine WP.mono (zcopy_ok hL hc hsi (o := fH) (z := P.Q - P.F.H.D) (D := P.F.H.D) (by simp only [fH]; omega)
        (by simp only [fH]; omega) (by omega) hD4 (Nat.le_refl _)) fun u₁ ⟨hc₁, hg₁, hf₁, hb₁⟩ => ?_
      refine WP.mono (zcopy_ok hL hc₁ ((hg₁ _ (by decide)).trans hsi) (o := fX) (z := P.Q - P.F.H.D - 1)
        (D := P.F.H.D) (by simp only [fX]; omega) (by simp only [fX]; omega) (by omega) hD4 (Nat.le_refl _))
        fun u₂ ⟨hc₂, _, hf₂, hb₂⟩ => ⟨hc₂, ?_, ?_⟩
      · refine (hf₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
          (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
        all_goals simp only [List.mem_singleton] at hr; subst hr; exact sub _ (by decide) (by decide)
      · have e₁ := hb₁ 0 (by omega)
        have e₂ := hb₂ 1 (by omega)
        rw [show P.Q - P.F.H.D + P.F.H.D + 0 = P.Q by omega, List.replicate_zero, List.append_nil] at e₁
        rw [show P.Q - P.F.H.D - 1 + P.F.H.D + 1 = P.Q by omega] at e₂
        simp only [XOk, hW, ite_true, xA, hOf]
        refine ⟨?_, by rw [show (340 : Nat) = 76 + fX from rfl, e₂]; rfl⟩
        rw [show (272 : Nat) = 76 + fH from rfl, bytesAt_frame hf₂ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by simp only [fH, fX]; omega) (by unfold fH; omega) (by unfold fX; omega)) (by omega), e₁]

/-! ## The case of the run's hash function -/

/-- The sizes, then `X`: `Ctx` holds. -/
theorem setupCase_ok {L : Lay P.I.hashLen} (hL : L.Ok) (hk : Fits P L) {u : State} (hc : Ctx0 L g m₀ u)
    (hsi : u.gpr .esi = L.a2) :
    WP isa (.block ((cfgOf P).storeSizes P.F ++ (cfgOf P).digestX P.F.H.D)) u fun u' => Ctx L g m₀ u' ∧
      Frame [⟨L.B + BitVec.ofNat 64 204, 32⟩, ⟨L.B + BitVec.ofNat 64 272, 136⟩] u.mem u'.mem ∧ XOk P L m₀ u'.mem := by
  rw [WP.block_append_iff, storeSizes_eq]
  refine WP.mono (stores_ok hL hc (sizeVal P) 8 (Nat.le_refl _)) fun u₁ ⟨hc₁, hg₁, hf₁, hv₁⟩ => ?_
  have hc₁' : Ctx L g m₀ u₁ := ⟨hc₁, fun i hi => by rw [hv₁ i hi, pv_sizeVal hk i hi]⟩
  refine WP.mono (digestX_ok hL hc₁' ((hg₁ _ (by decide)).trans hsi)) fun u₂ ⟨hc₂, hf₂, hx₂⟩ =>
    ⟨hc₂, (hf₁.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩).trans (hf₂.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩),
      hx₂⟩

/-- What depends on the hash function, through the dispatch on `hash` in `ebx`. -/
theorem setup_ok {L : Lay P.I.hashLen} (hL : L.Ok) (hk : Fits P L) {u : State} (hc : Ctx0 L g m₀ u)
    (hsi : u.gpr .esi = L.a2) (hbx : u.gpr .ebx = L.hs) :
    WP isa (cfgOf P).setup u fun u' => Ctx L g m₀ u' ∧
      Frame [⟨L.B + BitVec.ofNat 64 204, 32⟩, ⟨L.B + BitVec.ofNat 64 272, 136⟩] u.mem u'.mem ∧ XOk P L m₀ u'.mem :=
  calls_wp (mk := fun F => .block ((cfgOf P).storeSizes F ++ (cfgOf P).digestX F.H.D)) hk hbx fun u' hr =>
    WP.mono (setupCase_ok hL hk (hc.regs hL hr.rd hr.wr hr.mem (hr.gpr _) hr.syms) (by rw [hr.gpr]; exact hsi))
      fun u'' ⟨h₁, h₂, h₃⟩ => ⟨h₁, by rw [← hr.mem]; exact h₂, h₃⟩

/-! ## `h`, `X`, `K` and `V` -/

/-- After `prep`: `h = bits2octets(digest)`, `X`'s number is `bits2int` of
the digest, `K = 0x00…` and `V = 0x01…`. -/
structure Prepped (P : RfcHash) {dn : Nat} (L : Lay dn) (m₀ : Mem) (u : State) : Prop where
  h : hOf P L u.mem = Spec.Ecdsa.Rfc6979.bits2octets P.R.E.C (Spec.Sha256.bytesAt m₀ L.dg P.F.H.D)
  x : Spec.Ecdsa.hashToInt P.R.E.C (Spec.Sha256.bytesAt u.mem (xA L) P.Q) =
    Spec.Ecdsa.hashToInt P.R.E.C (Spec.Sha256.bytesAt m₀ L.dg P.F.H.D)
  k : ∀ n ≤ 64, Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 76) n = List.replicate n 0
  v : ∀ n ≤ 64, Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 140) n = List.replicate n 1

theorem prep_ok {L : Lay P.I.hashLen} (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u)
    (hx : XOk P L m₀ u.mem) :
    WP isa (cfgOf P).prep u fun u' => Ctx L g m₀ u' ∧
      Frame [⟨L.B + BitVec.ofNat 64 76, 128⟩, ⟨L.B + BitVec.ofNat 64 272, 136⟩, ⟨L.scr + BitVec.ofNat 64 2560, 72⟩]
        u.mem u'.mem ∧ Prepped P L m₀ u' := by
  have nB := hL.nB
  have hs := P.sizes
  have hl := P.R.nBits_len
  have hlen : P.I.hashLen = P.F.H.D := rfl
  cases hW : P.R.wide
  · have h0 := P.sh0 hW
    obtain ⟨hQ4, -⟩ := P.sizesA hW
    have hB : Spec.Ecdsa.nBits P.R.E.C = 8 * P.Q := by show _ = 8 * P.R.E.C.len; omega
    simp only [XOk, hW, Bool.false_eq_true, ite_false] at hx
    simp only [Cfg.prep, show (cfgOf P).sh = 0 from h0, ite_true]
    rw [WP.block_append_iff]
    refine WP.mono (reduce_ok (P := P) hW hL hc) fun u₁ ⟨hc₁, hf₁, hh₁⟩ => ?_
    refine WP.mono (initKV_ok hL hc₁) fun u₂ ⟨hc₂, hf₂, hv₂, hk₂⟩ => ⟨hc₂, ?_, ?_, ?_, hk₂, hv₂⟩
    · exact (hf₁.sub fun r hr => by
        simp only [HW, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, List.mem_cons_self, sub_refl _⟩
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (by omega)⟩).trans
        (hf₂.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩)
    · -- `h`: `X` modulo `n`, in `Q` bytes.
      have e₂ : hOf P L u₂.mem = hOf P L u₁.mem := bytesAt_frame hf₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)
      rw [← hQ4] at hh₁
      rw [e₂, Spec.Ecdsa.Rfc6979.bits2octets, Spec.Ecdsa.Rfc6979.int2octets, Spec.Ecdsa.Rfc6979.bits2int,
        rlenQ hB, ← hx, ← hh₁]
      have e := toBytes_ofBytes (hOf P L u₁.mem)
      rw [length_bytesAt] at e
      exact e.symm
    · -- `X`, kept.
      have e : Spec.Sha256.bytesAt u₂.mem (xA L) P.Q = Spec.Sha256.bytesAt u.mem (xA L) P.Q := by
        rw [bytesAt_frame hf₂ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega),
          bytesAt_frame hf₁ (fun r hr => by
            simp only [HW, List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)]
      rw [e, hashToInt_takeQ hB (by rw [length_bytesAt]), List.take_of_length_le (by rw [length_bytesAt]), hx]
  · obtain ⟨-, hQ66, h7⟩ := P.sizesW hW
    simp only [XOk, hW, ite_true] at hx
    simp only [Cfg.prep, show (cfgOf P).sh = 7 from h7, show (7 : Nat) = 0 ↔ False by decide, ite_false]
    refine WP.seq (WP.mono (arg_ok hL hc (d := .edi) (by decide) (i := 4) (by omega)) fun u₁ h₁ => ?_)
    rw [WP.block_append_iff]
    refine WP.mono (conv_ok hL hW h₁.ctx h₁.val (o := fX) (s := 8 - 7) (by decide) (by decide) (by decide)
      (by decide)) fun u₂ ⟨hc₂, _, hf₂, hb₂⟩ => ?_
    refine WP.mono (initKV_ok hL hc₂) fun u₃ ⟨hc₃, hf₃, hv₃, hk₃⟩ => ⟨hc₃, ?_, ?_, ?_, hk₃, hv₃⟩
    · rw [← h₁.mem]
      refine (hf₂.sub fun r hr => ?_).trans (hf₃.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, sub_refl _⟩
      · exact ⟨⟨L.B + BitVec.ofNat 64 272, 136⟩, by simp, Offset.sub _ (by simp only [fX]; omega)
          (by simp only [fX]; omega)⟩
    · -- `h`, kept.
      have e : hOf P L u₃.mem = hOf P L u.mem := by
        rw [hOf, bytesAt_frame hf₃ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega),
          bytesAt_frame hf₂ (fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl
            · exact hL.stk_scr (by omega) (by omega)
            · exact Offset.disjoint _ (by simp only [fX]; omega) (by omega) (by simp only [fX]; omega)) (by omega),
          h₁.mem]
      rw [e, hx.1, bits2octets_short (R := P.Q) (by show _ ≤ 8 * P.R.E.C.len; omega)
        (by show 8 * P.R.E.C.len < _; omega) (by rw [length_bytesAt, (P.R.sizesW hW).2.2]; have := hs.2.2.2.2.2.1; omega) P.R.n_ne, length_bytesAt]
    · -- `X`: the digest's number shifted left by `sh` bits.
      have e₃ : Spec.Sha256.bytesAt u₃.mem (xA L) P.Q = Spec.Sha256.bytesAt u₂.mem (xA L) P.Q :=
        bytesAt_frame hf₃ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)
      have hX : Spec.Sha256.bytesAt u₂.mem (xA L) P.Q = Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg P.F.H.D) * 2 ^ 7) := by
        have := hb₂
        simp only [fX, show 76 + 264 = 340 from rfl] at this
        rw [xA, this, h₁.mem, hx.2, List.append_assoc, ofBytes_zeros,
          show ([0] : List Byte) = List.replicate 1 0 from rfl, ofBytes_append_zeros]
        congr 1
        rw [Nat.shiftRight_eq_div_pow, show 8 * 1 = 1 + 7 from rfl, Nat.pow_add, ← Nat.mul_assoc,
          Nat.mul_comm _ (2 ^ 1), Nat.mul_assoc, Nat.mul_div_cancel_left _ (by decide)]
      have hlt : Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg P.F.H.D) * 2 ^ 7 < 2 ^ (8 * P.Q) := by
        have := ofBytes_lt (Spec.Sha256.bytesAt m₀ L.dg P.F.H.D)
        rw [length_bytesAt] at this
        calc _ < 2 ^ (8 * P.F.H.D) * 2 ^ 7 := Nat.mul_lt_mul_of_pos_right this (Nat.two_pow_pos _)
          _ ≤ 2 ^ (8 * P.Q) := by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by omega) (by nums)
      have hl₁ : (Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg P.F.H.D) * 2 ^ 7)).length = P.Q := by
        simp [Spec.Weierstrass.toBytes]
      rw [e₃, hX, hashToInt_takeR (R := P.Q) (by show _ ≤ 8 * P.R.E.C.len; omega) (by rw [hl₁]),
        List.take_of_length_le (by rw [hl₁]), ofBytes_toBytes _ _ hlt,
        show 8 * P.Q - Spec.Ecdsa.nBits P.R.E.C = 7 by rw [← h7]; exact hl.2.2.symm, Nat.shiftRight_eq_div_pow,
        Nat.mul_div_cancel _ (Nat.two_pow_pos _),
        (hashToInt_short (h := Spec.Sha256.bytesAt m₀ L.dg P.F.H.D) (by rw [length_bytesAt, (P.R.sizesW hW).2.2]; have := hs.2.2.2.2.2.1; omega) P.R.n_ne).1]

end VG.Proof.Ecdsa.Rfc6979.X86
