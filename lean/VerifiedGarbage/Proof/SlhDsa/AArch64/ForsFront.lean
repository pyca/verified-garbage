module

-- separate module: the indices block, which forsSign and forsPk share

public import VerifiedGarbage.Proof.SlhDsa.AArch64.TreeBase
public import VerifiedGarbage.Impl.SlhDsa.AArch64.Fors
public import VerifiedGarbage.Proof.SlhDsa.AArch64.TopShared
public import VerifiedGarbage.Proof.SlhDsa.AArch64.WotsBase
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA (SHAKE) on AArch64: FORS's indices

`index a t` (`Impl/SlhDsa/AArch64/Fors.lean`): index `t` of
`base_2b(md, a, k)`, from the three bytes of the digest from byte
`⌊t·a / 8⌋` (`x19 = S`), to `oFidx + 8t` (`index_ok`); and the block of all
`k` of them (`indices_ok`), which `forsSign` and `forsPk` share. The value is
`ixv`, which `Proof/SlhDsa/ForsSpec.lean`'s `index_eq` relates to `base_2b`.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.Fors

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.AArch64 (Layout)
open VG.Proof.SlhDsa.AArch64.TreeBase
open VG.Proof.MlKem.AArch64 (Only Keep MemTo)

/-- Three bytes, most significant first, shifted and masked. -/
theorem idx_val (x₀ x₁ x₂ : Byte) {sh a : Nat} (ha : a ≤ 14) :
    ((((x₀.setWidth 64 <<< 16) ||| (x₁.setWidth 64 <<< 8)) ||| x₂.setWidth 64) >>> sh) &&&
        (BitVec.ofNat 16 (2 ^ a - 1)).setWidth 64 =
      BitVec.ofNat 64 ((x₀.toNat * 65536 + x₁.toNat * 256 + x₂.toNat) / 2 ^ sh % 2 ^ a) := by
  have h₀ := x₀.isLt
  have h₁ := x₁.isLt
  have h₂ := x₂.isLt
  have hm : 2 ^ a - 1 < 2 ^ 16 := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) ha; omega
  have hw : (BitVec.ofNat 16 (2 ^ a - 1)).setWidth 64 = BitVec.ofNat 64 (2 ^ a - 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  rw [hw]
  apply BitVec.eq_of_toNat_eq
  have e : (x₀.toNat <<< 16 ||| x₁.toNat <<< 8) ||| x₂.toNat = x₀.toNat * 65536 + x₁.toNat * 256 + x₂.toNat := by
    rw [show 16 = 8 + 8 from rfl, Nat.shiftLeft_add, ← Nat.shiftLeft_or_distrib, ← Nat.shiftLeft_add_eq_or_of_lt h₁,
      ← Nat.shiftLeft_add_eq_or_of_lt h₂, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
    omega
  have b₀ : x₀.toNat <<< 16 < 2 ^ 64 := by rw [Nat.shiftLeft_eq]; omega
  have b₁ : x₁.toNat <<< 8 < 2 ^ 64 := by rw [Nat.shiftLeft_eq]; omega
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show x₀.toNat < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show x₁.toNat < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show x₂.toNat < 2 ^ 64 by omega), Nat.mod_eq_of_lt b₀, Nat.mod_eq_of_lt b₁, e,
    Nat.mod_eq_of_lt (show 2 ^ a - 1 < 2 ^ 64 by omega), Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt (show (x₀.toNat * 65536 + x₁.toNat * 256 + x₂.toNat) / 2 ^ sh % 2 ^ a < 2 ^ 64 by
      have := Nat.mod_lt ((x₀.toNat * 65536 + x₁.toNat * 256 + x₂.toNat) / 2 ^ sh) (Nat.two_pow_pos a)
      have : 2 ^ a ≤ 2 ^ 14 := Nat.pow_le_pow_right (by decide) ha
      omega)]

/-- The value of index `t` from the digest's bytes in `m`. -/
abbrev ixv (m : Mem) (S : Addr) (a t : Nat) : Nat :=
  ((m (at' S (Layout.oDigest + t * a / 8))).toNat * 65536 + (m (at' S (Layout.oDigest + t * a / 8 + 1))).toNat * 256 +
    (m (at' S (Layout.oDigest + t * a / 8 + 2))).toNat) / 2 ^ (24 - t * a % 8 - a) % 2 ^ a

/-- Index `t`: its value to `oFidx + 8t`; only `x9` and `x10` change. -/
theorem index_ok {S : Addr} {a t : Nat} {u : State} (ha : a ≤ 14) (ht : t * a / 8 + 3 ≤ 64) (ht' : t < 40)
    (h19 : u.gpr .x19 = S) (hw : (⟨S, 65536⟩ : Region) ∈ u.wr) :
    WP isa (.block (Impl.SlhDsa.AArch64.Fors.index a t)) u fun u' =>
      (∀ g, g ≠ .x9 → g ≠ .x10 → u'.gpr g = u.gpr g) ∧ u'.sp = u.sp ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧
      u'.v = u.v ∧ u'.mem.readW (at' S (Layout.oFidx + 8 * t)) 64 = BitVec.ofNat 64 (ixv u.mem S a t) ∧
      Frame [⟨at' S (Layout.oFidx + 8 * t), 8⟩] u.mem u'.mem := by
  have eD : Layout.oDigest = 1792 := rfl
  have eF : Layout.oFidx = 2048 := rfl
  have hq := Nat.mod_lt (t * a) (show 0 < 8 by decide)
  have h2a : 2 ^ a - 1 < 65536 := by have := Nat.pow_le_pow_right (show 0 < 2 by decide) ha; omega
  simp only [Impl.SlhDsa.AArch64.Fors.index]
  refine wp_ldrb (a := at' S (Layout.oDigest + t * a / 8)) (by rw [eD]; omega) (by rw [h19])
    (in_scr' hw (by rw [eD]; omega)) fun u₁ e₁ => wp_lsl (by decide) fun u₂ e₂ => ?_
  refine wp_ldrb (a := at' S (Layout.oDigest + t * a / 8 + 1)) (by rw [eD]; omega)
    (by rw [e₂.other _ (by decide), e₁.other _ (by decide), h19])
    (by rw [e₂.rd, e₂.wr, e₁.rd, e₁.wr]; exact in_scr' hw (by rw [eD]; omega)) fun u₃ e₃ => ?_
  refine wp_lsl (by decide) fun u₄ e₄ => wp_orr fun u₅ e₅ => ?_
  refine wp_ldrb (a := at' S (Layout.oDigest + t * a / 8 + 2)) (by rw [eD]; omega)
    (by rw [e₅.other _ (by decide), e₄.other _ (by decide), e₃.other _ (by decide), e₂.other _ (by decide),
      e₁.other _ (by decide), h19])
    (by rw [e₅.rd, e₅.wr, e₄.rd, e₄.wr, e₃.rd, e₃.wr, e₂.rd, e₂.wr, e₁.rd, e₁.wr]
        exact in_scr' hw (by rw [eD]; omega)) fun u₆ e₆ => ?_
  refine wp_orr fun u₇ e₇ => wp_lsr (by omega) fun u₈ e₈ => wp_movz fun u₉ e₉ => wp_and fun u₁₀ e₁₀ => ?_
  have h19₁₀ : u₁₀.gpr .x19 = S := by
    rw [e₁₀.other _ (by decide), e₉.other _ (by decide), e₈.other _ (by decide), e₇.other _ (by decide),
      e₆.other _ (by decide), e₅.other _ (by decide), e₄.other _ (by decide), e₃.other _ (by decide),
      e₂.other _ (by decide), e₁.other _ (by decide), h19]
  refine wp_str (a := at' S (Layout.oFidx + 8 * t)) (by rw [eF]; omega) (by rw [h19₁₀])
    (by rw [e₁₀.wr, e₉.wr, e₈.wr, e₇.wr, e₆.wr, e₅.wr, e₄.wr, e₃.wr, e₂.wr, e₁.wr]
        exact in_scr hw (by rw [eF]; omega)) fun u' m' => WP.block_nil ?_
  have hm : u₁₀.mem = u.mem := by
    rw [e₁₀.mem, e₉.mem, e₈.mem, e₇.mem, e₆.mem, e₅.mem, e₄.mem, e₃.mem, e₂.mem, e₁.mem]
  have hx9 : u₁₀.gpr .x9 = BitVec.ofNat 64 (ixv u.mem S a t) := by
    rw [e₁₀.gpr, e₉.gpr, e₉.other .x9 (by decide), e₈.gpr, e₇.gpr, e₆.other .x9 (by decide), e₆.gpr, e₅.gpr,
      e₄.other .x9 (by decide), e₄.gpr, e₃.gpr, e₃.other .x9 (by decide), e₂.gpr, e₁.gpr,
      e₅.mem, e₄.mem, e₃.mem, e₂.mem, e₁.mem, idx_val _ _ _ ha]
  refine ⟨fun g h₀ h₁ => by
      rw [m'.gpr, e₁₀.other _ h₀, e₉.other _ h₁, e₈.other _ h₀, e₇.other _ h₀, e₆.other _ h₁, e₅.other _ h₀,
        e₄.other _ h₁, e₃.other _ h₁, e₂.other _ h₀, e₁.other _ h₀],
    by rw [m'.sp, e₁₀.sp, e₉.sp, e₈.sp, e₇.sp, e₆.sp, e₅.sp, e₄.sp, e₃.sp, e₂.sp, e₁.sp],
    by rw [m'.rd, e₁₀.rd, e₉.rd, e₈.rd, e₇.rd, e₆.rd, e₅.rd, e₄.rd, e₃.rd, e₂.rd, e₁.rd],
    by rw [m'.wr, e₁₀.wr, e₉.wr, e₈.wr, e₇.wr, e₆.wr, e₅.wr, e₄.wr, e₃.wr, e₂.wr, e₁.wr],
    by rw [m'.v, e₁₀.v, e₉.v, e₈.v, e₇.v, e₆.v, e₅.v, e₄.v, e₃.v, e₂.v, e₁.v],
    by rw [m'.mem, Mem.readW_writeW_self64, hx9], ?_⟩
  rw [m'.mem, hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

/-- The blocks of a `flatMap` over `range K` followed by `is`, one at a time. -/
theorem wp_flatRange {f : Nat → List Instr} {P : Nat → State → Prop} {Q : State → Prop} :
    ∀ (K : Nat) {s : State} {is : List Instr}, P 0 s →
      (∀ j < K, ∀ t (is' : List Instr), P j t → (∀ t', P (j + 1) t' → WP isa (.block is') t' Q) →
        WP isa (.block (f j ++ is')) t Q) →
      (∀ t, P K t → WP isa (.block is) t Q) →
      WP isa (.block ((List.range K).flatMap f ++ is)) s Q
  | 0, _, _, h0, _, k => by simpa using k _ h0
  | K + 1, _, is, h0, hs, k => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    exact wp_flatRange K h0 (fun j hj => hs j (by omega)) fun t ht => hs K (by omega) t is ht k

/-- What the indices block leaves, from `u`. -/
structure IxPost (S : Addr) (a k : Nat) (u v : State) : Prop where
  gpr : ∀ g, g ≠ .x9 → g ≠ .x10 → v.gpr g = u.gpr g
  sp : v.sp = u.sp
  rd : v.rd = u.rd
  wr : v.wr = u.wr
  vr : v.v = u.v
  idx : ∀ i < k, v.mem.readW (at' S (Layout.oFidx + 8 * i)) 64 = BitVec.ofNat 64 (ixv u.mem S a i)
  frame : Frame [⟨at' S Layout.oFidx, 8 * k⟩] u.mem v.mem

/-- The block of the indices: all `k`. -/
theorem indices_ok {S : Addr} {a k : Nat} {u : State} {is : List Instr} {Q : State → Prop} (ha : a ≤ 14) (hk : k ≤ 40)
    (hka : k * a ≤ 8 * 61) (h19 : u.gpr .x19 = S) (hw : (⟨S, 65536⟩ : Region) ∈ u.wr)
    (K : ∀ v, IxPost S a k u v → WP isa (.block is) v Q) :
    WP isa (.block (Impl.SlhDsa.AArch64.Fors.indices a k ++ is)) u Q := by
  have eF : Layout.oFidx = 2048 := rfl
  have eD : Layout.oDigest = 1792 := rfl
  let P : Nat → State → Prop := fun c v =>
    (∀ g, g ≠ .x9 → g ≠ .x10 → v.gpr g = u.gpr g) ∧ v.sp = u.sp ∧ v.rd = u.rd ∧ v.wr = u.wr ∧ v.v = u.v ∧
    (∀ i < c, v.mem.readW (at' S (Layout.oFidx + 8 * i)) 64 = BitVec.ofNat 64 (ixv u.mem S a i)) ∧
    Frame [⟨at' S Layout.oFidx, 8 * c⟩] u.mem v.mem
  unfold Impl.SlhDsa.AArch64.Fors.indices
  refine wp_flatRange (P := P) k ⟨fun _ _ _ => rfl, rfl, rfl, rfl, rfl, fun _ h => absurd h (by omega),
    Frame.refl _ _⟩ (fun c hc v is' ⟨g, sp, r, w, vv, fi, f⟩ k' => ?_) fun v ⟨g, sp, r, w, vv, fi, f⟩ =>
      K v ⟨g, sp, r, w, vv, fi, f⟩
  have hca : c * a / 8 + 3 ≤ 64 := by
    have := Nat.mul_le_mul_right a (show c ≤ k by omega); omega
  refine WP.block_append (WP.mono (index_ok (S := S) ha hca (by omega) (by rw [g _ (by decide) (by decide), h19])
    (by rw [w]; exact hw)) fun v' ⟨g', sp', r', w', vv', e', f'⟩ => k' v' ?_)
  have hkd : ∀ q, q < Layout.oFidx → v.mem (at' S q) = u.mem (at' S q) := fun q hq =>
    byte_frame f fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact disj_scr S (by omega) (by rw [eF] at hq; omega) (by rw [eF]; omega)
  have hix : ixv v.mem S a c = ixv u.mem S a c := by
    simp only [ixv]
    rw [hkd _ (by rw [eD, eF]; omega), hkd _ (by rw [eD, eF]; omega), hkd _ (by rw [eD, eF]; omega)]
  refine ⟨fun g'' h₀ h₁ => by rw [g' _ h₀ h₁, g _ h₀ h₁], by rw [sp', sp], by rw [r', r], by rw [w', w],
    by rw [vv', vv], fun i hi => ?_, ?_⟩
  · by_cases e : i = c
    · subst e; rw [e', hix]
    · rw [← fi i (by omega)]
      exact readW_frame f' fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact disj_scr S (by omega) (by rw [eF]; omega) (by rw [eF]; omega)
  · exact (f.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩).trans (f'.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub S (by omega) (by omega)⟩)

/-! ## `pkFors`: `T_k` of the roots -/

theorem laneB0 : Layout.laneB 0 = 3648 := rfl

theorem bytesAt_cat (m : Mem) (S : Addr) (a x y : Nat) :
    bytesAt m (at' S a) (x + y) = bytesAt m (at' S a) x ++ bytesAt m (at' S (a + x)) y := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, at_add, Nat.add_assoc]

/-- The fields of lane 0 of the lanes `B` for `T_k`: `FORS_ROOTS`, `kp`, 0, 0. -/
theorem pkFields_ok {p : Params} (hn32 : p.n ≤ 32) (hn8 : p.n % 8 = 0) {S : Addr} {t : State} {is : List Instr} {Q : State → Prop}
    (h19 : t.gpr .x19 = S) (hKP : (t.gpr .x20).toNat < 2 ^ 32) (hw : (⟨S, 65536⟩ : Region) ∈ t.wr)
    (K : ∀ t', Keep [.x9] t t' →
      bytesAt t'.mem (at' S (Layout.laneB 0 + p.n + 16)) 16 =
        toByte 4 4 ++ (toByte (t.gpr .x20).toNat 4 ++ (toByte 0 4 ++ toByte 0 4)) →
      Frame [⟨at' S (Layout.laneB 0 + p.n + 16), 16⟩] t.mem t'.mem → WP isa (.block is) t' Q) :
    WP isa (.block (Impl.SlhDsa.AArch64.setField .x19 (Layout.laneB 0 + (⟨p.n, p.len⟩ : Layout).adrsOff + 16) 4 ++
        Impl.SlhDsa.AArch64.setFieldR .x19 (Layout.laneB 0 + (⟨p.n, p.len⟩ : Layout).adrsOff + 20) .x20 ++
        Impl.SlhDsa.AArch64.setField .x19 (Layout.laneB 0 + (⟨p.n, p.len⟩ : Layout).adrsOff + 24) 0 ++
        Impl.SlhDsa.AArch64.setField .x19 (Layout.laneB 0 + (⟨p.n, p.len⟩ : Layout).adrsOff + 28) 0 ++ is)) t Q := by
  have hB := laneB0
  simp only [Layout.adrsOff, List.append_assoc]
  refine setField_ok (by decide) (by rw [hB]; omega) (by rw [h19]; exact in_scr hw (by rw [hB]; omega))
    fun t₁ f₁ => ?_
  have hb₁ : t₁.gpr .x19 = S := by rw [f₁.keep.get .x19, h19]
  refine setFieldR_ok (r := .x20) (by decide) (by rw [f₁.keep.get .x20]; exact hKP) (by rw [hB]; omega)
    (by rw [hb₁]; exact in_scr (by rw [f₁.keep.wr]; exact hw) (by rw [hB]; omega)) fun t₂ f₂ => ?_
  have hb₂ : t₂.gpr .x19 = S := by rw [f₂.keep.get .x19, hb₁]
  refine setField_ok (by decide) (by rw [hB]; omega)
    (by rw [hb₂]; exact in_scr (by rw [f₂.keep.wr, f₁.keep.wr]; exact hw) (by rw [hB]; omega)) fun t₃ f₃ => ?_
  have hb₃ : t₃.gpr .x19 = S := by rw [f₃.keep.get .x19, hb₂]
  refine setField_ok (by decide) (by rw [hB]; omega)
    (by rw [hb₃]; exact in_scr (by rw [f₃.keep.wr, f₂.keep.wr, f₁.keep.wr]; exact hw) (by rw [hB]; omega))
    fun t₄ f₄ => ?_
  have e₁ := f₁.frame; have e₂ := f₂.frame; have e₃ := f₃.frame; have e₄ := f₄.frame
  rw [h19] at e₁
  rw [hb₁] at e₂
  rw [hb₂] at e₃
  rw [hb₃] at e₄
  refine K t₄ (((f₁.keep.trans f₂.keep).trans (f₃.keep.trans f₄.keep)).mono (by simp)) ?_ ?_
  · have b₁ := f₁.bytes
    have b₂ := f₂.bytes
    have b₃ := f₃.bytes
    have b₄ := f₄.bytes
    rw [h19] at b₁
    rw [hb₁, f₁.keep.get .x20] at b₂
    rw [hb₂] at b₃
    rw [hb₃] at b₄
    have k1 : ∀ {m m' : Mem} {o : Nat}, Frame [⟨at' S o, 4⟩] m m' → ∀ q, q + 4 ≤ o ∨ o + 4 ≤ q → q + 4 ≤ 65536 →
        o + 4 ≤ 65536 → bytesAt m' (at' S q) 4 = bytesAt m (at' S q) 4 := fun hf q h h₁ h₂ =>
      TreeBase.bytesAt_frame hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact disj_scr S h h₁ h₂) (by decide)
    rw [show (16 : Nat) = 4 + (4 + (4 + 4)) from rfl, bytesAt_cat, bytesAt_cat, bytesAt_cat]
    rw [k1 e₄ _ (by omega) (by rw [hB]; omega) (by rw [hB]; omega),
      k1 e₃ _ (by omega) (by rw [hB]; omega) (by rw [hB]; omega),
      k1 e₂ _ (by omega) (by rw [hB]; omega) (by rw [hB]; omega), b₁,
      k1 e₄ _ (by omega) (by rw [hB]; omega) (by rw [hB]; omega),
      k1 e₃ _ (by omega) (by rw [hB]; omega) (by rw [hB]; omega),
      show Layout.laneB 0 + p.n + 16 + 4 = Layout.laneB 0 + p.n + 20 by omega, b₂,
      k1 e₄ _ (by omega) (by rw [hB]; omega) (by rw [hB]; omega),
      show Layout.laneB 0 + p.n + 20 + 4 = Layout.laneB 0 + p.n + 24 by omega, b₃,
      show Layout.laneB 0 + p.n + 24 + 4 = Layout.laneB 0 + p.n + 28 by omega, b₄]
  · have sub : ∀ o, o + 4 ≤ 16 → ∀ r ∈ [(⟨at' S (Layout.laneB 0 + p.n + 16 + o), 4⟩ : Region)],
        ∃ R ∈ [(⟨at' S (Layout.laneB 0 + p.n + 16), 16⟩ : Region)], Region.Sub r R := fun o ho r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub S (by omega) (by omega)⟩
    rw [show Layout.laneB 0 + p.n + 16 = Layout.laneB 0 + p.n + 16 + 0 from rfl] at e₁
    rw [show Layout.laneB 0 + p.n + 20 = Layout.laneB 0 + p.n + 16 + 4 by omega] at e₂
    rw [show Layout.laneB 0 + p.n + 24 = Layout.laneB 0 + p.n + 16 + 8 by omega] at e₃
    rw [show Layout.laneB 0 + p.n + 28 = Layout.laneB 0 + p.n + 16 + 12 by omega] at e₄
    exact (((e₁.sub (sub 0 (by decide))).trans (e₂.sub (sub 4 (by decide)))).trans
      (e₃.sub (sub 8 (by decide)))).trans (e₄.sub (sub 12 (by decide)))

/-- What `pkFors` changes. -/
abbrev pkW (n : Nat) (S : Addr) : List Region :=
  [⟨at' S (Layout.laneB 0 + n + 16), 16⟩] ++ Wots4.t4ch n S Layout.oB Layout.strideB ++ [⟨at' S Layout.oMsg, n⟩]

/-- The fields `pkFors` gives lane 0 of the lanes `B`. -/
abbrev pkF (kp : Nat) : List Byte := toByte 4 4 ++ (toByte kp 4 ++ (toByte 0 4 ++ toByte 0 4))

/-- `pkFors`: `T_k` of the `k` roots in lane 0's message to `oMsg`. -/
theorem pk_ok {p : Params} (hz : Sz p) (T : Thash4Impl p.n) (name : String) {S : Addr} {t : State}
    {Q : State → Prop} (hk : p.k * p.n + p.n + 32 ≤ Layout.strideB) (hk0 : 0 < p.k)
    (h19 : t.gpr .x19 = S) (hKP : (t.gpr .x20).toNat < 2 ^ 32) (hw : (⟨S, 65536⟩ : Region) ∈ t.wr)
    (hfit : S.toNat + 65536 ≤ 2 ^ 64)
    (K : ∀ t', t'.rd = t.rd → t'.wr = t.wr → t'.sp = t.sp → (∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r) →
      (∀ r ∈ preservedV, (t'.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64) →
      bytesAt t'.mem (at' S Layout.oMsg) p.n =
        Spec.Sha3.shake256 (bytesAt t.mem (at' S (Layout.laneB 0)) (p.n + 16) ++ pkF (t.gpr .x20).toNat ++
          bytesAt t.mem (at' S (Layout.laneB 0 + p.n + 32)) (p.k * p.n)) p.n →
      Frame (pkW p.n S) t.mem t'.mem → Q t') :
    WP isa (Impl.SlhDsa.AArch64.Fors.pkFors ⟨p.n, p.len⟩ p.k name T.code) t Q := by
  have hn32 := hz.n32
  have hn8 := hz.n8
  have hB := laneB0
  have eM : Layout.oMsg = 1984 := rfl
  have eSB : Layout.strideB = 2208 := rfl
  unfold Impl.SlhDsa.AArch64.Fors.pkFors Impl.SlhDsa.AArch64.thashCall
  have hb : WP isa (.block (Impl.SlhDsa.AArch64.setField .x19 (Layout.laneB 0 + (⟨p.n, p.len⟩ : Layout).adrsOff + 16) 4 ++
        Impl.SlhDsa.AArch64.setFieldR .x19 (Layout.laneB 0 + (⟨p.n, p.len⟩ : Layout).adrsOff + 20) .x20 ++
        Impl.SlhDsa.AArch64.setField .x19 (Layout.laneB 0 + (⟨p.n, p.len⟩ : Layout).adrsOff + 24) 0 ++
        Impl.SlhDsa.AArch64.setField .x19 (Layout.laneB 0 + (⟨p.n, p.len⟩ : Layout).adrsOff + 28) 0)) t
      (fun t₁ => Keep [.x9] t t₁ ∧ bytesAt t₁.mem (at' S (Layout.laneB 0 + p.n + 16)) 16 = pkF (t.gpr .x20).toNat ∧
        Frame [⟨at' S (Layout.laneB 0 + p.n + 16), 16⟩] t.mem t₁.mem) := by
    rw [← List.append_nil (_ ++ Impl.SlhDsa.AArch64.setField _ _ 0)]
    exact pkFields_ok hn32 hn8 h19 hKP hw fun t₁ k₁ b₁ f₁ => WP.block_nil ⟨k₁, b₁, f₁⟩
  refine WP.seq (WP.mono hb fun t₁ ⟨k₁, b₁, f₁⟩ => ?_)
  have h19₁ : t₁.gpr .x19 = S := by rw [k₁.get .x19, h19]
  refine WP.seq (WP.seq ?_)
  rw [Wots4.thashArgs_eq ⟨p.n, p.len⟩ (o := Layout.oB) (by decide)]
  refine wp_addi (imm := Layout.oB) (by decide) fun t₂ e₂ => wp_movz fun t₃ e₃ => wp_movz fun t₄ e₄ =>
    wp_addi (imm := p.n + 32) (by omega) fun t₅ e₅ => wp_mov fun t₆ e₆ => WP.block_nil ?_
  have g0 : t₆.gpr .x0 = at' S Layout.oB := by
    rw [e₆.other _ (by decide), e₅.other _ (by decide), e₄.other _ (by decide), e₃.other _ (by decide), e₂.gpr, h19₁]
  refine Wots4.t4call_ok T name (s := t₆) (S := S) (o := Layout.oB) (st := Layout.strideB) (len := p.n + 32 + p.k * p.n)
    (by rw [e₆.wr, e₅.wr, e₄.wr, e₃.wr, e₂.wr, k₁.wr]; exact hw) hfit (by decide) (by decide) g0
    (by rw [e₆.other _ (by decide), e₅.other _ (by decide), e₄.other _ (by decide), e₃.gpr, Wots4.movz_ofNat (by decide)])
    (by rw [e₆.other _ (by decide), e₅.other _ (by decide), e₄.gpr, Wots4.movz_ofNat (by dsimp only; rw [eSB] at hk; omega)])
    (by rw [e₆.other _ (by decide), e₅.gpr, e₄.other _ (by decide), e₃.other _ (by decide), e₂.gpr, h19₁, at_add,
        Nat.add_assoc])
    (by rw [e₆.gpr, e₅.other _ (by decide), e₄.other _ (by decide), e₃.other _ (by decide), e₂.other _ (by decide),
        h19₁])
    (by omega) (by rw [Nat.add_mod, Nat.add_mod p.n, hn8, Nat.mul_mod, hn8]; simp) (by omega) (by rw [eSB]; omega)
    fun t₇ r₇ w₇ sp₇ g₇ v₇ o₇ f₇ => ?_
  have hm₆ : t₆.mem = t₁.mem := by rw [e₆.mem, e₅.mem, e₄.mem, e₃.mem, e₂.mem]
  have h19₆ : t₆.gpr .x19 = S := by
    rw [e₆.other _ (by decide), e₅.other _ (by decide), e₄.other _ (by decide), e₃.other _ (by decide),
      e₂.other _ (by decide), h19₁]
  have h19₇ : t₇.gpr .x19 = S := by rw [g₇ _ (by decide) (by decide), h19₆]
  have hw₇ : (⟨S, 65536⟩ : Region) ∈ t₇.wr := by rw [w₇, e₆.wr, e₅.wr, e₄.wr, e₃.wr, e₂.wr, k₁.wr]; exact hw
  rw [← List.append_nil (Impl.SlhDsa.AArch64.copyWords _ _ _ _ _)]
  refine copyWords_ok (t := .x19) (sr := .x19) (d₂ := Layout.oMsg) (d₁ := Layout.laneB 0 + p.n + 32) (w := p.n / 8)
    ⟨by decide, by decide, by rw [hB]; omega, by rw [eM]; omega,
      by rw [h19₇]; exact in_scr' hw₇ (by rw [hB]; omega), by rw [h19₇]; exact in_scr hw₇ (by rw [eM]; omega),
      by rw [h19₇]; exact disj_scr S (by rw [hB, eM]; omega) (by rw [eM]; omega) (by rw [hB]; omega)⟩
    fun t₈ k₈ f₈ c₈ => WP.block_nil ?_
  rw [h19₇, show 8 * (p.n / 8) = p.n by omega] at f₈ c₈
  have hlane : bytesAt t₁.mem (at' S (Layout.laneB 0)) (p.n + 32 + p.k * p.n) =
      bytesAt t.mem (at' S (Layout.laneB 0)) (p.n + 16) ++ pkF (t.gpr .x20).toNat ++
        bytesAt t.mem (at' S (Layout.laneB 0 + p.n + 32)) (p.k * p.n) := by
    rw [show p.n + 32 + p.k * p.n = p.n + 16 + (16 + p.k * p.n) by omega,
      bytesAt_cat t₁.mem S (Layout.laneB 0) (p.n + 16) (16 + p.k * p.n),
      bytesAt_cat t₁.mem S (Layout.laneB 0 + (p.n + 16)) 16 (p.k * p.n),
      show Layout.laneB 0 + (p.n + 16) = Layout.laneB 0 + p.n + 16 by omega, b₁,
      show Layout.laneB 0 + p.n + 16 + 16 = Layout.laneB 0 + p.n + 32 by omega, List.append_assoc]
    have hk1 : ∀ {o l : Nat}, o + l ≤ Layout.laneB 0 + p.n + 16 ∨ Layout.laneB 0 + p.n + 32 ≤ o → o + l ≤ 65536 →
        bytesAt t₁.mem (at' S o) l = bytesAt t.mem (at' S o) l := fun h₁ h₂ =>
      TreeBase.bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact disj_scr S h₁ h₂ (by rw [hB]; omega)) (by omega)
    rw [hk1 (by omega) (by rw [hB]; omega), hk1 (by omega) (by rw [eSB] at hk; rw [hB]; omega)]
    simp only [pkF, List.append_assoc]
  refine K t₈ (by rw [k₈.rd, r₇, e₆.rd, e₅.rd, e₄.rd, e₃.rd, e₂.rd, k₁.rd])
    (by rw [k₈.wr, w₇, e₆.wr, e₅.wr, e₄.wr, e₃.wr, e₂.wr, k₁.wr])
    (by rw [k₈.sp, sp₇, e₆.sp, e₅.sp, e₄.sp, e₃.sp, e₂.sp, k₁.sp]) (fun r hr h30 => ?_)
    (fun r hr => by rw [k₈.vcs r hr, v₇ r hr, e₆.v, e₅.v, e₄.v, e₃.v, e₂.v, k₁.vcs r hr]) ?_ ?_
  · have hr' : r ∉ [Reg.x0, .x1, .x2, .x3, .x4, .x9, .x14] := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    rw [k₈.gpr r (by simpa using hr'.2.2.2.2.2.2), g₇ r hr h30, e₆.other _ hr'.2.2.2.2.1, e₅.other _ hr'.2.2.2.1,
      e₄.other _ hr'.2.2.1, e₃.other _ hr'.2.1, e₂.other _ hr'.1, k₁.gpr r (by simpa using hr'.2.2.2.2.2.1)]
  · rw [c₈, show Layout.laneB 0 + p.n + 32 = Layout.oB + 0 * Layout.strideB + p.n + 32 by rfl, o₇ 0 (by decide),
      hm₆, Nat.zero_mul, Nat.add_zero, show Layout.oB = Layout.laneB 0 from rfl, hlane]
  · rw [hm₆] at f₇
    refine ((f₁.mono fun r hr => ?_).trans (f₇.mono fun r hr => ?_)).trans (f₈.mono fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; simp [pkW]
    · simp only [pkW, List.mem_append]; exact .inl (.inr hr)
    · simp only [List.mem_singleton] at hr; subst hr; simp [pkW]

end VG.Proof.SlhDsa.AArch64.Fors
