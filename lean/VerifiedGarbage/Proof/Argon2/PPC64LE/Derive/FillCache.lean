module

import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.FillInput
import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.FillCall
public import VerifiedGarbage.Proof.Argon2.FillStep
import VerifiedGarbage.Proof.Argon2.FillPositions
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.ReadHalves
import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Initial
import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.MemoryInit
public import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Body
public import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.FillDep
import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Scratch
import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Locals
public import VerifiedGarbage.Proof.Argon2.Contract

/-!
# Argon2 on PPC64LE: the address block

`addressCalls_ok`: the address block, G(0, G(0, input)), at `scratch + 6144`.
`addressCache_ok`: J₁, J₂ from the cached address block, regenerated when
the index enters a new group of 128. `randomSource_ok`: J₁, J₂ are the
random word of `FillStep.random`.
-/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE.Derive

open VG VG.PPC64LE
open VG.Proof.MdStream.PPC64LE (Upd Mupd wp_add wp_addi wp_sub wp_li wp_lsl wp_lsr wp_and wp_mov wp_lwz)
open VG.Spec.Argon2 (Block zeroBlock FillState compress addressBlock)
open VG.Proof.Argon2 (matrixCell Represents)
open VG.Impl.Argon2.PPC64LE.Derive (indexOff counterOff j1Off j2Off)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `stage x y out`: G of the blocks at `scratch + x` and `scratch + y` to `scratch + out`. -/
theorem stage_ok {s : State} (h : Inv s₀ s) {x y o : Nat} (ho : 4096 ≤ o) (ho' : o + 1024 ≤ 8192)
    (hx : 4096 ≤ x) (hx' : x + 1024 ≤ 8192) (hxo : x + 1024 ≤ o ∨ o + 1024 ≤ x)
    (hy : 4096 ≤ y) (hy' : y + 1024 ≤ 8192) (hyo : y + 1024 ≤ o ∨ o + 1024 ≤ y) :
    WP isa (Impl.Argon2.PPC64LE.Derive.stage x y o) s fun t => Inv s₀ t ∧
      (∀ q ∈ preserved, t.gpr q = s.gpr q) ∧
      Frame [⟨scrP s₀ + BitVec.ofNat 64 o, 1024⟩, ⟨scrP s₀, 4096⟩] s.mem t.mem ∧
      blockAt t.mem (scrP s₀ + BitVec.ofNat 64 o) =
        compress (blockAt s.mem (scrP s₀ + BitVec.ofNat 64 x)) (blockAt s.mem (scrP s₀ + BitVec.ofNat 64 y)) := by
  unfold Impl.Argon2.PPC64LE.Derive.stage
  refine WP.seq (wp_addi (by omega_arith) fun s₁ u₁ => wp_addi (by omega_arith) fun s₂ u₂ =>
    wp_addi (by omega_arith) fun s₃ u₃ => wp_mov fun s₄ u₄ => WP.block_nil ?_)
  have o₄ := (((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)).trans (Only.of_upd u₄)
  have i₄ := h.only o₄
  have r31 : s.gpr .r31 = scrP s₀ := h.r31
  have dx : s₄.gpr .r6 = scrP s₀ := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), r31]
  have ax : s₄.gpr .r3 = scrP s₀ + BitVec.ofNat 64 x := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, r31]
  have sx : s₄.gpr .r4 = scrP s₀ + BitVec.ofNat 64 y := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), r31]
  have cx : s₄.gpr .r5 = scrP s₀ + BitVec.ofNat 64 o := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), r31]
  refine ccall_ok hp i₄ dx ho (by omega_arith) cx (by rw [ax]; exact .inr ⟨x, hx, by omega_arith, hxo, rfl⟩)
    (by rw [sx]; exact .inr ⟨y, hy, by omega_arith, hyo, rfl⟩) fun t it cs f post =>
      ⟨it, fun q hq => ?_, by rw [← o₄.mem]; exact f, by rw [post, ax, sx, o₄.mem]⟩
  rw [cs q hq]
  exact o₄.gpr q fun hm => by revert hq; revert hm; revert q; decide

omit hp in
/-- A block of `scratch` at `d`, outside the regions G's call at `o` writes. -/
theorem stage_keep {m m' : Mem} {o : Nat} (ho' : o + 1024 ≤ 16384)
    (f : Frame [⟨scrP s₀ + BitVec.ofNat 64 o, 1024⟩, ⟨scrP s₀, 4096⟩] m m') {d : Nat} (hd : 4096 ≤ d)
    (hd' : d + 1024 ≤ 16384) (hdo : d + 1024 ≤ o ∨ o + 1024 ≤ d) :
    blockAt m' (scrP s₀ + BitVec.ofNat 64 d) = blockAt m (scrP s₀ + BitVec.ofNat 64 d) := by
  refine blockAt_keep f fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint _ hdo (by omega_arith) (by omega_arith)
  · exact Offset.disjoint_base _ hd (by omega_arith)

omit hp in
theorem stage_frame {m m' : Mem} {o : Nat} (ho' : o + 1024 ≤ 16384)
    (f : Frame [⟨scrP s₀ + BitVec.ofNat 64 o, 1024⟩, ⟨scrP s₀, 4096⟩] m m') :
    Frame [scrR s₀] m m' :=
  f.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scrR s₀, by simp, Offset.sub_base _ ho'⟩
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩

/-- `addressCalls`: the address block for the counter `c` at `scratch + 6144`. -/
theorem addressCalls_ok {s : State} (h : Inv s₀ s) {pass slice lane index c : Nat}
    (ps : Pos s₀ s pass slice lane index) (hc : lw s₀ s counterOff = BitVec.ofNat 64 c) :
    WP isa Impl.Argon2.PPC64LE.Derive.addressCalls s fun t => Inv s₀ t ∧
      (∀ q ∈ preserved, t.gpr q = s.gpr q) ∧ Frame [scrR s₀] s.mem t.mem ∧
      blockAt t.mem (scrP s₀ + BitVec.ofNat 64 6144) = addressBlock (prm s₀) pass lane slice c := by
  unfold Impl.Argon2.PPC64LE.Derive.addressCalls
  refine WP.seq ((input_ok hp h ps hc).mono fun t₁ ⟨i₁, g₁, f₁, b₁, z₁⟩ => ?_)
  refine WP.seq ((stage_ok hp i₁ (x := 7168) (y := 5120) (o := 4096) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)).mono fun t₂ ⟨i₂, g₂, f₂, b₂⟩ => ?_)
  refine (stage_ok hp i₂ (x := 7168) (y := 4096) (o := 6144) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)).mono
    fun t ⟨it, gt, ft, bt⟩ => ⟨it, fun q hq => ?_, ?_, ?_⟩
  · rw [gt q hq, g₂ q hq]
    exact g₁ q fun e => by subst e; exact absurd hq (by decide)
  · refine Frame.trans (f₁.sub fun r hr => ?_) ((stage_frame (by decide) f₂).trans (stage_frame (by decide) ft))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scrR s₀, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨scrR s₀, by simp, Offset.sub_base _ (by decide)⟩
  · rw [bt, stage_keep (by decide) f₂ (d := 7168) (by decide) (by decide) (by decide), b₂, z₁, b₁]
    rfl

end

theorem and127 {n : Nat} (h : n < 2 ^ 64) :
    BitVec.ofNat 64 n &&& BitVec.ofNat 64 127 = BitVec.ofNat 64 (n % 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (a := 127) (by decide), Nat.mod_eq_of_lt (a := n % 128) (by omega_arith),
    show 127 = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem shr7 {n : Nat} (h : n < 2 ^ 64) : BitVec.ofNat 64 n >>> 7 = BitVec.ofNat 64 (n / 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.mod_eq_of_lt (by omega_arith), Nat.shiftRight_eq_div_pow]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `cacheWord`: J₁ and J₂ are doubleword `index mod 128` of the cached address block. -/
theorem cacheWord_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (hi : index < 2 ^ 30) :
    WP isa (.block Impl.Argon2.PPC64LE.Derive.cacheWord) s fun t => FS s₀ pass slice lane index ctr st t ∧
      Rand s₀ t ((blockAt s.mem (scrP s₀ + BitVec.ofNat 64 6144))[index % 128]'(Nat.mod_lt _ (by decide))) := by
  have e8 : 8 * (index % 128) < 1024 := by omega_arith
  unfold Impl.Argon2.PPC64LE.Derive.cacheWord
  refine wp_ldloc h.inv (d := indexOff) (by decide) fun s₁ u₁ => wp_li (by decide) fun s₂ u₂ =>
    wp_and fun s₃ u₃ => wp_lsl (by decide) fun s₄ u₄ => wp_add fun s₅ u₅ => ?_
  have o₅ := (((((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)).trans
    (Only.of_upd u₄)).trans (Only.of_upd u₅))
  have h₅ := h.of_only o₅
  have a₅ : s₅.gpr .r3 = scrP s₀ + BitVec.ofNat 64 (8 * (index % 128)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h.inv.r31, u₄.gpr, u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.gpr,
      h.pos.index, and127 (by omega_arith), ofNat_shl' (by omega_arith)]
    congr 2; omega_arith
  have m₅ : s₅.mem = s.mem := o₅.mem
  have inS : ∀ t : State, Inv s₀ t → ∀ o, o + 4 ≤ 1024 →
      InRegions (t.rd ++ t.wr) (scrP s₀ + BitVec.ofNat 64 (6144 + 8 * (index % 128) + o)) 4 :=
    fun t it o ho => by
      rw [it.wr]
      exact ⟨scrR s₀, List.mem_append_right _ (scr_mem hp), Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have ad : ∀ o, s₅.gpr .r3 + BitVec.ofNat 64 (6144 + o) =
      scrP s₀ + BitVec.ofNat 64 (6144 + 8 * (index % 128) + o) := fun o => by
    rw [a₅, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega_arith
  refine wp_lwz (a := scrP s₀ + BitVec.ofNat 64 (6144 + 8 * (index % 128) + 0)) (by decide) (ad 0)
    (inS _ h₅.inv 0 (by decide)) fun s₆ u₆ => ?_
  have h₆ := h₅.of_only (Only.of_upd u₆)
  refine wp_stloc h₆.inv (d := j1Off) (by decide) fun s₇ i₇ v₇ o₇ g₇ m₇ => ?_
  have h₇ := h₆.store hp i₇ (d := j1Off) (by decide) (by decide) m₇
  refine wp_lwz (a := scrP s₀ + BitVec.ofNat 64 (6144 + 8 * (index % 128) + 4)) (by decide)
    (by rw [g₇, u₆.other _ (by decide)]; exact ad 4) (inS _ h₇.inv 4 (by decide)) fun s₈ u₈ => ?_
  have h₈ := h₇.of_only (Only.of_upd u₈)
  refine wp_stloc h₈.inv (d := j2Off) (by decide) fun t it vt ot gt mt => WP.block_nil ⟨?_, ?_, ?_⟩
  · exact h₈.store hp it (d := j2Off) (by decide) (by decide) mt
  · have w0 : s.mem.readW (scrP s₀ + BitVec.ofNat 64 (6144 + 8 * (index % 128) + 0)) 64 =
        (blockAt s.mem (scrP s₀ + BitVec.ofNat 64 6144))[index % 128] := by
      rw [Nat.add_zero, blockAt_get _ _ (Nat.mod_lt _ (by decide)), BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    rw [ot j1Off (by decide) (by decide), lw_mem u₈.mem, v₇, u₆.gpr, m₅, Mem.readW_lo32 w0, lo_ext]
  · have w0 : s₇.mem.readW (scrP s₀ + BitVec.ofNat 64 (6144 + 8 * (index % 128) + 0)) 64 =
        (blockAt s.mem (scrP s₀ + BitVec.ofNat 64 6144))[index % 128] := by
      rw [m₇, (frame_loc _).readW (r := ⟨scrP s₀ + BitVec.ofNat 64 (6144 + 8 * (index % 128) + 0), 8⟩)
        (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (loc_scr hp (by decide) (by decide) (by omega_arith)).symm) (by decide),
        u₆.mem, m₅, Nat.add_zero, blockAt_get _ _ (Nat.mod_lt _ (by decide)), BitVec.add_assoc,
        BitVec.ofNat_add_ofNat]
    have e4 : scrP s₀ + BitVec.ofNat 64 (6144 + 8 * (index % 128) + 4) =
        scrP s₀ + BitVec.ofNat 64 (6144 + 8 * (index % 128) + 0) + BitVec.ofNat 64 4 := by
      rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    rw [vt, u₈.gpr, e4]
    exact (congrArg (BitVec.setWidth 64) (Mem.readW_hi32 w0)).trans (hi_ext _)

omit hp in
/-- The cached address block is that of `c`. -/
theorem cached {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) {c : Nat} (hc : 1 ≤ c) (hc' : c < 2 ^ 32)
    (he : lw s₀ s counterOff = BitVec.ofNat 64 c) :
    blockAt s.mem (scrP s₀ + BitVec.ofNat 64 6144) = addressBlock (prm s₀) pass lane slice c := by
  obtain ⟨c0, c1, c2 | ⟨_, c4⟩⟩ := h.cache
  · rw [he, c2] at c1
    have := congrArg BitVec.toNat c1
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at this
    exact absurd this (by simp; omega_arith)
  · rw [c4]
    rw [he] at c1
    have := congrArg BitVec.toNat c1
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith),
      Nat.mod_eq_of_lt (by omega_arith)] at this
    rw [this]

/-- `cacheCheck`: `r3 :=` the counter of the index's group; `r4` is zero if it is cached. -/
theorem cacheCheck_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (hi : index < (prm s₀).segmentLen) :
    WP isa (.block Impl.Argon2.PPC64LE.Derive.cacheCheck) s fun t => FS s₀ pass slice lane index ctr st t ∧
      t.gpr .r3 = BitVec.ofNat 64 (index / 128 + 1) ∧
      VG.PPC64LE.eval (.zero .d .r4) t =
        some (BitVec.ofNat 64 (index / 128 + 1) - lw s₀ t counterOff == 0) := by
  have sl := segLen_lt hp
  unfold Impl.Argon2.PPC64LE.Derive.cacheCheck
  refine wp_ldloc h.inv (d := indexOff) (by decide) fun s₁ u₁ => wp_lsr (by decide) fun s₂ u₂ =>
    wp_addi (by decide) fun s₃ u₃ => ?_
  have o₃ := ((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)
  have h₃ := h.of_only o₃
  have a₃ : s₃.gpr .r3 = BitVec.ofNat 64 (index / 128 + 1) := by
    rw [u₃.gpr, u₂.gpr, u₁.gpr, h.pos.index, shr7 (by omega_arith), BitVec.ofNat_add_ofNat]
  refine wp_ldloc h₃.inv (d := counterOff) (by decide) fun s₄ u₄ => wp_sub fun t u => WP.block_nil ?_
  have o₄ := (Only.of_upd u₄).trans (Only.of_upd u)
  refine ⟨h₃.of_only o₄, by rw [u.other _ (by decide), u₄.other _ (by decide), a₃], ?_⟩
  rw [MdStream.PPC64LE.eval_zero, u.gpr, u₄.other _ (by decide), a₃, u₄.gpr, lw_mem u.mem,
    lw_mem u₄.mem]

/-- The address block of the index's group, regenerated unless it is cached. -/
theorem cacheFill_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h₄ : FS s₀ pass slice lane index ctr st s) (hi : index < (prm s₀).segmentLen)
    (a₃ : s.gpr .r3 = BitVec.ofNat 64 (index / 128 + 1))
    (z₄ : VG.PPC64LE.eval (.zero .d .r4) s =
      some (BitVec.ofNat 64 (index / 128 + 1) - lw s₀ s counterOff == 0)) :
    WP isa (.ite (.zero .d .r4) (.block []) (.seq (.block [Impl.Argon2.PPC64LE.Derive.st counterOff .r3])
      Impl.Argon2.PPC64LE.Derive.addressCalls)) s fun t =>
      FS s₀ pass slice lane index (index / 128 + 1) st t ∧
      blockAt t.mem (scrP s₀ + BitVec.ofNat 64 6144) = addressBlock (prm s₀) pass lane slice (index / 128 + 1) := by
  have sl := segLen_lt hp
  refine WP.ite (BitVec.ofNat 64 (index / 128 + 1) - lw s₀ s counterOff == 0) z₄
    (fun hb => ?_) fun hb => ?_
  · have ce : lw s₀ s counterOff = BitVec.ofNat 64 (index / 128 + 1) := by
      have e := beq_iff_eq.mp hb
      exact ((BitVec.sub_eq_iff_eq_add.mp e).trans (by simp)).symm
    have cb := cached h₄ (c := index / 128 + 1) (by omega_arith) (by omega_arith) ce
    exact WP.block_nil ⟨⟨h₄.inv, h₄.pr, h₄.pos, ⟨by omega_arith, ce, .inr ⟨by omega_arith, cb⟩⟩, h₄.mem⟩, cb⟩
  · refine WP.seq (wp_stloc h₄.inv (d := counterOff) (by decide) fun s₅ i₅ v₅ o₅ g₅ m₅ => WP.block_nil ?_)
    have L₅ : ∀ d, 208 ≤ d → d + 8 ≤ 272 → (d + 8 ≤ counterOff ∨ counterOff + 8 ≤ d) →
        lw s₀ s₅ d = lw s₀ s d := fun d h₁ h₂ h₃ => o₅ d (by omega_arith) (by
          simp only [counterOff] at h₃ ⊢; omega_arith)
    have P₅ : Pos s₀ s₅ pass slice lane index :=
      ⟨by rw [L₅ _ (by decide) (by decide) (by decide)]; exact h₄.pos.pass,
        by rw [L₅ _ (by decide) (by decide) (by decide)]; exact h₄.pos.slice,
        by rw [L₅ _ (by decide) (by decide) (by decide)]; exact h₄.pos.lane,
        by rw [L₅ _ (by decide) (by decide) (by decide)]; exact h₄.pos.index⟩
    refine (addressCalls_ok hp i₅ (index := index) (c := index / 128 + 1) P₅ (by rw [v₅, a₃])).mono
      fun t ⟨it, _, ft, bt⟩ => ⟨?_, bt⟩
    have fsub : ∀ r ∈ [scrR s₀], ∃ r' ∈ [memR s₀, scrR s₀, outR s₀, callR s₀], Region.Sub r r' :=
      fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; simp, fun _ h => h⟩
    have Lt : ∀ d, 32 ≤ d → d + 8 ≤ 336 → lw s₀ t d = lw s₀ s₅ d := fun d h₁ h₂ =>
      lw_keep hp ft fsub h₁ h₂
    refine ⟨it, Prm.of_lw h₄.pr fun d h₁ h₂ => ?_, ⟨?_, ?_, ?_, ?_⟩, ⟨by omega_arith,
      by rw [Lt _ (by decide) (by decide), v₅, a₃], .inr ⟨by omega_arith, bt⟩⟩, Represents.keep h₄.mem fun k hk => ?_⟩
    · rw [Lt d (by omega_arith) (by omega_arith), L₅ d (by omega_arith) (by omega_arith) (by simp only [counterOff]; omega_arith)]
    · rw [Lt _ (by decide) (by decide)]; exact P₅.pass
    · rw [Lt _ (by decide) (by decide)]; exact P₅.slice
    · rw [Lt _ (by decide) (by decide)]; exact P₅.lane
    · rw [Lt _ (by decide) (by decide)]; exact P₅.index
    · have hk' : k < blocksN s₀ := by rw [hp.blocks]; exact hk
      have sk := Proof.Argon2.matrixCell_sub (memP s₀) _ _ hk'
      rw [blockAt_keep ft fun r hr => ?_, m₅, blockAt_keep (frame_loc _) fun r hr => ?_]
      · simp only [List.mem_singleton] at hr; subst hr
        exact (loc_disj hp (d := counterOff) (by decide) (by decide) (memR s₀) (by simp)).symm.sub_left sk
      · simp only [List.mem_singleton] at hr; subst hr
        exact hp.mem_scr.sub_left sk

/-- `addressCache`: J₁ and J₂ from the address block of the index's group of 128. -/
theorem addressCache_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (hi : index < (prm s₀).segmentLen) :
    WP isa Impl.Argon2.PPC64LE.Derive.addressCache s fun t =>
      FS s₀ pass slice lane index (index / 128 + 1) st t ∧
      Rand s₀ t ((addressBlock (prm s₀) pass lane slice (index / 128 + 1))[index % 128]'(Nat.mod_lt _ (by decide))) := by
  have sl := segLen_lt hp
  unfold Impl.Argon2.PPC64LE.Derive.addressCache
  refine WP.seq ((cacheCheck_ok hp h hi).mono fun s₄ ⟨h₄, a₄, z₄⟩ => ?_)
  refine WP.seq ((cacheFill_ok hp h₄ hi a₄ z₄).mono fun t ⟨ht, bt⟩ =>
    (cacheWord_ok hp ht (by omega_arith)).mono fun u ⟨hu, wu⟩ => ⟨hu, ?_⟩)
  rw [bt] at wu
  exact wu

/-- `randomSource`: J₁ and J₂ are the step's random word. -/
theorem randomSource_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (hpass : pass < 2 ^ 32) (hl : lane < lanesN s₀)
    (hs : slice < 4) (hi : index < (prm s₀).segmentLen) :
    WP isa Impl.Argon2.PPC64LE.Derive.randomSource s fun t =>
      FS s₀ pass slice lane index (ctrNext (prm s₀) pass slice index ctr) st t ∧
      Rand s₀ t (Proof.Argon2.FillStep.random (prm s₀) pass lane slice index st.memory) := by
  unfold Impl.Argon2.PPC64LE.Derive.randomSource
  refine WP.seq ((addressMode_ok hp h.inv h.pos hpass hs).mono fun s₁ ⟨z₁, k₁⟩ => ?_)
  have h₁ := h.of_only k₁
  refine WP.ite (!Spec.Argon2.independent (prm s₀) pass slice) z₁ (fun hb => ?_) fun hb => ?_
  · have hind : Spec.Argon2.independent (prm s₀) pass slice = false := by simpa using hb
    refine (dependentWord_ok hp h₁ hl hs hi).mono fun t ⟨ht, wt⟩ => ⟨by rw [ctrNext, hind]; exact ht, ?_⟩
    have cl := Proof.Argon2.previous_cell_lt (prm s₀) hp.lanes_pos hp.memory_ge
      (column := slice * (prm s₀).segmentLen + index) hl
    rw [k₁.mem, h.mem.block _ cl] at wt
    rw [Proof.Argon2.FillStep.random, hind]
    simpa only [Bool.false_eq_true, ite_false] using wt
  · have hind : Spec.Argon2.independent (prm s₀) pass slice = true := by simpa using hb
    refine (addressCache_ok hp h₁ hi).mono fun t ⟨ht, wt⟩ => ⟨by rw [ctrNext, hind]; exact ht, ?_⟩
    rw [Proof.Argon2.FillStep.random, hind]
    simpa only [ite_true] using wt

end

end VG.Proof.Argon2.PPC64LE.Derive
