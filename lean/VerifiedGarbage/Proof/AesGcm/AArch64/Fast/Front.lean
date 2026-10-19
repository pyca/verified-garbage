module
public import VerifiedGarbage.Proof.AesGcm.AArch64.J0
public import VerifiedGarbage.Impl.AesGcm.AArch64.Fast
public import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Groups

import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Pad
import VerifiedGarbage.Proof.AesGcm.AArch64.Front
import VerifiedGarbage.Proof.AesGcm.AArch64.Body
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# AES-GCM on AArch64, the path for TLS records: the front

Untrusted: everything here is checked by Lean. `front` writes `J₀` of the
12-byte nonce and the first counter block (as `j0` does), computes `H'` and
keeps it at `W + hO` (`KeyAt`), and absorbs the additional data (at most a
block), padded, into the accumulator at `St + 16` (`front_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64.Fast

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64 VG.WriteBytes
open VG.Proof.AesGcm.AArch64
open VG.Proof.Gcm.AArch64.Pmull
open VG.Impl.Gcm.AArch64.Pmull (LO MID HI A T C Y tReg sReg poly)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks zeros padLen ofBytes inc32)

/-- `H'` for `H`, and its halves swapped, kept at `W + hO`. -/
def KeyAt (H : Block) (m : Mem) (W : Addr) : Prop :=
  m.read (W + BitVec.ofNat 64 Impl.AesGcm.AArch64.Fast.hO) 16 = keyV H ∧
    m.read (W + BitVec.ofNat 64 (Impl.AesGcm.AArch64.Fast.hO + 16)) 16 =
      ext8 (m.read (W + BitVec.ofNat 64 Impl.AesGcm.AArch64.Fast.hO) 16)
        (m.read (W + BitVec.ofNat 64 Impl.AesGcm.AArch64.Fast.hO) 16)

/-- Where `H'` is kept. -/
abbrev keyR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 Impl.AesGcm.AArch64.Fast.hO, 32⟩

/-- `KeyAt` outside a frame apart from where `H'` is kept. -/
theorem KeyAt.frame {H : Block} {m m' : Mem} {W : Addr} {rs : List Region} (h : KeyAt H m W)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (keyR W).Disjoint r) : KeyAt H m' W := by
  have e₀ : m'.read (W + BitVec.ofNat 64 Impl.AesGcm.AArch64.Fast.hO) 16 =
      m.read (W + BitVec.ofNat 64 Impl.AesGcm.AArch64.Fast.hO) 16 :=
    hf.read (r := ⟨W + BitVec.ofNat 64 Impl.AesGcm.AArch64.Fast.hO, 16⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (Offset.sub W (Nat.le_refl _) (by decide))) (by decide)
  have e₁ : m'.read (W + BitVec.ofNat 64 (Impl.AesGcm.AArch64.Fast.hO + 16)) 16 =
      m.read (W + BitVec.ofNat 64 (Impl.AesGcm.AArch64.Fast.hO + 16)) 16 :=
    hf.read (r := ⟨W + BitVec.ofNat 64 (Impl.AesGcm.AArch64.Fast.hO + 16), 16⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (Offset.sub W (by decide) (by decide))) (by decide)
  exact ⟨by rw [e₀]; exact h.1, by rw [e₁, e₀]; exact h.2⟩

/-- The regions `front` writes. -/
abbrev frontFrame' (St W : Addr) : List Region := j0Frame St W ++ [keyR W]

/-- After `front`, from `s₀`: `J₀` and the first counter block, `H'`, the
additional data `a` absorbed, and the data `D` of `n` bytes in `x23` and `x26`. -/
structure FFront (Ctx St W SP : Addr) (H : Block) (iv a : List Byte) (D : Addr) (n : Nat) (s₀ s : State) :
    Prop where
  env : Env Ctx St W SP s
  x22 : s.gpr .x22 = s₀.gpr .x22
  x28 : s.gpr .x28 = s₀.gpr .x28
  x23 : s.gpr .x23 = D
  x26 : s.gpr .x26 = BitVec.ofNat 64 n
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H
  j0 : blockAt s.mem St = Spec.Gcm.j0 H iv
  cb : blockAt s.mem (St + BitVec.ofNat 64 48) = inc32 (Spec.Gcm.j0 H iv)
  y : blockAt s.mem (St + BitVec.ofNat 64 16) = ghash H (blocks (a ++ zeros (padLen a.length)))
  key : KeyAt H s.mem W
  frame : Frame (frontFrame' St W) s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W)
include L

theorem slots_frontFrame' : ∀ r ∈ frontFrame' St W, (⟨W + BitVec.ofNat 64 216, 40⟩ : Region).Disjoint r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact slots_j0Frame L r hr
  · simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)

omit L in
/-- `j012` writes only `x9`–`x12` of the registers. -/
theorem j012_others {k : Reg → BitVec 64} {H : Block} {Np : Addr} {s : State} (h : J0In Ctx St W SP k H Np 12 s) :
    WP isa (.block j012) s fun s' => Others [.x9, .x10, .x11, .x12] s s' := by
  have he := h.env
  have hd := h.data
  have r₀ := in_off hd.rd (show 0 + 4 ≤ 12 by decide) (by decide)
  have r₁ := in_off hd.rd (show 4 + 4 ≤ 12 by decide) (by decide)
  have r₂ := in_off hd.rd (show 8 + 4 ≤ 12 by decide) (by decide)
  have w₀ := he.perm.stW (show 0 + 4 ≤ 80 by decide)
  have w₁ := he.perm.stW (show 4 + 4 ≤ 80 by decide)
  have w₂ := he.perm.stW (show 8 + 4 ≤ 80 by decide)
  have w₃ := he.perm.stW (show 12 + 4 ≤ 80 by decide)
  rw [add_ofNat_zero] at r₀ w₀
  refine WP.of_runBlock ⟨_, by simp only [j012]; arun [h.x23, he.x20, r₀, r₁, r₂, w₀, w₁, w₂, w₃, add_ofNat_zero], ?_⟩
  others_tac

omit L in
/-- `initState` writes only `x9`–`x12` of the registers. -/
theorem initState_others {s : State} (he : Env Ctx St W SP s) :
    WP isa (.block initState) s fun s' => Others [.x9, .x10, .x11, .x12] s s' := by
  have r₀ := he.perm.stR (show 0 + 4 ≤ 80 by decide)
  have r₁ := he.perm.stR (show 4 + 4 ≤ 80 by decide)
  have r₂ := he.perm.stR (show 8 + 4 ≤ 80 by decide)
  have r₃ := he.perm.stR (show 12 + 4 ≤ 80 by decide)
  have w₀ := he.perm.stW (show 48 + 4 ≤ 80 by decide)
  have w₁ := he.perm.stW (show 52 + 4 ≤ 80 by decide)
  have w₂ := he.perm.stW (show 56 + 4 ≤ 80 by decide)
  have w₃ := he.perm.stW (show 60 + 4 ≤ 80 by decide)
  have z₀ := he.perm.stW (show 16 + 8 ≤ 80 by decide)
  have z₁ := he.perm.stW (show 24 + 8 ≤ 80 by decide)
  rw [add_ofNat_zero] at r₀
  refine WP.of_runBlock ⟨_, by simp only [initState]; arun [he.x20, r₀, r₁, r₂, r₃, w₀, w₁, w₂, w₃, z₀, z₁,
    add_ofNat_zero], ?_⟩
  others_tac

/-- `front`, from the 12-byte nonce at `Np`, the `al` (at most 16) bytes of
additional data at `A` (`x4`, `x5`), and the data (`x6`, `x7`). -/
theorem front_ok (hMK : MulKey) {k : Reg → BitVec 64} {H : Block} {Np A D : Addr} {al n : Nat} {s₀ : State}
    (hJ : J0In Ctx St W SP k H Np 12 s₀) (haad : DataOk St W s₀ A al) (hal : al ≤ 16)
    (h4 : s₀.gpr .x4 = A) (h5 : s₀.gpr .x5 = BitVec.ofNat 64 al) (h6 : s₀.gpr .x6 = D)
    (h7 : s₀.gpr .x7 = BitVec.ofNat 64 n) :
    WP isa Impl.AesGcm.AArch64.Fast.front s₀
      (FFront Ctx St W SP H (bytesAt s₀.mem Np 12) (bytesAt s₀.mem A al) D n s₀) := by
  unfold Impl.AesGcm.AArch64.Fast.front
  simp only [Impl.AesGcm.AArch64.Fast.hPrime, List.append_assoc]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.with_rdwr (WP.block_and (j012_ok L hJ) (j012_others hJ)))
    fun s₁ ⟨⟨h₁, o₁⟩, rd₁, wr₁⟩ => ?_
  rw [WP.block_append_iff]
  have he₁ := h₁.env
  obtain ⟨s₁', run₁', x25₁', x27₁', x23₁', x26₁', r₁'⟩ : ∃ s₁', runBlock isa
      [mov .x25 .x5, mov .x27 .x4, mov .x23 .x6, mov .x26 .x7] s₁ = some s₁' ∧
      s₁'.gpr .x25 = BitVec.ofNat 64 al ∧ s₁'.gpr .x27 = A ∧ s₁'.gpr .x23 = D ∧ s₁'.gpr .x26 = BitVec.ofNat 64 n ∧
      Regs [.x25, .x27, .x23, .x26] s₁ s₁' := by
    refine ⟨_, by arun [], ?_⟩
    exact ⟨by simp [gpr_write, o₁ .x5 (by decide), h5], by simp [gpr_write, o₁ .x4 (by decide), h4],
      by simp [gpr_write, o₁ .x6 (by decide), h6], by simp [gpr_write, o₁ .x7 (by decide), h7],
      ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  refine WP.of_runBlock ⟨s₁', run₁', ?_⟩
  have he₁' := he₁.of_regs r₁'
  have hM : J0Mid Ctx St W SP s₁'.gpr H (bytesAt s₀.mem Np 12) s₀.mem s₁' :=
    ⟨he₁', fun _ _ => rfl, by rw [r₁'.mem]; exact h₁.hH, by rw [r₁'.mem]; exact h₁.j0, by rw [r₁'.mem]; exact h₁.frame⟩
  rw [WP.block_append_iff]
  refine WP.mono (WP.with_rdwr (WP.block_and (initState_ok L hM) (initState_others he₁')))
    fun s₂ ⟨⟨h₂, o₂⟩, rd₂, wr₂⟩ => ?_
  rw [WP.block_append_iff]
  have he₂ := h₂.env
  have kg₂ : ∀ r, r ∉ [Reg.x9, .x10, .x11, .x12, .x25, .x27, .x23, .x26] → s₂.gpr r = s₀.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h9, h10, h11, h12, h25, h27, h23, h26⟩ := hr
    rw [o₂ r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h9, h10, h11, h12⟩),
      r₁'.others r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h25, h27, h23, h26⟩),
      o₁ r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h9, h10, h11, h12⟩)]
  have v₂ : ∀ r ∈ [Reg.x25, .x27, .x23, .x26], s₂.gpr r = s₁'.gpr r := fun r hr => o₂ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide)
  obtain ⟨s₃, run₃, x0₃, r₃⟩ : ∃ s₃, runBlock isa [ptr .x0 .x21 240] s₂ = some s₃ ∧
      s₃.gpr .x0 = Ctx + BitVec.ofNat 64 240 ∧ Regs [.x0] s₂ s₃ := by
    refine ⟨_, by arun [], ?_⟩
    exact ⟨by simp [gpr_write, he₂.x21], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have he₃ := he₂.of_regs r₃
  rw [WP.block_append_iff]
  refine WP.mono (key_ok (H := H) (by rw [x0₃, add_ofNat_zero]; exact he₃.perm.ctxR (by decide))
    (by rw [x0₃, add_ofNat_zero, r₃.mem]; exact h₂.hH)) fun s₄ ⟨hk₄, g₄, v₄, m₄, rd₄, wr₄, sp₄⟩ => ?_
  have he₄ : Env Ctx St W SP s₄ := he₃.keep (fun r hr => g₄ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₄ rd₄ wr₄
  rw [WP.block_append_iff]
  refine WP.mono (keep_ok (by rw [he₄.x19]; exact he₄.perm.wW (by decide))
    (by rw [he₄.x19]; exact he₄.perm.wW (by decide))) fun s₅ ⟨m₅, y₅, v₅, g₅, rd₅, wr₅, sp₅⟩ => ?_
  have he₅ : Env Ctx St W SP s₅ := he₄.keep (fun r _ => by rw [g₅]) sp₅ rd₅ wr₅
  -- Where `H'` is kept.
  have c₀ : (keyR W).Contains (W + BitVec.ofNat 64 Impl.AesGcm.AArch64.Fast.hO) 16 :=
    Offset.contains W (Nat.le_refl _) (by decide) (by decide)
  have c₁ : (keyR W).Contains (W + BitVec.ofNat 64 (Impl.AesGcm.AArch64.Fast.hO + 16)) 16 :=
    Offset.contains W (by decide) (by decide) (by decide)
  have fk : Frame [keyR W] s₄.mem s₅.mem := by
    rw [m₅, he₄.x19]
    exact ((Frame.refl _ _).write (List.mem_singleton_self _) _ c₀).write (List.mem_singleton_self _) _ c₁
  have key₅ : KeyAt H s₅.mem W := by
    have d₀₁ : (⟨W + BitVec.ofNat 64 Impl.AesGcm.AArch64.Fast.hO, 16⟩ : Region).Disjoint
        ⟨W + BitVec.ofNat 64 (Impl.AesGcm.AArch64.Fast.hO + 16), 16⟩ :=
      Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
    have e₀ : s₅.mem.read (W + BitVec.ofNat 64 Impl.AesGcm.AArch64.Fast.hO) 16 = s₄.v (tReg 1) := by
      rw [m₅, he₄.x19]
      rw [((Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)).read
        (Region.contains_self _ _) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact d₀₁)
        (by decide), read_write16]
    have e₁ : s₅.mem.read (W + BitVec.ofNat 64 (Impl.AesGcm.AArch64.Fast.hO + 16)) 16 = s₄.v (sReg 1) := by
      rw [m₅, he₄.x19, read_write16]
    exact ⟨by rw [e₀]; exact hk₄.t, by rw [e₁, e₀]; exact hk₄.sw⟩
  have hk₅ : HKey H s₅ := hk₄.of_v (v₅ C (by decide)) (v₅ _ (by decide)) (v₅ _ (by decide))
  have g₅' : ∀ r ∈ [Reg.x25, .x27, .x23, .x26], s₅.gpr r = s₁'.gpr r := fun r hr => by
    rw [g₅, g₄ r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide)
      (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide)
      (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide),
      r₃.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), v₂ r hr]
  obtain ⟨s₆, run₆, x13₆, x12₆, r₆, v₆⟩ : ∃ s₆, runBlock isa [mov .x13 .x25, mov .x12 .x27] s₅ =
      some s₆ ∧ s₆.gpr .x13 = BitVec.ofNat 64 al ∧ s₆.gpr .x12 = A ∧ Regs [.x13, .x12] s₅ s₆ ∧ s₆.v = s₅.v := by
    refine ⟨_, by arun [], ?_⟩
    exact ⟨by simp [gpr_write, g₅' .x25 (by simp), x25₁'], by simp [gpr_write, g₅' .x27 (by simp), x27₁'],
      ⟨by others_tac, rfl, rfl, rfl, rfl⟩, rfl⟩
  refine WP.of_runBlock ⟨s₆, run₆, ?_⟩
  have he₆ := he₅.of_regs r₆
  have hk₆ : HKey H s₆ := hk₅.of_v (by rw [v₆]) (by rw [v₆]) (by rw [v₆])
  have hy₆ : s₆.v Y = ext8 0 0 := by rw [v₆, y₅, ext8_zero]
  -- The memory up to `s₆`, and the additional data in it.
  have F₆ : Frame (frontFrame' St W) s₀.mem s₆.mem := by
    rw [r₆.mem]
    refine (h₂.frame.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ h => h⟩).trans ?_
    rw [← r₃.mem, ← m₄]
    exact fk.sub fun r hr => ⟨r, List.mem_append_right _ hr, fun _ h => h⟩
  have dA : ∀ r ∈ frontFrame' St W, (⟨A, al⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | rfl
    · exact haad.st
    · exact haad.w.sub_right (Lay.wSub (by decide))
    · exact haad.w.sub_right (Lay.wSub (by decide))
    · exact haad.w.sub_right (Lay.wSub (by decide))
  have hA₆ : bytesAt s₆.mem A al = bytesAt s₀.mem A al := bytesAt_frame F₆ dA (by have := haad.lt; omega)
  refine WP.seq (WP.mono (WP.with_rdwr (padMul_ok hMK he₆ hk₆ hy₆ x12₆ x13₆ hal
      (by rw [r₆.rd, r₆.wr, rd₅, wr₅, rd₄, wr₄, r₃.rd, r₃.wr, rd₂, wr₂, r₁'.rd, r₁'.wr, rd₁, wr₁]; exact haad.rd)
      (haad.w.sub_right (Lay.wSub (by decide)))))
    fun s₇ ⟨⟨y₇, hk₇, he₇, og₇, f₇, v₇⟩, rd₇, wr₇⟩ => ?_)
  refine WP.mono (storeY_ok y₇ (by rw [he₇.x20]; exact he₇.perm.stW (by decide)))
    fun s₈ ⟨m₈, b₈, o₈⟩ => ?_
  have f₈ : Frame [⟨St + BitVec.ofNat 64 16, 16⟩] s₇.mem s₈.mem := by
    rw [m₈, he₇.x20]; exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have g₈ : s₈.gpr = s₇.gpr := o₈.gpr
  -- What `front` writes after `J₀`.
  have F₅₈ : Frame [⟨W + BitVec.ofNat 64 96, 16⟩, ⟨St + BitVec.ofNat 64 16, 16⟩] s₅.mem s₈.mem := by
    rw [← r₆.mem]
    exact (f₇.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inl hr, fun _ h => h⟩).trans
      (f₈.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inr hr, fun _ h => h⟩)
  have F₂₈ : Frame [keyR W, ⟨W + BitVec.ofNat 64 96, 16⟩, ⟨St + BitVec.ofNat 64 16, 16⟩] s₂.mem s₈.mem := by
    have fk' : Frame [keyR W] s₂.mem s₅.mem := by rw [← r₃.mem, ← m₄]; exact fk
    refine (fk'.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inl hr, fun _ h => h⟩).trans
      (F₅₈.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inr hr, fun _ h => h⟩)
  have F₈ : Frame (frontFrame' St W) s₀.mem s₈.mem := by
    refine (h₂.frame.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ h => h⟩).trans (F₂₈.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), fun _ h => h⟩
    · exact ⟨_, List.mem_append_left _ (by simp), fun _ h => h⟩
    · exact ⟨⟨St, 80⟩, List.mem_append_left _ (by simp), Lay.stSub (by decide)⟩
  have dJ : ∀ {e : Nat}, e = 0 ∨ e = 48 → ∀ r ∈ [keyR W, ⟨W + BitVec.ofNat 64 96, 16⟩,
      ⟨St + BitVec.ofNat 64 16, 16⟩], (⟨St + BitVec.ofNat 64 e, 16⟩ : Region).Disjoint r := by
    intro e he r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
    · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
    · exact L.st_st (by omega) (by omega) (by decide)
  have gg : ∀ r, r ∉ [Reg.x0, .x5, .x6, .x7, .x9, .x11, .x12, .x13, .x14, .x15] → s₈.gpr r = s₂.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h0, h5, h6, h7, h9, h11, h12, h13, h14, h15⟩ := hr
    rw [g₈, og₇ r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h9, h11, h12, h13, h14, h15⟩),
      r₆.others r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h13, h12⟩),
      g₅, g₄ r h5 h6 h7, r₃.others r (by simp only [List.mem_singleton]; exact h0)]
  refine ⟨he₇.keep (fun r _ => by rw [g₈]) o₈.sp o₈.rd o₈.wr, by rw [gg _ (by decide), kg₂ _ (by decide)],
    by rw [gg _ (by decide), kg₂ _ (by decide)], by rw [gg _ (by decide), v₂ _ (by simp), x23₁'],
    by rw [gg _ (by decide), v₂ _ (by simp), x26₁'], ?_, ?_, ?_, ?_, ?_, F₈, ?_, ?_⟩
  · rw [blockAt_frame F₈ (fun r hr => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl | rfl) | rfl
      · exact L.cs.sub_left (Lay.ctxSub (by decide))
      · exact L.ctx_w (by decide) (by decide)
      · exact L.ctx_w (by decide) (by decide)
      · exact L.ctx_w (by decide) (by decide)), hJ.hH]
  · rw [show St = St + BitVec.ofNat 64 0 by simp, blockAt_frame F₂₈ (dJ (.inl rfl)), ← show St = St + BitVec.ofNat 64 0 by simp,
      h₂.j0]
  · rw [blockAt_frame F₂₈ (dJ (.inr rfl)), h₂.cb]
  · rw [← he₇.x20, b₈, hA₆, ← ghashFrom_pad H 0 (by rw [length_bytesAt]; exact hal), length_bytesAt]; rfl
  · refine key₅.frame F₅₈ fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint W (.inr (by decide)) (by decide) (by decide)
    · exact (L.st_w (a := 16) (n := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · rw [o₈.rd, rd₇, r₆.rd, rd₅, rd₄, r₃.rd, rd₂, r₁'.rd, rd₁]
  · rw [o₈.wr, wr₇, r₆.wr, wr₅, wr₄, r₃.wr, wr₂, r₁'.wr, wr₁]

end

end VG.Proof.AesGcm.AArch64.Fast
