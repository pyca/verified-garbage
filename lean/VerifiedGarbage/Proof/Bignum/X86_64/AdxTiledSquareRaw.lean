module
import VerifiedGarbage.Proof.Framework.OmegaNear
public import VerifiedGarbage.Impl.Bignum.X86_64.AdxTiledSquare
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareCross
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledInit

import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareChoice
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRaw
import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderFrame
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareDiagonalChoice
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow

/-! ## AdxTiledSquareCross -/

@[expose] public section

section

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxTiledProduct (ranges)
open VG.Proof.Bignum.X86_64.AdxRect8 (rawBase)
open VG.Proof.MlKem.X86_64 (Keep)

private theorem cross_congr {r n : Nat} {f g : Nat → Nat}
    (h : ∀ j<n, f j=g j) : Square.cross r f n=Square.cross r g n := by
  have val (k : Nat) (hk : k≤n) : Square.value r f k=Square.value r g k := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Square.value,Square.value,ih (by omega_near),h k (by omega_near)]
  induction n with
  | zero => rfl
  | succ n ih => rw [Square.cross,Square.cross,ih (fun j hj => h j (by omega_near)) (fun k hk => val k (by omega_near)),val n (by omega_near),h n (by omega_near)]

theorem crossBody_ok {s : State} {B : Addr} {Z w a n : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi=B) (hh : Hdr s.mem B w mi) (hZ : slot w 8≤Z)
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {ca : Nat} (pa : (ca, a) ∈ ps)
    (hw : w<2^31) (hwN : w=8*n) (hn : 0<n)
    (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp) :
    WP isa (.seq (AdxTri8.blocks ca) (AdxTiledSquare.rowsChoice ca)) s fun t =>
      wv t.mem B (rawBase w) (2*w)=AdxSquare.crossValue s.mem B (slot w a) w ∧
      Hdr t.mem B w mi ∧ Frm B (ranges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have nowrap := hs.nowrap
  refine WP.seq (WP.mono (AdxTri8.blocks_ok hs hd hh hZ hv pa hw hwN hn ha ha1 ha2) fun u hu => ?_)
  have fu : Frm B (ranges w) s.mem u.mem := by
    intro p hp
    apply hu.frame p
    intro r hr
    simp only [AdxTri8.diagonalRanges,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · have h := hp (rawBase w,16*w) (by simp [ranges])
      simp only [] at *; omega_near
    · have h := hp (8*sFn 12,32) (by simp [ranges])
      simp only [] at *; omega_near
  refine WP.mono (rowsChoice_ok hu.scr hu.rdi hu.hdr hZ (AdxTri8.diagonal_ops hv hu.frame) pa hw hwN hn ha ha1 ha2) fun t ⟨⟨c,vc⟩,ht,ft,kt⟩ => ?_
  have chunksEq : ∀ j<n, AdxTri8.chunks u.mem B (slot w a) j=AdxTri8.chunks s.mem B (slot w a) j := by
    intro j hj
    unfold AdxTri8.chunks
    rw [show 64*j=8*(8*j) by omega_near]
    exact AdxTiledProduct.input_preserved ha ha1 ha2 (by omega_near) (by omega_near) fu
  have crossEq : Square.cross (2^512) (AdxTri8.chunks u.mem B (slot w a)) n=
      Square.cross (2^512) (AdxTri8.chunks s.mem B (slot w a)) n := by
    apply cross_congr
    exact chunksEq
  have vu := hu.val
  rw [show 16*n=2*w by omega_near] at vu
  rw [vu,crossEq,← AdxTri8.chunks_cross,← hwN] at vc
  have dec := AdxSquare.square_decomposition s.mem B (slot w a) w
  have bound : wv s.mem B (slot w a) w*wv s.mem B (slot w a) w<2^(128*w) := by
    have h := Nat.mul_lt_mul'' (wv_lt s.mem B (slot w a) w) (wv_lt s.mem B (slot w a) w)
    rw [← Nat.pow_add,show 64*w+64*w=128*w by omega_near] at h
    exact h
  have cz : c=0 := by
    by_contra hc
    have h := Nat.mul_le_mul_left (2^(128*w)) (show 1≤c by omega_near)
    simp only [Nat.mul_one] at h
    omega_near
  rw [cz,Nat.mul_zero,Nat.add_zero] at vc
  exact ⟨vc,ht,fu.trans ft,(hu.keep.trans kt).mono (by decide)⟩

end VG.Proof.Bignum.X86_64.AdxTiledSquare

end

/-! ## AdxTiledSquareRawCross -/
section

/-! Full raw cross product with every borrowed header byte restored. -/
namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.Bignum.X86_64.AdxRect8 (rawBase)
open VG.Proof.Bignum.X86_64.AdxHeader (highPad)

theorem rawCross_ok {s : State} {B : Addr} {Z w a n : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hh : Hdr s.mem B w mi)
    {ps : List (Nat × Nat)} (hvs : Ops s.mem B w ps) {ca : Nat} (pa : (ca, a) ∈ ps)
    (hZ : slot w 8 ≤ Z) (hw : w < 2^31) (hwN : w=8*n) (hn : 0<n)
    (ha : a < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) :
    WP isa (AdxTiledSquare.rawCross ca) s fun t =>
      wv t.mem B (rawBase w) (2*w+2)=AdxSquare.crossValue s.mem B (slot w a) w ∧
      wv t.mem B (rawBase w) (2*w)=AdxSquare.crossValue s.mem B (slot w a) w ∧
      Outside B (slot w aAcc) (16*w+32) s.mem t.mem ∧ Keep mmRegs s t := by
  have nowrap := hs.nowrap
  have pads := AdxHeader.pads_bound hZ
  have rawZ : rawBase w+8*(2*w+2) ≤ Z := by unfold rawBase highPad at *; omega_near
  have Z64 : slot w 8 ≤ (2 : Nat)^64 := by omega_near
  unfold AdxTiledSquare.rawCross
  refine WP.seq (WP.mono (adxSetupV_ok hs hd hh hZ (hvs.at pa) (hvs.lt pa)) fun u ⟨_,_,pu,wu,mu,ku⟩ => ?_)
  have ov' : Outside B (slot w aAcc) (16*w+32) s.mem u.mem := by rw [mu]; exact Outside.refl _ _ _ _
  have hv : Hdr u.mem B w mi := mu ▸ hh
  have kuv := ku
  refine WP.seq (WP.mono (AdxHeader.save_ok (hs.congr kuv.2.2) ((kuv.gpr (by decide)).trans hd) hv hZ)
    fun x ⟨lo,hi,fx,kx⟩ => ?_)
  have ox : Outside B (slot w aAcc) (16*w+32) u.mem x.mem := by
    intro p hp
    apply fx p
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> simp only [] <;> unfold highPad at * <;> omega_near
  have hx : Hdr x.mem B w mi := hv.of_outside ox (by unfold slot; omega_near)
  have kuvx := kuv.trans kx
  change WP isa (.seq (.seq (AdxTri8.blocks ca) (AdxTiledSquare.rowsChoice ca)) AdxHeader.restore) x _
  refine WP.seq (WP.mono (crossBody_ok (hs.congr kuvx.2.2) ((kuvx.gpr (by decide)).trans hd)
    hx hZ (hvs.of_outside (ov'.trans ox) (by unfold slot sFn hdrBytes; omega_near)) pa hw hwN hn ha ha1 ha2) fun y ⟨vy,hy,fy,ky⟩ => ?_)
  have kuvxy := kuvx.trans ky
  refine WP.mono (AdxHeader.restore_ok (hs.congr kuvxy.2.2) ((kuvxy.gpr (by decide)).trans hd) hy hZ)
    fun t ⟨lot,hit,zt,ft,kt⟩ => ?_
  have bodyFrame : Frm B [(slot w aAcc+16,16*w),(8*sFn 12,32)] x.mem y.mem := fy
  have restored := AdxHeader.restored_frame (by omega_near : highPad w+16 ≤ 2^64) lo hi fx bodyFrame lot hit ft
  have low : wv t.mem B (rawBase w) (2*w)=AdxSquare.crossValue s.mem B (slot w a) w := by
    rw [ft.wv_eq (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl <;> simp only [] <;>
        simp only [rawBase,highPad,slot,hdrBytes,sFn] <;> omega_near) (by omega_near),vy,
      ]
    apply AdxSquare.crossValue_congr
    intro j hj
    have sa := slot_le (w := w) ha
    have s1 := slot_sep (w := w) ha1
    have s2 := slot_sep (w := w) ha2
    exact (ov'.trans ox).word (by unfold slot aAcc aTmp at *; omega_near) (by omega_near)
  refine ⟨?_,low,ov'.trans restored,(kuvxy.trans kt).mono (by decide)⟩
  have high : wv t.mem B (rawBase w+8*(2*w)) 2=0 := wv_zero fun k hk => by
    rw [show rawBase w+8*(2*w)+8*k=highPad w+8*k by unfold rawBase highPad; omega_near]
    exact zt k hk
  rw [wv_add,high,Nat.mul_zero,Nat.add_zero]; exact low


/-- `rawCross` without the header's save: the borrowed words change too. -/
theorem rawCrossBare_ok {s : State} {B : Addr} {Z w a n : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hh : Hdr s.mem B w mi)
    {ps : List (Nat × Nat)} (hvs : Ops s.mem B w ps) {ca : Nat} (pa : (ca, a) ∈ ps)
    (hZ : slot w 8 ≤ Z) (hw : w < 2^31) (hwN : w=8*n) (hn : 0<n)
    (ha : a < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) :
    WP isa (AdxTiledSquare.rawCrossBare ca) s fun t =>
      wv t.mem B (rawBase w) (2*w+2)=AdxSquare.crossValue s.mem B (slot w a) w ∧
      wv t.mem B (rawBase w) (2*w)=AdxSquare.crossValue s.mem B (slot w a) w ∧
      Frm B [(slot w aAcc,16*w+32),(8*sFn 12,32)] s.mem t.mem ∧ Keep mmRegs s t := by
  have nowrap := hs.nowrap
  have pads := AdxHeader.pads_bound hZ
  unfold AdxTiledSquare.rawCrossBare
  refine WP.seq (WP.mono (adxSetupV_ok hs hd hh hZ (hvs.at pa) (hvs.lt pa)) fun u ⟨_,_,_,_,mu,ku⟩ => ?_)
  refine WP.seq (WP.mono (crossBody_ok (hs.congr ku.2.2) ((ku.gpr (by decide)).trans hd)
    (mu ▸ hh) hZ (mu ▸ hvs) pa hw hwN hn ha ha1 ha2) fun y ⟨vy,hy,fy,ky⟩ => ?_)
  have kuy := ku.trans ky
  refine WP.mono (AdxHeader.clear_ok (hs.congr kuy.2.2) ((kuy.gpr (by decide)).trans hd) hy hZ)
    fun t ⟨zt,ot,kt⟩ => ?_
  rw [mu] at vy fy
  have low : wv t.mem B (rawBase w) (2*w)=AdxSquare.crossValue s.mem B (slot w a) w := by
    rw [ot.wv (by unfold rawBase highPad; omega_near) (by unfold rawBase highPad at *; omega_near)]; exact vy
  refine ⟨?_,low,fun x hx => ?_,(kuy.trans kt).mono (by decide)⟩
  · have high : wv t.mem B (rawBase w+8*(2*w)) 2=0 := wv_zero fun k hk => by
      rw [show rawBase w+8*(2*w)+8*k=highPad w+8*k by unfold rawBase highPad; omega_near]
      exact zt k hk
    rw [wv_add,high,Nat.mul_zero,Nat.add_zero]; exact low
  · have h1 := hx _ (List.mem_cons_self ..)
    have h2 := hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    simp only [] at h1 h2
    rw [ot x (by unfold highPad; omega_near)]
    exact fy x fun r hr => by
      simp only [AdxTiledProduct.ranges,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl <;> simp only [rawBase] <;> omega_near

end VG.Proof.Bignum.X86_64.AdxTiledSquare

end

/-! ## AdxTiledSquareRaw -/
section

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxSquare
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

/-- The diagonal, after a cross product from `s` that changed only the
accumulator. -/
theorem diagonal_ok {s s₂ : State} {B : Addr} {Z w n : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (hwN : w=8*n) (hnN : 0<n) (hw : w < 2 ^ 31)
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {ca a : Nat} (pa : (ca, a) ∈ ps)
    (ha : a < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    (full₂ : wv s₂.mem B (AdxRect8.rawBase w) (2*w+2)=AdxSquare.crossValue s.mem B (slot w a) w)
    (lo₂ : wv s₂.mem B (AdxRect8.rawBase w) (2*w)=AdxSquare.crossValue s.mem B (slot w a) w)
    (ho₂ : Outside B (slot w aAcc) (16*w+32) s.mem s₂.mem) (k12 : Keep mmRegs s s₂) :
    WP isa (AdxTiledSquare.diagonal ca) s₂ fun t =>
      wv t.mem B (slot w aAcc + 16) (2 * w + 2) =
        wv s.mem B (slot w a) w * wv s.mem B (slot w a) w ∧
      wv t.mem B (slot w aAcc + 16) (2 * w) =
        wv s.mem B (slot w a) w * wv s.mem B (slot w a) w ∧
      Outside B (slot w aAcc) (16*w+32) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  let A := slot w aAcc + 16
  let eb := slot w a
  have hA : A + 8 * (2 * w + 2) ≤ Z := by
    have := slot_le (w := w) (show aTmp < 8 by decide)
    unfold A slot aAcc aTmp at *
    omega_near
  have hb : eb + 8 * w ≤ Z := by have := slot_le (w := w) ha; omega_near
  have sb : eb + 8 * w ≤ A ∨ A + 8 * (2 * w + 2) ≤ eb := by
    have := slot_sep (w := w) ha1
    have := slot_sep (w := w) ha2
    unfold A eb slot aAcc aTmp at *
    omega_near
  have hg : hdrBytes ≤ A := by unfold A slot; omega_near
  unfold AdxTiledSquare.diagonal
  dsimp only [AdxRect8.rawBase] at full₂ lo₂
  have hs₂ := hs.congr k12.2.2
  have hH₂ := hH.of_outside ho₂ (by unfold slot; omega_near)
  have read₂ : ∀ j < w, word s₂.mem B (eb + 8 * j) = word s.mem B (eb + 8 * j) := by
    intro j hj
    have := slot_sep (w := w) ha1
    have := slot_sep (w := w) ha2
    exact ho₂.word (by unfold eb slot aAcc aTmp at *; omega_near) (by omega_near)
  have hz₂ : wv s₂.mem B (A+8*(2*w)) 2=0 := by
    rw [wv_add,lo₂] at full₂
    have pos : 0<2^(64*(2*w)) := Nat.two_pow_pos _
    have zero : 2^(64*(2*w))*wv s₂.mem B (A+8*(2*w)) 2=0 := by
      dsimp only [A]
      omega_near
    exact (Nat.mul_eq_zero.mp zero).resolve_left (by omega_near)
  have hv₂ : Ops s₂.mem B w ps := hv.of_outside ho₂ (by unfold slot sFn hdrBytes; omega_near)
  refine WP.seq (WP.mono (adxSetupV_ok hs₂ ((k12.gpr (by decide)).trans hdi) hH₂ hZ (hv₂.at pa) (hv₂.lt pa))
    fun s₃ ⟨h9₃, _, h8₃, hbx₃, hm₃, k₃⟩ => ?_)
  have mov : WP isa (.block [.mov .r10 (.reg .rbx)]) s₃ fun t =>
      t.gpr .r10 = BitVec.ofNat 64 w ∧ t.mem = s₃.mem ∧ Keep [.r10] s₃ t := by
    refine WP.mono (WP.keep [.r10] (Q := fun t => t.gpr .r10 = BitVec.ofNat 64 w ∧ t.mem = s₃.mem)
      (by xrun [hbx₃]) rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  refine WP.seq (WP.mono mov fun s₄ ⟨h10₄, hm₄, k₄⟩ => ?_)
  have k14 := (k12.trans k₃).trans k₄
  refine WP.mono (AdxSquareGrouped.diagonal8_ok (hs.congr k14.2.2) ((k₄.gpr (by decide)).trans h8₃)
    ((k₄.gpr (by decide)).trans h9₃) h10₄ (by omega_near) (by omega_near) (by omega_near) (by omega_near) hb (by omega_near))
    fun t ⟨hv, ho, kt⟩ => ?_
  rw [hm₄, hm₃] at hv ho
  rw [lo₂, diagonalValue_congr read₂, square_decomposition] at hv
  have bound : wv s.mem B eb w * wv s.mem B eb w < 2 ^ (128 * w) := by
    have hl := wv_lt s.mem B eb w
    have hp := Nat.mul_lt_mul'' hl hl
    rw [← Nat.pow_add, show 64 * w + 64 * w = 128 * w by omega_near] at hp
    exact hp
  dsimp only [eb] at bound
  have carry : (t.gpr .r15).toNat = 0 := by
    by_contra hc
    have hc' : 1 ≤ (t.gpr .r15).toNat := by omega_near
    have hm := Nat.mul_le_mul_left (2 ^ (128 * w)) hc'
    simp only [Nat.mul_one] at hm
    omega_near
  have low : wv t.mem B A (2 * w) = wv s.mem B eb w * wv s.mem B eb w := by
    rw [carry, Nat.mul_zero, Nat.add_zero] at hv
    exact hv
  have high : wv t.mem B (A + 8 * (2 * w)) 2 = 0 := by
    rw [ho.wv (by omega_near) (by omega_near)]
    exact hz₂
  refine ⟨?_, low, ho₂.trans (ho.mono (o' := slot w aAcc) (n' := 16*w+32) (by omega_near) (by omega_near)),
    (k14.trans kt).mono (by decide)⟩
  rw [wv_add, high, Nat.mul_zero, Nat.add_zero]
  exact low

theorem rawSquare_ok {s : State} {B : Addr} {Z w n : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (hwN : w=8*n) (hnN : 0<n) (hw : w < 2 ^ 31)
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {ca a : Nat} (pa : (ca, a) ∈ ps)
    (ha : a < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) :
    WP isa (AdxTiledSquare.rawSquare ca) s fun t =>
      wv t.mem B (slot w aAcc + 16) (2 * w + 2) =
        wv s.mem B (slot w a) w * wv s.mem B (slot w a) w ∧
      wv t.mem B (slot w aAcc + 16) (2 * w) =
        wv s.mem B (slot w a) w * wv s.mem B (slot w a) w ∧
      Outside B (slot w aAcc) (16*w+32) s.mem t.mem ∧ Keep mmRegs s t := by
  unfold AdxTiledSquare.rawSquare
  exact WP.seq (WP.mono (rawCross_ok hs hdi hH hv pa hZ hw hwN hnN ha ha1 ha2)
    fun _ ⟨full₂,lo₂,ho₂,k12⟩ => diagonal_ok hs hdi hH hZ hwN hnN hw hv pa ha ha1 ha2 full₂ lo₂ ho₂ k12)

/-- `rawSquare` without the header's save: the borrowed words change too,
as from `s` to a memory `m`, which the rest changes only in the accumulator. -/
theorem rawSquareBare_ok {s : State} {B : Addr} {Z w n : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (hwN : w=8*n) (hnN : 0<n) (hw : w < 2 ^ 31)
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {ca a : Nat} (pa : (ca, a) ∈ ps)
    (ha : a < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) :
    WP isa (AdxTiledSquare.rawSquareBare ca) s fun t => ∃ m,
      Outside B (8*sFn 12) 32 s.mem m ∧
      wv t.mem B (slot w aAcc + 16) (2 * w) =
        wv s.mem B (slot w a) w * wv s.mem B (slot w a) w ∧
      Outside B (slot w aAcc) (16*w+32) m t.mem ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  have sa := slot_le (w := w) ha
  have s0 : 8*sFn 12+32 ≤ slot w a := by unfold slot sFn hdrBytes; omega_near
  unfold AdxTiledSquare.rawSquareBare
  refine WP.seq (WP.mono (rawCrossBare_ok hs hdi hH hv pa hZ hw hwN hnN ha ha1 ha2)
    fun s₂ ⟨full₂,lo₂,fr,k12⟩ => ?_)
  obtain ⟨m₁,o₁,o₂⟩ := AdxHeader.frm_split fr
  have cv : AdxSquare.crossValue m₁ B (slot w a) w=AdxSquare.crossValue s.mem B (slot w a) w := by
    apply AdxSquare.crossValue_congr
    intro j hj
    exact o₁.word (Or.inr (by omega_near)) (by omega_near)
  have va : wv m₁ B (slot w a) w=wv s.mem B (slot w a) w := o₁.wv (Or.inr (by omega_near)) (by omega_near)
  refine WP.mono (diagonal_ok (s := {s with mem := m₁}) (hs.congr rfl) hdi
    (hH.of_outside_fn o₁ (by unfold sFn; omega_near)) hZ hwN hnN hw (hv.of_outside o₁ (Nat.le_refl _)) pa ha ha1 ha2
    (full₂.trans cv.symm) (lo₂.trans cv.symm) o₂ k12) fun t ⟨_,lo,ho,kt⟩ => ?_
  refine ⟨m₁,o₁,?_,ho,kt⟩
  rw [lo]; dsimp only; rw [va]

end VG.Proof.Bignum.X86_64.AdxTiledSquare

end
