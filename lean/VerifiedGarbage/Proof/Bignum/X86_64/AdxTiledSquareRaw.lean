import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareChoice
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRaw
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRaw
import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderFrame

/-! ## AdxTiledSquareCross -/
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
    | succ k ih => rw [Square.value,Square.value,ih (by omega),h k (by omega)]
  induction n with
  | zero => rfl
  | succ n ih => rw [Square.cross,Square.cross,ih (fun j hj => h j (by omega)) (fun k hk => val k (by omega)),val n (by omega),h n (by omega)]

theorem crossBody_ok {s : State} {B : Addr} {Z w a n : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi=B) (hh : Hdr s.mem B w mi) (hZ : slot w 8≤Z)
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {ca : Nat} (pa : (ca, a) ∈ ps)
    (hw : w<2^31) (hwN : w=8*n) (hn : 0<n)
    (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    (hz : ∀ j<2*w, word s.mem B (rawBase w+8*j)=0) :
    WP isa (.seq (AdxTri8.blocks ca) (AdxTiledSquare.rowsChoice ca)) s fun t =>
      wv t.mem B (rawBase w) (2*w)=AdxSquare.crossValue s.mem B (slot w a) w ∧
      Hdr t.mem B w mi ∧ Frm B (ranges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have nowrap := hs.nowrap
  refine WP.seq (WP.mono (AdxTri8.blocks_ok hs hd hh hZ hv pa hw hwN hn ha ha1 ha2 hz) fun u hu => ?_)
  have fu : Frm B (ranges w) s.mem u.mem := by
    intro p hp
    apply hu.frame p
    intro r hr
    simp only [AdxTri8.diagonalRanges,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · have h := hp (rawBase w,16*w) (by simp [ranges])
      simp only [] at *; omega
    · have h := hp (8*sFn 12,32) (by simp [ranges])
      simp only [] at *; omega
  refine WP.mono (rowsChoice_ok hu.scr hu.rdi hu.hdr hZ (AdxTri8.diagonal_ops hv hu.frame) pa hw hwN hn ha ha1 ha2) fun t ⟨⟨c,vc⟩,ht,ft,kt⟩ => ?_
  have chunksEq : ∀ j<n, AdxTri8.chunks u.mem B (slot w a) j=AdxTri8.chunks s.mem B (slot w a) j := by
    intro j hj
    unfold AdxTri8.chunks
    rw [show 64*j=8*(8*j) by omega]
    exact AdxTiledProduct.input_preserved ha ha1 ha2 (by omega) (by omega) fu
  have crossEq : Square.cross (2^512) (AdxTri8.chunks u.mem B (slot w a)) n=
      Square.cross (2^512) (AdxTri8.chunks s.mem B (slot w a)) n := by
    apply cross_congr
    exact chunksEq
  have vu := hu.val
  rw [show 16*n=2*w by omega] at vu
  rw [vu,crossEq,← AdxTri8.chunks_cross,← hwN] at vc
  have dec := AdxSquare.square_decomposition s.mem B (slot w a) w
  have bound : wv s.mem B (slot w a) w*wv s.mem B (slot w a) w<2^(128*w) := by
    have h := Nat.mul_lt_mul'' (wv_lt s.mem B (slot w a) w) (wv_lt s.mem B (slot w a) w)
    rw [← Nat.pow_add,show 64*w+64*w=128*w by omega] at h
    exact h
  have cz : c=0 := by
    by_contra hc
    have h := Nat.mul_le_mul_left (2^(128*w)) (show 1≤c by omega)
    simp only [Nat.mul_one] at h
    omega
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
  have rawZ : rawBase w+8*(2*w+2) ≤ Z := by unfold rawBase highPad at *; omega
  have Z64 : slot w 8 ≤ (2 : Nat)^64 := by omega
  unfold AdxTiledSquare.rawCross
  refine WP.seq (WP.mono (adxSetupV_ok hs hd hh hZ (hvs.at pa) (hvs.lt pa)) fun u ⟨_,_,pu,wu,mu,ku⟩ => ?_)
  refine WP.seq (WP.mono (zeroWin8_ok (hs.congr ku.2.2) pu wu hwN hn (by omega) rawZ)
    fun v ⟨zv,ov,kv⟩ => ?_)
  rw [mu] at ov
  have ov' : Outside B (slot w aAcc) (16*w+32) s.mem v.mem := ov.mono (by omega) (by omega)
  have hv : Hdr v.mem B w mi := hh.of_outside ov (by unfold slot; omega)
  have kuv := ku.trans kv
  refine WP.seq (WP.mono (AdxHeader.save_ok (hs.congr kuv.2.2) ((kuv.gpr (by decide)).trans hd) hv hZ)
    fun x ⟨lo,hi,fx,kx⟩ => ?_)
  have ox : Outside B (slot w aAcc) (16*w+32) v.mem x.mem := by
    intro p hp
    apply fx p
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> simp only [] <;> unfold highPad at * <;> omega
  have hx : Hdr x.mem B w mi := hv.of_outside ox (by unfold slot; omega)
  have zx : ∀ j<2*w, word x.mem B (rawBase w+8*j)=0 := by
    intro j hj
    rw [fx.word_eq (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl <;> simp only [] <;> simp only [rawBase,highPad] <;> omega) (by omega)]
    exact zv j (by omega)
  have kuvx := kuv.trans kx
  change WP isa (.seq (.seq (AdxTri8.blocks ca) (AdxTiledSquare.rowsChoice ca)) AdxHeader.restore) x _
  refine WP.seq (WP.mono (crossBody_ok (hs.congr kuvx.2.2) ((kuvx.gpr (by decide)).trans hd)
    hx hZ (hvs.of_outside (ov'.trans ox) (by unfold slot sFn hdrBytes; omega)) pa hw hwN hn ha ha1 ha2 zx) fun y ⟨vy,hy,fy,ky⟩ => ?_)
  have kuvxy := kuvx.trans ky
  refine WP.mono (AdxHeader.restore_ok (hs.congr kuvxy.2.2) ((kuvxy.gpr (by decide)).trans hd) hy hZ)
    fun t ⟨lot,hit,zt,ft,kt⟩ => ?_
  have bodyFrame : Frm B [(slot w aAcc+16,16*w),(8*sFn 12,32)] x.mem y.mem := fy
  have restored := AdxHeader.restored_frame (by omega : highPad w+16 ≤ 2^64) lo hi fx bodyFrame lot hit ft
  have low : wv t.mem B (rawBase w) (2*w)=AdxSquare.crossValue s.mem B (slot w a) w := by
    rw [ft.wv_eq (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl <;> simp only [] <;>
        simp only [rawBase,highPad,slot,hdrBytes,sFn] <;> omega) (by omega),vy,
      ]
    apply AdxSquare.crossValue_congr
    intro j hj
    have sa := slot_le (w := w) ha
    have s1 := slot_sep (w := w) ha1
    have s2 := slot_sep (w := w) ha2
    exact (ov'.trans ox).word (by unfold slot aAcc aTmp at *; omega) (by omega)
  refine ⟨?_,low,ov'.trans restored,(kuvxy.trans kt).mono (by decide)⟩
  have high : wv t.mem B (rawBase w+8*(2*w)) 2=0 := wv_zero fun k hk => by
    rw [show rawBase w+8*(2*w)+8*k=highPad w+8*k by unfold rawBase highPad; omega]
    exact zt k hk
  rw [wv_add,high,Nat.mul_zero,Nat.add_zero]; exact low

end VG.Proof.Bignum.X86_64.AdxTiledSquare

end

/-! ## AdxTiledSquareRaw -/
section

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxSquare
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

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
  have hn := hs.nowrap
  let A := slot w aAcc + 16
  let eb := slot w a
  have hA : A + 8 * (2 * w + 2) ≤ Z := by
    have := slot_le (w := w) (show aTmp < 8 by decide)
    unfold A slot aAcc aTmp at *
    omega
  have hb : eb + 8 * w ≤ Z := by have := slot_le (w := w) ha; omega
  have sb : eb + 8 * w ≤ A ∨ A + 8 * (2 * w + 2) ≤ eb := by
    have := slot_sep (w := w) ha1
    have := slot_sep (w := w) ha2
    unfold A eb slot aAcc aTmp at *
    omega
  have hg : hdrBytes ≤ A := by unfold A slot; omega
  unfold AdxTiledSquare.rawSquare
  refine WP.seq (WP.mono (rawCross_ok hs hdi hH hv pa hZ hw hwN hnN ha ha1 ha2)
    fun s₂ ⟨full₂,lo₂,ho₂,k12⟩ => ?_)
  dsimp only [AdxRect8.rawBase] at full₂ lo₂
  have hs₂ := hs.congr k12.2.2
  have hH₂ := hH.of_outside ho₂ (by unfold slot; omega)
  have read₂ : ∀ j < w, word s₂.mem B (eb + 8 * j) = word s.mem B (eb + 8 * j) := by
    intro j hj
    have := slot_sep (w := w) ha1
    have := slot_sep (w := w) ha2
    exact ho₂.word (by unfold eb slot aAcc aTmp at *; omega) (by omega)
  have hz₂ : wv s₂.mem B (A+8*(2*w)) 2=0 := by
    rw [wv_add,lo₂] at full₂
    have pos : 0<2^(64*(2*w)) := Nat.two_pow_pos _
    have zero : 2^(64*(2*w))*wv s₂.mem B (A+8*(2*w)) 2=0 := by
      dsimp only [A]
      omega
    exact (Nat.mul_eq_zero.mp zero).resolve_left (by omega)
  have hv₂ : Ops s₂.mem B w ps := hv.of_outside ho₂ (by unfold slot sFn hdrBytes; omega)
  refine WP.seq (WP.mono (adxSetupV_ok hs₂ ((k12.gpr (by decide)).trans hdi) hH₂ hZ (hv₂.at pa) (hv₂.lt pa))
    fun s₃ ⟨h9₃, _, h8₃, hbx₃, hm₃, k₃⟩ => ?_)
  have mov : WP isa (.block [.mov .r10 (.reg .rbx)]) s₃ fun t =>
      t.gpr .r10 = BitVec.ofNat 64 w ∧ t.mem = s₃.mem ∧ Keep [.r10] s₃ t := by
    refine WP.mono (WP.keep [.r10] (Q := fun t => t.gpr .r10 = BitVec.ofNat 64 w ∧ t.mem = s₃.mem)
      (by xrun [hbx₃]) rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  refine WP.seq (WP.mono mov fun s₄ ⟨h10₄, hm₄, k₄⟩ => ?_)
  have k14 := (k12.trans k₃).trans k₄
  refine WP.mono (diagonalChoice_ok (hs.congr k14.2.2) ((k₄.gpr (by decide)).trans h8₃)
    ((k₄.gpr (by decide)).trans h9₃) h10₄ (by omega) (by omega) (by omega) hb (by omega))
    fun t ⟨hv, ho, kt⟩ => ?_
  rw [hm₄, hm₃] at hv ho
  rw [lo₂, diagonalValue_congr read₂, square_decomposition] at hv
  have bound : wv s.mem B eb w * wv s.mem B eb w < 2 ^ (128 * w) := by
    have hl := wv_lt s.mem B eb w
    have hp := Nat.mul_lt_mul'' hl hl
    rw [← Nat.pow_add, show 64 * w + 64 * w = 128 * w by omega] at hp
    exact hp
  dsimp only [eb] at bound
  have carry : (t.gpr .r15).toNat = 0 := by
    by_contra hc
    have hc' : 1 ≤ (t.gpr .r15).toNat := by omega
    have hm := Nat.mul_le_mul_left (2 ^ (128 * w)) hc'
    simp only [Nat.mul_one] at hm
    omega
  have low : wv t.mem B A (2 * w) = wv s.mem B eb w * wv s.mem B eb w := by
    rw [carry, Nat.mul_zero, Nat.add_zero] at hv
    exact hv
  have high : wv t.mem B (A + 8 * (2 * w)) 2 = 0 := by
    rw [ho.wv (by omega) (by omega)]
    exact hz₂
  refine ⟨?_, low, ho₂.trans (ho.mono (o' := slot w aAcc) (n' := 16*w+32) (by omega) (by omega)),
    (k14.trans kt).mono (by decide)⟩
  rw [wv_add, high, Nat.mul_zero, Nat.add_zero]
  exact low

end VG.Proof.Bignum.X86_64.AdxTiledSquare

end
