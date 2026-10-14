module

public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemQuadK
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.Base

/-!
# The first blocks after the last group, through a mask, decrypted

`remQuadKD_ok`: as `remQuadK_ok`, for `StitchZH.remQuadKD src`: the blocks
at `src` are hashed as read, and their keystream added to them in `zmm13`,
whose `c` low lanes are written to `rdx`.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZH

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod)
open VG.Impl.Gcm.X86_64.Pclmul (at_)
open VG.Impl.Gcm.X86_64.StitchZH (remQuadKD)
open VG.Proof.Gcm.X86_64.StitchZ (restZ ldAcc ldAcc_ok)
open VG.Proof.Aes.X86_64.VaesZ (zmm_lane)
open VG.Proof.Gcm.X86_64 (revMask blockAt_eq)
open VG.Spec.Gcm (Block blockAt)

theorem remQuadKD_eq (src : Reg) :
    remQuadKD src = .kLoad .r10 .xmm12 (at_ .rax 0) :: .kLoad .r10 .xmm7 (at_ src 0) ::
      .kLoad .r10 .xmm13 (at_ .r11 768) :: .zop (.zbin .vpxord .xmm13 .xmm13 .xmm7) ::
      .kStore (at_ .rdx 0) .r10 .xmm13 :: (restZ 0 ++ ([.zop (.zbin .vpxord .xmm2 .xmm2 .xmm2)] : List Instr)) := rfl

/-- The first `c` blocks at `src`, with their keystream at `r11 + 768`,
decrypted to `rdx`, and the products of the blocks as read with their powers
at `rax` added to the lanes'; the other lanes' products with zero. -/
theorem remQuadKD_ok (src : Reg) (s : State) {c : Nat} (hc : c ≤ 4)
    (hk : State.qOn (s.gpr .r10) = List.range (2 * c))
    (hb : ∀ j < 8, (s.gpr .r10).getLsbD j = decide (j < 2 * c))
    (h0 : ∀ l < 4, s.zlane .xmm0 l = revMask)
    (hinS : InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofInt 64 ((0 : Nat) : Int)) (16 * c))
    (hinK : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofInt 64 ((768 : Nat) : Int)) (16 * c))
    (hinD : InRegions s.wr (s.gpr .rdx + BitVec.ofInt 64 ((0 : Nat) : Int)) (16 * c))
    (hinP : InRegions (s.rd ++ s.wr) (s.gpr .rax + BitVec.ofInt 64 ((0 : Nat) : Int)) (16 * c)) :
    WP isa (.block (remQuadKD src)) s fun s' =>
      (∃ v : BitVec 512,
        s'.mem = s.mem.writeW (s.gpr .rdx + BitVec.ofInt 64 ((0 : Nat) : Int)) (v.setWidth (128 * c))) ∧
      (∀ l < c, blockAt s'.mem (s.gpr .rdx + BitVec.ofInt 64 ((0 : Nat) : Int) + BitVec.ofNat 64 (16 * l)) =
        XBinOp.eval .pshufb
          (s.mem.readW (s.gpr .r11 + BitVec.ofInt 64 ((768 : Nat) : Int) + BitVec.ofNat 64 (16 * l)) 128 ^^^
            s.mem.readW (s.gpr src + BitVec.ofInt 64 ((0 : Nat) : Int) + BitVec.ofNat 64 (16 * l)) 128) revMask) ∧
      (∀ l < 4, prod (s'.zproj l) = (prod (s.zproj l)).acc
        (s.zlane .xmm2 l ^^^ XBinOp.eval .pshufb (if l < c then
          s.mem.readW (s.gpr src + BitVec.ofInt 64 ((0 : Nat) : Int) + BitVec.ofNat 64 (16 * l)) 128
          else 0) revMask)
        (if l < c then
          s.mem.readW (s.gpr .rax + BitVec.ofInt 64 ((0 : Nat) : Int) + BitVec.ofNat 64 (16 * l)) 128 else 0)) ∧
      (∀ l < 4, s'.zlane .xmm2 l = 0) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ∉ quadRegsK → ∀ l < 4, s'.zlane r l = s.zlane r l) := by
  let aS := s.gpr src + BitVec.ofInt 64 ((0 : Nat) : Int)
  let aK := s.gpr .r11 + BitVec.ofInt 64 ((768 : Nat) : Int)
  let aD := s.gpr .rdx + BitVec.ofInt 64 ((0 : Nat) : Int)
  let aP := s.gpr .rax + BitVec.ofInt 64 ((0 : Nat) : Int)
  let k := s.gpr .r10
  obtain ⟨vP, eP, lP⟩ := State.loadMasked512_prefix (s := s) (a := aP) hc hk hb hinP
  let s₁ := setZv s .xmm12 vP
  obtain ⟨vS, eS, lS⟩ := State.loadMasked512_prefix (s := s₁) (a := aS) hc hk hb hinS
  let s₂ := setZv s₁ .xmm7 vS
  obtain ⟨vK, eK, lK⟩ := State.loadMasked512_prefix (s := s₂) (a := aK) hc hk hb hinK
  let s₃ := setZv s₂ .xmm13 vK
  let s₄ := (ZOp.zbin .vpxord .xmm13 .xmm13 .xmm7).exec s₃
  let m₅ := s.mem.writeW aD ((s₄.zmm .xmm13).setWidth (128 * c))
  let s₅ : State := { s₄ with mem := m₅ }
  rw [remQuadKD_eq, WP.block_cons_iff]
  refine ⟨s₁, by simp only [isa, exec]; rw [show s.ea (at_ .rax 0) = aP from rfl, eP]; rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨s₂, by simp only [isa, exec]; rw [show s₁.ea (at_ src 0) = aS from rfl,
    show s₁.gpr .r10 = k from rfl, eS]; rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨s₃, by simp only [isa, exec]; rw [show s₂.ea (at_ .r11 768) = aK from rfl,
    show s₂.gpr .r10 = k from rfl, eK]; rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨s₄, rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨s₅, by
    simp only [isa, exec]
    rw [show s₄.ea (at_ .rdx 0) = aD from rfl, show s₄.gpr .r10 = k from rfl,
      State.storeMasked512_prefix (s := s₄) hc hk (show InRegions s₄.wr aD (16 * c) from hinD)]
    rfl, ?_⟩
  -- The lanes of the loads.
  have m₂ : s₂.mem = s.mem := rfl
  have m₁ : s₁.mem = s.mem := rfl
  have l13 : ∀ l < 4, s₄.zlane .xmm13 l =
      (if l < c then s.mem.readW (aK + BitVec.ofNat 64 (16 * l)) 128 else 0) ^^^
        (if l < c then s.mem.readW (aS + BitVec.ofNat 64 (16 * l)) 128 else 0) := fun l hl => by
    simp only [s₄, zlane_zbin _ _ _ _ _ _ hl, ite_true, ZBinOp.sse, Pclmul.eval_pxor, s₃]
    rw [zlane_setZv _ _ _ hl, State.zlane_setZ_ne _ (by decide) _ _ _ _ hl, zlane_setZv _ _ _ hl, lS l hl,
      lK l hl, m₁, m₂]
  have l13' : ∀ l < 4, s₄.zlane .xmm13 l =
      if l < c then s.mem.readW (aK + BitVec.ofNat 64 (16 * l)) 128 ^^^
        s.mem.readW (aS + BitVec.ofNat 64 (16 * l)) 128 else 0 := fun l hl => by
    rw [l13 l hl]; split <;> simp
  have l7' : ∀ l < 4, s₄.zlane .xmm7 l = if l < c then s.mem.readW (aS + BitVec.ofNat 64 (16 * l)) 128 else 0 :=
    fun l hl => by
      simp only [s₄, zlane_zbin _ _ _ _ _ _ hl, reduceCtorEq, ite_false, s₃]
      rw [State.zlane_setZ_ne _ (by decide) _ _ _ _ hl, zlane_setZv _ _ _ hl, lS l hl, m₁]
  have l12 : ∀ l < 4, s₄.zlane .xmm12 l = if l < c then s.mem.readW (aP + BitVec.ofNat 64 (16 * l)) 128 else 0 :=
    fun l hl => by
      simp only [s₄, zlane_zbin _ _ _ _ _ _ hl, reduceCtorEq, ite_false, s₃, s₂]
      rw [State.zlane_setZ_ne _ (by decide) _ _ _ _ hl, State.zlane_setZ_ne _ (by decide) _ _ _ _ hl,
        zlane_setZv _ _ _ hl, lP l hl]
  have keep : ∀ r, r ≠ .xmm7 → r ≠ .xmm12 → r ≠ .xmm13 → ∀ l < 4, s₄.zlane r l = s.zlane r l :=
    fun r h7 h12 h13 l hl => by
      simp only [s₄, zlane_zbin _ _ _ _ _ _ hl, ite_eq_right_iff.2 (fun h => absurd h h13), s₃, s₂, s₁]
      rw [State.zlane_setZ_ne _ h13 _ _ _ _ hl, State.zlane_setZ_ne _ h7 _ _ _ _ hl,
        State.zlane_setZ_ne _ h12 _ _ _ _ hl]
  have z₅ : ∀ r l, s₅.zlane r l = s₄.zlane r l := fun _ _ => rfl
  have hz : zlaneSseBlock (restZ 0) = some (ldAcc true) := rfl
  rw [WP.block_append_iff]
  refine WP.mono (WP.zlanes hz fun l _ => ldAcc_ok true (s₅.zproj l)) fun s₆ ⟨k₆, q₆⟩ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  have m₆ : s₆.mem = m₅ := by rw [k₆.mem]
  refine ⟨⟨s₄.zmm .xmm13, by rw [ZOp.exec_mem, m₆]⟩, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_,
    by rw [ZOp.exec_gpr, k₆.gpr]; rfl, by rw [ZOp.exec_rd, k₆.rd]; rfl, by rw [ZOp.exec_wr, k₆.wr]; rfl,
    fun r hr l hl => ?_⟩
  · have hl4 : l < 4 := by omega
    rw [ZOp.exec_mem, m₆, blockAt_eq]
    have e := readW_writeW_inside s.mem aD ((s₄.zmm .xmm13).setWidth (128 * c)) (k := 16 * l) (n := 16)
      (by omega) (by omega)
    rw [show 8 * 16 = 128 by rfl] at e
    rw [e, show 8 * (16 * l) = 128 * l by omega]
    have e2 : ((s₄.zmm .xmm13).setWidth (128 * c)).extractLsb' (128 * l) 128 =
        (s₄.zmm .xmm13).extractLsb' (128 * l) 128 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
      rw [decide_eq_true (show 128 * l + i < 128 * c by omega), Bool.true_and]
    rw [e2, zmm_lane _ _ hl4, l13' l hl4, ite_eq_left hl]
  · have hp : prod (((ZOp.zbin .vpxord .xmm2 .xmm2 .xmm2).exec s₆).zproj l) = prod (s₆.zproj l) := by
      simp only [prod, State.zproj_xmm, zlane_zbin _ _ _ _ _ _ hl, reduceCtorEq, ite_false]
    rw [hp, (q₆ l hl).1]
    have hp₅ : prod (s₅.zproj l) = prod (s.zproj l) := by
      simp only [prod, State.zproj_xmm, z₅, keep .xmm8 (by decide) (by decide) (by decide) l hl,
        keep .xmm9 (by decide) (by decide) (by decide) l hl, keep .xmm10 (by decide) (by decide) (by decide) l hl]
    simp only [hp₅, ite_true, State.zproj_xmm, z₅, l7' l hl, l12 l hl,
      keep .xmm0 (by decide) (by decide) (by decide) l hl, h0 l hl,
      keep .xmm2 (by decide) (by decide) (by decide) l hl]
    rfl
  · simp only [zlane_zbin _ _ _ _ _ _ hl, ite_true, ZBinOp.sse, Pclmul.eval_pxor, BitVec.xor_self]
    rfl
  · simp only [quadRegsK, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h7, h12, h13, h2, h8, h9, h10, h11⟩ := hr
    rw [zlane_zbin _ _ _ _ _ _ hl, ite_eq_right_iff.2 (fun h => absurd h h2)]
    have := (q₆ l hl).2.xmm r (by simp [h7, h8, h9, h10, h11])
    simp only [State.zproj_xmm] at this
    rw [this, z₅, keep r h7 h12 h13 l hl]

end VG.Proof.Gcm.X86_64.StitchZH
