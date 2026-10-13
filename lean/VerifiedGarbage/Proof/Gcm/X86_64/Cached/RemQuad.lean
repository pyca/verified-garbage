module

public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemBody
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Gh
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.Base

/-!
# Four of the blocks after the last group

`remQuad_ok`: `StitchZH.remQuad src` loads the four blocks at `src + r10`
and their keystream at `r11 + r10 + 768` into the lanes of `zmm7` and adds
them, stores the result to `rdx + r10`, loads their powers at `rax + r10`,
and, as a load of a group does (`StitchZ.ldAcc_ok`, `WP.zlanes`), adds each
lane's product, the block byte-reversed with `Y`'s lane added, to that
lane's products; then clears `Y`.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZH

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod)
open VG.Impl.Gcm.X86_64.StitchZTo (atIx)
open VG.Impl.Gcm.X86_64.StitchZH (remQuad remNext4)
open VG.Proof.Gcm.X86_64.StitchZTo (ea_atIx)
open VG.Proof.Gcm.X86_64.StitchZ (restZ ldAcc ldAcc_ok)
open VG.Proof.Aes.X86_64.VaesZ (load512_lane zmm_lane blockAt_writeW_lane)
open VG.Proof.Gcm.X86_64 (revMask blockAt_eq pshufb_rev_xor)
open VG.Spec.Gcm (Block blockAt)

theorem remQuad_eq (src : Reg) :
    remQuad src = .vmovdqu32Load .xmm7 (atIx src .r10 0) :: .vmovdqu32Load .xmm12 (atIx .r11 .r10 768) ::
      .zop (.zbin .vpxord .xmm7 .xmm7 .xmm12) :: .vmovdqu32Store (atIx .rdx .r10 0) .xmm7 ::
      .vmovdqu32Load .xmm12 (atIx .rax .r10 0) :: (restZ 0 ++ ([.zop (.zbin .vpxord .xmm2 .xmm2 .xmm2)] : List Instr)) := rfl

/-- The registers `remQuad` writes. -/
abbrev quadRegs : List XReg := [.xmm7, .xmm12, .xmm2, .xmm8, .xmm9, .xmm10, .xmm11]

theorem zlane_ld (s : State) (d : XReg) (a : Addr) {l : Nat} (hl : l < 4) :
    (s.setZ d ((s.mem.readW a 512).extractLsb' 0 128) ((s.mem.readW a 512).extractLsb' 128 128)
      ((s.mem.readW a 512).extractLsb' 256 128) ((s.mem.readW a 512).extractLsb' 384 128)).zlane d l =
      s.mem.readW (a + BitVec.ofNat 64 (16 * l)) 128 := by
  rw [State.zlane_setZ _ _ _ _ _ _ _ hl]
  simp only [ite_true]
  rw [pick4_lanes (fun i => (s.mem.readW a 512).extractLsb' (128 * i) 128) hl]
  exact load512_lane _ _ hl

/-- Four blocks at `src + r10`, with their keystream at `r11 + r10 + 768`,
encrypted to `rdx + r10`, and their products with their powers at `rax + r10`
added to the lanes'. -/
theorem remQuad_ok (src : Reg) (s : State) (h0 : ∀ l < 4, s.zlane .xmm0 l = revMask)
    (hinS : InRegions (s.rd ++ s.wr) (s.gpr src + s.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int)) 64)
    (hinK : InRegions (s.rd ++ s.wr) (s.gpr .r11 + s.gpr .r10 + BitVec.ofInt 64 ((768 : Nat) : Int)) 64)
    (hinD : InRegions s.wr (s.gpr .rdx + s.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int)) 64)
    (hinP : InRegions (s.rd ++ s.wr) (s.gpr .rax + s.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int)) 64)
    (hDP : Region.Disjoint ⟨s.gpr .rdx + s.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int), 64⟩
      ⟨s.gpr .rax + s.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int), 64⟩) :
    WP isa (.block (remQuad src)) s fun s' =>
      (∃ v : BitVec 512, s'.mem = s.mem.writeW (s.gpr .rdx + s.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int)) v) ∧
      (∀ l < 4, blockAt s'.mem (s.gpr .rdx + s.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int) +
          BitVec.ofNat 64 (16 * l)) =
        XBinOp.eval .pshufb
          (s.mem.readW (s.gpr src + s.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int) + BitVec.ofNat 64 (16 * l)) 128 ^^^
            s.mem.readW (s.gpr .r11 + s.gpr .r10 + BitVec.ofInt 64 ((768 : Nat) : Int) +
              BitVec.ofNat 64 (16 * l)) 128) revMask) ∧
      (∀ l < 4, prod (s'.zproj l) = (prod (s.zproj l)).acc
        (s.zlane .xmm2 l ^^^ XBinOp.eval .pshufb
          (s.mem.readW (s.gpr src + s.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int) + BitVec.ofNat 64 (16 * l)) 128 ^^^
            s.mem.readW (s.gpr .r11 + s.gpr .r10 + BitVec.ofInt 64 ((768 : Nat) : Int) +
              BitVec.ofNat 64 (16 * l)) 128) revMask)
        (s.mem.readW (s.gpr .rax + s.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int) + BitVec.ofNat 64 (16 * l)) 128)) ∧
      (∀ l < 4, s'.zlane .xmm2 l = 0) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ∉ quadRegs → ∀ l < 4, s'.zlane r l = s.zlane r l) := by
  let aS := s.gpr src + s.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int)
  let aK := s.gpr .r11 + s.gpr .r10 + BitVec.ofInt 64 ((768 : Nat) : Int)
  let aD := s.gpr .rdx + s.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int)
  let aP := s.gpr .rax + s.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int)
  let vS := s.mem.readW aS 512
  let s₁ := s.setZ .xmm7 (vS.extractLsb' 0 128) (vS.extractLsb' 128 128) (vS.extractLsb' 256 128)
    (vS.extractLsb' 384 128)
  let vK := s₁.mem.readW aK 512
  let s₂ := s₁.setZ .xmm12 (vK.extractLsb' 0 128) (vK.extractLsb' 128 128) (vK.extractLsb' 256 128)
    (vK.extractLsb' 384 128)
  let s₃ := (ZOp.zbin .vpxord .xmm7 .xmm7 .xmm12).exec s₂
  let m₄ := s.mem.writeW aD (s₃.zmm .xmm7)
  let s₄ := s₃.setMem m₄
  let vP := s₄.mem.readW aP 512
  let s₅ := s₄.setZ .xmm12 (vP.extractLsb' 0 128) (vP.extractLsb' 128 128) (vP.extractLsb' 256 128)
    (vP.extractLsb' 384 128)
  rw [remQuad_eq, WP.block_cons_iff]
  refine ⟨s₁, by simp only [isa, exec, State.load512, ea_atIx, hinS, ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨s₂, by simp only [isa, exec, State.load512, ea_atIx, s₁, State.setZ_gpr, State.setZ_rd,
    State.setZ_wr, hinK, ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨s₃, rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨s₄, by simp only [isa, exec, State.store512_eq, ea_atIx, s₃, s₂, s₁, ZOp.exec_gpr, State.setZ_gpr,
    ZOp.exec_wr, State.setZ_wr, ZOp.exec_mem, State.setZ_mem, hinD, ite_true, s₄, m₄, aD], ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨s₅, by simp only [isa, exec, State.load512, ea_atIx, s₄, s₃, s₂, s₁, State.setMem_gpr, ZOp.exec_gpr,
    State.setZ_gpr, State.setMem_rd, State.setMem_wr, ZOp.exec_rd, ZOp.exec_wr, State.setZ_rd, State.setZ_wr, hinP,
    ite_true, Option.map_some]; rfl, ?_⟩
  -- The lanes of the loads.
  have l7 : ∀ l < 4, s₃.zlane .xmm7 l =
      s.mem.readW (aS + BitVec.ofNat 64 (16 * l)) 128 ^^^ s.mem.readW (aK + BitVec.ofNat 64 (16 * l)) 128 :=
    fun l hl => by
      simp only [s₃, zlane_zbin _ _ _ _ _ _ hl, ite_true, ZBinOp.sse, Pclmul.eval_pxor, s₂]
      rw [State.zlane_setZ_ne _ (by decide) _ _ _ _ hl, zlane_ld s .xmm7 aS hl, zlane_ld s₁ .xmm12 aK hl]
      rfl
  have mP : ∀ l < 4, s₄.mem.readW (aP + BitVec.ofNat 64 (16 * l)) 128 =
      s.mem.readW (aP + BitVec.ofNat 64 (16 * l)) 128 := fun l hl => by
    show (s.mem.writeW aD (s₃.zmm .xmm7)).readW _ 128 = _
    exact Mem.readW_writeW_sep (hDP.symm.sep (Offset.contains_base _ (by omega) (by omega))
      (Region.contains_self _ _)) (by decide)
  have l12 : ∀ l < 4, s₅.zlane .xmm12 l = s.mem.readW (aP + BitVec.ofNat 64 (16 * l)) 128 := fun l hl => by
    rw [zlane_ld s₄ .xmm12 aP hl, mP l hl]
  have keep : ∀ r, r ≠ .xmm7 → r ≠ .xmm12 → ∀ l < 4, s₅.zlane r l = s.zlane r l := fun r h7 h12 l hl => by
    simp only [s₅, s₄, s₃, s₂, s₁]
    rw [State.zlane_setZ_ne _ h12 _ _ _ _ hl, State.setMem_zlane, zlane_zbin _ _ _ _ _ _ hl, ite_eq_right_iff.2 (fun h => absurd h h7),
      State.zlane_setZ_ne _ h12 _ _ _ _ hl, State.zlane_setZ_ne _ h7 _ _ _ _ hl]
  have l7 : ∀ l < 4, s₅.zlane .xmm7 l =
      s.mem.readW (aS + BitVec.ofNat 64 (16 * l)) 128 ^^^ s.mem.readW (aK + BitVec.ofNat 64 (16 * l)) 128 :=
    fun l hl => by
      simp only [s₅, s₄]
      rw [State.zlane_setZ_ne _ (by decide) _ _ _ _ hl, State.setMem_zlane]
      simp only [s₃, zlane_zbin _ _ _ _ _ _ hl, ite_true, ZBinOp.sse, Pclmul.eval_pxor, s₂]
      rw [State.zlane_setZ_ne _ (by decide) _ _ _ _ hl, zlane_ld s .xmm7 aS hl, zlane_ld s₁ .xmm12 aK hl]
      rfl
  have hz : zlaneSseBlock (restZ 0) = some (ldAcc true) := rfl
  rw [WP.block_append_iff]
  refine WP.mono (WP.zlanes hz fun l _ => ldAcc_ok true (s₅.zproj l)) fun s₆ ⟨k₆, q₆⟩ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  have m₆ : s₆.mem = m₄ := by rw [k₆.mem]; rfl
  refine ⟨⟨s₃.zmm .xmm7, by rw [ZOp.exec_mem, m₆]⟩, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_,
    by rw [ZOp.exec_gpr, k₆.gpr]; rfl, by rw [ZOp.exec_rd, k₆.rd]; rfl, by rw [ZOp.exec_wr, k₆.wr]; rfl,
    fun r hr l hl => ?_⟩
  · rw [ZOp.exec_mem, m₆, blockAt_writeW_lane _ _ _ hl, zmm_lane _ _ hl]
    have e : s₃.zlane .xmm7 l = s₅.zlane .xmm7 l := by
      simp only [s₅, s₄]
      rw [State.zlane_setZ_ne _ (by decide) _ _ _ _ hl, State.setMem_zlane]
    rw [e, l7 l hl]
  · have hp : prod (((ZOp.zbin .vpxord .xmm2 .xmm2 .xmm2).exec s₆).zproj l) = prod (s₆.zproj l) := by
      simp only [prod, State.zproj_xmm, zlane_zbin _ _ _ _ _ _ hl, reduceCtorEq, ite_false]
    rw [hp, (q₆ l hl).1]
    have hp₅ : prod (s₅.zproj l) = prod (s.zproj l) := by
      simp only [prod, State.zproj_xmm, keep .xmm8 (by decide) (by decide) l hl,
        keep .xmm9 (by decide) (by decide) l hl, keep .xmm10 (by decide) (by decide) l hl]
    simp only [hp₅, ite_true, State.zproj_xmm, l7 l hl, l12 l hl, keep .xmm0 (by decide) (by decide) l hl, h0 l hl,
      keep .xmm2 (by decide) (by decide) l hl]
    rfl
  · simp only [zlane_zbin _ _ _ _ _ _ hl, ite_true, ZBinOp.sse, Pclmul.eval_pxor, BitVec.xor_self]
    rfl
  · simp only [quadRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h7, h12, h2, h8, h9, h10, h11⟩ := hr
    rw [zlane_zbin _ _ _ _ _ _ hl, ite_eq_right_iff.2 (fun h => absurd h h2)]
    have := (q₆ l hl).2.xmm r (by simp [h7, h8, h9, h10, h11])
    simp only [State.zproj_xmm] at this
    rw [this, keep r h7 h12 l hl]

/-- `add r10, 64`, `sub r9, 4`, `cmp r9, 16`. -/
theorem remNext4_ok (s : State) {m : Nat} (h4 : 4 ≤ m) (h15 : m ≤ 15) {i : Nat}
    (h9 : s.gpr .r9 = BitVec.ofNat 64 (16 + m)) (h10 : s.gpr .r10 = BitVec.ofNat 64 (16 * i)) :
    WP isa (.block remNext4) s fun s' =>
      s'.gpr .r10 = BitVec.ofNat 64 (16 * (i + 4)) ∧ s'.gpr .r9 = BitVec.ofNat 64 (16 + (m - 4)) ∧
      s'.zf = some (decide (m = 4)) ∧ (∀ r, r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧
      (∀ r l, s'.zlane r l = s.zlane r l) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e64 : BitVec.signExtend 64 (64 : BitVec 32) = 64 := by decide
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  have e4 : BitVec.signExtend 64 (4 : BitVec 32) = 4 := by decide
  have a10 : BitVec.ofNat 64 (16 * i) + 64 = BitVec.ofNat 64 (16 * (i + 4)) := by
    rw [show (64 : BitVec 64) = BitVec.ofNat 64 64 from rfl, ← BitVec.ofNat_add]; congr 1
  have s9 : BitVec.ofNat 64 (16 + m) - 4 = BitVec.ofNat 64 (16 + (m - 4)) := by
    rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
      VG.Proof.Gcm.X86_64.Pclmul.ofNat_sub_ofNat (by omega) (by omega)]
    congr 1; omega
  have z9 : (BitVec.ofNat 64 (16 + (m - 4)) - 16 == 0) = decide (m = 4) := by
    rw [show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      VG.Proof.Gcm.X86_64.Pclmul.ofNat_sub_ofNat (by omega) (by omega)]
    by_cases h : m = 4
    · subst h; rfl
    · have : BitVec.ofNat 64 (16 + (m - 4) - 16) ≠ 0 := fun e => by
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 16 + (m - 4) - 16 < 2 ^ 64 by omega)] at this
        have h0 : BitVec.toNat (0 : BitVec 64) = 0 := rfl
        omega
      rw [beq_false_of_ne this, decide_eq_false h]
  apply WP.of_runBlock
  simp only [remNext4, reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e64, e16, e4, h9, h10, a10, s9, z9,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, fun r h1 h2 => by simp only [h1, h2, ite_false], fun _ _ => rfl,
    trivial, trivial, trivial⟩

end VG.Proof.Gcm.X86_64.StitchZH
