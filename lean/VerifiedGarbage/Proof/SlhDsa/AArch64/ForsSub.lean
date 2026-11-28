module

-- separate module: the heights of a FORS subtree, a stage of `forsSign`'s proof rebuilt only when it changes

public import VerifiedGarbage.Proof.SlhDsa.AArch64.ForsLeaves
import VerifiedGarbage.Proof.SlhDsa.Lemmas
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA (SHAKE) on AArch64: `forsSign`, the heights of a subtree

The first block of `subtreeHeights` (`Impl/SlhDsa/AArch64/Fors.lean`):
`levels`'s parameters in frame 3 (`capBase = u·2^s`, `adrsBase = t·2^a +
u·2^s`, the type `FORS_TREE`, `kp`) and its arguments (`sb_ok`). As
x86-64's `subB_ok` (`Proof/SlhDsa/X86_64/ForsTree.lean`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.Fors

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.AArch64 (Layout)
open VG.Proof.SlhDsa.AArch64.TreeBase
open VG.Proof.MlKem.AArch64 (Only Keep MemTo)

variable {p : Params}

/-- The first block of `subtreeHeights`. -/
abbrev sbList (n a : Nat) : List Instr :=
  ([.addImm .x .x10 .x24 n, .add .x .x11 .x27 .x25] : List Instr) ++
    Impl.SlhDsa.AArch64.Tree.setParams (.reg .x25) (.reg .x11) (.imm 3) (.reg .x20) ++
    ([Impl.SlhDsa.AArch64.Thash4.mov .x0 .x19] : List Instr) ++ Impl.SlhDsa.AArch64.lea .x1 .x19 Layout.oN ++
    Impl.SlhDsa.AArch64.movV .x2 (2 ^ Impl.SlhDsa.AArch64.Fors.s a) ++
    ([.movz .x .x3 0 0, Impl.SlhDsa.AArch64.Thash4.mov .x4 .x10, Impl.SlhDsa.AArch64.Thash4.mov .x5 .x21] : List Instr)

/-- The registers the first block writes. -/
abbrev sbRegs : List Reg := [.x0, .x1, .x2, .x3, .x4, .x5, .x9, .x10, .x11]

/-- After the first block of `subtreeHeights`, before the call of `levels`. -/
structure SB (u v : State) (S : Addr) (n a : Nat) : Prop where
  x0 : v.gpr .x0 = S
  x1 : v.gpr .x1 = at' S Layout.oN
  x2 : v.gpr .x2 = BitVec.ofNat 64 (2 ^ Impl.SlhDsa.AArch64.Fors.s a)
  x3 : v.gpr .x3 = 0
  x4 : v.gpr .x4 = u.gpr .x24 + BitVec.ofNat 64 n
  x5 : v.gpr .x5 = u.gpr .x21
  keep : Keep sbRegs u v
  v0 : varAt v.mem S 3 0 = u.gpr .x25
  v1 : varAt v.mem S 3 1 = u.gpr .x27 + u.gpr .x25
  v2 : varAt v.mem S 3 2 = BitVec.ofNat 64 3
  v3 : varAt v.mem S 3 3 = u.gpr .x20
  frame : Frame [⟨at' S (Layout.oVar 3 0), 32⟩] u.mem v.mem

theorem var3_eq (i : Nat) : Layout.oVar 3 i = 1496 + 8 * i := rfl

theorem readW_write_other' (m : Mem) {a b : Addr} (v : BitVec 64) (h : Mem.Sep a 8 b 8) :
    (m.writeW b v).readW a 64 = m.readW a 64 :=
  Mem.readW_writeW_sep h (by decide)

theorem sb_ok (hz : Sz p) {u : State} {S : Addr} (h19 : u.gpr .x19 = S) (hwS : (⟨S, 65536⟩ : Region) ∈ u.wr)
    {Q : State → Prop} (k : ∀ v, SB u v S p.n p.a → Q v) :
    WP isa (.block (sbList p.n p.a)) u Q := by
  have hn32 := hz.n32
  have hP := pow_s_le p.a
  rw [sbList]
  generalize hMV : Impl.SlhDsa.AArch64.movV .x2 (2 ^ Impl.SlhDsa.AArch64.Fors.s p.a) = MV
  generalize hLE : Impl.SlhDsa.AArch64.lea .x1 .x19 Layout.oN = LE
  simp only [Impl.SlhDsa.AArch64.Tree.setParams, Impl.SlhDsa.AArch64.Tree.Src.mov, Impl.SlhDsa.AArch64.Tree.var,
    Impl.SlhDsa.AArch64.Thash4.mov, List.append_assoc, List.cons_append, List.nil_append]
  refine MlKem.AArch64.wp_addImm (by omega) fun t₁ o₁ e₁ => MlKem.AArch64.wp_add fun t₂ o₂ e₂ => ?_
  have g19 : t₂.gpr .x19 = S := by rw [o₂.get .x19, o₁.get .x19, h19]
  have hw₂ : (⟨S, 65536⟩ : Region) ∈ t₂.wr := by rw [o₂.wr, o₁.wr]; exact hwS
  refine MlKem.AArch64.wp_addImm (by decide) fun t₃ o₃ e₃ => MlKem.AArch64.wp_strx (a := at' S (Layout.oVar 3 0))
    (by decide) (by rw [o₃.get .x19, g19]) (by rw [o₃.wr]; exact in_scr hw₂ (by rw [var3_eq]; omega)) fun t₄ m₄ => ?_
  refine MlKem.AArch64.wp_addImm (by decide) fun t₅ o₅ e₅ => MlKem.AArch64.wp_strx (a := at' S (Layout.oVar 3 1))
    (by decide) (by rw [o₅.get .x19, m₄.gpr, o₃.get .x19, g19])
    (by rw [o₅.wr, m₄.wr, o₃.wr]; exact in_scr hw₂ (by rw [var3_eq]; omega)) fun t₆ m₆ => ?_
  refine movV_ok (by decide) fun t₇ o₇ e₇ => MlKem.AArch64.wp_strx (a := at' S (Layout.oVar 3 2)) (by decide)
    (by rw [o₇.get .x19, m₆.gpr, o₅.get .x19, m₄.gpr, o₃.get .x19, g19])
    (by rw [o₇.wr, m₆.wr, o₅.wr, m₄.wr, o₃.wr]; exact in_scr hw₂ (by rw [var3_eq]; omega)) fun t₈ m₈ => ?_
  refine MlKem.AArch64.wp_addImm (by decide) fun t₉ o₉ e₉ => MlKem.AArch64.wp_strx (a := at' S (Layout.oVar 3 3))
    (by decide) (by rw [o₉.get .x19, m₈.gpr, o₇.get .x19, m₆.gpr, o₅.get .x19, m₄.gpr, o₃.get .x19, g19])
    (by rw [o₉.wr, m₈.wr, o₇.wr, m₆.wr, o₅.wr, m₄.wr, o₃.wr]; exact in_scr hw₂ (by rw [var3_eq]; omega))
    fun t₁₀ m₁₀ => ?_
  have K₁₀ : Keep [.x9] t₂ t₁₀ := (((((((o₃.keep.trans m₄.keep).trans o₅.keep).trans m₆.keep).trans o₇.keep).trans
    m₈.keep).trans o₉.keep).trans m₁₀.keep).mono (by simp)
  have hm₁₀ : t₁₀.mem = (((t₂.mem.writeW (at' S (Layout.oVar 3 0)) (u.gpr .x25)).writeW
      (at' S (Layout.oVar 3 1)) (u.gpr .x27 + u.gpr .x25)).writeW (at' S (Layout.oVar 3 2)) (BitVec.ofNat 64 3)).writeW
      (at' S (Layout.oVar 3 3)) (u.gpr .x20) := by
    have a0 : t₂.gpr .x25 = u.gpr .x25 := by rw [o₂.get .x25, o₁.get .x25]
    have a1 : t₄.gpr .x11 = u.gpr .x27 + u.gpr .x25 := by rw [m₄.gpr, o₃.get .x11, e₂, o₁.get .x27, o₁.get .x25]
    have a2 : t₈.gpr .x20 = u.gpr .x20 := by
      rw [m₈.gpr, o₇.get .x20, m₆.gpr, o₅.get .x20, m₄.gpr, o₃.get .x20, o₂.get .x20, o₁.get .x20]
    rw [m₁₀.mem, e₉, o₉.mem, m₈.mem, e₇, o₇.mem, m₆.mem, e₅, o₅.mem, m₄.mem, e₃, o₃.mem, BitVec.add_zero,
      BitVec.add_zero, BitVec.add_zero]
    rw [a1, a2, a0]
  have hc : ∀ i < 4, (⟨at' S (Layout.oVar 3 0), 32⟩ : Region).Contains (at' S (Layout.oVar 3 i)) (64 / 8) :=
    fun i hi => Offset.contains S (by rw [var3_eq, var3_eq]; omega) (by rw [var3_eq, var3_eq]; omega)
      (by rw [var3_eq]; omega)
  have hfw : Frame [⟨at' S (Layout.oVar 3 0), 32⟩] t₂.mem t₁₀.mem := by
    rw [hm₁₀]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (hc 0 (by decide))).writeW
      (List.mem_singleton_self _) _ (hc 1 (by decide))).writeW (List.mem_singleton_self _) _
      (hc 2 (by decide))).writeW (List.mem_singleton_self _) _ (hc 3 (by decide))
  -- the arguments
  refine MlKem.AArch64.wp_addImm (by decide) fun t₁₁ o₁₁ e₁₁ => ?_
  subst hLE hMV
  refine lea_ok (off := Layout.oN) (.inr (show Reg.x1 ≠ Reg.x19 by decide)) (by decide) fun t₁₂ o₁₂ e₁₂ => ?_
  refine movV_ok (by omega) fun t₁₃ o₁₃ e₁₃ => ?_
  refine MlKem.AArch64.wp_movz fun t₁₄ o₁₄ e₁₄ => MlKem.AArch64.wp_addImm (by decide) fun t₁₅ o₁₅ e₁₅ =>
    MlKem.AArch64.wp_addImm (by decide) fun t₁₆ o₁₆ e₁₆ => MlKem.AArch64.wp_nil (k t₁₆ ?_)
  have O : Only [.x0, .x1, .x2, .x3, .x4, .x5] t₁₀ t₁₆ :=
    (((((o₁₁.trans o₁₂).trans o₁₃).trans o₁₄).trans o₁₅).trans o₁₆).mono (by simp)
  have g10 : t₁₀.gpr .x10 = u.gpr .x24 + BitVec.ofNat 64 p.n := by rw [K₁₀.get .x10, o₂.get .x10, e₁]
  have g19' : t₁₀.gpr .x19 = S := by rw [K₁₀.get .x19, g19]
  have hsep : ∀ i j, i < 4 → j < 4 → i ≠ j → Mem.Sep (at' S (Layout.oVar 3 i)) 8 (at' S (Layout.oVar 3 j)) 8 :=
    fun i j hi hj hij => Offset.sep S (by rw [var3_eq, var3_eq]; omega) (by rw [var3_eq]; omega) (by rw [var3_eq]; omega)
  have hv : ∀ i, varAt t₁₆.mem S 3 i = t₁₀.mem.readW (at' S (Layout.oVar 3 i)) 64 := fun i => by
    simp only [varAt]; rw [O.mem]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [o₁₆.get .x0, o₁₅.get .x0, o₁₄.get .x0, o₁₃.get .x0, o₁₂.get .x0, e₁₁, g19', BitVec.add_zero]
  · rw [o₁₆.get .x1, o₁₅.get .x1, o₁₄.get .x1, o₁₃.get .x1, e₁₂, o₁₁.get .x19, g19']
  · rw [o₁₆.get .x2, o₁₅.get .x2, o₁₄.get .x2, e₁₃]
  · rw [o₁₆.get .x3, o₁₅.get .x3, e₁₄]; rfl
  · rw [o₁₆.get .x4, e₁₅, o₁₄.get .x10, o₁₃.get .x10, o₁₂.get .x10, o₁₁.get .x10, g10, BitVec.add_zero]
  · rw [e₁₆, o₁₅.get .x21, o₁₄.get .x21, o₁₃.get .x21, o₁₂.get .x21, o₁₁.get .x21, K₁₀.get .x21, o₂.get .x21,
      o₁.get .x21, BitVec.add_zero]
  · exact ((o₁.keep.trans o₂.keep).trans (K₁₀.trans O.keep)).mono (by simp)
  · rw [hv, hm₁₀, readW_write_other' _ _ (hsep 0 3 (by decide) (by decide) (by decide)),
      readW_write_other' _ _ (hsep 0 2 (by decide) (by decide) (by decide)),
      readW_write_other' _ _ (hsep 0 1 (by decide) (by decide) (by decide)), Mem.readW_writeW_self64]
  · rw [hv, hm₁₀, readW_write_other' _ _ (hsep 1 3 (by decide) (by decide) (by decide)),
      readW_write_other' _ _ (hsep 1 2 (by decide) (by decide) (by decide)), Mem.readW_writeW_self64]
  · rw [hv, hm₁₀, readW_write_other' _ _ (hsep 2 3 (by decide) (by decide) (by decide)), Mem.readW_writeW_self64]
  · rw [hv, hm₁₀, Mem.readW_writeW_self64]
  · rw [O.mem, show u.mem = t₂.mem by rw [o₂.mem, o₁.mem]]; exact hfw

end VG.Proof.SlhDsa.AArch64.Fors
