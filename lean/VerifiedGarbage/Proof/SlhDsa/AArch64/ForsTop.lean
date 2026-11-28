module

-- separate module: the heights of a FORS tree above its subtrees, a stage of `forsSign`'s proof rebuilt only when it changes

public import VerifiedGarbage.Proof.SlhDsa.AArch64.ForsSubLoop
import VerifiedGarbage.Proof.SlhDsa.Lemmas
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA (SHAKE) on AArch64: `forsSign`, the heights above the subtrees

`topHeights` (`Impl/SlhDsa/AArch64/Fors.lean`): for `s < a`, the subtree
roots copied to `oN` and `levels`'s parameters and arguments (`tb_ok`), its
precondition (`tbc_ok`), the call; then the tree's root to lane 0 of the
lanes `B` (`rootB_ok`). The whole of it from the subtrees' loop's end
(`top_ok`). As x86-64's `ForsTop.lean`.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.Fors

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.AArch64 (Layout)
open VG.Impl.SlhDsa.AArch64.Fors (s)
open VG.Proof.SlhDsa.AArch64.TreeBase
open VG.Proof.MlKem.AArch64 (Only Keep MemTo)
open VG.Proof.SlhDsa.X86_64.Fors (node sib acc up_node pick_eq)

variable {p : Params}

/-- The first block of `topHeights` for `s < a`. -/
abbrev tbList (n a : Nat) : List Instr :=
  Impl.SlhDsa.AArch64.copyWords .x19 Layout.oN .x19 Layout.oRoots (2 ^ (a - s a) * n / 8) ++
    ([.addImm .x .x10 .x24 (n + s a * n)] : List Instr) ++
    Impl.SlhDsa.AArch64.Tree.setParams (.imm 0) (.reg .x27) (.imm 3) (.reg .x20) ++
    ([Impl.SlhDsa.AArch64.Thash4.mov .x0 .x19] : List Instr) ++ Impl.SlhDsa.AArch64.lea .x1 .x19 Layout.oN ++
    Impl.SlhDsa.AArch64.movV .x2 (2 ^ (a - s a)) ++
    ([.movz .x .x3 (BitVec.ofNat 16 (s a)) 0, Impl.SlhDsa.AArch64.Thash4.mov .x4 .x10,
      Impl.SlhDsa.AArch64.Thash4.mov .x5 .x21] : List Instr)

/-- The registers the first block writes. -/
abbrev tbRegs : List Reg := [.x0, .x1, .x2, .x3, .x4, .x5, .x9, .x10, .x14]

/-- After the first block of `topHeights`, before the call of `levels`. -/
structure TB (u v : State) (S : Addr) (n a : Nat) : Prop where
  x0 : v.gpr .x0 = S
  x1 : v.gpr .x1 = at' S Layout.oN
  x2 : v.gpr .x2 = BitVec.ofNat 64 (2 ^ (a - s a))
  x3 : v.gpr .x3 = BitVec.ofNat 64 (s a)
  x4 : v.gpr .x4 = u.gpr .x24 + BitVec.ofNat 64 (n + s a * n)
  x5 : v.gpr .x5 = u.gpr .x21
  keep : Keep tbRegs u v
  v0 : varAt v.mem S 3 0 = BitVec.ofNat 64 0
  v1 : varAt v.mem S 3 1 = u.gpr .x27
  v2 : varAt v.mem S 3 2 = BitVec.ofNat 64 3
  v3 : varAt v.mem S 3 3 = u.gpr .x20
  nodes : bytesAt v.mem (at' S Layout.oN) (2 ^ (a - s a) * n) = bytesAt u.mem (at' S Layout.oRoots) (2 ^ (a - s a) * n)
  frame : Frame [⟨at' S Layout.oN, 2 ^ (a - s a) * n⟩, ⟨at' S (Layout.oVar 3 0), 32⟩] u.mem v.mem

theorem pow_as_le {a : Nat} (ha : a ≤ 14) : 2 ^ (a - s a) ≤ 32 :=
  calc 2 ^ (a - s a) ≤ 2 ^ 5 := Nat.pow_le_pow_right (by decide) (by simp only [Impl.SlhDsa.AArch64.Fors.s]; omega)
    _ = 32 := rfl

theorem tb_ok (hz : Sz p) (ha : p.a ≤ 14) {u : State} {S : Addr} (h19 : u.gpr .x19 = S)
    (hwS : (⟨S, 65536⟩ : Region) ∈ u.wr) {Q : State → Prop} (k : ∀ v, TB u v S p.n p.a → Q v) :
    WP isa (.block (tbList p.n p.a)) u Q := by
  have hn32 := hz.n32
  have hs9 := s_le9 p.a
  have hU := pow_as_le ha
  have hsn : s p.a * p.n ≤ 9 * 32 := Nat.mul_le_mul hs9 hn32
  have hUn : 2 ^ (p.a - s p.a) * p.n ≤ 1024 := by have := Nat.mul_le_mul hU hn32; omega
  have e8 : 8 * (2 ^ (p.a - s p.a) * p.n / 8) = 2 ^ (p.a - s p.a) * p.n :=
    Nat.mul_div_cancel' (Nat.dvd_mul_left_of_dvd (by have := hz.n8; omega) _)
  have eN : Layout.oN = 12480 := rfl
  have eR : Layout.oRoots = 29120 := rfl
  rw [tbList]
  generalize hMV : Impl.SlhDsa.AArch64.movV .x2 (2 ^ (p.a - s p.a)) = MV
  generalize hLE : Impl.SlhDsa.AArch64.lea .x1 .x19 Layout.oN = LE
  simp only [Impl.SlhDsa.AArch64.Tree.setParams, Impl.SlhDsa.AArch64.Tree.Src.mov, Impl.SlhDsa.AArch64.Tree.var,
    Impl.SlhDsa.AArch64.Thash4.mov, List.append_assoc, List.cons_append, List.nil_append]
  refine copyWords_ok ⟨by decide, by decide, ⟨by rw [eR] <;> omega, by rw [eR] <;> omega⟩,
      ⟨by rw [eN] <;> omega, by rw [eN] <;> omega⟩,
      by rw [h19, e8]; exact in_scr' hwS (by rw [eR]; omega),
      by rw [h19, e8]; exact in_scr hwS (by rw [eN]; omega),
      by rw [h19, e8]; exact disj_scr S (by rw [eN, eR]; omega) (by rw [eN]; omega) (by rw [eR]; omega)⟩
    fun t₁ k₁ f₁ c₁ => ?_
  rw [h19, e8] at f₁ c₁
  have g19₁ : t₁.gpr .x19 = S := by rw [k₁.get .x19, h19]
  have hw₁ : (⟨S, 65536⟩ : Region) ∈ t₁.wr := by rw [k₁.wr]; exact hwS
  refine MlKem.AArch64.wp_addImm (by omega) fun t₂ o₂ e₂ => movV_ok (by decide) fun t₃ o₃ e₃ => ?_
  have g19 : t₃.gpr .x19 = S := by rw [o₃.get .x19, o₂.get .x19, g19₁]
  have hw₂ : (⟨S, 65536⟩ : Region) ∈ t₃.wr := by rw [o₃.wr, o₂.wr]; exact hw₁
  refine MlKem.AArch64.wp_strx (a := at' S (Layout.oVar 3 0))
    (by decide) (by rw [g19]) (by exact in_scr hw₂ (by rw [var3_eq]; omega)) fun t₄ m₄ => ?_
  refine MlKem.AArch64.wp_addImm (by decide) fun t₅ o₅ e₅ => MlKem.AArch64.wp_strx (a := at' S (Layout.oVar 3 1))
    (by decide) (by rw [o₅.get .x19, m₄.gpr, g19])
    (by rw [o₅.wr, m₄.wr]; exact in_scr hw₂ (by rw [var3_eq]; omega)) fun t₆ m₆ => ?_
  refine movV_ok (by decide) fun t₇ o₇ e₇ => MlKem.AArch64.wp_strx (a := at' S (Layout.oVar 3 2)) (by decide)
    (by rw [o₇.get .x19, m₆.gpr, o₅.get .x19, m₄.gpr, g19])
    (by rw [o₇.wr, m₆.wr, o₅.wr, m₄.wr]; exact in_scr hw₂ (by rw [var3_eq]; omega)) fun t₈ m₈ => ?_
  refine MlKem.AArch64.wp_addImm (by decide) fun t₉ o₉ e₉ => MlKem.AArch64.wp_strx (a := at' S (Layout.oVar 3 3))
    (by decide) (by rw [o₉.get .x19, m₈.gpr, o₇.get .x19, m₆.gpr, o₅.get .x19, m₄.gpr, g19])
    (by rw [o₉.wr, m₈.wr, o₇.wr, m₆.wr, o₅.wr, m₄.wr]; exact in_scr hw₂ (by rw [var3_eq]; omega))
    fun t₁₀ m₁₀ => ?_
  have K₁₀ : Keep [.x9, .x10] t₁ t₁₀ := ((((((((o₂.keep.trans o₃.keep).trans m₄.keep).trans o₅.keep).trans m₆.keep).trans
    o₇.keep).trans m₈.keep).trans o₉.keep).trans m₁₀.keep).mono (by simp)
  have a1 : t₄.gpr .x27 = u.gpr .x27 := by rw [m₄.gpr, o₃.get .x27, o₂.get .x27, k₁.get .x27]
  have a2 : t₈.gpr .x20 = u.gpr .x20 := by
    rw [m₈.gpr, o₇.get .x20, m₆.gpr, o₅.get .x20, m₄.gpr, o₃.get .x20, o₂.get .x20, k₁.get .x20]
  have hm₁₀ : t₁₀.mem = (((t₁.mem.writeW (at' S (Layout.oVar 3 0)) (BitVec.ofNat 64 0)).writeW
      (at' S (Layout.oVar 3 1)) (u.gpr .x27)).writeW (at' S (Layout.oVar 3 2)) (BitVec.ofNat 64 3)).writeW
      (at' S (Layout.oVar 3 3)) (u.gpr .x20) := by
    rw [m₁₀.mem, e₉, o₉.mem, m₈.mem, e₇, o₇.mem, m₆.mem, e₅, o₅.mem, m₄.mem, e₃, o₃.mem, o₂.mem, BitVec.add_zero,
      BitVec.add_zero, a1, a2]
  have hc : ∀ i < 4, (⟨at' S (Layout.oVar 3 0), 32⟩ : Region).Contains (at' S (Layout.oVar 3 i)) (64 / 8) :=
    fun i hi => Offset.contains S (by rw [var3_eq, var3_eq]; omega) (by rw [var3_eq, var3_eq]; omega)
      (by rw [var3_eq]; omega)
  have hfw : Frame [⟨at' S (Layout.oVar 3 0), 32⟩] t₁.mem t₁₀.mem := by
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
  have g10 : t₁₀.gpr .x10 = u.gpr .x24 + BitVec.ofNat 64 (p.n + s p.a * p.n) := by
    rw [m₁₀.gpr, o₉.get .x10, m₈.gpr, o₇.get .x10, m₆.gpr, o₅.get .x10, m₄.gpr, o₃.get .x10, e₂, k₁.get .x24]
  have g19' : t₁₀.gpr .x19 = S := by rw [K₁₀.get .x19, g19₁]
  have hsep : ∀ i j, i < 4 → j < 4 → i ≠ j → Mem.Sep (at' S (Layout.oVar 3 i)) 8 (at' S (Layout.oVar 3 j)) 8 :=
    fun i j hi hj hij => Offset.sep S (by rw [var3_eq, var3_eq]; omega) (by rw [var3_eq]; omega) (by rw [var3_eq]; omega)
  have hv : ∀ i, varAt t₁₆.mem S 3 i = t₁₀.mem.readW (at' S (Layout.oVar 3 i)) 64 := fun i => by
    simp only [varAt]; rw [O.mem]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [o₁₆.get .x0, o₁₅.get .x0, o₁₄.get .x0, o₁₃.get .x0, o₁₂.get .x0, e₁₁, g19', BitVec.add_zero]
  · rw [o₁₆.get .x1, o₁₅.get .x1, o₁₄.get .x1, o₁₃.get .x1, e₁₂, o₁₁.get .x19, g19']
  · rw [o₁₆.get .x2, o₁₅.get .x2, o₁₄.get .x2, e₁₃]
  · rw [o₁₆.get .x3, o₁₅.get .x3, e₁₄, Wots4.movz_ofNat (by omega)]
  · rw [o₁₆.get .x4, e₁₅, o₁₄.get .x10, o₁₃.get .x10, o₁₂.get .x10, o₁₁.get .x10, g10, BitVec.add_zero]
  · rw [e₁₆, o₁₅.get .x21, o₁₄.get .x21, o₁₃.get .x21, o₁₂.get .x21, o₁₁.get .x21, K₁₀.get .x21, k₁.get .x21,
      BitVec.add_zero]
  · exact ((k₁.trans K₁₀).trans O.keep).mono (by simp)
  · rw [hv, hm₁₀, readW_write_other' _ _ (hsep 0 3 (by decide) (by decide) (by decide)),
      readW_write_other' _ _ (hsep 0 2 (by decide) (by decide) (by decide)),
      readW_write_other' _ _ (hsep 0 1 (by decide) (by decide) (by decide)), Mem.readW_writeW_self64]
  · rw [hv, hm₁₀, readW_write_other' _ _ (hsep 1 3 (by decide) (by decide) (by decide)),
      readW_write_other' _ _ (hsep 1 2 (by decide) (by decide) (by decide)), Mem.readW_writeW_self64]
  · rw [hv, hm₁₀, readW_write_other' _ _ (hsep 2 3 (by decide) (by decide) (by decide)), Mem.readW_writeW_self64]
  · rw [hv, hm₁₀, Mem.readW_writeW_self64]
  · rw [O.mem, bytesAt_frame hfw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact disj_scr S (by rw [var3_eq, eN]; omega) (by rw [eN]; omega) (by rw [var3_eq]; omega)) (by omega)]
    exact c₁
  · rw [O.mem]
    exact (f₁.mono fun r hr => by simp at hr ⊢; simp [hr]).trans (hfw.mono fun r hr => by simp at hr ⊢; simp [hr])

/-- The regions of the call of `levels` above the subtrees. -/
abbrev tbW (n a : Nat) (S AU : Addr) : List Region :=
  [⟨S, scratchLen⟩, ⟨AU + BitVec.ofNat 64 (n + s a * n), (a - s a) * n⟩]

/-- The state before the call of `levels` above the subtrees. -/
structure TBC (p : Params) (S AU : Addr) (pk a16 : List Byte) (u v : State) : Prop where
  tb : TB u v S p.n p.a
  env : Env p v.mem S pk a16
  pre : (levelsContract p).pre (v.callEntry.withRegions [] (tbW p.n p.a S AU))
  c₁ : Covers ([] ++ tbW p.n p.a S AU) (v.rd ++ v.wr)
  c₂ : Covers (tbW p.n p.a S AU) v.wr

/-- The first block of `topHeights` for `s < a`, and `levels`'s precondition after it. -/
theorem tbc_ok (hz : Sz p) (ha : p.a ≤ 14) (hsa : s p.a < p.a) {S SG AU : Addr} {L dA V4 idx : Nat}
    {pk a16 : List Byte} {u : State}
    (h19 : u.gpr .x19 = S) (hKP : (u.gpr .x20).toNat < 2 ^ 32) (h21 : u.gpr .x21 = BitVec.ofNat 64 idx)
    (hidx : idx < 2 ^ 32) (h24 : u.gpr .x24 = AU) (h27 : u.gpr .x27 = BitVec.ofNat 64 V4) (hV : V4 < 2 ^ 32)
    (hw : (⟨S, 65536⟩ : Region) ∈ u.wr) (hwG : (⟨SG, L⟩ : Region) ∈ u.wr) (hAU : AU = SG + BitVec.ofNat 64 dA)
    (hdA : dA + (p.a + 1) * p.n ≤ L) (hGf : SG.toNat + L ≤ 2 ^ 64) (hfit : S.toNat + 65536 ≤ 2 ^ 64)
    (hGd : Region.Disjoint ⟨SG, L⟩ ⟨S, Layout.oSigTmp⟩) (hE : Env p u.mem S pk a16) :
    WP isa (.block (tbList p.n p.a)) u (TBC p S AU pk a16 u) := by
  have hn32 := hz.n32
  have hs9 := s_le9 p.a
  have hU := pow_as_le ha
  have eN : Layout.oN = 12480 := rfl
  refine tb_ok hz ha h19 hw fun v hv => ?_
  have hve : Env p v.mem S pk a16 := env_keep hn32 hE hv.frame fun r hr k hk => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have := Nat.mul_le_mul hU hn32
      exact ⟨disj_scr S (by rw [laneA_eq, eN]; omega) (by rw [laneA_eq]; omega) (by rw [eN]; omega),
        disj_scr S (by rw [laneB_eq, eN]; omega) (by rw [laneB_eq]; omega) (by rw [eN]; omega)⟩
    · exact var3_lanes hn32 S _ (List.mem_singleton_self _) k hk
  have h2h : (BitVec.ofNat 64 (2 ^ (p.a - s p.a))).toNat = 2 ^ (p.a - s p.a) := by rw [BitVec.toNat_ofNat]; omega
  have hlog : heightsOf (v.callEntry.withRegions [] (tbW p.n p.a S AU)) = p.a - s p.a := by
    simp only [heightsOf]; rw [entry_gpr _ _ _ (by decide), hv.x2, h2h, Nat.log2_two_pow]
  have han : (p.a + 1) * p.n = p.n + s p.a * p.n + (p.a - s p.a) * p.n := by
    rw [Nat.add_assoc, ← Nat.add_mul, Nat.add_sub_cancel' (Nat.le_of_lt hsa), Nat.add_mul, Nat.one_mul, Nat.add_comm]
  have hsn : 1 ≤ (p.a - s p.a) * p.n := Nat.mul_pos (by omega) (by have := hz.n16; omega)
  have hdA' : dA + (p.n + s p.a * p.n) + (p.a - s p.a) * p.n ≤ L := by rw [han] at hdA; omega
  have hAUn : AU + BitVec.ofNat 64 (p.n + s p.a * p.n) = at' SG (dA + (p.n + s p.a * p.n)) := by
    rw [hAU, at', BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have hsub : Region.Sub ⟨AU + BitVec.ofNat 64 (p.n + s p.a * p.n), (p.a - s p.a) * p.n⟩ ⟨SG, L⟩ := by
    rw [hAUn]; exact Offset.sub_base SG (by omega)
  have hx0 : (v.callEntry.withRegions [] (tbW p.n p.a S AU)).gpr .x0 = S := by
    rw [entry_gpr _ _ _ (by decide), hv.x0]
  have hx4 : (v.callEntry.withRegions [] (tbW p.n p.a S AU)).gpr .x4 = AU + BitVec.ofNat 64 (p.n + s p.a * p.n) := by
    rw [entry_gpr _ _ _ (by decide), hv.x4, h24]
  have hvm : ∀ i, varAt (v.callEntry.withRegions [] (tbW p.n p.a S AU)).mem S 3 i = varAt v.mem S 3 i := fun _ => rfl
  have hc : Covers (tbW p.n p.a S AU) v.wr := Covers.of_sub fun r hr => by
    rw [hv.keep.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hw, 0, scr0 S, by simp [scratchLen]⟩
    · exact ⟨_, hwG, dA + (p.n + s p.a * p.n), hAUn, hdA'⟩
  refine ⟨hv, hve, ⟨?_, ⟨pk, a16, by rw [hx0]; exact hve⟩,
    by rw [hx0, entry_gpr _ _ _ (by decide), hv.x1], by rw [hlog]; omega,
    by rw [hlog, entry_gpr _ _ _ (by decide), hv.x3, BitVec.toNat_ofNat]; omega,
    by rw [hlog, entry_gpr _ _ _ (by decide), hv.x2, h2h],
    by rw [entry_gpr _ _ _ (by decide), hv.x2, h2h, show Layout.nodeSlots = 520 from rfl]
       have := Nat.mul_le_mul (show 2 ^ (p.a - s p.a) + 8 ≤ 520 by omega) hn32; omega,
    by rw [entry_gpr _ _ _ (by decide), hv.x5, h21, BitVec.toNat_ofNat]; omega,
    by rw [hx0, hvm, hv.v0]; decide,
    by rw [hx0, hvm, hv.v1, h27, BitVec.toNat_ofNat]; omega,
    by rw [hx0, hvm, hv.v2]; decide,
    by rw [hx0, hvm, hv.v3]; exact hKP⟩, by rw [List.nil_append]; exact Covers.right hc, hc⟩
  rw [hx0, hx4, hlog]
  refine ⟨rfl, rfl, hfit, ?_, hGd.sub_left hsub, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil⟩
  show (AU + BitVec.ofNat 64 (p.n + s p.a * p.n)).toNat + (p.a - s p.a) * p.n ≤ 2 ^ 64
  rw [hAUn, toNat_at (by omega)]; omega

/-! ## The tree's root to lane 0 of the lanes `B` -/

/-- The last block of `topHeights`, from `R`. -/
abbrev rbList (n : Nat) (R : Nat) : List Instr :=
  ([Impl.SlhDsa.AArch64.Thash4.mov .x10 .x23] : List Instr) ++ Impl.SlhDsa.AArch64.mulN n .x10 .x11 ++
    ([.add .x .x10 .x10 .x19] : List Instr) ++
    Impl.SlhDsa.AArch64.copyWords .x10 (Layout.laneB 0 + (n + 32)) .x19 R (n / 8)

/-- Where tree `tt`'s root goes. -/
abbrev rootAt (n tt : Nat) : Nat := Layout.laneB 0 + n + 32 + tt * n

theorem rootB_ok (hz : Sz p) {S : Addr} {tt R : Nat} {u : State} (h19 : u.gpr .x19 = S)
    (h23 : u.gpr .x23 = BitVec.ofNat 64 tt) (htk : (tt + 1) * p.n ≤ 1120) (hR : R % 8 = 0)
    (hR' : 4832 ≤ R) (hR'' : R + p.n ≤ 30144)
    (hw : (⟨S, 65536⟩ : Region) ∈ u.wr) {Q : State → Prop}
    (k : ∀ u', Keep [.x10, .x11, .x14] u u' →
      bytesAt u'.mem (at' S (rootAt p.n tt)) p.n = bytesAt u.mem (at' S R) p.n →
      Frame [⟨at' S (rootAt p.n tt), p.n⟩] u.mem u'.mem → Q u') :
    WP isa (.block (rbList p.n R)) u Q := by
  have hn32 := hz.n32
  have e8 : 8 * (p.n / 8) = p.n := by have := hz.n8; omega
  have eB : Layout.laneB 0 = 3648 := rfl
  have htn : tt * p.n + p.n ≤ 1120 := by rw [Nat.add_mul, Nat.one_mul] at htk; omega
  rw [← List.append_nil (rbList p.n R)]
  simp only [rbList, Impl.SlhDsa.AArch64.Thash4.mov, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_mov fun t₁ u₁ => mulN_ok hz.nv (by decide) fun t₂ o₂ e₂ => wp_addr fun t₃ u₃ => ?_
  have k₃ : Keep [.x10, .x11] u t₃ := (((upK u₁).trans o₂.keep).trans (upK u₃)).mono (by simp)
  have hm₃ : t₃.mem = u.mem := by rw [u₃.mem, o₂.mem, u₁.mem]
  have g19 : t₃.gpr .x19 = S := by rw [k₃.get .x19, h19]
  have hx₃ : t₃.gpr .x10 = at' S (tt * p.n) := by
    rw [u₃.gpr, e₂, u₁.gpr, o₂.get .x19, u₁.other _ (by decide), h19, h23, BitVec.ofNat_mul_ofNat, at',
      BitVec.add_comm]
  have hw₃ : (⟨S, 65536⟩ : Region) ∈ t₃.wr := by rw [k₃.wr]; exact hw
  have hdst : t₃.gpr .x10 + BitVec.ofNat 64 (Layout.laneB 0 + (p.n + 32)) = at' S (rootAt p.n tt) := by
    rw [hx₃, at_add, show tt * p.n + (Layout.laneB 0 + (p.n + 32)) = rootAt p.n tt by simp only [rootAt]; omega]
  have hn8 := hz.n8
  have hin : InRegions t₃.wr (at' S (rootAt p.n tt)) p.n := in_scr hw₃ (by simp only [rootAt]; rw [eB]; omega)
  have hdis : Region.Disjoint ⟨at' S (rootAt p.n tt), p.n⟩ ⟨at' S R, p.n⟩ :=
    disj_scr S (.inl (by simp only [rootAt]; rw [eB]; omega)) (by simp only [rootAt]; rw [eB]; omega) (by omega)
  refine copyWords_ok (d₂ := Layout.laneB 0 + (p.n + 32)) (d₁ := R) (w := p.n / 8)
    ⟨by decide, by decide, ⟨hR, by omega⟩, ⟨by rw [eB]; omega, by rw [eB]; omega⟩,
      by rw [g19, e8]; exact in_scr' hw₃ (by omega), by rw [hdst, e8]; exact hin,
      by rw [hdst, g19, e8]; exact hdis⟩
    fun u' k' f' c' => WP.block_nil (k u' ((k₃.trans k').mono (by simp)) ?_ ?_)
  · rw [hdst, e8] at c'; rw [c', g19, hm₃]
  · rw [hdst, e8, hm₃] at f'; exact f'

end VG.Proof.SlhDsa.AArch64.Fors
