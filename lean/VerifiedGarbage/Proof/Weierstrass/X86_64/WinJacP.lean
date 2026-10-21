module

import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJac
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FprogI
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelectY
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacSelect
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacBuild
import VerifiedGarbage.Proof.Weierstrass.X86_64.CachedJacField
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJP
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJDigit
import VerifiedGarbage.Proof.Weierstrass.X86_64.Window
import VerifiedGarbage.Proof.Weierstrass.WinJacMath
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacIter

/-!
# The Jacobian window method on x86-64, selecting each entry during the iteration before

`JacWinCfg.windowP` (`Impl/Weierstrass/X86_64/WinJac.lean`): while digit
`j`'s addition runs, digit `j - 1`'s entry is kept in the accumulators in
parts (`selChunk`, `SelW`), which the addition's field operations, scalar
code writing none of the table, leave as they are (`SelW.stab`); after the
masks, which are scalar code too, it is stored to `T` and negated
(`finNext_ok`), and the next iteration's doublings, which do not write `T`,
keep it (`JEnt.unch_self`). `winJac_ok`: `window`, pipelined or not, leaves
`[k]P` in `R`.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

variable {K : JacWinCfg} {size : Nat} {C : Curve}

/-! ## The table's bytes -/

/-- The table's bytes survive what is written apart from its 80 slots. -/
theorem tblByte_unch (hL : JacWinLay K size) {base : Addr} {W : List (Nat × Nat)} {m m' : Mem}
    (hU : Unch base W m m') (hn : base.toNat + size ≤ 2 ^ 64)
    (hW : ∀ w ∈ W, ∀ i < 80, jg K i + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ jg K i) :
    ∀ b < 16 * K.np16 * 16, m' (base + BitVec.ofNat 64 K.tbl + BitVec.ofNat 64 b) =
      m (base + BitVec.ofNat 64 K.tbl + BitVec.ofNat 64 b) := by
  intro b hb
  obtain ⟨-, -, h2n⟩ := np16_eq hL
  have hg := hL.grid_le
  have hn0 := hL.n0
  have hb' : b < 80 * (8 * K.M.n) := by omega_arith
  rw [Offset.add_add]
  refine hU _ fun w hw => ?_
  rw [show ofs base (base + BitVec.ofNat 64 (K.tbl + b)) = K.tbl + b from Mem.sub_ofNat_toNat base (by omega_arith)]
  have hi : b / (8 * K.M.n) < 80 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hb')
  have hlo := Nat.div_mul_le_self b (8 * K.M.n)
  have hhi := Nat.lt_div_mul_add (a := b) (show 0 < 8 * K.M.n by omega_arith)
  have e : jg K (b / (8 * K.M.n)) = K.tbl + 8 * K.M.n * (b / (8 * K.M.n)) := rfl
  rcases hW w hw _ hi with h | h
  · left; rw [e, Nat.mul_comm] at h; omega_arith
  · right; rw [e, Nat.mul_comm] at h; omega_arith

/-- Writes to the slots but the table's, and to the temporary area, are apart
from the table's slots. -/
theorem notTbl_apart (hL : JacWinLay K size) {x : Nat} (hx : x ∈ jwSlots K)
    (hnt : ∀ i < 80, jg K i ≠ x) : ∀ i < 80, jg K i + 8 * K.M.n ≤ x ∨ x + 8 * K.M.n ≤ jg K i :=
  fun i hi => hL.ap (jg_mem (by omega)) hx (hnt i hi)

/-! ## The selection's state during the addition -/

/-- The table's address. -/
abbrev tblX (K : JacWinCfg) (base : Addr) : Addr := base + BitVec.ofNat 64 K.tbl

/-- The selection of the magnitude `a ≤ 16`'s entry, after entries `1 … e`:
the broadcasts of `a` and one, the counter, the accumulators (`AccY`) of the
table as in `mem`, whose bytes the state holds. -/
structure SelW (K : JacWinCfg) (base : Addr) (a : Nat) (mem : Mem) (e : Nat) (t : State) : Prop where
  ha : a ≤ 16
  b13 : ∀ l < 2, t.lane .xmm13 l = bcast32 (BitVec.ofNat 32 a)
  b12 : ∀ l < 2, t.lane .xmm12 l = bcast32 (BitVec.ofNat 32 1)
  b14 : ∀ l < 2, t.lane .xmm14 l = bcast32 (BitVec.ofNat 32 (e + 1))
  acc : AccY t mem (tblX K base) (16 * K.np16) a e ((K.np16 + 1) / 2) (qY K.np16)
  reg : InRegions (t.rd ++ t.wr) (tblX K base) (16 * K.np16 * 16)
  tblm : ∀ b < 16 * K.np16 * 16, t.mem (tblX K base + BitVec.ofNat 64 b) = mem (tblX K base + BitVec.ofNat 64 b)
  rdi : t.gpr .rdi = base

/-- `SelW` survives code that keeps the vector registers, the regions, `rdi`
and the table's bytes. -/
theorem SelW.keep {base : Addr} {a e : Nat} {mem : Mem} {t t' : State} (h : SelW K base a mem e t)
    (hx : t'.xmm = t.xmm) (hy : t'.ymmHi = t.ymmHi) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hrdi : t'.gpr .rdi = t.gpr .rdi)
    (hm : ∀ b < 16 * K.np16 * 16, t'.mem (tblX K base + BitVec.ofNat 64 b) = t.mem (tblX K base + BitVec.ofNat 64 b)) :
    SelW K base a mem e t' := by
  have hl := lane_congr hx hy
  exact ⟨h.ha, fun l hl' => by rw [hl]; exact h.b13 l hl', fun l hl' => by rw [hl]; exact h.b12 l hl',
    fun l hl' => by rw [hl]; exact h.b14 l hl', fun c hc l hl' => by rw [hl]; exact h.acc c hc l hl',
    by rw [hrd, hwr]; exact h.reg, fun b hb => by rw [hm b hb]; exact h.tblm b hb, by rw [hrdi]; exact h.rdi⟩

/-- The slots the addition's field operations use: the method's, but the
table's. -/
def addSl (K : JacWinCfg) (x : Nat) : Prop := x ∈ jwSlots K ∧ ∀ i < 80, jg K i ≠ x

theorem addSl_lay (hL : JacWinLay K size) : Lay K.M size (addSl K) :=
  ⟨fun x h => hL.lay.le x h.1, fun x y hx hy => hL.lay.apart x y hx.1 hy.1, fun x h => hL.lay.mo x h.1,
    fun x h => hL.lay.tmp x h.1⟩

/-- A field operation on a slot but the table's keeps the selection's state
(`fprogBI_ok`'s `hstab`). -/
theorem SelW.stab (hL : JacWinLay K size) {base : Addr} {a e : Nat} {mem : Mem} {o : Nat} {t t' : State}
    (hn : base.toNat + size ≤ 2 ^ 64) (ho : addSl K o) (h : SelW K base a mem e t) (hk : OpKeep K.M base o t t')
    (hx : t'.xmm = t.xmm) (hy : t'.ymmHi = t.ymmHi) : SelW K base a mem e t' :=
  h.keep hx hy hk.rd hk.wr (hk.gpr _ (rdi_not_clob _))
    (tblByte_unch hL hk.unch hn fun w hw i hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact notTbl_apart hL ho.1 ho.2 i hi
      · exact hL.lay.tmp _ (jg_mem (by omega)))

/-- `rdx = rdi + tbl`, the table's address. -/
theorem tblAddr_ok (hL : JacWinLay K size) (s : State) {base : Addr} (hd : s.gpr .rdi = base) :
    WP isa (.block K.tblAddr) s fun t => t.gpr .rdx = tblX K base ∧ Keeps [.rdx] s t ∧
      t.xmm = s.xmm ∧ t.ymmHi = s.ymmHi := by
  have ht := hL.tbl31
  apply WP.of_runBlock
  simp only [JacWinCfg.tblAddr, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    Option.bind_some, Option.map_some, imm32_sext ht, hd, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ⟨fun r hr => ?_, rfl, rfl, rfl⟩, rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem chunkLo_mono (K : JacWinCfg) (i : Nat) : K.chunkLo i ≤ K.chunkLo (i + 1) :=
  Nat.div_le_div_right (Nat.mul_le_mul_left _ (by omega))

theorem chunkLo_le (K : JacWinCfg) {i : Nat} (hi : i ≤ K.nOps) : K.chunkLo i ≤ 16 := by
  unfold JacWinCfg.chunkLo
  rcases Nat.eq_zero_or_pos K.nOps with h | h
  · rw [h, Nat.div_zero]; omega
  · exact Nat.div_le_of_le_mul (by rw [Nat.mul_comm K.nOps]; exact Nat.mul_le_mul_left _ hi)

/-- A part of the selection (`fprogBI_ok`'s `hside`): entries `chunkLo i + 1 …
chunkLo (i + 1)`. -/
theorem selChunkW_ok (hL : JacWinLay K size) {base : Addr} {a : Nat} {mem : Mem} (i : Nat)
    {t : State} (hi : i < K.nOps) (h : SelW K base a mem (K.chunkLo i) t) :
    WP isa (.block (K.selChunk i)) t fun t' => SelW K base a mem (K.chunkLo (i + 1)) t' ∧
      SideKeep K.M t t' := by
  have hlo := chunkLo_mono K i
  have hhi := chunkLo_le K (i := i + 1) (by omega)
  obtain ⟨hnp, hst, h2n⟩ := np16_eq hL
  have h2 : 2 ≤ K.np16 := by omega
  have hnp' : (K.np16 + 1) / 2 ≤ 11 := by omega
  unfold JacWinCfg.selChunk
  split
  · next he => exact WP.block_nil ⟨by rw [he]; exact h, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  · rw [WP.block_append_iff]
    refine WP.mono (tblAddr_ok hL t h.rdi) fun t₁ ⟨x₁, k₁, xx₁, xy₁⟩ => ?_
    have hl₁ := lane_congr xx₁ xy₁
    have hm₁ : t₁.mem = t.mem := k₁.2.1
    have hst' : K.st = 16 * K.np16 := hst
    unfold JacWinCfg.selRange
    rw [hst']
    refine WP.mono (selEntriesFromY_ok (st := 16 * K.np16) (q := qY K.np16) (lo := K.chunkLo i) (a := a)
      (X := tblX K base) hnp' (by have := h.ha; omega) (K.chunkLo (i + 1) - K.chunkLo i) (by omega) t₁ x₁
      (fun l hl => by rw [hl₁]; exact h.b13 l hl) (fun l hl => by rw [hl₁]; exact h.b12 l hl)
      (fun l hl => by rw [hl₁]; exact h.b14 l hl)
      (fun e he c hc => by
        rw [k₁.2.2.1, k₁.2.2.2]
        refine VG.CallLay.inRegions_sub h.reg ?_ (by omega)
        have := Nat.mul_le_mul_left (16 * K.np16) (show K.chunkLo i + e + 1 ≤ 16 by omega)
        rw [Nat.mul_succ] at this
        have := qY_le c h2
        omega)
      (fun c hc l hl => by
        rw [hl₁, hm₁]
        exact AccY.congr (n := K.np16) (H := 16) h.ha h2
          (fun b hb => (h.tblm b hb).symm) h.acc c hc l hl))
      fun t' ⟨a', c', k'⟩ => ?_
    have hm' : t'.mem = t.mem := by rw [k'.mem, hm₁]
    have hlo' : K.chunkLo i + (K.chunkLo (i + 1) - K.chunkLo i) = K.chunkLo (i + 1) := by omega
    refine ⟨⟨h.ha, fun l hl => ?_, fun l hl => ?_, fun l hl => by rw [← hlo']; exact c' l hl,
      fun c hc l hl => ?_, by rw [k'.rd, k'.wr, k₁.2.2.1, k₁.2.2.2]; exact h.reg,
      fun b hb => by rw [hm']; exact h.tblm b hb,
      by rw [k'.gpr _ List.not_mem_nil, k₁.1 _ (by decide)]; exact h.rdi⟩,
      ⟨fun r hr => ?_, hm', by rw [k'.rd, k₁.2.2.1], by rw [k'.wr, k₁.2.2.2]⟩⟩
    · rw [k'.lane _ (by
        rintro (⟨c, hc, h'⟩ | h' | h' | h')
        · exact (selAcc_neY c (by omega)).2.2.1 h'.symm
        all_goals exact absurd h' (by decide)), hl₁]
      exact h.b13 l hl
    · rw [k'.lane _ (by
        rintro (⟨c, hc, h'⟩ | h' | h' | h')
        · exact (selAcc_neY c (by omega)).2.1 h'.symm
        all_goals exact absurd h' (by decide)), hl₁]
      exact h.b12 l hl
    · have e1 := a' c hc l hl
      rw [hlo', hm₁] at e1
      rw [e1]
      have hq := qY_le c h2
      exact accVal_congr (n := K.np16) (H := 16) h.ha (by omega) fun b hb => h.tblm b hb
    · rw [k'.gpr _ List.not_mem_nil, k₁.1 r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        exact fun h' => hr (h' ▸ by simp [clob]))]

/-! ## The next digit's selection, before the addition -/

/-- `prepNext`: the magnitude of digit `j - 1` and the counter broadcast, the
accumulators cleared, `rbx = j` again. -/
theorem prepNextW_ok (hL : JacWinLay K size) {base : Addr} {P : Point C} {s₀ : State} {k : Nat}
    (hF : JacWinFixed K C base s₀ P k) {u : State} {j : Nat} (hj1 : 1 ≤ j) (hjJ : j ≤ K.J)
    (hf : JFrame K C base size s₀ u) (hb : u.gpr .rbx = BitVec.ofNat 64 j) :
    WP isa (.block K.prepNext) u fun t =>
      SelW K base (magH 16 (Window5.nib (k + JacWinCfg.offset K.J) (j - 1))) u.mem 0 t ∧
      Keeps [.rax, .rcx, .rdx, .r8] u t := by
  have hs := hf.scr
  have hn := hs.nowrap
  have hbl := hL.bits
  have hg := hL.grid_le
  have hbits := hf.bits hL hF
  obtain ⟨hnp, hst, h2n⟩ := np16_eq hL
  have hnp' : (K.np16 + 1) / 2 ≤ 11 := by omega
  have ha16 := magH_le (H := 16) (v := Window5.nib (k + JacWinCfg.offset K.J) (j - 1))
    (by have := Window5.nib_lt (k + JacWinCfg.offset K.J) (j - 1); omega)
  generalize ha : magH 16 (Window5.nib (k + JacWinCfg.offset K.J) (j - 1)) = a at ha16
  unfold JacWinCfg.prepNext
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (decRbxJ_ok (j := j - 1) u (by rw [hb]; congr 1; omega)) fun u₁ ⟨b₁, k₁, _, _⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (digit_ok K.tc hs₁ (k := k + JacWinCfg.offset K.J) (j := j - 1) (N := 5 * K.J)
    (by show 1 ≤ 5; decide) (by show 5 < 9; decide) (by show 5 * (j - 1) + 5 ≤ 5 * K.J; omega)
    (by show K.bits + 5 * K.J ≤ size; omega) b₁ (fun t ht => by rw [k₁.2.1]; exact hbits t ht))
    fun u₂ ⟨_, r₂, k₂⟩ => ?_
  rw [show K.tc.w = 5 from rfl, Window5.combWin_five, show K.tc.H = 16 from rfl, ha] at r₂
  rw [WP.block_append_iff]
  refine WP.mono (incRbxJ_ok (j := j - 1) u₂ (by rw [k₂.1 _ (by decide), b₁])) fun u₃ ⟨b₃, k₃, _, _⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (selSetY_ok (a := a) u₃ (by omega) (by rw [k₃.1 _ (by decide), r₂]))
    fun u₄ ⟨b13, b12, b14, k₄⟩ => ?_
  have hnp32 : K.np32 ≤ 11 := hnp'
  refine WP.mono (clearAccY_ok K.np32 hnp' u₄) fun t ⟨z₅, k₅⟩ => ?_
  have hm : t.mem = u.mem := by rw [k₅.mem, k₄.mem, k₃.2.1, k₂.2.1, k₁.2.1]
  have hrd : t.rd = u.rd := by rw [k₅.rd, k₄.rd, k₃.2.2.1, k₂.2.2.1, k₁.2.2.1]
  have hwr : t.wr = u.wr := by rw [k₅.wr, k₄.wr, k₃.2.2.2, k₂.2.2.2, k₁.2.2.2]
  have hgr : ∀ r, r ∉ [Reg.rax, .rcx, .rdx, .r8] → t.gpr r = u.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    by_cases hrb : r = .rbx
    · subst hrb
      rw [k₅.gpr _ List.not_mem_nil, k₄.gpr _ (by decide), b₃, hb, show j - 1 + 1 = j by omega]
    · rw [k₅.gpr r List.not_mem_nil, k₄.gpr r (by simp [hr.2.1]), k₃.1 r (by simp [hrb]),
        k₂.1 r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]), k₁.1 r (by simp [hrb])]
  refine ⟨⟨by omega, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun c hc l hl => ?_, ?_,
    fun b _ => (by rw [hm]), (by rw [hgr _ (by simp)]; exact hs.rdi)⟩, ⟨hgr, hm, hrd, hwr⟩⟩
  · rw [k₅.lane _ (fun ⟨c, hc, h⟩ => (selAcc_neY c (by omega)).2.2.1 h.symm)]; exact b13 l hl
  · rw [k₅.lane _ (fun ⟨c, hc, h⟩ => (selAcc_neY c (by omega)).2.1 h.symm)]; exact b12 l hl
  · rw [k₅.lane _ (fun ⟨c, hc, h⟩ => (selAcc_neY c (by omega)).2.2.2.1 h.symm)]; exact b14 l hl
  · rw [z₅ c hc l hl, accVal, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  · rw [hrd, hwr]
    exact ⟨_, List.mem_append_right _ hs.wr, hs.contains (d := K.tbl) (by omega) (by omega)⟩

/-! ## `T` and `R` through code that writes neither -/

/-- A slot of the grid is apart from what the doublings write. -/
theorem dblW_apart (hL : JacWinLay K size) : ∀ w ∈ jwDblW K, ∀ i < 85, jg K i + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ jg K i := by
  intro w hw i hi
  rcases List.mem_append.mp hw with hw | hw
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hw
    have hxo : x ∈ jwOther K := by
      simp only [rcbW, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> jw_mem
    exact (hL.jg_apart (List.mem_append_right _ hxo) hi).symm
  · rw [List.mem_singleton.mp hw]; exact hL.lay.tmp _ (jg_mem hi)

/-- `T`'s entry, in its own state, survives a change of memory apart from the
grid, into a state of the frame. -/
theorem JEnt.unch_self (hL : JacWinLay K size) {base : Addr} {P : Point C} {s₀ : State} {k' i : Nat}
    {u u' : State} (E : JEnt K C base size P s₀ k' i u u) (F : JFrame K C base size s₀ u')
    {W : List (Nat × Nat)} (hU : Unch base W u.mem u'.mem)
    (hW : ∀ w ∈ W, ∀ i < 85, jg K i + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ jg K i) :
    JEnt K C base size P s₀ k' i u' u' := by
  have hn := F.scr.nowrap
  have wv : ∀ i < 85, wordsVal u'.mem base (jg K i) K.M.n = wordsVal u.mem base (jg K i) K.M.n :=
    fun i hi => jgWord_unch hL hU hn hi fun w hw => hW w hw i hi
  have tv : ∀ i < 85, tmv C K.M.n base u' (jg K i) = tmv C K.M.n base u (jg K i) := fun i hi => by
    show toM _ _ _ = toM _ _ _; rw [wv i hi]
  refine ⟨F, Unch.refl _ _ _, ⟨fun _ _ => rfl, rfl, rfl⟩, fun c hc => by rw [wv _ (by omega)]; exact E.lt c hc,
    by rw [tv _ (by omega), tv _ (by omega)]; exact E.z2, by rw [tv _ (by omega), tv _ (by omega), tv _ (by omega)]; exact E.z3,
    fun h => (E.ent h).congr fun c hc => wv (80 + c) (by omega), fun h => by rw [tv _ (by omega)]; exact E.zero h,
    fun h => ?_⟩
  have hm := magH_le (H := 16) (v := Window5.nib k' i) (by have := Window5.nib_lt k' i; omega)
  rw [wv _ (by omega), E.zent h, wv _ (by omega)]

/-- `JEnt`, in its own state, from one into a later state whose registers but
`rbx` and whose memory are the same. -/
theorem JEnt.self (hL : JacWinLay K size) {base : Addr} {P : Point C} {s₀ : State} {k' i : Nat}
    {u v t : State} (E : JEnt K C base size P s₀ k' i u v) (hk : Keeps [.rbx] v t) :
    JEnt K C base size P s₀ k' i t t := by
  have hn := E.fr.scr.nowrap
  have m : t.mem = v.mem := hk.2.1
  have tv : ∀ x, tmv C K.M.n base t x = tmv C K.M.n base v x := fun x => by
    show toM _ _ _ = toM _ _ _; rw [m]
  have hm := magH_le (H := 16) (v := Window5.nib k' i) (by have := Window5.nib_lt k' i; omega)
  refine ⟨E.fr.next hL (E.fr.scr.of_keeps hk (by decide)) ((Keeps.regs hk).mono (by simp [powClob])) (W := [])
      (by rw [m]; exact Unch.refl _ _ _) (by simp), Unch.refl _ _ _, ⟨fun _ _ => rfl, rfl, rfl⟩,
    fun c hc => by rw [m]; exact E.lt c hc, by rw [tv, tv]; exact E.z2, by rw [tv, tv, tv]; exact E.z3,
    fun h => (E.ent h).congr fun c _ => by rw [m], fun h => by rw [tv]; exact E.zero h, fun h => ?_⟩
  rw [m, E.zent h]
  refine (E.unch.wordsVal (fun w hw => ?_) (by
    have h := hL.le (jg_mem (K := K) (i := 5 * (magH 16 (Window5.nib k' i) - 1) + 2) (by omega))
    show jg K _ + 8 * K.M.n ≤ 2 ^ 64; omega)).symm
  rcases List.mem_append.mp hw with hw | hw
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hw
    exact jg_apart K (by have := List.mem_range.mp hc; omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact (hL.jg_apart (x := K.neg) (by jw_mem) (by omega)).symm
    · exact hL.lay.tmp _ (jg_mem (by omega))

/-- The loop's invariant survives a change of memory apart from `R` and the
table, into a state of the frame with the same `rbx`. -/
theorem JInv.of_unch (hL : JacWinLay K size) {base : Addr} {P : Point C} {s₀ : State} {k j : Nat}
    {u u' : State} (I : JInv K C base size P s₀ k j u) (F : JFrame K C base size s₀ u')
    {W : List (Nat × Nat)} (hU : Unch base W u.mem u'.mem)
    (hW : ∀ w ∈ W, (∀ i < 80, jg K i + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ jg K i) ∧
      ∀ x ∈ [K.R.x, K.R.y, K.R.z], x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x)
    (hb : u'.gpr .rbx = u.gpr .rbx) : JInv K C base size P s₀ k j u' := by
  obtain ⟨Q, hQ, hQe, R⟩ := I.st
  have hn := F.scr.nowrap
  have hR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal u'.mem base x K.M.n = wordsVal u.mem base x K.M.n := by
    intro x hx
    have hxs : x ∈ jwSlots K := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl | rfl <;> jw_mem
    exact hU.wordsVal (fun w hw => (hW w hw).2 x hx) (by have := hL.le hxs; omega)
  have tv : ∀ x ∈ [K.R.x, K.R.y, K.R.z], tmv C K.M.n base u' x = tmv C K.M.n base u x := fun x hx => by
    show toM _ _ _ = toM _ _ _; rw [hR x hx]
  refine ⟨⟨Q, hQ, hQe, F, R.tbl.unch hL hU hn (by decide) fun w hw i hi => (hW w hw).1 i (by omega),
    fun x hx => by rw [hR x hx]; exact R.lt x hx, ?_⟩, by rw [hb]; exact I.rbx⟩
  rw [tv _ (by simp), tv _ (by simp), tv _ (by simp)]; exact R.rep

/-! ## The addition, with the selection's parts between its operations -/

theorem slot_notTbl (hL : JacWinLay K size) {x : Nat} (hx : x ∈ jwRo K ++ jwOther K) : ∀ i < 80, jg K i ≠ x :=
  fun i hi e => hL.jg_ne hx (i := i) (by omega) e.symm

theorem T_notTbl (hL : JacWinLay K size) {c : Nat} (hc : c < 5) : ∀ i < 80, jg K i ≠ jg K (80 + c) :=
  fun i hi e => by
    have h1 := jg_apart K (i := i) (j := 80 + c) (by omega)
    have := hL.n0
    rw [e] at h1; omega

/-- `cadd_ok` with `selChunk i` after operation `i`, of a selection `SI`
that operations on slots but the table's keep. -/
theorem caddI_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {base : Addr}
    {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p (· ∈ jwSlots K) [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.z2,
      K.z2 + 8 * K.M.n] E s)
    (h2 : E K.z2 = E K.E.z * E K.E.z) (h3 : E (K.z2 + 8 * K.M.n) = E K.z2 * E K.E.z)
    {SI : Nat → State → Prop}
    (hside : ∀ i t, i < K.nOps → SI i t → WP isa (.block (K.selChunk i)) t fun t' => SI (i + 1) t' ∧ SideKeep K.M t t')
    (hstab : ∀ i o t t', addSl K o → SI i t → OpKeep K.M base o t t' → t'.xmm = t.xmm → t'.ymmHi = t.ymmHi →
      t'.syms = t.syms → SI i t')
    (hsc : ∀ op ∈ K.addOps, scalCode (opProg K.M op) = true) (hS : SI 0 s) :
    WP isa (fprogBI K.M K.addOps K.selChunk 0).inline s fun t =>
      ProgKeep K.M base (rcbW K.S K.D) s t ∧ (∃ E' : Nat → Fe C,
        Inv K.M base size C.p (· ∈ jwSlots K) ([K.D.x, K.D.y, K.D.z] ++ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y,
          K.E.z, K.z2, K.z2 + 8 * K.M.n]) E' t ∧
        (E' K.D.x, E' K.D.y, E' K.D.z) = jacAddF (E K.R.x) (E K.R.y) (E K.R.z) (E K.E.x) (E K.E.y) (E K.E.z)) ∧
      SI K.nOps t := by
  have hn0 := hL.n0
  have hgW := hL.gW
  have hA := hL.addApart
  have h2a : K.z2 ∉ rcbW K.S K.D := by rw [hL.Tz2]; exact hgW 3 (by decide)
  have h3a : K.z2 + 8 * K.M.n ∉ rcbW K.S K.D := by rw [hL.Tz3]; exact hgW 4 (by decide)
  have hSl : ∀ x ∈ (rcbW K.S K.D ++ rcbR K.S K.R K.E) ++ [K.z2, K.z2 + 8 * K.M.n], addSl K x := by
    intro x hx
    simp only [rcbW, rcbR, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rw [hL.Tz3, hL.Tx, hL.Ty, hL.Tz, hL.Tz2] at hx
    rcases hx with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h]
    all_goals first
      | exact ⟨jg_mem (by decide), T_notTbl hL (c := 0) (by decide)⟩
      | exact ⟨jg_mem (by decide), T_notTbl hL (c := 1) (by decide)⟩
      | exact ⟨jg_mem (by decide), T_notTbl hL (c := 2) (by decide)⟩
      | exact ⟨jg_mem (by decide), T_notTbl hL (c := 3) (by decide)⟩
      | exact ⟨jg_mem (by decide), T_notTbl hL (c := 4) (by decide)⟩
      | exact ⟨by jw_mem, slot_notTbl hL (by jw_mem)⟩
  have hV : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.z2, K.z2 + 8 * K.M.n], addSl K x := by
    intro x hx
    refine hSl x ?_
    simp only [rcbW, rcbR, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hx ⊢
    rcases hx with h | h | h | h | h | h | h | h <;> simp [h]
  have hI' : Inv K.M base size C.p (addSl K) [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.z2,
      K.z2 + 8 * K.M.n] E s := ⟨hI.scr, hI.mod, hV, hI.lt, hI.val⟩
  have hr : readsOk K.addOps [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.z2, K.z2 + 8 * K.M.n] = true := by
    rw [JacWinCfg.addOps, CachedJac.head_eq K.M.n K.S K.R K.E K.D K.z2,
      CachedJac.tail_eq K.M.n K.S K.R K.E K.D K.z2, ← List.map_append]
    refine readsOk_mono (readsOk_rename (CachedJac.rename K.M.n K.S K.R K.E K.D K.z2)
      (show readsOk (CachedJac.headN ++ jacTailN) [11, 12, 13, 14, 15, 16, 17, 18] = true by decide))
      fun x hx => ?_
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    rcases hx with h | h | h | h | h | h | h | h <;> rw [h] <;> simp [CachedJac.rename, rcbσ, rcbW, rcbR]
  have hs : ∀ op ∈ K.addOps, ∀ x ∈ op.out :: op.ins, addSl K x := by
    rw [JacWinCfg.addOps, CachedJac.head_eq K.M.n K.S K.R K.E K.D K.z2,
      CachedJac.tail_eq K.M.n K.S K.R K.E K.D K.z2, ← List.map_append]
    exact fun op hop x hx => hSl x (CachedJac.slots op hop x hx)
  refine WP.mono (fprogBI_ok (addSl_lay hL) hp hside hstab K.addOps 0 (Nat.le_of_eq (Nat.zero_add _)) hsc
    hI' hS hs hr) fun t ⟨kt, it, st⟩ => ?_
  have it' := it.sub (V' := [K.D.x, K.D.y, K.D.z] ++ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.z2,
    K.z2 + 8 * K.M.n]) fun x hx => by
    rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx | hx
    · right
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp [JacWinCfg.addOps, jacTail, FOp.out]
    · exact Or.inl hx
  refine ⟨kt.mono ?_, ⟨_, ⟨it'.scr, it'.mod, fun x hx => (it'.sl x hx).1, it'.lt, it'.val⟩,
    CachedJac.full_run hA h2a h3a E h2 h3⟩, by rw [Nat.zero_add] at st; exact st⟩
  intro x hx
  obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hx
  rw [JacWinCfg.addOps, CachedJac.head_eq K.M.n K.S K.R K.E K.D K.z2,
    CachedJac.tail_eq K.M.n K.S K.R K.E K.D K.z2, ← List.map_append] at hop
  exact CachedJac.out (show ∀ op ∈ CachedJac.headN ++ jacTailN, op.out < 9 by decide) hop

/-! ## After the masks: the next entry into `T` -/

/-- `T`'s slots, `-y` and the temporary area are apart from the table's slots
and from `R`. -/
theorem entW_apart (hL : JacWinLay K size) : ∀ w ∈ (List.range 5).map (fun c => (jg K (80 + c), 8 * K.M.n)) ++
    [(K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n)], (∀ i < 80, jg K i + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ jg K i) ∧
      ∀ x ∈ [K.R.x, K.R.y, K.R.z], x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x := by
  intro w hw
  have hR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∈ jwRo K ++ jwOther K := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> jw_mem
  rcases List.mem_append.mp hw with hw | hw
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hw
    have hc' := List.mem_range.mp hc
    exact ⟨fun i hi => jg_apart K (by omega), fun x hx => hL.jg_apart (hR x hx) (by omega)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · refine ⟨fun i hi => (hL.jg_apart (x := K.neg) (by jw_mem) (by omega)).symm, fun x hx => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact hL.ap_oth (i := 0) (j := 6) (by decide) (by decide) (by decide)
      · exact hL.ap_oth (i := 1) (j := 6) (by decide) (by decide) (by decide)
      · exact hL.ap_oth (i := 2) (j := 6) (by decide) (by decide) (by decide)
    · exact ⟨fun i hi => hL.lay.tmp _ (jg_mem (by omega)), fun x hx => hL.lay.tmp x (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl | rfl <;> jw_mem)⟩

/-- `finNext`: digit `i`'s entry, selected into the accumulators, into `T`,
negated for a negative digit, `rbx = i + 1` again, and `ZF` for `i = 0`. -/
theorem finNextW_ok (hL : JacWinLay K size) {base : Addr} {P : Point C} {s₀ : State} {k : Nat}
    (hF : JacWinFixed K C base s₀ P k) {v : State} {i : Nat} (hi : i + 1 < K.J)
    (hf : JFrame K C base size s₀ v) (hT : JTblOk K C base P 16 v) (hb : v.gpr .rbx = BitVec.ofNat 64 (i + 1))
    {mem : Mem} (hW : SelW K base (magH 16 (Window5.nib (k + JacWinCfg.offset K.J) i)) mem 16 v) :
    WP isa (.block K.finNext) v fun t => JEnt K C base size P s₀ (k + JacWinCfg.offset K.J) i t t ∧
      Unch base ((List.range 5).map (fun c => (jg K (80 + c), 8 * K.M.n)) ++
        [(K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n)]) v.mem t.mem ∧
      t.gpr .rbx = BitVec.ofNat 64 (i + 1) ∧ t.zf = some (decide (i + 1 = 1)) := by
  have hs := hf.scr
  have hn := hs.nowrap
  have hbl := hL.bits
  have hg := hL.grid_le
  have hJ := hL.J
  obtain ⟨hnp, hst, h2n⟩ := np16_eq hL
  have h2 : 2 ≤ K.np16 := by omega
  have hT80 : K.T = jg K 80 := hL.T80
  rw [JacWinCfg.finNext]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (decRbxJ_ok (j := i) v hb) fun u ⟨b₁, k₁, x₁, y₁⟩ => ?_
  have hsu := hs.of_keeps k₁ (by decide)
  have mu : u.mem = v.mem := k₁.2.1
  have fu : JFrame K C base size s₀ u := hf.next hL hsu ((Keeps.regs k₁).mono (by simp [powClob])) (W := [])
    (by rw [mu]; exact Unch.refl _ _ _) (by simp)
  have Tu : JTblOk K C base P 16 u := fun m h1 hm => (hT m h1 hm).congr fun c _ => by rw [mu]
  have Wu := hW.keep x₁ y₁ k₁.2.2.1 k₁.2.2.2 (k₁.1 _ (by decide)) fun b _ => by rw [mu]
  rw [WP.block_append_iff, JacWinCfg.storeT, WP.block_append_iff]
  refine WP.mono (storeAccY_ok (o := K.T) (n := K.np16) (q := qY K.np16)
    (V := accVal mem (tblX K base) (16 * K.np16) (16 * ·) (magH 16 (Window5.nib (k + JacWinCfg.offset K.J) i)) 16)
    (by rw [hT80]; unfold jg; omega) K.np32 u hsu (fun c _ => qY_le c h2) (fun c hc l hl => Wu.acc c hc l hl))
    fun t₁ ⟨a₁, O₁, g₁, r₁, w₁, _⟩ => ?_
  refine WP.mono (vzeroupper_ok t₁) fun t₂ ⟨m₂, g₂, r₂, w₂⟩ => ?_
  have hst₂ : Scr t₂ base size := ⟨by rw [g₂, g₁]; exact hsu.rdi, by rw [w₂, w₁]; exact hsu.wr, hn⟩
  have ha16 := magH_le (H := 16) (v := Window5.nib (k + JacWinCfg.offset K.J) i)
    (by have := Window5.nib_lt (k + JacWinCfg.offset K.J) i; omega)
  have a₂ : ∀ c < K.np16, t₂.mem.readW (off base (K.T + 16 * c)) 128 =
      accVal u.mem (base + BitVec.ofNat 64 K.tbl) (16 * K.np16) (16 * ·)
        (magH 16 (Window5.nib (k + JacWinCfg.offset K.J) i)) 16 c := by
    intro j hj
    obtain ⟨c, hc, l, hl, e⟩ := qY_cover h2 hj
    have h := a₁ c hc l hl
    rw [e] at h
    rw [m₂, h]
    exact accVal_congr (n := K.np16) (H := 16) ha16 hj fun b hb => (Wu.tblm b hb).symm
  obtain ⟨e₂, O₂⟩ := jsel_post hL hsu ha16 a₂ (by rw [m₂]; exact O₁)
  have U₂ : Unch base (jwLoopW K) u.mem t₂.mem := (outside_grid5 (b := 80) O₂).mono fun w hw => by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hw; exact T_loopW K (List.mem_range.mp hc)
  have F₂ := fu.next hL hst₂ ⟨fun r _ => by rw [g₂, g₁], by rw [r₂, r₁], by rw [w₂, w₁]⟩ U₂ (jwLoopW_sub K)
  rw [WP.block_append_iff]
  refine WP.mono (digit_ok K.tc hst₂ (k := k + JacWinCfg.offset K.J) (j := i) (N := 5 * K.J)
    (by show 1 ≤ 5; decide) (by show 5 < 9; decide) (by show 5 * i + 5 ≤ 5 * K.J; omega)
    (by show K.bits + 5 * K.J ≤ size; omega) (by rw [g₂, g₁]; exact b₁) (F₂.bits hL hF)) fun t₃ ⟨_, _, k₃⟩ => ?_
  have m₃ : t₃.mem = t₂.mem := k₃.2.1
  rw [WP.block_append_iff]
  refine WP.mono (jneg_ok hL hF (j := i) (by omega) fu Tu (fun c hc => by rw [m₃]; exact e₂ c hc)
    ⟨fun r hr => by rw [k₃.1 r hr, g₂, g₁], by rw [k₃.2.2.1, r₂, r₁], by rw [k₃.2.2.2, w₂, w₁]⟩
    (by rw [m₃]; exact O₂) (by rw [k₃.1 _ (by decide), g₂, g₁]; exact b₁)) fun t₄ E₄ => ?_
  have hb₄ : t₄.gpr .rbx = BitVec.ofNat 64 i := by rw [E₄.keep.gpr _ (rbx_not_clob _), b₁]
  rw [show ([.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm 1)] : List Instr) =
    [.alu .add .rbx (.imm 1)] ++ [.alu .cmp .rbx (.imm (BitVec.ofNat 32 1))] from rfl, WP.block_append_iff]
  refine WP.mono (incRbxJ_ok t₄ hb₄) fun t₅ ⟨b₅, k₅, _, _⟩ => ?_
  refine WP.mono (cmpRbx_ok t₅ (j := i + 1) (i := 1) (by decide) (by omega) b₅) fun t ⟨z₆, k₆⟩ => ?_
  have k₅₆ : Keeps [.rbx] t₄ t := k₅.trans (k₆.mono (by simp))
  refine ⟨E₄.self hL k₅₆, ?_, by rw [k₆.1 _ (by simp), b₅], z₆⟩
  rw [k₆.2.1, k₅.2.1, ← mu]; exact E₄.unch

/-! ## The iterations -/

theorem winPipeOk_facts {K : JacWinCfg} (hP : K.pipeOk = true) :
    3 ≤ K.J ∧ K.masks.all scalarI = true ∧ ∀ op ∈ K.addOps, scalCode (opProg K.M op) = true := by
  unfold JacWinCfg.pipeOk at hP
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hP
  exact ⟨hP.1.1.2, by simp only [List.all_eq_true]; exact hP.1.2, hP.2⟩

theorem winNOps_pos (K : JacWinCfg) : 0 < K.nOps := by
  unfold JacWinCfg.nOps JacWinCfg.addOps
  simp [CachedJac.head]

theorem chunkLo_nOps (K : JacWinCfg) : K.chunkLo K.nOps = 16 := by
  unfold JacWinCfg.chunkLo; exact Nat.mul_div_cancel _ (winNOps_pos K)

theorem RSt.keeps4 (hL : JacWinLay K size) {base : Addr} {P Q : Point C} {s₀ s s' : State}
    (h : RSt K C base size P s₀ Q s) (hk : Keeps [.rax, .rcx, .rdx, .r8] s s') : RSt K C base size P s₀ Q s' := by
  have m : s'.mem = s.mem := hk.2.1
  have e : ∀ x, tmv C K.M.n base s' x = tmv C K.M.n base s x := fun x => by
    show toM _ _ _ = toM _ _ _; rw [m]
  refine ⟨h.fr.next hL (h.fr.scr.of_keeps hk (by decide)) ((Keeps.regs hk).mono (sub_powClob (by decide)))
    (W := []) (by rw [m]; exact Unch.refl _ _ _) (by simp), fun j h1 hj => (h.tbl j h1 hj).congr
    fun c _ => by rw [m], fun x hx => by rw [m]; exact h.lt x hx, by rw [e, e, e]; exact h.rep⟩

/-- A pipelined iteration, `2 ≤ j ≤ J - 1`, digit `j - 1`'s entry in `T`:
`R = 32 R + [d_{j-1}]P`, digit `j - 2`'s entry into `T`. -/
theorem jstepP_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C)
    (hO : PrimeOrder C) {dbl : Pt → Prog isa} (hD : DblOk K.M K.S C dbl) {P : Point C}
    (hP : onCurve C P = true) (hP0 : P ≠ .infinity) (hn17 : 17 ≤ C.n % 32) (hn64 : 64 ≤ C.n)
    {base : Addr} {s₀ : State} {k : Nat} (hF : JacWinFixed K C base s₀ P k) (hPk : K.pipeOk = true) {j : Nat}
    (hj2 : 2 ≤ j) (hjJ : j + 1 ≤ K.J) {s : State} (hI : JInv K C base size P s₀ k j s)
    (hE : JEnt K C base size P s₀ (k + JacWinCfg.offset K.J) (j - 1) s s) :
    WP isa (K.stepP dbl).inline s fun t => (JInv K C base size P s₀ k (j - 1) t ∧
      JEnt K C base size P s₀ (k + JacWinCfg.offset K.J) (j - 2) t t) ∧
      t.zf = some (decide (j - 1 = 1)) := by
  obtain ⟨-, hscm, hsc⟩ := winPipeOk_facts hPk
  obtain ⟨Q, hQ, hQe, R₀⟩ := hI.st
  have hn := R₀.fr.scr.nowrap
  have hJ := hL.J
  unfold JacWinCfg.stepP
  simp only [Code.inline]
  refine WP.seq (WP.mono (decRbx_ok s (by omega) (by omega) hI.rbx) fun s₁ ⟨b₁, k₁⟩ => ?_)
  have R₁ := R₀.rbxKeeps hL k₁
  rw [← mul_one_pt Q] at R₁
  have E₁ := hE.self hL k₁
  refine WP.seq (WP.mono (dbls_ok hL hC hD hQ (j := j - 1) (by omega) b₁ R₁) fun s₂ ⟨R₂, b₂, U₂⟩ => ?_)
  have E₂ := E₁.unch_self hL R₂.fr U₂ (dblW_apart hL)
  refine WP.seq (WP.mono (prepNextW_ok hL hF (j := j - 1) (by omega) (by omega) R₂.fr b₂)
    fun s₃ ⟨S₃, k₃⟩ => ?_)
  have R₃ : RSt K C base size P s₀ (mul 32 Q) s₃ := R₂.keeps4 hL k₃
  have E₃ := E₂.unch_self hL R₃.fr (W := []) (by rw [k₃.2.1]; exact Unch.refl _ _ _) (by simp)
  have b₃ : s₃.gpr .rbx = BitVec.ofNat 64 (j - 1) := by rw [k₃.1 _ (by decide), b₂]
  obtain ⟨I₄, h2, h3⟩ := jaddIn hL R₃ E₃
  rw [show j - 1 - 1 = j - 2 by omega] at S₃
  refine WP.seq (WP.mono (caddI_ok hL hp I₄ h2 h3
    (SI := fun i t => SelW K base (magH 16 (Window5.nib (k + JacWinCfg.offset K.J) (j - 2))) s₂.mem (K.chunkLo i) t)
    (fun i t hi h => selChunkW_ok hL i hi h) (fun i o t t' ho h hk hx hy _ => SelW.stab hL hn ho h hk hx hy) hsc
    (by rw [show K.chunkLo 0 = 0 by simp [JacWinCfg.chunkLo]]; exact S₃)) fun s₅ ⟨k₅, ⟨E₅, I₅, v₅⟩, S₅⟩ => ?_)
  rw [chunkLo_nOps] at S₅
  rw [WP.block_append_iff]
  refine WP.mono (WP.vecKeep (c := .block K.masks) hscm
    (jmaskTail_ok hL hp hC hM3 hO hP hP0 hn17 hn64 hF (by omega) (by omega) hQ hQe R₃ b₃ E₃ k₅ I₅ v₅))
    fun s₆ ⟨⟨I₆, U₆⟩, x₆, y₆⟩ => ?_
  have hrd₅ : s₅.rd = s₀.rd := by rw [k₅.rd]; exact R₃.fr.keep.rd
  have hwr₅ : s₅.wr = s₀.wr := by rw [k₅.wr]; exact R₃.fr.keep.wr
  obtain ⟨Q₆, -, -, R₆⟩ := I₆.st
  have S₆ := S₅.keep x₆ y₆ (by rw [R₆.fr.keep.rd, hrd₅]) (by rw [R₆.fr.keep.wr, hwr₅])
    (by rw [R₆.fr.scr.rdi, (k₅.scr R₃.fr.scr).rdi])
    (tblByte_unch hL U₆ hn fun w hw i hi => loopW_apart hL hi w hw)
  refine WP.mono (finNextW_ok hL hF (i := j - 2) (by omega) R₆.fr R₆.tbl (by rw [I₆.rbx]; congr 1; omega) S₆)
    fun t ⟨E₇, U₇, b₇, z₇⟩ => ?_
  refine ⟨⟨I₆.of_unch hL E₇.fr U₇ (entW_apart hL) (by rw [b₇, I₆.rbx]; congr 1; omega), E₇⟩, ?_⟩
  rw [z₇]; congr 1; exact decide_eq_decide.mpr (by omega)

/-- The last iteration, digit `0`'s entry in `T`: `R = 32 R + [d_0]P`. -/
theorem jstepLast_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C)
    (hO : PrimeOrder C) {dbl : Pt → Prog isa} (hD : DblOk K.M K.S C dbl) {P : Point C}
    (hP : onCurve C P = true) (hP0 : P ≠ .infinity) (hn17 : 17 ≤ C.n % 32) (hn64 : 64 ≤ C.n)
    {base : Addr} {s₀ : State} {k : Nat} (hF : JacWinFixed K C base s₀ P k) {s : State}
    (hI : JInv K C base size P s₀ k 1 s) (hE : JEnt K C base size P s₀ (k + JacWinCfg.offset K.J) 0 s s) :
    WP isa (K.stepLast dbl).inline s fun t => JInv K C base size P s₀ k 0 t := by
  obtain ⟨Q, hQ, hQe, R₀⟩ := hI.st
  have hJ := hL.J
  unfold JacWinCfg.stepLast
  simp only [Code.inline]
  refine WP.seq (WP.mono (decRbx_ok s (by omega) (by omega) hI.rbx) fun s₁ ⟨b₁, k₁⟩ => ?_)
  have R₁ := R₀.rbxKeeps hL k₁
  rw [← mul_one_pt Q] at R₁
  have E₁ := hE.self hL k₁
  refine WP.seq (WP.mono (dbls_ok hL hC hD hQ (j := 1 - 1) (by omega) b₁ R₁) fun s₂ ⟨R₂, b₂, U₂⟩ => ?_)
  have E₂ := E₁.unch_self hL R₂.fr U₂ (dblW_apart hL)
  obtain ⟨I₄, h2, h3⟩ := jaddIn (j := 1) hL R₂ E₂
  refine WP.seq (WP.mono (cadd_ok hL hp I₄ (fun x hx => hx) h2 h3) fun s₅ ⟨k₅, E₅, I₅, v₅⟩ => ?_)
  exact WP.mono (jmaskTail_ok hL hp hC hM3 hO hP hP0 hn17 hn64 hF (j := 1) (by omega) (by omega) hQ hQe R₂ b₂ E₂
    k₅ I₅ v₅) fun t ⟨I₆, _⟩ => I₆

/-- `firstP`: the top digit's entry into `R`, `rbx = J - 1`, and digit
`J - 2`'s entry into `T`. -/
theorem jfirstP_ok (hL : JacWinLay K size) (hC : Law C) {base : Addr} {P : Point C}
    (hP : onCurve C P = true) {s₀ s : State} {k : Nat} (hF : JacWinFixed K C base s₀ P k)
    (hkJ : k + JacWinCfg.offset K.J < 32 ^ K.J) (hJ3 : 3 ≤ K.J) (hf : JFrame K C base size s₀ s)
    (hT : JTblOk K C base P 16 s) :
    WP isa (.block K.firstP) s fun t => JInv K C base size P s₀ k (K.J - 1) t ∧
      JEnt K C base size P s₀ (k + JacWinCfg.offset K.J) (K.J - 2) t t := by
  have hn := hf.scr.nowrap
  have hJ := hL.J
  rw [JacWinCfg.firstP, show K.first ++ [.alu .sub .rbx (.imm 1)] ++ K.tc.digit ++ K.select ++ K.tc.negY ++
      [.alu .add .rbx (.imm 1)] = K.first ++ ([.alu .sub .rbx (.imm 1)] ++ ((K.tc.digit ++ K.select) ++
      (K.tc.negY ++ [.alu .add .rbx (.imm 1)]))) by simp only [List.append_assoc], WP.block_append_iff]
  refine WP.mono (jfirst_ok hL hC hP hF hkJ hf hT) fun s₂ ⟨I₂, _⟩ => ?_
  obtain ⟨Q₂, -, -, R₂⟩ := I₂.st
  rw [WP.block_append_iff]
  refine WP.mono (decRbx_ok s₂ (j := K.J - 1) (by omega) (by omega) I₂.rbx) fun s₃ ⟨b₃, k₃⟩ => ?_
  have R₃ := R₂.rbxKeeps hL k₃
  rw [show K.J - 1 - 1 = K.J - 2 by omega] at b₃
  rw [WP.block_append_iff]
  refine WP.mono (jentry_ok hL hF (j := K.J - 2) (by omega) R₃.fr R₃.tbl b₃) fun s₄ h₄ => ?_
  rw [WP.block_append_iff]
  refine WP.mono h₄ fun s₅ E₅ => ?_
  have hb₅ : s₅.gpr .rbx = BitVec.ofNat 64 (K.J - 2) := by rw [E₅.keep.gpr _ (rbx_not_clob _), b₃]
  refine WP.mono (incRbxJ_ok s₅ hb₅) fun t ⟨b₆, k₆, _, _⟩ => ?_
  have E₆ := E₅.self hL k₆
  refine ⟨I₂.of_unch hL E₆.fr (W := (List.range 5).map (fun c => (jg K (80 + c), 8 * K.M.n)) ++
      [(K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n)]) (by rw [k₆.2.1, ← k₃.2.1]; exact E₅.unch) (entW_apart hL)
    (by rw [b₆, I₂.rbx]; congr 1; omega), E₆⟩

/-- `windowP`: `[k]P` into `R`, in projective coordinates, if `k < n`; only
`powClob` and `jwW` change. -/
theorem jwindowP_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C)
    (hM3 : AM3 C) (hO : PrimeOrder C) {dbl : Pt → Prog isa} (hD : DblOk K.M K.S C dbl)
    (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p) (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1)
    (hn17 : 17 ≤ C.n % 32) (hn64 : 64 ≤ C.n) {P : Point C} (hP : onCurve C P = true) {k : Nat}
    (hkJ : k + JacWinCfg.offset K.J < 32 ^ K.J) (hPk : K.pipeOk = true) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkW K.M size C.p s.mem base) (hF : JacWinFixed K C base s P k) :
    WP isa (K.windowP dbl).inline s fun s' => KeepRegs (powClob K.M.n) s s' ∧
      Unch base (jwW K) s.mem s'.mem ∧ ModOkW K.M size C.p s'.mem base ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      (k < C.n → Rep C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y)
        (tmv C K.M.n base s' K.R.z) (mul k P)) := by
  obtain ⟨hJ3, -, -⟩ := winPipeOk_facts hPk
  have hP0 : P ≠ .infinity := by
    intro h
    have := hF.pt
    rw [h, hF.pz] at this
    exact hC.one_ne_zero this.2.2
  unfold JacWinCfg.windowP
  simp only [Code.inline]
  refine WP.seq (WP.mono (jbuild_ok hL hp hC hM3 hO hP hP0 (by omega) hs hM hF) fun s₁ ⟨F₁, T₁⟩ => ?_)
  refine WP.seq (WP.mono (jfirstP_ok hL hC hP hF hkJ hJ3 F₁ T₁) fun s₂ ⟨I₂, E₂⟩ => ?_)
  refine WP.seq (WP.mono (countLoop_ok (Q := fun t => JInv K C base size P s k 1 t ∧
      JEnt K C base size P s (k + JacWinCfg.offset K.J) 0 t t)
    (Inv := fun r t => JInv K C base size P s k (r + 1) t ∧ JEnt K C base size P s (k + JacWinCfg.offset K.J) r t t)
    (n := K.J - 2)
    (fun r t h1 h2 hi => WP.mono (jstepP_ok hL hp hC hM3 hO hD hP hP0 hn17 hn64 hF hPk (j := r + 1) (by omega)
      (by omega) hi.1 (by rw [show r + 1 - 1 = r by omega]; exact hi.2)) fun t' ⟨⟨I, E⟩, z⟩ =>
        ⟨⟨by rw [show r - 1 + 1 = r + 1 - 1 by omega]; exact I, by rw [show r - 1 = r + 1 - 2 by omega]; exact E⟩,
          by rw [z]; congr 1; exact decide_eq_decide.mpr (by omega)⟩)
    (fun t h => h) (by omega) (by rw [show K.J - 2 + 1 = K.J - 1 by omega]; exact ⟨I₂, E₂⟩)) fun s₃ ⟨I₃, E₃⟩ => ?_)
  refine WP.seq (WP.mono (jstepLast_ok hL hp hC hM3 hO hD hP hP0 hn17 hn64 hF I₃ E₃) fun s₄ I₄ => ?_)
  exact jout_ok hL hp hC hpn hone_lt hone hF I₄

/-- `[k]P` into `R`, in projective coordinates, for `k` whose bits plus
`offset J` are the table at `K.bits`, if `k < n`; only `powClob` and `jwW`
change: `window`, pipelined or not (`jwindowP_ok`, `winJac0_ok`). -/
theorem winJac_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C)
    (hM3 : AM3 C) (hO : PrimeOrder C) {dbl : Pt → Prog isa} (hD : DblOk K.M K.S C dbl)
    (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p) (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1)
    (hn17 : 17 ≤ C.n % 32) (hn64 : 64 ≤ C.n) {P : Point C} (hP : onCurve C P = true) {k : Nat}
    (hkJ : k + JacWinCfg.offset K.J < 32 ^ K.J) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkW K.M size C.p s.mem base) (hF : JacWinFixed K C base s P k) :
    WP isa (K.window dbl).inline s fun s' => KeepRegs (powClob K.M.n) s s' ∧
      Unch base (jwW K) s.mem s'.mem ∧ ModOkW K.M size C.p s'.mem base ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      (k < C.n → Rep C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y)
        (tmv C K.M.n base s' K.R.z) (mul k P)) := by
  unfold JacWinCfg.window
  cases hPk : K.pipeOk
  · exact winJac0_ok hL hp hC hM3 hO hD hpn hone_lt hone hn17 hn64 hP hkJ hs hM hF
  · exact jwindowP_ok hL hp hC hM3 hO hD hpn hone_lt hone hn17 hn64 hP hkJ hPk hs hM hF

end VG.Proof.Weierstrass.X86_64
