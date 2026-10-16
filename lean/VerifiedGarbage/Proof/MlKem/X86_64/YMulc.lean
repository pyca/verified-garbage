module

public import VerifiedGarbage.Proof.MlKem.X86_64.YNttPack
public import VerifiedGarbage.Proof.MlKem.X86_64.Lazy
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# ML-KEM on x86-64: a word operation on every word of `S`

`ymulc c body` runs `body` on the words of `S`, sixteen at a time, with the
word `cw` of `c` in every word of `ymm13`. If `body` leaves `g w z` in each
word of `xmm3` from its word `w` and the word `z` of `xmm13` (`MapOk`), the
words of `S` become `g w cw` (`ymulc_ok`): the reductions of the lazy layers
(`yred`, `yredC`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-- `body` leaves `g w z` in each word of `xmm3`, from its word `w` and the
word `z` of `xmm13`, and changes only `xmm3` and `xmm2`. -/
def MapOk (body : List Instr) (g : BitVec 16 → BitVec 16 → BitVec 16) : Prop :=
  ∀ t : State, VConsts t → WP isa (.block body) t fun t' =>
    WLanes (t'.xmm .xmm3) (fun i => g (word (t.xmm .xmm3) i) (word (t.xmm .xmm13) i)) ∧ XOnly [.xmm3, .xmm2] t t'

theorem vmont_map : MapOk (vmont .xmm3 .xmm13 .xmm2) W.montW := fun _ hc =>
  WP.mono (vmont_ok (by decide) (by decide) (by decide) (by decide) (by decide) hc) fun _ ⟨l, o⟩ =>
    ⟨l, o.mono (by simp)⟩

theorem vmontc_map : MapOk (vmont .xmm3 .xmm13 .xmm2 ++ vcadd .xmm3 .xmm2) (fun w z => W.caddW (W.montW w z)) :=
  fun t hc => by
  rw [WP.block_append_iff]
  refine WP.mono (vmont_ok (d := .xmm3) (z := .xmm13) (t := .xmm2) (by decide) (by decide) (by decide)
    (by decide) (by decide) hc) fun t1 ⟨l1, o1⟩ => ?_
  refine WP.mono (vcadd_ok (d := .xmm3) (t := .xmm2) (by decide) (by decide)
    (o1.consts hc (by decide) (by decide))) fun t2 ⟨l2, o2⟩ => ⟨fun i hi => ?_, (o1.trans o2).mono (by simp)⟩
  rw [l2 i hi]; dsimp only; rw [l1 i hi]

/-- The words of `S` after `ymulc`. -/
theorem ymulc_ok {c : BitVec 32} {cw : BitVec 16} (hcw : ∀ i < 8, word (ofDwords c c c c) i = cw)
    {body : List Instr} {g : BitVec 16 → BitVec 16 → BitVec 16} (hY : laneSseBlock (toY body) = some body)
    (hb : MapOk body g) {sP : Addr} {G : WPoly} {s : State} (hc : YConsts s) (hsi : s.gpr .rsi = sP)
    (hS : S16R (· = ·) s.mem (spW sP) G) (hw : pR sP ∈ s.wr) :
    WP isa (ymulc c body) s fun s' => S16R (· = ·) s'.mem (spW sP) (G.map (g · cw)) ∧ BInvY sP s s' := by
  simp only [ymulc]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Q := fun (w : State) => w.gpr .rdx = spW sP ∧ GOnly [.rdx] s w ∧ w.ymmHi = s.ymmHi)
    (by
      simp only [leaR, oS]
      vrunm [sx_ofNat (show 256 < 2 ^ 31 by decide), hsi, RegUpd.ymmHi_setReg]
      exact ⟨by gonly, rfl⟩) fun w1 ⟨hdx1, og, hy⟩ => ?_
  refine WP.mono (yconst_ok .xmm13 _ w1) fun w2 ⟨q2, k2, m2, x2, o2⟩ => ?_
  have hl1 := GOnly.lane og hy
  have cw2 : YConsts w2 := fun l hl => by
    have h15 := (hc l hl).q; have h14 := (hc l hl).qinv
    rw [State.proj_xmm] at h15 h14
    exact ⟨by rw [State.proj_xmm, o2 _ (by decide) l hl, hl1]; exact h15,
      by rw [State.proj_xmm, o2 _ (by decide) l hl, hl1]; exact h14⟩
  have kw2 : Keep [.r8, .rcx, .rdx, .rax] s w2 := (og.keep.trans k2).mono (by simp)
  have hdx2 : w2.gpr .rdx = spW sP := by rw [k2.gpr (by decide), hdx1]
  have mw2 : w2.mem = s.mem := by rw [m2, og.mem]
  have xw2 : w2.mxcsr = s.mxcsr := by rw [x2, og.mxcsr]
  refine WP.mono (wp_rcxLoopY (N := 16) (by decide) (by decide)
    (fun u v => (∀ j < 256, wordAt v.mem (spW sP) j = if j < 16 * u then g G[j]! cw else G[j]!) ∧
      v.gpr .rdx = wAddr (spW sP) (16 * u) ∧ (∀ l < 2, v.lane .xmm13 l = ofDwords c c c c) ∧
      BInvY sP s v)
    (fun v o hy' _ => ⟨fun j hj => by rw [ite_eq_right (by bdd_omega), o.mem, mw2]; exact hS j hj,
      by rw [o.keep.gpr (by decide), hdx2, wAddr]; simp,
      fun l hl => by rw [GOnly.lane o hy']; exact q2 l hl,
      ⟨(kw2.trans o.keep).mono (by simp), by rw [o.mem, mw2]; exact Frame.refl _ _,
        lanes_gpr (s := w2) (GOnly.lane o hy') (YOnly.refl [] w2) cw2 (by decide) (by decide),
        by rw [o.mxcsr, xw2]⟩⟩)
    (fun u hu v ⟨hP, hdx', hz', hb'⟩ => ?_))
    fun v ⟨hP, _, _, hb'⟩ => ⟨fun j hj => by
      rw [hP j hj, ite_eq_left (by bdd_omega), getElem!_pos _ j (by rw [n_eq]; exact hj),
        getElem!_pos _ j (by rw [n_eq]; exact hj), Vector.getElem_map], hb'⟩
  have hw' : pR sP ∈ v.wr := by rw [hb'.keep.2.2]; exact hw
  have r0 : InRegions (v.rd ++ v.wr) (v.gpr .rdx + BitVec.ofNat 64 0) 32 := by
    rw [hdx', add_ofNat_zero]; exact sp_inY (List.mem_append_right _ hw') (by bdd_omega)
  rw [show ∀ (a : Instr) (b : List Instr) (c d : Instr), [a] ++ b ++ [c, d] ++ ([.alu .sub .rcx (.imm 1)] : List Instr) =
      [a] ++ (b ++ [c, d, .alu .sub .rcx (.imm 1)]) from fun _ _ _ _ => by simp,
    WP.block_append_iff]
  refine WP.mono (yld_ok r0) fun s1 ⟨L1, o1⟩ => ?_
  rw [WP.block_append_iff]
  have c1 : YConsts s1 := o1.consts hb'.consts (by decide) (by decide)
  refine WP.mono (ylanes hY (P := fun l t => WLanes (t.xmm .xmm3) (fun e => g G[16 * u + 8 * l + e]! cw))
    fun l hl => WP.mono (hb _ (c1 l hl)) fun t ⟨h, o⟩ => ⟨fun e he => by
      rw [h e he]; dsimp only
      rw [State.proj_xmm, L1 l hl, hdx', add_ofNat_zero, show 16 * l = 2 * (8 * l) by bdd_omega, wAddr_add,
        word_readW _ _ he, wAddr_add, ← wordAt, hP _ (by bdd_omega), ite_eq_right (by bdd_omega),
        State.proj_xmm, o1.lane _ (by decide) l hl, hz' l hl, hcw e he, Nat.add_assoc], o⟩) fun s2 ⟨l2, o2⟩ => ?_
  have o12 := o1.trans o2
  have w0 : InRegions s2.wr (s2.gpr .rdx) 32 := by rw [o12.wr, o12.gpr, hdx']; exact sp_inY hw' (by bdd_omega)
  vrunm [State.store256_eq, State.setMem_gpr, State.setMem_wr, State.setMem_mem, State.setMem_rd, State.setMem_ymm,
    w0, sx32]
  have dx2 : s2.gpr .rdx = wAddr (spW sP) (16 * u) := by rw [o12.gpr, hdx']
  have l2' : ∀ l < 2, WLanes (s2.lane .xmm3 l) (fun e => g G[16 * u + 8 * l + e]! cw) := fun l hl => by
    have := l2 l hl; rwa [State.proj_xmm] at this
  rw [dx2, o12.mem]
  refine ⟨⟨fun j hj => ?_, by rw [show (32 : BitVec 64) = BitVec.ofNat 64 (2 * 16) from rfl, wAddr_add, Nat.mul_succ],
    fun l hl => ?_, hb'.trans ⟨⟨fun r hr => ?_, by simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags, State.setMem_rd, o12.rd],
      by simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags, State.setMem_wr, o12.wr]⟩,
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (sR_containsY _ (by bdd_omega)), ?_,
      by simp only [RegUpd.mxcsr_setReg, RegUpd.mxcsr_setFlags]; exact o12.mxcsr⟩⟩,
    by rw [o12.gpr], by rw [o12.gpr]⟩
  · rw [wordAt_write256 _ _ (by bdd_omega) _ hj]
    split
    · rw [word_ymm _ _ (by bdd_omega), l2' _ (by bdd_omega) _ (Nat.mod_lt _ (by bdd_omega)), ite_eq_left (by bdd_omega)]
      dsimp only; rw [show 16 * u + 8 * ((j - 16 * u) / 8) + (j - 16 * u) % 8 = j by bdd_omega]
    · rw [hP j hj]
      by_cases h : j < 16 * u
      · rw [ite_eq_left h, ite_eq_left (by bdd_omega)]
      · rw [ite_eq_right h, ite_eq_right (by bdd_omega)]
  · simp only [lane_setReg, lane_setFlags, State.setMem_lane]
    rw [o12.lane _ (by decide) l hl]; exact hz' l hl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, State.setMem_gpr, hr, ite_false]
    rw [o12.gpr]
  · exact lanes_gpr (s := s2) (fun r l => by simp only [lane_setReg, lane_setFlags, State.setMem_lane]) o12
      hb'.consts (by decide) (by decide)

end VG.Proof.MlKem.X86_64
