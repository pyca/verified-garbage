module

public import VerifiedGarbage.Proof.MlKem.X86_64.AccY
import VerifiedGarbage.Proof.MlKem.X86_64.NttAvx2
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# ML-KEM on x86-64: `NTT⁻¹` of the AVX2 accumulator

`nttInvAccY` (`Impl/MlKem/X86_64/KpkeAccY.lean`) is `vg_mlkem_inv_ntt_avx2`
(`NttAvx2.lean`) with a prologue that puts the accumulator's words in order
into `S` (`yfromAcc_ok`) rather than packing `u32`s: word `o` of the 32 that
an iteration stores is word `srcW o` of the 32 it loads (`lo_word`,
`hi_word`), whose coefficient is `o` (`srcW_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-- The word of the accumulator that `yfromAcc` puts at word `o` of its 32. -/
def srcW (o : Nat) : Nat :=
  if o < 16 then 16 * (o % 2) + 8 * (o % 8 / 4) + 2 * (o / 8) + o % 4 / 2
  else 16 * ((o - 16) % 2) + 8 * ((o - 16) % 8 / 4) + 4 + 2 * ((o - 16) / 8) + (o - 16) % 4 / 2

theorem srcW_ok : ∀ o < 32, srcW o < 32 ∧ accIdx (srcW o) = o := by decide +kernel

theorem accIdx_add32 {u w : Nat} (hw : w < 32) : accIdx (32 * u + w) = 32 * u + accIdx w := by
  unfold accIdx; omega

/-- Word `o % 8` of lane `o / 8` of `vpermq` (`0xD8`) of `vpunpcklwd` of `a` and `b` (lanes `a₀, a₁`, `b₀, b₁`). -/
theorem lo_word (a0 a1 b0 b1 : BitVec 128) {o : Nat} (ho : o < 16) :
    word (if o / 8 = 0 then XBinOp.eval .punpcklqdq (XBinOp.eval .punpcklwd a0 b0) (XBinOp.eval .punpcklwd a1 b1)
      else XBinOp.eval .punpckhqdq (XBinOp.eval .punpcklwd a0 b0) (XBinOp.eval .punpcklwd a1 b1)) (o % 8) =
    word (if o % 2 = 0 then (if o % 8 / 4 = 0 then a0 else a1) else (if o % 8 / 4 = 0 then b0 else b1))
      (2 * (o / 8) + o % 4 / 2) := by
  rcases (by omega : o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 ∨ o = 4 ∨ o = 5 ∨ o = 6 ∨ o = 7 ∨ o = 8 ∨ o = 9 ∨ o = 10 ∨
    o = 11 ∨ o = 12 ∨ o = 13 ∨ o = 14 ∨ o = 15) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (disch := decide) only [word_punpcklqdq, word_punpckhqdq, word_punpcklwd, Nat.reduceDiv, Nat.reduceMod,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte]

/-- As `lo_word`, for `vpunpckhwd`. -/
theorem hi_word (a0 a1 b0 b1 : BitVec 128) {o : Nat} (ho : o < 16) :
    word (if o / 8 = 0 then XBinOp.eval .punpcklqdq (XBinOp.eval .punpckhwd a0 b0) (XBinOp.eval .punpckhwd a1 b1)
      else XBinOp.eval .punpckhqdq (XBinOp.eval .punpckhwd a0 b0) (XBinOp.eval .punpckhwd a1 b1)) (o % 8) =
    word (if o % 2 = 0 then (if o % 8 / 4 = 0 then a0 else a1) else (if o % 8 / 4 = 0 then b0 else b1))
      (4 + 2 * (o / 8) + o % 4 / 2) := by
  rcases (by omega : o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 ∨ o = 4 ∨ o = 5 ∨ o = 6 ∨ o = 7 ∨ o = 8 ∨ o = 9 ∨ o = 10 ∨
    o = 11 ∨ o = 12 ∨ o = 13 ∨ o = 14 ∨ o = 15) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (disch := decide) only [word_punpcklqdq, word_punpckhqdq, word_punpckhwd, Nat.reduceDiv, Nat.reduceMod,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte]

/-- `vpunpckhwd ymm2, ymm0, ymm1` and `vpunpcklwd ymm0, ymm0, ymm1` in each lane. -/
theorem zunpk2_ok (t : State) :
    WP isa (.block [xb .movdqa .xmm2 .xmm0, xb .punpckhwd .xmm2 .xmm1, xb .punpcklwd .xmm0 .xmm1]) t fun t' =>
      (t'.xmm .xmm2 = XBinOp.eval .punpckhwd (t.xmm .xmm0) (t.xmm .xmm1) ∧
        t'.xmm .xmm0 = XBinOp.eval .punpcklwd (t.xmm .xmm0) (t.xmm .xmm1)) ∧ XOnly [.xmm2, .xmm0] t t' := by
  simp only [xb]
  vrun
  exact ⟨⟨rfl, trivial⟩, by xonly⟩

/-- Word `e` of 16 bytes loaded from `wAddr p j + 32h + 16l`. -/
theorem acc_word (m : Mem) (p : Addr) (j h l : Nat) {e : Nat} (he : e < 8) :
    word (m.readW (wAddr p j + BitVec.ofNat 64 (32 * h) + BitVec.ofNat 64 (16 * l)) 128) e =
      wordAt m p (j + 16 * h + 8 * l + e) := by
  rw [word_readW _ _ he, BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add,
    show 32 * h + (16 * l + 2 * e) = 2 * (16 * h + 8 * l + e) by omega, wAddr_add, ← wordAt]
  exact congrArg _ (by omega)

theorem sel_eq {α : Type} (R : Nat → Nat → α) {o : Nat} :
    (if o % 2 = 0 then (if o % 8 / 4 = 0 then R 0 0 else R 0 1) else (if o % 8 / 4 = 0 then R 1 0 else R 1 1)) =
      R (o % 2) (o % 8 / 4) := by
  rcases (by omega : o % 2 = 0 ∨ o % 2 = 1) with h1 | h1 <;>
  rcases (by omega : o % 8 / 4 = 0 ∨ o % 8 / 4 = 1) with h2 | h2 <;>
  simp only [h1, h2, ↓reduceIte, Nat.one_ne_zero]

/-- The lanes of a register, by the lane's index. -/
theorem lane_sel (s : State) (r : XReg) {l : Nat} (hl : l < 2) :
    s.lane r l = if l = 0 then s.lane r 0 else s.lane r 1 := by
  rcases lane01 hl with rfl | rfl <;> rfl

theorem yfromAcc_ok {aP sP : Addr} {F : Poly} {s : State} (hc : YConsts s) (hA : Acc16 s.mem aP F)
    (h9 : s.gpr .r9 = aP) (hdx : s.gpr .rdx = spW sP) (hra : pR aP ∈ s.rd ++ s.wr) (hw : pR sP ∈ s.wr)
    (hd : (pR aP).Disjoint (pR sP)) :
    WP isa yfromAcc s fun s' => S16 s'.mem (spW sP) F ∧ Frame [sR (spW sP)] s.mem s'.mem ∧ YConsts s' ∧
      Keep [.r9, .rdx, .rcx] s s' ∧ s'.mxcsr = s.mxcsr := by
  have hsub : Region.Sub (sR (spW sP)) (pR sP) := Offset.sub_base sP (by omega)
  refine WP.mono (wp_rcxLoopY (N := 8) (by decide) (by decide)
    (fun u w => S16p w.mem (spW sP) F (32 * u) ∧ w.gpr .r9 = wAddr aP (32 * u) ∧
      w.gpr .rdx = wAddr (spW sP) (32 * u) ∧ Frame [sR (spW sP)] s.mem w.mem ∧ YConsts w ∧
      Keep [.r9, .rdx, .rcx] s w ∧ w.mxcsr = s.mxcsr)
    (fun w o hy hcx => ⟨fun _ h => absurd h (by omega), by rw [o.keep.gpr (by decide), h9, wAddr]; simp,
      by rw [o.keep.gpr (by decide), hdx, wAddr]; simp, by rw [o.mem]; exact Frame.refl _ _,
      lanes_gpr (s := s) (GOnly.lane o hy) (YOnly.refl [] s) hc (by decide) (by decide),
      o.keep.mono (by simp), o.mxcsr⟩)
    (fun u hu w ⟨hP, h9', hdx', hf, hc', hk', hx'⟩ => ?_))
    fun w ⟨hP, _, _, hf, hc', hk', hx'⟩ => ⟨fun i hi => hP i (by omega), hf, hc', hk', hx'⟩
  have hA' : Acc16 w.mem aP F := accY.frame hf (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact hd.sub_right hsub) hA
  have hra' : pR aP ∈ w.rd ++ w.wr := by rw [hk'.2.1, hk'.2.2]; exact hra
  have hw' : pR sP ∈ w.wr := by rw [hk'.2.2]; exact hw
  have r0 : InRegions (w.rd ++ w.wr) (w.gpr .r9 + BitVec.ofNat 64 0) 32 :=
    ⟨_, hra', by rw [h9', wAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
                 exact Offset.contains_base aP (by omega) (by omega)⟩
  have r1 : InRegions (w.rd ++ w.wr) (w.gpr .r9 + BitVec.ofNat 64 32) 32 :=
    ⟨_, hra', by rw [h9', wAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
                 exact Offset.contains_base aP (by omega) (by omega)⟩
  rw [show ∀ a b c d e f g h i j : Instr, [a, b, c, d, e, f, g, h, i, j] ++ ([.alu .sub .rcx (.imm 1)] : List Instr) =
      [a] ++ ([b] ++ ([c, d] ++ ([e] ++ ([f] ++ [g, h, i, j, .alu .sub .rcx (.imm 1)])))) from
      fun _ _ _ _ _ _ _ _ _ _ => rfl, WP.block_append_iff]
  refine WP.mono (yld_ok r0) fun s1 ⟨L0, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (yld_ok (by rw [o1.rd, o1.wr, o1.gpr]; exact r1)) fun s2 ⟨L1, o2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ylanes (vs := [yb .vpunpckhwd .xmm2 .xmm0 .xmm1, yb .vpunpcklwd .xmm0 .xmm0 .xmm1]) (by decide)
    (P := fun l t => t.xmm .xmm2 = XBinOp.eval .punpckhwd (s2.lane .xmm0 l) (s2.lane .xmm1 l) ∧
      t.xmm .xmm0 = XBinOp.eval .punpcklwd (s2.lane .xmm0 l) (s2.lane .xmm1 l))
    fun l _ => zunpk2_ok (s2.proj l)) fun s3 ⟨P3, o3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ypermq_ok (d := .xmm0) (r := .xmm0) s3) fun s4 ⟨Q0, Q1, o4⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ypermq_ok (d := .xmm2) (r := .xmm2) s4) fun s5 ⟨R0, R1, o5⟩ => ?_
  have o15 := (((o1.trans o2).trans o3).trans o4).trans o5
  have w0' : InRegions s5.wr (s5.gpr .rdx) 32 := by rw [o15.wr, o15.gpr, hdx']; exact sp_inY hw' (by omega)
  have w1' : InRegions s5.wr (s5.gpr .rdx + 32#64) 32 := by
    rw [o15.wr, o15.gpr, hdx', show (32#64 : BitVec 64) = BitVec.ofNat 64 (2 * 16) from rfl, wAddr_add]
    exact sp_inY hw' (by omega)
  have sx64 : BitVec.signExtend 64 (64 : BitVec 32) = BitVec.ofNat 64 (2 * 32) := by decide
  vrunm [State.store256_eq, State.setMem_gpr, State.setMem_wr, State.setMem_mem, State.setMem_rd, State.setMem_ymm,
    State.setMem_setMem, w0', w1', sx64]
  -- the lanes before the permutations
  have La : ∀ l < 2, s2.lane .xmm0 l = w.mem.readW (wAddr aP (32 * u) + BitVec.ofNat 64 (32 * 0) +
      BitVec.ofNat 64 (16 * l)) 128 := fun l hl => by
    rw [o2.lane _ (by decide) l hl, L0 l hl, h9']
  have Lb : ∀ l < 2, s2.lane .xmm1 l = w.mem.readW (wAddr aP (32 * u) + BitVec.ofNat 64 (32 * 1) +
      BitVec.ofNat 64 (16 * l)) 128 := fun l hl => by
    rw [L1 l hl, o1.gpr, o1.mem, h9']
  have U0 : ∀ l < 2, s3.lane .xmm0 l = XBinOp.eval .punpcklwd (s2.lane .xmm0 l) (s2.lane .xmm1 l) :=
    fun l hl => (P3 l hl).2
  have U2 : ∀ l < 2, s3.lane .xmm2 l = XBinOp.eval .punpckhwd (s2.lane .xmm0 l) (s2.lane .xmm1 l) :=
    fun l hl => (P3 l hl).1
  -- a word stored, as a word of the accumulator
  have src : ∀ o < 32, (word (if o < 16 then s5.lane .xmm0 (o / 8) else s5.lane .xmm2 ((o - 16) / 8))
      (if o < 16 then o % 8 else (o - 16) % 8)).toNat = (F[32 * u + o]!).val := fun o ho => by
    obtain ⟨hs1, hs2⟩ := srcW_ok o ho
    have e := hA' (32 * u + srcW o) (by omega)
    rw [accIdx_add32 hs1, hs2] at e
    rw [← e]
    by_cases h16 : o < 16
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h16), ite_eq_left_of_eq_true _ _ (eq_true h16),
        o5.lane _ (by decide) _ (by omega), lane_sel s4 .xmm0 (show o / 8 < 2 by omega), Q0, Q1, U0 0 (by decide),
        U0 1 (by decide), lo_word _ _ _ _ h16, La 0 (by decide), La 1 (by decide), Lb 0 (by decide), Lb 1 (by decide),
        sel_eq (fun h l => w.mem.readW (wAddr aP (32 * u) + BitVec.ofNat 64 (32 * h) + BitVec.ofNat 64 (16 * l)) 128),
        acc_word _ _ _ _ _ (by omega)]
      unfold srcW
      rw [ite_eq_left_of_eq_true _ _ (eq_true h16)]
      exact congrArg _ (congrArg _ (by omega))
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h16), ite_eq_right_of_eq_false _ _ (eq_false h16),
        lane_sel s5 .xmm2 (show (o - 16) / 8 < 2 by omega), R0, R1, o4.lane _ (by decide) 0 (by decide),
        o4.lane _ (by decide) 1 (by decide), U2 0 (by decide), U2 1 (by decide), hi_word _ _ _ _ (by omega),
        La 0 (by decide), La 1 (by decide), Lb 0 (by decide), Lb 1 (by decide),
        sel_eq (fun h l => w.mem.readW (wAddr aP (32 * u) + BitVec.ofNat 64 (32 * h) + BitVec.ofNat 64 (16 * l)) 128),
        acc_word _ _ _ _ _ (by omega)]
      unfold srcW
      rw [ite_eq_right_of_eq_false _ _ (eq_false h16)]
      exact congrArg _ (congrArg _ (by omega))
  have dx5 : s5.gpr .rdx = wAddr (spW sP) (32 * u) := by rw [o15.gpr, hdx']
  have r95 : s5.gpr .r9 = wAddr aP (32 * u) := by rw [o15.gpr, h9']
  have a16 : wAddr (spW sP) (32 * u) + 32#64 = wAddr (spW sP) (32 * u + 16) := by
    rw [show (32#64 : BitVec 64) = BitVec.ofNat 64 (2 * 16) from rfl, wAddr_add]
  rw [dx5, r95, o15.mem, a16]
  refine ⟨⟨fun j hj => ?_, by rw [wAddr_add, Nat.mul_succ], by rw [wAddr_add, Nat.mul_succ],
      ?_, ?_, ?_, ?_⟩, by rw [o15.gpr], by rw [o15.gpr]⟩
  · rw [wordAt_write256 _ _ (by omega) _ (by omega), wordAt_write256 _ _ (by omega) _ (by omega)]
    split
    · have := src (j - 32 * u) (by omega)
      rw [ite_eq_right_of_eq_false _ _ (eq_false (show ¬ j - 32 * u < 16 by omega)),
        ite_eq_right_of_eq_false _ _ (eq_false (show ¬ j - 32 * u < 16 by omega))] at this
      rw [word_ymm _ _ (by omega), show j - (32 * u + 16) = j - 32 * u - 16 by omega, this]
      exact congrArg _ (congrArg _ (by omega))
    · split
      · have := src (j - 32 * u) (by omega)
        rw [ite_eq_left_of_eq_true _ _ (eq_true (show j - 32 * u < 16 by omega)),
          ite_eq_left_of_eq_true _ _ (eq_true (show j - 32 * u < 16 by omega))] at this
        rw [word_ymm _ _ (by omega), this]
        exact congrArg _ (congrArg _ (by omega))
      · exact hP j (by omega)
  · exact hf.trans (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (sR_containsY _ (by omega))).writeW
      (List.mem_singleton_self _) _ (sR_containsY _ (by omega)))
  · exact lanes_gpr (s := s5) (fun r l => by simp only [lane_setReg, lane_setFlags, State.setMem_lane]) o15 hc'
      (by decide) (by decide)
  · refine ⟨fun r hr => ?_, by simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags, State.setMem_rd]; rw [o15.rd]; exact hk'.2.1,
      by simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags, State.setMem_wr]; rw [o15.wr]; exact hk'.2.2⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, State.setMem_gpr, hr, ite_false]
    rw [o15.gpr]; exact hk'.gpr (by simp [hr])
  · exact o15.mxcsr.trans hx'

/-- `ypro_ok` (`YNttPack.lean`), from the accumulator at `rdi`. -/
theorem yproAcc_ok (tab : Nat → Nat) {z : Nat → Zq} (htab : ∀ k, tab k = (z k).val * 65536 % 3329)
    {fP sP : Addr} {F : Poly} {s : State} (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP)
    (hF : Acc16 s.mem fP F) (hwf : pR fP ∈ s.rd ++ s.wr) (hw : pR sP ∈ s.wr) (hd : (pR fP).Disjoint (pR sP)) :
    WP isa (yproAcc tab) s fun s' => S16 s'.mem (spW sP) F ∧ TZ s'.mem sP z ∧ YConsts s' ∧
      Frame [pR sP] s.mem s'.mem ∧ Keep [.rax, .rcx, .rdx, .r9] s s' := by
  simp only [yproAcc, List.append_assoc]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  have htl : ∀ k, tab k < 65536 := fun k => by
    rw [htab k]; have := Nat.mod_lt ((z k).val * 65536) (show 3329 > 0 by decide); omega
  refine WP.mono (wordTab_gen tab htl (by decide) hsi hw) fun s1 ⟨hT, hf1, k1, _, _⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (yconsts_ok s1) fun s2 ⟨hc2, hm2, k2⟩ => ?_
  have k12 := k1.trans k2
  have hsi2 : s2.gpr .rsi = sP := by rw [k12.gpr (by decide), hsi]
  have hdi2 : s2.gpr .rdi = fP := by rw [k12.gpr (by decide), hdi]
  refine WP.mono (Q := fun (s3 : State) => s3.gpr .r9 = fP ∧ s3.gpr .rdx = spW sP ∧ GOnly [.r9, .rdx] s2 s3 ∧
      s3.ymmHi = s2.ymmHi)
    (by
      simp only [leaR, oS]
      vrunm [hsi2, hdi2, sx_ofNat (show 256 < 2 ^ 31 by decide), RegUpd.ymmHi_setReg]
      exact ⟨by gonly, rfl⟩) fun s3 ⟨h9, hdx, og, hy⟩ => ?_
  have k13 := k12.trans og.keep
  have hF3 : Acc16 s3.mem fP F := by
    rw [og.mem, hm2]
    exact accY.frame hf1 (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hd.sub_right (pR_sub_tab sP)) hF
  have hT3 : TZ s3.mem sP z := fun k hk => by rw [og.mem, hm2, hT k hk, htab]
  refine WP.mono (yfromAcc_ok (lanes_gpr (s := s2) (GOnly.lane og hy) (YOnly.refl [] s2) hc2 (by decide)
      (by decide)) hF3 h9 hdx (by rw [k13.2.1, k13.2.2]; exact hwf) (by rw [k13.2.2]; exact hw) hd)
    fun s4 ⟨hS, hf4, hc4, k4, _⟩ => ⟨hS, hT3.frame hf4, hc4, ?_, (k13.trans k4).mono (by simp)⟩
  refine (hf1.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
    ((og.mem.trans hm2) ▸ hf4.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
  · rw [List.mem_singleton.mp hr]; exact pR_sub_tab sP
  · rw [List.mem_singleton.mp hr]; exact pR_sub_S sP

theorem nttInvAccY_correct (s : State) (hs : (invAccK accY).pre s) :
    ∃ t s', Exec isa nttInvAccY s t s' ∧ abiPreserved s s' ∧ (invAccK accY).post s s' := by
  obtain ⟨F0, hF0⟩ := hs.2.2.2.2.2
  have hw : pR (s.gpr .rsi) ∈ s.wr := by rw [hs.2.1]; simp
  have hwf : pR (s.gpr .rdi) ∈ s.wr := by rw [hs.2.1]; simp
  have hd : (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) := hs.2.2.1
  have hW : WP isa nttInvAccY s fun s' => PolyIs s'.mem (s.gpr .rdi) (nttInv F0) ∧
      Frame [pR (s.gpr .rdi), pR (s.gpr .rsi)] s.mem s'.mem := by
    unfold nttInvAccY
    refine WP.seq (WP.mono (yproAcc_ok zmTabInv zmTabInv_eq rfl rfl hF0 (List.mem_append_right _ hwf)
      hw hd) fun s2 ⟨hS, hT, hc, hf2, k2⟩ => ?_)
    have hsi2 : s2.gpr .rsi = s.gpr .rsi := k2.gpr (by decide)
    have hw2 : pR (s.gpr .rsi) ∈ s2.wr := by rw [k2.2.2]; exact hw
    refine WP.seq (WP.mono (nttInvLazy_ok hc hsi2 hS hT hw2) fun s3 ⟨hS3, hb3⟩ => ?_)
    have hI : LIY (s.gpr .rsi) s2 zInv _ s3 :=
      ⟨hS3, hT.frame hb3.frame, hb3.consts, hb3.keep.mono (by decide), hb3.frame⟩
    refine WP.mono (yepi_ok hI.c hI.S (by rw [hI.keep.gpr (by decide), k2.gpr (by decide)])
      (by rw [hI.keep.gpr (by decide), hsi2]) (by rw [hI.keep.2.2, k2.2.2]; exact hwf)
      (by rw [hI.keep.2.2]; exact hw2) hd) fun s4 ⟨hP, hf4⟩ => ⟨?_, ?_⟩
    · exact hP
    · refine (frame_fs hf2 ?_).trans ((frame_fs hI.frame ?_).trans (frame_fs hf4 ?_)) <;>
        intro r hr <;> simp only [List.mem_singleton] at hr <;> subst hr
      exacts [.inr fun _ h => h, .inr (pR_sub_S _), .inl fun _ h => h]
  obtain ⟨t, s', he, ⟨hP, hf⟩, hk⟩ := WP.keep [.rax, .rcx, .rdx, .r8, .r9] hW (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he
    (gprPreserved_of hk (by decide) hf (by simpa using ⟨hs.2.2.2.1, hs.2.2.2.2.1⟩)),
    fun F hF => by rw [acc16_unique hF hF0]; exact hP⟩

end VG.Proof.MlKem.X86_64
