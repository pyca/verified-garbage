module

import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombJStep
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombJP
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelectV2
public import VerifiedGarbage.Proof.Framework.AArch64.InterleaveTable
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombJ
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombJFirst
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombJDigit
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Weierstrass.AArch64.FprogJ
public import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombJEntry
public import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombJInvariant
public import VerifiedGarbage.Impl.Weierstrass.AArch64.TCombJ
public import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
public import VerifiedGarbage.Proof.Weierstrass.Booth
public import VerifiedGarbage.Impl.Weierstrass.AArch64.TCombJ
public import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelectV

/-!
# The pipelined comb in two passes on AArch64

`TCombCfg.combJP2` (`Impl/Weierstrass/AArch64/TCombJ.lean`): `combJP` for an
entry of `n` pairs a coordinate, `n` even with `n / 2 ≤ 3`, whose selection
takes two passes (`pass2_ok`), both woven into the addition, with the table's
address in `x30` (`prepNext2_ok`); the first pass's accumulators wait in
`selKeep` until both are stored (`tentryJFin2_ok`). `tcombJP2_ok`: it
computes `[k]G`, as `combJWith` does.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.AArch64.Interleave (scalOk vecOk TabApart)
open Spec.Weierstrass

/-- What the two-pass pipelined comb's code must satisfy, checked by
evaluation for a curve: `JPChecks`, with the table's address in `x30` and the
two passes. -/
structure JPChecks2 (K : TCombCfg) (size : Nat) (mc : List Instr) : Prop where
  n6 : K.M.n / 2 ≤ 3
  n2 : K.M.n % 2 = 0
  J3 : 3 ≤ K.J
  scal : mc.all (scalOk .x0 .x30 size) = true
  vec : K.selPass2.all (vecOk .x30 K.tblBytes) = true
  mcv : mc.all (fun i => (vdstOf i).isNone) = true
  fixv : (instrs K.fixJ).all (fun i => (vdstOf i).isNone) = true
  bdv : (K.bdigit true).all (fun i => (vdstOf i).isNone) = true

/-- `x19 = j` from `j + 1`, `x30` = table `j + 1`'s address and `x5 = 1`. -/
theorem setupNext2_ok (K : TCombCfg) (s : State) {j : Nat} {T : Addr}
    (h19 : s.gpr .x19 = BitVec.ofNat 64 (j + 1)) (hT : s.syms K.tsym = T) (htb : K.tblBytes < 65536) :
    WP isa (.block (([.subImm .x .x19 .x19 1] : List Instr) ++ K.selSetupNext2 ++ ([.movz .x .x5 1 0] : List Instr))) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 j ∧ t.gpr .x30 = T + BitVec.ofNat 64 ((j + 1) * K.tblBytes) ∧
      t.gpr .x5 = 1 ∧ Keeps [.x5, .x17, .x19, .x30] s t := by
  subst hT
  apply WP.of_runBlock
  simp only [TCombCfg.selSetupNext2, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
    runBlock_nil, exec, read_x, Size.bits, show 1 < 4096 by decide, show 16 * 0 < Size.x.bits from by decide,
    ite_true, RegUpd.gpr_write, BitVec.setWidth_eq, ite_false, reduceCtorEq, h19, dec_ofNat,
    BitVec.ofNat_add_ofNat, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_, by decide, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · show s.syms K.tsym + _ = _
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
      Nat.shiftLeft_eq, Nat.mul_zero, Nat.pow_zero, Nat.mul_one,
      Nat.mod_eq_of_lt (show K.tblBytes < 2 ^ 16 by omega_using [htb]), Nat.mod_mod]
    rw [← Nat.mul_mod]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem prep2_tcombClob (n : Nat) (hn : n ≤ 9) :
    ∀ r ∈ [Reg.x2, .x3, .x4, .x5, .x7, .x9, .x16, .x17, .x19, .x30], r ∈ tcombClob n := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact combClob_tcombClob _ (List.mem_cons_self ..)
    | exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    | exact tcombClob_sub _ hn _ (List.mem_append_left _ (by decide))

/-- Before window `j`'s addition (`1 ≤ j`, `j + 2 ≤ J`): digit `j + 1`'s
magnitude broadcast for its selection (`v19`, with one in `v28` and two in
`v18`) and its table's address in `x30`, the rest as it was. -/
theorem prepNext2_ok {K : TCombCfg} {C : Curve} {base : Addr} {size k : Nat} {T : Addr}
    {ws : List (BitVec 64)} (hL : TCombLay K size) (hb1 : 1 ≤ K.bits) {s₀ s : State} {j : Nat}
    (hjn : j + 2 ≤ K.J) (hI : TCombJInv K C base size k T ws s₀ s j) :
    WP isa (.block K.prepNext2) s fun t => TCombJInv K C base size k T ws s₀ t j ∧ t.mem = s.mem ∧
      t.syms = s.syms ∧ KeepRegs (tcombClob K.M.n) s t ∧
      t.gpr .x30 = T + BitVec.ofNat 64 ((j + 1) * K.tblBytes) ∧
      t.v .v19 = dup2 (BitVec.ofNat 64 (bmag K.w k (j + 1))) ∧ t.v .v18 = dup2 2 ∧ t.v .v28 = dup2 1 := by
  have hs := hI.scr
  have hw := hL.w
  have hwi : K.w * (j + 1) + K.w ≤ K.w * K.J := by
    have := Nat.mul_le_mul_left K.w (show j + 1 + 1 ≤ K.J by omega_using [hjn]); rwa [Nat.mul_succ] at this
  have hb : K.bits + K.w * K.J ≤ size := by
    have := hL.bits
    have := hL.kbytes
    unfold TCombCfg.zw at *
    omega_arith
  have hwb : K.bits + K.w ≤ 4096 := by
    have := hL.bitsw
    omega_using [hwi, this]
  have hcl := prep2_tcombClob K.M.n hL.n8
  unfold TCombCfg.prepNext2
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono_syms (inc19_ok s hI.x19) fun s₁ ⟨b₁, k₁⟩ sy₁ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono_syms (bdigit_ok K hs₁ (k := k) (j := j + 1) (N := K.w * K.J) (by omega_using [hw])
    (by omega_using [hw]) hwi (by omega_using [hb, hwi]) hb1 hwb b₁ (fun t ht => by rw [k₁.mem]; exact hI.bits t ht)
    (Or.inl ⟨rfl, by omega_using []⟩)) fun s₂ ⟨r₂, k₂⟩ sy₂ => ?_
  rw [← List.append_assoc, ← List.append_assoc, WP.block_append_iff]
  refine WP.mono_syms (setupNext2_ok K s₂ (j := j) (T := T) (by rw [k₂.gpr _ (by decide), b₁])
    (by rw [sy₂, sy₁]; exact hI.tsym) hL.tbl.2) fun s₃ ⟨b₃, x₃, e₃, k₃⟩ sy₃ => ?_
  refine WP.mono_syms (bcastV_ok s₃) fun t ⟨v19, v28, v18, k₄⟩ sy₄ => ?_
  have hm : t.mem = s.mem := by rw [k₄.mem, k₃.mem, k₂.mem, k₁.mem]
  have hsy : t.syms = s.syms := by rw [sy₄, sy₃, sy₂, sy₁]
  have hk : KeepRegs (tcombClob K.M.n) s t :=
    (((Keeps.regs k₁).mono fun r hr => hcl r (by simp only [List.mem_singleton] at hr; simp [hr])).trans
      ((Keeps.regs k₂).mono fun r hr => hcl r (by revert r; decide))).trans
      (((Keeps.regs k₃).mono fun r hr => hcl r (by revert r; decide)).trans
        ((Keeps.regs k₄.keeps).mono fun _ h => absurd h List.not_mem_nil))
  have hst : Scr t base size :=
    ((hs₁.of_keeps k₂ (by decide)).of_keeps k₃ (by decide)).of_keeps k₄.keeps (by decide)
  refine ⟨hI.of_keep hk hm (by rw [k₄.gpr _ List.not_mem_nil, b₃]) hsy hst, hm, hsy, hk,
    by rw [k₄.gpr _ List.not_mem_nil, x₃], by rw [v19, k₃.gpr _ (by decide), r₂], ?_, by rw [v28, e₃]⟩
  rw [v18, e₃]; rfl

/-- After window `i - 1`'s corrections (`1 ≤ i < J`, `x19 = i`), with the
pass of window `i`'s selection in the accumulators (of the table at `x30` in
`r`, whose bytes the memory keeps) and its magnitude in `v19`: the digit
again, its entry stored to `E`, and negated (`tentryJ_ok` for the pipelined
selection). -/
theorem tentryJFin2_ok {K : TCombCfg} {C : Curve} {base : Addr} {size k i : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hA : CombA K.toComb) (hC : Law C)
    (hV : TCombVals K C tbl) (hpn : C.p < 2 ^ (64 * K.M.n)) (hn6 : K.M.n / 2 ≤ 3) (hn2 : K.M.n % 2 = 0)
    (hbdv : (K.bdigit true).all (fun i => (vdstOf i).isNone) = true) {u : State} (hs : Scr u base size)
    (hM : ModOkA K.M size C.p u.mem base) (hi : i < K.J) (hi1 : 1 ≤ i) (hx : u.gpr .x19 = BitVec.ofNat 64 i)
    (hb1 : 1 ≤ K.bits)
    (hbits : ∀ t < K.w * K.J, u.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0)
    (hz : wordsVal u.mem base K.zero K.M.n = 0)
    (hTM : TblMem u T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl))
    {r : State} (hr30 : r.gpr .x30 = T + BitVec.ofNat 64 (i * K.tblBytes))
    (hrm : ∀ b < K.tblBytes, r.mem (T + BitVec.ofNat 64 (i * K.tblBytes) + BitVec.ofNat 64 b) =
      u.mem (T + BitVec.ofNat 64 (i * K.tblBytes) + BitVec.ofNat 64 b))
    (h19 : u.v .v19 = dup2 (BitVec.ofNat 64 (bmag K.w k i)))
    (hkx : ∀ i' < K.M.n / 2, u.v (selKeep.getD i' .v3) =
      if 1 ≤ bmag K.w k i then ldE K.M.n 0 r (bmag K.w k i) i' .x30 else 0)
    (hay : ∀ i' < K.M.n / 2, u.v ((selA (K.M.n / 2)).acc.getD i' .v0) =
      if 1 ≤ bmag K.w k i then ldE K.M.n (8 * K.M.n) r (bmag K.w k i) i' .x30 else 0)
    {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s', TEntryPostJ K C base size k i u s' → s'.syms = u.syms → WP isa rest s' Q) :
    WP isa (.block K.finNext2) u fun s₂ => WP isa (.seq (.block K.bnegY) rest) s₂ Q := by
  have hw := hL.w
  have hwi : K.w * i + K.w ≤ K.w * K.J := by
    have := Nat.mul_le_mul_left K.w (show i + 1 ≤ K.J from hi)
    rwa [Nat.mul_succ] at this
  have hb : K.bits + K.w * K.J ≤ size := by
    have := hL.bits
    have := hL.kbytes
    unfold TCombCfg.zw at *
    omega_arith
  have hwb : K.bits + K.w ≤ 4096 := by
    have := hL.bitsw
    omega_using [hwi, this]
  have hmag : bmag K.w k i ≤ K.H := bmag_le (by omega_using [hw]) k i
  have hHle : K.H ≤ 128 := by
    unfold TCombCfg.H; exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (show K.w - 1 ≤ 7 by omega_using [hw]))
      (by decide)
  obtain ⟨hE, hap⟩ := combLay_E hL.comb hA
  dsimp only [TCombCfg.toComb] at hE hap
  unfold TCombCfg.finNext2
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono_syms (WP.novec (bdigit_ok K hs (k := k) (j := i) (N := K.w * K.J)
    (by omega_using [hw]) (by omega_using [hw]) hwi hb hb1 hwb hx hbits (Or.inl ⟨rfl, hi1⟩)) hbdv)
    fun t ⟨⟨hm, hk⟩, hv⟩ hsy => ?_
  have hs' := hs.of_keeps hk (by decide)
  have hM' : ModOkA K.M size C.p t.mem base := hk.mem ▸ hM
  have W := tselectFin2_ok K hn6 hn2 hs' (a := bmag K.w k i) (by omega_using [hmag, hHle]) hm (r := r) (tb := .x30)
    (by rw [hv, h19]) (fun i' hi' => by rw [hv, hkx i' hi'])
    (fun i' hi' => by rw [hv, hay i' hi']) hE ⟨hL.e16.1, hL.e16.2 hn2⟩ hap
    (Nat.lt_trans hV.one_lt hpn)
  simp only [List.append_assoc] at W
  refine WP.mono_syms W fun s₂ ⟨ex, ey, ez, k₂, U₂⟩ sy₂ => ?_
  have hrt : ∀ b < 16 * K.M.n * K.H, t.mem (T + BitVec.ofNat 64 (i * K.tblBytes) + BitVec.ofNat 64 b) =
      r.mem (T + BitVec.ofNat 64 (i * K.tblBytes) + BitVec.ofNat 64 b) := fun b hb' => by
    rw [hk.mem]; exact (hrm b hb').symm
  rw [hr30] at ex ey
  have ex' : wordsVal s₂.mem base K.E.x K.M.n = if 1 ≤ bmag K.w k i then
      wordsVal t.mem (T + BitVec.ofNat 64 (i * K.tblBytes)) (16 * K.M.n * (bmag K.w k i - 1)) K.M.n else 0 := by
    rw [ex]; split
    · next h1 => exact (wordsVal_tbl (o := 0) hmag h1 (by omega_using []) hrt).symm
    · rfl
  have ey' : wordsVal s₂.mem base K.E.y K.M.n = if 1 ≤ bmag K.w k i then
      wordsVal t.mem (T + BitVec.ofNat 64 (i * K.tblBytes)) (16 * K.M.n * (bmag K.w k i - 1) + 8 * K.M.n) K.M.n
      else K.one := by
    rw [ey]; split
    · next h1 => exact (wordsVal_tbl hmag h1 (Nat.le_refl _) hrt).symm
    · rfl
  refine tentryJ_of_sel hL hA hC hV hpn hs' hM' hi (by rw [hk.gpr _ (by decide)]; exact hx)
    (fun q hq => by rw [hk.mem]; exact hbits q hq) (by rw [hk.mem]; exact hz)
    (hTM.unch (by rw [hk.rd,hk.wr]) (fun _ _ _ _ => by rw [hk.mem])) ⟨ex', ey', ez, k₂, U₂⟩ sy₂
    fun s' hu syu => h s' ?_ (by rw [syu, hsy])
  refine ⟨hu.scr,?_,?_,?_,hu.lt,hu.z,hu.rep⟩
  · rw [hu.x19,hk.gpr _ (by decide)]
  · exact ((Keeps.regs hk).mono (fun r hr => tcombClob_sub _ hL.n8 r (by
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
      grind))).trans hu.keep
  · rw [← hk.mem]; exact hu.unch

/-- `tabApart_of`, for the table at `x30`. -/
theorem tabApart30_of {s : State} {base X : Addr} {size Tb : Nat} (hs : Scr s base size)
    (hx : s.gpr .x30 = X) (hout : ∀ b < Tb, size ≤ ofs base (X + BitVec.ofNat 64 b)) :
    TabApart .x0 .x30 size Tb s := by
  intro o ho o' ho' he
  have h := hout o' ho'
  rw [← hx, ← he, hs.x0] at h
  have hn := hs.nowrap
  have : ofs base (base + BitVec.ofNat 64 o) = o := ofs_off0 base (by omega_using [hn, ho])
  omega_using [h, this, ho]

/-- Pipelined window `j` (`1 ≤ j`, `j + 2 ≤ J`), its entry in `E`: window
`j + 1`'s selection woven into the addition `mc`, whose code runs as the
selection's pass and then the addition; then `x19 = j + 1`, its entry in
`E`, and `x4 = j + 1 - (J - 1)`. -/
theorem stepJP2_ok {arithmetic : Mod → List FOp → Prog isa} {mc : List Instr} {K : TCombCfg} {C : Curve}
    {base : Addr} {size k : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hA : CombA K.toComb)
    {X : List Reg} (hcompiler : FieldCompilerOn K.M C X arithmetic size)
    (hX : ∀ r ∈ X, r ∈ tcombClob K.M.n ∧ r ≠ .x19) (hJenc : K.J<4096) (hC : Law C) (hM3 : AM3 C)
    (hG : onCurve C (G C) = true) (hV : TCombVals K C tbl) (hpn : C.p < 2 ^ (64 * K.M.n))
    (hb1 : 1 ≤ K.bits) {kmax : Nat} (hB : BoothOk C K.w K.J kmax) (hk : k < kmax) {s₀ : State}
    (hF : TCombFixed K C base size s₀ k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl))
    (hblk : arithmetic K.M (maddJ K.S K.A K.E K.D) = .block mc) (hck : JPChecks2 K size mc)
    {j : Nat} {s : State} (hj : 1 ≤ j) (hjn : j + 2 ≤ K.J)
    (hI : TCombJInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s₀ s j)
    (E : TEntryPostJ K C base size k j s s) :
    WP isa (K.stepJP2 mc) s fun s' =>
      TCombJInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s₀ s' (j + 1) ∧
      TEntryPostJ K C base size k (j + 1) s' s' ∧
      s'.gpr .x4 = BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 (K.J - 1) := by
  have hw := hL.w
  have hle : ∀ x, x ∈ combSlots K.toComb → x + 8 * K.M.n ≤ size := fun x hx => hL.comb.lay.le x hx
  have hmag : bmag K.w k (j + 1) ≤ K.H := bmag_le (by omega_using [hw]) k (j + 1)
  have hHle : K.H ≤ 128 := by
    unfold TCombCfg.H; exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (show K.w - 1 ≤ 7 by omega_using [hw]))
      (by decide)
  have hHe : K.H % 2 = 0 := by
    unfold TCombCfg.H; rw [show K.w - 1 = (K.w - 2) + 1 by omega_using [hw], Nat.pow_succ]; omega_using []
  have hlen := tbl_len hV
  have hout := row_out (K := K) hF.out hlen (j := j + 1) (by omega_using [hjn])
  unfold TCombCfg.stepJP2
  refine WP.seq (WP.mono_syms (prepNext2_ok hL hb1 hjn hI)
    fun p ⟨Ip, hmp, syp, kp, x30p, v19p, v18p, v28p⟩ _ => ?_)
  refine WP.seq (VG.AArch64.Interleave.WP.weave_tab hck.scal hck.vec (tabApart30_of Ip.scr x30p hout) ?_)
  -- The table of window `j + 1`, in the regions.
  have hreg : InRegions (p.rd ++ p.wr) (T + BitVec.ofNat 64 ((j + 1) * K.tblBytes)) (16 * K.M.n * K.H) := by
    obtain ⟨r, hr, hc⟩ := Ip.tbl.rd
    refine ⟨r, hr, Region.contains_off hc ?_⟩
    have h2 := Nat.mul_le_mul_right K.tblBytes (show j + 1 + 1 ≤ K.J by omega_using [hjn])
    rw [Nat.succ_mul] at h2
    exact Nat.le_trans (by unfold TCombCfg.tblBytes at h2 ⊢; omega_using [h2]) hlen
  refine WP.mono_syms (pass2_ok K hck.n6 hck.n2 hmag hHe (by have := hL.tbl.1; omega_using [this])
    (by omega_using [hHle]) v18p v19p v28p (by rw [x30p]; exact hreg))
    fun q ⟨vkq, vaq, _, q19, _, kq⟩ syq => ?_
  have kq' : KeepRegs (tcombClob K.M.n) p q :=
    (Keeps.regs kq.keeps).mono fun _ h => absurd h List.not_mem_nil
  have hsq : Scr q base size := Ip.scr.of_keeps kq.keeps (by decide)
  have Iq := Ip.of_keep kq' kq.mem (by rw [kq.gpr _ List.not_mem_nil]; exact Ip.x19) syq hsq
  have Eq : TEntryPostJ K C base size k j q q := E.self (by rw [kq.mem, hmp]) hsq
  have hT := tailJ_ok hL hA hcompiler hX hJenc hC hM3 hG hV hb1 hB hk hF hj (by omega_using [hjn]) Iq Eq rfl
  rw [hblk] at hT
  have hT' := WP.mono_syms (WP.novec hT (by
    simp only [instrs, List.all_append, hck.mcv, hck.fixv, Bool.and_self])) fun u hu syu => And.intro hu syu
  refine WP.mono (WP.seq_iff.mp hT') fun t ht => WP.seq (WP.mono ht fun u ⟨⟨⟨Iu, _⟩, vu⟩, syu⟩ => ?_)
  -- Window `j + 1`'s entry, from the pass's accumulators.
  have hz : wordsVal u.mem base K.zero K.M.n = 0 := by
    rw [Iu.unch.wordsVal (tcombW_ro hL (x := K.zero) (by simp [combRo, TCombCfg.toComb]))
      (by have := hle K.zero (by tcomb_mem); have := Iu.scr.nowrap; omega_arith), hF.zero]
  have hrm : ∀ b < K.tblBytes, p.mem (T + BitVec.ofNat 64 ((j + 1) * K.tblBytes) + BitVec.ofNat 64 b) =
      u.mem (T + BitVec.ofNat 64 ((j + 1) * K.tblBytes) + BitVec.ofNat 64 b) := fun b hb => by
    rw [Ip.far hL (hout b hb), Iu.far hL (hout b hb)]
  refine WP.seq (WP.mono (tentryJFin2_ok hL hA hC hV hpn hck.n6 hck.n2 hck.bdv Iu.scr Iu.mod (i := j + 1)
    (by omega_using [hjn]) (by omega_using []) Iu.x19 hb1 Iu.bits hz Iu.tbl (r := p) x30p hrm
    (by rw [vu, q19, v19p]) (fun i' hi' => by rw [vu, vkq i' hi']) (fun i' hi' => by rw [vu, vaq i' hi']) (rest := .block [.subImm .x .x4 .x19 (K.J - 1)])
    (Q := fun s' => TCombJInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s₀ s' (j + 1) ∧
      TEntryPostJ K C base size k (j + 1) s' s' ∧
      s'.gpr .x4 = BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 (K.J - 1)) fun e E' sy' => ?_)
    fun s₂ h₂ => WP.block_append_iff.mpr (WP.seq_iff.mp h₂))
  refine WP.mono_syms (sub4_ok e (c := K.J - 1) (by omega_using [hJenc])) fun f ⟨x4f, kf⟩ syf => ?_
  have Ie := Iu.after_entry hL hF E' sy'
  have hsf : Scr f base size := E'.scr.of_keeps kf (by decide)
  have kf' : KeepRegs (tcombClob K.M.n) e f :=
    (Keeps.regs kf).mono fun r hr => by
      simp only [List.mem_singleton] at hr; rw [hr]; exact tcombClob_sub _ hL.n8 _ (by simp)
  refine ⟨Ie.of_keep kf' kf.mem (by rw [kf.gpr _ (by decide)]; exact Ie.x19) syf hsf, E'.self kf.mem hsf, ?_⟩
  rw [x4f, Ie.x19]

/-- The pipelined loop: windows `1 … J - 2`, each selecting the next one's entry. -/
theorem combJP2Loop_ok {arithmetic : Mod → List FOp → Prog isa} {mc : List Instr} {K : TCombCfg} {C : Curve}
    {base : Addr} {size k : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hA : CombA K.toComb)
    {X : List Reg} (hcompiler : FieldCompilerOn K.M C X arithmetic size)
    (hX : ∀ r ∈ X, r ∈ tcombClob K.M.n ∧ r ≠ .x19) (hJenc : K.J<4096) (hC : Law C) (hM3 : AM3 C)
    (hG : onCurve C (G C) = true) (hV : TCombVals K C tbl) (hpn : C.p < 2 ^ (64 * K.M.n))
    (hb1 : 1 ≤ K.bits) {kmax : Nat} (hB : BoothOk C K.w K.J kmax) (hk : k < kmax) {s₀ : State}
    (hF : TCombFixed K C base size s₀ k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl))
    (hblk : arithmetic K.M (maddJ K.S K.A K.E K.D) = .block mc) (hck : JPChecks2 K size mc) {s : State}
    (hI : TCombJInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s₀ s 1)
    (E : TEntryPostJ K C base size k 1 s s) :
    WP isa (.loop (K.stepJP2 mc) (.nonzero .x .x4)) s fun s' =>
      TCombJInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s₀ s' (K.J - 1) ∧
      TEntryPostJ K C base size k (K.J - 1) s' s' := by
  have hJ3 := hck.J3
  refine WP.loop (M:=isa) (fun r s' => 1≤r ∧ r≤K.J-2 ∧
    TCombJInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s₀ s' (K.J-1-r) ∧
    TEntryPostJ K C base size k (K.J-1-r) s' s')
    (fun r s' ⟨hr,hrJ,hi,he⟩ => ?_) (K.J-2) s
    ⟨by omega_arith,by omega_arith,by simpa [show K.J-1-(K.J-2)=1 by omega_arith] using hI,
      by simpa [show K.J-1-(K.J-2)=1 by omega_arith] using E⟩
  refine WP.mono (stepJP2_ok hL hA hcompiler hX hJenc hC hM3 hG hV hpn hb1 hB hk hF hblk hck
    (j:=K.J-1-r) (by omega_arith) (by omega_arith) hi he) fun t ⟨ht,et,hx⟩ => ?_
  have hz : (t.read .x .x4 != 0)=decide (r-1≠0) := by
    rw [read_x,hx]
    apply Bool.eq_iff_iff.mpr
    simp only [bne_iff_ne,decide_eq_true_eq,ne_eq,BitVec.sub_eq_iff_eq_add]
    have eqn : BitVec.ofNat 64 (K.J-1-r+1)=BitVec.ofNat 64 (K.J-1) ↔ K.J-1-r+1=K.J-1 := by
      constructor
      · intro h
        have := congrArg BitVec.toNat h
        simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega_arith : K.J-1-r+1<2^64),
          Nat.mod_eq_of_lt (by omega_arith : K.J-1<2^64)] using this
      · exact congrArg (BitVec.ofNat 64)
    change (¬BitVec.ofNat 64 (K.J-1-r+1) = (0#64) + BitVec.ofNat 64 (K.J-1)) ↔ ¬r-1=0
    rw [BitVec.zero_add, eqn]
    omega_arith
  by_cases hr1 : r-1=0
  · refine Or.inl ⟨?_,?_,?_⟩
    · show some (t.read .x .x4 != 0)=some false
      rw [hz,hr1]; rfl
    · simpa only [show K.J-1-r+1=K.J-1 by omega_arith] using ht
    · simpa only [show K.J-1-r+1=K.J-1 by omega_arith] using et
  · refine Or.inr ⟨?_,r-1,by omega_arith,by omega_arith,by omega_arith,?_,?_⟩
    · show some (t.read .x .x4 != 0)=some true
      rw [hz,decide_eq_true hr1]
    · simpa only [show K.J-1-(r-1)=K.J-1-r+1 by omega_arith] using ht
    · simpa only [show K.J-1-(r-1)=K.J-1-r+1 by omega_arith] using et

/-- The pipelined comb computes `[k]G`, as `combJWith` does (`tcombJWith_ok`). -/
theorem tcombJP2_ok {arithmetic : Mod → List FOp → Prog isa} {mc : List Instr} {K : TCombCfg} {C : Curve}
    {base : Addr} {size k : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hA : CombA K.toComb)
    {X : List Reg} (hcompiler : FieldCompilerOn K.M C X arithmetic size)
    (hX : ∀ r ∈ X, r ∈ tcombClob K.M.n ∧ r ≠ .x19) (hJenc : K.J<4096) (hC : Law C) (hM3 : AM3 C)
    (hG : onCurve C (G C) = true) (hV : TCombVals K C tbl) (hpn : C.p < 2 ^ (64 * K.M.n))
    (hb1 : 1 ≤ K.bits) {kmax : Nat} (hB : BoothOk C K.w K.J kmax) (hk : k < kmax)
    (hblk : arithmetic K.M (maddJ K.S K.A K.E K.D) = .block mc) (hck : JPChecks2 K size mc) {s : State}
    (hs : Scr s base size) (hM : ModOkA K.M size C.p s.mem base)
    (hF : TCombFixed K C base size s k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl)) :
    WP isa (K.combJP2 arithmetic mc) s fun s' => KeepRegs (tcombClob K.M.n) s s' ∧
      Unch base (tcombW K) s.mem s'.mem ∧ ModOkA K.M size C.p s'.mem base ∧
      (∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      Rep C (tmv C K.M.n base s' K.A.x) (tmv C K.M.n base s' K.A.y) (tmv C K.M.n base s' K.A.z)
        (mul k (G C)) := by
  have hJ3 := hck.J3
  have hle : ∀ x, x ∈ combSlots K.toComb → x + 8 * K.M.n ≤ size := fun x hx => hL.comb.lay.le x hx
  unfold TCombCfg.combJP2
  refine WP.seq (WP.mono (firstJ_ok hL hA hC hG hV hpn hb1 hs hM hF) fun s₁ I₁ => ?_)
  have hz : wordsVal s₁.mem base K.zero K.M.n = 0 := by
    rw [I₁.unch.wordsVal (tcombW_ro hL (x := K.zero) (by simp [combRo, TCombCfg.toComb]))
      (by have := hle K.zero (by tcomb_mem); have := I₁.scr.nowrap; omega_arith), hF.zero]
  refine WP.seq (tentryJ_ok hL hA hC hV hpn I₁.scr I₁.mod (i := 1) (by omega_arith) I₁.x19 hb1 (c := true)
    (Or.inl ⟨rfl, Nat.le_refl _⟩) I₁.bits hz I₁.tsym I₁.tbl hF.out fun s₂ E₂ sy₂ => ?_)
  have I₂ := I₁.after_entry hL hF E₂ sy₂
  refine WP.seq (WP.mono (combJP2Loop_ok hL hA hcompiler hX hJenc hC hM3 hG hV hpn hb1 hB hk hF hblk hck I₂
    (E₂.self rfl E₂.scr)) fun s₃ ⟨I₃, E₃⟩ => ?_)
  have hT := tailJ_ok hL hA hcompiler hX hJenc hC hM3 hG hV hb1 hB hk hF (j := K.J - 1) (by omega_arith)
    (by omega_arith) I₃ E₃ rfl
  rw [hblk] at hT
  refine WP.seq (WP.mono hT fun s₄ ⟨I₄, _⟩ => ?_)
  rw [show K.J - 1 + 1 = K.J by omega_arith] at I₄
  exact tcombJOut_ok hL hA hcompiler hX hJenc hC hV hpn hB hk hs hM hF I₄

end VG.Proof.Weierstrass.AArch64
