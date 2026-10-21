module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombJStep
public import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelectV
public import VerifiedGarbage.Proof.Framework.AArch64.InterleaveTable
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombJ
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombJFirst
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombJDigit
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelect
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombTbl
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Ed25519.AArch64.Mem

/-!
# The pipelined comb on AArch64

`TCombCfg.combJP` (`Impl/Weierstrass/AArch64/TCombJ.lean`): window `1`'s
entry is selected and negated before the loop (`tentryJ_ok`); iteration `j`
then adds window `j`'s entry while it selects window `j + 1`'s: the pass of
the selection, of vector code reading only the table, is woven into the
addition's code, of scalar code (`WP.weave_tab`), so that they run as the
pass and then the addition; the addition and its corrections (`tailJ_ok`)
leave the vector registers alone, so the pass's accumulators survive to be
stored after the corrections (`tentryJFin_ok`, `stepJP_ok`). Window `J - 1`
is added alone (`tailJ_ok`). `tcombJP_ok`: the pipelined comb computes
`[k]G`, as `combJWith` does.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.AArch64.Interleave (scalOk vecOk TabApart)
open Spec.Weierstrass

/-- Code that writes no vector register keeps them all. -/
theorem WP.novec {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q)
    (hc : (instrs c).all (fun i => (vdstOf i).isNone) = true) : WP isa c s fun s' => Q s' ∧ s'.v = s.v := by
  obtain ⟨t, s', he, hq⟩ := h
  refine ⟨t, s', he, hq, funext fun r => Exec.vec (fun i hi e => ?_) he⟩
  have := List.all_eq_true.mp hc i hi
  rw [e] at this
  cases this

/-- What the pipelined comb's code must satisfy, checked by evaluation for a
curve: the addition `mc` is scalar code storing within the working space,
woven with the pass of the selection from the table at `x21`, and neither
`mc`, the corrections nor the digit write a vector register. -/
structure JPChecks (K : TCombCfg) (size : Nat) (mc : List Instr) : Prop where
  n4 : K.M.n ≤ 4
  n2 : K.M.n % 2 = 0
  J3 : 3 ≤ K.J
  scal : mc.all (scalOk .x0 .x21 size) = true
  vec : (K.selPass 0 K.M.n .x21).all (vecOk .x21 K.tblBytes) = true
  mcv : mc.all (fun i => (vdstOf i).isNone) = true
  fixv : (instrs K.fixJ).all (fun i => (vdstOf i).isNone) = true
  bdv : (K.bdigit true).all (fun i => (vdstOf i).isNone) = true

/-- `TEntryPostJ` at a state with the same memory, from itself. -/
theorem TEntryPostJ.self {K : TCombCfg} {C : Curve} {base : Addr} {size k i : Nat} {s t u : State}
    (E : TEntryPostJ K C base size k i s t) (hm : u.mem = t.mem) (hs : Scr u base size) :
    TEntryPostJ K C base size k i u u :=
  ⟨hs, rfl, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, fun _ _ => rfl, fun x hx => by rw [hm]; exact E.lt x hx,
    by rw [hm]; exact E.z, by unfold tmv; rw [hm]; exact E.rep⟩

/-- The invariant at a state with the same memory, regions and statics, and
the registers but `tcombClob`'s. -/
theorem TCombJInv.of_keep {K : TCombCfg} {C : Curve} {base : Addr} {size k : Nat} {T : Addr}
    {ws : List (BitVec 64)} {s₀ s t : State} {j : Nat} (I : TCombJInv K C base size k T ws s₀ s j)
    (hk : KeepRegs (tcombClob K.M.n) s t) (hm : t.mem = s.mem) (hb : t.gpr .x19 = BitVec.ofNat 64 j)
    (hsy : t.syms = s.syms) (hs : Scr t base size) : TCombJInv K C base size k T ws s₀ t j where
  scr := hs
  x19 := hb
  keep := I.keep.trans hk
  unch := by rw [hm]; exact I.unch
  mod := by rw [hm]; exact I.mod
  lt := by rw [hm]; exact I.lt
  rep := by unfold tmv; rw [hm]; exact I.rep
  bits := by rw [hm]; exact I.bits
  tbl := I.tbl.unch (by rw [hk.rd, hk.wr]) fun _ _ _ _ => by rw [hm]
  tsym := by rw [hsy]; exact I.tsym

theorem dec_ofNat (j : Nat) : BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 1 = BitVec.ofNat 64 j := by
  rw [← BitVec.ofNat_add_ofNat, BitVec.add_sub_cancel]

/-- `x19 = j + 1`. -/
theorem inc19_ok (s : State) {j : Nat} (h19 : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block [.addImm .x .x19 .x19 1]) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (j + 1) ∧ Keeps [.x19] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, Size.bits, show 1 < 4096 by decide,
    ite_true, RegUpd.gpr_write, BitVec.setWidth_eq, h19, BitVec.ofNat_add_ofNat, Option.some.injEq,
    exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

/-- `x19 = j` from `j + 1`, `x21` = table `j + 1`'s address and `x5 = 1`. -/
theorem setupNext_ok (K : TCombCfg) (s : State) {j : Nat} {T : Addr}
    (h19 : s.gpr .x19 = BitVec.ofNat 64 (j + 1)) (hT : s.syms K.tsym = T) (htb : K.tblBytes < 65536) :
    WP isa (.block ([.subImm .x .x19 .x19 1] ++ K.selSetupNext ++ [.movz .x .x5 1 0])) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 j ∧ t.gpr .x21 = T + BitVec.ofNat 64 ((j + 1) * K.tblBytes) ∧
      t.gpr .x5 = 1 ∧ Keeps [.x5, .x17, .x19, .x21] s t := by
  subst hT
  apply WP.of_runBlock
  simp only [TCombCfg.selSetupNext, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
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

theorem prep_tcombClob (n : Nat) (hn : n ≤ 9) :
    ∀ r ∈ [Reg.x2, .x3, .x4, .x5, .x7, .x9, .x16, .x17, .x19, .x21], r ∈ tcombClob n := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact combClob_tcombClob _ (List.mem_cons_self ..)
    | exact List.mem_append_right _ (List.mem_singleton_self _)
    | exact tcombClob_sub _ hn _ (List.mem_append_left _ (by decide))

/-- Before window `j`'s addition (`1 ≤ j`, `j + 2 ≤ J`): digit `j + 1`'s
magnitude broadcast for its selection (`v19`, with one in `v28` and two in
`v18`) and its table's address in `x21`, the rest as it was. -/
theorem prepNext_ok {K : TCombCfg} {C : Curve} {base : Addr} {size k : Nat} {T : Addr}
    {ws : List (BitVec 64)} (hL : TCombLay K size) (hb1 : 1 ≤ K.bits) {s₀ s : State} {j : Nat}
    (hjn : j + 2 ≤ K.J) (hI : TCombJInv K C base size k T ws s₀ s j) :
    WP isa (.block K.prepNext) s fun t => TCombJInv K C base size k T ws s₀ t j ∧ t.mem = s.mem ∧
      t.syms = s.syms ∧ KeepRegs (tcombClob K.M.n) s t ∧
      t.gpr .x21 = T + BitVec.ofNat 64 ((j + 1) * K.tblBytes) ∧
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
  have hcl := prep_tcombClob K.M.n hL.n8
  unfold TCombCfg.prepNext
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono_syms (inc19_ok s hI.x19) fun s₁ ⟨b₁, k₁⟩ sy₁ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono_syms (bdigit_ok K hs₁ (k := k) (j := j + 1) (N := K.w * K.J) (by omega_using [hw])
    (by omega_using [hw]) hwi (by omega_using [hb, hwi]) hb1 hwb b₁ (fun t ht => by rw [k₁.mem]; exact hI.bits t ht)
    (Or.inl ⟨rfl, by omega_using []⟩)) fun s₂ ⟨r₂, k₂⟩ sy₂ => ?_
  rw [← List.append_assoc, ← List.append_assoc, WP.block_append_iff]
  refine WP.mono_syms (setupNext_ok K s₂ (j := j) (T := T) (by rw [k₂.gpr _ (by decide), b₁])
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

/-- Words read from a table whose bytes two memories share. -/
theorem wordsVal_tbl {m m' : Mem} {X : Addr} {n H a : Nat} (ha : a ≤ H) (h1 : 1 ≤ a) {o : Nat}
    (ho : o ≤ 8 * n) (h : ∀ b < 16 * n * H, m' (X + BitVec.ofNat 64 b) = m (X + BitVec.ofNat 64 b)) :
    wordsVal m' X (16 * n * (a - 1) + o) n = wordsVal m X (16 * n * (a - 1) + o) n :=
  wordsVal_of_bytes n _ fun i hi b hb => by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    refine h _ ?_
    have := Nat.mul_le_mul_left (16 * n) (show a - 1 + 1 ≤ H by omega_using [ha, h1])
    rw [Nat.mul_succ] at this
    omega_using [this, ho, hi, hb]

/-- After window `i - 1`'s corrections (`1 ≤ i < J`, `x19 = i`), with the
pass of window `i`'s selection in the accumulators (of the table at `x21` in
`r`, whose bytes the memory keeps) and its magnitude in `v19`: the digit
again, its entry stored to `E`, and negated (`tentryJ_ok` for the pipelined
selection). -/
theorem tentryJFin_ok {K : TCombCfg} {C : Curve} {base : Addr} {size k i : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hA : CombA K.toComb) (hC : Law C)
    (hV : TCombVals K C tbl) (hpn : C.p < 2 ^ (64 * K.M.n)) (hn4 : K.M.n ≤ 4) (hn2 : K.M.n % 2 = 0)
    (hbdv : (K.bdigit true).all (fun i => (vdstOf i).isNone) = true) {u : State} (hs : Scr u base size)
    (hM : ModOkA K.M size C.p u.mem base) (hi : i < K.J) (hi1 : 1 ≤ i) (hx : u.gpr .x19 = BitVec.ofNat 64 i)
    (hb1 : 1 ≤ K.bits)
    (hbits : ∀ t < K.w * K.J, u.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0)
    (hz : wordsVal u.mem base K.zero K.M.n = 0)
    (hTM : TblMem u T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl))
    {r : State} (hr21 : r.gpr .x21 = T + BitVec.ofNat 64 (i * K.tblBytes))
    (hrm : ∀ b < K.tblBytes, r.mem (T + BitVec.ofNat 64 (i * K.tblBytes) + BitVec.ofNat 64 b) =
      u.mem (T + BitVec.ofNat 64 (i * K.tblBytes) + BitVec.ofNat 64 b))
    (h19 : u.v .v19 = dup2 (BitVec.ofNat 64 (bmag K.w k i)))
    (hacc : ∀ i' < K.M.n, u.v ((selA K.M.n).acc.getD i' .v0) =
      if 1 ≤ bmag K.w k i then ldE K.M.n 0 r (bmag K.w k i) i' .x21 else 0)
    {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s', TEntryPostJ K C base size k i u s' → s'.syms = u.syms → WP isa rest s' Q) :
    WP isa (.block K.finNext) u fun s₂ => WP isa (.seq (.block K.bnegY) rest) s₂ Q := by
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
  unfold TCombCfg.finNext
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono_syms (WP.novec (bdigit_ok K hs (k := k) (j := i) (N := K.w * K.J)
    (by omega_using [hw]) (by omega_using [hw]) hwi hb hb1 hwb hx hbits (Or.inl ⟨rfl, hi1⟩)) hbdv)
    fun t ⟨⟨hm, hk⟩, hv⟩ hsy => ?_
  have hs' := hs.of_keeps hk (by decide)
  have hM' : ModOkA K.M size C.p t.mem base := hk.mem ▸ hM
  have W := tselectFin_ok K hn4 hn2 hs' (a := bmag K.w k i) (by omega_using [hmag, hHle]) hm (r := r) (tb := .x21)
    (by rw [hv, h19]) (fun i' hi' => by rw [hv, hacc i' hi']) hE ⟨hL.e16.1, hL.e16.2 hn2⟩ hap
    (Nat.lt_trans hV.one_lt hpn)
  simp only [List.append_assoc] at W
  refine WP.mono_syms W fun s₂ ⟨ex, ey, ez, k₂, U₂⟩ sy₂ => ?_
  have hrt : ∀ b < 16 * K.M.n * K.H, t.mem (T + BitVec.ofNat 64 (i * K.tblBytes) + BitVec.ofNat 64 b) =
      r.mem (T + BitVec.ofNat 64 (i * K.tblBytes) + BitVec.ofNat 64 b) := fun b hb' => by
    rw [hk.mem]; exact (hrm b hb').symm
  rw [hr21] at ex ey
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

end VG.Proof.Weierstrass.AArch64
