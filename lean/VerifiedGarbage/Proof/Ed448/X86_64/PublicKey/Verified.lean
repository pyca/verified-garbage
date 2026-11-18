module

import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ed448.X86_64.PublicKey.Layout
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Pad
import VerifiedGarbage.Proof.Ed448.X86_64.PublicKey.Hash
import VerifiedGarbage.Proof.Ed448.X86_64.VariantVerified
import VerifiedGarbage.Proof.Ed448.X86_64.BaseVerified
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ed448.Ref
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Ed448.X86_64.PointSums
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Spec.Weierstrass
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ed448.X86_64.PublicKey.Layout
meta import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Pad
meta import VerifiedGarbage.Proof.Ed448.X86_64.PublicKey.Hash
meta import VerifiedGarbage.Proof.Ed448.X86_64.VariantVerified
meta import VerifiedGarbage.Proof.Ed448.X86_64.BaseVerified
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Ed448.Ref
meta import Aesop.BuiltinRules
meta import VerifiedGarbage.Proof.Ed448.X86_64.PointSums
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlKem.X86_64.Wp
meta import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.Proof.Ed448.X86_64.BaseLit
public import VerifiedGarbage.Proof.Ed448.X86_64.BaseLocal
public import VerifiedGarbage.Proof.Ed448.X86_64.VerifyVerified
public import VerifiedGarbage.Proof.Ed448.X86_64.VariantLit
public import VerifiedGarbage.Proof.Sha3.X86_64.Round
import VerifiedGarbage.Proof.Ed448.Prune
import VerifiedGarbage.Proof.Ed448.X86_64.Words57
import VerifiedGarbage.Proof.Ed448.X86_64.VariantBounds
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Ed448.X86_64.BaseLit
meta import VerifiedGarbage.Proof.Ed448.X86_64.BaseLocal
meta import VerifiedGarbage.Proof.Ed448.X86_64.VerifyVerified
meta import VerifiedGarbage.Proof.Ed448.X86_64.VariantLit
meta import VerifiedGarbage.Proof.Sha3.X86_64.Round
meta import VerifiedGarbage.Proof.Ed448.Prune
meta import VerifiedGarbage.Proof.Ed448.X86_64.Words57
meta import VerifiedGarbage.Proof.Ed448.X86_64.VariantBounds
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-! ### `Ed448.X86_64.PublicKey.Base`, which only this module used -/

section

/-!
# Ed448 public-key derivation on x86-64: pruning and the base point

The first 57 bytes of the hash, pruned, are stored in the frame
(`prune_ok`), `[s]B` is encoded into `out` (`base_ok`), and the frame's copy
of `s` is cleared (`wipe_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.PublicKey

variable {v : VG.Impl.Ed448.X86_64.FieldVariant}

open VG VG.X86_64 VG.Impl.Ed448.X86_64
open VG.Proof.Ed448 (prune_nat)

variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

/-! ## Stores into the frame -/

/-- Code that writes only caller-saved registers and the frame's scalar. -/
theorem Ctx.store {t t' : State} (hc : Ctx L g mx m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hmx : t'.mxcsr = t.mxcsr) (hg : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r)
    (hf : Frame [⟨L.B + BitVec.ofNat 64 16, 64⟩] t.mem t'.mem) : Ctx L g mx m₀ t' := by
  have keep : ∀ d, 80 ≤ d → d + 8 ≤ 104 →
      t'.mem.readW (L.B + BitVec.ofNat 64 d) 64 = t.mem.readW (L.B + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => hf.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)
  exact ⟨hrd.trans hc.rd, hwr.trans hc.wr, (hg .rsp (by decide)).trans hc.rsp,
    fun r hr hr' => (hg r hr).trans (hc.cs r hr hr'), by rw [hmx]; exact hc.mx,
    (keep 80 (by omega_arith) (by omega_arith)).trans hc.pScr, (keep 88 (by omega_arith) (by omega_arith)).trans hc.pSeed,
    (keep 96 (by omega_arith) (by omega_arith)).trans hc.pOut,
    hc.frame.trans (Frame.sub hf fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.STK, by simp, Offset.sub_base _ (by omega_arith)⟩)⟩

theorem st_ok {t : State} (hc : Ctx L g mx m₀ t) {k : Nat} (hk : k < 8) (r : Reg) :
    WP isa (.block [Instr.store (stk (8 * k)) r]) t fun t' =>
      t'.mem = t.mem.writeW (L.B + BitVec.ofNat 64 (16 + 8 * k)) (t.gpr r) ∧ t'.gpr = t.gpr ∧
        t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.mxcsr = t.mxcsr := by
  have w := hc.inFrW (d := 16 + 8 * k) (by omega_arith) (by omega_arith)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store64, ea_stk, hc.rsp, add_add, w,
    ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

/-- The first `n` stores of `pkStores`. -/
abbrev storesN (n : Nat) : List Instr := (List.range n).map fun k => .store (stk (8 * k)) (pkRegs.getD k .r8)

theorem stores_ok : ∀ n ≤ 8, ∀ t : State, Ctx L g mx m₀ t →
    WP isa (.block (storesN n)) t fun t' => Ctx L g mx m₀ t' ∧ t'.gpr = t.gpr ∧
      Frame [⟨L.B + BitVec.ofNat 64 16, 64⟩] t.mem t'.mem ∧
      ∀ j < n, t'.mem.readW (L.B + BitVec.ofNat 64 (16 + 8 * j)) 64 = t.gpr (pkRegs.getD j .r8)
  | 0, _, _, hc => WP.block_nil ⟨hc, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn, t, hc => by
    rw [storesN, List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (stores_ok n (by omega_arith) t hc) fun u ⟨hu, ug, uf, uw⟩ => ?_
    refine WP.mono (st_ok hu (k := n) (by omega_arith) _) fun v ⟨vm, vg, vrd, vwr, vmx⟩ => ?_
    have hf1 : Frame [⟨L.B + BitVec.ofNat 64 16, 64⟩] u.mem v.mem := by
      rw [vm]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega_arith) (by omega_arith)
        (by omega_arith))
    refine ⟨hu.store vrd vwr vmx (fun r _ => by rw [vg]) hf1, by rw [vg, ug], uf.trans hf1, fun j hj => ?_⟩
    rw [vm]
    by_cases hjn : j = n
    · subst hjn; rw [Mem.readW_writeW_self64, ug]
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide), uw j (by omega_arith)]

/-! ## Pruning -/

/-- Word `k` of the hash. -/
abbrev hw (t : State) (L : Lay) (k : Nat) : BitVec 64 :=
  t.mem.readW (L.scr + BitVec.ofNat 64 (1024 + 8 * k)) 64

/-- `rdx = scratch`. -/
theorem rdx_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block [Instr.mov .rdx (.mem (stk fScratch))]) t fun t' => Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧
      t'.gpr .rdx = L.scr := by
  have h80 := hc.inFr (d := 80) (by omega_arith) (by omega_arith)
  apply WP.of_runBlock
  simp only [fScratch, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_stk,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, Option.map_some, ite_true, hc.rsp, add_add, Nat.reduceAdd, h80,
    hc.pScr, Option.some.injEq, exists_eq_left']
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial, trivial⟩

theorem loads_ok {t : State} (hc : Ctx L g mx m₀ t) (hdx : t.gpr .rdx = L.scr) :
    WP isa (.block pkLoads) t fun t' => Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧
      t'.gpr .r8 = hw t L 0 ∧ t'.gpr .r9 = hw t L 1 ∧ t'.gpr .r10 = hw t L 2 ∧ t'.gpr .r11 = hw t L 3 ∧
      t'.gpr .rax = hw t L 4 ∧ t'.gpr .rcx = hw t L 5 ∧ t'.gpr .rsi = hw t L 6 := by
  have s0 := hc.inScr (o := 1024) (by omega_arith)
  have s1 := hc.inScr (o := 1032) (by omega_arith)
  have s2 := hc.inScr (o := 1040) (by omega_arith)
  have s3 := hc.inScr (o := 1048) (by omega_arith)
  have s4 := hc.inScr (o := 1056) (by omega_arith)
  have s5 := hc.inScr (o := 1064) (by omega_arith)
  have s6 := hc.inScr (o := 1072) (by omega_arith)
  apply WP.of_runBlock
  simp only [pkLoads, hashWord, hashAt, Nat.reduceMul, Nat.reduceAdd, runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, State.load64, ea_base, RegUpd.gpr_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, RegUpd.mem_setReg, Option.map_some, reduceCtorEq, ite_false, ite_true, hdx,
    s0, s1, s2, s3, s4, s5, s6, Option.some.injEq, exists_eq_left']
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial, trivial, trivial, trivial, trivial, trivial, trivial,
    trivial⟩

theorem mods_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block pkMods) t fun t' => Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧
      t'.gpr .r8 = (t.gpr .r8 &&& BitVec.ofNat 64 (2 ^ 64 - 4)) ∧ t'.gpr .r9 = t.gpr .r9 ∧
      t'.gpr .r10 = t.gpr .r10 ∧ t'.gpr .r11 = t.gpr .r11 ∧ t'.gpr .rax = t.gpr .rax ∧
      t'.gpr .rcx = t.gpr .rcx ∧ t'.gpr .rsi = (t.gpr .rsi ||| BitVec.ofNat 64 (2 ^ 63)) ∧
      t'.gpr .rdi = 0 := by
  apply WP.of_runBlock
  simp only [pkMods, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, readSrc32, State.setReg32,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.gpr_arithFlags,
    RegUpd.mem_arithFlags, Option.map_some, Option.bind_some,
    reduceCtorEq, ite_false, ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial,
    congrArg (_ &&& ·) (by decide : BitVec.signExtend 64 (BitVec.ofInt 32 (-4)) = BitVec.ofNat 64 (2 ^ 64 - 4)),
    trivial, trivial, trivial, trivial, trivial, trivial, rfl⟩

/-- The loads, the pruning and the stores, with `rdx = scratch`. -/
theorem pruneRest_ok {t₀ : State} (hc₀ : Ctx L g mx m₀ t₀) (hd₀ : t₀.gpr .rdx = L.scr) {h : List Byte}
    (hh : Spec.Sha3.bytesAt t₀.mem (L.scr + BitVec.ofNat 64 1024) 114 = h) :
    WP isa (.block (pkLoads ++ (pkMods ++ pkStores))) t₀ fun t' => Ctx L g mx m₀ t' ∧
      Spec.Ed448.decodeLE (Spec.Ed448.bytesAt t'.mem (L.B + BitVec.ofNat 64 16) 57) = Spec.Ed448.prune h := by
  rw [WP.block_append_iff]
  refine WP.mono (loads_ok hc₀ hd₀) fun u ⟨hu, hmu, u8, u9, u10, u11, uax, ucx, usi⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mods_ok hu) fun v ⟨hv, hmv, v8, v9, v10, v11, vax, vcx, vsi, vdi⟩ => ?_
  refine WP.mono (stores_ok 8 (by omega_arith) v hv) fun w ⟨hw', _, _, ww⟩ => ⟨hw', ?_⟩
  have f0 : w.mem.readW (L.B + BitVec.ofNat 64 16) 64 = v.gpr .r8 := ww 0 (by omega_arith)
  have f1 : w.mem.readW (L.B + BitVec.ofNat 64 24) 64 = v.gpr .r9 := ww 1 (by omega_arith)
  have f2 : w.mem.readW (L.B + BitVec.ofNat 64 32) 64 = v.gpr .r10 := ww 2 (by omega_arith)
  have f3 : w.mem.readW (L.B + BitVec.ofNat 64 40) 64 = v.gpr .r11 := ww 3 (by omega_arith)
  have f4 : w.mem.readW (L.B + BitVec.ofNat 64 48) 64 = v.gpr .rax := ww 4 (by omega_arith)
  have f5 : w.mem.readW (L.B + BitVec.ofNat 64 56) 64 = v.gpr .rcx := ww 5 (by omega_arith)
  have f6 : w.mem.readW (L.B + BitVec.ofNat 64 64) 64 = v.gpr .rsi := ww 6 (by omega_arith)
  have f7 : w.mem.readW (L.B + BitVec.ofNat 64 72) 64 = v.gpr .rdi := ww 7 (by omega_arith)
  rw [decode57]
  simp only [add_add, Nat.reduceAdd]
  rw [f0, f1, f2, f3, f4, f5, f6, byte_of_zero _ _ (f7.trans vdi), v8, v9, v10, v11, vax, vcx, vsi, u8, u9,
    u10, u11, uax, ucx, usi, Spec.Ed448.prune, ← hh, take57, decode57]
  simp only [hw, add_add, Nat.reduceMul, Nat.reduceAdd]
  refine Eq.trans ?_ (prune_nat _ _ _ _ _ _ _ _ (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _)
    (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _)).symm
  have c₁ : (2 ^ 64 - 4) % 2 ^ 64 = 2 ^ 64 - 4 := by decide
  have c₂ : 2 ^ 63 % 2 ^ 64 = 2 ^ 63 := by decide
  rw [BitVec.toNat_and, BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat, c₁, c₂]

theorem prune_ok {t : State} (hc : Ctx L g mx m₀ t) {h : List Byte}
    (hh : Spec.Sha3.bytesAt t.mem (L.scr + BitVec.ofNat 64 1024) 114 = h) :
    WP isa pkPrune t fun t' => Ctx L g mx m₀ t' ∧
      Spec.Ed448.decodeLE (Spec.Ed448.bytesAt t'.mem (L.B + BitVec.ofNat 64 16) 57) = Spec.Ed448.prune h :=
  WP.seq (WP.mono (rdx_ok hc) fun _ ⟨hc₀, hm₀, hd₀⟩ => pruneRest_ok hc₀ hd₀ (hm₀ ▸ hh))

/-! ## The base point -/

/-- The arguments of `vg_ed448_scalar_base`. -/
def BaseArgs (L : Lay) (t : State) : Prop :=
  t.gpr .rdi = L.out ∧ t.gpr .rsi = L.B + BitVec.ofNat 64 16 ∧ t.gpr .rdx = L.scr

theorem baseArgs_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block pkBaseArgs) t fun t' => Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧ BaseArgs L t' := by
  have l80 := hc.inFr (d := 80) (by omega_arith) (by omega_arith)
  have l96 := hc.inFr (d := 96) (by omega_arith) (by omega_arith)
  apply WP.of_runBlock
  simp only [pkBaseArgs, fOut, fScratch, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.load64, ea_stk, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    Option.map_some, reduceCtorEq, ite_false, ite_true, hc.rsp, add_add, Nat.reduceAdd, l80, l96,
    Option.some.injEq, exists_eq_left', hc.pScr, hc.pOut, BaseArgs]
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial, trivial, trivial, trivial⟩

theorem base_nosp : NoSp (scalarBaseFor v) := scalarBaseFor_nosp v

theorem base_depth : (scalarBaseFor v).depth ≤ 1 := scalarBaseFor_depth v

abbrev baseRd (L : Lay) : List Region := [⟨L.B + BitVec.ofNat 64 16, 57⟩]
abbrev baseWr (L : Lay) : List Region := [L.OUT, L.SCR]

theorem base_regs {t : State} (ha : BaseArgs L t) (rd wr : List Region) :
    (t.callEntry.withRegions rd wr).gpr .rdi = L.out ∧
      (t.callEntry.withRegions rd wr).gpr .rsi = L.B + BitVec.ofNat 64 16 ∧
      (t.callEntry.withRegions rd wr).gpr .rdx = L.scr :=
  ⟨(gpr_ce _ _ _ (by decide)).trans ha.1, (gpr_ce _ _ _ (by decide)).trans ha.2.1,
    (gpr_ce _ _ _ (by decide)).trans ha.2.2⟩

theorem base_pre (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (ha : BaseArgs L t) :
    Proof.Ed448.X86_64.scalarBaseLocal.pre (t.callEntry.withRegions (baseRd L) (baseWr L)) := by
  obtain ⟨g1, g2, g3⟩ := base_regs ha (baseRd L) (baseWr L)
  simp only [Proof.Ed448.X86_64.scalarBaseLocal, g1, g2, g3, rsp_ce, hc.rsp, sub8,
    State.withRegions_rd, State.withRegions_wr]
  exact ⟨trivial, trivial, hL.stk_SCR (by omega_arith), hL.stk_OUT (by omega_arith), hL.stk_SCR (by omega_arith), hL.oc, hL.nc⟩

/-- The callee's buffers are apart from the 8 bytes below its `rsp`, the frame's lowest. -/
theorem base_clear (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) :
    Clear (hole ((t.callEntry.withRegions (baseRd L) (baseWr L)).gpr .rsp))
      (t.callEntry.withRegions (baseRd L) (baseWr L)) := by
  rw [rsp_ce, hc.rsp, sub8, Proof.Ed448.X86_64.hole_add8]
  intro r hr
  simp only [State.withRegions_rd, State.withRegions_wr, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
  · simpa using (hL.stk_OUT (d := 0) (n := 8) (by omega_arith)).symm
  · simpa using (hL.stk_SCR (d := 0) (n := 8) (by omega_arith)).symm

theorem base_sub : ∀ r ∈ baseRd L ++ baseWr L, ∃ R ∈ [L.SEED, L.FR, L.OUT, L.SCR], Within r R := by
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact ⟨L.FR, by simp, within_stk _ (by omega_arith) (by omega_arith)⟩
  · exact ⟨L.OUT, by simp, within_base _ (by omega_arith)⟩
  · exact ⟨L.SCR, by simp, within_base _ (by omega_arith)⟩

theorem base_wsub : ∀ r ∈ baseWr L, Within r L.OUT ∨ Within r L.SCR := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact .inl (within_base _ (by omega_arith))
  · exact .inr (within_base _ (by omega_arith))

theorem base_ok (hb : Proof.Ed448.BaseLadderOk) (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t)
    (ha : BaseArgs L t) {s : Nat}
    (hs : Spec.Ed448.decodeLE (Spec.Ed448.bytesAt t.mem (L.B + BitVec.ofNat 64 16) 57) = s) :
    WP isa (.call ("vg_ed448_scalar_base" ++ v.suffix) (scalarBaseFor v)) t fun t' => Ctx L g mx m₀ t' ∧
      Spec.Ed448.bytesAt t'.mem L.out 57 =
        Spec.Ed448.encodePoint (Spec.Ed448.pointMul s Spec.Ed448.basePoint) := by
  refine call_ok hL (Proof.Ed448.X86_64.scalarBaseFor_ok v hb) base_nosp base_depth hc
    ⟨base_pre hL hc ha, base_clear hL hc⟩ base_sub base_wsub fun s' hc' _ _ ⟨s₂, hm, _, hpost⟩ => ⟨hc', ?_⟩
  obtain ⟨g1, g2, -⟩ := base_regs ha (baseRd L) (baseWr L)
  have h := hpost
  simp only [Contract.clear, Proof.Ed448.X86_64.scalarBaseLocal, g1, g2, State.withRegions_mem, hm] at h
  have e : Spec.Ed448.bytesAt t.callEntry.mem (L.B + BitVec.ofNat 64 16) 57 =
      Spec.Ed448.bytesAt t.mem (L.B + BitVec.ofNat 64 16) 57 := by
    simp only [Spec.Ed448.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    exact ce_byte t (R := ⟨L.B + BitVec.ofNat 64 16, 57⟩) (by
      rw [hc.ret]; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith))
      (by show (57 : Nat) ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  rw [h, e, Spec.Ed448.scalarBase, hs]

/-! ## Clearing the scalar -/

theorem zero_regs_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block (pkRegs.map fun r => Instr.mov32 r (.imm 0))) t fun t' =>
      Ctx L g mx m₀ t' ∧ t'.mem = t.mem := by
  apply WP.of_runBlock
  simp only [pkRegs, List.map_cons, List.map_nil, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32,
    State.setReg32, Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), rfl⟩

theorem wipe_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block pkWipe) t fun t' => Ctx L g mx m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 16, 64⟩] t.mem t'.mem := by
  rw [pkWipe, WP.block_append_iff]
  refine WP.mono (zero_regs_ok hc) fun u ⟨hu, hm⟩ => ?_
  exact WP.mono (stores_ok 8 (by omega_arith) u hu) fun u' ⟨hu', _, hf, _⟩ => ⟨hu', hm ▸ hf⟩

end VG.Proof.Ed448.X86_64.PublicKey

end

end

/-!
# Ed448 public-key derivation on x86-64: `Verified`

The frame's body leaves the public key in `out` (`body_ok`), and the whole
function meets `pkLocal` and the ABI (`publicKey_ok`), given that the
reference ladder encodes `[k]B` (`BaseLadderOk`, which the registration file
passes in).

Constant time: two runs whose pointers agree have the same layout, so between
the frame's push and pop they are related by `Two`: both satisfy `Ctx` with
that layout (and `Φ`, what the next block or call needs of the registers),
whatever their secrets. The blocks address only the stack and `scratch`, from
registers that agree (the taint analysis); each call is of constant-time code
whose public data, its pointers and lengths, agree (`RelCT.callEx`).
-/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.PublicKey

variable {v : VG.Impl.Ed448.X86_64.FieldVariant}

open VG VG.X86_64 VG.Impl.Ed448.X86_64

variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

/-! ## Correctness -/

/-- The public key of the seed in `out`. -/
theorem body_ok (hb : Proof.Ed448.BaseLadderOk) (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (pkBodyFor v) t fun t' => Ctx L g mx m₀ t' ∧
      Spec.Ed448.bytesAt t'.mem L.out 57 = Spec.Ed448.publicKey (Spec.Ed448.bytesAt m₀ L.seed 57) := by
  refine WP.seq (WP.mono (hash_ok hL hc) fun t₁ ⟨hc₁, hh₁⟩ => ?_)
  refine WP.seq (WP.mono (prune_ok hc₁ hh₁) fun t₂ ⟨hc₂, hs₂⟩ => ?_)
  refine WP.seq (WP.mono (baseArgs_ok hc₂) fun t₃ ⟨hc₃, hm₃, ha₃⟩ => ?_)
  refine WP.seq (WP.mono (base_ok hb hL hc₃ ha₃ (hm₃ ▸ hs₂)) fun t₄ ⟨hc₄, ho₄⟩ => ?_)
  refine WP.mono (wipe_ok hc₄) fun t₅ ⟨hc₅, hf₅⟩ => ⟨hc₅, ?_⟩
  have e : Spec.Ed448.bytesAt t₅.mem L.out 57 = Spec.Ed448.bytesAt t₄.mem L.out 57 := by
    simp only [Spec.Ed448.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    exact Frame.bytes (R := L.OUT) hf₅ (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact (hL.stk_OUT (d := 16) (n := 64) (by omega_using [])).symm) (by show (57 : Nat) ≤ 2 ^ 64; decide)
      (List.mem_range.mp hi)
  rw [e, ho₄]
  rfl

theorem pop_rsp (B : Addr) : B + BitVec.ofNat 64 16 + BitVec.ofNat 64 (8 * 11) = B + BitVec.ofNat 64 104 := by
  rw [add_add]

/-- The bytes of a region apart from a frame are what they were once the
frame's bytes are lost. -/
private theorem bytes_lost {F : Region} {m m' : Mem} (f : Frame [F] m m') {p : Addr} {n : Nat}
    (hd : (⟨p, n⟩ : Region).Disjoint F) : Spec.Ed448.bytesAt m' p n = Spec.Ed448.bytesAt m p n := by
  simp only [Spec.Ed448.bytesAt]
  exact List.map_congr_left fun i hi => lost_byte f hd (List.mem_range.mp hi)

/-- `vg_ed448_public_key` meets `pkLocal` and the ABI. -/
theorem publicKey_ok (hb : Proof.Ed448.BaseLadderOk) {s : State} (h : pkLocal.pre s) :
    WP isa (publicKeyFor v) s fun s' => abiPreserved s s' ∧ pkLocal.post s s' := by
  have hL := lay_ok h
  have hc := push_ctx h
  refine WP.frame (rs := pushRs) (by decide) (by decide) (by decide) (by show 8 * 11 ≤ _; have := h.1; omega_using [this])
    (WP.mono (body_ok hb hL hc) fun u ⟨hu, ho⟩ => ⟨hu.rsp.trans hc.rsp.symm, hu.wr.trans hc.wr.symm,
      fun m uk fm => ?_⟩)
  -- The pop loses the frame's 88 bytes, in the stack below `rsp`.
  obtain hF : Region.Sub ⟨s.gpr .rsp - BitVec.ofNat 64 (8 * pushRs.length), 8 * pushRs.length⟩ (lay s).STK :=
    Offset.sub_below _ (by decide) (by decide)
  dsimp only
  refine ⟨?_, ?_⟩
  · have hrsp : (popped .rax pushRs.length u).gpr .rsp = s.gpr .rsp := by
      rw [popped_rsp, hu.rsp, show pushRs.length = 11 from rfl, pop_rsp, lay_ret]
    refine ⟨fun r hr => ?_, ?_, by rw [popped_mxcsr, hu.mx]⟩
    · by_cases hr' : r = .rsp
      · subst hr'; exact hrsp
      · rw [popped_gpr _ _ _ hr' (ne_cs hr (by decide)), hu.cs r hr hr']
    · rw [fm.readW (r := (lay s).RET) (by rw [Lay.RET, lay_ret]; exact Region.contains_self _ _) (fun r hr => by
        rw [List.mem_singleton.mp hr, Lay.RET, lay_ret]
        exact (Offset.base_disjoint_below (s.gpr .rsp) (n := 104) (k := 8) (by decide)).sub_right hF) (by decide)]
      refine hu.frame.readW (r := (lay s).RET) ?_ ?_ (by decide)
      · rw [Lay.RET, lay_ret]; exact Region.contains_self _ _
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hL.ro
        · exact hL.rc
        · exact Offset.disjoint_base _ (by omega_using []) (by omega_using [])
  · show Spec.Ed448.bytesAt m (lay s).out 57 = _
    rw [bytes_lost fm (hL.ko.symm.sub_right hF), ho]
    rfl

/-! ## Constant time -/

/-- What each of two runs has, between the frame's push and pop. -/
abbrev Two.Env := Lay × (Reg → BitVec 64) × (Reg → BitVec 64) × BitVec 32 × BitVec 32 × Mem × Mem

/-- Two runs with the same layout, each satisfying `Ctx` and `Φ`. -/
def Two (Φ : Lay → State → Prop) (a b : State) : Prop :=
  ∃ e : Two.Env, e.1.Ok ∧ Ctx e.1 e.2.1 e.2.2.2.1 e.2.2.2.2.2.1 a ∧
    Ctx e.1 e.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2.2 b ∧ Φ e.1 a ∧ Φ e.1 b

/-- Code whose runs leak the same, and which keeps `Ctx` and establishes `Ψ`. -/
theorem two_wp {c : Prog isa} {Φ Ψ : Lay → State → Prop}
    (hct : RelCT isa (Two Φ) c fun _ _ => True)
    (hw : ∀ (L : Lay) g mx m₀ (t : State), L.Ok → Ctx L g mx m₀ t → Φ L t →
      WP isa c t fun t' => Ctx L g mx m₀ t' ∧ Ψ L t') :
    RelCT isa (Two Φ) c (Two Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨⟨L, g₁, g₂, mx₁, mx₂, m₁, m₂⟩, hL, c₁, c₂, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw L g₁ mx₁ m₁ s₁ hL c₁ f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw L g₂ mx₂ m₂ s₂ hL c₂ f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, ⟨L, g₁, g₂, mx₁, mx₂, m₁, m₂⟩, hL, y₁.1, y₂.1, y₁.2, y₂.2⟩

/-- A block whose addresses depend only on the registers `rs`, which agree. -/
theorem two_block {is : List Instr} {Φ : Lay → State → Prop} (rs : List Reg)
    (hrs : ∀ L t₁ t₂ g₁ g₂ mx₁ mx₂ m₁ m₂, Ctx L g₁ mx₁ m₁ t₁ → Ctx L g₂ mx₂ m₂ t₂ → Φ L t₁ → Φ L t₂ →
      ∀ r ∈ rs, t₁.gpr r = t₂.gpr r)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T} (h : (taint.check (Taint.ofRegs rs) (.block is) hc).isSome = true) :
    RelCT isa (Two Φ) (.block is) fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs rs)
    (fun _ _ ⟨_, _, c₁, c₂, f₁, f₂⟩ => Taint.agree_ofRegs (hrs _ _ _ _ _ _ _ _ _ c₁ c₂ f₁ f₂)) h

theorem rsp_two {L : Lay} {t₁ t₂ : State} {g₁ g₂ : Reg → BitVec 64} {mx₁ mx₂ : BitVec 32} {m₁ m₂ : Mem}
    (c₁ : Ctx L g₁ mx₁ m₁ t₁) (c₂ : Ctx L g₂ mx₂ m₂ t₂) : t₁.gpr .rsp = t₂.gpr .rsp :=
  c₁.rsp.trans c₂.rsp.symm

theorem covers {t : State} (hc : Ctx L g mx m₀ t) {rd wr : List Region}
    (hsub : ∀ r ∈ rd ++ wr, ∃ R ∈ [L.SEED, L.FR, L.OUT, L.SCR], Within r R)
    (hwsub : ∀ r ∈ wr, Within r L.OUT ∨ Within r L.SCR) :
    Covers (rd ++ wr) (t.rd ++ t.wr) ∧ Covers wr t.wr := by
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · obtain ⟨R, hR, hw⟩ := hsub r hr
    exact ⟨R, by rw [hc.rd, hc.wr]; simpa using hR, hw⟩
  · rw [hc.wr]
    rcases hwsub r hr with h | h
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩

/-- A call, with the same regions in both runs. -/
theorem two_call {n : String} {c : Prog isa} {k : Contract isa} {Φ : Lay → State → Prop}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (rd wr : Lay → List Region)
    (hpre : ∀ (L : Lay) g mx m₀ (t : State), L.Ok → Ctx L g mx m₀ t → Φ L t →
      k.pre (t.callEntry.withRegions (rd L) (wr L)))
    (hpub : ∀ L t₁ t₂ g₁ g₂ mx₁ mx₂ m₁ m₂, Ctx L g₁ mx₁ m₁ t₁ → Ctx L g₂ mx₂ m₂ t₂ → Φ L t₁ → Φ L t₂ →
      k.pub (t₁.callEntry.withRegions (rd L) (wr L)) (t₂.callEntry.withRegions (rd L) (wr L)))
    (hsub : ∀ L, ∀ r ∈ rd L ++ wr L, ∃ R ∈ [L.SEED, L.FR, L.OUT, L.SCR], Within r R)
    (hwsub : ∀ L, ∀ r ∈ wr L, Within r L.OUT ∨ Within r L.SCR) :
    RelCT isa (Two Φ) (.call n c) fun _ _ => True :=
  RelCT.callEx hv hct fun _ _ ⟨⟨L, _⟩, hL, c₁, c₂, f₁, f₂⟩ =>
    ⟨rd L, wr L, rd L, wr L, hpre _ _ _ _ _ hL c₁ f₁, hpre _ _ _ _ _ hL c₂ f₂,
      hpub _ _ _ _ _ _ _ _ _ c₁ c₂ f₁ f₂, (covers c₁ (hsub L) (hwsub L)).1, (covers c₁ (hsub L) (hwsub L)).2,
      (covers c₂ (hsub L) (hwsub L)).1, (covers c₂ (hsub L) (hwsub L)).2, rsp_two c₁ c₂⟩

/-- A block, with what it establishes. -/
theorem two_blk {is : List Instr} {Φ Ψ : Lay → State → Prop} (rs : List Reg)
    (hrs : ∀ L t₁ t₂ g₁ g₂ mx₁ mx₂ m₁ m₂, Ctx L g₁ mx₁ m₁ t₁ → Ctx L g₂ mx₂ m₂ t₂ → Φ L t₁ → Φ L t₂ →
      ∀ r ∈ rs, t₁.gpr r = t₂.gpr r)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T} (h : (taint.check (Taint.ofRegs rs) (.block is) hc).isSome = true)
    (hw : ∀ (L : Lay) g mx m₀ (t : State), L.Ok → Ctx L g mx m₀ t → Φ L t →
      WP isa (.block is) t fun t' => Ctx L g mx m₀ t' ∧ Ψ L t') :
    RelCT isa (Two Φ) (.block is) (Two Ψ) :=
  two_wp (two_block rs hrs h) hw

/-- A call of verified code, after which `Ctx` holds again. -/
theorem two_callP {n : String} {c : Prog isa} {k : Contract isa} {Φ : Lay → State → Prop}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (hsp : NoSp c) (hd : c.depth ≤ 1) (rd wr : Lay → List Region)
    (hpre : ∀ (L : Lay) g mx m₀ (t : State), L.Ok → Ctx L g mx m₀ t → Φ L t →
      k.pre (t.callEntry.withRegions (rd L) (wr L)))
    (hpub : ∀ L t₁ t₂ g₁ g₂ mx₁ mx₂ m₁ m₂, Ctx L g₁ mx₁ m₁ t₁ → Ctx L g₂ mx₂ m₂ t₂ → Φ L t₁ → Φ L t₂ →
      k.pub (t₁.callEntry.withRegions (rd L) (wr L)) (t₂.callEntry.withRegions (rd L) (wr L)))
    (hsub : ∀ L, ∀ r ∈ rd L ++ wr L, ∃ R ∈ [L.SEED, L.FR, L.OUT, L.SCR], Within r R)
    (hwsub : ∀ L, ∀ r ∈ wr L, Within r L.OUT ∨ Within r L.SCR) :
    RelCT isa (Two Φ) (.call n c) (Two fun _ _ => True) :=
  two_wp (two_call hv hct rd wr hpre hpub hsub hwsub) fun L _ _ _ _ hL hc hf =>
    call_ok hL hv hsp hd hc (hpre _ _ _ _ _ hL hc hf) (hsub L) (hwsub L) fun _ hc' _ _ _ => ⟨hc', trivial⟩

theorem rspOnly {Φ : Lay → State → Prop} : ∀ (L : Lay) (t₁ t₂ : State) g₁ g₂ mx₁ mx₂ m₁ m₂,
    Ctx L g₁ mx₁ m₁ t₁ → Ctx L g₂ mx₂ m₂ t₂ → Φ L t₁ → Φ L t₂ → ∀ r ∈ [Reg.rsp], t₁.gpr r = t₂.gpr r := by
  intro L t₁ t₂ _ _ _ _ _ _ c₁ c₂ _ _ r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact rsp_two c₁ c₂

/-- `rsp` and the register `r`, which `Φ` fixes for the layout. -/
theorem rspAnd {Φ : Lay → State → Prop} (r : Reg) (v : Lay → BitVec 64) (hv : ∀ L t, Φ L t → t.gpr r = v L) :
    ∀ (L : Lay) (t₁ t₂ : State) g₁ g₂ mx₁ mx₂ m₁ m₂,
    Ctx L g₁ mx₁ m₁ t₁ → Ctx L g₂ mx₂ m₂ t₂ → Φ L t₁ → Φ L t₂ → ∀ x ∈ [Reg.rsp, r], t₁.gpr x = t₂.gpr x := by
  intro L t₁ t₂ _ _ _ _ _ _ c₁ c₂ f₁ f₂ x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact rsp_two c₁ c₂
  · exact (hv L t₁ f₁).trans (hv L t₂ f₂).symm

/-- The frame's body. -/
theorem body_ct (hb : Proof.Ed448.BaseLadderOk) : RelCT isa (Two fun _ _ => True) (pkBodyFor v) fun _ _ => True := by
  -- zeroing the state
  have z₁ : RelCT isa (Two fun _ _ => True) (.block pkZeroHead)
      (Two fun L t => t.gpr .rdi = L.scr ∧ t.gpr .rax = 0) :=
    two_blk [.rsp] rspOnly (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (zeroHead_ok hc) fun _ ⟨hc', _, h1, h2⟩ => ⟨hc', h1, h2⟩
  have z₂ : RelCT isa (Two fun L t => t.gpr .rdi = L.scr ∧ t.gpr .rax = 0) (.block pkZeroStores)
      (Two fun _ _ => True) :=
    two_wp (two_block [.rsp, .rdi] (rspAnd .rdi Lay.scr fun _ _ h => h.1) (by taint_decide))
      fun _ _ _ _ t hL hc hf => WP.mono (zstores_ok hL 25 (by omega_using []) t hc hf.1 hf.2) fun _ h => ⟨h.1, trivial⟩
  -- `absorb`
  have a₁ : RelCT isa (Two fun _ _ => True) (.block pkAbsorbArgs) (Two AbsArgs) :=
    two_blk [.rsp] rspOnly (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (absArgs_ok hc) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have a₂ := two_callP (n := "vg_keccak_absorb_scratch") (Φ := AbsArgs)
    Proof.Sha3.X86_64.Stream.Absorb.absorb_correct Proof.Sha3.X86_64.Stream.Absorb.absorb_ct
    absorb_nosp absorb_depth absRd absWr (fun _ _ _ _ _ hL hc ha => abs_pre hL hc ha)
    (fun L t₁ t₂ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => by
      obtain ⟨d₁, s₁, x₁, c₁', r₁, n₁⟩ := abs_regs a₁ (absRd L) (absWr L)
      obtain ⟨d₂, s₂, x₂, c₂', r₂, n₂⟩ := abs_regs a₂ (absRd L) (absWr L)
      exact ⟨d₁.trans d₂.symm, s₁.trans s₂.symm, x₁.trans x₂.symm, c₁'.trans c₂'.symm,
        r₁.trans r₂.symm, n₁.trans n₂.symm, by rw [rsp_ce, rsp_ce, rsp_two c₁ c₂]⟩)
    (fun _ => abs_sub) (fun _ => abs_wsub)
  -- `pad`
  have p₁ : RelCT isa (Two fun _ _ => True) (.block pkPadArgs) (Two PadArgs) :=
    two_blk [.rsp] rspOnly (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (padArgs_ok hc) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have p₂ := two_callP (n := "vg_keccak_pad_scratch") (Φ := PadArgs)
    Proof.Sha3.X86_64.Stream.Pad.pad_correct Proof.Sha3.X86_64.Stream.Pad.pad_ct
    pad_nosp pad_depth (fun _ => padRd) padWr (fun _ _ _ _ _ hL hc ha => pad_pre hL hc ha)
    (fun L t₁ t₂ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => by
      obtain ⟨d₁, s₁, x₁, -, r₁⟩ := pad_regs a₁ padRd (padWr L)
      obtain ⟨d₂, s₂, x₂, -, r₂⟩ := pad_regs a₂ padRd (padWr L)
      exact ⟨d₁.trans d₂.symm, s₁.trans s₂.symm, x₁.trans x₂.symm, r₁.trans r₂.symm,
        by rw [rsp_ce, rsp_ce, rsp_two c₁ c₂]⟩)
    (fun _ => pad_sub) (fun _ => pad_wsub)
  -- `squeeze`
  have q₁ : RelCT isa (Two fun _ _ => True) (.block pkSqueezeArgs) (Two SqzArgs) :=
    two_blk [.rsp] rspOnly (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (sqzArgs_ok hc) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have q₂ := two_callP (n := "vg_keccak_squeeze_scratch") (Φ := SqzArgs)
    Proof.Sha3.X86_64.Stream.Squeeze.squeeze_correct Proof.Sha3.X86_64.Stream.Squeeze.squeeze_ct
    squeeze_nosp squeeze_depth (fun _ => sqzRd) sqzWr (fun _ _ _ _ _ hL hc ha => sqz_pre hL hc ha)
    (fun L t₁ t₂ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => by
      obtain ⟨d₁, s₁, x₁, c₁', r₁, n₁⟩ := sqz_regs a₁ sqzRd (sqzWr L)
      obtain ⟨d₂, s₂, x₂, c₂', r₂, n₂⟩ := sqz_regs a₂ sqzRd (sqzWr L)
      exact ⟨d₁.trans d₂.symm, s₁.trans s₂.symm, x₁.trans x₂.symm, c₁'.trans c₂'.symm,
        r₁.trans r₂.symm, n₁.trans n₂.symm, by rw [rsp_ce, rsp_ce, rsp_two c₁ c₂]⟩)
    (fun _ => sqz_sub) (fun _ => sqz_wsub)
  -- pruning
  have r₁ : RelCT isa (Two fun _ _ => True) (.block [Instr.mov .rdx (.mem (stk fScratch))])
      (Two fun L t => t.gpr .rdx = L.scr) :=
    two_blk [.rsp] rspOnly (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (rdx_ok hc) fun _ ⟨hc', _, h⟩ => ⟨hc', h⟩
  have r₂ : RelCT isa (Two fun L t => t.gpr .rdx = L.scr) (.block (pkLoads ++ (pkMods ++ pkStores)))
      (Two fun _ _ => True) :=
    two_wp (two_block [.rsp, .rdx] (rspAnd .rdx Lay.scr fun _ _ h => h) (by taint_decide))
      fun _ _ _ _ _ _ hc hd => WP.mono (pruneRest_ok hc hd rfl) fun _ h => ⟨h.1, trivial⟩
  -- the base point
  have b₁ : RelCT isa (Two fun _ _ => True) (.block pkBaseArgs) (Two BaseArgs) :=
    two_blk [.rsp] rspOnly (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (baseArgs_ok hc) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have b₂ := two_callP (n := "vg_ed448_scalar_base" ++ v.suffix) (Φ := BaseArgs)
    (Proof.Ed448.X86_64.scalarBaseFor_ok v hb) (Proof.Ed448.X86_64.scalarBaseFor_ct v)
    base_nosp base_depth baseRd baseWr (fun _ _ _ _ _ hL hc ha => ⟨base_pre hL hc ha, base_clear hL hc⟩)
    (fun L t₁ t₂ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => by
      obtain ⟨d₁, s₁, x₁⟩ := base_regs a₁ (baseRd L) (baseWr L)
      obtain ⟨d₂, s₂, x₂⟩ := base_regs a₂ (baseRd L) (baseWr L)
      exact ⟨by rw [rsp_ce, rsp_ce, rsp_two c₁ c₂], d₁.trans d₂.symm, s₁.trans s₂.symm, x₁.trans x₂.symm⟩)
    (fun _ => base_sub) (fun _ => base_wsub)
  have w : RelCT isa (Two fun _ _ => True) (.block pkWipe) fun _ _ => True :=
    two_block [.rsp] rspOnly (by taint_decide)
  exact ((z₁.seq z₂).seq ((a₁.seq a₂).seq ((p₁.seq p₂).seq (q₁.seq q₂)))).seq
    ((r₁.seq r₂).seq (b₁.seq (b₂.seq w)))

theorem publicKey_ct (hb : Proof.Ed448.BaseLadderOk) : ConstantTime isa pkLocal.pre pkLocal.pub (publicKeyFor v) := by
  refine RelCT.constantTime (RelCT.frame (fun _ _ h => h.2.2.1) (RelCT.mono (body_ct hb) ?_ fun _ _ _ => trivial))
  rintro _ _ ⟨s₁, s₂, ⟨h₁, h₂, hsp, hdi, hsi, hdx⟩, rfl, rfl⟩
  have e : lay s₂ = lay s₁ := by simp only [lay, hsp, hdi, hsi, hdx]
  exact ⟨⟨lay s₁, s₁.gpr, s₂.gpr, s₁.mxcsr, s₂.mxcsr, s₁.mem, s₂.mem⟩, lay_ok h₁, push_ctx h₁,
    e ▸ push_ctx h₂, trivial, trivial⟩

/-! ## The shared contract -/

theorem implies : pkLocal.Implies (Spec.Ed448.publicKeyContract X86_64.abi 104) := by
  sig_implies [Spec.Ed448.publicKeyContract, Spec.Ed448.publicKeySig, Spec.Ed448.scratchWords,
    X86_64.abi, X86_64.argRegs, pkLocal] [Proof.Ed448.X86_64.scalarBaseSat]
    using Proof.Ed448.X86_64.scalarBaseSat

theorem publicKey_verified (hb : Proof.Ed448.BaseLadderOk) :
    Verified X86_64.target (publicKeyFor v) (Spec.Ed448.publicKeyContract X86_64.abi 104) :=
  Verified.of_correct (fun _ h => publicKey_ok hb h) (publicKey_ct hb) implies

end VG.Proof.Ed448.X86_64.PublicKey
