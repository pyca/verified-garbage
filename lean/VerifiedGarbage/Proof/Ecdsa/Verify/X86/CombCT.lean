module

public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.PublicValues
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.Front
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.Main
public import VerifiedGarbage.Proof.Ecdsa.X86.CombTaint
public import VerifiedGarbage.Proof.Ecdsa.X86.CombLays
public import VerifiedGarbage.Proof.Ecdsa.X86.CombPrefix
public import VerifiedGarbage.Proof.Ecdsa.X86.CombFunctionCT
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.WindowPoints
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombMain
import VerifiedGarbage.Proof.Ecdsa.X86.CombMain
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ECDSA verification on x86 (32-bit), with a fixed-base comb

`Cfg.verifyComb`, for any curve with a comb, stage by stage as the signature
(`Proof/Ecdsa/X86/CombFunctionCT.lean`): the taints the stages' invariants
give (`vFrontAgree`, `vKeepArgAgree`, `vKeepScratchAgree`), the body's
constant time from its stages' taint checks and its points'
(`vCombBody_rel`), and, for a curve whose comb is by complete additions, the
points by the comb and the ladder (`vPointsLadder_rel`) and the whole
function: correct (`verifyComb_ok`) and constant time (`verifyComb_ct`) in
the pointers alone.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86
open VG.Impl.Ecdsa.Verify.X86

variable {c : Impl.Ecdsa.X86.Cfg}

/-- The front starts at the function's entry: its arguments public, the
fourth the base of the working space, and the calls' stack below. -/
def vFrontτ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [8192], argLen := 20, argBases := [(16, 0)],
    room := 20 }

theorem vFrontWf {s : State} {extra : List Region} (hp : VPre c s extra) : VG.X86.Taint.Wf vFrontτ s := by
  have hsc := hp.sc_fit; have hs := hp.sp_fit
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨by simp [hp.wr, vFrontτ], by simp [hp.wr], ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩ fun _ => ⟨Nat.le_trans (Cfg.stk_ge c) hp.sp_lo, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r rfl; simp only [ptr, BitVec.toNat_setWidth]; omega_using [hsc]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r rfl
    exact VG.X86.Taint.frame_disjoint (n := 16) (by omega_using [hs]) hp.ret_sc hp.args_sc
  · intro p hp'
    simp only [vFrontτ, List.mem_cons, List.not_mem_nil, or_false] at hp'
    subst hp'
    refine ⟨by decide, ?_⟩
    simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr, ptr]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r rfl
    have := Cfg.stk_ge c
    exact hp.stk_sc.sub_left (Offset.sub_below _ (a := 20) (n := 20) this (by omega_using [this]))

/-- Equal stack pointers and arguments establish the front's agreement. -/
theorem vFrontAgree {s t : State} {extra₁ extra₂ : List Region} (hp : VPre c s extra₁)
    (hq : VPre c t extra₂) (he : s.gpr .esp = t.gpr .esp) (ha : ∀ j < 4, arg s j = arg t j) :
    VG.X86.Taint.Agree vFrontτ s t := by
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, vFrontWf hp, vFrontWf hq,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => he,
    fun k h4 hk => ?_⟩
  · simp only [vFrontτ, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact he
  · rw [hp.wr, hq.wr]; simp only [ptr, ha 3 (by decide)]
  · simp only [vFrontτ] at hk
    rw [show VG.X86.Taint.depth vFrontτ.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (by have := hp.sp_fit; omega_using [this]) h4 hk,
      VG.X86.Taint.argByte_eq (by have := hq.sp_fit; omega_using [this]) h4 hk,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (ha ((k - 4) / 4) (by omega_using [hk]))

/-- Scratch writes preserve the four cdecl argument words. -/
theorem vKeep_arg {s₀ s : State} {extra : List Region}
    (hp : VPre c s₀ extra) (h : Keep c s₀ (ptr s₀ 3) s) {j : Nat} (hj : j < 4) :
    arg s j = arg s₀ j := by
  have he : argAddr s j = argAddr s₀ j := by simp only [argAddr, h.esp]
  change s.mem.readW (argAddr s j) 32 = _
  rw [he]
  have h4 : (s₀.gpr .esp).toNat + 4 + 4 * 4 ≤ 2 ^ 32 := by have := hp.sp_fit; omega_using [this]
  refine h.whole.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rw [hp.wr] at hr
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.args_sc.sub_left (arg_subN h4 hj)
  · exact (below_disjoint_args hp.sp_lo (k := 16) (by omega_using [h4]) (by decide)).symm.sub_left (arg_subN h4 hj)

theorem vArgWf {s₀ s : State} {extra : List Region} (rs : List Reg)
    (hp : VPre c s₀ extra) (he : s.gpr .esp = s₀.gpr .esp) (hw : s.wr = s₀.wr) :
    VG.X86.Taint.Wf (argτ rs 4 c.stk) s := by
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨?_, ?_, ?_, ?_, ?_⟩ fun _ => ⟨by rw [he]; exact hp.sp_lo, ?_⟩
  rotate_right
  · rw [he, hw, hp.wr]
    intro r hr
    rw [List.mem_singleton.mp hr]
    exact hp.stk_sc
  · intro h; cases h rfl
  · intro p h; cases h
  · intro p h; cases h
  · intro _
    rw [he, hw, hp.wr]
    refine ⟨hp.sp_fit, ?_⟩
    intro r hr
    rw [List.mem_singleton.mp hr]
    exact VG.X86.Taint.frame_disjoint (n := 16) (by have := hp.sp_fit; omega_using [this]) hp.ret_sc hp.args_sc
  · intro p h; cases h

theorem vKeepArgAgree {s₀ t₀ s t : State} {extra₁ extra₂ : List Region}
    (hp : VPre c s₀ extra₁) (hq : VPre c t₀ extra₂)
    (ks : Keep c s₀ (ptr s₀ 3) s) (kt : Keep c t₀ (ptr t₀ 3) t)
    (he : s₀.gpr .esp = t₀.gpr .esp) (ha : ∀ j < 4, arg s₀ j = arg t₀ j) :
    VG.X86.Taint.Agree (argτ [.esp, .edi] 4 c.stk) s t := by
  have esp : s.gpr .esp = t.gpr .esp := ks.esp.trans (he.trans kt.esp.symm)
  have edi : s.gpr .edi = t.gpr .edi := widen32_inj (ks.scr.edi.trans
    ((congrArg (BitVec.setWidth 64) (ha 3 (by decide))).trans kt.scr.edi.symm))
  refine argAgree (vArgWf _ hp ks.esp ks.wr) (vArgWf _ hq kt.esp kt.wr) ?_ esp ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact esp
    · exact edi
  · intro j hj
    rw [vKeep_arg hp ks hj, vKeep_arg hq kt hj, ha j hj]

theorem vKeepCombWf {s₀ s : State} {extra : List Region} (hp : VPre c s₀ extra)
    (ks : Keep c s₀ (ptr s₀ 3) s) : VG.X86.Taint.Wf (combτAt false) s := by
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨?_, ?_, ?_, ?_, ?_⟩ fun _ => ⟨?_, ?_⟩
  rotate_right 2
  · rw [ks.esp]; exact Nat.le_trans (Cfg.stk_ge c) hp.sp_lo
  · rw [ks.esp, ks.wr, hp.wr]
    intro r hr
    rw [List.mem_singleton.mp hr]
    exact hp.stk_sc.sub_left (stk20_sub (Cfg.stk_ge c) hp.sp_lo)
  · intro _
    rw [ks.wr, hp.wr]
    refine ⟨by simp [combτAt, size], by simp, ?_⟩
    intro r hr
    rw [List.mem_singleton.mp hr]
    simp only [ptr, BitVec.toNat_setWidth]; omega_using [hp.sc_fit]
  · intro p h
    rw [List.mem_singleton.mp h]
    change addr (s.gpr .edi) 0 = (VG.X86.Taint.region s 0).base
    simp only [VG.X86.Taint.region, ks.wr, hp.wr, List.getD_cons_zero, addr, BitVec.add_zero]
    exact ks.scr.edi
  · intro p h; cases h
  · intro h; cases h
  · intro p h; cases h

theorem vKeepScratchAgree {s₀ t₀ s t : State} {extra₁ extra₂ : List Region}
    (hp : VPre c s₀ extra₁) (hq : VPre c t₀ extra₂)
    (ks : Keep c s₀ (ptr s₀ 3) s) (kt : Keep c t₀ (ptr t₀ 3) t)
    (he : s₀.gpr .esp = t₀.gpr .esp) (ha : ∀ j < 4, arg s₀ j = arg t₀ j) :
    VG.X86.Taint.Agree (scratchArgτ 4 false c.stk) s t := by
  refine scratchArgAgree (vKeepArgAgree hp hq ks kt he ha) (vKeepCombWf hp ks) (vKeepCombWf hq kt) ?_
  rw [ks.wr, kt.wr, hp.wr, hq.wr]
  simp only [ptr, ha 3 (by decide)]

/-- Inputs to the fixed-base multiplication, after converting `u` to bits. -/
structure VCombInput (c : Impl.Ecdsa.X86.Cfg) (s₀ : State) (base : Addr) (s : State) : Prop extends
    Keep c s₀ base s where
  scalar : ∃ k, k < 2 ^ (64 * c.n) ∧
    (∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 0 + t)) = if k.testBit t then 1 else 0)
  rx : sv c base s RX = 0
  ry : sv c base s RY = c.mont 1
  rz : sv c base s RZ = 0
  values : VPublicValues c s₀ base s

theorem vBits_ok (hc : CfgOk c) {s₀ s : State} {base : Addr} (h : Mid c s₀ base s) :
    WP isa (Impl.Weierstrass.X86.bits (c.sl U) (bitsAt c.n 0) (8 * c.n)) s
      (VCombInput c s₀ base) := by
  have h7 := hc.n10
  refine WP.mono (bits_ok h.scr hc.n0 (sl_le c h7 (i := U) (by decide)) (tbl_le h7)
    (Or.inl (by have := sl_below_bits c (i := U) (by decide) 0 0; omega_using [this]))) fun t ⟨b, k, o⟩ => ?_
  have unch : Unch base [(bitsAt c.n 0, 64 * c.n)] s.mem t.mem := o.unch
  have v : ∀ {i}, i < 45 → sv c base t i = sv c base s i := fun hi =>
    sv_unch unch h7 h.scr.nowrap hi (apart_tbl hi 0)
  have hsc : (⟨base, size⟩ : Region) ∈ s₀.wr ++ [below (s₀.gpr .esp) c.stk] :=
    List.mem_append_left _ (by rw [← h.wr]; exact h.scr.wr)
  exact ⟨⟨h.scr.of_keeps k (by decide), (k.gpr _ (by decide)).trans h.esp,
    k.rd.trans h.rd, k.wr.trans h.wr, h.fixed.unch h7 h.scr.nowrap (fixedOk_tbl 0) unch,
    h.whole.trans (frame_of_unch unch (fun w hw => by rw [List.mem_singleton.mp hw]; exact tbl_le h7) hsc),
    h.sp_lo⟩,
    ⟨sv c base s U, wordsVal_lt _ _ _ _, b⟩,
    (v (by decide)).trans h.rx, (v (by decide)).trans h.ry, (v (by decide)).trans h.rz,h.publicValues.transfer (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl <;> exact v (by decide))⟩

/-- Read-only comb tables outside the working space. -/
def VCombTables (c : Impl.Ecdsa.X86.Cfg) (d : CombData) (s : State) : Prop :=
  TblMem s ((s.gpr .eax).setWidth 64) (c.combWords d) ∧
  (∀ i < (c.combWords d).length, ∀ b < 8,
    size ≤ ofs (ptr s 3) ((s.gpr .eax).setWidth 64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b)) ∧
  ∀ r ∈ s.wr ++ [below (s.gpr .esp) c.stk],
    Region.Disjoint ⟨(s.gpr .eax).setWidth 64, 8 * (c.combWords d).length⟩ r

variable {d : CombData}

theorem vTables_keep {s₀ s : State} (ht : VCombTables c d s₀) (K : Keep c s₀ (ptr s₀ 3) s) :
    TblMem s ((s₀.gpr .eax).setWidth 64) (c.combWords d) ∧
      ∀ r ∈ s.wr ++ [below (s.gpr .esp) 20],
        Region.Disjoint ⟨(s₀.gpr .eax).setWidth 64, 8 * (c.combWords d).length⟩ r :=
  K.tbls ht.1 ht.2.2

theorem vPoints_keep (hc : CfgOk c) (hC : Law c.C) (hT : CombTbls c) (hcd : c.comb = some d)
    (hCo : ∀ d, c.comb = some d → CombOk c d) (ham3 : c.n = 4 ∧ c.combJac = true → AM3 c.C)
    {s₀ s : State} (ht : VCombTables c d s₀) (h : Mid c s₀ (ptr s₀ 3) s)
    (hspG : SpOk c.gMul 20) (hsp : SpOk (Impl.Ecdsa.Verify.X86.Cfg.pointsComb c) c.stk) :
    WP isa (Impl.Ecdsa.Verify.X86.Cfg.pointsComb c) s (Keep c s₀ (ptr s₀ 3)) := by
  let P := Ecdh.X86.peerPt c (s₀.mem (ptr s₀ 0) = 4)
    (keyX c s₀) (keyY c s₀)
  have hPc : onCurve c.C P = true := Ecdh.X86.peerPt_onCurve hc _ _ _
  have hQ : Rep c.C (tmv c.C c.n (ptr s₀ 3) s (c.sl Impl.Ecdh.X86.PX))
      (tmv c.C c.n (ptr s₀ 3) s (c.sl Impl.Ecdh.X86.PY))
      (tmv c.C c.n (ptr s₀ 3) s (c.sl ONEP)) P := by
    obtain ⟨_, _, h1⟩ := consts_tmv hc h.fixed
    rw [h1]
    exact Ecdh.X86.peerPt_rep hC _ _ _ h.px h.py
  have H := pointsComb_ok hc hC hT hCo ham3 h
    (fun d' hd => by
      have e : d = d' := Option.some.inj (hcd.symm.trans hd)
      subst d'
      exact ⟨(vTables_keep ht h.keep).1, ht.2.1, ht.2.2⟩)
    hPc hQ hspG hsp
    (rest := .block []) (fun _ P => WP.block_nil P.keep)
  exact WP.mono (WP.seq_iff.mp H) (fun _ q => WP.block_nil_iff.mp q)

structure VCombPre (c : Cfg) (s : State) : Prop extends
    VPre c s (Abi.constRegions (fun n => (s.syms n).setWidth 64) c.combConsts) where
  tbls : TblsHeld c s (below (s.gpr .esp) c.stk :: s.wr)
  pk_stack : Region.Disjoint ⟨ptr s 0, 1 + 2 * c.C.len⟩ (below (s.gpr .esp) 4)
  dg_stack : Region.Disjoint ⟨ptr s 1, c.C.len⟩ (below (s.gpr .esp) 4)
  sig_stack : Region.Disjoint ⟨ptr s 2, 2 * c.C.len⟩ (below (s.gpr .esp) 4)


theorem VCombPre.sp4 {s : State} (hp : VCombPre c s) : 4 ≤ (s.gpr .esp).toNat := by
  have := Cfg.stk_ge c; have := hp.toVPre.sp_lo; omega_arith

theorem VPre.symAddr {s t : State} {extra : List Region} {name : String}
    (hp : VPre c s extra) (h : SymAddrPost name s t) (hsp : 4 ≤ (s.gpr .esp).toNat) : VPre c t extra := by
  have he := h.gpr .esp (by decide)
  have ha : ∀ j < 4, arg t j = arg s j := fun j hj => h.arg hsp (by have := hp.sp_fit; omega_using [hj, this])
  have haa : argAddr t 0 = argAddr s 0 := by simp only [argAddr, he]
  exact {
    rd := by simpa only [ptr, ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), haa, h.rd] using hp.rd
    wr := by simpa only [ptr, ha 3 (by decide), h.wr] using hp.wr
    pk_sc := by simpa only [ptr, ha 0 (by decide), ha 3 (by decide)] using hp.pk_sc
    dg_sc := by simpa only [ptr, ha 1 (by decide), ha 3 (by decide)] using hp.dg_sc
    sig_sc := by simpa only [ptr, ha 2 (by decide), ha 3 (by decide)] using hp.sig_sc
    args_sc := by simpa only [ptr, haa, ha 3 (by decide)] using hp.args_sc
    ret_sc := by simpa only [ptr, he, ha 3 (by decide)] using hp.ret_sc
    pk_fit := by rw [ha 0 (by decide)]; exact hp.pk_fit
    dg_fit := by rw [ha 1 (by decide)]; exact hp.dg_fit
    sig_fit := by rw [ha 2 (by decide)]; exact hp.sig_fit
    sc_fit := by rw [ha 3 (by decide)]; exact hp.sc_fit
    sp_fit := by rw [he]; exact hp.sp_fit
    sp_lo := by rw [he]; exact hp.sp_lo
    stk_sc := by simpa only [stkR, ptr, he, ha 3 (by decide)] using hp.stk_sc }

theorem VKeep.abi {s₀ s : State} {extra : List Region} (hp : VPre c s₀ extra) (K : VKeep c s₀ s) :
    abiPreserved s₀ s := by
  refine ⟨?_, ?_⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact K.saved (.ebx, 0) (by decide)
    · exact K.saved (.esi, 4) (by decide)
    · exact K.saved (.edi, 8) (by decide)
    · exact K.saved (.ebp, 12) (by decide)
    · exact K.esp
  · exact K.ret hp

theorem vPrefixTables {s t : State} (hcd : c.comb = some d) (hp : VCombPre c s)
    (P : SymAddrPost d.tsym s t) : VCombTables c d t := by
  have hp' := hp.toVPre.symAddr P hp.sp4
  have held := hp.tbls.symAddr (Nat.le_trans (by decide) (Cfg.stk_ge _)) hp.toVPre.sp_lo P
  have ht := tbl_of_held (c := c) (d := d) (base := ptr t 3) hcd held
    (by rw [hp'.wr]; simp) (fun r hr => by rw [hp'.rd]; simp only [P.syms] at hr; simp [hr]) (Unch.refl _ _ _)
  simpa only [VCombTables, P.addr, P.syms] using ht

/-! ## The stages' constant time, for any curve with a comb -/

/-- The taint checks of the stages of a curve's verification around its points: the checks of
the key, from the arguments; the scalars; and the final comparison. -/
structure VerifyStagesCT (c : Cfg) : Prop where
  front : RelCT isa (VG.X86.Taint.Agree vFrontτ) (Impl.Ecdsa.Verify.X86.Cfg.combFront c) (fun _ _ => True)
  mid : RelCT isa (VG.X86.Taint.Agree (scratchArgτ 4 false c.stk))
    (Impl.Ecdsa.Verify.X86.Cfg.combMid c) (fun _ _ => True)
  final : RelCT isa (VG.X86.Taint.Agree (scratchArgτ 4 false c.stk))
    (Impl.Ecdsa.Verify.X86.Cfg.tail c) (fun _ _ => True)

/-- The taint checks of `[u]G + [v]Q` by the comb and the ladder, around the comb: the table of
`u`'s bits, and all that follows `[u]G`. -/
structure VerifyLadderCT (c : Cfg) : Prop where
  bits : RelCT isa (VG.X86.Taint.Agree (argτ [.esp, .edi] 4 c.stk))
    (Impl.Weierstrass.X86.bits (c.sl U) (bitsAt c.n 0) (8 * c.n)) (fun _ _ => True)
  ladder : RelCT isa (VG.X86.Taint.Agree (scratchArgτ 4 false c.stk))
    (.seq (.block (Impl.Ecdsa.Verify.X86.Cfg.save c))
      (.seq (Impl.Weierstrass.X86.bits (c.sl V) (bitsAt c.n 0) (8 * c.n))
        (.seq (Impl.Weierstrass.X86.ladder (Impl.Ecdh.X86.Cfg.ladderQ c) c.SP)
          (Impl.Ecdsa.Verify.X86.Cfg.sum c)))) (fun _ _ => True)

/-- `[u]G + [v]Q` by the comb and the ladder leaks the same in two runs, whatever their
scalars and keys. -/
theorem vPointsLadder_rel (hc : CfgOk c) (hC : Law c.C) (hT : CombTbls c) (hcd : c.comb = some d)
    (hd : CombOk c d) (hG : GMulRel c d false) (ct : VerifyLadderCT c)
    {s₀ t₀ : State} {extra₁ extra₂ : List Region}
    (hp : VPre c s₀ extra₁) (hq : VPre c t₀ extra₂)
    (ht₁ : VCombTables c d s₀) (ht₂ : VCombTables c d t₀)
    (he : s₀.gpr .esp = t₀.gpr .esp) (ha : ∀ j < 4, arg s₀ j = arg t₀ j)
    (hg : s₀.gpr .eax = t₀.gpr .eax) (hspG : SpOk c.gMul 20) :
    RelCT isa (fun s t => Mid c s₀ (ptr s₀ 3) s ∧ Mid c t₀ (ptr t₀ 3) t)
      (Impl.Ecdsa.Verify.X86.Cfg.pointsCombLadder c) (fun _ _ => True) := by
  have hspG' : SpOk c.gMul c.stk := ⟨hspG.1, Nat.le_trans hspG.2 (Cfg.stk_ge _)⟩
  have hsp20 : ∀ {u₀ u : State} {extra : List Region}, VPre c u₀ extra →
      Keep c u₀ (ptr u₀ 3) u → 20 ≤ (u.gpr .esp).toNat := fun hp k => by
    rw [k.esp]; exact Nat.le_trans (Cfg.stk_ge _) hp.sp_lo
  have bits := ct.bits.mono
    (P' := fun s t => Mid c s₀ (ptr s₀ 3) s ∧ Mid c t₀ (ptr t₀ 3) t)
    (fun _ _ h => vKeepArgAgree hp hq h.1.keep h.2.keep he ha) (fun _ _ _ => trivial)
  have bits' := bits.wp (F₁ := VCombInput c s₀ (ptr s₀ 3))
    (F₂ := VCombInput c t₀ (ptr t₀ 3)) (fun s t h => ⟨vBits_ok hc h.1, vBits_ok hc h.2⟩)
  have hCo : ∀ d', c.comb = some d' → CombOk c d' := by
    intro d' h; have e : d = d' := Option.some.inj (hcd.symm.trans h); rw [← e]; exact hd
  have multCT : RelCT isa (fun s t => True ∧
      VCombInput c s₀ (ptr s₀ 3) s ∧ VCombInput c t₀ (ptr t₀ 3) t)
      c.gMul (fun _ _ => True) := by
    intro s t tr₁ tr₂ s' t' h e₁ e₂
    obtain ⟨_, S, T⟩ := h
    obtain ⟨tb₁, ap₁⟩ := vTables_keep ht₁ S.toKeep
    obtain ⟨tb₂, ap₂⟩ := vTables_keep ht₂ T.toKeep
    have hb : ptr s₀ 3 = ptr t₀ 3 := congrArg (BitVec.setWidth 64) (ha 3 (by decide))
    have T' := T
    rw [← hb] at T'
    obtain ⟨k₁, hk₁, b₁⟩ := S.scalar
    obtain ⟨k₂, hk₂, b₂⟩ := T'.scalar
    exact hG S.scr T'.scr S.fixed T'.fixed
      hk₁ hk₂ b₁ b₂ tb₁ tb₂ ht₁.2.1 ap₁ ap₂ (hsp20 hp S.toKeep) (hsp20 hq T.toKeep) hg
      (vKeepCombWf hp S.toKeep) (vKeepCombWf hq T.toKeep)
      (by rw [S.wr, T.wr, hp.wr, hq.wr]; simp only [ptr, ha 3 (by decide)])
      (by rw [S.esp, T.esp, he])
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  have functional : ∀ {u₀ u : State} {extra : List Region}, VPre c u₀ extra → VCombTables c d u₀ →
      VCombInput c u₀ (ptr u₀ 3) u →
      WP isa c.gMul u (Keep c u₀ (ptr u₀ 3)) := by
    intro u₀ u extra hp ht S
    obtain ⟨k, hk, b⟩ := S.scalar
    refine S.toKeep.withSp hspG' (WP.mono (gMul_ok' hc hC hT hCo S.scr S.fixed
      hk S.rx S.ry S.rz b ?_ (hsp20 hp S.toKeep) hspG) fun t h f => S.toKeep.gMul hc h.1 h.2.1 f)
    intro d' h
    have e : d = d' := Option.some.inj (hcd.symm.trans h)
    subst d'
    obtain ⟨tb, ap⟩ := vTables_keep ht S.toKeep
    exact ⟨tb, ht.2.1, ap⟩
  have mult := multCT.wp (F₁ := Keep c s₀ (ptr s₀ 3)) (F₂ := Keep c t₀ (ptr t₀ 3))
    (fun _ _ h => ⟨functional hp ht₁ h.2.1, functional hq ht₂ h.2.2⟩)
  exact bits'.seq (mult.seq (ct.ladder.mono
    (fun _ _ h => vKeepScratchAgree hp hq h.2.1 h.2.2 he ha) (fun _ _ _ => trivial)))

/-- Verification's body with a comb is constant time, given its points' (`hPts`: the comb with
the ladder, `vPointsLadder_rel`, or with P-256's windows). -/
theorem vCombBody_rel (hc : CfgOk c) (hC : Law c.C) (hT : CombTbls c) (hcd : c.comb = some d)
    (hd : CombOk c d) (ham3 : c.n = 4 ∧ c.combJac = true → AM3 c.C) (ct : VerifyStagesCT c)
    {s₀ t₀ : State} {extra₁ extra₂ : List Region}
    (hp : VPre c s₀ extra₁) (hq : VPre c t₀ extra₂)
    (ht₁ : VCombTables c d s₀) (ht₂ : VCombTables c d t₀)
    (he : s₀.gpr .esp = t₀.gpr .esp) (ha : ∀ j < 4, arg s₀ j = arg t₀ j)
    (hPts : RelCT isa (fun s t => Mid c s₀ (ptr s₀ 3) s ∧ Mid c t₀ (ptr t₀ 3) t)
      (Impl.Ecdsa.Verify.X86.Cfg.pointsComb c) (fun _ _ => True))
    (hspG : SpOk c.gMul 20)
    (hsp : SpOk (Impl.Ecdsa.Verify.X86.Cfg.verifyCombBody c) c.stk) :
    RelCT isa (fun s t => s = s₀ ∧ t = t₀) (Impl.Ecdsa.Verify.X86.Cfg.verifyCombBody c)
      (fun _ _ => True) := by
  have H := VCSp.of hsp
  have front := ct.front.mono (P' := fun s t => s = s₀ ∧ t = t₀)
    (fun _ _ h => by
      rcases h with ⟨rfl, rfl⟩
      exact vFrontAgree hp hq he ha)
    (fun _ _ _ => trivial)
  have front' := front.wp (F₁ := Front c s₀ (ptr s₀ 3))
    (F₂ := Front c t₀ (ptr t₀ 3)) (fun _ _ h => by
      rcases h with ⟨rfl, rfl⟩
      exact ⟨front_ok hc hp H.validate (fun _ h => WP.block_nil h),
        front_ok hc hq H.validate (fun _ h => WP.block_nil h)⟩)
  have mid := ct.mid.mono
    (P' := fun s t => True ∧ Front c s₀ (ptr s₀ 3) s ∧ Front c t₀ (ptr t₀ 3) t)
    (fun _ _ h => vKeepScratchAgree hp hq h.2.1.keep h.2.2.keep he ha) (fun _ _ _ => trivial)
  have mid' := mid.wp (F₁ := Mid c s₀ (ptr s₀ 3))
    (F₂ := Mid c t₀ (ptr t₀ 3)) (fun _ _ h =>
      ⟨mid_ok hc h.2.1 H.scalars H.nPow H.uv (fun _ h => WP.block_nil h),
        mid_ok hc h.2.2 H.scalars H.nPow H.uv (fun _ h => WP.block_nil h)⟩)
  have pts := hPts.mono
    (P' := fun s t => True ∧ Mid c s₀ (ptr s₀ 3) s ∧ Mid c t₀ (ptr t₀ 3) t)
    (fun _ _ h => h.2) (fun _ _ _ => trivial)
  have hCo : ∀ d', c.comb = some d' → CombOk c d' := by
    intro d' h; have e : d = d' := Option.some.inj (hcd.symm.trans h); rw [← e]; exact hd
  have pts' := pts.wp (F₁ := Keep c s₀ (ptr s₀ 3)) (F₂ := Keep c t₀ (ptr t₀ 3))
    (fun _ _ h => ⟨vPoints_keep hc hC hT hcd hCo ham3 ht₁ h.2.1 hspG H.points,
      vPoints_keep hc hC hT hcd hCo ham3 ht₂ h.2.2 hspG H.points⟩)
  exact front'.seq (mid'.seq (pts'.seq (ct.final.mono
    (fun _ _ h => vKeepScratchAgree hp hq h.2.1 h.2.2 he ha) (fun _ _ _ => trivial))))

/-! ## Verification with the comb for `[u]G` and the ladder for `[v]Q` -/

/-- A curve whose comb is by complete additions multiplies `Q` by the ladder. -/
theorem pointsComb_ladder (hcd : c.comb = some d) (hj : d.jac = false) :
    Impl.Ecdsa.Verify.X86.Cfg.pointsComb c = Impl.Ecdsa.Verify.X86.Cfg.pointsCombLadder c := by
  unfold Impl.Ecdsa.Verify.X86.Cfg.pointsComb
  rw [ite_eq_right (by simp [Cfg.combJac, hcd, hj])]

/-- Verification with the comb and the ladder: the specification's result, the cdecl ABI kept. -/
theorem verifyComb_ok (hc : CfgOk c) (hC : Law c.C) (hT : CombTbls c) (hcd : c.comb = some d)
    (hd : CombOk c d) (hj : d.jac = false) (hspG : SpOk c.gMul 20)
    (hsp : SpOk (Impl.Ecdsa.Verify.X86.Cfg.verifyCombBody c) c.stk) {s₀ : State} (hp : VCombPre c s₀) :
    WP isa (Impl.Ecdsa.Verify.X86.Cfg.verifyComb c) s₀ fun s' => abiPreserved s₀ s' ∧ VPost c s₀ s' := by
  have hCo : ∀ d', c.comb = some d' → CombOk c d' := by
    intro d' h; have e : d = d' := Option.some.inj (hcd.symm.trans h); rw [← e]; exact hd
  unfold Impl.Ecdsa.Verify.X86.Cfg.verifyComb
  rw [tableAddr_eq hcd]
  refine WP.seq (WP.mono (symFrame_ok d.tsym s₀ hp.sp4) fun s₁ P => ?_)
  have hp₁ := hp.toVPre.symAddr P hp.sp4
  have ht := vPrefixTables hcd hp P
  refine WP.mono (verifyCombBody_ok hc hC hT hCo
    (fun h => absurd h.2 (by simp [Cfg.combJac, hcd, hj])) hp₁
    (fun d' hd' => by have e : d = d' := Option.some.inj (hcd.symm.trans hd'); subst d'; exact ht)
    hspG hsp) fun s₂ ⟨K, post⟩ => ?_
  have ha := K.abi hp₁
  have he := P.gpr .esp (by decide)
  refine ⟨⟨fun r hr => (ha.1 r hr).trans (P.gpr r (by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)), ?_⟩, ?_⟩
  · have ht := ha.2
    rw [he] at ht
    exact ht.trans (P.ret hp.sp4 (by have := hp.sp_fit; omega_using [this]))
  · have harg : ∀ j < 4, arg s₁ j = arg s₀ j := fun j hj => P.arg hp.sp4 (by have := hp.sp_fit; omega_using [hj, this])
    have hpk := prefix_bytesAt P hp.pk_stack (by have := hp.pk_fit; change 1 + 2 * c.C.len ≤ 2 ^ 64; omega_using [this])
    have hdg := prefix_bytesAt P hp.dg_stack (by have := hp.dg_fit; change c.C.len ≤ 2 ^ 64; omega_using [this])
    have hsig := prefix_bytesAt P hp.sig_stack (by have := hp.sig_fit; change 2 * c.C.len ≤ 2 ^ 64; omega_using [this])
    simpa only [VPost, ptr, harg 0 (by decide), harg 1 (by decide), harg 2 (by decide), hpk, hdg, hsig] using post

/-- What may affect the timing of verification with the comb and the ladder: the pointers, the
stack and the tables' address (the contract would let the key, the hash and the signature
affect it too). -/
def VCombPubL (d : CombData) (s t : State) : Prop :=
  s.gpr .esp = t.gpr .esp ∧ (∀ j < 4, arg s j = arg t j) ∧ s.syms d.tsym = t.syms d.tsym

theorem verifyComb_ct (hc : CfgOk c) (hC : Law c.C) (hT : CombTbls c) (hcd : c.comb = some d)
    (hd : CombOk c d) (hj : d.jac = false) (hG : GMulRel c d false) (ct : VerifyStagesCT c)
    (cl : VerifyLadderCT c) (hspG : SpOk c.gMul 20)
    (hsp : SpOk (Impl.Ecdsa.Verify.X86.Cfg.verifyCombBody c) c.stk) :
    ConstantTime isa (VCombPre c) (VCombPubL d) (Impl.Ecdsa.Verify.X86.Cfg.verifyComb c) := by
  apply RelCT.constantTime (Q := fun _ _ => True)
  unfold Impl.Ecdsa.Verify.X86.Cfg.verifyComb
  have preCT : RelCT isa (fun s t => VCombPre c s ∧ VCombPre c t ∧ VCombPubL d s t)
      c.tableAddr (fun _ _ => True) := by
    rw [tableAddr_eq hcd]
    intro s t tr₁ tr₂ s' t' h e₁ e₂
    exact ⟨by rw [symFrame_trace h.1.sp4 e₁, symFrame_trace h.2.1.sp4 e₂, h.2.2.1], trivial⟩
  have pre := preCT.wpDep (F := fun s t => SymAddrPost d.tsym s t) (by
    intro s t h
    rw [tableAddr_eq hcd]
    exact ⟨symFrame_ok d.tsym s h.1.sp4, symFrame_ok d.tsym t h.2.1.sp4⟩)
  refine pre.seq ?_
  intro s t tr₁ tr₂ s' t' h e₁ e₂
  obtain ⟨_, a, b, ⟨hp, hq, he, ha, hg⟩, P, Q⟩ := h
  have he' : s.gpr .esp = t.gpr .esp := by rw [P.gpr .esp (by decide), Q.gpr .esp (by decide), he]
  have ha' : ∀ j < 4, arg s j = arg t j := by
    intro j hj
    rw [P.arg hp.sp4 (by have := hp.sp_fit; omega_using [hj, this]), Q.arg hq.sp4 (by have := hq.sp_fit; omega_using [hj, this]), ha j hj]
  have hg' : s.gpr .eax = t.gpr .eax := by rw [P.addr, Q.addr, hg]
  have hp₁ := hp.toVPre.symAddr P hp.sp4
  have hq₁ := hq.toVPre.symAddr Q hq.sp4
  have ht₁ := vPrefixTables hcd hp P
  have ht₂ := vPrefixTables hcd hq Q
  exact vCombBody_rel hc hC hT hcd hd (fun h => absurd h.2 (by simp [Cfg.combJac, hcd, hj])) ct
    hp₁ hq₁ ht₁ ht₂ he' ha'
    (by rw [pointsComb_ladder hcd hj]
        exact vPointsLadder_rel hc hC hT hcd hd hG cl hp₁ hq₁ ht₁ ht₂ he' ha' hg' hspG)
    hspG hsp _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂

end VG.Proof.Ecdsa.Verify.X86
