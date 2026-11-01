module

public import VerifiedGarbage.Proof.Ecdsa.X86.MulFn
public import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
import VerifiedGarbage.Proof.Weierstrass.X86.LadderPCall
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ecdsa.X86.Stages

/-!
# `[k]P` on x86 (32-bit): the call of `vg_<curve>_mul`, or the ladder inline

`qMul_ok`: `R = [k]P` for the point at `gx`, `gy`, `ONEP` (`Cfg.qMul`), by a
call of `vg_<curve>_mul` if the curve has it (`Cfg.mul`), from `k` at `K`'s
slot, else by the signature's ladder inline (`ladderP`), from the table of
`k`'s bits. For any invariant `Q` of the ladder from that point that accepts
both `R` and `O` (as zero and one hold it), `Q 0` accepts what `R` holds at
the end; only `powClob`, what `ladderP` writes and `genX` change, and the
caller's argument holding the working space (`Point.LadArg`), which the call
reloads `edi` from as `ladderP`'s calls do, is kept. As on PPC64LE
(`Proof/Ecdsa/PPC64LE/MulFn.lean`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

variable {c : Cfg}

/-- What `qMul` writes besides `ladderP`: `ACC`, `PT` (`vg_<curve>_mul`'s
copy of `Q`), the table of `k`'s bits and where it keeps the callee-saved
registers. -/
abbrev genX (c : Cfg) : List (Nat × Nat) :=
  slW c [ACC, PT] ++ [(bitsAt c.n 0, 64 * c.n), (c.sl nslots, 16)]

theorem apart_genX (h7 : c.n < 10) {i : Nat} (hi : i < 45) (hr : i ∉ [ACC, PT]) :
    ∀ w ∈ genX c, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  refine apart_append (apart_slW hr) ?_
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact Or.inl (by have := sl_below_bits c hi 0 0; omega_arith)
  · exact Or.inl (sl_lt c hi)

theorem fixedOk_genX (h7 : c.n < 10) : FixedOk c (genX c) := by
  refine (fixedOk_slW (l := [ACC, PT]) (by decide)).append ?_
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact Or.inr (Nat.le_trans (Nat.le_add_right _ _) (sl_below_bits c (i := 12) (by decide) 0 0))
  · exact Or.inr (Nat.le_of_lt_succ (Nat.lt_succ_of_le (Nat.le_trans (Nat.le_add_right _ _)
      (sl_lt c (i := 12) (j := nslots) (by decide)))))

theorem genX_le (h7 : c.n < 10) : ∀ w ∈ genX c, w.1 + w.2 ≤ size := by
  have := sl_le c h7 (i := ACC) (by decide)
  have := sl_le c h7 (i := PT) (by decide)
  have := bitsAt_le c h7 (j := 0) (by decide)
  have := save_le_wk (c := c) h7
  have := wk_own c
  have hsz : size = 8192 := rfl
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false, List.mem_append, slW, List.map_cons, List.map_nil] at hw
  rcases hw with (rfl | rfl) | rfl | rfl <;> (dsimp only; omega_arith)

theorem tbl_apart_genX (h7 : c.n < 10) {j t : Nat} (hj : j ≠ 0) (ht : t < 64 * c.n) :
    ∀ w ∈ genX c, bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t := by
  have := sl_below_bits c (i := ACC) (by decide) j t
  have := sl_below_bits c (i := PT) (by decide) j t
  have := save_le_wk (c := c) h7
  have := wk_below_bits c j
  have := bitsAt_eq c j
  have := bitsAt_eq c 0
  have hj1 : 1 ≤ j := Nat.pos_of_ne_zero hj
  have : (64 * c.n + 4) * 1 ≤ (64 * c.n + 4) * j := Nat.mul_le_mul_left _ hj1
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false, List.mem_append, slW, List.map_cons, List.map_nil] at hw
  rcases hw with (rfl | rfl) | rfl | rfl <;> (dsimp only; omega_arith)

theorem flag_apart_genX (h0 : 0 < c.n) (h7 : c.n < 10) : ∀ w ∈ genX c, c.sl FLAG + 4 ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG := by
  intro w hw
  rcases apart_genX h7 (i := FLAG) (by decide) (by decide) w hw with h | h
  · exact .inl (by omega_arith)
  · exact .inr h

/-- Memory that changed only in the 8 bytes below `esp` (a push and a return
address) keeps the working space. -/
theorem unch_of_frame8 {s : State} {base : Addr} (hs : Scr s base 8192) {m m' : Mem}
    (hF : Frame [below (s.gpr .esp) 8] m m') (h28 : 28 ≤ (s.gpr .esp).toNat)
    (hz : (s.gpr .esp).toNat ≤ base.toNat ∨ base.toNat + 8192 + 28 ≤ (s.gpr .esp).toNat) :
    Unch base [Mont.outW] m m' := fun x hx => hF x fun r hr hc => by
  rw [List.mem_singleton.mp hr] at hc
  have := Point.zone8 hs h28 hz hc
  have := hx _ (List.mem_singleton_self _)
  simp only at this
  have := (x - base).isLt
  simp only [ofs] at *
  omega_arith

theorem mulFW_sub (c : Cfg) (gx gy : Nat) :
    ∀ w ∈ mulFW c, w ∈ Point.ladWp (ladAt c gx gy) c.wk ++ genX c := by
  intro w hw
  simp only [mulFW, mulBW, mulBX, List.mem_append, List.mem_singleton] at hw
  simp only [Point.ladWp, List.mem_append, genX, List.mem_cons, List.not_mem_nil, or_false]
  rcases hw with (hw | hw | hw) | hw
  · exact .inl (.inl hw)
  · exact .inr (.inl hw)
  · exact .inr (.inr (.inl hw))
  · exact .inr (.inr (.inr hw))

/-- `vg_<curve>_mul` as the call sees it: from a state whose working space
is the argument, writable and the only writable region, with the numbers of
`s₀`'s working space, it changes only `mulFW`, with `Q 0` accepting what `R`
holds. -/
def mulK (c : Cfg) (base : Addr) (s₀ : State) (Q : Nat → Fe c.C → Fe c.C → Fe c.C → Prop) : Contract isa where
  pre u := Point.ArgP u base ∧ u.wr = [⟨base, 8192⟩] ∧
    Region.Disjoint ⟨(u.gpr .esp).setWidth 64, 4⟩ ⟨base, 8192⟩ ∧ Unch base [Mont.outW] s₀.mem u.mem
  post u u' := Unch base (mulFW c) u.mem u'.mem ∧
    (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal u'.mem base x c.n < c.C.p) ∧
    Q 0 (tmv c.C c.n base u' (c.sl RX)) (tmv c.C c.n base u' (c.sl RY)) (tmv c.C c.n base u' (c.sl RZ))
  pub _ _ := True

theorem mulK_ok (hc : CfgOk c) (hsp : SpOk c.mulFn 20) {s₀ : State} {base : Addr}
    (hmp : sv c base s₀ MP = c.C.p)
    (hap : sv c base s₀ AP < c.C.p) (hb3 : sv c base s₀ B3P < c.C.p) (hone : sv c base s₀ ONEP < c.C.p)
    (hzero : sv c base s₀ ZERO < c.C.p) (hqx : sv c base s₀ RX < c.C.p) (hqy : sv c base s₀ RY < c.C.p)
    {Q : Nat → Fe c.C → Fe c.C → Fe c.C → Prop}
    (hstep : Step (ladAt c RX RY) c.C base s₀ (sv c base s₀ K) Q)
    (hO : Q c.ladderCfg.nbits (tmv c.C c.n base s₀ (c.sl ZERO)) (tmv c.C c.n base s₀ (c.sl ONEP))
      (tmv c.C c.n base s₀ (c.sl ZERO))) (u : State) (hu : (mulK c base s₀ Q).pre u) :
    ∃ tr u', Exec isa c.mulFn u tr u' ∧ abiPreserved u u' ∧ (mulK c base s₀ Q).post u u' := by
  obtain ⟨hpu, hwu, hru, Uu⟩ := hu
  have h7 := hc.n10
  have hsz : size = 8192 := rfl
  have sv_u : ∀ {i}, i < 45 → sv c base u i = sv c base s₀ i := fun hi =>
    Uu.wordsVal (fun w hw => by
      rw [List.mem_singleton.mp hw]; exact .inl (by have := sl_le c h7 hi; simp only; omega_arith))
      (by have := sl_le c h7 hi; omega_arith)
  have tv : ∀ {i}, i < 45 → tmv c.C c.n base u (c.sl i) = tmv c.C c.n base s₀ (c.sl i) := fun hi => by
    show toM _ _ (sv c base u _) = toM _ _ (sv c base s₀ _); rw [sv_u hi]
  have hstepu : Step (ladAt c RX RY) c.C base u (sv c base u K) Q := by
    rw [sv_u (by decide)]
    exact step_congr rfl (tv (by decide)) (tv (by decide)) (tv (by decide)) (tv (by decide)) (tv (by decide)) hstep
  have hOu : Q c.ladderCfg.nbits (tmv c.C c.n base u (c.sl ZERO)) (tmv c.C c.n base u (c.sl ONEP))
      (tmv c.C c.n base u (c.sl ZERO)) := by
    rw [tv (by decide), tv (by decide)]; exact hO
  have h20 := hpu.stk.1
  obtain ⟨tr, u', he, ⟨G, -, -, U, L, R⟩, F⟩ := WP.spFrame hsp h20 (mulFn_ok hc hpu
    (by rw [sv_u (by decide)]; exact hmp) (by rw [sv_u (by decide)]; exact hap)
    (by rw [sv_u (by decide)]; exact hb3) (by rw [sv_u (by decide)]; exact hone)
    (by rw [sv_u (by decide)]; exact hzero) (by rw [sv_u (by decide)]; exact hqx)
    (by rw [sv_u (by decide)]; exact hqy) hstepu hOu)
  refine ⟨tr, u', he, ⟨G, ?_⟩, U, L, R⟩
  refine F.readW (r := ⟨(u.gpr .esp).setWidth 64, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rw [hwu] at hr
  simp only [List.mem_append, List.mem_singleton] at hr
  rcases hr with rfl | rfl
  · exact hru
  · exact (below_disjoint_ret h20).symm

/-- The call of `vg_<curve>_mul` on `Q` at `R`'s first two slots, from the
working space at `edi`, which is then loaded again from the caller's
argument at `[esp + ao]`. -/
theorem mulCall_ok (hc : CfgOk c) (hsp : SpOk c.mulFn 20) {C : Impl.Weierstrass.Mul.Curve} {ao : Nat}
    {s : State} {base : Addr} (hs : Scr s base size) (hA : Point.LadArg s base ao)
    (hmp : sv c base s MP = c.C.p)
    (hap : sv c base s AP < c.C.p) (hb3 : sv c base s B3P < c.C.p) (hone : sv c base s ONEP < c.C.p)
    (hzero : sv c base s ZERO < c.C.p) (hqx : sv c base s RX < c.C.p) (hqy : sv c base s RY < c.C.p)
    {Q : Nat → Fe c.C → Fe c.C → Fe c.C → Prop}
    (hstep : Step (ladAt c RX RY) c.C base s (sv c base s K) Q)
    (hO : Q c.ladderCfg.nbits (tmv c.C c.n base s (c.sl ZERO)) (tmv c.C c.n base s (c.sl ONEP))
      (tmv c.C c.n base s (c.sl ZERO))) :
    WP isa (.seq (.frame (.push [.edi]) (.call s!"vg_{C.curve}_mul" c.mulFn) (.pop .eax 1))
      (.block [.mov .edi (.mem (at_ .esp ao))])) s fun s' => Keeps powClob s s' ∧
      Unch base (Mont.outW :: mulFW c) s.mem s'.mem ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem base x c.n < c.C.p) ∧
      Q 0 (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY)) (tmv c.C c.n base s' (c.sl RZ)) ∧
      Point.LadArg s' base ao := by
  have hn := hs.nowrap
  have h28 := hA.s28
  have hz := hA.sz
  have hspN := (s.gpr .esp).isLt
  have hedi := hs.edi_toNat
  have hst : stackUse c.mulFn ≤ 20 := hsp.2
  have hfit : 4 * [Reg.edi].length + 4 ≤ (s.gpr .esp).toNat := by
    simp only [List.length_cons, List.length_nil]; omega_arith
  -- The callee's view.
  let t := ((pushed [Reg.edi] s).callEntry).withRegions [below (s.gpr .esp) 4] [⟨base, 8192⟩]
  have a0 : arg t 0 = s.gpr .edi := callEntry_arg hfit (by decide) (by decide)
  have hws : (arg t 0).setWidth 64 = base := by rw [a0]; exact hs.edi
  have espT : (t.gpr .esp).toNat = (s.gpr .esp).toNat - 8 := by
    show ((pushed _ s).callEntry.gpr .esp).toNat = _
    rw [callEntry_espNat hfit]; rfl
  have argA : argAddr t 0 = (s.gpr .esp - BitVec.ofNat 32 4).setWidth 64 := callEntry_argAddr0 _ _
  have argN : (argAddr t 0).toNat = (s.gpr .esp).toNat - 4 := by
    rw [argA, BitVec.toNat_setWidth, sub_toNat (by omega_arith)]
    exact Nat.mod_eq_of_lt (by omega_arith)
  have retN : ((t.gpr .esp).setWidth 64).toNat = (s.gpr .esp).toNat - 8 := by
    rw [BitVec.toNat_setWidth, espT]; exact Nat.mod_eq_of_lt (by omega_arith)
  have fr : Frame [below (s.gpr .esp) 8] s.mem t.mem := callEntry_frame hfit (rs := [Reg.edi]) (by decide)
  have Ut : Unch base [Mont.outW] s.mem t.mem := unch_of_frame8 hs fr h28 hz
  have hargT : Point.ArgP t base :=
    ⟨hws, by show _ ∈ [below (s.gpr .esp) 4]; rw [argA]; exact List.mem_singleton_self _,
      List.mem_singleton_self _, hn, ⟨by rw [espT]; omega_arith, by rw [espT]; omega_arith⟩,
      by rw [espT]; omega_arith,
      Region.disjoint_of_le (by simp only; rw [argN]; omega_arith) (by simp only; rw [argN]; omega_arith)
        (by simp only; omega_arith)⟩
  have hretT : Region.Disjoint ⟨(t.gpr .esp).setWidth 64, 4⟩ ⟨base, 8192⟩ :=
    Region.disjoint_of_le (by simp only; rw [retN]; omega_arith) (by simp only; rw [retN]; omega_arith)
      (by simp only; omega_arith)
  have hpre : CallPre (mulK c base s Q) [.edi] [below (s.gpr .esp) 4] [⟨base, 8192⟩] s := by
    refine ⟨⟨hargT, rfl, hretT, Ut⟩, ?_, ?_⟩
    · refine Covers.append_left (Covers.of_mem fun r hr => ?_) (Covers.of_mem fun r hr => ?_)
      · rw [List.mem_singleton.mp hr]; simp
      · rw [List.mem_singleton.mp hr]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hs.wr)
    · exact Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_of_mem _ hs.wr
  refine WP.seq (WP.callWith (k := mulK c base s Q) (mulK_ok hc hsp hmp hap hb3 hone hzero hqx hqy hstep hO)
    hsp.1 (by decide) (by decide) (by simp only [List.length_cons, List.length_nil]; omega_arith) hpre ?_)
  intro s' rd' wr' cs' F' ⟨s₃, m₃, U₃, L₃, R₃⟩
  have F₂ : Frame [⟨base, 8192⟩, below (s.gpr .esp) 28] s.mem s'.mem := by
    have := Frame.below_mono F' (b := 28) (by simp only [List.length_cons, List.length_nil]; omega_arith) h28
    exact this.mono fun r hr => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      exact hr
  have esp' : s'.gpr .esp = s.gpr .esp := cs' .esp (by decide)
  refine wp_ldm (b := .esp) esp' (by rw [rd', wr']; exact hA.rd) fun s₄ u₄ => WP.block_nil ?_
  have hv' : s'.mem.readW (addr (s.gpr .esp) ao) 32 = s.gpr .edi := by
    rw [F₂.readW (r := ⟨addr (s.gpr .esp) ao, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hA.aw
      · exact hA.as) (by decide), hA.val]
  have m₄ : s₄.mem = s₃.mem := by rw [u₄.mem, m₃]
  have edi₄ : s₄.gpr .edi = s.gpr .edi := by rw [u₄.gpr, hv']
  refine ⟨⟨fun r hr => ?_, by rw [u₄.rd, rd'], by rw [u₄.wr, wr']⟩, ?_, by rw [m₄]; exact L₃, ?_, ?_⟩
  · by_cases h : r = .edi
    · subst h; exact edi₄
    · rw [u₄.other _ h]
      exact cs' r (by revert hr h; cases r <;> decide)
  · rw [m₄]; exact Ut.trans U₃
  · show Q 0 (toM _ _ (wordsVal s₄.mem _ _ _)) (toM _ _ (wordsVal s₄.mem _ _ _)) (toM _ _ (wordsVal s₄.mem _ _ _))
    rw [m₄]; exact R₃
  · exact hA.keep (by rw [u₄.other _ (by decide), esp']) edi₄ (by rw [u₄.rd, rd']) (by rw [u₄.wr, wr'])
      (by rw [m₄, m₃]; exact F₂)

/-- The call's stack: what `vg_<curve>_mul`'s own calls use, below the push
and the return address. -/
theorem mulFn_spOk {gx gy ao : Nat} {C : Impl.Weierstrass.Mul.Curve} (hC : c.mul = some C)
    (h : SpOk (c.qMul gx gy ao) 28) : SpOk c.mulFn 20 := by
  unfold Cfg.qMul at h
  simp only [hC] at h
  refine ⟨fun i hi => h.1 i ?_, ?_⟩
  · simp only [Cfg.mulAt, instrs, List.mem_append, List.mem_cons]
    simp [hi]
  · have := h.2
    simp only [Cfg.mulAt, stackUse, frameBytes, List.length_cons, List.length_nil, Nat.max_le] at this
    omega

/-- `R = [k]P` for the point at `gx`, `gy`, `ONEP`: the call of
`vg_<curve>_mul` if the curve has it, from `k` at `K`'s slot, else the ladder
inline, from the table of `k`'s bits. -/
theorem qMul_ok (hc : CfgOk c) {gx gy ao : Nat} (hgx : gx < 45) (hgy : gy < 45) (hg1 : gx ≠ RX)
    (hg2 : gy ≠ RX) (hg3 : gy ≠ RY)
    (hL : LadLay (ladAt c gx gy) size) (hW : LadWk (ladAt c gx gy) c.SP c.C.p size c.wk)
    (hP : 3 ≤ c.n ∧ c.n ≤ 6 → Point.LadPt (ladAt c gx gy))
    (hsp : SpOk (c.qMul gx gy ao) 28)
    {s : State} {base : Addr} (hs : Scr s base size)
    (hA : c.mul.isSome ∨ 3 ≤ c.n ∧ c.n ≤ 6 → Point.LadArg s base ao)
    (hmp : sv c base s MP = c.C.p)
    (hap : sv c base s AP < c.C.p) (hb3 : sv c base s B3P < c.C.p) (hone : sv c base s ONEP < c.C.p)
    (hzero : sv c base s ZERO < c.C.p) (hqx : sv c base s gx < c.C.p) (hqy : sv c base s gy < c.C.p)
    (hrx : sv c base s RX < c.C.p) (hry : sv c base s RY < c.C.p) (hrz : sv c base s RZ < c.C.p)
    {k : Nat} {Q : Nat → Fe c.C → Fe c.C → Fe c.C → Prop}
    (hstep : Step (ladAt c gx gy) c.C base s k Q c.qA0)
    (hR : Q (64 * c.n) (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY))
      (tmv c.C c.n base s (c.sl RZ)))
    (hO : Q (64 * c.n) (tmv c.C c.n base s (c.sl ZERO)) (tmv c.C c.n base s (c.sl ONEP))
      (tmv c.C c.n base s (c.sl ZERO)))
    (hk : c.mul.isSome → sv c base s K = k)
    (ht : c.mul = none → ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 0 + t)) = if k.testBit t then 1 else 0) :
    WP isa (c.qMul gx gy ao) s fun s' => Keeps powClob s s' ∧
      Unch base (Point.ladWp (ladAt c gx gy) c.wk ++ genX c) s.mem s'.mem ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem base x c.n < c.C.p) ∧
      Q 0 (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY)) (tmv c.C c.n base s' (c.sl RZ)) ∧
      (c.mul.isSome ∨ 3 ≤ c.n ∧ c.n ≤ 6 → Point.LadArg s' base ao) := by
  have h7 := hc.n10
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  unfold Cfg.qMul
  split
  · -- The call: `Q` copied to `R`'s first two slots.
    next C hC =>
    have hsome : c.mul.isSome := by rw [hC]; rfl
    rw [Cfg.mulAt]
    refine WP.seq ?_
    refine WP.block_append (WP.mono (copySl_ok hc hs (o := RX) (a := gx) (by decide) hgx (Ne.symm hg1))
      fun s₁ ⟨x₁, k₁, O₁⟩ => ?_)
    have hs₁ := hs.of_keeps k₁ (by decide)
    refine WP.mono (copySl_ok hc hs₁ (o := RY) (a := gy) (by decide) hgy (Ne.symm hg3))
      fun s₂ ⟨x₂, k₂, O₂⟩ => ?_
    have hs₂ := hs₁.of_keeps k₂ (by decide)
    have K₂ : Keeps [.eax] s s₂ := k₁.trans k₂
    have o : ∀ {s s' : State} {j i : Nat}, Outside base (c.sl j) (8 * c.n) s.mem s'.mem → i < 45 → i ≠ j →
        sv c base s' i = sv c base s i := fun O hi hij => sv_outside h7 O hi hij
    have e₂ : ∀ {i}, i < 45 → i ≠ RX → i ≠ RY → sv c base s₂ i = sv c base s i := fun hi h1 h2 =>
      (o O₂ hi h2).trans (o O₁ hi h1)
    have rx₂ : sv c base s₂ RX = sv c base s gx := (o O₂ (by decide) (by decide)).trans x₁
    have ry₂ : sv c base s₂ RY = sv c base s gy := x₂.trans (o O₁ hgy hg2)
    have U₂ : Unch base (slW c [RX, RY]) s.mem s₂.mem := by
      have := O₁.unch.trans O₂.unch
      exact this.mono fun w hw => by simpa using hw
    have hA₂ : Point.LadArg s₂ base ao := (hA (.inl hsome)).keep (K₂.1 _ (by decide)) (K₂.1 _ (by decide))
      K₂.2.1 K₂.2.2 (frame_of_unch U₂ (slW_le h7 (by decide)) (List.mem_cons_self ..))
    have tv : ∀ {i j}, sv c base s₂ i = sv c base s j →
        tmv c.C c.n base s₂ (c.sl i) = tmv c.C c.n base s (c.sl j) := fun h => by
      show toM _ _ (sv c base s₂ _) = toM _ _ (sv c base s _); rw [h]
    have hq : c.qA0 = false := by simp only [Cfg.qA0, hC, Option.isNone_some, Bool.false_and]
    rw [hq] at hstep
    have hstep₂ : Step (ladAt c RX RY) c.C base s₂ (sv c base s₂ K) Q := by
      rw [e₂ (by decide) (by decide) (by decide), hk hsome]
      exact step_congr (L := ladAt c gx gy) (L' := ladAt c RX RY) rfl (tv (e₂ (by decide) (by decide) (by decide)))
        (tv (e₂ (by decide) (by decide) (by decide))) (tv rx₂) (tv ry₂)
        (tv (e₂ (by decide) (by decide) (by decide))) hstep
    have hO₂ : Q c.ladderCfg.nbits (tmv c.C c.n base s₂ (c.sl ZERO)) (tmv c.C c.n base s₂ (c.sl ONEP))
        (tmv c.C c.n base s₂ (c.sl ZERO)) := by
      rw [tv (e₂ (i := ZERO) (by decide) (by decide) (by decide)),
        tv (e₂ (i := ONEP) (by decide) (by decide) (by decide))]
      exact hO
    refine WP.mono (mulCall_ok hc (mulFn_spOk hC hsp) (C := C) hs₂ hA₂
      (by rw [e₂ (by decide) (by decide) (by decide)]; exact hmp)
      (by rw [e₂ (by decide) (by decide) (by decide)]; exact hap)
      (by rw [e₂ (by decide) (by decide) (by decide)]; exact hb3)
      (by rw [e₂ (by decide) (by decide) (by decide)]; exact hone)
      (by rw [e₂ (by decide) (by decide) (by decide)]; exact hzero)
      (by rw [rx₂]; exact hqx) (by rw [ry₂]; exact hqy) hstep₂ hO₂) fun s' ⟨K', U', L', R', A'⟩ =>
      ⟨(K₂.mono (by decide)).trans K', ?_, L', R', fun _ => A'⟩
    refine (U₂.trans U').mono fun w hw => ?_
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      refine List.mem_append_left _ (List.mem_append_left _ ?_)
      rw [ladWx_at]
      refine List.mem_append_left _ (List.mem_map.mpr ⟨i, ?_, rfl⟩)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
      rcases hi with rfl | rfl <;> simp
    rcases List.mem_cons.mp hw with hw | hw
    · rw [hw]
      refine List.mem_append_left _ (List.mem_append_left _ ?_)
      rw [ladWx_at]; simp [wkW]
    · exact mulFW_sub c gx gy w hw
  · -- The ladder inline.
    next hN =>
    have hlt : ∀ x ∈ ladR (ladAt c gx gy), wordsVal s.mem base x (ladAt c gx gy).M.n < c.C.p := by
      intro x hx
      have hx' : x ∈ [AP, B3P, gx, gy, ONEP, RX, RY, RZ].map c.sl := hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      show sv c base s i < c.C.p
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hap
      · exact hb3
      · exact hqx
      · exact hqy
      · exact hone
      · exact hrx
      · exact hry
      · exact hrz
    have hnone : c.mul = none := hN
    refine WP.mono (Point.ladderP_ok (L := ladAt c gx gy) (k := k) hL hW hP hpR hs
      (fun h => hA (.inr h)) (modP_of hc hmp) hlt (fun h => by
        simp only [Cfg.qA0, Bool.and_eq_true, decide_eq_true_eq] at h
        exact h.2.2) hstep hR (ht hnone)) fun s' ⟨K, U, _, L, R, A⟩ =>
      ⟨K, U.mono fun w hw => List.mem_append_left _ hw, L, R, fun h => A (h.resolve_left (by rw [hnone]; decide))⟩

end VG.Proof.Ecdsa.X86
