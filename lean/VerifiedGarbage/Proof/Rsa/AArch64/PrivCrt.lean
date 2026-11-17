module

public import VerifiedGarbage.Proof.Rsa.AArch64.PrivImpl
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Rsa.AArch64.PrivFrame
public import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! ### `Rsa.AArch64.PrivCall`, which this module and modules that import it used -/

section

/-!
# `vg_rsa_private_checked` on AArch64: calls from the frames

`call_ok` runs a call of verified code without frames from a state in which
`Ctx` and `Slots` hold, given regions within ours to read and, to write,
regions within `out`, `scratch` or the inner frame above the slots: they
hold again afterwards.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Rsa.AArch64.PrivChecked

/-- `r` lies at an offset within `R`. -/
def Within (r R : Region) : Prop := ∃ off, r.base = R.base + BitVec.ofNat 64 off ∧ off + r.len ≤ R.len

theorem Within.sub {r R : Region} (h : Within r R) : Region.Sub r R := by
  obtain ⟨off, hb, hl⟩ := h
  obtain ⟨b, n⟩ := r
  simp only at hb hl
  subst hb
  exact Offset.sub_base _ hl

theorem within_off (p : Addr) {d n k : Nat} (h : d + n ≤ k) :
    Within ⟨p + BitVec.ofNat 64 d, n⟩ ⟨p, k⟩ := ⟨d, rfl, h⟩

theorem within_base (p : Addr) {n k : Nat} (h : n ≤ k) : Within ⟨p, n⟩ ⟨p, k⟩ :=
  ⟨0, (BitVec.add_zero p).symm, by simpa using h⟩

/-- The regions a callee may be given. -/
abbrev Lay.regions (L : Lay) : List Region :=
  [L.N, L.E, L.IN, L.P, L.Q, L.DP, L.DQ, L.QI, L.ARGS, L.FR, L.OUT, L.SC]

/-- The inner frame above the slots: `M` and `n`'s values. -/
abbrev Lay.HI (L : Lay) : Region := ⟨L.B + BitVec.ofNat 64 oM, frameBytes - oM⟩

/-- A region a callee may write. -/
def InW (L : Lay) (r : Region) : Prop := Within r L.OUT ∨ Within r L.SC ∨ Within r L.HI

theorem InW.sub {L : Lay} (hL : L.Ok) {r : Region} (h : InW L r) :
    ∃ R ∈ [L.OUT, L.SC, L.STK], Region.Sub r R := by
  have hnB := hL.nB
  rcases h with h | h | h
  · exact ⟨_, by simp, h.sub⟩
  · exact ⟨_, by simp, h.sub⟩
  · refine ⟨L.STK, by simp, fun a ha => ?_⟩
    exact Offset.sub_base L.B (d := oM) (n := frameBytes - oM) (k := stackBytes) (by decide) a (h.sub a ha)

/-- A region a callee may write misses the slots and our return address. -/
theorem InW.disj {L : Lay} (hL : L.Ok) {r : Region} (h : InW L r) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 oOut, 48⟩ r ∧ Region.Disjoint L.LR r := by
  have hnB := hL.nB
  rcases h with h | h | h
  · have hs : Region.Sub ⟨L.B + BitVec.ofNat 64 oOut, 48⟩ L.STK :=
      Offset.sub_base _ (by decide)
    have hs' : Region.Sub L.LR L.STK := Offset.sub_base _ (by decide)
    exact ⟨(hL.ko.sub_left hs).sub_right h.sub, (hL.ko.sub_left hs').sub_right h.sub⟩
  · have hs : Region.Sub ⟨L.B + BitVec.ofNat 64 oOut, 48⟩ L.STK :=
      Offset.sub_base _ (by decide)
    have hs' : Region.Sub L.LR L.STK := Offset.sub_base _ (by decide)
    exact ⟨(hL.ksc.sub_left hs).sub_right h.sub, (hL.ksc.sub_left hs').sub_right h.sub⟩
  · exact ⟨(Offset.disjoint L.B (d := oOut) (n := 48) (e := oM) (k := frameBytes - oM) (by decide)
        (by simp only [oOut]; omega_using []) (by simp only [oM, frameBytes]; omega_using [])).sub_right h.sub,
      (Offset.disjoint L.B (d := frameBytes) (n := 16) (e := oM) (k := frameBytes - oM) (by decide)
        (by simp only [frameBytes]; omega_using []) (by simp only [oM, frameBytes]; omega_using [])).sub_right h.sub⟩

theorem covers {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (hc : Ctx L g vv m₀ t) {rd wr : List Region}
    (hsub : ∀ r ∈ rd ++ wr, ∃ R ∈ L.regions, Within r R) (hwsub : ∀ r ∈ wr, InW L r) :
    Covers (rd ++ wr) (t.rd ++ t.wr) ∧ Covers wr t.wr := by
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · obtain ⟨R, hR, hw⟩ := hsub r hr
    refine ⟨R, ?_, hw⟩
    rw [hc.rd, hc.wr]
    simp only [Lay.regions, List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · rw [hc.wr]
    rcases hwsub r hr with h | h | h
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · obtain ⟨off, hb, hl⟩ := h
      refine ⟨L.FR, by simp, oM + off, ?_, ?_⟩
      · rw [hb, add_add]
      · simp only [oM, frameBytes] at hl ⊢; omega_using [hl]

/-- A call of verified code without frames, given regions within ours to
read, and within `out`, `scratch` or the inner frame above the slots to
write: afterwards `Ctx` and `Slots` hold again, memory changed only within
what it writes, and the callee's postcondition holds. -/
theorem call_ok {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}
    {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hn : c.noFrames = true) {t : State} (hc : Ctx L g vv m₀ t) (hs : Slots L t.mem)
    {rd wr : List Region} (hpre : k.pre (t.callEntry.withRegions rd wr))
    (hsub : ∀ r ∈ rd ++ wr, ∃ R ∈ L.regions, Within r R) (hwsub : ∀ r ∈ wr, InW L r)
    {Q : State → Prop}
    (hQ : ∀ s', Ctx L g vv m₀ s' → Slots L s'.mem → Frame wr t.mem s'.mem →
      k.post (t.callEntry.withRegions rd wr) (s'.withRegions rd wr) → Q s') :
    WP isa (.call n c) t Q := by
  obtain ⟨hcov, hcovw⟩ := covers hc hsub hwsub
  refine WP.callV hv hpre hcov hcovw (fun s' hrd hwr hsp hf hcs _ hvs hpost => ?_) hn
  have hnB := hL.nB
  refine hQ s' ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp,
    fun r hr hr' => (hcs r hr hr').trans (hc.cs r hr hr'), fun r hr => (hvs r hr).trans (hc.vs r hr),
    ?_, hc.frame.trans (Frame.sub hf fun r hr => (hwsub r hr).sub hL)⟩
    (hs.frame hf (fun R hR => ((hwsub R hR).disj hL).1) (by omega_using [hnB])) hf hpost
  have hlr : L.LR.Contains (L.B + BitVec.ofNat 64 frameBytes) (64 / 8) := by
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide
  rw [hf.readW hlr (fun R hR => ((hwsub R hR).disj hL).2) (by decide)]
  exact hc.lr

end VG.Proof.Rsa.AArch64

end

end

/-! ### `Rsa.AArch64.PrivArgs`, which this module and modules that import it used -/

section

/-!
# `vg_rsa_private_checked` on AArch64: the arguments of the CRT

`saveSlots` keeps our arguments in the slots (`saveSlots_ok`), `copyArgs`
copies our last ten stack arguments to the bottom of the inner frame as the
CRT's (`copyArgs_ok`, one word at a time), and `crtRegs` sets its arguments
in registers (`crtRegs_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Rsa.AArch64.PrivChecked

/-- The registers a block writes, other than the callee-saved ones. -/
macro "priv_cs_tac" : tactic => `(tactic| plain_simp_names (
                   intro r hr _
                   revert hr
                   simp only [preserved, List.mem_cons, List.not_mem_nil, or_false]
                   rintro (h | h | h | h | h | h | h | h | h | h | h) <;> subst h <;>
                     simp only [RegUpd.gpr_write, reduceCtorEq, ite_false]))

/-- Six words stored in the slots. -/
theorem six_ok (B : Addr) (_hB : B.toNat + 128 ≤ 2 ^ 64) (m : Mem) (a b c d e f : BitVec 64) :
    let m' := (((((m.writeW (B + BitVec.ofNat 64 80) a).writeW (B + BitVec.ofNat 64 88) b).writeW
      (B + BitVec.ofNat 64 96) c).writeW (B + BitVec.ofNat 64 104) d).writeW (B + BitVec.ofNat 64 112) e).writeW
      (B + BitVec.ofNat 64 120) f
    Frame [⟨B + BitVec.ofNat 64 80, 48⟩] m m' ∧ m'.readW (B + BitVec.ofNat 64 80) 64 = a ∧
      m'.readW (B + BitVec.ofNat 64 88) 64 = b ∧ m'.readW (B + BitVec.ofNat 64 96) 64 = c ∧
      m'.readW (B + BitVec.ofNat 64 104) 64 = d ∧ m'.readW (B + BitVec.ofNat 64 112) 64 = e ∧
      m'.readW (B + BitVec.ofNat 64 120) 64 = f := by
  have sep : ∀ x y, x + 8 ≤ y ∨ y + 8 ≤ x → x + 8 ≤ 128 → y + 8 ≤ 128 →
      Mem.Sep (B + BitVec.ofNat 64 x) (64 / 8) (B + BitVec.ofNat 64 y) (64 / 8) :=
    fun x y h h₁ h₂ => Offset.sep B h (by omega_arith) (by omega_arith)
  have ct : ∀ x, 80 ≤ x → x + 8 ≤ 128 →
      (⟨B + BitVec.ofNat 64 80, 48⟩ : Region).Contains (B + BitVec.ofNat 64 x) (64 / 8) :=
    fun x h₁ h₂ => Offset.contains B h₁ (by omega_arith) (by omega_arith)
  refine ⟨((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (ct 80 (by omega_arith) (by omega_arith))).writeW
    (List.mem_singleton_self _) _ (ct 88 (by omega_arith) (by omega_arith))).writeW (List.mem_singleton_self _) _
    (ct 96 (by omega_arith) (by omega_arith))).writeW (List.mem_singleton_self _) _ (ct 104 (by omega_arith) (by omega_arith))).writeW
    (List.mem_singleton_self _) _ (ct 112 (by omega_arith) (by omega_arith))).writeW (List.mem_singleton_self _) _
    (ct 120 (by omega_arith) (by omega_arith)), ?_, ?_, ?_, ?_, ?_, Mem.readW_writeW_self64 _ _ _⟩
  · rw [Mem.readW_writeW_sep (sep 80 120 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (sep 80 112 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (sep 80 104 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (sep 80 96 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (sep 80 88 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_sep (sep 88 120 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (sep 88 112 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (sep 88 104 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (sep 88 96 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_sep (sep 96 120 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (sep 96 112 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (sep 96 104 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_sep (sep 104 120 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (sep 104 112 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_sep (sep 112 120 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_self64]

section
variable {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}

/-- Our arguments in registers. -/
structure Regs (L : Lay) (t : State) : Prop where
  x0 : t.gpr .x0 = L.out
  x2 : t.gpr .x2 = L.n
  x3 : t.gpr .x3 = L.k
  x4 : t.gpr .x4 = L.e
  x5 : t.gpr .x5 = L.el
  x6 : t.gpr .x6 = L.inp

theorem saveSlots_ok (hL : L.Ok) {t : State} (hc : Ctx L g vv m₀ t) (hr : Regs L t) :
    WP isa (.block saveSlots) t fun t' => Ctx L g vv m₀ t' ∧ Slots L t'.mem ∧ Regs L t' ∧
      t'.gpr .x15 = L.B ∧ Frame [⟨L.B + BitVec.ofNat 64 80, 48⟩] t.mem t'.mem := by
  have hnB := hL.nB
  have w := fun d (h : d + 8 ≤ frameBytes) => hc.inFrW hL (d := d) (n := 8) h
  have w80 := w 80 (by decide)
  have w88 := w 88 (by decide)
  have w96 := w 96 (by decide)
  have w104 := w 104 (by decide)
  have w112 := w 112 (by decide)
  have w120 := w 120 (by decide)
  apply WP.of_runBlock
  simp only [saveSlots, oOut, oN, oK, oE, oEl, oIn, runBlock_cons, runStep_some, runBlock_nil, exec, addr,
    State.store, State.read, Size.bits, Size.bytes, BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.rd_write,
    RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, Option.bind_some, reduceCtorEq, ite_false,
    ite_true, hc.sp, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self, w80, w88, w96,
    w104, w112, w120, write8, Option.some.injEq, exists_eq_left', BitVec.add_zero]
  obtain ⟨f, k80, k88, k96, k104, k112, k120⟩ := six_ok L.B (by omega_arith) t.mem (t.gpr .x0) (t.gpr .x2)
    (t.gpr .x3) (t.gpr .x4) (t.gpr .x5) (t.gpr .x6)
  refine ⟨hc.store hL rfl rfl (hc.sp.symm ▸ rfl) rfl
    (by priv_cs_tac) (Frame.sub f fun r hr => ?_), ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, f⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨L.FR, by simp, Offset.sub_base _ (by decide)⟩
  all_goals try simp only [RegUpd.gpr_write, reduceCtorEq, ite_false]
  exacts [k80.trans hr.x0, k88.trans hr.x2, k96.trans hr.x3, k104.trans hr.x4, k112.trans hr.x5,
    k120.trans hr.x6, hr.x0, hr.x2, hr.x3, hr.x4, hr.x5, hr.x6]

/-- After copying `j` of the CRT's stack arguments, from `t₀`. -/
structure CopyInv (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (t₀ : State) (j : Nat)
    (t : State) : Prop where
  ctx : Ctx L g vv m₀ t
  slots : Slots L t.mem
  regs : Regs L t
  x15 : t.gpr .x15 = L.B
  frame : Frame [⟨L.B, 80⟩] t₀.mem t.mem
  args : ∀ i < j, t.mem.readW (L.B + BitVec.ofNat 64 (8 * i)) 64 = m₀.readW (L.B + BitVec.ofNat 64 (arg (i + 2))) 64

theorem copyArg_ok (hL : L.Ok) {t₀ t : State} {j : Nat} (hj : j < 10) (hI : CopyInv L g vv m₀ t₀ j t) :
    WP isa (.block (copyArg j)) t (CopyInv L g vv m₀ t₀ (j + 1)) := by
  have hnB := hL.nB
  have hc := hI.ctx
  have la := hc.inArgs hL (j := j + 2) (by omega_arith)
  have aw := hc.argW hL (j := j + 2) (by omega_arith)
  have w := hc.inFrW hL (d := 8 * j) (n := 8) (by simp only [frameBytes]; omega_arith)
  apply WP.of_runBlock
  simp only [copyArg, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store,
    State.read, Size.bits, Size.bytes, BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.rd_write,
    RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, Option.map_some, Option.bind_some, reduceCtorEq,
    ite_false, ite_true, hc.sp, hI.x15, la, w, read8, aw, write8, Option.some.injEq, exists_eq_left',
    show 8 * j % 8 = 0 by omega_arith, show 8 * j < 4096 * 8 by omega_arith, show arg (j + 2) % 8 = 0 by
      simp only [arg, frameBytes]; omega_arith, show arg (j + 2) < 32768 by simp only [arg, frameBytes]; omega_arith,
    and_self]
  have hfr : Frame [L.FR] t.mem (t.mem.writeW (L.B + BitVec.ofNat 64 (8 * j))
      (m₀.readW (L.B + BitVec.ofNat 64 (arg (j + 2))) 64)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by simp only [frameBytes]; omega_arith) (by omega_arith))
  have hf80 : Frame [⟨L.B, 80⟩] t.mem (t.mem.writeW (L.B + BitVec.ofNat 64 (8 * j))
      (m₀.readW (L.B + BitVec.ofNat 64 (arg (j + 2))) 64)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
  refine ⟨hc.store hL rfl rfl hc.sp.symm rfl (by priv_cs_tac) hfr, hI.slots.frame hf80 (fun R hR => by
      simp only [List.mem_singleton] at hR; subst hR
      have := Offset.disjoint_base L.B (d := oOut) (n := 48) (k := 80) (by decide) (by simp only [oOut]; omega_arith)
      exact this) (by omega_arith), ?_, ?_, hI.frame.trans hf80, fun i hi => ?_⟩
  · have r := hI.regs
    exact ⟨r.x0, r.x2, r.x3, r.x4, r.x5, r.x6⟩
  · exact hI.x15
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
      exact hI.args i hi
    · exact Mem.readW_writeW_self64 _ _ _

theorem copyArgs_upto (hL : L.Ok) {t₀ : State} :
    ∀ n ≤ 10, ∀ t, CopyInv L g vv m₀ t₀ 0 t →
      WP isa (.block ((List.range n).flatMap copyArg)) t (CopyInv L g vv m₀ t₀ n)
  | 0, _, _, h => WP.block_nil h
  | n + 1, hn, t, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    exact WP.mono (copyArgs_upto hL n (by omega_arith) t h) fun t' h' => copyArg_ok hL (by omega_arith) h'

/-- The arguments of the CRT in registers, and on the stack at `B`. -/
structure CrtArgs (L : Lay) (t : State) : Prop where
  x0 : t.gpr .x0 = L.B + BitVec.ofNat 64 oM
  x1 : t.gpr .x1 = L.k
  x2 : t.gpr .x2 = L.n
  x3 : t.gpr .x3 = L.k
  x4 : t.gpr .x4 = L.inp
  x5 : t.gpr .x5 = L.k
  x6 : t.gpr .x6 = L.p
  x7 : t.gpr .x7 = L.pl
  stk : ∀ i < 10, t.mem.readW (L.B + BitVec.ofNat 64 (8 * i)) 64 = L.argv (i + 2)

theorem crtRegs_ok (hL : L.Ok) {t₀ t : State} (ha : ArgsAt L m₀) (hI : CopyInv L g vv m₀ t₀ 10 t) :
    WP isa (.block crtRegs) t fun t' => Ctx L g vv m₀ t' ∧ Slots L t'.mem ∧ CrtArgs L t' ∧
      Frame [⟨L.B, 80⟩] t₀.mem t'.mem := by
  have hc := hI.ctx
  have l0 := hc.inArgs hL (j := 0) (by omega_arith)
  have l1 := hc.inArgs hL (j := 1) (by omega_arith)
  have a0 := (hc.argW hL (j := 0) (by omega_arith)).trans (ha 0 (by omega_arith))
  have a1 := (hc.argW hL (j := 1) (by omega_arith)).trans (ha 1 (by omega_arith))
  apply WP.of_runBlock
  simp only [crtRegs, runBlock_cons, runStep_some, runBlock_nil, exec, State.load, State.read, Size.bits,
    BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write,
    RegUpd.mem_write, Option.map_some, reduceCtorEq, ite_false, ite_true, hc.sp, l0, l1, read8, a0, a1,
    Option.some.injEq, exists_eq_left', show arg 0 % 8 = 0 by decide, show arg 0 < 32768 by decide,
    show arg 1 % 8 = 0 by decide, show arg 1 < 32768 by decide, show oM < 4096 by decide, and_self,
    show (0 : Nat) < 4096 by decide]
  have r := hI.regs
  refine ⟨hc.regs rfl rfl rfl rfl rfl (by priv_cs_tac), hI.slots, ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl,
    fun i hi => (hI.args i hi).trans (ha _ (by omega_arith))⟩, hI.frame⟩
  all_goals simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, BitVec.setWidth_eq,
    BitVec.add_zero, r.x2, r.x3, r.x6]

end

end VG.Proof.Rsa.AArch64

end

end

/-!
# `vg_rsa_private_checked` on AArch64: the call of the CRT

From `CrtArgs`, the CRT reads `n`, the input, the private key and its stack
arguments at `B`, and writes `M` and `scratch` (`crt_call`).
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Rsa.AArch64.PrivChecked

theorem gpr_ce (t : State) (rd wr : List Region) {r : Reg} (h : r ∉ linkRegs) :
    (t.callEntry.withRegions rd wr).gpr r = t.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h]

section
variable {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}

/-- The regions the CRT reads and writes. -/
abbrev crtRd (L : Lay) : List Region :=
  [L.N, ⟨L.inp, L.k.toNat⟩, L.P, L.Q, L.DP, L.DQ, L.QI, ⟨L.B, 80⟩]
abbrev crtWr (L : Lay) : List Region := [L.M, L.SC]

theorem low_sub (L : Lay) {n : Nat} (h : n ≤ stackBytes) : Region.Sub ⟨L.B, n⟩ L.STK := Region.sub_prefix h

namespace Lay.Ok
variable (hL : L.Ok)
include hL

/-- A range of the stack misses every buffer. -/
theorem stk_sub {r : Region} (h : Region.Sub r L.STK) :
    r.Disjoint L.OUT ∧ r.Disjoint L.N ∧ r.Disjoint L.E ∧ r.Disjoint L.IN ∧ r.Disjoint L.P ∧
      r.Disjoint L.Q ∧ r.Disjoint L.DP ∧ r.Disjoint L.DQ ∧ r.Disjoint L.QI ∧ r.Disjoint L.SC :=
  ⟨hL.ko.sub_left h, hL.kn.sub_left h, hL.ke.sub_left h, hL.ki.sub_left h, hL.kp.sub_left h,
    hL.kq.sub_left h, hL.kdp.sub_left h, hL.kdq.sub_left h, hL.kqi.sub_left h, hL.ksc.sub_left h⟩

theorem M_sub : Region.Sub L.M L.STK := Offset.sub_base _ (by have := hL.khi; simp only [oM, stackBytes]; omega_arith)

theorem PRE_sub : Region.Sub L.PRE L.STK := by
  have := hL.khi
  refine Offset.sub_base _ ?_
  simp only [oPre, stackBytes, Lay.pw]; omega_arith

theorem M_HI : Within L.M L.HI := ⟨0, by simp, by have := hL.khi; simp only [oM, frameBytes]; omega_arith⟩

theorem PRE_HI : Within L.PRE L.HI :=
  ⟨oPre - oM, by rw [add_add]; rfl, by have := hL.khi; simp only [oPre, oM, frameBytes, Lay.pw]; omega_arith⟩

theorem IN_k : Within ⟨L.inp, L.k.toNat⟩ L.IN := within_base _ (by rw [hL.ilk])

end Lay.Ok

theorem crtCall_pre (hL : L.Ok) {t : State} (hc : Ctx L g vv m₀ t) (ha : CrtArgs L t) :
    crtA.pre (t.callEntry.withRegions (crtRd L) (crtWr L)) := by
  have hnB := hL.nB
  have hk := hL.khi
  have sa : ∀ i < 10, stackArg (t.callEntry.withRegions (crtRd L) (crtWr L)) i = L.argv (i + 2) := by
    intro i hi
    simp only [stackArg, stackArgAddr, State.withRegions_mem, State.callEntry_mem, State.withRegions_sp,
      State.callEntry_sp, hc.sp]
    exact ha.stk i hi
  have hM := hL.stk_sub hL.M_sub
  have hA := hL.stk_sub (low_sub L (n := 80) (by decide))
  have hMA : L.M.Disjoint ⟨L.B, 80⟩ :=
    Offset.disjoint_base _ (by decide) (by simp only [oM]; omega_arith)
  simp only [crtA, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp, State.callEntry_sp,
    hc.sp, sa 0 (by omega_arith), sa 1 (by omega_arith), sa 2 (by omega_arith), sa 3 (by omega_arith), sa 4 (by omega_arith),
    sa 5 (by omega_arith), sa 6 (by omega_arith), sa 7 (by omega_arith), sa 8 (by omega_arith), sa 9 (by omega_arith), Lay.argv,
    gpr_ce _ _ _ (by decide : Reg.x0 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x1 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x4 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x5 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x6 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x7 ∉ linkRegs),
    ha.x0, ha.x1, ha.x2, ha.x3, ha.x4, ha.x5, ha.x6, ha.x7, stackArgAddr, Nat.mul_zero, BitVec.add_zero]
  have hdp := hL.dpl
  have hqi := hL.qil
  have hdq := hL.dql
  have hIk : (⟨L.inp, L.k.toNat⟩ : Region).Disjoint L.SC := hL.isc.sub_left hL.IN_k.sub
  obtain ⟨-, hMn, -, hMi, hMp, hMq, hMdp, hMdq, hMqi, hMsc⟩ := hM
  have hMk : BitVec.toNat (L.B + BitVec.ofNat 64 oM) + L.k.toNat ≤ 2 ^ 64 := by
    rw [Offset.toNat_add_ofNat]; simp only [oM]; omega_arith
  exact ⟨by omega_arith, trivial, trivial, hMn, hMi.sub_right hL.IN_k.sub, hMp, hMq, hMdp, hMdq, hMqi, hMsc, hMA,
    hL.nsc, hIk, hL.psc, hL.qsc, hL.dpsc, hL.dqsc, hL.qisc, hA.2.2.2.2.2.2.2.2.2.symm, hMk, hL.bn,
    by have := hL.bi; rw [hL.ilk] at this; exact this, hL.bp, hL.bq, hL.bdp, hL.bdq, hL.bqi, hL.bsc,
    ⟨hL.klo, hL.khi⟩, trivial, trivial, hL.pl1, hL.plk, hL.ql1, hL.qlk, hdp, hqi, hdq, hL.slk⟩

theorem crt_sub (hL : L.Ok) : ∀ r ∈ crtRd L ++ crtWr L, ∃ R ∈ L.regions, Within r R := by
  have hk := hL.khi
  simp only [crtRd, crtWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact ⟨L.N, by simp, within_base _ (Nat.le_refl _)⟩
  · exact ⟨L.IN, by simp, hL.IN_k⟩
  · exact ⟨L.P, by simp, within_base _ (Nat.le_refl _)⟩
  · exact ⟨L.Q, by simp, within_base _ (Nat.le_refl _)⟩
  · exact ⟨L.DP, by simp, within_base _ (Nat.le_refl _)⟩
  · exact ⟨L.DQ, by simp, within_base _ (Nat.le_refl _)⟩
  · exact ⟨L.QI, by simp, within_base _ (Nat.le_refl _)⟩
  · exact ⟨L.FR, by simp, within_base _ (by decide)⟩
  · exact ⟨L.FR, by simp, within_off _ (by simp only [oM, frameBytes]; omega_arith)⟩
  · exact ⟨L.SC, by simp, within_base _ (Nat.le_refl _)⟩

theorem crt_wsub (hL : L.Ok) : ∀ r ∈ crtWr L, InW L r := by
  simp only [crtWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact .inr (.inr hL.M_HI)
  · exact .inr (.inl (within_base _ (Nat.le_refl _)))

/-- What the CRT writes to `M` and returns, from the memory `m` at the call. -/
abbrev CrtOut (L : Lay) (m m' : Mem) (r : BitVec 64) : Prop :=
  Spec.Rsa.written m' (L.B + BitVec.ofNat 64 oM) L.k.toNat (r.setWidth 32)
    (Spec.Rsa.privateCrt (Spec.Rsa.bytesAt m L.n L.k.toNat) (Spec.Rsa.bytesAt m L.inp L.k.toNat)
      (Spec.Rsa.bytesAt m L.p L.pl.toNat) (Spec.Rsa.bytesAt m L.q L.ql.toNat)
      (Spec.Rsa.bytesAt m L.dp L.pl.toNat) (Spec.Rsa.bytesAt m L.dq L.ql.toNat)
      (Spec.Rsa.bytesAt m L.qi L.pl.toNat))

/-- The call of the CRT `C`, for a call state with `C.K`. -/
theorem crt_call (C : CrtCallee) (hL : L.Ok) {t : State} (hc : Ctx L g vv m₀ t) (hs : Slots L t.mem)
    (ha : CrtArgs L t) (hK : C.K (t.callEntry.withRegions (crtRd L) (crtWr L))) :
    WP isa (.call C.name C.code) t fun t' => Ctx L g vv m₀ t' ∧ Slots L t'.mem ∧
      Frame (crtWr L) t.mem t'.mem ∧ CrtOut L t.mem t'.mem (t'.gpr .x0) := by
  refine call_ok hL C.ok C.noFrames hc hs ⟨crtCall_pre hL hc ha, hK⟩ (crt_sub hL) (crt_wsub hL)
    fun s' hc' hs' hf hpost => ⟨hc', hs', hf, ?_⟩
  have sa : ∀ i < 10, stackArg (t.callEntry.withRegions (crtRd L) (crtWr L)) i = L.argv (i + 2) := by
    intro i hi
    simp only [stackArg, stackArgAddr, State.withRegions_mem, State.callEntry_mem, State.withRegions_sp,
      State.callEntry_sp, hc.sp]
    exact ha.stk i hi
  have h := hpost
  simp only [crtKA, crtA, State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr,
    gpr_ce _ _ _ (by decide : Reg.x0 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x4 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x6 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x7 ∉ linkRegs),
    ha.x0, ha.x2, ha.x3, ha.x4, ha.x6, ha.x7, sa 0 (by omega_arith), sa 1 (by omega_arith), sa 2 (by omega_arith),
    sa 4 (by omega_arith), sa 6 (by omega_arith), Lay.argv] at h
  exact h

end

end VG.Proof.Rsa.AArch64
