import VerifiedGarbage.Proof.Ed448.AArch64.Point56.CombFn
import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Call

/-!
# Ed448's comb on AArch64: calls of the two affine additions

Untrusted: everything here is checked by Lean. `fnCallV_ok`: `fnCall_ok` for a
function that keeps the low halves of `v8`–`v15` by restoring them, rather than
by never writing them. `combAddCall_ok`: a call of `vg_ed448_r56_comb_add`, as
the inlined additions.
-/

namespace VG.Proof.Ed448.AArch64.Point56

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64 (slot ACC)
open VG.Proof.X448.AArch64 (Scr Keeps Outside2 ofs)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd Same fclob)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)

/-- **A call** of a function `fn` that, from `ws` (`base`) in `x0`, every slot's limbs below `Ib`
and `P` of the memory, ends in `FnPost` with `Q` of the memories and the low halves of
`v8`–`v15` restored, which keeps the memory outside the slots and the products'
coefficients. -/
theorem fnCallV_ok {name : String} {c : Bool} {rs : List Reg} {fn : Prog isa} {base : Addr}
    {P : Mem → Prop} {Q : Mem → Mem → Prop}
    (hrs : ∀ r, r ∉ .x30 :: fclob → r ∉ rs ∨ r ∈ (keptRegs c).map Prod.fst)
    (hpk : ∀ r ∈ preserved, r ∉ rs ∨ r ∈ (keptRegs c).map Prod.fst)
    (hfn : ∀ t, FnPre t → t.gpr .x0 = base → P t.mem → WP isa fn t fun u => FnPost c rs t u (Q t.mem) ∧
      ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64)
    (hframe : ∀ m m', Q m m' → Outside2 base 64 2816 ACC 1152 m m') (hnf : fn.noFrames = true)
    {s : State} (hs : Scr s base) (hb : BEnv s.mem base) (hp : P s.mem) :
    WP isa (fnCall name fn) s fun t => CKeep base s t ∧ Q s.mem t.mem := by
  have hpres : ∀ r ∈ preserved, (r ∉ rs ∨ r ∈ (keptRegs c).map Prod.fst) ∧ r ≠ .x3 ∧ r ≠ .x12 :=
    fun r hr => ⟨hpk r hr, by revert hr; cases r <;> decide,
      by revert hr; cases r <;> decide⟩
  unfold fnCall
  rw [WP.seq_iff]
  refine WP.of_runBlock ⟨s.write .x .x0 (s.gpr .x3 + BitVec.ofNat 64 0), ?_, ?_⟩
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
      show (0 : Nat) < 4096 from by decide, ite_true, BitVec.setWidth_eq]
  generalize hs1 : s.write .x .x0 (s.gpr .x3 + BitVec.ofNat 64 0) = s1
  have g0 : s1.gpr .x0 = base := by
    rw [← hs1, RegUpd.gpr_write_self, BitVec.setWidth_eq, BitVec.add_zero, hs.x3]
  have gk : ∀ r, r ≠ .x0 → s1.gpr r = s.gpr r := fun r hr => by
    rw [← hs1, RegUpd.gpr_write_of_ne _ _ _ hr]
  have m1 : s1.mem = s.mem := by rw [← hs1]; rfl
  have r1 : s1.rd = s.rd := by rw [← hs1]; rfl
  have w1 : s1.wr = s.wr := by rw [← hs1]; rfl
  have sp1 : s1.sp = s.sp := by rw [← hs1]; rfl
  have v1 : s1.v = s.v := by rw [← hs1]; rfl
  have hcov : Covers [⟨base, 8192⟩] s1.wr := Covers.of_mem fun r hr => by
    rw [List.mem_singleton.mp hr, w1]; exact hs.wr
  refine WP.callV (k := fnK c rs base P Q) (rd := []) (wr := [⟨base, 8192⟩]) ?hv
    ⟨rfl, rfl, by rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), g0], hs.nowrap,
      by rw [State.withRegions_mem, State.callEntry_mem, m1]; exact hb,
      by rw [State.withRegions_mem, State.callEntry_mem, m1]; exact hp⟩
    (Covers.right hcov) hcov ?_ hnf
  case hv =>
    intro t ⟨_, hwr, hx0, hn, hbt, hpt⟩
    have fp : FnPre t := ⟨by rw [hwr, hx0]; exact List.mem_singleton_self _, by rw [hx0]; exact hn,
      by rw [hx0]; exact hbt⟩
    obtain ⟨tr, t', he, hpost, hv⟩ := hfn t fp hx0 hpt
    exact ⟨tr, t', he, ⟨fun r hr => hpost.1 r (hpres r hr).1 (hpres r hr).2.1 (hpres r hr).2.2,
      hpost.2.2.2.2.2.1, hv⟩, hpost⟩
  intro t hrd hwr hsp _ _ _ hv ⟨hg, h3, h12, _, _, _, hq⟩
  simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, m1] at hg h3 h12 hq
  refine ⟨⟨⟨fun r hr => ?_, by rw [hrd, r1], by rw [hwr, w1]⟩, by rw [hsp, sp1], hframe _ _ hq,
    fun r hr => by rw [hv r hr, v1]⟩, hq⟩
  by_cases e3 : r = .x3
  · subst e3; rw [h3, State.callEntry_gpr _ (by decide), g0, hs.x3]
  by_cases e12 : r = .x12
  · subst e12; rw [h12, hs.mask]
  have hl : r ∉ VG.AArch64.linkRegs := by
    simp only [List.mem_cons, not_or] at hr
    simp only [VG.AArch64.linkRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨?_, ?_, hr.1⟩ <;> intro h <;> subst h <;> exact absurd hr.2 (by decide)
  have h0 : r ≠ .x0 := fun h => by subst h; exact hr (by decide)
  rw [hg r (hrs r hr) e3 e12, State.callEntry_gpr _ hl, gk r h0]

theorem fnOk_slots : ∀ d, fnOk d = true → 64 ≤ d ∧ d + 8 ≤ 2880 ∨ 3584 ≤ d ∧ d + 8 ≤ 4736 := by
  intro d hd; simp only [fnOk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hd; omega

/-- **A call of `vg_ed448_r56_comb_add`**, as the inlined additions. -/
theorem combAddCall_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base)
    (hz : Bnd Mb s.mem base (slot (19 : Index).val)) :
    WP isa Point56.combAddCall s fun t => CKeep base s t ∧ CombMem base s.mem t.mem :=
  fnCallV_ok (c := false) (P := fun m => Bnd Mb m base (slot (19 : Index).val))
    (fun r hr => .inl fun h => hr (List.mem_cons_of_mem _ h)) (by decide)
    (fun t ht h0 hp => by
      refine WP.mono (combAddFn_ok ht (by rw [h0]; exact hp)) fun u hu => ?_
      rw [h0] at hu; exact hu)
    (fun m m' hq => outside2_of fnOk_slots hq.2.2.2.2) (by decide +kernel) hs hb hz

end VG.Proof.Ed448.AArch64.Point56
