import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Body
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.Covers

/-!
# Ed448 on AArch64: calls of the functions

Untrusted: everything here is checked by Lean. `fnCall_ok`: a call (`fnCall`,
with `ws` from `x3`) of a function proven as `doubleFn_ok`, `addFn_ok` and
`powFn_ok` are, from the register-resident arithmetic's state (`Scr`, every
slot's limbs below `Ib`), keeps what a field operation keeps but `x30`
(`CKeep`) and ends in the function's memory. The call runs on the working
space alone (`WP.call`, with the function's own proof as its contract, `fnK`).

`doubleCall_ok`, `addCall_ok` and `powCall_ok`: the calls, as the inlined code
(`dblOps_ok`, `addOps_ok`, `root_spec`).
-/

namespace VG.Proof.Ed448.AArch64.Point56

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64 (slot ACC)
open VG.Proof.X448.AArch64 (Scr Keeps Outside2 ofs)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd Same fclob)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.X448.AArch64.Base (genEnv temps)
open VG.Proof.Ed448.AArch64.Window (dblEnv)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

theorem genEnv_pt (e : Env) :
    VG.Proof.X448.AArch64.Base.pt (genEnv 3 4 5 6 7 8 e) 3 4 5 =
      VG.Proof.X448.AArch64.Base.genPt (VG.Proof.X448.AArch64.Base.pt e 3 4 5)
        (VG.Proof.X448.AArch64.Base.pt e 6 7 8) (e 19) := rfl

/-- What a call keeps: every register but `x30` and the field operations' (`fclob`, which has
`x0`, `x16` and `x17`), the stack pointer, and the memory outside the slots and the products'
coefficients. -/
structure CKeep (base : Addr) (s t : State) : Prop where
  regs : Keeps (.x30 :: fclob) s t
  sp : t.sp = s.sp
  mem : Outside2 base 64 2816 ACC 1152 s.mem t.mem

theorem CKeep.scr {base : Addr} {s t : State} (h : CKeep base s t) (hs : Scr s base) : Scr t base :=
  hs.of_keeps h.regs (by decide)

theorem CKeep.trans {base : Addr} {s t u : State} (h : CKeep base s t) (h' : CKeep base t u) :
    CKeep base s u := ⟨h.regs.trans h'.regs, h'.sp.trans h.sp, h.mem.trans h'.mem⟩

/-- The contract of a call, from the function's own proof: from `ws` (`base`) in `x0` and every
slot's limbs below `Ib`, and `P` of the memory, `FnPost` with `Q` of the memories. -/
def fnK (c : Bool) (rs : List Reg) (base : Addr) (P : Mem → Prop) (Q : Mem → Mem → Prop) :
    Contract isa where
  pre t := t.rd = [] ∧ t.wr = [⟨base, 8192⟩] ∧ t.gpr .x0 = base ∧ base.toNat + 8192 ≤ 2 ^ 64 ∧
    BEnv t.mem base ∧ P t.mem
  post t t' := FnPost c rs t t' (Q t.mem)
  pub _ _ := True

/-- **A call** of a function `fn` that, from `ws` (`base`) in `x0`, every slot's limbs below
`Ib` and `P` of the memory, ends in `FnPost` with `Q` of the memories, which keeps the memory
outside the slots and the products' coefficients. -/
theorem fnCall_ok {name : String} {c : Bool} {rs : List Reg} {fn : Prog isa} {base : Addr}
    {P : Mem → Prop} {Q : Mem → Mem → Prop}
    (hrs : ∀ r, r ∉ .x30 :: fclob → r ∉ rs ∨ r ∈ (keptRegs c).map Prod.fst)
    (hpk : ∀ r ∈ preserved, r ∉ rs ∨ r ∈ (keptRegs c).map Prod.fst)
    (hfn : ∀ t, FnPre t → t.gpr .x0 = base → P t.mem → WP isa fn t fun u => FnPost c rs t u (Q t.mem))
    (hframe : ∀ m m', Q m m' → Outside2 base 64 2816 ACC 1152 m m')
    (hkv : fn.allInstrs keepsV = true) (hnf : fn.noFrames = true)
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
  have hcov : Covers [⟨base, 8192⟩] s1.wr := Covers.of_mem fun r hr => by
    rw [List.mem_singleton.mp hr, w1]; exact hs.wr
  refine WP.call (k := fnK c rs base P Q) (rd := []) (wr := [⟨base, 8192⟩]) ?hv
    ⟨rfl, rfl, by rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), g0], hs.nowrap,
      by rw [State.withRegions_mem, State.callEntry_mem, m1]; exact hb,
      by rw [State.withRegions_mem, State.callEntry_mem, m1]; exact hp⟩
    (Covers.right hcov) hcov ?_ hnf
  case hv =>
    intro t ⟨_, hwr, hx0, hn, hbt, hpt⟩
    have fp : FnPre t := ⟨by rw [hwr, hx0]; exact List.mem_singleton_self _, by rw [hx0]; exact hn,
      by rw [hx0]; exact hbt⟩
    obtain ⟨tr, t', he, hpost, hv⟩ := WP.preservedV (hfn t fp hx0 hpt) hkv
    exact ⟨tr, t', he, ⟨fun r hr => hpost.1 r (hpres r hr).1 (hpres r hr).2.1 (hpres r hr).2.2,
      hpost.2.2.2.2.2.1, hv⟩, hpost⟩
  intro t hrd hwr hsp _ _ _ ⟨hg, h3, h12, _, _, _, hq⟩
  simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, m1] at hg h3 h12 hq
  refine ⟨⟨⟨fun r hr => ?_, by rw [hrd, r1], by rw [hwr, w1]⟩, by rw [hsp, sp1], hframe _ _ hq⟩, hq⟩
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

/-- The memory outside the slots and the products' coefficients, from the stores. -/
theorem outside2_of {ok : Nat → Bool} (hok : ∀ d, ok d = true → 64 ≤ d ∧ d + 8 ≤ 2880 ∨ 3584 ≤ d ∧ d + 8 ≤ 4736)
    {base : Addr} {m m' : Mem}
    (h : ∀ a, Unstored ok base a → m' a = m a) : Outside2 base 64 2816 ACC 1152 m m' := by
  intro a h1 h2
  refine h a fun d hd => ?_
  have := hok d hd
  simp only [ACC] at h2
  rw [show a - (base + BitVec.ofNat 64 d) = (a - base) - BitVec.ofNat 64 d by
    exact Offset.sub_add_eq a base _]
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  simp only [ofs] at h1 h2
  have : (a - base).toNat < 2 ^ 64 := (a - base).isLt
  omega

theorem dblOk_slots : ∀ d, dblOk d = true → 64 ≤ d ∧ d + 8 ≤ 2880 ∨ 3584 ≤ d ∧ d + 8 ≤ 4736 := by
  intro d hd; simp only [dblOk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hd; omega

theorem powOk_slots : ∀ d, powOk d = true → 64 ≤ d ∧ d + 8 ≤ 2880 ∨ 3584 ≤ d ∧ d + 8 ≤ 4736 := by
  intro d hd; simp only [powOk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hd; omega

/-- **A call of `vg_ed448_r56_point_double`**, as the inlined doubling. -/
theorem doubleCall_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base)
    (hz : Bnd Mb s.mem base (slot 5)) :
    WP isa Point56.doubleCall s fun t => CKeep base s t ∧ PtMem base (dblEnv 3 4 5) s.mem t.mem :=
  fnCall_ok (c := false) (P := fun m => Bnd Mb m base (slot 5)) (fun r hr => .inl fun h => hr (List.mem_cons_of_mem _ h)) (by decide)
    (fun t ht h0 hp => by
      refine WP.mono (doubleFn_ok ht (by rw [h0]; exact hp)) fun u hu => ?_
      rw [h0] at hu; exact hu)
    (fun m m' hq => outside2_of dblOk_slots hq.2.2.2.2.2.2) doubleFn_keepsV
    (by decide +kernel) hs hb hz

/-- **A call of `vg_ed448_r56_point_add`**, as the inlined addition. -/
theorem addCall_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base)
    (hz : Bnd Mb s.mem base (slot 19)) :
    WP isa Point56.addCall s fun t => CKeep base s t ∧ PtMem base (genEnv 3 4 5 6 7 8) s.mem t.mem :=
  fnCall_ok (c := false) (P := fun m => Bnd Mb m base (slot 19)) (fun r hr => .inl fun h => hr (List.mem_cons_of_mem _ h)) (by decide)
    (fun t ht h0 hp => by
      refine WP.mono (addFn_ok ht (by rw [h0]; exact hp)) fun u hu => ?_
      rw [h0] at hu; exact hu)
    (fun m m' hq => outside2_of dblOk_slots hq.2.2.2.2.2.2) addFn_keepsV
    (by decide +kernel) hs hb hz

/-- **A call of `vg_gf448_r56_pow_p34`**, as the inlined power. -/
theorem powCall_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) :
    WP isa Point56.powCall s fun t => CKeep base s t ∧ PowMem base s.mem t.mem :=
  fnCall_ok (c := true) (P := fun _ => True) (fun r hr => by
      by_cases h : r = .x19
      · exact .inr (by rw [h]; decide)
      · exact .inl fun h' => hr (List.mem_cons_of_mem _ ((List.mem_cons.mp h').resolve_left h)))
    (by decide)
    (fun t ht h0 _ => by
      refine WP.mono (powFn_ok ht) fun u hu => ?_
      rw [h0] at hu; exact hu)
    (fun m m' hq => outside2_of powOk_slots hq.2.2) powFn_keepsV
    (by decide +kernel) hs hb trivial

end VG.Proof.Ed448.AArch64.Point56
