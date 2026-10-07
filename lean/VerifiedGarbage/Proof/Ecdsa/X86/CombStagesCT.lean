import VerifiedGarbage.Proof.Ecdsa.X86.CombCT

/-! # Public arguments across the fixed-base signing stages -/
namespace VG.Proof.Ecdsa.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

/-- The scalar stages use public scratch and argument addresses. -/
def argτ (rs : List Reg) (n : Nat := 5) : VG.X86.Taint.T :=
  { regs := .ofList rs, flags := false, argLen := 4 + 4 * n }

/-- Public scratch addresses let fixed loop counters survive memory stores. -/
def scratchArgτ (n : Nat) (second : Bool := true) : VG.X86.Taint.T :=
  { argτ [.esp, .edi] n with lens := (combτAt second).lens, bases := (combτAt second).bases }

def signPrepCode : Prog isa := p256Comb.signPrep
def signTailCode : Prog isa := p256Comb.signTail
materialize_code signPrepCode
materialize_code signTailCode

theorem signPrep_rel : RelCT isa (VG.X86.Taint.Agree (argτ [.esp]))
    signPrepCode (fun _ _ => True) :=
  RelCT.taint (A := taint) _ (fun _ _ h => h) (by taint_decide)

theorem signTail_rel : RelCT isa (VG.X86.Taint.Agree (scratchArgτ 5))
    signTailCode (fun _ _ => True) :=
  RelCT.taint (A := taint) _ (fun _ _ h => h) (by taint_decide)

/-- Writes within scratch leave all cdecl argument words unchanged. -/
theorem Keep.arg {c : Cfg} {s₀ s : State} {extra : List Region}
    (hp : Pre c s₀ extra) (h : Keep c s₀ (ptr s₀ 4) s) {j : Nat} (hj : j < 5) :
    arg s j = arg s₀ j := by
  have he : argAddr s j = argAddr s₀ j := by simp only [argAddr, h.esp]
  change s.mem.readW (argAddr s j) 32 = _
  rw [he]
  apply arg_keep (h.whole.outside (fun w hw => by
    rw [List.mem_singleton.mp hw]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩))
  exact hp.args_sc.sub_left (arg_sub hp.sp_fit hj)

/-- The public argument area is disjoint from every writable buffer. -/
theorem argWf {c : Cfg} {s₀ s : State} {extra : List Region} (rs : List Reg)
    (hp : Pre c s₀ extra) (he : s.gpr .esp = s₀.gpr .esp) (hw : s.wr = s₀.wr) :
    VG.X86.Taint.Wf (argτ rs) s := by
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h; cases h rfl
  · intro p h; cases h
  · intro p h; cases h
  · intro _
    rw [he, hw, hp.wr]
    refine ⟨hp.sp_fit, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by have := hp.sp_fit; omega) hp.ret_out hp.args_out
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by have := hp.sp_fit; omega) hp.ret_sc hp.args_sc
  · intro p h; cases h

/-- Equal pointers and stack arguments establish a taint agreement. -/
theorem argAgree {rs : List Reg} {n : Nat} {s t : State}
    (ws : VG.X86.Taint.Wf (argτ rs n) s) (wt : VG.X86.Taint.Wf (argτ rs n) t)
    (hr : ∀ r ∈ rs, s.gpr r = t.gpr r) (he : s.gpr .esp = t.gpr .esp)
    (ha : ∀ j < n, arg s j = arg t j) : VG.X86.Taint.Agree (argτ rs n) s t := by
  refine ⟨⟨fun r h => hr r (by simpa only [argτ, RegSet.mem_ofList] using h),
    fun h => by cases h⟩, fun h => False.elim (h rfl), ws, wt,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => he, ?_⟩
  intro k hlo hhi
  have hs := (ws.args (show 0 < 4 + 4 * n by omega)).1
  have ht := (wt.args (show 0 < 4 + 4 * n by omega)).1
  change 4 ≤ k at hlo
  change k < 4 + 4 * n at hhi
  rw [show VG.X86.Taint.depth (argτ rs n).stk = 0 from rfl, Nat.zero_add]
  change (s.gpr .esp).toNat + 0 + (4 + 4 * n) ≤ 2 ^ 32 at hs
  change (t.gpr .esp).toNat + 0 + (4 + 4 * n) ≤ 2 ^ 32 at ht
  rw [VG.X86.Taint.argByte_eq (by omega) hlo hhi,
    VG.X86.Taint.argByte_eq (by omega) hlo hhi,
    Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)),
    Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
  exact congrArg _ (ha ((k - 4) / 4) (by omega))

theorem scratchArgWf {n : Nat} {second : Bool} {s : State}
    (a : VG.X86.Taint.Wf (argτ [.esp, .edi] n) s) (b : VG.X86.Taint.Wf (combτAt second) s) :
    VG.X86.Taint.Wf (scratchArgτ n second) s :=
  ⟨b.lens, b.bases, fun _ h => (List.not_mem_nil h).elim, a.args, a.argBases, a.stk, a.frames, a.room⟩

theorem scratchArgAgree {n : Nat} {second : Bool} {s t : State}
    (a : VG.X86.Taint.Agree (argτ [.esp, .edi] n) s t)
    (ws : VG.X86.Taint.Wf (combτAt second) s) (wt : VG.X86.Taint.Wf (combτAt second) t)
    (hw : s.wr = t.wr) : VG.X86.Taint.Agree (scratchArgτ n second) s t :=
  ⟨a.rf, fun _ => hw, scratchArgWf a.wf₁ ws, scratchArgWf a.wf₂ wt, (fun _ h => (List.not_mem_nil h).elim), a.slots, a.sp, a.argMem⟩

/-- The functional stage invariant restores public cdecl arguments. -/
theorem keepArgAgree {c : Cfg} {s₀ t₀ s t : State} {extra₁ extra₂ : List Region}
    (hp : Pre c s₀ extra₁) (hq : Pre c t₀ extra₂)
    (ks : Keep c s₀ (ptr s₀ 4) s) (kt : Keep c t₀ (ptr t₀ 4) t)
    (he : s₀.gpr .esp = t₀.gpr .esp) (ha : ∀ j < 5, arg s₀ j = arg t₀ j) :
    VG.X86.Taint.Agree (argτ [.esp, .edi]) s t := by
  have esp : s.gpr .esp = t.gpr .esp := ks.esp.trans (he.trans kt.esp.symm)
  have edi : s.gpr .edi = t.gpr .edi := widen32_inj (ks.scr.edi.trans
    ((congrArg (BitVec.setWidth 64) (ha 4 (by decide))).trans kt.scr.edi.symm))
  refine argAgree (argWf _ hp ks.esp ks.wr) (argWf _ hq kt.esp kt.wr) ?_ esp ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact esp
    · exact edi
  · intro j hj
    rw [ks.arg hp hj, kt.arg hq hj, ha j hj]

/-- The static-table scan's scratch region is the second writable argument. -/
theorem keepCombWf {s₀ s : State} {extra : List Region} (hp : Pre p256Comb s₀ extra)
    (ks : Keep p256Comb s₀ (ptr s₀ 4) s) : VG.X86.Taint.Wf combτ s := by
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro _
    rw [ks.wr, hp.wr]
    refine ⟨by simp [combτ, combτAt, outR, scR, size], ?_, ?_⟩
    · simpa using hp.out_sc
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · simp only [ptr, BitVec.toNat_setWidth]; omega_using [hp.out_fit]
      · simp only [ptr, BitVec.toNat_setWidth]; omega_using [hp.sc_fit]
  · intro p h
    rw [List.mem_singleton.mp h]
    change addr (s.gpr .edi) 0 = (VG.X86.Taint.region s 1).base
    simp only [VG.X86.Taint.region, ks.wr, hp.wr, List.getD_cons_succ, List.getD_cons_zero,
      addr, BitVec.add_zero]
    exact ks.scr.edi
  · intro p h; cases h
  · intro h; cases h
  · intro p h; cases h

theorem keepScratchAgree {s₀ t₀ s t : State} {extra₁ extra₂ : List Region}
    (hp : Pre p256Comb s₀ extra₁) (hq : Pre p256Comb t₀ extra₂)
    (ks : Keep p256Comb s₀ (ptr s₀ 4) s) (kt : Keep p256Comb t₀ (ptr t₀ 4) t)
    (he : s₀.gpr .esp = t₀.gpr .esp) (ha : ∀ j < 5, arg s₀ j = arg t₀ j) :
    VG.X86.Taint.Agree (scratchArgτ 5 true) s t := by
  refine scratchArgAgree (keepArgAgree hp hq ks kt he ha) (keepCombWf hp ks) (keepCombWf hq kt) ?_
  rw [ks.wr, kt.wr, hp.wr, hq.wr]
  simp only [outR, scR, ptr, ha 4 (by decide), ha 0 (by decide)]

end VG.Proof.Ecdsa.X86
