import VerifiedGarbage.Proof.Ed25519.X86.Point32.Fn
import VerifiedGarbage.Proof.Ed25519.X86.Point32.Lit
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Mont.Words32

/-!
# `vg_ed25519_r32_point_add` on x86 (32-bit): its `Verified`

Correctness under `addX86`, the facts of the shared contract of
`Spec/Ed25519/Point32.lean` stated for x86 (`fnPre`: the working space, and
the argument on the stack), from `addFn_ok` (`elemAt` reads what `F` does,
`elemAt_eq`); constant time by taint tracking (every address is `ws` or
`esp` plus a constant: only the argument, which is public, and `esp` need
be); satisfiability; and the shared contract.
-/

namespace VG.Proof.Ed25519.X86.Point32

open VG VG.X86 VG.Impl.Ed25519.X86 VG.Impl.Ed25519.X86.Point32 VG.Proof.Ed25519.X86
open VG.Impl.X25519.X86 (T)
open VG.Spec.Ed25519.Point32 (elemAt pointAt)

/-- The working space, the argument. -/
abbrev wsOf (s : State) : Addr := (arg s 0).setWidth 64

/-- The shared contract's facts about the state. -/
def fnPre (s : State) : Prop :=
  (s.gpr .esp).toNat + 4 + 4 ≤ 2 ^ 32 ∧ s.rd = [⟨argAddr s 0, 4⟩] ∧ s.wr = [⟨wsOf s, 8192⟩] ∧
    Region.Disjoint ⟨wsOf s, 8192⟩ ⟨argAddr s 0, 4⟩ ∧
    Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨wsOf s, 8192⟩ ∧ (arg s 0).toNat + 8192 ≤ 2 ^ 32

/-- The contract the function is proven against. -/
def addX86 : Contract isa where
  pre s := fnPre s ∧ elemAt s.mem (wsOf s) Spec.Ed25519.Point32.dAt = Spec.Ed25519.d
  post s s' :=
    pointAt s'.mem (wsOf s) Spec.Ed25519.Point32.pAt =
      Spec.Ed25519.pointAdd (pointAt s.mem (wsOf s) Spec.Ed25519.Point32.pAt)
        (pointAt s.mem (wsOf s) Spec.Ed25519.Point32.qAt) ∧
    Spec.Ed25519.Point32.Keeps (wsOf s) s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0

/-- The entry the contract's facts give. -/
theorem entry_of_pre {s : State} (h : fnPre s) : Entry s (arg s 0) := by
  obtain ⟨hsp, hrd, hwr, _, _, hfit⟩ := h
  exact ⟨rfl, hfit, by rw [hwr]; exact List.mem_singleton_self _,
    ⟨_, by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _), Region.contains_self _ _⟩⟩

/-- The 32-bit words of an element, as `Proof/Mont` reads them. -/
theorem num_eq_val32 (m : Mem) {x : BitVec 32} {o : Nat} (hx : x.toNat + o + 32 ≤ 2 ^ 32) :
    ∀ n ≤ 8, num (fun k => wv m x (o + 4 * k)) n = Proof.Mont.val32 m (x.setWidth 64) o n
  | 0, _ => rfl
  | n + 1, hn => by
    rw [num_succ, Proof.Mont.val32_succ, num_eq_val32 m hx n (by omega), ← Nat.pow_mul]
    refine congrArg (Proof.Mont.val32 m (x.setWidth 64) o n + 2 ^ (32 * n) * ·) ?_
    show (m.readW (addr x (o + 4 * n)) 32).toNat = _
    rw [addr_eq (by omega)]

/-- The coordinate at `o`, as `Spec` states it. -/
theorem elemAt_eq (m : Mem) {x : BitVec 32} {o : Nat} (hx : x.toNat + o + 32 ≤ 2 ^ 32) :
    elemAt m (x.setWidth 64) o = VG.Proof.X25519.X86.F m x o := by
  rw [elemAt, VG.Proof.X25519.X86.F, fe, num_eq_val32 m hx 8 (Nat.le_refl _)]
  show _ = VG.Proof.X25519.toFe (Proof.Mont.val32 m _ _ (2 * 4))
  rw [← Proof.Mont.wordsVal_eq_val32, ← Proof.Mont.read_eq_wordsVal]
  rfl

/-- The point at slot `i`, as `Spec` states it. -/
theorem pointAt_eq (m : Mem) {x : BitVec 32} (hx : x.toNat + 8192 ≤ 2 ^ 32) (i : Nat) (hi : i + 3 < 22) :
    pointAt m (x.setWidth 64) (64 + 32 * i) =
      point (env m x) ⟨i, by omega⟩ ⟨i + 1, by omega⟩ ⟨i + 2, by omega⟩ ⟨i + 3, by omega⟩ := by
  simp only [pointAt, point, env, offset, Spec.Ed25519.Point32.elemBytes]
  rw [elemAt_eq m (by omega), elemAt_eq m (by omega), elemAt_eq m (by omega), elemAt_eq m (by omega)]
  congr 2 <;> omega

/-- `Keeps` from the function's frame. -/
theorem keeps_of_frame {x : BitVec 32} (hfit : x.toNat + 8192 ≤ 2 ^ 32) {m m' : Mem}
    (h : Frame (addW x) m m') : Spec.Ed25519.Point32.Keeps (x.setWidth 64) m m' := by
  intro i hi hp hown hown'
  simp only [Spec.Ed25519.Point32.wsBytes, Spec.Ed25519.Point32.pAt, Spec.Ed25519.Point32.elemBytes] at hi hp
  refine h _ fun r hr hc => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [sub, addr_eq (by omega)] at hc
    exact Offset.disjoint (x.setWidth 64) (d := i) (n := 1) (e := 64) (k := 128) (by omega) (by omega)
      (by omega) _ (Region.contains_self _ _) hc
  · rw [sub, addr_eq (by omega)] at hc
    exact Offset.disjoint (x.setWidth 64) (d := i) (n := 1) (e := 320) (k := 256) (by omega) (by omega)
      (by omega) _ (Region.contains_self _ _) hc
  · rw [sub, addr_eq (by simp only [T]; omega)] at hc
    exact Offset.disjoint (x.setWidth 64) (d := i) (n := 1) (e := T) (k := 160) (by simp only [T]; omega)
      (by omega) (by simp only [T]; omega) _ (Region.contains_self _ _) hc

theorem add_correct (s : State) (hs : addX86.pre s) :
    ∃ t s', Exec isa addFn s t s' ∧ abiPreserved s s' ∧ addX86.post s s' := by
  obtain ⟨hp, hd⟩ := hs
  have he := entry_of_pre hp
  obtain ⟨t, s', ex, hk, hrd, hwr, hf, hv⟩ := addFn_ok he
  have hfit := he.fit
  have hret := hp.2.2.2.2.1
  refine ⟨t, s', ex, ⟨hk, ?_⟩, ?_, keeps_of_frame hfit hf⟩
  · refine hf.readW (Region.contains_self _ _) (fun r hr => hret.sub_right ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    show Region.Sub r (scR 8192 (arg s 0))
    rw [scR_eq]
    rcases hr with rfl | rfl | rfl
    · exact sub_sub hfit (Nat.zero_le _) (by decide) (by decide)
    · exact sub_sub hfit (Nat.zero_le _) (by decide) (by decide)
    · exact sub_sub hfit (Nat.zero_le _) (by simp only [T]; decide) (by simp only [T]; decide)
  · have hd' : env s.mem (arg s 0) 16 = Spec.Ed25519.d := by
      rw [← hd, wsOf, elemAt_eq _ (by simp only [Spec.Ed25519.Point32.dAt]; omega)]; rfl
    rw [show Spec.Ed25519.Point32.pAt = 64 + 32 * 0 from rfl, show Spec.Ed25519.Point32.qAt = 64 + 32 * 4 from rfl,
      pointAt_eq _ hfit 0 (by decide), pointAt_eq _ hfit 0 (by decide), pointAt_eq _ hfit 4 (by decide)]
    exact hv hd'

/-- A function running the field program `ops`, from the shared contract's facts: the calling
convention kept, the slots' values `evalOps ops` of theirs, and `Keeps`. -/
theorem fnOf_correct {ops : List FieldOp} (hd : DestsOk ops) (s : State) (hp : fnPre s) :
    ∃ t s', Exec isa (fnOf ops) s t s' ∧ abiPreserved s s' ∧
      env s'.mem (arg s 0) = evalOps ops (env s.mem (arg s 0)) ∧
      Spec.Ed25519.Point32.Keeps (wsOf s) s.mem s'.mem := by
  have he := entry_of_pre hp
  obtain ⟨t, s', ex, hk, hrd, hwr, hf, hv⟩ := fnOf_ok hd he
  have hfit := he.fit
  have hret := hp.2.2.2.2.1
  refine ⟨t, s', ex, ⟨hk, ?_⟩, hv, keeps_of_frame hfit hf⟩
  refine hf.readW (Region.contains_self _ _) (fun r hr => hret.sub_right ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  show Region.Sub r (scR 8192 (arg s 0))
  rw [scR_eq]
  rcases hr with rfl | rfl | rfl
  · exact sub_sub hfit (Nat.zero_le _) (by decide) (by decide)
  · exact sub_sub hfit (Nat.zero_le _) (by decide) (by decide)
  · exact sub_sub hfit (Nat.zero_le _) (by simp only [T]; decide) (by simp only [T]; decide)

/-- The affine addition's contract on x86. -/
def affX86 : Contract isa where
  pre := fnPre
  post s s' := (∀ q : Spec.Ed25519.Point, q.Z = 1 →
      elemAt s.mem (wsOf s) Spec.Ed25519.Point32.qAt = q.Y - q.X →
      elemAt s.mem (wsOf s) (Spec.Ed25519.Point32.qAt + Spec.Ed25519.Point32.elemBytes) = q.Y + q.X →
      elemAt s.mem (wsOf s) (Spec.Ed25519.Point32.qAt + 2 * Spec.Ed25519.Point32.elemBytes) =
        q.T * 2 * Spec.Ed25519.d →
      pointAt s'.mem (wsOf s) Spec.Ed25519.Point32.pAt =
        Spec.Ed25519.pointAdd (pointAt s.mem (wsOf s) Spec.Ed25519.Point32.pAt) q) ∧
    Spec.Ed25519.Point32.Keeps (wsOf s) s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0

/-- The doubling's contract on x86. -/
def doubleX86 : Contract isa where
  pre := fnPre
  post s s' := pointAt s'.mem (wsOf s) Spec.Ed25519.Point32.pAt =
      Spec.Ed25519.Point64.pointDouble (pointAt s.mem (wsOf s) Spec.Ed25519.Point32.pAt) ∧
    Spec.Ed25519.Point32.Keeps (wsOf s) s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0

theorem aff_correct (s : State) (hs : affX86.pre s) :
    ∃ t s', Exec isa affFn s t s' ∧ abiPreserved s s' ∧ affX86.post s s' := by
  obtain ⟨t, s', ex, ha, hv, hk⟩ := fnOf_correct pointAddAffineOps_dests s hs
  have hfit := (entry_of_pre hs).fit
  refine ⟨t, s', ex, ha, fun q hz h4 h5 h6 => ?_, hk⟩
  have el : ∀ o, o + 32 ≤ 8192 → elemAt s.mem (wsOf s) o = VG.Proof.X25519.X86.F s.mem (arg s 0) o :=
    fun o ho => elemAt_eq _ (by omega)
  rw [el _ (by decide)] at h4 h5 h6
  rw [show Spec.Ed25519.Point32.pAt = 64 + 32 * 0 from rfl, pointAt_eq _ hfit 0 (by decide),
    pointAt_eq _ hfit 0 (by decide), hv]
  refine (addAffine_formula _).trans ?_
  rw [show env s.mem (arg s 0) 4 = q.Y - q.X from h4, show env s.mem (arg s 0) 5 = q.Y + q.X from h5,
    show env s.mem (arg s 0) 6 = q.T * 2 * Spec.Ed25519.d from h6]
  exact mixedResult_eq (point (env s.mem (arg s 0)) 0 1 2 3) q hz

theorem double_correct (s : State) (hs : doubleX86.pre s) :
    ∃ t s', Exec isa doubleFn s t s' ∧ abiPreserved s s' ∧ doubleX86.post s s' := by
  obtain ⟨t, s', ex, ha, hv, hk⟩ := fnOf_correct pointDoubleRfcOps_dests s hs
  have hfit := (entry_of_pre hs).fit
  refine ⟨t, s', ex, ha, ?_, hk⟩
  rw [show Spec.Ed25519.Point32.pAt = 64 + 32 * 0 from rfl, pointAt_eq _ hfit 0 (by decide),
    pointAt_eq _ hfit 0 (by decide), hv]
  exact dbl_eval _

/-! ## Constant time -/

/-- The analysis starts with `esp` and the 4 bytes of the argument public. -/
def fnτ : VG.X86.Taint.T := { regs := .ofList [.esp], flags := false, argLen := 4 + 4 }

theorem fn_wf {s : State} (h : fnPre s) : VG.X86.Taint.Wf fnτ s := by
  obtain ⟨hsp, _, hwr, hdis, hret, _⟩ := h
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨by simp only [fnτ]; omega, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim⟩
  rw [hwr]
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact VG.X86.Taint.frame_disjoint (n := 4) hsp hret hdis.symm

/-- Two states of the precondition whose `esp` and argument agree agree on
what `fnτ` says is public. -/
theorem fn_agree {s₁ s₂ : State} (h₁ : fnPre s₁) (h₂ : fnPre s₂)
    (hesp : s₁.gpr .esp = s₂.gpr .esp) (ha : arg s₁ 0 = arg s₂ 0) :
    VG.X86.Taint.Agree fnτ s₁ s₂ := by
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, fn_wf h₁, fn_wf h₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [fnτ, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · simp only [fnτ] at hk
    rw [show VG.X86.Taint.depth fnτ.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (n := 4 + 4) (by have := h₁.1; omega) h4 hk,
      VG.X86.Taint.argByte_eq (n := 4 + 4) (by have := h₂.1; omega) h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    have e : (k - 4) / 4 = 0 := by omega
    rw [e]
    exact congrArg _ ha

theorem addFn_check : ∃ h, (taint.check fnτ addFn h).isSome = true := ⟨_, by taint_decide⟩

theorem add_agree (s₁ s₂ : State) (h₁ : addX86.pre s₁) (h₂ : addX86.pre s₂) (hp : addX86.pub s₁ s₂) :
    VG.X86.Taint.Agree fnτ s₁ s₂ :=
  fn_agree h₁.1 h₂.1 hp.1 hp.2

theorem addFn_ct : ConstantTime isa addX86.pre addX86.pub addFn :=
  let ⟨_, hc⟩ := addFn_check
  VG.Taint.constantTime (A := taint) fnτ add_agree hc

theorem affFn_ct : ConstantTime isa affX86.pre affX86.pub affFn :=
  VG.Taint.constantTime (A := taint) fnτ (fun _ _ h₁ h₂ hp => fn_agree h₁ h₂ hp.1 hp.2) (by taint_decide)

theorem doubleFn_ct : ConstantTime isa doubleX86.pre doubleX86.pub doubleFn :=
  VG.Taint.constantTime (A := taint) fnτ (fun _ _ h₁ h₂ hp => fn_agree h₁ h₂ hp.1 hp.2) (by taint_decide)

/-! ## The shared contract -/

/-- `d`'s value. -/
def dLit : Nat := 37095705934669439343138083508754565189542113879843219016388785533085940283555

/-- The memory of `fnSat`: its argument `0x1000`, and `d` in slot 16. -/
def fnMem : Mem := fun a => if a = 0x8005 then 0x10 else
  if 0x1240 ≤ a.toNat ∧ a.toNat < 0x1260 then BitVec.ofNat 8 (dLit / 256 ^ (a.toNat - 0x1240)) else 0

/-- A state with the working space at `0x1000`, holding `d` in slot 16, and
its argument at `0x8004`. -/
def fnSat : State where
  gpr r := match r with
    | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := fnMem
  rd := [⟨0x8004, 4⟩]
  wr := [⟨0x1000, 8192⟩]

theorem fnMem_d : (fnMem.read ((0x1000 : Addr) + BitVec.ofNat 64 576) 32).toNat = dLit := by
  decide +kernel

theorem d_eq : Spec.Ed25519.d = Fin.ofNat Spec.X25519.P dLit := by decide +kernel

theorem fnSat_d : elemAt fnSat.mem (0x1000 : Addr) Spec.Ed25519.Point32.dAt = Spec.Ed25519.d := by
  rw [d_eq, elemAt]
  exact congrArg _ fnMem_d

theorem addX86_implies : addX86.Implies (Spec.Ed25519.Point32.addContract X86.abi) := by
  have a0 : arg fnSat 0 = 0x1000 := by decide
  have e : argAddr fnSat 0 = 0x8004 := by decide
  have esp : fnSat.gpr .esp = 0x8000 := rfl
  exact
    { pre := by sig_implies_pre [Spec.Ed25519.Point32.addContract, Spec.Ed25519.Point32.sig, addX86, fnPre,
        wsOf, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      post := by sig_implies_post [Spec.Ed25519.Point32.addContract, Spec.Ed25519.Point32.sig, addX86, fnPre,
        wsOf, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      pub := by sig_implies_pub [Spec.Ed25519.Point32.addContract, Spec.Ed25519.Point32.sig, addX86, fnPre,
        wsOf, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      sat := by
        refine ⟨fnSat, ?_⟩
        sig_pre [Spec.Ed25519.Point32.addContract, Spec.Ed25519.Point32.sig, addX86, fnPre, wsOf, X86.abi,
          X86.argSlots, X86.argVal, X86.argBytes]
        sig_and_intros
        all_goals first
          | exact fnSat_d
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | (intro a h₁ h₂
             simp only [Region.Contains, a0, e, esp] at h₁ h₂
             bv_omega) }

theorem addFn_verified : Verified X86.target addFn (Spec.Ed25519.Point32.addContract X86.abi) :=
  Verified.of_correct add_correct addFn_ct addX86_implies

theorem affX86_implies : affX86.Implies (Spec.Ed25519.Point32.addAffineContract X86.abi) := by
  have a0 : arg fnSat 0 = 0x1000 := by decide
  have e : argAddr fnSat 0 = 0x8004 := by decide
  have esp : fnSat.gpr .esp = 0x8000 := rfl
  exact
    { pre := by sig_implies_pre [Spec.Ed25519.Point32.addAffineContract, Spec.Ed25519.Point32.sig, affX86,
        fnPre, wsOf, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      post := by sig_implies_post [Spec.Ed25519.Point32.addAffineContract, Spec.Ed25519.Point32.sig, affX86,
        fnPre, wsOf, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      pub := by sig_implies_pub [Spec.Ed25519.Point32.addAffineContract, Spec.Ed25519.Point32.sig, affX86,
        fnPre, wsOf, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      sat := by
        refine ⟨fnSat, ?_⟩
        sig_pre [Spec.Ed25519.Point32.addAffineContract, Spec.Ed25519.Point32.sig, affX86, fnPre, wsOf,
          X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | (intro a h₁ h₂
             simp only [Region.Contains, a0, e, esp] at h₁ h₂
             bv_omega) }

theorem doubleX86_implies : doubleX86.Implies (Spec.Ed25519.Point32.doubleContract X86.abi) := by
  have a0 : arg fnSat 0 = 0x1000 := by decide
  have e : argAddr fnSat 0 = 0x8004 := by decide
  have esp : fnSat.gpr .esp = 0x8000 := rfl
  exact
    { pre := by sig_implies_pre [Spec.Ed25519.Point32.doubleContract, Spec.Ed25519.Point32.sig, doubleX86,
        fnPre, wsOf, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      post := by sig_implies_post [Spec.Ed25519.Point32.doubleContract, Spec.Ed25519.Point32.sig, doubleX86,
        fnPre, wsOf, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      pub := by sig_implies_pub [Spec.Ed25519.Point32.doubleContract, Spec.Ed25519.Point32.sig, doubleX86,
        fnPre, wsOf, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      sat := by
        refine ⟨fnSat, ?_⟩
        sig_pre [Spec.Ed25519.Point32.doubleContract, Spec.Ed25519.Point32.sig, doubleX86, fnPre, wsOf,
          X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | (intro a h₁ h₂
             simp only [Region.Contains, a0, e, esp] at h₁ h₂
             bv_omega) }

theorem affFn_verified : Verified X86.target affFn (Spec.Ed25519.Point32.addAffineContract X86.abi) :=
  Verified.of_correct aff_correct affFn_ct affX86_implies

theorem doubleFn_verified : Verified X86.target doubleFn (Spec.Ed25519.Point32.doubleContract X86.abi) :=
  Verified.of_correct double_correct doubleFn_ct doubleX86_implies

end VG.Proof.Ed25519.X86.Point32
