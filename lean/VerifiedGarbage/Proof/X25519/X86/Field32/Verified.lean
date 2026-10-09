import VerifiedGarbage.Proof.X25519.X86.Field32.Fn
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Mont.Words32

/-!
# `vg_gf25519_r32_mul` on x86 (32-bit): its `Verified`

Correctness under `mulX86`, the facts of the shared contract of
`Spec/X25519/Field32.lean` stated for x86 (`fnPre`: the working space, and
the arguments on the stack), from `mulFn_ok` (`valAt` reads what `fe` does,
`valAt_eq`); constant time by taint tracking (the branch is on the
offsets, and every address is `ws`, `ws` plus an offset, or `esp`, plus a
constant: only the arguments, which are public, and `esp` need be);
satisfiability; and the shared contract.
-/

namespace VG.Proof.X25519.X86.Field32

open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.X25519.X86.Field32 VG.Proof.X25519.X86

/-- The working space, the first argument. -/
abbrev wsOf (s : State) : Addr := (arg s 0).setWidth 64

/-- The shared contract's facts about the state. -/
def fnPre (s : State) : Prop :=
  (s.gpr .esp).toNat + 4 + 16 ≤ 2 ^ 32 ∧ s.rd = [⟨argAddr s 0, 16⟩] ∧ s.wr = [⟨wsOf s, 4096⟩] ∧
    Region.Disjoint ⟨wsOf s, 4096⟩ ⟨argAddr s 0, 16⟩ ∧
    Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨wsOf s, 4096⟩ ∧ (arg s 0).toNat + 4096 ≤ 2 ^ 32

/-- The contract the function is proven against. -/
def mulX86 : Contract isa where
  pre s := fnPre s ∧ Spec.X25519.Field32.Fits (arg s 1) ∧ Spec.X25519.Field32.Fits (arg s 2) ∧
    Spec.X25519.Field32.Fits (arg s 3)
  post s s' :=
    Spec.X25519.Field32.valAt s'.mem (wsOf s) (arg s 1) % Spec.X25519.P =
      Spec.X25519.Field32.valAt s.mem (wsOf s) (arg s 2) * Spec.X25519.Field32.valAt s.mem (wsOf s) (arg s 3) %
        Spec.X25519.P ∧
    Spec.X25519.Field32.Keeps (wsOf s) (arg s 1) s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧
    arg s₁ 2 = arg s₂ 2 ∧ arg s₁ 3 = arg s₂ 3

theorem fits_toNat {o : BitVec 32} (h : Spec.X25519.Field32.Fits o) : o.toNat + 32 ≤ 768 := h

/-- The entry the contract's facts give. -/
theorem entry_of_pre {s : State} (h : mulX86.pre s) :
    Entry s (arg s 0) (arg s 1).toNat (arg s 2).toNat (arg s 3).toNat := by
  obtain ⟨⟨hsp, hrd, hwr, hdis, hret, hfit⟩, ho, ha, hb⟩ := h
  have cont : ∀ i < 4, (⟨argAddr s 0, 16⟩ : Region).Contains (argAddr s i) 4 := fun i hi =>
    VG.Proof.X25519.X86.sub_contains (x := s.gpr .esp) (a := 4) (k := 16) (by omega) (by omega)
      (by omega) (by decide)
  refine ⟨rfl, hfit, by rw [hwr]; exact List.mem_singleton_self _, fun i hi => ?_, fun i hi => ?_, hret,
    by simp, by simp, by simp, fits_toNat ho, fits_toNat ha, fits_toNat hb⟩
  · exact ⟨_, by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _), cont i hi⟩
  · refine hdis.symm.sub_left fun y hy => (cont i hi).byte ?_
    simp only [Region.Contains] at hy; omega

/-- The 32-bit words of an element, as `Proof/Mont` reads them. -/
theorem num_eq_val32 (m : Mem) {x : BitVec 32} {o : Nat} (hx : x.toNat + o + 32 ≤ 2 ^ 32) :
    ∀ n ≤ 8, num (fun k => wv m x (o + 4 * k)) n = Proof.Mont.val32 m (x.setWidth 64) o n
  | 0, _ => rfl
  | n + 1, hn => by
    rw [num_succ, Proof.Mont.val32_succ, num_eq_val32 m hx n (by omega), ← Nat.pow_mul]
    congr 2
    show (m.readW (addr x (o + 4 * n)) 32).toNat = _
    rw [addr_eq (by omega)]

/-- The value of an element, as `Spec` states it. -/
theorem valAt_eq (m : Mem) {x : BitVec 32} {o : BitVec 32} (hx : x.toNat + o.toNat + 32 ≤ 2 ^ 32) :
    Spec.X25519.Field32.valAt m (x.setWidth 64) o = fe m x o.toNat := by
  rw [fe, num_eq_val32 m hx 8 (Nat.le_refl _)]
  show _ = Proof.Mont.val32 m _ _ (2 * 4)
  rw [← Proof.Mont.wordsVal_eq_val32, ← Proof.Mont.read_eq_wordsVal]
  rfl

/-- `Keeps` from the function's frame. -/
theorem keeps_of_frame {x : BitVec 32} (hfit : x.toNat + 4096 ≤ 2 ^ 32) {o : BitVec 32}
    (ho : o.toNat + 32 ≤ 768) {m m' : Mem} (h : Frame [sub x o.toNat 32, sub x opA 256] m m') :
    Spec.X25519.Field32.Keeps (x.setWidth 64) o m m' := by
  intro i hi hown hout
  simp only [Spec.X25519.Field32.wsBytes, Spec.X25519.Field32.ownAt, Spec.X25519.Field32.ownEnd,
    Spec.X25519.Field32.elemBytes] at hi hown hout
  refine h _ fun r hr hc => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [sub, addr_eq (by omega)] at hc
    exact Offset.disjoint (x.setWidth 64) (d := i) (n := 1) (e := o.toNat) (k := 32) (by omega) (by omega)
      (by omega) _ (Region.contains_self _ _) hc
  · rw [sub, addr_eq (by simp only [opA]; omega)] at hc
    exact Offset.disjoint (x.setWidth 64) (d := i) (n := 1) (e := opA) (k := 256)
      (by simp only [opA]; omega) (by omega) (by simp only [opA]; omega) _ (Region.contains_self _ _) hc

theorem mul_correct (s : State) (hs : mulX86.pre s) :
    ∃ t s', Exec isa mulFn s t s' ∧ abiPreserved s s' ∧ mulX86.post s s' := by
  have he := entry_of_pre hs
  obtain ⟨t, s', ex, hk, hrd, hwr, hf, hv⟩ := mulFn_ok he
  have hfit := he.fit
  refine ⟨t, s', ex, ⟨hk, ?_⟩, ?_, keeps_of_frame hfit he.ho hf⟩
  · refine frame_out hf (fun r hr => ?_) he.ret
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sub_ws hfit (by have := he.ho; omega) (by decide)
    · exact sub_ws hfit (by decide) (by decide)
  · rw [valAt_eq _ (by have := he.ho; omega), valAt_eq _ (by have := he.ha; omega),
      valAt_eq _ (by have := he.hb; omega)]
    exact hv

/-! ## Constant time -/

/-- The analysis starts with `esp` and the 16 bytes of arguments public. -/
def fnτ : VG.X86.Taint.T := { regs := .ofList [.esp], flags := false, argLen := 4 + 16 }

theorem fn_wf {s : State} (h : fnPre s) : VG.X86.Taint.Wf fnτ s := by
  obtain ⟨hsp, _, hwr, hdis, hret, _⟩ := h
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨by simp only [fnτ]; omega, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim⟩
  rw [hwr]
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact VG.X86.Taint.frame_disjoint (n := 16) hsp hret hdis.symm

/-- Two states of the precondition whose `esp` and arguments agree agree on
what `fnτ` says is public. -/
theorem fn_agree {s₁ s₂ : State} (h₁ : fnPre s₁) (h₂ : fnPre s₂)
    (hesp : s₁.gpr .esp = s₂.gpr .esp) (ha : ∀ i, 4 * i < 16 → arg s₁ i = arg s₂ i) :
    VG.X86.Taint.Agree fnτ s₁ s₂ := by
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, fn_wf h₁, fn_wf h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [fnτ, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · simp only [fnτ] at hk
    rw [show VG.X86.Taint.depth fnτ.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (n := 4 + 16) (by have := h₁.1; omega) h4 hk,
      VG.X86.Taint.argByte_eq (n := 4 + 16) (by have := h₂.1; omega) h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (ha _ (by omega))

theorem mulFn_check : ∃ h, (taint.check fnτ mulFn h).isSome = true := ⟨_, by taint_decide⟩

theorem mul_agree (s₁ s₂ : State) (h₁ : mulX86.pre s₁) (h₂ : mulX86.pre s₂) (hp : mulX86.pub s₁ s₂) :
    VG.X86.Taint.Agree fnτ s₁ s₂ := by
  obtain ⟨e, a0, a1, a2, a3⟩ := hp
  refine fn_agree h₁.1 h₂.1 e fun i hi => ?_
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl
  exacts [a0, a1, a2, a3]

theorem mulFn_ct : ConstantTime isa mulX86.pre mulX86.pub mulFn :=
  let ⟨_, hc⟩ := mulFn_check
  VG.Taint.constantTime (A := taint) fnτ mul_agree hc

/-! ## The shared contract -/

/-- A state with the working space at `0x1000` and the offsets 0, its
arguments at `0x8004`. -/
def fnSat : State where
  gpr r := match r with
    | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else 0
  rd := [⟨0x8004, 16⟩]
  wr := [⟨0x1000, 4096⟩]

theorem mulX86_implies : mulX86.Implies (Spec.X25519.Field32.mulContract X86.abi) := by
  have a0 : arg fnSat 0 = 0x1000 := by decide
  have a1 : arg fnSat 1 = 0 := by decide
  have a2 : arg fnSat 2 = 0 := by decide
  have a3 : arg fnSat 3 = 0 := by decide
  have e : argAddr fnSat 0 = 0x8004 := by decide
  have esp : fnSat.gpr .esp = 0x8000 := rfl
  exact
    { pre := by sig_implies_pre [Spec.X25519.Field32.mulContract, Spec.X25519.Field32.sig, mulX86, fnPre, wsOf,
        X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      post := by sig_implies_post [Spec.X25519.Field32.mulContract, Spec.X25519.Field32.sig, mulX86, fnPre, wsOf,
        X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      pub := by sig_implies_pub [Spec.X25519.Field32.mulContract, Spec.X25519.Field32.sig, mulX86, fnPre, wsOf,
        X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      sat := by
        refine ⟨fnSat, ?_⟩
        sig_pre [Spec.X25519.Field32.mulContract, Spec.X25519.Field32.sig, mulX86, fnPre, wsOf, X86.abi,
          X86.argSlots, X86.argVal, X86.argBytes]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | (intro a h₁ h₂
             simp only [Region.Contains, a0, a1, a2, a3, e, esp] at h₁ h₂
             bv_omega) }

theorem mulFn_verified : Verified X86.target mulFn (Spec.X25519.Field32.mulContract X86.abi) :=
  Verified.of_correct mul_correct mulFn_ct mulX86_implies

end VG.Proof.X25519.X86.Field32
