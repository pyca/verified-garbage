import VerifiedGarbage.Proof.X25519.X86.Field32.Fn
import VerifiedGarbage.Proof.X25519.X86.Field32.Lit
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Mont.Words32

/-!
# `vg_gf25519_r32_pow250` on x86 (32-bit): its `Verified`

Correctness under `powX86`, the facts of the shared contract of
`Spec/X25519/Field32.lean` stated for x86 (`fnPre`: the working space, and
the argument on the stack), from `pow250Fn_ok` (`valAt` reads what `fe`
does, `valAt_eq`); constant time by taint tracking (every address is `ws`
or `esp` plus a constant, and the only branches are on the counter: only the
argument, which is public, and `esp` need be); satisfiability; and the
shared contract.
-/

namespace VG.Proof.X25519.X86.Field32

open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.X25519.X86.Field32 VG.Proof.X25519.X86 VG.Spec.X25519
open VG.Proof.X25519 (pw)

/-- The working space, the argument. -/
abbrev wsOf (s : State) : Addr := (arg s 0).setWidth 64

/-- The shared contract's facts about the state. -/
def fnPre (s : State) : Prop :=
  (s.gpr .esp).toNat + 4 + 4 ≤ 2 ^ 32 ∧ s.rd = [⟨argAddr s 0, 4⟩] ∧ s.wr = [⟨wsOf s, 4096⟩] ∧
    Region.Disjoint ⟨wsOf s, 4096⟩ ⟨argAddr s 0, 4⟩ ∧
    Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨wsOf s, 4096⟩ ∧ (arg s 0).toNat + 4096 ≤ 2 ^ 32

/-- The contract the function is proven against. -/
def powX86 : Contract isa where
  pre s := fnPre s
  post s s' :=
    Spec.X25519.Field32.valAt s'.mem (wsOf s) (BitVec.ofNat 32 Spec.X25519.Field32.oAt) % P =
      Spec.X25519.Field32.valAt s.mem (wsOf s) (BitVec.ofNat 32 Spec.X25519.Field32.aAt) ^ (2 ^ 250 - 1) % P ∧
    Spec.X25519.Field32.valAt s'.mem (wsOf s) (BitVec.ofNat 32 Spec.X25519.Field32.eAt) % P =
      Spec.X25519.Field32.valAt s.mem (wsOf s) (BitVec.ofNat 32 Spec.X25519.Field32.aAt) ^ 11 % P ∧
    Spec.X25519.Field32.Keeps₂ (wsOf s) s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0

/-- The entry the contract's facts give. -/
theorem entry_of_pre {s : State} (h : fnPre s) : Entry s (arg s 0) := by
  obtain ⟨_, hrd, hwr, _, _, hfit⟩ := h
  exact ⟨rfl, hfit, by rw [hwr]; exact List.mem_singleton_self _,
    ⟨_, by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _), Region.contains_self _ _⟩⟩

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
theorem valAt_eq (m : Mem) {x : BitVec 32} {o : Nat} (ho : o < 2 ^ 32) (hx : x.toNat + o + 32 ≤ 2 ^ 32) :
    Spec.X25519.Field32.valAt m (x.setWidth 64) (BitVec.ofNat 32 o) = fe m x o := by
  rw [fe, num_eq_val32 m hx 8 (Nat.le_refl _), Spec.X25519.Field32.valAt, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ho]
  show _ = Proof.Mont.val32 m _ _ (2 * 4)
  rw [← Proof.Mont.wordsVal_eq_val32, ← Proof.Mont.read_eq_wordsVal]
  rfl

/-- A power, as the contract states it. -/
theorem val_of_F {m m' : Mem} {x : BitVec 32} {o a e : Nat} (h : F m' x o = pw (F m x a) e) :
    fe m' x o % P = fe m x a ^ e % P := by
  have := congrArg Fin.val h
  simp only [F, VG.Proof.X25519.toFe, pw, Fin.val_ofNat] at this
  rw [this, ← Nat.pow_mod]

/-- `Keeps₂` from the function's frame. -/
theorem keeps_of_frame {x : BitVec 32} (hfit : x.toNat + 4096 ≤ 2 ^ 32) {m m' : Mem}
    (h : Frame (powW x) m m') : Spec.X25519.Field32.Keeps₂ (x.setWidth 64) m m' := by
  intro i hi hown
  simp only [Spec.X25519.Field32.wsBytes, Spec.X25519.Field32.eAt, Spec.X25519.Field32.ownEnd] at hi hown
  refine h _ fun r hr hc => ?_
  rw [List.mem_singleton.mp hr, sub, addr_eq (by omega)] at hc
  exact Offset.disjoint (x.setWidth 64) (d := i) (n := 1) (e := 512) (k := 512) (by omega) (by omega)
    (by omega) _ (Region.contains_self _ _) hc

theorem pow_correct (s : State) (hs : powX86.pre s) :
    ∃ t s', Exec isa pow250Fn s t s' ∧ abiPreserved s s' ∧ powX86.post s s' := by
  have he := entry_of_pre hs
  obtain ⟨t, s', ex, hk, hrd, hwr, hf, h1, h0⟩ := pow250Fn_ok he
  replace h1 : F s'.mem (arg s 0) Spec.X25519.Field32.oAt = _ := h1
  replace h0 : F s'.mem (arg s 0) Spec.X25519.Field32.eAt = _ := h0
  have hfit := he.fit
  have hret := hs.2.2.2.2.1
  refine ⟨t, s', ex, ⟨hk, ?_⟩, ?_, ?_, keeps_of_frame hfit hf⟩
  · refine hf.readW (Region.contains_self _ _) (fun r hr => hret.sub_right ?_) (by decide)
    rw [List.mem_singleton.mp hr]
    show Region.Sub _ (scR 4096 (arg s 0))
    rw [scR_eq]
    exact sub_sub hfit (Nat.zero_le _) (by decide) (by decide)
  · rw [valAt_eq _ (by decide) (by simp only [Spec.X25519.Field32.oAt]; omega),
      valAt_eq _ (by decide) (by simp only [Spec.X25519.Field32.aAt]; omega)]
    have hh := val_of_F h1
    exact hh
  · rw [valAt_eq _ (by decide) (by simp only [Spec.X25519.Field32.eAt]; omega),
      valAt_eq _ (by decide) (by simp only [Spec.X25519.Field32.aAt]; omega)]
    have hh := val_of_F h0
    exact hh

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
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
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

theorem pow250Fn_check : ∃ h, (taint.check fnτ pow250Fn h).isSome = true := ⟨_, by taint_decide⟩

theorem pow_agree (s₁ s₂ : State) (h₁ : powX86.pre s₁) (h₂ : powX86.pre s₂) (hp : powX86.pub s₁ s₂) :
    VG.X86.Taint.Agree fnτ s₁ s₂ :=
  fn_agree h₁ h₂ hp.1 hp.2

theorem pow250Fn_ct : ConstantTime isa powX86.pre powX86.pub pow250Fn :=
  let ⟨_, hc⟩ := pow250Fn_check
  VG.Taint.constantTime (A := taint) fnτ pow_agree hc

/-! ## The shared contract -/

/-- A state with the working space at `0x1000` and its argument at `0x8004`. -/
def fnSat : State where
  gpr r := match r with
    | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else 0
  rd := [⟨0x8004, 4⟩]
  wr := [⟨0x1000, 4096⟩]

theorem powX86_implies : powX86.Implies (Spec.X25519.Field32.pow250Contract X86.abi) := by
  have a0 : arg fnSat 0 = 0x1000 := by decide
  have e : argAddr fnSat 0 = 0x8004 := by decide
  have esp : fnSat.gpr .esp = 0x8000 := rfl
  exact
    { pre := by sig_implies_pre [Spec.X25519.Field32.pow250Contract, Spec.X25519.Field32.pow250Sig, powX86,
        fnPre, wsOf, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      post := by sig_implies_post [Spec.X25519.Field32.pow250Contract, Spec.X25519.Field32.pow250Sig, powX86,
        fnPre, wsOf, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      pub := by sig_implies_pub [Spec.X25519.Field32.pow250Contract, Spec.X25519.Field32.pow250Sig, powX86,
        fnPre, wsOf, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      sat := by
        refine ⟨fnSat, ?_⟩
        sig_pre [Spec.X25519.Field32.pow250Contract, Spec.X25519.Field32.pow250Sig, powX86, fnPre, wsOf,
          X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | (intro a h₁ h₂
             simp only [Region.Contains, a0, e, esp] at h₁ h₂
             bv_omega) }

theorem pow250Fn_verified : Verified X86.target pow250Fn (Spec.X25519.Field32.pow250Contract X86.abi) :=
  Verified.of_correct pow_correct pow250Fn_ct powX86_implies

end VG.Proof.X25519.X86.Field32
