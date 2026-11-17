module

public import VerifiedGarbage.Proof.Dsa.Arm.GenerateCompute
import VerifiedGarbage.Proof.Dsa.Arm.Dispatch
public import VerifiedGarbage.Proof.Dsa.Arm.SignCorrect
import VerifiedGarbage.Proof.Dsa.Derive
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Dsa.Arm.Entry
public import VerifiedGarbage.Proof.Dsa.Arm.PublicKey
public import VerifiedGarbage.Proof.Dsa.Arm.Shape
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.Dsa.Arm.Generate
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Spec.Dsa.Derive
public import VerifiedGarbage.Proof.Dsa.Contract

/-! ### `Dsa.Arm.GenerateEntry`, which this module and modules that import it used -/

section

/-! ### `Dsa.Arm.GenerateContract`, which this module and modules that import it used -/

section

/-!
# DSA domain checks and key derivation on 32-bit ARM: the contracts

Untrusted: everything here is checked by Lean. The facts of
`Proof.Dsa.checkParametersContract`, `Spec.Dsa.deriveKeyContract` and
`Spec.Dsa.deriveKeyDomainCheckedContract` for 32-bit ARM, by name. `vg_dsa_check_parameters(params, params_len, p_len,
q_len, scratch, scratch_len)` has its first four arguments in `r0`–`r3`
and the others on the stack; `vg_dsa_derive_key(out, out_len, params,
params_len, p_len, x, q_len, scratch, scratch_len)` likewise.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm

/-! ## Checking a domain -/

/-- What `vg_dsa_check_parameters` needs: `(params = r0, params_len = r1,
p_len = r2, q_len = r3, scratch = [sp], scratch_len = [sp + 4])`. -/
def checkPre (s : State) : Prop :=
  let params : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
  let scratch : Region := ⟨State.addr (arg s 0), (arg s 1).toNat * 8⟩
  let args : Region := ⟨State.addr s.sp, 8⟩
  s.sp.toNat + 8 ≤ 2 ^ 32 ∧ s.rd = [params, args] ∧ s.wr = [scratch] ∧
    params.Disjoint scratch ∧ scratch.Disjoint args ∧
    (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32 ∧ (arg s 0).toNat + (arg s 1).toNat * 8 ≤ 2 ^ 32 ∧
    Spec.Dsa.lengthsValid (s.gpr .r2).toNat (s.gpr .r3).toNat ∧
    (s.gpr .r1).toNat = 2 * (s.gpr .r2).toNat + (s.gpr .r3).toNat ∧
    Spec.Dsa.scratchWords (s.gpr .r2).toNat ≤ (arg s 1).toNat

/-- The bytes of the domain. -/
abbrev checkParams (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat

/-- The result of the check in a state. -/
abbrev checkRes (s : State) : Bool :=
  Spec.Dsa.checkParametersBytes (s.gpr .r2).toNat (s.gpr .r3).toNat (checkParams s)

def checkArm : Contract isa where
  pre := checkPre
  post s s' := (BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0)).toNat = if checkRes s then 1 else 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ (checkParams s₁).map (·.toNat) = (checkParams s₂).map (·.toNat) ∧
    s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ ∀ i < 2, arg s₁ i = arg s₂ i

/-! ## Deriving a key -/

/-- What `vg_dsa_derive_key` needs: `(out = r0, out_len = r1, params = r2,
params_len = r3, p_len = [sp], x = [sp + 4], q_len = [sp + 8],
scratch = [sp + 12], scratch_len = [sp + 16])`. -/
def derivePre (s : State) : Prop :=
  let out : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
  let params : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
  let x : Region := ⟨State.addr (arg s 1), (arg s 2).toNat⟩
  let scratch : Region := ⟨State.addr (arg s 3), (arg s 4).toNat * 8⟩
  let args : Region := ⟨State.addr s.sp, 20⟩
  s.sp.toNat + 20 ≤ 2 ^ 32 ∧ s.rd = [params, x, args] ∧ s.wr = [out, scratch] ∧
    out.Disjoint params ∧ out.Disjoint x ∧ out.Disjoint scratch ∧ out.Disjoint args ∧
    params.Disjoint scratch ∧ x.Disjoint scratch ∧ scratch.Disjoint args ∧
    (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
    (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32 ∧ (arg s 3).toNat + (arg s 4).toNat * 8 ≤ 2 ^ 32 ∧
    Spec.Dsa.lengthsValid (arg s 0).toNat (arg s 2).toNat ∧
    (s.gpr .r1).toNat = 3 * (arg s 0).toNat + 2 * (arg s 2).toNat ∧
    (s.gpr .r3).toNat = 2 * (arg s 0).toNat + (arg s 2).toNat ∧
    Spec.Dsa.scratchWords (arg s 0).toNat ≤ (arg s 4).toNat

/-- The bytes of the domain and of x. -/
abbrev deriveParams (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat
abbrev deriveX (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (State.addr (arg s 1)) (arg s 2).toNat

/-- The result of the derivation in a state. -/
abbrev deriveRes (s : State) : Option (List Byte) :=
  Spec.Dsa.deriveKeyBytes (arg s 0).toNat (arg s 2).toNat (deriveParams s) (deriveX s)

/-- What derivation may leak: the domain and whether it succeeds. -/
abbrev deriveLeak (s : State) : List Nat :=
  (deriveParams s).map (·.toNat) ++ [Spec.Dsa.signStatus (deriveRes s)]

def deriveArm : Contract isa where
  pre := derivePre
  post s s' := (BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0)).toNat = Spec.Dsa.signStatus (deriveRes s) ∧
    Spec.Rsa.bytesAt s'.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat =
      (deriveRes s).getD (List.replicate (s.gpr .r1).toNat 0)
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ deriveLeak s₁ = deriveLeak s₂ ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧
    s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ ∀ i < 5, arg s₁ i = arg s₂ i

/-- `deriveArm` for a domain whose exact bytes pass the domain check, as
`Spec.Dsa.deriveKeyDomainCheckedContract` restates `deriveKeyContract`. -/
def deriveCheckedArm : Contract isa :=
  { deriveArm with
    pre := fun s => derivePre s ∧
      Spec.Dsa.checkParametersBytes (arg s 0).toNat (arg s 2).toNat (deriveParams s) = true }

end VG.Proof.Dsa.Arm

end

end

/-!
# DSA domain checks and key derivation on 32-bit ARM: the entries

As signing's (`Install.lean`): `checkEntry_ok` and `deriveEntry_ok` leave
`r12` at `scratch`, the registers to restore at its offset 128, and the
arguments and the components' pointers at their fields (`Installed`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd)

/-- The fields of the domain check. -/
abbrev checkFields (s : State) : Fields :=
  [(64, s.gpr .r0), (100, s.gpr .r2), (104, s.gpr .r3), (108, s.gpr .r2),
    (68, s.gpr .r0 + s.gpr .r2), (72, s.gpr .r0 + s.gpr .r2 + s.gpr .r3),
    (76, s.gpr .r0 + s.gpr .r2 + s.gpr .r3 + s.gpr .r2), (80, s.gpr .r0 + s.gpr .r2 + s.gpr .r3 + s.gpr .r2 + s.gpr .r2)]

/-- The fields of derivation. -/
abbrev deriveFields (s : State) : Fields :=
  [(96, s.gpr .r0), (64, s.gpr .r2), (100, arg s 0), (88, arg s 1), (104, arg s 2), (108, arg s 0),
    (68, s.gpr .r2 + arg s 0), (72, s.gpr .r2 + arg s 0 + arg s 2), (76, s.gpr .r2 + arg s 0 + arg s 2 + arg s 0),
    (80, s.gpr .r2 + arg s 0 + arg s 2 + arg s 0 + arg s 0)]

theorem checkFields_ok (s : State) : FieldsOk (checkFields s) := by
  intro f hf
  simp only [checkFields, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem deriveFields_ok (s : State) : FieldsOk (deriveFields s) := by
  intro f hf
  simp only [deriveFields, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- The arguments of the domain check at their fields. -/
theorem checkArgs_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (hz : 164 ≤ size) :
    WP isa (.block (Generate.checkArguments.flatMap Entry.saveArgument)) s fun t =>
      t.mem.readW (off base 64) 32 = s.gpr .r0 ∧ t.mem.readW (off base 100) 32 = s.gpr .r2 ∧
      t.mem.readW (off base 104) 32 = s.gpr .r3 ∧ t.mem.readW (off base 108) 32 = s.gpr .r2 ∧
      Rest [] s t ∧ Outside base 64 48 s.mem t.mem ∧ t.sp = s.sp := by
  have nw := hs.nowrap
  show WP isa (.block [.str .r0 .r12 64, .str .r2 .r12 100, .str .r3 .r12 104, .str .r2 .r12 108]) s _
  refine wp_str12 hs (by decide) (by omega_arith) fun s₁ m₁ => ?_
  refine wp_str12 (hs.of_mupd m₁) (by decide) (by omega_arith) fun s₂ m₂ => ?_
  refine wp_str12 ((hs.of_mupd m₁).of_mupd m₂) (by decide) (by omega_arith) fun s₃ m₃ => ?_
  refine wp_str12 (((hs.of_mupd m₁).of_mupd m₂).of_mupd m₃) (by decide) (by omega_arith) fun t m₄ => WP.block_nil ?_
  obtain v₁ : s₁.mem.readW (off base 64) 32 = s.gpr .r0 := by rw [m₁.mem]; exact readW_off_self _ _ _ _
  obtain v₂ : s₂.mem.readW (off base 100) 32 = s.gpr .r2 := by rw [m₂.mem, m₁.gpr]; exact readW_off_self _ _ _ _
  obtain v₃ : s₃.mem.readW (off base 104) 32 = s.gpr .r3 := by
    rw [m₃.mem, m₂.gpr, m₁.gpr]; exact readW_off_self _ _ _ _
  obtain v₄ : t.mem.readW (off base 108) 32 = s.gpr .r2 := by
    rw [m₄.mem, m₃.gpr, m₂.gpr, m₁.gpr]; exact readW_off_self _ _ _ _
  obtain k₄ : ∀ {d v}, (d + 4 ≤ 108 ∨ 112 ≤ d) → d + 4 ≤ 164 → s₃.mem.readW (off base d) 32 = v →
      t.mem.readW (off base d) 32 = v :=
    fun hd hd' h => by rw [m₄.mem]; exact stored hd (by omega_arith) (by omega_arith) h _
  obtain k₃ : ∀ {d v}, (d + 4 ≤ 104 ∨ 108 ≤ d) → d + 4 ≤ 164 → s₂.mem.readW (off base d) 32 = v →
      s₃.mem.readW (off base d) 32 = v :=
    fun hd hd' h => by rw [m₃.mem]; exact stored hd (by omega_arith) (by omega_arith) h _
  obtain k₂ : ∀ {d v}, (d + 4 ≤ 100 ∨ 104 ≤ d) → d + 4 ≤ 164 → s₁.mem.readW (off base d) 32 = v →
      s₂.mem.readW (off base d) 32 = v :=
    fun hd hd' h => by rw [m₂.mem]; exact stored hd (by omega_arith) (by omega_arith) h _
  refine ⟨k₄ (by decide) (by decide) (k₃ (by decide) (by decide) (k₂ (by decide) (by decide) v₁)),
    k₄ (by decide) (by decide) (k₃ (by decide) (by decide) v₂), k₄ (by decide) (by decide) v₃, v₄, ?_, ?_, ?_⟩
  · exact (((m₁.rest _).trans (m₂.rest _)).trans (m₃.rest _)).trans (m₄.rest _)
  · rw [m₄.mem, m₃.mem, m₂.mem, m₁.mem]
    exact (((outside_word (by decide) (by decide) (by omega_arith) _).trans
      (outside_word (by decide) (by decide) (by omega_arith) _)).trans (outside_word (by decide) (by decide) (by omega_arith) _)).trans
      (outside_word (by decide) (by decide) (by omega_arith) _)
  · rw [m₄.sp, m₃.sp, m₂.sp, m₁.sp]

/-- The arguments of derivation at their fields. -/
theorem deriveArgs_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (hz : 164 ≤ size)
    (hr : ArgsRead s 5) (ha : ArgsApart s base 5) :
    WP isa (.block (Generate.deriveArguments.flatMap Entry.saveArgument)) s fun t =>
      t.mem.readW (off base 96) 32 = s.gpr .r0 ∧ t.mem.readW (off base 64) 32 = s.gpr .r2 ∧
      t.mem.readW (off base 100) 32 = stackArg s 0 ∧ t.mem.readW (off base 88) 32 = stackArg s 1 ∧
      t.mem.readW (off base 104) 32 = stackArg s 2 ∧ t.mem.readW (off base 108) 32 = stackArg s 0 ∧
      Rest [.r4] s t ∧ Outside base 64 48 s.mem t.mem ∧ ∀ i < 5, stackArg t i = stackArg s i := by
  have nw := hs.nowrap
  show WP isa (.block [.str .r0 .r12 96, .str .r2 .r12 64, .ldrSp .r4 (4 * 0), .str .r4 .r12 100,
    .ldrSp .r4 (4 * 1), .str .r4 .r12 88, .ldrSp .r4 (4 * 2), .str .r4 .r12 104,
    .ldrSp .r4 (4 * 0), .str .r4 .r12 108]) s _
  refine wp_str12 hs (by decide) (by omega_arith) fun s₁ m₁ => ?_
  obtain a₁ := ha.mupd m₁
  refine wp_str12 (hs.of_mupd m₁) (by decide) (by omega_arith) fun s₂ m₂ => ?_
  obtain a₂ := a₁.mupd m₂
  obtain w₂ := (hs.of_mupd m₁).of_mupd m₂
  obtain r₂ : ArgsRead s₂ 5 := (hr.keep m₁.rd m₁.wr m₁.sp).keep m₂.rd m₂.wr m₂.sp
  obtain A₂ : ∀ i < 5, stackArg s₂ i = stackArg s i := fun i hi => by
    rw [stackArg_mupd m₂ a₁ hi (by decide), stackArg_mupd m₁ ha hi (by decide)]
  refine wp_ldrSp (by decide) (r₂ 0 (by decide)) fun s₃ u₃ => wp_str12 (w₂.of_upd u₃ (by decide)) (by decide)
    (by omega_arith) fun s₄ m₄ => ?_
  obtain a₄ := (a₂.upd u₃).mupd m₄
  obtain w₄ := (w₂.of_upd u₃ (by decide)).of_mupd m₄
  obtain r₄ : ArgsRead s₄ 5 := (r₂.keep u₃.rd u₃.wr u₃.sp).keep m₄.rd m₄.wr m₄.sp
  obtain A₄ : ∀ i < 5, stackArg s₄ i = stackArg s i := fun i hi => by
    rw [stackArg_mupd m₄ (a₂.upd u₃) hi (by decide), stackArg_upd u₃, A₂ i hi]
  refine wp_ldrSp (by decide) (r₄ 1 (by decide)) fun s₅ u₅ => wp_str12 (w₄.of_upd u₅ (by decide)) (by decide)
    (by omega_arith) fun s₆ m₆ => ?_
  obtain a₆ := (a₄.upd u₅).mupd m₆
  obtain w₆ := (w₄.of_upd u₅ (by decide)).of_mupd m₆
  obtain r₆ : ArgsRead s₆ 5 := (r₄.keep u₅.rd u₅.wr u₅.sp).keep m₆.rd m₆.wr m₆.sp
  obtain A₆ : ∀ i < 5, stackArg s₆ i = stackArg s i := fun i hi => by
    rw [stackArg_mupd m₆ (a₄.upd u₅) hi (by decide), stackArg_upd u₅, A₄ i hi]
  refine wp_ldrSp (by decide) (r₆ 2 (by decide)) fun s₇ u₇ => wp_str12 (w₆.of_upd u₇ (by decide)) (by decide)
    (by omega_arith) fun s₈ m₈ => ?_
  obtain a₈ := (a₆.upd u₇).mupd m₈
  obtain w₈ := (w₆.of_upd u₇ (by decide)).of_mupd m₈
  obtain r₈ : ArgsRead s₈ 5 := (r₆.keep u₇.rd u₇.wr u₇.sp).keep m₈.rd m₈.wr m₈.sp
  obtain A₈ : ∀ i < 5, stackArg s₈ i = stackArg s i := fun i hi => by
    rw [stackArg_mupd m₈ (a₆.upd u₇) hi (by decide), stackArg_upd u₇, A₆ i hi]
  refine wp_ldrSp (by decide) (r₈ 0 (by decide)) fun s₉ u₉ => wp_str12 (w₈.of_upd u₉ (by decide)) (by decide)
    (by omega_arith) fun t m₁₀ => WP.block_nil ?_
  obtain A : ∀ i < 5, stackArg t i = stackArg s i := fun i hi => by
    rw [stackArg_mupd m₁₀ (a₈.upd u₉) hi (by decide), stackArg_upd u₉, A₈ i hi]
  obtain v₁ : s₁.mem.readW (off base 96) 32 = s.gpr .r0 := by rw [m₁.mem]; exact readW_off_self _ _ _ _
  obtain v₂ : s₂.mem.readW (off base 64) 32 = s.gpr .r2 := by rw [m₂.mem, m₁.gpr]; exact readW_off_self _ _ _ _
  obtain v₄ : s₄.mem.readW (off base 100) 32 = stackArg s 0 := by
    rw [m₄.mem, u₃.gpr, A₂ 0 (by decide)]; exact readW_off_self _ _ _ _
  obtain v₆ : s₆.mem.readW (off base 88) 32 = stackArg s 1 := by
    rw [m₆.mem, u₅.gpr, A₄ 1 (by decide)]; exact readW_off_self _ _ _ _
  obtain v₈ : s₈.mem.readW (off base 104) 32 = stackArg s 2 := by
    rw [m₈.mem, u₇.gpr, A₆ 2 (by decide)]; exact readW_off_self _ _ _ _
  obtain v₁₀ : t.mem.readW (off base 108) 32 = stackArg s 0 := by
    rw [m₁₀.mem, u₉.gpr, A₈ 0 (by decide)]; exact readW_off_self _ _ _ _
  obtain k₁₀ : ∀ {d v}, (d + 4 ≤ 108 ∨ 112 ≤ d) → d + 4 ≤ 164 → s₈.mem.readW (off base d) 32 = v →
      t.mem.readW (off base d) 32 = v :=
    fun hd hd' h => by rw [m₁₀.mem, u₉.mem]; exact stored hd (by omega_arith) (by omega_arith) h _
  obtain k₈ : ∀ {d v}, (d + 4 ≤ 104 ∨ 108 ≤ d) → d + 4 ≤ 164 → s₆.mem.readW (off base d) 32 = v →
      s₈.mem.readW (off base d) 32 = v :=
    fun hd hd' h => by rw [m₈.mem, u₇.mem]; exact stored hd (by omega_arith) (by omega_arith) h _
  obtain k₆ : ∀ {d v}, (d + 4 ≤ 88 ∨ 92 ≤ d) → d + 4 ≤ 164 → s₄.mem.readW (off base d) 32 = v →
      s₆.mem.readW (off base d) 32 = v :=
    fun hd hd' h => by rw [m₆.mem, u₅.mem]; exact stored hd (by omega_arith) (by omega_arith) h _
  obtain k₄ : ∀ {d v}, (d + 4 ≤ 100 ∨ 104 ≤ d) → d + 4 ≤ 164 → s₂.mem.readW (off base d) 32 = v →
      s₄.mem.readW (off base d) 32 = v :=
    fun hd hd' h => by rw [m₄.mem, u₃.mem]; exact stored hd (by omega_arith) (by omega_arith) h _
  obtain k₂ : ∀ {d v}, (d + 4 ≤ 64 ∨ 68 ≤ d) → d + 4 ≤ 164 → s₁.mem.readW (off base d) 32 = v →
      s₂.mem.readW (off base d) 32 = v :=
    fun hd hd' h => by rw [m₂.mem]; exact stored hd (by omega_arith) (by omega_arith) h _
  refine ⟨k₁₀ (by decide) (by decide) (k₈ (by decide) (by decide) (k₆ (by decide) (by decide)
      (k₄ (by decide) (by decide) (k₂ (by decide) (by decide) v₁)))),
    k₁₀ (by decide) (by decide) (k₈ (by decide) (by decide) (k₆ (by decide) (by decide) (k₄ (by decide) (by decide) v₂))),
    k₁₀ (by decide) (by decide) (k₈ (by decide) (by decide) (k₆ (by decide) (by decide) v₄)),
    k₁₀ (by decide) (by decide) (k₈ (by decide) (by decide) v₆),
    k₁₀ (by decide) (by decide) v₈, v₁₀, ?_, ?_, A⟩
  · exact (((((((((m₁.rest _).trans (m₂.rest _)).trans (u₃.rest (by decide))).trans (m₄.rest _)).trans
      (u₅.rest (by decide))).trans (m₆.rest _)).trans (u₇.rest (by decide))).trans (m₈.rest _)).trans
      (u₉.rest (by decide))).trans (m₁₀.rest _)
  · rw [m₁₀.mem, u₉.mem, m₈.mem, u₇.mem, m₆.mem, u₅.mem, m₄.mem, u₃.mem, m₂.mem, m₁.mem]
    exact (((((outside_word (by decide) (by decide) (by omega_arith) _).trans
      (outside_word (by decide) (by decide) (by omega_arith) _)).trans (outside_word (by decide) (by decide) (by omega_arith) _)).trans
      (outside_word (by decide) (by decide) (by omega_arith) _)).trans (outside_word (by decide) (by decide) (by omega_arith) _)).trans
      (outside_word (by decide) (by decide) (by omega_arith) _)

/-- The entry of the domain check, from what it uses of `checkPre`, which
public-key validation's precondition also gives. -/
theorem checkEntry_of {s : State} (hsp : s.sp.toNat + 8 ≤ 2 ^ 32)
    (hrd : (⟨State.addr s.sp, 4 * 2⟩ : Region) ∈ s.rd)
    (hwr : s.wr = [⟨State.addr (arg s 0), (arg s 1).toNat * 8⟩])
    (hsb : (arg s 0).toNat + (arg s 1).toNat * 8 ≤ 2 ^ 32)
    (hv : Spec.Dsa.lengthsValid (s.gpr .r2).toNat (s.gpr .r3).toNat)
    (hsw : Spec.Dsa.scratchWords (s.gpr .r2).toNat ≤ (arg s 1).toNat) :
    WP isa (.block Generate.checkEntry) s
      (Installed s (State.addr (arg s 0)) ((arg s 1).toNat * 8) (checkFields s)) := by
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  obtain hs16 : 16384 ≤ (arg s 1).toNat * 8 := by unfold Spec.Dsa.scratchWords at hsw; omega_arith
  show WP isa (.block (((Entry.openScratch 0) ++ Generate.checkArguments.flatMap Entry.saveArgument) ++
    Entry.keyPointers)) s _
  simp only [Entry.openScratch, List.append_assoc, List.singleton_append]
  refine wp_ldrSp (i := 0) (by decide) (args_read (n := 2) hrd hsp 0 (by decide)) fun u₁ v₁ => ?_
  obtain w₁ := openScratch_ws v₁ ((arg s 1).toNat * 8) (by rw [hwr]; simp) hsb
  have nw := w₁.nowrap
  refine VG.Proof.X25519.Arm.WP.append (save_ok w₁ (by omega_arith)) fun u₂ ⟨S₂, R₂, O₂⟩ => ?_
  obtain w₂ := w₁.of_rest R₂ (by decide)
  rw [v₁.mem] at O₂
  refine VG.Proof.X25519.Arm.WP.append (checkArgs_ok w₂ (by omega_arith))
    fun u₃ ⟨F₁, F₂, F₃, F₄, R₃, O₃, _⟩ => ?_
  obtain w₃ := w₂.of_rest R₃ (by decide)
  obtain g0 : u₂.gpr .r0 = s.gpr .r0 := by rw [R₂.gpr _ (by decide), v₁.other _ (by decide)]
  obtain g2 : u₂.gpr .r2 = s.gpr .r2 := by rw [R₂.gpr _ (by decide), v₁.other _ (by decide)]
  obtain g3 : u₂.gpr .r3 = s.gpr .r3 := by rw [R₂.gpr _ (by decide), v₁.other _ (by decide)]
  rw [g0] at F₁
  rw [g2] at F₂ F₄
  rw [g3] at F₃
  refine WP.mono (keyPointers_ok w₃ (by omega_arith) F₁ F₂ F₃) fun u ⟨K₁, K₂, K₃, K₄, R₄, O₄⟩ =>
    ⟨w₃.of_rest R₄ (by decide), ?_, ?_, ?_, ?_⟩
  · intro f hf
    obtain k : ∀ {d} {x : BitVec 32}, (d + 4 ≤ 68 ∨ 84 ≤ d) → d + 4 ≤ 164 →
        u₃.mem.readW (off (State.addr (arg s 0)) d) 32 = x →
        u.mem.readW (off (State.addr (arg s 0)) d) 32 = x := fun hd' hd'' h => keep_word O₄ hd' (by omega_arith) h
    simp only [checkFields, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact k (d := 64) (by decide) (by decide) F₁
    · exact k (d := 100) (by decide) (by decide) F₂
    · exact k (d := 104) (by decide) (by decide) F₃
    · exact k (d := 108) (by decide) (by decide) F₄
    · exact K₁
    · exact K₂
    · exact K₃
    · exact K₄
  · intro i hi
    obtain g : u₁.gpr (Entry.savedRegs.getD i .r0) = s.gpr (Entry.savedRegs.getD i .r0) :=
      v₁.other _ (saved_ne i hi)
    rw [← g]
    exact keep_word O₄ (.inr (by omega_arith)) (by omega_arith) (keep_word O₃ (.inr (by omega_arith)) (by omega_arith) (S₂ i hi))
  · exact ((O₂.mono (by decide) (by decide)).trans (O₃.mono (by decide) (by decide))).trans
      (O₄.mono (by decide) (by decide))
  · exact (((v₁.rest (by decide)).trans (R₂.mono (by decide))).trans (R₃.mono (by decide))).trans
      (R₄.mono (by decide))

theorem checkEntry_ok {s : State} (h : checkPre s) :
    WP isa (.block Generate.checkEntry) s
      (Installed s (State.addr (arg s 0)) ((arg s 1).toNat * 8) (checkFields s)) := by
  obtain ⟨hsp, hrd, hwr, _, _, _, hsb, hv, _, hsw⟩ := h
  exact checkEntry_of hsp (by rw [hrd]; simp) hwr hsb hv hsw

theorem deriveEntry_ok {s : State} (h : derivePre s) :
    WP isa (.block Generate.deriveEntry) s
      (Installed s (State.addr (arg s 3)) ((arg s 4).toNat * 8) (deriveFields s)) := by
  obtain ⟨hsp, hrd, hwr, _, _, _, _, _, _, hsa, _, _, _, hsb, hv, _, _, hsw⟩ := h
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  obtain hs16 : 16384 ≤ (arg s 4).toNat * 8 := by unfold Spec.Dsa.scratchWords at hsw; omega_arith
  have hd : Region.Disjoint ⟨State.addr s.sp, 4 * 5⟩ ⟨State.addr (arg s 3), (arg s 4).toNat * 8⟩ := hsa.symm
  show WP isa (.block (((Entry.openScratch 3) ++ Generate.deriveArguments.flatMap Entry.saveArgument) ++
    Entry.keyPointers)) s _
  simp only [Entry.openScratch, List.append_assoc, List.singleton_append]
  refine wp_ldrSp (i := 3) (by decide) (args_read (n := 5) (by rw [hrd]; simp) hsp 3 (by decide)) fun u₁ v₁ => ?_
  obtain w₁ := openScratch_ws v₁ ((arg s 4).toNat * 8) (by rw [hwr]; simp) hsb
  have nw := w₁.nowrap
  obtain aa : ArgsApart s (State.addr (arg s 3)) 5 := args_apart hd hsp (by omega_arith)
  refine VG.Proof.X25519.Arm.WP.append (save_ok w₁ (by omega_arith)) fun u₂ ⟨S₂, R₂, O₂⟩ => ?_
  obtain w₂ := w₁.of_rest R₂ (by decide)
  obtain hsp₂ : u₂.sp = s.sp := by rw [R₂.sp, v₁.sp]
  rw [v₁.mem] at O₂
  obtain A₂ : ∀ i < 5, stackArg u₂ i = stackArg s i := fun i hi =>
    stackArg_apart O₂ hsp₂ hd hi hsp (by omega_arith) (by omega_arith)
  obtain r₂ : ArgsRead u₂ 5 := (args_read (n := 5) (by rw [hrd]; simp) hsp).keep (by rw [R₂.rd, v₁.rd])
    (by rw [R₂.wr, v₁.wr]) hsp₂
  refine VG.Proof.X25519.Arm.WP.append (deriveArgs_ok w₂ (by omega_arith) r₂ (aa.sp hsp₂))
    fun u₃ ⟨F₁, F₂, F₃, F₄, F₅, F₆, R₃, O₃, A₃⟩ => ?_
  obtain w₃ := w₂.of_rest R₃ (by decide)
  obtain g0 : u₂.gpr .r0 = s.gpr .r0 := by rw [R₂.gpr _ (by decide), v₁.other _ (by decide)]
  obtain g2 : u₂.gpr .r2 = s.gpr .r2 := by rw [R₂.gpr _ (by decide), v₁.other _ (by decide)]
  rw [g0] at F₁
  rw [g2] at F₂
  rw [A₂ 0 (by decide)] at F₃ F₆
  rw [A₂ 1 (by decide)] at F₄
  rw [A₂ 2 (by decide)] at F₅
  refine WP.mono (keyPointers_ok w₃ (by omega_arith) F₂ F₃ F₅) fun u ⟨K₁, K₂, K₃, K₄, R₄, O₄⟩ =>
    ⟨w₃.of_rest R₄ (by decide), ?_, ?_, ?_, ?_⟩
  · intro f hf
    obtain k : ∀ {d} {x : BitVec 32}, (d + 4 ≤ 68 ∨ 84 ≤ d) → d + 4 ≤ 164 →
        u₃.mem.readW (off (State.addr (arg s 3)) d) 32 = x →
        u.mem.readW (off (State.addr (arg s 3)) d) 32 = x := fun hd' hd'' h => keep_word O₄ hd' (by omega_arith) h
    simp only [deriveFields, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact k (d := 96) (by decide) (by decide) F₁
    · exact k (d := 64) (by decide) (by decide) F₂
    · exact k (d := 100) (by decide) (by decide) F₃
    · exact k (d := 88) (by decide) (by decide) F₄
    · exact k (d := 104) (by decide) (by decide) F₅
    · exact k (d := 108) (by decide) (by decide) F₆
    · exact K₁
    · exact K₂
    · exact K₃
    · exact K₄
  · intro i hi
    obtain g : u₁.gpr (Entry.savedRegs.getD i .r0) = s.gpr (Entry.savedRegs.getD i .r0) :=
      v₁.other _ (saved_ne i hi)
    rw [← g]
    exact keep_word O₄ (.inr (by omega_arith)) (by omega_arith) (keep_word O₃ (.inr (by omega_arith)) (by omega_arith) (S₂ i hi))
  · exact ((O₂.mono (by decide) (by decide)).trans (O₃.mono (by decide) (by decide))).trans
      (O₄.mono (by decide) (by decide))
  · exact (((v₁.rest (by decide)).trans (R₂.mono (by decide))).trans (R₃.mono (by decide))).trans
      (R₄.mono (by decide))

end VG.Proof.Dsa.Arm

end

end

/-!
# DSA domain checks on 32-bit ARM: correctness

`genDispatch_ok` follows the public widths to their code, as the signer's
dispatch does; `check_correct`: from `checkArm`'s precondition,
`vg_dsa_check_parameters` returns whether `Spec.Dsa.checkParametersBytes`
accepts the domain, and restores the registers the ABI preserves.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm
open VG.Proof.Ecdsa.Arm (mask32)
open VG.Proof.X25519.Arm (Rest eval_eq wp_mov op2_imm)

variable {umaal : Bool}

theorem genDispatch_ok (sized : Nat → Nat → Prog isa) (widths : List (Nat × Nat))
    {s : State} {base : Addr} {size pLen qLen : Nat} {Q : State → Prop}
    (hs : Ws s base size) (hz : 120 ≤ size) (member : (pLen, qLen) ∈ widths)
    (bound : ∀ w ∈ widths, w.1 < 2 ^ 16 ∧ w.2 < 2 ^ 16)
    (hp : (hdr base s 100).toNat = pLen) (hq : (hdr base s 104).toNat = qLen)
    (body : ∀ t, Rest [.r4, .r5] s t → t.mem = s.mem → WP isa (sized pLen qLen) t Q) :
    WP isa (Generate.dispatch sized widths) s Q := by
  induction widths generalizing s with
  | nil => simp only [List.not_mem_nil] at member
  | cons w rest ih =>
    obtain ⟨wp, wq⟩ := w
    have B := bound (wp, wq) List.mem_cons_self
    unfold Generate.dispatch
    refine WP.seq (WP.mono (widthMatch_ok hs hz hp hq B.1 B.2) fun t ⟨Z, R, M⟩ => ?_)
    refine WP.ite t.z (eval_eq _) (fun ht => ?_) (fun hf => ?_)
    · have Both : pLen = wp ∧ qLen = wq := of_decide_eq_true (Z ▸ ht)
      rw [← Both.1, ← Both.2]
      exact body t R M
    · have Both : ¬ (pLen = wp ∧ qLen = wq) := of_decide_eq_false (Z ▸ hf)
      refine ih (hs.of_rest R (by decide))
        (by simpa only [List.mem_cons, Prod.mk.injEq, Both, false_or] using member)
        (fun w hw => bound w (List.mem_cons_of_mem _ hw))
        (by simp only [hdr, M]; exact hp) (by simp only [hdr, M]; exact hq)
        fun u Ru Mu => body u (R.trans Ru) (Mu.trans M)

theorem genWidths_mem {pLen qLen : Nat} (h : Spec.Dsa.lengthsValid pLen qLen) :
    (pLen, qLen) ∈ Generate.widths := widths_mem h

/-- A domain p||q||g, by its components. -/
theorem paramsBytes_at (mem : Mem) (ptr : Addr) {pLen qLen total : Nat} (h : 2 * pLen + qLen ≤ total) :
    Spec.Dsa.paramsBytes pLen qLen (Spec.Rsa.bytesAt mem ptr total) =
      ⟨Spec.Dsa.decodeBE (Spec.Rsa.bytesAt mem ptr pLen),
        Spec.Dsa.decodeBE (Spec.Rsa.bytesAt mem (ptr + BitVec.ofNat 64 pLen) qLen),
        Spec.Dsa.decodeBE (Spec.Rsa.bytesAt mem (ptr + BitVec.ofNat 64 (pLen + qLen)) pLen)⟩ := by
  have h0 := VG.Proof.Dsa.bytesAt_slice mem ptr (offset := 0) (len := pLen) (by omega_arith : 0 + pLen ≤ total)
  simp only [List.drop_zero, BitVec.add_zero] at h0
  rw [VG.Proof.Dsa.paramsBytes_eq, h0, VG.Proof.Dsa.bytesAt_slice mem ptr (by omega_arith : pLen + qLen ≤ total),
    VG.Proof.Dsa.bytesAt_slice mem ptr (by omega_arith : (pLen + qLen) + pLen ≤ total)]

/-- The domain check, by the checks the code makes. -/
theorem checkParametersBytes_iff {pLen qLen : Nat} {params : List Byte}
    (hl : Spec.Dsa.lengthsValid pLen qLen) (hpl : params.length = 2 * pLen + qLen) :
    Spec.Dsa.checkParametersBytes pLen qLen params = true ↔
      shapeValid (Spec.Dsa.paramsBytes pLen qLen params).p (Spec.Dsa.paramsBytes pLen qLen params).q ∧
      domainChecks (Spec.Dsa.paramsBytes pLen qLen params).p (Spec.Dsa.paramsBytes pLen qLen params).q
        (Spec.Dsa.paramsBytes pLen qLen params).g := by
  rw [VG.Proof.Dsa.checkParametersBytes_eq hl hpl]
  simp only [VG.Proof.Dsa.powMod_eq, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq, shapeValid,
    domainChecks]
  exact ⟨fun ⟨⟨a, b, c⟩, d, e, f, _⟩ => ⟨⟨a, c, b⟩, ⟨f, e⟩, d⟩, fun ⟨⟨a, c, b⟩, ⟨f, e⟩, d⟩ => ⟨⟨a, b, c⟩, d, e, f, f⟩⟩

/-- The domain's components, at a state with the environment of the check. -/
theorem checkIn {s t : State} {base : Addr} {size : Nat} (h : checkPre s) (hb : State.addr (arg s 0) = base)
    (hsz : (arg s 1).toNat * 8 = size) (E : Env s base size (checkFields s) t) :
    Input t base size (.input .p) (s.gpr .r2).toNat
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r2).toNat)) ∧
      Input t base size (.input .q) (s.gpr .r3).toNat
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 (s.gpr .r2).toNat)
          (s.gpr .r3).toNat)) ∧
      Input t base size (.input .g) (s.gpr .r2).toNat
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
          (State.addr (s.gpr .r0) + BitVec.ofNat 64 ((s.gpr .r2).toNat + (s.gpr .r3).toNat)) (s.gpr .r2).toNat)) := by
  subst hb hsz
  obtain ⟨_, hrd, _, dPS, _, fP, _, hv, hr1, hsw⟩ := h
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  have hz : 12016 ≤ (arg s 1).toNat * 8 := by unfold Spec.Dsa.scratchWords at hsw; omega_arith
  have pr : (⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  have ip := input_of E (p := .input .p) (by decide : Impl.Dsa.Layout.Field.p ≠ .mask) (o := 0)
    (len := (s.gpr .r2).toNat) (by rw [BitVec.add_zero]; exact E.field (d := 64) (v := s.gpr .r0) (by simp))
    pr fP (by omega_arith) (.inr rfl) dPS hz
  rw [BitVec.add_zero] at ip
  have cg := fun {a : Nat} {xs : List (BitVec 32)} (h : (xs.map BitVec.toNat).sum = a) =>
    (sum_ofNat (s.gpr .r0) xs).trans (congrArg (fun n => s.gpr .r0 + BitVec.ofNat 32 n) h)
  refine ⟨ip, input_of E (p := .input .q) (by decide : Impl.Dsa.Layout.Field.q ≠ .mask) ?_ pr fP (by omega_arith)
      (.inl (by omega_arith)) dPS hz,
    input_of E (p := .input .g) (by decide : Impl.Dsa.Layout.Field.g ≠ .mask) ?_ pr fP (by omega_arith)
      (.inl (by omega_arith)) dPS hz⟩
  · exact (E.field (d := 68) (v := s.gpr .r0 + s.gpr .r2) (by simp)).trans (cg (xs := [s.gpr .r2]) (by simp))
  · exact (E.field (d := 72) (v := s.gpr .r0 + s.gpr .r2 + s.gpr .r3) (by simp)).trans
      (cg (xs := [s.gpr .r2, s.gpr .r3]) (by simp))

theorem check_correct {s : State} (h : checkPre s) :
    WP isa (Generate.checkParameters umaal) s fun t => abiPreserved s t ∧ checkArm.post s t := by
  obtain ⟨hsp, hrd, hwr, dPS, dSA, fP, fS, hv, hr1, hsw⟩ := id h
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  have hs16 : 128 * (s.gpr .r2).toNat ≤ (arg s 1).toNat * 8 := by unfold Spec.Dsa.scratchWords at hsw; omega_arith
  obtain ⟨wp, wq, qp, q32, q0, p128⟩ := width_of hv
  simp only [Generate.checkParameters, Core.sequence, List.foldr]
  refine WP.seq (WP.mono (checkEntry_ok h) fun u I => ?_)
  have E₀ := Env.of_installed I (by omega_arith)
  have fok := checkFields_ok s
  refine WP.seq (genDispatch_ok (Generate.checkSized umaal) _ E₀.ws (by omega_arith) (genWidths_mem hv) (by decide)
    (by rw [E₀.field (d := 100) (v := s.gpr .r2) (by simp)]) (by rw [E₀.field (d := 104) (v := s.gpr .r3) (by simp)])
    fun t₁ R₁ M₁ => ?_)
  have E₁ := E₀.of_mem R₁ (by decide) M₁
  have hz : 12016 ≤ (arg s 1).toNat * 8 := by omega_arith
  obtain ⟨Ip₁, Iq₁, Ig₁⟩ := checkIn h rfl rfl E₁
  -- The specification's components.
  have hpl : (checkParams s).length = 2 * (s.gpr .r2).toNat + (s.gpr .r3).toNat := by
    simp only [checkParams, Spec.Rsa.bytesAt, List.length_map, List.length_range]; exact hr1
  have PB := paramsBytes_at s.mem (State.addr (s.gpr .r0)) (pLen := (s.gpr .r2).toNat) (qLen := (s.gpr .r3).toNat)
    (total := (s.gpr .r1).toNat) (by omega_arith)
  have spec := checkParametersBytes_iff hv hpl
  simp only [checkParams] at spec
  rw [PB] at spec
  dsimp only at spec
  unfold Generate.checkSized
  refine WP.seq (WP.mono (check_ok E₁.ws hz wp wq Ip₁.toReady Iq₁.toReady Ip₁.value Iq₁.value)
    fun t₂ ⟨Z, M, _, R₂, O₂⟩ => ?_)
  have E₂ := E₁.keep fok R₂ (by decide) O₂ (fun r hr => by
    simp only [shapeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only <;> omega_arith)
  refine WP.ite t₂.z (eval_eq _) (fun ht => ?_) (fun hf => ?_)
  · -- A rejected shape.
    have nv := of_decide_eq_true (Z ▸ ht)
    refine wp_mov (op2_imm (by decide)) fun t₃ v₃ => WP.block_nil ?_
    refine finish_ok (E₂.ws.of_upd v₃ (by decide)) (by omega_arith) (fun i hi => by rw [v₃.mem]; exact E₂.saved i hi)
      (v₃.sp.trans E₂.sp) fun u A r0 _ => ⟨A, ?_⟩
    have : checkRes s = false := by
      by_contra hc
      exact nv (spec.mp (Bool.not_eq_false _ ▸ hc)).1
    show (BitVec.setWidth 32 (u.gpr .r1 ++ u.gpr .r0)).toNat = if checkRes s = true then 1 else 0
    rw [this, BitVec.setWidth_append_eq_right, r0, v₃.gpr]
    rfl
  · have valid : shapeValid _ _ := Classical.not_not.mp (of_decide_eq_false (Z ▸ hf))
    obtain ⟨Ip, Iq, Ig⟩ := checkIn h rfl rfl E₂
    obtain ⟨hP, hPo, hQ, hQo⟩ := shape_bounds valid
    have hm : maskW (State.addr (arg s 0)) t₂ = BitVec.allOnes 32 := by
      rw [M]; unfold mask32; split
      · rfl
      · contradiction
    refine WP.seq (WP.mono (parameters_ok ⟨E₂.ws, by omega_arith, wp, wq, qp, q32⟩ Ip Iq Ig hP hPo hQ hQo)
      fun t₃ ⟨F₃, Rn₃⟩ => ?_)
    have E₃ := E₂.keep fok Rn₃.rest (by decide) Rn₃.mem (fun r hr => by
      simp only [runRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp only <;> omega_arith)
    rw [hm, BitVec.allOnes_and] at F₃
    refine WP.mono (result_ok E₃.ws (by omega_arith) _ F₃) fun t₄ ⟨r0₄, R₄, M₄⟩ => ?_
    refine finish_ok (E₃.ws.of_rest R₄ (by decide)) (by omega_arith) (fun i hi => by rw [M₄]; exact E₃.saved i hi)
      (R₄.sp.trans E₃.sp) fun u A r0 _ => ⟨A, ?_⟩
    show (BitVec.setWidth 32 (u.gpr .r1 ++ u.gpr .r0)).toNat = if checkRes s = true then 1 else 0
    rw [status_toNat (r0.trans r0₄)]
    by_cases hc : checkRes s = true
    · have d := (spec.mp hc).2
      rw [ite_eq_left hc]
      split
      · rfl
      · contradiction
    · have d : ¬ domainChecks _ _ _ := fun d => hc (spec.mpr ⟨valid, d⟩)
      rw [ite_eq_right hc]
      split
      · contradiction
      · rfl

end VG.Proof.Dsa.Arm
