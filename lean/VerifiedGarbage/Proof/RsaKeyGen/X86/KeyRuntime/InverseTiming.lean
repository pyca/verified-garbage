module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.InverseCall
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Inverse
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Public
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaKeyGen.X86.Inverse.Verified
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Inverse.Entry
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseLoad
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
public import VerifiedGarbage.Proof.RsaKeyGen.Contract

/-! # The key's calls of `vg_rsa_keygen_inverse` leak only public data

The arguments' block is checked by the taint analysis, which finds the length argument it loads
into `eax` public. The call itself is constant time by the callee's contract, which holds in both
runs (`CallAt.callPre`) and whose public data, the arguments, agree. The call leaves the registers
and the arguments the analysis tracks as they were (`agree_after_call`). -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.Rsa.X86.KeyRt (kw)
open VG.Proof.Rsa.X86.Keys (num)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

/-- Two runs that both satisfy `P` and agree on what `runtimeTaint` says is public. -/
def Both (P : State → Prop) (s t : State) : Prop := P s ∧ P t ∧ VG.X86.Taint.Agree runtimeTaint s t

/-- `runtimeTaint`, with the length argument in `eax`. -/
def argsTaint : VG.X86.Taint.T := { runtimeTaint with regs := .ofList [.edi, .esi, .esp, .eax] }

theorem args_trace (w : Width) (hw : w ≠ .correction) :
    RelCT isa (VG.X86.Taint.Agree runtimeTaint) (.block (inverseArgs w)) (VG.X86.Taint.Agree argsTaint) := by
  have H : (VG.Taint.check taint runtimeTaint (.block (inverseArgs w))
      (VG.Taint.hintOf taint runtimeTaint (.block (inverseArgs w)))).any (taint.le argsTaint) = true := by
    cases w
    all_goals first | rfl | exact absurd rfl hw
  cases e : VG.Taint.check taint runtimeTaint (.block (inverseArgs w))
      (VG.Taint.hintOf taint runtimeTaint (.block (inverseArgs w))) with
  | none => rw [e] at H; cases H
  | some τ' => exact checkedProgramChange e (by simpa only [e, Option.any_some] using H)

theorem CallAt.pub {B : Addr} {Z n N : Nat} {w : Width} {p : BitVec 32} {a : Nat} {u₁ u₂ : State}
    (C₁ : CallAt B Z n N w p a u₁) (C₂ : CallAt B Z n N w p a u₂) :
    VG.Proof.RsaKeyGen.X86.Inverse.contract.pub (invEntry B (8 * invWords a) u₁)
      (invEntry B (8 * invWords a) u₂) := by
  have fit₁ : 16 ≤ (u₁.gpr .esp).toNat := by have := C₁.ready.ws.deep.1; omega
  have fit₂ : 16 ≤ (u₂.gpr .esp).toNat := by have := C₂.ready.ws.deep.1; omega
  have sa := fun {i} (hi : i < 3) => invEntry_arg (L := 8 * invWords a) C₁.args fit₁ hi
  have ta := fun {i} (hi : i < 3) => invEntry_arg (L := 8 * invWords a) C₂.args fit₂ hi
  have sp : (invEntry B (8 * invWords a) u₁).gpr .esp = (invEntry B (8 * invWords a) u₂).gpr .esp := by
    change (pushed invArgs u₁).callEntry.gpr .esp = (pushed invArgs u₂).callEntry.gpr .esp
    rw [callEntry_esp', callEntry_esp', C₁.sp, C₂.sp]
  sig_pub [VG.Proof.RsaKeyGen.X86.Inverse.contract, VG.Proof.RsaKeyGen.X86.Inverse.inverseStack,
    Proof.RsaKeyGen.inverseContract, Proof.RsaKeyGen.inverseSig, abi, argSlots, argVal, argBytes]
  simp only [sa (by decide : 0 < 3), sa (by decide : 1 < 3), sa (by decide : 2 < 3),
    ta (by decide : 0 < 3), ta (by decide : 1 < 3), ta (by decide : 2 < 3), ↓reduceIte]
  exact ⟨sp, trivial, trivial, trivial⟩

theorem call_trace (B : Addr) (Z n N : Nat) (w : Width) (p : BitVec 32) (a : Nat) :
    RelCT isa (fun u₁ u₂ => CallAt B Z n N w p a u₁ ∧ CallAt B Z n N w p a u₂) inverseCall
      (fun _ _ => True) := by
  refine VG.X86.RelCT.callWith (rs := invArgs) VG.Proof.RsaKeyGen.X86.Inverse.verified.1
    VG.Proof.RsaKeyGen.X86.Inverse.verified.2.1 [⟨(below p 12).base, 12⟩] [⟨B, 8 * invWords a⟩] ?_
  intro u₁ u₂ ⟨C₁, C₂⟩
  refine ⟨C₁.callPre, C₂.callPre, C₁.sp.trans C₂.sp.symm, ?_⟩
  rw [C₁.entry_eq, C₂.entry_eq]
  exact C₁.pub C₂

/-- What `runtimeTaint` says of a state depends only on its stack pointer and regions. -/
theorem wf_keep {u t : State} (W : VG.X86.Taint.Wf runtimeTaint u) (sp : t.gpr .esp = u.gpr .esp)
    (wr : t.wr = u.wr) : VG.X86.Taint.Wf runtimeTaint t where
  lens h := absurd rfl h
  bases _ h := by cases h
  wbases _ h := by cases h
  args h := by
    rw [sp, wr]
    have := W.args h
    simp only [VG.X86.Taint.argByte, sp] at this ⊢
    exact this
  argBases _ h := by cases h
  stk := by rw [sp]; exact W.stk
  frames _ h := by cases h
  room h := by cases h

/-- A call that keeps the callee-saved registers and writes only the workspace and the stack
below `esp` keeps what `runtimeTaint` says is public. -/
theorem agree_after_call {B : Addr} {Z : Nat} {u₁ u₂ t₁ t₂ : State}
    (A : VG.X86.Taint.Agree runtimeTaint u₁ u₂)
    (K₁ : Keeps [.eax, .ecx, .edx] u₁ t₁) (K₂ : Keeps [.eax, .ecx, .edx] u₂ t₂)
    (F₁ : Frame [⟨B, Z⟩, below (u₁.gpr .esp) 52] u₁.mem t₁.mem)
    (F₂ : Frame [⟨B, Z⟩, below (u₂.gpr .esp) 52] u₂.mem t₂.mem)
    (ws₁ : (⟨B, Z⟩ : Region) ∈ u₁.wr) (ws₂ : (⟨B, Z⟩ : Region) ∈ u₂.wr)
    (low₁ : 52 ≤ (u₁.gpr .esp).toNat) (low₂ : 52 ≤ (u₂.gpr .esp).toNat) :
    VG.X86.Taint.Agree runtimeTaint t₁ t₂ := by
  have sp₁ : t₁.gpr .esp = u₁.gpr .esp := K₁.1 .esp (by decide)
  have sp₂ : t₂.gpr .esp = u₂.gpr .esp := K₂.1 .esp (by decide)
  have kept {u t : State} (K : Keeps [.eax, .ecx, .edx] u t) (W : VG.X86.Taint.Wf runtimeTaint u)
      (F : Frame [⟨B, Z⟩, below (u.gpr .esp) 52] u.mem t.mem) (ws : (⟨B, Z⟩ : Region) ∈ u.wr)
      (low : 52 ≤ (u.gpr .esp).toNat) {k : Nat} (hk : k < 76) :
      t.mem (VG.X86.Taint.argByte t (16 + k)) = u.mem (VG.X86.Taint.argByte u (16 + k)) := by
    have sp : t.gpr .esp = u.gpr .esp := K.1 .esp (by decide)
    have args := W.args (by decide)
    have fit : (u.gpr .esp).toNat + 16 + 76 ≤ 2 ^ 32 := args.1
    simp only [VG.X86.Taint.argByte, sp]
    apply F
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · intro c
      refine args.2 _ ws _ ?_ c
      change (⟨(u.gpr .esp).setWidth 64 + BitVec.ofNat 64 16, 76⟩ : Region).Contains _ 1
      rw [show (u.gpr .esp).setWidth 64 + BitVec.ofNat 64 (16 + k) =
        ((u.gpr .esp).setWidth 64 + BitVec.ofNat 64 16) + BitVec.ofNat 64 k by
          rw [BitVec.add_assoc, BitVec.ofNat_add]]
      exact Offset.contains_base _ (by omega) (by omega)
    · intro c
      have hb : below (u.gpr .esp) 52 = ⟨(u.gpr .esp).setWidth 64 - BitVec.ofNat 64 52, 52⟩ := by
        unfold below
        rw [Taint.sub_setWidth low]
      rw [hb] at c
      exact Offset.base_disjoint_below ((u.gpr .esp).setWidth 64) (n := 52) (k := 92) (by decide) _
        (Offset.contains_base _ (by omega) (by omega)) c
  refine ⟨⟨?_, fun h => by cases h⟩, fun h => absurd rfl h, wf_keep A.wf₁ sp₁ K₁.2.2, wf_keep A.wf₂ sp₂ K₂.2.2,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => by rw [sp₁, sp₂]; exact A.sp (by decide), ?_⟩
  · intro r hr
    have out : r ∉ [Reg.eax, .ecx, .edx] := by
      revert hr
      cases r <;> decide
    rw [K₁.1 r out, K₂.1 r out]
    exact A.rf.1 r hr
  · intro k lo hk
    change t₁.mem (VG.X86.Taint.argByte t₁ (16 + k)) = t₂.mem (VG.X86.Taint.argByte t₂ (16 + k))
    rw [kept K₁ A.wf₁ F₁ ws₁ low₁ hk, kept K₂ A.wf₂ F₂ ws₂ low₂ hk]
    exact A.argMem k lo hk

theorem callInverse_trace (B : Addr) (Z n N : Nat) (w : Width) (hw : w ≠ .correction) :
    RelCT isa (Both (InvReady B Z n N w)) (callInverse w) (VG.X86.Taint.Agree runtimeTaint) := by
  intro s₁ s₂ tr₁ tr₂ t₁ t₂ ⟨R₁, R₂, A⟩ E₁ E₂
  unfold callInverse at E₁ E₂
  cases E₁ with
  | seq Ea₁ Ec₁ =>
    cases E₂ with
    | seq Ea₂ Ec₂ =>
      obtain ⟨T₁, A'⟩ := args_trace w hw _ _ _ _ _ _ A Ea₁ Ea₂
      obtain ⟨a₁, C₁, K₁, m₁⟩ := wp_result (args_ok R₁) Ea₁
      obtain ⟨a₂, C₂, K₂, m₂⟩ := wp_result (args_ok R₂) Ea₂
      have eax := A'.rf.1 .eax (by decide)
      rw [C₁.eax, C₂.eax] at eax
      have same : a₁ = a₂ := by
        have := congrArg BitVec.toNat eax
        simp only [BitVec.toNat_ofNat] at this
        rw [Nat.mod_eq_of_lt (by have := C₁.len; omega), Nat.mod_eq_of_lt (by have := C₂.len; omega)] at this
        exact this
      subst same
      have sp : s₁.gpr .esp = s₂.gpr .esp := A.sp (by decide)
      rw [← sp] at C₂
      obtain ⟨T₂, -⟩ := call_trace B Z n N w (s₁.gpr .esp) a₁ _ _ _ _ _ _ ⟨C₁, C₂⟩ Ec₁ Ec₂
      obtain ⟨-, -, -, -, -, Kt₁, Ft₁⟩ := wp_result (call_ok C₁) Ec₁
      obtain ⟨-, -, -, -, -, Kt₂, Ft₂⟩ := wp_result (call_ok C₂) Ec₂
      refine ⟨by rw [T₁, T₂], ?_⟩
      have A₀ : VG.X86.Taint.Agree runtimeTaint _ _ := taint.le_sound (τ := runtimeTaint) (σ := argsTaint) rfl A'
      exact agree_after_call A₀ Kt₁ Kt₂ (by rw [C₁.sp]; exact Ft₁) (by rw [C₂.sp]; exact Ft₂)
        C₁.ready.ws.old.workspace.wr C₂.ready.ws.old.workspace.wr C₁.ready.ws.deep.1 C₂.ready.ws.deep.1

/-- A step whose trace the taint analysis checks, and whose result each run satisfies. -/
theorem step_trace {c : Prog isa} {P Q : State → Prop} (pub : Public c) (ok : ∀ s, P s → WP isa c s Q) :
    RelCT isa (Both P) c (Both Q) :=
  (((public_trace pub).mono (fun _ _ h => h.2.2) (fun _ _ h => h)).wp
    (fun s t h => ⟨ok s h.1, ok t h.2.1⟩)).mono (fun _ _ h => h) (fun _ _ ⟨A, q₁, q₂⟩ => ⟨q₁, q₂, A⟩)

/-- A last step whose trace the taint analysis checks. -/
theorem last_trace {c : Prog isa} {P : State → Prop} (pub : Public c) :
    RelCT isa (Both P) c (VG.X86.Taint.Agree runtimeTaint) :=
  (public_trace pub).mono (fun _ _ h => h.2.2) (fun _ _ h => h)

/-- Number `j` is odd and more than one. -/
def OddAt (B : Addr) (n j : Nat) (s : State) : Prop := num s.mem B n j % 2 = 1 ∧ 1 < num s.mem B n j

/-- What `oddModulus` leaves is odd and more than one. -/
theorem oddAt_of {B : Addr} {n j x : Nat} {s : State}
    (h : num s.mem B n j = if x % 2 = 1 ∧ 3 ≤ x then x else 3) : OddAt B n j s := by
  unfold OddAt
  rw [h]
  split
  · next H => exact ⟨H.1, by omega⟩
  · decide

/-- What an inversion needs of the state it starts from. -/
def FromReady (B : Addr) (Z n N : Nat) (w : Width) (mo : Loc) (s : State) : Prop :=
  Ws s B Z n N ∧ val32 s.mem B (mo.offset n) (w.words n) % 2 = 1 ∧
    1 < val32 s.mem B (mo.offset n) (w.words n)

theorem inverseFrom_trace {B : Addr} {Z n N : Nat} {w : Width} {src mo : Loc}
    (bound : 15 ≤ N) (hw : w ≠ .correction)
    (L : VG.Proof.RsaKeyGen.X86.Key.InverseLayout Z (w.words n) (src.offset n) (mo.offset n))
    (setup : Public (inverseSetup w src mo)) :
    RelCT isa (Both (FromReady B Z n N w mo)) (inverseFrom w src mo) (VG.X86.Taint.Agree runtimeTaint) := by
  unfold inverseFrom
  refine RelCT.seq (step_trace setup fun s ⟨h, odd, large⟩ =>
    WP.mono (inverseSetup_ok h bound hw L odd large) fun v H => H.1) (callInverse_trace B Z n N w hw)

end VG.Proof.RsaKeyGen.X86.KeyRuntime
