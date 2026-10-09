import VerifiedGarbage.Proof.X25519.X86.Field32.Call
import VerifiedGarbage.Proof.X25519.X86.Field32.Verified
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.X86.TaintErase

/-!
# Calls of `vg_gf25519_r32_mul` on x86 (32-bit): constant time

The taint analysis cannot follow a call of `vg_gf25519_r32_mul`: the
function stores through a pointer it forms from its arguments (`ws + o`),
which the analysis cannot place in a region, and it restores `edi` from its
own working space. So code that calls it is related run by run (`RelCT`),
as X448's is (`Proof/X448/X86/CallCT.lean`): `RF x` relates two runs with
the working space at `x` and the stack a call uses apart from it (`Ctx`) in
each, that agree on `esp`. A call leaks the same in both
(`mulCall_tr`): the `mov`s of the offsets by the taint analysis, and the
call itself by the function's constant time (`mulFn_ct`, `RelCT.callWith`),
from the function's contract, which each run meets (`callPre_mul`); and
it keeps `RF` (`mulCall_rf`), by its correctness (`mulCall_ok`).
-/

namespace VG.Proof.X25519.X86.Field32

open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.X25519.X86.Field32 VG.Proof.X25519.X86

/-- Two runs with the working space at `x` and the stack a call uses apart
from it, that agree on `esp`. -/
def RF (x : BitVec 32) (s₁ s₂ : State) : Prop :=
  Ctx 8192 x s₁ ∧ Ctx 8192 x s₂ ∧ s₁.gpr .esp = s₂.gpr .esp

theorem RF.agree {x : BitVec 32} {s₁ s₂ : State} (h : RF x s₁ s₂) :
    VG.X86.Taint.Agree (τr [.esp, .edi]) s₁ s₂ := by
  refine agree_regs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.2.2
  · exact h.1.edi.trans h.2.1.edi.symm

/-- The arguments pushed. -/
abbrev callRegs : List Reg := [.edx, .ecx, .eax, .edi]

/-- The state `vg_gf25519_r32_mul` is entered in, its arguments readable and
its working space writable. -/
abbrev entryOf (s : State) (x : BitVec 32) : State :=
  (pushed callRegs s).callEntry.withRegions [below (s.gpr .esp) (4 * callRegs.length)] [scR 4096 x]

/-- The function's contract, at a call after the offsets' `mov`s. -/
theorem callPre_mul {x : BitVec 32} {s : State} (hc : Ctx 8192 x s) {o a b : Nat}
    (ho : o + 32 ≤ 768) (ha : a + 32 ≤ 768) (hb : b + 32 ≤ 768)
    (heax : s.gpr .eax = BitVec.ofNat 32 o) (hecx : s.gpr .ecx = BitVec.ofNat 32 a)
    (hedx : s.gpr .edx = BitVec.ofNat 32 b) :
    CallPre mulX86 callRegs [below (s.gpr .esp) (4 * callRegs.length)] [scR 4096 x] s := by
  obtain ⟨hE, hdis⟩ := hc.stk rfl (Nat.le_refl _)
  have hfit8 := hc.fit
  have fit : 4 * callRegs.length + 4 ≤ (s.gpr .esp).toNat := hE
  have av : ∀ i (hi : i < 4), arg (entryOf s x) i = s.gpr callRegs[4 - 1 - i] :=
    fun i hi => by rw [arg_withRegions]; exact callEntry_arg fit (by decide) hi
  have a0 : arg (entryOf s x) 0 = x := (av 0 (by decide)).trans hc.edi
  have esp : (entryOf s x).gpr .esp = s.gpr .esp - BitVec.ofNat 32 20 := by
    rw [State.withRegions_gpr]; exact callEntry_esp' callRegs s
  have aa : argAddr (entryOf s x) 0 = (s.gpr .esp - BitVec.ofNat 32 16).setWidth 64 := by
    rw [argAddr_withRegions]; exact callEntry_argAddr0 callRegs s
  have sub4 : Region.Sub (scR 4096 x) (scR 8192 x) := Region.sub_prefix (by decide)
  have dis4 : (scR 4096 x).Disjoint (callStk s) := hdis.sub_left sub4
  have fits : ∀ {v : Nat}, v + 32 ≤ 768 → Spec.X25519.Field32.Fits (BitVec.ofNat 32 v) := fun hv => by
    show (BitVec.ofNat 32 _).toNat + 32 ≤ 768
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hv
  have hws : wsOf (entryOf s x) = x.setWidth 64 := by rw [wsOf, a0]
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [esp, sub_toNat (by omega)]; have := (s.gpr .esp).isLt; omega
  · rw [aa]; rfl
  · rw [hws]; rfl
  · rw [hws, aa]
    exact dis4.sub_right (below_sub (by decide) hE)
  · rw [hws, esp]
    exact (dis4.sub_right (Region.sub_prefix (len := 4) (len' := 20) (by decide))).symm
  · rw [a0]; omega
  · rw [av 1 (by decide)]; exact heax ▸ fits ho
  · rw [av 2 (by decide)]; exact hecx ▸ fits ha
  · rw [av 3 (by decide)]; exact hedx ▸ fits hb
  · refine Covers.append_left (Covers.of_mem fun r hr => by
      rw [List.mem_singleton.mp hr]; exact List.mem_append_right _ List.mem_cons_self) ?_
    exact Covers.of_sub fun r hr => ⟨scR 8192 x, List.mem_append_right _ (List.mem_cons_of_mem _ hc.wr), 0,
      by rw [List.mem_singleton.mp hr]; exact (BitVec.add_zero _).symm,
      by rw [List.mem_singleton.mp hr]; show 0 + 4096 ≤ 8192; decide⟩
  · exact Covers.of_sub fun r hr => ⟨scR 8192 x, List.mem_cons_of_mem _ hc.wr, 0,
      by rw [List.mem_singleton.mp hr]; exact (BitVec.add_zero _).symm,
      by rw [List.mem_singleton.mp hr]; show 0 + 4096 ≤ 8192; decide⟩

/-- The `mov`s of the offsets leak nothing that depends on them. -/
theorem movs_check (o a b : Nat) :
    (taint.check (τr [.esp, .edi]) (.block [.mov .eax (.imm (BitVec.ofNat 32 o)),
      .mov .ecx (.imm (BitVec.ofNat 32 a)), .mov .edx (.imm (BitVec.ofNat 32 b))])
      (.block [] 256)).isSome = true := by
  have h := Taint.check_erase (.block [.mov .eax (.imm (BitVec.ofNat 32 o)),
      .mov .ecx (.imm (BitVec.ofNat 32 a)), .mov .edx (.imm (BitVec.ofNat 32 b))]) (τr [.esp, .edi])
    (.block [] 256) rfl rfl
  have e : Code.erase (.block [.mov .eax (.imm (BitVec.ofNat 32 o)), .mov .ecx (.imm (BitVec.ofNat 32 a)),
      .mov .edx (.imm (BitVec.ofNat 32 b))]) =
      Code.erase (.block [.mov .eax (.imm 0), .mov .ecx (.imm 0), .mov .edx (.imm 0)]) := rfl
  rw [e] at h
  have h0 : (taint.check (τr [.esp, .edi]) (Code.erase (.block [.mov .eax (.imm 0), .mov .ecx (.imm 0),
      .mov .edx (.imm 0)])) (.block [] 256)).isSome = true := by decide +kernel
  exact (congrArg Option.isSome h).symm.trans h0

/-- The `mov`s of the offsets. -/
theorem movs_ok (s : State) (o a b : Nat) :
    WP isa (.block [.mov .eax (.imm (BitVec.ofNat 32 o)), .mov .ecx (.imm (BitVec.ofNat 32 a)),
      .mov .edx (.imm (BitVec.ofNat 32 b))]) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 o ∧ t.gpr .ecx = BitVec.ofNat 32 a ∧ t.gpr .edx = BitVec.ofNat 32 b ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
      t.wr = s.wr :=
  Wp.wp_movi fun s₁ u₁ => Wp.wp_movi fun s₂ u₂ => Wp.wp_movi fun s₃ u₃ => WP.block_nil
    ⟨by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr],
      by rw [u₃.other _ (by decide), u₂.gpr], u₃.gpr,
      fun r h1 h2 h3 => by rw [u₃.other _ h3, u₂.other _ h2, u₁.other _ h1],
      by rw [u₃.mem, u₂.mem, u₁.mem], by rw [u₃.rd, u₂.rd, u₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr]⟩

/-- A call of `vg_gf25519_r32_mul` leaks the same in two runs `RF` relates. -/
theorem mulCall_tr (x : BitVec 32) {o a b : Nat} (ho : o + 32 ≤ 768) (ha : a + 32 ≤ 768)
    (hb : b + 32 ≤ 768) : RelCT isa (RF x) (mulCall o a b) fun _ _ => True := by
  have pre : ∀ sp, RelCT isa (fun s₁ s₂ => RF x s₁ s₂ ∧ s₁.gpr .esp = sp) (mulCall o a b)
      fun _ _ => True := by
    intro sp
    let F : State → State → Prop := fun s t =>
      t.gpr .eax = BitVec.ofNat 32 o ∧ t.gpr .ecx = BitVec.ofNat 32 a ∧ t.gpr .edx = BitVec.ofNat 32 b ∧
        (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
        t.wr = s.wr
    have movs := (RelCT.taint (A := taint) (P := fun s₁ s₂ => RF x s₁ s₂ ∧ s₁.gpr .esp = sp)
      (τr [.esp, .edi]) (fun _ _ h => RF.agree h.1)
      (c := .block [.mov .eax (.imm (BitVec.ofNat 32 o)), .mov .ecx (.imm (BitVec.ofNat 32 a)),
        .mov .edx (.imm (BitVec.ofNat 32 b))]) (movs_check o a b)).wpDep (F := F)
      fun s₁ s₂ _ => ⟨movs_ok s₁ o a b, movs_ok s₂ o a b⟩
    unfold mulCall
    refine RelCT.seq movs (RelCT.callWith mul_correct mulFn_ct [below sp (4 * callRegs.length)]
      [scR 4096 x] ?_)
    rintro t₁ t₂ ⟨-, s₁, s₂, ⟨⟨c₁, c₂, e⟩, sp₁⟩, ⟨a₁, b₁, d₁, g₁, -, -, w₁⟩, ⟨a₂, b₂, d₂, g₂, -, -, w₂⟩⟩
    have esp₁ : t₁.gpr .esp = s₁.gpr .esp := g₁ _ (by decide) (by decide) (by decide)
    have esp₂ : t₂.gpr .esp = s₂.gpr .esp := g₂ _ (by decide) (by decide) (by decide)
    have edi₁ : t₁.gpr .edi = s₁.gpr .edi := g₁ _ (by decide) (by decide) (by decide)
    have edi₂ : t₂.gpr .edi = s₂.gpr .edi := g₂ _ (by decide) (by decide) (by decide)
    have k₁ : Ctx 8192 x t₁ := c₁.keep edi₁ w₁ esp₁
    have k₂ : Ctx 8192 x t₂ := c₂.keep edi₂ w₂ esp₂
    have hsp : t₁.gpr .esp = t₂.gpr .esp := by rw [esp₁, esp₂, e]
    refine ⟨?_, ?_, hsp, ?_⟩
    · rw [← sp₁, ← esp₁]; exact callPre_mul k₁ ho ha hb a₁ b₁ d₁
    · rw [← sp₁, e, ← esp₂]; exact callPre_mul k₂ ho ha hb a₂ b₂ d₂
    · have hr : ∀ q ∈ callRegs, t₁.gpr q = t₂.gpr q := by
        intro q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl
        · rw [d₁, d₂]
        · rw [b₁, b₂]
        · rw [a₁, a₂]
        · exact k₁.edi.trans k₂.edi.symm
      have fit : 4 * callRegs.length + 4 ≤ (t₁.gpr .esp).toNat := (k₁.stk rfl (Nat.le_refl _)).1
      have ae := fun i (hi : i < 4) => callEntry_arg_eq (by decide) fit hsp hr hi
      exact ⟨by rw [State.withRegions_gpr, State.withRegions_gpr, callEntry_esp', callEntry_esp', hsp],
        ae 0 (by decide), ae 1 (by decide), ae 2 (by decide), ae 3 (by decide)⟩
  exact (RelCT.exists_ fun sp => pre sp).mono (fun s₁ s₂ h => ⟨_, h, rfl⟩) fun _ _ h => h

/-- A call of `vg_gf25519_r32_mul` leaks the same in two runs `RF` relates,
and keeps `RF`. -/
theorem mulCall_rf (x : BitVec 32) {o a b : Nat} (ho : o + 32 ≤ 768) (ha : a + 32 ≤ 768)
    (hb : b + 32 ≤ 768) : RelCT isa (RF x) (mulCall o a b) (RF x) := by
  refine ((mulCall_tr x ho ha hb).wpDep (F := fun s t => Keep s t)
    fun s₁ s₂ h => ⟨WP.mono (mulCall_ok h.1 ho ha hb) fun _ h => h.1,
      WP.mono (mulCall_ok h.2.1 ho ha hb) fun _ h => h.1⟩).mono (fun _ _ h => h) ?_
  rintro t₁ t₂ ⟨-, s₁, s₂, ⟨c₁, c₂, e⟩, k₁, k₂⟩
  exact ⟨k₁.ctx c₁, k₂.ctx c₂, by rw [k₁.esp, k₂.esp, e]⟩

end VG.Proof.X25519.X86.Field32
