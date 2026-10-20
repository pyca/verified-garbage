module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Prepare
public import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Omega

/-! # A Montgomery context of private CRT at a run-time width

`CtxOk c M`: the inputs, the odd modulus `M` above one in slot 0 of the
context `c`, and `-M⁻¹ mod 2³²` in the header. A multiplication keeps it
(`cmul_ok`), as does any stage that changes neither (`CtxOk.keepF`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86

structure CtxOk (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (c : Ctx) (M : Nat) (s : State) :
    Prop where
  inp : In base bytes len args s
  mod : sv s.mem base len c 0 = M
  gt : 1 < M
  odd : M % 2 = 1
  inv : (M * w32 s.mem base invOff + 1) % 2 ^ 32 = 0

section
variable {s t : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {c : Ctx} {M : Nat}

/-- `R = 2^(8 Bc)` is prime to `M`. -/
theorem CtxOk.coprime (C : CtxOk base bytes len args c M s) : Nat.Coprime (2 ^ (8 * bc len c)) M :=
  VG.Proof.Bignum.coprime_pow2 C.odd _

theorem CtxOk.keepF (C : CtxOk base bytes len args c M s) {regs : List Reg} (K : Keeps regs s t)
    (di : .edi ∉ regs) (sp : .esp ∉ regs) {ws : List (Nat × Nat)}
    (F : Frame (frameR base (s.gpr .esp) ws) s.mem t.mem) (hfit : ∀ p ∈ ws, p.1 + p.2 ≤ bytes)
    (h0 : ∀ p ∈ ws, numBase + bc len c ≤ p.1) : CtxOk base bytes len args c M t := by
  have h := C.inp
  have nw := h.crt.scratch.nowrap
  have f0 := h.slot_fit c (j := 0) (by decide)
  have bw := bc_eq_cwc len c
  have z0 : lo len (.slot c 0) = numBase := sl_zero len c
  have est : st len c = 2 * bc len c + 32 := rfl
  refine ⟨h.keepF K di sp F hfit, ?_, C.gt, C.odd, ?_⟩
  · have hm := C.mod
    simp only [sv, z0] at hm ⊢
    rw [frameR_val32 F h.crt.room nw (by omega) (fun p hp => .inl (by have := h0 p hp; omega)) hfit]
    exact hm
  · rw [← w32_val32_one, frameR_val32 F h.crt.room nw (by simp only [invOff, numBase] at *; omega)
      (fun p hp => .inl (by have := h0 p hp; simp only [invOff, numBase] at *; omega)) hfit, w32_val32_one]
    exact C.inv

/-- The ranges of a multiplication into slot `o`. -/
abbrev mulR (len : Nat) (c : Ctx) (o : Nat) : List (Nat × Nat) :=
  [(lo len (.slot c o), bc len c), (lo len (.slot c 1), 3 * bc len c + 56)]

theorem cmul_ok (C : CtxOk base bytes len args c M s) {o a b : Nat} (ho3 : 3 ≤ o) (ho : o ≤ 8) (ha3 : 3 ≤ a)
    (ha : a ≤ 8) (hb3 : 3 ≤ b) (hb : b ≤ 8) (hB : sv s.mem base len c b < M) :
    WP isa (mul c o a b) s fun t =>
      CtxOk base bytes len args c M t ∧ Keeps [.eax, .ecx, .edx] s t ∧
      Frame (frameR base (s.gpr .esp) (mulR len c o)) s.mem t.mem ∧
      sv t.mem base len c o < M ∧
      sv t.mem base len c o * 2 ^ (8 * bc len c) % M = sv s.mem base len c a * sv s.mem base len c b % M := by
  have h := C.inp
  have f8 := h.slot_fit c (j := 8) (by decide)
  have z0 : lo len (.slot c 0) = numBase := sl_zero len c
  have est : st len c = 2 * bc len c + 32 := rfl
  have bw := bc_eq_cwc len c
  have g := bc_ge h.lower' c
  have hm := C.mod
  simp only [sv, z0] at hm hB
  have ok := mul_ok h c ho3 ho ha3 ha hb3 hb (by rw [hm]; exact C.inv) (by rw [hm]; exact hB)
  rw [hm] at ok
  refine WP.mono ok fun t ⟨cs, rd, wr, F, L, V⟩ => ?_
  have Ks : Keeps [.eax, .ecx, .edx] s t := ⟨fun r hr => by
    have := cs r; revert hr this; cases r <;> simp [calleeSaved], rd, wr⟩
  have F' : Frame (frameR base (s.gpr .esp) (mulR len c o)) s.mem t.mem := frameR_of_mul F (by simp) (by simp)
  have mo : ∀ j, 3 ≤ j → j ≤ 8 → numBase + 3 * st len c ≤ lo len (.slot c j) ∧
      lo len (.slot c j) + st len c ≤ lo len (.slot c 8) + st len c := fun j h3 h8 => by
    have := Nat.mul_le_mul_right (st len c) h3
    have := Nat.mul_le_mul_right (st len c) h8
    simp only [lo]; omega
  obtain ⟨o1, o2⟩ := mo o ho3 ho
  have s1 : lo len (.slot c 1) = numBase + st len c := by simp [lo]
  refine ⟨C.keepF Ks (by decide) (by decide) F' (by
      intro p hp; simp only [mulR, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> dsimp only <;> omega) (by
      intro p hp; simp only [mulR, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> dsimp only <;> omega), Ks, F', L, V⟩

/-- The context holds after register changes but `edi` and `esp`. -/
theorem CtxOk.regs (C : CtxOk base bytes len args c M s) {regs : List Reg} (K : Keeps regs s t)
    (m : t.mem = s.mem) (di : .edi ∉ regs := by decide) (sp : .esp ∉ regs := by decide) :
    CtxOk base bytes len args c M t :=
  ⟨C.inp.regs K m di sp, by rw [sv, m]; exact C.mod, C.gt, C.odd, by rw [m]; exact C.inv⟩

end

end VG.Proof.Bignum.X86.CrtRt
