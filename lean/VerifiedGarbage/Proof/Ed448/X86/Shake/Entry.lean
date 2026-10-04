import VerifiedGarbage.Proof.Ed448.X86.Shake.Layout
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.OffsetBelow

/-!
# Ed448 on x86 (32-bit): a complete operation's frame, from its caller

A complete operation pushes 64 words (`Impl/Ed25519/X86/PublicKey.lean`'s
frame): `base s` is `esp` after the push, the caller's `n` argument words
(`ARGS s n`) are at `base s + 260`, and the stack the operation uses is the
280 bytes below its return address (`stack_eq`). `push_ctx`: after the push,
`Whole.Ctx` holds of the regions the operation reads and writes; `kit`: the
layout facts the calls need (`Kit`), from its precondition's;
`pop_abi`: after the pop, the callee-saved registers and the return address
are as they were.
-/

namespace VG.Proof.Ed448.X86.Shake

open VG VG.X86
open VG.Proof.Ed25519.X86 (Whole.Ctx Whole.FR Whole.STK Whole.Within)

/-- The frame's base: `esp` after the push of 64 words. -/
abbrev base (s : State) : BitVec 32 := s.gpr .esp - BitVec.ofNat 32 256

/-- The caller's `n` argument words. -/
abbrev ARGS (s : State) (n : Nat) : Region := ⟨argAddr s 0, 4 * n⟩

/-- The return address. -/
abbrev RET (s : State) : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩

theorem whole (r : Region) : Whole.Within r r := ⟨0, (BitVec.add_zero _).symm, by simp⟩

variable {s : State} {n : Nat}

theorem arg_address (s : State) (j : Nat) : addr (base s) (260 + 4 * j) = argAddr s j := by
  simp only [addr, base, argAddr]
  rw [show 260 + 4 * j = 256 + (4 + 4 * j) by omega, BitVec.ofNat_add,
    ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem args_val (s : State) (n : Nat) : Args (base s) n (arg s) s.mem := fun i _ => by
  rw [arg_address]; rfl

theorem stack_eq (hb : 280 ≤ (s.gpr .esp).toNat) : Whole.STK (base s) = below (s.gpr .esp) 280 := by
  simp only [Whole.STK, below, base]
  rw [Taint.sub_setWidth (by omega : 256 ≤ (s.gpr .esp).toNat),
    Taint.sub_setWidth hb, BitVec.sub_sub]
  rfl

theorem base_toNat (hb : 280 ≤ (s.gpr .esp).toNat) : (base s).toNat = (s.gpr .esp).toNat - 256 :=
  sub_toNat (by omega)

theorem argAddr64 (ha : (s.gpr .esp).toNat + 4 + 4 * n ≤ 2 ^ 32) {j : Nat} (hj : j < n) :
    argAddr s j = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * j) :=
  addr_eq (by omega)

theorem args_stack (hb : 280 ≤ (s.gpr .esp).toNat) (ha : (s.gpr .esp).toNat + 4 + 4 * n ≤ 2 ^ 32) (hn : 0 < n) :
    (ARGS s n).Disjoint (below (s.gpr .esp) 280) := by
  change Region.Disjoint ⟨argAddr s 0, 4 * n⟩ ⟨((s.gpr .esp) - BitVec.ofNat 32 280).setWidth 64, 280⟩
  rw [argAddr64 ha hn, Taint.sub_setWidth hb]
  exact (Offset.disjoint_below_above _ (m := 280) (a := 4 + 4 * 0) (l := 4 * n) (by omega)).symm

theorem args_contains (ha : (s.gpr .esp).toNat + 4 + 4 * n ≤ 2 ^ 32) {j : Nat} (hj : j < n) :
    (ARGS s n).Contains (argAddr s j) 4 := by
  change (⟨argAddr s 0, 4 * n⟩ : Region).Contains _ _
  rw [argAddr64 ha (by omega), argAddr64 ha hj]
  exact Offset.contains _ (by omega) (by omega) (by omega)

/-- The layout facts the calls need, from the precondition's. -/
theorem kit {sc : Nat} {ins outs : List Region} (hb : 280 ≤ (s.gpr .esp).toNat)
    (ha : (s.gpr .esp).toNat + 4 + 4 * n ≤ 2 ^ 32) (hnc : (arg s sc).toNat + 8192 ≤ 2 ^ 32)
    (so : SCR (arg s sc) ∈ outs) (ko : ∀ R ∈ outs, (below (s.gpr .esp) 280).Disjoint R)
    (io : ∀ r ∈ ins, ∀ R ∈ outs, r.Disjoint R) (is : ∀ r ∈ ins, r.Disjoint (below (s.gpr .esp) 280))
    (hargs : ARGS s n ∈ ins) : Kit (base s) (arg s sc) n ins outs := by
  have hE := base_toNat hb
  refine ⟨by omega, by omega, hnc, so, fun R hR => stack_eq hb ▸ ko R hR, fun r hr R hR => ?_,
    fun i hi => ⟨ARGS s n, hargs, by rw [arg_address]; exact args_contains ha hi⟩⟩
  rcases List.mem_append.mp hR with hR | hR
  · exact io r hr R hR
  · rw [List.mem_singleton.mp hR, stack_eq hb]; exact is r hr

/-- After the push, the frame's invariant holds of the regions the operation
reads (`ins`) and writes (`outs`). -/
theorem push_ctx {ins outs : List Region} (hrd : s.rd = ins) (hwr : s.wr = outs)
    (hb : 280 ≤ (s.gpr .esp).toNat) :
    Whole.Ctx (base s) s.gpr s.mem ins outs (pushed (List.replicate 64 .eax) s) := by
  have hf := pushed_frame (s := s) (rs := List.replicate 64 .eax) (by simp)
    (by simp only [List.length_replicate]; omega)
  refine ⟨(pushed_rd _ _).trans hrd, ?_, ?_, fun r _ hn => pushed_gpr _ _ hn, ?_⟩
  · rw [pushed_wr, hwr]
    simp only [List.length_replicate]
  · rw [pushed_esp, List.length_replicate]
  · refine Frame.sub hf fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    refine ⟨Whole.STK (base s), List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
    rw [stack_eq hb]
    exact below_sub (by simp) hb

/-- After the pop, the callee-saved registers and the return address. -/
theorem pop_abi {ins outs : List Region} {u : State} {q : Reg} (hq : q ∉ calleeSaved)
    (hb : 280 ≤ (s.gpr .esp).toNat)
    (hu : Whole.Ctx (base s) s.gpr s.mem ins outs u) (hret : ∀ R ∈ outs, (RET s).Disjoint R) :
    abiPreserved s (popped q (List.replicate 64 Reg.eax).length u) := by
  refine ⟨fun r hr => ?_, ?_⟩
  · by_cases he : r = .esp
    · subst r
      rw [popped_esp, hu.esp, List.length_replicate]
      exact BitVec.sub_add_cancel _ _
    · rw [popped_gpr _ _ _ he (by intro e; subst r; exact hq hr), hu.cs r hr he]
  · rw [popped_mem]
    refine hu.frame.readW (r := RET s) (Region.contains_self _ _) ?_ (by decide)
    intro R hR
    rcases List.mem_append.mp hR with hR | hR
    · exact hret R hR
    · rw [List.mem_singleton.mp hR, stack_eq hb]
      change Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩
        ⟨(s.gpr .esp - BitVec.ofNat 32 280).setWidth 64, 280⟩
      rw [Taint.sub_setWidth hb]
      exact (Offset.below_disjoint _ (by decide)).symm

/-- `abiPreserved` from a state that differs from the entry state only in
registers that are not callee-saved. -/
theorem abi_of {s' u : State} (hs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) (hm : s'.mem = s.mem)
    (h : abiPreserved s' u) : abiPreserved s u := by
  have he := hs .esp (by simp [calleeSaved])
  refine ⟨fun r hr => (h.1 r hr).trans (hs r hr), ?_⟩
  have := h.2
  rw [he, hm] at this
  exact this

end VG.Proof.Ed448.X86.Shake
