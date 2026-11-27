module

public import VerifiedGarbage.Proof.Sm4Gcm.Arm.Run
public import VerifiedGarbage.Proof.Sm4Gcm.Arm.Fn
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! ### `Sm4Gcm.Arm.Entry`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on ARMv7: the stack arguments, and the entry of the functions

Untrusted: everything here is checked by Lean. The functions other than
`init` load `W` from the stack (`ldr r12, [sp, #off]`) and save our caller's
registers there (`entry_ok`); they read their other stack arguments when they
need them, which no write changes (`arg_frame`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Sm4Gcm.Arm
open VG.Spec.Aes (bytesAt)

theorem stackArg_eq (s : State) (k : Nat) :
    stackArg s k = s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 (4 * k))) 32 := rfl

theorem stackArg_zero (s : State) : stackArg s 0 = s.mem.readW (State.addr s.sp) 32 := by
  simp only [stackArg, stackArgAddr, Nat.mul_zero, add_ofNat_zero]

/-- The stack argument `i` (of `n`) is readable. -/
theorem arg_in {s : State} {n i : Nat} (hi : i < n) (hf : s.sp.toNat + 4 * n ≤ 2 ^ 32) (h : args s n ∈ s.rd) :
    InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 (4 * i))) 4 := by
  have e : State.addr (s.sp + BitVec.ofNat 32 (4 * i)) = stackArgAddr s 0 + BitVec.ofNat 64 (4 * i) := by
    simp only [stackArgAddr, Nat.mul_zero, add_ofNat_zero]; exact addr_add (by omega_using [hi, hf])
  rw [e]; exact in_off (covers_of_mem (List.mem_append_left _ h)) (by omega_using [hi]) (by omega_using [hf])

/-- The stack arguments stay where they are, outside a frame. -/
theorem arg_frame {s s' : State} {n : Nat} {rs : List Region} (hsp : s'.sp = s.sp)
    (hf : s.sp.toNat + 4 * n ≤ 2 ^ 32) (hfr : Frame rs s.mem s'.mem) (hd : ∀ r ∈ rs, (args s n).Disjoint r)
    {i : Nat} (hi : i < n) : stackArg s' i = stackArg s i := by
  have e : stackArgAddr s i = stackArgAddr s 0 + BitVec.ofNat 64 (4 * i) := by
    simp only [stackArgAddr, Nat.mul_zero, add_ofNat_zero]; exact addr_add (by omega_using [hf, hi])
  have hs : Region.Sub ⟨stackArgAddr s i, 4⟩ (args s n) := by rw [e]; exact Offset.sub_base _ (by omega_using [hi])
  simp only [stackArg, show stackArgAddr s' i = stackArgAddr s i by simp only [stackArgAddr, hsp]]
  exact hfr.readW (Region.contains_self _ _) (fun r hr => (hd r hr).sub_left hs) (by decide)

/-- The entry: `W` loaded from the stack into `r12`, and our caller's
registers saved there. -/
theorem entry_ok {s : State} {off : Nat} (hoff : off < 4096)
    (harg : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 off)) 4)
    (hfit : (s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 off)) 32).toNat + 768 ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr (s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 off)) 32), 768⟩] s.wr)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr .r12 = s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 off)) 32 →
      (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      SavedAt s'.mem (s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 off)) 32) s →
      Frame [savedR (s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 off)) 32)] s.mem s'.mem →
      WP isa (.block rest) s' Q) :
    WP isa (.block (.ldrSp .r12 off :: (save .r12 ++ rest))) s Q := by
  rw [← List.singleton_append]
  refine WP.block_append (WP.of_runBlock ⟨s.setReg .r12 (s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 off)) 32), ?_, ?_⟩)
  · arun [hoff, harg]
  refine save_ok (s := s.setReg .r12 (s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 off)) 32)) (b := .r12) (by simp [gpr_setReg]) hfit hw fun s' g rd wr sp sv fr => k s' ?_ ?_ rd wr sp ?_ fr
  · rw [g]; simp [gpr_setReg]
  · intro r hr; rw [g]; simp [gpr_setReg, hr]
  · intro p hp
    rw [sv p hp]
    have : p.1 ≠ .r12 := by
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simp [gpr_setReg, this]

end VG.Proof.Sm4Gcm.Arm

end

end

/-!
# SM4-GCM on ARMv7: stack arguments read after other code

Untrusted: everything here is checked by Lean. `ArgsKeep n s₀ s`: the stack
pointer, the permissions and the first `n` stack arguments of `s` are those
of `s₀`; code that writes only regions apart from the arguments keeps it
(`ArgsKeep.frame`), and `ldr rX, [sp, #4i]` then loads argument `i` of `s₀`
(`ArgsKeep.read`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.Arm

open VG VG.Arm

theorem argAddr_zero (s : State) : stackArgAddr s 0 = State.addr s.sp := by
  simp only [stackArgAddr, Nat.mul_zero, add_ofNat_zero]

theorem args_sp {s s' : State} (h : s'.sp = s.sp) (n : Nat) : args s' n = args s n := by
  simp only [args, stackArgAddr, h]

/-- The stack below `sp` is apart from the stack arguments. -/
theorem below_args (s : State) {n : Nat} (hf : s.sp.toNat + 4 * n ≤ 2 ^ 32) : (below s.sp).Disjoint (args s n) := by
  simp only [args, argAddr_zero]
  exact (Offset.base_disjoint_below (State.addr s.sp) (n := 1520) (k := 4 * n) (by omega_using [hf])).symm

/-- The low word of a 64-bit length gives it modulo 16. -/
theorem low_mod16 {hi lo : BitVec 32} {L : Nat} (h : hi ++ lo = BitVec.ofNat 64 L) : lo.toNat % 16 = L % 16 := by
  have e := congrArg BitVec.toNat h
  rw [Proof.Gcm.toNat_append, BitVec.toNat_ofNat] at e
  have : L % 2 ^ 64 % 16 = L % 16 := Nat.mod_mod_of_dvd _ (by decide)
  omega_using [e]

structure ArgsKeep (n : Nat) (s₀ s : State) : Prop where
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  arg : ∀ i < n, stackArg s i = stackArg s₀ i

theorem ArgsKeep.refl (n : Nat) (s : State) : ArgsKeep n s s := ⟨rfl, rfl, rfl, fun _ _ => rfl⟩

theorem ArgsKeep.of_eq {n : Nat} {s₀ s s' : State} (h : ArgsKeep n s₀ s) (hm : s'.mem = s.mem) (hsp : s'.sp = s.sp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : ArgsKeep n s₀ s' :=
  ⟨hsp.trans h.sp, hrd.trans h.rd, hwr.trans h.wr, fun i hi => by
    rw [← h.arg i hi]; simp only [stackArg, stackArgAddr, hm, hsp]⟩

theorem ArgsKeep.frame {n : Nat} {s₀ s s' : State} (h : ArgsKeep n s₀ s) (hf : s₀.sp.toNat + 4 * n ≤ 2 ^ 32)
    {rs : List Region} (hfr : Frame rs s.mem s'.mem) (hd : ∀ r ∈ rs, (args s₀ n).Disjoint r) (hsp : s'.sp = s.sp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : ArgsKeep n s₀ s' := by
  refine ⟨hsp.trans h.sp, hrd.trans h.rd, hwr.trans h.wr, fun i hi => ?_⟩
  rw [← h.arg i hi]
  exact arg_frame hsp (by rw [h.sp]; exact hf) hfr (fun r hr => by rw [args_sp h.sp]; exact hd r hr) hi

theorem ArgsKeep.read {n : Nat} {s₀ s : State} (h : ArgsKeep n s₀ s) (hf : s₀.sp.toNat + 4 * n ≤ 2 ^ 32)
    (hin : args s₀ n ∈ s₀.rd) {i : Nat} (hi : i < n) :
    InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 (4 * i))) 4 ∧
      s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 (4 * i))) 32 = stackArg s₀ i :=
  ⟨arg_in hi (by rw [h.sp]; exact hf) (by rw [h.rd, args_sp h.sp]; exact hin), h.arg i hi⟩

/-- `ArgsKeep.read`, at a literal offset. -/
theorem ArgsKeep.at {n : Nat} {s₀ s : State} (h : ArgsKeep n s₀ s) (hf : s₀.sp.toNat + 4 * n ≤ 2 ^ 32)
    (hin : args s₀ n ∈ s₀.rd) (i : Nat) {off : Nat} (hi : i < n) (hoff : 4 * i = off) :
    InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 off)) 4 ∧
      s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 off)) 32 = stackArg s₀ i := by
  subst hoff; exact h.read hf hin hi

end VG.Proof.Sm4Gcm.Arm
