module

public import VerifiedGarbage.Proof.Poly1305.PPC64LE.Setup
public import VerifiedGarbage.Proof.Poly1305.PPC64LE.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Poly1305.PPC64LE.Setup
meta import VerifiedGarbage.Proof.Poly1305.PPC64LE.Contract
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# Poly1305 on PPC64LE: `init`
-/

@[expose] public section

namespace VG.Proof.Poly1305.PPC64LE

open VG VG.PPC64LE VG.Impl.Poly1305.PPC64LE
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr leBytes)

/-- No instruction of `c` writes a register of `rs`. -/
def Untouched (c : Prog isa) (rs : List Reg) : Prop := ∀ r ∈ rs, ∀ i ∈ instrs c, dstOf i ≠ some r

theorem Untouched.of_all {c : Prog isa} {rs : List Reg}
    (h : ((instrs c).all fun i => rs.all fun r => dstOf i != some r) = true) : Untouched c rs := by
  intro r hr i hi
  have := List.all_eq_true.mp (List.all_eq_true.mp h i hi) r hr
  simpa using this

/-- The 32 bytes at `p` as four little-endian words. -/
theorem bytesAt_32 (m : Mem) (p : Addr) :
    bytesAt m p 32 = leBytes 8 (m.readW (off p 0) 64).toNat ++ leBytes 8 (m.readW (off p 8) 64).toNat ++
      leBytes 8 (m.readW (off p 16) 64).toNat ++ leBytes 8 (m.readW (off p 24) 64).toNat := by
  rw [show 32 = 8 + (8 + (8 + 8)) from rfl, Poly1305.bytesAt_add, Poly1305.bytesAt_add,
    Poly1305.bytesAt_add, Poly1305.bytesAt_leBytes_64, Poly1305.bytesAt_leBytes_64,
    Poly1305.bytesAt_leBytes_64, Poly1305.bytesAt_leBytes_64]
  simp only [off, add_ofNat_zero, BitVec.add_assoc, ← BitVec.ofNat_add, List.append_assoc]

/-- The memory `init` leaves. -/
def initMem (m : Mem) (st key : Addr) : Mem :=
  ((((((m.writeW (off st 24) (m.readW (off key 0) 64)).writeW (off st 32) (m.readW (off key 8) 64)).writeW
    (off st 40) (m.readW (off key 16) 64)).writeW (off st 48) (m.readW (off key 24) 64)).writeW
    (off st 0) (BitVec.ofNat 64 0)).writeW (off st 8) (BitVec.ofNat 64 0)).writeW (off st 16)
    (BitVec.ofNat 64 0)

section
variable (s₀ : State)
abbrev ist : Addr := s₀.gpr .r3
abbrev kp : Addr := s₀.gpr .r4
end

structure IPre (s₀ : State) : Prop where
  rd : s₀.rd = [⟨kp s₀, 32⟩]
  wr : s₀.wr = [sR (ist s₀)]
  st_key : (sR (ist s₀)).Disjoint ⟨kp s₀, 32⟩

set_option simprocs false in
theorem init_exec {s₀ : State} (hp : IPre s₀) :
    WP isa init s₀ fun s' => s'.mem = initMem s₀.mem (ist s₀) (kp s₀) ∧
      ∀ r, r ∉ [Reg.r5, .r6, .r7, .r8] → s'.gpr r = s₀.gpr r := by
  have o : ∀ d, d + 8 ≤ 128 → InRegions s₀.wr (off (ist s₀) d) 8 :=
    fun d hd => ⟨_, by rw [hp.wr]; exact List.mem_singleton_self _, contains_off hd (by omega)⟩
  have i : ∀ d, d + 8 ≤ 32 → InRegions (s₀.rd ++ s₀.wr) (off (kp s₀) d) 8 :=
    fun d hd => ⟨_, by rw [hp.rd]; exact List.mem_append_left _ (List.mem_singleton_self _),
      contains_off hd (by omega)⟩
  have o0 := o 0 (by decide); have o8 := o 8 (by decide); have o16 := o 16 (by decide)
  have o24 := o 24 (by decide); have o32 := o 32 (by decide); have o40 := o 40 (by decide)
  have o48 := o 48 (by decide)
  have i0 := i 0 (by decide); have i8 := i 8 (by decide); have i16 := i 16 (by decide)
  have i24 := i 24 (by decide)
  simp only [off, ist, kp] at o0 o8 o16 o24 o32 o40 o48 i0 i8 i16 i24
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d, exec_store_d, exec_li, State.write, o0, o8, o16, o24, o32, o40, o48, i0, i8, i16,
    i24, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem initMem_frame (m : Mem) (st key : Addr) : Frame [sR st] m (initMem m st key) := by
  have c : ∀ d, d + 8 ≤ 128 → (sR st).Contains (off st d) (64 / 8) :=
    fun d hd => contains_off hd (by omega)
  simp only [initMem]
  refine ((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 24 ?_)).writeW
    (List.mem_singleton_self _) _ (c 32 ?_)).writeW (List.mem_singleton_self _) _ (c 40 ?_)).writeW
    (List.mem_singleton_self _) _ (c 48 ?_)).writeW (List.mem_singleton_self _) _ (c 0 ?_)).writeW
    (List.mem_singleton_self _) _ (c 8 ?_) |>.writeW (List.mem_singleton_self _) _ (c 16 ?_)
  all_goals decide

set_option simprocs false in
theorem initMem_word (m : Mem) (st key : Addr) {j : Nat} (hj : j < 4) :
    (initMem m st key).readW (off st (24 + 8 * j)) 64 = m.readW (off key (8 * j)) 64 := by
  simp only [initMem]
  obtain rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  all_goals simp (config := {decide := true}) only [Nat.mul_zero, Nat.add_zero, Nat.mul_one,
    Mem.readW_writeW_self64, readW_writeW_off]

set_option simprocs false in
theorem initMem_acc (m : Mem) (st key : Addr) :
    leNum (bytesAt (initMem m st key) st 24) = 0 := by
  rw [leNum_acc]
  simp (config := {decide := true}) only [w64, initMem, Mem.readW_writeW_self64, readW_writeW_off]

theorem init_correct {s₀ : State} (hp : IPre s₀) :
    WP isa init s₀ fun s' => (∀ r, r ∉ [Reg.r5, .r6, .r7, .r8] → s'.gpr r = s₀.gpr r) ∧
      Proof.Poly1305.initPPC64LE.post s₀ s' := by
  refine WP.mono (init_exec hp) fun s' ⟨hm, hg⟩ => ⟨hg, rfl, ?_, ?_⟩
  · rw [← off_24, hm, bytesAt_32, bytesAt_32, off_off, off_off, off_off, off_off,
      initMem_word _ _ _ (j := 0) (by decide), initMem_word _ _ _ (j := 1) (by decide),
      initMem_word _ _ _ (j := 2) (by decide), initMem_word _ _ _ (j := 3) (by decide)]
  · rw [hm, initMem_acc]
    rfl

/-- A state satisfying the precondition. -/
def initSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | _ => 0
  lr := 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x2000, 32⟩]
  wr := [⟨0x1000, 128⟩]

theorem init_verified : Verified PPC64LE.target init Proof.Poly1305.initPPC64LE := by
  refine ⟨fun s hs => ?_, ?_, ⟨initSat, rfl, rfl, Region.disjoint_of_sep (by decide)⟩⟩
  · obtain ⟨h1, h2, h3⟩ := hs
    obtain ⟨t, s', he, hk, h⟩ := init_correct ⟨h1, h2, h3⟩
    exact ⟨t, s', he, ⟨fun r hr => hk r (by revert r; decide), Exec.sp he,
      Exec.lr he (by decide +kernel) (by rw [← Code.allInstrs_eq]; decide +kernel)⟩, h⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, hsp⟩
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [VG.PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> with_reducible assumption

end VG.Proof.Poly1305.PPC64LE
