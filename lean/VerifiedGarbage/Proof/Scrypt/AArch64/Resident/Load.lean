module

public import VerifiedGarbage.Proof.Scrypt.AArch64.Resident.Words
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Range

@[expose] public section
namespace VG.Proof.Scrypt.AArch64.Resident
open VG VG.AArch64 VG.Spec.Scrypt
open VG.Proof.Scrypt.AArch64 (Holds Words wreg_inj)
open VG.Impl.Scrypt.AArch64 (wreg)

structure LI (s₀ : State) (i : Nat) (s : State) : Prop where
  holds : ∀ j (hj : j < 16), j < i → s.gpr (wreg j) = (words s₀.mem (s₀.gpr .x24))[j].setWidth 64
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  keep : ∀ r, ¬ Words r → s.gpr r = s₀.gpr r

theorem load_step {s₀ s : State} {i : Nat} (hi : i < 16)
    (hin : ∀ j < 16, InRegions (s₀.rd ++ s₀.wr) (addr (s₀.gpr .x24) j) 4)
    (h : LI s₀ i s) :
    WP isa (.block [VG.Impl.Scrypt.AArch64.Resident.loadWord i]) s (LI s₀ (i+1)) := by
  have n24 := (pin_ne (r := .x24) (by simp)).1
  have hx : s.gpr .x24 = s₀.gpr .x24 := h.keep _ n24
  have ir : InRegions (s.rd ++ s.wr) (s.gpr .x24 + BitVec.ofNat 64 (4*i)) 4 := by
    rw [h.rd,h.wr,hx]; exact hin i hi
  apply WP.of_runBlock
  simp only [VG.Impl.Scrypt.AArch64.Resident.loadWord,runBlock_cons,runStep_some,runBlock_nil,
    exec_ldr_w (show 4*i % 4 = 0 ∧ 4*i < 16384 by omega) ir,isa,Option.some.injEq,exists_eq_left']
  refine ⟨?_,h.mem,h.rd,h.wr,h.sp,?_⟩
  · intro j hj hji
    rcases Nat.lt_succ_iff_lt_or_eq.mp hji with hji | rfl
    · have ne : wreg j ≠ wreg i := fun e => (by omega : j ≠ i) (wreg_inj hj hi e)
      simp only [State.write,ne,ite_false]
      exact h.holds j hj hji
    · simp only [State.write,ite_true,Size.bits,h.mem,hx,words_get _ _ hi,addr]
  · intro r hr
    have ne : r ≠ wreg i := fun e => hr ⟨i,hi,e⟩
    simp only [State.write,ne,ite_false]
    exact h.keep r hr

theorem load_ok (s₀ : State)
    (hin : ∀ j < 16, InRegions (s₀.rd ++ s₀.wr) (addr (s₀.gpr .x24) j) 4) :
    WP isa (.block VG.Impl.Scrypt.AArch64.Resident.load) s₀ (LI s₀ 16) := by
  have eq : VG.Impl.Scrypt.AArch64.Resident.load =
      (List.range 16).flatMap (fun i => [VG.Impl.Scrypt.AArch64.Resident.loadWord i]) := by
    decide +kernel
  rw [eq]
  exact wp_range_flatMap (M := isa) (LI s₀) (fun i s hi h => load_step hi hin h)
    16 (by omega) s₀ ⟨fun _ _ h => by omega,rfl,rfl,rfl,rfl,fun _ _ => rfl⟩
end VG.Proof.Scrypt.AArch64.Resident
