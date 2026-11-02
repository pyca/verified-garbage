module

import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeControl
public import VerifiedGarbage.Proof.Rsa.MontContract
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeState

/-! Arithmetic values that persist throughout public comb table construction. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt Keeps Operand)
open VG.Proof.X25519.Arm (Rest)

structure Core (p : Inputs) (sp : BitVec 32) (s : State) : Prop where
  memory : Memory p sp s
  modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P
  odd : p.P % 2 = 1
  r2 : numAt s.mem (State.addr p.base) p.w 4 = 2^(128*p.w)%p.P
  one : numAt s.mem (State.addr p.base) p.w 7 = 1

def Power5 (p : Inputs) (exponent : Nat) (s : State) : Prop :=
  numAt s.mem (State.addr p.base) p.w 5 = Spec.Rsa.powMod p.G exponent p.P * 2^(64*p.w) % p.P

theorem Core.after_workspace {p : Inputs} {sp : BitVec 32} {s t : State}
    (h : Core p sp s) (memory : Memory p sp t)
    (eq : WorkspaceEq (State.addr p.base) (8*p.len) s.mem t.mem) : Core p sp t := by
  have fit := h.memory.ready.width ▸ h.memory.ready.layout.2.2.1
  exact ⟨memory,(eq.number fit (by decide : 0<8)).trans h.modulus,h.odd,
    (eq.number fit (by decide : 4<8)).trans h.r2,(eq.number fit (by decide : 7<8)).trans h.one⟩

theorem Core.after_array {p : Inputs} {sp : BitVec 32} {s t : State} {o : Nat}
    (h : Core p sp s) (memory : Memory p sp t)
    (keep : Keeps (State.addr p.base) p.len p.w o s.mem t.mem)
    (h0 : 0 ≠ o) (h4 : 4 ≠ o) (h7 : 7 ≠ o) : Core p sp t := by
  have fit := h.memory.ready.width ▸ h.memory.ready.layout.2.2.1
  have operand (a : Nat) (ha : a=0 ∨ a=4 ∨ a=7) : Operand a := by
    rcases ha with rfl|rfl|rfl <;> simp [Operand,Proof.Rsa.Mont.aAcc,Proof.Rsa.Mont.aTmp]
  exact ⟨memory,(keeps_array_num keep fit (operand 0 (by simp)) h0).trans h.modulus,h.odd,
    (keeps_array_num keep fit (operand 4 (by simp)) h4).trans h.r2,
    (keeps_array_num keep fit (operand 7 (by simp)) h7).trans h.one⟩

theorem Power5.after_workspace {p : Inputs} {sp : BitVec 32} {s t : State} {exponent : Nat}
    (h : Core p sp s) (power : Power5 p exponent s)
    (eq : WorkspaceEq (State.addr p.base) (8*p.len) s.mem t.mem) : Power5 p exponent t := by
  have fit := h.memory.ready.width ▸ h.memory.ready.layout.2.2.1
  exact (eq.number fit (by decide : 5<8)).trans power

end VG.Proof.Ffdh.Arm.CombBuilder
