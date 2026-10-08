import VerifiedGarbage.Impl.P256.EcdhJac
import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedState
import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
import VerifiedGarbage.Proof.Weierstrass.WinJacPoint

/-! Shared invariants for secret-scalar P-256 Jacobian windows. -/
namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

abbrev C := Spec.P256.curve
abbrev K := Impl.P256.EcdhJac.K
abbrev M := K.M
abbrev tc := Impl.P256.EcdhJac.tc

def ro : List Nat := winRo K
def slots : List Nat := ro++winOther K++[5400,5432]
abbrev Sl := (·∈slots)
def live : List Nat := [K.R.x,K.R.y,K.R.z]++ro
def work : List (Nat × Nat) := [(128,32),(512,544),(5400,64),(7104,576)]
def buildWork : List (Nat × Nat) := work++[(2816,2560)]
def regs : List Reg := .x19::allocatedRegs
abbrev Frame := AllocatedFrame regs

def entrySlot (a i : Nat) : Nat := 2816+160*(a-1)+32*i
def selectedSlot (i : Nat) : Nat := if i<3 then 704+32*i else 5400+32*(i-3)
def offset : Nat := 16*((32^52-1)/31)

theorem offset_eq : offset=16*Window5.geom 52 := by
  have h := Window5.geom_mul 52
  unfold offset
  omega

theorem layout : Lay M 8192 Sl where
  le := by decide +kernel
  apart := by
    have h : ∀ x∈slots,∀ y∈slots,x≠y→x+32≤y ∨ y+32≤x := by decide +kernel
    exact fun x y hx hy hxy => h x hx y hy hxy
  mo := by decide +kernel
  tmp := by decide +kernel

theorem aligned : Aligned M Sl := ⟨by decide +kernel,
  VG.Proof.Ecdsa.AArch64.MP'_A VG.Impl.Ecdsa.AArch64.p256,
  fun _ _ h => nomatch (callOf_small (M:=M) (by decide)).symm.trans h⟩

theorem regs_x0 : Reg.x0∉regs := by decide
theorem clob_regs : ∀ r∈clob 4,r∈regs := by decide
theorem allocated_regs : ∀ r∈allocatedRegs,r∈regs := fun _ hr => List.mem_cons_of_mem _ hr
theorem work_bounds : ∀ w∈work,w.1+w.2≤8192 := by decide
theorem buildWork_bounds : ∀ w∈buildWork,w.1+w.2≤8192 := by decide

structure JPt (base : Addr) (s : State) (o : Nat → Nat) (Q : Point C) : Prop where
  lt : ∀ i<5,wordsVal s.mem base (o i) 4<C.p
  jac : InvJ C (tmv C 4 base s (o 0)) (tmv C 4 base s (o 1)) (tmv C 4 base s (o 2)) Q
  z : tmv C 4 base s (o 2)≠0
  z2 : tmv C 4 base s (o 3)=tmv C 4 base s (o 2)*tmv C 4 base s (o 2)
  z3 : tmv C 4 base s (o 4)=tmv C 4 base s (o 3)*tmv C 4 base s (o 2)

def TblOk (base : Addr) (P : Point C) (n : Nat) (s : State) : Prop :=
  ∀ a,1≤a→a≤n→JPt base s (entrySlot a) (mul a P)

structure Fixed (base : Addr) (P : Point C) (k : Nat) (s : State) : Prop where
  field : Inv M base 8192 C.p Sl ro (tmv C 4 base s) s
  zero : wordsVal s.mem base K.zero 4=0
  peer : Rep C (tmv C 4 base s K.P.x) (tmv C 4 base s K.P.y) (tmv C 4 base s K.P.z) P
  one : tmv C 4 base s K.P.z=1
  bits : ∀ i<260,s.mem (off base (K.bits+i))=if (k+offset).testBit i then 1 else 0

structure RState (base : Addr) (P Q : Point C) (k : Nat) (s : State) : Prop where
  fixed : Fixed base P k s
  table : TblOk base P 16 s
  field : Inv M base 8192 C.p Sl live (tmv C 4 base s) s
  point : InvJ C (tmv C 4 base s K.R.x) (tmv C 4 base s K.R.y) (tmv C 4 base s K.R.z) Q

structure LoopInv (base : Addr) (P : Point C) (k j : Nat) (s : State) : Prop where
  state : ∃ Q,onCurve C Q=true ∧ (k<C.n→Q=mul (Window5.winE (k+offset) 52 j) P) ∧ RState base P Q k s
  counter : s.gpr .x19=BitVec.ofNat 64 j

end VG.Proof.P256.EcdhJac
