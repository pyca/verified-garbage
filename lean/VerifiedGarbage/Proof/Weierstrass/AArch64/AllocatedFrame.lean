import VerifiedGarbage.Impl.P256.VerifyRegisters
import VerifiedGarbage.Proof.Weierstrass.AArch64.Unch

/-! Internal register and memory frames for allocated arithmetic.

The allowed registers and byte ranges are explicit parameters. In particular,
this does not relax the field compiler's existing `ProgKeep` contract or the
outer function's ABI: the caller must restore its saved registers separately.
-/
namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps)

structure AllocatedFrame (rs : List Reg) (base : Addr) (W : List (Nat × Nat))
    (s t : State) : Prop where
  regs : KeepRegs rs s t
  unch : Unch base W s.mem t.mem

namespace AllocatedFrame

theorem refl (rs : List Reg) (base : Addr) (W : List (Nat × Nat)) (s : State) :
    AllocatedFrame rs base W s s := ⟨⟨fun _ _ => rfl,rfl,rfl,rfl⟩,Unch.refl base W s.mem⟩

theorem trans {rs : List Reg} {base : Addr} {W : List (Nat × Nat)} {s t u : State}
    (h : AllocatedFrame rs base W s t) (h' : AllocatedFrame rs base W t u) :
    AllocatedFrame rs base W s u :=
  ⟨h.regs.trans h'.regs,fun x hx => (h'.unch x hx).trans (h.unch x hx)⟩

theorem mono {rs rs' : List Reg} {base : Addr} {W W' : List (Nat × Nat)} {s t : State}
    (h : AllocatedFrame rs base W s t) (hr : ∀ r∈rs,r∈rs')
    (hw : ∀ w∈W,∃ w'∈W',w'.1≤w.1 ∧ w.1+w.2≤w'.1+w'.2) :
    AllocatedFrame rs' base W' s t := ⟨h.regs.mono hr,h.unch.cover hw⟩

theorem widenRegs {rs rs' : List Reg} {base : Addr} {W : List (Nat × Nat)} {s t : State}
    (h : AllocatedFrame rs base W s t) (hr : ∀ r∈rs,r∈rs') :
    AllocatedFrame rs' base W s t := ⟨h.regs.mono hr,h.unch⟩

theorem of_keeps {rs : List Reg} {base : Addr} {W : List (Nat × Nat)} {s t : State}
    (h : Keeps rs s t) : AllocatedFrame rs base W s t :=
  ⟨Keeps.regs h,fun _ _ => congrFun h.mem _⟩

theorem of_prog {M : Mod} {base : Addr} {V : List Nat} {rs : List Reg}
    {W : List (Nat × Nat)} {s t : State} (h : ProgKeep M base V s t)
    (hr : ∀ r∈clob M.n,r∈rs)
    (hw : ∀ w∈V.map (·,8*M.n)++[(M.tmp,8*M.n)],
      ∃ w'∈W,w'.1≤w.1 ∧ w.1+w.2≤w'.1+w'.2) : AllocatedFrame rs base W s t :=
  ⟨(⟨h.gpr,h.rd,h.wr,h.sp⟩ : KeepRegs (clob M.n) s t).mono hr,h.unch.cover hw⟩

theorem scr {rs : List Reg} {base : Addr} {W : List (Nat × Nat)} {size : Nat} {s t : State}
    (h : AllocatedFrame rs base W s t) (h0 : Reg.x0∉rs) (hs : Scr s base size) :
    Scr t base size := hs.of_keepRegs h.regs h0

end AllocatedFrame

/-- Allocation never consumes the scratch pointer or the joint loop counter. -/
def allocatedRegs : List Reg := VG.Impl.P256.VerifyRegisters.pool

theorem allocatedRegs_x0 : Reg.x0∉allocatedRegs := by decide
theorem allocatedRegs_x19 : Reg.x19∉allocatedRegs := by decide

theorem clob4_allocatedRegs : ∀ r∈clob 4,r∈allocatedRegs := by decide

end VG.Proof.Weierstrass.AArch64
