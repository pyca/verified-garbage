module

public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontCall
public import VerifiedGarbage.Proof.Mont.PPC64LE.Words

/-!
# What the curves' code keeps, on PPC64LE

Code that calls the Montgomery functions changes the link register, which
the functions built on it save; what the code keeps is the registers but
some, the regions and the stack pointer (`Rk`), whether it is a block
(`Kp.rk`) or a call (`Mont.CallKeep.rk`). The working space, its base in
`r3` (`Mont.WsReg`), gives the blocks' working space (`WsReg.ws`) and `r3`
at its base (`WsReg.at3`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass.PPC64LE.Mont

/-- `s'` agrees with `s` but on the registers `rs`, the link register and
memory. -/
structure Rk (rs : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ rs → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Rk.refl (rs : List Reg) (s : State) : Rk rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Rk.trans {rs : List Reg} {s₁ s₂ s₃ : State} (h₁ : Rk rs s₁ s₂) (h₂ : Rk rs s₂ s₃) : Rk rs s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp⟩

theorem Rk.mono {rs rs' : List Reg} {s s' : State} (h : Rk rs s s') (hs : ∀ r ∈ rs, r ∈ rs' := by decide) :
    Rk rs' s s' := ⟨fun r hr => h.gpr r fun h' => hr (hs r h'), h.rd, h.wr, h.sp⟩

theorem Rk.g {rs : List Reg} {s s' : State} (h : Rk rs s s') {r : Reg} (hr : r ∉ rs := by decide) :
    s'.gpr r = s.gpr r := h.gpr r hr

theorem _root_.VG.Proof.Mont.PPC64LE.Kp.rk {rs rs' : List Reg} {s s' : State} (h : Kp rs s s') (hs : ∀ r ∈ rs, r ∈ rs' := by decide) :
    Rk rs' s s' := ⟨fun r hr => h.gpr r fun h' => hr (hs r h'), h.rd, h.wr, h.sp⟩

theorem _root_.VG.Proof.Weierstrass.PPC64LE.Mont.CallKeep.rk {n : Nat} {base : Addr} {o : Nat} {s s' : State}
    (h : CallKeep n base o s s') {rs : List Reg} (hs : ∀ r ∈ fnClob, r ∈ rs := by decide) : Rk rs s s' :=
  ⟨fun r hr => h.gpr r fun h' => hr (hs r h'), h.rd, h.wr, h.sp⟩

theorem _root_.VG.Proof.Weierstrass.PPC64LE.Mont.WsReg.ws {s : State} {base : Addr} (h : WsReg s base) :
    Ws s base 8192 :=
  ⟨⟨8192, Nat.le_refl _, h.wr, h.nowrap⟩, by decide⟩

theorem _root_.VG.Proof.Weierstrass.PPC64LE.Mont.WsReg.at3 {s : State} {base : Addr} (h : WsReg s base) :
    At s base .r3 0 := by
  rw [At, h.r3, off]; exact (BitVec.add_zero _).symm

theorem _root_.VG.Proof.Weierstrass.PPC64LE.Mont.WsReg.of_rk {s s' : State} {base : Addr} (h : WsReg s base)
    {rs : List Reg} (k : Rk rs s s') (hr : Reg.r3 ∉ rs := by decide) : WsReg s' base :=
  h.of_keep (k.gpr _ hr) k.wr

theorem _root_.VG.Proof.Weierstrass.PPC64LE.Mont.WsReg.of_kp {s s' : State} {base : Addr} (h : WsReg s base)
    {rs : List Reg} (k : Kp rs s s') (hr : Reg.r3 ∉ rs := by decide) : WsReg s' base :=
  h.of_keep (k.gpr _ hr) k.wr

end VG.Proof.Weierstrass.PPC64LE
