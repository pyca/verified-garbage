module

public import VerifiedGarbage.Proof.Mont.X86.Sse2.Dot
public import VerifiedGarbage.Proof.Mont.X86.ArgFar
import VerifiedGarbage.Proof.Framework.Omega

/-! # The parameters

The kernel's seven parameters are words on the stack, `d` bytes above `esp`
(`Params`), past the working space, so changes within it keep them; `Sk`
records what a step keeps.
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Sse2
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Sse2 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt
open VG.Proof.Mont.X86.Dynamic (ArgFar readSrc_keep readSrc_upd)

/-- The parameters `V i` at `[esp + d + 4 i]`, past the working space. -/
structure Params (s : State) (W : Addr) (L : Nat) (V : Nat → BitVec 32) (d : Nat) : Prop where
  read : ∀ i < 7, readSrc s (.mem (prm d i)) = some (V i)
  far : ∀ i < 7, ArgFar s W L (prm d i)

/-- Changes within the working space, with `esp` and the permissions as they
were, keep the parameters. -/
theorem Params.keep {s t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {d : Nat} (h : Params s W L V d)
    (O : Outs W [(0, L)] s.mem t.mem) (hsp : t.gpr .esp = s.gpr .esp) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) : Params t W L V d :=
  ⟨fun i hi => (readSrc_keep (h.far i hi) O (by simp) hsp hrd hwr).trans (h.read i hi),
    fun i hi => (h.far i hi).keep hsp⟩

/-- What scalar code leaves: the registers but `rs`, the memory, the MCDT
depth and the XMM registers. -/
structure Sk (rs : List Reg) (s t : State) : Prop where
  keep : Keeps rs s t
  mem : t.mem = s.mem
  mcdt : t.mcdt = s.mcdt
  xmm : t.xmm = s.xmm

theorem Sk.refl (rs : List Reg) (s : State) : Sk rs s s := ⟨Keeps.refl _ _, rfl, rfl, rfl⟩

theorem Sk.trans {rs rs' : List Reg} {s₁ s₂ s₃ : State} (h₁ : Sk rs' s₁ s₂) (h₂ : Sk rs s₂ s₃)
    (hs : ∀ r ∈ rs, r ∈ rs' := by decide) : Sk rs' s₁ s₃ :=
  ⟨h₁.keep.widen h₂.keep hs, h₂.mem.trans h₁.mem, h₂.mcdt.trans h₁.mcdt, h₂.xmm.trans h₁.xmm⟩

theorem Sk.mono {rs : List Reg} {s t : State} (h : Sk rs s t) (rs' : List Reg)
    (hs : ∀ r ∈ rs, r ∈ rs' := by decide) : Sk rs' s t :=
  ⟨h.keep.mono hs, h.mem, h.mcdt, h.xmm⟩

theorem Sk.of_upd (rs : List Reg) {s t : State} {d : Reg} {v : BitVec 32} (u : Upd s t d v)
    (hm : t.mcdt = s.mcdt) (hx : t.xmm = s.xmm) (hd : d ∈ rs := by decide) : Sk rs s t :=
  ⟨u.keeps.mono fun r hr => by simp only [List.mem_singleton] at hr; exact hr ▸ hd, u.mem, hm, hx⟩

theorem Sk.of_fupd {s t : State} (u : Fupd s t) (hm : t.mcdt = s.mcdt) (hx : t.xmm = s.xmm) (rs : List Reg) :
    Sk rs s t := ⟨u.keeps rs, u.mem, hm, hx⟩

theorem Params.of_sk {s t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {d : Nat} (h : Params s W L V d)
    {rs : List Reg} (K : Sk rs s t) (hsp : .esp ∉ rs := by decide) : Params t W L V d :=
  h.keep (by rw [K.mem]; exact Outs.refl _ _ _) (K.keep.1 _ hsp) K.keep.2.1 K.keep.2.2

theorem Ws.of_sk {s t : State} {W : Addr} {L : Nat} (h : Ws s W L) {rs : List Reg} (K : Sk rs s t) : Ws t W L :=
  h.of_keeps K.keep

/-- A parameter read in a state `Sk` from one where it is known. -/
theorem Params.readSk {s t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {d : Nat} (h : Params s W L V d)
    {rs : List Reg} (K : Sk rs s t) {i : Nat} (hi : i < 7) (hsp : .esp ∉ rs := by decide) :
    readSrc t (.mem (prm d i)) = some (V i) := (h.of_sk K hsp).read i hi

theorem ofNat_of_toNat {v : BitVec 32} {n : Nat} (h : v.toNat = n) : v = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq; rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (h ▸ v.isLt)]

end VG.Proof.Mont.X86.Sse2
