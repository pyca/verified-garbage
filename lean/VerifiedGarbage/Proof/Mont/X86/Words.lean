import VerifiedGarbage.Impl.Mont.X86
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.X86.Wp

/-!
# Montgomery arithmetic on x86 (32-bit): words in the working space

The working space is `size` bytes at `base`, whose low 32 bits `edi` holds
(`Scr`), below `2³²`. Its numbers are read as 32-bit words (`w32`, `val32`):
`k` of them at an offset are the same bytes, and the same number, as
`k / 2` 64-bit words (`wordsVal_eq_val32`), in which the other targets and
the target-independent proofs state them. The loads and stores of the
arithmetic, through `edi` or through `ebp`, which the multiplication moves
by 4 bytes a row (`ea_at`), and what changes (`Keeps`).
-/

namespace VG.Proof.Mont.X86

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Proof.Mont

/-! ## The working space -/

/-- The 20 bytes of stack below `sp`, where a call pushes its arguments and
its return address (`Impl/Weierstrass/X86/Mont.lean`'s `callOp`), are above
address 0 and apart from the `size` bytes at `base`. -/
def StkOk (sp : BitVec 32) (base : Addr) (size : Nat) : Prop :=
  20 ≤ sp.toNat ∧ (sp.toNat ≤ base.toNat ∨ base.toNat + size + 20 ≤ sp.toNat)

/-- The working space: `edi` holds its base `base`, it is writable and it
lies below `2³²`, apart from the stack the calls use. -/
structure Scr (s : State) (base : Addr) (size : Nat) : Prop where
  edi : (s.gpr .edi).setWidth 64 = base
  wr : (⟨base, size⟩ : Region) ∈ s.wr
  nowrap : base.toNat + size ≤ 2 ^ 32
  stk : StkOk (s.gpr .esp) base size

theorem Scr.edi_toNat {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) :
    (s.gpr .edi).toNat = base.toNat := by
  rw [← hs.edi, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (s.gpr .edi).isLt
    (Nat.pow_le_pow_right (by decide) (by decide)))]

/-- `[edi + d]`. -/
theorem Scr.ea {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat}
    (hd : d < size) : s.ea (sc d) = off base d := by
  change addr (s.gpr .edi) d = _
  rw [addr_eq (by have := hs.nowrap; have := hs.edi_toNat; omega), hs.edi]

/-- `[ebp + d]`, with `ebp` at `4i` bytes into the working space. -/
theorem Scr.ea_at {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {i d : Nat}
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i)) (hd : 4 * i + d < size) :
    s.ea (at_ .ebp d) = off base (4 * i + d) := by
  change ((s.gpr .ebp + BitVec.ofNat 32 d).setWidth 64) = _
  rw [hp, Offset.add_add]
  exact hs.ea hd

theorem Scr.contains {base : Addr} {size d n : Nat} (hn : base.toNat + size ≤ 2 ^ 32) (h : d + n ≤ size) :
    (⟨base, size⟩ : Region).Contains (off base d) n :=
  Offset.contains_base base h (by omega)

theorem Scr.read {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d n : Nat}
    (hd : d + n ≤ size) : InRegions (s.rd ++ s.wr) (off base d) n :=
  ⟨_, List.mem_append_right _ hs.wr, Scr.contains hs.nowrap hd⟩

theorem Scr.write {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d n : Nat}
    (hd : d + n ≤ size) : InRegions s.wr (off base d) n := ⟨_, hs.wr, Scr.contains hs.nowrap hd⟩

/-- The registers and permissions that a piece of code preserves. -/
def Keeps (rs : List Reg) (s s' : State) : Prop :=
  (∀ r, r ∉ rs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem Keeps.refl (rs : List Reg) (s : State) : Keeps rs s s := ⟨fun _ _ => rfl, rfl, rfl⟩

theorem Keeps.trans {rs : List Reg} {s₁ s₂ s₃ : State} (h₁ : Keeps rs s₁ s₂) (h₂ : Keeps rs s₂ s₃) :
    Keeps rs s₁ s₃ := ⟨fun r hr => (h₂.1 r hr).trans (h₁.1 r hr), h₂.2.1.trans h₁.2.1,
      h₂.2.2.trans h₁.2.2⟩

theorem Keeps.mono {rs rs' : List Reg} {s s' : State} (h : Keeps rs s s') (hs : ∀ r ∈ rs, r ∈ rs') :
    Keeps rs' s s' := ⟨fun r hr => h.1 r fun h' => hr (hs r h'), h.2⟩

theorem Scr.of_keeps {rs : List Reg} {s s' : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (h : Keeps rs s s') (hr : .edi ∉ rs) (hsp : .esp ∉ rs := by decide) : Scr s' base size :=
  ⟨by rw [h.1 _ hr]; exact hs.edi, h.2.2 ▸ hs.wr, hs.nowrap, by rw [h.1 _ hsp]; exact hs.stk⟩

/-- `Scr` from the registers `edi` and `esp` and the writable regions. -/
theorem Scr.of_eq {s s' : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hdi : s'.gpr .edi = s.gpr .edi) (hsp : s'.gpr .esp = s.gpr .esp) (hwr : s'.wr = s.wr) :
    Scr s' base size :=
  ⟨by rw [hdi]; exact hs.edi, hwr ▸ hs.wr, hs.nowrap, by rw [hsp]; exact hs.stk⟩

end VG.Proof.Mont.X86
