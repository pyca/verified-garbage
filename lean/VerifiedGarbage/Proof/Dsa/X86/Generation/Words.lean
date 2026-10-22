module

public import VerifiedGarbage.Impl.Dsa.X86.Generation
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.X86.Exec
public import VerifiedGarbage.Proof.Framework.Covers

/-! # The search's state words in `scratch`

Loads, stores and additions of the words at fixed offsets of the working
space that `edi` holds (`[edi + d]`, `sc d`). -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86 (sc)
open VG.Impl.Dsa.X86.Generation (scr)

theorem Scr.addr {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat} (hd : d < size) :
    VG.X86.addr (s.gpr .edi) d = off base d :=
  hs.ea hd

/-- `d := edi + o`. -/
theorem scr_ok {d : Reg} {o : Nat} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', s'.gpr d = s.gpr .edi + BitVec.ofNat 32 o → (∀ r, r ≠ d → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.syms = s.syms → WP isa (.block is) s' Q) :
    WP isa (.block (scr d o ++ is)) s Q := by
  simp only [scr, List.cons_append, List.nil_append]
  exact wp_mov fun s₁ u₁ => wp_addi fun s₂ u₂ => k s₂ (by rw [u₂.gpr, u₁.gpr])
    (fun r hr => by rw [u₂.other r hr, u₁.other r hr]) (by rw [u₂.mem, u₁.mem]) (by rw [u₂.rd, u₁.rd])
    (by rw [u₂.wr, u₁.wr]) (by rw [u₂.syms, u₁.syms])

/-- `edi + d`, widened: the address `d` bytes into the working space. -/
theorem Scr.wide {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat} (hd : d < size) :
    (s.gpr .edi + BitVec.ofNat 32 d).setWidth 64 = off base d :=
  hs.ea hd

theorem Scr.toNat_add {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat} (hd : d < size) :
    (s.gpr .edi + BitVec.ofNat 32 d).toNat = base.toNat + d := by
  have := hs.nowrap; have := hs.edi_toNat
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), hs.edi_toNat,
    Nat.mod_eq_of_lt (by omega)]

/-- A part of the working space is within the writable regions. -/
theorem Scr.covers {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d n : Nat}
    (h : d + n ≤ size) : Covers [⟨off base d, n⟩] s.wr :=
  Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, hs.wr, d, rfl, h⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop} {base : Addr} {size : Nat}

/-- `mov r, [edi + d]`. -/
theorem ld_ok {r : Reg} {d : Nat} (hs : Scr s base size) (hd : d + 4 ≤ size)
    (k : ∀ s', Upd s s' r (s.mem.readW (off base d) 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov r (.mem (sc d)) :: is)) s Q := by
  have e := Scr.addr hs (d := d) (by omega)
  exact wp_ldm (B := s.gpr .edi) rfl (by rw [e]; exact hs.read hd) fun s' u => by rw [e] at u; exact k s' u

/-- `mov [edi + d], r`. -/
theorem st_ok {r : Reg} {d : Nat} (hs : Scr s base size) (hd : d + 4 ≤ size)
    (k : ∀ s', Mupd s s' (s.mem.writeW (off base d) (s.gpr r)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store (sc d) r :: is)) s Q := by
  have e := Scr.addr hs (d := d) (by omega)
  exact wp_stm (B := s.gpr .edi) rfl (by rw [e]; exact hs.write hd) fun s' u => by rw [e] at u; exact k s' u

/-- `add r, [edi + d]`. -/
theorem addm_ok {r : Reg} {d : Nat} (hs : Scr s base size) (hd : d + 4 ≤ size)
    (k : ∀ s', Upd s s' r (s.gpr r + s.mem.readW (off base d) 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add r (.mem (sc d)) :: is)) s Q := by
  have e := Scr.addr hs (d := d) (by omega)
  exact wp_addm (B := s.gpr .edi) rfl (by rw [e]; exact hs.read hd) fun s' u => by rw [e] at u; exact k s' u

end

end VG.Proof.Dsa.X86.Generation
