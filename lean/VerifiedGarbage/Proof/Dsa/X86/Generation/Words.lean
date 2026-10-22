module

public import VerifiedGarbage.Impl.Dsa.X86.Generation
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.X86.Exec

/-! # The search's state words in `scratch`

Loads, stores and additions of the words at fixed offsets of the working
space that `edi` holds (`[edi + d]`, `sc d`). -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86 (sc)

theorem Scr.addr {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat} (hd : d < size) :
    VG.X86.addr (s.gpr .edi) d = off base d :=
  hs.ea hd

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
