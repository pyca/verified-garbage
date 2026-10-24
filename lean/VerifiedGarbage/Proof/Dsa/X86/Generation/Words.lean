module

public import VerifiedGarbage.Impl.Dsa.X86.Generation
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.X86.Exec
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Mont.Words

/-! # The search's state words in `scratch`

Loads, stores and additions of the words at fixed offsets of the working
space that `edi` holds (`[edi + d]`, `sc d`). -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86 (sc)
open VG.Impl.Dsa.X86.Generation (scr orByte)

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

/-- `and r, [edi + d]`. -/
theorem andm_ok {r : Reg} {d : Nat} (hs : Scr s base size) (hd : d + 4 ≤ size)
    (k : ∀ s', Upd s s' r (s.gpr r &&& s.mem.readW (off base d) 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and r (.mem (sc d)) :: is)) s Q := by
  have e := Scr.addr hs (d := d) (by omega)
  have hin := hs.read hd
  rw [← e] at hin
  refine cons (by simp [exec, execAlu, sc, VG.Impl.Mont.X86.at_, readSrc_mem (B := s.gpr .edi) rfl hin]; rfl)
    (k _ ?_)
  rw [← e]; exact Upd.flags _ _ _ _ _ _

/-- `movzx r, byte [edi + d]`. -/
theorem ld8_ok {r : Reg} {d : Nat} (hs : Scr s base size) (hd : d + 1 ≤ size)
    (k : ∀ s', Upd s s' r ((s.mem (off base d)).setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movzx8 r (sc d) :: is)) s Q := by
  have e := Scr.addr hs (d := d) (by omega)
  refine cons (s' := s.setReg r ((s.mem (off base d)).setWidth 32)) ?_ (k _ (Upd.setReg _ _ _))
  have hin := hs.read (d := d) (n := 1) hd
  simp only [exec, State.load8, sc, VG.Impl.Mont.X86.at_, ea_mk, e, hin, ↓reduceIte, Option.map_some]

/-- `mov byte [edi + d], r8`. -/
theorem st8_ok {r : Reg8} {d : Nat} (hs : Scr s base size) (hd : d + 1 ≤ size)
    (k : ∀ s', Mupd s s' (s.mem.writeW (off base d) ((s.gpr r.reg).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store8 (sc d) r :: is)) s Q := by
  have e := Scr.addr hs (d := d) (by omega)
  refine cons (s' := { s with mem := s.mem.writeW (off base d) ((s.gpr r.reg).setWidth 8) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
  have hout := hs.write (d := d) (n := 1) hd
  simp only [exec, State.store8, sc, VG.Impl.Mont.X86.at_, ea_mk, e, hout, ↓reduceIte]

/-- `or d, imm`. -/
theorem wp_ori {d : Reg} {v : BitVec 32} (k : ∀ s', Upd s s' d (s.gpr d ||| v) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .or d (.imm v) :: is)) s Q :=
  cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem or_byte (b : Byte) (v : Nat) (hv : v < 256) :
    ((b.setWidth 32 ||| BitVec.ofNat 32 v).setWidth 8) = b ||| BitVec.ofNat 8 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_or, BitVec.toNat_ofNat]
  have := b.isLt
  rw [Nat.mod_eq_of_lt (a := b.toNat) (by omega), Nat.mod_eq_of_lt (a := v) (by omega),
    Nat.mod_eq_of_lt (a := v) (by omega), Nat.mod_eq_of_lt (Nat.or_lt_two_pow (n := 8) (by omega) (by omega))]

/-- The byte at `scratch + o` ORed with `v`. -/
theorem orByte_ok {o v : Nat} (hs : Scr s base size) (ho : o + 1 ≤ size) (hv : v < 256)
    (k : ∀ s', (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.syms = s.syms →
      s'.mem = s.mem.writeW (off base o) (s.mem (off base o) ||| BitVec.ofNat 8 v) → WP isa (.block is) s' Q) :
    WP isa (.block (orByte o v ++ is)) s Q := by
  simp only [orByte, List.cons_append, List.nil_append]
  refine ld8_ok hs ho fun s₁ u₁ => wp_ori fun s₂ u₂ =>
    st8_ok (Scr.of_eq hs (by rw [u₂.other _ (by decide), u₁.other _ (by decide)])
      (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]) (by rw [u₂.wr, u₁.wr])) ho fun s₃ M₃ => ?_
  refine k s₃ (fun r hr => by rw [M₃.gpr, u₂.other r hr, u₁.other r hr]) (by rw [M₃.rd, u₂.rd, u₁.rd])
    (by rw [M₃.wr, u₂.wr, u₁.wr]) (by rw [M₃.syms, u₂.syms, u₁.syms]) ?_
  rw [M₃.mem, u₂.mem, u₁.mem]
  simp only [Reg8.reg, u₂.gpr, u₁.gpr]
  rw [or_byte _ _ hv]

end

end VG.Proof.Dsa.X86.Generation
