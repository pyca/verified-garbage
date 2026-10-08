import VerifiedGarbage.Proof.X448.Arm.Normalize

/-!
# X448 on ARMv7: field operations and their frame
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448.Radix16

abbrev F (m : Mem) (base : Addr) (o : Nat) : Spec.X448.Fe := toFe (fe m base o)

/-- The registers a field operation may change: `r1`–`r3`, `r12` and `lr`,
which a call of one of the field functions changes, and `r4`, `r5` and `r7`,
which the inlined operations (copying, the swap) use. -/
def clob : List Reg := [.r1, .r2, .r3, .r4, .r5, .r7, .r12, .lr]

/-- The registers the operations change within the field functions. -/
def fclob : List Reg := [.r1, .r2, .r3, .r4, .r5, .r7]

structure Op (base : Addr) (o : Nat) (s t : State) : Prop where
  keeps : Keeps clob s t
  mem : FieldMem base o s.mem t.mem

theorem Op.scr {base : Addr} {o : Nat} {s t : State} (h : Op base o s t) (hs : Scr s base) :
    Scr t base := hs.of_keeps h.keeps (by decide)

abbrev Slot (o : Nat) : Prop := o + 112 ≤ ACC

/-- A register update preserving the working-space pointer and limb mask. -/
theorem Scr.of_upd {s t : State} {base : Addr} {r : Reg} {v : BitVec 32}
    (hs : Scr s base) (h : VG.Proof.X25519.Arm.Upd s t r v) (h0 : Reg.r0 ≠ r) (h6 : Reg.r6 ≠ r) :
    Scr t base :=
  ⟨by rw [h.other _ h0]; exact hs.r0, (h.other _ h6).trans hs.mask, h.wr ▸ hs.wr,
    by rw [h.other _ h0]; exact hs.nowrap⟩

theorem load_ok {s : State} {base : Addr} (hs : Scr s base) {r : Reg} {d : Nat}
    (hd : d + 4 ≤ 4096) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, VG.Proof.X25519.Arm.Upd s t r (word s.mem base d) → WP isa (.block is) t Q) :
    WP isa (.block (ld r d :: is)) s Q :=
  VG.Proof.X25519.Arm.wp_ldr (by omega) (hs.ea (by omega)) (hs.read (by omega)) k

theorem store_ok {s : State} {base : Addr} (hs : Scr s base) {r : Reg} {d : Nat}
    (hd : d + 4 ≤ 4096) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, VG.Proof.X25519.Arm.Mupd s t (s.mem.writeW (off base d) (s.gpr r)) →
      WP isa (.block is) t Q) : WP isa (.block (st r d :: is)) s Q :=
  VG.Proof.X25519.Arm.wp_str (by omega) (hs.ea (by omega)) (hs.write (by omega)) k

theorem Ptr.of_upd {s t : State} {p r : Reg} {v : BitVec 32} {o : Nat} (h : Ptr s p o)
    (u : VG.Proof.X25519.Arm.Upd s t r v) (hp : p ≠ r) (h0 : Reg.r0 ≠ r) : Ptr t p o := by
  rw [Ptr, u.other _ hp, u.other _ h0]; exact h

theorem loadP_ok {s : State} {base : Addr} (hs : Scr s base) {p r : Reg} {o d : Nat} (hp : Ptr s p o)
    (hd : d < 4096) (hod : o + d + 4 ≤ 4096) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, VG.Proof.X25519.Arm.Upd s t r (word s.mem base (o + d)) → WP isa (.block is) t Q) :
    WP isa (.block (.ldr r p d :: is)) s Q :=
  VG.Proof.X25519.Arm.wp_ldr hd (hs.eaP hp (by omega)) (hs.read (by omega)) k

end VG.Proof.X448.Arm
