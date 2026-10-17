module

public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Proof.Mont.Words32
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Address and memory facts for a runtime-sized ARMv7 RSA workspace -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont

structure Workspace (s : State) (base : BitVec 32) (size : Nat) : Prop where
  nowrap : base.toNat + size ≤ 2 ^ 32
  writable : (⟨State.addr base, size⟩ : Region) ∈ s.wr

theorem Workspace.congr {s t : State} {base : BitVec 32} {size : Nat}
    (h : Workspace s base size) (hw : t.wr = s.wr) : Workspace t base size :=
  ⟨h.nowrap, by rw [hw]; exact h.writable⟩

theorem Workspace.ea {s : State} {base : BitVec 32} {size off imm : Nat} {r : Reg}
    (h : Workspace s base size) (hp : s.gpr r = base + BitVec.ofNat 32 off)
    (hd : off + imm < size) :
    State.addr (s.gpr r + BitVec.ofNat 32 imm) = VG.Proof.Mont.off (State.addr base) (off + imm) := by
  rw [hp, Offset.add_add]
  exact VG.Arm.addr_add (by have := h.nowrap; omega)

theorem Workspace.write {s : State} {base : BitVec 32} {size off : Nat}
    (h : Workspace s base size) (hd : off + 4 ≤ size) :
    InRegions s.wr (VG.Proof.Mont.off (State.addr base) off) 4 :=
  ⟨_, h.writable, Offset.contains_base _ hd (by have := h.nowrap; omega)⟩

theorem Workspace.read {s : State} {base : BitVec 32} {size off : Nat}
    (h : Workspace s base size) (hd : off + 4 ≤ size) :
    InRegions (s.rd ++ s.wr) (VG.Proof.Mont.off (State.addr base) off) 4 := by
  obtain ⟨R, hR, hsub⟩ := h.write hd
  exact ⟨R, List.mem_append_right _ hR, hsub⟩

/-- Equality of native words outside a changed range, without unpacking bytes. -/
theorem outside_read32 {mem mem' : Mem} {base : Addr} {o n d : Nat}
    (h : Outside base o n mem mem') (sep : d + 4 ≤ o ∨ o + n ≤ d) (fit : d + 4 ≤ 2 ^ 64) :
    mem'.readW (off base d) 32 = mem.readW (off base d) 32 :=
  BitVec.eq_of_toNat_eq (h.w32 sep fit)

theorem outs_word32 {mem mem' : Mem} {base : Addr} {ranges : List (Nat × Nat)} {d : Nat}
    (h : Outs base ranges mem mem')
    (sep : ∀ r ∈ ranges, d + 4 ≤ r.1 ∨ r.1 + r.2 ≤ d) (fit : d + 4 ≤ 2 ^ 64) :
    w32 mem' base d = w32 mem base d := by
  have eq := h.val32 (d := d) (k := 1) sep fit
  simpa only [val32, Nat.mul_zero, Nat.add_zero] using eq

/-- Stores preserve the loop condition computed immediately before them. -/
theorem wp_str_z {s : State} {is : List Instr} {Q : State → Prop}
    {t n : Reg} {d : Nat} {a : Addr} (hd : d < 4096)
    (ha : State.addr (s.gpr n + BitVec.ofNat 32 d) = a) (hw : InRegions s.wr a 4)
    (k : ∀ s', VG.Proof.X25519.Arm.Mupd s s' (s.mem.writeW a (s.gpr t)) →
      s'.z = s.z → WP isa (.block is) s' Q) :
    WP isa (.block (.str t n d :: is)) s Q := by
  subst ha
  exact VG.Proof.X25519.Arm.WP.cons (exec_str hd hw) (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl)

end VG.Proof.Bignum.Arm
