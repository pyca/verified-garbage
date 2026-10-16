module

public import VerifiedGarbage.Proof.Ed25519.AArch64.Mem
public import VerifiedGarbage.Proof.Curve448.AArch64.Neon.Arith
public import VerifiedGarbage.Proof.Curve448.AArch64.Neon.Exec
public import VerifiedGarbage.Impl.X25519.AArch64.Neon
public import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
public import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
public import VerifiedGarbage.Proof.Framework.AArch64.Simd64
public import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.Framework.AArch64.Interleave
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# X25519 on AArch64: the vector loads and stores of `Neon.prod2`

Untrusted: everything here is checked by Lean. The working space is X25519's
4 KiB at `x0` (`Scratch`); `ldq` and `stq` move 16 bytes of it, and `dw m base d`
is the 64-bit word at offset `d`, as a number.
-/

@[expose] public section

namespace VG.Proof.X25519.AArch64.Hybrid

open VG VG.AArch64
open VG.Impl.X25519.AArch64.Neon (V ldq stq vo)
open VG.Proof.Ed25519.AArch64 (Scr off word Outside ofs contains_scWith)
open VG.Proof.Curve448.AArch64.Neon (setMem)

/-- X25519's working space: 4 KiB at `x0`. -/
abbrev Scratch (s : State) (base : Addr) : Prop := Scr s base false

/-- The 64-bit word at offset `d`, as a number. -/
abbrev dw (m : Mem) (base : Addr) (d : Nat) : Nat := (word m base d).toNat

theorem off_add (base : Addr) (d e : Nat) : off base d + BitVec.ofNat 64 e = off base (d + e) := by
  simp only [off, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem exec_ldq {s : State} {base : Addr} (hs : Scratch s base) (t : Nat) {d : Nat} (h16 : d % 16 = 0)
    (hd : d + 16 ≤ 4096) : isa.exec (ldq t d) s = some (s.setV (V t) (s.mem.read (off base d) 16)) := by
  have hr : InRegions (s.rd ++ s.wr) (off base d) 16 :=
    ⟨_, List.mem_append_right _ hs.wr, contains_scWith (large := false) hd⟩
  simp only [ldq, exec, addr, show d % 16 = 0 ∧ d < 4096 * 16 from ⟨h16, by omega⟩, and_self, ite_true,
    Option.bind_some, State.load, hs.x0]
  rw [ite_eq_left_iff.mpr fun h => absurd hr h]
  rfl

theorem exec_stq {s : State} {base : Addr} (hs : Scratch s base) (t : Nat) {d : Nat} (h16 : d % 16 = 0)
    (hd : d + 16 ≤ 4096) :
    isa.exec (stq t d) s = some (setMem s (s.mem.write (off base d) 16 (s.v (V t)))) := by
  have hw : InRegions s.wr (off base d) 16 := ⟨_, hs.wr, contains_scWith (large := false) hd⟩
  simp only [stq, exec, addr, show d % 16 = 0 ∧ d < 4096 * 16 from ⟨h16, by omega⟩, and_self, ite_true,
    Option.bind_some, State.store, hs.x0]
  rw [ite_eq_left_iff.mpr fun h => absurd hw h]
  rfl

/-- The 64-bit lanes of 16 bytes loaded at `d`. -/
theorem vdword_ld (m : Mem) (base : Addr) (d : Nat) {e : Nat} (he : e < 2) :
    vdword (m.read (off base d) 16) e = word m base (d + 8 * e) := by
  rw [vdword_read16 _ _ he, off_add]

/-- The 64-bit lanes of 16 bytes stored at `d`. -/
theorem word_st (m : Mem) (base : Addr) {d : Nat} (v : BitVec 128) (hd : d + 16 ≤ 4096) {e : Nat} (he : e < 2) :
    word (m.write (off base d) 16 v) base (d + 8 * e) = vdword v e := by
  have hv : v = ofVDwords (vdword v 0) (vdword v 1) :=
    vec64_ext (by rw [vdword_ofVDwords_0]) (by rw [vdword_ofVDwords_1])
  rw [hv, write16_dwords, off_add]
  rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
  · rw [vdword_ofVDwords_0, VG.Proof.Ed25519.AArch64.word_writeW_sep _ _ _ (by omega) (by omega) (by omega)]
    exact VG.Proof.Ed25519.AArch64.word_writeW_self _ _ _ _
  · rw [vdword_ofVDwords_1]
    exact VG.Proof.Ed25519.AArch64.word_writeW_self _ _ _ _

theorem st_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 128) (h : d + 16 ≤ 4096) :
    Outside base d 16 m (m.write (off base d) 16 v) := by
  intro x hx
  apply Mem.write_apply
  rw [Offset.lt_iff x base (by omega)]
  simp only [ofs] at hx
  omega

theorem scratch_of {s t : State} {base : Addr} (hs : Scratch s base) (hg : t.gpr = s.gpr) (hw : t.wr = s.wr) :
    Scratch t base := ⟨by rw [hg]; exact hs.x0, hw ▸ hs.wr, hs.nowrap⟩

theorem exec_vo_of {op : VOp} {s : State} {d : VReg} {x : BitVec 128} (h : op.eval s = some (d, x)) :
    isa.exec (vo op) s = some (s.setV d x) := by
  show (op.eval s).map (fun p => s.setV p.1 p.2) = _
  rw [h]; rfl


/-- The 32-bit word at offset `d`, as a number. -/
abbrev nw (m : Mem) (base : Addr) (d : Nat) : Nat := (m.readW (off base d) 32).toNat

theorem vword_ld (m : Mem) (base : Addr) (d : Nat) {c : Nat} (hc : c < 4) :
    (vword (m.read (off base d) 16) c).toNat = nw m base (d + 4 * c) := by
  rw [vword_read16 _ _ hc, off_add]

theorem nw_st (m : Mem) (base : Addr) (d : Nat) (v : BitVec 128) {c : Nat} (hc : c < 4) :
    nw (m.write (off base d) 16 v) base (d + 4 * c) = (vword v c).toNat := by
  rw [nw, ← off_add, VG.Proof.Curve448.AArch64.Neon.write16_word _ _ _ hc]

theorem Outside.nw {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') {d : Nat}
    (hd : d + 4 ≤ o ∨ o + n ≤ d) (hd' : d + 4 ≤ 4096) : nw m' base d = nw m base d :=
  congrArg BitVec.toNat
    (Mem.readW_congr fun i hi => (h _ (by rw [VG.Proof.Ed25519.AArch64.ofs_off base (by omega)]; omega)).symm).symm

theorem nw_st_other (m : Mem) (base : Addr) {d d' : Nat} (v : BitVec 128) (h : d + 16 ≤ 4096)
    (h' : d' + 4 ≤ 4096) (hd : d' + 4 ≤ d ∨ d + 16 ≤ d') : nw (m.write (off base d) 16 v) base d' = nw m base d' :=
  Outside.nw (st_outside m base v h) hd h'

theorem Outside.word' {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') {d : Nat}
    (hd : d + 8 ≤ o ∨ o + n ≤ d) (hd' : d + 8 ≤ 4096) : word m' base d = word m base d :=
  VG.Proof.Ed25519.AArch64.Outside.word h hd (by omega)

theorem flags_setMem (s : State) (m : Mem) : (setMem s m).flags = s.flags := rfl

end VG.Proof.X25519.AArch64.Hybrid
