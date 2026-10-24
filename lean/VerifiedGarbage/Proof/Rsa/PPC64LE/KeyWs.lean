module

public import VerifiedGarbage.Impl.Rsa.PPC64LE.KeyWs
public import VerifiedGarbage.Proof.Rsa.KeyWorkspace
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The working space of the RSA key operations on PPC64LE

`Ws s B Z w N`: `r29`, `r30` and `r31` hold `w`, the stride and the base
`B`, and the working space (`Z` bytes at `B`, `N` arrays after the header) is
writable (`Scr`). The arrays and the header's slots are
`Proof/Rsa/KeyWorkspace.lean`'s: `num m B w j` is the number in array `j`,
`slot m B d` the 32-bit word at byte `d` of the header, and `Keep B w js ds m
m'` says `m'` is `m` but on the arrays `js` and the slots `ds`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Keys

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.KeyWorkspace
open VG.Impl.Rsa.PPC64LE.Keys (ptr)

theorem hdr_eq : VG.Impl.Rsa.PPC64LE.Keys.hdr = KeyWorkspace.hdr := rfl

structure Ws (s : State) (B : Addr) (Z w N : Nat) : Prop where
  scr : Scr s B Z
  fits : arr w N ≤ Z
  wpos : 0 < w
  wle : w ≤ 1024
  r29 : s.gpr .r29 = BitVec.ofNat 64 w
  r30 : s.gpr .r30 = BitVec.ofNat 64 (S w)
  r31 : s.gpr .r31 = B

/-- The registers the key operations keep. -/
abbrev wsRegs : List Reg := [.r29, .r30, .r31]

theorem Ws.of_keep {s t : State} {B : Addr} {Z w N : Nat} {rs : List Reg} (h : Ws s B Z w N)
    (k : Keep rs s t) (h29 : .r29 ∉ rs := by decide) (h30 : .r30 ∉ rs := by decide)
    (h31 : .r31 ∉ rs := by decide) : Ws t B Z w N :=
  ⟨h.scr.congr k.wr, h.fits, h.wpos, h.wle, (k.gpr _ h29).trans h.r29, (k.gpr _ h30).trans h.r30,
    (k.gpr _ h31).trans h.r31⟩

theorem Ws.nowrap {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w N) : B.toNat + Z ≤ 2 ^ 64 :=
  h.scr.nowrap

theorem Ws.arr_fit {s : State} {B : Addr} {Z w N j : Nat} (h : Ws s B Z w N) (hj : j < N) :
    arr w j + S w ≤ Z :=
  Nat.le_trans (arr_end hj) h.fits

theorem Ws.fit64 {s : State} {B : Addr} {Z w N j : Nat} (h : Ws s B Z w N) (hj : j < N) :
    arr w j + S w ≤ 2 ^ 64 := by
  have := h.arr_fit hj; have := h.nowrap; omega

theorem Ws.hdr_le {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w N) : KeyWorkspace.hdr ≤ Z :=
  Nat.le_trans (Nat.le_add_right _ _) h.fits

/-! ## Array addresses -/

theorem ptr_val (B : Addr) (j S : Nat) :
    BitVec.ofNat 64 j * BitVec.ofNat 64 S + B + BitVec.ofNat 64 KeyWorkspace.hdr =
      off B (KeyWorkspace.hdr + j * S) := by
  simp only [off, BitVec.ofNat_add, BitVec.ofNat_mul]
  ac_rfl

theorem write_write (s : State) (r : Reg) (a b : BitVec 64) : (s.write r a).write r b = s.write r b := by
  simp only [State.write]
  congr 1
  funext x
  split <;> rfl

/-- `ptr r j`: `r` holds the address of array `j`. -/
theorem ptr_ok {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w N) {r : Reg} (hr : r ≠ .r0)
    (h30 : r ≠ .r30) (h31 : r ≠ .r31) {j : Nat} (hj : j < 2 ^ 15) {rest : List Instr}
    {Q : State → Prop} (k : WP isa (.block rest) (s.write r (off B (arr w j))) Q) :
    WP isa (.block (ptr r j ++ rest)) s Q := by
  rw [WP.block_append_iff]
  refine WP.of_runBlock ?_
  simp only [ptr, runBlock_cons, runStep_some, runBlock_nil, exec_li hj, exec_mul, exec_add,
    exec_addi hr (show KeyWorkspace.hdr < 2 ^ 15 by decide), Option.some.injEq,
    exists_eq_left', gpr_write, ite_true, Ne.symm h30, Ne.symm h31, ite_false, write_write, h.r30,
    h.r31, hdr_eq, ptr_val]
  exact k

end VG.Proof.Rsa.PPC64LE.Keys
