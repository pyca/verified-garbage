module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.FrontRt
public import VerifiedGarbage.Impl.Bignum.X86.PublicContext
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.MillerRabin.X86.Scale
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Array addresses from the candidate's length in the header -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.FrontRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Impl.Bignum.X86.PublicContext VG.Impl.RsaKeyGen.X86.FrontRt
open VG.Impl.Mont.X86 (sc at_)

/-- The workspace at `edi`, with the candidate's length `8 w` at header byte 4. -/
structure Space (W : Addr) (L w : Nat) (s : State) : Prop where
  scratch : Scr s W L
  width : 4 ≤ w
  widthBound : w ≤ 64
  space : slot w 5 ≤ L
  len : s.mem.readW (off W 4) 32 = BitVec.ofNat 32 (8 * w)

theorem Space.keep {W : Addr} {L w : Nat} {s t : State} (S : Space W L w s) {rs : List Reg}
    (K : Keeps rs s t) (edi : .edi ∉ rs) (esp : .esp ∉ rs)
    (M : t.mem.readW (off W 4) 32 = s.mem.readW (off W 4) 32) : Space W L w t :=
  ⟨S.scratch.of_keeps K edi esp, S.width, S.widthBound, S.space, M.trans S.len⟩

theorem Space.keepMem {W : Addr} {L w : Nat} {s t : State} (S : Space W L w s) {rs : List Reg}
    (K : Keeps rs s t) (edi : .edi ∉ rs) (esp : .esp ∉ rs) (M : t.mem = s.mem) : Space W L w t :=
  S.keep K edi esp (by rw [M])

theorem Space.header {W : Addr} {L w : Nat} {s : State} (S : Space W L w s) : 256 + 5 * (8 * w + 16) ≤ L := by
  have := S.space
  unfold slot stride VG.Impl.Bignum.hdrBytes at this
  omega

theorem Space.ws {W : Addr} {L w : Nat} {s : State} (S : Space W L w s) : Ws s W L :=
  ⟨S.scratch.wr, S.scratch.nowrap⟩

theorem Space.edi_toNat {W : Addr} {L w : Nat} {s : State} (S : Space W L w s) :
    (s.gpr .edi).toNat = W.toNat := S.scratch.edi_toNat

theorem Space.base {W : Addr} {L w : Nat} {s : State} (S : Space W L w s) : PtrAt s W .edi 0 := by
  have := S.scratch.nowrap
  have := S.header
  rw [PtrAt, S.edi_toNat, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]

/-- `len` from header byte 4. -/
theorem Space.lenRead {W : Addr} {L w : Nat} {s : State} (S : Space W L w s) :
    readSrc s (.mem (sc 4)) = some (BitVec.ofNat 32 (8 * w)) := by
  have head := S.header
  rw [show sc 4 = at_ .edi (0 + 4) from rfl, readSrc_ptr S.ws S.base (d := 4) (by omega), Nat.zero_add, S.len]

theorem lenPtr_ok {W : Addr} {L w : Nat} {s : State} (S : Space W L w s) {r t : Reg} (j : Nat)
    (index : j < 32) (hrt : t ≠ r) (hr : r ≠ .edi) (ht : t ≠ .edi) :
    WP isa (.block (lenPtr r t j)) s fun u =>
      PtrAt u W r (slot w j) ∧ u.mem = s.mem ∧ Keeps [r, t] s u := by
  have head := S.header
  have nowrap := S.ws.nowrap
  have bound := S.widthBound
  unfold lenPtr
  simp only [List.cons_append, List.nil_append]
  refine wp_movS S.lenRead fun a A _ => wp_addS rfl fun b B _ => wp_movS rfl fun c C _ => ?_
  refine WP.block_append (WP.mono (VG.Proof.MillerRabin.X86.scaleIndex_ok c r t hrt j index C.gpr)
    fun d ⟨R, M, K⟩ => ?_)
  refine wp_addS rfl fun e E _ => wp_addS rfl fun u U _ => WP.block_nil ?_
  have tc : c.gpr t = BitVec.ofNat 32 (8 * w) + 16 := by rw [C.other t hrt, B.gpr, A.gpr]
  have ediD : d.gpr .edi = s.gpr .edi := by
    rw [K.1 .edi (by simp [hr.symm]), C.other .edi hr.symm, B.other .edi ht.symm, A.other .edi ht.symm]
  refine ⟨?_, by rw [U.mem, E.mem, M, C.mem, B.mem, A.mem], ?_⟩
  · rw [PtrAt, U.gpr, E.gpr, R, tc, ediD]
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, S.edi_toNat,
      show (16 : BitVec 32).toNat = 16 from rfl, show (256 : BitVec 32).toNat = 256 from rfl]
    rw [Nat.mod_eq_of_lt (a := j) (by omega), Nat.mod_eq_of_lt (a := 8 * w) (by omega),
      Nat.mod_eq_of_lt (a := 8 * w + 16) (by omega)]
    unfold slot stride VG.Impl.Bignum.hdrBytes
    have : j * (8 * w + 16) ≤ 32 * (8 * 64 + 16) := Nat.mul_le_mul (by omega) (by omega)
    omega
  · have kr {a b : State} {v : BitVec 32} (h : Upd a b r v) : Keeps [r, t] a b := h.keeps.mono (by simp)
    have kt {a b : State} {v : BitVec 32} (h : Upd a b t v) : Keeps [r, t] a b := h.keeps.mono (by simp)
    exact (((((kt A).trans (kt B)).trans (kr C)).trans (K.mono (by simp))).trans (kr E)).trans (kr U)

end VG.Proof.RsaKeyGen.X86.FrontRt
