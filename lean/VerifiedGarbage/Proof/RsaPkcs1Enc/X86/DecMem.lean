module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecBase
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSAES-PKCS1-v1_5 decryption on x86: `scratch`

As on ARMv7 (`Proof/RsaPkcs1Enc/Arm/DecMem.lean`): the parts of `scratch`
the function uses (`sc P o n`, its `n` bytes from offset `o`, all within its
first 8448 bytes, which every `scratch` has), and where they are: apart from
each other as their offsets say (`sc_sep`), from the frames and the stack
below (`In.fr_sc`, `In.low_sc`), and from the other buffers (`In.sc_ro`,
`In.sc_out`, `In.sc_ml`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Dec

open VG VG.Impl.RsaPkcs1Enc.X86.Decrypt VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes

variable {P : EP} {σ : State}

/-- The `n` bytes of `scratch` from offset `o`. -/
abbrev sc (P : EP) (o n : Nat) : Region := ⟨P.scr.setWidth 64 + BitVec.ofNat 64 o, n⟩

namespace In

variable (h : In P σ)
include h

theorem sl8 : 8448 ≤ P.sl * 8 := by
  have := h.slK; have := h.k64; simp only [Spec.Rsa.scratchWords] at *; omega

theorem scr_fit : P.scr.toNat + P.sl * 8 ≤ 2 ^ 32 := by
  have := h.ok.fits P.SCR (by simp)
  simp only [BitVec.toNat_setWidth] at this
  rwa [Nat.mod_eq_of_lt (by have := P.scr.isLt; omega)] at this

theorem scr_toNat {o : Nat} (ho : o < 8448) : (P.scr + BitVec.ofNat 32 o).toNat = P.scr.toNat + o := by
  have := h.scr_fit; have := h.sl8
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega), Nat.mod_eq_of_lt (by omega)]

/-- `scratch + o`, as an address. -/
theorem scrA {o : Nat} (ho : o < 8448) :
    (P.scr + BitVec.ofNat 32 o).setWidth 64 = P.scr.setWidth 64 + BitVec.ofNat 64 o := by
  have := h.scr_fit; have := h.sl8
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, h.scr_toNat ho, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := P.scr.toNat) (by have := P.scr.isLt; omega), Nat.mod_eq_of_lt (a := o) (by omega)]

/-- `[scratch + o + d]`, as an address. -/
theorem addrSc {o d : Nat} (ho : o + d < 8448) :
    addr (P.scr + BitVec.ofNat 32 o) d = P.scr.setWidth 64 + BitVec.ofNat 64 (o + d) := by
  rw [addr, BitVec.add_assoc, BitVec.ofNat_add_ofNat, h.scrA ho]

theorem sc_sub {o n : Nat} (hn : o + n ≤ 8448) : Region.Sub (sc P o n) P.SCR :=
  Offset.sub_base _ (by have := h.sl8; omega)

theorem sc_ro {o n : Nat} (hn : o + n ≤ 8448) {R : Region} (hR : R ∈ P.lay.ro) : (sc P o n).Disjoint R :=
  (h.ok.rw_ro (w := P.SCR) (by simp) hR).sub_left (h.sc_sub hn)

theorem sc_out {o n : Nat} (hn : o + n ≤ 8448) : (sc P o n).Disjoint P.OUT := by
  have := h.ok.wrw
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at this
  exact (this.1.2.symm).sub_left (h.sc_sub hn)

theorem sc_ml {o n : Nat} (hn : o + n ≤ 8448) : (sc P o n).Disjoint P.ML := by
  have := h.ok.wrw
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at this
  exact (this.2.1.symm).sub_left (h.sc_sub hn)

theorem fr_sc {d k o n : Nat} (hd : d + k ≤ frameBytes + 16) (hn : o + n ≤ 8448) :
    Region.Disjoint ⟨P.lay.fr d, k⟩ (sc P o n) :=
  (h.ok.stk_fr (R := P.SCR) (.inr (by simp)) hd).sub_right (h.sc_sub hn)

theorem low_sc {o n : Nat} (hn : o + n ≤ 8448) : P.lay.LOW.Disjoint (sc P o n) :=
  (h.ok.low_buf (R := P.SCR) (.inr (by simp))).sub_right (h.sc_sub hn)

end In

theorem sc_sep {o n o' n' : Nat} (hs : o + n ≤ o' ∨ o' + n' ≤ o) (h₁ : o + n ≤ 8448) (h₂ : o' + n' ≤ 8448) :
    (sc P o n).Disjoint (sc P o' n') :=
  Offset.disjoint _ hs (by omega) (by omega)

theorem St.sc_w {s : State} (hs : S P σ s) {o n : Nat} (hn : o + n ≤ 8448) :
    InRegions s.wr (P.scr.setWidth 64 + BitVec.ofNat 64 o) n :=
  ⟨P.SCR, hs.2.inRw (by simp), Offset.contains_base _ (by have := hs.1.sl8; omega) (by omega)⟩

theorem St.sc_r {s : State} (hs : S P σ s) {o n : Nat} (hn : o + n ≤ 8448) :
    InRegions (s.rd ++ s.wr) (P.scr.setWidth 64 + BitVec.ofNat 64 o) n :=
  let ⟨r, hr, hc⟩ := St.sc_w hs hn
  ⟨r, List.mem_append_right _ hr, hc⟩

end VG.Proof.RsaPkcs1Enc.X86.Dec
