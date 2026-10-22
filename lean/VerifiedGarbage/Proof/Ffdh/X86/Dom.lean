module

import VerifiedGarbage.Proof.Ffdh.X86.Stages
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Load
public import VerifiedGarbage.Impl.Ffdh.X86.Domain
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Power
public import VerifiedGarbage.Proof.Bignum.X86.CrtValue
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Ffdh.Contract

/-!
# FFDH on i686: the domain's components

`DomGeo`: the domain buffer of `dlen` bytes at synthetic argument 2, its
components p, g and q (`p_len` bytes each) at arguments 2, 4 and 6, with
their lengths. `loadComp_ok`: the `k`-th component into a wide slot, the
value `domainOf` gives it (`comp_p`, `comp_g`, `comp_q`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt

variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len dlen : Nat}
  {args : Nat → BitVec 32}

/-- The domain buffer and its components, as the synthetic arguments give them. -/
structure DomGeo (args : Nat → BitVec 32) (base : Addr) (bytes len dlen : Nat) (rd wr : List Region) : Prop where
  e3 : args 3 = BitVec.ofNat 32 len
  e5 : args 5 = BitVec.ofNat 32 len
  e7 : args 7 = BitVec.ofNat 32 len
  e4 : args 4 = args 2 + args 3
  e6 : args 6 = args 2 + args 3 + args 3
  e12 : args 12 = BitVec.ofNat 32 dlen
  dl : dlen = 2 * len ∨ dlen = 3 * len
  fit : (args 2).toNat + dlen ≤ 2 ^ 32
  rd : InRegions (rd ++ wr) (byteAddr (args 2)) dlen
  apart : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ ⟨base, bytes⟩
  lower : 64 ≤ len
  upper : len ≤ 1024

theorem DomGeo.keep {rd wr : List Region} (G : DomGeo args base bytes len dlen rd wr) {s t : State} {rs : List Reg}
    (e : s.rd = rd ∧ s.wr = wr) (K : Keeps rs s t) : DomGeo args base bytes len dlen t.rd t.wr := by
  rw [K.2.1, K.2.2, e.1, e.2]; exact G

/-- The `k`-th component's address. -/
theorem DomGeo.addr {rd wr : List Region} (G : DomGeo args base bytes len dlen rd wr) {k : Nat} (hk : k ≤ 2)
    (hkl : (k + 1) * len ≤ dlen) :
    byteAddr (args (2 + 2 * k)) = byteAddr (args 2) + BitVec.ofNat 64 (k * len) ∧
      (args (2 + 2 * k)).toNat = (args 2).toNat + k * len := by
  have f := G.fit
  have l := G.upper
  have e3 : (args 3).toNat = len := by rw [G.e3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl
  · simp
  · rw [show 2 + 2 * 1 = 4 from rfl, G.e4, G.e3, byteAddr_add (by omega)]
    refine ⟨by simp, ?_⟩
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := len) (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [show 2 + 2 * 2 = 6 from rfl, G.e6, G.e3, byteAddr_add (by rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := len) (by omega), Nat.mod_eq_of_lt (by omega)]; omega), byteAddr_add (by omega),
      VG.Offset.add_add]
    refine ⟨by congr 2; omega, ?_⟩
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := len) (by omega),
      Nat.mod_eq_of_lt (a := (args 2).toNat + len) (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

/-- The value of the `k`-th component. -/
abbrev comp (m : Mem) (args : Nat → BitVec 32) (len k : Nat) : Nat :=
  Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (byteAddr (args 2) + BitVec.ofNat 64 (k * len)) len)

/-- The `k`-th component into the wide slot `j`. -/
theorem loadComp_ok (h : In Ex base bytes len args s) (G : DomGeo args base bytes len dlen s.rd s.wr) {k j : Nat}
    (hk : k ≤ 2) (hkl : (k + 1) * len ≤ dlen) (hj : j ≤ 19) :
    WP isa (load (.slot .wide j) (one .wide) (2 + 2 * k) (3 + 2 * k)) s fun u =>
      sv u.mem base len .wide j = comp s.mem args len k ∧
      Outside base (lo len (.slot .wide j)) (bc len .wide) s.mem u.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  obtain ⟨ea, en⟩ := G.addr hk hkl
  have f := G.fit
  have l := G.upper
  have lb := len_le_bc len
  have lw := G.lower
  have hl : args (3 + 2 * k) = BitVec.ofNat 32 len := by
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl
    · exact G.e3
    · exact G.e5
    · exact G.e7
  have hkl' : k * len + len ≤ dlen := by rw [Nat.succ_mul] at hkl; exact hkl
  have rd : InRegions (s.rd ++ s.wr) (byteAddr (args (2 + 2 * k))) len := by
    rw [ea]; exact VG.CallLay.inRegions_sub G.rd (by omega) (by omega)
  have apart : Region.Disjoint ⟨byteAddr (args (2 + 2 * k)), len⟩ ⟨base, bytes⟩ := by
    rw [ea]; exact G.apart.sub_left (Offset.sub_base _ (by omega))
  refine WP.mono (load_ok h (one_ok .wide) (slot_fit1 h (j := j) (by omega)) (p := 2 + 2 * k) (l := 3 + 2 * k)
    (L := len) (by omega) (by omega) hl (by omega) (by rw [cb1]; exact lb) (by omega) rd apart)
    fun u ⟨V, O, K⟩ => ⟨by rw [cw1, ea] at V; exact V, by rw [cb1] at O; exact O, K⟩

/-- The components are `domainOf`'s p, g and q. -/
theorem comp_p (m : Mem) (args : Nat → BitVec 32) (h : 2 * len ≤ dlen) :
    comp m args len 0 = (Spec.Ffdh.domainOf len (Spec.Rsa.bytesAt m (byteAddr (args 2)) dlen)).p := by
  rw [VG.Proof.Ffdh.domainOf_p m _ h, comp, Nat.zero_mul]; congr 2; exact BitVec.add_zero _

theorem comp_g (m : Mem) (args : Nat → BitVec 32) (h : 2 * len ≤ dlen) :
    comp m args len 1 = (Spec.Ffdh.domainOf len (Spec.Rsa.bytesAt m (byteAddr (args 2)) dlen)).g := by
  rw [VG.Proof.Ffdh.domainOf_g m _ h, comp, Nat.one_mul]

theorem comp_q (m : Mem) (args : Nat → BitVec 32) :
    (Spec.Ffdh.domainOf len (Spec.Rsa.bytesAt m (byteAddr (args 2)) (3 * len))).q = some (comp m args len 2) := by
  rw [VG.Proof.Ffdh.domainOf_q3, comp, Nat.mul_comm 2 len]

end VG.Proof.Ffdh.X86
