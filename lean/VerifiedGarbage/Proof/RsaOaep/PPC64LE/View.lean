module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Base
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Mgf1.Bytes

/-!
# RSA paddings on PPC64LE: writes to our part of the working space

Untrusted: everything here is checked by Lean. Writes to our part of the
working space as its view (`view_wb`, `view_w8`), which keep `Base`
(`Base.wb`); which bytes are writable and readable (`sc_w`, `rd_in`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.WriteBytes
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo)
open VG.Proof.Mgf1 (ifp ifn)

/-! ## Views of writes -/

theorem view_wb (m : Mem) {S : Addr} {d o : Nat} (xs : List Byte)
    (hd : d + xs.length ≤ oRsa) (ho : o < oRsa) :
    view (writeBytes m (off S d) xs) S o = if d ≤ o ∧ o < d + xs.length then xs.getD (o - d) 0 else view m S o := by
  simp only [view, writeBytes]
  rw [Offset.sub_toNat' S (by unfold oRsa at *; omega) (by unfold oRsa at *; omega)]
  by_cases h : d ≤ o
  · rw [ifp h]
    by_cases h' : o - d < xs.length
    · rw [ifp h', ifp ⟨h, by omega⟩]
    · rw [ifn h', ifn (by omega)]
  · rw [ifn h, ifn (by unfold oRsa at *; omega), ifn (by omega)]

theorem view_w8 (m : Mem) {S : Addr} {d o : Nat} (b : Byte) (hd : d < oRsa)
    (ho : o < oRsa) : view (m.writeW (off S d) b) S o = if o = d then b else view m S o := by
  simp only [view]
  rw [writeW8_apply]
  by_cases h : o = d
  · subst h; simp
  · rw [ifn (Offset.add_ofNat_ne S (by unfold oRsa at *; omega) (by unfold oRsa at *; omega) h), ifn h]

section
variable {S : State → Addr} {vf : State → Reg → BitVec 64} {s : State} (P : Fits S s)
include P

theorem S_fits : (S s).toNat + oRsa ≤ 2 ^ 64 := P.wS

/-- The bytes at `S + d`, `d + n ≤ oRsa`, are writable. -/
theorem sc_w {t : State} (ht : t.wr = fr s :: s.wr) {d n : Nat} (hd : d + n ≤ oRsa) :
    ∀ i < n, InRegions t.wr (off (S s) d + BitVec.ofNat 64 i) 1 := fun i hi => by
  show InRegions t.wr (off (off (S s) d) i) 1
  rw [ht, off_off]; exact sc_inW P (by omega)

omit P in
/-- Bytes of a caller's buffer are readable. -/
theorem rd_in {t : State} (ht : t.rd = s.rd) {R : Region} (hR : R ∈ s.rd) (hw : R.base.toNat + R.len ≤ 2 ^ 64)
    {n : Nat} (hn : n ≤ R.len) : ∀ j < n, InRegions (t.rd ++ t.wr) (R.base + BitVec.ofNat 64 j) 1 := fun j hj => by
  rw [ht]
  exact ⟨R, List.mem_append_left _ hR, Offset.contains_base _ (by omega) (by omega)⟩

omit P in
/-- Bytes of two disjoint regions are at different addresses. -/
theorem ne_of_dis {A B : Region} (h : A.Disjoint B) {a b : Addr} (ha : A.Contains a 1) (hb : B.Contains b 1) :
    a ≠ b := fun e => h a ha (e ▸ hb)

/-- A write of bytes to our part of the working space keeps `Base`. -/
theorem Base.wb {t w : State} {rs : List Reg} (h : Base S vf s t) (o : Keep rs t w) {d : Nat} {xs : List Byte}
    (hd : d + xs.length ≤ oRsa) (hm : w.mem = writeBytes t.mem (off (S s) d) xs)
    (hrs : ∀ r ∈ rs, r ∉ .r14 :: fx ++ hiRegs := by decide) : Base S vf s w :=
  h.keep P o (R := [⟨off (S s) d, xs.length⟩]) (by rw [hm]; exact writeBytes_frame _ _ _ (Region.contains_self _ _))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (sc_in hd)) hrs

end

end VG.Proof.RsaOaep.PPC64LE
