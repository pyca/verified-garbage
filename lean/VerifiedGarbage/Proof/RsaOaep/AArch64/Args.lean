import VerifiedGarbage.Proof.RsaOaep.AArch64.Label

/-!
# RSAES-OAEP on AArch64: MGF1's arguments

The blocks that set MGF1's slots before each masking: the seed with `DB`
(`seedArgs_ok`) and `DB` with the seed (`dbArgs_ok`), from `k` in its slot.
-/

namespace VG.Proof.RsaOaep.AArch64

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Proof.Mgf1 (ifp ifn)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)

/-- The slot of `k`. -/
theorem Rep.rdK {m : Mem} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep m F S V W) {k : Nat}
    (hk : W 21 = BitVec.ofNat 64 k) : m.read (F + BitVec.ofNat 64 168) 8 = BitVec.ofNat 64 k :=
  R.rd8 (d := 168) (k := 21) rfl (by decide) hk

/-- MGF1's slots set: `src` and `srcLen` in words 13, 14, `dst` and
`dstLen` in 15, 16. -/
def mW (W : Nat → BitVec 64) (S : Addr) (src srcLen dst dstLen : Nat) : Nat → BitVec 64 :=
  upd (upd (upd (upd W 15 (off S dst)) 16 (BitVec.ofNat 64 dstLen)) 13 (off S src)) 14 (BitVec.ofNat 64 srcLen)

theorem mW_args (W : Nat → BitVec 64) (S : Addr) (src srcLen dst dstLen : Nat) :
    MArgs (mW W S src srcLen dst dstLen) S src srcLen dst dstLen :=
  ⟨by simp [mW, upd], by simp [mW, upd], by simp [mW, upd], by simp [mW, upd]⟩

theorem mW_eq (W : Nat → BitVec 64) (S : Addr) (src srcLen dst dstLen : Nat) {k : Nat} (hk : k < 13 ∨ 16 < k) :
    mW W S src srcLen dst dstLen k = W k := by
  simp only [mW, upd]
  rw [ifn (by omega), ifn (by omega), ifn (by omega), ifn (by omega)]

theorem seedArgs_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {H : Hash} {k : Nat} (hk : W 21 = BitVec.ofNat 64 k) (hD : 2 * H.D + 2 ≤ k)
    (hD' : H.D < 1024) (hk' : k ≤ 1024) (ws : List Region) :
    WP isa (.block (seedArgs H)) u fun u' => Lay u' F S ∧ Step F S ws u u' ∧
      Rep u'.mem F S V (mW W S (1 + H.D) (k - H.D - 1) 1 H.D) := by
  have G' := L.geo
  have R4 : Rep ((((u.mem.write (off F 120) 8 (off S 1)).write (off F 128) 8 (BitVec.ofNat 64 H.D)).write
      (off F 104) 8 (off S (1 + H.D))).write (off F 112) 8 (BitVec.ofNat 64 (k - H.D - 1))) F S V
      (mW W S (1 + H.D) (k - H.D - 1) 1 H.D) :=
    (((R.wq G' (k := 15) (by decide) _).wq G' (k := 16) (by decide) _).wq G' (k := 13) (by decide) _).wq G'
      (k := 14) (by decide) _
  have h96 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  have h168 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 168) 8 := L.ld (d := 168) (by decide)
  have w104 : InRegions u.wr (F + BitVec.ofNat 64 104) 8 := L.st (d := 104) (by decide)
  have w112 : InRegions u.wr (F + BitVec.ofNat 64 112) 8 := L.st (d := 112) (by decide)
  have w120 : InRegions u.wr (F + BitVec.ofNat 64 120) 8 := L.st (d := 120) (by decide)
  have w128 : InRegions u.wr (F + BitVec.ofNat 64 128) 8 := L.st (d := 128) (by decide)
  have hs : u.mem.read (F + BitVec.ofNat 64 96) 8 = S := L.slot
  have rk := R.rdK hk
  refine WP.mono (Q := fun (u' : State) => u'.mem = (((u.mem.write (off F 120) 8 (off S 1)).write (off F 128) 8
      (BitVec.ofNat 64 H.D)).write (off F 104) 8 (off S (1 + H.D))).write (off F 112) 8
      (BitVec.ofNat 64 (k - H.D - 1)) ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧ u'.v = u.v ∧
      (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u.gpr r)) ?_ fun u' ⟨hm, hrd, hwr, hsp, hv, hcs⟩ => ?_
  · oaep_run [seedArgs, scr, Mgf1.scr, lay, sScr, sK, sDst, sDstLen, sSrc, sSrcLen, oEm, h96, h168, w104, w112,
      w120, w128, L.sp, hs, rk, BitVec.add_zero, Nat.zero_add, imm16 (show H.D < 65536 by omega),
      Offset.ofNat_sub_ofNat (show H.D + 1 ≤ k by omega), show k - (H.D + 1) = k - H.D - 1 by omega,
      show 1 + H.D < 4096 by omega, show H.D + 1 < 4096 by omega]
    oaep_fin
  have R' : Rep u'.mem F S V (mW W S (1 + H.D) (k - H.D - 1) 1 H.D) := by rw [hm]; exact R4
  refine ⟨L.congr hsp hwr ?_, ⟨hrd, hwr, hsp, hcs, fun r _ => by rw [hv], ?_⟩, R'⟩
  · rw [show sScr = 8 * 12 from rfl, R'.fr 12 (by decide), R.fr 12 (by decide), mW_eq _ _ _ _ _ _ (by omega)]
  · rw [hm]
    exact Frame.write (Frame.write (Frame.write (Frame.write (Frame.refl _ _) (List.mem_cons_self ..) _
      (cF F (by decide))) (List.mem_cons_self ..) _ (cF F (by decide))) (List.mem_cons_self ..) _
      (cF F (by decide))) (List.mem_cons_self ..) _ (cF F (by decide))

theorem dbArgs_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {H : Hash} {k : Nat} (hk : W 21 = BitVec.ofNat 64 k) (hD : 2 * H.D + 2 ≤ k)
    (hD' : H.D < 1024) (hk' : k ≤ 1024) (ws : List Region) :
    WP isa (.block (dbArgs H)) u fun u' => Lay u' F S ∧ Step F S ws u u' ∧
      Rep u'.mem F S V (mW W S 1 H.D (1 + H.D) (k - H.D - 1)) := by
  have G' := L.geo
  have R4 : Rep ((((u.mem.write (off F 120) 8 (off S (1 + H.D))).write (off F 128) 8
      (BitVec.ofNat 64 (k - H.D - 1))).write (off F 104) 8 (off S 1)).write (off F 112) 8 (BitVec.ofNat 64 H.D)) F S V
      (mW W S 1 H.D (1 + H.D) (k - H.D - 1)) :=
    (((R.wq G' (k := 15) (by decide) _).wq G' (k := 16) (by decide) _).wq G' (k := 13) (by decide) _).wq G'
      (k := 14) (by decide) _
  have h96 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  have h168 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 168) 8 := L.ld (d := 168) (by decide)
  have w104 : InRegions u.wr (F + BitVec.ofNat 64 104) 8 := L.st (d := 104) (by decide)
  have w112 : InRegions u.wr (F + BitVec.ofNat 64 112) 8 := L.st (d := 112) (by decide)
  have w120 : InRegions u.wr (F + BitVec.ofNat 64 120) 8 := L.st (d := 120) (by decide)
  have w128 : InRegions u.wr (F + BitVec.ofNat 64 128) 8 := L.st (d := 128) (by decide)
  have hs : u.mem.read (F + BitVec.ofNat 64 96) 8 = S := L.slot
  have rk := R.rdK hk
  refine WP.mono (Q := fun (u' : State) => u'.mem = (((u.mem.write (off F 120) 8 (off S (1 + H.D))).write
      (off F 128) 8 (BitVec.ofNat 64 (k - H.D - 1))).write (off F 104) 8 (off S 1)).write (off F 112) 8
      (BitVec.ofNat 64 H.D) ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧ u'.v = u.v ∧
      (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u.gpr r)) ?_ fun u' ⟨hm, hrd, hwr, hsp, hv, hcs⟩ => ?_
  · oaep_run [dbArgs, scr, Mgf1.scr, lay, sScr, sK, sDst, sDstLen, sSrc, sSrcLen, oEm, h96, h168, w104, w112,
      w120, w128, L.sp, hs, rk, BitVec.add_zero, Nat.zero_add, imm16 (show H.D < 65536 by omega),
      Offset.ofNat_sub_ofNat (show H.D + 1 ≤ k by omega), show k - (H.D + 1) = k - H.D - 1 by omega,
      show 1 + H.D < 4096 by omega, show H.D + 1 < 4096 by omega]
    oaep_fin
  have R' : Rep u'.mem F S V (mW W S 1 H.D (1 + H.D) (k - H.D - 1)) := by rw [hm]; exact R4
  refine ⟨L.congr hsp hwr ?_, ⟨hrd, hwr, hsp, hcs, fun r _ => by rw [hv], ?_⟩, R'⟩
  · rw [show sScr = 8 * 12 from rfl, R'.fr 12 (by decide), R.fr 12 (by decide), mW_eq _ _ _ _ _ _ (by omega)]
  · rw [hm]
    exact Frame.write (Frame.write (Frame.write (Frame.write (Frame.refl _ _) (List.mem_cons_self ..) _
      (cF F (by decide))) (List.mem_cons_self ..) _ (cF F (by decide))) (List.mem_cons_self ..) _
      (cF F (by decide))) (List.mem_cons_self ..) _ (cF F (by decide))

end VG.Proof.RsaOaep.AArch64
