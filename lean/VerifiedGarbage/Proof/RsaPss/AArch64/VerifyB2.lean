import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyB1

/-!
# RSASSA-PSS verification on AArch64: hashing `M'` and comparing

After `posCheck`: `M' = (0x00)⁸ ‖ mHash ‖ salt` in `Y` (`clearY`,
`copyDigest`, `copyDb`, `shift`), hashed (`verifyNb`, `ctHash`), and the
hash compared with `H` into `acc`, `x0 = 1` exactly when `acc = 0` (`cmpH`):
`b2_ok`.
-/

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)

theorem orF_congr {g g' : Nat → BitVec 64} : ∀ {j : Nat}, (∀ i < j, g i = g' i) → orF g j = orF g' j
  | 0, _ => rfl
  | j + 1, h => by
    simp only [orF]
    rw [orF_congr (fun i hi => h i (by omega)), h j (by omega)]

/-- `M'`: eight zeros, `mHash` and the salt, the `db - pos - 1` bytes of
`DB` (`W`) after `pos`. -/
def msgV (mH : List Byte) (W : Nat → Byte) (db pos : Nat) : List Byte :=
  Spec.RsaPss.zeros 8 ++ mH ++ (List.range (db - pos - 1)).map fun i => W (pos + 1 + i)

theorem msgV_length (mH : List Byte) (W : Nat → Byte) (db pos : Nat) :
    (msgV mH W db pos).length = 8 + mH.length + (db - pos - 1) := by
  simp only [msgV, List.length_append, RsaPss.zeros_length, List.length_map, List.length_range]

/-- `x0` after `cmpH`, for `acc` and the hash `h` of `M'` against `H` in
`W` at `e + db`. -/
def resV (acc : BitVec 64) (h : List Byte) (W : Nat → Byte) (e db D : Nat) : BitVec 64 :=
  ((acc ||| orF (fun i => (h.getD i 0).setWidth 64 ^^^ (W (e + db + i)).setWidth 64) D) - 1#64) >>> 63

section
variable {H : Hash} (hH : HashOK H)

include hH in
/-- `Y` from `clearY`, `copyDigest`, `copyDb` and `shift` is `M'` padded
with zeros. -/
theorem msg_y {V0 : Nat → Byte} {W : Nat → Byte} {mH : List Byte} {e db pos i : Nat} (hm : mH.length = H.D)
    (hpos : pos < db) (hdb : db < 1024) (hi : i < 2048) :
    shW (updL (updL (clr V0 oY 2048) (oY + 8) mH) (oY + 8 + H.D)
      ((List.range db).map fun j => updL (clr V0 oY 2048) (oY + 8) mH (e + j))) (oY + 8 + H.D) db
      (fun j => W j) (pos + 1) (oY + i) = (msgV mH W db pos).getD i 0 := by
  have hDN := hH.sizes.DN
  have hN := hH.N_le
  unfold msgV
  rw [getD_app, getD_app]
  simp only [List.length_append, RsaPss.zeros_length, hm]
  by_cases h1 : i < 8
  · simp (disch := omega) only [shW, updL, clr, ite_eq_left, ite_eq_right, hm, List.length_map,
      List.length_range]
    exact (RsaPss.zeros_getD _ _).symm
  by_cases h2 : i < 8 + H.D
  · simp (disch := omega) only [shW, updL, clr, ite_eq_left, ite_eq_right, hm, List.length_map,
      List.length_range]
    rw [show oY + i - (oY + 8) = i - 8 by omega]
  by_cases h3 : i < 8 + H.D + db
  · simp (disch := omega) only [shW, updL, clr, ite_eq_left, ite_eq_right, hm, List.length_map,
      List.length_range]
    unfold zf
    rw [show oY + i - (oY + 8 + H.D) + (pos + 1) = pos + 1 + (i - (8 + H.D)) by omega]
    by_cases h4 : i - (8 + H.D) < db - pos - 1
    · rw [ite_eq_left (by omega), List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h4]
      rfl
    · rw [ite_eq_right (by omega), List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_none (by rw [List.length_range]; omega)]
      rfl
  · simp (disch := omega) only [shW, updL, clr, ite_eq_left, ite_eq_right, hm, List.length_map,
      List.length_range]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_none (by rw [List.length_range]; omega)]
    rfl

include hH in
/-- From `posCheck`'s state (`u`): `x0` is 1 exactly when `acc` is zero and
the hash of `M'` is `H`. -/
theorem b2_ok {u : State} {F S : Addr} (L : Lay u F S) {W : Nat → Byte} {e db pos : Nat} {acc : BitVec 64}
    {dig : Addr} (hEm : ∀ o, oEm ≤ o → o < oY → u.mem (off S o) = W o) (he : oEm ≤ e)
    (hfit : e + db + H.D ≤ oY) (hpos : pos < db) (hdb : db < 1024)
    (h19 : u.gpr .x19 = off S oSt) (h21 : u.gpr .x21 = off S oDig) (h24 : u.gpr .x24 = off S e)
    (h25 : u.gpr .x25 = BitVec.ofNat 64 db) (h26 : u.gpr .x26 = acc)
    (hP : u.mem.readW (off F sPos) 64 = BitVec.ofNat 64 pos) (hdg : u.mem.readW (off F sDig) 64 = dig)
    (hr : ∀ j < H.D, InRegions (u.rd ++ u.wr) (dig + BitVec.ofNat 64 j) 1)
    (hd : Region.Disjoint ⟨dig, H.D⟩ ⟨S, oRsa⟩) :
    WP isa (seqs [clearY, copyDigest H, copyDb H, shift H, .block (verifyNb H), ctHash H, cmpH H]) u
      fun u' => u'.sp = u.sp ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧
        (∀ r ∈ [Reg.x19, .x20, .x21, .x23, .x24, .x25], u'.gpr r = u.gpr r) ∧
        (∀ r ∈ preservedV, (u'.v r).extractLsb' 0 64 = (u.v r).extractLsb' 0 64) ∧
        Frame (mgfWr F S) u.mem u'.mem ∧
        u'.gpr .x0 = resV acc (hH.SH.H.hash (msgV (Spec.Rsa.bytesAt u.mem dig H.D) (fun i => W (e + i)) db pos))
          W e db H.D := by
  have hD := hH.sizes.D0
  have hDN := hH.sizes.DN
  have hN := hH.N_le
  have hL := hH.L
  have hB0 := hH.B_pos
  have hBl := hH.B_le
  have c1 : oEm = 2560 := rfl
  have c2 : oY = 3584 := rfl
  have c3 : oDig = 2304 := rfl
  have c6 : oRsa = 8192 := rfl
  unfold seqs seqs seqs seqs seqs seqs
  -- `Y` cleared.
  refine WP.seq (WP.mono (clearY_ok L (V := fun o => u.mem (off S o)) (fun _ _ => rfl)) fun u1 ⟨k1, f1, R1⟩ => ?_)
  have L1 := L.congr k1.sp k1.wr (k1.get .x20)
  have hm1 : Spec.Rsa.bytesAt u1.mem dig H.D = Spec.Rsa.bytesAt u.mem dig H.D :=
    bytes_apartL f1 (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) (by omega)
  -- `mHash`.
  refine WP.seq (WP.mono (copyDigest_ok hH L1 R1 (dig := dig) (by rw [slot_keep f1 (L.slotSd (by decide)), hdg])
    (by rw [k1.rd, k1.wr]; exact hr) hd) fun u2 ⟨k2, f2, R2⟩ => ?_)
  rw [hm1] at R2
  generalize hmH : Spec.Rsa.bytesAt u.mem dig H.D = mH at R2
  have hml : mH.length = H.D := by rw [← hmH, VG.Proof.RsaPkcs1Sig.bytesAt_length]
  have L2 := L1.congr k2.sp k2.wr (k2.get .x20)
  -- `DB`.
  refine WP.seq (WP.mono (copyDb_ok hH L2 R2 (e := e) (db := db) (by omega) (by omega)
    (by rw [k2.get .x24, k1.get .x24, h24]) (by rw [k2.get .x25, k1.get .x25, h25])) fun u3 ⟨k3, f3, R3⟩ => ?_)
  have L3 := L2.congr k3.sp k3.wr (k3.get .x20)
  have F3 : Frame [⟨S, oRsa⟩] u.mem u3.mem := f1.trans (f2.trans f3)
  -- The salt to `DB`'s place.
  refine WP.seq (WP.mono (shift_ok H (by omega) L3 R3 (W := fun j => W (e + j)) hpos hdb (by omega)
    (fun m hm => ?_) (by rw [k3.get .x25, k2.get .x25, k1.get .x25, h25])
    (by rw [slot_keep F3 (L.slotSd (by decide)), hP])) fun u4 ⟨k4, f4, R4, x22₄⟩ => ?_)
  · unfold zf
    by_cases h : m < db
    · rw [ite_eq_left h]
      simp (disch := omega) only [updL, clr, ite_eq_left, ite_eq_right, hml, List.length_map, List.length_range]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
      simp (disch := omega) only [Option.map_some, Option.getD_some, ite_eq_right]
      rw [show oY + 8 + H.D + m - (oY + 8 + H.D) = m by omega, hEm _ (by omega) (by omega)]
    · rw [ite_eq_right h]
      simp (disch := omega) only [updL, clr, ite_eq_left, ite_eq_right, hml, List.length_map, List.length_range]
  have L4 := L3.congr k4.sp k4.wr (k4.get .x20)
  -- `nbm`.
  refine WP.seq (WP.mono (verifyNb_ok hH L4 (db := db) (by omega)
    (by rw [k4.get .x25, k3.get .x25, k2.get .x25, k1.get .x25, h25])) fun u5 ⟨k5, m5⟩ => ?_)
  have L5 := L4.congr k5.sp k5.wr (k5.get .x20)
  have R5 := R4.frame (m' := u5.mem) (rs := [slotR F sNb]) (by rw [m5]; exact frame_slot _ F sNb _)
    (L.slotS (by decide))
  -- `Hash(M')`.
  generalize hmsg : msgV mH (fun i => W (e + i)) db pos = msg
  have hmsgl : msg.length = 8 + H.D + (db - pos - 1) := by rw [← hmsg, msgV_length, hml]
  have hnb1 := Nat.lt_div_mul_add (a := db + 7 + H.D + H.P.L) (b := H.P.B) hB0
  have hnb2 := Nat.div_mul_le_self (db + 7 + H.D + H.P.L) H.P.B
  have hnbB : ((db + 7 + H.D + H.P.L) / H.P.B + 1) * H.P.B =
      (db + 7 + H.D + H.P.L) / H.P.B * H.P.B + H.P.B := Nat.succ_mul _ _
  have g5 : ∀ r ∈ [Reg.x19, .x20, .x21, .x23, .x24, .x25, .x26], u5.gpr r = u.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [k5.get _ (by decide), k4.get _ (by decide), k3.get _ (by decide), k2.get _ (by decide),
        k1.get _ (by decide)]
  refine WP.seq (WP.mono (ctHash_ok hH L5 R5 (msg := msg) (nbm := (db + 7 + H.D + H.P.L) / H.P.B + 1)
    (by rw [g5 .x19 (by decide), h19]) (by rw [g5 .x21 (by decide), h21])
    (by rw [k5.get .x22, x22₄, hmsgl]) (by rw [m5, Mem.readW_writeW_self64]) (by rw [hmsgl, hnbB]; omega)
    (by rw [hnbB]; omega) (fun i hi => ?_)) fun u6 ⟨O6, d6⟩ => ?_)
  · rw [← hmsg]
    exact msg_y hH hml hpos hdb (by rw [hnbB] at hi; omega)
  have L6 := L5.congr O6.sp O6.wr (O6.cs .x20 (by decide))
  -- The comparison.
  refine WP.mono (cmpH_ok hH L6 (V := fun o => u6.mem (off S o)) (fun _ _ => rfl) (e := e) (db := db) (acc := acc)
    hfit (by rw [O6.cs .x21 (by decide), g5 .x21 (by decide), h21])
    (by rw [O6.cs .x24 (by decide), g5 .x24 (by decide), h24])
    (by rw [O6.cs .x25 (by decide), g5 .x25 (by decide), h25])
    (by rw [O6.cs .x26 (by decide), g5 .x26 (by decide), h26])) fun u7 ⟨O7, x0₇⟩ => ?_
  have F5 : Frame (mgfWr F S) u.mem u5.mem :=
    (F3.trans f4).mono (by simp) |>.trans (by rw [m5]; exact (frame_slot _ F sNb _).mono (by simp))
  refine ⟨by rw [O7.sp, O6.sp, k5.sp, k4.sp, k3.sp, k2.sp, k1.sp], by rw [O7.rd, O6.rd, k5.rd, k4.rd, k3.rd, k2.rd, k1.rd],
    by rw [O7.wr, O6.wr, k5.wr, k4.wr, k3.wr, k2.wr, k1.wr], fun r hr => ?_,
    fun r hr => by rw [O7.vcs r hr, O6.vec r hr, k5.vcs r hr, k4.vcs r hr, k3.vcs r hr, k2.vcs r hr, k1.vcs r hr],
    by rw [O7.mem]; exact F5.trans (O6.fr.mono (by simp)), ?_⟩
  · have hr' := hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [O7.get r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
      O6.cs r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
      g5 r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
  · rw [x0₇, resV]
    congr 2
    refine congrArg (acc ||| ·) (orF_congr fun i hi => ?_)
    rw [← off_add, byte_of_bytesAt d6 hi, O6.em _ (by omega) (by omega)]
    simp (disch := omega) only [shW, updL, clr, ite_eq_right, hml, List.length_map, List.length_range]
    rw [hEm _ (by omega) (by omega)]

end

end VG.Proof.RsaPss.AArch64
