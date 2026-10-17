module

import VerifiedGarbage.Proof.RsaPss.AArch64.SignEnc
public import VerifiedGarbage.Proof.RsaPss.AArch64.EmView
public import VerifiedGarbage.Proof.RsaPss.AArch64.OnHash
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs

/-!
# RSASSA-PSS on AArch64: the encoding, verified

After the checks, `signEnc` leaves at `scratch + oEm` the `k` bytes
`emT …` of the encoding of the digest with the salt (`signEnc_ok`), writing
only our working space, the stack below the frame and two slots: the part
for the hash function `H` that `hash` names (`encH_ok`), then MGF1 with the
one `G` that `mgf1_hash` names, of the `hLen` bytes of `H`'s digest.
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64 VG.WriteBytes
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only Keep)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.RsaPss (getD_app)

theorem bytes_apartL {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {q : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨q, n⟩ r) (hn : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' q n = Spec.Rsa.bytesAt m q n := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun i hi => hf.bytes (R := ⟨q, n⟩) hd hn (List.mem_range.mp hi)

theorem Lay.slotW {t : State} {F S : Addr} (L : Lay t F S) {d : Nat} (hd : d + 8 ≤ frameBytes)
    (h1 : d + 8 ≤ sNb ∨ sNb + 8 ≤ d) (h2 : d + 8 ≤ sDone ∨ sDone + 8 ≤ d) :
    ∀ r ∈ mgfWr F S, Region.Disjoint (slotR F d) r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.dFS.sub_left (Offset.sub_base F hd)
  · exact slot_not_below F hd
  · exact Offset.disjoint F h1 (by unfold frameBytes at hd; omega_using [hd]) (by decide)
  · exact Offset.disjoint F h2 (by unfold frameBytes at hd; omega_using [hd]) (by decide)

/-- What `encH` leaves: `EM` before the mask, with `H` (`h`) and the salt in
place (`V9`), and `H` the `hLen` bytes after `DB`. -/
def EncDone (k lo db sl : Nat) (saltB h : List Byte) (D : Nat) (V9 : Nat → Byte) : Prop :=
  (∀ x, oEm ≤ x → x < oEm + k → V9 x =
    if x = oEm + k - 1 then 0xbc
    else if oEm + lo + db ≤ x then h.getD (x - (oEm + lo + db)) 0
    else if oEm + lo + db - sl ≤ x then saltB.getD (x - (oEm + lo + db - sl)) 0
    else if x = oEm + lo + db - sl - 1 then 1 else 0) ∧
  (List.range D).map (fun i => V9 (oEm + lo + db + i)) = h

section
variable {H : Hash} (hH : HashOK H)

include hH in
/-- `encH`: `M'` hashed to `H`, then `EM` before the mask. -/
theorem encH_ok {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x)
    {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} (R : Rep t.mem S V)
    {k lo db sl : Nat} {dig q : Addr}
    (h19 : t.gpr .x19 = off S oSt) (h21 : t.gpr .x21 = off S oDig) (h23 : t.gpr .x23 = BitVec.ofNat 64 k)
    (h24 : t.gpr .x24 = off S (oEm + lo)) (h25 : t.gpr .x25 = BitVec.ofNat 64 db)
    (hdg : t.mem.readW (off F sDig) 64 = dig) (hq : t.mem.readW (off F sSalt) 64 = q)
    (hsl : t.mem.readW (off F sSaltLen) 64 = BitVec.ofNat 64 sl)
    (hk : k ≤ 1024) (hkd : lo + db + H.D + 1 = k) (hfit : sl + 1 ≤ db)
    (hdR : ∀ j < H.D, InRegions (t.rd ++ t.wr) (dig + BitVec.ofNat 64 j) 1)
    (hdW : ∀ r ∈ mgfWr F S, Region.Disjoint ⟨dig, H.D⟩ r)
    (hqR : ∀ j < sl, InRegions (t.rd ++ t.wr) (q + BitVec.ofNat 64 j) 1)
    (hqW : ∀ r ∈ mgfWr F S, Region.Disjoint ⟨q, sl⟩ r) :
    WP isa (encH H) t fun t' => t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r ∈ [Reg.x19, .x20, .x21, .x23, .x24, .x25, .x26], t'.gpr r = t.gpr r) ∧
      (∀ r ∈ preservedV, (t'.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64) ∧
      Frame (mgfWr F S) t.mem t'.mem ∧
      EncDone k lo db sl (Spec.Rsa.bytesAt t.mem q sl)
        (Hs.hash (Spec.RsaPss.zeros 8 ++ Spec.Rsa.bytesAt t.mem dig H.D ++ Spec.Rsa.bytesAt t.mem q sl)) H.D
        (fun o => t'.mem (off S o)) := by
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
  have hsl1 : sl ≤ 1024 := by omega_using [hk, hkd, hfit]
  have hD64 : H.D ≤ 64 := by omega_using [hDN, hN]
  generalize hsB : Spec.Rsa.bytesAt t.mem q sl = saltB
  generalize hdB : Spec.Rsa.bytesAt t.mem dig H.D = digB
  have hsBl : saltB.length = sl := by rw [← hsB, VG.Proof.RsaPkcs1Sig.bytesAt_length]
  have hdBl : digB.length = H.D := by rw [← hdB, VG.Proof.RsaPkcs1Sig.bytesAt_length]
  have hW : ∀ {d : Nat}, d + 8 ≤ frameBytes → (d + 8 ≤ sNb ∨ sNb + 8 ≤ d) → (d + 8 ≤ sDone ∨ sDone + 8 ≤ d) →
      ∀ {m : Mem}, Frame (mgfWr F S) t.mem m → m.readW (off F d) 64 = t.mem.readW (off F d) 64 :=
    fun hd h1 h2 _ hf => slot_keep hf (L.slotW hd h1 h2)
  unfold encH seqs seqs seqs seqs seqs seqs seqs seqs
  -- `Y` cleared.
  refine WP.seq (WP.mono (clearY_ok L R) fun u2 ⟨k2, f2, R2⟩ => ?_)
  have L2 := L.congr k2.sp k2.wr (k2.get .x20)
  have F2 : Frame (mgfWr F S) t.mem u2.mem := f2.mono (by simp)
  -- `mHash`.
  refine WP.seq (WP.mono (copyDigest_ok hH L2 R2 (dig := dig)
    (by rw [hW (by decide) (by decide) (by decide) F2, hdg])
    (by rw [k2.rd, k2.wr]; exact hdR) (hdW _ (by simp))) fun u3 ⟨k3, f3, R3⟩ => ?_)
  rw [bytes_apartL F2 hdW (by omega_using [hDN, hN]), hdB] at R3
  have L3 := L2.congr k3.sp k3.wr (k3.get .x20)
  have F3 : Frame (mgfWr F S) t.mem u3.mem := F2.trans (f3.mono (by simp))
  -- The salt.
  refine WP.seq (WP.mono (copySaltY_ok hH L3 R3 (q := q) (sl := sl)
    (by rw [hW (by decide) (by decide) (by decide) F3, hq])
    (by rw [hW (by decide) (by decide) (by decide) F3, hsl]) hsl1
    (by rw [k3.rd, k3.wr, k2.rd, k2.wr]; exact hqR) (hqW _ (by simp))) fun u4 ⟨k4, f4, R4⟩ => ?_)
  rw [bytes_apartL F3 hqW (by omega_using [hsl1]), hsB] at R4
  have L4 := L3.congr k4.sp k4.wr (k4.get .x20)
  have F4 : Frame (mgfWr F S) t.mem u4.mem := F3.trans (f4.mono (by simp))
  -- `ℓ` and `nbm`.
  refine WP.seq (WP.mono (signLen_ok hH L4 (sl := sl) (by rw [hW (by decide) (by decide) (by decide) F4, hsl])
    hsl1) fun u5 ⟨k5, x22₅, m5⟩ => ?_)
  have L5 := L4.congr k5.sp k5.wr (k5.get .x20)
  have R5 := R4.frame (m' := u5.mem) (rs := [slotR F sNb]) (by rw [m5]; exact frame_slot _ F sNb _)
    (L.slotS (by decide))
  have F5 : Frame (mgfWr F S) t.mem u5.mem := F4.trans (by rw [m5]; exact (frame_slot _ F sNb _).mono (by simp))
  -- `H = Hash(M')`.
  generalize hmsg : Spec.RsaPss.zeros 8 ++ digB ++ saltB = msg
  have hml : msg.length = 8 + H.D + sl := by
    rw [← hmsg, List.length_append, List.length_append, RsaPss.zeros_length, hdBl, hsBl]
  have hnb1 := Nat.lt_div_mul_add (a := 8 + H.D + sl + H.P.L) (b := H.P.B) hB0
  have hnb2 := Nat.div_mul_le_self (8 + H.D + sl + H.P.L) H.P.B
  have hnbB : ((8 + H.D + sl + H.P.L) / H.P.B + 1) * H.P.B = (8 + H.D + sl + H.P.L) / H.P.B * H.P.B + H.P.B :=
    Nat.succ_mul _ _
  have g5 : ∀ r ∈ [Reg.x19, .x20, .x21, .x23, .x24, .x25, .x26], u5.gpr r = t.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [k5.get _ (by decide), k4.get _ (by decide), k3.get _ (by decide), k2.get _ (by decide)]
  refine WP.seq (WP.mono (ctHash_ok hH L5 R5 (msg := msg) (nbm := (8 + H.D + sl + H.P.L) / H.P.B + 1)
    (by rw [g5 .x19 (by decide), h19]) (by rw [g5 .x21 (by decide), h21]) (by rw [x22₅, hml])
    (by rw [m5, Mem.readW_writeW_self64]) (by rw [hml, hnbB]; omega_using [hnb1])
        (by rw [hnbB]; omega_using [hDN, hN, hL, hBl, hsl1, hnb2]) (fun i hi => ?_))
    fun u6 ⟨O6, d6⟩ => ?_)
  · rw [← hmsg, getD_app, getD_app, RsaPss.zeros_length]
    by_cases h1 : i < 8
    · simp (disch := omega_arith) only [updL, clr, ↓ite_eq_left, ↓ite_eq_right, hdBl, List.length_append,
        RsaPss.zeros_length]
      exact (RsaPss.zeros_getD _ _).symm
    by_cases h2 : i < 8 + H.D
    · simp (disch := omega_arith) only [updL, ↓ite_eq_left, ↓ite_eq_right, hdBl, List.length_append,
        RsaPss.zeros_length]
      rw [show oY + i - (oY + 8) = i - 8 by omega_using []]
    by_cases h3 : i < 8 + H.D + sl
    · simp (disch := omega_arith) only [updL, ↓ite_eq_left, ↓ite_eq_right, hdBl, List.length_append,
        RsaPss.zeros_length]
      rw [show oY + i - (oY + 8 + H.D) = i - (8 + H.D) by omega_using []]
    · simp (disch := omega_arith) only [updL, clr, ↓ite_eq_left, ↓ite_eq_right, hdBl, List.length_append,
        RsaPss.zeros_length]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega_using [hsBl, h3])]
      rfl
  have L6 := L5.congr O6.sp O6.wr (O6.cs .x20 (by decide))
  have F6 : Frame (mgfWr F S) t.mem u6.mem := F5.trans (O6.fr.mono (by simp))
  have g6 : ∀ r ∈ [Reg.x19, .x20, .x21, .x23, .x24, .x25, .x26], u6.gpr r = t.gpr r := by
    intro r hr
    have hr' := hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [O6.cs r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide), g5 r hr']
  generalize hh : Hs.hash msg = h
  have hhl : h.length = H.D := by
    rw [← hh, hHh, hH.hash, List.length_take, MdStream.Md.hash, hH.md.digest_length]; omega_using [hDN]
  have hdig : ∀ j < H.D, (fun o => u6.mem (off S o)) (oDig + j) = h.getD j 0 := fun j hj => by
    show u6.mem (off S (oDig + j)) = _
    rw [← off_add, byte_of_bytesAt d6 hj, ← hh, hHh]
  have hW6 : ∀ {d : Nat}, d + 8 ≤ frameBytes → (d + 8 ≤ sNb ∨ sNb + 8 ≤ d) → (d + 8 ≤ sDone ∨ sDone + 8 ≤ d) →
      u6.mem.readW (off F d) 64 = t.mem.readW (off F d) 64 := fun hd h1 h2 => hW hd h1 h2 F6
  -- `EM` cleared.
  refine WP.seq (WP.mono (clearEm_ok L6 (fun _ _ => rfl) (k := k) (by rw [g6 .x23 (by decide), h23])
    (by omega_using [hkd]) hk) fun u7 ⟨k7, f7, R7⟩ => ?_)
  have L7 := L6.congr k7.sp k7.wr (k7.get .x20)
  have F7 : Frame (mgfWr F S) t.mem u7.mem := F6.trans (f7.mono (by simp))
  -- `0x01` and the salt.
  refine WP.seq (WP.mono (putSalt_ok L7 R7 (e := oEm + lo) (db := db) (q := q) (sl := sl)
    (by rw [k7.get .x24, g6 .x24 (by decide), h24]) (by rw [k7.get .x25, g6 .x25 (by decide), h25])
    (by rw [hW (by decide) (by decide) (by decide) F7, hq]) (by rw [hW (by decide) (by decide) (by decide) F7, hsl])
    (by omega_using [hfit]) (by omega_using [hk, hkd, c1, c2])
    (by rw [k7.rd, k7.wr, O6.rd, O6.wr, k5.rd, k5.wr, k4.rd, k4.wr, k3.rd, k3.wr, k2.rd, k2.wr]; exact hqR)
    (hqW _ (by simp))) fun u8 ⟨k8, f8, R8⟩ => ?_)
  rw [bytes_apartL F7 hqW (by omega_using [hk, hkd, hfit]), hsB] at R8
  have L8 := L7.congr k8.sp k8.wr (k8.get .x20)
  have F8 : Frame (mgfWr F S) t.mem u8.mem := F7.trans (f8.mono (by simp))
  -- `H` and `0xbc`.
  refine WP.mono (putH_ok hH L8 R8 (e := oEm + lo) (db := db) (k := k)
    (by rw [k8.get .x24, k7.get .x24, g6 .x24 (by decide), h24]) (by rw [k8.get .x25, k7.get .x25, g6 .x25 (by decide), h25])
    (by rw [k8.get .x21, k7.get .x21, g6 .x21 (by decide), h21]) (by rw [k8.get .x23, k7.get .x23, g6 .x23 (by decide), h23])
    (by omega_using []) (by omega_using [hkd]) hk)
    fun u9 ⟨k9, f9, R9⟩ => ?_
  have R9' : Rep u9.mem S (encV (fun o => u6.mem (off S o)) k lo db sl saltB H.D) := R9
  refine ⟨by rw [k9.sp, k8.sp, k7.sp, O6.sp, k5.sp, k4.sp, k3.sp, k2.sp],
    by rw [k9.rd, k8.rd, k7.rd, O6.rd, k5.rd, k4.rd, k3.rd, k2.rd],
    by rw [k9.wr, k8.wr, k7.wr, O6.wr, k5.wr, k4.wr, k3.wr, k2.wr], fun r hr => ?_,
    fun r hr => by rw [k9.vcs r hr, k8.vcs r hr, k7.vcs r hr, O6.vec r hr, k5.vcs r hr, k4.vcs r hr, k3.vcs r hr,
      k2.vcs r hr], F8.trans (f9.mono (by simp)), fun x hx₁ hx₂ => ?_, ?_⟩
  · have hr' := hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [k9.get r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
      k8.get r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
      k7.get r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide), g6 r hr']
  · show u9.mem (off S x) = _
    rw [R9' x (by omega_using [hx₂, hk, c1, c6])]
    exact encV_eq hsBl hkd hfit hk hD64 hdig x hx₁ hx₂
  · refine Eq.trans (List.map_congr_left fun i hi => ?_) (encV_seed (V6 := fun o => u6.mem (off S o)) hsBl hkd hfit hk hD64 hhl hdig)
    have := List.mem_range.mp hi
    exact R9' _ (by omega_using [this, hk, hkd, c1, c6])

end

/-- After the checks, with the hash function `H` (`kH` in `hs`) and MGF1's
`G` (`kG`): `EM`. -/
theorem signEnc_ok {hs : List Hash} {kH kG : Nat} {H G : Hash} (hkH : hs[kH]? = some H)
    (hkG : hs[kG]? = some G) (hl : hs.length ≤ 4096) (hH : HashOK H) (hG : HashOK G)
    {Hs Gs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x)
    (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs)
    {t : State} {F S : Addr} (L : Lay t F S)
    {k lo sl : Nat} {c : Byte} {dig q : Addr}
    (h19 : t.gpr .x19 = off S oSt) (h21 : t.gpr .x21 = off S oDig) (h23 : t.gpr .x23 = BitVec.ofNat 64 k)
    (h9 : t.gpr .x9 = BitVec.ofNat 64 (k - lo - (H.D + 2)))
    (hlo : t.mem.readW (off F sLo) 64 = BitVec.ofNat 64 lo)
    (hc : t.mem.readW (off F sC) 64 = BitVec.setWidth 64 c)
    (hdg : t.mem.readW (off F sDig) 64 = dig) (hq : t.mem.readW (off F sSalt) 64 = q)
    (hsl : t.mem.readW (off F sSaltLen) 64 = BitVec.ofNat 64 sl)
    (hsH : t.mem.readW (off F sHash) 64 = BitVec.ofNat 64 kH)
    (hsG : t.mem.readW (off F sMgf) 64 = BitVec.ofNat 64 kG)
    (hsD : t.mem.readW (off F sHLen) 64 = BitVec.ofNat 64 H.D)
    (hk : k ≤ 1024) (_hlo1 : lo ≤ 1) (hfit : H.D + sl + 2 ≤ k - lo)
    (hdR : ∀ j < H.D, InRegions (t.rd ++ t.wr) (dig + BitVec.ofNat 64 j) 1)
    (hdW : ∀ r ∈ mgfWr F S, Region.Disjoint ⟨dig, H.D⟩ r)
    (hqR : ∀ j < sl, InRegions (t.rd ++ t.wr) (q + BitVec.ofNat 64 j) 1)
    (hqW : ∀ r ∈ mgfWr F S, Region.Disjoint ⟨q, sl⟩ r) :
    WP isa (signEnc hs) t fun t' => t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r ∈ [Reg.x19, .x20, .x21, .x23, .x26], t'.gpr r = t.gpr r) ∧
      (∀ r ∈ preservedV, (t'.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64) ∧
      Frame (mgfWr F S) t.mem t'.mem ∧
      ∀ i < k, t'.mem (off S (oEm + i)) = RsaPss.emT lo (k - lo - H.D - 1) sl (Spec.Rsa.bytesAt t.mem q sl)
        (Hs.hash (Spec.RsaPss.zeros 8 ++ Spec.Rsa.bytesAt t.mem dig H.D ++ Spec.Rsa.bytesAt t.mem q sl))
        (Spec.Mgf1.mgf1 Gs (Hs.hash (Spec.RsaPss.zeros 8 ++ Spec.Rsa.bytesAt t.mem dig H.D ++
          Spec.Rsa.bytesAt t.mem q sl)) (k - lo - H.D - 1)) c i := by
  have hD := hH.sizes.D0
  have hDN := hH.sizes.DN
  have hN := hH.N_le
  have c1 : oEm = 2560 := rfl
  have c2 : oY = 3584 := rfl
  have c6 : oRsa = 8192 := rfl
  generalize hdb : k - lo - H.D - 1 = db
  have hW : ∀ {d : Nat}, d + 8 ≤ frameBytes → (d + 8 ≤ sNb ∨ sNb + 8 ≤ d) → (d + 8 ≤ sDone ∨ sDone + 8 ≤ d) →
      ∀ {m : Mem}, Frame (mgfWr F S) t.mem m → m.readW (off F d) 64 = t.mem.readW (off F d) 64 :=
    fun hd h1 h2 _ hf => slot_keep hf (L.slotW hd h1 h2)
  unfold signEnc seqs seqs seqs
  -- `DB`'s registers.
  refine WP.seq (WP.mono (dbRegs_ok L h9 hlo) fun u1 ⟨O1, x25₁, x24₁⟩ => ?_)
  rw [show k - lo - (H.D + 2) + 1 = db by omega_using [hfit, hdb]] at x25₁
  have L1 := L.congr O1.sp O1.wr (O1.get .x20)
  -- The part for `H`.
  refine WP.seq (onHash_wp hkH hl (by decide) (ld_slot L1 (by decide)) (by rw [L1.sp, O1.mem, hsH]) fun u1' O1' => ?_)
  have L1' := L1.congr O1'.sp O1'.wr (O1'.get .x20)
  have g1 : ∀ r ∈ [Reg.x19, .x20, .x21, .x23, .x24, .x25, .x26], u1'.gpr r = u1.gpr r := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact O1'.get _ (by decide)
  have m1 : u1'.mem = t.mem := by rw [O1'.mem, O1.mem]
  refine WP.mono (encH_ok hH hHh L1' (V := fun o => u1'.mem (off S o)) (fun _ _ => rfl) (k := k) (lo := lo) (db := db)
    (sl := sl) (dig := dig) (q := q)
    (by rw [g1 .x19 (by decide), O1.get .x19, h19]) (by rw [g1 .x21 (by decide), O1.get .x21, h21])
    (by rw [g1 .x23 (by decide), O1.get .x23, h23]) (by rw [g1 .x24 (by decide), x24₁])
    (by rw [g1 .x25 (by decide), x25₁]) (by rw [m1, hdg]) (by rw [m1, hq]) (by rw [m1, hsl]) hk
    (by omega_using [hfit, hdb]) (by omega_using [hfit, hdb]) (by rw [O1'.rd, O1'.wr, O1.rd, O1.wr]; exact hdR)
    (by rw [m1] at *; exact hdW) (by rw [O1'.rd, O1'.wr, O1.rd, O1.wr]; exact hqR) hqW)
    fun u9 ⟨sp9, rd9, wr9, cs9, v9, fr9, ed9, sd9⟩ => ?_
  rw [m1] at fr9 ed9 sd9
  have L9 := L1'.congr sp9 wr9 (cs9 .x20 (by decide))
  have g9 : ∀ r ∈ [Reg.x19, .x20, .x21, .x23, .x24, .x25, .x26], u9.gpr r = u1.gpr r := fun r hr => by
    rw [cs9 r hr, g1 r hr]
  -- MGF1 with `G`.
  refine WP.seq (onHash_wp hkG hl (by decide) (ld_slot L9 (by decide))
    (by rw [L9.sp, hW (by decide) (by decide) (by decide) fr9, hsG]) fun u9' O9' => ?_)
  have L9' := L9.congr O9'.sp O9'.wr (O9'.get .x20)
  have g9' : ∀ r ∈ [Reg.x19, .x20, .x21, .x23, .x24, .x25, .x26], u9'.gpr r = u1.gpr r := by
    intro r hr; have hr' := hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [O9'.get r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide), g9 r hr']
  have F9' : Frame (mgfWr F S) t.mem u9'.mem := by rw [O9'.mem]; exact fr9
  refine (WP.mono (mgfXor_ok hG hGh hGl hGv L9' (V := fun o => u9'.mem (off S o)) (fun _ _ => rfl)
      (sd := H.D) (e := oEm + lo) (db := db) ⟨by omega_using [], by omega_using [hfit, hdb], by omega_using [hk, hfit, hdb, c1, c2]⟩
      ⟨hD, by omega_using [hDN, hN]⟩ (by rw [hW (by decide) (by decide) (by decide) F9', hsD])
      (by rw [g9' .x19 (by decide), O1.get .x19, h19]) (by rw [g9' .x21 (by decide), O1.get .x21, h21])
      (by rw [g9' .x24 (by decide), x24₁]) (by rw [g9' .x25 (by decide), x25₁]))
    fun u10 ⟨sp10, rd10, wr10, cs10, v10, fr10, em10⟩ => ?_)
  have hseed : (List.range H.D).map (fun i => u9'.mem (off S (oEm + lo + db + i))) =
      Hs.hash (Spec.RsaPss.zeros 8 ++ Spec.Rsa.bytesAt t.mem dig H.D ++ Spec.Rsa.bytesAt t.mem q sl) := by
    rw [O9'.mem]; exact sd9
  rw [hseed] at em10
  have L10 := L9'.congr sp10 wr10 (cs10 .x20 (by decide))
  have F10 : Frame (mgfWr F S) t.mem u10.mem := F9'.trans fr10
  have hhl : (Hs.hash (Spec.RsaPss.zeros 8 ++ Spec.Rsa.bytesAt t.mem dig H.D ++ Spec.Rsa.bytesAt t.mem q sl)).length =
      H.D := by
    rw [← hseed, List.length_map, List.length_range]
  -- `DB`'s top bits.
  refine WP.mono (clearTop_ok L10 (fun _ _ => rfl) (e := oEm + lo) (c := c)
    (by rw [cs10 .x24 (by decide), g9' .x24 (by decide), x24₁]) (by omega_using [hk, hfit, hdb, c1, c6])
    (by rw [hW (by decide) (by decide) (by decide) F10, hc])) fun u11 ⟨k11, f11, R11⟩ => ?_
  refine ⟨by rw [k11.sp, sp10, O9'.sp, sp9, O1'.sp, O1.sp], by rw [k11.rd, rd10, O9'.rd, rd9, O1'.rd, O1.rd],
    by rw [k11.wr, wr10, O9'.wr, wr9, O1'.wr, O1.wr], fun r hr => ?_,
    fun r hr => by rw [k11.vcs r hr, v10 r hr, O9'.vcs r hr, v9 r hr, O1'.vcs r hr, O1.vcs r hr],
    F10.trans (f11.mono (by simp)), fun i hi => ?_⟩
  · have hr' := hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [k11.get _ (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide),
      cs10 _ (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp),
      g9' _ (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp),
      O1.get _ (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)]
  rw [← em_view (V9 := fun o => u9'.mem (off S o)) (mk := Spec.Mgf1.mgf1 Gs _ db) (c := c) hhl
    (by omega_using [hfit, hdb]) (by omega_using [hfit, hdb]) (fun x h₁ h₂ => by
      show u9'.mem (off S x) = _
      rw [O9'.mem]; exact ed9 x h₁ h₂) i hi, R11 _ (by omega_using [hk, c1, c6, hi])]
  simp only [upd]
  rw [em10 _ (by omega_using []) (by omega_using [hk, hfit, hdb, c1, c2]), em10 _ (by omega_using [])
    (by omega_using [hk, c1, c2, hi])]

end VG.Proof.RsaPss.AArch64
