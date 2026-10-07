import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyParts

/-!
# RSASSA-PSS verification on AArch64: unmasking `DB`

From RSAVP1's result in `EM`: the first checks into `acc` (`acc0`), `DB`
unmasked (`mgfXor`) and its top bits cleared (`clearTop`), its first
nonzero byte found (`posScan`) and checked (`posCheck`): `b1_ok`.
-/

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)

/-- `EM` after the mask and `clearTop`, from `V`, with `DB` at `e`. -/
def wct (V : Nat → Byte) (mk : List Byte) (e db : Nat) (c : Byte) : Nat → Byte :=
  upd (mixV V mk e db) e (mixV V mk e db e &&& c)

/-- The mask: MGF1 of `H`, the `hLen` bytes after `DB`. -/
def mkB (G : Spec.Mgf1.Hash) (D : Nat) (V : Nat → Byte) (e db : Nat) : List Byte :=
  Spec.Mgf1.mgf1 G ((List.range D).map fun i => V (e + db + i)) db

/-- `acc` after `acc0`. -/
def acc0V (V : Nat → Byte) (k lo : Nat) (c : Byte) : BitVec 64 :=
  ((V (oEm + k - 1)).setWidth 64 ^^^ BitVec.ofNat 64 0xbc) |||
    ((V oEm).setWidth 64 &&& (0#64 - BitVec.ofNat 64 lo)) |||
    ((V (oEm + lo)).setWidth 64 &&& (c.setWidth 64 ^^^ BitVec.ofNat 64 0xFF))

/-- `acc` after `posCheck`, for `DB`'s bytes `f`. -/
def acc1V (a0 : BitVec 64) (f : Nat → Byte) (db : Nat) (any sv : BitVec 64) : BitVec 64 :=
  (a0 ||| (((nzV f db).setWidth 64 ^^^ 1#64) |||
    (if nz f db = none then BitVec.allOnes 64 else 0) >>> 63)) |||
    (if any = 0 then sv ^^^ BitVec.ofNat 64 (db - (nz f db).getD 0 - 1) else 0)

/-- After `posCheck`. -/
structure B1 (G : Spec.Mgf1.Hash) (D : Nat) (t : State) (F S : Addr) (V : Nat → Byte) (k lo db : Nat) (c : Byte)
    (any sv : BitVec 64) (u : State) : Prop where
  sp : u.sp = t.sp
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  cs : ∀ r ∈ [Reg.x19, .x20, .x21, .x23, .x24, .x25], u.gpr r = t.gpr r
  v : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64
  fr : Frame (mgfWr F S ++ [slotR F sPos]) t.mem u.mem
  em : ∀ o, oEm ≤ o → o < oY → u.mem (off S o) = wct V (mkB G D V (oEm + lo) db) (oEm + lo) db c o
  pos : u.mem.readW (off F sPos) 64 =
    BitVec.ofNat 64 ((nz (fun i => wct V (mkB G D V (oEm + lo) db) (oEm + lo) db c (oEm + lo + i)) db).getD 0)
  acc : u.gpr .x26 = acc1V (acc0V V k lo c)
    (fun i => wct V (mkB G D V (oEm + lo) db) (oEm + lo) db c (oEm + lo + i)) db any sv

theorem nz_congr {f g : Nat → Byte} : ∀ {j : Nat}, (∀ i < j, f i = g i) → nz f j = nz g j
  | 0, _ => rfl
  | j + 1, h => by
    simp only [nz]
    rw [nz_congr (fun i hi => h i (by omega)), h j (by omega)]

theorem nzV_congr {f g : Nat → Byte} {j : Nat} (h : ∀ i < j, f i = g i) : nzV f j = nzV g j := by
  unfold nzV
  rw [← nz_congr h]
  split
  · rename_i i hi
    exact h i (nz_some hi).1
  · rfl

theorem nz_lt {f : Nat → Byte} {j : Nat} (hj : 0 < j) : (nz f j).getD 0 < j := by
  cases h : nz f j with
  | none => exact hj
  | some i => exact (nz_some h).1

section
variable {H : Hash} (hH : HashOK H)

include hH in
/-- From RSAVP1's result in `EM` (`V`), `DB` at `oEm + lo`, to `B1`. -/
theorem b1_ok {G : Spec.Mgf1.Hash} (hGh : ∀ x, G.hash x = hH.SH.H.hash x) (hGl : G.len = H.D)
    (hG : Proof.Mgf1.Valid G) {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} (R : Rep t.mem S V)
    {k lo db : Nat} {c : Byte} {any sv : BitVec 64} (hk : lo + db + H.D + 1 = k) (hdb : 1 ≤ db)
    (hk2 : k ≤ 1024) (hlo : lo ≤ 1) (h19 : t.gpr .x19 = off S oSt) (h21 : t.gpr .x21 = off S oDig)
    (h23 : t.gpr .x23 = BitVec.ofNat 64 k) (h24 : t.gpr .x24 = off S (oEm + lo))
    (h25 : t.gpr .x25 = BitVec.ofNat 64 db) (hLo : t.mem.readW (off F sLo) 64 = BitVec.ofNat 64 lo)
    (hC : t.mem.readW (off F sC) 64 = c.setWidth 64) (hA : t.mem.readW (off F sAny) 64 = any)
    (hS : t.mem.readW (off F sSaltLen) 64 = sv) {rest : Prog isa} {Q : State → Prop}
    (hQ : ∀ u, B1 G H.D t F S V k lo db c any sv u → WP isa rest u Q) :
    WP isa (seqs [.block acc0, mgfXor H, .block clearTop, posScan, posCheck, rest]) t Q := by
  have c1 : oEm = 2560 := rfl
  have c2 : oY = 3584 := rfl
  have c6 : oRsa = 8192 := rfl
  have hW : ∀ {d : Nat}, d + 8 ≤ frameBytes → (d + 8 ≤ sNb ∨ sNb + 8 ≤ d) → (d + 8 ≤ sDone ∨ sDone + 8 ≤ d) →
      ∀ {m : Mem}, Frame (mgfWr F S) t.mem m → m.readW (off F d) 64 = t.mem.readW (off F d) 64 :=
    fun hd h1 h2 _ hf => slot_keep hf (L.slotW hd h1 h2)
  unfold seqs seqs seqs seqs seqs
  -- `acc0`.
  refine WP.seq (WP.mono (acc0_ok L R (by omega) hk2 hlo h23 h24 hLo hC) fun u1 ⟨O1, x26₁⟩ => ?_)
  have L1 := L.congr O1.sp O1.wr (O1.get .x20)
  have R1 : Rep u1.mem S V := O1.mem ▸ R
  -- The mask.
  refine WP.seq (WP.mono (mgfXor_ok hH hGh hGl hG L1 R1 (e := oEm + lo) (db := db) ⟨by omega, hdb, by omega⟩
    (by rw [O1.get .x19, h19]) (by rw [O1.get .x21, h21]) (by rw [O1.get .x24, h24]) (by rw [O1.get .x25, h25]))
    fun u2 ⟨sp2, rd2, wr2, cs2, v2, fr2, em2⟩ => ?_)
  have L2 := L1.congr sp2 wr2 (cs2 .x20 (by decide))
  have F2 : Frame (mgfWr F S) t.mem u2.mem := by rw [O1.mem] at fr2; exact fr2
  -- `DB`'s top bits.
  refine WP.seq (WP.mono (clearTop_ok L2 (fun _ _ => rfl) (e := oEm + lo) (c := c)
    (by rw [cs2 .x24 (by decide), O1.get .x24, h24]) (by omega)
    (by rw [hW (by decide) (by decide) (by decide) F2, hC])) fun u3 ⟨k3, f3, R3⟩ => ?_)
  have L3 := L2.congr k3.sp k3.wr (k3.get .x20)
  have hX : ∀ {d : Nat}, d + 8 ≤ frameBytes → (d + 8 ≤ sNb ∨ sNb + 8 ≤ d) → (d + 8 ≤ sDone ∨ sDone + 8 ≤ d) →
      u3.mem.readW (off F d) 64 = t.mem.readW (off F d) 64 := fun hd h1 h2 => by
    rw [slot_keep f3 (L.slotSd hd), hW hd h1 h2 F2]
  -- The first nonzero byte.
  generalize hmk : mkB G H.D V (oEm + lo) db = mk
  have hmk' : Spec.Mgf1.mgf1 G ((List.range H.D).map fun i => V (oEm + lo + db + i)) db = mk := hmk
  rw [hmk'] at em2
  have hv : ∀ o, oEm ≤ o → o < oY →
      upd (fun o => u2.mem (off S o)) (oEm + lo) (u2.mem (off S (oEm + lo)) &&& c) o =
        wct V mk (oEm + lo) db c o := fun o h1 h2 => by
    unfold wct upd
    simp only []
    rw [em2 o h1 h2, em2 (oEm + lo) (by omega) (by omega)]
  have hf : ∀ i < db, upd (fun o => u2.mem (off S o)) (oEm + lo) (u2.mem (off S (oEm + lo)) &&& c) (oEm + lo + i) =
      wct V mk (oEm + lo) db c (oEm + lo + i) := fun i hi => hv _ (by omega) (by omega)
  refine WP.seq (WP.mono (posScan_ok L3 R3 (e := oEm + lo) (db := db) (by omega) (by omega)
    (by rw [k3.get .x24, cs2 .x24 (by decide), O1.get .x24, h24])
    (by rw [k3.get .x25, cs2 .x25 (by decide), O1.get .x25, h25])) fun u4 ⟨O4, x13₄, x14₄, x15₄⟩ => ?_)
  rw [nz_congr hf] at x13₄ x14₄
  rw [nzV_congr hf] at x15₄
  have L4 := L3.congr O4.sp O4.wr (O4.get .x20)
  -- Its checks.
  refine WP.seq (WP.mono (posCheck_ok L4 x13₄ x14₄ x15₄ (acc := acc0V V k lo c) (any := any) (sv := sv)
    (by rw [O4.get .x26, k3.get .x26, cs2 .x26 (by decide), x26₁]; rfl)
    (by rw [O4.get .x25, k3.get .x25, cs2 .x25 (by decide), O1.get .x25, h25]) (nz_lt (by omega))
    (by rw [O4.mem, hX (by decide) (by decide) (by decide), hA])
    (by rw [O4.mem, hX (by decide) (by decide) (by decide), hS])) fun u5 ⟨k5, m5, x26₅⟩ => hQ u5 ?_)
  have R5 := R3.frame (m' := u5.mem) (rs := [slotR F sPos]) (by rw [m5, O4.mem]; exact frame_slot _ F sPos _)
    (L.slotS (by decide))
  subst hmk
  exact {
    sp := by rw [k5.sp, O4.sp, k3.sp, sp2, O1.sp]
    rd := by rw [k5.rd, O4.rd, k3.rd, rd2, O1.rd]
    wr := by rw [k5.wr, O4.wr, k3.wr, wr2, O1.wr]
    cs := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      · rw [k5.get _ (by decide), O4.get _ (by decide), k3.get _ (by decide), cs2 _ (by decide),
          O1.get _ (by decide)]
    v := fun r hr => by rw [k5.vcs r hr, O4.vcs r hr, k3.vcs r hr, v2 r hr, O1.vcs r hr]
    fr := ((F2.mono (by simp)).trans ((f3.mono (by simp)).trans (by
      rw [m5, O4.mem]; exact (frame_slot _ F sPos _).mono (by simp))))
    em := fun o h1 h2 => by rw [R5 o (by omega), hv o h1 h2]
    pos := by rw [m5, Mem.readW_writeW_self64]
    acc := x26₅ }

end

end VG.Proof.RsaPss.AArch64
