module

public import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyMain
public import VerifiedGarbage.Proof.RsaPss.X86_64.MgfAny
public import VerifiedGarbage.Proof.RsaPss.X86_64.AnySafe
public import VerifiedGarbage.Proof.RsaPss.X86_64.SaltBack
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT

/-!
# RSASSA-PSS verification with the hash functions as arguments on x86-64: `DB`

After the public-key operation, `acc0`, MGF1 with the `g`th hash function
(`mgfXorAny`), `clearTop` and `posScan` leave `acc`, `DB` unmasked and its
first nonzero byte as `vmid_ok` does for one hash function (`vmidA_ok`);
the digest's hash function decides the rest (`verifyTail`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Any

open VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64 VG.Impl.RsaPss.X86_64.AnyHash
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)

theorem vmidA_safe {hs : List Hash} (ht : TierOk hs) :
    (seqs [.block acc0, mgfXorAny hs, .block clearTop, posScan]).allInstrs safeI = true := by
  simp only [seqs, posScan, Code.allInstrs, mgfXorAny_safe ht, rec_all, List.all_append, byteLoop, step,
    Bool.and_true, Bool.true_and]
  rfl

theorem vmidA_xd {hs : List Hash} (ht : TierOk hs) :
    (seqs [.block acc0, mgfXorAny hs, .block clearTop, posScan]).x86_64Depth ≤ 8 := by
  have := mgfXorAny_xd ht
  simp only [seqs, posScan, byteLoop, Code.x86_64Depth, Nat.max_le]
  omega

theorem verifyTail_safe {H : Hash} (hH : HashOK H) (K : Callees H) : (verifyTail H).allInstrs safeI = true := by
  simp only [verifyTail, posCheck, Code.allInstrs, saltBack_safe hH K, Bool.and_true]
  rfl

theorem verifyTail_xd {H : Hash} (K : Callees H) : (verifyTail H).x86_64Depth ≤ 8 := by
  simp only [verifyTail, posCheck, Code.x86_64Depth, saltBack_xd K]
  decide

theorem verifyTailD_safe {hs : List Hash} (ht : TierOk hs) : (dispatch sHsel verifyTail hs).allInstrs safeI = true :=
  dispatch_all test_safe rfl fun h hh => let ⟨⟨hH⟩, K⟩ := ht h hh; verifyTail_safe hH K

theorem verifyTailD_xd {hs : List Hash} (ht : TierOk hs) : (dispatch sHsel verifyTail hs).x86_64Depth ≤ 8 :=
  dispatch_xd fun h hh => verifyTail_xd (ht h hh).2

/-- `vmid_ok` up to `posScan`, with MGF1's hash function `hs[g]` and the
digest's length `D`. -/
theorem vmidA_ok {hs : List Hash} {g : Nat} (hg : g < hs.length) (hl : hs.length ≤ 2 ^ 31)
    (hG : HashOK hs[g]) (K : Callees hs[g]) {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x)
    (hGl : Gs.len = hs[g].D) (hGv : Proof.Mgf1.Valid Gs) {D : Nat} (hD0 : 0 < D) (hD64 : D ≤ 64)
    {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep u.mem F S V W) {k lo db z : Nat}
    (hk : W 17 = BitVec.ofNat 64 k) (he : W 23 = off S (oEm + lo)) (hdb : W 24 = BitVec.ofNat 64 db)
    (hc : W 25 = BitVec.setWidth 64 ((0xFF : Byte) >>> z)) (hlo : W 26 = BitVec.ofNat 64 lo)
    (h15 : W 15 = BitVec.ofNat 64 D) (h48 : W 48 = BitVec.ofNat 64 g)
    (hlo1 : lo ≤ 1) (hdb1 : 1 ≤ db) (hlay : lo + db + D + 1 = k) (hk2 : k ≤ 1024) :
    let hB := (List.range D).map fun i => V (oEm + lo + db + i)
    let dbL := Spec.RsaPss.clearTop z (Spec.Mgf1.xorBytes ((List.range db).map fun i => V (oEm + lo + i))
      (Spec.Mgf1.mgf1 Gs hB db))
    WP isa (seqs [.block acc0, mgfXorAny hs, .block clearTop, posScan]) u fun u' => Lay u' F S ∧
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ (∀ r ∈ [Reg.r13, .r14, .r15, .rsp], u'.gpr r = u.gpr r) ∧
      u'.gpr .rdx = (if lz dbL < db then BitVec.allOnes 64 else 0) ∧
      u'.gpr .rsi = BitVec.ofNat 64 (if lz dbL < db then lz dbL else 0) ∧
      u'.gpr .r11 = BitVec.setWidth 64 (if lz dbL < db then dbL.getD (lz dbL) 0 else 0) ∧
      ∃ V' W', Rep u'.mem F S V' W' ∧
        W' 33 = acc0V (V (oEm + k - 1)) (V oEm) (V (oEm + lo)) ((0xFF : Byte) >>> z) lo ∧
        (∀ j < nW, (j < 27 ∨ 32 < j) → j ≠ 33 → W' j = W j) ∧
        (∀ i < db, V' (oEm + lo + i) = dbL.getD i 0) ∧
        (∀ o < oRsa, ctOut o → ¬ (oEm + lo ≤ o ∧ o < oEm + lo + db) → V' o = V o) := by
  intro hB dbL
  have c1 : oEm = 2560 := rfl
  have c5 : oRsa = 8192 := rfl
  simp only [seqs]
  -- `acc0`.
  refine WP.seq (WP.mono (acc0_ok L R (c := (0xFF : Byte) >>> z) hk he hc hlo (by omega_arith) hk2 (by omega_arith))
    fun u1 ⟨L1, k1, R1⟩ => ?_)
  set a0 := acc0V (V (oEm + k - 1)) (V oEm) (V (oEm + lo)) ((0xFF : Byte) >>> z) lo
  have g1 : ∀ j, j ≠ 33 → upd W 33 a0 j = W j := fun j h => by simp [upd, h]
  -- The mask.
  refine WP.seq (WP.mono (mgfXorAny_ok hg hl hG K hGh hGl hGv L1 R1 (e := oEm + lo) (db := db) (D := D)
    ⟨by omega_arith, hdb1, by omega_arith⟩ hD0 hD64 (by rw [g1 23 (by decide), he]) (by rw [g1 24 (by decide), hdb])
    (by rw [g1 15 (by decide), h15]) (by rw [g1 48 (by decide), h48]))
    fun u2 ⟨L2, rd2, wr2, cs2, V2, W2, R2, hW2, hV2⟩ => ?_)
  -- The top bits.
  have h23 : W2 23 = off S (oEm + lo) := by rw [hW2 23 (by decide) (by omega_arith), g1 23 (by decide), he]
  have h25 : W2 25 = BitVec.setWidth 64 ((0xFF : Byte) >>> z) := by
    rw [hW2 25 (by decide) (by omega_arith), g1 25 (by decide), hc]
  refine WP.seq (WP.mono (clearTop_ok L2 R2 (e := oEm + lo) h23 h25 (by omega_arith)) fun u3 ⟨L3, k3, R3⟩ => ?_)
  set V3 := upd V2 (oEm + lo) (V2 (oEm + lo) &&& ((0xFF : Byte) >>> z))
  -- `DB`'s bytes.
  have hmk : (Spec.Mgf1.mgf1 Gs hB db).length = db := Proof.Mgf1.mgf1_length hGv _ _
  have hV3 : ∀ i < db, V3 (oEm + lo + i) = dbL.getD i 0 := fun i hi => by
    have hm : ∀ o < oRsa, ctOut o → V2 o = mixV V (Spec.Mgf1.mgf1 Gs hB db) (oEm + lo) db o := hV2
    have hco : ∀ j < db, ctOut (oEm + lo + j) := fun j hj => ⟨by unfold oLen; omega_arith, by unfold oY; omega_arith⟩
    have := db_bytes V (Spec.Mgf1.mgf1 Gs hB db) (e := oEm + lo) (z := z) hmk i hi
    rw [← this]
    simp only [V3, upd]
    by_cases h0 : i = 0
    · subst h0
      have hco0 : ctOut (oEm + lo) := ⟨by unfold oLen; omega_arith, by unfold oY; omega_arith⟩
      rw [Nat.add_zero, ifp rfl, ifp rfl, hm _ (by omega_arith) hco0]
    · rw [ifn (by omega_arith), ifn (by omega_arith), hm _ (by omega_arith) (hco i hi)]
  have hfnz : fnz (fun i => V3 (oEm + lo + i)) db = if lz dbL < db then some (lz dbL) else none := by
    rw [fnz_congr (g := fun i => dbL.getD i 0) fun i hi => hV3 i hi]
    exact fnz_lz dbL db (by simp only [dbL]; rw [clearTop_length, Proof.Mgf1.xorBytes_length]; simp [hmk])
  -- The first nonzero byte.
  have R3' : Rep u3.mem F S V3 W2 := R3
  have h24 : W2 24 = BitVec.ofNat 64 db := by rw [hW2 24 (by decide) (by omega_arith), g1 24 (by decide), hdb]
  refine WP.mono (posScan_ok L3 R3' h23 h24 hdb1 (by omega_arith))
    fun u4 ⟨k4, hm4, hdx4, hsi4, h114⟩ => ?_
  have L4 : Lay u4 F S := L3.congr (k4.gpr (by decide)) k4.2.2 (by rw [hm4])
  have R4 : Rep u4.mem F S V3 W2 := hm4 ▸ R3'
  rw [hfnz] at hdx4 hsi4 h114
  refine ⟨L4, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, _, _, R4, ?_, fun j hj hj' h33 => ?_, hV3,
    fun o ho hco hn => ?_⟩
  · rw [k4.2.1, k3.2.1, rd2, k1.2.1]
  · rw [k4.2.2, k3.2.2, wr2, k1.2.2]
  · rw [keep_cs k4 (by decide) r hr, keep_cs k3 (by decide) r hr, cs2 r hr, keep_cs k1 (by decide) r hr]
  · rw [hdx4]; by_cases hc : lz dbL < db <;> simp [hc]
  · rw [hsi4]; by_cases hc : lz dbL < db <;> simp [hc]
  · rw [h114]; by_cases hc : lz dbL < db <;> [simp [hc, hV3 _ hc]; simp [hc]]
  · rw [hW2 33 (by decide) (by omega_arith)]; simp [upd, a0]
  · rw [hW2 j hj hj', g1 j h33]
  · simp only [V3, upd]
    rw [ifn (by omega_arith), hV2 o ho hco]
    simp only [mixV]
    rw [ifn hn]

end VG.Proof.RsaPss.X86_64.Any
