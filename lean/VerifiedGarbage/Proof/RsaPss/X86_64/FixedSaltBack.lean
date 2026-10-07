import VerifiedGarbage.Proof.RsaPss.X86_64.FixedSaltCopy
import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyMain

/-! Verification's fixed-length salt input, built without a masked shift. -/
namespace VG.Proof.RsaPss.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep ifp ifn)

variable {H : Impl.Pbkdf2.Md.X86_64.Hash} (hH : Pbkdf2.Md.X86_64.HashOK H)
  (K : Pbkdf2.Md.X86_64.Callees H)

include hH K in
theorem fixedSaltBack_ok (lk : Pbkdf2.Md.X86_64.MgfLink H hH)
    {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {lo db sl : Nat} {dig : Addr}
    (he : W 23 = off S (oEm + lo)) (hdb : W 24 = BitVec.ofNat 64 db)
    (hsl : W 36 = BitVec.ofNat 64 sl) (hdg : W 37 = dig)
    (hlo : lo ≤ 1) (hslFit : sl < db) (hfit : lo + db + H.D + 1 ≤ 1024)
    (hdR : ∀ i < H.D, InRegions (u.rd ++ u.wr) (dig + BitVec.ofNat 64 i) 1)
    (hdO : ∀ i < H.D, Outside u.wr F (dig + BitVec.ofNat 64 i)) :
    let msg := Spec.RsaPss.zeros 8 ++ (List.range H.D).map (bytesF u.mem dig) ++
      (List.range sl).map (fun i => V (oEm + lo + db - sl + i))
    WP isa (fixedSaltBack H) u fun u' =>
      Lay u' F S ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧
      (∀ r ∈ [Reg.r13, .r14, .r15, .rsp], u'.gpr r = u.gpr r) ∧
      (∃ V' W', Rep u'.mem F S V' W' ∧
        ∀ j < nW, j ≠ 27 → j ≠ 28 → j ≠ 29 → j ≠ 30 → W' j = W j) ∧
      u'.gpr .rax = if W 33 = 0 ∧ ∀ i < H.D,
        (lk.G.hash msg).getD i 0 = V (oEm + lo + db + i) then 1 else 0 := by
  intro msg
  have hD := hH.hD0
  have hDN := hH.hDN
  have hN := hH.N_le
  have c1 : oEm = 2560 := rfl
  have c2 : oY = 3584 := rfl
  have c3 : oDig = 2304 := rfl
  have c5 : oRsa = 8192 := rfl
  unfold fixedSaltBack fixedSaltPrefix seqs seqs seqs
  apply WP.assoc'
  refine WP.seq (WP.mono (WP.keepIn (by safe_by [clearY]) (by exact Nat.zero_le 8)
    (clearY_ok L R)) fun u1 ⟨⟨L1, k1, hcx1, R1⟩, f1⟩ => ?_)
  have hS1 := chain (u := u) rfl L.rsp (fun _ _ => rfl) f1
  apply WP.assoc'
  refine WP.seq (WP.mono (copyDigest_ok hH L1 R1 (p := dig) hdg hcx1
    (fun i hi => by rw [k1.2.1, k1.2.2]; exact hdR i hi)
    (fun i hi j hj => Outside.ne L1 (by rw [k1.2.2]; exact hdO i hi) (by omega)))
    fun u2 ⟨L2, k2, R2⟩ => ?_)
  have salt_src : ∀ i < sl, u2.mem (off S (oEm + lo + db - sl + i)) =
      V (oEm + lo + db - sl + i) := by
    intro i hi
    rw [R2.scr _ (by omega)]
    simp only [cpV, clrV]
    rw [ifn (by omega), ifn (by omega)]
  apply WP.assoc'
  refine WP.seq (WP.mono (copyFixedSalt_ok hH L2 R2 he hdb hsl hslFit (by omega) (by omega)
    ((k2.gpr (by decide)).trans hcx1)) fun u3 ⟨L3, k3, R3⟩ => ?_)
  refine WP.seq (WP.mono (hashSaltLen_ok hH L3 R3 (k := 36) (by decide) hsl (by omega))
    fun u4 ⟨L4, k4, R4⟩ => ?_)
  have hml : msg.length = 8 + H.D + sl := by
    simp only [msg, List.length_append, RsaPss.zeros_length, List.length_map, List.length_range]
  have hB0 := hH.B_pos
  have hBl := hH.B_le
  have hL := hH.dims.L
  have hnb1 := Nat.lt_div_mul_add (a := 8 + H.D + sl + H.P.L) (b := H.P.B) hB0
  have hnb2 := Nat.div_mul_le_self (8 + H.D + sl + H.P.L) H.P.B
  refine WP.seq (WP.mono (ctHash_ok hH K L4 R4 (msg := msg)
    (nbm := (8 + H.D + sl + H.P.L) / H.P.B + 1)
    (by simp [upd, hml]) (by simp [upd]) (by rw [hml, Nat.succ_mul]; omega)
    (by rw [Nat.succ_mul]; omega) (fun i hi => ?_))
    fun u5 ⟨L5, rd5, wr5, cs5, V5, W5, R5, hout5, hW5, hdig5⟩ => ?_)
  · have hi' : i < 2048 := by rw [Nat.succ_mul] at hi; omega
    simp only [cpV, clrV, msg, getD_app, List.length_append, RsaPss.zeros_length,
      List.length_map, List.length_range, getD_map_range, bytesF]
    by_cases h1 : i < 8
    · rw [ifn (show ¬(oY + (8 + H.D) ≤ oY + i ∧ oY + i < oY + (8 + H.D) + sl) by omega),
        ifn (show ¬(oY + 8 ≤ oY + i ∧ oY + i < oY + 8 + H.D) by omega),
        ifp (show oY ≤ oY + i ∧ oY + i < oY + 2048 by omega), ifp (show i < 8 + H.D by omega), ifp h1,
        RsaPss.zeros_getD]
    by_cases h2 : i < 8 + H.D
    · rw [ifn (show ¬(oY + (8 + H.D) ≤ oY + i ∧ oY + i < oY + (8 + H.D) + sl) by omega),
        ifp (show oY + 8 ≤ oY + i ∧ oY + i < oY + 8 + H.D by omega), ifp h2, ifn h1,
        ifp (show i - 8 < H.D by omega), show oY + i - (oY + 8) = i - 8 by omega]
      exact hS1 _ (hdO _ (by omega))
    by_cases h3 : i < 8 + H.D + sl
    · rw [ifp (show oY + (8 + H.D) ≤ oY + i ∧ oY + i < oY + (8 + H.D) + sl by omega), ifn h2,
        ifp (show i - (8 + H.D) < sl by omega), show oY + i - (oY + (8 + H.D)) = i - (8 + H.D) by omega]
      exact salt_src _ (by omega)
    · rw [ifn (show ¬(oY + (8 + H.D) ≤ oY + i ∧ oY + i < oY + (8 + H.D) + sl) by omega),
        ifn (show ¬(oY + 8 ≤ oY + i ∧ oY + i < oY + 8 + H.D) by omega),
        ifp (show oY ≤ oY + i ∧ oY + i < oY + 2048 by omega), ifn h2,
        ifn (show ¬ i - (8 + H.D) < sl by omega)]
  have h23 : W5 23 = off S (oEm + lo) := by
    rw [hW5 23 (by decide) (by decide) (by decide)]; simp [upd, he]
  have h24 : W5 24 = BitVec.ofNat 64 db := by
    rw [hW5 24 (by decide) (by decide) (by decide)]; simp [upd, hdb]
  refine WP.mono (cmpH_ok hH L5 R5 h23 h24 (by omega)) fun u6 ⟨k6, hm6, hax6⟩ => ?_
  have L6 : Lay u6 F S := L5.congr (k6.gpr (by decide)) k6.2.2 (by rw [hm6])
  refine ⟨L6, k6.2.1.trans (rd5.trans (k4.2.1.trans (k3.2.1.trans (k2.2.1.trans k1.2.1)))),
    k6.2.2.trans (wr5.trans (k4.2.2.trans (k3.2.2.trans (k2.2.2.trans k1.2.2)))),
    fun r hr => ?_, ⟨V5, W5, hm6 ▸ R5, fun j hj a b c d => ?_⟩, ?_⟩
  · rw [keep_cs k6 (by decide) r hr, cs5 r hr, keep_cs k4 (by decide) r hr,
      keep_cs k3 (by decide) r hr, keep_cs k2 (by decide) r hr, keep_cs k1 (by decide) r hr]
  · rw [hW5 j hj c d]; simp [upd, a, b]
  · rw [hax6]
    have h33 : W5 33 = W 33 := by
      rw [hW5 33 (by decide) (by decide) (by decide)]; simp [upd]
    have hH' : ∀ i < H.D, V5 (oDig + i) = (lk.G.hash msg).getD i 0 := fun i hi => by
      rw [map_range_getD hdig5 hi, ← lk.hash]
    have hE : ∀ i < H.D, V5 (oEm + lo + db + i) = V (oEm + lo + db + i) := fun i hi => by
      rw [hout5 _ (by omega) ⟨by unfold oLen; omega, by omega⟩]
      simp only [cpV, clrV]
      rw [ifn (by omega), ifn (by omega), ifn (by omega)]
    rw [h33]
    congr 1
    apply propext
    exact and_congr_right fun _ => forall_congr' fun i => imp_congr_right fun hi => by rw [hH' i hi, hE i hi]

end VG.Proof.RsaPss.X86_64
