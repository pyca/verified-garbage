module

public import VerifiedGarbage.Proof.RsaPss.X86_64.SignMain
public import VerifiedGarbage.Proof.RsaPss.X86_64.MgfAny
public import VerifiedGarbage.Proof.RsaPss.X86_64.AnySafe
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs

/-!
# RSASSA-PSS signing on x86-64 with the hash functions as arguments: the encoding

After the checks, `signEnc hs` leaves `EM` (`k` bytes, `emT`) at
`scratch + oEm` (`signEncAny_ok`), with the digest's hash function `H` the
one `hash` names (`hs[k]`, in `sHsel`) and MGF1's `G` the one `mgf1_hash`
names (`hs[g]`, in `sMsel`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Any

open VG VG.X86_64 VG.Impl.RsaPss.X86_64 VG.Impl.RsaPss.X86_64.AnyHash
open VG.Proof.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Bignum (off off_off)
open VG.Proof.Bignum.X86_64 (Scr)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

theorem signEncAny_ok {hs : List Hash} {kh g : Nat} (hkh : kh < hs.length) (hg : g < hs.length)
    (hl : hs.length ≤ 2 ^ 31)
    {H : Hash} (hkH : hs[kh] = H) (hH : HashOK H) (K : Callees H) (lk : MgfLink H hH)
    (hG : HashOK hs[g]) (KG : Callees hs[g]) (lkG : MgfLink hs[g] hG) {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep u.mem F S V W) {k lo sl : Nat} {c : Byte} {dig q : Addr}
    (hk : W 17 = BitVec.ofNat 64 k) (hlo : W 26 = BitVec.ofNat 64 lo) (hc : W 25 = BitVec.setWidth 64 c)
    (hdg : W 37 = dig) (hq : W 39 = q) (hsl : W 40 = BitVec.ofNat 64 sl)
    (h15 : W 15 = BitVec.ofNat 64 H.D) (h47 : W 47 = BitVec.ofNat 64 kh) (h48 : W 48 = BitVec.ofNat 64 g)
    (_hk1 : 64 ≤ k) (hk2 : k ≤ 1024) (hlo1 : lo ≤ 1) (hfit : H.D + sl + 2 ≤ k - lo)
    (hax : u.gpr .rax = BitVec.ofNat 64 (k - lo - (H.D + 2)))
    (hdR : ∀ i < H.D, InRegions (u.rd ++ u.wr) (dig + BitVec.ofNat 64 i) 1)
    (hdO : ∀ i < H.D, Outside u.wr F (dig + BitVec.ofNat 64 i))
    (hqR : ∀ i < sl, InRegions (u.rd ++ u.wr) (q + BitVec.ofNat 64 i) 1)
    (hqO : ∀ i < sl, Outside u.wr F (q + BitVec.ofNat 64 i)) :
    let db := k - lo - H.D - 1
    let saltB := (List.range sl).map (bytesF u.mem q)
    let h := lk.G.hash (Spec.RsaPss.zeros 8 ++ (List.range H.D).map (bytesF u.mem dig) ++ saltB)
    WP isa (AnyHash.signEnc hs) u fun u' => Lay u' F S ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧
      (∀ r ∈ [Reg.r13, .r14, .r15, .rsp], u'.gpr r = u.gpr r) ∧
      ∃ V' W', Rep u'.mem F S V' W' ∧ (∀ j < nW, j < 23 ∨ 32 < j → W' j = W j) ∧
        ∀ i < k, V' (oEm + i) = RsaPss.emT lo db sl saltB h (Spec.Mgf1.mgf1 lkG.G h db) c i := by
  intro db saltB h
  have hD := hH.hD0
  have hDN := hH.hDN
  have hN := hH.N_le
  have c1 : oEm = 2560 := rfl
  have c2 : oY = 3584 := rfl
  have c3 : oDig = 2304 := rfl
  have c5 : oRsa = 8192 := rfl
  have hdb : k - lo - (H.D + 2) + 1 = db := by omega_using [hfit]
  rw [AnyHash.signEnc]
  simp only [seqs]
  -- `DB`'s slots.
  refine WP.seq (WP.mono (WP.keepIn (by safe_by [dbSlots]) (by exact Nat.zero_le 8)
    (dbSlots_ok L R hlo hax)) fun u1 ⟨⟨L1, k1, R1⟩, f1⟩ => ?_)
  have hS1' := chain (u := u) rfl L.rsp (fun _ _ => rfl) f1
  rw [hdb] at R1
  -- The digest's hash function.
  refine WP.seq (dispatch_ok (j := 47) L1 R1 rfl (by decide) ((upd_ne _ (by decide)).trans ((upd_ne _ (by decide)).trans h47)) hl hkh
    fun v kv hmv _ => ?_)
  rw [hkH, signPre]
  simp only [seqs]
  have L1' : Lay v F S := L1.congr (kv.gpr (by decide)) kv.2.2 (by rw [hmv])
  have R1' := hmv ▸ R1
  have k1 := k1.trans kv
  have hS1 : ∀ a, Outside u.wr F a → v.mem a = u.mem a := fun a ha => (congrFun hmv a).trans (hS1' a ha)
  clear L1 R1
  have L1 := L1'
  have R1 := R1'
  -- `Y` cleared.
  refine WP.seq (WP.mono (WP.keepIn (by safe_by [clearY]) (by exact Nat.zero_le 8)
    (clearY_ok L1 R1)) fun u2 ⟨⟨L2, k2, hcx2, R2⟩, f2⟩ => ?_)
  have hS2 := chain (u := u) k1.2.2 L1.rsp hS1 f2
  -- `mHash`.
  refine WP.seq (WP.mono (WP.keepIn (by safe_by [copyDigest]) (by exact Nat.zero_le 8)
    (copyDigest_ok hH L2 R2 (p := dig) (by simp [upd, hdg]) hcx2
      (fun i hi => by rw [k2.2.1, k2.2.2, k1.2.1, k1.2.2]; exact hdR i hi)
      (fun i hi j hj => Outside.ne L2 (by rw [k2.2.2, k1.2.2]; exact hdO i hi) (by omega_using [hDN, hN, c2, c5, hj]))))
    fun u3 ⟨⟨L3, k3, R3⟩, f3⟩ => ?_)
  have hS3 := chain (u := u) (k2.2.2.trans k1.2.2) L2.rsp hS2 f3
  -- The salt.
  refine WP.seq (WP.mono (WP.keepIn (by safe_by [copySaltY]) (by exact Nat.zero_le 8)
    (copySaltY_ok hH L3 R3 (q := q) (sl := sl) (by simp [upd, hq]) (by simp [upd, hsl]) (by omega_using [hk2, hfit])
      ((k3.gpr (by decide)).trans hcx2)
      (fun i hi => by rw [k3.2.1, k3.2.2, k2.2.1, k2.2.2, k1.2.1, k1.2.2]; exact hqR i hi)
      (fun i hi j hj => Outside.ne L3 (by rw [k3.2.2, k2.2.2, k1.2.2]; exact hqO i hi) (by omega_using [hk2, hfit, c2, c5, hj]))))
    fun u4 ⟨⟨L4, k4, R4⟩, f4⟩ => ?_)
  have hS4 := chain (u := u) (k3.2.2.trans (k2.2.2.trans k1.2.2)) L3.rsp hS3 f4
  -- The length of `M'`.
  refine WP.seq (WP.mono (WP.keepIn (by safe_by [signLen]) (by exact Nat.zero_le 8)
    (signLen_ok hH L4 R4 (sl := sl) (by simp [upd, hsl]) (by omega_using [hk2, hfit]))) fun u5 ⟨⟨L5, k5, R5⟩, f5⟩ => ?_)
  have hS5 := chain (u := u) (k4.2.2.trans (k3.2.2.trans (k2.2.2.trans k1.2.2))) L4.rsp hS4 f5
  -- `H`.
  set digB := (List.range H.D).map (bytesF u.mem dig) with hdigB
  set msg := Spec.RsaPss.zeros 8 ++ digB ++ saltB with hmsg
  have hml : msg.length = 8 + H.D + sl := by
    simp only [hmsg, hdigB, saltB, List.length_append, RsaPss.zeros_length, List.length_map, List.length_range]
  have hB0 := hH.B_pos
  have hBl := hH.B_le
  have hL := hH.dims.L
  have hnb1 := Nat.lt_div_mul_add (a := 8 + H.D + sl + H.P.L) (b := H.P.B) hB0
  have hnb2 := Nat.div_mul_le_self (8 + H.D + sl + H.P.L) H.P.B
  refine WP.seq (WP.mono (WP.keepIn (ctHash_safe hH K) (by rw [ctHash_xd K])
    (ctHash_ok hH K L5 R5 (msg := msg) (nbm := (8 + H.D + sl + H.P.L) / H.P.B + 1)
      (by simp [upd, hml]) (by simp [upd]) (by rw [hml, Nat.succ_mul]; omega_using [hnb1])
          (by rw [Nat.succ_mul]; omega_using [hk2, hfit, hBl, hL, hnb2])
      (fun i hi => ?_))) fun u6 ⟨⟨L6, rd6, wr6, cs6, V5, W3, R6, hout6, hW6, hdig6⟩, f6⟩ => ?_)
  · have hi' : i < 2048 := by rw [Nat.succ_mul] at hi; omega_using [hk2, hfit, hBl, hL, hnb2, hi]
    simp only [cpV, clrV, hmsg, getD_app, List.length_append, RsaPss.zeros_length, hdigB, saltB, List.length_map,
      List.length_range, getD_map_range, bytesF]
    by_cases h1 : i < 8
    · rw [ifn (show ¬(oY + (8 + H.D) ≤ oY + i ∧ oY + i < oY + (8 + H.D) + sl) by omega_using [h1]),
        ifn (show ¬(oY + 8 ≤ oY + i ∧ oY + i < oY + 8 + H.D) by omega_using [h1]),
        ifp (show oY ≤ oY + i ∧ oY + i < oY + 2048 by omega_using [h1]), ifp (show i < 8 + H.D by omega_using [h1]), ifp h1,
        RsaPss.zeros_getD]
    by_cases h2 : i < 8 + H.D
    · rw [ifn (show ¬(oY + (8 + H.D) ≤ oY + i ∧ oY + i < oY + (8 + H.D) + sl) by omega_using [h2]),
        ifp (show oY + 8 ≤ oY + i ∧ oY + i < oY + 8 + H.D by omega_using [h1, h2]), ifp h2, ifn h1,
        ifp (show i - 8 < H.D by omega_using [h1, h2]), show oY + i - (oY + 8) = i - 8 by omega_using []]
      exact hS2 _ (hdO _ (by omega_using [h1, h2]))
    by_cases h3 : i < 8 + H.D + sl
    · rw [ifp (show oY + (8 + H.D) ≤ oY + i ∧ oY + i < oY + (8 + H.D) + sl by omega_using [h2, h3]), ifn h2,
        ifp (show i - (8 + H.D) < sl by omega_using [h2, h3]), show oY + i - (oY + (8 + H.D)) = i - (8 + H.D) by omega_using []]
      exact hS3 _ (hqO _ (by omega_using [h2, h3]))
    · rw [ifn (show ¬(oY + (8 + H.D) ≤ oY + i ∧ oY + i < oY + (8 + H.D) + sl) by omega_using [h3]),
        ifn (show ¬(oY + 8 ≤ oY + i ∧ oY + i < oY + 8 + H.D) by omega_using [h3]),
        ifp (show oY ≤ oY + i ∧ oY + i < oY + 2048 by omega_using [hi']), ifn h2, ifn (show ¬ i - (8 + H.D) < sl by omega_using [h3])]
  have hS6 := chain (u := u) (k5.2.2.trans (k4.2.2.trans (k3.2.2.trans (k2.2.2.trans k1.2.2)))) L5.rsp hS5 f6
  have wr6' : u6.wr = u.wr := wr6.trans (k5.2.2.trans (k4.2.2.trans (k3.2.2.trans (k2.2.2.trans k1.2.2))))
  have rd6' : u6.rd = u.rd := rd6.trans (k5.2.1.trans (k4.2.1.trans (k3.2.1.trans (k2.2.1.trans k1.2.1))))
  have hW3 : ∀ j < nW, j ≠ 23 → j ≠ 24 → j ≠ 27 → j ≠ 28 → j ≠ 29 → j ≠ 30 → W3 j = W j := fun j hj a b c d e f => by
    rw [hW6 j hj e f]; simp [upd, a, b, c, d]
  have hW3' : ∀ j, j < nW → (j < 23 ∨ j = 25 ∨ j = 26 ∨ 30 < j) → W3 j = W j := fun j hj hj' =>
    hW3 j hj (by omega_using [hj']) (by omega_using [hj']) (by omega_using [hj']) (by omega_using [hj'])
        (by omega_using [hj']) (by omega_using [hj'])
  have h23 : W3 23 = off S (oEm + lo) := by rw [hW6 23 (by decide) (by decide) (by decide)]; simp [upd]
  have h24 : W3 24 = BitVec.ofNat 64 db := by rw [hW6 24 (by decide) (by decide) (by decide)]; simp [upd]
  -- `EM` cleared.
  refine WP.seq (WP.mono (WP.keepIn (by decide) (by exact Nat.zero_le 8)
    (clearEm_ok L6 R6 (k := k) (by rw [hW3' 17 (by decide) (by decide)]; exact hk) (by omega_using [hdb]) hk2))
    fun u7 ⟨⟨L7, k7, R7⟩, f7⟩ => ?_)
  have hS7 := chain (u := u) wr6' L6.rsp hS6 f7
  -- `0x01` and the salt.
  refine WP.seq (WP.mono (putSalt_ok L7 R7 (e := oEm + lo) (db := db) (q := q) (sl := sl) h23 h24
    (by rw [hW3' 39 (by decide) (by decide)]; exact hq)
    (by rw [hW3' 40 (by decide) (by decide)]; exact hsl)
    (by omega_using [hfit]) (by omega_using [hk2, c1, c5, hdb]) (fun i hi => by rw [k7.2.1, k7.2.2, rd6', wr6']; exact hqR i hi)
    (fun i hi j hj => Outside.ne L7 (by rw [k7.2.2, wr6']; exact hqO i hi) (by omega_using [hk2, hfit, c1, c5, hj])))
    fun u8 ⟨L8, k8, R8⟩ => ?_)
  -- `H` and `0xbc`.
  refine WP.mono (putH_ok hH L8 R8 (e := oEm + lo) (db := db) (k := k) h23 h24
    (by rw [hW3' 17 (by decide) (by decide)]; exact hk)
    (by omega_using []) (by omega_using [hdb]) hk2) fun u9 ⟨L9, k9, R9⟩ => ?_
  -- The mask.
  have hW15 : W3 15 = BitVec.ofNat 64 H.D := by rw [hW3' 15 (by decide) (by decide)]; exact h15
  have hW48 : W3 48 = BitVec.ofNat 64 g := by rw [hW3' 48 (by decide) (by decide)]; exact h48
  refine WP.seq (WP.mono (mgfXorAny_ok hg hl hG KG lkG.hash lkG.len (validG hG lkG.hash lkG.len) L9 R9
    (e := oEm + lo) (db := db) (D := H.D)
    ⟨by omega_using [], by omega_using [hdb], by omega_using [hk2, hdb]⟩ hD (by omega_using [hDN, hN]) h23 h24
    hW15 hW48) fun u10 ⟨L10, rd10, wr10, cs10, V9,
        W4, R10, hW10, hV10⟩ => ?_)
  -- The top bits.
  have h23' : W4 23 = off S (oEm + lo) := by rw [hW10 23 (by decide) (by omega_using []), h23]
  have h25' : W4 25 = BitVec.setWidth 64 c := by rw [hW10 25 (by decide) (by omega_using []), hW3' 25 (by decide) (by decide)]; exact hc
  refine WP.mono (clearTop_ok L10 R10 (e := oEm + lo) (c := c) h23' h25' (by omega_using [hlo1, c1, c5])) fun u11 ⟨L11, k11, R11⟩ => ?_
  refine ⟨L11, by rw [k11.2.1, rd10, k9.2.1, k8.2.1, k7.2.1, rd6'], by rw [k11.2.2, wr10, k9.2.2, k8.2.2, k7.2.2, wr6'],
    fun r hr => ?_, _, _, R11, fun j hj h' => by rw [hW10 j hj (by omega_using [h']), hW3' j hj (by omega_using [h'])], fun i hi => ?_⟩
  · rw [keep_cs k11 (by decide) r hr, cs10 r hr, keep_cs k9 (by decide) r hr, keep_cs k8 (by decide) r hr,
      keep_cs k7 (by decide) r hr, cs6 r hr, keep_cs k5 (by decide) r hr, keep_cs k4 (by decide) r hr,
      keep_cs k3 (by decide) r hr, keep_cs k2 (by decide) r hr, keep_cs k1 (by decide) r hr]
  -- The digest `H`, at `scratch + oDig`.
  have hh : h.length = H.D := by rw [← lk.len]; exact (validG hH lk.hash lk.len).2 _
  have hdig : ∀ j < H.D, V5 (oDig + j) = h.getD j 0 := fun j hj => by
    rw [map_range_getD hdig6 hj, ← lk.hash]
  refine em_bytes (V5 := V5) (sf := fun j => u7.mem (q + BitVec.ofNat 64 j)) (saltB := saltB) hdig hh
    (by simp [saltB]) (fun j hj => ?_) hk2 hlo1 (by omega_using [hdb]) (by omega_using [hfit]) hD (by omega_using [hDN, hN]) hV10 i hi
  simp only [saltB, getD_map_range, ifp hj, bytesF]
  exact hS7 _ (hqO j hj)

end VG.Proof.RsaPss.X86_64.Any
