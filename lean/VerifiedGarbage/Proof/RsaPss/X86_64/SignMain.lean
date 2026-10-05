import VerifiedGarbage.Proof.RsaPss.X86_64.Safe
import VerifiedGarbage.Proof.RsaPss.EncBytes

/-!
# RSASSA-PSS on x86-64: the encoding

After the checks, `signEnc` leaves `EM` (`k` bytes, `emT`) at
`scratch + oEm` (`signEnc_ok`), from the digest and the salt, which it
reads where nothing it writes is.
-/

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Bignum.X86_64 (off Scr off_off)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

/-- An address that no writable region of `wr` holds, nor the 8 bytes
below `F`. -/
def Outside (wr : List Region) (F a : Addr) : Prop :=
  (∀ r ∈ wr, ¬ r.Contains a 1) ∧ ¬ (below F 8).Contains a 1

/-- Bytes outside are not in our working space. -/
theorem Outside.ne {u : State} {F S : Addr} (L : Lay u F S) {a : Addr} (h : Outside u.wr F a) {x : Nat}
    (hx : x < oRsa) : a ≠ off S x := by
  intro he
  obtain ⟨r, hr, hc⟩ := L.sst8 (d := x) (by omega)
  exact h.1 r hr (he ▸ hc)

theorem chain {u v v' : State} {F : Addr} (hw : v.wr = u.wr) (hsp : v.gpr .rsp = F)
    (hS : ∀ a, Outside u.wr F a → v.mem a = u.mem a)
    (hk : ∀ a, (∀ r ∈ v.wr, ¬ r.Contains a 1) → ¬ (below (v.gpr .rsp) 8).Contains a 1 → v'.mem a = v.mem a) :
    ∀ a, Outside u.wr F a → v'.mem a = u.mem a :=
  fun a ha => (hk a (hw ▸ ha.1) (hsp ▸ ha.2)).trans (hS a ha)

/-- Safety of a piece of code, by unfolding it. -/
macro "safe_by " "[" ds:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp only [$ds,*, Code.allInstrs, rec_all, List.all_append, byteLoop, step, Bool.and_true, Bool.true_and]
  rfl))

/-- The bytes `n` at `p`, as a function. -/
def bytesF (m : Mem) (p : Addr) : Nat → Byte := fun i => m (p + BitVec.ofNat 64 i)

theorem getD_map_range (f : Nat → Byte) (n i : Nat) :
    ((List.range n).map f).getD i 0 = if i < n then f i else 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  split
  · rename_i h; rw [List.getElem?_range h]; rfl
  · rename_i h; rw [List.getElem?_eq_none (by simp; omega)]; rfl

variable {H : Hash} (hH : HashOK H) (K : Callees H)

include hH in
theorem validG {G : Spec.Mgf1.Hash} (hGh : ∀ x, G.hash x = hH.SH.H.hash x) (hGl : G.len = H.D) :
    Proof.Mgf1.Valid G := by
  refine ⟨hGl ▸ hH.hD0, fun x => ?_⟩
  rw [hGh, hH.hash, List.length_take, MdStream.Md.hash, hH.md.digest_length, hGl]
  exact Nat.min_eq_left hH.hDN

/-- `EM` from the bytes the blocks leave: `V5` (with `H` at `oDig`) cleared
over `EM`, `0x01` and the salt `sf`, `H` and `0xbc`, the mask XORed into
`DB` and its first byte ANDed with `c`. -/
theorem em_bytes {G : Spec.Mgf1.Hash} {V5 V9 sf : Nat → Byte} {k lo db sl D : Nat} {h saltB : List Byte}
    {c : Byte} (hdig : ∀ j < D, V5 (oDig + j) = h.getD j 0) (hh : h.length = D) (hsl : saltB.length = sl)
    (hsf : ∀ j < sl, sf j = saltB.getD j 0) (hk : k ≤ 1024) (hlo : lo ≤ 1) (hdb : lo + db + D + 1 = k)
    (hfit : sl + 1 ≤ db) (hD : 0 < D) (hDk : D ≤ 64)
    (h9 : ∀ o < oRsa, ctOut o →
      V9 o = mixV (upd (cpV (cpV (upd (clrV V5 oEm k) (oEm + lo + db - sl - 1) 1) sf (oEm + lo + db - sl - 1 + 1) sl)
        (fun i => cpV (upd (clrV V5 oEm k) (oEm + lo + db - sl - 1) 1) sf (oEm + lo + db - sl - 1 + 1) sl (oDig + i))
        (oEm + lo + db) D) (oEm + k - 1) 0xbc)
        (Spec.Mgf1.mgf1 G ((List.range D).map fun i => upd (cpV (cpV (upd (clrV V5 oEm k) (oEm + lo + db - sl - 1) 1)
          sf (oEm + lo + db - sl - 1 + 1) sl) (fun i => cpV (upd (clrV V5 oEm k) (oEm + lo + db - sl - 1) 1) sf
            (oEm + lo + db - sl - 1 + 1) sl (oDig + i)) (oEm + lo + db) D) (oEm + k - 1) 0xbc (oEm + lo + db + i)) db)
        (oEm + lo) db o) :
    ∀ i < k, upd V9 (oEm + lo) (V9 (oEm + lo) &&& c) (oEm + i) = RsaPss.emT lo db sl saltB h (Spec.Mgf1.mgf1 G h db) c i := by
  have c1 : oEm = 2560 := rfl
  have c3 : oDig = 2304 := rfl
  have c5 : oRsa = 8192 := rfl
  have c6 : oLen = 2368 := rfl
  have c7 : oY = 3584 := rfl
  -- `V7`: `EM` with `0x01` and the salt, and `H` at `oDig` still.
  have hV7 : ∀ x, cpV (upd (clrV V5 oEm k) (oEm + lo + db - sl - 1) 1) sf (oEm + lo + db - sl - 1 + 1) sl x =
      if oEm ≤ x ∧ x < oEm + k then
        (if oEm + lo + db - sl ≤ x ∧ x < oEm + lo + db then saltB.getD (x - (oEm + lo + db - sl)) 0
          else if x = oEm + lo + db - sl - 1 then 1 else 0)
      else V5 x := fun x => by
    simp only [cpV, upd, clrV]
    by_cases h1 : oEm + lo + db - sl - 1 + 1 ≤ x ∧ x < oEm + lo + db - sl - 1 + 1 + sl
    · rw [ifp h1, ifp (by omega), ifp (by omega), hsf _ (by omega), show x - (oEm + lo + db - sl - 1 + 1) =
        x - (oEm + lo + db - sl) by omega]
    · rw [ifn h1]
      by_cases h2 : x = oEm + lo + db - sl - 1
      · rw [ifp h2, ifp (by omega), ifn (by omega), ifp h2]
      · rw [ifn h2]
        by_cases h3 : oEm ≤ x ∧ x < oEm + k
        · rw [ifp h3, ifp h3, ifn (by omega), ifn h2]
        · rw [ifn h3, ifn h3]
  -- `H` after `DB`.
  have hHB : (List.range D).map (fun i => upd (cpV (cpV (upd (clrV V5 oEm k) (oEm + lo + db - sl - 1) 1) sf
      (oEm + lo + db - sl - 1 + 1) sl) (fun i => cpV (upd (clrV V5 oEm k) (oEm + lo + db - sl - 1) 1) sf
        (oEm + lo + db - sl - 1 + 1) sl (oDig + i)) (oEm + lo + db) D) (oEm + k - 1) 0xbc (oEm + lo + db + i)) = h := by
    rw [← List.take_of_length_le (Nat.le_of_eq hh), ← range_map_getD (Nat.le_of_eq hh.symm)]
    refine List.map_congr_left fun j hj => ?_
    have hj := List.mem_range.mp hj
    simp only [upd, cpV, clrV]
    rw [ifn (by omega), ifp (by omega), Nat.add_sub_cancel_left, ifn (by omega), ifn (by omega), ifn (by omega),
      hdig j hj]
  -- `V8`, over `EM`.
  have hV8 : ∀ x, oEm ≤ x → x < oEm + k → upd (cpV (cpV (upd (clrV V5 oEm k) (oEm + lo + db - sl - 1) 1) sf
      (oEm + lo + db - sl - 1 + 1) sl) (fun i => cpV (upd (clrV V5 oEm k) (oEm + lo + db - sl - 1) 1) sf
        (oEm + lo + db - sl - 1 + 1) sl (oDig + i)) (oEm + lo + db) D) (oEm + k - 1) 0xbc x =
      if x = oEm + k - 1 then 0xbc else if oEm + lo + db ≤ x then h.getD (x - (oEm + lo + db)) 0
      else if oEm + lo + db - sl ≤ x then saltB.getD (x - (oEm + lo + db - sl)) 0
      else if x = oEm + lo + db - sl - 1 then 1 else 0 := fun x h1 h2 => by
    simp only [upd]
    by_cases hx : x = oEm + k - 1
    · rw [ifp hx, ifp hx]
    rw [ifn hx, ifn hx]
    simp only [cpV]
    by_cases hy : oEm + lo + db ≤ x
    · rw [ifp (show oEm + lo + db ≤ x ∧ x < oEm + lo + db + D by omega), ifp hy, ifn (by omega)]
      simp only [upd, clrV]
      rw [ifn (by omega), ifn (by omega), hdig _ (by omega)]
    rw [ifn (show ¬(oEm + lo + db ≤ x ∧ x < oEm + lo + db + D) by omega), ifn hy]
    have := hV7 x
    simp only [cpV] at this
    rw [this, ifp (show oEm ≤ x ∧ x < oEm + k by omega)]
    by_cases hz : oEm + lo + db - sl ≤ x
    · rw [ifp (show oEm + lo + db - sl ≤ x ∧ x < oEm + lo + db by omega), ifp hz]
    · rw [ifn (show ¬(oEm + lo + db - sl ≤ x ∧ x < oEm + lo + db) by omega), ifn hz]
  intro i hi
  have hco : ctOut (oEm + i) := ⟨by omega, by omega⟩
  simp only [upd, RsaPss.emT]
  by_cases hz : i = lo
  · rw [hz] at hco hi ⊢
    rw [ifp rfl, h9 _ (by omega) hco, hHB, mixV, hV8 _ (by omega) (by omega)]
    simp (disch := omega) only [ifp, ifn, Nat.sub_self, ite_true]
    by_cases hdz : db - sl - 1 = 0
    · simp (disch := omega) only [ifp, ifn]
    · simp (disch := omega) only [ifp, ifn]
  · rw [ifn (show ¬ oEm + i = oEm + lo by omega), h9 _ (by omega) hco, hHB, mixV, hV8 _ (by omega) (by omega)]
    rw [hh]
    by_cases hl : i < lo
    · simp (disch := omega) only [ifp, ifn]
    by_cases hj : i - lo < db
    · rw [show oEm + i - (oEm + lo) = i - lo by omega]
      by_cases hs : db - sl ≤ i - lo
      · rw [show oEm + i - (oEm + lo + db - sl) = i - lo - (db - sl) by omega]
        simp (disch := omega) only [ifp, ifn]
      · by_cases ho : i - lo = db - sl - 1
        · simp (disch := omega) only [ifp, ifn]
        · simp (disch := omega) only [ifp, ifn]
    · by_cases hH : i - lo < db + D
      · rw [show oEm + i - (oEm + lo + db) = i - lo - db by omega]
        simp (disch := omega) only [ifp, ifn]
      · simp (disch := omega) only [ifp, ifn]

include K in
theorem signEnc_ok (lk : MgfLink H hH) {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep u.mem F S V W) {k lo sl : Nat} {c : Byte} {dig q : Addr}
    (hk : W 17 = BitVec.ofNat 64 k) (hlo : W 26 = BitVec.ofNat 64 lo) (hc : W 25 = BitVec.setWidth 64 c)
    (hdg : W 37 = dig) (hq : W 39 = q) (hsl : W 40 = BitVec.ofNat 64 sl)
    (hk1 : 64 ≤ k) (hk2 : k ≤ 1024) (hlo1 : lo ≤ 1) (hfit : H.D + sl + 2 ≤ k - lo)
    (hax : u.gpr .rax = BitVec.ofNat 64 (k - lo - (H.D + 2)))
    (hdR : ∀ i < H.D, InRegions (u.rd ++ u.wr) (dig + BitVec.ofNat 64 i) 1)
    (hdO : ∀ i < H.D, Outside u.wr F (dig + BitVec.ofNat 64 i))
    (hqR : ∀ i < sl, InRegions (u.rd ++ u.wr) (q + BitVec.ofNat 64 i) 1)
    (hqO : ∀ i < sl, Outside u.wr F (q + BitVec.ofNat 64 i)) :
    let db := k - lo - H.D - 1
    let saltB := (List.range sl).map (bytesF u.mem q)
    let h := lk.G.hash (Spec.RsaPss.zeros 8 ++ (List.range H.D).map (bytesF u.mem dig) ++ saltB)
    WP isa (signEnc H) u fun u' => Lay u' F S ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧
      (∀ r ∈ [Reg.r13, .r14, .r15, .rsp], u'.gpr r = u.gpr r) ∧
      ∃ V' W', Rep u'.mem F S V' W' ∧ (∀ j < nW, j < 23 ∨ 32 < j → W' j = W j) ∧
        ∀ i < k, V' (oEm + i) = RsaPss.emT lo db sl saltB h (Spec.Mgf1.mgf1 lk.G h db) c i := by
  intro db saltB h
  have hD := hH.hD0
  have hDN := hH.hDN
  have hN := hH.N_le
  have c1 : oEm = 2560 := rfl
  have c2 : oY = 3584 := rfl
  have c3 : oDig = 2304 := rfl
  have c5 : oRsa = 8192 := rfl
  have hdb : k - lo - (H.D + 2) + 1 = db := by omega
  rw [signEnc]
  simp only [seqs]
  -- `DB`'s slots.
  refine WP.seq (WP.mono (WP.keepIn (by safe_by [dbSlots]) (by exact Nat.zero_le 8)
    (dbSlots_ok L R hlo hax)) fun u1 ⟨⟨L1, k1, R1⟩, f1⟩ => ?_)
  have hS1 := chain (u := u) rfl L.rsp (fun _ _ => rfl) f1
  rw [hdb] at R1
  -- `Y` cleared.
  refine WP.seq (WP.mono (WP.keepIn (by safe_by [clearY]) (by exact Nat.zero_le 8)
    (clearY_ok L1 R1)) fun u2 ⟨⟨L2, k2, hcx2, R2⟩, f2⟩ => ?_)
  have hS2 := chain (u := u) k1.2.2 L1.rsp hS1 f2
  -- `mHash`.
  refine WP.seq (WP.mono (WP.keepIn (by safe_by [copyDigest]) (by exact Nat.zero_le 8)
    (copyDigest_ok hH L2 R2 (p := dig) (by simp [upd, hdg]) hcx2
      (fun i hi => by rw [k2.2.1, k2.2.2, k1.2.1, k1.2.2]; exact hdR i hi)
      (fun i hi j hj => Outside.ne L2 (by rw [k2.2.2, k1.2.2]; exact hdO i hi) (by omega))))
    fun u3 ⟨⟨L3, k3, R3⟩, f3⟩ => ?_)
  have hS3 := chain (u := u) (k2.2.2.trans k1.2.2) L2.rsp hS2 f3
  -- The salt.
  refine WP.seq (WP.mono (WP.keepIn (by safe_by [copySaltY]) (by exact Nat.zero_le 8)
    (copySaltY_ok hH L3 R3 (q := q) (sl := sl) (by simp [upd, hq]) (by simp [upd, hsl]) (by omega)
      ((k3.gpr (by decide)).trans hcx2)
      (fun i hi => by rw [k3.2.1, k3.2.2, k2.2.1, k2.2.2, k1.2.1, k1.2.2]; exact hqR i hi)
      (fun i hi j hj => Outside.ne L3 (by rw [k3.2.2, k2.2.2, k1.2.2]; exact hqO i hi) (by omega))))
    fun u4 ⟨⟨L4, k4, R4⟩, f4⟩ => ?_)
  have hS4 := chain (u := u) (k3.2.2.trans (k2.2.2.trans k1.2.2)) L3.rsp hS3 f4
  -- The length of `M'`.
  refine WP.seq (WP.mono (WP.keepIn (by safe_by [signLen]) (by exact Nat.zero_le 8)
    (signLen_ok hH L4 R4 (sl := sl) (by simp [upd, hsl]) (by omega))) fun u5 ⟨⟨L5, k5, R5⟩, f5⟩ => ?_)
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
      (by simp [upd, hml]) (by simp [upd]) (by rw [hml, Nat.succ_mul]; omega) (by rw [Nat.succ_mul]; omega)
      (fun i hi => ?_))) fun u6 ⟨⟨L6, rd6, wr6, cs6, V5, W3, R6, hout6, hW6, hdig6⟩, f6⟩ => ?_)
  · have hi' : i < 2048 := by rw [Nat.succ_mul] at hi; omega
    simp only [cpV, clrV, hmsg, getD_app, List.length_append, RsaPss.zeros_length, hdigB, saltB, List.length_map,
      List.length_range, getD_map_range, bytesF]
    by_cases h1 : i < 8
    · rw [ifn (show ¬(oY + (8 + H.D) ≤ oY + i ∧ oY + i < oY + (8 + H.D) + sl) by omega),
        ifn (show ¬(oY + 8 ≤ oY + i ∧ oY + i < oY + 8 + H.D) by omega),
        ifp (show oY ≤ oY + i ∧ oY + i < oY + 2048 by omega), ifp (show i < 8 + H.D by omega), ifp h1,
        RsaPss.zeros_getD]
    by_cases h2 : i < 8 + H.D
    · rw [ifn (show ¬(oY + (8 + H.D) ≤ oY + i ∧ oY + i < oY + (8 + H.D) + sl) by omega),
        ifp (show oY + 8 ≤ oY + i ∧ oY + i < oY + 8 + H.D by omega), ifp h2, ifn h1,
        ifp (show i - 8 < H.D by omega), show oY + i - (oY + 8) = i - 8 by omega]
      exact hS2 _ (hdO _ (by omega))
    by_cases h3 : i < 8 + H.D + sl
    · rw [ifp (show oY + (8 + H.D) ≤ oY + i ∧ oY + i < oY + (8 + H.D) + sl by omega), ifn h2,
        ifp (show i - (8 + H.D) < sl by omega), show oY + i - (oY + (8 + H.D)) = i - (8 + H.D) by omega]
      exact hS3 _ (hqO _ (by omega))
    · rw [ifn (show ¬(oY + (8 + H.D) ≤ oY + i ∧ oY + i < oY + (8 + H.D) + sl) by omega),
        ifn (show ¬(oY + 8 ≤ oY + i ∧ oY + i < oY + 8 + H.D) by omega),
        ifp (show oY ≤ oY + i ∧ oY + i < oY + 2048 by omega), ifn h2, ifn (show ¬ i - (8 + H.D) < sl by omega)]
  have hS6 := chain (u := u) (k5.2.2.trans (k4.2.2.trans (k3.2.2.trans (k2.2.2.trans k1.2.2)))) L5.rsp hS5 f6
  have wr6' : u6.wr = u.wr := wr6.trans (k5.2.2.trans (k4.2.2.trans (k3.2.2.trans (k2.2.2.trans k1.2.2))))
  have rd6' : u6.rd = u.rd := rd6.trans (k5.2.1.trans (k4.2.1.trans (k3.2.1.trans (k2.2.1.trans k1.2.1))))
  have hW3 : ∀ j < nW, j ≠ 23 → j ≠ 24 → j ≠ 27 → j ≠ 28 → j ≠ 29 → j ≠ 30 → W3 j = W j := fun j hj a b c d e f => by
    rw [hW6 j hj e f]; simp [upd, a, b, c, d]
  have hW3' : ∀ j, j < nW → (j < 23 ∨ j = 25 ∨ j = 26 ∨ 30 < j) → W3 j = W j := fun j hj hj' =>
    hW3 j hj (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have h23 : W3 23 = off S (oEm + lo) := by rw [hW6 23 (by decide) (by decide) (by decide)]; simp [upd]
  have h24 : W3 24 = BitVec.ofNat 64 db := by rw [hW6 24 (by decide) (by decide) (by decide)]; simp [upd]
  -- `EM` cleared.
  refine WP.seq (WP.mono (WP.keepIn (by decide) (by exact Nat.zero_le 8)
    (clearEm_ok L6 R6 (k := k) (by rw [hW3' 17 (by decide) (by decide)]; exact hk) (by omega) hk2)) fun u7 ⟨⟨L7, k7, R7⟩, f7⟩ => ?_)
  have hS7 := chain (u := u) wr6' L6.rsp hS6 f7
  -- `0x01` and the salt.
  refine WP.seq (WP.mono (putSalt_ok L7 R7 (e := oEm + lo) (db := db) (q := q) (sl := sl) h23 h24
    (by rw [hW3' 39 (by decide) (by decide)]; exact hq)
    (by rw [hW3' 40 (by decide) (by decide)]; exact hsl)
    (by omega) (by omega) (fun i hi => by rw [k7.2.1, k7.2.2, rd6', wr6']; exact hqR i hi)
    (fun i hi j hj => Outside.ne L7 (by rw [k7.2.2, wr6']; exact hqO i hi) (by omega)))
    fun u8 ⟨L8, k8, R8⟩ => ?_)
  -- `H` and `0xbc`.
  refine WP.seq (WP.mono (putH_ok hH L8 R8 (e := oEm + lo) (db := db) (k := k) h23 h24
    (by rw [hW3' 17 (by decide) (by decide)]; exact hk)
    (by omega) (by omega) hk2) fun u9 ⟨L9, k9, R9⟩ => ?_)
  -- The mask.
  refine WP.seq (WP.mono (mgfXor_ok hH K lk.hash lk.len (validG hH lk.hash lk.len) L9 R9 (e := oEm + lo) (db := db)
    ⟨by omega, by omega, by omega⟩ h23 h24) fun u10 ⟨L10, rd10, wr10, cs10, V9, W4, R10, hW10, hV10⟩ => ?_)
  -- The top bits.
  have h23' : W4 23 = off S (oEm + lo) := by rw [hW10 23 (by decide) (by omega), h23]
  have h25' : W4 25 = BitVec.setWidth 64 c := by rw [hW10 25 (by decide) (by omega), hW3' 25 (by decide) (by decide)]; exact hc
  refine WP.mono (clearTop_ok L10 R10 (e := oEm + lo) (c := c) h23' h25' (by omega)) fun u11 ⟨L11, k11, R11⟩ => ?_
  refine ⟨L11, by rw [k11.2.1, rd10, k9.2.1, k8.2.1, k7.2.1, rd6'], by rw [k11.2.2, wr10, k9.2.2, k8.2.2, k7.2.2, wr6'],
    fun r hr => ?_, _, _, R11, fun j hj h' => by rw [hW10 j hj (by omega), hW3' j hj (by omega)], fun i hi => ?_⟩
  · rw [keep_cs k11 (by decide) r hr, cs10 r hr, keep_cs k9 (by decide) r hr, keep_cs k8 (by decide) r hr,
      keep_cs k7 (by decide) r hr, cs6 r hr, keep_cs k5 (by decide) r hr, keep_cs k4 (by decide) r hr,
      keep_cs k3 (by decide) r hr, keep_cs k2 (by decide) r hr, keep_cs k1 (by decide) r hr]
  -- The digest `H`, at `scratch + oDig`.
  have hh : h.length = H.D := by rw [← lk.len]; exact (validG hH lk.hash lk.len).2 _
  have hdig : ∀ j < H.D, V5 (oDig + j) = h.getD j 0 := fun j hj => by
    rw [map_range_getD hdig6 hj, ← lk.hash]
  refine em_bytes (V5 := V5) (sf := fun j => u7.mem (q + BitVec.ofNat 64 j)) (saltB := saltB) hdig hh
    (by simp [saltB]) (fun j hj => ?_) hk2 hlo1 (by omega) (by omega) hD (by omega) hV10 i hi
  simp only [saltB, getD_map_range, ifp hj, bytesF]
  exact hS7 _ (hqO j hj)

end VG.Proof.RsaPss.X86_64
