module

public import VerifiedGarbage.Proof.RsaPss.X86_64.MgfHashAny
public import VerifiedGarbage.Proof.RsaPss.X86_64.AnyDispatch
public import VerifiedGarbage.Proof.RsaPss.X86_64.Mgf
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSASSA-PSS on x86-64 with the hash functions as arguments: MGF1

`mgfXorAny hs` XORs `MGF1(G, H, dbLen)` into `DB`, the `dbLen` bytes at
`scratch + e`, where `H` is the `D` bytes after them (`D` in the slot
`sHd`) and `G` the hash function of `hs` that the slot `sMsel` names
(`mgfXorAny_ok`): for each counter `c`, `H ‖ I2OSP(c, 4)` is written to `Y`
(`clearSeedBlocks`, `copySeed`, `counterAny`), and `G`'s code, chosen by the
dispatch, hashes it (`mgfHashAny`) and XORs the first
`min(gLen, dbLen - c gLen)` bytes of its digest into `DB` at `c gLen`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Any

open VG VG.X86_64 VG.Impl.RsaPss.X86_64 VG.Impl.RsaPss.X86_64.AnyHash
open VG.Proof.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Bignum (off off_off)
open VG.Proof.Bignum.X86_64 (Scr ofNat_add_one ofNat_sub_beq wp_upto)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.RsaPss (i2osp_len mgf1_getD)

/-! ## `H ‖ C` in `Y` -/

theorem clearSeedBlocks_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) :
    WP isa clearSeedBlocks u fun u' => Lay u' F S ∧ Keep [.rcx, .rax, .r8] u u' ∧ u'.gpr .rcx = off S oY ∧
      Rep u'.mem F S (clrV V oY 256) W := by
  refine WP.seq (WP.mono (WP.keep [.rcx, .rax, .r8] (Q := fun v => v.gpr .rcx = off S oY ∧ v.gpr .rax = 0 ∧
      v.gpr .r8 = BitVec.ofNat 64 0 ∧ v.mem = u.mem) ?_ rfl) fun v ⟨⟨h₁, h₂, h₃, hm⟩, hk⟩ => ?_)
  · have hs := L.slot
    simp only [Bignum.word] at hs
    xrun [scr, List.cons_append, List.nil_append, ea_sp, L.rsp, L.ld (d := sScr) (by decide), hs,
      VG.Proof.MlKem.X86_64.sx_ofNat (show oY < 2 ^ 31 by decide)]
  have Lv : Lay v F S := L.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm])
  refine WP.mono (clearQ_ok Lv (hm ▸ R) (n := 256) (by decide) (by decide) (by decide) (by decide) h₁ h₂ h₃)
    fun w ⟨Lw, kw, Rw⟩ => ⟨Lw, (hk.trans kw).mono (by decide), (kw.gpr (by decide)).trans h₁, Rw⟩

theorem copySeed_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {D e db : Nat} (hd : DbAt D e db) (he : W 23 = off S e)
    (hdb : W 24 = BitVec.ofNat 64 db) (hD : W 15 = BitVec.ofNat 64 D) (hD0 : 0 < D)
    (hcx : u.gpr .rcx = off S oY) :
    WP isa copySeed u fun u' => Lay u' F S ∧ Keep [.rsi, .r8, .r10, .rax] u u' ∧
      Rep u'.mem F S (cpV V (fun i => V (e + db + i)) oY D) W := by
  have hfit := hd.fit
  have c1 : oEm = 2560 := rfl
  have c2 : oY = 3584 := rfl
  have h23 : u.mem.readW (off F sEb) 64 = off S e := by rw [← he, ← R.fr 23 (by decide)]; rfl
  have h24 : u.mem.readW (off F sDb) 64 = BitVec.ofNat 64 db := by rw [← hdb, ← R.fr 24 (by decide)]; rfl
  have h15 : u.mem.readW (off F sHd) 64 = BitVec.ofNat 64 D := by rw [← hD, ← R.fr 15 (by decide)]; rfl
  refine WP.seq (WP.mono (WP.keep [.rsi, .r8, .r10] (Q := fun v => v.gpr .rsi = off S (e + db) ∧
      v.gpr .r10 = BitVec.ofNat 64 D ∧ v.gpr .r8 = BitVec.ofNat 64 0 ∧ v.mem = u.mem) ?_ rfl)
    fun v ⟨⟨h₁, h₁₀, h₂, hm⟩, hk⟩ => ?_)
  · xrun [copySeed, ea_sp, L.rsp, L.ld (d := sEb) (by decide), L.ld (d := sDb) (by decide),
      L.ld (d := sHd) (by decide), h23, h24, h15]
    exact off_off S e db
  have Lv : Lay v F S := L.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm])
  have Rv : Rep v.mem F S V W := hm ▸ R
  have hcp := copy_ok Lv Rv (d := .rcx) (by decide) (p := off S (e + db)) (o := oY) (disp := 0) (n := D)
    (stepR_ok (show D < 2 ^ 63 by omega_using [hfit, c1]) v (rs := [.rax, .r8]) (r := .r10) (by decide) (by decide) h₁₀)
    hD0 (by unfold oRsa; omega_using [hfit, c1, c2]) h₁ ((hk.gpr (by decide)).trans hcx) h₂
    (fun i hi => by rw [off_plus]; exact Lv.sld8 (by unfold oRsa; omega_using [hfit, c1, hi]))
    (fun i hi j hj => by
      rw [off_plus]; exact Offset.add_ofNat_ne S (by omega_using [hfit, c1, hi]) (by omega_using [hfit, c1, c2, hj])
          (by omega_using [hfit, c1, c2, hi]))
  refine WP.mono hcp fun w ⟨Lw, kw, Rw⟩ => ⟨Lw, (hk.trans kw).mono (by decide), ?_⟩
  refine (congrArg (fun V' => Rep w.mem F S V' W) (funext fun x => ?_)).mp Rw
  simp only [cpV, Nat.add_zero]
  split
  · rw [off_plus, Rv.scr _ (by unfold oRsa; omega_arith)]
  · rfl

theorem counterAny_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {c D : Nat} (hc : W 31 = BitVec.ofNat 64 c) (hc32 : c < 2 ^ 32)
    (hD : W 15 = BitVec.ofNat 64 D) (hD64 : D ≤ 64) (hcx : u.gpr .rcx = off S oY) :
    WP isa (.block counterAny) u fun u' => Lay u' F S ∧ Keep [.r9, .rdi, .rax] u u' ∧
      Rep u'.mem F S (ctrV D V c) (upd (upd W 27 (BitVec.ofNat 64 (D + 4))) 28 (BitVec.ofNat 64 2)) := by
  have h31 : u.mem.readW (off F sCtr) 64 = BitVec.ofNat 64 c := by rw [← hc, ← R.fr 31 (by decide)]; rfl
  have h15 : u.mem.readW (off F sHd) 64 = BitVec.ofNat 64 D := by rw [← hD, ← R.fr 15 (by decide)]; rfl
  have G := L.geo
  -- The bytes, most significant first.
  have R1 := (((R.wb G (o := oY + D + 3) (by unfold oY oRsa; omega_arith) (BitVec.ofNat 8 c)).wb G
    (o := oY + D + 2) (by unfold oY oRsa; omega_arith) (BitVec.ofNat 8 (c / 2 ^ 8))).wb G
    (o := oY + D + 1) (by unfold oY oRsa; omega_arith) (BitVec.ofNat 8 (c / 2 ^ 8 / 2 ^ 8))).wb G
    (o := oY + D) (by unfold oY oRsa; omega_arith) (BitVec.ofNat 8 (c / 2 ^ 8 / 2 ^ 8 / 2 ^ 8))
  have R2 := (R1.wf G (k := 27) (by decide) (BitVec.ofNat 64 (D + 4))).wf G (k := 28) (by decide)
    (BitVec.ofNat 64 2)
  rw [show off F (8 * 27) = off F sL from rfl, show off F (8 * 28) = off F sNb from rfl] at R2
  refine WP.mono (WP.keep [.r9, .rdi, .rax] (Q := fun u' => u'.mem =
      (((((u.mem.writeW (off S (oY + D + 3)) (BitVec.ofNat 8 c)).writeW (off S (oY + D + 2))
        (BitVec.ofNat 8 (c / 2 ^ 8))).writeW (off S (oY + D + 1)) (BitVec.ofNat 8 (c / 2 ^ 8 / 2 ^ 8))).writeW
        (off S (oY + D)) (BitVec.ofNat 8 (c / 2 ^ 8 / 2 ^ 8 / 2 ^ 8))).writeW (off F sL)
        (BitVec.ofNat 64 (D + 4))).writeW (off F sNb) (BitVec.ofNat 64 2)) ?_ rfl)
    fun u' ⟨hm, hk⟩ => ⟨?_, hk, hm ▸ ?_⟩
  · xrun [counterAny, ea_at, ea_at0, ea_sp, hcx, L.rsp, L.ld (d := sCtr) (by decide), L.ld (d := sHd) (by decide),
      h31, h15, off_off, off_plus,
      L.sst8 (d := oY + D + 3) (by unfold oY oRsa; omega_arith), L.sst8 (d := oY + D + 2) (by unfold oY oRsa; omega_arith),
      L.sst8 (d := oY + D + 1) (by unfold oY oRsa; omega_arith), L.sst8 (d := oY + D) (by unfold oY oRsa; omega_arith),
      L.st (d := sL) (by decide), L.st (d := sNb) (by decide), trunc_ofNat,
      shr_ofNat 8 (show c < 2 ^ 64 by omega_using [hc32]), shr_ofNat 8 (show c / 2 ^ 8 < 2 ^ 64 by omega_using [hc32]),
      shr_ofNat 8 (show c / 2 ^ 8 / 2 ^ 8 < 2 ^ 64 by omega_using [hc32]), ofNat_add_lit,
      VG.Proof.MlKem.X86_64.sx_ofNat (show 4 < 2 ^ 31 by decide), show BitVec.setWidth 64 (2 : BitVec 32) = 2#64 from rfl]
  · refine L.congr (hk.gpr (by decide)) hk.2.2 ?_
    have h1 := R2.fr 21 (by decide)
    rw [← hm] at h1
    rw [slot_eq sScr 21 rfl, slot_eq sScr 21 rfl, h1, R.fr 21 (by decide)]
    simp [upd]
  · refine (congrArg (fun V' => Rep _ F S V' _) (funext fun x => ?_)).mp R2
    have e1 : c / 2 ^ 8 / 2 ^ 8 / 2 ^ 8 = c / 256 ^ 3 := by
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
    have e2 : c / 2 ^ 8 / 2 ^ 8 = c / 256 ^ 2 := by rw [Nat.div_div_eq_div_mul]
    simp only [upd, ctrV, Spec.Rsa.i2osp, List.getD_eq_getElem?_getD, List.getElem?_map]
    rcases (show x = oY + D ∨ x = oY + D + 1 ∨ x = oY + D + 2 ∨ x = oY + D + 3 ∨
        ¬(oY + D ≤ x ∧ x < oY + D + 4) by omega_using []) with h | h | h | h | h
    · subst h; simp [e1]
    · subst h
      simp [e2, show oY + D + 1 - (oY + D) = 1 by omega_using [], show oY + D + 1 < oY + D + 4 by omega_using []]
    · subst h
      simp [show oY + D + 2 - (oY + D) = 2 by omega_using [], show oY + D + 2 < oY + D + 4 by omega_using []]
    · subst h
      simp [show oY + D + 3 - (oY + D) = 3 by omega_using [], show oY + D + 3 < oY + D + 4 by omega_using []]
    · rw [ifn h, ifn (by omega_using [h]), ifn (by omega_using [h]), ifn (by omega_using [h]), ifn (by omega_using [h])]

/-! ## One counter -/

section
variable {hs : List Hash} {g : Nat} (hg : g < hs.length) (hG : HashOK hs[g]) (K : Callees hs[g])
  {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = hs[g].D)
  (hGv : Proof.Mgf1.Valid Gs)

include hGh hGl hGv K in
/-- MGF1's hash function's part of a counter. -/
theorem gPart_ok {u₀ : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    {e db c D : Nat} (hd : DbAt D e db) (hD64 : D ≤ 64)
    (he : W 23 = off S e) (hdb : W 24 = BitVec.ofNat 64 db) (hc : c * hs[g].D < db)
    {u : State} {V3 : Nat → Byte} {W1 : Nat → BitVec 64} (L : Lay u F S)
    (R : Rep u.mem F S V3 (upd (upd W1 27 (BitVec.ofNat 64 (D + 4))) 28 (BitVec.ofNat 64 2)))
    (h31 : W1 31 = BitVec.ofNat 64 c) (h32 : W1 32 = BitVec.ofNat 64 (c * hs[g].D))
    (hW : ∀ k < nW, k < 27 ∨ 32 < k → W1 k = W k)
    (hV : ∀ o < oRsa, ctOut o → V3 o = mixV V (Spec.Mgf1.mgf1 Gs ((List.range D).map fun i => V (e + db + i)) db)
      e (min (c * hs[g].D) db) o)
    (hY : ∀ i < 256, V3 (oY + i) = (((List.range D).map fun i => V (e + db + i)) ++ Spec.Rsa.i2osp c 4).getD i 0)
    (hrd : u.rd = u₀.rd) (hwr : u.wr = u₀.wr) (hcs : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], u.gpr r = u₀.gpr r) :
    WP isa (gPart hs[g]) u fun v' => v'.cf = some (decide ((c + 1) * hs[g].D < db)) ∧
      MgfI u₀ F S V W (Spec.Mgf1.mgf1 Gs ((List.range D).map fun i => V (e + db + i)) db)
        e db hs[g].D (c + 1) v' := by
  have hD := hG.hD0
  have hDN := hG.hDN
  have hN := hG.N_le
  have hB := hG.B_le
  have hBc := hG.dims.B
  have hL := hG.dims.L
  have hfit := hd.fit
  have he1 := hd.e1
  have c1 : oEm = 2560 := rfl
  have c2 : oY = 3584 := rfl
  have c3 : oDig = 2304 := rfl
  have c4 : oLen = 2368 := rfl
  have c5 : oRsa = 8192 := rfl
  set seed := (List.range D).map fun i => V (e + db + i) with hseed
  set mk := Spec.Mgf1.mgf1 Gs seed db with hmk
  have hsl : seed.length = D := by rw [hseed, List.length_map, List.length_range]
  have hcD : c ≤ c * hs[g].D := Nat.le_mul_of_pos_right c hD
  unfold gPart seqs seqs
  have hml : (seed ++ Spec.Rsa.i2osp c 4).length = D + 4 := by rw [List.length_append, hsl, i2osp_len]
  refine WP.seq (WP.mono (mgfHashAny_gen hG K L R (ℓ := D + 4) (by simp [upd]) (by simp [upd])
      (by rcases hBc with h | h <;> rw [h] <;> omega_using [hD64, hL, h]))
    fun u4 ⟨L4, rd4, wr4, cs4, V5, W3, R4, hout4, hW4, hdig⟩ => ?_)
  have hdig := hdig _ hml (fun i hi => hY i (by rcases hBc with h | h <;> rw [h] at hi <;> omega_using [hi]))
  -- Into `DB`.
  have hW3 : ∀ k < nW, k < 27 ∨ 32 < k → W3 k = W k := fun k hk h => by
    rw [hW4 k hk (by omega_using [h]) (by omega_using [h])]; simp only [upd, ifn (show k ≠ 28 by omega_using [h]),
        ifn (show k ≠ 27 by omega_using [h])]
    exact hW k hk h
  have hW3' : ∀ k, k = 31 ∨ k = 32 → W3 k = W1 k := fun k h => by
    rw [hW4 k (by unfold nW frameBytes; omega_using [h]) (by omega_using [h]) (by omega_using [h])]
    simp only [upd, ifn (show k ≠ 28 by omega_using [h]), ifn (show k ≠ 27 by omega_using [h])]
  have hcD' : c * hs[g].D + hs[g].D ≤ db + hs[g].D := by omega_using [hc]
  refine WP.seq (WP.mono (xorOut_ok hG L4 R4 hd.zero ((hW3 23 (by decide) (by omega_using [])).trans he)
    ((hW3 24 (by decide) (by omega_using [])).trans hdb) ((hW3' 32 (by omega_using [])).trans h32) hc)
    fun u5 ⟨L5, k5, R5⟩ => ?_)
  -- The next counter.
  refine WP.mono (nextCtr_ok hG L5 R5 ((hW3' 31 (by omega_using [])).trans h31) ((hW3' 32 (by omega_using [])).trans h32)
    ((hW3 24 (by decide) (by omega_using [])).trans hdb) (by omega_using [hfit, c1, hcD', hDN, hN])
        (by omega_using [hfit, c1])) fun u6 ⟨L6, k6, cf6, R6⟩ => ?_
  refine ⟨by rw [cf6, Nat.succ_mul], L6, ?_, ?_, ?_, _, _, R6, by simp [upd], ?_, ?_, ?_⟩
  · rw [k6.2.1, k5.2.1, rd4, hrd]
  · rw [k6.2.2, k5.2.2, wr4, hwr]
  · intro r hr
    rw [keep_cs k6 (by decide) r hr, keep_cs k5 (by decide) r hr, cs4 r hr, hcs r hr]
  · simp [upd, Nat.succ_mul]
  · intro k hk h
    simp only [upd, ifn (show k ≠ 32 by omega_using [h]), ifn (show k ≠ 31 by omega_using [h])]
    exact hW3 k hk h
  · intro o ho hco
    have hcm : hs[g].D * c = c * hs[g].D := Nat.mul_comm _ _
    have hs1 : (c + 1) * hs[g].D = c * hs[g].D + hs[g].D := Nat.succ_mul _ _
    have hdg : ∀ j < hs[g].D, V5 (oDig + j) = (hG.SH.H.hash (seed ++ Spec.Rsa.i2osp c 4)).getD j 0 :=
      fun j hj => map_range_getD (f := fun i => V5 (oDig + i)) hdig hj
    have hold : V5 o = mixV V mk e (min (c * hs[g].D) db) o := by
      rw [hout4 o ho hco, hV o ho hco]
    simp only [xorV]
    by_cases hx : e + c * hs[g].D ≤ o ∧ o < e + c * hs[g].D + min hs[g].D (db - c * hs[g].D)
    · have hq : (o - e) / hs[g].D = c :=
        Nat.div_eq_of_lt_le (by rw [Nat.mul_comm]; omega_using [hcm, hx]) (by rw [Nat.succ_mul, Nat.mul_comm]; omega_using [hcm, hx])
      have hr : (o - e) % hs[g].D = o - (e + c * hs[g].D) := by
        rw [Nat.mod_eq_sub_mul_div, hq, Nat.mul_comm]; omega_using []
      rw [ifp hx, hold, hdg _ (by omega_using [hx]), mixV, mixV, ifn (by omega_using [hx]), ifp (by omega_using [hs1, hx]), hmk,
        mgf1_getD hGv seed (show o - e < db by omega_using [hx]), hGl, hGh, hq, hr]
    · rw [ifn hx, hold, mixV, mixV]
      by_cases hy : e ≤ o ∧ o < e + min (c * hs[g].D) db
      · rw [ifp hy, ifp (by omega_using [hs1, hy])]
      · rw [ifn hy, ifn (by omega_using [hs1, hx, hy])]

end

/-- One counter. -/
theorem roundAny_ok {hs : List Hash} {g : Nat} (hg : g < hs.length) (hl : hs.length ≤ 2 ^ 31)
    (hG : HashOK hs[g]) (K : Callees hs[g]) {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x)
    (hGl : Gs.len = hs[g].D) (hGv : Proof.Mgf1.Valid Gs)
    {u₀ : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    {e db c D : Nat} (hd : DbAt D e db) (hD0 : 0 < D) (hD64 : D ≤ 64)
    (he : W 23 = off S e) (hdb : W 24 = BitVec.ofNat 64 db) (h15 : W 15 = BitVec.ofNat 64 D)
    (h48 : W 48 = BitVec.ofNat 64 g)
    {v : State} (I : MgfI u₀ F S V W (Spec.Mgf1.mgf1 Gs ((List.range D).map fun i => V (e + db + i)) db)
      e db hs[g].D c v) (hc : c * hs[g].D < db) :
    WP isa (.seq seedPart (dispatch sMsel gPart hs)) v
      fun v' => v'.cf = some (decide ((c + 1) * hs[g].D < db)) ∧
        MgfI u₀ F S V W (Spec.Mgf1.mgf1 Gs ((List.range D).map fun i => V (e + db + i)) db)
          e db hs[g].D (c + 1) v' := by
  have hD := hG.hD0
  have hfit := hd.fit
  have he1 := hd.e1
  have c1 : oEm = 2560 := rfl
  have c2 : oY = 3584 := rfl
  have c4 : oLen = 2368 := rfl
  have c5 : oRsa = 8192 := rfl
  have hcD : c ≤ c * hs[g].D := Nat.le_mul_of_pos_right c hD
  obtain ⟨V1, W1, R1, h31, h32, hW, hV⟩ := I.rep
  have hW23 : W1 23 = off S e := (hW 23 (by decide) (by omega_using [])).trans he
  have hW24 : W1 24 = BitVec.ofNat 64 db := (hW 24 (by decide) (by omega_using [])).trans hdb
  have hW15 : W1 15 = BitVec.ofNat 64 D := (hW 15 (by decide) (by omega_using [])).trans h15
  have hW48 : W1 48 = BitVec.ofNat 64 g := (hW 48 (by decide) (by omega_using [])).trans h48
  have hH1 : ∀ i < D, V1 (e + db + i) = V (e + db + i) := fun i hi => by
    rw [hV _ (by omega_using [hfit, c1, c5, hi]) ⟨by omega_using [he1, c1, c4], by omega_using [hfit, c1, c2, hi]⟩,
        mixV, ifn (by omega_using [])]
  set seed := (List.range D).map fun i => V (e + db + i) with hseed
  have hsl : seed.length = D := by rw [hseed, List.length_map, List.length_range]
  have hsg : ∀ i < D, seed.getD i 0 = V (e + db + i) := fun i hi => by
    rw [hseed, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]; rfl
  unfold seedPart seqs seqs
  -- `Y` cleared.
  refine WP.seq (WP.seq (WP.mono (clearSeedBlocks_ok I.L R1) fun u1 ⟨L1, k1, hcx1, R1'⟩ => ?_))
  -- `H`.
  refine WP.seq (WP.mono (copySeed_ok L1 R1' hd hW23 hW24 hW15 hD0 hcx1) fun u2 ⟨L2, k2, R2⟩ => ?_)
  -- The counter.
  refine WP.mono (counterAny_ok L2 R2 h31 (by omega_using [hc, hfit, c1, hcD]) hW15 hD64
    ((k2.gpr (by decide)).trans hcx1)) fun u3 ⟨L3, k3, R3⟩ => ?_
  -- MGF1's hash function.
  refine dispatch_ok (j := 48) L3 R3 rfl (by decide) (by simp [upd, hW48]) hl hg fun w kw hmw hax => ?_
  have Lw : Lay w F S := L3.congr (kw.gpr (by decide)) kw.2.2 (by rw [hmw])
  refine gPart_ok hg hG K hGh hGl hGv hd hD64 he hdb hc Lw (hmw ▸ R3) h31 h32 hW (fun o ho hco => ?_)
    (fun i hi => ?_) ?_ ?_ ?_
  · have hY := hco.2
    simp only [ctrV, cpV, clrV]
    rw [ifn (by omega_using [hY, hD64]), ifn (by omega_using [hY, hD64]), ifn (by omega_using [hY]), hV o ho hco]
  · rw [← hseed]
    simp only [ctrV, cpV, clrV, getD_app, hsl]
    by_cases h1 : i < D
    · rw [ifn (by omega_using [h1]), ifp (by omega_using [h1]), ifp h1, ifn (by omega_using [hfit, c1, c2, h1]),
        Nat.add_sub_cancel_left, hH1 i h1, hsg i h1]
    · by_cases h2 : i < D + 4
      · rw [ifp (by omega_using [h1, h2]), ifn h1, show oY + i - (oY + D) = i - D by omega_using []]
      · rw [ifn (by omega_using [h2]), ifn (by omega_using [h2]), ifp (by omega_using [hi]), ifn h1, List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by rw [i2osp_len]; omega_using [h2])]
        rfl
  · rw [kw.2.1, k3.2.1, k2.2.1, k1.2.1, I.rd]
  · rw [kw.2.2, k3.2.2, k2.2.2, k1.2.2, I.wr]
  · intro r hr
    rw [keep_cs kw (by decide) r hr, keep_cs k3 (by decide) r hr, keep_cs k2 (by decide) r hr,
      keep_cs k1 (by decide) r hr, I.cs r hr]

/-! ## MGF1 -/

/-- `DB ⊕= MGF1(G, H, dbLen)`, where `H` is the `D` bytes after `DB` and `G`
the hash function the slot `sMsel` names. -/
theorem mgfXorAny_ok {hs : List Hash} {g : Nat} (hg : g < hs.length) (hl : hs.length ≤ 2 ^ 31)
    (hG : HashOK hs[g]) (K : Callees hs[g]) {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x)
    (hGl : Gs.len = hs[g].D) (hGv : Proof.Mgf1.Valid Gs)
    {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {e db D : Nat} (hd : DbAt D e db) (hD0 : 0 < D) (hD64 : D ≤ 64)
    (he : W 23 = off S e) (hdb : W 24 = BitVec.ofNat 64 db) (h15 : W 15 = BitVec.ofNat 64 D)
    (h48 : W 48 = BitVec.ofNat 64 g) :
    WP isa (mgfXorAny hs) u fun u' => Lay u' F S ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧
      (∀ r ∈ [Reg.r13, .r14, .r15, .rsp], u'.gpr r = u.gpr r) ∧
      ∃ V' W', Rep u'.mem F S V' W' ∧ (∀ k < nW, k < 27 ∨ 32 < k → W' k = W k) ∧
        ∀ o < oRsa, ctOut o → V' o = mixV V (Spec.Mgf1.mgf1 Gs ((List.range D).map fun i => V (e + db + i)) db)
          e db o := by
  have hD := hG.hD0
  have hdb1 := hd.db1
  have G' := L.geo
  have R2 := (R.wf G' (k := 31) (by decide) 0#64).wf G' (k := 32) (by decide) 0#64
  rw [show off F (8 * 31) = off F sCtr from rfl, show off F (8 * 32) = off F sDone from rfl] at R2
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun v => v.mem =
      (u.mem.writeW (off F sCtr) 0#64).writeW (off F sDone) 0#64) ?_ rfl)
    fun v ⟨hm, hk⟩ => ?_)
  · xrun [ea_sp, L.rsp, L.st (d := sCtr) (by decide), L.st (d := sDone) (by decide),
      show BitVec.setWidth 64 (0 : BitVec 32) = 0#64 from rfl]
  have R2' : Rep v.mem F S V (upd (upd W 31 0#64) 32 0#64) := hm ▸ R2
  have Lv : Lay v F S := L.congr (hk.gpr (by decide)) hk.2.2 (by
    rw [slot_eq sScr 21 rfl, slot_eq sScr 21 rfl, R2'.fr 21 (by decide), R.fr 21 (by decide)]; simp [upd])
  have I0 : MgfI u F S V W (Spec.Mgf1.mgf1 Gs ((List.range D).map fun i => V (e + db + i)) db) e db hs[g].D 0 v :=
    ⟨Lv, hk.2.1, hk.2.2, keep_cs hk (by decide), _, _, R2', by simp [upd], by simp [upd],
      fun k _ h => by simp only [upd, ifn (show k ≠ 32 by omega_using [h]), ifn (show k ≠ 31 by omega_using [h])],
      fun o _ _ => by simp only [mixV, Nat.zero_mul, Nat.zero_min, Nat.add_zero]; rw [ifn (by omega_using [])]⟩
  refine WP.loop (M := isa) (fun n w => ∃ c, n = db - c * hs[g].D ∧ c * hs[g].D < db ∧
      MgfI u F S V W (Spec.Mgf1.mgf1 Gs ((List.range D).map fun i => V (e + db + i)) db) e db hs[g].D c w)
    ?_ (db - 0 * hs[g].D) v ⟨0, rfl, by omega_using [hdb1], I0⟩
  rintro n w ⟨c, rfl, hc, I⟩
  refine WP.mono (roundAny_ok hg hl hG K hGh hGl hGv hd hD0 hD64 he hdb h15 h48 I hc) fun w' ⟨hcf, I'⟩ => ?_
  have hs1 : (c + 1) * hs[g].D = c * hs[g].D + hs[g].D := Nat.succ_mul _ _
  by_cases h : (c + 1) * hs[g].D < db
  · refine .inr ⟨by simp only [eval, hcf, h, decide_true], _, ?_, c + 1, rfl, h, I'⟩
    omega_using [hD, hs1, h]
  · refine .inl ⟨by simp only [eval, hcf, h, decide_false], I'.L, I'.rd, I'.wr, I'.cs, ?_⟩
    obtain ⟨V', W', R', _, _, hW', hV'⟩ := I'.rep
    exact ⟨V', W', R', hW', fun o ho hco => by rw [hV' o ho hco, Nat.min_eq_right (by omega_using [h])]⟩

end VG.Proof.RsaPss.X86_64.Any
