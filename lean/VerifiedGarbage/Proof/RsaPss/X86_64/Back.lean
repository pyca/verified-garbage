module

public import VerifiedGarbage.Proof.RsaPss.X86_64.Copy
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSASSA-PSS verification on x86-64: the salt's hash, with its length given

`fixedBack` (`fixedBack_ok`): with the salt the last `sl` bytes of `DB`, at a
public offset, `M'`'s prefix written, `H(prefix ‖ salt)` computed, and `rax`
1 if `acc` is zero and it is `H`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Impl.Mgf1.X86_64 (sp ix at_ step byteLoop seqs)
open VG.Impl.RsaOaep.X86_64 (frameBytes sScr sK sHD oEm oBuf oSt oDig oW oRsa scr lay)
open VG.Proof.RsaOaep.X86_64 (Lay Rep upd ea_sp ofNat_add_lit off_plus nW Here Fns WP.here updF_ok finF_ok sizes inR
  inR_cons inR_nil keep_cs' cs_disj stBytes cpV)
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Bignum (off)
open VG.Proof.HashFns (StreamingOK)

/-- `update`'s arguments for the salt at the end of `DB` (`e`, `db`), `sl`
bytes, after the prefix. -/
theorem updFix_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {D e db sl : Nat} (hD : W 39 = BitVec.ofNat 64 D) (he : W 33 = off S e)
    (hdb : W 44 = BitVec.ofNat 64 db) (hsl : W 29 = BitVec.ofNat 64 sl) (hsl1 : sl ≤ db) :
    WP isa (.block (scr .rdi oSt ++ plen ++ ([.mov .rdx (.mem (sp sEb)), .alu .add .rdx (.mem (sp sDb)),
      .alu .sub .rdx (.mem (sp sSlen)), .mov .rcx (.mem (sp sSlen))] : List Instr) ++ scr .r8 oW)) u fun u' =>
      u'.gpr .rdi = off S oSt ∧ u'.gpr .rsi = BitVec.ofNat 64 (D + 8) ∧ u'.gpr .rdx = off S (e + db - sl) ∧
      u'.gpr .rcx = BitVec.ofNat 64 sl ∧ u'.gpr .r8 = off S oW ∧ u'.mem = u.mem ∧
      Keep [.rdi, .rsi, .rdx, .rcx, .r8] u u' := by
  have hs := L.slot
  simp only [Bignum.word] at hs
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .rcx, .r8] (Q := fun u' => u'.gpr .rdi = off S oSt ∧
      u'.gpr .rsi = BitVec.ofNat 64 (D + 8) ∧ u'.gpr .rdx = off S (e + db - sl) ∧ u'.gpr .rcx = BitVec.ofNat 64 sl ∧
      u'.gpr .r8 = off S oW ∧ u'.mem = u.mem) ?_ rfl) fun u' ⟨⟨a, b, c, d, f, g⟩, k⟩ => ⟨a, b, c, d, f, g, k⟩
  xrun [scr, plen, Impl.Mgf1.X86_64.scr, lay, List.cons_append, List.nil_append, ea_sp, L.rsp,
    L.ld (d := sScr) (by decide), L.ld (d := sHD) (by decide), L.ld (d := sEb) (by decide),
    L.ld (d := sDb) (by decide), L.ld (d := sSlen) (by decide), hs, R.rd (d := sHD) 39 rfl (by decide),
    R.rd (d := sEb) 33 rfl (by decide), R.rd (d := sDb) 44 rfl (by decide), R.rd (d := sSlen) 29 rfl (by decide),
    hD, he, hdb, hsl, ofNat_add_lit, off_plus, VG.Proof.RsaOaep.X86_64.off_sub S (show sl ≤ e + db by omega),
    VG.Proof.MlKem.X86_64.sx_ofNat (show oSt < 2 ^ 31 by decide),
    VG.Proof.MlKem.X86_64.sx_ofNat (show oW < 2 ^ 31 by decide)]

variable {T : Spec.HashFns.Streaming} {Hh : Spec.Mgf1.Hash} (hT : StreamingOK T Hh)
variable {stack : Nat} {e₀ : State} {fi fu ff : Addr}

include hT in
/-- With the salt's length `sl` given: `rax` is 1 if `acc` (word 4) is zero
and `H(0⁸ ‖ mHash ‖ salt)` is `H`, the salt the last `sl` bytes of `DB`. -/
theorem fixedBack_ok (hF : Fns stack e₀ T fi fu ff) {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = T.S.H.hash x)
    {u : State} {F S : Addr} (hh : Here stack e₀ u F S) (L : Lay u F S) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep u.mem F S V W) {D e db sl : Nat} {p : Addr}
    (hD : W 39 = BitVec.ofNat 64 D) (hDl : T.S.digestBytes = D) (hD64 : D ≤ 64)
    (hfn : W 45 = fi ∧ W 46 = fu ∧ W 47 = ff) (hp : W 27 = p) (he : W 33 = off S e)
    (hdb : W 44 = BitVec.ofNat 64 db) (hsl : W 29 = BitVec.ofNat 64 sl) (hsl1 : sl ≤ db)
    (hfit : e + db + D ≤ oBuf)
    (hsrc : ∀ i < D, InRegions (u.rd ++ u.wr) (p + BitVec.ofNat 64 i) 1)
    (hdis : ∀ i < D, ∀ j < D, p + BitVec.ofNat 64 i ≠ off S (oMp + 8 + j)) :
    WP isa fixedBack u fun u' => Lay u' F S ∧ Here stack e₀ u' F S ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧
      (∀ r ∈ calleeSaved, u'.gpr r = u.gpr r) ∧
      u'.gpr .rax = if W 4 = 0 ∧ ∀ i < D, (Hs.hash (Spec.RsaPss.zeros 8 ++
          (List.range D).map (fun i => u.mem (p + BitVec.ofNat 64 i)) ++
          (List.range sl).map (fun i => V (e + db - sl + i)))).getD i 0 = V (e + db + i) then 1 else 0 := by
  obtain ⟨hzS, hzF, hzW, hzDF, hzD⟩ := sizes hT
  have c3 : oBuf = 1024 := rfl
  have c1 : oSt = 3072 := rfl
  have c2 : oDig = 3328 := rfl
  have c4 : oW = 4096 := rfl
  have c5 : oRsa = 8192 := rfl
  have c6 : oMp = 3584 := rfl
  unfold fixedBack seqs seqs seqs seqs seqs seqs
  refine WP.seq (WP.mono (WP.here (by decide) hh (mPrefix_ok L R hp hD (by omega) hD64 hsrc hdis))
    fun u1 ⟨⟨L1, k1, R1⟩, hh1⟩ => ?_)
  refine WP.seq (WP.mono (hashPrefix_ok hT hF hh1 L1 R1 hD hD64 hfn)
    fun u2 ⟨L2, hh2, rd2, wr2, cs2, V2, R2, hV2, hr2⟩ => ?_)
  refine WP.seq (WP.mono (WP.here rfl hh2 (updFix_ok L2 R2 hD he hdb hsl hsl1))
    fun u3 ⟨⟨hdi3, hsi3, hdx3, hcx3, h83, hm3, k3⟩, hh3⟩ => ?_)
  have L3 : Lay u3 F S := L2.congr (k3.gpr (by decide)) k3.2.2 (by rw [hm3])
  have R3 : Rep u3.mem F S V2 W := hm3 ▸ R2
  refine WP.seq (WP.mono (updF_ok hT hF hh3 L3 R3 (j := 45) rfl (by decide) hfn.2.1 (a := e + db - sl) (len := sl)
      (by omega) (.inl (by omega)) (.inl (by omega)) hdi3 hdx3 hcx3 h83)
    fun u4 ⟨L4, rd4, wr4, cs4, R4, hh4, hr4⟩ => ?_)
  have hpl : ((List.range (D + 8)).map fun i => mpV V (fun i => u.mem (p + BitVec.ofNat 64 i)) D (oMp + i)).length
      = D + 8 := by simp
  have hR4 := hr4 _ (hm3 ▸ hr2) (by rw [hsi3, hpl])
  obtain ⟨V4, R4, hV4, -⟩ := VG.Proof.RsaOaep.X86_64.Rep.ex R4
  refine WP.seq (WP.mono (WP.here rfl hh4 (finSl_ok L4 R4 hD hsl (o := oDig) (by decide)))
    fun u5 ⟨⟨hdi5, hsi5, hdx5, hcx5, hm5, k5⟩, hh5⟩ => ?_)
  have L5 : Lay u5 F S := L4.congr (k5.gpr (by decide)) k5.2.2 (by rw [hm5])
  have R5 : Rep u5.mem F S V4 W := hm5 ▸ R4
  refine WP.seq (WP.mono (finF_ok hT hF hh5 L5 R5 (j := 45) rfl (by decide) hfn.2.2 (o := oDig)
    (Or.inr (by omega)) hdi5 hdx5 hcx5) fun u6 ⟨L6, rd6, wr6, cs6, R6, hh6, hr6⟩ => ?_)
  have hml : ((List.range (D + 8)).map (fun i => mpV V (fun i => u.mem (p + BitVec.ofNat 64 i)) D (oMp + i)) ++
      (List.range sl).map fun i => V2 (e + db - sl + i)).length = D + 8 + sl := by simp
  have hdig := hr6 _ (hm5 ▸ hR4) (by rw [hml]; omega) (by rw [hsi5, hml])
  obtain ⟨V6, R6, hV6, hV6'⟩ := VG.Proof.RsaOaep.X86_64.Rep.ex R6
  -- The bytes of `EM` are unchanged.
  have hEM : ∀ x, x < oBuf → V6 x = V x := fun x hx => by
    rw [hV6 _ (by simp only [inR_cons, inR_nil, or_false]; omega),
      hV4 _ (by simp only [inR_cons, inR_nil, or_false]; omega),
      hV2 _ (by simp only [hR, inR_cons, inR_nil, or_false]; omega)]
    simp only [mpV, stBytes, cpV]
    rw [ifn (by omega), ifn (by omega)]
  refine WP.mono (WP.here (by decide) hh6 (cmpH_ok L6 R6 he hdb hD (by omega) hD64 (by omega)))
    fun u7 ⟨⟨k7, hm7, hax7⟩, hh7⟩ => ⟨L6.congr (k7.gpr (by decide)) k7.2.2 (by rw [hm7]), hh7,
      k7.2.1.trans (rd6.trans (k5.2.1.trans (rd4.trans (k3.2.1.trans (rd2.trans k1.2.1))))),
      k7.2.2.trans (wr6.trans (k5.2.2.trans (wr4.trans (k3.2.2.trans (wr2.trans k1.2.2))))), fun r hr => ?_, ?_⟩
  · rw [keep_cs' k7 (cs_disj _ (by decide)) r hr, cs6 r hr, keep_cs' k5 (cs_disj _ (by decide)) r hr, cs4 r hr,
      keep_cs' k3 (cs_disj _ (by decide)) r hr, cs2 r hr, keep_cs' k1 (cs_disj _ (by decide)) r hr]
  · have hsalt : (List.range sl).map (fun i => V2 (e + db - sl + i)) =
        (List.range sl).map (fun i => V (e + db - sl + i)) := List.map_congr_left fun j hj => by
      have := List.mem_range.mp hj
      rw [hV2 _ (by simp only [hR, inR_cons, inR_nil, or_false]; omega)]
      simp only [mpV, stBytes, cpV]
      rw [ifn (by omega), ifn (by omega)]
    have hc : (W 4 = 0 ∧ ∀ i < D, V6 (oDig + i) = V6 (e + db + i)) ↔ (W 4 = 0 ∧ ∀ i < D, (Hs.hash
        (Spec.RsaPss.zeros 8 ++ (List.range D).map (fun i => u.mem (p + BitVec.ofNat 64 i)) ++
          (List.range sl).map (fun i => V (e + db - sl + i)))).getD i 0 = V (e + db + i)) :=
      and_congr_right fun _ => forall_congr' fun i => imp_congr_right fun hi => by
        rw [hEM (e + db + i) (by omega), hV6' (oDig + i) (by simp only [inR_cons, inR_nil, or_false]; omega),
          hdig i (by omega), ← hHh, mpV_bytes, hsalt]
    rw [hax7]
    by_cases h : W 4 = 0 ∧ ∀ i < D, V6 (oDig + i) = V6 (e + db + i)
    · rw [ifp h, ifp (hc.mp h)]
    · rw [ifn h, ifn (fun h' => h (hc.mpr h'))]

end VG.Proof.RsaPss.X86_64
