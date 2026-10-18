module

public import VerifiedGarbage.Proof.RsaPss.X86_64.Enc
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Label
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSASSA-PSS on x86-64: hashing `M'`

`hashPrefix` sets the streaming state of `H` (whose functions' addresses
are in the slots from `sFnH`) to represent `M'`'s prefix, the `hLen + 8`
bytes at `scratch + oMp` (`hashPrefix_ok`); `hashM` then absorbs the salt,
from the caller's memory, and finalizes `H = Hash(M')` to `scratch + oDig`
(`hashM_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Impl.Mgf1.X86_64 (sp ix at_ step byteLoop seqs)
open VG.Impl.RsaOaep.X86_64 (frameBytes sScr sK sHD oEm oSt oDig oW oRsa scr lay)
open VG.Proof.RsaOaep.X86_64 (Lay Rep upd ea_sp ofNat_add_lit off_plus nW Here Fns WP.here scr_ok initF_ok updF_ok
  updExtF_ok finF_ok sizes inR inR_cons inR_nil keep_cs' cs_disj)
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Bignum (off)
open VG.Proof.HashFns (StreamingOK)

/-- `update`'s arguments for the prefix: the state, after nothing, the
`D + 8` bytes at `scratch + oMp`, the working space. -/
theorem updPre_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {D : Nat} (hD : W 39 = BitVec.ofNat 64 D) :
    WP isa (.block (scr .rdi oSt ++ ([.mov32 .rsi (.imm 0)] : List Instr) ++ scr .rdx oMp ++
      ([.mov .rcx (.mem (sp sHD)), .alu .add .rcx (.imm 8)] : List Instr) ++ scr .r8 oW)) u fun u' =>
      u'.gpr .rdi = off S oSt ∧ u'.gpr .rsi = BitVec.ofNat 64 0 ∧ u'.gpr .rdx = off S oMp ∧
      u'.gpr .rcx = BitVec.ofNat 64 (D + 8) ∧ u'.gpr .r8 = off S oW ∧ u'.mem = u.mem ∧
      Keep [.rdi, .rsi, .rdx, .rcx, .r8] u u' := by
  have hs := L.slot
  simp only [Bignum.word] at hs
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .rcx, .r8] (Q := fun u' => u'.gpr .rdi = off S oSt ∧
      u'.gpr .rsi = BitVec.ofNat 64 0 ∧ u'.gpr .rdx = off S oMp ∧ u'.gpr .rcx = BitVec.ofNat 64 (D + 8) ∧
      u'.gpr .r8 = off S oW ∧ u'.mem = u.mem) ?_ rfl) fun u' ⟨⟨a, b, c, d, f, g⟩, k⟩ => ⟨a, b, c, d, f, g, k⟩
  xrun [scr, Impl.Mgf1.X86_64.scr, lay, List.cons_append, List.nil_append, ea_sp, L.rsp,
    L.ld (d := sScr) (by decide), L.ld (d := sHD) (by decide), hs, R.rd (d := sHD) 39 rfl (by decide), hD,
    ofNat_add_lit, VG.Proof.MlKem.X86_64.sx_ofNat (show oSt < 2 ^ 31 by decide),
    VG.Proof.MlKem.X86_64.sx_ofNat (show oMp < 2 ^ 31 by decide),
    VG.Proof.MlKem.X86_64.sx_ofNat (show oW < 2 ^ 31 by decide)]

variable {T : Spec.HashFns.Streaming} {Hh : Spec.Mgf1.Hash} (hT : StreamingOK T Hh)
variable {stack : Nat} {e : State} {fi fu ff : Addr}

/-- The ranges of our working space that `H`'s calls write. -/
def hR : List (Nat × Nat) := [(oSt, 256), (oW, 2048)]

include hT in
/-- `H`'s state set to represent the prefix: the `D + 8` bytes at
`scratch + oMp`. -/
theorem hashPrefix_ok (hF : Fns stack e T fi fu ff) {u : State} {F S : Addr} (hh : Here stack e u F S)
    (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep u.mem F S V W) {D : Nat}
    (hD : W 39 = BitVec.ofNat 64 D) (hD64 : D ≤ 64) (hfn : W 45 = fi ∧ W 46 = fu ∧ W 47 = ff) :
    WP isa hashPrefix u fun u' => Lay u' F S ∧ Here stack e u' F S ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧
      (∀ r ∈ calleeSaved, u'.gpr r = u.gpr r) ∧
      ∃ V', Rep u'.mem F S V' W ∧ (∀ x, ¬ inR hR x → V' x = V x) ∧
        T.S.Repr u'.mem (off S oSt) ((List.range (D + 8)).map fun i => V (oMp + i)) := by
  obtain ⟨hzS, hzF, hzW, hzDF, hzD⟩ := sizes hT
  unfold hashPrefix seqs seqs seqs
  refine WP.seq (WP.mono (WP.here rfl hh (scr_ok L (d := .rdi) (by decide) (o := oSt) (by decide)))
    fun u1 ⟨⟨hdi1, hm1, k1⟩, hh1⟩ => ?_)
  have L1 : Lay u1 F S := L.congr (k1.gpr (by decide)) k1.2.2 (by rw [hm1])
  have R1 : Rep u1.mem F S V W := hm1 ▸ R
  refine WP.seq (WP.mono (initF_ok hT hF hh1 L1 R1 (j := 45) rfl (by decide) hfn.1 hdi1)
    fun u2 ⟨L2, rd2, wr2, cs2, R2, _, hh2, hr2⟩ => ?_)
  obtain ⟨V2, R2, hV2, -⟩ := VG.Proof.RsaOaep.X86_64.Rep.ex R2
  refine WP.seq (WP.mono (WP.here rfl hh2 (updPre_ok L2 R2 hD))
    fun u3 ⟨⟨hdi3, hsi3, hdx3, hcx3, h83, hm3, k3⟩, hh3⟩ => ?_)
  have L3 : Lay u3 F S := L2.congr (k3.gpr (by decide)) k3.2.2 (by rw [hm3])
  have R3 : Rep u3.mem F S V2 W := hm3 ▸ R2
  refine WP.mono (updF_ok hT hF hh3 L3 R3 (j := 45) rfl (by decide) hfn.2.1 (a := oMp) (len := D + 8)
      (by unfold oMp oRsa; omega) (.inr (by unfold oMp oSt; omega)) (.inl (by unfold oMp oW; omega))
      hdi3 hdx3 hcx3 h83)
    fun u4 ⟨L4, rd4, wr4, cs4, R4, hh4, hr4⟩ => ?_
  have hR4 := hr4 [] (hm3 ▸ hr2) (by rw [hsi3]; rfl)
  rw [List.nil_append] at hR4
  obtain ⟨V4, R4, hV4, -⟩ := VG.Proof.RsaOaep.X86_64.Rep.ex R4
  have nh : ∀ x, ¬ inR hR x → V2 x = V x := fun x hx => hV2 x (by
    simp only [hR, inR_cons, inR_nil, or_false] at hx ⊢; omega)
  refine ⟨L4, hh4, rd4.trans (k3.2.1.trans (rd2.trans k1.2.1)), wr4.trans (k3.2.2.trans (wr2.trans k1.2.2)),
    fun r hr => ?_, V4, R4, fun x hx => ?_, ?_⟩
  · rw [cs4 r hr, keep_cs' k3 (cs_disj _ (by decide)) r hr, cs2 r hr, keep_cs' k1 (cs_disj _ (by decide)) r hr]
  · rw [hV4 _ (by simp only [hR, inR_cons, inR_nil, or_false] at hx ⊢; unfold oSt oW at *; omega), nh x hx]
  · refine VG.Proof.RsaOaep.X86_64.repr_congr (List.map_congr_left fun i hi => ?_) hR4
    have := List.mem_range.mp hi
    exact nh _ (by simp only [hR, inR_cons, inR_nil, or_false]; unfold oMp oSt oW; omega)

/-- Where the salt is: its slots (words 28 and 29), and its bytes apart from
our working space and the stack below the frame. -/
structure SaltAt (t : State) (F S : Addr) (W : Nat → BitVec 64) (q : Addr) (sl : Nat) : Prop where
  hq : W 28 = q
  hsl : W 29 = BitVec.ofNat 64 sl
  len : sl < 2 ^ 64
  cov : Covers [⟨q, sl⟩] (t.rd ++ t.wr)
  dS : Region.Disjoint ⟨q, sl⟩ ⟨S, oRsa⟩
  dK : (below F 16).Disjoint ⟨q, sl⟩

theorem SaltAt.congr {t t' : State} {F S : Addr} {W W' : Nat → BitVec 64} {q : Addr} {sl : Nat}
    (h : SaltAt t F S W q sl) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (h28 : W' 28 = W 28)
    (h29 : W' 29 = W 29) : SaltAt t' F S W' q sl :=
  ⟨h28.trans h.hq, h29.trans h.hsl, h.len, by rw [hrd, hwr]; exact h.cov, h.dS, h.dK⟩

/-- `update`'s arguments for the salt, after the prefix. -/
theorem updSalt_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {D : Nat} (hD : W 39 = BitVec.ofNat 64 D) {q : Addr} {sl : Nat}
    (A : SaltAt u F S W q sl) :
    WP isa (.block (scr .rdi oSt ++ plen ++ ([.mov .rdx (.mem (sp sSalt)), .mov .rcx (.mem (sp sSaltLen))] : List Instr) ++
      scr .r8 oW)) u fun u' =>
      u'.gpr .rdi = off S oSt ∧ u'.gpr .rsi = BitVec.ofNat 64 (D + 8) ∧ u'.gpr .rdx = q ∧
      u'.gpr .rcx = BitVec.ofNat 64 sl ∧ u'.gpr .r8 = off S oW ∧ u'.mem = u.mem ∧
      Keep [.rdi, .rsi, .rdx, .rcx, .r8] u u' := by
  have hs := L.slot
  simp only [Bignum.word] at hs
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .rcx, .r8] (Q := fun u' => u'.gpr .rdi = off S oSt ∧
      u'.gpr .rsi = BitVec.ofNat 64 (D + 8) ∧ u'.gpr .rdx = q ∧ u'.gpr .rcx = BitVec.ofNat 64 sl ∧
      u'.gpr .r8 = off S oW ∧ u'.mem = u.mem) ?_ rfl) fun u' ⟨⟨a, b, c, d, f, g⟩, k⟩ => ⟨a, b, c, d, f, g, k⟩
  xrun [scr, plen, Impl.Mgf1.X86_64.scr, lay, List.cons_append, List.nil_append, ea_sp, L.rsp,
    L.ld (d := sScr) (by decide), L.ld (d := sHD) (by decide), L.ld (d := sSalt) (by decide),
    L.ld (d := sSaltLen) (by decide), hs, R.rd (d := sHD) 39 rfl (by decide),
    R.rd (d := sSalt) 28 rfl (by decide), R.rd (d := sSaltLen) 29 rfl (by decide), hD, A.hq, A.hsl,
    ofNat_add_lit, VG.Proof.MlKem.X86_64.sx_ofNat (show oSt < 2 ^ 31 by decide),
    VG.Proof.MlKem.X86_64.sx_ofNat (show oW < 2 ^ 31 by decide)]

/-- `finalize`'s arguments, after the prefix and `sl` more bytes (word 29),
to `scratch + o`. -/
theorem finSl_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {D sl : Nat} (hD : W 39 = BitVec.ofNat 64 D) (hsl : W 29 = BitVec.ofNat 64 sl)
    {o : Nat} (ho : o < 2 ^ 31) :
    WP isa (.block (scr .rdi oSt ++ plen ++ ([.alu .add .rsi (.mem (sp sSaltLen))] : List Instr) ++ scr .rdx o ++ scr .rcx oW))
      u fun u' => u'.gpr .rdi = off S oSt ∧ u'.gpr .rsi = BitVec.ofNat 64 (D + 8 + sl) ∧ u'.gpr .rdx = off S o ∧
      u'.gpr .rcx = off S oW ∧ u'.mem = u.mem ∧ Keep [.rdi, .rsi, .rdx, .rcx] u u' := by
  have hs := L.slot
  simp only [Bignum.word] at hs
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .rcx] (Q := fun u' => u'.gpr .rdi = off S oSt ∧
      u'.gpr .rsi = BitVec.ofNat 64 (D + 8 + sl) ∧ u'.gpr .rdx = off S o ∧ u'.gpr .rcx = off S oW ∧
      u'.mem = u.mem) ?_ rfl) fun u' ⟨⟨a, b, c, d, f⟩, k⟩ => ⟨a, b, c, d, f, k⟩
  xrun [scr, plen, Impl.Mgf1.X86_64.scr, lay, List.cons_append, List.nil_append, ea_sp, L.rsp,
    L.ld (d := sScr) (by decide), L.ld (d := sHD) (by decide), L.ld (d := sSaltLen) (by decide), hs,
    R.rd (d := sHD) 39 rfl (by decide), R.rd (d := sSaltLen) 29 rfl (by decide), hD, hsl, ofNat_add_lit,
    BitVec.ofNat_add, VG.Proof.MlKem.X86_64.sx_ofNat (show oSt < 2 ^ 31 by decide),
    VG.Proof.MlKem.X86_64.sx_ofNat ho, VG.Proof.MlKem.X86_64.sx_ofNat (show oW < 2 ^ 31 by decide)]

/-- The ranges `hashM` writes. -/
def mR : List (Nat × Nat) := [(oSt, 256), (oDig, 64), (oW, 2048)]

include hT in
/-- `H = Hash(M')` to `scratch + oDig`, `M'` the prefix and the salt. -/
theorem hashM_ok (hF : Fns stack e T fi fu ff) {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = T.S.H.hash x)
    {u : State} {F S : Addr} (hh : Here stack e u F S) (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {D : Nat} (hD : W 39 = BitVec.ofNat 64 D) (hD64 : D ≤ 64)
    (hfn : W 45 = fi ∧ W 46 = fu ∧ W 47 = ff) {q : Addr} {sl : Nat} (A : SaltAt u F S W q sl)
    (hbd : q.toNat + sl ≤ 2 ^ 64) (hslb : sl ≤ 1024)
    (hcd : ∀ x, (⟨q, sl⟩ : Region).Contains x 1 → InRegions (e.rd ++ e.wr ++ abi.reserved stack e) x 1)
    (hsW : ∀ x, (⟨q, sl⟩ : Region).Contains x 1 → ∀ r ∈ e.wr ++ abi.reserved stack e, ¬ r.Contains x 1) :
    WP isa hashM u fun u' => Lay u' F S ∧ Here stack e u' F S ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧
      (∀ r ∈ calleeSaved, u'.gpr r = u.gpr r) ∧
      ∃ V', Rep u'.mem F S V' W ∧ (∀ x, ¬ inR mR x → V' x = V x) ∧
        ∀ i < T.S.digestBytes, V' (oDig + i) =
          (Hs.hash ((List.range (D + 8)).map (fun i => V (oMp + i)) ++ Spec.Rsa.bytesAt e.mem q sl)).getD i 0 := by
  obtain ⟨hzS, hzF, hzW, hzDF, hzD⟩ := sizes hT
  have hlen := A.len
  unfold hashM seqs seqs seqs seqs
  refine WP.seq (WP.mono (hashPrefix_ok hT hF hh L R hD hD64 hfn)
    fun u1 ⟨L1, hh1, rd1, wr1, cs1, V1, R1, hV1, hr1⟩ => ?_)
  have A1 : SaltAt u1 F S W q sl := A.congr rd1 wr1 rfl rfl
  refine WP.seq (WP.mono (WP.here rfl hh1 (updSalt_ok L1 R1 hD A1))
    fun u2 ⟨⟨hdi2, hsi2, hdx2, hcx2, h82, hm2, k2⟩, hh2⟩ => ?_)
  have L2 : Lay u2 F S := L1.congr (k2.gpr (by decide)) k2.2.2 (by rw [hm2])
  have R2 : Rep u2.mem F S V1 W := hm2 ▸ R1
  have A2 : SaltAt u2 F S W q sl := A1.congr k2.2.1 k2.2.2 rfl rfl
  refine WP.seq (WP.mono (updExtF_ok hT hF hh2 L2 R2 (j := 45) rfl (by decide) hfn.2.1 A2.len hbd hcd A2.dS
      A2.dK hdi2 hdx2 hcx2 h82)
    fun u3 ⟨L3, rd3, wr3, cs3, R3, hF3, hh3, hr3⟩ => ?_)
  have hpl : ((List.range (D + 8)).map fun i => V (oMp + i)).length = D + 8 := by simp
  have hR3 := hr3 _ (hm2 ▸ hr1) (by rw [hsi2, hpl])
  rw [hm2] at hR3
  obtain ⟨V3, R3, hV3, -⟩ := VG.Proof.RsaOaep.X86_64.Rep.ex R3
  refine WP.seq (WP.mono (WP.here rfl hh3 (finSl_ok L3 R3 hD A.hsl (o := oDig) (by decide)))
    fun u4 ⟨⟨hdi4, hsi4, hdx4, hcx4, hm4, k4⟩, hh4⟩ => ?_)
  have L4 : Lay u4 F S := L3.congr (k4.gpr (by decide)) k4.2.2 (by rw [hm4])
  have R4 : Rep u4.mem F S V3 W := hm4 ▸ R3
  refine WP.mono (finF_ok hT hF hh4 L4 R4 (j := 45) rfl (by decide) hfn.2.2 (o := oDig)
    (Or.inr (by unfold oSt oDig oW; omega)) hdi4 hdx4 hcx4) fun u5 ⟨L5, rd5, wr5, cs5, R5, hh5, hr5⟩ => ?_
  have hsb : (Spec.Rsa.bytesAt u1.mem q sl).length = sl := by simp [Spec.Rsa.bytesAt]
  have hdig := hr5 _ (hm4 ▸ hR3) (by rw [List.length_append, hpl, hsb]; omega)
    (by rw [hsi4, List.length_append, hpl, hsb])
  have hsalt : Spec.Rsa.bytesAt u1.mem q sl = Spec.Rsa.bytesAt e.mem q sl := by
    simp only [Spec.Rsa.bytesAt]
    exact List.map_congr_left fun i hi => by
      have := List.mem_range.mp hi
      exact hh1.world.mem _ (hsW _ (Offset.contains_base q (d := i) (n := 1) (by omega) (by omega)))
  obtain ⟨V5, R5, hV5, hV5'⟩ := VG.Proof.RsaOaep.X86_64.Rep.ex R5
  refine ⟨L5, hh5, rd5.trans (k4.2.1.trans (rd3.trans (k2.2.1.trans rd1))),
    wr5.trans (k4.2.2.trans (wr3.trans (k2.2.2.trans wr1))), fun r hr => ?_, V5, R5, fun x hx => ?_,
    fun i hi => ?_⟩
  · rw [cs5 r hr, keep_cs' k4 (cs_disj _ (by decide)) r hr, cs3 r hr, keep_cs' k2 (cs_disj _ (by decide)) r hr,
      cs1 r hr]
  · simp only [mR, inR_cons, inR_nil, or_false] at hx
    rw [hV5 _ (by simp only [inR_cons, inR_nil, or_false]; omega),
      hV3 _ (by simp only [inR_cons, inR_nil, or_false]; omega),
      hV1 _ (by simp only [hR, inR_cons, inR_nil, or_false]; omega)]
  · rw [hV5' _ (by simp only [inR_cons, inR_nil, or_false]; omega), hdig i hi, hHh, hsalt]

end VG.Proof.RsaPss.X86_64
