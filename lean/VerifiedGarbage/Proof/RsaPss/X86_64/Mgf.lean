module

public import VerifiedGarbage.Proof.RsaPss.X86_64.StreamCalls
public import VerifiedGarbage.Proof.RsaPss.X86_64.TabCall
public import VerifiedGarbage.Proof.RsaPss.X86_64.Loops
public import VerifiedGarbage.Proof.RsaPss.X86_64.CtHashOk
public import VerifiedGarbage.Proof.Mgf1.Basic
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# RSASSA-PSS on x86-64: MGF1

`mgfXor H g` XORs `MGF1(H, dbLen)` into `DB`, the `dbLen` bytes at
`scratch + e`, where `H` is the `hLen` bytes after them (`mgfXor_ok`), with
the streaming functions of the hash function `G` of the table of `Hash`
whose words are in the frame's slots (`GT`): `mgfSeed` puts the seed's
address and length in the slots `sB` and `sFb`, and for each counter `c`
(`round_ok`) the state at `scratch + oSt` is set by `init`, `update` absorbs
the seed and then `I2OSP(c, 4)` (written to `scratch + oLen`, `updCtr_ok`),
`finalize` writes the digest to `scratch + oDig`, and its first
`min(hLen, dbLen - c hLen)` bytes are XORed into `DB` at `c hLen`
(`xorOut_ok`). Each call is through its slot (`scall_ok`), as the call of
`G`'s function (`initS_ok`, `updS_ok`, `finS_ok`, from `StreamCalls.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Bignum (off word off_off)
open VG.Impl.Pbkdf2.Md.X86_64 (Stream Hash)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (StreamOK)
open VG.Impl.Mgf1.X86_64.Table (Fns)

theorem ea_msp (t : State) (d : Nat) : t.ea (Impl.Mgf1.X86_64.sp d) = off (t.gpr .rsp) d := ea_sp t d

theorem ea_mat (t : State) (b : Reg) (d : Nat) : t.ea (Impl.Mgf1.X86_64.at_ b d) = off (t.gpr b) d := ea_at t b d

/-! ## Where MGF1 works -/

/-- Where `DB` and `H` are: `DB` the `db` bytes at `scratch + e`, `H` the
`hLen` after them, within `EM`'s place. -/
structure DbAt (D e db : Nat) : Prop where
  e1 : oEm ≤ e
  db1 : 1 ≤ db
  fit : e + db + D ≤ oEm + 1024

/-- `DB` with the first `n` bytes of the mask `mk` XORed in. -/
def mixV (V : Nat → Byte) (mk : List Byte) (e n : Nat) (o : Nat) : Byte :=
  if e ≤ o ∧ o < e + n then V o ^^^ mk.getD (o - e) 0 else V o

theorem map_range_getD {f : Nat → Byte} {n : Nat} {xs : List Byte} (h : (List.range n).map f = xs) {j : Nat}
    (hj : j < n) : f j = xs.getD j 0 := by
  subst h
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
  rfl

/-- A slot, read through `Rep`. -/
theorem Rep.slot {m : Mem} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep m F S V W) {d k : Nat}
    (hd : d = 8 * k) (hk : k < nW) {v : BitVec 64} (hv : W k = v) : m.readW (off F d) 64 = v := by
  rw [← hv, R.rd k hd hk]

/-- The view of memory after a call, as a function of its own. -/
theorem Rep.ex {m : Mem} {F S : Addr} {p : Nat → Prop} [DecidablePred p] {f V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep m F S (fun o => if p o then f o else V o) W) :
    ∃ V', Rep m F S V' W ∧ (∀ o, ¬ p o → V' o = V o) ∧ (∀ o, p o → V' o = f o) :=
  ⟨_, R, fun _ h => ifn h _ _, fun _ h => ifp h _ _⟩

theorem repr_congr {R : Mem → Addr → List Byte → Prop} {m : Mem} {p : Addr} {a b : List Byte} (h : a = b)
    (hr : R m p a) : R m p b := h ▸ hr

theorem keep_cs {u v : State} {rs : List Reg} (k : Keep rs u v)
    (h : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], r ∉ rs) : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], v.gpr r = u.gpr r :=
  fun r hr => k.gpr (h r hr)

theorem keep_cs' {u v : State} {rs : List Reg} (k : Keep rs u v)
    (h : ∀ r ∈ calleeSaved, r ∉ rs) : ∀ r ∈ calleeSaved, v.gpr r = u.gpr r :=
  fun r hr => k.gpr (h r hr)

theorem cs_disj (rs : List Reg) (h : rs.all (fun r => !calleeSaved.contains r) = true) :
    ∀ r ∈ calleeSaved, r ∉ rs := fun r hr hr' => by
  have := List.all_eq_true.mp h r hr'
  simp only [Bool.not_eq_true'] at this
  simp_all

theorem GT.sy {G : Stream} {g : Fns} {W : Nat → BitVec 64} {sy sy' : String → Addr} (T : GT G g W sy)
    (h : sy' = sy) : GT G g W sy' :=
  T.congr h fun _ _ _ => rfl

/-! ## The arguments of the calls -/

theorem updSrc_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {src srcLen : Nat} (hsrc : W 29 = off S src) (hsl : W 30 = BitVec.ofNat 64 srcLen) :
    WP isa (.block (Impl.Mgf1.X86_64.updSrcArgs mgfLay)) u fun u' => u'.gpr .rdi = off S oSt ∧
      u'.gpr .rsi = BitVec.ofNat 64 0 ∧ u'.gpr .rdx = off S src ∧ u'.gpr .rcx = BitVec.ofNat 64 srcLen ∧
      u'.gpr .r8 = off S oCW ∧ u'.mem = u.mem ∧ Keep [.rdi, .rsi, .rdx, .rcx, .r8] u u' := by
  have hs := L.slot
  simp only [Bignum.word] at hs
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .rcx, .r8] (Q := fun u' => u'.gpr .rdi = off S oSt ∧
      u'.gpr .rsi = BitVec.ofNat 64 0 ∧ u'.gpr .rdx = off S src ∧ u'.gpr .rcx = BitVec.ofNat 64 srcLen ∧
      u'.gpr .r8 = off S oCW ∧ u'.mem = u.mem) ?_ rfl) fun u' ⟨⟨a, b, c, d, e, f⟩, k⟩ => ⟨a, b, c, d, e, f, k⟩
  xrun [Impl.Mgf1.X86_64.updSrcArgs, Impl.Mgf1.X86_64.scr, mgfLay, List.cons_append, List.nil_append, ea_msp,
    L.rsp, L.ld (d := sScr) (by decide), L.ld (d := sB) (by decide), L.ld (d := sFb) (by decide), hs,
    R.slot (d := sB) (k := 29) rfl (by decide) hsrc, R.slot (d := sFb) (k := 30) rfl (by decide) hsl,
    VG.Proof.MlKem.X86_64.sx_ofNat (show oSt < 2 ^ 31 by decide),
    VG.Proof.MlKem.X86_64.sx_ofNat (show oCW < 2 ^ 31 by decide)]

/-- `I2OSP(c, 4)` at `scratch + oLen`. -/
def ctrB (V : Nat → Byte) (c : Nat) (x : Nat) : Byte :=
  if oLen ≤ x ∧ x < oLen + 4 then (Spec.Rsa.i2osp c 4).getD (x - oLen) 0 else V x

theorem trunc_ofNat (x : Nat) : BitVec.setWidth 8 (BitVec.ofNat 64 x) = BitVec.ofNat 8 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_mod_of_dvd _ (by decide)]

theorem updCtr_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {srcLen c : Nat} (hl : W 30 = BitVec.ofNat 64 srcLen) (hc : W 31 = BitVec.ofNat 64 c)
    (hc32 : c < 2 ^ 32) :
    WP isa (.block (Impl.Mgf1.X86_64.updCtrArgs mgfLay)) u fun u' => Lay u' F S ∧ u'.gpr .rdi = off S oSt ∧
      u'.gpr .rsi = BitVec.ofNat 64 srcLen ∧ u'.gpr .rdx = off S oLen ∧ u'.gpr .rcx = BitVec.ofNat 64 4 ∧
      u'.gpr .r8 = off S oCW ∧ Keep [.rdi, .rsi, .rdx, .rcx, .r8, .rax] u u' ∧ Rep u'.mem F S (ctrB V c) W := by
  have hs := L.slot
  simp only [Bignum.word] at hs
  have G' := L.geo
  have R1 := (((R.wb G' (o := oLen + 3) (by decide) (BitVec.ofNat 8 c)).wb G'
    (o := oLen + 2) (by decide) (BitVec.ofNat 8 (c / 2 ^ 8))).wb G'
    (o := oLen + 1) (by decide) (BitVec.ofNat 8 (c / 2 ^ 8 / 2 ^ 8))).wb G'
    (o := oLen) (by decide) (BitVec.ofNat 8 (c / 2 ^ 8 / 2 ^ 8 / 2 ^ 8))
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .rcx, .r8, .rax] (Q := fun u' => u'.gpr .rdi = off S oSt ∧
      u'.gpr .rsi = BitVec.ofNat 64 srcLen ∧ u'.gpr .rdx = off S oLen ∧ u'.gpr .rcx = BitVec.ofNat 64 4 ∧
      u'.gpr .r8 = off S oCW ∧ u'.mem =
      (((u.mem.writeW (off S (oLen + 3)) (BitVec.ofNat 8 c)).writeW (off S (oLen + 2))
        (BitVec.ofNat 8 (c / 2 ^ 8))).writeW (off S (oLen + 1)) (BitVec.ofNat 8 (c / 2 ^ 8 / 2 ^ 8))).writeW
        (off S oLen) (BitVec.ofNat 8 (c / 2 ^ 8 / 2 ^ 8 / 2 ^ 8))) ?_ rfl)
    fun u' ⟨⟨h₁, h₂, h₃, h₄, h₅, hm⟩, hk⟩ => ⟨?_, h₁, h₂, h₃, h₄, h₅, hk, hm ▸ ?_⟩
  · xrun [Impl.Mgf1.X86_64.updCtrArgs, Impl.Mgf1.X86_64.scr, mgfLay, List.cons_append, List.nil_append, ea_mat,
      ea_msp, L.rsp, L.ld (d := sScr) (by decide), L.ld (d := sCtr) (by decide), L.ld (d := sFb) (by decide), hs,
      R.slot (d := sCtr) (k := 31) rfl (by decide) hc, off_off,
      VG.Proof.MlKem.X86_64.sx_ofNat (show oSt < 2 ^ 31 by decide),
      VG.Proof.MlKem.X86_64.sx_ofNat (show oLen < 2 ^ 31 by decide),
      VG.Proof.MlKem.X86_64.sx_ofNat (show oCW < 2 ^ 31 by decide),
      L.sst8 (d := oLen + 3) (by decide), L.sst8 (d := oLen + 2) (by decide), L.sst8 (d := oLen + 1) (by decide),
      L.sst8 (d := oLen) (by decide), trunc_ofNat, shr_ofNat 8 (show c < 2 ^ 64 by omega_using [hc32]),
      shr_ofNat 8 (show c / 2 ^ 8 < 2 ^ 64 by omega_using [hc32]),
      shr_ofNat 8 (show c / 2 ^ 8 / 2 ^ 8 < 2 ^ 64 by omega_using [hc32]),
      zx32 (show 4 < 2 ^ 32 by omega_using []), show off S oLen + 0 = off S oLen from BitVec.add_zero _]
    have w21 : W 21 = S := (R.rd 21 rfl (by decide)).symm.trans hs
    simp only [show S + BitVec.ofNat 64 oLen = off S oLen from rfl, R1.slot (d := sScr) (k := 21) rfl (by decide) w21,
      R1.slot (d := sFb) (k := 30) rfl (by decide) hl]
    exact ⟨trivial, trivial, trivial⟩
  · exact L.congr (hk.gpr (by decide)) hk.2.2 (by
      rw [hm, slot_eq sScr 21 rfl, slot_eq sScr 21 rfl, R1.fr 21 (by decide), R.fr 21 (by decide)])
  · refine (congrArg (fun V' => Rep _ F S V' _) (funext fun x => ?_)).mp R1
    have e1 : c / 2 ^ 8 / 2 ^ 8 / 2 ^ 8 = c / 256 ^ 3 := by
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
    have e2 : c / 2 ^ 8 / 2 ^ 8 = c / 256 ^ 2 := by rw [Nat.div_div_eq_div_mul]
    have e3 : c / 2 ^ 8 = c / 256 ^ 1 := rfl
    simp only [upd, ctrB, Spec.Rsa.i2osp, List.getD_eq_getElem?_getD, List.getElem?_map]
    rcases (show x = oLen ∨ x = oLen + 1 ∨ x = oLen + 2 ∨ x = oLen + 3 ∨
        ¬(oLen ≤ x ∧ x < oLen + 4) by omega_using []) with h | h | h | h | h
    · subst h; simp [e1]
    · subst h; simp [e2]
    · subst h; simp [e3]
    · subst h; simp
    · rw [ifn h, ifn (by omega_using [h]), ifn (by omega_using [h]), ifn (by omega_using [h]),
        ifn (by omega_using [h])]

theorem finA_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {srcLen : Nat} (hl : W 30 = BitVec.ofNat 64 srcLen) :
    WP isa (.block (Impl.Mgf1.X86_64.finArgs mgfLay)) u fun u' => u'.gpr .rdi = off S oSt ∧
      u'.gpr .rsi = BitVec.ofNat 64 (srcLen + 4) ∧ u'.gpr .rdx = off S oDig ∧ u'.gpr .rcx = off S oCW ∧
      u'.mem = u.mem ∧ Keep [.rdi, .rsi, .rdx, .rcx] u u' := by
  have hs := L.slot
  simp only [Bignum.word] at hs
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .rcx] (Q := fun u' => u'.gpr .rdi = off S oSt ∧
      u'.gpr .rsi = BitVec.ofNat 64 (srcLen + 4) ∧ u'.gpr .rdx = off S oDig ∧ u'.gpr .rcx = off S oCW ∧
      u'.mem = u.mem) ?_ rfl) fun u' ⟨⟨a, b, c, d, e⟩, k⟩ => ⟨a, b, c, d, e, k⟩
  xrun [Impl.Mgf1.X86_64.finArgs, Impl.Mgf1.X86_64.scr, mgfLay, List.cons_append, List.nil_append, ea_msp, L.rsp,
    L.ld (d := sScr) (by decide), L.ld (d := sFb) (by decide), hs,
    R.slot (d := sFb) (k := 30) rfl (by decide) hl, ofNat_add_lit,
    VG.Proof.MlKem.X86_64.sx_ofNat (show oSt < 2 ^ 31 by decide),
    VG.Proof.MlKem.X86_64.sx_ofNat (show oDig < 2 ^ 31 by decide),
    VG.Proof.MlKem.X86_64.sx_ofNat (show oCW < 2 ^ 31 by decide)]

/-! ## The calls -/

variable {G : Stream} (hG : StreamOK G) {g : Fns}

include hG in
theorem initS_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) (T : GT G g W t.syms) (hdi : t.gpr .rdi = off S oSt) :
    WP isa (scall sIniG g.init) t fun t' => Lay t' F S ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧
      Rep t'.mem F S (fun o => if inR [(oSt, G.S)] o then t'.mem (off S o) else V o) W ∧
      hG.SH.Repr t'.mem (off S oSt) [] :=
  scall_ok L R (k := 11) rfl (by decide) (by decide) T.wi T.fi fun _ k hm _ =>
    WP.mono (init_ok hG (lay_keep11 L k hm) (hm ▸ R) ((k.gpr (by decide)).trans hdi))
      fun _ ⟨L', rd', wr', cs', R', _, hr'⟩ => ⟨L', rd'.trans k.2.1, wr'.trans k.2.2,
        fun r hr => (cs' r hr).trans (cs_keep11 k r hr), R', hr'⟩

include hG in
theorem updS_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) (T : GT G g W t.syms) {a len : Nat} (ha : a + len ≤ oRsa)
    (hda : a + len ≤ oSt ∨ oSt + G.S ≤ a) (hwa : a + len ≤ oCW ∨ oCW + hG.Wb ≤ a)
    (hdi : t.gpr .rdi = off S oSt) (hdx : t.gpr .rdx = off S a) (hcx : t.gpr .rcx = BitVec.ofNat 64 len)
    (h8 : t.gpr .r8 = off S oCW) :
    WP isa (scall sUpdG g.upd) t fun t' => Lay t' F S ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧
      Rep t'.mem F S (fun o => if inR [(oSt, G.S), (oCW, hG.Wb)] o then t'.mem (off S o) else V o) W ∧
      (∀ m, hG.SH.Repr t.mem (off S oSt) m → t.gpr .rsi = BitVec.ofNat 64 m.length →
        hG.SH.Repr t'.mem (off S oSt) (m ++ (List.range len).map fun i => V (a + i))) :=
  scall_ok L R (k := 12) rfl (by decide) (by decide) T.wu T.fu fun _ k hm _ =>
    WP.mono (upd_ok hG (lay_keep11 L k hm) (hm ▸ R) ha hda hwa ((k.gpr (by decide)).trans hdi)
        ((k.gpr (by decide)).trans hdx) ((k.gpr (by decide)).trans hcx) ((k.gpr (by decide)).trans h8))
      fun _ ⟨L', rd', wr', cs', R', hr'⟩ => ⟨L', rd'.trans k.2.1, wr'.trans k.2.2,
        fun r hr => (cs' r hr).trans (cs_keep11 k r hr), R', fun m hm' hc =>
          hr' m (hm ▸ hm') ((k.gpr (by decide)).trans hc)⟩

include hG in
theorem finS_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) (T : GT G g W t.syms) {o : Nat} (ho : oSt + 256 ≤ o ∧ o + 64 ≤ oRsa)
    (hdi : t.gpr .rdi = off S oSt) (hdx : t.gpr .rdx = off S o) (hcx : t.gpr .rcx = off S oCW) :
    WP isa (scall sFinG g.fin) t fun t' => Lay t' F S ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧
      Rep t'.mem F S (fun x => if inR [(oSt, G.S), (o, G.F), (oCW, hG.Wb)] x then t'.mem (off S x) else V x) W ∧
      (∀ m, hG.SH.Repr t.mem (off S oSt) m → m.length < 2 ^ 64 → t.gpr .rsi = BitVec.ofNat 64 m.length →
        ∀ i < G.D, t'.mem (off S (o + i)) = (hG.SH.H.hash m).getD i 0) :=
  scall_ok L R (k := 13) rfl (by decide) (by decide) T.wf T.ff fun _ k hm _ =>
    WP.mono (fin_ok hG (lay_keep11 L k hm) (hm ▸ R) ho ((k.gpr (by decide)).trans hdi)
        ((k.gpr (by decide)).trans hdx) ((k.gpr (by decide)).trans hcx))
      fun _ ⟨L', rd', wr', cs', R', hr'⟩ => ⟨L', rd'.trans k.2.1, wr'.trans k.2.2,
        fun r hr => (cs' r hr).trans (cs_keep11 k r hr), R', fun m hm' hl hc =>
          hr' m (hm ▸ hm') hl ((k.gpr (by decide)).trans hc)⟩

/-! ## The digest into `DB` -/

omit hG in
theorem xorOut_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {dst dstLen done : Nat} (hd1 : oDig + 64 ≤ dst) (hd2 : dst + dstLen ≤ oRsa)
    (hD : 0 < G.D) (hDF : G.D ≤ 64) (h14 : W 14 = BitVec.ofNat 64 G.D)
    (he : W 23 = off S dst) (hdb : W 24 = BitVec.ofNat 64 dstLen) (hdn : W 32 = BitVec.ofNat 64 done)
    (hlt : done < dstLen) :
    WP isa (Impl.Mgf1.X86_64.Table.xorOut mgfLay sDG) u fun u' => Lay u' F S ∧
      Keep [.rcx, .rdi, .rax, .r10, .r8, .rdx] u u' ∧
      Rep u'.mem F S (xorV V oDig (dst + done) (min G.D (dstLen - done))) W := by
  have c3 : oDig = 2304 := rfl
  have c5 : oRsa = 8192 := rfl
  have hs := L.slot
  simp only [Bignum.word] at hs
  unfold Impl.Mgf1.X86_64.Table.xorOut Impl.Mgf1.X86_64.seqs Impl.Mgf1.X86_64.seqs Impl.Mgf1.X86_64.seqs
  refine WP.seq (WP.mono (WP.keep [.rcx, .rdi, .rax, .r10, .rdx] (Q := fun v => v.gpr .rcx = off S oDig ∧
      v.gpr .rdi = off S (dst + done) ∧ v.gpr .rax = BitVec.ofNat 64 (dstLen - done) ∧
      v.gpr .r10 = BitVec.ofNat 64 G.D ∧ v.cf = some (decide (dstLen - done < G.D)) ∧ v.mem = u.mem) ?_ rfl)
    fun v ⟨⟨h₁, h₂, h₃, h₄, h₅, hm⟩, hk⟩ => ?_)
  · xrun [Impl.Mgf1.X86_64.Table.xorHead, Impl.Mgf1.X86_64.scr, mgfLay, List.cons_append, List.nil_append,
      ea_msp, L.rsp, L.ld (d := sScr) (by decide), hs, VG.Proof.MlKem.X86_64.sx_ofNat (show oDig < 2 ^ 31 by decide),
      L.ld (d := sEb) (by decide), L.ld (d := sDone) (by decide), L.ld (d := sDb) (by decide),
      L.ld (d := sDG) (by decide), R.slot (d := sDG) (k := 14) rfl (by decide) h14,
      R.slot (d := sEb) (k := 23) rfl (by decide) he, R.slot (d := sDb) (k := 24) rfl (by decide) hdb,
      R.slot (d := sDone) (k := 32) rfl (by decide) hdn,
      VG.Offset.ofNat_sub_ofNat (show done ≤ dstLen by omega_using [hlt]), off_plus]
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hd2, c5]),
      Nat.mod_eq_of_lt (by omega_using [hDF])]
  have Lv : Lay v F S := L.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm])
  have Rv : Rep v.mem F S V W := hm ▸ R
  have hmin : 0 < min G.D (dstLen - done) := by omega_using [hD, hlt]
  refine WP.seq (WP.mono (Q := fun (w : State) => Keep [.r10] v w ∧ w.mem = v.mem ∧
      w.gpr .r10 = BitVec.ofNat 64 (min G.D (dstLen - done))) ?_ fun w ⟨kw, hmw, h10⟩ => ?_)
  · refine WP.ite (M := isa) _ (show isa.eval .b v = _ from h₅) (fun hb => ?_) (fun hb => ?_)
    · rw [decide_eq_true_eq] at hb
      refine WP.mono (WP.keep [.r10] (Q := fun w => w.mem = v.mem ∧ w.gpr .r10 = BitVec.ofNat 64 (dstLen - done))
        ?_ rfl) fun w ⟨⟨hm', h'⟩, k'⟩ => ⟨k', hm', by rw [h', Nat.min_eq_right (by omega_using [hb])]⟩
      xrun [h₃]
    · rw [decide_eq_false_iff_not] at hb
      refine WP.mono (WP.keep [] (Q := fun w => w = v) ?_ rfl) fun w ⟨hw, _⟩ => ?_
      · xrun
      · subst hw; exact ⟨Keep.refl _ _, rfl, by rw [h₄, Nat.min_eq_left (by omega_using [hb])]⟩
  have Lw : Lay w F S := Lv.congr (kw.gpr (by decide)) kw.2.2 (by rw [hmw])
  have Rw : Rep w.mem F S V W := hmw ▸ Rv
  refine WP.seq (WP.mono (WP.keep [.r8] (Q := fun x => x.gpr .r8 = BitVec.ofNat 64 0 ∧ x.mem = w.mem) ?_ rfl)
    fun x ⟨⟨h8, hmx⟩, kx⟩ => ?_)
  · xrun
  have Lx : Lay x F S := Lw.congr (kx.gpr (by decide)) kx.2.2 (by rw [hmx])
  have Rx : Rep x.mem F S V W := hmx ▸ Rw
  have kvx := kw.trans kx
  refine WP.mono (xor_ok Lx Rx (a := oDig) (b := dst + done) (n := min G.D (dstLen - done))
    (stepR_ok (by omega_using [hDF]) x (show Reg.r10 ∉ [Reg.rax, .rdx, .r8] by decide) (by decide)
      ((kx.gpr (by decide)).trans h10)) hmin (by omega_using [hDF, c3, c5])
      (by omega_using [hd2, hmin, hlt]) (by omega_using [hd1, c3, hDF, hmin])
    ((kvx.gpr (by decide)).trans h₁) ((kvx.gpr (by decide)).trans h₂) h8)
    fun y ⟨Ly, ky, Ry⟩ => ⟨Ly, ?_, Ry⟩
  exact (hk.trans (kvx.trans ky)).mono (by decide)

/-! ## The next counter -/

omit hG in
theorem nextCtr_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {c done dstLen : Nat} (hc : W 31 = BitVec.ofNat 64 c)
    (hdn : W 32 = BitVec.ofNat 64 done) (hdb : W 24 = BitVec.ofNat 64 dstLen) (h14 : W 14 = BitVec.ofNat 64 G.D)
    (hd' : done + G.D < 2 ^ 32) (hdb' : dstLen < 2 ^ 32) :
    WP isa (.block (Impl.Mgf1.X86_64.Table.nextCtr mgfLay sDG)) u fun u' => Lay u' F S ∧ Keep [.rax] u u' ∧
      u'.cf = some (decide (done + G.D < dstLen)) ∧
      Rep u'.mem F S V (upd (upd W 31 (BitVec.ofNat 64 (c + 1))) 32 (BitVec.ofNat 64 (done + G.D))) := by
  have G' := L.geo
  have R1 := R.wf G' (k := 31) (by decide) (BitVec.ofNat 64 (c + 1))
  have R2 := R1.wf G' (k := 32) (by decide) (BitVec.ofNat 64 (done + G.D))
  rw [show off F (8 * 31) = off F sCtr from rfl] at R1 R2
  rw [show off F (8 * 32) = off F sDone from rfl] at R2
  have h32 : (u.mem.writeW (off F sCtr) (BitVec.ofNat 64 (c + 1))).readW (off F sDone) 64 =
      BitVec.ofNat 64 done := by
    have := R1.fr 32 (by decide); simp only [upd, Nat.reduceEqDiff, ite_false] at this; rw [← hdn, ← this]; rfl
  have h14' : (u.mem.writeW (off F sCtr) (BitVec.ofNat 64 (c + 1))).readW (off F sDG) 64 =
      BitVec.ofNat 64 G.D := by
    have := R1.fr 14 (by decide); simp only [upd, Nat.reduceEqDiff, ite_false] at this; rw [← h14, ← this]; rfl
  have h24 : ((u.mem.writeW (off F sCtr) (BitVec.ofNat 64 (c + 1))).writeW (off F sDone)
      (BitVec.ofNat 64 (done + G.D))).readW (off F sDb) 64 = BitVec.ofNat 64 dstLen := by
    have := R2.fr 24 (by decide); simp only [upd, Nat.reduceEqDiff, ite_false] at this; rw [← hdb, ← this]; rfl
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.cf = some (decide (done + G.D < dstLen)) ∧ u'.mem =
      (u.mem.writeW (off F sCtr) (BitVec.ofNat 64 (c + 1))).writeW (off F sDone) (BitVec.ofNat 64 (done + G.D)))
      ?_ rfl) fun u' ⟨⟨hcf, hm⟩, hk⟩ => ⟨?_, hk, hcf, hm ▸ R2⟩
  · xrun [Impl.Mgf1.X86_64.Table.nextCtr, mgfLay, ea_msp, L.rsp, L.ld (d := sCtr) (by decide),
      L.ld (d := sDone) (by decide), L.ld (d := sDG) (by decide),
      L.ld (d := sDb) (by decide), L.st (d := sCtr) (by decide), L.st (d := sDone) (by decide),
      R.slot (d := sCtr) (k := 31) rfl (by decide) hc, h32, h14', h24,
      ofNat_add_lit, BitVec.ofNat_add_ofNat]
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hd']),
      Nat.mod_eq_of_lt (by omega_using [hdb'])]
  · refine L.congr (hk.gpr (by decide)) hk.2.2 ?_
    have h1 := R2.fr 21 (by decide)
    rw [← hm] at h1
    rw [slot_eq sScr 21 rfl, slot_eq sScr 21 rfl, h1, R.fr 21 (by decide)]
    simp [upd]

/-! ## One counter -/

/-- The loop's invariant after `c` counters. -/
structure MgfI (u₀ : State) (F S : Addr) (V : Nat → Byte) (W : Nat → BitVec 64) (mk : List Byte)
    (e db D c : Nat) (v : State) : Prop where
  L : Lay v F S
  rd : v.rd = u₀.rd
  wr : v.wr = u₀.wr
  cs : ∀ r ∈ calleeSaved, v.gpr r = u₀.gpr r
  sy : v.syms = u₀.syms
  rep : ∃ V' W', Rep v.mem F S V' W' ∧ W' 31 = BitVec.ofNat 64 c ∧ W' 32 = BitVec.ofNat 64 (c * D) ∧
    (∀ k < nW, k ≠ 31 → k ≠ 32 → W' k = W k) ∧
    ∀ o < oRsa, ctOut o → V' o = mixV V mk e (min (c * D) db) o

include hG in
theorem round_ok {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D)
    (hGv : Proof.Mgf1.Valid Gs) {D : Nat} {u₀ : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    {e db c : Nat} (hd : DbAt D e db) (he : W 23 = off S e) (hdb : W 24 = BitVec.ofNat 64 db)
    (hsrc : W 29 = off S (e + db)) (hsl : W 30 = BitVec.ofNat 64 D) (T : GT G g W u₀.syms)
    {v : State} (I : MgfI u₀ F S V W (Spec.Mgf1.mgf1 Gs ((List.range D).map fun i => V (e + db + i)) db)
      e db G.D c v) (hc : c * G.D < db) :
    WP isa (mgfRound g) v fun v' => v'.cf = some (decide ((c + 1) * G.D < db)) ∧
      MgfI u₀ F S V W (Spec.Mgf1.mgf1 Gs ((List.range D).map fun i => V (e + db + i)) db) e db G.D (c + 1) v' := by
  obtain ⟨hzS, hzF, hzW, hzDF, hzD⟩ := sizes hG
  have c1 : oSt = 2048 := rfl
  have c2 : oDig = 2304 := rfl
  have c3 : oLen = 2368 := rfl
  have c4 : oCW = 0 := rfl
  have c5 : oRsa = 8192 := rfl
  have c6 : oEm = 2560 := rfl
  have c7 : oY = 3584 := rfl
  have he1 := hd.e1
  have hfit := hd.fit
  have hcD : c ≤ c * G.D := Nat.le_mul_of_pos_right c hzD
  obtain ⟨V1, W1, R1, h31, h32, hW, hV⟩ := I.rep
  have w14 : W1 14 = BitVec.ofNat 64 G.D := (hW 14 (by decide) (by decide) (by decide)).trans T.wd
  have w23 : W1 23 = off S e := (hW 23 (by decide) (by decide) (by decide)).trans he
  have w24 : W1 24 = BitVec.ofNat 64 db := (hW 24 (by decide) (by decide) (by decide)).trans hdb
  have w29 : W1 29 = off S (e + db) := (hW 29 (by decide) (by decide) (by decide)).trans hsrc
  have w30 : W1 30 = BitVec.ofNat 64 D := (hW 30 (by decide) (by decide) (by decide)).trans hsl
  have T1 : GT G g W1 v.syms := T.congr I.sy fun k h1 h2 =>
    hW k (by unfold nW frameBytes; omega_using [h2]) (by omega_using [h2]) (by omega_using [h2])
  have hsrc1 : ∀ i < D, V1 (e + db + i) = V (e + db + i) := fun i hi => by
    rw [hV _ (by omega_using [hfit, c5, c6, hi]) ⟨by omega_using [he1, c3, c6], by omega_using [hfit, c6, c7, hi]⟩,
      mixV, ifn (by omega_using [])]
  unfold mgfRound seqs seqs seqs seqs seqs seqs seqs seqs seqs
  -- `init`.
  refine WP.seq (X86_64.WP.mono_syms (scr_ok I.L (d := .rdi) (by decide) (o := oSt) (by decide))
    fun u1 ⟨hdi1, hm1, k1⟩ s1 => ?_)
  have L1 : Lay u1 F S := I.L.congr (k1.gpr (by decide)) k1.2.2 (by rw [hm1])
  have R1' : Rep u1.mem F S V1 W1 := hm1 ▸ R1
  refine WP.seq (X86_64.WP.mono_syms (initS_ok hG L1 R1' (T1.sy s1) hdi1)
    fun u2 ⟨L2, rd2, wr2, cs2, R2, hr2⟩ s2 => ?_)
  obtain ⟨V2, R2, hV2, -⟩ := Rep.ex R2
  -- `update` with the seed.
  refine WP.seq (X86_64.WP.mono_syms (updSrc_ok L2 R2 w29 w30)
    fun u3 ⟨hdi3, hsi3, hdx3, hcx3, h83, hm3, k3⟩ s3 => ?_)
  have L3 : Lay u3 F S := L2.congr (k3.gpr (by decide)) k3.2.2 (by rw [hm3])
  have R3 : Rep u3.mem F S V2 W1 := hm3 ▸ R2
  have hr3 : hG.SH.Repr u3.mem (off S oSt) [] := hm3 ▸ hr2
  refine WP.seq (X86_64.WP.mono_syms (updS_ok hG L3 R3 (T1.sy (s3.trans (s2.trans s1))) (a := e + db) (len := D)
      (by omega_using [hfit, c5, c6]) (Or.inr (by omega_using [hzS, c1, c6, he1]))
      (Or.inr (by omega_using [hzW, c4, c6, he1])) hdi3 hdx3 hcx3 h83)
    fun u4 ⟨L4, rd4, wr4, cs4, R4, hr4⟩ s4 => ?_)
  have hR4 := hr4 [] hr3 (by rw [hsi3]; rfl)
  obtain ⟨V4, R4, hV4, hV4'⟩ := Rep.ex R4
  -- The counter, and `update` with it.
  refine WP.seq (X86_64.WP.mono_syms (updCtr_ok L4 R4 w30 h31 (by omega_using [hc, hfit, he1, c6, hcD]))
    fun u5 ⟨L5, hdi5, hsi5, hdx5, hcx5, h85, k5, R5⟩ s5 => ?_)
  have hst5 : ∀ i < G.S, u5.mem (off S oSt + BitVec.ofNat 64 i) = u4.mem (off S oSt + BitVec.ofNat 64 i) :=
    fun i hi => by
      rw [off_plus, R5.scr _ (by omega_using [hzS, c1, c5, hi]), R4.scr _ (by omega_using [hzS, c1, c5, hi]), ctrB,
          ifn (by omega_using [hzS, c1, c3, hi])]
  have hR5 := hG.repr _ _ _ _ _ hst5 hR4
  refine WP.seq (X86_64.WP.mono_syms (updS_ok hG L5 R5 (T1.sy (s5.trans (s4.trans (s3.trans (s2.trans s1)))))
      (a := oLen) (len := 4) (by omega_using [c3, c5]) (Or.inr (by omega_using [hzS, c1, c3]))
      (Or.inr (by omega_using [hzW, c3, c4])) hdi5 hdx5 hcx5 h85)
    fun u6 ⟨L6, rd6, wr6, cs6, R6, hr6⟩ s6 => ?_)
  have hR6 : hG.SH.Repr u6.mem (off S oSt) (((List.range D).map fun i => V (e + db + i)) ++ Spec.Rsa.i2osp c 4) :=
    repr_congr ?msg (hr6 _ hR5 (by rw [hsi5, List.nil_append, List.length_map, List.length_range]))
  case msg =>
    rw [List.nil_append]
    refine (congrArg (· ++ _) ?_).trans (congrArg (_ ++ ·) ?_)
    · refine List.map_congr_left fun i hi => ?_
      have := List.mem_range.mp hi
      rw [hV2 _ (by simp only [inR_cons, inR_nil, or_false]; omega_using [hzS, c1, c6, he1, this]), hsrc1 i this]
    · refine (List.map_congr_left fun i hi => ?_).trans ((range_map_getD (n := 4) (xs := Spec.Rsa.i2osp c 4)
        (by rw [Proof.Mgf1.i2osp_length])).trans (List.take_of_length_le (by rw [Proof.Mgf1.i2osp_length])))
      have := List.mem_range.mp hi
      rw [ctrB, ifp (by omega_using [this]), Nat.add_sub_cancel_left]
  obtain ⟨V6, R6, hV6, -⟩ := Rep.ex R6
  -- `finalize`.
  refine WP.seq (X86_64.WP.mono_syms (finA_ok L6 R6 w30)
    fun u7 ⟨hdi7, hsi7, hdx7, hcx7, hm7, k7⟩ s7 => ?_)
  have L7 : Lay u7 F S := L6.congr (k7.gpr (by decide)) k7.2.2 (by rw [hm7])
  have R7 : Rep u7.mem F S V6 W1 := hm7 ▸ R6
  have hR7 : hG.SH.Repr u7.mem (off S oSt) (((List.range D).map fun i => V (e + db + i)) ++ Spec.Rsa.i2osp c 4) :=
    hm7 ▸ hR6
  have sy7 : u7.syms = v.syms := s7.trans (s6.trans (s5.trans (s4.trans (s3.trans (s2.trans s1)))))
  refine WP.seq (X86_64.WP.mono_syms (finS_ok hG L7 R7 (T1.sy sy7) (o := oDig)
      ⟨by omega_using [c1, c2], by omega_using [c2, c5]⟩ hdi7 hdx7 hcx7)
    fun u8 ⟨L8, rd8, wr8, cs8, R8, hr8⟩ s8 => ?_)
  have hml : (((List.range D).map fun i => V (e + db + i)) ++ Spec.Rsa.i2osp c 4).length = D + 4 := by
    rw [List.length_append, List.length_map, List.length_range, Proof.Mgf1.i2osp_length]
  have hdig := hr8 _ hR7 (by rw [hml]; omega_using [hfit, c6]) (by rw [hsi7, hml])
  obtain ⟨V8, R8, hV8, hV8'⟩ := Rep.ex R8
  -- Into `DB`.
  refine WP.seq (X86_64.WP.mono_syms (xorOut_ok (G := G) L8 R8 (dst := e) (dstLen := db) (done := c * G.D)
      (by omega_using [he1, c2, c6]) (by omega_using [hfit, c5, c6]) hzD (by omega_using [hzF, hzDF]) w14 w23 w24
      h32 hc)
    fun u9 ⟨L9, k9, R9⟩ s9 => ?_)
  -- The next counter.
  refine X86_64.WP.mono_syms (nextCtr_ok (G := G) L9 R9 h31 h32 w24 w14
      (by omega_using [hzF, hzDF, hfit, he1, c6, hc]) (by omega_using [hfit, he1, c6]))
    fun u10 ⟨L10, k10, cf10, R10⟩ s10 => ?_
  have hs1 : (c + 1) * G.D = c * G.D + G.D := Nat.succ_mul _ _
  refine ⟨by rw [cf10, hs1], L10, ?_, ?_, ?_, ?_, _, _, R10, by simp [upd], by simp [upd, hs1], ?_, ?_⟩
  · rw [k10.2.1, k9.2.1, rd8, k7.2.1, rd6, k5.2.1, rd4, k3.2.1, rd2, k1.2.1, I.rd]
  · rw [k10.2.2, k9.2.2, wr8, k7.2.2, wr6, k5.2.2, wr4, k3.2.2, wr2, k1.2.2, I.wr]
  · intro r hr
    rw [keep_cs' k10 (cs_disj _ (by decide)) r hr, keep_cs' k9 (cs_disj _ (by decide)) r hr, cs8 r hr,
      keep_cs' k7 (cs_disj _ (by decide)) r hr, cs6 r hr, keep_cs' k5 (cs_disj _ (by decide)) r hr, cs4 r hr,
      keep_cs' k3 (cs_disj _ (by decide)) r hr, cs2 r hr, keep_cs' k1 (cs_disj _ (by decide)) r hr, I.cs r hr]
  · exact s10.trans (s9.trans (s8.trans (sy7.trans I.sy)))
  · intro k hk h1 h2
    simp only [upd, ifn h2, ifn h1]
    exact hW k hk h1 h2
  · intro o ho hco
    have hold : ∀ x, ctOut x → V8 x = V1 x := by
      intro x hx
      have := hx.1
      rw [hV8 _ (by simp only [inR_cons, inR_nil, or_false]; omega_using [hzS, hzF, hzW, c1, c2, c3, c4, this]),
        hV6 _ (by simp only [inR_cons, inR_nil, or_false]; omega_using [hzS, hzW, c1, c3, c4, this]), ctrB,
        ifn (by omega_using [c3, this]),
        hV4 _ (by simp only [inR_cons, inR_nil, or_false]; omega_using [hzS, hzW, c1, c3, c4, this]),
        hV2 _ (by simp only [inR_cons, inR_nil, or_false]; omega_using [hzS, c1, c3, this])]
    have hdg : ∀ j < G.D, V8 (oDig + j) =
        (Gs.hash (((List.range D).map fun i => V (e + db + i)) ++ Spec.Rsa.i2osp c 4)).getD j 0 :=
      fun j hj => by
        rw [hV8' _ (by simp only [inR_cons, inR_nil, or_false]; omega_using [hzDF, hj]), hdig j hj, hGh]
    simp only [xorV]
    by_cases hx : e + c * G.D ≤ o ∧ o < e + c * G.D + min G.D (db - c * G.D)
    · have hq : (o - e) / G.D = c :=
        Nat.div_eq_of_lt_le (by omega_using [hx]) (by omega_using [hs1, hx])
      have hr : (o - e) % G.D = o - (e + c * G.D) := by
        rw [Nat.mod_eq_sub_mul_div, hq, Nat.mul_comm]; omega_using []
      rw [ifp hx, hold o hco, hV o ho hco, mixV, mixV,
        ifn (show ¬ (e ≤ o ∧ o < e + min (c * G.D) db) by omega_using [hx]),
        ifp (show e ≤ o ∧ o < e + min ((c + 1) * G.D) db by omega_using [hs1, hx]), hdg _ (by omega_using [hx]),
        Proof.Mgf1.mgf1_getD hGv _ (show o - e < db by omega_using [hx]), hGl, hq, hr]
    · rw [ifn hx, hold o hco, hV o ho hco, mixV, mixV]
      by_cases hy : e ≤ o ∧ o < e + min (c * G.D) db
      · rw [ifp hy, ifp (by omega_using [hs1, hy])]
      · rw [ifn hy, ifn (by omega_using [hs1, hx, hy])]

/-! ## MGF1 -/

/-- The seed's address and length to the slots `sB` and `sFb`, and the
counter and `done` set to 0. -/
theorem mgfHead_ok (H : Hash) {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {e db : Nat} (hd : DbAt H.D e db) (he : W 23 = off S e)
    (hdb : W 24 = BitVec.ofNat 64 db) :
    WP isa (.block (mgfSeed H ++ [.mov32 .rax (.imm 0), .store (sp sCtr) .rax, .store (sp sDone) .rax])) u
      fun v => Lay v F S ∧ Keep [.rax] u v ∧ Rep v.mem F S V
        (upd (upd (upd (upd W 29 (off S (e + db))) 30 (BitVec.ofNat 64 H.D)) 31 0#64) 32 0#64) := by
  have G' := L.geo
  have hfit := hd.fit
  have he1 := hd.e1
  have R4 := (((R.wf G' (k := 29) (by decide) (off S (e + db))).wf G' (k := 30) (by decide)
    (BitVec.ofNat 64 H.D)).wf G' (k := 31) (by decide) 0#64).wf G' (k := 32) (by decide) 0#64
  rw [show off F (8 * 29) = off F sB from rfl, show off F (8 * 30) = off F sFb from rfl,
    show off F (8 * 31) = off F sCtr from rfl, show off F (8 * 32) = off F sDone from rfl] at R4
  refine WP.mono (WP.keep [.rax] (Q := fun v => v.mem =
      (((u.mem.writeW (off F sB) (off S (e + db))).writeW (off F sFb) (BitVec.ofNat 64 H.D)).writeW
        (off F sCtr) 0#64).writeW (off F sDone) 0#64) ?_ rfl) fun v ⟨hm, hk⟩ => ⟨?_, hk, hm ▸ R4⟩
  · xrun [mgfSeed, List.cons_append, List.nil_append, ea_sp, L.rsp, L.ld (d := sEb) (by decide),
      L.ld (d := sDb) (by decide), L.st (d := sB) (by decide), L.st (d := sFb) (by decide),
      L.st (d := sCtr) (by decide), L.st (d := sDone) (by decide),
      R.slot (d := sEb) (k := 23) rfl (by decide) he, R.slot (d := sDb) (k := 24) rfl (by decide) hdb, off_plus,
      zx32 (show H.D < 2 ^ 32 by unfold oEm at hfit; omega_using [hfit]),
      show BitVec.setWidth 64 (0 : BitVec 32) = 0#64 from rfl]
  · refine L.congr (hk.gpr (by decide)) hk.2.2 ?_
    have h1 := R4.fr 21 (by decide)
    rw [← hm] at h1
    rw [slot_eq sScr 21 rfl, slot_eq sScr 21 rfl, h1, R.fr 21 (by decide)]
    simp [upd]

include hG in
/-- `DB ⊕= MGF1(H, dbLen)`, where `H` is the `hLen` bytes after `DB`, with
the hash function `G` of the table of `Hash` whose words are in the slots. -/
theorem mgfXor_ok {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D)
    (hGv : Proof.Mgf1.Valid Gs) (H : Hash) {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep u.mem F S V W) (T : GT G g W u.syms) {e db : Nat} (hd : DbAt H.D e db)
    (he : W 23 = off S e) (hdb : W 24 = BitVec.ofNat 64 db) :
    WP isa (mgfXor H g) u fun u' => Lay u' F S ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧
      (∀ r ∈ [Reg.r13, .r14, .r15, .rsp], u'.gpr r = u.gpr r) ∧
      ∃ V' W', Rep u'.mem F S V' W' ∧ (∀ k < nW, k < 27 ∨ 32 < k → W' k = W k) ∧
        ∀ o < oRsa, ctOut o →
          V' o = mixV V (Spec.Mgf1.mgf1 Gs ((List.range H.D).map fun i => V (e + db + i)) db) e db o := by
  have hD := (sizes hG).2.2.2.2
  have hdb1 := hd.db1
  refine WP.seq (X86_64.WP.mono_syms (mgfHead_ok H L R hd he hdb) fun v ⟨Lv, hk, Rv⟩ sv => ?_)
  let W₀ := upd (upd W 29 (off S (e + db))) 30 (BitVec.ofNat 64 H.D)
  have hW₀ : ∀ k, k ≠ 29 → k ≠ 30 → W₀ k = W k := fun k h1 h2 => by simp only [W₀, upd, ifn h1, ifn h2]
  have T₀ : GT G g W₀ v.syms := T.congr sv fun k h1 h2 => hW₀ k (by omega_using [h1, h2]) (by omega_using [h1, h2])
  have I0 : MgfI v F S V W₀ (Spec.Mgf1.mgf1 Gs ((List.range H.D).map fun i => V (e + db + i)) db) e db G.D 0 v :=
    ⟨Lv, rfl, rfl, fun _ _ => rfl, rfl, _, _, Rv, by simp [upd], by simp [upd],
      fun k _ h1 h2 => by simp only [upd, ifn h2, ifn h1]; rfl,
      fun o _ _ => by simp only [mixV, Nat.zero_mul, Nat.zero_min, Nat.add_zero]; rw [ifn (by omega_using [])]⟩
  refine WP.loop (M := isa) (fun n w => ∃ c, n = db - c * G.D ∧ c * G.D < db ∧
      MgfI v F S V W₀ (Spec.Mgf1.mgf1 Gs ((List.range H.D).map fun i => V (e + db + i)) db) e db G.D c w)
    ?_ (db - 0 * G.D) v ⟨0, rfl, by omega_using [hdb1], I0⟩
  rintro n w ⟨c, rfl, hc, I⟩
  refine WP.mono (round_ok hG hGh hGl hGv hd (by simp only [W₀, upd]; exact he) (by simp only [W₀, upd]; exact hdb)
    (by simp [W₀, upd]) (by simp [W₀, upd]) T₀ I hc) fun w' ⟨hcf, I'⟩ => ?_
  have hs1 : (c + 1) * G.D = c * G.D + G.D := Nat.succ_mul _ _
  by_cases h : (c + 1) * G.D < db
  · refine .inr ⟨by simp only [eval, hcf, h, decide_true], _, ?_, c + 1, rfl, h, I'⟩
    omega_using [hD, hs1, h]
  · refine .inl ⟨by simp only [eval, hcf, h, decide_false], I'.L, I'.rd.trans hk.2.1, I'.wr.trans hk.2.2,
      fun r hr => (I'.cs r (by revert r hr; decide)).trans (hk.gpr (by revert r hr; decide)), ?_⟩
    obtain ⟨V', W', R', _, _, hW', hV'⟩ := I'.rep
    exact ⟨V', W', R', fun k hk' hk2 => (hW' k hk' (by omega_using [hk2]) (by omega_using [hk2])).trans
        (hW₀ k (by omega_using [hk2]) (by omega_using [hk2])),
      fun o ho hco => by rw [hV' o ho hco, Nat.min_eq_right (by omega_using [h])]⟩

end VG.Proof.RsaPss.X86_64
