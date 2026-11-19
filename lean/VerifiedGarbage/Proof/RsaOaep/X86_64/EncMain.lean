module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.EncCall
public import VerifiedGarbage.Proof.RsaOaep.X86_64.MgfT
import VerifiedGarbage.Proof.RsaOaep.X86_64.Good
public import VerifiedGarbage.Proof.RsaOaep.Encode
public import VerifiedGarbage.Proof.Mgf1.Basic
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Core
import VerifiedGarbage.Proof.RsaOaep.X86_64.EncEm
import VerifiedGarbage.Proof.RsaOaep.Decode
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Label
import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-! ### `RsaOaep.X86_64.LabelT`, which this module and modules that import it used -/

section

/-!
# RSAES-OAEP on x86-64: the label's hash with the hash function of a table

`hashLabelT f o` writes the label's hash `H(label)` to `scratch + o` as
`hashLabel` does (`hashLabelT_ok`), for `H` the hash
function of the table whose address is in the slot `sTab` (word 35): each
of its calls is an indirect call (`tcall`) that reaches `H`'s function
(`Table.TabAt`), and so runs as its call (`Table.initT_ok`, `updExtT_ok`,
`Table.finT_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp ix at_ step byteLoop seqs)
open VG.Impl.Mgf1.X86_64.Table (Fns tcall)
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Bignum (off word off_off)
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (StreamOK)
open VG.Proof.RsaOaep.X86_64.Table (Tab TabAt TJ tcall_ok lay_keep11 cs_keep11 initT_ok finT_ok FnsGood
  tcall_good wp_gs)

/-! ## The table and its digest length -/

/-- The address of the table at the stack argument `j` to its slot. -/
theorem tabSlot_ok {G : Stream} {f : Fns} {j : Nat} {u : State} {F S p : Addr} (L : Lay u F S)
    {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep u.mem F S V W) (T : Tab G f F p (frameBytes + 8 + 8 * j) u) :
    WP isa (.block (tabSlot j)) u fun u' => Keep [.r11] u u' ∧ Lay u' F S ∧ Rep u'.mem F S V (upd W 35 p) ∧
      u'.syms = u.syms := by
  have G' := L.geo
  have R1 := R.wf G' (k := 35) (by decide) p
  rw [show off F (8 * 35) = off F sTab from rfl] at R1
  refine WP.mono (WP.keep [.r11] (Q := fun u' => u'.mem = u.mem.writeW (off F sTab) p ∧ u'.syms = u.syms) ?_ rfl)
    fun u' ⟨⟨hm, hs⟩, k⟩ => ⟨k, ?_, hm ▸ R1, hs⟩
  · xrun [tabSlot, arg, ea_sp, L.rsp, T.rdA, (T.mem _ (Frame.refl _ _)).2.2, L.st (d := sTab) (by decide),
      setReg_syms]
  · refine L.congr (k.gpr (by decide)) k.2.2 ?_
    have h1 := R1.fr 14 (by decide)
    rw [← hm] at h1
    rw [slot_eq sScr 14 rfl, slot_eq sScr 14 rfl, h1, R.fr 14 (by decide)]
    simp [upd]

/-- The digest length of the table at `p`, whose address is in its slot, to
`r11`. -/
theorem lenLoad_ok {u : State} {F S p : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) (h35 : W 35 = p) (hrd : InRegions (u.rd ++ u.wr) (off p 48) 8) {D : Nat}
    (hD : u.mem.readW (off p 48) 64 = BitVec.ofNat 64 D) :
    WP isa (.block lenLoad) u fun u' => Keep [.r11] u u' ∧ u'.gpr .r11 = BitVec.ofNat 64 D ∧ u'.mem = u.mem ∧
      u'.syms = u.syms := by
  refine WP.mono (WP.keep [.r11] (Q := fun u' => u'.gpr .r11 = BitVec.ofNat 64 D ∧ u'.mem = u.mem ∧
      u'.syms = u.syms) ?_ rfl) fun u' ⟨⟨h11, hm, hs⟩, k⟩ => ⟨k, h11, hm, hs⟩
  xrun [lenLoad, ea_sp, VG.Proof.RsaOaep.X86_64.ea_at, L.rsp, L.ld (d := sTab) (by decide),
    R.slot (d := sTab) (k := 35) rfl (by decide) h35, hrd, hD, setReg_syms]

theorem mem_lens {G : Spec.Mgf1.Hash} (h : G ∈ Proof.Pbkdf2.Md.X86_64.mdHashes) : G.len ∈ lens := by
  simp only [Proof.Pbkdf2.Md.X86_64.mdHashes, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem mem_lens_lt {d : Nat} (h : d ∈ lens) : d < 2 ^ 31 := by
  simp only [lens, List.mem_cons, List.not_mem_nil, or_false] at h; omega_using [h]

/-- The comparison of the digest length `d` in `r11` with `x`. -/
theorem cmpLen_ok {u : State} {d x : Nat} (h11 : u.gpr .r11 = BitVec.ofNat 64 d) (hd : d < 2 ^ 31)
    (hx : x < 2 ^ 31) :
    WP isa (.block [.alu .cmp .r11 (im x)]) u fun u' => u'.zf = some (decide (d = x)) ∧ Keep [] u u' ∧
      u'.mem = u.mem ∧ u'.syms = u.syms ∧ u'.mxcsr = u.mxcsr := by
  refine WP.mono_syms (WP.keep [.r11] (Q := fun u' => u'.zf = some (decide (d = x)) ∧
      u'.gpr .r11 = u.gpr .r11 ∧ u'.mem = u.mem ∧ u'.mxcsr = u.mxcsr) ?_ rfl)
    fun u' ⟨⟨hz, h11', hm, hmx⟩, k⟩ hs => ⟨hz, ⟨fun r _ => by
      by_cases hr : r = .r11
      · subst hr; exact h11'
      · exact k.gpr (by simpa using hr), k.2.1, k.2.2⟩, hm, hs, hmx⟩
  xrun [im, h11, VG.Proof.MlKem.X86_64.sx_ofNat hx,
    VG.Proof.Bignum.X86_64.ofNat_sub_beq (show d < 2 ^ 64 by omega_using [hd]) (show x < 2 ^ 64 by omega_using [hx]),
    VG.X86_64.RegUpd.mxcsr_setFlags]

/-- The code for the digest length `d` in `r11`, from a state that differs
only in its flags. -/
theorem byLen_ok {b : Nat → Prog isa} : ∀ {ds : List Nat} {d : Nat}, d ∈ ds → (∀ x ∈ ds, x < 2 ^ 31) →
    d < 2 ^ 31 → ∀ {u : State} {Q : State → Prop}, u.gpr .r11 = BitVec.ofNat 64 d →
    (∀ u', Keep [] u u' → u'.mem = u.mem → u'.syms = u.syms → u'.mxcsr = u.mxcsr → WP isa (b d) u' Q) →
    WP isa (byLen b ds) u Q
  | [], _, h, _, _, _, _, _, _ => absurd h List.not_mem_nil
  | [x], d, h, _, _, u, _, _, hb => by
    obtain rfl := List.mem_singleton.mp h
    exact hb u ⟨fun _ _ => rfl, rfl, rfl⟩ rfl rfl rfl
  | x :: y :: ds, d, h, hx, hd, u, Q, h11, hb => by
    refine WP.seq (WP.mono (cmpLen_ok h11 hd (hx x (List.mem_cons_self ..))) fun u' ⟨hz, k0, hm, hs, hmx⟩ => ?_)
    refine WP.ite (M := isa) _ (show isa.eval .e u' = _ from hz) (fun he => ?_) (fun he => ?_)
    · rw [decide_eq_true_eq] at he; subst he
      exact hb u' k0 hm hs hmx
    · rw [decide_eq_false_iff_not] at he
      have hm' : d ∈ y :: ds := (List.mem_cons.mp h).resolve_left he
      exact byLen_ok hm' (fun z hz => hx z (List.mem_cons_of_mem _ hz)) hd ((k0.gpr (by simp)).trans h11)
        fun u'' k' hm'' hs'' hmx'' => hb u'' ⟨fun _ hr => (k'.gpr hr).trans (k0.gpr hr), k'.2.1.trans k0.2.1,
          k'.2.2.trans k0.2.2⟩ (hm''.trans hm) (hs''.trans hs) (hmx''.trans hmx)

theorem hashLabelT_good {f : Fns} (hgi : FnsGood f.init) (hgu : FnsGood f.upd) (hgf : FnsGood f.fin) (o : Nat) :
    Good (hashLabelT f o) := by
  have hi := tcall_good hgi 0; have hu := tcall_good hgu 1; have hf := tcall_good hgf 2
  refine ⟨?_, ?_⟩
  · simp only [hashLabelT, seqs, Code.allInstrs, hi.1, hu.1, hf.1, Bool.and_true, Bool.true_and]
    rfl
  · have := hi.2; have := hu.2; have := hf.2
    simp only [hashLabelT, seqs, Code.depth, Nat.max_le]
    omega

variable {G : Stream} (hG : StreamOK G) {f : Fns}

include hG in
/-- `update` with the `len` bytes at `d`, outside our working space, by an
indirect call. -/
theorem updExtT_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) {p : Addr} (hp : W 35 = p) (T : TabAt G f p t) {d : Addr} {len : Nat}
    (hlen : len < 2 ^ 64) (hcd : Covers [⟨d, len⟩] (t.rd ++ t.wr)) (hds : Region.Disjoint ⟨d, len⟩ ⟨S, oRsa⟩)
    (hdk : (below F 16).Disjoint ⟨d, len⟩)
    (hdi : t.gpr .rdi = off S oSt) (hdx : t.gpr .rdx = d) (hcx : t.gpr .rcx = BitVec.ofNat 64 len)
    (h8 : t.gpr .r8 = off S oW) :
    WP isa (tcall sTab 1 f.upd) t fun t' => Lay t' F S ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧
      Rep t'.mem F S (fun o => if inR [(oSt, G.S), (oW, hG.Wb)] o then t'.mem (off S o) else V o) W ∧
      (∀ m, hG.SH.Repr t.mem (off S oSt) m → t.gpr .rsi = BitVec.ofNat 64 m.length →
        hG.SH.Repr t'.mem (off S oSt) (m ++ Spec.Rsa.bytesAt t.mem d len)) :=
  tcall_ok L R hp (T.rd 1 (by decide)) T.mem.2.1 T.ok.u fun u k hm _ =>
    WP.mono (updExt_ok hG (lay_keep11 L k hm) (hm ▸ R) hlen (by rw [k.2.1, k.2.2]; exact hcd) hds hdk
        ((k.gpr (by decide)).trans hdi) ((k.gpr (by decide)).trans hdx) ((k.gpr (by decide)).trans hcx)
        ((k.gpr (by decide)).trans h8))
      fun t' ⟨L', rd', wr', cs', R', _, hr'⟩ => ⟨L', rd'.trans k.2.1, wr'.trans k.2.2,
        fun r hr => (cs' r hr).trans (cs_keep11 k r hr), R', fun m hm' hc => by
          have := hr' m (hm ▸ hm') ((k.gpr (by decide)).trans hc)
          rwa [hm] at this⟩

include hG in
/-- The label's hash to `scratch + o`, with the hash function of the table
at `p`, whose address is in the slot `sTab` (`W 35`): the table of `Tab`
from a state `u₀` whose memory differs from `u`'s only where the code may
write (`TJ`). -/
theorem hashLabelT_ok (hgi : FnsGood f.init) (hgu : FnsGood f.upd)
    {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hG.SH.H.hash x) {u₀ u : State} {F S p : Addr} {sArg : Nat}
    (T : Tab G f F p sArg u₀) (J : TJ u₀ F u) (hrd₀ : u.rd = u₀.rd) (hwr₀ : u.wr = u₀.wr)
    (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep u.mem F S V W) (hp : W 35 = p)
    {lab : Addr} {labLen : Nat} (A : LabAt u F S W lab labLen) {o : Nat} (ho : o = oDig ∨ o = oLh) :
    WP isa (hashLabelT f o) u fun u' => Lay u' F S ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧
      (∀ r ∈ calleeSaved, u'.gpr r = u.gpr r) ∧
      ∃ V', Rep u'.mem F S V' W ∧ (∀ x, ¬ inR (labR o) x → V' x = V x) ∧
        ∀ i < G.D, V' (o + i) = (Hs.hash (Spec.Rsa.bytesAt u.mem lab labLen)).getD i 0 := by
  obtain ⟨hzS, hzF, hzW, hzDF, hzD⟩ := sizes hG
  have hoo : oSt + 256 ≤ o ∧ o + 64 ≤ oW := by rcases ho with rfl | rfl <;> decide
  have hlen := A.len
  unfold hashLabelT seqs seqs seqs seqs seqs
  refine WP.seq (WP.mono (wp_gs (block_good _ rfl) (scr_ok L (d := .rdi) (by decide) (o := oSt) (by decide)))
    fun u1 ⟨⟨hdi1, hm1, k1⟩, f1, s1⟩ => ?_)
  have L1 : Lay u1 F S := L.congr (k1.gpr (by decide)) k1.2.2 (by rw [hm1])
  have R1 : Rep u1.mem F S V W := hm1 ▸ R
  have J1 : TJ u₀ F u1 := J.step hwr₀ L.rsp f1 s1
  have rd1 : u1.rd = u₀.rd := k1.2.1.trans hrd₀
  have wr1 : u1.wr = u₀.wr := k1.2.2.trans hwr₀
  refine WP.seq (WP.mono (wp_gs (tcall_good hgi 0) (initT_ok hG L1 R1 hp (T.at J1 rd1 wr1) hdi1))
    fun u2 ⟨⟨L2, rd2, wr2, cs2, R2, hF2, hr2⟩, f2, s2⟩ => ?_)
  have J2 : TJ u₀ F u2 := J1.step wr1 L1.rsp f2 s2
  obtain ⟨V2, R2, hV2, -⟩ := Rep.ex R2
  have A2 : LabAt u2 F S W lab labLen := A.congr (rd2.trans k1.2.1) (wr2.trans k1.2.2) rfl rfl
  refine WP.seq (WP.mono (wp_gs (block_good _ rfl) (labA_ok L2 R2 A2))
    fun u3 ⟨⟨hdi3, hsi3, hdx3, hcx3, h83, hm3, k3⟩, f3, s3⟩ => ?_)
  have L3 : Lay u3 F S := L2.congr (k3.gpr (by decide)) k3.2.2 (by rw [hm3])
  have R3 : Rep u3.mem F S V2 W := hm3 ▸ R2
  have A3 : LabAt u3 F S W lab labLen := A2.congr k3.2.1 k3.2.2 rfl rfl
  have J3 : TJ u₀ F u3 := J2.step (wr2.trans wr1) L2.rsp f3 s3
  have rd3 : u3.rd = u₀.rd := k3.2.1.trans (rd2.trans rd1)
  have wr3 : u3.wr = u₀.wr := k3.2.2.trans (wr2.trans wr1)
  refine WP.seq (WP.mono (wp_gs (tcall_good hgu 1) (updExtT_ok hG L3 R3 hp (T.at J3 rd3 wr3) A3.len A3.cov A3.dS
      A3.dK hdi3 hdx3 hcx3 h83))
    fun u4 ⟨⟨L4, rd4, wr4, cs4, R4, hr4⟩, f4, s4⟩ => ?_)
  have hR4 := hr4 [] (hm3 ▸ hr2) (by rw [hsi3]; rfl)
  rw [List.nil_append, hm3] at hR4
  obtain ⟨V4, R4, hV4, -⟩ := Rep.ex R4
  have J4 : TJ u₀ F u4 := J3.step wr3 L3.rsp f4 s4
  have rd4' : u4.rd = u₀.rd := rd4.trans rd3
  have wr4' : u4.wr = u₀.wr := wr4.trans wr3
  refine WP.seq (WP.mono (wp_gs (block_good _ rfl) (labF_ok L4 R4 A.hll (o := o) (by rcases ho with rfl | rfl <;> decide)))
    fun u5 ⟨⟨hdi5, hsi5, hdx5, hcx5, hm5, k5⟩, f5, s5⟩ => ?_)
  have L5 : Lay u5 F S := L4.congr (k5.gpr (by decide)) k5.2.2 (by rw [hm5])
  have R5 : Rep u5.mem F S V4 W := hm5 ▸ R4
  have J5 : TJ u₀ F u5 := J4.step wr4' L4.rsp f5 s5
  refine WP.mono (finT_ok hG L5 R5 hp (T.at J5 (k5.2.1.trans rd4') (k5.2.2.trans wr4')) (o := o) (Or.inr hoo)
    hdi5 hdx5 hcx5) fun u6 ⟨L6, rd6, wr6, cs6, R6, hr6⟩ => ?_
  have hlb : (Spec.Rsa.bytesAt u2.mem lab labLen).length = labLen := by
    simp [Spec.Rsa.bytesAt]
  have hdig := hr6 _ (hm5 ▸ hR4) (by rw [hlb]; omega_using [hlen]) (by rw [hsi5, hlb])
  have hlab : Spec.Rsa.bytesAt u2.mem lab labLen = Spec.Rsa.bytesAt u.mem lab labLen := by
    rw [← hm1]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => hF2.bytes (R := ⟨lab, labLen⟩) (fun r hr => ?_)
      (by show labLen ≤ 2 ^ 64; omega_using [hlen]) (List.mem_range.mp hi)
    rcases List.mem_append.mp hr with hr | hr
    · simp only [regs, List.map_cons, List.map_nil, List.mem_singleton] at hr; subst hr
      have h1 : oSt + G.S ≤ oRsa := by unfold oSt oRsa; omega_using [hzS]
      have hs : Region.Sub ⟨off S oSt, G.S⟩ ⟨S, oRsa⟩ := Offset.sub_base S h1
      exact A.dS.sub_right hs
    · rw [List.mem_singleton.mp hr]; exact A.dK.symm
  obtain ⟨V6, R6, hV6, hV6'⟩ := Rep.ex R6
  refine ⟨L6, rd6.trans (k5.2.1.trans (rd4.trans (k3.2.1.trans (rd2.trans k1.2.1)))),
    wr6.trans (k5.2.2.trans (wr4.trans (k3.2.2.trans (wr2.trans k1.2.2)))), fun r hr => ?_, V6, R6,
    fun x hx => ?_, fun i hi => ?_⟩
  · rw [cs6 r hr, keep_cs' k5 (cs_disj _ (by decide)) r hr, cs4 r hr, keep_cs' k3 (cs_disj _ (by decide)) r hr,
      cs2 r hr, keep_cs' k1 (cs_disj _ (by decide)) r hr]
  · simp only [labR, inR_cons, inR_nil, or_false] at hx
    rw [hV6 _ (by simp only [inR_cons, inR_nil, or_false]; omega_using [hzS, hzF, hzW, hx]),
      hV4 _ (by simp only [inR_cons, inR_nil, or_false]; omega_using [hzS, hzW, hx]),
      hV2 _ (by simp only [inR_cons, inR_nil, or_false]; omega_using [hzS, hx])]
  · rw [hV6' _ (by simp only [inR_cons, inR_nil, or_false]; omega_using [hzDF, hi]), hdig i hi, hHh, hlab]

end VG.Proof.RsaOaep.X86_64

end

end

/-!
# RSAES-OAEP encryption on x86-64: after the checks

`EM` written and masked in our working space (`encMask_ok`), before the
public operation's call (`PcCorrect`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp ix at_ step byteLoop seqs mgfXor)
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)
open VG.Proof.RsaPkcs1Sig.X86_64 (pubChecked)

theorem valid_of_link {H : Hash} (hH : HashOK H) (l : MgfLink H hH) : Proof.Mgf1.Valid l.G :=
  ⟨by rw [l.len]; exact hH.hD0, fun x => by
    rw [l.hash, hH.hash, List.length_take, MdStream.Md.hash, hH.md.digest_length, l.len]
    exact Nat.min_eq_left hH.hDN⟩

/-- In the frame, from the entry state `s`. -/
structure EnvE (s t : State) : Prop where
  rsp : t.gpr .rsp = fb s
  rd : t.rd = s.rd
  wr : t.wr = [frR s, outR s, scrR s]
  cs : ∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = s.gpr r
  mx : t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10
  fr : FrE s t.mem

theorem EnvE.step {s t t' : State} (he : EnvE s t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.gpr .rsp = t.gpr .rsp) (hcs : ∀ r ∈ calleeSaved, r ≠ .rsp → t'.gpr r = t.gpr r)
    (hmx : t'.mxcsr = t.mxcsr) (hf : Frame (t.wr ++ [below (t.gpr .rsp) 16]) t.mem t'.mem) : EnvE s t' :=
  ⟨hsp.trans he.rsp, hrd.trans he.rd, hwr.trans he.wr, fun r hr h => (hcs r hr h).trans (he.cs r hr h),
    by rw [hmx]; exact he.mx, FrE.step he.fr (ws := t.wr) he.wr (by rw [he.rsp] at hf; exact hf)⟩

theorem keep_cs3 {u v : State} {rs : List Reg} (k : Keep rs u v)
    (h : rs.all (fun r => !calleeSaved.contains r) = true) : ∀ r ∈ calleeSaved, r ≠ .rsp → v.gpr r = u.gpr r :=
  fun r hr _ => k.gpr (cs_disj rs h r hr)

theorem ne_of_disjoint {A B : Region} (hd : A.Disjoint B) {a b : Addr} (ha : A.Contains a 1) (hb : B.Contains b 1) :
    a ≠ b := fun h => hd a ha (h ▸ hb)

/-- A byte of a region apart from what the function writes, as on entry. -/
theorem FrE.byte {s : State} {m : Mem} (h : FrE s m) {p : Addr} {n : Nat} (hk : (stkR s).Disjoint ⟨p, n⟩)
    (ho : (outR s).Disjoint ⟨p, n⟩) (hs : (scrR s).Disjoint ⟨p, n⟩) (hn : n ≤ 2 ^ 64) {i : Nat} (hi : i < n) :
    m (p + BitVec.ofNat 64 i) = s.mem (p + BitVec.ofNat 64 i) := by
  have := congrArg (fun l => l.getD i 0) (FrE.bytes h hk ho hs hn)
  simpa [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi] using this

theorem bytesAt_getD (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (Spec.Rsa.bytesAt m p n).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]

/-- The function's argument slots, as the prologue stored them. -/
def ArgsW (s : State) (W : Nat → BitVec 64) : Prop := ∀ k, k = 14 ∨ (21 ≤ k ∧ k ≤ 31) → W k = encW s k

theorem ArgsW.w {s : State} {W : Nat → BitVec 64} (h : ArgsW s W) :
    W 14 = stackArg s 6 ∧ W 21 = s.gpr .rdi ∧ W 22 = s.gpr .rdx ∧ W 23 = s.gpr .rcx ∧ W 24 = s.gpr .r8 ∧
    W 25 = s.gpr .r9 ∧ W 26 = stackArg s 7 ∧ W 27 = stackArg s 0 ∧ W 28 = stackArg s 1 ∧
    W 29 = stackArg s 2 ∧ W 30 = stackArg s 3 ∧ W 31 = stackArg s 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [h _ (by omega_using [])]; simp [encW, upd])

variable {Hl Gm : Hash} (hH : HashOK Hl) (KH : Callees Hl) (hG : HashOK Gm) (KG : Callees Gm)
  (mH : MgfLink Hl hH) (mG : MgfLink Gm hG)

include hH mH in
theorem encEm_ok {f : Impl.Mgf1.X86_64.Table.Fns} (hgi : Table.FnsGood f.init) (hgu : Table.FnsGood f.upd)
    (hgf : Table.FnsGood f.fin) {s t : State} (hp : EPre mH.G s) (he : EnvE s t) (hsy : t.syms = s.syms)
    (hTL : ∀ t, EnvE s t → t.syms = s.syms → Table.Tab Hl.stream f (fb s) (stackArg s 10) (frameBytes + 8 + 8 * 10) t)
    (L : Lay t (fb s) (stackArg s 6))
    {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep t.mem (fb s) (stackArg s 6) V W) (hW : ArgsW s W)
    (hk : 2 * Hl.D + 2 + (stackArg s 3).toNat ≤ (s.gpr .rcx).toNat) :
    WP isa (encEm Hl.stream f) t fun t' => EnvE s t' ∧ Lay t' (fb s) (stackArg s 6) ∧
      ∃ V', Rep t'.mem (fb s) (stackArg s 6) V' (upd W 35 (stackArg s 10)) ∧
        EmAt V' (s.gpr .rcx).toNat Hl.D (Spec.Rsa.bytesAt s.mem (stackArg s 4) mH.G.len)
          (mH.G.hash (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat))
          (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat) (stackArg s 3).toNat := by
  obtain ⟨w14, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31⟩ := hW.w
  obtain hk1 := hp.k1; have hk2 := hp.k2; have hsl := hp.hsl; have wS := hp.wS
  obtain hD := hH.hD0; have hDN := hH.hDN; have hN := hH.N_le
  have hlen : mH.G.len = Hl.D := mH.len
  have hsD : Hl.stream.D = Hl.D := rfl
  have c0 : oEm = 0 := rfl
  have cS : oSt = 3072 := rfl
  have cD : oDig = 3328 := rfl
  have cW : oW = 4096 := rfl
  -- What reads the caller's buffers needs.
  obtain scrC : ∀ {o : Nat}, o < oRsa → (scrR s).Contains (off (stackArg s 6) o) 1 := fun ho =>
    Offset.contains_base _ (by unfold oRsa at ho; omega_using [hsl, ho]) (by unfold oRsa at ho; omega_using [ho])
  unfold encEm seqs seqs seqs seqs seqs
  -- `EM`'s place cleared.
  refine WP.seq (WP.mono_syms (wp_good clearEm_good (clearEm_ok L R)) fun t1 ⟨⟨L1, k1, R1⟩, sp1, mx1, f1⟩ sy1 => ?_)
  obtain he1 : EnvE s t1 := he.step k1.2.1 k1.2.2 sp1 (keep_cs3 k1 (by decide)) mx1 f1
  -- The seed.
  refine WP.seq (WP.mono_syms (wp_good (copySeed_good _) (copySeed_ok (H := Hl.stream) L1 R1 w31 hD (by omega_using [hDN, hN, hsD])
    (fun i hi => hp.rd_in he1.rd (by simp [rdL]) (Offset.contains_base (stackArg s 4) (d := i) (n := 1)
      (k := mH.G.len) (by omega_using [hlen, hsD, hi]) (by omega_using [hDN, hN, hsD, hi])))
    (fun i hi j hj => ne_of_disjoint hp.d_sd_scr (Offset.contains_base (stackArg s 4) (d := i) (n := 1)
      (k := mH.G.len) (by omega_using [hlen, hsD, hi]) (by omega_using [hDN, hN, hsD, hi])) (scrC
          (by unfold oRsa; omega_using [hDN, hN, hsD, c0, hj])))))
    fun t2 ⟨⟨L2, k2, R2⟩, sp2, mx2, f2⟩ sy2 => ?_)
  obtain he2 : EnvE s t2 := he1.step k2.2.1 k2.2.2 sp2 (keep_cs3 k2 (by decide)) mx2 f2
  -- The table of the label's hash function to its slot.
  obtain TL2 := hTL t2 he2 (sy2.trans (sy1.trans hsy))
  refine WP.seq (WP.mono_syms (wp_good (block_good _ rfl) (tabSlot_ok L2 R2 TL2))
    fun t2' ⟨⟨ka, La, Ra, sya⟩, spa, mxa, fa⟩ _ => ?_)
  obtain he2' : EnvE s t2' := he2.step ka.2.1 ka.2.2 spa (keep_cs3 ka (by decide)) mxa fa
  obtain hW' : ArgsW s (upd W 35 (stackArg s 10)) := fun k hk => by
    simp only [upd]; rw [ifn (by omega_using [hk])]; exact hW k hk
  obtain ⟨-, -, -, w23, -, -, -, w27, w28, w29, w30, -⟩ := hW'.w
  -- The label's hash.
  obtain hll : upd W 35 (stackArg s 10) 28 = BitVec.ofNat 64 (stackArg s 1).toNat := by
    rw [w28, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain sS : Region.Sub ⟨stackArg s 6, oRsa⟩ (scrR s) := Region.sub_prefix (by unfold oRsa; omega_using [hsl])
  obtain A2 : LabAt t2' (fb s) (stackArg s 6) (upd W 35 (stackArg s 10)) (stackArg s 0) (stackArg s 1).toNat :=
    ⟨w27, hll, (stackArg s 1).isLt, Covers.left (by
        rw [he2'.rd]; exact (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp [rdL]).trans hp.hrd),
      (hp.d_lb_scr.sub_right sS), (hp.d_stk_lb.sub_left (ret_sub s))⟩
  refine WP.seq (WP.mono (wp_good (hashLabelT_good hgi hgu hgf oDig)
    (hashLabelT_ok hH.stream hgi hgu (Hs := mH.G) mH.hash (hTL t2' he2' (sya.trans (sy2.trans (sy1.trans hsy))))
      (Table.TJ.refl t2' _) rfl rfl La Ra (by simp [upd]) A2 (Or.inl rfl)))
    fun t3 ⟨⟨L3, rd3, wr3, cs3, V3, R3, hV3, hV3'⟩, sp3, mx3, f3⟩ => ?_)
  obtain he3 : EnvE s t3 := he2'.step rd3 wr3 sp3 (fun r hr _ => cs3 r hr) mx3 f3
  obtain hlab : Spec.Rsa.bytesAt t2'.mem (stackArg s 0) (stackArg s 1).toNat =
      Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat :=
    FrE.bytes he2'.fr hp.d_stk_lb hp.d_out_lb hp.d_lb_scr.symm (by have := hp.wL; omega_using [])
  rw [hlab] at hV3'
  -- `lHash` after the seed.
  refine WP.seq (WP.mono (wp_good (copyLh_good _) (copyLh_ok (H := Hl.stream) L3 R3 hD (by omega_using [hDN, hN, hsD])))
    fun t4 ⟨⟨L4, k4, R4⟩, sp4, mx4, f4⟩ => ?_)
  obtain he4 : EnvE s t4 := he3.step k4.2.1 k4.2.2 sp4 (keep_cs3 k4 (by decide)) mx4 f4
  -- `0x01` and the message.
  obtain hmA : ∀ i < (stackArg s 3).toNat, (⟨stackArg s 2, (stackArg s 3).toNat⟩ : Region).Contains
      (stackArg s 2 + BitVec.ofNat 64 i) 1 := fun i hi => Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])
  refine WP.mono (wp_good putMsg_good (putMsg_ok L4 R4 (k := (s.gpr .rcx).toNat) (mLen := (stackArg s 3).toNat)
    (by rw [w23, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by rw [w30, BitVec.ofNat_toNat, BitVec.setWidth_eq]) w29
    (by omega_using [hk]) hk2 (fun i hi => hp.rd_in he4.rd (by simp [rdL]) (hmA i hi))
    (fun i hi j hj => ne_of_disjoint hp.d_ms_scr (hmA i hi) (scrC (by unfold oRsa; omega_using [hk, hk2, hj])))))
    fun t5 ⟨⟨L5, k5, R5⟩, sp5, mx5, f5⟩ => ?_
  obtain he5 : EnvE s t5 := he4.step k5.2.1 k5.2.2 sp5 (keep_cs3 k5 (by decide)) mx5 f5
  obtain nl : ∀ x, x < oSt → ¬ inR (labR oDig) x := fun x hx => by
    simp only [labR, inR_cons, inR_nil, or_false]; omega_using [cS, cD, cW, hx]
  refine ⟨he5, L5, _, R5, ?_⟩
  refine ⟨?_, fun i hi => ?_, fun i hi => ?_, fun i h1 h2 => ?_, ?_, fun i hi => ?_⟩
  · simp only [cpV, upd]
    rw [ifn (by omega_using []), ifn (by omega_using [hk]), ifn (by unfold oEm; omega_using []), hV3 _ (nl _ (by omega_using [cS]))]
    simp only [cpV, clrV]
    rw [ifn (by unfold oEm; omega_using []), ifp (by unfold oEm; omega_using [])]
  · simp only [cpV, upd]
    rw [ifn (by omega_using [hk, hi]), ifn (by omega_using [hk, hi]), ifn (by unfold oEm; omega_using [hsD, hi]),
        hV3 _ (nl _ (by omega_using [hDN, hN, cS, hi]))]
    simp only [cpV]
    rw [ifp (by unfold oEm; omega_using [hsD, hi]), show 1 + i - (oEm + (oEm + 1)) = i by unfold oEm; omega_using [],
      FrE.byte he1.fr hp.d_stk_sd hp.d_out_sd hp.d_sd_scr.symm (by have := hp.wSd; omega_using [this]) (by omega_using [hlen, hi]),
      bytesAt_getD _ _ (by omega_using [hlen, hi])]
  · simp only [cpV, upd]
    rw [ifn (by omega_using [hk, hi]), ifn (by omega_using [hk, hi]), ifp (by unfold oEm; omega_using [hsD, hi]),
      show 1 + Hl.D + i - (oEm + (oEm + 1 + Hl.stream.D)) = i by unfold oEm; omega_using [hsD], hV3' i (by omega_using [hsD, hi])]
  · simp only [cpV, upd]
    rw [ifn (by omega_using [h2]), ifn (by omega_using [h2]), ifn (by unfold oEm; omega_using [hsD, h1]),
        hV3 _ (nl _ (by omega_using [hk2, cS, h2]))]
    simp only [cpV, clrV]
    rw [ifn (by unfold oEm; omega_using [hsD, h1]), ifp (by unfold oEm; omega_using [hk2, h2])]
  · simp only [cpV, upd]
    rw [ifn (by omega_using [])]; rfl
  · simp only [cpV]
    rw [ifp (by omega_using [hk, hi]), show (s.gpr .rcx).toNat - (stackArg s 3).toNat + i -
      ((s.gpr .rcx).toNat - (stackArg s 3).toNat - 1 + 1) = i by omega_using [hk],
      FrE.byte he4.fr hp.d_stk_ms hp.d_out_ms hp.d_ms_scr.symm (by have := hp.wM; omega_using []) hi,
      bytesAt_getD _ _ hi]

include hH hG mH mG in
/-- `EM` built and masked, with the label's hash function the one of the
table that the stack argument 10 points to (`hTL`, its address in its slot)
and MGF1's the one of the table that the stack argument 11 points to
(`hT`), then `rest`, from the state with
the arguments of the public operation's call to make: `EnvE`, the slots, and
`EM` in the working space. -/
theorem encMask_ok {f : Impl.Mgf1.X86_64.Table.Fns} (hgi : Table.FnsGood f.init) (hgu : Table.FnsGood f.upd)
    (hgf : Table.FnsGood f.fin) {s t : State} (hp : EPre mH.G s) (he : EnvE s t) (hsy : t.syms = s.syms)
    (hT : ∀ t, EnvE s t → t.syms = s.syms → Table.Tab Gm.stream f (fb s) (stackArg s 11) (frameBytes + 8 + 8 * 11) t)
    (hTL : ∀ t, EnvE s t → t.syms = s.syms → Table.Tab Hl.stream f (fb s) (stackArg s 10) (frameBytes + 8 + 8 * 10) t)
    (L : Lay t (fb s) (stackArg s 6))
    {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep t.mem (fb s) (stackArg s 6) V W) (hW : ArgsW s W)
    (hk : 2 * Hl.D + 2 + (stackArg s 3).toNat ≤ (s.gpr .rcx).toNat) {rest : Prog isa} {Q : State → Prop}
    (hrest : ∀ t9 V9 W9, EnvE s t9 → Lay t9 (fb s) (stackArg s 6) → Rep t9.mem (fb s) (stackArg s 6) V9 W9 →
      (∀ k, 21 ≤ k → k ≤ 26 → W9 k = encW s k) →
      (List.range (s.gpr .rcx).toNat).map (fun i => V9 (oEm + i)) =
        emOf mG.G Hl.D (s.gpr .rcx).toNat (stackArg s 3).toNat (Spec.Rsa.bytesAt s.mem (stackArg s 4) mH.G.len)
          (mH.G.hash (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat))
          (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat) → WP isa rest t9 Q) :
    WP isa (.seq (encEm Hl.stream f) (.seq (.block (dbArgs Hl.stream)) (.seq (mgfT f 11)
      (.seq (.block (seedArgs Hl.stream)) (.seq (mgfT f 11) rest))))) t Q := by
  obtain ⟨w14, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31⟩ := hW.w
  obtain hk1 := hp.k1; have hk2 := hp.k2
  have hD := hH.hD0
  have hsD : Hl.stream.D = Hl.D := rfl
  have hgD : Gm.stream.D = Gm.D := rfl
  have c0 : oEm = 0 := rfl
  have cS : oSt = 3072 := rfl
  obtain w23' : W 23 = BitVec.ofNat 64 (s.gpr .rcx).toNat := by rw [w23, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  -- `EM` before masking.
  refine WP.seq (WP.mono_syms (encEm_ok hH mH hgi hgu hgf hp he hsy hTL L R hW hk)
    fun t5 ⟨he5, L5, V5, R5, E⟩ sy5 => ?_)
  obtain hW5 : ArgsW s (upd W 35 (stackArg s 10)) := fun k hk => by
    simp only [upd]; rw [ifn (by omega_using [hk])]; exact hW k hk
  obtain w23'' : upd W 35 (stackArg s 10) 23 = BitVec.ofNat 64 (s.gpr .rcx).toNat := by
    simp only [upd]; exact w23'
  -- `DB` masked.
  refine WP.seq (WP.mono_syms (wp_good (dbArgs_good _) (dbArgs_ok (H := Hl.stream) L5 R5 w23''
      (by omega_using [hk, hk2, hsD]) (by omega_using [hk, hsD])))
    fun t6 ⟨⟨L6, k6, R6⟩, sp6, mx6, f6⟩ sy6 => ?_)
  obtain he6 : EnvE s t6 := he5.step k6.2.1 k6.2.2 sp6 (keep_cs3 k6 (by decide)) mx6 f6
  refine WP.seq (WP.mono_syms (wp_good (Table.mgfT_good hgi hgu hgf _) (Table.mgfXorT_ok hG.stream hgi hgu hgf
    mG.hash mG.len (valid_of_link hG mG) (hT t6 he6 (sy6.trans (sy5.trans hsy)))
        L6 R6 ⟨by unfold oEm oSt; omega_using [hk, hk2, hsD], by unfold oEm oSt; omega_using [hk, hk2, hsD], by omega_using [], by omega_using [hk, hsD], by omega_using [hk2]⟩
    (mW_args _ _ _ _ _ _))) fun t7 ⟨⟨L7, rd7, wr7, cs7, V7, W7, R7, hW7, hV7⟩, sp7, mx7, f7⟩ sy7 => ?_)
  obtain he7 : EnvE s t7 := he6.step rd7 wr7 sp7 (fun r hr _ => cs7 r hr) mx7 f7
  obtain W7e : ∀ k, (k < 15 ∨ (18 < k ∧ k < 35)) → k < nW → k ≠ 19 → k ≠ 20 → W7 k = upd W 35 (stackArg s 10) k := fun k h1 h2 h3 h4 =>
    (hW7 k h2 h3 h4 (by omega_using [h1]) (by omega_using [h1])).trans (mW_other (by omega_using [h1]))
  -- The seed masked.
  refine WP.seq (WP.mono_syms (wp_good (seedArgs_good _) (seedArgs_ok (H := Hl.stream) L7 R7
    ((W7e 23 (by omega_using []) (by decide) (by omega_using []) (by omega_using [])).trans w23'')
        (by omega_using [hk, hk2, hsD]) (by omega_using [hk, hsD])))
    fun t8 ⟨⟨L8, k8, R8⟩, sp8, mx8, f8⟩ sy8 => ?_)
  obtain he8 : EnvE s t8 := he7.step k8.2.1 k8.2.2 sp8 (keep_cs3 k8 (by decide)) mx8 f8
  refine WP.seq (WP.mono (wp_good (Table.mgfT_good hgi hgu hgf _) (Table.mgfXorT_ok hG.stream hgi hgu hgf
    mG.hash mG.len (valid_of_link hG mG) (hT t8 he8 (sy8.trans (sy7.trans (sy6.trans (sy5.trans hsy)))))
        L8 R8 ⟨by unfold oEm oSt; omega_using [hk, hk2, hsD], by unfold oEm oSt; omega_using [hk, hk2, hsD], by omega_using [], by omega_using [hD, hsD], by omega_using [hk, hk2, hsD]⟩
    (mW_args _ _ _ _ _ _))) fun t9 ⟨⟨L9, rd9, wr9, cs9, V9, W9, R9, hW9, hV9⟩, sp9, mx9, f9⟩ => ?_)
  obtain he9 : EnvE s t9 := he8.step rd9 wr9 sp9 (fun r hr _ => cs9 r hr) mx9 f9
  -- The call.
  obtain W9e : ∀ k, 21 ≤ k → k ≤ 26 → W9 k = encW s k := fun k h1 h2 => by
    rw [hW9 k (by unfold nW frameBytes; omega_using [h2]) (by omega_using [h1]) (by omega_using [h1])
      (by omega_using [h2]) (by omega_using [h2]), mW_other (by omega_using [h1]),
      W7e k (by omega_using [h1, h2]) (by unfold nW frameBytes; omega_using [h2]) (by omega_using [h1]) (by omega_using [h1])]
    exact hW5 k (.inr ⟨h1, by omega_using [h2]⟩)
  obtain e1 : (s.gpr .rcx).toNat - (Hl.D + 1) = (s.gpr .rcx).toNat - Hl.D - 1 := by omega_using []
  rw [hsD, e1] at hV7 hV9
  obtain hm : ∀ o, o < (s.gpr .rcx).toNat → mOut o := fun o ho => (mOut_iff o).mpr (.inl (by omega_using [hk2, cS, ho]))
  have hlen : mH.G.len = Hl.D := mH.len
  obtain hsdl : (Spec.Rsa.bytesAt s.mem (stackArg s 4) mH.G.len).length = Hl.D := by simp [Spec.Rsa.bytesAt, hlen]
  obtain hlhl : (mH.G.hash (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)).length = Hl.D := by
    rw [(valid_of_link hH mH).2, hlen]
  obtain hml : (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat).length = (stackArg s 3).toNat := by
    simp [Spec.Rsa.bytesAt]
  obtain hsrc : srcB V7 (oEm + 1 + Hl.D) ((s.gpr .rcx).toNat - Hl.D - 1) =
      srcB (mixV V5 (Spec.Mgf1.mgf1 mG.G (srcB V5 1 Hl.D) ((s.gpr .rcx).toNat - Hl.D - 1)) (1 + Hl.D)
        ((s.gpr .rcx).toNat - Hl.D - 1)) (1 + Hl.D) ((s.gpr .rcx).toNat - Hl.D - 1) :=
    List.map_congr_left fun i hi => by
      have := List.mem_range.mp hi
      exact hV7 _ (by unfold oRsa; omega_using [hk2, c0, this]) (hm _ (by unfold oEm; omega_using [this]))
  obtain hlist : (List.range (s.gpr .rcx).toNat).map (fun i => V9 (oEm + i)) =
      emOf mG.G Hl.D (s.gpr .rcx).toNat (stackArg s 3).toNat (Spec.Rsa.bytesAt s.mem (stackArg s 4) mH.G.len)
        (mH.G.hash (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat))
        (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat) := by
    unfold emOf
    rw [← em_mask (valid_of_link hG mG) (V₁ := V5) (by omega_using [hk]) hsdl (by
        simp only [List.length_append, List.length_cons, hlhl, hml, Spec.RsaOaep.zeros, List.length_replicate]; omega_using [hk])
      E.z0 E.sd (E.db hlhl hml hk)]
    refine List.map_congr_left fun i hi => ?_
    obtain hi' := List.mem_range.mp hi
    rw [show oEm + i = i by unfold oEm; omega_using [], hV9 _ (by unfold oRsa; omega_using [hk2, hi']) (hm _ hi'), hsrc]
    exact mixV_congr _ _ _ (hV7 _ (by unfold oRsa; omega_using [hk2, hi']) (hm _ hi'))
  exact hrest t9 V9 W9 he9 L9 R9 W9e hlist

end VG.Proof.RsaOaep.X86_64
