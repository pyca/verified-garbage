module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.Label
public import VerifiedGarbage.Proof.RsaOaep.X86_64.MgfT
import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-!
# RSAES-OAEP on x86-64: the label's hash with the hash function of a table

`hashLabelT f o` writes the label's hash `H(label)` to `scratch + o` as
`hashLabel` does (`hashLabelT_ok`, as `hashLabel_ok`), for `H` the hash
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
    (R : Rep u.mem F S V W) (h35 : W 35 = p) (hrd : InRegions (u.rd ++ u.wr) (off p 32) 8) {D : Nat}
    (hD : u.mem.readW (off p 32) 64 = BitVec.ofNat 64 D) :
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
  simp only [lens, List.mem_cons, List.not_mem_nil, or_false] at h; omega

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
    VG.Proof.Bignum.X86_64.ofNat_sub_beq (show d < 2 ^ 64 by omega) (show x < 2 ^ 64 by omega),
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
  have hdig := hr6 _ (hm5 ▸ hR4) (by rw [hlb]; omega) (by rw [hsi5, hlb])
  have hlab : Spec.Rsa.bytesAt u2.mem lab labLen = Spec.Rsa.bytesAt u.mem lab labLen := by
    rw [← hm1]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => hF2.bytes (R := ⟨lab, labLen⟩) (fun r hr => ?_)
      (by show labLen ≤ 2 ^ 64; omega) (List.mem_range.mp hi)
    rcases List.mem_append.mp hr with hr | hr
    · simp only [regs, List.map_cons, List.map_nil, List.mem_singleton] at hr; subst hr
      have h1 : oSt + G.S ≤ oRsa := by unfold oSt oRsa; omega
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
    rw [hV6 _ (by simp only [inR_cons, inR_nil, or_false]; omega),
      hV4 _ (by simp only [inR_cons, inR_nil, or_false]; omega),
      hV2 _ (by simp only [inR_cons, inR_nil, or_false]; omega)]
  · rw [hV6' _ (by simp only [inR_cons, inR_nil, or_false]; omega), hdig i hi, hHh, hlab]

end VG.Proof.RsaOaep.X86_64
