module

public import VerifiedGarbage.Proof.RsaOaep.AArch64.Label
public import VerifiedGarbage.Proof.RsaOaep.AArch64.MgfT
import VerifiedGarbage.Proof.RsaOaep.AArch64.Mgf
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hash

/-!
# RSAES-OAEP on AArch64: the label's hash with the hash function of a table

As on x86-64 (`Proof/RsaOaep/X86_64/LabelT.lean`): `hashLabelT f o` writes
the label's hash `H(label)` to `scratch + o` as `hashLabel` does
(`hashLabelT_ok`), for `H` the hash function of the table whose address is
in the slot `sTab` (word 32): each of its calls is an indirect call
(`tcall`) that reaches `H`'s function (`Table.TabAt`). And the pieces that
pick the code for the table's digest length: its address to `sTab`
(`tabSlot_ok`), its digest length to `x16` (`lenLoad_ok`) and the branch on
it (`byLen_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.AArch64

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Impl.RsaOaep.AArch64.Mgf1 (seqs)
open VG.Impl.RsaOaep.AArch64.Mgf1.Table (Fns tcall)
open VG.Impl.Pbkdf2.Md.AArch64 (Stream Hash)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (StreamOK)
open VG.Proof.RsaOaep.AArch64.Table (Tab TabAt tcall_ok initT_ok finT_ok wp_sy)

/-! ## The table and its digest length -/

/-- The address of the table that is our stack argument `j` to its slot. -/
theorem tabSlot_ok {G : Stream} {f : Fns} {j : Nat} (hj : arg j < 32768 ∧ arg j % 8 = 0) {u : State}
    {F S p : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep u.mem F S V W)
    (T : Tab G f F S p (arg j) u) :
    WP isa (.block (tabSlot j)) u fun u' => Lay u' F S ∧ Step F S [] u u' ∧ Rep u'.mem F S V (upd W 32 p) ∧
      u'.gpr .x0 = u.gpr .x0 := by
  have G' := L.geo
  have R1 : Rep (u.mem.write (off F 256) 8 p) F S V (upd W 32 p) := R.wq G' (k := 32) (by decide) _
  have w256 : InRegions u.wr (F + BitVec.ofNat 64 256) 8 := L.st (d := 256) (by decide)
  have ha : u.mem.read (F + BitVec.ofNat 64 (arg j)) 8 = p := by
    simpa [Mem.readW] using (T.mem _ (Frame.refl _ _)).2.2
  refine WP.mono (Q := fun (u' : State) => u'.mem = u.mem.write (off F 256) 8 p ∧ u'.rd = u.rd ∧
      u'.wr = u.wr ∧ u'.sp = u.sp ∧ u'.v = u.v ∧ (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u.gpr r) ∧
      u'.gpr .x0 = u.gpr .x0) ?_
    fun u' ⟨hm, hrd, hwr, hsp, hv, hcs, h0⟩ => ?_
  · oaep_run [tabSlot, sTab, T.rdA, L.sp, ha, w256, BitVec.add_zero, hj.1, hj.2]
    oaep_fin
  have R' : Rep u'.mem F S V (upd W 32 p) := by rw [hm]; exact R1
  refine ⟨L.congr hsp hwr ?_, ⟨hrd, hwr, hsp, hcs, fun r _ => by rw [hv], ?_⟩, R', h0⟩
  · rw [show sScr = 8 * 12 from rfl, R'.fr 12 (by decide), R.fr 12 (by decide)]; rfl
  · rw [hm]; exact Frame.write (Frame.refl _ _) (List.mem_cons_self ..) _ (cF F (by decide))

/-- The digest length of the table at `p`, whose address is in its slot, to
`x16`. -/
theorem lenLoad_ok {u : State} {F S p : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) (h32 : W 32 = p) (hrd : InRegions (u.rd ++ u.wr) (off p 32) 8) {D : Nat}
    (hD : u.mem.readW (off p 32) 64 = BitVec.ofNat 64 D) :
    WP isa (.block lenLoad) u fun u' => Step F S [] u u' ∧ u'.mem = u.mem ∧ u'.gpr .x16 = BitVec.ofNat 64 D ∧
      u'.gpr .x0 = u.gpr .x0 := by
  have h256 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 256) 8 := L.ld (d := 256) (by decide)
  have r32 := R.rd8 (d := 256) (k := 32) rfl (by decide) h32
  have hD' : u.mem.read (p + BitVec.ofNat 64 32) 8 = BitVec.ofNat 64 D := by simpa [Mem.readW] using hD
  oaep_run [lenLoad, sTab, h256, L.sp, r32, hrd, hD']
  oaep_fin

theorem mem_lens {G : Spec.Mgf1.Hash} (h : G ∈ VG.Proof.Pbkdf2.Md.AArch64.mdHashes) : G.len ∈ lens := by
  simp only [VG.Proof.Pbkdf2.Md.AArch64.mdHashes, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem mem_lens_lt {d : Nat} (h : d ∈ lens) : d < 4096 := by
  simp only [lens, List.mem_cons, List.not_mem_nil, or_false] at h; omega

theorem ofNat_sub_beq {j N : Nat} (hj : j < 2 ^ 64) (hN : N < 2 ^ 64) :
    (BitVec.ofNat 64 j - BitVec.ofNat 64 N == 0) = decide (j = N) := by
  by_cases h : j = N
  · subst h; simp
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    apply h
    have e : BitVec.ofNat 64 j = BitVec.ofNat 64 N := by bv_omega
    have := congrArg BitVec.toNat e
    rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hN] at this

/-- The comparison of the digest length `d` in `x16` with `x`: `x17` zero iff
they are equal. -/
theorem cmpLen_ok {F S : Addr} {u : State} {d x : Nat} (h16 : u.gpr .x16 = BitVec.ofNat 64 d) (hd : d < 4096)
    (hx : x < 4096) :
    WP isa (.block [.subImm .x .x17 .x16 x]) u fun u' => (u'.gpr .x17 == 0) = decide (d = x) ∧
      Step F S [] u u' ∧ u'.mem = u.mem ∧ (∀ r, r ≠ .x17 → u'.gpr r = u.gpr r) := by
  oaep_run [h16, hx]
  refine ⟨?_, blk_step, trivial, fun r hr => by simp [hr]⟩
  rw [ofNat_sub_beq (by omega) (by omega)]

/-- The code for the digest length `d` in `x16`, from a state that differs
only in `x17`. -/
theorem byLen_ok {F S : Addr} {b : Nat → Prog isa} : ∀ {ds : List Nat} {d : Nat}, d ∈ ds →
    (∀ x ∈ ds, x < 4096) → d < 4096 → ∀ {u : State} {Q : State → Prop}, u.gpr .x16 = BitVec.ofNat 64 d →
    (∀ u', Step F S [] u u' → u'.mem = u.mem → u'.syms = u.syms → (∀ r, r ≠ .x17 → u'.gpr r = u.gpr r) →
      WP isa (b d) u' Q) →
    WP isa (byLen b ds) u Q
  | [], _, h, _, _, _, _, _, _ => absurd h List.not_mem_nil
  | [x], d, h, _, _, u, _, _, hb => by
    obtain rfl := List.mem_singleton.mp h
    exact hb u (Step.refl _ _ _ _) rfl rfl fun _ _ => rfl
  | x :: y :: ds, d, h, hx, hd, u, Q, h16, hb => by
    refine WP.seq (WP.mono (wp_sy (cmpLen_ok (F := F) (S := S) h16 hd (hx x (List.mem_cons_self ..))))
      fun u' ⟨⟨hz, st, hm, hg⟩, hs⟩ => ?_)
    refine WP.ite (M := isa) _ (show isa.eval (.zero .x .x17) u' = some (decide (d = x)) by
      show eval (.zero .x .x17) u' = _
      simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hz]) (fun he => ?_) (fun he => ?_)
    · rw [decide_eq_true_eq] at he; subst he
      exact hb u' st hm hs hg
    · rw [decide_eq_false_iff_not] at he
      have hm' : d ∈ y :: ds := (List.mem_cons.mp h).resolve_left he
      exact byLen_ok hm' (fun z hz => hx z (List.mem_cons_of_mem _ hz)) hd ((hg _ (by decide)).trans h16)
        fun u'' st' hm'' hs'' hg'' => hb u'' (st.trans st') (hm''.trans hm) (hs''.trans hs)
          fun r hr => (hg'' r hr).trans (hg r hr)

/-! ## The label's hash -/

variable {G : Hash} (hG : StreamOK G.stream) {f : Fns}

include hG in
/-- `update` with the `len` bytes at `d`, outside our working space, by an
indirect call. -/
theorem updExtT_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) {p : Addr} (hp : W 32 = p) (T : TabAt G.stream f p t) {d : Addr} {len : Nat}
    (hlen : len < 2 ^ 64) (hcd : Covers [⟨d, len⟩] (t.rd ++ t.wr)) (hds : Region.Disjoint ⟨d, len⟩ ⟨S, oRsa⟩)
    (hdk : (below F 16).Disjoint ⟨d, len⟩)
    (h0 : t.gpr .x0 = off S oSt) (h2 : t.gpr .x2 = d) (h3 : t.gpr .x3 = BitVec.ofNat 64 len)
    (h4 : t.gpr .x4 = off S oW) :
    WP isa (tcall sTab 1 f.upd) t fun t' => Lay t' F S ∧ Step F S [] t t' ∧
      Rep t'.mem F S (fun o => if inR [(oSt, G.stream.S), (oW, hG.Wb)] o then t'.mem (off S o) else V o) W ∧
      (∀ m, hG.SH.Repr t.mem (off S oSt) m → t.gpr .x1 = BitVec.ofNat 64 m.length →
        hG.SH.Repr t'.mem (off S oSt) (m ++ Spec.Rsa.bytesAt t.mem d len)) :=
  tcall_ok L R hp (by decide) (T.rd 1 (by decide)) T.mem.2.1 T.ok.u fun u st hm _ x0 x1 x2 x3 x4 =>
    WP.mono (updExt_ok hG (L.congr st.sp st.wr (by rw [hm])) (hm ▸ R) hlen (by rw [st.rd, st.wr]; exact hcd)
        hds hdk (x0.trans h0) (x2.trans h2) (x3.trans h3) (x4.trans h4) [])
      fun t' ⟨L', S', R', hr'⟩ => ⟨L', st.trans S', R', fun m hm' hc => by
        have := hr' m (hm ▸ hm') (x1.trans hc)
        rwa [hm] at this⟩

include hG in
/-- The label's hash to `scratch + o`, with the hash function of the table
at `p`, whose address is in the slot `sTab` (`W 32`): the table of `Tab`
from the state `u`. -/
theorem hashLabelT_ok {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hG.SH.H.hash x) {u : State} {F S p : Addr}
    {sArg : Nat} (T : Tab G.stream f F S p sArg u) (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) (hp : W 32 = p) {lab : Addr} {labLen : Nat} (A : LabAt u F S W lab labLen) {o : Nat}
    (ho : o = oDig ∨ o = oLh) :
    WP isa (hashLabelT f o) u fun u' => Lay u' F S ∧ Step F S [] u u' ∧
      ∃ V', Rep u'.mem F S V' W ∧ (∀ x, ¬ inR (labR o) x → V' x = V x) ∧
        ∀ i < G.D, V' (o + i) = (Hs.hash (Spec.Rsa.bytesAt u.mem lab labLen)).getD i 0 := by
  obtain ⟨hzS, hzF, hzW, hzDF, hzD⟩ := sizes hG
  have eD : G.stream.D = G.D := rfl
  rw [eD] at hzDF hzD
  have hoo : oSt + 256 ≤ o ∧ o + 64 ≤ oW := by rcases ho with rfl | rfl <;> decide
  have hlen := A.len
  unfold hashLabelT seqs seqs seqs seqs seqs
  refine WP.seq (WP.mono (wp_sy (initArgs_ok L [])) fun u1 ⟨⟨S1, hm1, x01⟩, sy1⟩ => ?_)
  have L1 : Lay u1 F S := L.congr S1.sp S1.wr (by rw [hm1])
  have R1 : Rep u1.mem F S V W := hm1 ▸ R
  refine WP.seq (WP.mono (wp_sy (initT_ok hG L1 R1 hp (T.at S1 sy1) x01))
    fun u2 ⟨⟨L2, S2, R2, hr2⟩, sy2⟩ => ?_)
  obtain ⟨V2, R2, hV2, -⟩ := Rep.ex R2
  have A2 : LabAt u2 F S W lab labLen := A.congr (S2.rd.trans S1.rd) (S2.wr.trans S1.wr) rfl rfl
  refine WP.seq (WP.mono (wp_sy (labA_ok L2 R2 A2 [])) fun u3 ⟨⟨S3, hm3, x03, x13, x23, x33, x43⟩, sy3⟩ => ?_)
  have L3 : Lay u3 F S := L2.congr S3.sp S3.wr (by rw [hm3])
  have R3 : Rep u3.mem F S V2 W := hm3 ▸ R2
  have A3 : LabAt u3 F S W lab labLen := A2.congr S3.rd S3.wr rfl rfl
  have S13 := S1.trans (S2.trans S3)
  have sy13 : u3.syms = u.syms := sy3.trans (sy2.trans sy1)
  refine WP.seq (WP.mono (wp_sy (updExtT_ok hG L3 R3 hp (T.at S13 sy13) A3.len A3.cov A3.dS A3.dK x03 x23 x33
      x43)) fun u4 ⟨⟨L4, S4, R4, hr4⟩, sy4⟩ => ?_)
  have hR4 := hr4 [] (hm3 ▸ hr2) (by rw [x13]; rfl)
  rw [List.nil_append, hm3] at hR4
  obtain ⟨V4, R4, hV4, -⟩ := Rep.ex R4
  refine WP.seq (WP.mono (wp_sy (labF_ok L4 R4 A.hll (o := o) (by rcases ho with rfl | rfl <;> decide) []))
    fun u5 ⟨⟨S5, hm5, x05, x15, x25, x35⟩, sy5⟩ => ?_)
  have L5 : Lay u5 F S := L4.congr S5.sp S5.wr (by rw [hm5])
  have R5 : Rep u5.mem F S V4 W := hm5 ▸ R4
  have S15 := S13.trans (S4.trans S5)
  have sy15 : u5.syms = u.syms := sy5.trans (sy4.trans sy13)
  refine WP.mono (finT_ok hG L5 R5 hp (T.at S15 sy15) (o := o) (Or.inr hoo) x05 x25 x35)
    fun u6 ⟨L6, S6, R6, hr6⟩ => ?_
  have hlb : (Spec.Rsa.bytesAt u2.mem lab labLen).length = labLen := by
    simp [Spec.Rsa.bytesAt]
  have hdig := hr6 _ (hm5 ▸ hR4) (by rw [hlb]; omega) (by rw [x15, hlb])
  have hlab : Spec.Rsa.bytesAt u2.mem lab labLen = Spec.Rsa.bytesAt u.mem lab labLen := by
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => (S1.trans S2).frame.bytes (R := ⟨lab, labLen⟩) (fun r hr => ?_)
      (by show labLen ≤ 2 ^ 64; omega) (List.mem_range.mp hi)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [A.dF, A.dS, A.dK.symm]
  obtain ⟨V6, R6, hV6, hV6'⟩ := Rep.ex R6
  refine ⟨L6, S15.trans S6, V6, R6, fun x hx => ?_, fun i hi => ?_⟩
  · simp only [labR, inR_cons, inR_nil, or_false] at hx
    have : hG.Wb ≤ 1072 := hzW
    rw [hV6 _ (by simp only [inR_cons, inR_nil, or_false]; omega),
      hV4 _ (by simp only [inR_cons, inR_nil, or_false]; omega),
      hV2 _ (by simp only [inR_cons, inR_nil, or_false]; omega)]
  · rw [hV6' _ (by simp only [inR_cons, inR_nil, or_false]; omega), hdig i hi, hHh, hlab]

end VG.Proof.RsaOaep.AArch64
