import VerifiedGarbage.Proof.RsaPss.X86_64.CtComp
import VerifiedGarbage.Proof.RsaPss.X86_64.FixedPad

/-!
# RSASSA-PSS on x86-64: `ctHash`, verified

From a state whose `Y` holds a message of `ℓ` bytes followed by zeros up to
`nbm` blocks, with `ℓ` and `nbm` in their slots, `ctHash` leaves the
message's digest at `scratch + oDig` (`ctHash_ok`), changing only the start
of our working space, `Y`, and the slots of its counters.
-/

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Bignum (off off_off)
open VG.Proof.Bignum.X86_64 (Scr ofNat_add_one ofNat_sub_beq wp_upto)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.RsaPss (lastBlk padded)

/-- `Y` after the `0x80` and the length field: the padded message. -/
theorem y_padded {B L fb : Nat} (msg len : List Byte) (hfb : fb = lastBlk B L msg.length) (hLB : L < B)
    (hlen : len.length = L) (V : Nat → Byte)
    (hV : ∀ j < B * (fb + 1), V (oY + j) = msg.getD j 0 ||| (if j = msg.length then 0x80 else 0)) :
    ∀ j < B * (fb + 1), lenAt V len B L fb L (oY + j) = padded B L msg len j := by
  intro j hj
  have oz : ∀ x : Byte, x ||| 0 = x := fun x => BitVec.or_zero
  have zo : ∀ x : Byte, 0 ||| x = x := fun x => BitVec.zero_or
  have hfit : msg.length + L < B * (fb + 1) := by
    subst hfb; unfold lastBlk
    have := Nat.lt_div_mul_add (a := msg.length + L) (b := B) (by omega)
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm]; omega
  rw [Nat.mul_add, Nat.mul_one] at hj hfit
  simp only [lenAt, padded, ← hfb, hV j (by rw [Nat.mul_add, Nat.mul_one]; omega)]
  by_cases h1 : j < msg.length
  · rw [ifn (by omega), ifp h1, ifn (by omega), oz]
  · have hz : msg.getD j 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    rw [hz, zo, ifn h1]
    by_cases h2 : j = msg.length
    · rw [ifp h2, ifn (by omega), ifp h2]
    · rw [ifn h2, ifn h2]
      by_cases h3 : B * fb + B - L ≤ j ∧ j < B * fb + B
      · rw [ifp (by omega), ifp h3, zo, show oY + j - (oY + B * fb + (B - L)) = j - (B * fb + B - L) by omega]
      · rw [ifn (by omega), ifn h3]

variable {H : Hash} (hH : HashOK H) (K : Callees H)

/-- Where `ctHash` may change our working space: below `oLen + 16`, and `Y`. -/
def ctOut (o : Nat) : Prop := oLen + 16 ≤ o ∧ ¬ (oY ≤ o ∧ o < oY + 2048)

include K in
/-- `ctHash` on the first `ℓ` bytes of `Y` (`sL`), in `nbm` blocks (`sNb`):
what it changes, and its digest if those bytes are followed by zeros. -/
theorem ctHashWith_gen (padding : Prog isa) {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) {ℓ nbm : Nat} (hl : W 27 = BitVec.ofNat 64 ℓ)
    (hn : W 28 = BitVec.ofNat 64 nbm) (hfit : ℓ + 1 + H.P.L ≤ nbm * H.P.B) (hnb : nbm * H.P.B ≤ 2048)
    (hp : ∀ {u : State} {F' S' : Addr} {V' : Nat → Byte} {W' : Nat → BitVec 64},
      Lay u F' S' → Rep u.mem F' S' V' W' → W' 27 = BitVec.ofNat 64 ℓ →
      W' 28 = BitVec.ofNat 64 nbm → WP isa padding u (PadResult u F' S' V' W' ℓ (nbm * H.P.B))) :
    WP isa (ctHashWith H padding) t fun t' => Lay t' F S ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r ∈ [Reg.r13, .r14, .r15, .rsp], t'.gpr r = t.gpr r) ∧
      ∃ V' W', Rep t'.mem F S V' W' ∧ (∀ o < oRsa, ctOut o → V' o = V o) ∧
        (∀ k < nW, k ≠ 29 → k ≠ 30 → W' k = W k) ∧
        ∀ msg : List Byte, msg.length = ℓ → (∀ i < nbm * H.P.B, V (oY + i) = msg.getD i 0) →
          (List.range H.D).map (fun i => V' (oDig + i)) = hH.SH.H.hash msg := by
  have hB := hH.B_le
  have hB0 := hH.B_pos
  have hN := hH.N_le
  have hL := hH.dims.L
  have hNL := hH.hNL
  have hDN := hH.hDN
  have hnbm : nbm ≤ 2048 := Nat.le_trans (Nat.le_mul_of_pos_right nbm hB0) hnb
  have hfb : lastBlk H.P.B H.P.L ℓ < nbm := (Nat.div_lt_iff_lt_mul hB0).mpr (by omega)
  have hfbB : H.P.B * (lastBlk H.P.B H.P.L ℓ + 1) ≤ nbm * H.P.B := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ hfb
  unfold ctHashWith seqs seqs seqs seqs seqs
  -- `init`.
  refine WP.seq (WP.mono (ctInit_ok hH K L R) fun u1 ⟨L1, rd1, wr1, cs1, R1, iv1⟩ => ?_)
  -- `0x80`.
  refine WP.seq (WP.mono (hp L1 R1 hl hn) fun u2 P => ?_)
  -- The length field.
  refine WP.seq (WP.mono (lenField_ok hH P.L P.R hl (by omega)) fun u3 ⟨L3, k3, R3⟩ => ?_)
  -- Into the last block.
  refine WP.seq (WP.mono (lenLoop_ok hH L3 R3 (len := hH.md.lenBytes ℓ) (fun i hi => by
      simp only [lenV, hH.md.lenBytes_length]; rw [ifp (by omega), Nat.add_sub_cancel_left])
    (by simp [upd]) (by simp [upd, hn]) hfb hnb) fun u4 O => ?_)
  -- Every block.
  refine WP.seq (WP.mono (compLoop_ok hH O.L O.R ?_ (by simp [upd]) (by simp [upd, hn]) hfb hnb)
    fun u5 ⟨L5, rd5, wr5, cs5, V5, R5, keep5, st5, sel5⟩ => ?_)
  · rw [← iv1]
    refine stateAt_rep hH R1 O.R (by unfold oSt oRsa; omega) fun i hi => ?_
    simp only [lenAt, lenV, v80]
    rw [ifn (by unfold oY oSt; omega), ifn (by unfold oLen oSt; omega), ifn (by unfold oY oSt; omega)]
  -- The digest.
  refine WP.mono (digestOut_ok hH L5 R5) fun u6 ⟨L6, k6, R6⟩ => ?_
  have hO : (if lastBlk H.P.B H.P.L ℓ < nbm then H.P.L else 0) = H.P.L := by rw [ifp hfb]
  have c1 : oY = 3584 := rfl
  have c2 : oLen = 2368 := rfl
  have c3 : oDig = 2304 := rfl
  have c4 : oSt = 2048 := rfl
  have c5 : oSel = 2240 := rfl
  have hso := hH.hso
  have hfbB' : H.P.B * lastBlk H.P.B H.P.L ℓ + H.P.B ≤ 2048 := by
    rw [← Nat.mul_add_one]; omega
  have hsel := sel5 hfb
  refine ⟨L6, k6.2.1.trans (rd5.trans (O.keep.2.1.trans (k3.2.1.trans (P.keep.2.1.trans rd1)))),
    k6.2.2.trans (wr5.trans (O.keep.2.2.trans (k3.2.2.trans (P.keep.2.2.trans wr1)))), ?_, _, _, R6, ?_, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have hcs : r ∈ calleeSaved := by rcases hr with rfl | rfl | rfl | rfl <;> decide
    have h1 : r ∉ [Reg.rbx, .rbp, .rax] := by rcases hr with rfl | rfl | rfl | rfl <;> decide
    have h2 : r ∉ [Reg.rcx, .rsi, .rdx, .r10, .r8, .r11, .r9, .rax, .rdi] := by
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    have h3 : r ∉ [Reg.rbx, .r12, .rax] := by rcases hr with rfl | rfl | rfl | rfl <;> decide
    have h4 : r ∉ [Reg.rcx, .rdx, .r10, .r8, .rax, .r9] := by rcases hr with rfl | rfl | rfl | rfl <;> decide
    rw [k6.gpr h1, cs5 r hcs, O.keep.gpr h2, k3.gpr h3, P.keep.gpr h4, cs1 r hcs]
  · intro o ho ⟨h1, h2⟩
    have hno : ¬ (oDig ≤ o ∧ o < oDig + H.P.N) := by omega
    simp only [hno, ite_false]
    rw [keep5 o ho (by simp only [inR_cons, inR_nil, or_false]; omega)]
    simp only [lenAt, lenV, v80, inR_cons, inR_nil, or_false]
    rw [ifn (by omega), ifn (by rw [hH.md.lenBytes_length]; omega), ifn (by omega), ifn (by omega)]
  · intro k hk h29 h30
    simp [upd, h29, h30]
  · intro msg hml hY
    subst hml
    rw [hH.hash, MdStream.Md.hash, ← range_map_getD (by rw [hH.md.digest_length]; exact hDN)]
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    simp only [show oDig ≤ oDig + i ∧ oDig + i < oDig + H.P.N from ⟨by omega, by omega⟩,
      Nat.add_sub_cancel_left]
    rw [hsel]
    refine congrArg (fun x => (hH.md.digest x).getD i 0) ?_
    rw [RsaPss.pad_length hH.md msg hB0 (by omega), Nat.mul_div_cancel_left _ hB0]
    refine hH.md.compressList_congr fun j hj => ?_
    rw [yList_getD _ (by omega), RsaPss.pad_getD hH.md msg hB0 (by omega) hj, hO]
    refine y_padded msg _ rfl (by omega) (hH.md.lenBytes_length _) _ (fun j' hj' => ?_) j hj
    simp only [lenV, v80, inR_cons, inR_nil, or_false, hH.md.lenBytes_length]
    rw [ifn (by omega), ifp (by omega), ifn (by omega), Nat.add_sub_cancel_left, hY j' (by omega)]

include K in
theorem ctHash_gen {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) {ℓ nbm : Nat} (hl : W 27 = BitVec.ofNat 64 ℓ)
    (hn : W 28 = BitVec.ofNat 64 nbm) (hfit : ℓ + 1 + H.P.L ≤ nbm * H.P.B) (hnb : nbm * H.P.B ≤ 2048) :
    WP isa (ctHash H) t fun t' => Lay t' F S ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r ∈ [Reg.r13, .r14, .r15, .rsp], t'.gpr r = t.gpr r) ∧
      ∃ V' W', Rep t'.mem F S V' W' ∧ (∀ o < oRsa, ctOut o → V' o = V o) ∧
        (∀ k < nW, k ≠ 29 → k ≠ 30 → W' k = W k) ∧
        ∀ msg : List Byte, msg.length = ℓ → (∀ i < nbm * H.P.B, V (oY + i) = msg.getD i 0) →
          (List.range H.D).map (fun i => V' (oDig + i)) = hH.SH.H.hash msg := by
  have hfb : lastBlk H.P.B H.P.L ℓ < nbm :=
    (Nat.div_lt_iff_lt_mul hH.B_pos).mpr (by omega)
  exact ctHashWith_gen hH K (pad80 H) L R hl hn hfit hnb fun L' R' hl' hn' =>
    WP.mono (pad80_ok hH L' R' hl' hn' (by omega) hnb (by omega)) fun _ P => ⟨P.L, P.keep, P.R⟩


include K in
theorem ctHash_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) {msg : List Byte} {nbm : Nat} (hl : W 27 = BitVec.ofNat 64 msg.length)
    (hn : W 28 = BitVec.ofNat 64 nbm) (hfit : msg.length + 1 + H.P.L ≤ nbm * H.P.B) (hnb : nbm * H.P.B ≤ 2048)
    (hY : ∀ i < nbm * H.P.B, V (oY + i) = msg.getD i 0) :
    WP isa (ctHash H) t fun t' => Lay t' F S ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r ∈ [Reg.r13, .r14, .r15, .rsp], t'.gpr r = t.gpr r) ∧
      ∃ V' W', Rep t'.mem F S V' W' ∧ (∀ o < oRsa, ctOut o → V' o = V o) ∧
        (∀ k < nW, k ≠ 29 → k ≠ 30 → W' k = W k) ∧
        (List.range H.D).map (fun i => V' (oDig + i)) = hH.SH.H.hash msg :=
  WP.mono (ctHash_gen hH K L R hl hn hfit hnb) fun _ ⟨L', rd, wr, cs, V', W', R', hV, hW, hd⟩ =>
    ⟨L', rd, wr, cs, V', W', R', hV, hW, hd msg rfl hY⟩


include K in
theorem mgfHash_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) {msg : List Byte} {nbm : Nat} (hml : msg.length = H.D + 4) (hl : W 27 = BitVec.ofNat 64 msg.length)
    (hn : W 28 = BitVec.ofNat 64 nbm) (hfit : msg.length + 1 + H.P.L ≤ nbm * H.P.B) (hnb : nbm * H.P.B ≤ 2048)
    (hY : ∀ i < nbm * H.P.B, V (oY + i) = msg.getD i 0) :
    WP isa (mgfHash H) t fun t' => Lay t' F S ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r ∈ [Reg.r13, .r14, .r15, .rsp], t'.gpr r = t.gpr r) ∧
      ∃ V' W', Rep t'.mem F S V' W' ∧ (∀ o < oRsa, ctOut o → V' o = V o) ∧
        (∀ k < nW, k ≠ 29 → k ≠ 30 → W' k = W k) ∧
        (List.range H.D).map (fun i => V' (oDig + i)) = hH.SH.H.hash msg := by
  refine WP.mono (ctHashWith_gen hH K (fixedPad80 (H.D + 4)) L R hl hn hfit hnb ?_)
    fun _ ⟨L', rd, wr, cs, V', W', R', hV, hW, hd⟩ =>
      ⟨L', rd, wr, cs, V', W', R', hV, hW, hd msg rfl hY⟩
  intro u F' S' V' W' L' R' _ _
  simpa only [hml] using fixedPad80_ok L' R' (ℓ := H.D + 4) (N := nbm * H.P.B) (by omega) hnb

end VG.Proof.RsaPss.X86_64
