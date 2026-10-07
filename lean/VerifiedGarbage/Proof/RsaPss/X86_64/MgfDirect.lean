import VerifiedGarbage.Proof.RsaPss.X86_64.CtHashOk

/-! One-block MGF1 hashing without masked state selection. -/
namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Bignum (off off_off)
open VG.Proof.Bignum.X86_64 (Scr ofNat_add_one ofNat_sub_beq wp_upto)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.RsaPss (lastBlk padded)

theorem startZero_ok {t : State} {F S : Addr} (L : Lay t F S)
    {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep t.mem F S V W) :
    WP isa (.block [.mov32 .rax (.imm 0), .store (sp sB) .rax]) t fun u =>
      Lay u F S ∧ Keep [.rax] t u ∧ Rep u.mem F S V (upd W 29 (BitVec.ofNat 64 0)) := by
  refine WP.mono (WP.keep [.rax] (Q := fun u =>
    u.mem = t.mem.writeW (off F sB) (BitVec.ofNat 64 0)) ?_ rfl) fun u ⟨hm, hk⟩ => ?_
  · xrun [ea_sp, L.rsp, L.st (d := sB) (by decide)]
    rfl
  have R0 := R.wf L.geo (k := 29) (by decide) (BitVec.ofNat 64 0)
  rw [show off F (8*29) = off F sB from rfl, ← hm] at R0
  exact ⟨L.of_rep' R R0 (by simp [upd]) (hk.gpr (by decide)) hk.2.2, hk, R0⟩

variable {H : Hash} (hH : HashOK H) (K : Callees H)

include K in
theorem mgfDirectHash_gen {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) {ℓ nbm : Nat} (hl : W 27 = BitVec.ofNat 64 ℓ)
    (hn : W 28 = BitVec.ofNat 64 nbm) (hfit : ℓ + 1 + H.P.L ≤ nbm * H.P.B) (hnb : nbm * H.P.B ≤ 2048)
    (hℓ : ℓ = H.D + 4) (hone : ℓ + H.P.L < H.P.B) :
    WP isa (mgfDirectHash H) t fun t' => Lay t' F S ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
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
  have fb0 : lastBlk H.P.B H.P.L ℓ = 0 := Nat.div_eq_of_lt hone
  have hBB : H.P.B ≤ nbm * H.P.B := by
    have : 1 ≤ nbm := by omega
    exact Nat.le_mul_of_pos_left _ this
  unfold mgfDirectHash seqs seqs seqs seqs seqs seqs
  -- `init`.
  refine WP.seq (WP.mono (ctInit_ok hH K L R) fun u1 ⟨L1, rd1, wr1, cs1, R1, iv1⟩ => ?_)
  -- `0x80`.
  refine WP.seq (WP.mono (fixedPad80_ok L1 R1 (ℓ := H.D + 4) (N := nbm * H.P.B) (by omega) hnb) fun u2 P0 => ?_)
  have P : PadResult u1 F S _ _ ℓ (nbm * H.P.B) u2 := hℓ.symm ▸ P0
  -- The length field.
  refine WP.seq (WP.mono (lenField_ok hH P.L P.R hl (by omega)) fun u3 ⟨L3, k3, R3⟩ => ?_)
  -- Into the last block.
  refine WP.seq (WP.mono (lenLoop_ok hH L3 R3 (len := hH.md.lenBytes ℓ) (fun i hi => by
      simp only [lenV, hH.md.lenBytes_length]; rw [ifp (by omega), Nat.add_sub_cancel_left])
    (by simp [upd]) (by simp [upd, hn]) hfb hnb) fun u4 O => ?_)
  -- A single compression suffices; its state is already the output state.
  refine WP.seq (WP.mono (startZero_ok O.L O.R) fun u0 ⟨L0, k0, R0⟩ => ?_)
  refine WP.seq (WP.mono (compCall_ok hH L0 R0 (b := 0) (by omega) (by simp [upd]))
    fun u5 ⟨L5, rd5, wr5, cs5, R5, st5⟩ => ?_)
  have iv0 : hH.md.stateAt u0.mem (off S oSt) = hH.iv := by
    rw [← iv1]
    refine stateAt_rep hH R1 R0 (by unfold oSt oRsa; omega) fun i hi => ?_
    simp only [lenAt, lenV, v80]
    rw [ifn (by unfold oY oSt; omega), ifn (by unfold oLen oSt; omega), ifn (by unfold oY oSt; omega)]
  refine WP.mono (digestAt_ok hH L5 R5 (src := oSt) (by unfold oSt oDig; omega))
    fun u6 ⟨L6, k6, R6⟩ => ?_
  have hO0 : (if 0 < nbm then H.P.L else 0) = H.P.L := by rw [ifp (by omega)]
  have hO : (if lastBlk H.P.B H.P.L ℓ < nbm then H.P.L else 0) = H.P.L := by rw [ifp hfb]
  have c1 : oY = 3584 := rfl
  have c2 : oLen = 2368 := rfl
  have c3 : oDig = 2304 := rfl
  have c4 : oSt = 2048 := rfl
  have c5 : oSel = 2240 := rfl
  have hso := hH.hso
  have hfbB' : H.P.B * lastBlk H.P.B H.P.L ℓ + H.P.B ≤ 2048 := by
    rw [← Nat.mul_add_one]; omega
  refine ⟨L6, k6.2.1.trans (rd5.trans (k0.2.1.trans (O.keep.2.1.trans (k3.2.1.trans (P.keep.2.1.trans rd1))))),
    k6.2.2.trans (wr5.trans (k0.2.2.trans (O.keep.2.2.trans (k3.2.2.trans (P.keep.2.2.trans wr1))))), ?_, _, _, R6, ?_, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have hcs : r ∈ calleeSaved := by rcases hr with rfl | rfl | rfl | rfl <;> decide
    have h1 : r ∉ [Reg.rbx, .rbp, .rax] := by rcases hr with rfl | rfl | rfl | rfl <;> decide
    have h2 : r ∉ [Reg.rcx, .rsi, .rdx, .r10, .r8, .r11, .r9, .rax, .rdi] := by
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    have h3 : r ∉ [Reg.rbx, .r12, .rax] := by rcases hr with rfl | rfl | rfl | rfl <;> decide
    have h4 : r ∉ [Reg.rcx, .rdx, .r10, .r8, .rax, .r9] := by rcases hr with rfl | rfl | rfl | rfl <;> decide
    rw [k6.gpr h1, cs5 r hcs, k0.gpr (by rcases hr with rfl | rfl | rfl | rfl <;> decide), O.keep.gpr h2, k3.gpr h3, P.keep.gpr h4, cs1 r hcs]
  · intro o ho ⟨h1, h2⟩
    have hno : ¬ (oDig ≤ o ∧ o < oDig + H.P.N) := by omega
    simp only [hno, ite_false]
    simp only [lenAt, lenV, v80, inR_cons, inR_nil, or_false]
    rw [ifn (by omega), ifn (by omega), ifn (by rw [hH.md.lenBytes_length]; omega), ifn (by omega), ifn (by omega)]
  · intro k hk h29 h30
    simp [upd, h29, h30]
  · intro msg hml hY
    subst hml
    rw [hH.hash, MdStream.Md.hash, ← range_map_getD (by rw [hH.md.digest_length]; exact hDN)]
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    simp only [show oDig ≤ oDig + i ∧ oDig + i < oDig + H.P.N from ⟨by omega, by omega⟩,
      Nat.add_sub_cancel_left]
    rw [st5, iv0]
    refine congrArg (fun x => (hH.md.digest x).getD i 0) ?_
    have fbmsg : lastBlk H.P.B H.P.L msg.length = 0 := fb0
    rw [RsaPss.pad_length hH.md msg hB0 (by omega), fbmsg,
      Nat.zero_add, Nat.mul_one, Nat.div_self hB0, MdStream.Md.compressList_one]
    refine congrArg (hH.md.compress hH.iv) (hH.md.parse_congr fun j hj => ?_)
    simp only [Nat.mul_zero, Nat.add_zero]
    rw [RsaPss.pad_getD hH.md msg hB0 (by omega) (by simpa only [fbmsg, Nat.zero_add, Nat.mul_one] using hj), hO0]
    refine y_padded msg _ fbmsg.symm (by omega) (hH.md.lenBytes_length _) _ (fun j' hj' => ?_) j (by
      simpa only [fbmsg, Nat.zero_add, Nat.mul_one] using hj)
    simp only [lenV, v80, inR_cons, inR_nil, or_false, hH.md.lenBytes_length]
    rw [ifn (by omega), ifp (by omega), ifn (by omega), Nat.add_sub_cancel_left, hY j' (by omega)]

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
  unfold mgfHash
  split
  · rename_i hOne
    exact WP.mono (mgfDirectHash_gen hH K L R hl hn hfit hnb hml (by rw [hml]; exact hOne))
      fun _ ⟨L', rd, wr, cs, V', W', R', hV, hW, hd⟩ =>
        ⟨L', rd, wr, cs, V', W', R', hV, hW, hd msg rfl hY⟩
  · exact mgfGenericHash_ok hH K L R hml hl hn hfit hnb hY

end VG.Proof.RsaPss.X86_64
