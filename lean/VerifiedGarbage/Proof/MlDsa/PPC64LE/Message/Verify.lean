module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Message.Sign
import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Common
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.MlDsa.Message.Common
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Message

/-!
# ML-DSA on PPC64LE, `verify_message`: correctness

As signing (`Sign.lean`), with `sig` in `r8` and `scratch` in `r9`: from a
state satisfying `MVPre`, `verifyMessage n f p` returns 2 if the context
string is longer than 255 bytes; otherwise it saves our caller's registers in
the 1 KiB at `E` (`MV1`), computes `tr = H(pk, 64)` into `840(E)` (`MV2`),
then `μ` of the formatted message from it in place (`MV3`), and calls the
verification function on `μ` `f`, whose result is the result
(`verifyMessage_wp`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Message

open VG VG.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Impl.MlDsa.PPC64LE.Message
open VG.Impl.Sha3.PPC64LE.Stream (mov)
open VG.Impl.Ed25519.PPC64LE.Whole (saveRegs restoreRegs slots)
open VG.Proof.Ed25519.PPC64LE.Whole (Inv slotArea restore_ok restoreList)
open VG.Impl.Sha3.PPC64LE.Pieces (Piece Len hash)
open VG.Proof.Sha3.PPC64LE.Pieces (Kept PieceOk KEnv kW hash_ok)
open VG.Proof.MlDsa.PPC64LE.KeyGen (Callee)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## The invariant -/

/-- What the registers hold: the arguments, and `E`. -/
def verifyV (p : Params) (s : State) : Reg → BitVec 64
  | .r22 => s.gpr .r3 | .r23 => s.gpr .r4 | .r24 => s.gpr .r5 | .r25 => s.gpr .r6 | .r26 => s.gpr .r7
  | .r27 => s.gpr .r8 | .r29 => s.gpr .r9 | .r30 => eAt p (s.gpr .r9) | _ => 0

/-- What the body may write. -/
abbrev vW (p : Params) (STK : Nat) (s : State) : List Region := [vscrR p s, below s.sp STK]

abbrev VInv (p : Params) (STK : Nat) (s : State) : State → Prop :=
  Inv s (eAt p (s.gpr .r9)) oSV verifyRegs (verifyV p s) (vW p STK s)

theorem verifyRegs_pres : ∀ r ∈ verifyRegs, r ∈ preserved := by decide

section
variable {p : Params} {STK : Nat} {s : State} (hF : MFacts p) (hp : MVPre p STK s) (h48 : 48 ≤ STK)

theorem v_e {t : State} (h : VInv p STK s t) : t.gpr .r30 = eAt p (s.gpr .r9) := h.regs _ (by decide)

theorem vslot_sub : Region.Sub (slotArea (eAt p (s.gpr .r9)) oSV verifyRegs) (vscrR p s) := e_sub (by decide)

theorem vslot_e {d n : Nat} (h : d + n ≤ oSV ∨ oSV + 72 ≤ d) (h₁ : d + n ≤ 1024) :
    (slotArea (eAt p (s.gpr .r9)) oSV verifyRegs).Disjoint ⟨eAt p (s.gpr .r9) + BitVec.ofNat 64 d, n⟩ :=
  e_e (h.symm.imp id id) (by decide) h₁

theorem vslot_e0 {n : Nat} (h : n ≤ oSV) :
    (slotArea (eAt p (s.gpr .r9)) oSV verifyRegs).Disjoint ⟨eAt p (s.gpr .r9), n⟩ :=
  (e_e0 h (by decide)).symm

include hF in
theorem vslot_w : (slotArea (eAt p (s.gpr .r9)) oSV verifyRegs).Disjoint ⟨s.gpr .r9, scratchWords p * 8⟩ :=
  (e_w hF (by decide)).symm

include hp h48 in
theorem vbelow48 : Region.Sub (below s.sp 48) (below s.sp STK) := below_sub h48 (by have := hp.stk; omega)

include hp h48 in
theorem vslot_b : (slotArea (eAt p (s.gpr .r9)) oSV verifyRegs).Disjoint (below s.sp 48) :=
  (hp.bx.symm.sub_left vslot_sub).sub_right (vbelow48 hp h48)

include hF hp in
theorem ve_in {t : State} (hw : t.wr = s.wr) {d n : Nat} (h : d + n ≤ 1024) :
    InRegions t.wr (eAt p (s.gpr .r9) + BitVec.ofNat 64 d) n := by
  rw [hw, hp.wr, e_add]
  exact in_base List.mem_cons_self (by rw [msw]; omega) (by have := hF.e; omega)

include hp in
theorem ve_cov {t : State} (hw : t.wr = s.wr) {d n : Nat} (h : d + n ≤ 1024) :
    PPC64LE.Covers [⟨eAt p (s.gpr .r9) + BitVec.ofNat 64 d, n⟩] t.wr := by
  rw [hw, hp.wr]
  refine Covers.of_sub fun r hr => ?_
  rw [List.mem_singleton.mp hr]
  exact ⟨vscrR p s, List.mem_cons_self, oE p + d, e_add _ _ _, by simp only [msw]; omega⟩

include hp in
theorem ve_cov0 {t : State} (hw : t.wr = s.wr) {n : Nat} (h : n ≤ 1024) :
    PPC64LE.Covers [⟨eAt p (s.gpr .r9), n⟩] t.wr := by
  have := ve_cov hp hw (d := 0) (n := n) (by omega)
  rwa [BitVec.add_zero] at this

/-- The inputs, while the body runs: none of them is in `vW`. -/
theorem v_keep {t : State} (h : VInv p STK s t) {R : Region} (hn : R.len < 2 ^ 64)
    (hc : R.Disjoint (vscrR p s)) (hb : (below s.sp STK).Disjoint R) :
    bytesAt t.mem R.base R.len = bytesAt s.mem R.base R.len := by
  refine Proof.Sha3.PPC64LE.Pieces.bytes_keep h.frame hn fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hc
  · exact hb.symm

end

/-! ## The setup -/

/-- After the setup: the invariant, and `0 ‖ ctx_len` at `oHdr(E)`. -/
structure MV1 (p : Params) (STK : Nat) (s t : State) : Prop where
  inv : VInv p STK s t
  hdr : bytesAt t.mem (eAt p (s.gpr .r9) + BitVec.ofNat 64 oHdr) 2 = [0, BitVec.ofNat 8 (s.gpr .r7).toNat]

theorem verifySetup_ok {p : Params} {STK : Nat} {s u : State} (hF : MFacts p) (hp : MVPre p STK s)
    (hu : ∀ r, r ≠ .r11 → u.gpr r = s.gpr r) (hrd : u.rd = s.rd) (hwr : u.wr = s.wr) (hsp : u.sp = s.sp)
    (hlr : u.lr = s.lr) (hm : u.mem = s.mem) :
    WP isa (.block (enter .r9 p verifyRegs verifyMs)) u (MV1 p STK s) := by
  unfold enter
  refine WP.block_append_iff.mpr (WP.mono (base_ok p hF (by decide) u) fun u₁ ⟨h₁, l₁⟩ => ?_)
  have g9 : u.gpr .r9 = s.gpr .r9 := hu _ (by decide)
  rw [g9] at h₁
  have hw₁ : u₁.wr = s.wr := h₁.wr.trans hwr
  refine setup_ok (v := verifyV p s) (W := vW p STK s) (by decide) (by decide) (by decide)
    (fun q hq => by rw [h₁.gpr]; exact ve_in hF hp hw₁ (by revert q; decide))
    ⟨vscrR p s, by simp, by rw [h₁.gpr]; exact vslot_sub⟩ rfl (by decide) (by decide) (fun q hq => by
      simp only [verifyMs, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      iterate 7 exact ((h₁.other _ (by decide)).trans (hu _ (by decide))).symm
      exact h₁.gpr.symm)
    fun t₁ i₁ => ?_
  rw [h₁.gpr] at i₁
  have i₁ : VInv p STK s t₁ := inv_rebase i₁ verifyRegs_pres (h₁.rd.trans hrd) hw₁ (h₁.sp.trans hsp)
    (l₁.trans hlr)
    (fun r hr => (h₁.other r fun e => by revert hr; rw [e]; decide).trans (hu r fun e => by revert hr; rw [e]; decide))
    (h₁.mem.trans hm)
  have g30 : t₁.gpr .r30 = eAt p (s.gpr .r9) := i₁.regs _ (by decide)
  have g26 : t₁.gpr .r26 = s.gpr .r7 := i₁.regs _ (by decide)
  refine hdr_ok (o := oHdr) (by decide) (by decide) (by decide) (by rw [g30]; exact ve_in hF hp i₁.wr (by decide))
    (by rw [g30]; exact ve_in hF hp i₁.wr (by decide)) fun t ht hrd' hwr' hsp' hg => WP.block_nil ⟨?_, ?_⟩
  · refine i₁.step verifyRegs_pres hrd' hwr' hsp' (fun r hr => hg r fun e => by revert hr; rw [e]; decide)
      (ht ▸ hdrMem_frame _ _ _) (fun r hr => ?_) fun r hr => ?_
    · rw [List.mem_singleton.mp hr, g30]; exact ⟨vscrR p s, by simp, e_sub (by decide)⟩
    · rw [List.mem_singleton.mp hr, g30]; exact vslot_e (.inr (by decide)) (by decide)
  · rw [ht, g30, g26, show s.gpr .r7 = BitVec.ofNat 64 (s.gpr .r7).toNat by simp, hdrMem_bytes]
    simp

/-! ## `tr` and `μ` -/

/-- The public key. -/
abbrev pkB (p : Params) (s : State) : List Byte := bytesAt s.mem (s.gpr .r3) p.pkLen

/-- The signature. -/
abbrev vsigB (p : Params) (s : State) : List Byte := bytesAt s.mem (s.gpr .r8) p.sigLen

/-- What a hash keeps of the invariant. -/
theorem vinv_hash {p : Params} {STK : Nat} {s t t' : State} (hp : MVPre p STK s) (h48 : 48 ≤ STK)
    (hi : VInv p STK s t)
    (k : Kept ([⟨eAt p (s.gpr .r9) + BitVec.ofNat 64 oMU, 64⟩] ++ kW 840 (eAt p (s.gpr .r9)) t.sp) t t') :
    VInv p STK s t' := by
  have hsp : t.sp = s.sp := hi.sp
  refine inv_kept hi verifyRegs_pres k (fun r hr => ?_) fun r hr => ?_
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨vscrR p s, by simp, e_sub (by decide)⟩
    · exact ⟨vscrR p s, by simp, e_sub0 (by decide)⟩
    · exact ⟨below s.sp STK, by simp, by rw [hsp]; exact vbelow48 hp h48⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact vslot_e (.inl (by decide)) (by decide)
    · exact vslot_e0 (by decide)
    · rw [hsp]; exact vslot_b hp h48

/-- After `tr`: the invariant, the header, and `tr` at `oMU(E)`. -/
structure MV2 (p : Params) (STK : Nat) (s t : State) : Prop where
  inv : VInv p STK s t
  hdr : bytesAt t.mem (eAt p (s.gpr .r9) + BitVec.ofNat 64 oHdr) 2 = [0, BitVec.ofNat 8 (s.gpr .r7).toNat]
  tr : bytesAt t.mem (eAt p (s.gpr .r9) + BitVec.ofNat 64 oMU) 64 = pkTr (pkB p s)

/-- After `μ`: the invariant, and `μ` at `oMU(E)`. -/
structure MV3 (p : Params) (STK : Nat) (s t : State) : Prop where
  inv : VInv p STK s t
  mu : bytesAt t.mem (eAt p (s.gpr .r9) + BitVec.ofNat 64 oMU) 64 = messageRep (pkTr (pkB p s)) (fmtB s)

section
variable {p : Params} {STK : Nat} {s t : State} (hF : MFacts p) (hp : MVPre p STK s) (h48 : 48 ≤ STK)
include hF hp h48

omit hF in
theorem vke (hi : VInv p STK s t) : KEnv 840 (eAt p (s.gpr .r9)) t :=
  ⟨by decide, ve_cov0 hp hi.wr (by decide), by rw [hi.sp]; have := hp.stk; omega,
    by rw [hi.sp]; exact (hp.bx.sub_left (vbelow48 hp h48)).sub_right (e_sub0 (by decide))⟩

theorem trHash_ins (hi : VInv p STK s t) :
    ∀ q ∈ [(⟨.r22, 0, .imm p.pkLen⟩ : Piece)], PieceOk 840 (eAt p (s.gpr .r9)) t q := by
  have g22 : t.gpr .r22 = s.gpr .r3 := hi.regs _ (by decide)
  have g30 := v_e hi
  have hsp : t.sp = s.sp := hi.sp
  have b48 := vbelow48 hp h48
  have eS := e_sub0 (p := p) (x := s.gpr .r9) (n := 840) (by decide)
  intro q hq
  rw [List.mem_singleton.mp hq]
  exact pieceOk_of (R := pkR p s) (by simp only [Piece.R, Piece.addr, Len.val, g22, BitVec.add_zero])
    (show Reg.r22 ∈ preserved by decide) (show (0 : Nat) < 2 ^ 15 by decide) hF.pk
    (cov_rd (by rw [hi.rd, hp.rd]; exact cov_in0 (k := p.pkLen) (by simp) (Nat.le_refl _)))
    (hp.kc.sub_right eS) (by rw [hsp]; exact hp.bk.sub_left b48)

theorem trHash_ok (h : MV1 p STK s t) : WP isa (trHash p) t (MV2 p STK s) := by
  have hi := h.inv
  have g22 : t.gpr .r22 = s.gpr .r3 := hi.regs _ (by decide)
  have g30 := v_e hi
  have hsp : t.sp = s.sp := hi.sp
  have b48 := vbelow48 hp h48
  have eS := e_sub0 (p := p) (x := s.gpr .r9) (n := 840) (by decide)
  have hin := trHash_ins hF hp h48 hi
  unfold trHash
  refine WP.mono (hash_ok (N := 840) (n := 64) (o := oMU) (out := eAt p (s.gpr .r9) + BitVec.ofNat 64 oMU)
    (by decide) (by decide) (by decide) (by decide) g30 (by rw [g30]) (vke hp h48 hi) (by simp) hin
    (ve_cov hp hi.wr (by decide)) (e_e0 (by decide) (by decide)).symm
    (by rw [hsp]; exact (hp.bx.sub_left b48).sub_right (e_sub (by decide)))) fun t' ⟨k', d'⟩ => ⟨?_, ?_, ?_⟩
  · exact vinv_hash hp h48 hi k'
  · rw [show bytesAt t'.mem (eAt p (s.gpr .r9) + BitVec.ofNat 64 oHdr) 2 =
      bytesAt t.mem (eAt p (s.gpr .r9) + BitVec.ofNat 64 oHdr) 2 from
      Proof.Sha3.PPC64LE.Pieces.bytes_keep k'.frame (by decide) fun r hr => by
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact e_e (.inr (by decide)) (by decide) (by decide)
        · exact (e_e0 (by decide) (by decide)).symm
        · rw [hsp]; exact ((hp.bx.sub_left b48).sub_right (e_sub (by decide))).symm, h.hdr]
  · rw [d']
    have kp : bytesAt t.mem (s.gpr .r3) p.pkLen = pkB p s :=
      v_keep hi (R := pkR p s) (by have := hF.pk; show p.pkLen < 2 ^ 64; omega) hp.kc hp.bk
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, Piece.bytes,
      Piece.addr, Len.val, g22, BitVec.add_zero]
    rw [kp]
    rfl

omit hF in
theorem muHash_ins (hi : VInv p STK s t) :
    ∀ q ∈ (⟨.r30, oMU, .imm 64⟩ : Piece) :: fmtPieces, PieceOk 840 (eAt p (s.gpr .r9)) t q := by
  have g23 : t.gpr .r23 = s.gpr .r4 := hi.regs _ (by decide)
  have g24 : t.gpr .r24 = s.gpr .r5 := hi.regs _ (by decide)
  have g25 : t.gpr .r25 = s.gpr .r6 := hi.regs _ (by decide)
  have g26 : t.gpr .r26 = s.gpr .r7 := hi.regs _ (by decide)
  have g30 := v_e hi
  have hsp : t.sp = s.sp := hi.sp
  have b48 := vbelow48 hp h48
  have eS := e_sub0 (p := p) (x := s.gpr .r9) (n := 840) (by decide)
  have cr : ∀ R ∈ [pkR p s, msgR s, ctxR s, vsigR p s], PPC64LE.Covers [R] (t.rd ++ t.wr) := fun R hR => by
    rw [hi.rd, hp.rd]; exact cov_rd fun a n ⟨r, hr, hc⟩ => ⟨r, by rw [List.mem_singleton.mp hr]; exact hR, hc⟩
  intro q hq
  simp only [fmtPieces, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact pieceOk_of (R := ⟨eAt p (s.gpr .r9) + BitVec.ofNat 64 oMU, 64⟩)
      (by simp only [Piece.R, Piece.addr, Len.val, g30]) (by decide) (by decide) (show 64 < 2 ^ 15 by decide)
      (Proof.Sha3.PPC64LE.Pieces.cov_right (ve_cov hp hi.wr (by decide))) (e_e0 (by decide) (by decide)).symm
      (by rw [hsp]; exact (hp.bx.sub_left b48).sub_right (e_sub (by decide)))
  · exact pieceOk_of (R := ⟨eAt p (s.gpr .r9) + BitVec.ofNat 64 oHdr, 2⟩)
      (by simp only [Piece.R, Piece.addr, Len.val, g30]) (by decide) (by decide) (show 2 < 2 ^ 15 by decide)
      (Proof.Sha3.PPC64LE.Pieces.cov_right (ve_cov hp hi.wr (by decide))) (e_e0 (by decide) (by decide)).symm
      (by rw [hsp]; exact (hp.bx.sub_left b48).sub_right (e_sub (by decide)))
  · exact pieceOk_of (R := ctxR s) (by simp only [Piece.R, Piece.addr, Len.val, g25, g26, BitVec.add_zero])
      (by decide) (by decide) (show Reg.r26 ∈ preserved by decide) (cr _ (by simp))
      (hp.cc.sub_right eS) (by rw [hsp]; exact hp.bc.sub_left b48)
  · exact pieceOk_of (R := msgR s) (by simp only [Piece.R, Piece.addr, Len.val, g23, g24, BitVec.add_zero])
      (by decide) (by decide) (show Reg.r24 ∈ preserved by decide) (cr _ (by simp))
      (hp.mc.sub_right eS) (by rw [hsp]; exact hp.bm.sub_left b48)

omit hF in
theorem verifyHash_ok (h : MV2 p STK s t) : WP isa (muHash ⟨.r30, oMU, .imm 64⟩) t (MV3 p STK s) := by
  have hi := h.inv
  have g23 : t.gpr .r23 = s.gpr .r4 := hi.regs _ (by decide)
  have g24 : t.gpr .r24 = s.gpr .r5 := hi.regs _ (by decide)
  have g25 : t.gpr .r25 = s.gpr .r6 := hi.regs _ (by decide)
  have g26 : t.gpr .r26 = s.gpr .r7 := hi.regs _ (by decide)
  have g30 := v_e hi
  have hsp : t.sp = s.sp := hi.sp
  have b48 := vbelow48 hp h48
  have eS := e_sub0 (p := p) (x := s.gpr .r9) (n := 840) (by decide)
  have cr : ∀ R ∈ [pkR p s, msgR s, ctxR s, vsigR p s], PPC64LE.Covers [R] (t.rd ++ t.wr) := fun R hR => by
    rw [hi.rd, hp.rd]; exact cov_rd fun a n ⟨r, hr, hc⟩ => ⟨r, by rw [List.mem_singleton.mp hr]; exact hR, hc⟩
  have hin := muHash_ins hp h48 hi
  unfold muHash
  refine WP.mono (hash_ok (N := 840) (n := 64) (o := oMU) (out := eAt p (s.gpr .r9) + BitVec.ofNat 64 oMU)
    (by decide) (by decide) (by decide) (by decide) g30 (by rw [g30]) (vke hp h48 hi) (by simp) hin
    (ve_cov hp hi.wr (by decide)) (e_e0 (by decide) (by decide)).symm
    (by rw [hsp]; exact (hp.bx.sub_left b48).sub_right (e_sub (by decide)))) fun t' ⟨k', d'⟩ => ⟨?_, ?_⟩
  · exact vinv_hash hp h48 hi k'
  · rw [d']
    have kc : bytesAt t.mem (s.gpr .r6) (s.gpr .r7).toNat = ctxB s :=
      v_keep hi (R := ctxR s) (BitVec.isLt _) hp.cc hp.bc
    have km : bytesAt t.mem (s.gpr .r4) (s.gpr .r5).toNat = msgB s :=
      v_keep hi (R := msgR s) (BitVec.isLt _) hp.mc hp.bm
    simp only [fmtPieces, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
      Piece.bytes, Piece.addr, Len.val, g23, g24, g25, g26, g30, BitVec.add_zero]
    rw [h.tr, h.hdr, kc, km]
    simp only [messageRep, H, List.append_assoc]

end

/-! ## The call of the verification function on `μ` -/

/-- The arguments of the call. -/
abbrev verifyArgs : List Instr := [mov .r3 .r22, .addi .r4 .r30 oMU, mov .r5 .r27, mov .r6 .r29]

theorem args4_ok {t : State} {a b c d : Reg} {i j k l : Nat} (ha : a ≠ .r0) (hb : b ≠ .r0) (hc : c ≠ .r0)
    (hd : d ≠ .r0) (hi : i < 2 ^ 15) (hj : j < 2 ^ 15) (hk : k < 2 ^ 15) (hl : l < 2 ^ 15)
    (hs : ∀ x ∈ [b, c, d], x ∈ preserved) {Q : State → Prop}
    (K : ∀ u, u.mem = t.mem → u.rd = t.rd → u.wr = t.wr → u.sp = t.sp → (∀ r ∈ preserved, u.gpr r = t.gpr r) →
      u.gpr .r3 = t.gpr a + BitVec.ofNat 64 i →
      u.gpr .r4 = t.gpr b + BitVec.ofNat 64 j → u.gpr .r5 = t.gpr c + BitVec.ofNat 64 k →
      u.gpr .r6 = t.gpr d + BitVec.ofNat 64 l → Q u) :
    WP isa (.block [.addi .r3 a i, .addi .r4 b j, .addi .r5 c k, .addi .r6 d l]) t Q := by
  have pb := Ed25519.PPC64LE.Whole.pres_args (hs b (by simp))
  have pc := Ed25519.PPC64LE.Whole.pres_args (hs c (by simp))
  have pd := Ed25519.PPC64LE.Whole.pres_args (hs d (by simp))
  exact wp_addi ha hi fun u₁ h₁ => wp_addi hb hj fun u₂ h₂ => wp_addi hc hk fun u₃ h₃ =>
    wp_addi hd hl fun u₄ h₄ => WP.block_nil <|
    K u₄ (by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem]) (by rw [h₄.rd, h₃.rd, h₂.rd, h₁.rd])
      (by rw [h₄.wr, h₃.wr, h₂.wr, h₁.wr]) (by rw [h₄.sp, h₃.sp, h₂.sp, h₁.sp]) (fun r hr => by
        obtain ⟨p3, p4, p5, p6, -⟩ := Ed25519.PPC64LE.Whole.pres_args hr
        rw [h₄.other _ p6, h₃.other _ p5, h₂.other _ p4, h₁.other _ p3])
      (by rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide), h₁.gpr])
      (by rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.gpr, h₁.other _ pb.1])
      (by rw [h₄.other _ (by decide), h₃.gpr, h₂.other _ pc.2.1, h₁.other _ pc.1])
      (by rw [h₄.gpr, h₃.other _ pd.2.2.1, h₂.other _ pd.2.1, h₁.other _ pd.1])

/-- What the verification function on `μ` returns. -/
abbrev vres (p : Params) (s : State) (r : BitVec 32) : Prop :=
  let v := fun b => verifyMu p b (pkB p s) (messageRep (pkTr (pkB p s)) (fmtB s)) (vsigB p s)
  (r = 1 ∧ ∃ b, v b = some true) ∨ (r = 0 ∧ v minBounds ≠ some true)

/-- After the arguments of the call: `μ`, and the arguments in `r3`–`r6`. -/
structure VA (p : Params) (STK : Nat) (s u : State) : Prop where
  ms : MV3 p STK s u
  r3 : u.gpr .r3 = s.gpr .r3
  r4 : u.gpr .r4 = eAt p (s.gpr .r9) + BitVec.ofNat 64 oMU
  r5 : u.gpr .r5 = s.gpr .r8
  r6 : u.gpr .r6 = s.gpr .r9

theorem verifyArgs_ok {p : Params} {STK : Nat} {s t : State} (h : MV3 p STK s t) :
    WP isa (.block verifyArgs) t (VA p STK s) := by
  have hi := h.inv
  have g22 : t.gpr .r22 = s.gpr .r3 := hi.regs _ (by decide)
  have g27 : t.gpr .r27 = s.gpr .r8 := hi.regs _ (by decide)
  have g29 : t.gpr .r29 = s.gpr .r9 := hi.regs _ (by decide)
  have g30 := v_e hi
  unfold verifyArgs mov
  refine args4_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) fun u um urd' uwr' usp' upres a3 a4 a5 a6 =>
    ⟨⟨hi.step verifyRegs_pres urd' uwr' usp' upres (by rw [um]; exact Frame.refl _ _)
      (fun _ h => absurd h List.not_mem_nil) (fun _ h => absurd h List.not_mem_nil), by rw [um]; exact h.mu⟩,
      ?_, ?_, ?_, ?_⟩
  · rw [a3, g22, BitVec.add_zero]
  · rw [a4, g30]
  · rw [a5, g27, BitVec.add_zero]
  · rw [a6, g29, BitVec.add_zero]

/-- What the verification function on `μ` reads and writes. -/
abbrev vRd (p : Params) (s : State) : List Region :=
  [pkR p s, ⟨eAt p (s.gpr .r9) + BitVec.ofNat 64 oMU, 64⟩, vsigR p s]
abbrev vWr (p : Params) (s : State) : List Region := [⟨s.gpr .r9, scratchWords p * 8⟩]

/-- The call's precondition, and its regions. -/
theorem verifyCall_pre {p : Params} {STK stk : Nat} {s u : State} (hF : MFacts p) (hp : MVPre p STK s)
    (hstk : stk ≤ STK) (h : VA p STK s u) :
    (verifyContract p PPC64LE.abi stk).pre (u.callEntry.withRegions (vRd p s) (vWr p s)) ∧
      PPC64LE.Covers (vRd p s ++ vWr p s) (u.rd ++ u.wr) ∧ PPC64LE.Covers (vWr p s) u.wr := by
  have iu := h.ms.inv
  have hstkS : STK ≤ s.sp.toNat := hp.stk
  have hE := hF.e
  have fx := hp.fx
  rw [msw] at fx
  have hsw : scratchWords p * 8 ≤ oE p := by simp only [oE]; omega
  have usp : u.sp = s.sp := iu.sp
  have urd : u.rd = s.rd := iu.rd
  have uwr : u.wr = s.wr := iu.wr
  have bs : Region.Sub (below s.sp stk) (below s.sp STK) := below_sub (by omega) (by omega)
  have muS : Region.Sub ⟨eAt p (s.gpr .r9) + BitVec.ofNat 64 oMU, 64⟩ (vscrR p s) := e_sub (by decide)
  have muW : Region.Disjoint ⟨s.gpr .r9, scratchWords p * 8⟩ ⟨eAt p (s.gpr .r9) + BitVec.ofNat 64 oMU, 64⟩ :=
    e_w hF (by decide)
  have muF : (eAt p (s.gpr .r9) + BitVec.ofNat 64 oMU).toNat + 64 ≤ 2 ^ 64 := e_fit hp.fx (by decide) (by decide)
  refine ⟨?_, ?_, ?_⟩
  · refine verify_pre ((ce_gpr _ _ _ (by decide)).trans h.r3) ((ce_gpr _ _ _ (by decide)).trans h.r4)
      ((ce_gpr _ _ _ (by decide)).trans h.r5) ((ce_gpr _ _ _ (by decide)).trans h.r6) rfl rfl
      (by simp only [State.withRegions_sp, State.callEntry_sp, usp]; omega)
      (hp.kc.sub_right w_sub) muW.symm (hp.gc.sub_right w_sub) ?_ ?_ ?_ ?_ hp.fk muF hp.fg (by omega)
    all_goals simp only [State.withRegions_sp, State.callEntry_sp, usp]
    · exact hp.bk.sub_left bs
    · exact (hp.bx.sub_left bs).sub_right muS
    · exact hp.bg.sub_left bs
    · exact (hp.bx.sub_left bs).sub_right w_sub
  · rw [urd, uwr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨pkR p s, by simp, 0, by simp, by simp⟩
    · exact ⟨vscrR p s, by simp, oE p + oMU, e_add _ _ _, e_len p (d := oMU) (n := 64) (by decide)⟩
    · exact ⟨vsigR p s, by simp, 0, by simp, by simp⟩
    · exact ⟨vscrR p s, by simp, 0, by simp, by simp only [msw]; omega⟩
  · rw [uwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    exact ⟨vscrR p s, by simp, 0, by simp, by simp only [msw]; omega⟩

theorem verifyCall_ok {p : Params} {STK S : Nat} {s t : State} (hF : MFacts p) (hp : MVPre p STK s)
    {f : Prog isa} (hf : Callee f (fun stk => verifyContract p PPC64LE.abi stk) S) (hS : S ≤ STK) {n : String}
    (h : MV3 p STK s t) :
    WP isa (.seq (.block verifyArgs) (.call n f)) t fun t' => VInv p STK s t' ∧
      vres p s ((t'.gpr .r3).setWidth 32) := by
  obtain ⟨stk, hstk, hver⟩ := hf.verified
  have hstkS : STK ≤ s.sp.toNat := hp.stk
  refine WP.seq (WP.mono (verifyArgs_ok h) fun u hu => ?_)
  have iu := hu.ms.inv
  have usp : u.sp = s.sp := iu.sp
  obtain ⟨hpre, hc, hw⟩ := verifyCall_pre hF hp (Nat.le_trans hstk hS) hu
  have hd : sdepth f < 2 ^ 64 := by have := hf.stack; omega
  refine WP.callAny hver.1 hpre hc hw (fun s' rd' wr' sp' fr' cs' post' => ?_) hd
  refine ⟨iu.step verifyRegs_pres rd' wr' sp' cs' fr' (fun r hr => ?_) fun r hr => ?_, ?_⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨vscrR p s, by simp, w_sub⟩
    · exact ⟨below s.sp STK, by simp, by rw [usp]; exact below_sub (by have := hf.stack; omega) (by omega)⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact vslot_w hF
    · rw [usp]
      exact (hp.bx.symm.sub_left vslot_sub).sub_right (below_sub (by have := hf.stack; omega) (by omega))
  · have q := verify_post post'
    simp only [State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem,
      State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r4 ∉ linkRegs by decide),
      State.callEntry_gpr _ (show Reg.r5 ∉ linkRegs by decide), hu.r3, hu.r4, hu.r5] at q
    rw [v_keep iu (R := pkR p s) (by have := hF.pk; show p.pkLen < 2 ^ 64; omega) hp.kc hp.bk, hu.ms.mu,
      v_keep iu (R := vsigR p s) (by have := hF.sgl; show p.sigLen < 2 ^ 64; omega) hp.gc hp.bg] at q
    exact q

/-! ## `verify_message` -/

theorem verifyMessage_wp {p : Params} {STK S : Nat} (hF : MFacts p) (h48 : 48 ≤ STK) {f : Prog isa}
    (hf : Callee f (fun stk => verifyContract p PPC64LE.abi stk) S) (hS : S ≤ STK) {n : String} {s : State}
    (hp : MVPre p STK s) :
    WP isa (verifyMessage n f p) s fun t =>
      abiPreserved s t ∧ (verifyMessageContract p PPC64LE.abi STK).post s t := by
  unfold verifyMessage top
  refine WP.seq (WP.cons (exec_lsr_d (by decide)) (WP.block_nil ?_))
  have hu := Upd.write s .r11 (s.gpr .r7 >>> 8)
  refine wp_ite (decide ((s.gpr .r7).toNat < 256)) (by rw [eval_zero, hu.gpr]; exact congrArg some (shr8_zero _))
    (fun hcl => ?_) fun hcl => ?_
  · have hcl' : (s.gpr .r7).toNat < 256 := of_decide_eq_true hcl
    refine WP.seq (WP.mono (verifySetup_ok hF hp hu.other hu.rd hu.wr hu.sp rfl hu.mem) fun t₁ h₁ => ?_)
    refine WP.seq (WP.mono (trHash_ok hF hp h48 h₁) fun t₂ h₂ => ?_)
    refine WP.seq (WP.mono (verifyHash_ok hp h48 h₂) fun t₃ h₃ => ?_)
    refine WP.seq (WP.mono (verifyCall_ok hF hp hf hS h₃) fun t₄ ⟨h₄, r₄⟩ => ?_)
    have hrl : ∀ q ∈ restoreList oSV verifyRegs, q.2 + 8 ≤ 1024 := by decide
    refine restore_ok h₄ (by decide) (v_e h₄) (by decide) (by decide) (by decide) (by decide)
      (fun q hq => by
        have := hrl q hq
        have := e_len p (d := q.2) (n := 8) (by omega)
        have := hF.e
        rw [h₄.rd, h₄.wr, hp.rd, hp.wr, e_add]
        exact ⟨vscrR p s, by simp, Offset.contains_base _ (by omega) (by omega)⟩)
      fun t₅ g₅ sp₅ lr₅ m₅ o₅ => ⟨⟨g₅, sp₅, lr₅⟩, ?_⟩
    sig_post [verifyMessageContract, verifyMessageSig, PPC64LE.abi, PPC64LE.argRegs]
    rw [Proof.MlDsa.Message.formatMessage_some (by rw [Proof.MlKem.bytesAt_length]; exact hcl'), o₅ .r3 (by decide)
      (by decide)]
    simp only [verifyInternal, Proof.MlKem.bytesAt_length]
    exact r₄
  · have hcl' : ¬ (s.gpr .r7).toNat < 256 := of_decide_eq_false hcl
    refine WP.cons (exec_li (d := .r3) (imm := 2) (by decide)) (WP.block_nil ⟨⟨fun r hr => ?_, rfl, rfl⟩, ?_⟩)
    · rw [(Upd.write _ _ _).other _ (Proof.Sha3.PPC64LE.Pieces.pres_ne hr).2.1,
        hu.other _ (by revert hr; cases r <;> decide)]
    · sig_post [verifyMessageContract, verifyMessageSig, PPC64LE.abi, PPC64LE.argRegs]
      rw [Proof.MlDsa.Message.formatMessage_none (by rw [Proof.MlKem.bytesAt_length]; omega)]
      rfl

end VG.Proof.MlDsa.PPC64LE.Message
