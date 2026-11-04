module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.Message.Sign
import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Common
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.MlDsa.Message.Common
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.MlDsa.RISCV64.Message

public import VerifiedGarbage.TCB.RISCV64.Target
/-!
# ML-DSA on RISC-V, `verify_message` and `verify_message_cached`: correctness

As signing (`Sign.lean`), with `sig` in `a5` and `scratch` in `a6`: from a
state satisfying `MVPre`, `verifyMessage n f p` returns 2 if the context
string is longer than 255 bytes; otherwise it saves our caller's registers in
the 1 KiB at `E` (`MV1`), computes `tr = H(pk, 64)` into `840(E)` (`MV2`),
then `μ` of the formatted message from it in place (`MV3`), and calls the
verification function on `μ` `f`, whose result is the result
(`verifyMessage_wp`).

`verifyMessageCached n f p`, from a state satisfying `MVCPre`, does the same
but computes `μ` from the 64 bytes at `tr`, which are `H(pk, 64)`, keeping
`tr` in `s6` too (`verifyMessageCached_wp`). The steps they share are proved
once, for the registers `rs` that hold `V` (`VInvG`), of which `VL` says what
they need.
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Message

open VG VG.RISCV64 VG.Proof.X25519.RISCV64
open VG.Impl.MlDsa.RISCV64.Message
open VG.Impl.Ed25519.RISCV64.Whole (mov saveRegs restoreRegs slots)
open VG.Proof.Ed25519.RISCV64.Whole (Inv slotArea restore_ok restoreList)
open VG.Impl.Sha3.RISCV64.Pieces (Piece Len hash)
open VG.Proof.Sha3.RISCV64.Pieces (Kept PieceOk KEnv kW hash_ok)
open VG.Proof.MlDsa.RISCV64.KeyGen (Callee)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## The invariant -/

/-- What the registers hold: the arguments, and `E`. -/
def verifyV (p : Params) (s : State) : Reg → BitVec 64
  | .s0 => s.gpr .a0 | .s1 => s.gpr .a1 | .s2 => s.gpr .a2 | .s3 => s.gpr .a3 | .s4 => s.gpr .a4
  | .s5 => s.gpr .a5 | .s7 => s.gpr .a6 | .s8 => eAt p (s.gpr .a6) | _ => 0

/-- What the registers hold with a cached `tr`: as `verifyV`, and `tr` in `s6`. -/
def cachedV (p : Params) (s : State) : Reg → BitVec 64
  | .s6 => s.gpr .a7 | r => verifyV p s r

/-- What the body may write. -/
abbrev vW (p : Params) (STK : Nat) (s : State) : List Region := [vscrR p s, below s.sp STK]

/-- Between the steps of a body that keeps the registers `rs`, which hold `V`. -/
abbrev VInvG (p : Params) (STK : Nat) (s : State) (rs : List Reg) (V : Reg → BitVec 64) : State → Prop :=
  Inv s (eAt p (s.gpr .a6)) oSV rs V (vW p STK s)

abbrev VInv (p : Params) (STK : Nat) (s : State) : State → Prop := VInvG p STK s verifyRegs (verifyV p s)

theorem verifyRegs_pres : ∀ r ∈ verifyRegs, r ∈ preserved := by decide

/-- What the steps need of the registers `rs` that the body keeps, holding `V`: they are callee-saved, they
and the link register fit in the 80 bytes at `oSV`, and they hold what `verifyV` says of `verifyRegs`. -/
structure VL (p : Params) (s : State) (rs : List Reg) (V : Reg → BitVec 64) : Prop where
  pres : ∀ r ∈ rs, r ∈ preserved
  len : rs.length ≤ 9
  regs : ∀ r ∈ verifyRegs, r ∈ rs ∧ V r = verifyV p s r

theorem vl_verify (p : Params) (s : State) : VL p s verifyRegs (verifyV p s) :=
  ⟨verifyRegs_pres, by decide, fun _ h => ⟨h, rfl⟩⟩

theorem vl_cached (p : Params) (s : State) : VL p s signRegs (cachedV p s) := by
  refine ⟨signRegs_pres, by decide, fun r hr => ?_⟩
  simp only [verifyRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, rfl⟩

section
variable {p : Params} {STK : Nat} {X : List Region} {s : State} {rs : List Reg} {V : Reg → BitVec 64}
  (hL : VL p s rs V) (hF : MFacts p) (hp : MVPre p STK X s) (h48 : 1168 ≤ STK)

include hL in
theorem v_reg {t : State} (h : VInvG p STK s rs V t) {r : Reg} (hr : r ∈ verifyRegs) :
    t.gpr r = verifyV p s r :=
  (h.regs r (hL.regs r hr).1).trans (hL.regs r hr).2

include hL in
theorem v_e {t : State} (h : VInvG p STK s rs V t) : t.gpr .s8 = eAt p (s.gpr .a6) := v_reg hL h (by decide)

include hL in
theorem vslot_len : oSV + 8 * (rs.length + 1) ≤ oHdr := by
  have := hL.len; simp only [oSV, oHdr]; omega

include hL in
theorem vslot_sub : Region.Sub (slotArea (eAt p (s.gpr .a6)) oSV rs) (vscrR p s) :=
  e_sub (by have := vslot_len hL; simp only [oHdr] at this; omega)

include hL in
theorem vslot_e {d n : Nat} (h : d + n ≤ oSV ∨ oSV + 80 ≤ d) (h₁ : d + n ≤ 1024) :
    (slotArea (eAt p (s.gpr .a6)) oSV rs).Disjoint ⟨eAt p (s.gpr .a6) + BitVec.ofNat 64 d, n⟩ :=
  e_e (h.symm.imp (fun h' => by have := hL.len; omega) id) (by have := vslot_len hL; simp only [oHdr] at this; omega)
    h₁

include hL in
theorem vslot_e0 {n : Nat} (h : n ≤ oSV) :
    (slotArea (eAt p (s.gpr .a6)) oSV rs).Disjoint ⟨eAt p (s.gpr .a6), n⟩ :=
  (e_e0 h (by have := vslot_len hL; simp only [oHdr] at this; omega)).symm

include hL hF in
theorem vslot_w : (slotArea (eAt p (s.gpr .a6)) oSV rs).Disjoint ⟨s.gpr .a6, scratchWords p * 8⟩ :=
  (e_w hF (by have := vslot_len hL; simp only [oHdr] at this; omega)).symm

include hp h48 in
theorem vbelow48 : Region.Sub (below s.sp 1168) (below s.sp STK) := below_sub h48 (by have := hp.stk; omega_arith)

include hL hp h48 in
theorem vslot_b : (slotArea (eAt p (s.gpr .a6)) oSV rs).Disjoint (below s.sp 1168) :=
  (hp.bx.symm.sub_left (vslot_sub hL)).sub_right (vbelow48 hp h48)

include hF hp in
theorem ve_in {t : State} (hw : t.wr = s.wr) {d n : Nat} (h : d + n ≤ 1024) :
    InRegions t.wr (eAt p (s.gpr .a6) + BitVec.ofNat 64 d) n := by
  rw [hw, hp.wr, e_add]
  exact in_base List.mem_cons_self (by rw [msw]; omega_arith) (by have := hF.e; omega_arith)

include hp in
theorem ve_cov {t : State} (hw : t.wr = s.wr) {d n : Nat} (h : d + n ≤ 1024) :
    RISCV64.Covers [⟨eAt p (s.gpr .a6) + BitVec.ofNat 64 d, n⟩] t.wr := by
  rw [hw, hp.wr]
  refine Covers.of_sub fun r hr => ?_
  rw [List.mem_singleton.mp hr]
  exact ⟨vscrR p s, List.mem_cons_self, oE p + d, e_add _ _ _, by simp only [msw]; omega_arith⟩

include hp in
theorem ve_cov0 {t : State} (hw : t.wr = s.wr) {n : Nat} (h : n ≤ 1024) :
    RISCV64.Covers [⟨eAt p (s.gpr .a6), n⟩] t.wr := by
  have := ve_cov hp hw (d := 0) (n := n) (by omega_arith)
  rwa [BitVec.add_zero] at this

/-- The inputs, while the body runs: none of them is in `vW`. -/
theorem v_keep {t : State} (h : VInvG p STK s rs V t) {R : Region} (hn : R.len < 2 ^ 64)
    (hc : R.Disjoint (vscrR p s)) (hb : (below s.sp STK).Disjoint R) :
    bytesAt t.mem R.base R.len = bytesAt s.mem R.base R.len := by
  refine Proof.Sha3.RISCV64.Pieces.bytes_keep h.frame hn fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hc
  · exact hb.symm

end

/-! ## The setup -/

/-- After the setup: the invariant, and `0 ‖ ctx_len` at `oHdr(E)`. -/
structure MV1 (p : Params) (STK : Nat) (s : State) (rs : List Reg) (V : Reg → BitVec 64) (t : State) : Prop where
  inv : VInvG p STK s rs V t
  hdr : bytesAt t.mem (eAt p (s.gpr .a6) + BitVec.ofNat 64 oHdr) 2 = [0, BitVec.ofNat 8 (s.gpr .a4).toNat]

/-- The setup that saves the registers `rs` and moves the arguments into them by `ms`, `E` into the last. -/
theorem vsetup_ok {p : Params} {STK : Nat} {X : List Region} {s u : State} {rs : List Reg} {V : Reg → BitVec 64}
    {ms : List (Reg × Reg)} (hL : VL p s rs V) (hF : MFacts p) (hp : MVPre p STK X s)
    (hfits : Spill.Fits (slots oSV rs)) (hlo : oSV + 8 * (rs.length + 1) < 2 ^ 64)
    (hsl : ∀ q ∈ slots oSV rs, q.2 + 8 ≤ 1024) (hms : ms.map Prod.fst = rs) (hsrc : ∀ q ∈ ms, q.2 ∉ rs)
    (hnd : rs.Nodup)
    (hv : ∀ q ∈ ms, (q.2 = .t2 ∧ V q.1 = eAt p (s.gpr .a6)) ∨ (q.2 ≠ .t2 ∧ q.2 ≠ .t1 ∧ V q.1 = s.gpr q.2))
    (hu : ∀ r, r ≠ .t1 → u.gpr r = s.gpr r) (hrd : u.rd = s.rd) (hwr : u.wr = s.wr) (hsp : u.sp = s.sp)
    (hlr : u.gpr .ra = s.gpr .ra) (hm : u.mem = s.mem) :
    WP isa (.block (enter .a6 p rs ms)) u (MV1 p STK s rs V) := by
  unfold enter
  refine WP.block_append_iff.mpr (WP.mono (base_ok p hF (by decide) u) fun u₁ ⟨h₁, l₁⟩ => ?_)
  have g9 : u.gpr .a6 = s.gpr .a6 := hu _ (by decide)
  rw [g9] at h₁
  have hw₁ : u₁.wr = s.wr := h₁.wr.trans hwr
  refine setup_ok (v := V) (W := vW p STK s) (by rw [h₁.gpr]; exact e_al hp.alx hp.fx) hfits hlo
    (fun q hq => by rw [h₁.gpr]; exact ve_in hF hp hw₁ (hsl q hq))
    ⟨vscrR p s, by simp, by rw [h₁.gpr]; exact vslot_sub hL⟩ hms hsrc hnd (fun q hq => by
      rcases hv q hq with ⟨e2, ev⟩ | ⟨e2, e1, ev⟩
      · rw [ev, e2, h₁.gpr]
      · rw [ev, h₁.other _ e2, hu _ e1])
    fun t₁ i₁ _ => ?_
  rw [h₁.gpr] at i₁
  have i₁ : VInvG p STK s rs V t₁ := inv_rebase i₁ hL.pres (h₁.rd.trans hrd) hw₁ (h₁.sp.trans hsp)
    (l₁.trans hlr)
    (fun r hr => (h₁.other r fun e => by revert hr; rw [e]; decide).trans (hu r fun e => by revert hr; rw [e]; decide))
    (h₁.mem.trans hm)
  have g30 : t₁.gpr .s8 = eAt p (s.gpr .a6) := v_e hL i₁
  have g26 : t₁.gpr .s4 = s.gpr .a4 := v_reg hL i₁ (by decide)
  refine hdr_ok (o := oHdr) (by decide) (by decide) (by decide) (by rw [g30]; exact ve_in hF hp i₁.wr (by decide))
    (by rw [g30]; exact ve_in hF hp i₁.wr (by decide)) fun t ht hrd' hwr' hsp' hg => WP.block_nil ⟨?_, ?_⟩
  · refine i₁.step hL.pres hrd' hwr' hsp' (fun r hr => hg r fun e => by revert hr; rw [e]; decide)
      (ht ▸ hdrMem_frame _ _ _) (fun r hr => ?_) fun r hr => ?_
    · rw [List.mem_singleton.mp hr, g30]; exact ⟨vscrR p s, by simp, e_sub (by decide)⟩
    · rw [List.mem_singleton.mp hr, g30]; exact vslot_e hL (.inr (by decide)) (by decide)
  · rw [ht, g30, g26, show s.gpr .a4 = BitVec.ofNat 64 (s.gpr .a4).toNat by simp, hdrMem_bytes]
    simp

theorem verifySetup_ok {p : Params} {STK : Nat} {X : List Region} {s u : State} (hF : MFacts p)
    (hp : MVPre p STK X s) (hu : ∀ r, r ≠ .t1 → u.gpr r = s.gpr r) (hrd : u.rd = s.rd) (hwr : u.wr = s.wr)
    (hsp : u.sp = s.sp) (hlr : u.gpr .ra = s.gpr .ra) (hm : u.mem = s.mem) :
    WP isa (.block (enter .a6 p verifyRegs verifyMs)) u (MV1 p STK s verifyRegs (verifyV p s)) :=
  vsetup_ok (vl_verify p s) hF hp (by decide) (by decide) (by decide) rfl (by decide) (by decide) (fun q hq => by
      simp only [verifyMs, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      iterate 7 exact .inr ⟨by decide, by decide, rfl⟩
      exact .inl ⟨rfl, rfl⟩)
    hu hrd hwr hsp hlr hm

theorem cachedSetup_ok {p : Params} {STK : Nat} {X : List Region} {s u : State} (hF : MFacts p)
    (hp : MVPre p STK X s) (hu : ∀ r, r ≠ .t1 → u.gpr r = s.gpr r) (hrd : u.rd = s.rd) (hwr : u.wr = s.wr)
    (hsp : u.sp = s.sp) (hlr : u.gpr .ra = s.gpr .ra) (hm : u.mem = s.mem) :
    WP isa (.block (enter .a6 p signRegs cachedMs)) u (MV1 p STK s signRegs (cachedV p s)) :=
  vsetup_ok (vl_cached p s) hF hp (by decide) (by decide) (by decide) rfl (by decide) (by decide) (fun q hq => by
      simp only [cachedMs, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      iterate 8 exact .inr ⟨by decide, by decide, rfl⟩
      exact .inl ⟨rfl, rfl⟩)
    hu hrd hwr hsp hlr hm

/-! ## `tr` and `μ` -/

/-- The public key. -/
abbrev pkB (p : Params) (s : State) : List Byte := bytesAt s.mem (s.gpr .a0) p.pkLen

/-- The signature. -/
abbrev vsigB (p : Params) (s : State) : List Byte := bytesAt s.mem (s.gpr .a5) p.sigLen

/-- What a hash keeps of the invariant. -/
theorem vinv_hash {p : Params} {STK : Nat} {X : List Region} {s t t' : State} {rs : List Reg}
    {V : Reg → BitVec 64} (hL : VL p s rs V) (hp : MVPre p STK X s) (h48 : 1168 ≤ STK)
    (hi : VInvG p STK s rs V t)
    (k : Kept ([⟨eAt p (s.gpr .a6) + BitVec.ofNat 64 oMU, 64⟩] ++ kW 840 (eAt p (s.gpr .a6)) t.sp) t t') :
    VInvG p STK s rs V t' := by
  have hsp : t.sp = s.sp := hi.sp
  refine inv_kept hi hL.pres k (fun r hr => ?_) fun r hr => ?_
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨vscrR p s, by simp, e_sub (by decide)⟩
    · exact ⟨vscrR p s, by simp, e_sub0 (by decide)⟩
    · exact ⟨below s.sp STK, by simp, by rw [hsp]; exact vbelow48 hp h48⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact vslot_e hL (.inl (by decide)) (by decide)
    · exact vslot_e0 hL (by decide)
    · rw [hsp]; exact vslot_b hL hp h48

/-- After `tr`: the invariant, the header, and `tr` at `oMU(E)`. -/
structure MV2 (p : Params) (STK : Nat) (s t : State) : Prop where
  inv : VInv p STK s t
  hdr : bytesAt t.mem (eAt p (s.gpr .a6) + BitVec.ofNat 64 oHdr) 2 = [0, BitVec.ofNat 8 (s.gpr .a4).toNat]
  tr : bytesAt t.mem (eAt p (s.gpr .a6) + BitVec.ofNat 64 oMU) 64 = pkTr (pkB p s)

/-- After `μ`: the invariant, and `μ` at `oMU(E)`. -/
structure MV3 (p : Params) (STK : Nat) (s : State) (rs : List Reg) (V : Reg → BitVec 64) (t : State) : Prop where
  inv : VInvG p STK s rs V t
  mu : bytesAt t.mem (eAt p (s.gpr .a6) + BitVec.ofNat 64 oMU) 64 = messageRep (pkTr (pkB p s)) (fmtB s)

section
variable {p : Params} {STK : Nat} {X : List Region} {s t : State} {rs : List Reg} {V : Reg → BitVec 64}
  (hF : MFacts p) (hp : MVPre p STK X s) (h48 : 1168 ≤ STK)
include hF hp h48

omit hF in
theorem vke (hi : VInvG p STK s rs V t) : KEnv 840 (eAt p (s.gpr .a6)) t :=
  ⟨by decide, ve_cov0 hp hi.wr (by decide), e_al hp.alx hp.fx, by rw [hi.sp]; exact hp.al,
    by rw [hi.sp]; have := hp.stk; omega_arith,
    by rw [hi.sp]; exact (hp.bx.sub_left (vbelow48 hp h48)).sub_right (e_sub0 (by decide))⟩

theorem trHash_ins (hi : VInv p STK s t) :
    ∀ q ∈ [(⟨.s0, 0, .imm 1024⟩ : Piece), ⟨.s0, 1024, .imm (p.pkLen - 1024)⟩],
      PieceOk 840 (eAt p (s.gpr .a6)) t q := by
  have g22 : t.gpr .s0 = s.gpr .a0 := hi.regs _ (by decide)
  have hsp : t.sp = s.sp := hi.sp
  have b48 := vbelow48 hp h48
  have eS := e_sub0 (p := p) (x := s.gpr .a6) (n := 840) (by decide)
  have h1 := hF.pk1
  have h2 := hF.pk
  have s1 : Region.Sub ⟨s.gpr .a0, 1024⟩ (pkR p s) := Region.sub_prefix (by omega_arith)
  have s2 : Region.Sub ⟨s.gpr .a0 + BitVec.ofNat 64 1024, p.pkLen - 1024⟩ (pkR p s) :=
    Offset.sub_base _ (by omega_arith)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact pieceOk_of (R := ⟨s.gpr .a0, 1024⟩) (by simp only [Piece.R, Piece.addr, Len.val, g22, BitVec.add_zero])
      (show Reg.s0 ∈ preserved by decide) (show (0 : Nat) < 2048 by decide) (show 1024 < 2048 by decide)
      (cov_rd (by rw [hi.rd, hp.rd]; exact cov_in0 (k := p.pkLen) (by simp) (by omega_arith)))
      ((hp.kc.sub_left s1).sub_right eS) (by rw [hsp]; exact (hp.bk.sub_left b48).sub_right s1)
  · exact pieceOk_of (R := ⟨s.gpr .a0 + BitVec.ofNat 64 1024, p.pkLen - 1024⟩)
      (by simp only [Piece.R, Piece.addr, Len.val, g22])
      (show Reg.s0 ∈ preserved by decide) (show (1024 : Nat) < 2048 by decide)
      (show p.pkLen - 1024 < 2048 by omega_arith)
      (cov_rd (by rw [hi.rd, hp.rd]; exact cov_in (k := p.pkLen) (by simp) (by omega_arith)))
      ((hp.kc.sub_left s2).sub_right eS) (by rw [hsp]; exact (hp.bk.sub_left b48).sub_right s2)

theorem trHash_ok (h : MV1 p STK s verifyRegs (verifyV p s) t) : WP isa (trHash p) t (MV2 p STK s) := by
  have hi := h.inv
  have g22 : t.gpr .s0 = s.gpr .a0 := hi.regs _ (by decide)
  have g30 := v_e (vl_verify p s) hi
  have hsp : t.sp = s.sp := hi.sp
  have b48 := vbelow48 hp h48
  have eS := e_sub0 (p := p) (x := s.gpr .a6) (n := 840) (by decide)
  have hin := trHash_ins hF hp h48 hi
  unfold trHash
  refine WP.mono (hash_ok (N := 840) (n := 64) (o := oMU) (out := eAt p (s.gpr .a6) + BitVec.ofNat 64 oMU)
    (by decide) (by decide) (by decide) (by decide) g30 (by rw [g30]) (vke hp h48 hi) (by simp) hin
    (ve_cov hp hi.wr (by decide)) (e_e0 (by decide) (by decide)).symm
    (by rw [hsp]; exact (hp.bx.sub_left b48).sub_right (e_sub (by decide)))) fun t' ⟨k', d'⟩ => ⟨?_, ?_, ?_⟩
  · exact vinv_hash (vl_verify p s) hp h48 hi k'
  · rw [show bytesAt t'.mem (eAt p (s.gpr .a6) + BitVec.ofNat 64 oHdr) 2 =
      bytesAt t.mem (eAt p (s.gpr .a6) + BitVec.ofNat 64 oHdr) 2 from
      Proof.Sha3.RISCV64.Pieces.bytes_keep k'.frame (by decide) fun r hr => by
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact e_e (.inr (by decide)) (by decide) (by decide)
        · exact (e_e0 (by decide) (by decide)).symm
        · rw [hsp]; exact ((hp.bx.sub_left b48).sub_right (e_sub (by decide))).symm, h.hdr]
  · rw [d']
    have kp : bytesAt t.mem (s.gpr .a0) p.pkLen = pkB p s :=
      v_keep hi (R := pkR p s) (by have := hF.pk; show p.pkLen < 2 ^ 64; omega_arith) hp.kc hp.bk
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, Piece.bytes,
      Piece.addr, Len.val, g22, BitVec.add_zero]
    rw [← Proof.MlKem.bytesAt_add, Nat.add_sub_cancel' hF.pk1, kp]
    rfl

omit hF in
/-- The pieces of the formatted message after the first, `q₀`. -/
theorem mu_ins (hL : VL p s rs V) (hi : VInvG p STK s rs V t) {q₀ : Piece} (h₀ : PieceOk 840 (eAt p (s.gpr .a6)) t q₀) :
    ∀ q ∈ q₀ :: fmtPieces, PieceOk 840 (eAt p (s.gpr .a6)) t q := by
  have g23 : t.gpr .s1 = s.gpr .a1 := v_reg hL hi (by decide)
  have g24 : t.gpr .s2 = s.gpr .a2 := v_reg hL hi (by decide)
  have g25 : t.gpr .s3 = s.gpr .a3 := v_reg hL hi (by decide)
  have g26 : t.gpr .s4 = s.gpr .a4 := v_reg hL hi (by decide)
  have g30 := v_e hL hi
  have hsp : t.sp = s.sp := hi.sp
  have b48 := vbelow48 hp h48
  have eS := e_sub0 (p := p) (x := s.gpr .a6) (n := 840) (by decide)
  have cr : ∀ R ∈ [pkR p s, msgR s, ctxR s, vsigR p s], RISCV64.Covers [R] (t.rd ++ t.wr) := fun R hR => by
    rw [hi.rd, hp.rd]
    exact cov_rd fun a n ⟨r, hr, hc⟩ => ⟨r, by rw [List.mem_singleton.mp hr]; exact List.mem_append_left _ hR, hc⟩
  intro q hq
  simp only [fmtPieces, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact h₀
  · exact pieceOk_of (R := ⟨eAt p (s.gpr .a6) + BitVec.ofNat 64 oHdr, 2⟩)
      (by simp only [Piece.R, Piece.addr, Len.val, g30]) (by decide) (by decide) (show 2 < 2048 by decide)
      (Proof.Sha3.RISCV64.Pieces.cov_right (ve_cov hp hi.wr (by decide))) (e_e0 (by decide) (by decide)).symm
      (by rw [hsp]; exact (hp.bx.sub_left b48).sub_right (e_sub (by decide)))
  · exact pieceOk_of (R := ctxR s) (by simp only [Piece.R, Piece.addr, Len.val, g25, g26, BitVec.add_zero])
      (by decide) (by decide) (show Reg.s4 ∈ preserved by decide) (cr _ (by simp))
      (hp.cc.sub_right eS) (by rw [hsp]; exact hp.bc.sub_left b48)
  · exact pieceOk_of (R := msgR s) (by simp only [Piece.R, Piece.addr, Len.val, g23, g24, BitVec.add_zero])
      (by decide) (by decide) (show Reg.s2 ∈ preserved by decide) (cr _ (by simp))
      (hp.mc.sub_right eS) (by rw [hsp]; exact hp.bm.sub_left b48)

omit hF in
/-- `verify_message`'s first piece of `μ`: `tr`, at `oMU(E)`. -/
theorem muPiece_ok (hL : VL p s rs V) (hi : VInvG p STK s rs V t) :
    PieceOk 840 (eAt p (s.gpr .a6)) t ⟨.s8, oMU, .imm 64⟩ :=
  pieceOk_of (R := ⟨eAt p (s.gpr .a6) + BitVec.ofNat 64 oMU, 64⟩)
    (by simp only [Piece.R, Piece.addr, Len.val, v_e hL hi]) (by decide) (by decide) (show 64 < 2048 by decide)
    (Proof.Sha3.RISCV64.Pieces.cov_right (ve_cov hp hi.wr (by decide))) (e_e0 (by decide) (by decide)).symm
    (by rw [hi.sp]; exact (hp.bx.sub_left (vbelow48 hp h48)).sub_right (e_sub (by decide)))

omit hF in
/-- `μ` from the first piece `q₀`, which holds `tr`. -/
theorem muHash_ok (hL : VL p s rs V) (hi : VInvG p STK s rs V t)
    (hdr : bytesAt t.mem (eAt p (s.gpr .a6) + BitVec.ofNat 64 oHdr) 2 = [0, BitVec.ofNat 8 (s.gpr .a4).toNat])
    {q₀ : Piece} (h₀ : PieceOk 840 (eAt p (s.gpr .a6)) t q₀) (hb : q₀.bytes t.mem t.gpr = pkTr (pkB p s)) :
    WP isa (muHash q₀) t (MV3 p STK s rs V) := by
  have g23 : t.gpr .s1 = s.gpr .a1 := v_reg hL hi (by decide)
  have g24 : t.gpr .s2 = s.gpr .a2 := v_reg hL hi (by decide)
  have g25 : t.gpr .s3 = s.gpr .a3 := v_reg hL hi (by decide)
  have g26 : t.gpr .s4 = s.gpr .a4 := v_reg hL hi (by decide)
  have g30 := v_e hL hi
  have hsp : t.sp = s.sp := hi.sp
  have b48 := vbelow48 hp h48
  unfold muHash
  refine WP.mono (hash_ok (N := 840) (n := 64) (o := oMU) (out := eAt p (s.gpr .a6) + BitVec.ofNat 64 oMU)
    (by decide) (by decide) (by decide) (by decide) g30 (by rw [g30]) (vke hp h48 hi) (by simp)
    (mu_ins hp h48 hL hi h₀) (ve_cov hp hi.wr (by decide)) (e_e0 (by decide) (by decide)).symm
    (by rw [hsp]; exact (hp.bx.sub_left b48).sub_right (e_sub (by decide)))) fun t' ⟨k', d'⟩ => ⟨?_, ?_⟩
  · exact vinv_hash hL hp h48 hi k'
  · rw [d', List.map_cons, hb]
    have kc : bytesAt t.mem (s.gpr .a3) (s.gpr .a4).toNat = ctxB s :=
      v_keep hi (R := ctxR s) (BitVec.isLt _) hp.cc hp.bc
    have km : bytesAt t.mem (s.gpr .a1) (s.gpr .a2).toNat = msgB s :=
      v_keep hi (R := msgR s) (BitVec.isLt _) hp.mc hp.bm
    simp only [fmtPieces, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
      Piece.bytes, Piece.addr, Len.val, g23, g24, g25, g26, g30, BitVec.add_zero]
    rw [hdr, kc, km]
    simp only [messageRep, H, List.append_assoc]

omit hF in
theorem verifyHash_ok (h : MV2 p STK s t) :
    WP isa (muHash ⟨.s8, oMU, .imm 64⟩) t (MV3 p STK s verifyRegs (verifyV p s)) :=
  muHash_ok hp h48 (vl_verify p s) h.inv h.hdr (muPiece_ok hp h48 (vl_verify p s) h.inv) (by
    simp only [Piece.bytes, Piece.addr, Len.val, v_e (vl_verify p s) h.inv]; exact h.tr)

end

/-! ## `μ` from a cached `tr` -/

section
variable {p : Params} {STK : Nat} {s t : State} (hc : MVCPre p STK s) (h48 : 1168 ≤ STK)
include hc h48

/-- The first piece of `μ`: `tr`, at `s6`. -/
theorem trPiece_ok (hi : VInvG p STK s signRegs (cachedV p s) t) :
    PieceOk 840 (eAt p (s.gpr .a6)) t ⟨.s6, 0, .imm 64⟩ := by
  have g28 : t.gpr .s6 = s.gpr .a7 := hi.regs _ (by decide)
  exact pieceOk_of (R := trR s) (by simp only [Piece.R, Piece.addr, Len.val, g28, BitVec.add_zero])
    (by decide) (by decide) (show 64 < 2048 by decide)
    (cov_rd (by rw [hi.rd, hc.mv.rd]; exact cov_in0 (k := 64) (List.mem_append_right _ List.mem_cons_self) (Nat.le_refl _)))
    (hc.tc.symm.sub_right (e_sub0 (by decide))) (by rw [hi.sp]; exact hc.bt.sub_left (vbelow48 hc.mv h48))

theorem cachedHash_ok (h : MV1 p STK s signRegs (cachedV p s) t) :
    WP isa (muHash ⟨.s6, 0, .imm 64⟩) t (MV3 p STK s signRegs (cachedV p s)) := by
  have hi := h.inv
  have g28 : t.gpr .s6 = s.gpr .a7 := hi.regs _ (by decide)
  refine muHash_ok hc.mv h48 (vl_cached p s) hi h.hdr (trPiece_ok hc h48 hi) ?_
  simp only [Piece.bytes, Piece.addr, Len.val, g28, BitVec.add_zero]
  rw [v_keep hi (R := trR s) (show (64 : Nat) < 2 ^ 64 by decide) hc.tc.symm hc.bt, hc.tr]

end

/-! ## The call of the verification function on `μ` -/

/-- The arguments of the call. -/
abbrev verifyArgs : List Instr := [mov .a0 .s0, .addi .a1 .s8 oMU, mov .a2 .s5, mov .a3 .s7]

theorem args4_ok {t : State} {a b c d : Reg} {i j k l : Nat} (hi : i < 2048) (hj : j < 2048) (hk : k < 2048) (hl : l < 2048)
    (hs : ∀ x ∈ [b, c, d], x ∈ preserved) {Q : State → Prop}
    (K : ∀ u, u.mem = t.mem → u.rd = t.rd → u.wr = t.wr → u.sp = t.sp → (∀ r ∈ preserved, u.gpr r = t.gpr r) →
      u.gpr .a0 = t.gpr a + BitVec.ofNat 64 i →
      u.gpr .a1 = t.gpr b + BitVec.ofNat 64 j → u.gpr .a2 = t.gpr c + BitVec.ofNat 64 k →
      u.gpr .a3 = t.gpr d + BitVec.ofNat 64 l → Q u) :
    WP isa (.block [.addi .a0 a i, .addi .a1 b j, .addi .a2 c k, .addi .a3 d l]) t Q := by
  have pb := Ed25519.RISCV64.Whole.pres_args (hs b (by simp))
  have pc := Ed25519.RISCV64.Whole.pres_args (hs c (by simp))
  have pd := Ed25519.RISCV64.Whole.pres_args (hs d (by simp))
  exact Steps.wp_addi hi fun u₁ h₁ => Steps.wp_addi hj fun u₂ h₂ => Steps.wp_addi hk fun u₃ h₃ =>
    Steps.wp_addi hl fun u₄ h₄ => WP.block_nil <|
    K u₄ (by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem]) (by rw [h₄.rd, h₃.rd, h₂.rd, h₁.rd])
      (by rw [h₄.wr, h₃.wr, h₂.wr, h₁.wr]) (by rw [h₄.sp, h₃.sp, h₂.sp, h₁.sp]) (fun r hr => by
        obtain ⟨p3, p4, p5, p6, -⟩ := Ed25519.RISCV64.Whole.pres_args hr
        rw [h₄.other _ p6, h₃.other _ p5, h₂.other _ p4, h₁.other _ p3])
      (by rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide), h₁.gpr])
      (by rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.gpr, h₁.other _ pb.1])
      (by rw [h₄.other _ (by decide), h₃.gpr, h₂.other _ pc.2.1, h₁.other _ pc.1])
      (by rw [h₄.gpr, h₃.other _ pd.2.2.1, h₂.other _ pd.2.1, h₁.other _ pd.1])

/-- What the verification function on `μ` returns. -/
abbrev vres (p : Params) (s : State) (r : BitVec 32) : Prop :=
  let v := fun b => verifyMu p b (pkB p s) (messageRep (pkTr (pkB p s)) (fmtB s)) (vsigB p s)
  (r = 1 ∧ ∃ b, v b = some true) ∨ (r = 0 ∧ v minBounds ≠ some true)

/-- After the arguments of the call: `μ`, and the arguments in `a0`–`a3`. -/
structure VA (p : Params) (STK : Nat) (s : State) (rs : List Reg) (V : Reg → BitVec 64) (u : State) : Prop where
  ms : MV3 p STK s rs V u
  a0 : u.gpr .a0 = s.gpr .a0
  a1 : u.gpr .a1 = eAt p (s.gpr .a6) + BitVec.ofNat 64 oMU
  a2 : u.gpr .a2 = s.gpr .a5
  a3 : u.gpr .a3 = s.gpr .a6

theorem verifyArgs_ok {p : Params} {STK : Nat} {s t : State} {rs : List Reg} {V : Reg → BitVec 64}
    (hL : VL p s rs V) (h : MV3 p STK s rs V t) :
    WP isa (.block verifyArgs) t (VA p STK s rs V) := by
  have hi := h.inv
  have g22 : t.gpr .s0 = s.gpr .a0 := v_reg hL hi (by decide)
  have g27 : t.gpr .s5 = s.gpr .a5 := v_reg hL hi (by decide)
  have g29 : t.gpr .s7 = s.gpr .a6 := v_reg hL hi (by decide)
  have g30 := v_e hL hi
  unfold verifyArgs mov
  refine args4_ok (by decide) (by decide) (by decide)
    (by decide) (by decide) fun u um urd' uwr' usp' upres a3 a4 a5 a6 =>
    ⟨⟨hi.step hL.pres urd' uwr' usp' upres (by rw [um]; exact Frame.refl _ _)
      (fun _ h => absurd h List.not_mem_nil) (fun _ h => absurd h List.not_mem_nil), by rw [um]; exact h.mu⟩,
      ?_, ?_, ?_, ?_⟩
  · rw [a3, g22, BitVec.add_zero]
  · rw [a4, g30]
  · rw [a5, g27, BitVec.add_zero]
  · rw [a6, g29, BitVec.add_zero]

/-- What the verification function on `μ` reads and writes. -/
abbrev vRd (p : Params) (s : State) : List Region :=
  [pkR p s, ⟨eAt p (s.gpr .a6) + BitVec.ofNat 64 oMU, 64⟩, vsigR p s]
abbrev vWr (p : Params) (s : State) : List Region := [⟨s.gpr .a6, scratchWords p * 8⟩]

/-- The call's precondition, and its regions. -/
theorem verifyCall_pre {p : Params} {STK stk : Nat} {X : List Region} {s u : State} {rs : List Reg}
    {V : Reg → BitVec 64} (hF : MFacts p) (hp : MVPre p STK X s) (hstk : stk ≤ STK) (h : VA p STK s rs V u) :
    (verifyContract p RISCV64.abi stk).pre (u.callEntry.withRegions (vRd p s) (vWr p s)) ∧
      RISCV64.Covers (vRd p s ++ vWr p s) (u.rd ++ u.wr) ∧ RISCV64.Covers (vWr p s) u.wr := by
  have iu := h.ms.inv
  have hstkS : STK ≤ s.sp.toNat := hp.stk
  have hE := hF.e
  have fx := hp.fx
  rw [msw] at fx
  have hsw : scratchWords p * 8 ≤ oE p := by simp only [oE]; omega_arith
  have usp : u.sp = s.sp := iu.sp
  have urd : u.rd = s.rd := iu.rd
  have uwr : u.wr = s.wr := iu.wr
  have bs : Region.Sub (below s.sp stk) (below s.sp STK) := below_sub (by omega_arith) (by omega_arith)
  have muS : Region.Sub ⟨eAt p (s.gpr .a6) + BitVec.ofNat 64 oMU, 64⟩ (vscrR p s) := e_sub (by decide)
  have muW : Region.Disjoint ⟨s.gpr .a6, scratchWords p * 8⟩ ⟨eAt p (s.gpr .a6) + BitVec.ofNat 64 oMU, 64⟩ :=
    e_w hF (by decide)
  have muF : (eAt p (s.gpr .a6) + BitVec.ofNat 64 oMU).toNat + 64 ≤ 2 ^ 64 := e_fit hp.fx (by decide) (by decide)
  refine ⟨?_, ?_, ?_⟩
  · refine verify_pre ((ce_gpr _ _ _ (by decide)).trans h.a0) ((ce_gpr _ _ _ (by decide)).trans h.a1)
      ((ce_gpr _ _ _ (by decide)).trans h.a2) ((ce_gpr _ _ _ (by decide)).trans h.a3) rfl rfl
      (by simp only [State.withRegions_sp, State.callEntry_sp, usp]; omega_arith)
      (by simp only [State.withRegions_sp, State.callEntry_sp, usp]; exact hp.al) hp.alx
      (hp.kc.sub_right w_sub) muW.symm (hp.gc.sub_right w_sub) ?_ ?_ ?_ ?_ hp.fk muF hp.fg (by omega_arith)
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
    · exact ⟨vscrR p s, by simp, 0, by simp, by simp only [msw]; omega_arith⟩
  · rw [uwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    exact ⟨vscrR p s, by simp, 0, by simp, by simp only [msw]; omega_arith⟩

theorem verifyCall_ok {p : Params} {STK S : Nat} {X : List Region} {s t : State} {rs : List Reg}
    {V : Reg → BitVec 64} (hL : VL p s rs V) (hF : MFacts p) (hp : MVPre p STK X s)
    {f : Prog isa} (hf : Callee f (fun stk => verifyContract p RISCV64.abi stk) S) (hS : S ≤ STK) {n : String}
    (h : MV3 p STK s rs V t) :
    WP isa (.seq (.block verifyArgs) (.call n f)) t fun t' => VInvG p STK s rs V t' ∧
      vres p s ((t'.gpr .a0).setWidth 32) := by
  obtain ⟨stk, hstk, hver⟩ := hf.verified
  have hstkS : STK ≤ s.sp.toNat := hp.stk
  refine WP.seq (WP.mono (verifyArgs_ok hL h) fun u hu => ?_)
  have iu := hu.ms.inv
  have usp : u.sp = s.sp := iu.sp
  obtain ⟨hpre, hc, hw⟩ := verifyCall_pre hF hp (Nat.le_trans hstk hS) hu
  have hd : sdepth f < 2 ^ 64 := by have := hf.stack; omega_arith
  refine WP.callAny hver.1 hpre hc hw (fun s' rd' wr' sp' fr' cs' post' => ?_) hd
  refine ⟨iu.step hL.pres rd' wr' sp' cs' fr' (fun r hr => ?_) fun r hr => ?_, ?_⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨vscrR p s, by simp, w_sub⟩
    · exact ⟨below s.sp STK, by simp, by rw [usp]; exact below_sub (by have := hf.stack; omega_arith) (by omega_arith)⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact vslot_w hL hF
    · rw [usp]
      exact (hp.bx.symm.sub_left (vslot_sub hL)).sub_right (below_sub (by have := hf.stack; omega_arith) (by omega_arith))
  · have q := verify_post post'
    simp only [State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem,
      State.callEntry_gpr _ (show Reg.a0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a1 ∉ linkRegs by decide),
      State.callEntry_gpr _ (show Reg.a2 ∉ linkRegs by decide), hu.a0, hu.a1, hu.a2] at q
    rw [v_keep iu (R := pkR p s) (by have := hF.pk; show p.pkLen < 2 ^ 64; omega_arith) hp.kc hp.bk, hu.ms.mu,
      v_keep iu (R := vsigR p s) (by have := hF.sgl; show p.sigLen < 2 ^ 64; omega_arith) hp.gc hp.bg] at q
    exact q

/-! ## `verify_message` -/

theorem verifyMessage_wp {p : Params} {STK S : Nat} (hF : MFacts p) (h48 : 1168 ≤ STK) {f : Prog isa}
    (hf : Callee f (fun stk => verifyContract p RISCV64.abi stk) S) (hS : S ≤ STK) {n : String} {s : State}
    (hp : MVPre p STK [] s) :
    WP isa (verifyMessage n f p) s fun t =>
      abiPreserved s t ∧ (verifyMessageContract p RISCV64.abi STK).post s t := by
  unfold verifyMessage top
  refine WP.seq (Steps.WP.cons (exec_shift_d (by decide)) (WP.block_nil ?_))
  have hu := Steps.Upd.write s .t1 (s.gpr .a4 >>> 8)
  refine wp_ite (decide ((s.gpr .a4).toNat < 256)) (by rw [eval_zero, hu.gpr]; exact congrArg some (shr8_zero _))
    (fun hcl => ?_) fun hcl => ?_
  · have hcl' : (s.gpr .a4).toNat < 256 := of_decide_eq_true hcl
    refine WP.seq (WP.mono (verifySetup_ok hF hp hu.other hu.rd hu.wr hu.sp rfl hu.mem) fun t₁ h₁ => ?_)
    refine WP.seq (WP.mono (trHash_ok hF hp h48 h₁) fun t₂ h₂ => ?_)
    refine WP.seq (WP.mono (verifyHash_ok hp h48 h₂) fun t₃ h₃ => ?_)
    refine WP.seq (WP.mono (verifyCall_ok (vl_verify p s) hF hp hf hS h₃) fun t₄ ⟨h₄, r₄⟩ => ?_)
    have hrl : ∀ q ∈ restoreList oSV verifyRegs, q.2 + 8 ≤ 1024 := by decide
    refine restore_ok h₄ (e_al hp.alx hp.fx) (v_e (vl_verify p s) h₄) (by decide) (by decide) (by decide) (by decide)
      (fun q hq => by
        have := hrl q hq
        have := e_len p (d := q.2) (n := 8) (by omega_arith)
        have := hF.e
        rw [h₄.rd, h₄.wr, hp.rd, hp.wr, e_add]
        exact ⟨vscrR p s, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
      fun t₅ g₅ sp₅ lr₅ m₅ o₅ => ⟨⟨g₅, sp₅, lr₅⟩, ?_⟩
    sig_post [verifyMessageContract, verifyMessageSig, RISCV64.abi, RISCV64.argRegs]
    rw [Proof.MlDsa.Message.formatMessage_some (by rw [Proof.MlKem.bytesAt_length]; exact hcl'), o₅ .a0 (by decide)
      (by decide)]
    simp only [verifyInternal, Proof.MlKem.bytesAt_length]
    exact r₄
  · have hcl' : ¬ (s.gpr .a4).toNat < 256 := of_decide_eq_false hcl
    refine Steps.WP.cons (exec_li (d := .a0) (imm := 2) (by decide)) (WP.block_nil ⟨⟨fun r hr => ?_, rfl, rfl⟩, ?_⟩)
    · rw [(Steps.Upd.write _ _ _).other _ (Proof.Sha3.RISCV64.Pieces.pres_ne hr).2.1,
        hu.other _ (by revert hr; cases r <;> decide)]
    · sig_post [verifyMessageContract, verifyMessageSig, RISCV64.abi, RISCV64.argRegs]
      rw [Proof.MlDsa.Message.formatMessage_none (by rw [Proof.MlKem.bytesAt_length]; omega_arith)]
      rfl

/-! ## `verify_message_cached` -/

theorem verifyMessageCached_wp {p : Params} {STK S : Nat} (hF : MFacts p) (h48 : 1168 ≤ STK) {f : Prog isa}
    (hf : Callee f (fun stk => verifyContract p RISCV64.abi stk) S) (hS : S ≤ STK) {n : String} {s : State}
    (hc : MVCPre p STK s) :
    WP isa (verifyMessageCached n f p) s fun t =>
      abiPreserved s t ∧ (verifyMessageCachedContract p RISCV64.abi STK).post s t := by
  have hp := hc.mv
  unfold verifyMessageCached top
  refine WP.seq (Steps.WP.cons (exec_shift_d (by decide)) (WP.block_nil ?_))
  have hu := Steps.Upd.write s .t1 (s.gpr .a4 >>> 8)
  refine wp_ite (decide ((s.gpr .a4).toNat < 256)) (by rw [eval_zero, hu.gpr]; exact congrArg some (shr8_zero _))
    (fun hcl => ?_) fun hcl => ?_
  · have hcl' : (s.gpr .a4).toNat < 256 := of_decide_eq_true hcl
    refine WP.seq (WP.mono (cachedSetup_ok hF hp hu.other hu.rd hu.wr hu.sp rfl hu.mem) fun t₁ h₁ => ?_)
    refine WP.seq (WP.mono (cachedHash_ok hc h48 h₁) fun t₃ h₃ => ?_)
    refine WP.seq (WP.mono (verifyCall_ok (vl_cached p s) hF hp hf hS h₃) fun t₄ ⟨h₄, r₄⟩ => ?_)
    have hrl : ∀ q ∈ restoreList oSV signRegs, q.2 + 8 ≤ 1024 := by decide
    refine restore_ok h₄ (e_al hp.alx hp.fx) (v_e (vl_cached p s) h₄) (by decide) (by decide) (by decide)
      (by decide)
      (fun q hq => by
        have := hrl q hq
        have := e_len p (d := q.2) (n := 8) (by omega_arith)
        have := hF.e
        rw [h₄.rd, h₄.wr, hp.rd, hp.wr, e_add]
        exact ⟨vscrR p s, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
      fun t₅ g₅ sp₅ lr₅ m₅ o₅ => ⟨⟨g₅, sp₅, lr₅⟩, ?_⟩
    sig_post [verifyMessageCachedContract, verifyMessageCachedSig, RISCV64.abi, RISCV64.argRegs]
    rw [Proof.MlDsa.Message.formatMessage_some (by rw [Proof.MlKem.bytesAt_length]; exact hcl'), o₅ .a0 (by decide)
      (by decide)]
    simp only [verifyInternal, Proof.MlKem.bytesAt_length]
    exact r₄
  · have hcl' : ¬ (s.gpr .a4).toNat < 256 := of_decide_eq_false hcl
    refine Steps.WP.cons (exec_li (d := .a0) (imm := 2) (by decide)) (WP.block_nil ⟨⟨fun r hr => ?_, rfl, rfl⟩, ?_⟩)
    · rw [(Steps.Upd.write _ _ _).other _ (Proof.Sha3.RISCV64.Pieces.pres_ne hr).2.1,
        hu.other _ (by revert hr; cases r <;> decide)]
    · sig_post [verifyMessageCachedContract, verifyMessageCachedSig, RISCV64.abi, RISCV64.argRegs]
      rw [Proof.MlDsa.Message.formatMessage_none (by rw [Proof.MlKem.bytesAt_length]; omega_arith)]
      rfl

end VG.Proof.MlDsa.RISCV64.Message
