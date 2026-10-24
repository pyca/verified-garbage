module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Message.Steps
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Message.Contracts
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Base
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Common
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.MlDsa.Message.Common
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
public import VerifiedGarbage.Proof.Framework.PowLit

/-!
# ML-DSA on PPC64LE, `sign_message`: correctness

From a state satisfying `MSPre`, `signMessage n f p` returns 2 if the
context string is longer than 255 bytes; otherwise it saves our caller's
registers in the 1 KiB at `E` (`MS1`), computes `μ` of the formatted message
into `840(E)` (`MS2`), and calls the signing function on `μ` `f`, which gives
the signature of `ML-DSA.Sign_internal` on the formatted message
(`signMessage_wp`). Between the steps, `Inv` records the arguments in
`r22`–`r30` and the saved registers, and that only `scratch`, `sig` and the
stack below the stack pointer change.
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

/-! ## The parameter sets -/

/-- What the proofs need of the parameter set. -/
structure MFacts (p : Params) : Prop where
  e : oE p + 1024 < 2 ^ 31
  sk : 128 ≤ p.skLen
  pk : p.pkLen < 2 ^ 15
  skl : p.skLen < 2 ^ 15
  sgl : p.sigLen < 2 ^ 15

theorem mfacts {p : Params} (h : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) : MFacts p := by
  rcases h with rfl | rfl | rfl <;> exact ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem msw (p : Params) : messageScratchWords p * 8 = oE p + 1024 := by
  simp only [messageScratchWords, oE]; omega

theorem e_len (p : Params) {d n : Nat} (h : d + n ≤ 1024) : oE p + d + n ≤ messageScratchWords p * 8 := by
  rw [msw]; omega

/-- A region of the 1 KiB does not wrap around. -/
theorem e_fit {p : Params} {x : Addr} (hx : x.toNat + messageScratchWords p * 8 ≤ 2 ^ 64) {d n : Nat}
    (hn : 0 < n) (h : d + n ≤ 1024) : (x + BitVec.ofNat 64 (oE p) + BitVec.ofNat 64 d).toNat + n ≤ 2 ^ 64 := by
  have := e_len p h
  rw [Proof.MlDsa.Message.add_add, Proof.MlDsa.Message.toNat_add_ofNat (by omega)]; omega

/-! ## The 1 KiB -/

/-- `E`, from `scratch` in `r` of the entry state. -/
abbrev eAt (p : Params) (x : Addr) : Addr := x + BitVec.ofNat 64 (oE p)

theorem e_add (p : Params) (x : Addr) (d : Nat) :
    eAt p x + BitVec.ofNat 64 d = x + BitVec.ofNat 64 (oE p + d) :=
  Proof.MlDsa.Message.add_add _ _ _

section
variable {p : Params} {x : Addr}

/-- A region in the 1 KiB lies in `scratch`. -/
theorem e_sub {d n : Nat} (h : d + n ≤ 1024) :
    Region.Sub ⟨eAt p x + BitVec.ofNat 64 d, n⟩ ⟨x, messageScratchWords p * 8⟩ := by
  rw [e_add]; exact Offset.sub_base _ (by rw [msw]; omega)

theorem e_sub0 {n : Nat} (h : n ≤ 1024) : Region.Sub ⟨eAt p x, n⟩ ⟨x, messageScratchWords p * 8⟩ := by
  have := e_sub (p := p) (x := x) (d := 0) (n := n) (by omega)
  rwa [BitVec.add_zero] at this

/-- The working space of the function on `μ` lies in `scratch`. -/
theorem w_sub : Region.Sub ⟨x, scratchWords p * 8⟩ ⟨x, messageScratchWords p * 8⟩ :=
  Region.sub_prefix (by simp only [messageScratchWords]; omega)

/-- A region in the 1 KiB lies apart from the working space of the function on `μ`. -/
theorem e_w {d n : Nat} (hp : MFacts p) (h : d + n ≤ 1024) :
    Region.Disjoint ⟨x, scratchWords p * 8⟩ ⟨eAt p x + BitVec.ofNat 64 d, n⟩ := by
  have := hp.e
  rw [e_add]; exact Offset.base_disjoint _ (by simp only [oE]; omega) (by omega)

theorem e_w0 {n : Nat} (hp : MFacts p) (h : n ≤ 1024) :
    Region.Disjoint ⟨x, scratchWords p * 8⟩ ⟨eAt p x, n⟩ := by
  have := e_w (x := x) (d := 0) (n := n) hp (by omega)
  rwa [BitVec.add_zero] at this

/-- Two regions of the 1 KiB. -/
theorem e_e {d n d' n' : Nat} (h : d + n ≤ d' ∨ d' + n' ≤ d) (h₁ : d + n ≤ 1024) (h₂ : d' + n' ≤ 1024) :
    Region.Disjoint ⟨eAt p x + BitVec.ofNat 64 d, n⟩ ⟨eAt p x + BitVec.ofNat 64 d', n'⟩ :=
  Offset.disjoint _ h (by omega) (by omega)

theorem e_e0 {n d' n' : Nat} (h : n ≤ d') (h₂ : d' + n' ≤ 1024) :
    Region.Disjoint ⟨eAt p x, n⟩ ⟨eAt p x + BitVec.ofNat 64 d', n'⟩ :=
  Offset.disjoint_base _ h (by omega) |>.symm

end

/-! ## The invariant -/

/-- What the registers hold: the arguments, and `E`. -/
def signV (p : Params) (s : State) : Reg → BitVec 64
  | .r22 => s.gpr .r3 | .r23 => s.gpr .r4 | .r24 => s.gpr .r5 | .r25 => s.gpr .r6 | .r26 => s.gpr .r7
  | .r27 => s.gpr .r8 | .r28 => s.gpr .r9 | .r29 => s.gpr .r10 | .r30 => eAt p (s.gpr .r10) | _ => 0

/-- What the body may write. -/
abbrev sW (p : Params) (STK : Nat) (s : State) : List Region := [scrR p s, sigR p s, below s.sp STK]

abbrev SInv (p : Params) (STK : Nat) (s : State) : State → Prop :=
  Inv s (eAt p (s.gpr .r10)) oSV signRegs (signV p s) (sW p STK s)

theorem signRegs_pres : ∀ r ∈ signRegs, r ∈ preserved := by decide

section
variable {p : Params} {STK : Nat} {s : State} (hF : MFacts p) (hp : MSPre p STK s) (h48 : 48 ≤ STK)

theorem s_e {t : State} (h : SInv p STK s t) : t.gpr .r30 = eAt p (s.gpr .r10) := h.regs _ (by decide)

/-- The slots, in `scratch` and apart from what the body writes there. -/
theorem slot_sub : Region.Sub (slotArea (eAt p (s.gpr .r10)) oSV signRegs) (scrR p s) := e_sub (by decide)

theorem slot_e {d n : Nat} (h : d + n ≤ oSV ∨ oSV + 80 ≤ d) (h₁ : d + n ≤ 1024) :
    (slotArea (eAt p (s.gpr .r10)) oSV signRegs).Disjoint ⟨eAt p (s.gpr .r10) + BitVec.ofNat 64 d, n⟩ :=
  e_e (h.symm.imp id id) (by decide) h₁

include hF in
theorem slot_w : (slotArea (eAt p (s.gpr .r10)) oSV signRegs).Disjoint ⟨s.gpr .r10, scratchWords p * 8⟩ :=
  (e_w hF (by decide)).symm

include hp in
theorem slot_g : (slotArea (eAt p (s.gpr .r10)) oSV signRegs).Disjoint (sigR p s) :=
  hp.gc.symm.sub_left slot_sub

include hp h48 in
theorem below48 : Region.Sub (below s.sp 48) (below s.sp STK) := below_sub h48 (by have := hp.stk; omega)

include hp h48 in
theorem slot_b : (slotArea (eAt p (s.gpr .r10)) oSV signRegs).Disjoint (below s.sp 48) :=
  (hp.bx.symm.sub_left slot_sub).sub_right (below48 hp h48)

include hF hp in
theorem e_in {t : State} (hw : t.wr = s.wr) {d n : Nat} (h : d + n ≤ 1024) :
    InRegions t.wr (eAt p (s.gpr .r10) + BitVec.ofNat 64 d) n := by
  rw [hw, hp.wr, e_add]
  exact in_base (List.mem_cons_of_mem _ List.mem_cons_self) (by rw [msw]; omega)
    (by have := hF.e; omega)

include hp in
/-- A region of the 1 KiB, writable. -/
theorem e_cov {t : State} (hw : t.wr = s.wr) {d n : Nat} (h : d + n ≤ 1024) :
    PPC64LE.Covers [⟨eAt p (s.gpr .r10) + BitVec.ofNat 64 d, n⟩] t.wr := by
  rw [hw, hp.wr]
  refine Covers.of_sub fun r hr => ?_
  rw [List.mem_singleton.mp hr]
  exact ⟨scrR p s, List.mem_cons_of_mem _ List.mem_cons_self, oE p + d, e_add _ _ _, by
    simp only [msw]; omega⟩

include hp in
theorem e_cov0 {t : State} (hw : t.wr = s.wr) {n : Nat} (h : n ≤ 1024) :
    PPC64LE.Covers [⟨eAt p (s.gpr .r10), n⟩] t.wr := by
  have := e_cov hp hw (d := 0) (n := n) (by omega)
  rwa [BitVec.add_zero] at this

theorem slot_e0 {n : Nat} (h : n ≤ oSV) :
    (slotArea (eAt p (s.gpr .r10)) oSV signRegs).Disjoint ⟨eAt p (s.gpr .r10), n⟩ :=
  (e_e0 h (by decide)).symm

/-- The inputs, while the body runs: none of them is in `sW`. -/
theorem s_keep {t : State} (h : SInv p STK s t) {R : Region} (hn : R.len < 2 ^ 64)
    (hg : R.Disjoint (sigR p s)) (hc : R.Disjoint (scrR p s)) (hb : (below s.sp STK).Disjoint R) :
    bytesAt t.mem R.base R.len = bytesAt s.mem R.base R.len := by
  refine Proof.Sha3.PPC64LE.Pieces.bytes_keep h.frame hn fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hc
  · exact hg
  · exact hb.symm

end

/-! ## The setup -/

/-- After the setup: the invariant, and `0 ‖ ctx_len` at `oHdr(E)`. -/
structure MS1 (p : Params) (STK : Nat) (s t : State) : Prop where
  inv : SInv p STK s t
  hdr : bytesAt t.mem (eAt p (s.gpr .r10) + BitVec.ofNat 64 oHdr) 2 = [0, BitVec.ofNat 8 (s.gpr .r7).toNat]

/-- `E` into `r12`, from `scratch` in `sr`. -/
theorem base_ok (p : Params) (hF : MFacts p) {sr : Reg} (hsr : sr ≠ .r12) (u : State) :
    WP isa (.block (base sr p)) u fun u' => Upd u u' .r12 (eAt p (u.gpr sr)) ∧ u'.lr = u.lr := by
  unfold base
  refine WP.block_append_iff.mpr (WP.mono (KeyGen.loadImm_ok .r12 (by have := hF.e; omega) u) fun u₁ e₁ => ?_)
  subst e₁
  refine WP.cons exec_add (WP.block_nil ⟨⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩, rfl⟩)
  · rw [RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne _ _ hsr, RegUpd.gpr_write_self]
  · rw [RegUpd.gpr_write_of_ne _ _ hr, RegUpd.gpr_write_of_ne _ _ hr]

theorem signSetup_ok {p : Params} {STK : Nat} {s u : State} (hF : MFacts p) (hp : MSPre p STK s)
    (hu : ∀ r, r ≠ .r11 → u.gpr r = s.gpr r) (hrd : u.rd = s.rd) (hwr : u.wr = s.wr) (hsp : u.sp = s.sp)
    (hlr : u.lr = s.lr) (hm : u.mem = s.mem) :
    WP isa (.block (enter .r10 p signRegs signMs)) u (MS1 p STK s) := by
  unfold enter
  refine WP.block_append_iff.mpr (WP.mono (base_ok p hF (by decide) u) fun u₁ ⟨h₁, l₁⟩ => ?_)
  have g10 : u.gpr .r10 = s.gpr .r10 := hu _ (by decide)
  rw [g10] at h₁
  have hw₁ : u₁.wr = s.wr := h₁.wr.trans hwr
  refine setup_ok (v := signV p s) (W := sW p STK s) (by decide) (by decide) (by decide)
    (fun q hq => by rw [h₁.gpr]; exact e_in hF hp hw₁ (by revert q; decide))
    ⟨scrR p s, by simp, by rw [h₁.gpr]; exact slot_sub⟩ rfl (by decide) (by decide) (fun q hq => by
      simp only [signMs, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      iterate 8 exact ((h₁.other _ (by decide)).trans (hu _ (by decide))).symm
      exact h₁.gpr.symm)
    fun t₁ i₁ => ?_
  rw [h₁.gpr] at i₁
  have i₁ : SInv p STK s t₁ := inv_rebase i₁ signRegs_pres (h₁.rd.trans hrd) hw₁ (h₁.sp.trans hsp) (l₁.trans hlr)
    (fun r hr => (h₁.other r fun e => by revert hr; rw [e]; decide).trans (hu r fun e => by revert hr; rw [e]; decide))
    (h₁.mem.trans hm)
  have g30 : t₁.gpr .r30 = eAt p (s.gpr .r10) := i₁.regs _ (by decide)
  have g26 : t₁.gpr .r26 = s.gpr .r7 := i₁.regs _ (by decide)
  refine hdr_ok (o := oHdr) (by decide) (by decide) (by decide) (by rw [g30]; exact e_in hF hp i₁.wr (by decide))
    (by rw [g30]; exact e_in hF hp i₁.wr (by decide)) fun t ht hrd' hwr' hsp' hg => WP.block_nil ⟨?_, ?_⟩
  · refine i₁.step signRegs_pres hrd' hwr' hsp' (fun r hr => hg r fun e => by revert hr; rw [e]; decide)
      (ht ▸ hdrMem_frame _ _ _) (fun r hr => ?_) fun r hr => ?_
    · rw [List.mem_singleton.mp hr, g30]; exact ⟨scrR p s, by simp, e_sub (by decide)⟩
    · rw [List.mem_singleton.mp hr, g30]; exact slot_e (.inr (by decide)) (by decide)
  · rw [ht, g30, g26, show s.gpr .r7 = BitVec.ofNat 64 (s.gpr .r7).toNat by simp, hdrMem_bytes]
    simp

/-! ## `μ` -/

section
variable (p : Params) (s : State)

/-- The inputs. -/
abbrev skB : List Byte := bytesAt s.mem (s.gpr .r3) p.skLen
abbrev msgB : List Byte := bytesAt s.mem (s.gpr .r4) (s.gpr .r5).toNat
abbrev ctxB : List Byte := bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat
abbrev rndB : List Byte := bytesAt s.mem (s.gpr .r8) 32

/-- The formatted message. -/
abbrev fmtB : List Byte := [0, BitVec.ofNat 8 (s.gpr .r7).toNat] ++ ctxB s ++ msgB s

end

/-- After `μ`: the invariant, and `μ` at `oMU(E)`. -/
structure MS2 (p : Params) (STK : Nat) (s t : State) : Prop where
  inv : SInv p STK s t
  mu : bytesAt t.mem (eAt p (s.gpr .r10) + BitVec.ofNat 64 oMU) 64 = messageRep (skTr (skB p s)) (fmtB s)

theorem signHash_ok {p : Params} {STK : Nat} {s t : State} (hF : MFacts p) (hp : MSPre p STK s) (h48 : 48 ≤ STK)
    (h : MS1 p STK s t) : WP isa (muHash ⟨.r22, 64, .imm 64⟩) t (MS2 p STK s) := by
  have hi := h.inv
  have g22 : t.gpr .r22 = s.gpr .r3 := hi.regs _ (by decide)
  have g23 : t.gpr .r23 = s.gpr .r4 := hi.regs _ (by decide)
  have g24 : t.gpr .r24 = s.gpr .r5 := hi.regs _ (by decide)
  have g25 : t.gpr .r25 = s.gpr .r6 := hi.regs _ (by decide)
  have g26 : t.gpr .r26 = s.gpr .r7 := hi.regs _ (by decide)
  have g30 := s_e hi
  have hsk := hF.sk
  have b48 := below48 hp h48
  have hsp : t.sp = s.sp := hi.sp
  have trS : Region.Sub ⟨s.gpr .r3 + BitVec.ofNat 64 64, 64⟩ (skR p s) := Offset.sub_base _ (by omega)
  have eS := e_sub0 (p := p) (x := s.gpr .r10) (n := 840) (by decide)
  have cr : ∀ R ∈ [skR p s, msgR s, ctxR s, rndR s], PPC64LE.Covers [R] (t.rd ++ t.wr) := fun R hR => by
    rw [hi.rd, hp.rd]; exact cov_rd fun a n ⟨r, hr, hc⟩ => ⟨r, by rw [List.mem_singleton.mp hr]; exact hR, hc⟩
  have ke : KEnv 840 (eAt p (s.gpr .r10)) t :=
    ⟨by decide, e_cov0 hp hi.wr (by decide), by rw [hsp]; have := hp.stk; omega,
      by rw [hsp]; exact (hp.bx.sub_left b48).sub_right eS⟩
  have hin : ∀ q ∈ (⟨.r22, 64, .imm 64⟩ : Piece) :: fmtPieces, PieceOk 840 (eAt p (s.gpr .r10)) t q := by
    intro q hq
    simp only [fmtPieces, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact pieceOk_of (R := ⟨s.gpr .r3 + BitVec.ofNat 64 64, 64⟩)
        (by simp only [Piece.R, Piece.addr, Len.val, g22]) (by decide) (by decide) (show 64 < 2 ^ 15 by decide)
        (cov_rd (cov_in (k := p.skLen) (by rw [hi.rd, hp.rd]; simp) (by omega)))
        ((hp.kc.sub_left trS).sub_right eS) (by rw [hsp]; exact (hp.bk.sub_left b48).sub_right trS)
    · exact pieceOk_of (R := ⟨eAt p (s.gpr .r10) + BitVec.ofNat 64 oHdr, 2⟩)
        (by simp only [Piece.R, Piece.addr, Len.val, g30]) (by decide) (by decide) (show 2 < 2 ^ 15 by decide)
        (Proof.Sha3.PPC64LE.Pieces.cov_right (e_cov hp hi.wr (by decide))) (e_e0 (by decide) (by decide)).symm
        (by rw [hsp]; exact (hp.bx.sub_left b48).sub_right (e_sub (by decide)))
    · exact pieceOk_of (R := ctxR s) (by simp only [Piece.R, Piece.addr, Len.val, g25, g26, BitVec.add_zero])
        (by decide) (by decide) (show Reg.r26 ∈ preserved by decide) (cr _ (by simp))
        (hp.cc.sub_right eS) (by rw [hsp]; exact hp.bc.sub_left b48)
    · exact pieceOk_of (R := msgR s) (by simp only [Piece.R, Piece.addr, Len.val, g23, g24, BitVec.add_zero])
        (by decide) (by decide) (show Reg.r24 ∈ preserved by decide) (cr _ (by simp))
        (hp.mc.sub_right eS) (by rw [hsp]; exact hp.bm.sub_left b48)
  unfold muHash
  refine WP.mono (hash_ok (N := 840) (n := 64) (o := oMU) (out := eAt p (s.gpr .r10) + BitVec.ofNat 64 oMU) (by decide) (by decide) (by decide) (by decide) g30
    (by rw [g30]) ke (by simp) hin (e_cov hp hi.wr (by decide)) (e_e0 (by decide) (by decide)).symm
    (by rw [hsp]; exact (hp.bx.sub_left b48).sub_right (e_sub (by decide)))) fun t' ⟨k', d'⟩ => ⟨?_, ?_⟩
  · refine inv_kept hi signRegs_pres k' (fun r hr => ?_) fun r hr => ?_
    · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨scrR p s, by simp, e_sub (by decide)⟩
      · exact ⟨scrR p s, by simp, eS⟩
      · exact ⟨below s.sp STK, by simp, by rw [hsp]; exact b48⟩
    · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact slot_e (.inl (by decide)) (by decide)
      · exact slot_e0 (by decide)
      · rw [hsp]; exact slot_b hp h48
  · rw [d']
    have kt : bytesAt t.mem (s.gpr .r3 + BitVec.ofNat 64 64) 64 = skTr (skB p s) := by
      rw [s_keep hi (R := ⟨s.gpr .r3 + BitVec.ofNat 64 64, 64⟩) (show (64 : Nat) < 2 ^ 64 by decide) (hp.kg.sub_left trS)
        (hp.kc.sub_left trS) ((hp.bk.symm.sub_left trS).symm), skTr, Proof.MlKem.bytesAt_slice _ _ (by omega)]
    have kc : bytesAt t.mem (s.gpr .r6) (s.gpr .r7).toNat = ctxB s :=
      s_keep hi (R := ctxR s) (BitVec.isLt _) hp.cg hp.cc hp.bc
    have km : bytesAt t.mem (s.gpr .r4) (s.gpr .r5).toNat = msgB s :=
      s_keep hi (R := msgR s) (BitVec.isLt _) hp.mg hp.mc hp.bm
    have hh := h.hdr
    simp only [fmtPieces, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
      Piece.bytes, Piece.addr, Len.val, g22, g23, g24, g25, g26, g30, BitVec.add_zero]
    rw [kt, hh, kc, km]
    simp only [messageRep, H, List.append_assoc]

/-! ## The call of the signing function on `μ` -/

theorem ce_gpr (u : State) (rd wr : List Region) {r : Reg} (h : r ∉ linkRegs) :
    (u.callEntry.withRegions rd wr).gpr r = u.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h]

/-- The arguments of the call. -/
abbrev signArgs : List Instr := [mov .r3 .r22, .addi .r4 .r30 oMU, mov .r5 .r27, mov .r6 .r28, mov .r7 .r29]

theorem signCall_ok {p : Params} {STK S : Nat} {s t : State} (hF : MFacts p) (hp : MSPre p STK s)
    {f : Prog isa} (hf : Callee f (fun stk => signContract p PPC64LE.abi stk) S) (hS : S ≤ STK) {n : String}
    (h : MS2 p STK s t) :
    WP isa (.seq (.block signArgs) (.call n f)) t fun t' => SInv p STK s t' ∧
      Outcome (fun b => signMu p b (skB p s) (messageRep (skTr (skB p s)) (fmtB s)) (rndB s))
        ((t'.gpr .r3).setWidth 32) (bytesAt t'.mem (s.gpr .r9) p.sigLen) := by
  obtain ⟨stk, hstk, hver⟩ := hf.verified
  have hi := h.inv
  have hstkS : STK ≤ s.sp.toNat := hp.stk
  have g22 : t.gpr .r22 = s.gpr .r3 := hi.regs _ (by decide)
  have g27 : t.gpr .r27 = s.gpr .r8 := hi.regs _ (by decide)
  have g28 : t.gpr .r28 = s.gpr .r9 := hi.regs _ (by decide)
  have g29 : t.gpr .r29 = s.gpr .r10 := hi.regs _ (by decide)
  have g30 := s_e hi
  have hE := hF.e
  have fx := hp.fx
  rw [msw] at fx
  have hsw : scratchWords p * 8 ≤ oE p := by simp only [oE]; omega
  unfold signArgs mov
  refine WP.seq (Ed25519.PPC64LE.Whole.args5_ok (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) fun u hu a3 a4 a5 a6 a7 => ?_)
  rw [g22, BitVec.add_zero] at a3
  rw [g30] at a4
  rw [g27, BitVec.add_zero] at a5
  rw [g28, BitVec.add_zero] at a6
  rw [g29, BitVec.add_zero] at a7
  have iu : SInv p STK s u := hi.step signRegs_pres hu.rd hu.wr hu.sp hu.pres (by rw [hu.mem]; exact Frame.refl _ _)
    (fun _ h => absurd h List.not_mem_nil) (fun _ h => absurd h List.not_mem_nil)
  have usp : u.sp = s.sp := iu.sp
  have urd : u.rd = s.rd := iu.rd
  have uwr : u.wr = s.wr := iu.wr
  have bs : Region.Sub (below s.sp stk) (below s.sp STK) := below_sub (by omega) (by omega)
  have muS : Region.Sub ⟨eAt p (s.gpr .r10) + BitVec.ofNat 64 oMU, 64⟩ (scrR p s) := e_sub (by decide)
  have muW : Region.Disjoint ⟨s.gpr .r10, scratchWords p * 8⟩ ⟨eAt p (s.gpr .r10) + BitVec.ofNat 64 oMU, 64⟩ :=
    e_w hF (by decide)
  have muF : (eAt p (s.gpr .r10) + BitVec.ofNat 64 oMU).toNat + 64 ≤ 2 ^ 64 := e_fit hp.fx (by decide) (by decide)
  have hd : sdepth f < 2 ^ 64 := by have := hf.stack; omega
  refine WP.callAny (k := signContract p PPC64LE.abi stk) hver.1
    (rd := [skR p s, ⟨eAt p (s.gpr .r10) + BitVec.ofNat 64 oMU, 64⟩, rndR s])
    (wr := [sigR p s, ⟨s.gpr .r10, scratchWords p * 8⟩]) ?_ ?_ ?_ (fun s' rd' wr' sp' fr' cs' post' => ?_) hd
  · refine sign_pre ((ce_gpr _ _ _ (by decide)).trans a3) ((ce_gpr _ _ _ (by decide)).trans a4)
      ((ce_gpr _ _ _ (by decide)).trans a5) ((ce_gpr _ _ _ (by decide)).trans a6)
      ((ce_gpr _ _ _ (by decide)).trans a7) rfl rfl (by simp only [State.withRegions_sp, State.callEntry_sp, usp]; omega)
      hp.kg (hp.kc.sub_right w_sub) (hp.gc.symm.sub_left muS) muW.symm hp.rg (hp.rc.sub_right w_sub)
      (hp.gc.sub_right w_sub) ?_ ?_ ?_ ?_ ?_ hp.fk muF hp.fr hp.fg (by omega)
    all_goals simp only [State.withRegions_sp, State.callEntry_sp, usp]
    · exact hp.bk.sub_left bs
    · exact (hp.bx.sub_left bs).sub_right muS
    · exact hp.br.sub_left bs
    · exact hp.bg.sub_left bs
    · exact (hp.bx.sub_left bs).sub_right w_sub
  · rw [urd, uwr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨skR p s, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR p s, by simp, oE p + oMU, e_add _ _ _, e_len p (d := oMU) (n := 64) (by decide)⟩
    · exact ⟨rndR s, by simp, 0, by simp, by simp⟩
    · exact ⟨sigR p s, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR p s, by simp, 0, by simp, by simp only [msw]; omega⟩
  · rw [uwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨sigR p s, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR p s, by simp, 0, by simp, by simp only [msw]; omega⟩
  · refine ⟨iu.step signRegs_pres rd' wr' sp' cs' fr' (fun r hr => ?_) fun r hr => ?_, ?_⟩
    · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨sigR p s, by simp, fun _ h => h⟩
      · exact ⟨scrR p s, by simp, w_sub⟩
      · exact ⟨below s.sp STK, by simp, by rw [usp]; exact below_sub (by have := hf.stack; omega) (by omega)⟩
    · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact slot_g hp
      · exact slot_w hF
      · rw [usp]
        exact (hp.bx.symm.sub_left slot_sub).sub_right (below_sub (by have := hf.stack; omega) (by omega))
    · have q := sign_post post'
      simp only [State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem,
        State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r4 ∉ linkRegs by decide),
        State.callEntry_gpr _ (show Reg.r5 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r6 ∉ linkRegs by decide),
        a3, a4, a5, a6, hu.mem] at q
      rw [s_keep hi (R := skR p s) (by have := hF.skl; show p.skLen < 2 ^ 64; omega) hp.kg hp.kc hp.bk, h.mu,
        s_keep hi (R := rndR s) (show (32 : Nat) < 2 ^ 64 by decide) hp.rg hp.rc hp.br] at q
      exact q

/-! ## `sign_message` -/

/-- The result: 2 for a context string longer than 255 bytes, else the
signature of the formatted message. -/
theorem signMessage_wp {p : Params} {STK S : Nat} (hF : MFacts p) (h48 : 48 ≤ STK) {f : Prog isa}
    (hf : Callee f (fun stk => signContract p PPC64LE.abi stk) S) (hS : S ≤ STK) {n : String} {s : State}
    (hp : MSPre p STK s) :
    WP isa (signMessage n f p) s fun t => abiPreserved s t ∧ (signMessageContract p PPC64LE.abi STK).post s t := by
  unfold signMessage top
  refine WP.seq (WP.cons (exec_lsr_d (by decide)) (WP.block_nil ?_))
  have hu := Upd.write s .r11 (s.gpr .r7 >>> 8)
  refine wp_ite (decide ((s.gpr .r7).toNat < 256)) (by rw [eval_zero, hu.gpr]; exact congrArg some (shr8_zero _)) (fun hcl => ?_)
    fun hcl => ?_
  · have hcl' : (s.gpr .r7).toNat < 256 := of_decide_eq_true hcl
    refine WP.seq (WP.mono (signSetup_ok hF hp hu.other hu.rd hu.wr hu.sp rfl hu.mem) fun t₁ h₁ => ?_)
    refine WP.seq (WP.mono (signHash_ok hF hp h48 h₁) fun t₂ h₂ => ?_)
    refine WP.seq (WP.mono (signCall_ok hF hp hf hS h₂) fun t₃ ⟨h₃, r₃⟩ => ?_)
    have hrl : ∀ q ∈ restoreList oSV signRegs, q.2 + 8 ≤ 1024 := by decide
    refine restore_ok h₃ (by decide) (s_e h₃) (by decide) (by decide) (by decide) (by decide)
      (fun q hq => by
        have := hrl q hq
        have := e_len p (d := q.2) (n := 8) (by omega)
        have := hF.e
        rw [h₃.rd, h₃.wr, hp.rd, hp.wr, e_add]
        exact ⟨scrR p s, by simp, Offset.contains_base _ (by omega) (by omega)⟩)
      fun t₄ g₄ sp₄ lr₄ m₄ o₄ => ⟨⟨g₄, sp₄, lr₄⟩, ?_⟩
    · sig_post [signMessageContract, signMessageSig, PPC64LE.abi, PPC64LE.argRegs]
      rw [Proof.MlDsa.Message.formatMessage_some (by rw [Proof.MlKem.bytesAt_length]; exact hcl'), o₄ .r3 (by decide)
        (by decide), m₄]
      simp only [signInternal, Proof.MlKem.bytesAt_length]
      exact r₃
  · have hcl' : ¬ (s.gpr .r7).toNat < 256 := of_decide_eq_false hcl
    refine WP.cons (exec_li (d := .r3) (imm := 2) (by decide)) (WP.block_nil ⟨⟨fun r hr => ?_, rfl, rfl⟩, ?_⟩)
    · rw [(Upd.write _ _ _).other _ (Proof.Sha3.PPC64LE.Pieces.pres_ne hr).2.1, hu.other _ (by revert hr; cases r <;> decide)]
    · sig_post [signMessageContract, signMessageSig, PPC64LE.abi, PPC64LE.argRegs]
      rw [Proof.MlDsa.Message.formatMessage_none (by rw [Proof.MlKem.bytesAt_length]; omega)]
      rfl

end VG.Proof.MlDsa.PPC64LE.Message
