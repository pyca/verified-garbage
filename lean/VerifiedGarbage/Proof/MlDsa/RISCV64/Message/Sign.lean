module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.Message.Steps
public import VerifiedGarbage.Proof.MlDsa.RISCV64.Message.Contracts
public import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Base
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Common
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.MlDsa.Message.Common
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Impl.MlDsa.RISCV64.Message

public import VerifiedGarbage.TCB.RISCV64.Target
/-!
# ML-DSA on RISC-V, `sign_message`: correctness

From a state satisfying `MSPre`, `signMessage n f p` returns 2 if the
context string is longer than 255 bytes; otherwise it saves our caller's
registers in the 1 KiB at `E` (`MS1`), computes `μ` of the formatted message
into `840(E)` (`MS2`), and calls the signing function on `μ` `f`, which gives
the signature of `ML-DSA.Sign_internal` on the formatted message
(`signMessage_wp`). Between the steps, `Inv` records the arguments in
`s0`–`s8` and the saved registers, and that only `scratch`, `sig` and the
stack below the stack pointer change.
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

/-! ## The parameter sets -/

/-- What the proofs need of the parameter set. -/
structure MFacts (p : Params) : Prop where
  e : oE p + 1024 < 2 ^ 31 - 2048
  sk : 128 ≤ p.skLen
  pk1 : 1024 ≤ p.pkLen
  pk : p.pkLen < 3072
  skl : p.skLen < 8192
  sgl : p.sigLen < 8192
  psk : preparedSecretKeyBytes p < 2 ^ 31
  ppk : preparedPublicKeyBytes p < 2 ^ 31
  psk1 : p.skLen ≤ preparedSecretKeyBytes p
  ppk1 : p.pkLen ≤ preparedPublicKeyBytes p

theorem mfacts {p : Params} (h : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) : MFacts p := by
  rcases h with rfl | rfl | rfl <;> exact ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩

/-- The key's length, encoded or prepared. -/
theorem sk128 {p : Params} (hF : MFacts p) (q : Bool) : 128 ≤ PreparedKey.skBytes p q ∧ p.skLen ≤ PreparedKey.skBytes p q ∧
    PreparedKey.skBytes p q < 2 ^ 31 := by
  have := hF.sk; have := hF.skl; have := hF.psk; have := hF.psk1
  cases q <;> simp only [PreparedKey.skBytes] <;> omega

/-- The encoded key, in the key. -/
theorem skE_sub {p : Params} (hF : MFacts p) (q : Bool) (x : State) :
    Region.Sub ⟨x.gpr .a0, p.skLen⟩ (skR p x q) := by
  have e := Offset.sub_base (x.gpr .a0) (d := 0) (n := p.skLen) (k := PreparedKey.skBytes p q)
    (by have := (sk128 hF q).2.1; omega)
  rwa [BitVec.add_zero] at e

theorem pkL {p : Params} (hF : MFacts p) (q : Bool) : p.pkLen ≤ PreparedKey.pkBytes p q ∧
    PreparedKey.pkBytes p q < 2 ^ 31 := by
  have := hF.pk; have := hF.ppk; have := hF.ppk1
  cases q <;> simp only [PreparedKey.pkBytes] <;> omega

/-- The encoded public key, in the key. -/
theorem pkE_sub {p : Params} (hF : MFacts p) (q : Bool) (x : State) :
    Region.Sub ⟨x.gpr .a0, p.pkLen⟩ (pkR p x q) := by
  have e := Offset.sub_base (x.gpr .a0) (d := 0) (n := p.pkLen) (k := PreparedKey.pkBytes p q)
    (by have := (pkL hF q).1; omega)
  rwa [BitVec.add_zero] at e

theorem msw (p : Params) : messageScratchWords p * 8 = oE p + 1024 := by
  simp only [messageScratchWords, oE]; omega_arith

theorem e_len (p : Params) {d n : Nat} (h : d + n ≤ 1024) : oE p + d + n ≤ messageScratchWords p * 8 := by
  rw [msw]; omega_arith

/-- A region of the 1 KiB does not wrap around. -/
theorem e_fit {p : Params} {x : Addr} (hx : x.toNat + messageScratchWords p * 8 ≤ 2 ^ 64) {d n : Nat}
    (hn : 0 < n) (h : d + n ≤ 1024) : (x + BitVec.ofNat 64 (oE p) + BitVec.ofNat 64 d).toNat + n ≤ 2 ^ 64 := by
  have := e_len p h
  rw [Proof.MlDsa.Message.add_add, Proof.MlDsa.Message.toNat_add_ofNat (by omega_arith)]; omega_arith

/-! ## The 1 KiB -/

/-- `E`, from `scratch` in `r` of the entry state. -/
abbrev eAt (p : Params) (x : Addr) : Addr := x + BitVec.ofNat 64 (oE p)

theorem e_add (p : Params) (x : Addr) (d : Nat) :
    eAt p x + BitVec.ofNat 64 d = x + BitVec.ofNat 64 (oE p + d) :=
  Proof.MlDsa.Message.add_add _ _ _

/-- `E` is a multiple of 8. -/
theorem e_al {p : Params} {x : Addr} (hx : x.toNat % 8 = 0) (hf : x.toNat + messageScratchWords p * 8 ≤ 2 ^ 64) :
    (eAt p x).toNat % 8 = 0 := by
  have := msw p
  rw [Proof.MlDsa.Message.toNat_add_ofNat (by omega_arith)]
  simp only [oE] at this ⊢; omega_arith

section
variable {p : Params} {x : Addr}

/-- A region in the 1 KiB lies in `scratch`. -/
theorem e_sub {d n : Nat} (h : d + n ≤ 1024) :
    Region.Sub ⟨eAt p x + BitVec.ofNat 64 d, n⟩ ⟨x, messageScratchWords p * 8⟩ := by
  rw [e_add]; exact Offset.sub_base _ (by rw [msw]; omega_arith)

theorem e_sub0 {n : Nat} (h : n ≤ 1024) : Region.Sub ⟨eAt p x, n⟩ ⟨x, messageScratchWords p * 8⟩ := by
  have := e_sub (p := p) (x := x) (d := 0) (n := n) (by omega_arith)
  rwa [BitVec.add_zero] at this

/-- The working space of the function on `μ` lies in `scratch`. -/
theorem w_sub : Region.Sub ⟨x, scratchWords p * 8⟩ ⟨x, messageScratchWords p * 8⟩ :=
  Region.sub_prefix (by simp only [messageScratchWords]; omega_arith)

/-- A region in the 1 KiB lies apart from the working space of the function on `μ`. -/
theorem e_w {d n : Nat} (hp : MFacts p) (h : d + n ≤ 1024) :
    Region.Disjoint ⟨x, scratchWords p * 8⟩ ⟨eAt p x + BitVec.ofNat 64 d, n⟩ := by
  have := hp.e
  rw [e_add]; exact Offset.base_disjoint _ (by simp only [oE]; omega_arith) (by omega_arith)

/-- Two regions of the 1 KiB. -/
theorem e_e {d n d' n' : Nat} (h : d + n ≤ d' ∨ d' + n' ≤ d) (h₁ : d + n ≤ 1024) (h₂ : d' + n' ≤ 1024) :
    Region.Disjoint ⟨eAt p x + BitVec.ofNat 64 d, n⟩ ⟨eAt p x + BitVec.ofNat 64 d', n'⟩ :=
  Offset.disjoint _ h (by omega_arith) (by omega_arith)

theorem e_e0 {n d' n' : Nat} (h : n ≤ d') (h₂ : d' + n' ≤ 1024) :
    Region.Disjoint ⟨eAt p x, n⟩ ⟨eAt p x + BitVec.ofNat 64 d', n'⟩ :=
  Offset.disjoint_base _ h (by omega_arith) |>.symm

end

/-! ## The invariant -/

/-- What the registers hold: the arguments, and `E`. -/
def signV (p : Params) (s : State) : Reg → BitVec 64
  | .s0 => s.gpr .a0 | .s1 => s.gpr .a1 | .s2 => s.gpr .a2 | .s3 => s.gpr .a3 | .s4 => s.gpr .a4
  | .s5 => s.gpr .a5 | .s6 => s.gpr .a6 | .s7 => s.gpr .a7 | .s8 => eAt p (s.gpr .a7) | _ => 0

/-- What the body may write. -/
abbrev sW (p : Params) (STK : Nat) (s : State) : List Region := [scrR p s, sigR p s, below s.sp STK]

abbrev SInv (p : Params) (STK : Nat) (s : State) : State → Prop :=
  Inv s (eAt p (s.gpr .a7)) oSV signRegs (signV p s) (sW p STK s)

theorem signRegs_pres : ∀ r ∈ signRegs, r ∈ preserved := by decide

section
variable {p : Params} {q : Bool} {STK : Nat} {s : State} (hF : MFacts p) (hp : MSPre p q STK s) (h48 : 1168 ≤ STK)

theorem s_e {t : State} (h : SInv p STK s t) : t.gpr .s8 = eAt p (s.gpr .a7) := h.regs _ (by decide)

/-- The slots, in `scratch` and apart from what the body writes there. -/
theorem slot_sub : Region.Sub (slotArea (eAt p (s.gpr .a7)) oSV signRegs) (scrR p s) := e_sub (by decide)

theorem slot_e {d n : Nat} (h : d + n ≤ oSV ∨ oSV + 80 ≤ d) (h₁ : d + n ≤ 1024) :
    (slotArea (eAt p (s.gpr .a7)) oSV signRegs).Disjoint ⟨eAt p (s.gpr .a7) + BitVec.ofNat 64 d, n⟩ :=
  e_e (h.symm.imp id id) (by decide) h₁

include hF in
theorem slot_w : (slotArea (eAt p (s.gpr .a7)) oSV signRegs).Disjoint ⟨s.gpr .a7, scratchWords p * 8⟩ :=
  (e_w hF (by decide)).symm

include hp in
theorem slot_g : (slotArea (eAt p (s.gpr .a7)) oSV signRegs).Disjoint (sigR p s) :=
  hp.gc.symm.sub_left slot_sub

include hp h48 in
theorem below48 : Region.Sub (below s.sp 1168) (below s.sp STK) := below_sub h48 (by have := hp.stk; omega_arith)

include hp h48 in
theorem slot_b : (slotArea (eAt p (s.gpr .a7)) oSV signRegs).Disjoint (below s.sp 1168) :=
  (hp.bx.symm.sub_left slot_sub).sub_right (below48 hp h48)

include hF hp in
theorem e_in {t : State} (hw : t.wr = s.wr) {d n : Nat} (h : d + n ≤ 1024) :
    InRegions t.wr (eAt p (s.gpr .a7) + BitVec.ofNat 64 d) n := by
  rw [hw, hp.wr, e_add]
  exact in_base (List.mem_cons_of_mem _ List.mem_cons_self) (by rw [msw]; omega_arith)
    (by have := hF.e; omega_arith)

include hp in
/-- A region of the 1 KiB, writable. -/
theorem e_cov {t : State} (hw : t.wr = s.wr) {d n : Nat} (h : d + n ≤ 1024) :
    RISCV64.Covers [⟨eAt p (s.gpr .a7) + BitVec.ofNat 64 d, n⟩] t.wr := by
  rw [hw, hp.wr]
  refine Covers.of_sub fun r hr => ?_
  rw [List.mem_singleton.mp hr]
  exact ⟨scrR p s, List.mem_cons_of_mem _ List.mem_cons_self, oE p + d, e_add _ _ _, by
    simp only [msw]; omega_arith⟩

include hp in
theorem e_cov0 {t : State} (hw : t.wr = s.wr) {n : Nat} (h : n ≤ 1024) :
    RISCV64.Covers [⟨eAt p (s.gpr .a7), n⟩] t.wr := by
  have := e_cov hp hw (d := 0) (n := n) (by omega_arith)
  rwa [BitVec.add_zero] at this

theorem slot_e0 {n : Nat} (h : n ≤ oSV) :
    (slotArea (eAt p (s.gpr .a7)) oSV signRegs).Disjoint ⟨eAt p (s.gpr .a7), n⟩ :=
  (e_e0 h (by decide)).symm

/-- The inputs, while the body runs: none of them is in `sW`. -/
theorem s_keep {t : State} (h : SInv p STK s t) {R : Region} (hn : R.len < 2 ^ 64)
    (hg : R.Disjoint (sigR p s)) (hc : R.Disjoint (scrR p s)) (hb : (below s.sp STK).Disjoint R) :
    bytesAt t.mem R.base R.len = bytesAt s.mem R.base R.len := by
  refine Proof.Sha3.RISCV64.Pieces.bytes_keep h.frame hn fun r hr => ?_
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
  hdr : bytesAt t.mem (eAt p (s.gpr .a7) + BitVec.ofNat 64 oHdr) 2 = [0, BitVec.ofNat 8 (s.gpr .a4).toNat]

/-- `E` into `t2`, from `scratch` in `sr`. -/
theorem base_ok (p : Params) (hF : MFacts p) {sr : Reg} (hsr : sr ≠ .t2) (u : State) :
    WP isa (.block (base sr p)) u fun u' => Steps.Upd u u' .t2 (eAt p (u.gpr sr)) ∧ u'.gpr .ra = u.gpr .ra := by
  unfold base
  refine WP.block_append_iff.mpr (WP.mono (KeyGen.loadImm_ok .t2 (by have := hF.e; omega_arith) u) fun u₁ e₁ => ?_)
  subst e₁
  refine Steps.WP.cons exec_add (WP.block_nil ⟨⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩, rfl⟩)
  · rw [RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne _ _ hsr, RegUpd.gpr_write_self]
  · rw [RegUpd.gpr_write_of_ne _ _ hr, RegUpd.gpr_write_of_ne _ _ hr]

theorem signSetup_ok {p : Params} {q : Bool} {STK : Nat} {s u : State} (hF : MFacts p) (hp : MSPre p q STK s)
    (hu : ∀ r, r ≠ .t1 → u.gpr r = s.gpr r) (hrd : u.rd = s.rd) (hwr : u.wr = s.wr) (hsp : u.sp = s.sp)
    (hlr : u.gpr .ra = s.gpr .ra) (hm : u.mem = s.mem) :
    WP isa (.block (enter .a7 p signRegs signMs)) u (MS1 p STK s) := by
  unfold enter
  refine WP.block_append_iff.mpr (WP.mono (base_ok p hF (by decide) u) fun u₁ ⟨h₁, l₁⟩ => ?_)
  have g10 : u.gpr .a7 = s.gpr .a7 := hu _ (by decide)
  rw [g10] at h₁
  have hw₁ : u₁.wr = s.wr := h₁.wr.trans hwr
  refine setup_ok (v := signV p s) (W := sW p STK s) (by rw [h₁.gpr]; exact e_al hp.alx hp.fx) (by decide) (by decide)
    (fun q hq => by rw [h₁.gpr]; exact e_in hF hp hw₁ (by revert q; decide))
    ⟨scrR p s, by simp, by rw [h₁.gpr]; exact slot_sub⟩ rfl (by decide) (by decide) (fun q hq => by
      simp only [signMs, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      iterate 8 exact ((h₁.other _ (by decide)).trans (hu _ (by decide))).symm
      exact h₁.gpr.symm)
    fun t₁ i₁ _ => ?_
  rw [h₁.gpr] at i₁
  have i₁ : SInv p STK s t₁ := inv_rebase i₁ signRegs_pres (h₁.rd.trans hrd) hw₁ (h₁.sp.trans hsp) (l₁.trans hlr)
    (fun r hr => (h₁.other r fun e => by revert hr; rw [e]; decide).trans (hu r fun e => by revert hr; rw [e]; decide))
    (h₁.mem.trans hm)
  have g30 : t₁.gpr .s8 = eAt p (s.gpr .a7) := i₁.regs _ (by decide)
  have g26 : t₁.gpr .s4 = s.gpr .a4 := i₁.regs _ (by decide)
  refine hdr_ok (o := oHdr) (by decide) (by decide) (by decide) (by rw [g30]; exact e_in hF hp i₁.wr (by decide))
    (by rw [g30]; exact e_in hF hp i₁.wr (by decide)) fun t ht hrd' hwr' hsp' hg => WP.block_nil ⟨?_, ?_⟩
  · refine i₁.step signRegs_pres hrd' hwr' hsp' (fun r hr => hg r fun e => by revert hr; rw [e]; decide)
      (ht ▸ hdrMem_frame _ _ _) (fun r hr => ?_) fun r hr => ?_
    · rw [List.mem_singleton.mp hr, g30]; exact ⟨scrR p s, by simp, e_sub (by decide)⟩
    · rw [List.mem_singleton.mp hr, g30]; exact slot_e (.inr (by decide)) (by decide)
  · rw [ht, g30, g26, show s.gpr .a4 = BitVec.ofNat 64 (s.gpr .a4).toNat by simp, hdrMem_bytes]
    simp

/-! ## `μ` -/

section
variable (p : Params) (s : State)

/-- The inputs. -/
abbrev skB : List Byte := bytesAt s.mem (s.gpr .a0) p.skLen
abbrev msgB : List Byte := bytesAt s.mem (s.gpr .a1) (s.gpr .a2).toNat
abbrev ctxB : List Byte := bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat
abbrev rndB : List Byte := bytesAt s.mem (s.gpr .a5) 32

/-- The formatted message. -/
abbrev fmtB : List Byte := [0, BitVec.ofNat 8 (s.gpr .a4).toNat] ++ ctxB s ++ msgB s

end

/-- After `μ`: the invariant, and `μ` at `oMU(E)`. -/
structure MS2 (p : Params) (STK : Nat) (s t : State) : Prop where
  inv : SInv p STK s t
  mu : bytesAt t.mem (eAt p (s.gpr .a7) + BitVec.ofNat 64 oMU) 64 = messageRep (skTr (skB p s)) (fmtB s)

/-- Where the hash of `μ` may run, from the invariant. -/
theorem signHash_env {p : Params} {q : Bool} {STK : Nat} {s t : State} (hF : MFacts p) (hp : MSPre p q STK s) (h48 : 1168 ≤ STK)
    (hi : SInv p STK s t) : KEnv 840 (eAt p (s.gpr .a7)) t ∧
      ∀ q ∈ (⟨.s0, 64, .imm 64⟩ : Piece) :: fmtPieces, PieceOk 840 (eAt p (s.gpr .a7)) t q := by
  have g22 : t.gpr .s0 = s.gpr .a0 := hi.regs _ (by decide)
  have g23 : t.gpr .s1 = s.gpr .a1 := hi.regs _ (by decide)
  have g24 : t.gpr .s2 = s.gpr .a2 := hi.regs _ (by decide)
  have g25 : t.gpr .s3 = s.gpr .a3 := hi.regs _ (by decide)
  have g26 : t.gpr .s4 = s.gpr .a4 := hi.regs _ (by decide)
  have g30 := s_e hi
  have hsk := (sk128 hF q).1
  have hsk0 := hF.sk
  have b48 := below48 hp h48
  have hsp : t.sp = s.sp := hi.sp
  have trS : Region.Sub ⟨s.gpr .a0 + BitVec.ofNat 64 64, 64⟩ (skR p s q) := Offset.sub_base _ (by omega_arith)
  have eS := e_sub0 (p := p) (x := s.gpr .a7) (n := 840) (by decide)
  have cr : ∀ R ∈ [skR p s q, msgR s, ctxR s, rndR s], RISCV64.Covers [R] (t.rd ++ t.wr) := fun R hR => by
    rw [hi.rd, hp.rd]; exact cov_rd fun a n ⟨r, hr, hc⟩ => ⟨r, by rw [List.mem_singleton.mp hr]; exact hR, hc⟩
  have ke : KEnv 840 (eAt p (s.gpr .a7)) t :=
    ⟨by decide, e_cov0 hp hi.wr (by decide), e_al hp.alx hp.fx, by rw [hsp]; exact hp.al,
      by rw [hsp]; have := hp.stk; omega_arith, by rw [hsp]; exact (hp.bx.sub_left b48).sub_right eS⟩
  have hin : ∀ q ∈ (⟨.s0, 64, .imm 64⟩ : Piece) :: fmtPieces, PieceOk 840 (eAt p (s.gpr .a7)) t q := by
    intro q hq
    simp only [fmtPieces, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact pieceOk_of (R := ⟨s.gpr .a0 + BitVec.ofNat 64 64, 64⟩)
        (by simp only [Piece.R, Piece.addr, Len.val, g22]) (by decide) (by decide) (show 64 < 2048 by decide)
        (cov_rd (cov_in (k := PreparedKey.skBytes p q) (by rw [hi.rd, hp.rd]; simp) (by omega_arith)))
        ((hp.kc.sub_left trS).sub_right eS) (by rw [hsp]; exact (hp.bk.sub_left b48).sub_right trS)
    · exact pieceOk_of (R := ⟨eAt p (s.gpr .a7) + BitVec.ofNat 64 oHdr, 2⟩)
        (by simp only [Piece.R, Piece.addr, Len.val, g30]) (by decide) (by decide) (show 2 < 2048 by decide)
        (Proof.Sha3.RISCV64.Pieces.cov_right (e_cov hp hi.wr (by decide))) (e_e0 (by decide) (by decide)).symm
        (by rw [hsp]; exact (hp.bx.sub_left b48).sub_right (e_sub (by decide)))
    · exact pieceOk_of (R := ctxR s) (by simp only [Piece.R, Piece.addr, Len.val, g25, g26, BitVec.add_zero])
        (by decide) (by decide) (show Reg.s4 ∈ preserved by decide) (cr _ (by simp))
        (hp.cc.sub_right eS) (by rw [hsp]; exact hp.bc.sub_left b48)
    · exact pieceOk_of (R := msgR s) (by simp only [Piece.R, Piece.addr, Len.val, g23, g24, BitVec.add_zero])
        (by decide) (by decide) (show Reg.s2 ∈ preserved by decide) (cr _ (by simp))
        (hp.mc.sub_right eS) (by rw [hsp]; exact hp.bm.sub_left b48)
  exact ⟨ke, hin⟩

theorem signHash_ok {p : Params} {q : Bool} {STK : Nat} {s t : State} (hF : MFacts p) (hp : MSPre p q STK s) (h48 : 1168 ≤ STK)
    (h : MS1 p STK s t) : WP isa (muHash ⟨.s0, 64, .imm 64⟩) t (MS2 p STK s) := by
  have hi := h.inv
  obtain ⟨ke, hin⟩ := signHash_env hF hp h48 hi
  have g22 : t.gpr .s0 = s.gpr .a0 := hi.regs _ (by decide)
  have g23 : t.gpr .s1 = s.gpr .a1 := hi.regs _ (by decide)
  have g24 : t.gpr .s2 = s.gpr .a2 := hi.regs _ (by decide)
  have g25 : t.gpr .s3 = s.gpr .a3 := hi.regs _ (by decide)
  have g26 : t.gpr .s4 = s.gpr .a4 := hi.regs _ (by decide)
  have g30 := s_e hi
  have hsk := (sk128 hF q).1
  have hsk0 := hF.sk
  have b48 := below48 hp h48
  have hsp : t.sp = s.sp := hi.sp
  have trS : Region.Sub ⟨s.gpr .a0 + BitVec.ofNat 64 64, 64⟩ (skR p s q) := Offset.sub_base _ (by omega_arith)
  have eS := e_sub0 (p := p) (x := s.gpr .a7) (n := 840) (by decide)
  unfold muHash
  refine WP.mono (hash_ok (N := 840) (n := 64) (o := oMU) (out := eAt p (s.gpr .a7) + BitVec.ofNat 64 oMU) (by decide) (by decide) (by decide) (by decide) g30
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
    have kt : bytesAt t.mem (s.gpr .a0 + BitVec.ofNat 64 64) 64 = skTr (skB p s) := by
      rw [s_keep hi (R := ⟨s.gpr .a0 + BitVec.ofNat 64 64, 64⟩) (show (64 : Nat) < 2 ^ 64 by decide) (hp.kg.sub_left trS)
        (hp.kc.sub_left trS) ((hp.bk.symm.sub_left trS).symm), skTr, Proof.MlKem.bytesAt_slice _ _ (by omega_arith)]
    have kc : bytesAt t.mem (s.gpr .a3) (s.gpr .a4).toNat = ctxB s :=
      s_keep hi (R := ctxR s) (BitVec.isLt _) hp.cg hp.cc hp.bc
    have km : bytesAt t.mem (s.gpr .a1) (s.gpr .a2).toNat = msgB s :=
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
abbrev signArgs : List Instr := [mov .a0 .s0, .addi .a1 .s8 oMU, mov .a2 .s5, mov .a3 .s6, mov .a4 .s7]

/-- After the arguments of the call: `μ`, and the arguments in `a0`–`a4`. -/
structure SA (p : Params) (STK : Nat) (s u : State) : Prop where
  ms : MS2 p STK s u
  a0 : u.gpr .a0 = s.gpr .a0
  a1 : u.gpr .a1 = eAt p (s.gpr .a7) + BitVec.ofNat 64 oMU
  a2 : u.gpr .a2 = s.gpr .a5
  a3 : u.gpr .a3 = s.gpr .a6
  a4 : u.gpr .a4 = s.gpr .a7

theorem signArgs_ok {p : Params} {STK : Nat} {s t : State} (h : MS2 p STK s t) :
    WP isa (.block signArgs) t (SA p STK s) := by
  have hi := h.inv
  have g22 : t.gpr .s0 = s.gpr .a0 := hi.regs _ (by decide)
  have g27 : t.gpr .s5 = s.gpr .a5 := hi.regs _ (by decide)
  have g28 : t.gpr .s6 = s.gpr .a6 := hi.regs _ (by decide)
  have g29 : t.gpr .s7 = s.gpr .a7 := hi.regs _ (by decide)
  have g30 := s_e hi
  unfold signArgs mov
  refine Ed25519.RISCV64.Whole.args5_ok (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) fun u hu a3 a4 a5 a6 a7 =>
    ⟨⟨hi.step signRegs_pres hu.rd hu.wr hu.sp hu.pres (by rw [hu.mem]; exact Frame.refl _ _)
      (fun _ h => absurd h List.not_mem_nil) (fun _ h => absurd h List.not_mem_nil), by rw [hu.mem]; exact h.mu⟩,
      ?_, ?_, ?_, ?_, ?_⟩
  · rw [a3, g22, BitVec.add_zero]
  · rw [a4, g30]
  · rw [a5, g27, BitVec.add_zero]
  · rw [a6, g28, BitVec.add_zero]
  · rw [a7, g29, BitVec.add_zero]

/-- What the signing function on `μ` reads and writes. -/
abbrev sRd (p : Params) (q : Bool) (s : State) : List Region :=
  [skR p s q, ⟨eAt p (s.gpr .a7) + BitVec.ofNat 64 oMU, 64⟩, rndR s]
abbrev sWr (p : Params) (s : State) : List Region := [sigR p s, ⟨s.gpr .a7, scratchWords p * 8⟩]

/-- The call's precondition, and its regions. -/
theorem signCall_pre {p : Params} {q : Bool} {STK stk : Nat} {s u : State} (hF : MFacts p) (hp : MSPre p q STK s)
    (hstk : stk ≤ STK) (h : SA p STK s u) :
    (PreparedKey.signEK p q stk).pre (u.callEntry.withRegions (sRd p q s) (sWr p s)) ∧
      RISCV64.Covers (sRd p q s ++ sWr p s) (u.rd ++ u.wr) ∧ RISCV64.Covers (sWr p s) u.wr := by
  have iu := h.ms.inv
  have hstkS : STK ≤ s.sp.toNat := hp.stk
  have hE := hF.e
  have fx := hp.fx
  rw [msw] at fx
  have usp : u.sp = s.sp := iu.sp
  have urd : u.rd = s.rd := iu.rd
  have uwr : u.wr = s.wr := iu.wr
  have bs : Region.Sub (below s.sp stk) (below s.sp STK) := below_sub (by omega_arith) (by omega_arith)
  have muS : Region.Sub ⟨eAt p (s.gpr .a7) + BitVec.ofNat 64 oMU, 64⟩ (scrR p s) := e_sub (by decide)
  have muW : Region.Disjoint ⟨s.gpr .a7, scratchWords p * 8⟩ ⟨eAt p (s.gpr .a7) + BitVec.ofNat 64 oMU, 64⟩ :=
    e_w hF (by decide)
  have muF : (eAt p (s.gpr .a7) + BitVec.ofNat 64 oMU).toNat + 64 ≤ 2 ^ 64 := e_fit hp.fx (by decide) (by decide)
  refine ⟨?_, ?_, ?_⟩
  · refine sign_pre ((ce_gpr _ _ _ (by decide)).trans h.a0) ((ce_gpr _ _ _ (by decide)).trans h.a1)
      ((ce_gpr _ _ _ (by decide)).trans h.a2) ((ce_gpr _ _ _ (by decide)).trans h.a3)
      ((ce_gpr _ _ _ (by decide)).trans h.a4) rfl rfl (by simp only [State.withRegions_sp, State.callEntry_sp, usp]; omega_arith)
      (by simp only [State.withRegions_sp, State.callEntry_sp, usp]; exact hp.al) hp.alx
      hp.kg (hp.kc.sub_right w_sub) (hp.gc.symm.sub_left muS) muW.symm hp.rg (hp.rc.sub_right w_sub)
      (hp.gc.sub_right w_sub) ?_ ?_ ?_ ?_ ?_ hp.fk muF hp.fr hp.fg (by have : scratchWords p * 8 ≤ oE p := (by simp only [oE]; omega_arith); omega_arith) ?_
    case' refine_6 =>
      intro hq
      have hk := hp.kp hq
      subst hq
      have hl : preparedSecretKeyBytes p < 2 ^ 64 := by have := hF.psk; omega_arith
      exact PreparedKey.preparedSecret_of_bytes (s_keep iu (R := skR p s true) hl hp.kg hp.kc hp.bk) hk
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
    · exact ⟨skR p s q, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR p s, by simp, oE p + oMU, e_add _ _ _, e_len p (d := oMU) (n := 64) (by decide)⟩
    · exact ⟨rndR s, by simp, 0, by simp, by simp⟩
    · exact ⟨sigR p s, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR p s, by simp, 0, by simp, by simp only [messageScratchWords]; omega_arith⟩
  · rw [uwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨sigR p s, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR p s, by simp, 0, by simp, by simp only [messageScratchWords]; omega_arith⟩

theorem signCall_ok {p : Params} {q : Bool} {STK S : Nat} {s t : State} (hF : MFacts p) (hp : MSPre p q STK s)
    {f : Prog isa} (hf : Callee f (fun stk => PreparedKey.signEK p q stk) S) (hS : S ≤ STK) {n : String}
    (h : MS2 p STK s t) :
    WP isa (.seq (.block signArgs) (.call n f)) t fun t' => SInv p STK s t' ∧
      Outcome (fun b => signMu p b (skB p s) (messageRep (skTr (skB p s)) (fmtB s)) (rndB s))
        ((t'.gpr .a0).setWidth 32) (bytesAt t'.mem (s.gpr .a6) p.sigLen) := by
  obtain ⟨stk, hstk, hver⟩ := hf.verified
  have hstkS : STK ≤ s.sp.toNat := hp.stk
  refine WP.seq (WP.mono (signArgs_ok h) fun u hu => ?_)
  have iu := hu.ms.inv
  have usp : u.sp = s.sp := iu.sp
  obtain ⟨hpre, hc, hw⟩ := signCall_pre hF hp (Nat.le_trans hstk hS) hu
  have hd : sdepth f < 2 ^ 64 := by have := hf.stack; omega_arith
  refine WP.callAny hver.1 hpre hc hw (fun s' rd' wr' sp' fr' cs' post' => ?_) hd
  refine ⟨iu.step signRegs_pres rd' wr' sp' cs' fr' (fun r hr => ?_) fun r hr => ?_, ?_⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨sigR p s, by simp, fun _ h => h⟩
    · exact ⟨scrR p s, by simp, w_sub⟩
    · exact ⟨below s.sp STK, by simp, by rw [usp]; exact below_sub (by have := hf.stack; omega_arith) (by omega_arith)⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact slot_g hp
    · exact slot_w hF
    · rw [usp]
      exact (hp.bx.symm.sub_left slot_sub).sub_right (below_sub (by have := hf.stack; omega_arith) (by omega_arith))
  · have hq := sign_post post'
    simp only [State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem,
      State.callEntry_gpr _ (show Reg.a0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a1 ∉ linkRegs by decide),
      State.callEntry_gpr _ (show Reg.a2 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a3 ∉ linkRegs by decide),
      hu.a0, hu.a1, hu.a2, hu.a3] at hq
    have ks := skE_sub hF q s
    rw [s_keep iu (R := ⟨s.gpr .a0, p.skLen⟩) (by have := hF.skl; show p.skLen < 2 ^ 64; omega_arith)
      (hp.kg.sub_left ks) (hp.kc.sub_left ks) (hp.bk.sub_right ks), hu.ms.mu,
      s_keep iu (R := rndR s) (show (32 : Nat) < 2 ^ 64 by decide) hp.rg hp.rc hp.br] at hq
    exact hq

/-! ## `sign_message` -/

/-- The result: 2 for a context string longer than 255 bytes, else the
signature of the formatted message. -/
theorem signMessage_wp {p : Params} {q : Bool} {STK S : Nat} (hF : MFacts p) (h48 : 1168 ≤ STK) {f : Prog isa}
    (hf : Callee f (fun stk => PreparedKey.signEK p q stk) S) (hS : S ≤ STK) {n : String} {s : State}
    (hp : MSPre p q STK s) :
    WP isa (signMessage n f p) s fun t => abiPreserved s t ∧ (signMessageEK p q STK).post s t := by
  unfold signMessage top
  refine WP.seq (Steps.WP.cons (exec_shift_d (by decide)) (WP.block_nil ?_))
  have hu := Steps.Upd.write s .t1 (s.gpr .a4 >>> 8)
  refine wp_ite (decide ((s.gpr .a4).toNat < 256)) (by rw [eval_zero, hu.gpr]; exact congrArg some (shr8_zero _)) (fun hcl => ?_)
    fun hcl => ?_
  · have hcl' : (s.gpr .a4).toNat < 256 := of_decide_eq_true hcl
    refine WP.seq (WP.mono (signSetup_ok hF hp hu.other hu.rd hu.wr hu.sp rfl hu.mem) fun t₁ h₁ => ?_)
    refine WP.seq (WP.mono (signHash_ok hF hp h48 h₁) fun t₂ h₂ => ?_)
    refine WP.seq (WP.mono (signCall_ok hF hp hf hS h₂) fun t₃ ⟨h₃, r₃⟩ => ?_)
    have hrl : ∀ q ∈ restoreList oSV signRegs, q.2 + 8 ≤ 1024 := by decide
    refine restore_ok h₃ (e_al hp.alx hp.fx) (s_e h₃) (by decide) (by decide) (by decide) (by decide)
      (fun q hq => by
        have := hrl q hq
        have := e_len p (d := q.2) (n := 8) (by omega_arith)
        have := hF.e
        rw [h₃.rd, h₃.wr, hp.rd, hp.wr, e_add]
        exact ⟨scrR p s, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
      fun t₄ g₄ sp₄ lr₄ m₄ o₄ => ⟨⟨g₄, sp₄, lr₄⟩, ?_⟩
    · cases q
      all_goals simp only [signMessageEK, Bool.false_eq_true, ↓reduceIte]
      all_goals first
        | sig_post [signMessageContract, signMessageSig, RISCV64.abi, RISCV64.argRegs]
        | sig_post [preparedSignMessageContract, preparedSignMessageSig, RISCV64.abi, RISCV64.argRegs]
      all_goals rw [Proof.MlDsa.Message.formatMessage_some (by rw [Proof.MlKem.bytesAt_length]; exact hcl'), o₄ .a0 (by decide)
        (by decide), m₄]
      all_goals simp only [signInternal, Proof.MlKem.bytesAt_length]
      all_goals exact r₃
  · have hcl' : ¬ (s.gpr .a4).toNat < 256 := of_decide_eq_false hcl
    refine Steps.WP.cons (exec_li (d := .a0) (imm := 2) (by decide)) (WP.block_nil ⟨⟨fun r hr => ?_, rfl, rfl⟩, ?_⟩)
    · rw [(Steps.Upd.write _ _ _).other _ (Proof.Sha3.RISCV64.Pieces.pres_ne hr).2.1, hu.other _ (by revert hr; cases r <;> decide)]
    · cases q
      all_goals simp only [signMessageEK, Bool.false_eq_true, ↓reduceIte]
      all_goals first
        | sig_post [signMessageContract, signMessageSig, RISCV64.abi, RISCV64.argRegs]
        | sig_post [preparedSignMessageContract, preparedSignMessageSig, RISCV64.abi, RISCV64.argRegs]
      all_goals rw [Proof.MlDsa.Message.formatMessage_none (by rw [Proof.MlKem.bytesAt_length]; omega_arith)]
      all_goals rfl

end VG.Proof.MlDsa.RISCV64.Message
