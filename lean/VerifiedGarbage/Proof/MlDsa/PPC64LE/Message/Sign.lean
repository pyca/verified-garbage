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

theorem mfacts {p : Params} (h : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) : MFacts p := by
  rcases h with rfl | rfl | rfl <;> exact ⟨by decide, by decide, by decide⟩

theorem msw (p : Params) : messageScratchWords p * 8 = oE p + 1024 := by
  simp only [messageScratchWords, oE]; omega

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
  · rw [RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne _ _ (Ne.symm hsr), RegUpd.gpr_write_self]
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
      all_goals first | exact h₁.gpr.symm | exact ((h₁.other _ (by decide)).trans (hu _ (by decide))).symm)
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

end VG.Proof.MlDsa.PPC64LE.Message
