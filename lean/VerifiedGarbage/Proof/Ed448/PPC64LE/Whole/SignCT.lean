module

public import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.SignNonce
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.Lit
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.SignNonce
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
meta import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.Common
meta import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.Common
meta import VerifiedGarbage.Proof.Ed448.Ref
public import VerifiedGarbage.Proof.Ed448.Ref
public import VerifiedGarbage.Proof.X448.PPC64LE.Invert
import VerifiedGarbage.Proof.Ed448.Signing
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ed448.PPC64LE.VChecks
import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.Hash
import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.Prune
public import VerifiedGarbage.Spec.Ed448
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Common
import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.Calls
meta import VerifiedGarbage.Proof.Ed448.Signing
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Ed448.PPC64LE.VChecks
meta import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.Hash
meta import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.Prune
meta import VerifiedGarbage.Proof.X448.PPC64LE.Invert
meta import VerifiedGarbage.Spec.Ed448
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Common
meta import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.Calls

/-! ### `Ed448.PPC64LE.Whole.SignCached`, which this module and modules that import it used -/

section

/-! ### `Ed448.PPC64LE.Whole.SignChallenge`, which this module and modules that import it used -/

section

/-!
# `vg_ed448_sign_cached` on PPC64LE: the challenge and `S`

From `S3`: `H(dom4(0, C) ‖ R ‖ A ‖ M)` into `16(F)`, reduced modulo `L`
into `320(F)` (`k`), and `S = (r + k s) mod L` into the second half of `out`
(`challenge_ok`, `S4`).
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE.Whole VG.Proof.X25519.PPC64LE
open VG.Impl.Ed25519.PPC64LE.Whole (mov)
open VG.Proof.Ed25519.PPC64LE.Whole (Inv slotArea ArgsKeep args5_ok)
open VG.Spec.Ed448 (bytesAt)

/-- `k`. -/
abbrev kB (s : State) : List Byte :=
  Spec.Ed448.scalarReduce (Spec.Ed448.hash (ctxB s) (RB s ++ pkB s ++ msgB s))

/-- After `S`. -/
structure S4 (s t : State) : Prop where
  inv : SInv s t
  R : bytesAt t.mem (s.gpr .r3) 57 = RB s
  S : ∃ σ, Spec.Ed448.decodeLE σ = Spec.Ed448.prune (hS s) ∧
    bytesAt t.mem (s.gpr .r3 + BitVec.ofNat 64 57) 57 = Spec.Ed448.scalarMulAdd (rB s) (kB s) σ

theorem challenge_ok {s t : State} (hp : SignPre s) (h : S3 s t) : WP isa signChallenge t (S4 s) := by
  obtain ⟨cP, cB⟩ := ctxPiece hp h.inv
  obtain ⟨mP, mB⟩ := msgPiece hp h.inv
  obtain ⟨hP, hB⟩ := fPiece0 hp h.inv
  obtain g20 : t.gpr .r20 = s.gpr .r3 := h.inv.regs _ (by decide)
  obtain g22 : t.gpr .r24 = s.gpr .r5 := h.inv.regs _ (by decide)
  obtain g29 : t.gpr .r22 = s.gpr .r10 := h.inv.regs _ (by decide)
  obtain g30 : t.gpr .r21 = sF s := h.inv.regs _ (by decide)
  obtain hO57 : Region.Sub ⟨s.gpr .r3, 57⟩ (oR s) := Region.sub_prefix (by decide)
  obtain oP : PieceOk (s.gpr .r10) t ⟨.r20, 0, .imm 57⟩ :=
    pieceOk_of (R := ⟨s.gpr .r3, 57⟩) (by simp only [Piece.R, Piece.addr, Len.val, g20, BitVec.add_zero])
      (by decide) (by decide) (show 57 < 2 ^ 15 by decide) (cov_right (cov_in0 (fO hp h.inv) (by decide)))
      (hp.oC.sub_left hO57) (by rw [h.inv.sp]; exact hp.bO.sub_right hO57)
  obtain oB : Piece.bytes t.mem t.gpr ⟨.r20, 0, .imm 57⟩ = RB s := by
    simp only [Piece.bytes, Piece.addr, Len.val, g20, BitVec.add_zero]; exact h.R
  obtain pP : PieceOk (s.gpr .r10) t ⟨.r24, 0, .imm 57⟩ :=
    pieceOk_of (R := pkR s) (by simp only [Piece.R, Piece.addr, Len.val, g22, BitVec.add_zero])
      (by decide) (by decide) (show 57 < 2 ^ 15 by decide)
      (by rw [h.inv.rd, hp.rd]; exact cov_rd fun a n ⟨r, hr, hc⟩ => ⟨r, by rw [List.mem_singleton.mp hr]; simp, hc⟩)
      hp.cP.symm (by rw [h.inv.sp]; exact hp.bP)
  obtain pB : Piece.bytes t.mem t.gpr ⟨.r24, 0, .imm 57⟩ = pkB s := by
    have := sign_keep hp h.inv (R := pkR s) (.inr (.inl rfl))
    simp only [Piece.bytes, Piece.addr, Len.val, g22, BitVec.add_zero]; exact this
  unfold signChallenge
  simp only [dom4Pieces, List.cons_append, List.nil_append]
  refine WP.seq (WP.mono (hash_ok (sc := .r22) (f := .r21) (o := 16) (out := sF s + BitVec.ofNat 64 16)
    (by decide) (by decide) (by decide) g29 (by rw [g30]) (kenv hp h.inv) (by simp) (fun p hp' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl | rfl | rfl
      · exact hP
      · exact cP
      · exact oP
      · exact pP
      · exact mP) (cov_in (fF hp h.inv) (by decide))
    (fsc hp (by decide)) (by rw [h.inv.sp]; exact fbelow hp (by decide))) fun t₂ ⟨k₂, d₂⟩ => ?_)
  obtain h₂ := h.inv.hash hp (by decide) k₂
  obtain hh : bytesAt t₂.mem (sF s + BitVec.ofNat 64 16) 114 =
      Spec.Ed448.hash (ctxB s) (RB s ++ pkB s ++ msgB s) := by
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, hB, cB, oB, pB,
      mB, h.hdr, bytesAt_sha3] at d₂
    rw [d₂, show (s.gpr .r7).toNat = (ctxB s).length by simp [bytesAt], ← List.append_assoc, List.append_assoc (RB s)]
    exact dom4_hash _ _
  -- `k`.
  refine reduceF_ok hp h₂ (o := 320) (by decide) (by decide) fun t₃ h₃ f₃ r₃ => ?_
  rw [hh] at r₃
  -- `S`.
  obtain g20' : t₃.gpr .r20 = s.gpr .r3 := h₃.regs _ (by decide)
  obtain g29' : t₃.gpr .r22 = s.gpr .r10 := h₃.regs _ (by decide)
  obtain g30' : t₃.gpr .r21 = sF s := h₃.regs _ (by decide)
  unfold mov
  refine WP.seq (args5_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) fun u hu a3 a4 a5 a6 a7 => ?_)
  rw [g20'] at a3
  rw [g30'] at a4 a5 a6
  rw [g29', BitVec.add_zero] at a7
  obtain hOs : Region.Sub ⟨s.gpr .r3 + BitVec.ofNat 64 57, 57⟩ (oR s) := osub (by decide)
  obtain hW : PPC64LE.Covers [⟨s.gpr .r3 + BitVec.ofNat 64 57, 57⟩, scR s] u.wr := by
    rw [hu.wr]
    intro a n ⟨r, hr, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact cov_in (fO hp h₃) (by decide) a n ⟨_, List.mem_singleton_self _, hc⟩
    · exact ⟨_, fC hp h₃, hc⟩
  obtain hR : PPC64LE.Covers [⟨sF s + BitVec.ofNat 64 256, 57⟩, ⟨sF s + BitVec.ofNat 64 320, 57⟩,
      ⟨sF s + BitVec.ofNat 64 136, 57⟩] (u.rd ++ u.wr) := by
    rw [hu.rd, hu.wr]
    intro a n ⟨r, hr, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact cov_right (cov_in (fF hp h₃) (by decide)) a n ⟨_, List.mem_singleton_self _, hc⟩
    · exact cov_right (cov_in (fF hp h₃) (by decide)) a n ⟨_, List.mem_singleton_self _, hc⟩
    · exact cov_right (cov_in (fF hp h₃) (by decide)) a n ⟨_, List.mem_singleton_self _, hc⟩
  refine mulAdd_call a3 a4 a5 a6 a7 (hp.oC.sub_left hOs) (fsc hp (by decide)) (fsc hp (by decide))
    (fsc hp (by decide)) (cov_app hR (cov_right hW)) hW fun t₄ rd₄ wr₄ sp₄ f₄ cs₄ b₄ => ?_
  rw [hu.mem] at f₄ b₄
  obtain h₄ : SInv s t₄ := h₃.step signRegs_pres (rd₄.trans hu.rd) (wr₄.trans hu.wr) (sp₄.trans hu.sp)
    (fun r hr => (cs₄ r hr).trans (hu.pres r hr)) f₄ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨oR s, by simp, hOs⟩
      · exact ⟨scR s, by simp, fun _ h => h⟩) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact oslot hp (by decide)
      · exact cslot hp
  -- What the steps keep.
  obtain kr : ∀ {d n : Nat}, d + n ≤ 464 → (d + n ≤ 320 ∨ 377 ≤ d) →
      bytesAt t₃.mem (sF s + BitVec.ofNat 64 d) n = bytesAt t₂.mem (sF s + BitVec.ofNat 64 d) n :=
    fun hdn hd => bytes_keep f₃ (by omega_using [hdn]) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (by omega_using [hd]) (by omega_using [hdn]) (by omega_using [])
      · exact fsc hp hdn
  obtain e256 : bytesAt t₃.mem (sF s + BitVec.ofNat 64 256) 57 = rB s := by
    rw [kr (by decide) (by decide), keep_hash hp h.inv (o := 16) (d := 256) (n := 57) (by decide) (by decide)
      (by decide) k₂, h.r]
  obtain e136 : Spec.Ed448.decodeLE (bytesAt t₃.mem (sF s + BitVec.ofNat 64 136) 57) = Spec.Ed448.prune (hS s) := by
    rw [kr (by decide) (by decide), keep_hash hp h.inv (o := 16) (d := 136) (n := 57) (by decide) (by decide)
      (by decide) k₂, h.sc]
  obtain hO0 : ∀ {m m' : Mem} {W : List Region}, Frame W m m' →
      (∀ r ∈ W, Region.Disjoint ⟨s.gpr .r3, 57⟩ r) → bytesAt m' (s.gpr .r3) 57 = bytesAt m (s.gpr .r3) 57 :=
    fun hf hd => bytes_keep hf (by decide) hd
  refine ⟨h₄, ?_, ⟨_, e136, by rw [b₄, e256, r₃]⟩⟩
  rw [hO0 f₄ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simpa using Offset.disjoint (s.gpr .r3) (d := 0) (n := 57) (e := 57) (k := 57) (.inl (by decide))
          (by decide) (by decide)
      · exact hp.oC.sub_left hO57,
    hO0 f₃ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hp.oF.sub_left hO57).sub_right (fsub (by decide))
      · exact hp.oC.sub_left hO57,
    hO0 k₂.frame fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (hp.oF.sub_left hO57).sub_right (fsub (by decide))
      · exact hp.oC.sub_left hO57
      · rw [h.inv.sp]; exact (hp.bO.sub_right hO57).symm, h.R]

end VG.Proof.Ed448.PPC64LE.Whole

end

end

/-!
# `vg_ed448_sign_cached` on PPC64LE, with its frame as an argument

The setup (`frame_ok`, `signSetup_ok`), the steps (`expand_ok`, `nonce_ok`,
`challenge_ok`), then `F` from 16 to 384 zeroed (`wipe_ok`) and the
registers restored: `out` holds `R ‖ S`, the signature (`signCached_wp`, by
`Proof.Ed448.sign_pipeline`).
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE.Whole VG.Proof.X25519.PPC64LE
open VG.Proof.Ed25519.PPC64LE.Whole (Inv slotArea restore_ok restoreList)
open VG.Spec.Ed448 (bytesAt)

/-- After the stores of `wipe` from the first `k`. -/
structure WInv (t₀ : State) (F : Addr) (o n : Nat) (k : Nat) (u : State) : Prop where
  gpr : u.gpr = t₀.gpr
  rd : u.rd = t₀.rd
  wr : u.wr = t₀.wr
  sp : u.sp = t₀.sp
  frame : Frame [⟨F + BitVec.ofNat 64 o, 8 * n⟩] t₀.mem u.mem

/-- `wipe f o n`: the `n` doublewords from `o(F)` zeroed, only `r8` written. -/
theorem wipe_ok {t : State} {f : Reg} {F : Addr} {o n : Nat} (hf0 : f ≠ .r0) (hf8 : f ≠ .r8) (hF : t.gpr f = F)
    (hon : o + 8 * n < 2 ^ 15) (ho : o % 4 = 0)
    (hw : ∀ k < n, InRegions t.wr (F + BitVec.ofNat 64 (o + 8 * k)) 8) {rest : List Instr} {Q : State → Prop}
    (K : ∀ u, Frame [⟨F + BitVec.ofNat 64 o, 8 * n⟩] t.mem u.mem → u.rd = t.rd → u.wr = t.wr → u.sp = t.sp →
      (∀ r, r ≠ .r8 → u.gpr r = t.gpr r) → WP isa (.block rest) u Q) :
    WP isa (.block (wipe f o n ++ rest)) t Q := by
  unfold wipe
  rw [List.cons_append]
  refine wp_li (by decide) fun u₁ h₁ => ?_
  rw [List.map_eq_flatMap, WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (WInv u₁ F o n) (fun k u hk h => ?_) n (Nat.le_refl _) u₁
    ⟨rfl, rfl, rfl, rfl, Frame.refl _ _⟩) fun u h => ?_
  · have hf : u.gpr f = F := by rw [h.gpr, h₁.other _ hf8, hF]
    refine wp_stdd (a := F + BitVec.ofNat 64 (o + 8 * k)) hf0 ⟨by omega_using [hon, hk], by omega_using [ho]⟩ (by rw [hf])
      (by rw [h.wr, h₁.wr]; exact hw k hk) fun u' h' => WP.block_nil ⟨by rw [h'.gpr, h.gpr], by rw [h'.rd, h.rd],
        by rw [h'.wr, h.wr], by rw [h'.sp, h.sp], ?_⟩
    rw [h'.mem]
    refine h.frame.writeW List.mem_cons_self _ ?_
    rw [← Offset.add_add]
    exact Offset.contains_base _ (by omega_using [hk]) (by omega_using [hon, hk])
  · refine K u (by rw [← h₁.mem]; exact h.frame) (by rw [h.rd, h₁.rd]) (by rw [h.wr, h₁.wr])
      (by rw [h.sp, h₁.sp]) fun r hr => by rw [h.gpr, h₁.other r hr]

theorem bytesAt_split114 (m : Mem) (p : Addr) :
    bytesAt m p 114 = bytesAt m p 57 ++ bytesAt m (p + BitVec.ofNat 64 57) 57 := by
  rw [← bytesAt_take57, ← bytesAt_drop57, List.take_append_drop]

theorem signCached_wp (hl : Proof.Ed448.BaseLadder2Ok) {s : State} (hp : SignPre s) :
    WP isa signCached s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.lr = s.lr ∧
      bytesAt t.mem (s.gpr .r3) 114 = Spec.Ed448.sign (seedB s) (ctxB s) (msgB s) := by
  unfold signCached
  refine WP.seq (frame_ok hp fun u hu hlr => WP.block_nil ?_)
  refine WP.seq (WP.mono (signSetup_ok hp hu hlr) fun t₁ h₁ => ?_)
  refine WP.seq (WP.mono (expand_ok hp h₁) fun t₂ h₂ => ?_)
  refine WP.seq (WP.mono (nonce_ok hl hp h₂) fun t₃ h₃ => ?_)
  refine WP.seq (WP.mono (challenge_ok hp h₃) fun t₄ h₄ => ?_)
  obtain ⟨σ, hσ, hS⟩ := h₄.S
  have g30 : t₄.gpr .r21 = sF s := h₄.inv.regs _ (by decide)
  have hFw : (fR s) ∈ t₄.wr := fF hp h₄.inv
  refine wipe_ok (f := .r21) (o := 16) (n := 46) (by decide) (by decide) g30 (by decide) (by decide)
    (fun k hk => in_base hFw (by omega_using [hk]) (by omega_using [hk])) fun u uf urd uwr usp ug => ?_
  have h₅ : SInv s u := h₄.inv.step signRegs_pres urd uwr usp (fun r hr => ug r fun e => by revert hr; rw [e]; decide)
    uf (fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨fR s, by simp, fsub (by decide)⟩)
    fun r hr => by rw [List.mem_singleton.mp hr]; exact fslot (by decide)
  have hrl : ∀ p ∈ restoreList 384 signRegs, p.2 + 8 ≤ 464 := by decide
  refine restore_ok h₅ (by decide) (h₅.regs _ (by decide)) (by decide) (by decide) (by decide) (by decide)
    (fun p (hp' : p ∈ restoreList 384 signRegs) => show InRegions (u.rd ++ u.wr) (sF s + BitVec.ofNat 64 p.2) 8 by
      rw [h₅.rd, h₅.wr, hp.rd, hp.wr]
      exact ⟨fR s, by simp, Offset.contains_base _ (hrl p hp') (by have := hrl p hp'; omega_using [this])⟩)
    fun t₆ g₆ sp₆ lr₆ m₆ _ => ⟨g₆, sp₆, lr₆, ?_⟩
  have kO : bytesAt t₆.mem (s.gpr .r3) 114 = bytesAt t₄.mem (s.gpr .r3) 114 := by
    rw [m₆]
    exact bytes_keep uf (by decide) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hp.oF.sub_right (fsub (by decide))
  rw [kO, bytesAt_split114, h₄.R, hS]
  exact Proof.Ed448.sign_pipeline _ _ _ _ σ hp.pk hσ

end VG.Proof.Ed448.PPC64LE.Whole

end

end

/-!
# `vg_ed448_sign_cached` on PPC64LE in constant time

Two runs from states that satisfy `SignPre` and agree on the arguments (the
registers, the stack pointer and the stack argument, `SPub`) leak the same
trace (`sign_ct`). Each piece of the body is related from the invariants the
correctness proof gives each run (`S1`–`S4`): the hashes by `hash_ct`, the
code between them by the taint analysis (`ct_prog`) from the registers the
invariants give the same values in both runs, the callees' bodies included
(the Ed448 functions save and restore other registers than these, or, as
`scalar_base` does with `r15`–`r31`, are called last in a piece, whose
successor starts again from its run's invariant).
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE.Whole
open VG.Proof.MlKem.PPC64LE.Sample (taint_block relct_wp)
open VG.Proof.Ed25519.PPC64LE.Whole (Inv)
open VG.Proof.X25519.PPC64LE (Upd)

/-! ## Combinators -/

/-- Code the taint analysis checks from the registers `rs`, on which the runs agree. -/
theorem ct_prog {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hsp : ∀ a b, P a b → a.sp = b.sp) (hP : ∀ a b, P a b → ∀ r ∈ rs, a.gpr r = b.gpr r)
    {hc : VG.Taint.Hint VG.PPC64LE.taint.T} (h : (VG.PPC64LE.taint.check (Taint.ofRegs rs) c hc).isSome = true) :
    RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := VG.PPC64LE.taint) (Taint.ofRegs rs)
    (fun a b hab => ⟨hsp a b hab, fun r hr => hP a b hab r (Taint.mem_ofRegs.mp hr)⟩) h

/-- A hash, then code the taint analysis checks from registers `rs` that the hash keeps (callee-saved), on which
the runs agree. -/
theorem hash_then {sc f : Reg} {o : Nat} {ps : List Piece} {P : State → State → Prop} {c : Prog isa}
    {hint : VG.Taint.Hint VG.PPC64LE.taint.T}
    (hz : (VG.PPC64LE.taint.check (Taint.ofRegs [sc]) (.block (Impl.MlKem.PPC64LE.zeroState sc)) hint).isSome =
      true)
    (hP : ∀ a b, P a b → HashOk sc f o ps a ∧ HashOk sc f o ps b ∧ a.sp = b.sp ∧
      ∀ r ∈ hashRegs sc f ps, a.gpr r = b.gpr r)
    (rs : List Reg) (hrs : ∀ a b, P a b → ∀ r ∈ rs, r ∈ preserved ∧ a.gpr r = b.gpr r)
    {hint₂ : VG.Taint.Hint VG.PPC64LE.taint.T} (hc : (VG.PPC64LE.taint.check (Taint.ofRegs rs) c hint₂).isSome = true) :
    RelCT isa P (.seq (hash sc ps f o) c) fun _ _ => True := by
  refine RelCT.mono (P := fun a b => ∃ x : State × State, a = x.1 ∧ b = x.2 ∧ P x.1 x.2)
    (RelCT.exists_ fun ⟨t₁, t₂⟩ => ?_) (fun a b h => ⟨(a, b), rfl, rfl, h⟩) (fun _ _ h => h)
  by_cases hH : P t₁ t₂
  swap
  · exact RelCT.of_false fun a b h => hH h.2.2
  obtain ⟨h₁, h₂, hsp, -⟩ := hP _ _ hH
  refine RelCT.mono (P := fun a b => a = t₁ ∧ b = t₂) ?_ (fun a b h => ⟨h.1, h.2.1⟩) (fun _ _ h => h)
  have hP' : ∀ a b, (a = t₁ ∧ b = t₂) → HashOk sc f o ps a ∧ HashOk sc f o ps b ∧ a.sp = b.sp ∧
      ∀ r ∈ hashRegs sc f ps, a.gpr r = b.gpr r := fun a b h => by
    obtain ⟨rfl, rfl⟩ := h; exact hP _ _ hH
  have hw : ∀ t, HashOk sc f o ps t → WP isa (hash sc ps f o) t (Rg t) := fun t ht =>
    WP.mono (hash_ok ht.psc ht.pf ht.po rfl rfl ht.env ht.ne ht.ins ht.w ht.dsc ht.dsp)
      fun _ ⟨k, _⟩ => ⟨k.rd, k.wr, k.sp, k.cs⟩
  refine RelCT.seq (R := fun a b => Rg t₁ a ∧ Rg t₂ b)
    (RelCT.mono (relct_wp (hash_ct hz hP') fun a b hab => ⟨by rw [hab.1]; exact hw _ h₁, by rw [hab.2]; exact hw _ h₂⟩)
      (fun _ _ h => h) (fun _ _ h => h)) ?_
  exact ct_prog rs (fun a b hab => hab.1.sp.trans (hsp.trans hab.2.sp.symm)) (fun a b hab r hr => by
    obtain ⟨hp, he⟩ := hrs _ _ hH r hr
    rw [hab.1.cs r hp, hab.2.cs r hp, he]) hc

/-- `hash_then`, with the code after the hash related by any proof from the states the hash leaves. -/
theorem hash_then_rel {sc f : Reg} {o : Nat} {ps : List Piece} {P : State → State → Prop} {c : Prog isa}
    {hint : VG.Taint.Hint VG.PPC64LE.taint.T}
    (hz : (VG.PPC64LE.taint.check (Taint.ofRegs [sc]) (.block (Impl.MlKem.PPC64LE.zeroState sc)) hint).isSome =
      true)
    (hP : ∀ a b, P a b → HashOk sc f o ps a ∧ HashOk sc f o ps b ∧ a.sp = b.sp ∧
      ∀ r ∈ hashRegs sc f ps, a.gpr r = b.gpr r)
    (hc : ∀ t₁ t₂, P t₁ t₂ → RelCT isa (fun a b => Rg t₁ a ∧ Rg t₂ b) c fun _ _ => True) :
    RelCT isa P (.seq (hash sc ps f o) c) fun _ _ => True := by
  refine RelCT.mono (P := fun a b => ∃ x : State × State, a = x.1 ∧ b = x.2 ∧ P x.1 x.2)
    (RelCT.exists_ fun ⟨t₁, t₂⟩ => ?_) (fun a b h => ⟨(a, b), rfl, rfl, h⟩) (fun _ _ h => h)
  by_cases hH : P t₁ t₂
  swap
  · exact RelCT.of_false fun a b h => hH h.2.2
  obtain ⟨h₁, h₂, -, -⟩ := hP _ _ hH
  refine RelCT.mono (P := fun a b => a = t₁ ∧ b = t₂) ?_ (fun a b h => ⟨h.1, h.2.1⟩) (fun _ _ h => h)
  have hP' : ∀ a b, (a = t₁ ∧ b = t₂) → HashOk sc f o ps a ∧ HashOk sc f o ps b ∧ a.sp = b.sp ∧
      ∀ r ∈ hashRegs sc f ps, a.gpr r = b.gpr r := fun a b h => by
    obtain ⟨rfl, rfl⟩ := h; exact hP _ _ hH
  have hw : ∀ t, HashOk sc f o ps t → WP isa (hash sc ps f o) t (Rg t) := fun t ht =>
    WP.mono (hash_ok ht.psc ht.pf ht.po rfl rfl ht.env ht.ne ht.ins ht.w ht.dsc ht.dsp)
      fun _ ⟨k, _⟩ => ⟨k.rd, k.wr, k.sp, k.cs⟩
  exact RelCT.seq (R := fun a b => Rg t₁ a ∧ Rg t₂ b)
    (RelCT.mono (relct_wp (hash_ct hz hP') fun a b hab => ⟨by rw [hab.1]; exact hw _ h₁, by rw [hab.2]; exact hw _ h₂⟩)
      (fun _ _ h => h) (fun _ _ h => h)) (hc _ _ hH)

/-! ## The runs' agreement -/

/-- What two runs agree on: the arguments. -/
def SPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .r10 = s₂.gpr .r10 ∧ s₁.sp = s₂.sp ∧ stackArg s₁ 0 = stackArg s₂ 0

theorem signV_eq {s₁ s₂ : State} (hp : SPub s₁ s₂) : ∀ r ∈ signRegs, signV s₁ r = signV s₂ r := by
  obtain ⟨p3, p4, p5, p6, p7, p8, p9, p10, -, pf⟩ := hp
  intro r hr
  simp only [signRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [p3, p10, p4, p5, p6, p7, p8, p9, pf]

theorem inv_regs {s₁ s₂ a b : State} (hp : SPub s₁ s₂) (ha : SInv s₁ a) (hb : SInv s₂ b) :
    ∀ r ∈ signRegs, a.gpr r = b.gpr r := fun r hr =>
  (ha.regs r hr).trans ((signV_eq hp r hr).trans (hb.regs r hr).symm)

theorem inv_sp {s₁ s₂ a b : State} (hp : SPub s₁ s₂) (ha : SInv s₁ a) (hb : SInv s₂ b) : a.sp = b.sp :=
  ha.sp.trans (hp.2.2.2.2.2.2.2.2.1.trans hb.sp.symm)

theorem sub_regs {rs : List Reg} (h : ∀ r ∈ rs, r ∈ signRegs) {g₁ g₂ : Reg → BitVec 64}
    (he : ∀ r ∈ signRegs, g₁ r = g₂ r) : ∀ r ∈ rs, g₁ r = g₂ r := fun r hr => he r (h r hr)

/-! ## The hashes' preconditions -/

section
variable {s : State} (hp : SignPre s)
include hp

theorem hashOk_of {t : State} (h : SInv s t) {o : Nat} (ho : o + 114 ≤ 464) (ho' : o < 2 ^ 15) {ps : List Piece}
    (hne : ps ≠ []) (hps : ∀ p ∈ ps, PieceOk (s.gpr .r10) t p) : HashOk .r22 .r21 o ps t := by
  have g29 : t.gpr .r22 = s.gpr .r10 := h.regs _ (by decide)
  have g30 : t.gpr .r21 = sF s := h.regs _ (by decide)
  exact ⟨by decide, by decide, ho', hne, by rw [g29]; exact kenv hp h, by rw [g29]; exact hps,
    by rw [g30]; exact cov_in (fF hp h) ho, by rw [g30, g29]; exact fsc hp ho,
    by rw [g30, h.sp]; exact fbelow hp ho⟩

theorem S1.hashOk {t : State} (h : S1 s t) : HashOk .r22 .r21 136 [⟨.r23, 0, .imm 57⟩] t := by
  have g21 : t.gpr .r23 = s.gpr .r4 := h.inv.regs _ (by decide)
  refine hashOk_of hp h.inv (by decide) (by decide) (by simp) fun p hp' => ?_
  rw [List.mem_singleton.mp hp']
  exact pieceOk_of (R := sdR s) (by simp only [Piece.R, Piece.addr, Len.val, g21, BitVec.add_zero]) (by decide)
    (by decide) (show 57 < 2 ^ 15 by decide)
    (by rw [h.inv.rd, hp.rd]; exact cov_rd fun a n ⟨r, hr, hc⟩ => ⟨r, by rw [List.mem_singleton.mp hr]; simp, hc⟩)
    hp.cS.symm (by rw [h.inv.sp]; exact hp.bS)

theorem S2.hashOk {t : State} (h : S2 s t) :
    HashOk .r22 .r21 16 (dom4Pieces .r21 .r25 .r28 ++ [⟨.r21, 193, .imm 57⟩, ⟨.r29, 0, .reg .r30⟩]) t := by
  refine hashOk_of hp h.inv (by decide) (by decide) (by simp [dom4Pieces]) fun p hp' => ?_
  simp only [dom4Pieces, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hp'
  rcases hp' with rfl | rfl | rfl | rfl
  · exact (fPiece0 hp h.inv).1
  · exact (ctxPiece hp h.inv).1
  · exact (fPiece hp h.inv (d := 193) (n := 57) (by decide) (by decide) (by decide)).1
  · exact (msgPiece hp h.inv).1

theorem S3.hashOk {t : State} (h : S3 s t) :
    HashOk .r22 .r21 16 (dom4Pieces .r21 .r25 .r28 ++ [⟨.r20, 0, .imm 57⟩, ⟨.r24, 0, .imm 57⟩, ⟨.r29, 0, .reg .r30⟩])
      t := by
  have g20 : t.gpr .r20 = s.gpr .r3 := h.inv.regs _ (by decide)
  have g22 : t.gpr .r24 = s.gpr .r5 := h.inv.regs _ (by decide)
  have hO57 : Region.Sub ⟨s.gpr .r3, 57⟩ (oR s) := Region.sub_prefix (by decide)
  refine hashOk_of hp h.inv (by decide) (by decide) (by simp [dom4Pieces]) fun p hp' => ?_
  simp only [dom4Pieces, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hp'
  rcases hp' with rfl | rfl | rfl | rfl | rfl
  · exact (fPiece0 hp h.inv).1
  · exact (ctxPiece hp h.inv).1
  · exact pieceOk_of (R := ⟨s.gpr .r3, 57⟩) (by simp only [Piece.R, Piece.addr, Len.val, g20, BitVec.add_zero])
      (by decide) (by decide) (show 57 < 2 ^ 15 by decide) (cov_right (cov_in0 (fO hp h.inv) (by decide)))
      (hp.oC.sub_left hO57) (by rw [h.inv.sp]; exact hp.bO.sub_right hO57)
  · exact pieceOk_of (R := pkR s) (by simp only [Piece.R, Piece.addr, Len.val, g22, BitVec.add_zero])
      (by decide) (by decide) (show 57 < 2 ^ 15 by decide)
      (by rw [h.inv.rd, hp.rd]; exact cov_rd fun a n ⟨r, hr, hc⟩ => ⟨r, by rw [List.mem_singleton.mp hr]; simp, hc⟩)
      hp.cP.symm (by rw [h.inv.sp]; exact hp.bP)
  · exact (msgPiece hp h.inv).1

end

/-! ## The pieces -/

section
variable {s₁ s₂ : State} (hp₁ : SignPre s₁) (hp₂ : SignPre s₂) (hpub : SPub s₁ s₂)
include hp₁ hp₂ hpub

theorem expand_ct : RelCT isa (fun a b => S1 s₁ a ∧ S1 s₂ b) signExpand fun _ _ => True :=
  hash_then (by taint_decide) (fun a b h => ⟨h.1.hashOk hp₁, h.2.hashOk hp₂, inv_sp hpub h.1.inv h.2.inv,
    sub_regs (by decide) (inv_regs hpub h.1.inv h.2.inv)⟩) [.r21] (fun a b h r hr =>
      ⟨signRegs_pres r (by revert r; decide), inv_regs hpub h.1.inv h.2.inv r (by revert r; decide)⟩)
    (by taint_decide)

theorem nonce_ct : RelCT isa (fun a b => S2 s₁ a ∧ S2 s₂ b) signNonce fun _ _ => True :=
  hash_then (by taint_decide) (fun a b h => ⟨h.1.hashOk hp₁, h.2.hashOk hp₂, inv_sp hpub h.1.inv h.2.inv,
    sub_regs (by decide) (inv_regs hpub h.1.inv h.2.inv)⟩) [.r20, .r22, .r21] (fun a b h r hr =>
      ⟨signRegs_pres r (by revert r; decide), inv_regs hpub h.1.inv h.2.inv r (by revert r; decide)⟩)
    (by taint_decide)

theorem challenge_ct : RelCT isa (fun a b => S3 s₁ a ∧ S3 s₂ b) signChallenge fun _ _ => True :=
  hash_then (by taint_decide) (fun a b h => ⟨h.1.hashOk hp₁, h.2.hashOk hp₂, inv_sp hpub h.1.inv h.2.inv,
    sub_regs (by decide) (inv_regs hpub h.1.inv h.2.inv)⟩) [.r20, .r22, .r21] (fun a b h r hr =>
      ⟨signRegs_pres r (by revert r; decide), inv_regs hpub h.1.inv h.2.inv r (by revert r; decide)⟩)
    (by taint_decide)

end

/-! ## The whole body -/

theorem signCached_ct (hl : Proof.Ed448.BaseLadder2Ok) :
    ConstantTime isa SignPre SPub signCached := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  refine RelCT.mono (P := fun a b => ∃ x : State × State, a = x.1 ∧ b = x.2 ∧ SignPre x.1 ∧ SignPre x.2 ∧
    SPub x.1 x.2) (RelCT.exists_ fun ⟨s₁, s₂⟩ => ?_) (fun a b h => ⟨(a, b), rfl, rfl, h⟩) (fun _ _ h => h)
  by_cases hH : SignPre s₁ ∧ SignPre s₂ ∧ SPub s₁ s₂
  swap
  · exact RelCT.of_false fun a b h => hH h.2.2
  obtain ⟨hp₁, hp₂, hpub⟩ := hH
  refine RelCT.mono (P := fun a b => a = s₁ ∧ b = s₂) ?_ (fun a b h => ⟨h.1, h.2.1⟩) (fun _ _ h => h)
  have pub := hpub
  obtain ⟨p3, p4, p5, p6, p7, p8, p9, p10, psp, pf⟩ := pub
  unfold signCached
  -- `F`.
  let F₁ := fun u => Upd s₁ u .r12 (sF s₁) ∧ u.lr = s₁.lr
  let F₂ := fun u => Upd s₂ u .r12 (sF s₂) ∧ u.lr = s₂.lr
  refine RelCT.seq (R := fun a b => F₁ a ∧ F₂ b)
    (RelCT.mono (relct_wp (taint_block [] (fun a b hab => by rw [hab.1, hab.2, psp])
      (fun _ _ _ r hr => absurd hr List.not_mem_nil) (by taint_decide)) fun a b hab =>
      ⟨by rw [hab.1]; exact frame_ok hp₁ fun u hu hl => WP.block_nil ⟨hu, hl⟩,
       by rw [hab.2]; exact frame_ok hp₂ fun u hu hl => WP.block_nil ⟨hu, hl⟩⟩) (fun _ _ h => h) fun _ _ h => h) ?_
  -- The setup.
  refine RelCT.seq (R := fun a b => S1 s₁ a ∧ S1 s₂ b)
    (relct_wp (ct_prog [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r12] (fun a b hab => by
      rw [hab.1.1.sp, hab.2.1.sp, psp]) (fun a b hab r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact (hab.1.1.gpr.trans pf).trans hab.2.1.gpr.symm
        | rw [hab.1.1.other _ (by decide), hab.2.1.other _ (by decide)]; assumption) (by taint_decide))
      fun a b hab => ⟨signSetup_ok hp₁ hab.1.1 hab.1.2, signSetup_ok hp₂ hab.2.1 hab.2.2⟩) ?_
  -- The steps.
  refine RelCT.seq (R := fun a b => S2 s₁ a ∧ S2 s₂ b)
    (relct_wp (expand_ct hp₁ hp₂ hpub) fun a b hab => ⟨expand_ok hp₁ hab.1, expand_ok hp₂ hab.2⟩) ?_
  refine RelCT.seq (R := fun a b => S3 s₁ a ∧ S3 s₂ b)
    (relct_wp (nonce_ct hp₁ hp₂ hpub) fun a b hab => ⟨nonce_ok hl hp₁ hab.1, nonce_ok hl hp₂ hab.2⟩) ?_
  refine RelCT.seq (R := fun a b => S4 s₁ a ∧ S4 s₂ b)
    (relct_wp (challenge_ct hp₁ hp₂ hpub) fun a b hab => ⟨challenge_ok hp₁ hab.1, challenge_ok hp₂ hab.2⟩) ?_
  -- The wipe and the restores.
  exact ct_prog [.r21] (fun a b hab => inv_sp hpub hab.1.inv hab.2.inv)
    (fun a b hab => sub_regs (by decide) (inv_regs hpub hab.1.inv hab.2.inv)) (by taint_decide)

end VG.Proof.Ed448.PPC64LE.Whole
