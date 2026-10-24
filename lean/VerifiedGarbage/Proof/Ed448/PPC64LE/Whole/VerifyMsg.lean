module

import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.SignSteps
import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.SignNonce
public import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.HashCT
import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Common
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.Calls
import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.Common
import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.Prune
public import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.SignSetup
public import VerifiedGarbage.Proof.Ed448.Ref
public import VerifiedGarbage.Proof.X448.PPC64LE.Ladder

/-!
# `vg_ed448_verify` on PPC64LE, with its frame as an argument

The contract by register (`VerPre`): `pk` in `r3`, the context in `r4`
(`ctxlen` in `r5`), the message in `r6` (`len` in `r7`), the signature in
`r8`, `scratch` in `r9` and the frame `F` (272 bytes) in `r10`. If
`ctxlen ≥ 256` it returns 0, which is `Spec.Ed448.verify`'s result. Else
the registers are saved at `200(F)`, the arguments moved (`pk`, the signature,
`scratch` and `F` to `r20`–`r23`, which no function called saves and
restores), the header of `dom4` written at `F` (`verSetup_ok`, `V1`),
`H(dom4(0, C) ‖ R ‖ A ‖ M)` hashed into `16(F)` and reduced modulo `L` into
`136(F)` (`k`), and the arguments of `vg_ed448_verify_equation` set
(`verHash_ok`, `VArgs`); its result is the result (`verifyMessage_wp`).
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE.Whole VG.Proof.X25519.PPC64LE
open VG.Impl.Ed25519.PPC64LE.Whole (mov saveRegs restoreRegs slots)
open VG.Proof.Ed25519.PPC64LE.Whole (Inv slotArea args3_ok restore_ok restoreList)
open VG.Spec.Ed448 (bytesAt)

/-! ## The regions -/

section
variable (s : State)

abbrev vpkR : Region := ⟨s.gpr .r3, 57⟩
abbrev vcxR : Region := ⟨s.gpr .r4, (s.gpr .r5).toNat⟩
abbrev vmsR : Region := ⟨s.gpr .r6, (s.gpr .r7).toNat⟩
abbrev vsgR : Region := ⟨s.gpr .r8, 114⟩
abbrev vscR : Region := ⟨s.gpr .r9, 8192⟩
abbrev vfR : Region := ⟨s.gpr .r10, 272⟩

/-- The inputs. -/
abbrev vpkB : List Byte := bytesAt s.mem (s.gpr .r3) 57
abbrev vctxB : List Byte := bytesAt s.mem (s.gpr .r4) (s.gpr .r5).toNat
abbrev vmsgB : List Byte := bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat
abbrev vsigB : List Byte := bytesAt s.mem (s.gpr .r8) 114

/-- `k`. -/
abbrev vkB : List Byte :=
  Spec.Ed448.scalarReduce (Spec.Ed448.hash (vctxB s) (bytesAt s.mem (s.gpr .r8) 57 ++ vpkB s ++ vmsgB s))

end

/-- The precondition, by register. -/
structure VerPre (s : State) : Prop where
  rd : s.rd = [vpkR s, vcxR s, vmsR s, vsgR s]
  wr : s.wr = [vscR s, vfR s]
  cP : (vscR s).Disjoint (vpkR s)
  cX : (vscR s).Disjoint (vcxR s)
  cM : (vscR s).Disjoint (vmsR s)
  cS : (vscR s).Disjoint (vsgR s)
  cF : (vscR s).Disjoint (vfR s)
  fP : (vfR s).Disjoint (vpkR s)
  fX : (vfR s).Disjoint (vcxR s)
  fM : (vfR s).Disjoint (vmsR s)
  fS : (vfR s).Disjoint (vsgR s)
  sp : 48 ≤ s.sp.toNat
  bP : (below s.sp 48).Disjoint (vpkR s)
  bX : (below s.sp 48).Disjoint (vcxR s)
  bM : (below s.sp 48).Disjoint (vmsR s)
  bS : (below s.sp 48).Disjoint (vsgR s)
  bC : (below s.sp 48).Disjoint (vscR s)
  bF : (below s.sp 48).Disjoint (vfR s)

/-- What the body may write. -/
abbrev verW (s : State) : List Region := [vscR s, vfR s, below s.sp 48]

/-- The values in the registers. -/
def verV (s : State) : Reg → BitVec 64
  | .r20 => s.gpr .r3 | .r21 => s.gpr .r8 | .r22 => s.gpr .r9 | .r23 => s.gpr .r10 | .r24 => s.gpr .r4
  | .r25 => s.gpr .r5 | .r28 => s.gpr .r6 | .r29 => s.gpr .r7 | _ => 0

abbrev VInv (s : State) : State → Prop := Inv s (s.gpr .r10) 200 verifyRegs (verV s) (verW s)

theorem verifyRegs_pres : ∀ r ∈ verifyRegs, r ∈ preserved := by decide

theorem vfsub {s : State} {d n : Nat} (h : d + n ≤ 272) : Region.Sub ⟨s.gpr .r10 + BitVec.ofNat 64 d, n⟩ (vfR s) :=
  Offset.sub_base _ h

theorem vfslot {s : State} {d n : Nat} (h : d + n ≤ 200) :
    (slotArea (s.gpr .r10) 200 verifyRegs).Disjoint ⟨s.gpr .r10 + BitVec.ofNat 64 d, n⟩ :=
  Offset.disjoint _ (.inr h) (by decide) (by omega)

section
variable {s : State} (hp : VerPre s)
include hp

/-- The inputs, while the body runs: none of them is in `verW`. -/
theorem ver_keep {t : State} (h : VInv s t) {R : Region}
    (hR : R = vpkR s ∨ R = vcxR s ∨ R = vmsR s ∨ R = vsgR s) :
    bytesAt t.mem R.base R.len = bytesAt s.mem R.base R.len := by
  refine bytes_keep h.frame (by
      rcases hR with rfl | rfl | rfl | rfl
      all_goals first
        | (show (57 : Nat) < 2 ^ 64; decide)
        | (show (114 : Nat) < 2 ^ 64; decide)
        | exact BitVec.isLt _)
    fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hR with rfl | rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl
  all_goals first
    | exact hp.cP.symm | exact hp.cX.symm | exact hp.cM.symm | exact hp.cS.symm
    | exact hp.fP.symm | exact hp.fX.symm | exact hp.fM.symm | exact hp.fS.symm
    | exact hp.bP.symm | exact hp.bX.symm | exact hp.bM.symm | exact hp.bS.symm

theorem vF {t : State} (h : VInv s t) : (vfR s) ∈ t.wr := by rw [h.wr, hp.wr]; simp
theorem vC {t : State} (h : VInv s t) : (vscR s) ∈ t.wr := by rw [h.wr, hp.wr]; simp

theorem vfsc {d n : Nat} (h : d + n ≤ 272) : Region.Disjoint ⟨s.gpr .r10 + BitVec.ofNat 64 d, n⟩ (vscR s) :=
  hp.cF.symm.sub_left (vfsub h)

theorem vfbelow {d n : Nat} (h : d + n ≤ 272) : (below s.sp 48).Disjoint ⟨s.gpr .r10 + BitVec.ofNat 64 d, n⟩ :=
  hp.bF.sub_right (vfsub h)

theorem vcslot : (slotArea (s.gpr .r10) 200 verifyRegs).Disjoint (vscR s) :=
  hp.cF.symm.sub_left (Offset.sub_base _ (by decide))

theorem vbslot : (slotArea (s.gpr .r10) 200 verifyRegs).Disjoint (below s.sp 48) :=
  hp.bF.symm.sub_left (Offset.sub_base _ (by decide))

theorem vkenv {t : State} (h : VInv s t) : KEnv (s.gpr .r9) t :=
  ⟨vC hp h, by rw [h.sp]; exact hp.sp, by rw [h.sp]; exact hp.bC⟩

end

/-! ## The setup -/

/-- After the setup: the invariant, and the header of `dom4` at `F`. -/
structure V1 (s t : State) : Prop where
  inv : VInv s t
  hdr : bytesAt t.mem (s.gpr .r10) 10 = hdrBytes (s.gpr .r5).toNat

/-- The setup, from `u`, which differs from `s` only in `r11`. -/
theorem verSetup_ok {s u : State} (hp : VerPre s) (hu : ∀ r, r ≠ .r11 → u.gpr r = s.gpr r) (hrd : u.rd = s.rd)
    (hwr : u.wr = s.wr) (hsp : u.sp = s.sp) (hlr : u.lr = s.lr) (hm : u.mem = s.mem) :
    WP isa (.block (saveRegs .r10 200 verifyRegs ++
      [mov .r20 .r3, mov .r21 .r8, mov .r22 .r9, mov .r24 .r4, mov .r25 .r5, mov .r28 .r6, mov .r29 .r7,
        mov .r23 .r10] ++ hdr .r23 .r25)) u (V1 s) := by
  have hFw : (vfR s) ∈ u.wr := by rw [hwr, hp.wr]; simp
  have g10 : u.gpr .r10 = s.gpr .r10 := hu _ (by decide)
  refine (show WP isa (.block (saveRegs .r10 200 verifyRegs ++
      ([(.r20, .r3), (.r21, .r8), (.r22, .r9), (.r24, .r4), (.r25, .r5), (.r28, .r6), (.r29, .r7),
        (.r23, .r10)] : List (Reg × Reg)).map (fun p => mov p.1 p.2) ++ hdr .r23 .r25)) u (V1 s) from ?_)
  refine setup_ok (v := verV s) (W := verW s) (by decide) (by decide) (by decide)
    (fun p hp' => by rw [g10]; exact in_base hFw (by revert p; decide) (by revert p; decide))
    ⟨vfR s, by simp, by rw [g10]; exact Offset.sub_base _ (by decide)⟩ rfl (by decide) (by decide) (fun p hp' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact (hu _ (by decide)).symm) fun t₁ h₁ => ?_
  rw [g10] at h₁
  have h₁ : VInv s t₁ := h₁.rebase verifyRegs_pres hrd hwr hsp hlr
    (fun r hr => hu r fun e => by revert hr; rw [e]; decide) hm
  have g23 : t₁.gpr .r23 = s.gpr .r10 := h₁.regs _ (by decide)
  have g25 : t₁.gpr .r25 = s.gpr .r5 := h₁.regs _ (by decide)
  have hFw₁ : (vfR s) ∈ t₁.wr := by rw [h₁.wr, hp.wr]; simp
  refine hdr_ok (F := s.gpr .r10) (cl := (s.gpr .r5).toNat) (by decide) (by decide) g23
    (by rw [g25, ofNat_toNat]) (fun j hj => in_base hFw₁ (by omega) (by omega))
    (by simpa using in_base (d := 0) (n := 8) hFw₁ (by decide) (by decide)) (by decide)
    fun t ht hrd hwr hsp hg => WP.block_nil ⟨?_, ?_⟩
  · refine h₁.step verifyRegs_pres hrd hwr hsp (fun r hr => hg r fun e => by revert hr; rw [e]; decide)
      (ht ▸ hdrMem_frame _ _ _) (fun r hr => ?_) fun r hr => ?_
    · rw [List.mem_singleton.mp hr]; exact ⟨vfR s, by simp, Region.sub_prefix (by decide)⟩
    · rw [List.mem_singleton.mp hr]; exact Offset.disjoint_base _ (by decide) (by decide)
  · rw [ht, hdrMem_bytes]

/-! ## The challenge -/

/-- The pieces the challenge hashes. -/
abbrev verPieces : List Piece :=
  dom4Pieces .r23 .r24 .r25 ++ [⟨.r21, 0, .imm 57⟩, ⟨.r20, 0, .imm 57⟩, ⟨.r28, 0, .reg .r29⟩]

theorem V1.hashOk {s t : State} (hp : VerPre s) (h : V1 s t) : HashOk .r22 .r23 16 verPieces t ∧
    (verPieces.map (Piece.bytes t.mem t.gpr)).flatten =
      hdrBytes (s.gpr .r5).toNat ++ vctxB s ++ (bytesAt s.mem (s.gpr .r8) 57 ++ vpkB s ++ vmsgB s) := by
  have g20 : t.gpr .r20 = s.gpr .r3 := h.inv.regs _ (by decide)
  have g21 : t.gpr .r21 = s.gpr .r8 := h.inv.regs _ (by decide)
  have g22 : t.gpr .r22 = s.gpr .r9 := h.inv.regs _ (by decide)
  have g23 : t.gpr .r23 = s.gpr .r10 := h.inv.regs _ (by decide)
  have g24 : t.gpr .r24 = s.gpr .r4 := h.inv.regs _ (by decide)
  have g25 : t.gpr .r25 = s.gpr .r5 := h.inv.regs _ (by decide)
  have g28 : t.gpr .r28 = s.gpr .r6 := h.inv.regs _ (by decide)
  have g29 : t.gpr .r29 = s.gpr .r7 := h.inv.regs _ (by decide)
  have hS57 : Region.Sub ⟨s.gpr .r8, 57⟩ (vsgR s) := Region.sub_prefix (by decide)
  have cr : ∀ R ∈ [vpkR s, vcxR s, vmsR s, vsgR s], PPC64LE.Covers [R] (t.rd ++ t.wr) := fun R hR => by
    rw [h.inv.rd, hp.rd]; exact cov_rd fun a n ⟨r, hr, hc⟩ => ⟨r, by rw [List.mem_singleton.mp hr]; exact hR, hc⟩
  refine ⟨⟨by decide, by decide, by decide, by simp [verPieces, dom4Pieces], by rw [g22]; exact vkenv hp h.inv, ?_,
    by rw [g23]; exact cov_in (vF hp h.inv) (by decide), by rw [g23, g22]; exact vfsc hp (by decide),
    by rw [g23, h.inv.sp]; exact vfbelow hp (by decide)⟩, ?_⟩
  · intro p hp'
    rw [g22]
    simp only [verPieces, dom4Pieces, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl | rfl
    · exact pieceOk_of (R := ⟨s.gpr .r10, 10⟩) (by simp only [Piece.R, Piece.addr, Len.val, g23, BitVec.add_zero])
        (by decide) (by decide) (show 10 < 2 ^ 15 by decide) (cov_right (cov_in0 (vF hp h.inv) (by decide)))
        (by simpa using vfsc hp (d := 0) (n := 10) (by decide))
        (by rw [h.inv.sp]; simpa using vfbelow hp (d := 0) (n := 10) (by decide))
    · exact pieceOk_of (R := vcxR s) (by simp only [Piece.R, Piece.addr, Len.val, g24, g25, BitVec.add_zero])
        (by decide) (by decide) (show Reg.r25 ∈ preserved by decide) (cr _ (by simp)) hp.cX.symm
        (by rw [h.inv.sp]; exact hp.bX)
    · exact pieceOk_of (R := ⟨s.gpr .r8, 57⟩) (by simp only [Piece.R, Piece.addr, Len.val, g21, BitVec.add_zero])
        (by decide) (by decide) (show 57 < 2 ^ 15 by decide)
        (cov_rd (cov_in0 (P := s.gpr .r8) (k := 114) (by rw [h.inv.rd, hp.rd]; simp) (by decide)))
        (hp.cS.symm.sub_left hS57) (by rw [h.inv.sp]; exact hp.bS.sub_right hS57)
    · exact pieceOk_of (R := vpkR s) (by simp only [Piece.R, Piece.addr, Len.val, g20, BitVec.add_zero])
        (by decide) (by decide) (show 57 < 2 ^ 15 by decide) (cr _ (by simp)) hp.cP.symm
        (by rw [h.inv.sp]; exact hp.bP)
    · exact pieceOk_of (R := vmsR s) (by simp only [Piece.R, Piece.addr, Len.val, g28, g29, BitVec.add_zero])
        (by decide) (by decide) (show Reg.r29 ∈ preserved by decide) (cr _ (by simp)) hp.cM.symm
        (by rw [h.inv.sp]; exact hp.bM)
  · have kx := ver_keep hp h.inv (R := vcxR s) (.inr (.inl rfl))
    have km := ver_keep hp h.inv (R := vmsR s) (.inr (.inr (.inl rfl)))
    have kp := ver_keep hp h.inv (R := vpkR s) (.inl rfl)
    have ks : bytesAt t.mem (s.gpr .r8) 57 = bytesAt s.mem (s.gpr .r8) 57 := by
      rw [← bytesAt_take57, ← bytesAt_take57 s.mem]
      exact congrArg (List.take 57) (ver_keep hp h.inv (R := vsgR s) (.inr (.inr (.inr rfl))))
    have h0 := h.hdr
    simp only [verPieces, dom4Pieces, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
      List.flatten_cons, List.flatten_nil, List.append_nil, Piece.bytes, Piece.addr, Len.val, g20, g21, g23, g24, g25,
      g28, g29, BitVec.add_zero, bytesAt_sha3]
    rw [h0, kx, km, kp, ks]
    simp only [List.append_assoc]

/-- The arguments of `vg_ed448_verify_equation` set. -/
structure VArgs (s t : State) : Prop where
  inv : VInv s t
  r3 : t.gpr .r3 = s.gpr .r3
  r4 : t.gpr .r4 = s.gpr .r8
  r5 : t.gpr .r5 = s.gpr .r10 + BitVec.ofNat 64 136
  r6 : t.gpr .r6 = s.gpr .r9
  ch : bytesAt t.mem (s.gpr .r10 + BitVec.ofNat 64 136) 57 = vkB s

/-- The challenge into `136(F)`, and the arguments of `vg_ed448_verify_equation`. -/
theorem verHash_ok {s t : State} (hp : VerPre s) (h : V1 s t) :
    WP isa (.seq (hash .r22 verPieces .r23 16) (.seq (.block [.addi .r3 .r23 136, .addi .r4 .r23 16, mov .r5 .r22])
      (.seq (.call "vg_ed448_scalar_reduce" Impl.Ed448.PPC64LE.scalarReduce)
        (.block [mov .r3 .r20, mov .r4 .r21, .addi .r5 .r23 136, mov .r6 .r22])))) t (VArgs s) := by
  obtain ⟨ho, hb⟩ := h.hashOk hp
  have g22 : t.gpr .r22 = s.gpr .r9 := h.inv.regs _ (by decide)
  have g23 : t.gpr .r23 = s.gpr .r10 := h.inv.regs _ (by decide)
  refine WP.seq (WP.mono (hash_ok ho.psc ho.pf ho.po rfl rfl ho.env ho.ne ho.ins ho.w ho.dsc ho.dsp)
    fun t₂ ⟨k₂, d₂⟩ => ?_)
  rw [g22, g23] at k₂
  rw [g23] at d₂
  rw [hb, show (s.gpr .r5).toNat = (vctxB s).length by simp [bytesAt], dom4_hash, bytesAt_sha3] at d₂
  have h₂ : VInv s t₂ := Inv.kept h.inv verifyRegs_pres k₂ (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨vfR s, by simp, vfsub (by decide)⟩
      · exact ⟨vscR s, by simp, fun _ h => h⟩
      · exact ⟨below s.sp 48, by simp, by rw [h.inv.sp]; exact fun _ h => h⟩) fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact vfslot (by decide)
      · exact vcslot hp
      · rw [h.inv.sp]; exact vbslot hp
  -- `k`.
  have g22' : t₂.gpr .r22 = s.gpr .r9 := h₂.regs _ (by decide)
  have g23' : t₂.gpr .r23 = s.gpr .r10 := h₂.regs _ (by decide)
  unfold mov
  refine WP.seq (args3_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) fun u hu a3 a4 a5 => ?_)
  rw [g23'] at a3 a4
  rw [g22', BitVec.add_zero] at a5
  have hW : PPC64LE.Covers [⟨s.gpr .r10 + BitVec.ofNat 64 136, 57⟩, vscR s] u.wr := by
    rw [hu.wr]
    intro a n ⟨r, hr, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact cov_in (vF hp h₂) (by decide) a n ⟨_, List.mem_singleton_self _, hc⟩
    · exact ⟨_, vC hp h₂, hc⟩
  refine WP.seq (reduce_call a3 a4 a5 (Offset.disjoint _ (.inr (by decide)) (by decide) (by decide))
    (vfsc hp (by decide)) (vfsc hp (by decide))
    (cov_app (cov_right (by rw [hu.wr]; exact cov_in (vF hp h₂) (by decide))) (cov_right hW)) hW
    fun t₃ rd₃ wr₃ sp₃ f₃ cs₃ r₃ => ?_)
  rw [hu.mem, d₂] at r₃
  rw [hu.mem] at f₃
  have h₃ : VInv s t₃ := h₂.step verifyRegs_pres (rd₃.trans hu.rd) (wr₃.trans hu.wr) (sp₃.trans hu.sp)
    (fun r hr => (cs₃ r hr).trans (hu.pres r hr)) f₃ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨vfR s, by simp, vfsub (by decide)⟩
      · exact ⟨vscR s, by simp, fun _ h => h⟩) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact vfslot (by decide)
      · exact vcslot hp
  -- The arguments.
  have g20 : t₃.gpr .r20 = s.gpr .r3 := h₃.regs _ (by decide)
  have g21 : t₃.gpr .r21 = s.gpr .r8 := h₃.regs _ (by decide)
  have g22'' : t₃.gpr .r22 = s.gpr .r9 := h₃.regs _ (by decide)
  have g23'' : t₃.gpr .r23 = s.gpr .r10 := h₃.regs _ (by decide)
  refine wp_addi (by decide) (by decide) fun v₁ e₁ => wp_addi (by decide) (by decide) fun v₂ e₂ =>
    wp_addi (by decide) (by decide) fun v₃ e₃ => wp_addi (by decide) (by decide) fun v₄ e₄ => WP.block_nil ?_
  refine ⟨h₃.step verifyRegs_pres (by rw [e₄.rd, e₃.rd, e₂.rd, e₁.rd]) (by rw [e₄.wr, e₃.wr, e₂.wr, e₁.wr])
    (by rw [e₄.sp, e₃.sp, e₂.sp, e₁.sp]) (fun r hr => ?_) (by rw [e₄.mem, e₃.mem, e₂.mem, e₁.mem]; exact Frame.refl _ _)
    (fun _ h => absurd h List.not_mem_nil) (fun _ h => absurd h List.not_mem_nil), ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨-, p3, p4, p5, p6, -, -⟩ := pres_ne hr
    rw [e₄.other _ p6, e₃.other _ p5, e₂.other _ p4, e₁.other _ p3]
  · rw [e₄.other _ (by decide), e₃.other _ (by decide), e₂.other _ (by decide), e₁.gpr, BitVec.add_zero, g20]
  · rw [e₄.other _ (by decide), e₃.other _ (by decide), e₂.gpr, BitVec.add_zero, e₁.other _ (by decide), g21]
  · rw [e₄.other _ (by decide), e₃.gpr, e₂.other _ (by decide), e₁.other _ (by decide), g23'']
  · rw [e₄.gpr, BitVec.add_zero, e₃.other _ (by decide), e₂.other _ (by decide), e₁.other _ (by decide), g22'']
  · rw [e₄.mem, e₃.mem, e₂.mem, e₁.mem, r₃]

/-- The call of `vg_ed448_verify_equation`. -/
theorem verCall_ok (hR : Proof.Ed448.RecoverOk) (hV : Proof.Ed448.VerifyEq4Ok) {s t : State} (hp : VerPre s)
    (h : VArgs s t) :
    WP isa (.call "vg_ed448_verify_equation" Impl.Ed448.PPC64LE.verifyEquation) t fun t' => VInv s t' ∧
      (t'.gpr .r3).setWidth 32 = if Spec.Ed448.verifyEquation (vpkB s) (vsigB s) (vkB s) then 1 else 0 := by
  have cr : ∀ R ∈ [vpkR s, vcxR s, vmsR s, vsgR s], PPC64LE.Covers [R] (t.rd ++ t.wr) := fun R hR => by
    rw [h.inv.rd, hp.rd]; exact cov_rd fun a n ⟨r, hr, hc⟩ => ⟨r, by rw [List.mem_singleton.mp hr]; exact hR, hc⟩
  have hW : PPC64LE.Covers [vscR s] t.wr := fun a n ⟨r, hr, hc⟩ => by
    rw [List.mem_singleton.mp hr] at hc; exact ⟨_, vC hp h.inv, hc⟩
  have hc : PPC64LE.Covers ([vpkR s, vsgR s, ⟨s.gpr .r10 + BitVec.ofNat 64 136, 57⟩] ++ [vscR s]) (t.rd ++ t.wr) := by
    intro a n ⟨r, hr, hc⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact cr _ (by simp) a n ⟨_, List.mem_singleton_self _, hc⟩
    · exact cr _ (by simp) a n ⟨_, List.mem_singleton_self _, hc⟩
    · exact cov_right (cov_in (vF hp h.inv) (by decide)) a n ⟨_, List.mem_singleton_self _, hc⟩
    · exact cov_right hW a n ⟨_, List.mem_singleton_self _, hc⟩
  refine veq_call hR hV h.r3 h.r4 h.r5 h.r6 hp.cP.symm hp.cS.symm (vfsc hp (by decide)) hc hW
    fun t' rd' wr' sp' f' cs' r' => ⟨h.inv.step verifyRegs_pres rd' wr' sp' cs' f' (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨vscR s, by simp, fun _ h => h⟩) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact vcslot hp, ?_⟩
  rw [r', ver_keep hp h.inv (R := vpkR s) (.inl rfl), ver_keep hp h.inv (R := vsgR s) (.inr (.inr (.inr rfl))),
    h.ch]

theorem wp_ite {c : Cond} {th el : Prog isa} {s : State} {Q : State → Prop} (b : Bool)
    (hc : isa.eval c s = some b) (ht : b = true → WP isa th s Q) (he : b = false → WP isa el s Q) :
    WP isa (.ite c th el) s Q := by
  cases b
  · obtain ⟨t, s', e, q⟩ := he rfl; exact ⟨_, s', Exec.iteF hc e, q⟩
  · obtain ⟨t, s', e, q⟩ := ht rfl; exact ⟨_, s', Exec.iteT hc e, q⟩

/-- The result `vg_ed448_verify` returns. -/
abbrev verResult (s : State) : BitVec 32 :=
  if Spec.Ed448.verify (vpkB s) (vctxB s) (vmsgB s) (vsigB s) then 1 else 0

theorem shr8_zero (x : BitVec 64) : (x >>> 8 == 0) = decide (x.toNat < 256) := by
  have h : (x >>> 8).toNat = x.toNat / 256 := by rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  by_cases hx : x.toNat < 256
  · simp only [hx, decide_true, beq_iff_eq]
    exact BitVec.eq_of_toNat_eq (by rw [h, Nat.div_eq_of_lt hx]; rfl)
  · simp only [hx, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e
    have := congrArg BitVec.toNat e
    rw [h] at this
    exact hx (by simp at this; omega)

theorem verifyMessage_wp (hR : Proof.Ed448.RecoverOk) (hV : Proof.Ed448.VerifyEq4Ok) {s : State} (hp : VerPre s) :
    WP isa verifyMessage s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.lr = s.lr ∧
      (t.gpr .r3).setWidth 32 = verResult s := by
  unfold verifyMessage
  refine WP.seq (WP.cons (exec_lsr_d (by decide)) (WP.block_nil ?_))
  have hu := Upd.write s .r11 (s.gpr .r5 >>> 8)
  refine wp_ite (decide ((s.gpr .r5).toNat < 256)) (by rw [eval_zero, hu.gpr, shr8_zero]) (fun hcl => ?_)
    fun hcl => ?_
  · -- `ctxlen < 256`.
    have hcl' : (s.gpr .r5).toNat < 256 := of_decide_eq_true hcl
    unfold verifyMain verifyHash
    refine WP.seq (WP.seq (WP.mono (verSetup_ok hp hu.other hu.rd hu.wr hu.sp rfl hu.mem) fun t₁ h₁ => ?_))
    refine WP.mono (verHash_ok hp h₁) fun t₂ h₂ => ?_
    refine WP.seq (WP.mono (verCall_ok hR hV hp h₂) fun t₃ ⟨h₃, r₃⟩ => ?_)
    have hrl : ∀ p ∈ restoreList 200 verifyRegs, p.2 + 8 ≤ 272 := by decide
    refine restore_ok h₃ (by decide) (h₃.regs _ (by decide)) (by decide) (by decide) (by decide) (by decide)
      (fun p (hp' : p ∈ restoreList 200 verifyRegs) =>
        show InRegions (t₃.rd ++ t₃.wr) (s.gpr .r10 + BitVec.ofNat 64 p.2) 8 by
        rw [h₃.rd, h₃.wr, hp.rd, hp.wr]
        exact ⟨vfR s, by simp, Offset.contains_base _ (hrl p hp') (by have := hrl p hp'; omega)⟩)
      fun t₄ g₄ sp₄ lr₄ m₄ o₄ => ⟨g₄, sp₄, lr₄, ?_⟩
    rw [o₄ .r3 (by decide) (by decide), r₃]
    have : Spec.Ed448.verify (vpkB s) (vctxB s) (vmsgB s) (vsigB s) =
        Spec.Ed448.verifyEquation (vpkB s) (vsigB s) (vkB s) := by
      simp only [Spec.Ed448.verify, show (vctxB s).length ≤ 255 by simp [bytesAt]; omega, decide_true,
        Bool.true_and, vkB, bytesAt_take57]
    simp only [verResult, this]
  · -- `ctxlen ≥ 256`: 0.
    have hcl' : ¬ (s.gpr .r5).toNat < 256 := of_decide_eq_false hcl
    refine WP.cons (exec_li (d := .r3) (imm := 0) (by decide)) (WP.block_nil ⟨fun r hr => ?_, rfl, rfl, ?_⟩)
    · rw [(Upd.write _ _ _).other _ (pres_ne hr).2.1, hu.other _ (by revert hr; cases r <;> decide)]
    · rw [(Upd.write _ _ _).gpr]
      have : Spec.Ed448.verify (vpkB s) (vctxB s) (vmsgB s) (vsigB s) = false := by
        simp only [Spec.Ed448.verify, Bool.and_eq_false_iff, decide_eq_false_iff_not]
        left; simp [bytesAt]; omega
      simp only [verResult, this]; rfl

end VG.Proof.Ed448.PPC64LE.Whole
