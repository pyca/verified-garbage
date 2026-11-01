module

import VerifiedGarbage.Proof.Ed448.RISCV64.Whole.SignSteps
import VerifiedGarbage.Proof.Ed448.RISCV64.Whole.SignNonce
public import VerifiedGarbage.Proof.Ed448.RISCV64.Whole.HashCT
import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Common
import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Prune
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ed448.RISCV64.Whole.Calls
import VerifiedGarbage.Proof.Ed448.RISCV64.Whole.Common
import VerifiedGarbage.Proof.Ed448.RISCV64.Whole.Prune
public import VerifiedGarbage.Proof.Ed448.RISCV64.Whole.SignSetup
public import VerifiedGarbage.Proof.Ed448.Ref
public import VerifiedGarbage.Proof.X448.RISCV64.Ladder

/-!
# `vg_ed448_verify` on RISC-V, with its frame as an argument

The contract by register (`VerPre`): `pk` in `a0`, the context in `a1`
(`ctxlen` in `a2`), the message in `a3` (`len` in `a4`), the signature in
`a5`, `scratch` in `a6` and the frame `F` (448 bytes) in `a7`. If
`ctxlen ≥ 256` it returns 0, which is `Spec.Ed448.verify`'s result. Else
the registers are saved at `384(F)`, the arguments moved (`scratch`, the
context, its length, the message, its length and `F` to `s1` and
`s7`–`s11`, which no function called saves and restores), the signature
and `pk` copied to `200(F)` and `320(F)`, the header of `dom4` written at
`F` (`verSetup_ok`, `V1`), `H(dom4(0, C) ‖ R ‖ A ‖ M)` hashed into `16(F)`
and reduced modulo `L` into `136(F)` (`k`), and the arguments of
`vg_ed448_verify_equation` set (`verHash_ok`, `VArgs`); its result is the
result (`verifyMessage_wp`).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64.Whole

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64.Whole VG.Proof.X25519.RISCV64
open VG.Impl.Ed25519.RISCV64.Whole (mov saveRegs restoreRegs slots copyIn)
open VG.Proof.Ed25519.RISCV64.Whole (Inv slotArea args3_ok restore_ok restoreList copyIn_ok)
open VG.Spec.Ed448 (bytesAt)

/-! ## The regions -/

section
variable (s : State)

abbrev vpkR : Region := ⟨s.gpr .a0, 57⟩
abbrev vcxR : Region := ⟨s.gpr .a1, (s.gpr .a2).toNat⟩
abbrev vmsR : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
abbrev vsgR : Region := ⟨s.gpr .a5, 114⟩
abbrev vscR : Region := ⟨s.gpr .a6, 8192⟩
abbrev vfR : Region := ⟨s.gpr .a7, 448⟩

/-- The inputs. -/
abbrev vpkB : List Byte := bytesAt s.mem (s.gpr .a0) 57
abbrev vctxB : List Byte := bytesAt s.mem (s.gpr .a1) (s.gpr .a2).toNat
abbrev vmsgB : List Byte := bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat
abbrev vsigB : List Byte := bytesAt s.mem (s.gpr .a5) 114

/-- `k`. -/
abbrev vkB : List Byte :=
  Spec.Ed448.scalarReduce (Spec.Ed448.hash (vctxB s) (bytesAt s.mem (s.gpr .a5) 57 ++ vpkB s ++ vmsgB s))

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
  alC : (s.gpr .a6).toNat % 8 = 0
  alF : (s.gpr .a7).toNat % 8 = 0
  spal : s.sp.toNat % 16 = 0
  sp : 1168 ≤ s.sp.toNat
  bP : (below s.sp 1168).Disjoint (vpkR s)
  bX : (below s.sp 1168).Disjoint (vcxR s)
  bM : (below s.sp 1168).Disjoint (vmsR s)
  bS : (below s.sp 1168).Disjoint (vsgR s)
  bC : (below s.sp 1168).Disjoint (vscR s)
  bF : (below s.sp 1168).Disjoint (vfR s)

/-- What the body may write. -/
abbrev verW (s : State) : List Region := [vscR s, vfR s, below s.sp 1168]

/-- The values in the registers. -/
def verV (s : State) : Reg → BitVec 64
  | .s1 => s.gpr .a6 | .s7 => s.gpr .a1 | .s8 => s.gpr .a2 | .s9 => s.gpr .a3 | .s10 => s.gpr .a4
  | .s11 => s.gpr .a7 | _ => 0

abbrev VInv (s : State) : State → Prop := Inv s (s.gpr .a7) 384 verifyRegs (verV s) (verW s)

theorem verifyRegs_pres : ∀ r ∈ verifyRegs, r ∈ preserved := by decide

theorem vfsub {s : State} {d n : Nat} (h : d + n ≤ 448) : Region.Sub ⟨s.gpr .a7 + BitVec.ofNat 64 d, n⟩ (vfR s) :=
  Offset.sub_base _ h

theorem vfslot {s : State} {d n : Nat} (h : d + n ≤ 384) :
    (slotArea (s.gpr .a7) 384 verifyRegs).Disjoint ⟨s.gpr .a7 + BitVec.ofNat 64 d, n⟩ :=
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

theorem vfsc {d n : Nat} (h : d + n ≤ 448) : Region.Disjoint ⟨s.gpr .a7 + BitVec.ofNat 64 d, n⟩ (vscR s) :=
  hp.cF.symm.sub_left (vfsub h)

theorem vfbelow {d n : Nat} (h : d + n ≤ 448) :
    (below s.sp 1168).Disjoint ⟨s.gpr .a7 + BitVec.ofNat 64 d, n⟩ :=
  hp.bF.sub_right (vfsub h)

theorem vcslot : (slotArea (s.gpr .a7) 384 verifyRegs).Disjoint (vscR s) :=
  hp.cF.symm.sub_left (Offset.sub_base _ (by decide))

theorem vbslot : (slotArea (s.gpr .a7) 384 verifyRegs).Disjoint (below s.sp 1168) :=
  hp.bF.symm.sub_left (Offset.sub_base _ (by decide))

theorem vkenv {t : State} (h : VInv s t) : KEnv (s.gpr .a6) t :=
  ⟨vC hp h, hp.alC, by rw [h.sp]; exact hp.spal, by rw [h.sp]; exact hp.sp, by rw [h.sp]; exact hp.bC⟩

omit hp in
/-- A step writing within `o(F)`, `n` bytes, below the saves. -/
theorem VInv.stepF {t t' : State} (h : VInv s t) {o n : Nat} (hon : o + n ≤ 384) (hrd : t'.rd = t.rd)
    (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp) (hg : ∀ r ∈ preserved, t'.gpr r = t.gpr r)
    (hf : Frame [⟨s.gpr .a7 + BitVec.ofNat 64 o, n⟩] t.mem t'.mem) : VInv s t' :=
  h.step verifyRegs_pres hrd hwr hsp hg hf
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨vfR s, by simp, vfsub (by omega)⟩)
    fun r hr => by rw [List.mem_singleton.mp hr]; exact vfslot hon

end

/-! ## The setup -/

/-- After the setup: the invariant, the header of `dom4` at `F`, and the copies of the signature and
`pk`. -/
structure V1 (s t : State) : Prop where
  inv : VInv s t
  hdr : bytesAt t.mem (s.gpr .a7) 10 = hdrBytes (s.gpr .a2).toNat
  sg : bytesAt t.mem (s.gpr .a7 + BitVec.ofNat 64 200) 114 = vsigB s
  pk : bytesAt t.mem (s.gpr .a7 + BitVec.ofNat 64 320) 57 = vpkB s

theorem verSlot_sub (F : Addr) : Region.Sub (slotArea F 384 verifyRegs) ⟨F, 448⟩ := Offset.sub_base _ (by decide)

theorem verSetup_eq : (saveRegs .a7 384 verifyRegs ++
    [mov .s1 .a6, mov .s7 .a1, mov .s8 .a2, mov .s9 .a3, mov .s10 .a4, mov .s11 .a7, mov .t1 .a5] ++
    copyIn .t1 .s11 200 114 ++ copyIn .a0 .s11 320 57 ++ hdr .s11 .s8) = saveRegs .a7 384 verifyRegs ++
    ([(.s1, .a6), (.s7, .a1), (.s8, .a2), (.s9, .a3), (.s10, .a4), (.s11, .a7)] :
      List (Reg × Reg)).map (fun p => mov p.1 p.2) ++
    (mov .t1 .a5 :: (copyIn .t1 .s11 200 114 ++ (copyIn .a0 .s11 320 57 ++ hdr .s11 .s8))) := by
  simp only [List.append_assoc]; rfl

/-- The setup, from `u`, which differs from `s` only in `t0`. -/
theorem verSetup_ok {s u : State} (hp : VerPre s) (hu : Upd s u .t0 (s.gpr .a2 >>> 8)) :
    WP isa (.block (saveRegs .a7 384 verifyRegs ++
      [mov .s1 .a6, mov .s7 .a1, mov .s8 .a2, mov .s9 .a3, mov .s10 .a4, mov .s11 .a7, mov .t1 .a5] ++
      copyIn .t1 .s11 200 114 ++ copyIn .a0 .s11 320 57 ++ hdr .s11 .s8)) u (V1 s) := by
  have hFw : (vfR s) ∈ u.wr := by rw [hu.wr, hp.wr]; simp
  have hug : ∀ r, r ≠ .t0 → u.gpr r = s.gpr r := hu.other
  have g7 : u.gpr .a7 = s.gpr .a7 := hug _ (by decide)
  rw [verSetup_eq]
  refine setup_ok (v := verV s) (W := verW s) (by rw [g7]; exact hp.alF) (by decide) (by decide)
    (fun p hp' => by rw [g7]; exact in_base hFw (by revert p; decide) (by revert p; decide))
    ⟨vfR s, by simp, by rw [g7]; exact verSlot_sub _⟩ rfl (by decide) (by decide) (fun p hp' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;> exact (hug _ (by decide)).symm) fun t₁ h₁ g₁ => ?_
  rw [g7] at h₁
  have h₁' : VInv s t₁ := h₁.rebase hu.rd hu.wr hu.sp hug (by decide) hu.mem
  have g11 : t₁.gpr .s11 = s.gpr .a7 := h₁'.regs _ (by decide)
  have g0 : t₁.gpr .a0 = s.gpr .a0 := by rw [g₁ _ (by decide), hug _ (by decide)]
  have g5 : t₁.gpr .a5 = s.gpr .a5 := by rw [g₁ _ (by decide), hug _ (by decide)]
  -- The signature's pointer into `t1`.
  unfold mov
  refine wp_addi (by decide) fun t₂ e₂ => ?_
  have h₂ : VInv s t₂ := h₁'.step verifyRegs_pres e₂.rd e₂.wr e₂.sp (fun r hr => e₂.other r fun e => by
      revert hr; rw [e]; decide) (by rw [e₂.mem]; exact Frame.refl _ _) (Wc := [])
    (fun _ h => absurd h List.not_mem_nil) fun _ h => absurd h List.not_mem_nil
  have hFw₂ : (vfR s) ∈ t₂.wr := by rw [h₂.wr, hp.wr]; simp
  have hS : (vsgR s) ∈ t₂.rd := by rw [h₂.rd, hp.rd]; simp
  have hP : (vpkR s) ∈ t₂.rd := by rw [h₂.rd, hp.rd]; simp
  -- The signature, copied to `200(F)`.
  refine copyIn_ok (P := s.gpr .a5) (F := s.gpr .a7) (o := 200) (n := 114) (by decide) (by decide)
    (by rw [e₂.gpr, BitVec.add_zero, g5]) (by rw [e₂.other _ (by decide), g11]) (by decide)
    (fun i hi => in_base (List.mem_append_left _ hS) (by omega) (by omega))
    (fun i hi => in_base hFw₂ (by omega) (by omega))
    (hp.fS.symm.sub_right (Offset.sub_base _ (by decide))) fun t₃ r₃ f₃ b₃ => ?_
  have h₃ : VInv s t₃ := h₂.stepF (by decide) r₃.rd r₃.wr r₃.sp
    (fun r hr => r₃.gpr r fun e => by rw [List.mem_singleton] at e; revert hr; rw [e]; decide) f₃
  have hFw₃ : (vfR s) ∈ t₃.wr := by rw [h₃.wr, hp.wr]; simp
  have hP₃ : (vpkR s) ∈ t₃.rd := by rw [h₃.rd, hp.rd]; simp
  -- `pk`, copied to `320(F)`.
  refine copyIn_ok (P := s.gpr .a0) (F := s.gpr .a7) (o := 320) (n := 57) (by decide) (by decide)
    (by rw [r₃.gpr _ (by decide), e₂.other _ (by decide), g0]) (by rw [h₃.regs _ (by decide)]; rfl) (by decide)
    (fun i hi => in_base (List.mem_append_left _ hP₃) (by omega) (by omega))
    (fun i hi => in_base hFw₃ (by omega) (by omega))
    (hp.fP.symm.sub_right (Offset.sub_base _ (by decide))) fun t₄ r₄ f₄ b₄ => ?_
  have h₄ : VInv s t₄ := h₃.stepF (by decide) r₄.rd r₄.wr r₄.sp
    (fun r hr => r₄.gpr r fun e => by rw [List.mem_singleton] at e; revert hr; rw [e]; decide) f₄
  have hFw₄ : (vfR s) ∈ t₄.wr := by rw [h₄.wr, hp.wr]; simp
  -- The header.
  refine hdr_ok (F := s.gpr .a7) (cl := (s.gpr .a2).toNat) (by decide) (by decide)
    (by rw [h₄.regs _ (by decide)]; rfl) (by rw [h₄.regs _ (by decide)]; exact (ofNat_toNat _).symm)
    (fun j hj => in_base hFw₄ (by omega) (by omega))
    (by simpa using in_base (d := 0) (n := 8) hFw₄ (by decide) (by decide)) hp.alF (by decide) (by decide)
    fun t ht hrd hwr hsp hg => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · refine h₄.step verifyRegs_pres hrd hwr hsp
      (fun r hr => hg r (fun e => by revert hr; rw [e]; decide) fun e => by revert hr; rw [e]; decide)
      (ht ▸ hdrMem_frame _ _ _) (fun r hr => ?_) fun r hr => ?_
    · rw [List.mem_singleton.mp hr]; exact ⟨vfR s, by simp, Region.sub_prefix (by decide)⟩
    · rw [List.mem_singleton.mp hr]; exact Offset.disjoint_base _ (by decide) (by decide)
  · rw [ht, hdrMem_bytes]
  -- What the header and the second copy keep.
  · have hk := bytes_keep (W := [⟨s.gpr .a7, 10⟩]) (ht ▸ hdrMem_frame _ _ _)
      (p := s.gpr .a7 + BitVec.ofNat 64 200) (n := 114) (by decide) fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint_base _ (by decide) (by decide)
    have hk₄ := bytes_keep f₄ (p := s.gpr .a7 + BitVec.ofNat 64 200) (n := 114) (by decide) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
    rw [show bytesAt t.mem (s.gpr .a7 + BitVec.ofNat 64 200) 114 =
        Spec.Sha3.bytesAt t.mem (s.gpr .a7 + BitVec.ofNat 64 200) 114 from rfl, hk, hk₄]
    show Spec.Ed25519.bytesAt t₃.mem _ 114 = _
    rw [b₃]
    show Spec.Sha3.bytesAt t₂.mem (s.gpr .a5) 114 = Spec.Sha3.bytesAt s.mem (s.gpr .a5) 114
    exact ver_keep hp h₂ (R := vsgR s) (.inr (.inr (.inr rfl)))
  · have hk := bytes_keep (W := [⟨s.gpr .a7, 10⟩]) (ht ▸ hdrMem_frame _ _ _)
      (p := s.gpr .a7 + BitVec.ofNat 64 320) (n := 57) (by decide) fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint_base _ (by decide) (by decide)
    rw [show bytesAt t.mem (s.gpr .a7 + BitVec.ofNat 64 320) 57 =
        Spec.Sha3.bytesAt t.mem (s.gpr .a7 + BitVec.ofNat 64 320) 57 from rfl, hk]
    show Spec.Ed25519.bytesAt t₄.mem _ 57 = _
    rw [b₄]
    show Spec.Sha3.bytesAt t₃.mem (s.gpr .a0) 57 = Spec.Sha3.bytesAt s.mem (s.gpr .a0) 57
    exact ver_keep hp h₃ (R := vpkR s) (.inl rfl)

/-! ## The challenge -/

/-- The pieces the challenge hashes. -/
abbrev verPieces : List Piece :=
  dom4Pieces .s11 .s7 .s8 ++ [⟨.s11, 200, .imm 57⟩, ⟨.s11, 320, .imm 57⟩, ⟨.s9, 0, .reg .s10⟩]

theorem V1.hashOk {s t : State} (hp : VerPre s) (h : V1 s t) : HashOk .s1 .s11 16 verPieces t ∧
    (verPieces.map (Piece.bytes t.mem t.gpr)).flatten =
      hdrBytes (s.gpr .a2).toNat ++ vctxB s ++ (bytesAt s.mem (s.gpr .a5) 57 ++ vpkB s ++ vmsgB s) := by
  have g1 : t.gpr .s1 = s.gpr .a6 := h.inv.regs _ (by decide)
  have g7 : t.gpr .s7 = s.gpr .a1 := h.inv.regs _ (by decide)
  have g8 : t.gpr .s8 = s.gpr .a2 := h.inv.regs _ (by decide)
  have g9 : t.gpr .s9 = s.gpr .a3 := h.inv.regs _ (by decide)
  have g10 : t.gpr .s10 = s.gpr .a4 := h.inv.regs _ (by decide)
  have g11 : t.gpr .s11 = s.gpr .a7 := h.inv.regs _ (by decide)
  have cr : ∀ R ∈ [vpkR s, vcxR s, vmsR s, vsgR s], Covers [R] (t.rd ++ t.wr) := fun R hR => by
    rw [h.inv.rd, hp.rd]; exact cov_rd fun a n ⟨r, hr, hc⟩ => ⟨r, by rw [List.mem_singleton.mp hr]; exact hR, hc⟩
  have fP : ∀ {d n : Nat}, d < 2048 → d + n ≤ 448 → n < 2048 →
      PieceOk (s.gpr .a6) t ⟨.s11, d, .imm n⟩ := fun hd hdn hn =>
    pieceOk_of (R := ⟨s.gpr .a7 + BitVec.ofNat 64 _, _⟩) (by simp only [Piece.R, Piece.addr, Len.val, g11])
      (show Reg.s11 ∈ preserved by decide) hd hn (cov_right (cov_in (vF hp h.inv) hdn)) (vfsc hp hdn)
      (by rw [h.inv.sp]; exact vfbelow hp hdn)
  refine ⟨⟨by decide, by decide, by decide, by simp [verPieces, dom4Pieces], by rw [g1]; exact vkenv hp h.inv, ?_,
    by rw [g11]; exact cov_in (vF hp h.inv) (by decide), by rw [g11, g1]; exact vfsc hp (by decide),
    by rw [g11, h.inv.sp]; exact vfbelow hp (by decide)⟩, ?_⟩
  · intro p hp'
    rw [g1]
    simp only [verPieces, dom4Pieces, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl | rfl
    · exact pieceOk_of (R := ⟨s.gpr .a7, 10⟩) (by simp only [Piece.R, Piece.addr, Len.val, g11, BitVec.add_zero])
        (by decide) (by decide) (show 10 < 2048 by decide) (cov_right (cov_in0 (vF hp h.inv) (by decide)))
        (by simpa using vfsc hp (d := 0) (n := 10) (by decide))
        (by rw [h.inv.sp]; simpa using vfbelow hp (d := 0) (n := 10) (by decide))
    · exact pieceOk_of (R := vcxR s) (by simp only [Piece.R, Piece.addr, Len.val, g7, g8, BitVec.add_zero])
        (by decide) (by decide) (show Reg.s8 ∈ preserved by decide) (cr _ (by simp)) hp.cX.symm
        (by rw [h.inv.sp]; exact hp.bX)
    · exact fP (by decide) (by decide) (by decide)
    · exact fP (by decide) (by decide) (by decide)
    · exact pieceOk_of (R := vmsR s) (by simp only [Piece.R, Piece.addr, Len.val, g9, g10, BitVec.add_zero])
        (by decide) (by decide) (show Reg.s10 ∈ preserved by decide) (cr _ (by simp)) hp.cM.symm
        (by rw [h.inv.sp]; exact hp.bM)
  · have kx := ver_keep hp h.inv (R := vcxR s) (.inr (.inl rfl))
    have km := ver_keep hp h.inv (R := vmsR s) (.inr (.inr (.inl rfl)))
    have ks : bytesAt t.mem (s.gpr .a7 + BitVec.ofNat 64 200) 57 = bytesAt s.mem (s.gpr .a5) 57 := by
      rw [← bytesAt_take57, ← bytesAt_take57 s.mem]
      exact congrArg (List.take 57) h.sg
    have h0 := h.hdr
    simp only [verPieces, dom4Pieces, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
      List.flatten_cons, List.flatten_nil, List.append_nil, Piece.bytes, Piece.addr, Len.val, g7, g8, g9, g10, g11,
      BitVec.add_zero, bytesAt_sha3]
    rw [h0, kx, km, ks, h.pk]
    simp only [List.append_assoc]

/-- The arguments of `vg_ed448_verify_equation` set. -/
structure VArgs (s t : State) : Prop where
  inv : VInv s t
  a0 : t.gpr .a0 = s.gpr .a7 + BitVec.ofNat 64 320
  a1 : t.gpr .a1 = s.gpr .a7 + BitVec.ofNat 64 200
  a2 : t.gpr .a2 = s.gpr .a7 + BitVec.ofNat 64 136
  a3 : t.gpr .a3 = s.gpr .a6
  ch : bytesAt t.mem (s.gpr .a7 + BitVec.ofNat 64 136) 57 = vkB s
  sg : bytesAt t.mem (s.gpr .a7 + BitVec.ofNat 64 200) 114 = vsigB s
  pk : bytesAt t.mem (s.gpr .a7 + BitVec.ofNat 64 320) 57 = vpkB s

/-- The challenge into `136(F)`, and the arguments of `vg_ed448_verify_equation`. -/
theorem verHash_ok {s t : State} (hp : VerPre s) (h : V1 s t) :
    WP isa (.seq (hash .s1 verPieces .s11 16) (.seq (.block [.addi .a0 .s11 136, .addi .a1 .s11 16, mov .a2 .s1])
      (.seq (.call "vg_ed448_scalar_reduce" Impl.Ed448.RISCV64.scalarReduce)
        (.block [.addi .a0 .s11 320, .addi .a1 .s11 200, .addi .a2 .s11 136, mov .a3 .s1])))) t (VArgs s) := by
  obtain ⟨ho, hb⟩ := h.hashOk hp
  have g1 : t.gpr .s1 = s.gpr .a6 := h.inv.regs _ (by decide)
  have g11 : t.gpr .s11 = s.gpr .a7 := h.inv.regs _ (by decide)
  refine WP.seq (WP.mono (hash_ok ho.psc ho.pf ho.po rfl rfl ho.env ho.ne ho.ins ho.w ho.dsc ho.dsp)
    fun t₂ ⟨k₂, d₂⟩ => ?_)
  rw [g1, g11] at k₂
  rw [g11] at d₂
  rw [hb, show (s.gpr .a2).toNat = (vctxB s).length by simp [bytesAt], dom4_hash, bytesAt_sha3] at d₂
  have h₂ : VInv s t₂ := Inv.kept h.inv verifyRegs_pres k₂ (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨vfR s, by simp, vfsub (by decide)⟩
      · exact ⟨vscR s, by simp, fun _ h => h⟩
      · exact ⟨below s.sp 1168, by simp, by rw [h.inv.sp]; exact fun _ h => h⟩) fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact vfslot (by decide)
      · exact vcslot hp
      · rw [h.inv.sp]; exact vbslot hp
  -- What the hash keeps of the copies.
  have kH : ∀ {d n : Nat}, d + n ≤ 448 → 130 ≤ d →
      bytesAt t₂.mem (s.gpr .a7 + BitVec.ofNat 64 d) n = bytesAt t.mem (s.gpr .a7 + BitVec.ofNat 64 d) n :=
    fun hdn hd => bytes_keep k₂.frame (by omega) fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
      · exact vfsc hp hdn
      · rw [h.inv.sp]; exact (vfbelow hp hdn).symm
  -- `k`.
  have g1' : t₂.gpr .s1 = s.gpr .a6 := h₂.regs _ (by decide)
  have g11' : t₂.gpr .s11 = s.gpr .a7 := h₂.regs _ (by decide)
  unfold mov
  refine WP.seq (args3_ok (i := 136) (j := 16) (k := 0) (by decide) (by decide) (by decide) (by decide)
    (by decide) fun u hu a3 a4 a5 => ?_)
  rw [g11'] at a3 a4
  rw [g1', BitVec.add_zero] at a5
  have hW : Covers [⟨s.gpr .a7 + BitVec.ofNat 64 136, 57⟩, vscR s] u.wr := by
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
  have kR : ∀ {d n : Nat}, d + n ≤ 448 → 193 ≤ d →
      bytesAt t₃.mem (s.gpr .a7 + BitVec.ofNat 64 d) n = bytesAt t₂.mem (s.gpr .a7 + BitVec.ofNat 64 d) n :=
    fun hdn hd => bytes_keep f₃ (by omega) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
      · exact vfsc hp hdn
  -- The arguments.
  have g1'' : t₃.gpr .s1 = s.gpr .a6 := h₃.regs _ (by decide)
  have g11'' : t₃.gpr .s11 = s.gpr .a7 := h₃.regs _ (by decide)
  refine wp_addi (by decide) fun v₁ e₁ => wp_addi (by decide) fun v₂ e₂ =>
    wp_addi (by decide) fun v₃ e₃ => wp_addi (by decide) fun v₄ e₄ => WP.block_nil ?_
  refine ⟨h₃.step verifyRegs_pres (by rw [e₄.rd, e₃.rd, e₂.rd, e₁.rd]) (by rw [e₄.wr, e₃.wr, e₂.wr, e₁.wr])
    (by rw [e₄.sp, e₃.sp, e₂.sp, e₁.sp]) (fun r hr => ?_) (by rw [e₄.mem, e₃.mem, e₂.mem, e₁.mem]; exact Frame.refl _ _)
    (fun _ h => absurd h List.not_mem_nil) (fun _ h => absurd h List.not_mem_nil), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨-, p0, p1, p2, p3, -⟩ := pres_ne hr
    rw [e₄.other _ p3, e₃.other _ p2, e₂.other _ p1, e₁.other _ p0]
  · rw [e₄.other _ (by decide), e₃.other _ (by decide), e₂.other _ (by decide), e₁.gpr, g11'']
  · rw [e₄.other _ (by decide), e₃.other _ (by decide), e₂.gpr, e₁.other _ (by decide), g11'']
  · rw [e₄.other _ (by decide), e₃.gpr, e₂.other _ (by decide), e₁.other _ (by decide), g11'']
  · rw [e₄.gpr, BitVec.add_zero, e₃.other _ (by decide), e₂.other _ (by decide), e₁.other _ (by decide), g1'']
  · rw [e₄.mem, e₃.mem, e₂.mem, e₁.mem, r₃]
  · rw [e₄.mem, e₃.mem, e₂.mem, e₁.mem, kR (by decide) (by decide), kH (by decide) (by decide), h.sg]
  · rw [e₄.mem, e₃.mem, e₂.mem, e₁.mem, kR (by decide) (by decide), kH (by decide) (by decide), h.pk]

/-- The call of `vg_ed448_verify_equation`. -/
theorem verCall_ok (hR : Proof.Ed448.RecoverOk) (hV : Proof.Ed448.VerifyEq4Ok) {s t : State} (hp : VerPre s)
    (h : VArgs s t) :
    WP isa (.call "vg_ed448_verify_equation" Impl.Ed448.RISCV64.verifyEquation) t fun t' => VInv s t' ∧
      (t'.gpr .a0).setWidth 32 = if Spec.Ed448.verifyEquation (vpkB s) (vsigB s) (vkB s) then 1 else 0 := by
  have hW : Covers [vscR s] t.wr := fun a n ⟨r, hr, hc⟩ => by
    rw [List.mem_singleton.mp hr] at hc; exact ⟨_, vC hp h.inv, hc⟩
  have hc : Covers ([⟨s.gpr .a7 + BitVec.ofNat 64 320, 57⟩, ⟨s.gpr .a7 + BitVec.ofNat 64 200, 114⟩,
      ⟨s.gpr .a7 + BitVec.ofNat 64 136, 57⟩] ++ [vscR s]) (t.rd ++ t.wr) := by
    intro a n ⟨r, hr, hc⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact cov_right (cov_in (vF hp h.inv) (by decide)) a n ⟨_, List.mem_singleton_self _, hc⟩
    · exact cov_right (cov_in (vF hp h.inv) (by decide)) a n ⟨_, List.mem_singleton_self _, hc⟩
    · exact cov_right (cov_in (vF hp h.inv) (by decide)) a n ⟨_, List.mem_singleton_self _, hc⟩
    · exact cov_right hW a n ⟨_, List.mem_singleton_self _, hc⟩
  refine veq_call hR hV h.a0 h.a1 h.a2 h.a3 (vfsc hp (by decide)) (vfsc hp (by decide)) (vfsc hp (by decide)) hc hW
    fun t' rd' wr' sp' f' cs' r' => ⟨h.inv.step verifyRegs_pres rd' wr' sp' cs' f' (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨vscR s, by simp, fun _ h => h⟩) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact vcslot hp, ?_⟩
  rw [r', h.pk, h.sg, h.ch]

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
    WP isa verifyMessage s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.gpr .ra = s.gpr .ra ∧
      (t.gpr .a0).setWidth 32 = verResult s := by
  unfold verifyMessage
  refine WP.seq (wp_srl (by decide) fun u hu => WP.block_nil ?_)
  refine wp_ite (decide ((s.gpr .a2).toNat < 256)) (by rw [eval_zero, hu.gpr, shr8_zero]) (fun hcl => ?_)
    fun hcl => ?_
  · -- `ctxlen < 256`.
    have hcl' : (s.gpr .a2).toNat < 256 := of_decide_eq_true hcl
    unfold verifyMain verifyHash
    refine WP.seq (WP.seq (WP.mono (verSetup_ok hp hu) fun t₁ h₁ => ?_))
    refine WP.mono (verHash_ok hp h₁) fun t₂ h₂ => ?_
    refine WP.seq (WP.mono (verCall_ok hR hV hp h₂) fun t₃ ⟨h₃, r₃⟩ => ?_)
    have hrl : ∀ p ∈ restoreList 384 verifyRegs, p.2 + 8 ≤ 448 := by decide
    refine restore_ok h₃ hp.alF (h₃.regs _ (by decide)) (by decide) (by decide) (by decide) (by decide)
      (fun p (hp' : p ∈ restoreList 384 verifyRegs) =>
        show InRegions (t₃.rd ++ t₃.wr) (s.gpr .a7 + BitVec.ofNat 64 p.2) 8 by
        rw [h₃.rd, h₃.wr, hp.rd, hp.wr]
        exact ⟨vfR s, by simp, Offset.contains_base _ (hrl p hp') (by have := hrl p hp'; omega)⟩)
      fun t₄ g₄ sp₄ ra₄ m₄ o₄ => ⟨g₄, sp₄, ra₄, ?_⟩
    rw [o₄ .a0 (by decide) (by decide), r₃]
    have : Spec.Ed448.verify (vpkB s) (vctxB s) (vmsgB s) (vsigB s) =
        Spec.Ed448.verifyEquation (vpkB s) (vsigB s) (vkB s) := by
      simp only [Spec.Ed448.verify, show (vctxB s).length ≤ 255 by simp [bytesAt]; omega, decide_true,
        Bool.true_and, vkB, bytesAt_take57]
    simp only [verResult, this]
  · -- `ctxlen ≥ 256`: 0.
    have hcl' : ¬ (s.gpr .a2).toNat < 256 := of_decide_eq_false hcl
    refine wp_li (d := .a0) (imm := 0) (by decide) fun v hv => WP.block_nil ⟨fun r hr => ?_, ?_, ?_, ?_⟩
    · rw [hv.other _ (pres_ne hr).2.1, hu.other _ (pres_ne hr).1]
    · rw [hv.sp, hu.sp]
    · rw [hv.other _ (by decide), hu.other _ (by decide)]
    · rw [hv.gpr]
      have : Spec.Ed448.verify (vpkB s) (vctxB s) (vmsgB s) (vsigB s) = false := by
        simp only [Spec.Ed448.verify, Bool.and_eq_false_iff, decide_eq_false_iff_not]
        left; simp [bytesAt]; omega
      simp only [verResult, this]; rfl

end VG.Proof.Ed448.RISCV64.Whole
