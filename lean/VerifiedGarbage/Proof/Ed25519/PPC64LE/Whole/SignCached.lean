module

import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointScalar
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ed25519.Signing
import VerifiedGarbage.Proof.Ed25519.VerifyBytes
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.BaseContract
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.ScalarVerified
import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Prune
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Common
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Frame

/-! ### `Ed25519.PPC64LE.Whole.SignNonce`, which only this module used -/

section

/-! ### `Ed25519.PPC64LE.Whole.SignExpand`, which this module and modules that import it used -/

section

/-! ### `Ed25519.PPC64LE.Whole.SignSetup`, which this module and modules that import it used -/

section

/-!
# `vg_ed25519_sign_expanded` on PPC64LE: the setup

`out` in `r3`, `expanded` (the seed's digest) in `r4`, `pk` in `r5`, the message in `r6` (`len` in
`r7`), `scratch` in `r8` and the frame `F` (288 bytes) in `r9`. The setup
saves the registers at `224(F)`, moves what lives across calls to `r20`–`r25`
and copies `pk` to `192(F)` (`signSetup_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE.Whole VG.Proof.X25519.PPC64LE
open VG.Spec.Ed25519 (bytesAt)
open VG.Impl.Ed25519.PPC64LE (combSym combWord)

/-- The message. -/
abbrev msgR (s : State) : Region := ⟨s.gpr .r6, (s.gpr .r7).toNat⟩

/-- What the body may write. -/
abbrev signW (s : State) : List Region := [⟨s.gpr .r3, 64⟩, ⟨s.gpr .r8, 8192⟩, ⟨s.gpr .r9, 288⟩, below s.sp 48]

/-- The precondition, by register, with `sn` bytes (64 here) at `r4` (the seed's digest), and
without the public key's relation to it. -/
structure SignPre (sn : Nat) (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .r4, sn⟩, ⟨s.gpr .r5, 32⟩, msgR s, TBL (s.syms combSym)]
  wr : s.wr = [⟨s.gpr .r3, 64⟩, ⟨s.gpr .r8, 8192⟩, ⟨s.gpr .r9, 288⟩]
  oS : Region.Disjoint ⟨s.gpr .r3, 64⟩ ⟨s.gpr .r4, sn⟩
  oP : Region.Disjoint ⟨s.gpr .r3, 64⟩ ⟨s.gpr .r5, 32⟩
  oM : Region.Disjoint ⟨s.gpr .r3, 64⟩ (msgR s)
  oC : Region.Disjoint ⟨s.gpr .r3, 64⟩ ⟨s.gpr .r8, 8192⟩
  oF : Region.Disjoint ⟨s.gpr .r3, 64⟩ ⟨s.gpr .r9, 288⟩
  sC : Region.Disjoint ⟨s.gpr .r4, sn⟩ ⟨s.gpr .r8, 8192⟩
  sF : Region.Disjoint ⟨s.gpr .r4, sn⟩ ⟨s.gpr .r9, 288⟩
  pC : Region.Disjoint ⟨s.gpr .r5, 32⟩ ⟨s.gpr .r8, 8192⟩
  pF : Region.Disjoint ⟨s.gpr .r5, 32⟩ ⟨s.gpr .r9, 288⟩
  mC : Region.Disjoint (msgR s) ⟨s.gpr .r8, 8192⟩
  mF : Region.Disjoint (msgR s) ⟨s.gpr .r9, 288⟩
  cF : Region.Disjoint ⟨s.gpr .r8, 8192⟩ ⟨s.gpr .r9, 288⟩
  sp : 48 ≤ s.sp.toNat
  bO : (below s.sp 48).Disjoint ⟨s.gpr .r3, 64⟩
  bS : (below s.sp 48).Disjoint ⟨s.gpr .r4, sn⟩
  bP : (below s.sp 48).Disjoint ⟨s.gpr .r5, 32⟩
  bM : (below s.sp 48).Disjoint (msgR s)
  bC : (below s.sp 48).Disjoint ⟨s.gpr .r8, 8192⟩
  bF : (below s.sp 48).Disjoint ⟨s.gpr .r9, 288⟩
  tfit : (s.syms combSym).toNat + 49152 ≤ 2 ^ 64
  words : ∀ q < 64 * 96, s.mem.readW (s.syms combSym + BitVec.ofNat 64 (8 * q)) 64 = combWord q
  tW : ∀ r ∈ signW s, (TBL (s.syms combSym)).Disjoint r

/-- The values in `r20`–`r25`. -/
def signV (s : State) : Reg → BitVec 64
  | .r20 => s.gpr .r3 | .r21 => s.gpr .r4 | .r22 => s.gpr .r6 | .r23 => s.gpr .r7 | .r24 => s.gpr .r8
  | .r25 => s.gpr .r9 | _ => 0

abbrev SignInv (s : State) : State → Prop := Inv s (s.gpr .r9) 224 signRegs (signV s) (signW s)

theorem signRegs_pres : ∀ r ∈ signRegs, r ∈ preserved := by decide

/-- The slots are apart from everything but the frame's first 224 bytes. -/
theorem sign_slot {sn : Nat} {s : State} (hp : SignPre sn s) :
    (slotArea (s.gpr .r9) 224 signRegs).Disjoint ⟨s.gpr .r3, 64⟩ ∧
    (slotArea (s.gpr .r9) 224 signRegs).Disjoint ⟨s.gpr .r8, 8192⟩ ∧
    (slotArea (s.gpr .r9) 224 signRegs).Disjoint (below s.sp 48) ∧
    ∀ d n, d + n ≤ 224 → (slotArea (s.gpr .r9) 224 signRegs).Disjoint ⟨s.gpr .r9 + BitVec.ofNat 64 d, n⟩ := by
  obtain hs : Region.Sub (slotArea (s.gpr .r9) 224 signRegs) ⟨s.gpr .r9, 288⟩ := Offset.sub_base _ (by decide)
  refine ⟨(hp.oF.symm.sub_left hs), (hp.cF.symm.sub_left hs), (hp.bF.symm.sub_left hs), fun d n h => ?_⟩
  exact Offset.disjoint _ (.inr h) (by decide) (by omega_using [h])

theorem signV_r20 (s : State) : signV s .r20 = s.gpr .r3 := rfl
theorem signV_r24 (s : State) : signV s .r24 = s.gpr .r8 := rfl
theorem signV_r25 (s : State) : signV s .r25 = s.gpr .r9 := rfl

/-- The setup: the registers saved, the pointers moved to `r20`–`r25`, `pk` copied to `192(F)`. -/
theorem signSetup_ok {sn : Nat} {s : State} (hp : SignPre sn s) :
    WP isa (.block signSetup) s fun t => SignInv s t ∧
      bytesAt t.mem (s.gpr .r9 + BitVec.ofNat 64 192) 32 = bytesAt s.mem (s.gpr .r5) 32 := by
  obtain hF : (⟨s.gpr .r9, 288⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  obtain hsl : ∀ p ∈ slots 224 signRegs, p.2 + 8 ≤ 288 := by decide
  obtain ⟨-, -, -, hsl₄⟩ := sign_slot hp
  unfold signSetup
  refine save_ok (by decide) (by decide) (by decide)
    (fun p hp' => in_base hF (hsl p hp') (by have := hsl p hp'; omega_using [this])) fun u hu _ hsv hfr => ?_
  unfold mov
  simp only [List.cons_append, List.nil_append]
  refine wp_addi (by decide) (by decide) fun u₁ h₁ => wp_addi (by decide) (by decide) fun u₂ h₂ =>
    wp_addi (by decide) (by decide) fun u₃ h₃ => wp_addi (by decide) (by decide) fun u₄ h₄ =>
    wp_addi (by decide) (by decide) fun u₅ h₅ => wp_addi (by decide) (by decide) fun u₆ h₆ => ?_
  obtain m₆ : u₆.mem = u.mem := by rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  obtain g₆ : ∀ r, r ∉ signRegs → u₆.gpr r = u.gpr r := fun r hr => by
    simp only [signRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨a, b, c, d, e, f⟩ := hr
    rw [h₆.other _ f, h₅.other _ e, h₄.other _ d, h₃.other _ c, h₂.other _ b, h₁.other _ a]
  obtain gu : ∀ r, r ≠ .r0 → u.gpr r = s.gpr r := fun r h => hu.gpr r (by simpa using h)
  obtain rd₆ : u₆.rd = s.rd := by rw [h₆.rd, h₅.rd, h₄.rd, h₃.rd, h₂.rd, h₁.rd, hu.rd]
  obtain wr₆ : u₆.wr = s.wr := by rw [h₆.wr, h₅.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr, hu.wr]
  obtain sp₆ : u₆.sp = s.sp := by rw [h₆.sp, h₅.sp, h₄.sp, h₃.sp, h₂.sp, h₁.sp, hu.sp]
  obtain e5 : u₆.gpr .r5 = s.gpr .r5 := by rw [g₆ _ (by decide), gu _ (by decide)]
  obtain e25 : u₆.gpr .r25 = s.gpr .r9 := by
    rw [h₆.gpr, h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide),
      h₁.other _ (by decide), BitVec.add_zero, gu _ (by decide)]
  obtain hP : (⟨s.gpr .r5, 32⟩ : Region) ∈ s.rd := by rw [hp.rd]; simp
  obtain hsep : ∀ i < 4, ∀ j < 4, Mem.Sep (s.gpr .r5 + BitVec.ofNat 64 (8 * i)) 8
      (s.gpr .r9 + BitVec.ofNat 64 (192 + 8 * j)) 8 := fun i hi j hj =>
    hp.pF.sep (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])) (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj]))
  rw [← List.append_nil (copyIn .r5 .r25 192)]
  refine copy_ok (A := s.gpr .r5) (B := s.gpr .r9) (da := fun k => 8 * k) (db := fun k => 192 + 8 * k)
    (R := ⟨s.gpr .r9 + BitVec.ofNat 64 192, 32⟩) (by decide) (by decide) (by decide) (by decide) e5 e25
    (fun k hk => ⟨by omega_using [hk], by omega_using []⟩) (fun k hk => ⟨by omega_using [hk], by omega_using []⟩)
    (fun k hk => by rw [rd₆, wr₆]; exact in_base (List.mem_append_left _ hP) (by omega_using [hk]) (by omega_using [hk]))
    (fun k hk => by rw [wr₆]; exact in_base hF (by omega_using [hk]) (by omega_using [hk]))
    (fun k hk => Offset.contains _ (by omega_using []) (by omega_using [hk]) (by omega_using [])) hsep
    (fun i hi j hj hij => Offset.sep _ (by omega_using [hij]) (by omega_using [hi]) (by omega_using [hj])) fun t ht hft hw => WP.block_nil ?_
  obtain fin : Frame [slotArea (s.gpr .r9) 224 signRegs, ⟨s.gpr .r9 + BitVec.ofNat 64 192, 32⟩] s.mem t.mem :=
    (hfr.mono (by simp)).trans (by rw [m₆] at hft; exact hft.mono (by simp))
  refine ⟨⟨by rw [ht.rd, rd₆], by rw [ht.wr, wr₆], by rw [ht.sp, sp₆], fun r hr => ?_, fun r hr hn => ?_, ?_,
    fin.sub fun r hr => ?_⟩, ?_⟩
  · rw [ht.gpr r (by revert hr; decide +revert)]
    simp only [signRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h₆.other _ (by decide), h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide),
        h₂.other _ (by decide), h₁.gpr, BitVec.add_zero, gu _ (by decide)]; rfl
    · rw [h₆.other _ (by decide), h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide),
        h₂.gpr, h₁.other _ (by decide), BitVec.add_zero, gu _ (by decide)]; rfl
    · rw [h₆.other _ (by decide), h₅.other _ (by decide), h₄.other _ (by decide), h₃.gpr,
        h₂.other _ (by decide), h₁.other _ (by decide), BitVec.add_zero, gu _ (by decide)]; rfl
    · rw [h₆.other _ (by decide), h₅.other _ (by decide), h₄.gpr, h₃.other _ (by decide),
        h₂.other _ (by decide), h₁.other _ (by decide), BitVec.add_zero, gu _ (by decide)]; rfl
    · rw [h₆.other _ (by decide), h₅.gpr, h₄.other _ (by decide), h₃.other _ (by decide),
        h₂.other _ (by decide), h₁.other _ (by decide), BitVec.add_zero, gu _ (by decide)]; rfl
    · rw [e25]; rfl
  · have h8 : r ∉ [Reg.r8] := by
      simp only [List.mem_singleton]; intro e; rw [e] at hr; exact absurd hr (by decide)
    rw [ht.gpr r h8, g₆ r hn, gu r fun e => r0_pres (e ▸ hr)]
  · refine (hsv.frame_in (slots_in 224 signRegs) (m₆ ▸ hft) fun r hr => ?_)
    rw [List.mem_singleton.mp hr]
    exact (Offset.disjoint _ (.inr (by decide)) (by decide) (by decide))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨s.gpr .r9, 288⟩, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨s.gpr .r9, 288⟩, by simp, Offset.sub_base _ (by decide)⟩
  · refine bytes32_of_words fun k hk => ?_
    obtain hw' := hw k hk
    obtain hr' : u.mem.readW (s.gpr .r5 + BitVec.ofNat 64 (8 * k)) 64 = s.mem.readW (s.gpr .r5 + BitVec.ofNat 64 (8 * k)) 64 :=
      hfr.readW (r := ⟨s.gpr .r5, 32⟩) (Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])) (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact (hp.pF.sub_right (Offset.sub_base _ (by decide)))) (by decide)
    rw [Offset.add_add, hw', m₆, hr']

/-- The regions a step of the body may write: the scratch space, the callees' frames, `out`, its
halves, or the frame below the slots. -/
def SignWr (s : State) (r : Region) : Prop :=
  r = ⟨s.gpr .r8, 8192⟩ ∨ r = below s.sp 48 ∨ r = ⟨s.gpr .r3, 64⟩ ∨ r = ⟨s.gpr .r3 + BitVec.ofNat 64 32, 32⟩ ∨
    r = ⟨s.gpr .r3, 32⟩ ∨ ∃ d n, d + n ≤ 224 ∧ r = ⟨s.gpr .r9 + BitVec.ofNat 64 d, n⟩

theorem signStep {sn : Nat} {s t t' : State} (hp : SignPre sn s) (h : SignInv s t) (hrd : t'.rd = t.rd)
    (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp) (hg : ∀ r ∈ preserved, t'.gpr r = t.gpr r) {Wc : List Region}
    (hf : Frame Wc t.mem t'.mem) (hW : ∀ r ∈ Wc, SignWr s r) : SignInv s t' := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := sign_slot hp
  refine Inv.step h signRegs_pres hrd hwr hsp hg hf (fun r hr => ?_) fun r hr => ?_
  · rcases hW r hr with rfl | rfl | rfl | rfl | rfl | ⟨d, n, hdn, rfl⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨⟨s.gpr .r3, 64⟩, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨s.gpr .r3, 64⟩, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨⟨s.gpr .r9, 288⟩, by simp, Offset.sub_base _ (by omega_using [hdn])⟩
  · rcases hW r hr with rfl | rfl | rfl | rfl | rfl | ⟨d, n, hdn, rfl⟩
    · exact h₂
    · exact h₃
    · exact h₁
    · exact h₁.sub_right (Offset.sub_base _ (by decide))
    · exact h₁.sub_right (Region.sub_prefix (by decide))
    · exact h₄ d n hdn

end VG.Proof.Ed25519.PPC64LE.Whole

end

end

/-!
# `vg_ed25519_sign_expanded` on PPC64LE: the secret scalar and the nonce's prefix

The digest at `r4` copied to `128(F)` (`signCopy_ok`), the first half of the
digest pruned into `0(F)` and its second half copied to `32(F)`
(`signExpandWith_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE.Whole VG.Proof.X25519.PPC64LE
open VG.Spec.Ed25519 (bytesAt decodeLE encodeLE)

theorem sign_env {sn : Nat} {s t : State} (hp : SignPre sn s) (h : SignInv s t) : ScEnv (s.gpr .r8) t :=
  ⟨by rw [h.wr, hp.wr]; simp, by rw [h.sp]; exact hp.sp, by rw [h.sp]; exact hp.bC⟩

theorem sign_Fw {sn : Nat} {s t : State} (hp : SignPre sn s) (h : SignInv s t) : (⟨s.gpr .r9, 288⟩ : Region) ∈ t.wr := by
  rw [h.wr, hp.wr]; simp

theorem sign_inF {sn : Nat} {s t : State} (hp : SignPre sn s) (h : SignInv s t) {d : Nat} (hd : d + 8 ≤ 288) :
    InRegions t.wr (s.gpr .r9 + BitVec.ofNat 64 d) 8 := in_base (sign_Fw hp h) hd (by omega_arith)

theorem sign_inF' {sn : Nat} {s t : State} (hp : SignPre sn s) (h : SignInv s t) {d : Nat} (hd : d + 8 ≤ 288) :
    InRegions (t.rd ++ t.wr) (s.gpr .r9 + BitVec.ofNat 64 d) 8 :=
  in_base (List.mem_append_right _ (sign_Fw hp h)) hd (by omega_arith)

/-- An input, while the body runs. -/
theorem sign_input {s t : State} (h : SignInv s t) {p : Addr} {n : Nat} (hn : n < 2 ^ 64)
    (hO : Region.Disjoint ⟨p, n⟩ ⟨s.gpr .r3, 64⟩) (hC : Region.Disjoint ⟨p, n⟩ ⟨s.gpr .r8, 8192⟩)
    (hF : Region.Disjoint ⟨p, n⟩ ⟨s.gpr .r9, 288⟩) (hB : Region.Disjoint ⟨p, n⟩ (below s.sp 48)) :
    bytesAt t.mem p n = bytesAt s.mem p n :=
  bytes_keep h.frame hn fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hO
    · exact hC
    · exact hF
    · exact hB

/-- The secret scalar and the nonce's prefix, from a first step that leaves the digest `D` at
`128(F)`. -/
theorem signExpandWith_ok {sn : Nat} {s t : State} (hp : SignPre sn s) {digest : Prog isa} {D : List Byte}
    (hd : WP isa digest t fun t' => SignInv s t' ∧
      Frame [⟨s.gpr .r8, 8192⟩, ⟨s.gpr .r9, 192⟩, below s.sp 48] t.mem t'.mem ∧
      bytesAt t'.mem (s.gpr .r9 + BitVec.ofNat 64 128) 64 = D) :
    WP isa (signExpandWith digest) t fun t' => SignInv s t' ∧
      Frame [⟨s.gpr .r8, 8192⟩, ⟨s.gpr .r9, 192⟩, below s.sp 48] t.mem t'.mem ∧
      bytesAt t'.mem (s.gpr .r9) 32 = encodeLE 32 (Spec.Ed25519.prune D) ∧
      bytesAt t'.mem (s.gpr .r9 + BitVec.ofNat 64 32) 32 = D.drop 32 := by
  unfold signExpandWith
  refine WP.seq (WP.mono hd fun t₄ ⟨h₄, f₄, dg⟩ => ?_)
  -- The pruning, and the copy of the second half.
  refine prune_ok (f := .r25) (F := s.gpr .r9) (d := 128) (o := 0) (by decide) (by decide) (h₄.regs _ (by decide))
    (by decide) (by decide) (by decide) (fun k hk => sign_inF' hp h₄ (by omega_arith)) (fun k hk => sign_inF hp h₄ (by omega_arith))
    fun u hu hfu hpr => ?_
  have hu' : SignInv s u := signStep hp h₄ hu.rd hu.wr hu.sp
    (fun r hr => hu.gpr r (by revert hr; cases r <;> decide)) hfu fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inr (.inr (.inr (.inr (.inr ⟨0, 32, by decide, rfl⟩))))
  rw [← List.append_nil (copy32 .r25 160 32)]
  refine copy_ok (A := s.gpr .r9) (B := s.gpr .r9) (da := fun k => 160 + 8 * k) (db := fun k => 32 + 8 * k)
    (R := ⟨s.gpr .r9 + BitVec.ofNat 64 32, 32⟩) (by decide) (by decide) (by decide) (by decide)
    (hu'.regs _ (by decide)) (hu'.regs _ (by decide)) (fun k hk => ⟨by omega_arith, by omega_arith⟩)
    (fun k hk => ⟨by omega_arith, by omega_arith⟩) (fun k hk => sign_inF' hp hu' (by omega_arith)) (fun k hk => sign_inF hp hu' (by omega_arith))
    (fun k hk => Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))
    (fun i hi j hj => Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith))
    (fun i hi j hj hij => Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) fun v hv hfv hw => WP.block_nil ?_
  have hv' : SignInv s v := signStep hp hu' hv.rd hv.wr hv.sp
    (fun r hr => hv.gpr r (by revert hr; cases r <;> decide)) hfv fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inr (.inr (.inr (.inr (.inr ⟨32, 32, by decide, rfl⟩))))
  have F0 : Region.Sub ⟨s.gpr .r9 + BitVec.ofNat 64 0, 32⟩ ⟨s.gpr .r9, 192⟩ := Offset.sub_base _ (by decide)
  have F32 : Region.Sub ⟨s.gpr .r9 + BitVec.ofNat 64 32, 32⟩ ⟨s.gpr .r9, 192⟩ := Offset.sub_base _ (by decide)
  refine ⟨hv', ?_, ?_, ?_⟩
  · -- The writes: the digest's, the scalar's and the prefix's.
    refine f₄.trans <| (hfu.sub fun r hr => ?_).trans (hfv.sub fun r hr => ?_)
    · rw [List.mem_singleton.mp hr]; exact ⟨_, by simp, F0⟩
    · rw [List.mem_singleton.mp hr]; exact ⟨_, by simp, F32⟩
  · have e₁ : bytesAt v.mem (s.gpr .r9) 32 = bytesAt u.mem (s.gpr .r9) 32 :=
      bytes_keep hfv (by decide) fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.base_disjoint _ (by decide) (by decide)
    have hdec : decodeLE (bytesAt u.mem (s.gpr .r9) 32) = Spec.Ed25519.prune D := by
      have := hpr
      rwa [BitVec.add_zero, dg] at this
    rw [e₁, Proof.Ed25519.bytesAt_encodeLE, hdec]
  · have e₁ : bytesAt v.mem (s.gpr .r9 + BitVec.ofNat 64 32) 32 =
        bytesAt u.mem (s.gpr .r9 + BitVec.ofNat 64 160) 32 :=
      bytes32_of_words fun k hk => by rw [Offset.add_add, Offset.add_add]; exact hw k hk
    have e₂ : bytesAt u.mem (s.gpr .r9 + BitVec.ofNat 64 160) 32 =
        bytesAt t₄.mem (s.gpr .r9 + BitVec.ofNat 64 160) 32 :=
      bytes_keep hfu (by decide) fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
    rw [e₁, e₂, show s.gpr .r9 + BitVec.ofNat 64 160 = s.gpr .r9 + BitVec.ofNat 64 128 + BitVec.ofNat 64 32 by
      rw [Offset.add_add], ← Proof.Ed25519.signatureBytes_drop, dg]

/-- The digest at `r4` copied to `128(F)`. -/
theorem signCopy_ok {s t : State} (hp : SignPre 64 s) (h : SignInv s t) :
    WP isa (.block (copyIn64 .r21 .r25 128)) t fun t' => SignInv s t' ∧
      Frame [⟨s.gpr .r8, 8192⟩, ⟨s.gpr .r9, 192⟩, below s.sp 48] t.mem t'.mem ∧
      bytesAt t'.mem (s.gpr .r9 + BitVec.ofNat 64 128) 64 = bytesAt s.mem (s.gpr .r4) 64 := by
  have hS : (⟨s.gpr .r4, 64⟩ : Region) ∈ s.rd := by rw [hp.rd]; simp
  have F128 : Region.Sub ⟨s.gpr .r9 + BitVec.ofNat 64 128, 64⟩ ⟨s.gpr .r9, 288⟩ := Offset.sub_base _ (by decide)
  rw [← List.append_nil (copyIn64 .r21 .r25 128)]
  refine copy64_ok (A := s.gpr .r4) (B := s.gpr .r9) (o := 128) (by decide) (by decide) (by decide) (by decide)
    (h.regs _ (by decide)) (h.regs _ (by decide)) (by decide) (by decide)
    (fun k hk => by rw [h.rd, h.wr]; exact in_base (List.mem_append_left _ hS) (by omega_using [hk]) (by omega_using [hk]))
    (fun k hk => sign_inF hp h (by omega_using [hk])) (hp.sF.sub_right F128) fun u hu hfu hb => WP.block_nil
      ⟨signStep hp h hu.rd hu.wr hu.sp (fun r hr => hu.gpr r (by revert hr; cases r <;> decide)) hfu
        (fun r hr => by
          rw [List.mem_singleton.mp hr]; exact .inr (.inr (.inr (.inr (.inr ⟨128, 64, by decide, rfl⟩))))),
      hfu.sub fun r hr => by
        rw [List.mem_singleton.mp hr]; exact ⟨⟨s.gpr .r9, 192⟩, by simp, Offset.sub_base _ (by decide)⟩, ?_⟩
  rw [hb, sign_input h (by decide) hp.oS.symm hp.sC hp.sF hp.bS.symm]

end VG.Proof.Ed25519.PPC64LE.Whole

end

end

/-!
# `vg_ed25519_sign_expanded` on PPC64LE: the nonce, and `R`

The prefix at `32(F)` and the message hashed into `128(F)`, the digest
reduced into the nonce at `64(F)` by a call of `vg_ed25519_scalar_reduce`,
and `R = [r]B` encoded into `out` by a call of `vg_ed25519_scalar_base`
(`signNonce_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE.Whole VG.Proof.X25519.PPC64LE
open VG.Spec.Ed25519 (bytesAt)
open VG.Impl.Ed25519.PPC64LE (combSym)

/-- The message's bytes. -/
abbrev msgB (s : State) : List Byte := bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat

theorem msgB_length (s : State) : (msgB s).length = (s.gpr .r7).toNat := by simp [bytesAt]

theorem sign_msg {sn : Nat} {s t : State} (hp : SignPre sn s) (h : SignInv s t) :
    bytesAt t.mem (s.gpr .r6) (s.gpr .r7).toNat = msgB s :=
  sign_input h (s.gpr .r7).isLt hp.oM.symm hp.mC hp.mF hp.bM.symm

theorem sign_msg_cov {sn : Nat} {s t : State} (hp : SignPre sn s) (h : SignInv s t) : Covers [msgR s] (t.rd ++ t.wr) :=
  fun a n hi => by
    obtain ⟨r, hr, hc⟩ := hi
    rw [h.rd, hp.rd]
    exact ⟨r, List.mem_append_left _ (by rw [List.mem_singleton.mp hr]; simp), hc⟩

/-- The message fits beside the scratch space. -/
theorem sign_len {sn : Nat} {s : State} (hp : SignPre sn s) : (s.gpr .r7).toNat + 8192 ≤ 2 ^ 64 :=
  len_add_le (Nat.le_of_lt (s.gpr .r7).isLt) (by decide) hp.mC

theorem signNonce_ok (C : ShaOK) (B : BaseOk) {sn : Nat} {s t : State} (hp : SignPre sn s) (h : SignInv s t) {P : List Byte}
    (hP : bytesAt t.mem (s.gpr .r9 + BitVec.ofNat 64 32) 32 = P) (hsy : t.syms combSym = s.syms combSym) :
    WP isa signNonce t fun t' => SignInv s t' ∧
      Frame [⟨s.gpr .r8, 8192⟩, ⟨s.gpr .r9 + BitVec.ofNat 64 64, 128⟩, below s.sp 48, ⟨s.gpr .r3, 32⟩]
        t.mem t'.mem ∧
      bytesAt t'.mem (s.gpr .r9 + BitVec.ofNat 64 64) 32 =
        Spec.Ed25519.scalarReduce (Spec.Sha512.sha512 (P ++ msgB s)) ∧
      bytesAt t'.mem (s.gpr .r3) 32 =
        Spec.Ed25519.scalarBase (Spec.Ed25519.scalarReduce (Spec.Sha512.sha512 (P ++ msgB s))) := by
  obtain hPl : P.length = 32 := by rw [← hP]; simp [bytesAt]
  obtain hlen := sign_len hp
  -- The hashes write the scratch space and the callees' frames.
  obtain toL : ∀ {m m' : Mem} {sp : Addr}, sp = s.sp → Frame [⟨s.gpr .r8, 8192⟩, below sp 48] m m' →
      Frame [⟨s.gpr .r8, 8192⟩, ⟨s.gpr .r9 + BitVec.ofNat 64 64, 128⟩, below s.sp 48, ⟨s.gpr .r3, 32⟩] m m' :=
    fun e hf => by subst e; exact hf.mono (by simp)
  obtain scW : ∀ {t : State}, SignInv s t → ∀ r ∈ [(⟨s.gpr .r8, 8192⟩ : Region), below t.sp 48], SignWr s r :=
    fun h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inl rfl
      · exact .inr (.inl (by rw [h.sp]))
  obtain F32 : Region.Sub ⟨s.gpr .r9 + BitVec.ofNat 64 32, 32⟩ ⟨s.gpr .r9, 288⟩ := Offset.sub_base _ (by decide)
  obtain F64 : Region.Sub ⟨s.gpr .r9 + BitVec.ofNat 64 64, 32⟩ ⟨s.gpr .r9, 288⟩ := Offset.sub_base _ (by decide)
  obtain F128 : Region.Sub ⟨s.gpr .r9 + BitVec.ofNat 64 128, 64⟩ ⟨s.gpr .r9, 288⟩ := Offset.sub_base _ (by decide)
  unfold signNonce
  refine WP.seq (WP.of_syms <| hashInit_ok C (sr := .r24) (by decide) (h.regs _ (by decide)) (sign_env hp h)
    fun t₂ a b c f₂ g hr₂ sy₂ => ?_)
  obtain h₂ := signStep hp h a b c g f₂ (scW h)
  refine WP.seq (WP.of_syms <| hashUpdate_ok C (sr := .r24) (src := .r25) (off := 32) (len := 32) (by decide) (by decide)
    (by decide) (by decide) (by decide) (h₂.regs _ (by decide)) (by rw [h₂.regs _ (by decide)]; rfl)
    (Sets.li (d := .r4) (k := 0) (by decide)) (Sets.li (d := .r6) (k := 32) (by decide))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) rfl (sign_env hp h₂)
    (Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨_, List.mem_append_right _ (sign_Fw hp h₂), 32, rfl, show 32 + 32 ≤ 288 by decide⟩)
    (hp.cF.symm.sub_left F32) (by rw [h₂.sp]; exact hp.bF.sub_right F32) fun t₃ a b c f₃ g hr₃ sy₃ => ?_)
  obtain h₃ := signStep hp h₂ a b c g f₃ (scW h₂)
  obtain P₂ : bytesAt t₂.mem (s.gpr .r9 + BitVec.ofNat 64 32) 32 = P := by
    rw [← hP]
    exact bytes_keep f₂ (by decide) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.cF.symm.sub_left F32
      · rw [h.sp]; exact hp.bF.symm.sub_left F32
  obtain r₃ : Repr t₃.mem (s.gpr .r8) P := by
    have := hr₃ [] hr₂ rfl
    rwa [List.nil_append, P₂] at this
  refine WP.seq (WP.of_syms <| hashUpdate_ok C (sr := .r24) (src := .r22) (off := 0) (len := (s.gpr .r7).toNat) (by decide)
    (by decide) (by decide) (by decide) (by decide) (h₃.regs _ (by decide))
    (by rw [h₃.regs _ (by decide), BitVec.add_zero]; rfl)
    (Sets.li (d := .r4) (k := 32) (by decide)) (Sets.addi (d := .r6) (n := .r23) (k := 0) (by decide) (by decide))
    (fun _ _ _ => rfl) (fun g g' hg => by rw [hg .r23 (by decide) (by decide) (by decide)])
    (by rw [BitVec.add_zero, h₃.regs _ (by decide)]; rfl) (sign_env hp h₃) (sign_msg_cov hp h₃)
    hp.mC (by rw [h₃.sp]; exact hp.bM) fun t₄ a b c f₄ g hr₄ sy₄ => ?_)
  obtain h₄ := signStep hp h₃ a b c g f₄ (scW h₃)
  obtain r₄ : Repr t₄.mem (s.gpr .r8) (P ++ msgB s) := by
    have := hr₄ P r₃ (by rw [hPl])
    rwa [sign_msg hp h₃] at this
  refine WP.seq (WP.of_syms <| hashFinalize_ok C (sr := .r24) (f := .r25) (o := 128) (out := s.gpr .r9 + BitVec.ofNat 64 128)
    (vc := fun g => g .r23 + BitVec.ofNat 64 32)
    (by decide) (by decide) (by decide) (by decide) (by decide) (h₄.regs _ (by decide))
    (by rw [h₄.regs _ (by decide)]; rfl)
    (Sets.addi (d := .r4) (n := .r23) (k := 32) (by decide) (by decide)) (fun g g' hg => by rw [hg .r23 (by decide)])
    (sign_env hp h₄)
    (Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, sign_Fw hp h₄, 128, rfl, show 128 + 64 ≤ 288 by decide⟩)
    (hp.cF.symm.sub_left F128) (by rw [h₄.sp]; exact hp.bF.sub_right F128) fun t₅ a b c f₅ g hd₅ sy₅ => ?_)
  obtain h₅ := signStep hp h₄ a b c g f₅ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl rfl
    · exact .inr (.inr (.inr (.inr (.inr ⟨128, 64, by decide, rfl⟩))))
    · exact .inr (.inl (by rw [h₄.sp])))
  obtain dg : bytesAt t₅.mem (s.gpr .r9 + BitVec.ofNat 64 128) 64 = Spec.Sha512.sha512 (P ++ msgB s) :=
    hd₅ _ r₄ (by rw [List.length_append, hPl, msgB_length]; omega_using [hlen])
      (by rw [h₄.regs _ (by decide), List.length_append, hPl, msgB_length, cnt_eq]; rfl)
  -- The nonce: `scalar_reduce`.
  obtain sF : Region.Disjoint ⟨s.gpr .r9 + BitVec.ofNat 64 64, 32⟩ ⟨s.gpr .r9 + BitVec.ofNat 64 128, 64⟩ :=
    Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
  obtain hFw := sign_Fw hp h₅
  obtain hCw : (⟨s.gpr .r8, 8192⟩ : Region) ∈ t₅.wr := (sign_env hp h₅).w
  obtain hOw : (⟨s.gpr .r3, 64⟩ : Region) ∈ t₅.wr := by rw [h₅.wr, hp.wr]; simp
  unfold mov
  refine WP.seq (WP.of_syms <| args3_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) fun t₆ k₆ c3 c4 c5 sy₆ => ?_)
  rw [h₅.regs _ (by decide), signV_r25] at c3 c4
  rw [h₅.regs _ (by decide), BitVec.add_zero, signV_r24] at c5
  obtain ce : ∀ (u : State) q, q ∉ linkRegs → ∀ rd wr, (u.callEntry.withRegions rd wr).gpr q = u.gpr q :=
    fun _ q hq _ _ => by rw [State.withRegions_gpr, State.callEntry_gpr _ hq]
  refine WP.seq (WP.of_syms <| WP.call (k := reducePPC) reduce_ok' (rd := [⟨s.gpr .r9 + BitVec.ofNat 64 128, 64⟩])
    (wr := [⟨s.gpr .r9 + BitVec.ofNat 64 64, 32⟩, ⟨s.gpr .r8, 8192⟩])
    ⟨by rw [State.withRegions_rd, ce _ _ (by decide), c4],
      by rw [State.withRegions_wr, ce _ _ (by decide), ce _ _ (by decide), c3, c5],
      by rw [ce _ _ (by decide), ce _ _ (by decide), c3, c4]; exact sF,
      by rw [ce _ _ (by decide), ce _ _ (by decide), c3, c5]; exact hp.cF.symm.sub_left F64,
      by rw [ce _ _ (by decide), ce _ _ (by decide), c4, c5]; exact hp.cF.symm.sub_left F128⟩
    (Covers.of_sub fun r hr => by
      rw [k₆.rd, k₆.wr]
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_append_right _ hFw, 128, rfl, show 128 + 64 ≤ 288 by decide⟩
      · exact ⟨_, List.mem_append_right _ hFw, 64, rfl, show 64 + 32 ≤ 288 by decide⟩
      · exact ⟨_, List.mem_append_right _ hCw, 0, by simp, by simp⟩)
    (Covers.of_sub fun r hr => by
      rw [k₆.wr]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, hFw, 64, rfl, show 64 + 32 ≤ 288 by decide⟩
      · exact ⟨_, hCw, 0, by simp, by simp⟩) (fun t₇ a b c f₇ g _ hpost sy₇ => ?_) (by decide +kernel))
  simp only [reducePPC, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem,
    State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r4 ∉ linkRegs by decide),
    c3, c4, k₆.mem, dg] at hpost
  obtain h₇ := signStep hp h₅ (a.trans k₆.rd) (b.trans k₆.wr) (c.trans k₆.sp)
    (fun r hr => (g r hr).trans (k₆.pres r hr)) (k₆.mem ▸ f₇) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr (.inr (.inr (.inr (.inr ⟨64, 32, by decide, rfl⟩))))
      · exact .inl rfl
  -- `R`: `scalar_base`.
  refine WP.seq (WP.of_syms <| args3_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) fun t₈ k₈ d3 d4 d5 sy₈ => ?_)
  rw [h₇.regs _ (by decide), BitVec.add_zero] at d3 d5
  rw [signV_r20] at d3
  rw [signV_r24] at d5
  rw [h₇.regs _ (by decide), signV_r25] at d4
  obtain sy : t₈.syms combSym = s.syms combSym := by rw [sy₈, sy₇, sy₆, sy₅, sy₄, sy₃, sy₂, hsy]
  obtain wd₈ : ∀ q < 64 * 96, t₈.mem.readW (s.syms combSym + BitVec.ofNat 64 (8 * q)) 64 =
      Impl.Ed25519.PPC64LE.combWord q := fun q hq => by
    rw [← hp.words q hq, k₈.mem]
    exact h₇.frame.readW (r := TBL (s.syms combSym)) (Offset.contains_base _ (by omega_using [hq]) (by omega_using [hq])) hp.tW
      (by decide)
  refine WP.call (k := baseRV) B (rd := [⟨s.gpr .r9 + BitVec.ofNat 64 64, 32⟩, TBL (s.syms combSym)])
    (wr := [⟨s.gpr .r3, 32⟩, ⟨s.gpr .r8, 8192⟩])
    (basePre_call d3 d4 d5 sy (hp.oC.sub_left (Region.sub_prefix (by decide))) (hp.cF.symm.sub_left F64)
      hp.tfit wd₈ (hp.tW _ (by simp)))
    (Covers.of_sub fun r hr => by
      rw [k₈.rd, k₈.wr, h₇.wr, h₇.rd]
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨s.gpr .r9, 288⟩, List.mem_append_right _ (by rw [hp.wr]; simp), 64, rfl,
          show 64 + 32 ≤ 288 by decide⟩
      · exact ⟨TBL (s.syms combSym), List.mem_append_left _ (by rw [hp.rd]; simp), 0, by simp, by simp⟩
      · exact ⟨⟨s.gpr .r3, 64⟩, List.mem_append_right _ (by rw [hp.wr]; simp), 0, by simp, by simp⟩
      · exact ⟨⟨s.gpr .r8, 8192⟩, List.mem_append_right _ (by rw [hp.wr]; simp), 0, by simp, by simp⟩)
    (Covers.of_sub fun r hr => by
      rw [k₈.wr, h₇.wr, hp.wr]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨s.gpr .r3, 64⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨s.gpr .r8, 8192⟩, by simp, 0, by simp, by simp⟩) (fun t₉ a b c f₉ g _ hpost' => ?_) (by decide +kernel)
  simp only [baseRV, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem,
    State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r4 ∉ linkRegs by decide),
    d3, d4, k₈.mem] at hpost'
  obtain h₉ := signStep hp h₇ (a.trans k₈.rd) (b.trans k₈.wr) (c.trans k₈.sp)
    (fun r hr => (g r hr).trans (k₈.pres r hr)) (k₈.mem ▸ f₉) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr (.inr (.inr (.inr (.inl rfl))))
      · exact .inl rfl
  obtain keepN : bytesAt t₉.mem (s.gpr .r9 + BitVec.ofNat 64 64) 32 = bytesAt t₇.mem (s.gpr .r9 + BitVec.ofNat 64 64) 32 := by
    rw [← k₈.mem]
    exact bytes_keep f₉ (by decide) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.oF.symm.sub_left F64 |>.sub_right (Region.sub_prefix (by decide))
      · exact hp.cF.symm.sub_left F64
  refine ⟨h₉, ?_, by rw [keepN, hpost], by rw [hpost', hpost]⟩
  -- The writes.
  obtain L64 : Region.Sub ⟨s.gpr .r9 + BitVec.ofNat 64 64, 32⟩ ⟨s.gpr .r9 + BitVec.ofNat 64 64, 128⟩ :=
    Region.sub_prefix (by decide)
  obtain L128 : Region.Sub ⟨s.gpr .r9 + BitVec.ofNat 64 128, 64⟩ ⟨s.gpr .r9 + BitVec.ofNat 64 64, 128⟩ := by
    have := Offset.sub (s.gpr .r9) (d := 128) (n := 64) (e := 64) (k := 128) (by decide) (by decide)
    exact this
  obtain g₅ : Frame [⟨s.gpr .r8, 8192⟩, ⟨s.gpr .r9 + BitVec.ofNat 64 64, 128⟩, below s.sp 48, ⟨s.gpr .r3, 32⟩]
      t₄.mem t₅.mem := f₅.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨_, by simp, L128⟩
    · exact ⟨below s.sp 48, by simp, by rw [h₄.sp]; exact fun _ h => h⟩
  obtain g₇ : Frame [⟨s.gpr .r8, 8192⟩, ⟨s.gpr .r9 + BitVec.ofNat 64 64, 128⟩, below s.sp 48, ⟨s.gpr .r3, 32⟩]
      t₅.mem t₇.mem := by
    rw [← k₆.mem]
    exact f₇.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, L64⟩
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  obtain g₉ : Frame [⟨s.gpr .r8, 8192⟩, ⟨s.gpr .r9 + BitVec.ofNat 64 64, 128⟩, below s.sp 48, ⟨s.gpr .r3, 32⟩]
      t₇.mem t₉.mem := by
    rw [← k₈.mem]
    exact f₉.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  exact (toL h.sp f₂).trans <| (toL h₂.sp f₃).trans <| (toL h₃.sp f₄).trans <| g₅.trans <| g₇.trans g₉

end VG.Proof.Ed25519.PPC64LE.Whole

end

end

/-! ### `Ed25519.PPC64LE.Whole.SignChallenge`, which only this module used -/

section

/-!
# `vg_ed25519_sign_expanded` on PPC64LE: the challenge, and `S`

`R` (in `out`), the copy of `pk` at `192(F)` and the message hashed into
`128(F)`, the digest reduced into the challenge at `96(F)` by a call of
`vg_ed25519_scalar_reduce`, and `S = (r + k s) mod L` into `out + 32` by a
call of `vg_ed25519_scalar_mul_add` (`signChallenge_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE.Whole VG.Proof.X25519.PPC64LE
open VG.Spec.Ed25519 (bytesAt)

/-- What the challenge's steps write. -/
abbrev chW (s : State) : List Region :=
  [⟨s.gpr .r8, 8192⟩, ⟨s.gpr .r9 + BitVec.ofNat 64 96, 96⟩, below s.sp 48, ⟨s.gpr .r3 + BitVec.ofNat 64 32, 32⟩]

theorem signChallenge_ok (C : ShaOK) {sn : Nat} {s t : State} (hp : SignPre sn s) (h : SignInv s t) {Rb Nb Sb Kb : List Byte}
    (hR : bytesAt t.mem (s.gpr .r3) 32 = Rb) (hN : bytesAt t.mem (s.gpr .r9 + BitVec.ofNat 64 64) 32 = Nb)
    (hS : bytesAt t.mem (s.gpr .r9) 32 = Sb) (hK : bytesAt t.mem (s.gpr .r9 + BitVec.ofNat 64 192) 32 = Kb) :
    WP isa signChallenge t fun t' => SignInv s t' ∧ bytesAt t'.mem (s.gpr .r3) 32 = Rb ∧
      bytesAt t'.mem (s.gpr .r3 + BitVec.ofNat 64 32) 32 =
        Spec.Ed25519.scalarMulAdd Nb (Spec.Ed25519.scalarReduce (Spec.Sha512.sha512 (Rb ++ Kb ++ msgB s))) Sb := by
  obtain hRl : Rb.length = 32 := by rw [← hR]; simp [bytesAt]
  obtain hKl : Kb.length = 32 := by rw [← hK]; simp [bytesAt]
  obtain hlen := sign_len hp
  obtain toL : ∀ {m m' : Mem} {sp : Addr}, sp = s.sp → Frame [⟨s.gpr .r8, 8192⟩, below sp 48] m m' →
      Frame (chW s) m m' := fun e hf => by subst e; exact hf.mono (by simp)
  obtain scW : ∀ {t : State}, SignInv s t → ∀ r ∈ [(⟨s.gpr .r8, 8192⟩ : Region), below t.sp 48], SignWr s r :=
    fun h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inl rfl
      · exact .inr (.inl (by rw [h.sp]))
  obtain F0 : Region.Sub ⟨s.gpr .r9 + BitVec.ofNat 64 0, 32⟩ ⟨s.gpr .r9, 288⟩ := Offset.sub_base _ (by decide)
  obtain F64 : Region.Sub ⟨s.gpr .r9 + BitVec.ofNat 64 64, 32⟩ ⟨s.gpr .r9, 288⟩ := Offset.sub_base _ (by decide)
  obtain F96 : Region.Sub ⟨s.gpr .r9 + BitVec.ofNat 64 96, 32⟩ ⟨s.gpr .r9, 288⟩ := Offset.sub_base _ (by decide)
  obtain F128 : Region.Sub ⟨s.gpr .r9 + BitVec.ofNat 64 128, 64⟩ ⟨s.gpr .r9, 288⟩ := Offset.sub_base _ (by decide)
  obtain F192 : Region.Sub ⟨s.gpr .r9 + BitVec.ofNat 64 192, 32⟩ ⟨s.gpr .r9, 288⟩ := Offset.sub_base _ (by decide)
  obtain O32 : Region.Sub ⟨s.gpr .r3, 32⟩ ⟨s.gpr .r3, 64⟩ := Region.sub_prefix (by decide)
  obtain O32' : Region.Sub ⟨s.gpr .r3 + BitVec.ofNat 64 32, 32⟩ ⟨s.gpr .r3, 64⟩ := Offset.sub_base _ (by decide)
  -- What the steps keep.
  obtain keep : ∀ {m m' : Mem} {p : Addr}, Frame (chW s) m m' → Region.Sub ⟨p, 32⟩ ⟨s.gpr .r3, 32⟩ ∨
      (∃ d, d + 32 ≤ 96 ∧ p = s.gpr .r9 + BitVec.ofNat 64 d) ∨ p = s.gpr .r9 + BitVec.ofNat 64 192 →
      bytesAt m' p 32 = bytesAt m p 32 := by
    intro m m' p hf hpr
    refine bytes_keep hf (by decide) fun r hr => ?_
    obtain hF : Region.Sub ⟨p, 32⟩ ⟨s.gpr .r9, 288⟩ ∨ Region.Sub ⟨p, 32⟩ ⟨s.gpr .r3, 32⟩ := by
      rcases hpr with h | ⟨d, hd, rfl⟩ | rfl
      · exact .inr h
      · exact .inl (Offset.sub_base _ (by omega_using [hd]))
      · exact .inl F192
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rcases hF with hF | hF
      · exact hp.cF.symm.sub_left hF
      · exact (hp.oC.sub_left O32).sub_left hF
    · rcases hpr with h | ⟨d, hd, rfl⟩ | rfl
      · exact (hp.oF.sub_left O32).sub_left h |>.sub_right (Offset.sub_base _ (by decide))
      · exact Offset.disjoint _ (.inl hd) (by omega_using [hd]) (by decide)
      · exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
    · rcases hF with hF | hF
      · exact hp.bF.symm.sub_left hF
      · exact (hp.bO.symm.sub_left O32).sub_left hF
    · rcases hF with hF | hF
      · exact hp.oF.symm.sub_left hF |>.sub_right O32'
      · exact ((Offset.base_disjoint _ (by decide) (by decide) : Region.Disjoint ⟨s.gpr .r3, 32⟩
          ⟨s.gpr .r3 + BitVec.ofNat 64 32, 32⟩)).sub_left hF
  obtain kR : ∀ {m m' : Mem}, Frame (chW s) m m' → bytesAt m' (s.gpr .r3) 32 = bytesAt m (s.gpr .r3) 32 :=
    fun hf => keep hf (.inl fun _ h => h)
  obtain kF : ∀ {m m' : Mem} {d : Nat}, Frame (chW s) m m' → d + 32 ≤ 96 →
      bytesAt m' (s.gpr .r9 + BitVec.ofNat 64 d) 32 = bytesAt m (s.gpr .r9 + BitVec.ofNat 64 d) 32 :=
    fun hf hd => keep hf (.inr (.inl ⟨_, hd, rfl⟩))
  unfold signChallenge
  refine WP.seq (hashInit_ok C (sr := .r24) (by decide) (h.regs _ (by decide)) (sign_env hp h)
    fun t₂ a b c f₂ g hr₂ => ?_)
  obtain h₂ := signStep hp h a b c g f₂ (scW h)
  obtain hOw : (⟨s.gpr .r3, 64⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  refine WP.seq (hashUpdate_ok C (sr := .r24) (src := .r20) (off := 0) (len := 32) (by decide) (by decide)
    (by decide) (by decide) (by decide) (h₂.regs _ (by decide)) (by rw [h₂.regs _ (by decide), BitVec.add_zero]; rfl)
    (Sets.li (d := .r4) (k := 0) (by decide)) (Sets.li (d := .r6) (k := 32) (by decide))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) rfl (sign_env hp h₂)
    (Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr, h₂.rd, h₂.wr]
      exact ⟨_, List.mem_append_right _ hOw, 0, by simp, by simp⟩)
    (hp.oC.sub_left O32) (by rw [h₂.sp]; exact hp.bO.sub_right O32) fun t₃ a b c f₃ g hr₃ => ?_)
  obtain h₃ := signStep hp h₂ a b c g f₃ (scW h₂)
  obtain e₂ : ∀ {p : Addr}, Region.Sub ⟨p, 32⟩ ⟨s.gpr .r3, 32⟩ ∨
      (∃ d, d + 32 ≤ 96 ∧ p = s.gpr .r9 + BitVec.ofNat 64 d) ∨ p = s.gpr .r9 + BitVec.ofNat 64 192 →
      bytesAt t₂.mem p 32 = bytesAt t.mem p 32 := fun hpr => keep (toL h.sp f₂) hpr
  obtain r₃ : Repr t₃.mem (s.gpr .r8) Rb := by
    have := hr₃ [] hr₂ rfl
    rwa [List.nil_append, e₂ (.inl fun _ h => h), hR] at this
  obtain e₃ : ∀ {p : Addr}, Region.Sub ⟨p, 32⟩ ⟨s.gpr .r3, 32⟩ ∨
      (∃ d, d + 32 ≤ 96 ∧ p = s.gpr .r9 + BitVec.ofNat 64 d) ∨ p = s.gpr .r9 + BitVec.ofNat 64 192 →
      bytesAt t₃.mem p 32 = bytesAt t.mem p 32 := fun hpr => (keep (toL h₂.sp f₃) hpr).trans (e₂ hpr)
  refine WP.seq (hashUpdate_ok C (sr := .r24) (src := .r25) (off := 192) (len := 32) (by decide) (by decide)
    (by decide) (by decide) (by decide) (h₃.regs _ (by decide)) (by rw [h₃.regs _ (by decide)]; rfl)
    (Sets.li (d := .r4) (k := 32) (by decide)) (Sets.li (d := .r6) (k := 32) (by decide))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) rfl (sign_env hp h₃)
    (Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨_, List.mem_append_right _ (sign_Fw hp h₃), 192, rfl, show 192 + 32 ≤ 288 by decide⟩)
    (hp.cF.symm.sub_left F192) (by rw [h₃.sp]; exact hp.bF.sub_right F192) fun t₄ a b c f₄ g hr₄ => ?_)
  obtain h₄ := signStep hp h₃ a b c g f₄ (scW h₃)
  obtain r₄ : Repr t₄.mem (s.gpr .r8) (Rb ++ Kb) := by
    have := hr₄ Rb r₃ (by rw [hRl])
    rwa [e₃ (.inr (.inr rfl)), hK] at this
  obtain e₄ : ∀ {p : Addr}, Region.Sub ⟨p, 32⟩ ⟨s.gpr .r3, 32⟩ ∨
      (∃ d, d + 32 ≤ 96 ∧ p = s.gpr .r9 + BitVec.ofNat 64 d) ∨ p = s.gpr .r9 + BitVec.ofNat 64 192 →
      bytesAt t₄.mem p 32 = bytesAt t.mem p 32 := fun hpr => (keep (toL h₃.sp f₄) hpr).trans (e₃ hpr)
  refine WP.seq (hashUpdate_ok C (sr := .r24) (src := .r22) (off := 0) (len := (s.gpr .r7).toNat) (by decide)
    (by decide) (by decide) (by decide) (by decide) (h₄.regs _ (by decide))
    (by rw [h₄.regs _ (by decide), BitVec.add_zero]; rfl)
    (Sets.li (d := .r4) (k := 64) (by decide)) (Sets.addi (d := .r6) (n := .r23) (k := 0) (by decide) (by decide))
    (fun _ _ _ => rfl) (fun g g' hg => by rw [hg .r23 (by decide) (by decide) (by decide)])
    (by rw [BitVec.add_zero, h₄.regs _ (by decide)]; rfl) (sign_env hp h₄) (sign_msg_cov hp h₄)
    hp.mC (by rw [h₄.sp]; exact hp.bM) fun t₅ a b c f₅ g hr₅ => ?_)
  obtain h₅ := signStep hp h₄ a b c g f₅ (scW h₄)
  obtain r₅ : Repr t₅.mem (s.gpr .r8) (Rb ++ Kb ++ msgB s) := by
    have := hr₅ (Rb ++ Kb) r₄ (by rw [List.length_append, hRl, hKl])
    rwa [sign_msg hp h₄] at this
  obtain e₅ : ∀ {p : Addr}, Region.Sub ⟨p, 32⟩ ⟨s.gpr .r3, 32⟩ ∨
      (∃ d, d + 32 ≤ 96 ∧ p = s.gpr .r9 + BitVec.ofNat 64 d) ∨ p = s.gpr .r9 + BitVec.ofNat 64 192 →
      bytesAt t₅.mem p 32 = bytesAt t.mem p 32 := fun hpr => (keep (toL h₄.sp f₅) hpr).trans (e₄ hpr)
  refine WP.seq (hashFinalize_ok C (sr := .r24) (f := .r25) (o := 128) (out := s.gpr .r9 + BitVec.ofNat 64 128)
    (vc := fun g => g .r23 + BitVec.ofNat 64 64)
    (by decide) (by decide) (by decide) (by decide) (by decide) (h₅.regs _ (by decide))
    (by rw [h₅.regs _ (by decide)]; rfl)
    (Sets.addi (d := .r4) (n := .r23) (k := 64) (by decide) (by decide)) (fun g g' hg => by rw [hg .r23 (by decide)])
    (sign_env hp h₅)
    (Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, sign_Fw hp h₅, 128, rfl, show 128 + 64 ≤ 288 by decide⟩)
    (hp.cF.symm.sub_left F128) (by rw [h₅.sp]; exact hp.bF.sub_right F128) fun t₆ a b c f₆ g hd₆ => ?_)
  obtain h₆ := signStep hp h₅ a b c g f₆ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl rfl
    · exact .inr (.inr (.inr (.inr (.inr ⟨128, 64, by decide, rfl⟩))))
    · exact .inr (.inl (by rw [h₅.sp])))
  obtain dg : bytesAt t₆.mem (s.gpr .r9 + BitVec.ofNat 64 128) 64 = Spec.Sha512.sha512 (Rb ++ Kb ++ msgB s) :=
    hd₆ _ r₅ (by rw [List.length_append, List.length_append, hRl, hKl, msgB_length]; omega_using [hlen])
      (by rw [h₅.regs _ (by decide), List.length_append, List.length_append, hRl, hKl, msgB_length, cnt_eq]; rfl)
  obtain f₆' : Frame (chW s) t₅.mem t₆.mem := f₆.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨⟨s.gpr .r9 + BitVec.ofNat 64 96, 96⟩, by simp,
        Offset.sub (s.gpr .r9) (d := 128) (n := 64) (e := 96) (k := 96) (by decide) (by decide)⟩
    · exact ⟨below s.sp 48, by simp, by rw [h₅.sp]; exact fun _ h => h⟩
  obtain e₆ : ∀ {p : Addr}, Region.Sub ⟨p, 32⟩ ⟨s.gpr .r3, 32⟩ ∨
      (∃ d, d + 32 ≤ 96 ∧ p = s.gpr .r9 + BitVec.ofNat 64 d) ∨ p = s.gpr .r9 + BitVec.ofNat 64 192 →
      bytesAt t₆.mem p 32 = bytesAt t.mem p 32 := fun hpr => (keep f₆' hpr).trans (e₅ hpr)
  obtain ce : ∀ (u : State) q, q ∉ linkRegs → ∀ rd wr, (u.callEntry.withRegions rd wr).gpr q = u.gpr q :=
    fun _ q hq _ _ => by rw [State.withRegions_gpr, State.callEntry_gpr _ hq]
  obtain hFw := sign_Fw hp h₆
  obtain hCw : (⟨s.gpr .r8, 8192⟩ : Region) ∈ t₆.wr := (sign_env hp h₆).w
  -- The challenge: `scalar_reduce`.
  unfold mov
  refine WP.seq (args3_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) fun t₇ k₇ c3 c4 c5 => ?_)
  rw [h₆.regs _ (by decide), signV_r25] at c3 c4
  rw [h₆.regs _ (by decide), BitVec.add_zero, signV_r24] at c5
  refine WP.seq (WP.call (k := reducePPC) reduce_ok' (rd := [⟨s.gpr .r9 + BitVec.ofNat 64 128, 64⟩])
    (wr := [⟨s.gpr .r9 + BitVec.ofNat 64 96, 32⟩, ⟨s.gpr .r8, 8192⟩])
    ⟨by rw [State.withRegions_rd, ce _ _ (by decide), c4],
      by rw [State.withRegions_wr, ce _ _ (by decide), ce _ _ (by decide), c3, c5],
      by rw [ce _ _ (by decide), ce _ _ (by decide), c3, c4]; exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide),
      by rw [ce _ _ (by decide), ce _ _ (by decide), c3, c5]; exact hp.cF.symm.sub_left F96,
      by rw [ce _ _ (by decide), ce _ _ (by decide), c4, c5]; exact hp.cF.symm.sub_left F128⟩
    (Covers.of_sub fun r hr => by
      rw [k₇.rd, k₇.wr]
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_append_right _ hFw, 128, rfl, show 128 + 64 ≤ 288 by decide⟩
      · exact ⟨_, List.mem_append_right _ hFw, 96, rfl, show 96 + 32 ≤ 288 by decide⟩
      · exact ⟨_, List.mem_append_right _ hCw, 0, by simp, by simp⟩)
    (Covers.of_sub fun r hr => by
      rw [k₇.wr]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, hFw, 96, rfl, show 96 + 32 ≤ 288 by decide⟩
      · exact ⟨_, hCw, 0, by simp, by simp⟩) (fun t₈ a b c f₈ g _ hpost => ?_) (by decide +kernel))
  simp only [reducePPC, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem,
    State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r4 ∉ linkRegs by decide),
    c3, c4, k₇.mem, dg] at hpost
  obtain h₈ := signStep hp h₆ (a.trans k₇.rd) (b.trans k₇.wr) (c.trans k₇.sp)
    (fun r hr => (g r hr).trans (k₇.pres r hr)) (k₇.mem ▸ f₈) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr (.inr (.inr (.inr (.inr ⟨96, 32, by decide, rfl⟩))))
      · exact .inl rfl
  obtain f₈' : Frame (chW s) t₆.mem t₈.mem := by
    rw [← k₇.mem]
    exact f₈.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨s.gpr .r9 + BitVec.ofNat 64 96, 96⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  obtain e₈ : ∀ {p : Addr}, Region.Sub ⟨p, 32⟩ ⟨s.gpr .r3, 32⟩ ∨
      (∃ d, d + 32 ≤ 96 ∧ p = s.gpr .r9 + BitVec.ofNat 64 d) ∨ p = s.gpr .r9 + BitVec.ofNat 64 192 →
      bytesAt t₈.mem p 32 = bytesAt t.mem p 32 := fun hpr => (keep f₈' hpr).trans (e₆ hpr)
  -- `S`: `scalar_mul_add`.
  refine WP.seq (args5_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) fun t₉ k₉ d3 d4 d5 d6 d7 => ?_)
  rw [h₈.regs _ (by decide), signV_r20] at d3
  rw [h₈.regs _ (by decide), signV_r25] at d4 d5
  rw [h₈.regs _ (by decide), signV_r25, BitVec.add_zero] at d6
  rw [h₈.regs _ (by decide), signV_r24, BitVec.add_zero] at d7
  obtain hOw' : (⟨s.gpr .r3, 64⟩ : Region) ∈ t₉.wr := by rw [k₉.wr, h₈.wr, hp.wr]; simp
  obtain hFw' : (⟨s.gpr .r9, 288⟩ : Region) ∈ t₉.wr := by rw [k₉.wr]; exact sign_Fw hp h₈
  obtain hCw' : (⟨s.gpr .r8, 8192⟩ : Region) ∈ t₉.wr := by rw [k₉.wr]; exact (sign_env hp h₈).w
  refine WP.call (k := mulAddPPC) mulAdd_ok'
    (rd := [⟨s.gpr .r9 + BitVec.ofNat 64 64, 32⟩, ⟨s.gpr .r9 + BitVec.ofNat 64 96, 32⟩, ⟨s.gpr .r9, 32⟩])
    (wr := [⟨s.gpr .r3 + BitVec.ofNat 64 32, 32⟩, ⟨s.gpr .r8, 8192⟩])
    ⟨by rw [State.withRegions_rd, ce _ _ (by decide), ce _ _ (by decide), ce _ _ (by decide), d4, d5, d6],
      by rw [State.withRegions_wr, ce _ _ (by decide), ce _ _ (by decide), d3, d7],
      by rw [ce _ _ (by decide), ce _ _ (by decide), d3, d7]; exact hp.oC.sub_left O32',
      by rw [ce _ _ (by decide), ce _ _ (by decide), d4, d7]; exact hp.cF.symm.sub_left F64,
      by rw [ce _ _ (by decide), ce _ _ (by decide), d5, d7]; exact hp.cF.symm.sub_left F96,
      by rw [ce _ _ (by decide), ce _ _ (by decide), d6, d7]
         exact hp.cF.symm.sub_left (Region.sub_prefix (by decide))⟩
    (Covers.of_sub fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_append_right _ hFw', 64, rfl, show 64 + 32 ≤ 288 by decide⟩
      · exact ⟨_, List.mem_append_right _ hFw', 96, rfl, show 96 + 32 ≤ 288 by decide⟩
      · exact ⟨_, List.mem_append_right _ hFw', 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ hOw', 32, rfl, show 32 + 32 ≤ 64 by decide⟩
      · exact ⟨_, List.mem_append_right _ hCw', 0, by simp, by simp⟩)
    (Covers.of_sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, hOw', 32, rfl, show 32 + 32 ≤ 64 by decide⟩
      · exact ⟨_, hCw', 0, by simp, by simp⟩) (fun t₁₀ a b c f₁₀ g _ hpost' => ?_) (by decide +kernel)
  simp only [mulAddPPC, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem,
    State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r4 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.r5 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r6 ∉ linkRegs by decide),
    d3, d4, d5, d6, k₉.mem] at hpost'
  obtain h₁₀ := signStep hp h₈ (a.trans k₉.rd) (b.trans k₉.wr) (c.trans k₉.sp)
    (fun r hr => (g r hr).trans (k₉.pres r hr)) (k₉.mem ▸ f₁₀) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr (.inr (.inr (.inl rfl)))
      · exact .inl rfl
  obtain f₁₀' : Frame (chW s) t₈.mem t₁₀.mem := by
    rw [← k₉.mem]
    exact f₁₀.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  refine ⟨h₁₀, by rw [kR f₁₀', e₈ (.inl fun _ h => h), hR], ?_⟩
  rw [hpost', e₈ (.inr (.inl ⟨64, by decide, rfl⟩)), hN, hpost,
    show s.gpr .r9 = s.gpr .r9 + BitVec.ofNat 64 0 from (BitVec.add_zero _).symm, e₈ (.inr (.inl ⟨0, by decide, rfl⟩)),
    ← show s.gpr .r9 = s.gpr .r9 + BitVec.ofNat 64 0 from (BitVec.add_zero _).symm, hS]

end VG.Proof.Ed25519.PPC64LE.Whole

end

end


/-!
# `vg_ed25519_sign_expanded` on PPC64LE, with its frame as an argument

The setup, the three phases and the restores (`signWith_wp`): `out` then
holds `R ‖ S`, RFC 8032's signature (`Proof.Ed25519.sign_pipeline`), given that
the first step leaves the seed's digest at `128(F)` and that `pk` is the seed's
public key. The first step copies the digest from `r4` (`signExpanded_wp`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE.Whole VG.Proof.X25519.PPC64LE
open VG.Spec.Ed25519 (bytesAt)

theorem signWith_wp (C : ShaOK) (B : BaseOk) {sn : Nat} {s : State} (hp : SignPre sn s) {digest : Prog isa}
    {seed : List Byte}
    (hd : ∀ t, SignInv s t → WP isa digest t fun t' => SignInv s t' ∧
      Frame [⟨s.gpr .r8, 8192⟩, ⟨s.gpr .r9, 192⟩, below s.sp 48] t.mem t'.mem ∧
      bytesAt t'.mem (s.gpr .r9 + BitVec.ofNat 64 128) 64 = Spec.Sha512.sha512 seed)
    (hpk : bytesAt s.mem (s.gpr .r5) 32 = Spec.Ed25519.publicKey seed) :
    WP isa (signWith digest) s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.lr = s.lr ∧
      bytesAt t.mem (s.gpr .r3) 64 = Spec.Ed25519.sign seed (msgB s) := by
  obtain F192 : Region.Sub ⟨s.gpr .r9 + BitVec.ofNat 64 192, 32⟩ ⟨s.gpr .r9, 288⟩ := Offset.sub_base _ (by decide)
  obtain F0 : Region.Sub ⟨s.gpr .r9, 32⟩ ⟨s.gpr .r9, 288⟩ := Region.sub_prefix (by decide)
  unfold signWith
  refine WP.seq (WP.mono_syms (signSetup_ok hp) fun t₁ ⟨h₁, hk₁⟩ sy₁ => ?_)
  refine WP.seq (WP.mono_syms (signExpandWith_ok hp (hd t₁ h₁)) fun t₂ ⟨h₂, f₂, hs₂, hp₂⟩ sy₂ => ?_)
  obtain hk₂ : bytesAt t₂.mem (s.gpr .r9 + BitVec.ofNat 64 192) 32 = bytesAt s.mem (s.gpr .r5) 32 := by
    rw [← hk₁]
    exact bytes_keep f₂ (by decide) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.cF.symm.sub_left F192
      · exact Offset.disjoint_base _ (by decide) (by decide)
      · exact hp.bF.symm.sub_left F192
  refine WP.seq (WP.mono (signNonce_ok C B hp h₂ hp₂ (by rw [sy₂, sy₁])) fun t₃ ⟨h₃, f₃, hn₃, hr₃⟩ => ?_)
  obtain keep₃ : ∀ {p : Addr}, Region.Sub ⟨p, 32⟩ ⟨s.gpr .r9, 288⟩ →
      (Region.Disjoint ⟨p, 32⟩ ⟨s.gpr .r9 + BitVec.ofNat 64 64, 128⟩) →
      bytesAt t₃.mem p 32 = bytesAt t₂.mem p 32 := fun hs hd =>
    bytes_keep f₃ (by decide) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hp.cF.symm.sub_left hs
      · exact hd
      · exact hp.bF.symm.sub_left hs
      · exact (hp.oF.symm.sub_left hs).sub_right (Region.sub_prefix (by decide))
  obtain hk₃ := (keep₃ F192 (Offset.disjoint _ (.inr (by decide)) (by decide) (by decide))).trans hk₂
  obtain hs₃ := (keep₃ F0 (Offset.base_disjoint _ (by decide) (by decide))).trans hs₂
  refine WP.seq (WP.mono (signChallenge_ok C hp h₃ hr₃ hn₃ hs₃ hk₃) fun t₄ ⟨h₄, hR, hS⟩ => ?_)
  obtain hFw : (⟨s.gpr .r9, 288⟩ : Region) ∈ t₄.rd ++ t₄.wr := List.mem_append_right _ (sign_Fw hp h₄)
  obtain hrl : ∀ p ∈ restoreList 224 signRegs, p.2 + 8 ≤ 288 := by decide
  refine restore_ok h₄ (by decide) (h₄.regs _ (by decide)) (by decide) (by decide) (by decide) (by decide)
    (fun p hp' => in_base hFw (hrl p hp') (by have := hrl p hp'; omega_using [this]))
    fun t₅ g₅ sp₅ lr₅ m₅ _ => ⟨g₅, sp₅, lr₅, ?_⟩
  rw [m₅, Proof.Ed25519.signatureBytes_split, hR, hS]
  exact Proof.Ed25519.sign_pipeline _ _ _ hpk

/-- `vg_ed25519_sign_expanded`: the signature of every seed whose digest is at `r4` and whose
public key is at `r5`. -/
theorem signExpanded_wp (C : ShaOK) (B : BaseOk) {s : State} (hp : SignPre 64 s) {seed : List Byte}
    (hs : bytesAt s.mem (s.gpr .r4) 64 = Spec.Sha512.sha512 seed)
    (hpk : bytesAt s.mem (s.gpr .r5) 32 = Spec.Ed25519.publicKey seed) :
    WP isa signExpanded s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.lr = s.lr ∧
      bytesAt t.mem (s.gpr .r3) 64 = Spec.Ed25519.sign seed (msgB s) :=
  signWith_wp C B hp (fun _ h => WP.mono (signCopy_ok hp h) fun _ ⟨a, b, c⟩ => ⟨a, b, c.trans hs⟩) hpk

end VG.Proof.Ed25519.PPC64LE.Whole
