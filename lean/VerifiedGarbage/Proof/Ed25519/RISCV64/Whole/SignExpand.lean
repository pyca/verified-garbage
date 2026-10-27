module

public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.SignSetup
import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Prune
import VerifiedGarbage.Proof.Ed25519.Signing
import VerifiedGarbage.Proof.Ed25519.VerifyBytes
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# `vg_ed25519_sign_cached` on RISCV64: the secret scalar and the nonce's prefix

The seed hashed into `128(F)`, the first half of the digest pruned into
`0(F)` and its second half copied to `32(F)` (`signExpand_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64.Whole

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64.Whole VG.Proof.X25519.RISCV64
open VG.Spec.Ed25519 (bytesAt decodeLE encodeLE)

/-- The seed's digest. -/
abbrev seedH (s : State) : List Byte := Spec.Sha512.sha512 (bytesAt s.mem (s.gpr .a1) 32)

theorem sign_env {s t : State} (hp : SignPre s) (h : SignInv s t) : ScEnv (s.gpr .a5) t :=
  ⟨by rw [h.wr, hp.wr]; simp, by rw [h.sp]; exact hp.spal, by rw [h.sp]; exact hp.sp, by rw [h.sp]; exact hp.bC⟩

theorem sign_Fw {s t : State} (hp : SignPre s) (h : SignInv s t) : (⟨s.gpr .a6, 288⟩ : Region) ∈ t.wr := by
  rw [h.wr, hp.wr]; simp

theorem sign_inF {s t : State} (hp : SignPre s) (h : SignInv s t) {d : Nat} (hd : d + 8 ≤ 288) :
    InRegions t.wr (s.gpr .a6 + BitVec.ofNat 64 d) 8 := in_base (sign_Fw hp h) hd (by omega_arith)

theorem sign_inF' {s t : State} (hp : SignPre s) (h : SignInv s t) {d : Nat} (hd : d + 8 ≤ 288) :
    InRegions (t.rd ++ t.wr) (s.gpr .a6 + BitVec.ofNat 64 d) 8 :=
  in_base (List.mem_append_right _ (sign_Fw hp h)) hd (by omega_arith)

/-- An input, while the body runs. -/
theorem sign_input {s t : State} (h : SignInv s t) {p : Addr} {n : Nat} (hn : n < 2 ^ 64)
    (hO : Region.Disjoint ⟨p, n⟩ ⟨s.gpr .a0, 64⟩) (hC : Region.Disjoint ⟨p, n⟩ ⟨s.gpr .a5, 8192⟩)
    (hF : Region.Disjoint ⟨p, n⟩ ⟨s.gpr .a6, 288⟩) (hB : Region.Disjoint ⟨p, n⟩ (below s.sp 208)) :
    bytesAt t.mem p n = bytesAt s.mem p n :=
  bytes_keep h.frame hn fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hO
    · exact hC
    · exact hF
    · exact hB

/-- A region of the frame kept by steps that write within `[F, F + 192)`, the scratch space and
the callees' frames. -/
theorem keep_hi {s : State} (hp : SignPre s) {d n : Nat} (hd : 192 ≤ d) (hdn : d + n ≤ 288) :
    ∀ r ∈ [(⟨s.gpr .a5, 8192⟩ : Region), ⟨s.gpr .a6, 192⟩, below s.sp 208],
      Region.Disjoint ⟨s.gpr .a6 + BitVec.ofNat 64 d, n⟩ r := by
  have hs : Region.Sub ⟨s.gpr .a6 + BitVec.ofNat 64 d, n⟩ ⟨s.gpr .a6, 288⟩ := Offset.sub_base _ hdn
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.cF.symm.sub_left hs
  · exact Offset.disjoint_base _ hd (by omega_arith)
  · exact hp.bF.symm.sub_left hs

theorem signExpand_ok (C : ShaOK) {s t : State} (hp : SignPre s) (h : SignInv s t) :
    WP isa signExpand t fun t' => SignInv s t' ∧
      Frame [⟨s.gpr .a5, 8192⟩, ⟨s.gpr .a6, 192⟩, below s.sp 208] t.mem t'.mem ∧
      bytesAt t'.mem (s.gpr .a6) 32 = encodeLE 32 (Spec.Ed25519.prune (seedH s)) ∧
      bytesAt t'.mem (s.gpr .a6 + BitVec.ofNat 64 32) 32 = (seedH s).drop 32 := by
  have hS : (⟨s.gpr .a1, 32⟩ : Region) ∈ s.rd := by rw [hp.rd]; simp
  -- Writes of the scratch space and the callees' frames, into the frame's list.
  have toL : ∀ {m m' : Mem} {sp : Addr}, sp = s.sp → Frame [⟨s.gpr .a5, 8192⟩, below sp 208] m m' →
      Frame [⟨s.gpr .a5, 8192⟩, ⟨s.gpr .a6, 192⟩, below s.sp 208] m m' := fun e hf => by
    subst e; exact hf.mono (by simp)
  unfold signExpand
  refine WP.seq (hashInit_ok C (sr := .s10) (h.regs _ (by decide)) (sign_env hp h)
    fun t₂ a b c f₂ g hr₂ => ?_)
  have h₂ := signStep hp h a b c g f₂ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inl rfl
    · exact .inr (.inl (by rw [h.sp])))
  refine WP.seq (hashUpdate_ok C (sr := .s10) (src := .s1) (off := 0) (len := 32) (by decide)
    (by decide) (by decide) (h₂.regs _ (by decide)) (by rw [h₂.regs _ (by decide), BitVec.add_zero]; rfl)
    (Sets.li (d := .a1) (k := 0) (by decide)) (Sets.li (d := .a3) (k := 32) (by decide))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) rfl (sign_env hp h₂)
    (fun a n hi => by obtain ⟨r, hr, hc⟩ := hi; rw [h₂.rd]; exact ⟨r, List.mem_append_left _ (by
      rw [List.mem_singleton.mp hr]; exact hS), hc⟩)
    hp.sC (by rw [h₂.sp]; exact hp.bS) fun t₃ a b c f₃ g hr₃ => ?_)
  have h₃ := signStep hp h₂ a b c g f₃ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inl rfl
    · exact .inr (.inl (by rw [h₂.sp])))
  have r₃ : Repr t₃.mem (s.gpr .a5) (bytesAt s.mem (s.gpr .a1) 32) := by
    have := hr₃ [] hr₂ rfl
    rwa [List.nil_append, sign_input h₂ (by decide) hp.oS.symm hp.sC hp.sF hp.bS.symm] at this
  have F128 : Region.Sub ⟨s.gpr .a6 + BitVec.ofNat 64 128, 64⟩ ⟨s.gpr .a6, 288⟩ := Offset.sub_base _ (by decide)
  refine WP.seq (hashFinalize_ok C (sr := .s10) (f := .s11) (o := 128) (out := s.gpr .a6 + BitVec.ofNat 64 128)
    (by decide) (by decide) (by decide) (h₃.regs _ (by decide))
    (by rw [h₃.regs _ (by decide)]; rfl)
    (Sets.li (d := .a1) (k := 32) (by decide)) (fun _ _ _ => rfl) (sign_env hp h₃)
    (Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, sign_Fw hp h₃, 128, rfl, show 128 + 64 ≤ 288 by decide⟩)
    (hp.cF.symm.sub_left F128) (by rw [h₃.sp]; exact hp.bF.sub_right F128) fun t₄ a b c f₄ g hd₄ => ?_)
  have h₄ := signStep hp h₃ a b c g f₄ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl rfl
    · exact .inr (.inr (.inr (.inr (.inr ⟨128, 64, by decide, rfl⟩))))
    · exact .inr (.inl (by rw [h₃.sp])))
  have dg : bytesAt t₄.mem (s.gpr .a6 + BitVec.ofNat 64 128) 64 = seedH s :=
    hd₄ _ r₃ (by simp [bytesAt]) (by simp [bytesAt])
  -- The pruning, and the copy of the second half.
  refine prune_ok (f := .s11) (F := s.gpr .a6) (d := 128) (o := 0) (by decide) (h₄.regs _ (by decide)) hp.alF
    (by decide) (by decide) (by decide) (fun k hk => sign_inF' hp h₄ (by omega_arith)) (fun k hk => sign_inF hp h₄ (by omega_arith))
    fun u hu hfu hpr => ?_
  have hu' : SignInv s u := signStep hp h₄ hu.rd hu.wr hu.sp
    (fun r hr => hu.gpr r (by revert hr; cases r <;> decide)) hfu fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inr (.inr (.inr (.inr (.inr ⟨0, 32, by decide, rfl⟩))))
  rw [← List.append_nil (copy32 .s11 160 32)]
  refine copy_ok (A := s.gpr .a6) (B := s.gpr .a6) (da := fun k => 160 + 8 * k) (db := fun k => 32 + 8 * k)
    (R := ⟨s.gpr .a6 + BitVec.ofNat 64 32, 32⟩) (by decide) (by decide)
    (hu'.regs _ (by decide)) (hu'.regs _ (by decide)) (fun k hk => ⟨by omega_arith, Spill.al8 hp.alF (by omega_arith)⟩)
    (fun k hk => ⟨by omega_arith, Spill.al8 hp.alF (by omega_arith)⟩) (fun k hk => sign_inF' hp hu' (by omega_arith)) (fun k hk => sign_inF hp hu' (by omega_arith))
    (fun k hk => Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))
    (fun i hi j hj => Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith))
    (fun i hi j hj hij => Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) fun v hv hfv hw => WP.block_nil ?_
  have hv' : SignInv s v := signStep hp hu' hv.rd hv.wr hv.sp
    (fun r hr => hv.gpr r (by revert hr; cases r <;> decide)) hfv fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inr (.inr (.inr (.inr (.inr ⟨32, 32, by decide, rfl⟩))))
  have F0 : Region.Sub ⟨s.gpr .a6 + BitVec.ofNat 64 0, 32⟩ ⟨s.gpr .a6, 192⟩ := Offset.sub_base _ (by decide)
  have F32 : Region.Sub ⟨s.gpr .a6 + BitVec.ofNat 64 32, 32⟩ ⟨s.gpr .a6, 192⟩ := Offset.sub_base _ (by decide)
  refine ⟨hv', ?_, ?_, ?_⟩
  · -- The writes: the hashes', the scalar's and the prefix's.
    refine (toL h.sp f₂).trans <| (toL h₂.sp f₃).trans <| (f₄.sub fun r hr => ?_).trans <|
      (hfu.sub fun r hr => ?_).trans (hfv.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨⟨s.gpr .a6, 192⟩, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨below s.sp 208, by simp, by rw [h₃.sp]; exact fun _ h => h⟩
    · rw [List.mem_singleton.mp hr]; exact ⟨_, by simp, F0⟩
    · rw [List.mem_singleton.mp hr]; exact ⟨_, by simp, F32⟩
  · have e₁ : bytesAt v.mem (s.gpr .a6) 32 = bytesAt u.mem (s.gpr .a6) 32 :=
      bytes_keep hfv (by decide) fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.base_disjoint _ (by decide) (by decide)
    have hdec : decodeLE (bytesAt u.mem (s.gpr .a6) 32) = Spec.Ed25519.prune (seedH s) := by
      have := hpr
      rwa [BitVec.add_zero, dg] at this
    rw [e₁, Proof.Ed25519.bytesAt_encodeLE, hdec]
  · have e₁ : bytesAt v.mem (s.gpr .a6 + BitVec.ofNat 64 32) 32 =
        bytesAt u.mem (s.gpr .a6 + BitVec.ofNat 64 160) 32 :=
      bytes32_of_words fun k hk => by rw [Offset.add_add, Offset.add_add]; exact hw k hk
    have e₂ : bytesAt u.mem (s.gpr .a6 + BitVec.ofNat 64 160) 32 =
        bytesAt t₄.mem (s.gpr .a6 + BitVec.ofNat 64 160) 32 :=
      bytes_keep hfu (by decide) fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
    rw [e₁, e₂, show s.gpr .a6 + BitVec.ofNat 64 160 = s.gpr .a6 + BitVec.ofNat 64 128 + BitVec.ofNat 64 32 by
      rw [Offset.add_add], ← Proof.Ed25519.signatureBytes_drop, dg]

end VG.Proof.Ed25519.RISCV64.Whole
