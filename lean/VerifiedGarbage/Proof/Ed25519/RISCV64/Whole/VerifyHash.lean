module

public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Common
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Frame
public import VerifiedGarbage.Proof.Ed25519.RISCV64.ScalarVerified
import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Prune
import VerifiedGarbage.Proof.Ed25519.Challenge
import VerifiedGarbage.Proof.Ed25519.VerifyBytes
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# `vg_ed25519_verify` on RISC-V: the challenge

`pk` in `a0`, the message in `a1` (`len` in `a2`), the signature in `a3`,
`scratch` in `a4` and the frame `F` (272 bytes) in `a5`. The registers
saved at `224(F)`, the signature copied to `128(F)` and `pk` to `192(F)`,
`R ‖ A ‖ M` hashed into `64(F)` (`R` and `A` from their copies), the digest
reduced into `0(F)` by a call of `vg_ed25519_scalar_reduce` and its upper
half zeroed, and the arguments of `verify_equation` set, the copies its
`pk` and signature (`verifyHash_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64.Whole

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64.Whole VG.Proof.X25519.RISCV64
open VG.Spec.Ed25519 (bytesAt)

/-- The message. -/
abbrev vmsgR (s : State) : Region := ⟨s.gpr .a1, (s.gpr .a2).toNat⟩

/-- The precondition, by register. -/
structure VerPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .a0, 32⟩, vmsgR s, ⟨s.gpr .a3, 64⟩]
  wr : s.wr = [⟨s.gpr .a4, 8192⟩, ⟨s.gpr .a5, 272⟩]
  alC : (s.gpr .a4).toNat % 8 = 0
  alF : (s.gpr .a5).toNat % 8 = 0
  pC : Region.Disjoint ⟨s.gpr .a0, 32⟩ ⟨s.gpr .a4, 8192⟩
  pF : Region.Disjoint ⟨s.gpr .a0, 32⟩ ⟨s.gpr .a5, 272⟩
  mC : Region.Disjoint (vmsgR s) ⟨s.gpr .a4, 8192⟩
  mF : Region.Disjoint (vmsgR s) ⟨s.gpr .a5, 272⟩
  sC : Region.Disjoint ⟨s.gpr .a3, 64⟩ ⟨s.gpr .a4, 8192⟩
  sF : Region.Disjoint ⟨s.gpr .a3, 64⟩ ⟨s.gpr .a5, 272⟩
  cF : Region.Disjoint ⟨s.gpr .a4, 8192⟩ ⟨s.gpr .a5, 272⟩
  spal : s.sp.toNat % 16 = 0
  sp : 208 ≤ s.sp.toNat
  bP : (below s.sp 208).Disjoint ⟨s.gpr .a0, 32⟩
  bM : (below s.sp 208).Disjoint (vmsgR s)
  bS : (below s.sp 208).Disjoint ⟨s.gpr .a3, 64⟩
  bC : (below s.sp 208).Disjoint ⟨s.gpr .a4, 8192⟩
  bF : (below s.sp 208).Disjoint ⟨s.gpr .a5, 272⟩

/-- What the body may write. -/
abbrev verW (s : State) : List Region := [⟨s.gpr .a4, 8192⟩, ⟨s.gpr .a5, 272⟩, below s.sp 208]

/-- The values in `s7`–`s10`. -/
def verV (s : State) : Reg → BitVec 64
  | .s7 => s.gpr .a1 | .s8 => s.gpr .a2 | .s9 => s.gpr .a4 | .s10 => s.gpr .a5 | _ => 0

abbrev VerInv (s : State) : State → Prop := Inv s (s.gpr .a5) 224 verifyRegs (verV s) (verW s)

theorem verifyRegs_pres : ∀ r ∈ verifyRegs, r ∈ preserved := by decide

theorem verV_s7 (s : State) : verV s .s7 = s.gpr .a1 := rfl
theorem verV_s8 (s : State) : verV s .s8 = s.gpr .a2 := rfl
theorem verV_s9 (s : State) : verV s .s9 = s.gpr .a4 := rfl
theorem verV_s10 (s : State) : verV s .s10 = s.gpr .a5 := rfl

/-- The regions a step may write: the scratch space, the callees' frames, or the frame below the
slots. -/
def VerWr (s : State) (r : Region) : Prop :=
  r = ⟨s.gpr .a4, 8192⟩ ∨ r = below s.sp 208 ∨ ∃ d n, d + n ≤ 224 ∧ r = ⟨s.gpr .a5 + BitVec.ofNat 64 d, n⟩

theorem verStep {s t t' : State} (hp : VerPre s) (h : VerInv s t) (hrd : t'.rd = t.rd)
    (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp) (hg : ∀ r ∈ preserved, t'.gpr r = t.gpr r) {Wc : List Region}
    (hf : Frame Wc t.mem t'.mem) (hW : ∀ r ∈ Wc, VerWr s r) : VerInv s t' := by
  have hs : Region.Sub (slotArea (s.gpr .a5) 224 verifyRegs) ⟨s.gpr .a5, 272⟩ := Offset.sub_base _ (by decide)
  refine Inv.step h verifyRegs_pres hrd hwr hsp hg hf (fun r hr => ?_) fun r hr => ?_
  · rcases hW r hr with rfl | rfl | ⟨d, n, hdn, rfl⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨⟨s.gpr .a5, 272⟩, by simp, Offset.sub_base _ (by omega)⟩
  · rcases hW r hr with rfl | rfl | ⟨d, n, hdn, rfl⟩
    · exact hp.cF.symm.sub_left hs
    · exact hp.bF.symm.sub_left hs
    · exact Offset.disjoint _ (.inr hdn) (by decide) (by omega)

/-- An input, while the body runs. -/
theorem ver_input {s t : State} (h : VerInv s t) {p : Addr} {n : Nat} (hn : n < 2 ^ 64)
    (hC : Region.Disjoint ⟨p, n⟩ ⟨s.gpr .a4, 8192⟩) (hF : Region.Disjoint ⟨p, n⟩ ⟨s.gpr .a5, 272⟩)
    (hB : Region.Disjoint ⟨p, n⟩ (below s.sp 208)) : bytesAt t.mem p n = bytesAt s.mem p n :=
  bytes_keep h.frame hn fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hC
    · exact hF
    · exact hB

theorem ver_env {s t : State} (hp : VerPre s) (h : VerInv s t) : ScEnv (s.gpr .a4) t :=
  ⟨by rw [h.wr, hp.wr]; simp, by rw [h.sp]; exact hp.spal, by rw [h.sp]; exact hp.sp, by rw [h.sp]; exact hp.bC⟩

theorem ver_Fw {s t : State} (hp : VerPre s) (h : VerInv s t) : (⟨s.gpr .a5, 272⟩ : Region) ∈ t.wr := by
  rw [h.wr, hp.wr]; simp

/-- The setup: the registers saved, the pointers moved to `s7`–`s10`, the signature and `pk`
copied. -/
theorem verSetup_ok {s : State} (hp : VerPre s) :
    WP isa (.block (saveRegs .a5 224 verifyRegs ++
      ([mov .s7 .a1, mov .s8 .a2, mov .s9 .a4, mov .s10 .a5] ++ copyIn .a3 .s10 128 64 ++ copyIn .a0 .s10 192)))
      s fun t => VerInv s t ∧
        bytesAt t.mem (s.gpr .a5 + BitVec.ofNat 64 128) 64 = bytesAt s.mem (s.gpr .a3) 64 ∧
        bytesAt t.mem (s.gpr .a5 + BitVec.ofNat 64 192) 32 = bytesAt s.mem (s.gpr .a0) 32 := by
  have hF : (⟨s.gpr .a5, 272⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hsl : ∀ p ∈ slots 224 verifyRegs, p.2 + 8 ≤ 272 := by decide
  refine save_ok hp.alF (by decide) (by decide)
    (fun p hp' => in_base hF (hsl p hp') (by have := hsl p hp'; omega)) fun u hu hsv hfr => ?_
  unfold mov
  simp only [List.cons_append, List.nil_append]
  refine wp_mv fun u₁ h₁ => wp_mv fun u₂ h₂ => wp_mv fun u₃ h₃ => wp_mv fun u₄ h₄ => ?_
  have m₄ : u₄.mem = u.mem := by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  have g₄ : ∀ r, r ∉ verifyRegs → u₄.gpr r = u.gpr r := fun r hr => by
    simp only [verifyRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨a, b, c, d⟩ := hr
    rw [h₄.other _ d, h₃.other _ c, h₂.other _ b, h₁.other _ a]
  have gu : ∀ r, u.gpr r = s.gpr r := fun r => hu.gpr r (by simp)
  have rd₄ : u₄.rd = s.rd := by rw [h₄.rd, h₃.rd, h₂.rd, h₁.rd, hu.rd]
  have wr₄ : u₄.wr = s.wr := by rw [h₄.wr, h₃.wr, h₂.wr, h₁.wr, hu.wr]
  have sp₄ : u₄.sp = s.sp := by rw [h₄.sp, h₃.sp, h₂.sp, h₁.sp, hu.sp]
  have e10 : u₄.gpr .s10 = s.gpr .a5 := by rw [h₄.gpr, h₃.other _ (by decide), h₂.other _ (by decide),
    h₁.other _ (by decide), gu]
  have hS : (⟨s.gpr .a3, 64⟩ : Region) ∈ s.rd := by rw [hp.rd]; simp
  have hP : (⟨s.gpr .a0, 32⟩ : Region) ∈ s.rd := by rw [hp.rd]; simp
  -- The signature, then `pk`.
  refine copyIn_ok (P := s.gpr .a3) (F := s.gpr .a5) (o := 128) (n := 64) (by decide) (by decide)
    (by rw [g₄ _ (by decide), gu]) e10 (by decide)
    (fun i hi => by rw [rd₄, wr₄]; exact in_base (List.mem_append_left _ hS) (by omega) (by omega))
    (fun i hi => by rw [wr₄]; exact in_base hF (by omega) (by omega))
    (hp.sF.sub_right (Offset.sub_base _ (by decide))) fun v hv hfv hbv => ?_
  rw [← List.append_nil (copyIn .a0 .s10 192)]
  refine copyIn_ok (P := s.gpr .a0) (F := s.gpr .a5) (o := 192) (n := 32) (by decide) (by decide)
    (by rw [hv.gpr _ (by decide), g₄ _ (by decide), gu]) (by rw [hv.gpr _ (by decide), e10]) (by decide)
    (fun i hi => by rw [hv.rd, hv.wr, rd₄, wr₄]; exact in_base (List.mem_append_left _ hP) (by omega) (by omega))
    (fun i hi => by rw [hv.wr, wr₄]; exact in_base hF (by omega) (by omega))
    (hp.pF.sub_right (Offset.sub_base _ (by decide))) fun t ht hft hbt => WP.block_nil ?_
  have F128 : Region.Sub ⟨s.gpr .a5 + BitVec.ofNat 64 128, 64⟩ ⟨s.gpr .a5, 272⟩ := Offset.sub_base _ (by decide)
  have F192 : Region.Sub ⟨s.gpr .a5 + BitVec.ofNat 64 192, 32⟩ ⟨s.gpr .a5, 272⟩ := Offset.sub_base _ (by decide)
  have fin : Frame [⟨s.gpr .a5, 272⟩] s.mem t.mem :=
    (hfr.sub fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact ⟨⟨s.gpr .a5, 272⟩, by simp, Offset.sub_base _ (by decide)⟩).trans
      ((by rw [m₄] at hfv; exact hfv.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, by simp, F128⟩ :
        Frame [⟨s.gpr .a5, 272⟩] u.mem v.mem).trans
        (hft.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, by simp, F192⟩))
  have keepIn : ∀ {p : Addr} {n : Nat}, n < 2 ^ 64 → Region.Disjoint ⟨p, n⟩ ⟨s.gpr .a5, 272⟩ →
      bytesAt t.mem p n = bytesAt s.mem p n := fun hn hd =>
    bytes_keep fin hn fun r hr => by rw [List.mem_singleton.mp hr]; exact hd
  refine ⟨⟨by rw [ht.rd, hv.rd, rd₄], by rw [ht.wr, hv.wr, wr₄], by rw [ht.sp, hv.sp, sp₄], fun r hr => ?_,
    fun r hr hn => ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [ht.gpr r (by revert hr; decide +revert), hv.gpr r (by revert hr; decide +revert)]
    simp only [verifyRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide), h₁.gpr, gu]; rfl
    · rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.gpr, h₁.other _ (by decide), gu]; rfl
    · rw [h₄.other _ (by decide), h₃.gpr, h₂.other _ (by decide), h₁.other _ (by decide), gu]; rfl
    · rw [e10]; rfl
  · have h5 : r ∉ [Reg.a5] := by
      simp only [List.mem_singleton]; intro e; rw [e] at hr; exact absurd hr (by decide)
    rw [ht.gpr r h5, hv.gpr r h5, g₄ r hn, gu r]
  · refine (hsv.frame_in (slots_in 224 verifyRegs) (m₄ ▸ hfv) fun r hr => ?_).frame_in (slots_in 224 verifyRegs)
      hft fun r hr => ?_
    · rw [List.mem_singleton.mp hr]
      exact (Offset.disjoint _ (.inr (by decide)) (by decide) (by decide))
    · rw [List.mem_singleton.mp hr]
      exact (Offset.disjoint _ (.inr (by decide)) (by decide) (by decide))
  · exact fin.mono (by simp)
  · rw [bytes_keep hft (by decide) fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide), hbv, m₄]
    exact bytes_keep hfr (by decide) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (hp.sF.sub_right (Offset.sub_base _ (by decide)))
  · rw [hbt]
    have e : bytesAt v.mem (s.gpr .a0) 32 = bytesAt s.mem (s.gpr .a0) 32 := by
      rw [bytes_keep hfv (by decide) fun r hr => by
          rw [List.mem_singleton.mp hr]; exact hp.pF.sub_right F128, m₄]
      exact bytes_keep hfr (by decide) fun r hr => by
        rw [List.mem_singleton.mp hr]; exact (hp.pF.sub_right (Offset.sub_base _ (by decide)))
    exact e

/-- The message's bytes, and `verify`'s challenge. -/
abbrev vmsgB (s : State) : List Byte := bytesAt s.mem (s.gpr .a1) (s.gpr .a2).toNat

abbrev vChallenge (s : State) : List Byte :=
  Spec.Ed25519.encodeLE 64 (Spec.Ed25519.decodeLE (Spec.Sha512.sha512
    (bytesAt s.mem (s.gpr .a3) 32 ++ bytesAt s.mem (s.gpr .a0) 32 ++ vmsgB s)) % Spec.Ed25519.L)

/-- After the challenge: the arguments of `verify_equation`, the copies of `pk` and the signature
its own. -/
structure VerArgs (s t : State) : Prop where
  inv : VerInv s t
  a0 : t.gpr .a0 = s.gpr .a5 + BitVec.ofNat 64 192
  a1 : t.gpr .a1 = s.gpr .a5 + BitVec.ofNat 64 128
  a2 : t.gpr .a2 = s.gpr .a5
  a3 : t.gpr .a3 = s.gpr .a4
  ch : bytesAt t.mem (s.gpr .a5) 64 = vChallenge s
  pk : bytesAt t.mem (s.gpr .a5 + BitVec.ofNat 64 192) 32 = bytesAt s.mem (s.gpr .a0) 32
  sig : bytesAt t.mem (s.gpr .a5 + BitVec.ofNat 64 128) 64 = bytesAt s.mem (s.gpr .a3) 64

/-- The copies, through steps that write only the scratch space and the callees' frames. -/
theorem copies_keep {s : State} (hp : VerPre s) {m m' : Mem} {sp : Addr} (hsp : sp = s.sp)
    (hf : Frame [⟨s.gpr .a4, 8192⟩, below sp 208] m m') {d n : Nat} (hd : 128 ≤ d) (hdn : d + n ≤ 224) :
    bytesAt m' (s.gpr .a5 + BitVec.ofNat 64 d) n = bytesAt m (s.gpr .a5 + BitVec.ofNat 64 d) n := by
  subst hsp
  have hs : Region.Sub ⟨s.gpr .a5 + BitVec.ofNat 64 d, n⟩ ⟨s.gpr .a5, 272⟩ := Offset.sub_base _ (by omega)
  exact bytes_keep hf (by omega) fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.cF.symm.sub_left hs
    · exact hp.bF.symm.sub_left hs

theorem verifyHash_ok (C : ShaOK) {s : State} (hp : VerPre s) : WP isa verifyHash s (VerArgs s) := by
  have hlen : (s.gpr .a2).toNat + 8192 ≤ 2 ^ 64 := len_add_le (Nat.le_of_lt (s.gpr .a2).isLt) (by decide) hp.mC
  have scW : ∀ {t : State}, VerInv s t → ∀ r ∈ [(⟨s.gpr .a4, 8192⟩ : Region), below t.sp 208], VerWr s r :=
    fun h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inl rfl
      · exact .inr (.inl (by rw [h.sp]))
  have F0 : Region.Sub ⟨s.gpr .a5, 32⟩ ⟨s.gpr .a5, 272⟩ := Region.sub_prefix (by decide)
  have F64 : Region.Sub ⟨s.gpr .a5 + BitVec.ofNat 64 64, 64⟩ ⟨s.gpr .a5, 272⟩ := Offset.sub_base _ (by decide)
  have F128 : Region.Sub ⟨s.gpr .a5 + BitVec.ofNat 64 128, 32⟩ ⟨s.gpr .a5, 272⟩ := Offset.sub_base _ (by decide)
  have F192 : Region.Sub ⟨s.gpr .a5 + BitVec.ofNat 64 192, 32⟩ ⟨s.gpr .a5, 272⟩ := Offset.sub_base _ (by decide)
  have inRd : ∀ {t : State}, VerInv s t → ∀ {r : Region}, r ∈ s.rd → Covers [r] (t.rd ++ t.wr) :=
    fun h r hr a n hi => by
      obtain ⟨r', hr', hc⟩ := hi
      rw [List.mem_singleton.mp hr'] at hc
      exact ⟨r, List.mem_append_left _ (by rw [h.rd]; exact hr), hc⟩
  have inF : ∀ {t : State}, VerInv s t → ∀ {d n : Nat}, d + n ≤ 272 →
      Covers [⟨s.gpr .a5 + BitVec.ofNat 64 d, n⟩] (t.rd ++ t.wr) := fun h d n hdn =>
    Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨_, List.mem_append_right _ (ver_Fw hp h), d, rfl, hdn⟩
  unfold verifyHash
  refine WP.seq (WP.mono (verSetup_ok hp) fun t₁ ⟨h₁, cs₁, cp₁⟩ => ?_)
  refine WP.seq (hashInit_ok C (sr := .s9) (h₁.regs _ (by decide)) (ver_env hp h₁)
    fun t₂ a b c f₂ g hr₂ => ?_)
  have h₂ := verStep hp h₁ a b c g f₂ (scW h₁)
  have cs₂ : bytesAt t₂.mem (s.gpr .a5 + BitVec.ofNat 64 128) 64 = bytesAt s.mem (s.gpr .a3) 64 := by
    rw [copies_keep hp h₁.sp f₂ (by decide) (by decide), cs₁]
  have cp₂ : bytesAt t₂.mem (s.gpr .a5 + BitVec.ofNat 64 192) 32 = bytesAt s.mem (s.gpr .a0) 32 := by
    rw [copies_keep hp h₁.sp f₂ (by decide) (by decide), cp₁]
  -- `R`, the signature's first half, from its copy.
  refine WP.seq (hashUpdate_ok C (sr := .s9) (src := .s10) (off := 128) (len := 32) (by decide)
    (by decide) (by decide) (h₂.regs _ (by decide)) (by rw [h₂.regs _ (by decide)]; rfl)
    (Sets.li (d := .a1) (k := 0) (by decide)) (Sets.li (d := .a3) (k := 32) (by decide))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) rfl (ver_env hp h₂) (inF h₂ (by decide))
    (hp.cF.symm.sub_left F128) (by rw [h₂.sp]; exact hp.bF.sub_right F128) fun t₃ a b c f₃ g hr₃ => ?_)
  have h₃ := verStep hp h₂ a b c g f₃ (scW h₂)
  have r₃ : Repr t₃.mem (s.gpr .a4) (bytesAt s.mem (s.gpr .a3) 32) := by
    have := hr₃ [] hr₂ rfl
    rwa [List.nil_append, ← Proof.Ed25519.signatureBytes_take, cs₂, Proof.Ed25519.signatureBytes_take] at this
  have cp₃ : bytesAt t₃.mem (s.gpr .a5 + BitVec.ofNat 64 192) 32 = bytesAt s.mem (s.gpr .a0) 32 := by
    rw [copies_keep hp h₂.sp f₃ (by decide) (by decide), cp₂]
  have cs₃ : bytesAt t₃.mem (s.gpr .a5 + BitVec.ofNat 64 128) 64 = bytesAt s.mem (s.gpr .a3) 64 := by
    rw [copies_keep hp h₂.sp f₃ (by decide) (by decide), cs₂]
  -- `A`, from its copy.
  refine WP.seq (hashUpdate_ok C (sr := .s9) (src := .s10) (off := 192) (len := 32) (by decide)
    (by decide) (by decide) (h₃.regs _ (by decide)) (by rw [h₃.regs _ (by decide)]; rfl)
    (Sets.li (d := .a1) (k := 32) (by decide)) (Sets.li (d := .a3) (k := 32) (by decide))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) rfl (ver_env hp h₃) (inF h₃ (by decide))
    (hp.cF.symm.sub_left F192) (by rw [h₃.sp]; exact hp.bF.sub_right F192) fun t₄ a b c f₄ g hr₄ => ?_)
  have h₄ := verStep hp h₃ a b c g f₄ (scW h₃)
  have r₄ : Repr t₄.mem (s.gpr .a4) (bytesAt s.mem (s.gpr .a3) 32 ++ bytesAt s.mem (s.gpr .a0) 32) := by
    have := hr₄ _ r₃ (by simp [bytesAt])
    rwa [cp₃] at this
  have cs₄ : bytesAt t₄.mem (s.gpr .a5 + BitVec.ofNat 64 128) 64 = bytesAt s.mem (s.gpr .a3) 64 := by
    rw [copies_keep hp h₃.sp f₄ (by decide) (by decide), cs₃]
  have cp₄ : bytesAt t₄.mem (s.gpr .a5 + BitVec.ofNat 64 192) 32 = bytesAt s.mem (s.gpr .a0) 32 := by
    rw [copies_keep hp h₃.sp f₄ (by decide) (by decide), cp₃]
  -- The message.
  refine WP.seq (hashUpdate_ok C (sr := .s9) (src := .s7) (off := 0) (len := (s.gpr .a2).toNat) (by decide)
    (by decide) (by decide) (h₄.regs _ (by decide))
    (by rw [h₄.regs _ (by decide), BitVec.add_zero]; rfl)
    (Sets.li (d := .a1) (k := 64) (by decide)) (Sets.mov (d := .a3) (n := .s8))
    (fun _ _ _ => rfl) (fun g g' hg => by rw [hg .s8 (by decide) (by decide) (by decide)])
    (by rw [h₄.regs _ (by decide)]; rfl) (ver_env hp h₄) (inRd h₄ (by rw [hp.rd]; simp))
    hp.mC (by rw [h₄.sp]; exact hp.bM) fun t₅ a b c f₅ g hr₅ => ?_)
  have h₅ := verStep hp h₄ a b c g f₅ (scW h₄)
  have r₅ : Repr t₅.mem (s.gpr .a4)
      (bytesAt s.mem (s.gpr .a3) 32 ++ bytesAt s.mem (s.gpr .a0) 32 ++ vmsgB s) := by
    have := hr₅ _ r₄ (by simp [bytesAt])
    rwa [ver_input h₄ (s.gpr .a2).isLt hp.mC hp.mF hp.bM.symm] at this
  have cs₅ : bytesAt t₅.mem (s.gpr .a5 + BitVec.ofNat 64 128) 64 = bytesAt s.mem (s.gpr .a3) 64 := by
    rw [copies_keep hp h₄.sp f₅ (by decide) (by decide), cs₄]
  have cp₅ : bytesAt t₅.mem (s.gpr .a5 + BitVec.ofNat 64 192) 32 = bytesAt s.mem (s.gpr .a0) 32 := by
    rw [copies_keep hp h₄.sp f₅ (by decide) (by decide), cp₄]
  refine WP.seq (hashFinalize_ok C (sr := .s9) (f := .s10) (o := 64) (out := s.gpr .a5 + BitVec.ofNat 64 64)
    (vc := fun g => g .s8 + BitVec.ofNat 64 64)
    (by decide) (by decide) (by decide) (h₅.regs _ (by decide))
    (by rw [h₅.regs _ (by decide)]; rfl)
    (Sets.addi (d := .a1) (n := .s8) (k := 64) (by decide)) (fun g g' hg => by rw [hg .s8 (by decide)])
    (ver_env hp h₅)
    (Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, ver_Fw hp h₅, 64, rfl, show 64 + 64 ≤ 272 by decide⟩)
    (hp.cF.symm.sub_left F64) (by rw [h₅.sp]; exact hp.bF.sub_right F64) fun t₆ a b c f₆ g hd₆ => ?_)
  have h₆ := verStep hp h₅ a b c g f₆ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl rfl
    · exact .inr (.inr ⟨64, 64, by decide, rfl⟩)
    · exact .inr (.inl (by rw [h₅.sp])))
  have dg : bytesAt t₆.mem (s.gpr .a5 + BitVec.ofNat 64 64) 64 =
      Spec.Sha512.sha512 (bytesAt s.mem (s.gpr .a3) 32 ++ bytesAt s.mem (s.gpr .a0) 32 ++ vmsgB s) :=
    hd₆ _ r₅ (by simp [bytesAt]; omega)
      (by rw [h₅.regs _ (by decide), cnt_eq, verV_s8]; simp [bytesAt]; congr 1; omega)
  have keep6 : ∀ {d n : Nat}, 128 ≤ d → d + n ≤ 224 →
      bytesAt t₆.mem (s.gpr .a5 + BitVec.ofNat 64 d) n = bytesAt t₅.mem (s.gpr .a5 + BitVec.ofNat 64 d) n :=
    fun {d n} hd hdn => bytes_keep f₆ (by omega) fun r hr => by
      have hs : Region.Sub ⟨s.gpr .a5 + BitVec.ofNat 64 d, n⟩ ⟨s.gpr .a5, 272⟩ := Offset.sub_base _ (by omega)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.cF.symm.sub_left hs
      · exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
      · rw [h₅.sp]; exact hp.bF.symm.sub_left hs
  have cs₆ := (keep6 (d := 128) (n := 64) (by decide) (by decide)).trans cs₅
  have cp₆ := (keep6 (d := 192) (n := 32) (by decide) (by decide)).trans cp₅
  -- `scalar_reduce`.
  have ce : ∀ (u : State) q, q ∉ linkRegs → ∀ rd wr, (u.callEntry.withRegions rd wr).gpr q = u.gpr q :=
    fun _ q hq _ _ => by rw [State.withRegions_gpr, State.callEntry_gpr _ hq]
  have hFw := ver_Fw hp h₆
  have hCw : (⟨s.gpr .a4, 8192⟩ : Region) ∈ t₆.wr := (ver_env hp h₆).w
  unfold mov
  refine WP.seq (args3_ok (by decide) (by decide) (by decide) (by decide) (by decide) fun t₇ k₇ c3 c4 c5 => ?_)
  rw [h₆.regs _ (by decide), verV_s10, BitVec.add_zero] at c3
  rw [h₆.regs _ (by decide), verV_s10] at c4
  rw [h₆.regs _ (by decide), BitVec.add_zero, verV_s9] at c5
  refine WP.seq (WP.call (k := reduceRISCV64) reduce_ok' (rd := [⟨s.gpr .a5 + BitVec.ofNat 64 64, 64⟩])
    (wr := [⟨s.gpr .a5, 32⟩, ⟨s.gpr .a4, 8192⟩])
    ⟨by rw [State.withRegions_rd, ce _ _ (by decide), c4],
      by rw [State.withRegions_wr, ce _ _ (by decide), ce _ _ (by decide), c3, c5],
      by rw [ce _ _ (by decide), ce _ _ (by decide), c3, c4]; exact Offset.base_disjoint _ (by decide) (by decide),
      by rw [ce _ _ (by decide), ce _ _ (by decide), c3, c5]; exact hp.cF.symm.sub_left F0,
      by rw [ce _ _ (by decide), ce _ _ (by decide), c4, c5]; exact hp.cF.symm.sub_left F64⟩
    (Covers.of_sub fun r hr => by
      rw [k₇.rd, k₇.wr]
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_append_right _ hFw, 64, rfl, show 64 + 64 ≤ 272 by decide⟩
      · exact ⟨_, List.mem_append_right _ hFw, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ hCw, 0, by simp, by simp⟩)
    (Covers.of_sub fun r hr => by
      rw [k₇.wr]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, hFw, 0, by simp, by simp⟩
      · exact ⟨_, hCw, 0, by simp, by simp⟩) (fun t₈ a b c f₈ g _ hpost => ?_) (by decide +kernel))
  simp only [reduceRISCV64, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem,
    State.callEntry_gpr _ (show Reg.a0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a1 ∉ linkRegs by decide),
    c3, c4, k₇.mem, dg] at hpost
  have h₈ := verStep hp h₆ (a.trans k₇.rd) (b.trans k₇.wr) (c.trans k₇.sp)
    (fun r hr => (g r hr).trans (k₇.pres r hr)) (k₇.mem ▸ f₈) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr (.inr ⟨0, 32, by decide, by simp⟩)
      · exact .inl rfl
  have keep8 : ∀ {d n : Nat}, 128 ≤ d → d + n ≤ 224 →
      bytesAt t₈.mem (s.gpr .a5 + BitVec.ofNat 64 d) n = bytesAt t₆.mem (s.gpr .a5 + BitVec.ofNat 64 d) n :=
    fun {d n} hd hdn => by
      rw [← k₇.mem]
      exact bytes_keep f₈ (by omega) fun r hr => by
        have hs : Region.Sub ⟨s.gpr .a5 + BitVec.ofNat 64 d, n⟩ ⟨s.gpr .a5, 272⟩ := Offset.sub_base _ (by omega)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Offset.disjoint_base _ (by omega) (by omega)
        · exact hp.cF.symm.sub_left hs
  have cs₈ := (keep8 (d := 128) (n := 64) (by decide) (by decide)).trans cs₆
  have cp₈ := (keep8 (d := 192) (n := 32) (by decide) (by decide)).trans cp₆
  -- The upper half zeroed, and the arguments.
  have hFw₈ : (⟨s.gpr .a5, 272⟩ : Region) ∈ t₈.wr := ver_Fw hp h₈
  have e10 : t₈.gpr .s10 = s.gpr .a5 := h₈.regs _ (by decide)
  have inF8 : ∀ (u : State), u.wr = t₈.wr → ∀ d, d + 8 ≤ 272 → InRegions u.wr (s.gpr .a5 + BitVec.ofNat 64 d) 8 :=
    fun u hu d hd => by rw [hu]; exact in_base hFw₈ hd (by omega)
  refine wp_li (d := .a5) (imm := 0) (by decide) fun u₁ e₁ => ?_
  refine wp_stdd (a := s.gpr .a5 + BitVec.ofNat 64 32) ⟨by decide, Spill.al8 hp.alF (by decide)⟩
    (by rw [e₁.other _ (by decide), e10]) (inF8 _ e₁.wr 32 (by decide)) fun u₂ e₂ => ?_
  refine wp_stdd (a := s.gpr .a5 + BitVec.ofNat 64 40) ⟨by decide, Spill.al8 hp.alF (by decide)⟩
    (by rw [e₂.gpr, e₁.other _ (by decide), e10]) (inF8 _ (by rw [e₂.wr, e₁.wr]) 40 (by decide)) fun u₃ e₃ => ?_
  refine wp_stdd (a := s.gpr .a5 + BitVec.ofNat 64 48) ⟨by decide, Spill.al8 hp.alF (by decide)⟩
    (by rw [e₃.gpr, e₂.gpr, e₁.other _ (by decide), e10]) (inF8 _ (by rw [e₃.wr, e₂.wr, e₁.wr]) 48 (by decide))
    fun u₄ e₄ => ?_
  refine wp_stdd (a := s.gpr .a5 + BitVec.ofNat 64 56) ⟨by decide, Spill.al8 hp.alF (by decide)⟩
    (by rw [e₄.gpr, e₃.gpr, e₂.gpr, e₁.other _ (by decide), e10])
    (inF8 _ (by rw [e₄.wr, e₃.wr, e₂.wr, e₁.wr]) 56 (by decide)) fun u₅ e₅ => ?_
  refine wp_addi (by decide) fun v₁ g₁ => wp_addi (by decide) fun v₂ g₂ =>
    wp_addi (by decide) fun v₃ g₃ => wp_addi (by decide) fun v₄ g₄ => WP.block_nil ?_
  have z₁ : u₁.gpr .a5 = 0 := e₁.gpr
  have z₂ : u₂.gpr .a5 = 0 := by rw [e₂.gpr, z₁]
  have z₃ : u₃.gpr .a5 = 0 := by rw [e₃.gpr, z₂]
  have z₄ : u₄.gpr .a5 = 0 := by rw [e₄.gpr, z₃]
  have mv : v₄.mem = ((((t₈.mem.writeW (s.gpr .a5 + BitVec.ofNat 64 32) (0 : BitVec 64)).writeW
      (s.gpr .a5 + BitVec.ofNat 64 40) (0 : BitVec 64)).writeW (s.gpr .a5 + BitVec.ofNat 64 48) (0 : BitVec 64)).writeW
      (s.gpr .a5 + BitVec.ofNat 64 56) (0 : BitVec 64)) := by
    rw [g₄.mem, g₃.mem, g₂.mem, g₁.mem, e₅.mem, e₄.mem, e₃.mem, e₂.mem, e₁.mem, z₁, z₂, z₃, z₄]
  have gp : ∀ r ∈ preserved, v₄.gpr r = t₈.gpr r := fun r hr => by
    obtain ⟨p0, p1, p2, p3, -⟩ := pres_args hr
    rw [g₄.other _ p3, g₃.other _ p2, g₂.other _ p1, g₁.other _ p0, e₅.gpr, e₄.gpr, e₃.gpr, e₂.gpr,
      e₁.other _ (by revert hr; cases r <;> decide)]
  have cont : ∀ d, 32 ≤ d → d + 8 ≤ 64 → Region.Contains ⟨s.gpr .a5 + BitVec.ofNat 64 32, 32⟩
      (s.gpr .a5 + BitVec.ofNat 64 d) (64 / 8) := fun d h₁ h₂ => Offset.contains _ h₁ (by omega) (by omega)
  have fv : Frame [⟨s.gpr .a5 + BitVec.ofNat 64 32, 32⟩] t₈.mem v₄.mem := by
    rw [mv]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cont 32 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cont 40 (by decide) (by decide))).writeW (List.mem_singleton_self _) _
      (cont 48 (by decide) (by decide))).writeW (List.mem_singleton_self _) _ (cont 56 (by decide) (by decide))
  have rr : ∀ (x : Mem) (i j : Nat) (v : BitVec 64), i + 8 ≤ j ∨ j + 8 ≤ i → i + 8 ≤ 272 → j + 8 ≤ 272 →
      (x.writeW (s.gpr .a5 + BitVec.ofNat 64 j) v).readW (s.gpr .a5 + BitVec.ofNat 64 i) 64 =
        x.readW (s.gpr .a5 + BitVec.ofNat 64 i) 64 :=
    fun x i j v h hi hj => Mem.readW_writeW_sep (Offset.sep _ h (by omega) (by omega)) (by decide)
  have hz : ∀ k < 4, v₄.mem.readW (s.gpr .a5 + BitVec.ofNat 64 32 + BitVec.ofNat 64 (8 * k)) 64 = 0 := by
    intro k hk
    rw [mv, Offset.add_add]
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl
    · rw [show 32 + 8 * 0 = 32 from rfl, rr _ 32 56 _ (by decide) (by decide) (by decide),
        rr _ 32 48 _ (by decide) (by decide) (by decide), rr _ 32 40 _ (by decide) (by decide) (by decide),
        Mem.readW_writeW_self64]
    · rw [show 32 + 8 * 1 = 40 from rfl, rr _ 40 56 _ (by decide) (by decide) (by decide),
        rr _ 40 48 _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
    · rw [show 32 + 8 * 2 = 48 from rfl, rr _ 48 56 _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
    · rw [show 32 + 8 * 3 = 56 from rfl, Mem.readW_writeW_self64]
  have keepv : ∀ {d n : Nat}, 128 ≤ d → d + n ≤ 224 →
      bytesAt v₄.mem (s.gpr .a5 + BitVec.ofNat 64 d) n = bytesAt t₈.mem (s.gpr .a5 + BitVec.ofNat 64 d) n :=
    fun hd hdn => bytes_keep fv (by omega) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  refine ⟨verStep hp h₈ (by rw [g₄.rd, g₃.rd, g₂.rd, g₁.rd, e₅.rd, e₄.rd, e₃.rd, e₂.rd, e₁.rd])
    (by rw [g₄.wr, g₃.wr, g₂.wr, g₁.wr, e₅.wr, e₄.wr, e₃.wr, e₂.wr, e₁.wr])
    (by rw [g₄.sp, g₃.sp, g₂.sp, g₁.sp, e₅.sp, e₄.sp, e₃.sp, e₂.sp, e₁.sp]) gp fv fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inr (.inr ⟨32, 32, by decide, rfl⟩), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g₄.other _ (by decide), g₃.other _ (by decide), g₂.other _ (by decide), g₁.gpr,
      e₅.gpr, e₄.gpr, e₃.gpr, e₂.gpr, e₁.other _ (by decide), e10]
  · rw [g₄.other _ (by decide), g₃.other _ (by decide), g₂.gpr, g₁.other _ (by decide),
      e₅.gpr, e₄.gpr, e₃.gpr, e₂.gpr, e₁.other _ (by decide), e10]
  · rw [g₄.other _ (by decide), g₃.gpr, g₂.other _ (by decide), g₁.other _ (by decide), BitVec.add_zero,
      e₅.gpr, e₄.gpr, e₃.gpr, e₂.gpr, e₁.other _ (by decide), e10]
  · rw [g₄.gpr, g₃.other _ (by decide), g₂.other _ (by decide), g₁.other _ (by decide), BitVec.add_zero,
      e₅.gpr, e₄.gpr, e₃.gpr, e₂.gpr, e₁.other _ (by decide), h₈.regs _ (by decide)]; rfl
  · have low : bytesAt v₄.mem (s.gpr .a5) 32 = bytesAt t₈.mem (s.gpr .a5) 32 :=
      bytes_keep fv (by decide) fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.base_disjoint _ (by decide) (by decide)
    rw [Proof.Ed25519.signatureBytes_split, low, hpost, bytes32_zero hz, ← Proof.Ed25519.reduced_challenge]
  · rw [keepv (by decide) (by decide), cp₈]
  · rw [keepv (by decide) (by decide), cs₈]

end VG.Proof.Ed25519.RISCV64.Whole
